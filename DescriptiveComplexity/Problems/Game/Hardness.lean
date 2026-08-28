/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Game.Membership
import DescriptiveComplexity.Problems.HornSat
import DescriptiveComplexity.Problems.HornSat.Unsat
import DescriptiveComplexity.OccurrenceOrder

/-!
# HORN-SAT to GAME: unit propagation is a game

The hardness half of `DescriptiveComplexity.GAME`. The AND/OR graph drawn
inside a `Language.sat`-instance is unit propagation read as a game:

* a **variable** `x` is an existential node – to win at it, name a clause that
  forces it;
* a **clause** `c` is a universal node – the opponent challenges one of its
  negative literals, and the game continues there;
* a clause with **no** negative literal wins outright, which is what the
  `won` mark of `FirstOrder.Language.andOrGraph` is for and why a stuck
  universal node had to *lose* (`DescriptiveComplexity.Problems.Game.Defs`);
* the **goal** clauses – those with no positive literal – are the marked
  starts.

So the existential player wins exactly when some goal clause has all its
negative literals forced, which on a Horn formula is exactly unsatisfiability
(`DescriptiveComplexity.exists_goalClause` in one direction,
`DescriptiveComplexity.forced_subset_model` in the other).

## Reducing from the complement

The game computes a *least* fixed point, so what it decides is Horn
**un**satisfiability; a game deciding satisfiability would have to negate the
propagation. That costs nothing, since polynomial time is closed under
complement (`DescriptiveComplexity.piP_zero_eq`), and the last step is the same
one `DescriptiveComplexity.Problems.Cvp.Hardness` takes.

## The non-Horn escape

`DescriptiveComplexity.HORNSAT` folds the promise “at most one positive literal
per clause” into its yes-instances, so its complement holds outright on an
instance that is not Horn. The interpretation therefore marks *every* node both
`start` and `won` when the instance fails the promise
(`DescriptiveComplexity.GameHard.nonHornG`, a sentence, hence available to
every defining formula), which makes such an instance a yes-instance of GAME
with no propagation at all.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace GameHard

/-- The ordered expansion of the vocabulary of CNF formulas. -/
abbrev satOrd : Language.{0, 0} := Language.sat.sum Language.order

/-- The clause symbol in the ordered expansion. -/
abbrev satIsClauseO : satOrd.Relations 1 := Sum.inl satIsClause

/-- The positive-occurrence symbol in the ordered expansion. -/
abbrev satPosInO : satOrd.Relations 2 := Sum.inl satPosIn

/-- The negative-occurrence symbol in the ordered expansion. -/
abbrev satNegInO : satOrd.Relations 2 := Sum.inl satNegIn

/-- The two sorts of node the interpretation draws. -/
inductive GTag where
  /-- A propositional variable. -/
  | var
  /-- A clause. -/
  | cl
  deriving DecidableEq

instance : Fintype GTag := ⟨{GTag.var, GTag.cl}, by intro x; cases x <;> simp⟩

instance : Nonempty GTag := ⟨GTag.var⟩

/-! ### The guards -/

section Guards

variable {γ : Type}

/-- `x` is a clause, as a guard. -/
noncomputable def isClauseG (x : γ) : satOrd.Formula γ :=
  Relations.formula₁ satIsClauseO (Term.var x)

/-- `x` occurs positively in the clause `c`, as a guard. -/
noncomputable def posInG (c x : γ) : satOrd.Formula γ :=
  Relations.formula₂ satPosInO (Term.var c) (Term.var x)

/-- `x` occurs negatively in the clause `c`, as a guard. -/
noncomputable def negInG (c x : γ) : satOrd.Formula γ :=
  Relations.formula₂ satNegInO (Term.var c) (Term.var x)

/-- The instance is **not** Horn: some clause has two distinct positive
literals. A sentence, so every defining formula may use it. -/
noncomputable def nonHornG : satOrd.Formula γ :=
  fo% ∃ c x y, ((isClauseG⟨c⟩ ∧ posInG⟨c, x⟩) ∧ posInG⟨c, y⟩) ∧ ¬ x ≐ y

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_isClauseG (x : γ) :
    (isClauseG x).Realize v ↔ RelMap satIsClause ![v x] := by
  rw [isClauseG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_posInG (c x : γ) : (posInG c x).Realize v ↔ RelMap satPosIn ![v c, v x] := by
  rw [posInG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_negInG (c x : γ) : (negInG c x).Realize v ↔ RelMap satNegIn ![v c, v x] := by
  rw [negInG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

theorem realize_nonHornG : (nonHornG (γ := γ)).Realize v ↔ ¬AtMostOnePositive A := by
  rw [nonHornG, AtMostOnePositive]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_not,
    realize_isClauseG, realize_posInG, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, not_forall]
  constructor
  · rintro ⟨w, ⟨⟨hc, hp1⟩, hp2⟩, hne⟩
    exact ⟨w 0, w 1, w 2, hc, hp1, hp2, hne⟩
  · rintro ⟨c, x, y, hc, hp1, hp2, hne⟩
    exact ⟨![c, x, y], ⟨⟨hc, hp1⟩, hp2⟩, hne⟩

end Guards

/-! ### The interpretation -/

open Classical in
/-- **The AND/OR graph of unit propagation**: variables are existential nodes,
clauses universal ones, a clause with no negative literal wins outright, and
the goal clauses are the marked starts. -/
noncomputable def gameInterp : FOInterpretation satOrd Language.andOrGraph GTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .move => fun t =>
        match t 0, t 1 with
        | .var, .cl => fo%⟨x, c⟩ isClauseG⟨c⟩ ∧ posInG⟨c, x⟩
        | .cl, .var => fo%⟨c, x⟩ isClauseG⟨c⟩ ∧ negInG⟨c, x⟩
        | _, _ => ⊥
    | _, .univ => fun t =>
        match t 0 with
        | .var => ⊥
        | .cl => ⊤
    | _, .start => fun t =>
        match t 0 with
        | .var => nonHornG
        | .cl => fo%⟨c⟩ (isClauseG⟨c⟩ ∧ ∀ x, ¬ posInG⟨c, x⟩) ∨ !nonHornG
    | _, .won => fun t =>
        match t 0 with
        | .var => nonHornG
        | .cl => fo%⟨c⟩ (isClauseG⟨c⟩ ∧ ∀ y, ¬ negInG⟨c, y⟩) ∨ !nonHornG

/-! ### The points -/

section Points

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The node of a propositional variable. -/
def varPt (x : A) : gameInterp.Map A := (GTag.var, fun _ => x)

/-- The node of a clause. -/
def clPt (c : A) : gameInterp.Map A := (GTag.cl, fun _ => c)

omit [Language.sat.Structure A] [LinearOrder A] in
/-- Every node is a variable node or a clause node. -/
theorem pt_cases (p : gameInterp.Map A) : (∃ x, p = varPt x) ∨ ∃ c, p = clPt c := by
  obtain ⟨t, w⟩ := p
  have hw : w = fun _ => w 0 := funext fun j => congrArg w (Subsingleton.elim j 0)
  cases t with
  | var => exact Or.inl ⟨w 0, by rw [varPt, hw]⟩
  | cl => exact Or.inr ⟨w 0, by rw [clPt, hw]⟩

/-! ### Reading the drawn graph -/

@[simp]
theorem move_var_cl (x c : A) :
    AGMove (varPt x) (clPt c) ↔ RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] := by
  rw [AGMove, FOInterpretation.relMap_map]
  exact Formula.realize_inf.trans
    (and_congr (realize_isClauseG (A := A) _) (realize_posInG (A := A) _ _))

@[simp]
theorem move_cl_var (c y : A) :
    AGMove (clPt c) (varPt y) ↔ RelMap satIsClause ![c] ∧ RelMap satNegIn ![c, y] := by
  rw [AGMove, FOInterpretation.relMap_map]
  exact Formula.realize_inf.trans
    (and_congr (realize_isClauseG (A := A) _) (realize_negInG (A := A) _ _))

@[simp]
theorem move_var_var (x y : A) : ¬AGMove (varPt x) (varPt y) := by
  rw [AGMove, FOInterpretation.relMap_map]
  exact Formula.realize_bot.mp

@[simp]
theorem move_cl_cl (c c' : A) : ¬AGMove (clPt c) (clPt c') := by
  rw [AGMove, FOInterpretation.relMap_map]
  exact Formula.realize_bot.mp

@[simp]
theorem univ_var (x : A) : ¬AGUniv (varPt x) := by
  rw [AGUniv, FOInterpretation.relMap_map]
  exact Formula.realize_bot.mp

@[simp]
theorem univ_cl (c : A) : AGUniv (clPt c) := by
  rw [AGUniv, FOInterpretation.relMap_map]
  exact Formula.realize_top.mpr trivial

@[simp]
theorem won_var (x : A) : AGWon (varPt x) ↔ ¬AtMostOnePositive A := by
  rw [AGWon, FOInterpretation.relMap_map]
  exact realize_nonHornG

@[simp]
theorem won_cl (c : A) :
    AGWon (clPt c) ↔
      (RelMap satIsClause ![c] ∧ ∀ y : A, ¬RelMap satNegIn ![c, y]) ∨ ¬AtMostOnePositive A := by
  rw [AGWon, FOInterpretation.relMap_map]
  refine Formula.realize_sup.trans (or_congr ?_ realize_nonHornG)
  refine Formula.realize_inf.trans (and_congr (realize_isClauseG (A := A) _) ?_)
  simp only [Formula.realize_iAlls, Formula.realize_not, realize_negInG, Sum.elim_inl,
    Sum.elim_inr]
  exact ⟨fun h y => h fun _ => y, fun h w => h (w 0)⟩

@[simp]
theorem start_var (x : A) : AGStart (varPt x) ↔ ¬AtMostOnePositive A := by
  rw [AGStart, FOInterpretation.relMap_map]
  exact realize_nonHornG

@[simp]
theorem start_cl (c : A) :
    AGStart (clPt c) ↔
      (RelMap satIsClause ![c] ∧ ∀ x : A, ¬RelMap satPosIn ![c, x]) ∨ ¬AtMostOnePositive A := by
  rw [AGStart, FOInterpretation.relMap_map]
  refine Formula.realize_sup.trans (or_congr ?_ realize_nonHornG)
  refine Formula.realize_inf.trans (and_congr (realize_isClauseG (A := A) _) ?_)
  simp only [Formula.realize_iAlls, Formula.realize_not, realize_posInG, Sum.elim_inl,
    Sum.elim_inr]
  exact ⟨fun h y => h fun _ => y, fun h w => h (w 0)⟩

end Points

/-! ### Winning is being forced -/

section Correct

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- What winning says at each of the two sorts of node. -/
def Good (p : gameInterp.Map A) : Prop :=
  match p.1 with
  | .var => Forced (p.2 0)
  | .cl => RelMap satIsClause ![p.2 0] ∧ ∀ y : A, RelMap satNegIn ![p.2 0, y] → Forced y

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem good_varPt (x : A) : Good (varPt x) ↔ Forced x := Iff.rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem good_clPt (c : A) :
    Good (clPt c) ↔ RelMap satIsClause ![c] ∧ ∀ y : A, RelMap satNegIn ![c, y] → Forced y := Iff.rfl

omit [Nonempty A] in
/-- **Soundness**: a winning node is forced, and a winning clause node has all
its negative literals forced. -/
theorem good_of_winsOn (hhorn : AtMostOnePositive A) {p : gameInterp.Map A}
    (h : WinsOn (gameInterp.Map A) p) : Good p := by
  induction h with
  | @won b hb =>
    rcases pt_cases b with ⟨x, rfl⟩ | ⟨c, rfl⟩
    · exact absurd hhorn ((won_var x).mp hb)
    · rcases (won_cl c).mp hb with ⟨hc, hno⟩ | hnh
      · exact (good_clPt c).mpr ⟨hc, fun y hy => absurd hy (hno y)⟩
      · exact absurd hhorn hnh
  | @ex b b' hu hm _ ih =>
    rcases pt_cases b with ⟨x, rfl⟩ | ⟨c, rfl⟩
    · rcases pt_cases b' with ⟨y, rfl⟩ | ⟨c, rfl⟩
      · exact absurd hm (move_var_var x y)
      · obtain ⟨hc, hpos⟩ := (move_var_cl x c).mp hm
        obtain ⟨hcc, hall⟩ := (good_clPt c).mp ih
        obtain ⟨N, hN⟩ := exists_forcedIn_bound (A := A)
        exact (good_varPt x).mpr ⟨N + 1, c, hc, hpos, fun y hy => hN y (hall y hy)⟩
    · exact absurd (univ_cl c) hu
  | @all b hu hex _ ih =>
    rcases pt_cases b with ⟨x, rfl⟩ | ⟨c, rfl⟩
    · exact absurd hu (univ_var x)
    · obtain ⟨d, hd⟩ := hex
      have hc : RelMap satIsClause ![c] := by
        rcases pt_cases d with ⟨y, rfl⟩ | ⟨c', rfl⟩
        · exact ((move_cl_var c y).mp hd).1
        · exact absurd hd (move_cl_cl c c')
      refine (good_clPt c).mpr ⟨hc, fun y hy => ?_⟩
      exact (good_varPt y).mp (ih (varPt y) ((move_cl_var c y).mpr ⟨hc, hy⟩))

omit [Finite A] [Nonempty A] in
/-- A clause node with all its negative literals winning is winning: the
opponent's every challenge is answered, and a clause with nothing to challenge
wins outright. -/
theorem winsOn_clPt {c : A} (hc : RelMap satIsClause ![c])
    (hall : ∀ y : A, RelMap satNegIn ![c, y] → WinsOn (gameInterp.Map A) (varPt y)) :
    WinsOn (gameInterp.Map A) (clPt c) := by
  by_cases hsome : ∃ y : A, RelMap satNegIn ![c, y]
  · obtain ⟨y₀, hy₀⟩ := hsome
    refine .all (univ_cl c) ⟨varPt y₀, (move_cl_var c y₀).mpr ⟨hc, hy₀⟩⟩ (fun d hd => ?_)
    rcases pt_cases d with ⟨y, rfl⟩ | ⟨c', rfl⟩
    · exact hall y ((move_cl_var c y).mp hd).2
    · exact absurd hd (move_cl_cl c c')
  · refine .won ((won_cl c).mpr (Or.inl ⟨hc, fun y hy => hsome ⟨y, hy⟩⟩))

omit [Finite A] [Nonempty A] in
/-- **Completeness**: a forced variable wins. -/
theorem winsOn_of_forcedIn : ∀ (n : ℕ) (x : A), ForcedIn n x →
    WinsOn (gameInterp.Map A) (varPt x) := by
  intro n
  induction n with
  | zero => intro x h; exact h.elim
  | succ n ih =>
    rintro x ⟨c, hc, hpos, hneg⟩
    exact .ex (univ_var x) ((move_var_cl x c).mpr ⟨hc, hpos⟩)
      (winsOn_clPt hc fun y hy => ih y (hneg y hy))

omit [Finite A] [Nonempty A] in
theorem winsOn_of_forced {x : A} (h : Forced x) : WinsOn (gameInterp.Map A) (varPt x) := by
  obtain ⟨n, hn⟩ := h
  exact winsOn_of_forcedIn n x hn

/-! ### The game is won exactly on the no-instances -/

omit [Nonempty A] in
/-- On a Horn instance, the game is won exactly when some goal clause has all
its negative literals forced. -/
theorem gameWon_iff_goalClause (hhorn : AtMostOnePositive A) :
    GameWon (gameInterp.Map A) ↔
      ∃ c : A, RelMap satIsClause ![c] ∧ (∀ x : A, ¬RelMap satPosIn ![c, x]) ∧
        ∀ y : A, RelMap satNegIn ![c, y] → Forced y := by
  constructor
  · rintro ⟨s, hs, hw⟩
    rcases pt_cases s with ⟨x, rfl⟩ | ⟨c, rfl⟩
    · exact absurd hhorn ((start_var x).mp hs)
    · rcases (start_cl c).mp hs with ⟨hc, hno⟩ | hnh
      · exact ⟨c, hc, hno, ((good_clPt c).mp (good_of_winsOn hhorn hw)).2⟩
      · exact absurd hhorn hnh
  · rintro ⟨c, hc, hno, hall⟩
    exact ⟨clPt c, (start_cl c).mpr (Or.inl ⟨hc, hno⟩),
      winsOn_clPt hc fun y hy => winsOn_of_forced (hall y hy)⟩

/-- **The reduction is correct**: the game is won exactly on the instances that
are *not* yes-instances of HORN-SAT. -/
theorem gameWon_iff_not_hornSatisfiable :
    ¬HornSatisfiable A ↔ GameWon (gameInterp.Map A) := by
  classical
  by_cases hhorn : AtMostOnePositive A
  · rw [gameWon_iff_goalClause hhorn]
    constructor
    · intro h
      obtain ⟨c, hc, hall, hno⟩ := exists_goalClause fun hsat => h ⟨hhorn, hsat⟩
      exact ⟨c, hc, hno, hall⟩
    · rintro ⟨c, hc, hno, hall⟩ ⟨-, ν, hν⟩
      obtain ⟨x, hx | hx⟩ := hν c hc
      · exact hno x hx.1
      · exact hx.2 (forced_subset_model hhorn (fun c' hc' => hν c' hc') x (hall x hx.1))
  · refine iff_of_true (fun h => hhorn h.1) ?_
    obtain ⟨a⟩ := ‹Nonempty A›
    exact ⟨varPt a, (start_var a).mpr hhorn, .won ((won_var a).mpr hhorn)⟩

end Correct

end GameHard

open GameHard in
/-- **The complement of HORN-SAT reduces to GAME**: unit propagation, read as a
game. -/
noncomputable def hornSatCompl_ordered_fo_reduction_game : HORNSATᶜ ≤ᶠᵒ[≤] GAME where
  Tag := GTag
  dim := 1
  toInterpretation := gameInterp
  correct := fun _A _ _ _ _ => gameWon_iff_not_hornSatisfiable

/-- **GAME is PTIME-hard**: every SO-Horn definable problem reduces to it. The
route is the Horn discharge applied to the *complement* of the problem,
complemented back – which is available because polynomial time is closed under
complement. -/
theorem game_PTIME_hard : PTIME.Hard GAME := by
  refine (hard_PTIME_iff GAME).mpr fun Q hQ => ?_
  obtain ⟨f⟩ := hornSat_hard_of_sigmaSOHornDefinable Qᶜ hQ.compl
  exact ⟨((f.compl.congrSource fun A _ _ => not_not).trans
    hornSatCompl_ordered_fo_reduction_game).toRel⟩

/-- **GAME is PTIME-complete.** Membership is
`DescriptiveComplexity.game_mem_PTIME`, the least fixed point with its scan of
the order; hardness is unit propagation read as a game. -/
theorem game_PTIME_complete : PTIME.Complete GAME :=
  ⟨game_mem_PTIME, game_PTIME_hard⟩

end DescriptiveComplexity
