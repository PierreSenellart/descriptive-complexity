/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Game.Defs
import DescriptiveComplexity.FixedPointHorn
import DescriptiveComplexity.OrderWalk

/-!
# GAME is in PTIME

The membership half: `DescriptiveComplexity.GAME` is FO(LFP) definable
(`DescriptiveComplexity.game_lfpDefinable`), hence in
`DescriptiveComplexity.PTIME` by the Immerman–Vardi capture theorem the library
already carries.

## Why a second relation variable is needed

The winning set *is* a least fixed point, and two of its three clauses are
Horn rules already. The third is not:

> a universal node wins when it has a successor and **every** successor wins

has a universally quantified body, and a `DescriptiveComplexity.HornClause`
carries a *list* of atoms, not a quantified one. The standard repair is to walk
the order: a second variable `allge x y` – “every successor of `x` that is
`≥ y` wins” – is computed by a **downward** induction along the linear order,
from the greatest element to the least, one immediate predecessor at a time
(`DescriptiveComplexity.order_induction_down`). At the least element it says
“every successor of `x` wins”, which is the body the third clause wanted.

That this stays a *least* fixed point is the point of doing it this way: `allge`
is derivable exactly when the winners it quantifies over are already derived, so
nothing is derived early and the two variables grow together.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Game

/-- The ordered expansion of the vocabulary of AND/OR graphs. -/
abbrev agOrd : Language.{0, 0} := Language.andOrGraph.sum Language.order

/-! ### The block -/

/-- The relation variables the fixed point computes. -/
inductive GIx where
  /-- `win x`: the node `x` is winning. -/
  | win
  /-- `allge x y`: every successor of `x` that is at least `y` is winning. -/
  | allge
  deriving DecidableEq

instance : Fintype GIx := ⟨{GIx.win, GIx.allge}, by intro x; cases x <;> simp⟩

/-- The block of the fixed point: the winning set, and the scan that collects a
universal node's successors from the greatest element downwards. -/
abbrev gameBlock : SOBlock where
  ι := GIx
  arity := fun i => match i with | .win => 1 | .allge => 2

/-- The atom `win x`. -/
def winAt (x : Fin 3) : SOAtom gameBlock 3 := ⟨GIx.win, fun _ => x⟩

/-- The atom `allge x y`. -/
def allgeAt (x y : Fin 3) : SOAtom gameBlock 3 := ⟨GIx.allge, ![x, y]⟩

/-! ### The guards -/

section Guards

variable {α : Type}

/-- The node `x` wins outright, as a guard. -/
noncomputable def wonG (x : α) : agOrd.Formula α := Relations.formula₁ agWonO (Term.var x)

/-- The node `x` belongs to the universal player, as a guard. -/
noncomputable def univG (x : α) : agOrd.Formula α := Relations.formula₁ agUnivO (Term.var x)

/-- The node `x` is a marked start, as a guard. -/
noncomputable def startG (x : α) : agOrd.Formula α := Relations.formula₁ agStartO (Term.var x)

/-- There is a move from `x` to `y`, as a guard. -/
noncomputable def moveG (x y : α) : agOrd.Formula α :=
  Relations.formula₂ agMoveO (Term.var x) (Term.var y)

variable {A : Type} [Language.andOrGraph.Structure A] [LinearOrder A] {v : α → A}

@[simp]
theorem realize_wonG (x : α) : (wonG x).Realize v ↔ AGWon (v x) := by
  rw [wonG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_univG (x : α) : (univG x).Realize v ↔ AGUniv (v x) := by
  rw [univG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_startG (x : α) : (startG x).Realize v ↔ AGStart (v x) := by
  rw [startG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_moveG (x y : α) : (moveG x y).Realize v ↔ AGMove (v x) (v y) := by
  rw [moveG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

end Guards

/-! ### The rules -/

/-- A node that wins outright is winning. -/
noncomputable def rWon : HornClause agOrd gameBlock 3 :=
  ⟨wonG 0, [], some (winAt 0)⟩

/-- An existential node with a winning successor is winning. -/
noncomputable def rEx : HornClause agOrd gameBlock 3 :=
  ⟨∼(univG 0) ⊓ moveG 0 1, [winAt 1], some (winAt 0)⟩

/-- A universal node with a successor, all of whose successors are winning, is
winning: the scan has reached the least element. -/
noncomputable def rAll : HornClause agOrd gameBlock 3 :=
  ⟨univG 0 ⊓ moveG 0 1 ⊓ minF 2, [allgeAt 0 2], some (winAt 0)⟩

/-- The scan starts at the greatest element, which is not a successor. -/
noncomputable def rTopNo : HornClause agOrd gameBlock 3 :=
  ⟨maxF 1 ⊓ ∼(moveG 0 1), [], some (allgeAt 0 1)⟩

/-- The scan starts at the greatest element, which is a winning successor. -/
noncomputable def rTopYes : HornClause agOrd gameBlock 3 :=
  ⟨maxF 1 ⊓ moveG 0 1, [winAt 1], some (allgeAt 0 1)⟩

/-- The scan steps down past an element that is not a successor. -/
noncomputable def rStepNo : HornClause agOrd gameBlock 3 :=
  ⟨succF 1 2 ⊓ ∼(moveG 0 1), [allgeAt 0 2], some (allgeAt 0 1)⟩

/-- The scan steps down past a winning successor. -/
noncomputable def rStepYes : HornClause agOrd gameBlock 3 :=
  ⟨succF 1 2 ⊓ moveG 0 1, [winAt 1, allgeAt 0 2], some (allgeAt 0 1)⟩

/-- The rules of the definition. -/
noncomputable def gameRules : List (HornClause agOrd gameBlock 3) :=
  [rWon, rEx, rAll, rTopNo, rTopYes, rStepNo, rStepYes]

theorem rWon_mem : rWon ∈ gameRules := by simp [gameRules]

theorem rEx_mem : rEx ∈ gameRules := by simp [gameRules]

theorem rAll_mem : rAll ∈ gameRules := by simp [gameRules]

theorem rTopNo_mem : rTopNo ∈ gameRules := by simp [gameRules]

theorem rTopYes_mem : rTopYes ∈ gameRules := by simp [gameRules]

theorem rStepNo_mem : rStepNo ∈ gameRules := by simp [gameRules]

theorem rStepYes_mem : rStepYes ∈ gameRules := by simp [gameRules]

/-! ### The output -/

/-- **The output**: some marked start is winning. -/
noncomputable def gameOut : ((agOrd).sum gameBlock.lang).Sentence :=
  Formula.iExs (Fin 3) (atomF (winAt 0) ⊓ guardOutF (startG 0))

/-! ### The intended fixed point -/

section Correct

variable {A : Type} [Language.andOrGraph.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable (A) in
/-- The assignment the rules are meant to compute. -/
def gameAssign : gameBlock.Assignment A := fun i =>
  match i with
  | .win => fun t => WinsOn A (t 0)
  | .allge => fun t => ∀ c : A, t 1 ≤ c → AGMove (t 0) c → WinsOn A c

omit [Finite A] [Nonempty A] in
/-- The intended assignment is closed under the rules, so the least fixed point
is contained in it. -/
theorem gameAssign_closed :
    ∀ c ∈ gameRules, ∀ a : SOAtom gameBlock 3, c.head = some a →
      ∀ v : Fin 3 → A, c.guard.Realize v →
        (∀ b ∈ c.body, b.Holds (gameAssign A) v) → a.Holds (gameAssign A) v := by
  intro c hc a ha v hg hb
  simp only [gameRules, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- a node that wins outright
    rw [rWon] at ha
    cases ha
    rw [rWon] at hg
    exact .won (realize_wonG (A := A) 0 |>.mp hg)
  · -- an existential node with a winning successor
    rw [rEx] at ha
    cases ha
    rw [rEx, Formula.realize_inf, Formula.realize_not] at hg
    refine .ex (fun hu => hg.1 ((realize_univG (A := A) 0).mpr hu))
      ((realize_moveG (A := A) 0 1).mp hg.2) ?_
    exact hb (winAt 1) (by simp [rEx])
  · -- a universal node whose scan has reached the least element
    rw [rAll] at ha
    cases ha
    rw [rAll, Formula.realize_inf, Formula.realize_inf] at hg
    obtain ⟨⟨hu, hm⟩, hmin⟩ := hg
    have hall := hb (allgeAt 0 2) (by simp [rAll])
    refine .all ((realize_univG (A := A) 0).mp hu) ⟨v 1, (realize_moveG (A := A) 0 1).mp hm⟩ ?_
    intro b hbm
    exact hall b ((realize_minF (L := Language.andOrGraph) 2).mp hmin b) hbm
  · -- the scan starts at the greatest element, not a successor
    rw [rTopNo] at ha
    cases ha
    rw [rTopNo, Formula.realize_inf, Formula.realize_not] at hg
    obtain ⟨hmax, hno⟩ := hg
    intro c hle hmv
    have hce : c = v 1 :=
      le_antisymm ((realize_maxF (L := Language.andOrGraph) 1).mp hmax c) hle
    exact absurd (hce ▸ hmv) (fun h => hno ((realize_moveG (A := A) 0 1).mpr h))
  · -- the scan starts at the greatest element, a winning successor
    rw [rTopYes] at ha
    cases ha
    rw [rTopYes, Formula.realize_inf] at hg
    obtain ⟨hmax, _⟩ := hg
    have hw := hb (winAt 1) (by simp [rTopYes])
    intro c hle _
    have hce : c = v 1 :=
      le_antisymm ((realize_maxF (L := Language.andOrGraph) 1).mp hmax c) hle
    exact hce ▸ hw
  · -- the scan steps down past a node that is not a successor
    rw [rStepNo] at ha
    cases ha
    rw [rStepNo, Formula.realize_inf, Formula.realize_not] at hg
    obtain ⟨hsucc, hno⟩ := hg
    have hrest := hb (allgeAt 0 2) (by simp [rStepNo])
    obtain ⟨hlt, hgap⟩ := (realize_succF (L := Language.andOrGraph) 1 2).mp hsucc
    intro c hle hmv
    rcases eq_or_lt_of_le hle with rfl | hlt'
    · exact absurd hmv (fun h => hno ((realize_moveG (A := A) 0 1).mpr h))
    · exact hrest c (not_lt.mp fun h2 => hgap c ⟨hlt', h2⟩) hmv
  · -- the scan steps down past a winning successor
    rw [rStepYes] at ha
    cases ha
    rw [rStepYes, Formula.realize_inf] at hg
    obtain ⟨hsucc, _⟩ := hg
    have hw := hb (winAt 1) (by simp [rStepYes])
    have hrest := hb (allgeAt 0 2) (by simp [rStepYes])
    obtain ⟨hlt, hgap⟩ := (realize_succF (L := Language.andOrGraph) 1 2).mp hsucc
    intro c hle hmv
    rcases eq_or_lt_of_le hle with rfl | hlt'
    · exact hw
    · exact hrest c (not_lt.mp fun h2 => hgap c ⟨hlt', h2⟩) hmv

omit [Finite A] [Nonempty A] in
/-- **Soundness**: everything the rules derive about `win` is winning. -/
theorem winsOn_of_derives {t : Fin (gameBlock.arity GIx.win) → A}
    (h : Derives (A := A) gameRules ⟨GIx.win, t⟩) : WinsOn A (t 0) :=
  lfpAssign_least_of_closed gameAssign_closed h

/-! ### Completeness: every winning node is derived -/

omit [Language.andOrGraph.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- The arguments of `allge x y` read out of the three variables. -/
theorem allgeArgs₁ (x y w : A) :
    (fun j => (![x, y, w] : Fin 3 → A) ((allgeAt 0 1).args j)) = ![x, y] := by
  funext j
  fin_cases j <;> rfl

omit [Language.andOrGraph.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- The arguments of `allge x z` read out of the three variables. -/
theorem allgeArgs₂ (x y w : A) :
    (fun j => (![x, y, w] : Fin 3 → A) ((allgeAt 0 2).args j)) = ![x, w] := by
  funext j
  fin_cases j <;> rfl

omit [Nonempty A] in
/-- The scan is derivable at every element, by a downward induction along the
order: this is the universal body the third rule needs. -/
theorem derives_allge {x : A} (hw : ∀ b : A, AGMove x b → Derives (A := A) gameRules
      ⟨GIx.win, fun _ => b⟩) (y : A) :
    Derives (A := A) gameRules ⟨GIx.allge, ![x, y]⟩ := by
  classical
  induction y using order_induction_down with
  | hmax z hz =>
    rw [← allgeArgs₁ x z z]
    by_cases hmv : AGMove x z
    · refine Derives.rule (c := rTopYes) rTopYes_mem (a := allgeAt 0 1) rfl
        (v := ![x, z, z]) ?_ ?_
      · rw [rTopYes, Formula.realize_inf]
        exact ⟨(realize_maxF (L := Language.andOrGraph) 1).mpr hz,
          (realize_moveG (A := A) 0 1).mpr hmv⟩
      · intro b hbmem
        rw [rTopYes] at hbmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbmem
        subst hbmem
        exact hw z hmv
    · refine Derives.rule (c := rTopNo) rTopNo_mem (a := allgeAt 0 1) rfl
        (v := ![x, z, z]) ?_ ?_
      · rw [rTopNo, Formula.realize_inf, Formula.realize_not]
        exact ⟨(realize_maxF (L := Language.andOrGraph) 1).mpr hz,
          fun h => hmv (by first | assumption | simpa using (realize_moveG (A := A) 0 1).mp h)⟩
      · intro b hbmem
        rw [rTopNo] at hbmem
        simp at hbmem
  | hstep w z hwz hgap ih =>
    rw [← allgeArgs₁ x w z]
    by_cases hmv : AGMove x w
    · refine Derives.rule (c := rStepYes) rStepYes_mem (a := allgeAt 0 1) rfl
        (v := ![x, w, z]) ?_ ?_
      · rw [rStepYes, Formula.realize_inf]
        refine ⟨(realize_succF (L := Language.andOrGraph) 1 2).mpr ⟨hwz, ?_⟩,
          (realize_moveG (A := A) 0 1).mpr hmv⟩
        intro a ha
        exact hgap a ha
      · intro b hbmem
        rw [rStepYes] at hbmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbmem
        rcases hbmem with rfl | rfl
        · exact hw w hmv
        · rw [allgeArgs₂ x w z]
          exact ih
    · refine Derives.rule (c := rStepNo) rStepNo_mem (a := allgeAt 0 1) rfl
        (v := ![x, w, z]) ?_ ?_
      · rw [rStepNo, Formula.realize_inf, Formula.realize_not]
        refine ⟨(realize_succF (L := Language.andOrGraph) 1 2).mpr ⟨hwz, ?_⟩,
          fun h => hmv (by first | assumption | simpa using (realize_moveG (A := A) 0 1).mp h)⟩
        intro a ha
        exact hgap a ha
      · intro b hbmem
        rw [rStepNo] at hbmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbmem
        subst hbmem
        rw [allgeArgs₂ x w z]
        exact ih

/-- **Completeness**: every winning node is derived. -/
theorem derives_of_winsOn {x : A} (h : WinsOn A x) :
    Derives (A := A) gameRules ⟨GIx.win, fun _ => x⟩ := by
  classical
  induction h with
  | @won a hwon =>
    refine Derives.rule (c := rWon) rWon_mem (a := winAt 0) rfl (v := ![a, a, a])
      ?_ ?_
    · exact (realize_wonG (A := A) 0).mpr hwon
    · intro b hbmem
      rw [rWon] at hbmem
      simp at hbmem
  | @ex a b hu hmv _ ih =>
    refine Derives.rule (c := rEx) rEx_mem (a := winAt 0) rfl (v := ![a, b, b])
      ?_ ?_
    · rw [rEx, Formula.realize_inf, Formula.realize_not]
      exact ⟨fun hc => hu (by first | assumption | simpa using (realize_univG (A := A) 0).mp hc),
        (realize_moveG (A := A) 0 1).mpr hmv⟩
    · intro c hcmem
      rw [rEx] at hcmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcmem
      subst hcmem
      exact ih
  | @all a hu hex _ ih =>
    obtain ⟨b, hb⟩ := hex
    obtain ⟨m, hm⟩ := Finite.exists_min (id : A → A)
    refine Derives.rule (c := rAll) rAll_mem (a := winAt 0) rfl (v := ![a, b, m])
      ?_ ?_
    · rw [rAll, Formula.realize_inf, Formula.realize_inf]
      refine ⟨⟨(realize_univG (A := A) 0).mpr hu,
        (realize_moveG (A := A) 0 1).mpr hb⟩, ?_⟩
      exact (realize_minF (L := Language.andOrGraph) 2).mpr hm
    · intro c hcmem
      rw [rAll] at hcmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcmem
      subst hcmem
      have heq : (fun j => (![a, b, m] : Fin 3 → A) ((allgeAt 0 2).args j)) = ![a, m] := by
        funext j
        fin_cases j <;> rfl
      rw [heq]
      exact derives_allge (fun d hd => ih d hd) m

end Correct

/-- **Reading the output**: some marked start is in the fixed point. -/
theorem realize_gameOut {A : Type} [Language.andOrGraph.Structure A] [LinearOrder A]
    (ρ : gameBlock.Assignment A) :
    (@Sentence.Realize (agOrd.sum gameBlock.lang) A
        (@sumStructure _ _ A _ (gameBlock.structure ρ)) gameOut) ↔
      ∃ s : A, ρ GIx.win (fun _ => s) ∧ AGStart s := by
  letI := gameBlock.structure ρ
  rw [gameOut]
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_atomF, realize_guardOutF, realize_startG, Sum.elim_inr]
  constructor
  · rintro ⟨w, h1, h2⟩
    exact ⟨w 0, h1, h2⟩
  · rintro ⟨s, h1, h2⟩
    exact ⟨![s, s, s], h1, h2⟩

end Game

open Game in
/-- **GAME is FO(LFP) definable**: the winning set is the least fixed point of
the three clauses, the universal one carried by a scan of the order. -/
theorem game_lfpDefinable : LFPDefinable GAME := by
  refine ⟨⟨gameBlock, 3, gameRules, gameOut⟩, ?_⟩
  intro A _ _ _ _
  refine Iff.trans ?_ (realize_gameOut (lfpAssign gameRules)).symm
  constructor
  · rintro ⟨s, hs, hw⟩
    exact ⟨s, derives_of_winsOn hw, hs⟩
  · rintro ⟨s, hd, hs⟩
    exact ⟨s, hs, winsOn_of_derives hd⟩

/-- **GAME is in PTIME**, through the formalized translation of FO(LFP) into
the Horn fragment. -/
theorem game_mem_PTIME : GAME ∈ PTIME :=
  (lfpDefinable_iff_sigmaSOHornDefinable GAME).mp game_lfpDefinable

end DescriptiveComplexity
