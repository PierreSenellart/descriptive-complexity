/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderHorn
import DescriptiveComplexity.Problems.TwoSat.Implication
import DescriptiveComplexity.Problems.TwoSat.Membership

/-!
# 2SAT is in PTIME, by a Horn program for the implication graph

2SAT is SO-Horn definable (`DescriptiveComplexity.twoSat_sigmaSOHornDefinable`), hence in
`DescriptiveComplexity.PTIME`. This is what makes the inclusion `NL ⊆ PTIME` available:
the inclusion has no syntactic route, a Krom kernel not being a Horn kernel, so
it goes through the complete problem of the Krom fragment.

The program guesses the *reachability relation of the implication graph*
(`DescriptiveComplexity.TwoSatImpl`), as one binary relation variable per pair of
signs, and constrains it by Horn clauses:

* reflexivity, and transitivity `Reach s t x y ∧ Reach t r y z → Reach s r x z`;
* one clause per pair of signs whose guard recognizes a clause covered by the
  occurrences `(x, s)` and `(y, u)`, emitting the two implications
  `Reach (!s) u x y` and `Reach (!u) s y x` – the edges of the implication
  graph;
* the goal clauses: `Reach s (!s) x x ∧ Reach (!s) s x x → ⊥` (no variable
  reaches its own negation and back), plus the two guards that reject an empty
  clause and a violated width promise.

An assignment satisfies the program exactly when it contains reachability and
has no bad cycle, so correctness is the classical criterion
`DescriptiveComplexity.TwoSatImpl.satisfiable_of_no_bad_cycle` in one direction and
`DescriptiveComplexity.TwoSatImpl.no_bad_cycle_of_satisfiable` in the other.

Note the shape of the argument: the *acceptance* condition of 2SAT is negative
(“no bad cycle”), which a Horn program can state because a goal clause is
exactly a negative constraint on the guessed relation.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc TwoSatImpl

namespace TwoSatHorn

/-! ### The block and its atoms -/

/-- The block of the Horn program: one binary relation variable per pair of
signs, holding reachability in the implication graph. An `abbrev`, so that the
arity reduces when tuples are written as `![x, y]`. -/
abbrev reachBlock : SOBlock where
  ι := Bool × Bool
  arity := fun _ => 2

/-- The atom `Reach s t (v i) (v j)`. -/
def reachAtom (s t : Bool) (i j : Fin 4) : SOAtom reachBlock 4 where
  idx := (s, t)
  args := ![i, j]

section Semantics

variable {A : Type}

/-- Reachability as read off an assignment of the block. -/
def RVal (ρ : reachBlock.Assignment A) (s t : Bool) (x y : A) : Prop :=
  ρ (s, t) ![x, y]

theorem reachAtom_holds (ρ : reachBlock.Assignment A) (s t : Bool) (i j : Fin 4)
    (v : Fin 4 → A) : (reachAtom s t i j).Holds ρ v ↔ RVal ρ s t (v i) (v j) := by
  refine iff_of_eq (congrArg (ρ (s, t)) (funext fun m => ?_))
  fin_cases m <;> rfl

end Semantics

/-! ### The guards over four variables

The membership program of `DescriptiveComplexity.Problems.TwoSat.Membership` uses three
universally quantified variables (`c`, `x`, `y`); this program needs a fourth
one for transitivity, so its covering-pair guard is that formula relabelled. -/

/-- The injection of the three variables of the covering-pair guard into the
four variables of this program. -/
def var4 : Fin 3 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The covering-pair guard, over four variables. -/
noncomputable def pairGuard4 (s u : Bool) : satOrd.Formula (Fin 4) :=
  (TwoSatKrom.pairGuard s u).relabel var4

section Guards

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : Fin 4 → A}

/-- The covering-pair guard says exactly that the clause `v 0` is covered by
the occurrences `(v 1, s)` and `(v 2, u)`. -/
theorem realize_pairGuard4 {s u : Bool} :
    (pairGuard4 s u).Realize v ↔ Covers (v 0) (v 1) s (v 2) u := by
  rw [pairGuard4, Formula.realize_relabel, TwoSatKrom.realize_pairGuard, Covers]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.isCl, h1, h2, h3⟩

end Guards

/-! ### The program -/

/-- Reflexivity of reachability. -/
noncomputable def reflClause (s : Bool) : HornClause satOrd reachBlock 4 where
  guard := ⊤
  body := []
  head := some (reachAtom s s 1 1)

/-- The implication `¬ℓ(x, s) → ℓ(y, u)` of a clause covered by `(x, s)` and
`(y, u)`. -/
noncomputable def edgeClause₁ (s u : Bool) : HornClause satOrd reachBlock 4 where
  guard := pairGuard4 s u
  body := []
  head := some (reachAtom (!s) u 1 2)

/-- The implication `¬ℓ(y, u) → ℓ(x, s)` of the same clause. -/
noncomputable def edgeClause₂ (s u : Bool) : HornClause satOrd reachBlock 4 where
  guard := pairGuard4 s u
  body := []
  head := some (reachAtom (!u) s 2 1)

/-- Transitivity of reachability. -/
noncomputable def transClause (s t r : Bool) : HornClause satOrd reachBlock 4 where
  guard := ⊤
  body := [reachAtom s t 1 2, reachAtom t r 2 3]
  head := some (reachAtom s r 1 3)

/-- The goal clause forbidding a bad cycle: a variable reaching its own
negation and back. -/
noncomputable def cycleClause (s : Bool) : HornClause satOrd reachBlock 4 where
  guard := ⊤
  body := [reachAtom s (!s) 1 1, reachAtom (!s) s 1 1]
  head := none

/-- The goal clause rejecting an empty clause. -/
noncomputable def emptyGoal : HornClause satOrd reachBlock 4 where
  guard := emptyClF 0
  body := []
  head := none

/-- The goal clause rejecting a violated width promise. -/
noncomputable def wideGoal : HornClause satOrd reachBlock 4 where
  guard := wideTwoOrdF
  body := []
  head := none

/-- The Horn program defining 2SAT: reachability in the implication graph,
constrained to have no bad cycle. The sign combinations are spelled out, so
that membership of a clause is decided by `simp`. -/
noncomputable def twoSatHornProgram : HornProgram satOrd reachBlock 4 :=
  [reflClause true, reflClause false,
    edgeClause₁ true true, edgeClause₁ true false,
    edgeClause₁ false true, edgeClause₁ false false,
    edgeClause₂ true true, edgeClause₂ true false,
    edgeClause₂ false true, edgeClause₂ false false,
    transClause true true true, transClause true true false,
    transClause true false true, transClause true false false,
    transClause false true true, transClause false true false,
    transClause false false true, transClause false false false,
    cycleClause true, cycleClause false,
    emptyGoal, wideGoal]

theorem reflClause_mem (s : Bool) : reflClause s ∈ twoSatHornProgram := by
  cases s <;> simp [twoSatHornProgram]

theorem edgeClause₁_mem (s u : Bool) : edgeClause₁ s u ∈ twoSatHornProgram := by
  cases s <;> cases u <;> simp [twoSatHornProgram]

theorem edgeClause₂_mem (s u : Bool) : edgeClause₂ s u ∈ twoSatHornProgram := by
  cases s <;> cases u <;> simp [twoSatHornProgram]

theorem transClause_mem (s t r : Bool) : transClause s t r ∈ twoSatHornProgram := by
  cases s <;> cases t <;> cases r <;> simp [twoSatHornProgram]

theorem cycleClause_mem (s : Bool) : cycleClause s ∈ twoSatHornProgram := by
  cases s <;> simp [twoSatHornProgram]

theorem emptyGoal_mem : emptyGoal ∈ twoSatHornProgram := by
  simp [twoSatHornProgram]

theorem wideGoal_mem : wideGoal ∈ twoSatHornProgram := by
  simp [twoSatHornProgram]

/-! ### A yes-instance satisfies the program -/

section Soundness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The assignment induced by the actual reachability relation. -/
def reachAssign : reachBlock.Assignment A :=
  fun i w => Reach ((w 0, i.1) : A × Bool) (w 1, i.2)

omit [LinearOrder A] in
theorem rVal_reachAssign (s t : Bool) (x y : A) :
    RVal (reachAssign (A := A)) s t x y ↔ Reach ((x, s) : A × Bool) (y, t) :=
  Iff.rfl

variable (hsat : Satisfiable A) (hw : WidthAtMostTwo A)

theorem reflClause_holds (s : Bool) (v : Fin 4 → A) :
    (reflClause s).Holds (reachAssign (A := A)) v := by
  intro _
  rw [HornClause.HeadHolds, reflClause]
  exact (reachAtom_holds _ _ _ _ _ v).mpr ((rVal_reachAssign _ _ _ _).mpr
    Relation.ReflTransGen.refl)

theorem edgeClause₁_holds (s u : Bool) (v : Fin 4 → A) :
    (edgeClause₁ s u).Holds (reachAssign (A := A)) v := by
  intro hbody
  rw [HornClause.HeadHolds, edgeClause₁]
  refine (reachAtom_holds _ _ _ _ _ v).mpr ((rVal_reachAssign _ _ _ _).mpr
    (Relation.ReflTransGen.single ?_))
  exact ⟨v 0, v 1, s, v 2, u, realize_pairGuard4.mp hbody.1, Or.inl ⟨rfl, rfl⟩⟩

theorem edgeClause₂_holds (s u : Bool) (v : Fin 4 → A) :
    (edgeClause₂ s u).Holds (reachAssign (A := A)) v := by
  intro hbody
  rw [HornClause.HeadHolds, edgeClause₂]
  refine (reachAtom_holds _ _ _ _ _ v).mpr ((rVal_reachAssign _ _ _ _).mpr
    (Relation.ReflTransGen.single ?_))
  exact ⟨v 0, v 1, s, v 2, u, realize_pairGuard4.mp hbody.1, Or.inr ⟨rfl, rfl⟩⟩

theorem transClause_holds (s t r : Bool) (v : Fin 4 → A) :
    (transClause s t r).Holds (reachAssign (A := A)) v := by
  intro hbody
  rw [HornClause.HeadHolds, transClause]
  have h1 := (rVal_reachAssign s t (v 1) (v 2)).mp
    ((reachAtom_holds (reachAssign (A := A)) s t 1 2 v).mp
      (hbody.2 _ (by simp [transClause])))
  have h2 := (rVal_reachAssign t r (v 2) (v 3)).mp
    ((reachAtom_holds (reachAssign (A := A)) t r 2 3 v).mp
      (hbody.2 _ (by simp [transClause])))
  exact (reachAtom_holds _ _ _ _ _ v).mpr ((rVal_reachAssign _ _ _ _).mpr (h1.trans h2))

include hsat in
theorem cycleClause_holds (s : Bool) (v : Fin 4 → A) :
    (cycleClause s).Holds (reachAssign (A := A)) v := by
  intro hbody
  have h1 := (rVal_reachAssign s (!s) (v 1) (v 1)).mp
    ((reachAtom_holds (reachAssign (A := A)) s (!s) 1 1 v).mp
      (hbody.2 _ (by simp [cycleClause])))
  have h2 := (rVal_reachAssign (!s) s (v 1) (v 1)).mp
    ((reachAtom_holds (reachAssign (A := A)) (!s) s 1 1 v).mp
      (hbody.2 _ (by simp [cycleClause])))
  exact absurd ⟨h1, h2⟩ (no_bad_cycle_of_satisfiable hsat (v 1) s)

include hsat in
theorem emptyGoal_holds (v : Fin 4 → A) : emptyGoal.Holds (reachAssign (A := A)) v := by
  intro hbody
  obtain ⟨ν, hν⟩ := hsat
  have hempty : EmptyCl (v 0) := realize_emptyClF.mp hbody.1
  obtain ⟨z, hz⟩ := hν (v 0) hempty.1
  rcases hz with ⟨hp, -⟩ | ⟨hn, -⟩
  · exact absurd ⟨hempty.1, hp⟩ (hempty.2 z true)
  · exact absurd ⟨hempty.1, hn⟩ (hempty.2 z false)

include hw in
theorem wideGoal_holds (v : Fin 4 → A) : wideGoal.Holds (reachAssign (A := A)) v := by
  intro hbody
  exact absurd hw (wideTwo_iff_not_widthAtMostTwo.mp (realize_wideTwoOrdF.mp hbody.1))

include hsat hw in
/-- **A yes-instance satisfies the program**: the reachability relation itself
is a satisfying assignment. -/
theorem holds_reachAssign : twoSatHornProgram.Holds (reachAssign (A := A)) := by
  intro v c hc
  simp only [twoSatHornProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
      | exact reflClause_holds _ v
      | exact edgeClause₁_holds _ _ v
      | exact edgeClause₂_holds _ _ v
      | exact transClause_holds _ _ _ v
      | exact cycleClause_holds hsat _ v
      | exact emptyGoal_holds hsat v
      | exact wideGoal_holds hw v

end Soundness

/-! ### A satisfying assignment describes a yes-instance -/

section Completeness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {ρ : reachBlock.Assignment A} (hρ : twoSatHornProgram.Holds ρ)

omit [Finite A] [Nonempty A] in
include hρ in
/-- **A satisfying assignment contains reachability**: it is closed under the
reflexivity, edge and transitivity clauses. -/
theorem rVal_of_reach {p q : A × Bool} (h : Reach p q) : RVal ρ p.2 q.2 p.1 q.1 := by
  induction h with
  | refl =>
    have hcl := hρ ![p.1, p.1, p.1, p.1] (reflClause p.2) (reflClause_mem p.2)
      ⟨by simp [reflClause], by simp [reflClause]⟩
    rw [HornClause.HeadHolds, reflClause] at hcl
    simpa [reachAtom_holds] using hcl
  | @tail b c _ hbc ih =>
    -- the single step `b → c`, from the clause it comes from
    obtain ⟨cl, x, s, y, u, hcov, hstep⟩ := hbc
    have hedge : RVal ρ b.2 c.2 b.1 c.1 := by
      rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hcl := hρ ![cl, x, y, x] (edgeClause₁ s u) (edgeClause₁_mem s u)
          ⟨by simpa [edgeClause₁, realize_pairGuard4] using hcov, by simp [edgeClause₁]⟩
        rw [HornClause.HeadHolds, edgeClause₁] at hcl
        simpa [reachAtom_holds] using hcl
      · have hcl := hρ ![cl, x, y, x] (edgeClause₂ s u) (edgeClause₂_mem s u)
          ⟨by simpa [edgeClause₂, realize_pairGuard4] using hcov, by simp [edgeClause₂]⟩
        rw [HornClause.HeadHolds, edgeClause₂] at hcl
        simpa [reachAtom_holds] using hcl
    -- and transitivity
    have hcl := hρ ![p.1, p.1, b.1, c.1] (transClause p.2 b.2 c.2)
      (transClause_mem p.2 b.2 c.2) ⟨by simp [transClause], ?_⟩
    · rw [HornClause.HeadHolds, transClause] at hcl
      simpa [reachAtom_holds] using hcl
    · intro a ha
      simp only [transClause, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · simpa [reachAtom_holds] using ih
      · simpa [reachAtom_holds] using hedge

include hρ in
/-- **A satisfying assignment makes the instance a yes-instance.** -/
theorem twoSatisfiable_of_holds : TwoSatisfiable A := by
  -- the width promise
  have hw : WidthAtMostTwo A := by
    by_contra hnw
    have hwide := (wideTwo_iff_not_widthAtMostTwo (A := A)).mpr hnw
    have hcl := hρ (fun _ => Classical.arbitrary A) wideGoal wideGoal_mem
      ⟨by simpa [wideGoal] using hwide, by simp [wideGoal]⟩
    rw [HornClause.HeadHolds, wideGoal] at hcl
    exact hcl.elim
  -- no empty clause
  have hempty : ∀ c : A, ¬EmptyCl c := by
    intro c hc
    have hcl := hρ ![c, c, c, c] emptyGoal emptyGoal_mem
      ⟨by simpa [emptyGoal] using hc, by simp [emptyGoal]⟩
    rw [HornClause.HeadHolds, emptyGoal] at hcl
    exact hcl.elim
  -- no bad cycle, since reachability is contained in the assignment
  have hcyc : ∀ (x : A) (s : Bool),
      ¬(Reach ((x, s) : A × Bool) (x, !s) ∧ Reach ((x, !s) : A × Bool) (x, s)) := by
    rintro x s ⟨h1, h2⟩
    have hr1 := rVal_of_reach hρ h1
    have hr2 := rVal_of_reach hρ h2
    have hcl := hρ ![x, x, x, x] (cycleClause s) (cycleClause_mem s)
      ⟨by simp [cycleClause], ?_⟩
    · rw [HornClause.HeadHolds, cycleClause] at hcl
      exact hcl.elim
    · intro a ha
      simp only [cycleClause, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · simpa [reachAtom_holds] using hr1
      · simpa [reachAtom_holds] using hr2
  exact ⟨hw, satisfiable_of_no_bad_cycle hw hempty hcyc⟩

end Completeness

/-- **Correctness of the program**: it is satisfiable exactly on the
yes-instances of 2SAT. -/
theorem twoSatisfiable_iff_exists_holds {A : Type} [Language.sat.Structure A] [LinearOrder A]
    [Finite A] [Nonempty A] :
    TwoSatisfiable A ↔ ∃ ρ : reachBlock.Assignment A, twoSatHornProgram.Holds ρ :=
  ⟨fun h => ⟨reachAssign, holds_reachAssign h.2 h.1⟩,
    fun ⟨_, hρ⟩ => twoSatisfiable_of_holds hρ⟩

end TwoSatHorn

open TwoSatHorn in
/-- **2SAT is SO-Horn definable**: guess the reachability relation of the
implication graph, constrain it by reflexivity, the clause edges and
transitivity, and reject the instances where a variable reaches its own
negation and back. Since PTIME is *defined* as SO-Horn definability, this is
the statement `TwoSAT ∈ PTIME`. -/
theorem twoSat_sigmaSOHornDefinable : SigmaSOHornDefinable TwoSAT :=
  ⟨reachBlock, 4, twoSatHornProgram, fun _A _ _ _ _ => twoSatisfiable_iff_exists_holds⟩

/-- **2SAT is in PTIME.** -/
theorem twoSat_mem_PTIME : TwoSAT ∈ PTIME :=
  twoSat_sigmaSOHornDefinable

end DescriptiveComplexity
