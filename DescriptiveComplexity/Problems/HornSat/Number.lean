/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.HornSat.Unsat
import DescriptiveComplexity.FixedPointOrderTransfer
import DescriptiveComplexity.Counting
import DescriptiveComplexity.Vocabulary
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The number written by unit propagation: definition

The function counterpart of HORN-SAT (`DescriptiveComplexity.HORNSAT`): some
variables of a Horn formula are marked as *outputs* and compared by
significance, and the problem is to compute the number whose binary digits say
which of them unit propagation forces to be true
(`DescriptiveComplexity.Forced`), i.e., which are true in the least model.

* The vocabulary is the one of CNF instances (`FirstOrder.Language.sat`) with
  two more symbols (`FirstOrder.Language.digitOrder`): `out` marks the output
  variables and `below` compares them.
* `DescriptiveComplexity.hornNumber`: a forced output variable contributes
  `2 ^ r`, where `r` is the number of output variables strictly below it, when
  `below` linearly orders the output variables
  (`DescriptiveComplexity.VarOrder`). An instance that is not a satisfiable
  Horn formula, or whose `below` is not such an order, writes `0`.

This is the problem through which the number written by a machine
(`DescriptiveComplexity.DTMNumber`) is shown hard for FP: the least fixed
point of a system of rules is the least model of a Horn formula, and the
unit-propagation machine leaves that model on its tape.
-/

namespace FirstOrder

namespace Language

/-- The symbols reading a number off a set of marked elements. -/
fo_language digitOrder with dgo where
  /-- `out x`: the element `x` holds one digit. -/
  out : 1
  /-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
  below : 2

/-- The relational language of Horn formulas writing a number. -/
abbrev satOut : Language.{0, 0} := Language.sat.sum Language.digitOrder

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- “Is an output variable”. -/
abbrev hnOut : Language.satOut.Relations 1 := Sum.inr dgoOut

/-- The comparison of the output variables. -/
abbrev hnBelow : Language.satOut.Relations 2 := Sum.inr dgoBelow

/-- A Horn formula writing a number is a CNF instance. -/
instance satOutStructure (A : Type) [Language.satOut.Structure A] :
    Language.sat.Structure A :=
  (LHom.sumInl : Language.sat →ᴸ Language.satOut).reduct A

/-! ### The propagation closure is isomorphism-invariant -/

section ForcedIso

variable {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]

theorem forcedIn_map (e : A ≃[Language.sat] B) :
    ∀ (n : ℕ) (x : A), ForcedIn n x → ForcedIn n (e x) := by
  intro n
  induction n with
  | zero => exact fun _ h => h.elim
  | succ n ih =>
    rintro x ⟨c, hc, hp, hneg⟩
    refine ⟨e c, (relMap_equiv₁ e satIsClause c).mp hc, (relMap_equiv₂ e satPosIn c x).mp hp,
      fun y hy => ?_⟩
    have hy' : RelMap satNegIn ![c, e.symm y] := by
      refine (relMap_equiv₂ e satNegIn c (e.symm y)).mpr ?_
      rwa [show (e (e.symm y) : B) = y from e.toEquiv.apply_symm_apply y]
    have := ih (e.symm y) (hneg _ hy')
    rwa [show (e (e.symm y) : B) = y from e.toEquiv.apply_symm_apply y] at this

theorem forced_equiv (e : A ≃[Language.sat] B) (x : A) : Forced (e x) ↔ Forced x := by
  constructor
  · rintro ⟨n, hn⟩
    have := forcedIn_map e.symm n (e x) hn
    rw [show (e.symm (e x) : A) = x from e.toEquiv.symm_apply_apply x] at this
    exact ⟨n, this⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, forcedIn_map e n x hn⟩

end ForcedIso

/-! ### The number -/

section Semantics

variable {A : Type} [Language.satOut.Structure A]

/-- The output variable `x` is forced. -/
def ForcedDigit (x : A) : Prop :=
  RelMap hnOut ![x] ∧ Forced x

/-- `y` is an output variable strictly below `x`. -/
def LowerVar (x y : A) : Prop :=
  RelMap hnOut ![y] ∧ y ≠ x ∧ RelMap hnBelow ![y, x]

/-- The rank of a variable among the outputs: the number of output variables
strictly below it. -/
noncomputable def varRank (x : A) : ℕ :=
  Nat.card {y : A // LowerVar x y}

variable (A) in
/-- **The comparison of the outputs is a linear order on them**: reflexive,
transitive, antisymmetric and total among the output variables. -/
def VarOrder : Prop :=
  (∀ p : A, RelMap hnOut ![p] → RelMap hnBelow ![p, p]) ∧
    (∀ p q r : A, RelMap hnOut ![p] → RelMap hnOut ![q] → RelMap hnOut ![r] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, r] → RelMap hnBelow ![p, r]) ∧
    (∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, p] → p = q) ∧
    ∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] ∨ RelMap hnBelow ![q, p]

variable (A) in
open Classical in
/-- **The number written by unit propagation**: each forced output variable
contributes two to the power of its rank among the outputs. Instances that are
not satisfiable Horn formulas, or whose outputs are not linearly ordered,
write `0`. -/
noncomputable def hornNumber : ℕ :=
  if HornSatisfiable A ∧ VarOrder A then ∑ᶠ x : A, if ForcedDigit x then 2 ^ varRank x else 0
  else 0

end Semantics

section Iso

variable {A B : Type} [Language.satOut.Structure A] [Language.satOut.Structure B]

theorem forcedDigit_equiv (e : A ≃[Language.satOut] B) (x : A) :
    ForcedDigit (e x) ↔ ForcedDigit x :=
  and_congr (relMap_equiv₁ e hnOut x).symm (forced_equiv (reductSumInlEquiv e) x)

theorem lowerVar_equiv (e : A ≃[Language.satOut] B) (x y : A) :
    LowerVar (e x) (e y) ↔ LowerVar x y :=
  and_congr (relMap_equiv₁ e hnOut y).symm
    (and_congr e.toEquiv.injective.ne_iff (relMap_equiv₂ e hnBelow y x).symm)

theorem varRank_equiv (e : A ≃[Language.satOut] B) (x : A) : varRank (e x) = varRank x :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv fun y => (lowerVar_equiv e x y).symm)).symm

theorem varOrder_equiv (e : A ≃[Language.satOut] B) : VarOrder A ↔ VarOrder B := by
  have h1 : ∀ p, (RelMap hnOut ![e p] : Prop) ↔ RelMap hnOut ![p] :=
    fun p => (relMap_equiv₁ e hnOut p).symm
  have h2 : ∀ p q, (RelMap hnBelow ![e p, e q] : Prop) ↔ RelMap hnBelow ![p, q] :=
    fun p q => (relMap_equiv₂ e hnBelow p q).symm
  constructor
  · rintro ⟨hr, ht, ha, hl⟩
    refine ⟨fun p hp => ?_, fun p q r hp hq hr' hpq hqr => ?_, fun p q hp hq hpq hqp => ?_,
      fun p q hp hq => ?_⟩
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      exact (h2 p p).mpr (hr p ((h1 p).mp hp))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      obtain ⟨r, rfl⟩ := e.toEquiv.surjective r
      exact (h2 p r).mpr (ht p q r ((h1 p).mp hp) ((h1 q).mp hq) ((h1 r).mp hr')
        ((h2 p q).mp hpq) ((h2 q r).mp hqr))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      exact congrArg e (ha p q ((h1 p).mp hp) ((h1 q).mp hq) ((h2 p q).mp hpq) ((h2 q p).mp hqp))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      exact (hl p q ((h1 p).mp hp) ((h1 q).mp hq)).imp (h2 p q).mpr (h2 q p).mpr
  · rintro ⟨hr, ht, ha, hl⟩
    exact ⟨fun p hp => (h2 p p).mp (hr _ ((h1 p).mpr hp)),
      fun p q r hp hq hr' hpq hqr => (h2 p r).mp (ht _ _ _ ((h1 p).mpr hp) ((h1 q).mpr hq)
        ((h1 r).mpr hr') ((h2 p q).mpr hpq) ((h2 q r).mpr hqr)),
      fun p q hp hq hpq hqp => e.toEquiv.injective
        (ha _ _ ((h1 p).mpr hp) ((h1 q).mpr hq) ((h2 p q).mpr hpq) ((h2 q p).mpr hqp)),
      fun p q hp hq => (hl _ _ ((h1 p).mpr hp) ((h1 q).mpr hq)).imp (h2 p q).mp (h2 q p).mp⟩

/-- The number written is isomorphism-invariant. -/
theorem hornNumber_iso (e : A ≃[Language.satOut] B) : hornNumber A = hornNumber B := by
  classical
  have hsum : (∑ᶠ x : A, if ForcedDigit x then 2 ^ varRank x else 0) =
      ∑ᶠ x : B, if ForcedDigit x then 2 ^ varRank x else 0 := by
    rw [← finsum_comp_equiv e.toEquiv]
    refine finsum_congr fun x => ?_
    change _ = if ForcedDigit (e x) then 2 ^ varRank (e x) else 0
    rw [varRank_equiv e x, if_congr (forcedDigit_equiv e x) rfl rfl]
  rw [hornNumber, hornNumber, hsum]
  exact if_congr (and_congr (hornSatisfiable_iso (reductSumInlEquiv e)) (varOrder_equiv e)) rfl rfl

end Iso

/-- **The number written by unit propagation**, as a counting problem on
`Language.satOut`-structures: the function counterpart of
`DescriptiveComplexity.HORNSAT`. -/
noncomputable def HornNumber : CountingProblem Language.satOut where
  Count := fun A inst => @hornNumber A inst
  iso_invariant := fun e => hornNumber_iso e

end DescriptiveComplexity
