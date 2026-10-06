import Lax859101.OneCallClosure
import Lax859101.SubtractiveClosure
import Lax859101.DnfValues
import Lax859101.NaeSatValues
import Lax859101.RestrictedSatValues
import Lax859101.AllSetsValues
import Lax859101.BipartiteValues
import Lax859101.DnfComplete
import Lax859101.NaeSatComplete
import Lax859101.ColoringComplete
import Lax859101.AllSetsComplete
import Lax859101.RestrictedSatComplete
import Lax859101.BipartiteComplete
import Lax366625.SharpSatValue
import Lax366625.SharpSatComplete
import Lax280166.CliquesValues
import Lax280166.CountingCliques
import Lax280166.IndependentSetComplete
import Lax859101Proofs.DescriptiveComplexity.Composition
import Lax859101Proofs.DescriptiveComplexity.Counting
import Lax859101Proofs.DescriptiveComplexity.Counting.Reduction
import Lax859101Proofs.DescriptiveComplexity.Counting.Relativized
import Lax859101Proofs.DescriptiveComplexity.Counting.Subtractive
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingAll
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingBipartite
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingReductions
import Lax859101Proofs.DescriptiveComplexity.Problems.NaeSatCounting
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.Counting
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.CountingDnf
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.CountingDnfSubtractive
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.CountingRestricted
import Lax859101Proofs.DescriptiveComplexity.Problems.ThreeColorability.CountDraw
import Lax859101Proofs.DescriptiveComplexity.Problems.ThreeColorability.Counting
import Lax859101Proofs.DescriptiveComplexity.Relativized

/-!
# One-call and subtractive reductions, from the library's theorems

The reductions and the counting predicates are restated by the concepts; the
counting problems are bundled from the numbers they count, and agree with the
library's through the invariance of these numbers. Each completeness theorem
takes its membership from the library and its hardness from the problem it is
reduced from, so that the proofs follow the library's tree of reductions,
rooted at #SAT and #Independent Set.
-/

namespace Lax859101Proofs.Bridge

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- For an invariant number, the problem it gives takes that number. -/
theorem ofFun_eq {L : Language.{0, 0}} [L.IsRelational] {f : ∀ (A : Type) [L.Structure A], ℕ}
    (hf : ∀ {A B : Type} [L.Structure A] [L.Structure B], (A ≃[L] B) → f A = f B)
    (A : Type) [L.Structure A] : CountingProblem.ofFun f A = f A := by
  show sInf _ = _
  have hs : {n : ℕ | ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @f B i = n} =
      {f A} := by
    ext n
    constructor
    · rintro ⟨B, i, g, rfl⟩
      exact hf g
    · intro h
      exact ⟨A, inferInstance, Language.Equiv.refl _ _, h.symm⟩
  rw [hs, csInf_singleton]

/-- A count restricted by a condition is the count of the solutions with the
condition. -/
theorem ite_card {p q : Prop} {_ : Decidable p} (hpq : p ↔ q) {α : Type} (Q : α → Prop) :
    (if p then Nat.card {x // Q x} else 0) = Nat.card {x // q ∧ Q x} := by
  by_cases h : p
  · rw [if_pos h]
    exact Nat.card_congr ⟨fun x => ⟨x.1, hpq.mp h, x.2⟩, fun x => ⟨x.1, x.2.2⟩, fun _ =>
        rfl, fun _ => rfl⟩
  · rw [if_neg h]
    have : IsEmpty {x // q ∧ Q x} := ⟨fun x => h (hpq.mpr x.2.1)⟩
    exact Nat.card_of_isEmpty.symm

/-- The identity reduction between two problems with the same values. -/
noncomputable def idRed {L : Language.{0, 0}} [L.IsRelational] {C D : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = D A) : RelOrderedParsimoniousReduction C
        D :=
  DescriptiveComplexity.RelOrderedParsimoniousReduction.congrTarget h
    (DescriptiveComplexity.OrderedParsimoniousReduction.toRel
      (DescriptiveComplexity.ParsimoniousReduction.toOrdered
          (DescriptiveComplexity.ParsimoniousReduction.refl C)))

/-- One-call completeness for the library's #P, transported to the concepts
along an agreement of the problems. -/
theorem oneCallComplete_of_lib {L : Language.{0, 0}} [L.IsRelational] {C C' : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A], C A = C' A)
        (hc : DescriptiveComplexity.SharpP.OneCallComplete C) :
    OneCallComplete SharpP C' :=
  let ⟨⟨L'', i, D, hD, ⟨f⟩⟩, hh⟩ := hc
  ⟨⟨L'', i, D, hD, ⟨DescriptiveComplexity.OneCallReduction.congrSource (fun A _ _ => h A) f⟩⟩,
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ => h A).mp hh⟩

/-- The library's #SAT and the one of the required submission have the same
values. -/
theorem sharpSat_agree (A : Type) [sat.Structure A] :
    DescriptiveComplexity.SharpSAT A = SharpSAT A :=
  (Lax366625.SharpSatValue.sharpSat_eq A).symm

/-- The library's #Independent Set and the one of the required submission have
the same values. -/
theorem sharpIndependentSet_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    DescriptiveComplexity.SharpIndependentSet A = Lax280166.CountingCliques.SharpIndependentSet A :=
  (Lax280166.CliquesValues.sharpIndependentSet_eq A).symm

/-- The library's #2SAT is the number of models of the instances in the
class. -/
theorem sharpTwoSat_lib (A : Type) [sat.Structure A] :
    DescriptiveComplexity.SharpTwoSAT A = Nat.card
        {ν : A → Prop // WidthAtMostTwo A ∧ SatModel A ν} := by
  exact ite_card (DescriptiveComplexity.realize_widthTwoS) _

/-- The library's #HORN-SAT is the number of models of the instances in the
class. -/
theorem sharpHornSat_lib (A : Type) [sat.Structure A] :
    DescriptiveComplexity.SharpHornSAT A = Nat.card
        {ν : A → Prop // AtMostOnePositive A ∧ SatModel A ν} := by
  exact ite_card (DescriptiveComplexity.realize_hornS) _

/-- The library's #Monotone-2SAT is the number of models of the instances in the
class. -/
theorem sharpMonotoneTwoSat_lib (A : Type) [sat.Structure A] :
    DescriptiveComplexity.SharpMonotoneTwoSAT A = Nat.card {ν : A → Prop //
        (WidthAtMostTwo A ∧ NoNegative A) ∧ SatModel A ν} := by
  exact ite_card (Formula.realize_inf.trans
      (and_congr DescriptiveComplexity.realize_widthTwoS DescriptiveComplexity.realize_monotoneS)) _

/--
---
conclusion: Lax859101.OneCallClosure.oneCall_trans
---
The library's composition.
-/
theorem oneCall_trans {L L' L'' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    [L''.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'} {E : CountingProblem L''}
    (hf : Nonempty (OneCallReduction C D)) (hg : Nonempty (OneCallReduction D E)) : Nonempty
        (OneCallReduction C E) :=
  ⟨DescriptiveComplexity.OneCallReduction.trans hf.some hg.some⟩

/--
---
conclusion: Lax859101.OneCallClosure.oneCall_of_relOrderedParsimonious
---
The library's conversion.
-/
theorem oneCall_of_relOrderedParsimonious
    {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'}
    (hf : Nonempty (RelOrderedParsimoniousReduction C D)) : Nonempty (OneCallReduction C D) :=
  hf.map DescriptiveComplexity.RelOrderedParsimoniousReduction.toOneCall

/--
---
conclusion: Lax859101.OneCallClosure.oneCallMem_of_mem
---
The identity reduction, with the oracle as its term.
-/
theorem oneCallMem_of_mem (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    {C : CountingProblem L} (h : K.Mem C) :
    OneCallMem K C :=
  ⟨L, inferInstance, C, h, ⟨DescriptiveComplexity.ParsimoniousReduction.toOneCall
      (DescriptiveComplexity.ParsimoniousReduction.refl C)⟩⟩

/--
---
conclusion: Lax859101.OneCallClosure.oneCallMem_of_oneCall
---
The two reductions compose.
-/
theorem oneCallMem_of_oneCall (K : CountingClass)
    {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'}
    (hf : Nonempty (OneCallReduction C D)) (hD : OneCallMem K D) : OneCallMem K C :=
  let ⟨L'', _, E, hE, ⟨g⟩⟩ := hD
  ⟨L'', inferInstance, E, hE, ⟨DescriptiveComplexity.OneCallReduction.trans hf.some g⟩⟩

/--
---
conclusion: Lax859101.OneCallClosure.oneCallHard_of_oneCall
---
The two reductions compose.
-/
theorem oneCallHard_of_oneCall (K : CountingClass)
    {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'}
    (hf : Nonempty (OneCallReduction C D)) (hC : OneCallHard K C) : OneCallHard K D :=
  fun E hE => ⟨DescriptiveComplexity.OneCallReduction.trans (hC E hE).some hf.some⟩

/--
---
conclusion: Lax859101.OneCallClosure.oneCallHard_iff
---
The reduction to a member, composed with the one from the member.
-/
theorem oneCallHard_iff (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    {C : CountingProblem L} :
    OneCallHard K C ↔ ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
      OneCallMem K D → Nonempty (OneCallReduction D C) :=
  ⟨fun hC _ _ _ ⟨_, _, E, hE, ⟨g⟩⟩ => ⟨DescriptiveComplexity.OneCallReduction.trans g
      (hC E hE).some⟩,
    fun h _ _ D hD => h D ⟨_, inferInstance, D, hD,
      ⟨DescriptiveComplexity.ParsimoniousReduction.toOneCall
          (DescriptiveComplexity.ParsimoniousReduction.refl D)⟩⟩⟩

/--
---
conclusion: Lax859101.OneCallClosure.oneCallComplete_sharpP_of_parsimoniousComplete
---
Membership is the identity reduction; a parsimonious reduction is a one-call
reduction.
-/
theorem oneCallComplete_sharpP_of_parsimoniousComplete {L : Language.{0, 0}} [L.IsRelational]
    {C : CountingProblem L} (h : SharpP.ParsimoniousComplete C) :
    OneCallComplete SharpP C :=
  ⟨⟨_, inferInstance, C, h.1, ⟨DescriptiveComplexity.ParsimoniousReduction.toOneCall
      (DescriptiveComplexity.ParsimoniousReduction.refl C)⟩⟩,
    fun D hD => (h.2 D hD).map DescriptiveComplexity.RelOrderedParsimoniousReduction.toOneCall⟩

/--
---
conclusion: Lax859101.SubtractiveClosure.subtractive_trans
---
The library's theorem.
-/
theorem subtractive_trans {L L' L'' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    [L''.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'} {E : CountingProblem L''}
    (h₁ : SubtractiveReducible C D) (h₂ : SubtractiveReducible D E) : SubtractiveReducible C E :=
  DescriptiveComplexity.SubtractiveReducible.trans h₁ h₂

/--
---
conclusion: Lax859101.SubtractiveClosure.subtractive_of_relOrderedParsimonious
---
The library's theorem.
-/
theorem subtractive_of_relOrderedParsimonious
    {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'}
    (hf : Nonempty (RelOrderedParsimoniousReduction C D)) : SubtractiveReducible C D :=
  DescriptiveComplexity.RelOrderedParsimoniousReduction.subtractiveReducible hf.some

/--
---
conclusion: Lax859101.SubtractiveClosure.subtractive_of_strongSubtractive
---
The library's theorem.
-/
theorem subtractive_of_strongSubtractive {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'}
    (hf : Nonempty (StrongSubtractiveReduction C D)) : SubtractiveReducible C D :=
  DescriptiveComplexity.StrongSubtractiveReduction.subtractiveReducible hf.some

/--
---
conclusion: Lax859101.SubtractiveClosure.sharpP_mem_of_subtractive
---
The library's theorem.
-/
theorem sharpP_mem_of_subtractive {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'}
    (h : SubtractiveReducible C D) (hD : SharpP.Mem D) : SharpP.Mem C :=
  DescriptiveComplexity.mem_sharpP_of_subtractive h hD

/--
---
conclusion: Lax859101.SubtractiveClosure.subtractiveHard_of_subtractive
---
The chains concatenate.
-/
theorem subtractiveHard_of_subtractive (K : CountingClass)
    {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'}
    (h : SubtractiveReducible C D) (hC : SubtractiveHard K C) : SubtractiveHard K D :=
  fun E hE => DescriptiveComplexity.SubtractiveReducible.trans (hC E hE) h

/--
---
conclusion: Lax859101.SubtractiveClosure.subtractiveComplete_sharpP_of_parsimoniousComplete
---
The library's theorem.
-/
theorem subtractiveComplete_sharpP_of_parsimoniousComplete {L : Language.{0, 0}} [L.IsRelational]
    {C : CountingProblem L} (h : SharpP.ParsimoniousComplete C) :
    SubtractiveComplete SharpP C :=
  DescriptiveComplexity.complete_sharpP_of_parsimoniousComplete h

/--
---
conclusion: Lax859101.DnfValues.sharpDnf_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpDnf_count_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) : Nat.card {ν : A → Prop // DnfModel A ν} = Nat.card
        {ν : B → Prop // DnfModel B ν} :=
  (DescriptiveComplexity.SharpDNF).iso_invariant e

/--
---
conclusion: Lax859101.DnfValues.sharpDnf_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpDnf_eq (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpDNF A = Nat.card {ν : A → Prop // DnfModel A ν} :=
  ofFun_eq (f := fun A _ => Nat.card
      {ν : A → Prop // DnfModel A ν}) Lax859101.DnfValues.sharpDnf_count_iso A

/-- The library's #DNF and the concept's have the same values. -/
theorem sharpDnf_agree (A : Type) [Lax904597.Sat.sat.Structure A] :
    DescriptiveComplexity.SharpDNF A = SharpDNF A :=
  (sharpDnf_eq A).symm

/--
---
conclusion: Lax859101.NaeSatValues.sharpNaeSat_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpNaeSat_count_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) : Nat.card {ν : A → Prop // NAEModel A ν} = Nat.card
        {ν : B → Prop // NAEModel B ν} :=
  (DescriptiveComplexity.SharpNAESAT).iso_invariant e

/--
---
conclusion: Lax859101.NaeSatValues.sharpNaeSat_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpNaeSat_eq (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpNAESAT A = Nat.card {ν : A → Prop // NAEModel A ν} :=
  ofFun_eq (f := fun A _ => Nat.card
      {ν : A → Prop // NAEModel A ν}) Lax859101.NaeSatValues.sharpNaeSat_count_iso A

/-- The library's #NAE-SAT and the concept's have the same values. -/
theorem sharpNaeSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] :
    DescriptiveComplexity.SharpNAESAT A = SharpNAESAT A :=
  (sharpNaeSat_eq A).symm

/--
---
conclusion: Lax859101.NaeSatValues.sharpSetSplitting_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpSetSplitting_count_iso
    {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
        [Lax799700.SetFamily.setSystem.Structure B]
    (e : A ≃[Lax799700.SetFamily.setSystem] B) : Nat.card
        {S : A → Prop // SplitColoring A S} = Nat.card {S : B → Prop // SplitColoring B S} :=
  (DescriptiveComplexity.SharpSetSplitting).iso_invariant e

/--
---
conclusion: Lax859101.NaeSatValues.sharpSetSplitting_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpSetSplitting_eq (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    SharpSetSplitting A = Nat.card {S : A → Prop // SplitColoring A S} :=
  ofFun_eq (f := fun A _ => Nat.card
      {S : A → Prop // SplitColoring A S}) Lax859101.NaeSatValues.sharpSetSplitting_count_iso A

/-- The library's #Set Splitting and the concept's have the same values. -/
theorem sharpSetSplitting_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    DescriptiveComplexity.SharpSetSplitting A = SharpSetSplitting A :=
  (sharpSetSplitting_eq A).symm

/--
---
conclusion: Lax859101.RestrictedSatValues.sharpTwoSat_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpTwoSat_count_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) : Nat.card
        {ν : A → Prop // WidthAtMostTwo A ∧ SatModel A ν} = Nat.card
            {ν : B → Prop // WidthAtMostTwo B ∧ SatModel B ν} :=
  (sharpTwoSat_lib A).symm.trans (((DescriptiveComplexity.SharpTwoSAT).iso_invariant e).trans
      (sharpTwoSat_lib B))

/--
---
conclusion: Lax859101.RestrictedSatValues.sharpTwoSat_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpTwoSat_eq (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpTwoSAT A = Nat.card {ν : A → Prop // WidthAtMostTwo A ∧ SatModel A ν} :=
  ofFun_eq (f := fun A _ => Nat.card
      {ν : A → Prop // WidthAtMostTwo A ∧ SatModel A ν})
          Lax859101.RestrictedSatValues.sharpTwoSat_count_iso A

/-- The library's #2SAT and the concept's have the same values. -/
theorem sharpTwoSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] :
    DescriptiveComplexity.SharpTwoSAT A = SharpTwoSAT A :=
  (sharpTwoSat_lib A).trans (sharpTwoSat_eq A).symm

/--
---
conclusion: Lax859101.RestrictedSatValues.sharpHornSat_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpHornSat_count_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) : Nat.card
        {ν : A → Prop // AtMostOnePositive A ∧ SatModel A ν} = Nat.card
            {ν : B → Prop // AtMostOnePositive B ∧ SatModel B ν} :=
  (sharpHornSat_lib A).symm.trans (((DescriptiveComplexity.SharpHornSAT).iso_invariant e).trans
      (sharpHornSat_lib B))

/--
---
conclusion: Lax859101.RestrictedSatValues.sharpHornSat_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpHornSat_eq (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpHornSAT A = Nat.card {ν : A → Prop // AtMostOnePositive A ∧ SatModel A ν} :=
  ofFun_eq (f := fun A _ => Nat.card
      {ν : A → Prop // AtMostOnePositive A ∧ SatModel A ν})
          Lax859101.RestrictedSatValues.sharpHornSat_count_iso A

/-- The library's #HORN-SAT and the concept's have the same values. -/
theorem sharpHornSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] :
    DescriptiveComplexity.SharpHornSAT A = SharpHornSAT A :=
  (sharpHornSat_lib A).trans (sharpHornSat_eq A).symm

/--
---
conclusion: Lax859101.RestrictedSatValues.sharpMonotoneTwoSat_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpMonotoneTwoSat_count_iso
    {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) : Nat.card {ν : A → Prop //
        (WidthAtMostTwo A ∧ NoNegative A) ∧ SatModel A ν} = Nat.card {ν : B → Prop //
            (WidthAtMostTwo B ∧ NoNegative B) ∧ SatModel B ν} :=
  (sharpMonotoneTwoSat_lib A).symm.trans
      (((DescriptiveComplexity.SharpMonotoneTwoSAT).iso_invariant e).trans
          (sharpMonotoneTwoSat_lib B))

/--
---
conclusion: Lax859101.RestrictedSatValues.sharpMonotoneTwoSat_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpMonotoneTwoSat_eq (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpMonotoneTwoSAT A = Nat.card {ν : A → Prop //
        (WidthAtMostTwo A ∧ NoNegative A) ∧ SatModel A ν} :=
  ofFun_eq (f := fun A _ => Nat.card {ν : A → Prop //
      (WidthAtMostTwo A ∧ NoNegative A) ∧ SatModel A ν})
          Lax859101.RestrictedSatValues.sharpMonotoneTwoSat_count_iso A

/-- The library's #Monotone-2SAT and the concept's have the same values. -/
theorem sharpMonotoneTwoSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] :
    DescriptiveComplexity.SharpMonotoneTwoSAT A = SharpMonotoneTwoSAT A :=
  (sharpMonotoneTwoSat_lib A).trans (sharpMonotoneTwoSat_eq A).symm

/--
---
conclusion: Lax859101.AllSetsValues.sharpThreeCol_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpThreeCol_count_iso
    {A B : Type} [FirstOrder.Language.graph.Structure A] [FirstOrder.Language.graph.Structure B]
    (e : A ≃[FirstOrder.Language.graph] B) : Nat.card
        {χ : A → Fin 3 // ∀ x y : A, RelMap Language.adj ![x, y] → χ x ≠ χ y} = Nat.card
            {χ : B → Fin 3 // ∀ x y : B, RelMap Language.adj ![x, y] → χ x ≠ χ y} :=
  (DescriptiveComplexity.SharpThreeCol).iso_invariant e

/--
---
conclusion: Lax859101.AllSetsValues.sharpThreeCol_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpThreeCol_eq (A : Type) [FirstOrder.Language.graph.Structure A] :
    SharpThreeCol A = Nat.card {χ : A → Fin 3 // ∀ x y : A, RelMap Language.adj ![x, y] → χ x ≠ χ
        y} :=
  ofFun_eq (f := fun A _ => Nat.card
      {χ : A → Fin 3 // ∀ x y : A, RelMap Language.adj ![x, y] → χ x ≠ χ y})
          Lax859101.AllSetsValues.sharpThreeCol_count_iso A

/-- The library's #3-Colorability and the concept's have the same values. -/
theorem sharpThreeCol_agree (A : Type) [FirstOrder.Language.graph.Structure A] :
    DescriptiveComplexity.SharpThreeCol A = SharpThreeCol A :=
  (sharpThreeCol_eq A).symm

/--
---
conclusion: Lax859101.AllSetsValues.sharpAllIndependentSets_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpAllIndependentSets_count_iso
    {A B : Type} [FirstOrder.Language.graph.Structure A] [FirstOrder.Language.graph.Structure B]
    (e : A ≃[FirstOrder.Language.graph] B) : Nat.card {S : A → Prop // IndepSet (fun x y : A =>
        RelMap Language.adj ![x, y]) S} = Nat.card {S : B → Prop // IndepSet (fun x y : B =>
            RelMap Language.adj ![x, y]) S} :=
  (DescriptiveComplexity.SharpAllIndependentSets).iso_invariant e

/--
---
conclusion: Lax859101.AllSetsValues.sharpAllIndependentSets_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpAllIndependentSets_eq (A : Type) [FirstOrder.Language.graph.Structure A] :
    SharpAllIndependentSets A = Nat.card {S : A → Prop // IndepSet (fun x y : A =>
        RelMap Language.adj ![x, y]) S} :=
  ofFun_eq (f := fun A _ => Nat.card {S : A → Prop // IndepSet (fun x y : A =>
      RelMap Language.adj ![x, y]) S}) Lax859101.AllSetsValues.sharpAllIndependentSets_count_iso A

/-- The library's counting all independent sets and the concept's have the same values. -/
theorem sharpAllIndependentSets_agree (A : Type) [FirstOrder.Language.graph.Structure A] :
    DescriptiveComplexity.SharpAllIndependentSets A = SharpAllIndependentSets A :=
  (sharpAllIndependentSets_eq A).symm

/--
---
conclusion: Lax859101.AllSetsValues.sharpAllVertexCovers_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpAllVertexCovers_count_iso
    {A B : Type} [FirstOrder.Language.graph.Structure A] [FirstOrder.Language.graph.Structure B]
    (e : A ≃[FirstOrder.Language.graph] B) : Nat.card {C : A → Prop // GVertexCover A C} = Nat.card
        {C : B → Prop // GVertexCover B C} :=
  (DescriptiveComplexity.SharpAllVertexCovers).iso_invariant e

/--
---
conclusion: Lax859101.AllSetsValues.sharpAllVertexCovers_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpAllVertexCovers_eq (A : Type) [FirstOrder.Language.graph.Structure A] :
    SharpAllVertexCovers A = Nat.card {C : A → Prop // GVertexCover A C} :=
  ofFun_eq (f := fun A _ => Nat.card
      {C : A → Prop // GVertexCover A C}) Lax859101.AllSetsValues.sharpAllVertexCovers_count_iso A

/-- The library's counting all vertex covers and the concept's have the same values. -/
theorem sharpAllVertexCovers_agree (A : Type) [FirstOrder.Language.graph.Structure A] :
    DescriptiveComplexity.SharpAllVertexCovers A = SharpAllVertexCovers A :=
  (sharpAllVertexCovers_eq A).symm

/--
---
conclusion: Lax859101.BipartiteValues.sharpBIS_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpBIS_count_iso {A B : Type} [Lax859101.CountingBipartite.bipGraph.Structure A]
    [Lax859101.CountingBipartite.bipGraph.Structure B]
    (e : A ≃[Lax859101.CountingBipartite.bipGraph] B) : Nat.card
        {S : A → Prop // BipIndep A S} = Nat.card {S : B → Prop // BipIndep B S} :=
  (DescriptiveComplexity.SharpBIS).iso_invariant e

/--
---
conclusion: Lax859101.BipartiteValues.sharpBIS_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpBIS_eq (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    SharpBIS A = Nat.card {S : A → Prop // BipIndep A S} :=
  ofFun_eq (f := fun A _ => Nat.card
      {S : A → Prop // BipIndep A S}) Lax859101.BipartiteValues.sharpBIS_count_iso A

/-- The library's #BIS and the concept's have the same values. -/
theorem sharpBIS_agree (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    DescriptiveComplexity.SharpBIS A = SharpBIS A :=
  (sharpBIS_eq A).symm

/--
---
conclusion: Lax859101.BipartiteValues.sharpPP2DNF_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpPP2DNF_count_iso {A B : Type} [Lax859101.CountingBipartite.bipGraph.Structure A]
    [Lax859101.CountingBipartite.bipGraph.Structure B]
    (e : A ≃[Lax859101.CountingBipartite.bipGraph] B) : Nat.card
        {S : A → Prop // Pp2dnfModel A S} = Nat.card {S : B → Prop // Pp2dnfModel B S} :=
  (DescriptiveComplexity.SharpPP2DNF).iso_invariant e

/--
---
conclusion: Lax859101.BipartiteValues.sharpPP2DNF_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpPP2DNF_eq (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    SharpPP2DNF A = Nat.card {S : A → Prop // Pp2dnfModel A S} :=
  ofFun_eq (f := fun A _ => Nat.card
      {S : A → Prop // Pp2dnfModel A S}) Lax859101.BipartiteValues.sharpPP2DNF_count_iso A

/-- The library's #PP2DNF and the concept's have the same values. -/
theorem sharpPP2DNF_agree (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    DescriptiveComplexity.SharpPP2DNF A = SharpPP2DNF A :=
  (sharpPP2DNF_eq A).symm

/--
---
conclusion: Lax859101.DnfComplete.sharpSat_subtractive_sharpDnf
---
The library's reduction, with an identity step at each end for the agreements.
-/
theorem sharpSat_subtractive_sharpDnf : SubtractiveReducible SharpSAT SharpDNF :=
  .parsimonious (idRed fun A _ _ => (sharpSat_agree A).symm)
    (DescriptiveComplexity.SubtractiveReducible.trans
        DescriptiveComplexity.sharpSat_subtractive_sharpDnf
      (.parsimonious (idRed fun A _ _ => sharpDnf_agree A) (.refl _)))

/--
---
conclusion: Lax859101.DnfComplete.sharpDnf_sharpP_complete
---
Membership is the library's; hardness is #SAT's, by the statements of the
required submission and of this one, carried along the subtractive reduction.
-/
theorem sharpDnf_sharpP_complete : SubtractiveComplete SharpP SharpDNF :=
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpDnf_agree A).mp DescriptiveComplexity.sharpDnf_sharpP_complete.1,
    Lax859101.SubtractiveClosure.subtractiveHard_of_subtractive SharpP
      Lax859101.DnfComplete.sharpSat_subtractive_sharpDnf
      (Lax859101.SubtractiveClosure.subtractiveComplete_sharpP_of_parsimoniousComplete
        Lax366625.SharpSatComplete.sharpSat_sharpP_parsimoniousComplete).2⟩

/--
---
conclusion: Lax859101.DnfComplete.sharpDnf_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from #SAT, by this submission's statement or
    the one
it requires, along the library's reduction.
-/
theorem sharpDnf_sharpP_oneCallComplete : OneCallComplete SharpP SharpDNF :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard DescriptiveComplexity.SharpSAT :=
    DescriptiveComplexity.oneCallHard_sharpP_of_parsimoniousHard
      ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
          sharpSat_agree A).mpr
        Lax366625.SharpSatComplete.sharpSat_sharpP_parsimoniousComplete.2)
  oneCallComplete_of_lib sharpDnf_agree
    ⟨(DescriptiveComplexity.sharpDnf_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
          DescriptiveComplexity.sharpSat_oneCall_sharpDnf hY⟩

/--
---
conclusion: Lax859101.NaeSatComplete.sharpNaeSat_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from #SAT, by this submission's statement or
    the one
it requires, along the library's reduction.
-/
theorem sharpNaeSat_sharpP_oneCallComplete : OneCallComplete SharpP SharpNAESAT :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard DescriptiveComplexity.SharpSAT :=
    DescriptiveComplexity.oneCallHard_sharpP_of_parsimoniousHard
      ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
          sharpSat_agree A).mpr
        Lax366625.SharpSatComplete.sharpSat_sharpP_parsimoniousComplete.2)
  oneCallComplete_of_lib sharpNaeSat_agree
    ⟨(DescriptiveComplexity.sharpNaeSat_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
          DescriptiveComplexity.sharpSat_oneCall_sharpNaeSat hY⟩

/--
---
conclusion: Lax859101.NaeSatComplete.sharpSetSplitting_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from #NAE-SAT, by this submission's statement
    or the one
it requires, along the library's reduction.
-/
theorem sharpSetSplitting_sharpP_oneCallComplete : OneCallComplete SharpP SharpSetSplitting :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard DescriptiveComplexity.SharpNAESAT :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
        sharpNaeSat_agree A).mpr
      Lax859101.NaeSatComplete.sharpNaeSat_sharpP_oneCallComplete.2
  oneCallComplete_of_lib sharpSetSplitting_agree
    ⟨(DescriptiveComplexity.sharpSetSplitting_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
          DescriptiveComplexity.sharpNaeSat_oneCall_sharpSetSplitting hY⟩

/--
---
conclusion: Lax859101.ColoringComplete.sharpThreeCol_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from #SAT, by this submission's statement or
    the one
it requires, along the library's reduction.
-/
theorem sharpThreeCol_sharpP_oneCallComplete : OneCallComplete SharpP SharpThreeCol :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard DescriptiveComplexity.SharpSAT :=
    DescriptiveComplexity.oneCallHard_sharpP_of_parsimoniousHard
      ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
          sharpSat_agree A).mpr
        Lax366625.SharpSatComplete.sharpSat_sharpP_parsimoniousComplete.2)
  oneCallComplete_of_lib sharpThreeCol_agree
    ⟨(DescriptiveComplexity.sharpThreeCol_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
          DescriptiveComplexity.sharpSat_oneCall_sharpThreeCol hY⟩

/--
---
conclusion: Lax859101.AllSetsComplete.sharpAllIndependentSets_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from #Independent Set, by this submission's
    statement or the one
it requires, along the library's reduction.
-/
theorem sharpAllIndependentSets_sharpP_oneCallComplete : OneCallComplete SharpP
    SharpAllIndependentSets :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard DescriptiveComplexity.SharpIndependentSet :=
    DescriptiveComplexity.oneCallHard_sharpP_of_parsimoniousHard
      ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
          sharpIndependentSet_agree A).mpr
        Lax280166.IndependentSetComplete.sharpIndependentSet_sharpP_parsimoniousComplete.2)
  oneCallComplete_of_lib sharpAllIndependentSets_agree
    ⟨(DescriptiveComplexity.sharpAllIndependentSets_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
          DescriptiveComplexity.sharpIndependentSet_oneCall_sharpAllIndependentSets hY⟩

/--
---
conclusion: Lax859101.AllSetsComplete.sharpAllVertexCovers_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from counting all independent sets, by this
    submission's statement or the one
it requires, along the library's reduction.
-/
theorem sharpAllVertexCovers_sharpP_oneCallComplete : OneCallComplete SharpP SharpAllVertexCovers :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard
      DescriptiveComplexity.SharpAllIndependentSets :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
        sharpAllIndependentSets_agree A).mpr
      Lax859101.AllSetsComplete.sharpAllIndependentSets_sharpP_oneCallComplete.2
  oneCallComplete_of_lib sharpAllVertexCovers_agree
    ⟨(DescriptiveComplexity.sharpAllVertexCovers_sharpP_oneCallComplete).1,
      (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
      (DescriptiveComplexity.sharpAllVertexCovers_eq A).symm).mp hY⟩

/--
---
conclusion: Lax859101.RestrictedSatComplete.sharpTwoSat_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from counting all independent sets, by this
    submission's statement or the one
it requires, along the library's reduction.
-/
theorem sharpTwoSat_sharpP_oneCallComplete : OneCallComplete SharpP SharpTwoSAT :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard
      DescriptiveComplexity.SharpAllIndependentSets :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
        sharpAllIndependentSets_agree A).mpr
      Lax859101.AllSetsComplete.sharpAllIndependentSets_sharpP_oneCallComplete.2
  oneCallComplete_of_lib sharpTwoSat_agree
    ⟨(DescriptiveComplexity.sharpTwoSat_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
      ((DescriptiveComplexity.sharpAllIndependentSets_oneCall_sharpSat false).restrict
          DescriptiveComplexity.widthTwoS
        fun _ _ _ _ _ => DescriptiveComplexity.realize_widthTwoS.mpr
            DescriptiveComplexity.edge_widthAtMostTwo) hY⟩

/--
---
conclusion: Lax859101.RestrictedSatComplete.sharpHornSat_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from counting all independent sets, by this
    submission's statement or the one
it requires, along the library's reduction.
-/
theorem sharpHornSat_sharpP_oneCallComplete : OneCallComplete SharpP SharpHornSAT :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard
      DescriptiveComplexity.SharpAllIndependentSets :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
        sharpAllIndependentSets_agree A).mpr
      Lax859101.AllSetsComplete.sharpAllIndependentSets_sharpP_oneCallComplete.2
  oneCallComplete_of_lib sharpHornSat_agree
    ⟨(DescriptiveComplexity.sharpHornSat_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
      ((DescriptiveComplexity.sharpAllIndependentSets_oneCall_sharpSat false).restrict
          DescriptiveComplexity.hornS
        fun _ _ _ _ _ => DescriptiveComplexity.realize_hornS.mpr
            DescriptiveComplexity.edge_atMostOnePositive) hY⟩

/--
---
conclusion: Lax859101.RestrictedSatComplete.sharpMonotoneTwoSat_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from counting all independent sets, by this
    submission's statement or the one
it requires, along the library's reduction.
-/
theorem sharpMonotoneTwoSat_sharpP_oneCallComplete : OneCallComplete SharpP SharpMonotoneTwoSAT :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard
      DescriptiveComplexity.SharpAllIndependentSets :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
        sharpAllIndependentSets_agree A).mpr
      Lax859101.AllSetsComplete.sharpAllIndependentSets_sharpP_oneCallComplete.2
  oneCallComplete_of_lib sharpMonotoneTwoSat_agree
    ⟨(DescriptiveComplexity.sharpMonotoneTwoSat_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
      ((DescriptiveComplexity.sharpAllIndependentSets_oneCall_sharpSat true).restrict _ fun _ _ _ _
          _ =>
        Formula.realize_inf.mpr ⟨DescriptiveComplexity.realize_widthTwoS.mpr
            DescriptiveComplexity.edge_widthAtMostTwo,
          DescriptiveComplexity.realize_monotoneS.mpr DescriptiveComplexity.edge_noNegative⟩) hY⟩

/--
---
conclusion: Lax859101.BipartiteComplete.sharpBIS_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from counting all independent sets, by this
    submission's statement or the one
it requires, along the library's reduction.
-/
theorem sharpBIS_sharpP_oneCallComplete : OneCallComplete SharpP SharpBIS :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard
      DescriptiveComplexity.SharpAllIndependentSets :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
        sharpAllIndependentSets_agree A).mpr
      Lax859101.AllSetsComplete.sharpAllIndependentSets_sharpP_oneCallComplete.2
  oneCallComplete_of_lib sharpBIS_agree
    ⟨(DescriptiveComplexity.sharpBIS_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
          DescriptiveComplexity.sharpAllIndependentSets_oneCall_sharpBIS hY⟩

/--
---
conclusion: Lax859101.BipartiteComplete.sharpPP2DNF_sharpP_oneCallComplete
---
Membership is the library's; its hardness is carried from #BIS, by this submission's statement or
    the one
it requires, along the library's reduction.
-/
theorem sharpPP2DNF_sharpP_oneCallComplete : OneCallComplete SharpP SharpPP2DNF :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard DescriptiveComplexity.SharpBIS :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ => sharpBIS_agree A).mpr
      Lax859101.BipartiteComplete.sharpBIS_sharpP_oneCallComplete.2
  oneCallComplete_of_lib sharpPP2DNF_agree
    ⟨(DescriptiveComplexity.sharpPP2DNF_sharpP_oneCallComplete).1,
      DescriptiveComplexity.CountingClass.OneCallHard.of_oneCall
          DescriptiveComplexity.sharpBIS_oneCall_sharpPP2DNF hY⟩

end Lax859101Proofs.Bridge
