import Lax175070.CountingValues
import Lax175070.CountClassMembership
import Lax175070.CountClassInclusions
import Lax175070.CountClassComplements
import Lax175070.ParitySatComplete
import Lax175070.SelectedSatComplete
import Lax366625.SharpSatValue
import Lax366625.CountingRunsValue
import Lax175070Proofs.DescriptiveComplexity.Complexity
import Lax175070Proofs.DescriptiveComplexity.Counting.DecisionClasses
import Lax175070Proofs.DescriptiveComplexity.Problems.Machine.Counting
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.Counting
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.CountingCompare
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.CountingDecision

/-!
# The counting decision classes, from the library's theorems

The classes are built in the concepts from their membership predicates, which
are the library's, and the problems are decision versions of the counting
problems of the required submission. Statements are transported along the
agreement of the library's problems with the concepts'.
-/

namespace Lax175070Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Sat Lax904597.Interpretations
    Lax904597.Machines Lax564036.Hierarchy
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax366625.CountingRuns Lax175070.CountDefinability Lax175070.SelectedSat Lax485149.Problems
open Lax485149.Complement

/-- A problem given by an isomorphism-invariant property holds exactly when the
property does. -/
theorem ofPred_iff {L : Language.{0, 0}} [L.IsRelational] {Q : ∀ (A : Type) [L.Structure A], Prop}
    (hQ : ∀ {A B : Type} [L.Structure A] [L.Structure B], (A ≃[L] B) → (Q A ↔ Q B))
    (V : Type) [L.Structure V] : DecisionProblem.ofPred Q V ↔ Q V := by
  constructor
  · rintro ⟨B, i, f, h⟩
    exact (hQ f).mp h
  · intro h
    exact ⟨V, inferInstance, Language.Equiv.refl _ _, h⟩

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

/-- Completeness for a class of the library, transported along an agreement of
the finite instances. -/
theorem complete_congr (C : DescriptiveComplexity.ComplexityClass) {L : Language.{0, 0}}
    [L.IsRelational]
    {Q Q' : DecisionProblem L} (h : ∀ (A : Type) [L.Structure A] [Finite A], Q A ↔ Q' A)
    (hc : C.Complete Q) : C.Mem Q' ∧ C.Hard Q' :=
  ⟨(C.mem_congr_finite h).mp hc.1, (C.hard_congr_finite h).mp hc.2⟩

/-- An ordered first-order reduction transported along agreements of its two
ends. -/
def OrderedFOReduction.congr {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {Q Q₁ : DecisionProblem L} {T T₁ : DecisionProblem L'}
    (hQ : ∀ (A : Type) [L.Structure A], Q A ↔ Q₁ A) (hT : ∀ (A : Type) [L'.Structure A], T A ↔ T₁ A)
    (f : OrderedFOReduction Q T) : OrderedFOReduction Q₁ T₁ :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => ((hQ A).symm.trans (f.correct A)).trans (hT _) }

/-- The library's #SAT and the one of the required submission have the same
values. -/
theorem sharpSat_agree (A : Type) [sat.Structure A] :
    DescriptiveComplexity.SharpSAT A = SharpSAT A :=
  (Lax366625.SharpSatValue.sharpSat_eq A).symm

/-- The library's count of accepting runs and the one of the required
submission have the same values. -/
theorem sharpNtmAccept_agree (A : Type) [turing.Structure A] :
    DescriptiveComplexity.SharpNTMAccept A = SharpNTMAccept A :=
  (Lax366625.CountingRunsValue.sharpNtmAccept_eq A).symm

/-- The library's decision version of the count of accepting runs and the
concept's agree. -/
theorem decide_agree (R : ℕ → Prop) (A : Type) [turing.Structure A] :
    DescriptiveComplexity.SharpNTMAccept.decide R A ↔ decide R SharpNTMAccept A := by
  rw [Lax175070.CountingValues.decide_iff, ← sharpNtmAccept_agree]
  exact Iff.rfl

/--
---
conclusion: Lax175070.CountingValues.decide_iff
---
The counts of isomorphic structures are equal.
-/
theorem decide_iff {L : Language.{0, 0}} [L.IsRelational] (R : ℕ → Prop) (C : CountingProblem L)
    (A : Type) [L.Structure A] : decide R C A ↔ R (C A) :=
  ofPred_iff (fun e => by rw [C.iso_invariant e]) A

/--
---
conclusion: Lax175070.CountingValues.sharpSelSat_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpSelSat_count_iso (b : Bool) {A B : Type} [satSel.Structure A] [satSel.Structure B]
    (e : A ≃[satSel] B) :
    Nat.card {ν : A → Prop // SelModel A b ν} = Nat.card {ν : B → Prop // SelModel B b ν} :=
  (DescriptiveComplexity.SharpSelSAT b).iso_invariant e

/--
---
conclusion: Lax175070.CountingValues.sharpSelSat_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpSelSat_eq (b : Bool) (A : Type) [satSel.Structure A] :
    SharpSelSAT b A = Nat.card {ν : A → Prop // SelModel A b ν} :=
  ofFun_eq (f := fun A _ => Nat.card {ν : A → Prop // SelModel A b ν})
    (Lax175070.CountingValues.sharpSelSat_count_iso b) A

/-- The library's #SelSAT and the concept's have the same values. -/
theorem sharpSelSat_agree (b : Bool) (A : Type) [satSel.Structure A] :
    DescriptiveComplexity.SharpSelSAT b A = SharpSelSAT b A :=
  (sharpSelSat_eq b A).symm

/--
---
conclusion: Lax175070.CountingValues.selMajSat_iff
---
The two counts are invariant.
-/
theorem selMajSat_iff (A : Type) [satSel.Structure A] :
    SelMajSAT A ↔ SharpSelSAT false A < SharpSelSAT true A :=
  ofPred_iff (fun e => by rw [(SharpSelSAT false).iso_invariant e,
      (SharpSelSAT true).iso_invariant e]) A

/--
---
conclusion: Lax175070.CountingValues.selEqSat_iff
---
The two counts are invariant.
-/
theorem selEqSat_iff (A : Type) [satSel.Structure A] :
    SelEqSAT A ↔ SharpSelSAT true A = SharpSelSAT false A :=
  ofPred_iff (fun e => by rw [(SharpSelSAT false).iso_invariant e,
      (SharpSelSAT true).iso_invariant e]) A

/--
---
conclusion: Lax175070.CountClassMembership.mem_countClass_of_sharpP
---
The library's theorem.
-/
theorem mem_countClass_of_sharpP {L : Language.{0, 0}} [L.IsRelational] {S R : ℕ → ℕ → Prop} {C D :
    CountingProblem L}
    (hC : SharpP.Mem C) (hD : SharpP.Mem D) {P : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      S (C A) (D A) ∧ (P A ↔ R (C A) (D A))) : (countClass S R).Mem P :=
  DescriptiveComplexity.mem_countClass_of_sharpP hC hD h

/--
---
conclusion: Lax175070.CountClassInclusions.UP_subset_parityP
---
The library's theorem.
-/
theorem UP_subset_parityP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : UP.Mem P) :
    ParityP.Mem P :=
  DescriptiveComplexity.UP_subset_parityP h

/--
---
conclusion: Lax175070.CountClassInclusions.UP_subset_NP
---
The library's theorem.
-/
theorem UP_subset_NP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) (h : UP.Mem P) :
    NP.Mem P :=
  DescriptiveComplexity.UP_subset_NP h

/--
---
conclusion: Lax175070.CountClassInclusions.NP_subset_PP
---
The library's theorem.
-/
theorem NP_subset_PP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) (h : NP.Mem P) :
    PP.Mem P :=
  DescriptiveComplexity.NP_subset_PP h

/--
---
conclusion: Lax175070.CountClassInclusions.coNP_subset_PP
---
The library's theorem.
-/
theorem coNP_subset_PP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : coNP.Mem P) :
    PP.Mem P :=
  DescriptiveComplexity.coNP_subset_PP h

/--
---
conclusion: Lax175070.CountClassComplements.compl_mem_parityP
---
The library's theorem.
-/
theorem compl_mem_parityP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : ParityP.Mem P) :
    ParityP.Mem (DecisionProblem.compl P) :=
  DescriptiveComplexity.compl_mem_parityP h

/--
---
conclusion: Lax175070.CountClassComplements.compl_mem_PP
---
The library's theorem.
-/
theorem compl_mem_PP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) (h : PP.Mem P) :
    PP.Mem (DecisionProblem.compl P) :=
  DescriptiveComplexity.compl_mem_PP h

/--
---
conclusion: Lax175070.ParitySatComplete.paritySat_parityP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem paritySat_parityP_complete : ParityP.Complete ParitySAT :=
  complete_congr _ (fun A _ _ => by
    show _ ↔ decide Odd SharpSAT A
    rw [Lax175070.CountingValues.decide_iff, ← sharpSat_agree]; exact Iff.rfl)
    DescriptiveComplexity.paritySat_parityP_complete

/--
---
conclusion: Lax175070.ParitySatComplete.modSat_modP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem modSat_modP_complete (k : ℕ) : (ModP k).Complete (ModSAT k) :=
  complete_congr _ (fun A _ _ => by
    show _ ↔ decide (fun c => ¬ k ∣ c) SharpSAT A
    rw [Lax175070.CountingValues.decide_iff, ← sharpSat_agree]; exact Iff.rfl)
    (DescriptiveComplexity.modSat_modP_complete k)

/--
---
conclusion: Lax175070.ParitySatComplete.parityP_complete_of_sharpP_parsimoniousComplete
---
The library's theorem, transported along the agreement of the decision
versions.
-/
theorem parityP_complete_of_sharpP_parsimoniousComplete {L : Language.{0, 0}} [L.IsRelational] {C :
    CountingProblem L}
    (hC : SharpP.ParsimoniousComplete C) : ParityP.Complete (decide Odd C) :=
  complete_congr _ (fun A _ _ => (Lax175070.CountingValues.decide_iff Odd C A).symm)
    (DescriptiveComplexity.parityP_complete_of_sharpP_parsimoniousComplete hC)

/--
---
conclusion: Lax175070.ParitySatComplete.modP_complete_of_sharpP_parsimoniousComplete
---
The library's theorem, transported along the agreement of the decision
versions.
-/
theorem modP_complete_of_sharpP_parsimoniousComplete {L : Language.{0, 0}} [L.IsRelational]
    (k : ℕ) {C : CountingProblem L}
    (hC : SharpP.ParsimoniousComplete C) :
    (ModP k).Complete (decide (fun c => ¬ k ∣ c) C) :=
  complete_congr _ (fun A _ _ => (Lax175070.CountingValues.decide_iff (fun c => ¬ k ∣ c) C A).symm)
    (DescriptiveComplexity.modP_complete_of_sharpP_parsimoniousComplete k hC)

/--
---
conclusion: Lax175070.ParitySatComplete.mem_parityP_iff_le_parity_sharpNtmAccept
---
The library's theorem, the reductions transported to the concept's problem
along the agreement.
-/
theorem mem_parityP_iff_le_parity_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    ParityP.Mem P ↔ Nonempty (OrderedFOReduction P (decide Odd SharpNTMAccept)) :=
  (DescriptiveComplexity.mem_parityP_iff_le_parity_sharpNtmAccept P).trans
    ⟨Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) (decide_agree Odd)),
      Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) fun A _ =>
          (decide_agree Odd A).symm)⟩

/--
---
conclusion: Lax175070.ParitySatComplete.mem_modP_iff_le_mod_sharpNtmAccept
---
The library's theorem, the reductions transported to the concept's problem
along the agreement.
-/
theorem mem_modP_iff_le_mod_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational] (k : ℕ)
    (P : DecisionProblem L) :
    (ModP k).Mem P ↔ Nonempty (OrderedFOReduction P (decide (fun c => ¬ k ∣ c) SharpNTMAccept)) :=
  (DescriptiveComplexity.mem_modP_iff_le_mod_sharpNtmAccept k P).trans
    ⟨Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) (decide_agree _)),
      Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) fun A _ =>
          (decide_agree _ A).symm)⟩

/--
---
conclusion: Lax175070.SelectedSatComplete.selMajSat_PP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem selMajSat_PP_complete : PP.Complete SelMajSAT :=
  complete_congr _ (fun A _ _ => by
    rw [Lax175070.CountingValues.selMajSat_iff, ← sharpSelSat_agree, ← sharpSelSat_agree]; exact
        Iff.rfl)
    DescriptiveComplexity.selMajSat_PP_complete

/--
---
conclusion: Lax175070.SelectedSatComplete.selEqSat_CeqP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem selEqSat_CeqP_complete : CeqP.Complete SelEqSAT :=
  complete_congr _ (fun A _ _ => by
    rw [Lax175070.CountingValues.selEqSat_iff, ← sharpSelSat_agree, ← sharpSelSat_agree]; exact
        Iff.rfl)
    DescriptiveComplexity.selEqSat_CeqP_complete

end Lax175070Proofs.Bridge
