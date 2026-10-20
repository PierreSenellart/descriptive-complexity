import Lax480241.ExponentialCaptures
import Lax480241.ExponentialMonotone
import Lax480241.ExponentialComplements
import Lax480241.ExponentialInclusions
import Lax480241.AlternatingSpaceValue
import Lax480241.APSPACEIsEXPTIME
import Lax480241Proofs.DescriptiveComplexity.Complexity
import Lax480241Proofs.DescriptiveComplexity.Exponential.Classes
import Lax480241Proofs.DescriptiveComplexity.Exponential.FreeSpace
import Lax480241Proofs.DescriptiveComplexity.Exponential.FreeTime
import Lax480241Proofs.DescriptiveComplexity.Exponential.GameInterp
import Lax480241Proofs.DescriptiveComplexity.Exponential.Inclusions
import Lax480241Proofs.DescriptiveComplexity.Hierarchy
import Lax480241Proofs.DescriptiveComplexity.Problems.MachineAltSpace

/-!
# The exponential classes, from the library's theorems

The classes are built in the concepts from their membership predicates,
which are the library's, so membership statements are the library's theorems.
Alternating acceptance in bounded space is defined from its conditions and
agrees with the library's problem.
-/

namespace Lax480241Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax485149.Complement Lax485149.ClassNL
open Lax535992.ClassPTIME Lax564036.Hierarchy Lax564036.AlternatingMachines Lax134656.ClassPSPACE
open Lax480241.Expansions Lax480241.SecondOrderFixedPoints Lax480241.AlternatingSpace
    Lax480241.ExponentialClasses

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

/-- The concept's `Σ` level and the library's have the same members. -/
theorem sigma_mem_agree (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    (SigmaP k).Mem P ↔ (DescriptiveComplexity.SigmaP k).Mem P := by
  cases k with
  | zero => exact Iff.rfl
  | succ k => exact Iff.rfl

/-- Completeness for a class of the library, transported along an agreement of
the finite instances. -/
theorem complete_congr (C : DescriptiveComplexity.ComplexityClass)
    {L : Language.{0, 0}} [L.IsRelational]
    {Q Q' : DecisionProblem L} (h : ∀ (A : Type) [L.Structure A] [Finite A], Q A ↔ Q' A)
    (hc : C.Complete Q) : C.Mem Q' ∧ C.Hard Q' :=
  ⟨(C.mem_congr_finite h).mp hc.1, (C.hard_congr_finite h).mp hc.2⟩

/--
---
conclusion: Lax480241.AlternatingSpaceValue.atmAcceptSpace_iff
---
The library's problem is invariant.
-/
theorem atmAcceptSpace_iff (A : Type) [(turingAlt 2).Structure A] :
    ATMAcceptSpace A ↔ TMData.WellFormed (atmData 2 A).toTMData ∧
      ATMData.BlocksSplit (atmData 2 A) ∧ ATMData.AltAcceptsSpace (atmData 2 A) true :=
  ofPred_iff (fun e => (DescriptiveComplexity.ATMAcceptSpace).iso_invariant e) A

/-- The library's problem and the concept's agree. -/
theorem atmAcceptSpace_agree (A : Type) [(turingAlt 2).Structure A] :
    DescriptiveComplexity.ATMAcceptSpace A ↔ ATMAcceptSpace A :=
  (atmAcceptSpace_iff A).symm

/--
---
conclusion: Lax480241.ExponentialCaptures.EXPTIME_eq_PTIME_exp
---
The library's theorem.
-/
theorem EXPTIME_eq_PTIME_exp {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    EXPTIME.Mem P ↔ (expClass PTIME).Mem P :=
  Iff.of_eq (congrArg (fun C : DescriptiveComplexity.ComplexityClass =>
      C.Mem P) DescriptiveComplexity.EXPTIME_eq_PTIME_exp)

/--
---
conclusion: Lax480241.ExponentialCaptures.EXPSPACE_eq_PSPACE_exp
---
The library's theorem.
-/
theorem EXPSPACE_eq_PSPACE_exp {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    EXPSPACE.Mem P ↔ (expClass PSPACE).Mem P :=
  Iff.of_eq (congrArg (fun C : DescriptiveComplexity.ComplexityClass =>
      C.Mem P) DescriptiveComplexity.EXPSPACE_eq_PSPACE_exp)

/--
---
conclusion: Lax480241.ExponentialCaptures.mem_EXPTIME_iff_solfpDefinableFree
---
The library's theorem.
-/
theorem mem_EXPTIME_iff_solfpDefinableFree {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    EXPTIME.Mem P ↔ SOLFPDefinableFree P :=
  DescriptiveComplexity.mem_EXPTIME_iff_solfpDefinableFree P

/--
---
conclusion: Lax480241.ExponentialCaptures.mem_EXPSPACE_iff_sopfpDefinableFree
---
The library's theorem.
-/
theorem mem_EXPSPACE_iff_sopfpDefinableFree {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    EXPSPACE.Mem P ↔ SOPFPDefinableFree P :=
  DescriptiveComplexity.mem_EXPSPACE_iff_sopfpDefinableFree P

/--
---
conclusion: Lax480241.ExponentialMonotone.expClass_mono
---
The same expansion, the problem it reaches being in the larger class.
-/
theorem expClass_mono {C D : ComplexityClass}
    (h : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L), C.Mem P → D.Mem P)
    {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) (hP : (expClass C).Mem P) :
    (expClass D).Mem P :=
  let ⟨X, Q, hQ, hX⟩ := hP
  ⟨X, Q, h Q hQ, hX⟩

/--
---
conclusion: Lax480241.ExponentialComplements.mem_EXPTIME_compl_iff
---
The library's theorem.
-/
theorem mem_EXPTIME_compl_iff {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    EXPTIME.Mem (DecisionProblem.compl P) ↔ EXPTIME.Mem P :=
  DescriptiveComplexity.mem_EXPTIME_compl_iff P

/--
---
conclusion: Lax480241.ExponentialComplements.mem_EXPSPACE_compl_iff
---
The library's theorem.
-/
theorem mem_EXPSPACE_compl_iff {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    EXPSPACE.Mem (DecisionProblem.compl P) ↔ EXPSPACE.Mem P :=
  DescriptiveComplexity.mem_EXPSPACE_compl_iff P

/--
---
conclusion: Lax480241.ExponentialComplements.mem_coEXPTIME_iff
---
The definition of coEXPTIME, and closure under complement by this
submission's statement.
-/
theorem mem_coEXPTIME_iff {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    coEXPTIME.Mem P ↔ EXPTIME.Mem P :=
  Lax480241.ExponentialComplements.mem_EXPTIME_compl_iff P

/--
---
conclusion: Lax480241.ExponentialComplements.mem_coEXPSPACE_iff
---
The definition of coEXPSPACE, and closure under complement by this
submission's statement.
-/
theorem mem_coEXPSPACE_iff {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    coEXPSPACE.Mem P ↔ EXPSPACE.Mem P :=
  Lax480241.ExponentialComplements.mem_EXPSPACE_compl_iff P

/--
---
conclusion: Lax480241.ExponentialInclusions.PSPACE_subset_EXPTIME
---
The library's theorem.
-/
theorem PSPACE_subset_EXPTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PSPACE.Mem P) :
    EXPTIME.Mem P :=
  DescriptiveComplexity.PSPACE_subset_EXPTIME h

/--
---
conclusion: Lax480241.ExponentialInclusions.EXPTIME_subset_NEXPTIME
---
The library's theorem.
-/
theorem EXPTIME_subset_NEXPTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : EXPTIME.Mem P) :
    NEXPTIME.Mem P :=
  DescriptiveComplexity.EXPTIME_subset_NEXPTIME h

/--
---
conclusion: Lax480241.ExponentialInclusions.NEXPTIME_subset_EXPSPACE
---
The library's theorem.
-/
theorem NEXPTIME_subset_EXPSPACE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : NEXPTIME.Mem P) :
    EXPSPACE.Mem P :=
  DescriptiveComplexity.NEXPTIME_subset_EXPSPACE h

/--
---
conclusion: Lax480241.ExponentialInclusions.EXPTIME_subset_EXPSPACE
---
The library's theorem.
-/
theorem EXPTIME_subset_EXPSPACE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : EXPTIME.Mem P) :
    EXPSPACE.Mem P :=
  DescriptiveComplexity.EXPTIME_subset_EXPSPACE h

/--
---
conclusion: Lax480241.ExponentialInclusions.PTIME_subset_EXPTIME
---
The library's theorem.
-/
theorem PTIME_subset_EXPTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PTIME.Mem P) :
    EXPTIME.Mem P :=
  DescriptiveComplexity.PTIME_subset_EXPTIME h

/--
---
conclusion: Lax480241.ExponentialInclusions.NP_subset_NEXPTIME
---
The library's theorem.
-/
theorem NP_subset_NEXPTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : NP.Mem P) :
    NEXPTIME.Mem P :=
  DescriptiveComplexity.NP_subset_NEXPTIME h

/--
---
conclusion: Lax480241.ExponentialInclusions.PSPACE_subset_EXPSPACE
---
The library's theorem.
-/
theorem PSPACE_subset_EXPSPACE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PSPACE.Mem P) :
    EXPSPACE.Mem P :=
  DescriptiveComplexity.PSPACE_subset_EXPSPACE h

/--
---
conclusion: Lax480241.ExponentialInclusions.PH_subset_EXPTIME
---
The library's theorem, the level of the hierarchy matched.
-/
theorem PH_subset_EXPTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PH.Mem P) :
    EXPTIME.Mem P :=
  let ⟨k, hk⟩ := h
  DescriptiveComplexity.PH_subset_EXPTIME ⟨k, (sigma_mem_agree k P).mp hk⟩

/--
---
conclusion: Lax480241.ExponentialInclusions.NL_exp_subset_EXPTIME
---
The library's theorem.
-/
theorem NL_exp_subset_EXPTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) (h :
    (expClass NL).Mem P) :
    EXPTIME.Mem P :=
  DescriptiveComplexity.NL_exp_subset_EXPTIME h

/--
---
conclusion: Lax480241.APSPACEIsEXPTIME.atmAcceptSpace_EXPTIME_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem atmAcceptSpace_EXPTIME_complete : EXPTIME.Complete ATMAcceptSpace :=
  complete_congr _ (fun A _ _ => (atmAcceptSpace_agree A))
      DescriptiveComplexity.atmAcceptSpace_EXPTIME_complete

end Lax480241Proofs.Bridge
