import Lax904597.CookLevin
import Lax904597.MachineForm
import Lax904597.NPClass
import Lax904597Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax904597Proofs.DescriptiveComplexity.Problems.Machine

/-!
# From the library's theorems to the concepts

The concepts restate the library's definitions, which the vendored library
code uses directly, so every statement below is the library's theorem read on
the concepts' names. The one difference is the complexity class: the library
packs closure under reductions into the structure `ComplexityClass`, while the
concepts keep a class as its membership and hardness predicates and state the
closure facts separately (`Lax904597.NPClass`); membership and hardness
coincide definitionally.
-/

namespace Lax904597Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
  Lax904597.Classes Lax904597.Sat Lax904597.Machines

/--
---
conclusion: Lax904597.Machines.ntmAccept_iso
---
An isomorphism of machine instances makes the two machines agree symbol by
symbol, and agreement transports well-formedness and acceptance.
-/
theorem ntmAccept_iso : NTMAcceptInvariant := fun e =>
  have h := DescriptiveComplexity.agree_of_equiv e
  (and_congr h.wellFormed h.accepts).symm

/--
---
conclusion: Lax904597.CookLevin.sat_sigmaSODefinable
---
SAT is existential second-order definable: guess a truth assignment and check
every clause in first-order logic.
-/
theorem sat_sigmaSODefinable : SigmaSODefinable 1 SAT :=
  DescriptiveComplexity.sat_sigmaSODefinable

/--
---
conclusion: Lax904597.CookLevin.sat_hard_of_sigmaSODefinable
---
Every existential second-order definable problem reduces to SAT by an ordered
first-order reduction: the library's generic Tseitin reduction.
-/
theorem sat_hard_of_sigmaSODefinable {L : Language.{0, 0}} [L.IsRelational]
    (Q : DecisionProblem L) (h : SigmaSODefinable 1 Q) : Nonempty (OrderedFOReduction Q SAT) :=
  DescriptiveComplexity.sat_hard_of_sigmaSODefinable Q h

/--
---
conclusion: Lax904597.CookLevin.SAT_NP_complete
---
The Cook–Levin theorem, as the library states it: membership in NP and
cofinal NP-hardness coincide definitionally with the concepts' reading.
-/
theorem SAT_NP_complete : NP.Complete SAT :=
  ⟨DescriptiveComplexity.SAT_NP_complete.1, DescriptiveComplexity.SAT_NP_complete.2⟩

/--
---
conclusion: Lax904597.MachineForm.SAT_complete_for_ntmAccept
---
The two reductions between SAT and machine acceptance, from the library.
-/
theorem SAT_complete_for_ntmAccept (h : NTMAcceptInvariant) :
    Nonempty (OrderedFOReduction SAT (NTMAccept h)) ∧
      ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
        Nonempty (OrderedFOReduction P (NTMAccept h)) → Nonempty (OrderedFOReduction P SAT) :=
  DescriptiveComplexity.SAT_complete_for_ntmAccept

/--
---
conclusion: Lax904597.MachineForm.mem_NP_iff_le_ntmAccept
---
NP is the class of problems reducing to machine acceptance, from the library.
-/
theorem mem_NP_iff_le_ntmAccept (h : NTMAcceptInvariant) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) : NP.Mem P ↔ Nonempty (OrderedFOReduction P (NTMAccept h)) :=
  DescriptiveComplexity.mem_NP_iff_le_ntmAccept P

/--
---
conclusion: Lax904597.NPClass.NP_mem_of_foReduction
---
Second-order definability pulls back along first-order reductions.
-/
theorem NP_mem_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : NP.Mem Q) :
    NP.Mem P :=
  DescriptiveComplexity.SigmaSODefinable.of_foReduction f h

/--
---
conclusion: Lax904597.NPClass.NP_mem_of_orderedReduction
---
Second-order definability pulls back along ordered first-order reductions,
the first existential block guessing the order.
-/
theorem NP_mem_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q)
    (h : NP.Mem Q) : NP.Mem P :=
  DescriptiveComplexity.SigmaSODefinable.of_orderedReduction f h

/--
---
conclusion: Lax904597.NPClass.NP_mem_congr_finite
---
A `Σ₁` definition only speaks about finite structures.
-/
theorem NP_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : NP.Mem P ↔ NP.Mem Q :=
  DescriptiveComplexity.sigmaSODefinable_congr h _

/--
---
conclusion: Lax904597.NPClass.cofinalHard_of_foReduction
---
A first-order reduction composes, as an ordered relativized one, with the
reductions out of `Q`.
-/
theorem cofinalHard_of_foReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
    (f : FOReduction P Q) (hP : CofinalHard Mem P) : CofinalHard Mem Q :=
  DescriptiveComplexity.CofinalHard.of_foReduction f hP

/--
---
conclusion: Lax904597.NPClass.cofinalHard_of_orderedReduction
---
An ordered first-order reduction composes, relativized, with the reductions
out of `Q`.
-/
theorem cofinalHard_of_orderedReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
    (f : OrderedFOReduction P Q) (hP : CofinalHard Mem P) : CofinalHard Mem Q :=
  DescriptiveComplexity.CofinalHard.of_orderedReduction f hP

/--
---
conclusion: Lax904597.NPClass.cofinalHard_of_relOrderedReduction
---
Relativized ordered reductions compose.
-/
theorem cofinalHard_of_relOrderedReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
    (f : RelOrderedFOReduction P Q) (hP : CofinalHard Mem P) : CofinalHard Mem Q :=
  DescriptiveComplexity.CofinalHard.of_relOrderedReduction f hP

/--
---
conclusion: Lax904597.NPClass.cofinalHard_congr
---
A reduction only reads its source on finite structures.
-/
theorem cofinalHard_congr
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ : Language.{0, 0}} [L₁.IsRelational] {P P' : DecisionProblem L₁}
    (h : ∀ (A : Type) [L₁.Structure A] [Finite A], P A ↔ P' A)
    (hP : CofinalHard Mem P) : CofinalHard Mem P' :=
  DescriptiveComplexity.CofinalHard.congr h hP

/--
---
conclusion: Lax904597.NPClass.cofinalHard_iff
---
Over a relational vocabulary `P` reduces to itself, so cofinal hardness is
the usual one.
-/
theorem cofinalHard_iff {L : Language.{0, 0}} [L.IsRelational]
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) :
    CofinalHard Mem P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (RelOrderedFOReduction Q P) :=
  DescriptiveComplexity.cofinalHard_iff Mem P

end Lax904597Proofs.Bridge
