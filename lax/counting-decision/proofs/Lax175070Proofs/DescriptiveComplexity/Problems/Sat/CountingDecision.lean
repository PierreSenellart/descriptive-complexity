/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.CountingHardness
import Lax175070Proofs.DescriptiveComplexity.Problems.Machine.CountingHardness
import Lax175070Proofs.DescriptiveComplexity.Counting.DecisionClasses
import Lax175070.CountDefinability
import Lax175070.SelectedSat
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity.CountDefinable
end Lax175070Proofs.DescriptiveComplexity.CountDefinable

namespace Lax175070Proofs.DescriptiveComplexity.CountingProblem
end Lax175070Proofs.DescriptiveComplexity.CountingProblem

namespace Lax175070Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax175070Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax175070Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction
end Lax175070Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax175070Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

/-!
# ⊕SAT and Mod_k-SAT: complete problems for the classes defined by one count

For a property `R` of a number, `DescriptiveComplexity.CountingProblem.decide R C`
is the decision problem “`R` holds of the count of `C`”, and
`DescriptiveComplexity.countClass₁ R` the class of the problems defined by `R`
of one witness count: `⊕P` for `Odd`, `Mod_k P` for “not a multiple of `k`”.

* **The decision version of `#SAT` is complete for every such class**
  (`DescriptiveComplexity.decide_sharpSat_countClass₁_complete`): membership is
  that `#SAT` is in `#P`, and hardness is the parsimonious Tseitin
  interpretation of `DescriptiveComplexity.Problems.Sat.CountingHardness`, which
  carries a witness count to a model count exactly and so carries any
  property of it.
* **It transfers along parsimonious reductions**
  (`DescriptiveComplexity.countClass₁_complete_of_sharpP_parsimoniousComplete`):
  the decision version of every parsimoniously `#P`-complete problem is
  complete for every such class. So `⊕SAT`, `⊕3SAT`, `⊕Clique`, …, and the
  parity of the number of accepting runs of a machine, are `⊕P`-complete;
  likewise for `Mod_k P`.
* **The machine characterization**
  (`DescriptiveComplexity.mem_parityP_iff_le_parity_sharpNtmAccept`): a problem
  is in `⊕P` exactly when it reduces to the parity of the number of accepting
  runs of a nondeterministic polynomial-time machine, through the counting
  machine bridge of `DescriptiveComplexity.Problems.Machine.CountingHardness`.

The classical statements are [Papadimitriou, Zachos 1982][papadimitriou1982two]
for `⊕SAT` and [Valiant 1979][valiant1979complexity] for the transfer: a
parsimonious reduction preserves every property of the count.
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The decision version of a counting problem -/

section Decide

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The decision version of a counting problem** by a property `R` of
numbers: does the count satisfy `R`? -/
def CountingProblem.decide (R : ℕ → Prop) (C : Lax366625.CountingProblems.CountingProblem L) : Lax904597.Problems.DecisionProblem L where
  Holds := fun A inst => R (@Lax366625.CountingProblems.CountingProblem.Count L _ C A inst)
  iso_invariant := fun e => by rw [C.iso_invariant e]

end Decide

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax175070Proofs.DescriptiveComplexity.CountingProblem (decide)

end Lax366625.CountingProblems.CountingProblem

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Decide

variable {L : Language.{0, 0}} [L.IsRelational]

theorem CountingProblem.decide_iff (R : ℕ → Prop) (C : Lax366625.CountingProblems.CountingProblem L) (A : Type)
    [L.Structure A] : C.decide R A ↔ R (C A) :=
  Iff.rfl

end Decide

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax175070Proofs.DescriptiveComplexity.CountingProblem (decide_iff)

end Lax366625.CountingProblems.CountingProblem

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Decide

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The class of the problems defined by the property `R` of one witness
count. -/
noncomputable abbrev countClass₁ (R : ℕ → Prop) : ComplexityClass :=
  countClass (fun _ _ => True) fun c _ => R c

/-- The decision version of a problem of `#P` is in the class of its
property. -/
theorem decide_mem_countClass₁ (R : ℕ → Prop) {C : Lax366625.CountingProblems.CountingProblem L} (hC : C ∈ SharpP) :
    C.decide R ∈ countClass₁ R :=
  mem_countClass_of_sharpP hC hC fun _ _ _ _ => ⟨trivial, Iff.rfl⟩

variable {L' : Language.{0, 0}} [L'.IsRelational]

/-- A relativized parsimonious reduction is a relativized first-order
reduction between the decision versions by any property: equal counts share
every property. -/
def RelOrderedParsimoniousReduction.decide (R : ℕ → Prop) {C : Lax366625.CountingProblems.CountingProblem L}
    {D : Lax366625.CountingProblems.CountingProblem L'} (f : C ≤ʳᵖ[≤] D) : C.decide R ≤ʳᶠᵒ[≤] D.decide R :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toRelInterpretation
    dom_nonempty := f.dom_nonempty
    correct := fun A _ _ _ _ => by
      rw [CountingProblem.decide_iff, CountingProblem.decide_iff, f.correct A] }

end Decide

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction

export Lax175070Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction (decide)

end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Decide

variable {L : Language.{0, 0}} [L.IsRelational]

variable {L' : Language.{0, 0}} [L'.IsRelational]

/-- An ordered parsimonious reduction is an ordered first-order reduction
between the decision versions by any property. -/
def OrderedParsimoniousReduction.decide (R : ℕ → Prop) {C : Lax366625.CountingProblems.CountingProblem L}
    {D : Lax366625.CountingProblems.CountingProblem L'} (f : C ≤ᵖ[≤] D) : C.decide R ≤ᶠᵒ[≤] D.decide R :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => by
      rw [CountingProblem.decide_iff, CountingProblem.decide_iff, f.correct A] }

end Decide

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.OrderedParsimoniousReduction

export Lax175070Proofs.DescriptiveComplexity.OrderedParsimoniousReduction (decide)

end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Decide

variable {L : Language.{0, 0}} [L.IsRelational]

variable {L' : Language.{0, 0}} [L'.IsRelational]

end Decide

/-! ### The decision versions of `#SAT` -/

section Sat

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Every problem defined by a property of one witness count reduces to the
decision version of `#SAT` by that property**: the parsimonious Tseitin
interpretation. -/
noncomputable def CountDefinable.orderedReduction_decide_sharpSat (R : ℕ → Prop)
    {P : Lax904597.Problems.DecisionProblem L} (B : Lax904597.SecondOrder.SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ R (Lax366625.WitnessCounting.witnessCount B φ A)) : P ≤ᶠᵒ[≤] SharpSAT.decide R where
  Tag := SharpTseitinTag B φ
  dim := tseitinDim B φ
  toInterpretation := (sharpTseitinInterp B φ).liftSource (orderCollapse L)
  correct A _ _ _ _ := by
    rw [h A, CountingProblem.decide_iff,
      SharpSAT.iso_invariant ((sharpTseitinInterp B φ).liftSourceLEquiv (orderCollapse L) A),
      sharpSat_sharpTseitin B φ A]

end Sat

end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070.CountDefinability.CountDefinable

export Lax175070Proofs.DescriptiveComplexity.CountDefinable (orderedReduction_decide_sharpSat)

end Lax175070.CountDefinability.CountDefinable

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Sat

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The decision version of `#SAT` by `R` is hard for the class of `R`. -/
theorem decide_sharpSat_countClass₁_hard (R : ℕ → Prop) :
    (countClass₁ R).Hard (SharpSAT.decide R) := by
  rw [hard_countClass_iff]
  rintro L'' _ Q ⟨B, φ, B', φ', hφ⟩
  exact ⟨(CountDefinable.orderedReduction_decide_sharpSat R B φ fun A _ _ _ _ => (hφ A).2).toRel⟩

/-- **The decision version of `#SAT` by `R` is complete for the class of
`R`.** -/
theorem decide_sharpSat_countClass₁_complete (R : ℕ → Prop) :
    (countClass₁ R).Complete (SharpSAT.decide R) :=
  ⟨decide_mem_countClass₁ R sharpSat_mem_sharpP, decide_sharpSat_countClass₁_hard R⟩

/-- **Completeness transfers along parsimonious completeness**: the decision
version by `R` of every parsimoniously `#P`-complete problem is complete for
the class of `R`. -/
theorem countClass₁_complete_of_sharpP_parsimoniousComplete (R : ℕ → Prop)
    {C : Lax366625.CountingProblems.CountingProblem L} (hC : SharpP.ParsimoniousComplete C) :
    (countClass₁ R).Complete (C.decide R) :=
  ⟨decide_mem_countClass₁ R hC.mem,
    (countClass₁ R).hard_of_relOrderedReduction
      (((parsimoniousHard_sharpP_iff C).mp hC.parsimoniousHard SharpSAT
        sharpSat_mem_sharpP).some.decide R)
      (decide_sharpSat_countClass₁_hard R)⟩

end Sat

/-- **The machine characterization of the class of `R`**: a problem is in it
exactly when it reduces to the decision version by `R` of the number of
accepting runs of a nondeterministic machine. -/
theorem mem_countClass₁_iff_le_decide_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational]
    (R : ℕ → Prop) (P : Lax904597.Problems.DecisionProblem L) :
    P ∈ countClass₁ R ↔ Nonempty (P ≤ᶠᵒ[≤] SharpNTMAccept.decide R) := by
  constructor
  · rintro ⟨B, φ, B', φ', hφ⟩
    exact ⟨(CountDefinable.orderedReduction_decide_sharpSat R B φ fun A _ _ _ _ => (hφ A).2).trans
      (SatTM.sharpSat_ordered_parsimonious_sharpNtmAccept.decide R)⟩
  · rintro ⟨f⟩
    exact (countClass₁ R).mem_of_orderedReduction f
      (decide_mem_countClass₁ R sharpNtmAccept_mem_sharpP)

/-! ### ⊕SAT and Mod_k-SAT -/

/-- **⊕SAT**: the number of models of a CNF formula is odd. -/
noncomputable def ParitySAT : Lax904597.Problems.DecisionProblem Lax904597.Sat.sat :=
  SharpSAT.decide Odd

/-- **Mod_k-SAT**: the number of models of a CNF formula is not a multiple of
`k`. -/
noncomputable def ModSAT (k : ℕ) : Lax904597.Problems.DecisionProblem Lax904597.Sat.sat :=
  SharpSAT.decide fun c => ¬ k ∣ c

/-- **⊕SAT is `⊕P`-complete.** -/
theorem paritySat_parityP_complete : ParityP.Complete ParitySAT :=
  decide_sharpSat_countClass₁_complete Odd

/-- **Mod_k-SAT is `Mod_k P`-complete.** -/
theorem modSat_modP_complete (k : ℕ) : (ModP k).Complete (ModSAT k) :=
  decide_sharpSat_countClass₁_complete _

/-- The parity of every parsimoniously `#P`-complete problem is
`⊕P`-complete. -/
theorem parityP_complete_of_sharpP_parsimoniousComplete {L : Language.{0, 0}} [L.IsRelational]
    {C : Lax366625.CountingProblems.CountingProblem L} (hC : SharpP.ParsimoniousComplete C) :
    ParityP.Complete (C.decide Odd) :=
  countClass₁_complete_of_sharpP_parsimoniousComplete Odd hC

/-- **The machine characterization of `⊕P`**: a problem is in `⊕P` exactly
when it reduces to the parity of the number of accepting runs of a
nondeterministic polynomial-time machine. -/
theorem mem_parityP_iff_le_parity_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational]
    (P : Lax904597.Problems.DecisionProblem L) : P ∈ ParityP ↔ Nonempty (P ≤ᶠᵒ[≤] SharpNTMAccept.decide Odd) :=
  mem_countClass₁_iff_le_decide_sharpNtmAccept Odd P

/-- **The machine characterization of `Mod_k P`**. -/
theorem mem_modP_iff_le_mod_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational] (k : ℕ)
    (P : Lax904597.Problems.DecisionProblem L) :
    P ∈ ModP k ↔ Nonempty (P ≤ᶠᵒ[≤] SharpNTMAccept.decide fun c => ¬ k ∣ c) :=
  mem_countClass₁_iff_le_decide_sharpNtmAccept _ P

/-- The residue of every parsimoniously `#P`-complete problem is
`Mod_k P`-complete. -/
theorem modP_complete_of_sharpP_parsimoniousComplete {L : Language.{0, 0}} [L.IsRelational]
    (k : ℕ) {C : Lax366625.CountingProblems.CountingProblem L} (hC : SharpP.ParsimoniousComplete C) :
    (ModP k).Complete (C.decide fun c => ¬ k ∣ c) :=
  countClass₁_complete_of_sharpP_parsimoniousComplete _ hC

end Lax175070Proofs.DescriptiveComplexity


