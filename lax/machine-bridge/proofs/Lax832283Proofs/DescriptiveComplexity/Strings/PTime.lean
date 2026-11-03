/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax832283Proofs.DescriptiveComplexity.FixedPointHorn
import Lax832283Proofs.DescriptiveComplexity.FixedPointInflationaryLFP
import Lax832283Proofs.DescriptiveComplexity.Strings.FixedPointForward
import Lax832283Proofs.DescriptiveComplexity.Strings.FixedPointBackward
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.Captures
import Mathlib.Order.Fin.Basic
import Lax832283Proofs.DescriptiveComplexity.FixedPointInflationary
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
import Lax751879.FixedPointSemantics
import Lax751879.FixedPointSyntax
import Lax751879.LeastFixedPoints
import Lax751879.OrderedStructures
import Lax751879.PolynomialTime
import Lax751879.StructureEncoding
import Lax832283.StringProblems
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax988886.ExistentialSecondOrder
import Lax988886.FiniteStructures
import Lax988886.NondeterministicPolynomialTime

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax751879.FixedPointSemantics
end Lax751879.FixedPointSemantics

namespace Lax751879.PolynomialTime
end Lax751879.PolynomialTime

namespace Lax832283.StringProblems
end Lax832283.StringProblems

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics
export Lax751879.FixedPointSemantics (Definable)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime
export Lax751879.PolynomialTime (InP)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime

namespace Lax832283Proofs.DescriptiveComplexity.Strings
export Lax832283.StringProblems (FinVocab ofOrdered toQuery)
end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax832283Proofs.DescriptiveComplexity

namespace Lax832283Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax832283Proofs.DescriptiveComplexity

namespace Lax832283Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable)
end Lax832283Proofs.DescriptiveComplexity

/-!
# The class PTIME, against a polynomial-time machine

The class `DescriptiveComplexity.PTIME` of this library is defined by second-order
Horn logic, and equals FO(LFP) and FO(IFP). The theorems of this file say that, over a
vocabulary with finitely many relation symbols, it is the textbook class: a problem
belongs to it exactly when a polynomial-time Mathlib `Turing.FinTM2` decides the language
of the binary encodings of its yes-instances.

The logical half, `DescriptiveComplexity.Strings.mem_PTIME_iff_definable`, is
unconditional, and is the substance of the two files
`DescriptiveComplexity.Strings.FixedPointForward` (Bekić's principle) and
`DescriptiveComplexity.Strings.FixedPointBackward` (nested and negated fixed points). The
machine half takes the Immerman–Vardi theorem as a hypothesis
(`DescriptiveComplexity.Strings.Lax.ImmermanVardiCaptures`), which the Lax archive registers
as `lax-751879`.

A problem of the library is order-invariant, and its query is read on `Fin n` with the
usual order; so the ordered definability of the library, which quantifies over every linear
order of the universe, becomes the definability on the canonical representatives.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder Language Structure

open Lax.OrderedStructures Lax.FixedPointSemantics Lax.PolynomialTime

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The round trip, as an isomorphism of the ordered expansions, along an order
isomorphism. -/
noncomputable def ofOrderedOrdEquiv (V : Lax832283.StringProblems.FinVocab L) (A : Type) [L.Structure A] [LinearOrder A]
    {n : ℕ} (e : A ≃o Fin n) :
    @Language.Equiv (L.sum Language.order) A (Fin n) _
      (@Lax904597.Interpretations.sumOrderStructure L (Fin n) (Lax832283.StringProblems.ofOrdered V (toOrdered V A e.toEquiv)) _) :=
  letI : L.Structure (Fin n) := Lax832283.StringProblems.ofOrdered V (toOrdered V A e.toEquiv)
  { toEquiv := e.toEquiv
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {m} R x => by
      rcases R with R | R
      · exact (ofOrderedEquiv V A e.toEquiv).map_rel' R x
      · cases R
        exact e.le_iff_le }

/-- **A query of the archive's FO(LFP) reads as a definition in FO(IFP).** -/
theorem definable_imp_ifpDefinable (V : Lax832283.StringProblems.FinVocab L) {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax751879.FixedPointSemantics.Definable (Lax832283.StringProblems.toQuery V P)) : Lax535992.InflationaryFixedPoint.IFPDefinable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨sentenceDef V φ.1, ?_⟩
  intro A _ _ _ _
  let := Fintype.ofFinite A
  let e : A ≃o Fin (Fintype.card A) := (Fintype.orderIsoFinOfCardEq A rfl).symm
  let S := toOrdered V A e.toEquiv
  have hS : 0 < S.size := Fintype.card_pos
  have h₁ : P A ↔ Lax832283.StringProblems.toQuery V P ⟨S, Fin.elim0⟩ := (toProperty_toOrdered V P A e.toEquiv).symm
  refine h₁.trans ((hφ _).trans ?_)
  have h₂ := @StepDef.ifpHolds_equiv (L.sum Language.order) (sentenceDef V φ.1) A
    (Fin (Fintype.card A)) _ (@Lax904597.Interpretations.sumOrderStructure L _ (Lax832283.StringProblems.ofOrdered V S) _) (ofOrderedOrdEquiv V A e)
  exact (sentenceDef_holds V S hS φ).symm.trans h₂.symm

/-- **`PTIME`, logically**: a problem is in `PTIME` exactly when it reads as a query
defined by a formula of the archive's FO(LFP). -/
theorem mem_PTIME_iff_definable (V : Lax832283.StringProblems.FinVocab L) (P : Lax904597.Problems.DecisionProblem L) :
    P ∈ PTIME ↔ Lax751879.FixedPointSemantics.Definable (Lax832283.StringProblems.toQuery V P) :=
  ⟨fun h => lfpDefinable_imp_definable V ((lfpDefinable_iff_mem_PTIME P).mpr h),
    fun h => (ifpDefinable_iff_mem_PTIME P).mp (definable_imp_ifpDefinable V h)⟩

end Lax832283Proofs.DescriptiveComplexity.Strings


