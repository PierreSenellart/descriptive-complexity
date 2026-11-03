/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointHorn
import DescriptiveComplexity.FixedPointInflationaryLFP
import DescriptiveComplexity.Strings.FixedPointForward
import DescriptiveComplexity.Strings.FixedPointBackward
import DescriptiveComplexity.Strings.Lax.Captures
import Mathlib.Order.Fin.Basic
import DescriptiveComplexity.FixedPointInflationary

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

namespace DescriptiveComplexity.Strings

open FirstOrder Language Structure
open Lax.OrderedStructures Lax.FixedPointSemantics Lax.PolynomialTime

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The round trip, as an isomorphism of the ordered expansions, along an order
isomorphism. -/
noncomputable def ofOrderedOrdEquiv (V : FinVocab L) (A : Type) [L.Structure A] [LinearOrder A]
    {n : ℕ} (e : A ≃o Fin n) :
    @Language.Equiv (L.sum Language.order) A (Fin n) _
      (@sumOrderStructure L (Fin n) (ofOrdered V (toOrdered V A e.toEquiv)) _) :=
  letI : L.Structure (Fin n) := ofOrdered V (toOrdered V A e.toEquiv)
  { toEquiv := e.toEquiv
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {m} R x => by
      rcases R with R | R
      · exact (ofOrderedEquiv V A e.toEquiv).map_rel' R x
      · cases R
        exact e.le_iff_le }

/-- **A query of the archive's FO(LFP) reads as a definition in FO(IFP).** -/
theorem definable_imp_ifpDefinable (V : FinVocab L) {P : DecisionProblem L}
    (h : Definable (toQuery V P)) : IFPDefinable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨sentenceDef V φ.1, ?_⟩
  intro A _ _ _ _
  let := Fintype.ofFinite A
  let e : A ≃o Fin (Fintype.card A) := (Fintype.orderIsoFinOfCardEq A rfl).symm
  let S := toOrdered V A e.toEquiv
  have hS : 0 < S.size := Fintype.card_pos
  have h₁ : P A ↔ toQuery V P ⟨S, Fin.elim0⟩ := (toProperty_toOrdered V P A e.toEquiv).symm
  refine h₁.trans ((hφ _).trans ?_)
  have h₂ := @StepDef.ifpHolds_equiv (L.sum Language.order) (sentenceDef V φ.1) A
    (Fin (Fintype.card A)) _ (@sumOrderStructure L _ (ofOrdered V S) _) (ofOrderedOrdEquiv V A e)
  exact (sentenceDef_holds V S hS φ).symm.trans h₂.symm

/-- **`PTIME`, logically**: a problem is in `PTIME` exactly when it reads as a query
defined by a formula of the archive's FO(LFP). -/
theorem mem_PTIME_iff_definable (V : FinVocab L) (P : DecisionProblem L) :
    P ∈ PTIME ↔ Definable (toQuery V P) :=
  ⟨fun h => lfpDefinable_imp_definable V ((lfpDefinable_iff_mem_PTIME P).mpr h),
    fun h => (ifpDefinable_iff_mem_PTIME P).mp (definable_imp_ifpDefinable V h)⟩

/-- **`PTIME` is the textbook class**: from the Immerman–Vardi theorem, a problem is in
`PTIME` exactly when a polynomial-time machine decides the language of the binary encodings
of its yes-instances. -/
theorem mem_PTIME_iff_inP (h : Lax.ImmermanVardiCaptures) (V : FinVocab L)
    (P : DecisionProblem L) :
    P ∈ PTIME ↔ InP (toQuery V P) :=
  (mem_PTIME_iff_definable V P).trans (h _)

end DescriptiveComplexity.Strings
