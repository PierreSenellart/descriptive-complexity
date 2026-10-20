/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.OrderedComposition
import Lax366625Proofs.DescriptiveComplexity.Numbers.BinRel
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

namespace Lax366625Proofs.DescriptiveComplexity.FOInterpretation
end Lax366625Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation sumOrderStructure)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax366625Proofs.DescriptiveComplexity

/-!
# Replacing the order of an ordered structure by a definable one

An ordered reduction is correct for *every* linear order of its input, which
it has no say over. What it may do is replace that order, before anything
else, by any linear order it can define: `DescriptiveComplexity.FOInterpretation.reorder`
is the one-dimensional interpretation of the ordered expansion in itself that
keeps every symbol and interprets the order symbol by a given formula, and
`DescriptiveComplexity.FOInterpretation.reorderLEquiv` says that, when the
formula defines a linear order `ord'` of the structure, the interpreted
structure is the input structure ordered by `ord'`.

This is how a reduction into a problem that reads its output in the order of
the universe – the tape order of `DescriptiveComplexity.DTMNumber` – can be
composed after one that produces the order of significance as a relation of
the instance: the second reduction reorders its input so that the two agree.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Reordering**: the identity interpretation of the ordered expansion in
itself, with the order symbol interpreted by the formula `φ` (its two free
variables being the two arguments). -/
noncomputable def FOInterpretation.reorder (φ : (L.sum Language.order).Formula (Fin 2 × Fin 1)) :
    Lax904597.Interpretations.FOInterpretation (L.sum Language.order) (L.sum Language.order) Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl r => fun _ => Relations.formula (Sum.inl r) fun i => Term.var (i, 0)
    | _, Sum.inr .le => fun _ => φ

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax366625Proofs.DescriptiveComplexity.FOInterpretation (reorder)

end Lax904597.Interpretations.FOInterpretation

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable (φ : (L.sum Language.order).Formula (Fin 2 × Fin 1))

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- When `φ` defines a relation `Le'` that is a linear order, the reordered
structure is the input structure ordered by `Le'`
(`DescriptiveComplexity.IsLinOrd.toLinearOrder`). The new order is passed as
a relation rather than as a `LinearOrder` so that it does not shadow the
order of the input in the statement. -/
noncomputable def FOInterpretation.reorderLEquiv {Le' : A → A → Prop} (h : Lax904597.Machines.IsLinOrd Le')
    (hφ : ∀ v : Fin 2 × Fin 1 → A, φ.Realize v ↔ Le' (v (0, 0)) (v (1, 0))) :
    @Language.Equiv (L.sum Language.order) ((FOInterpretation.reorder φ).Map A) A
      (Lax904597.Interpretations.FOInterpretation.mapStructure (FOInterpretation.reorder φ) A)
      (letI := h.toLinearOrder; Lax904597.Interpretations.sumOrderStructure L A) :=
  @Language.Equiv.mk (L.sum Language.order) _ A
    (Lax904597.Interpretations.FOInterpretation.mapStructure (FOInterpretation.reorder φ) A)
    (letI := h.toLinearOrder; Lax904597.Interpretations.sumOrderStructure L A)
    { toFun := fun x => x.2 0
      invFun := fun a => ((), fun _ => a)
      left_inv := fun x =>
        Prod.ext_iff.mpr ⟨rfl, funext fun j => congrArg x.2 (Subsingleton.elim 0 j)⟩
      right_inv := fun _ => rfl }
    (fun f => isEmptyElim f)
    fun {n} R x => by
      cases R with
      | inl r => exact Iff.rfl
      | inr r =>
        cases r with
        | le =>
          change Le' _ _ ↔ ((FOInterpretation.reorder φ).relFormula (Sum.inr .le)
            fun i => (x i).1).Realize fun p => (x p.1).2 p.2
          exact (hφ fun p => (x p.1).2 p.2).symm

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax366625Proofs.DescriptiveComplexity.FOInterpretation (reorderLEquiv)

end Lax904597.Interpretations.FOInterpretation

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable (φ : (L.sum Language.order).Formula (Fin 2 × Fin 1))

variable (A : Type) [L.Structure A] [LinearOrder A]

end Lax366625Proofs.DescriptiveComplexity


