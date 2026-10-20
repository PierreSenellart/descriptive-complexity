/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Machines
import Lax822549Proofs.DescriptiveComplexity.Interpretation
import Lax822549Proofs.DescriptiveComplexity.Exponential.AddrExp
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace FirstOrder.Language
export Lax822549.WideMachines (wide wideRel wmAcc wmBlank wmDst wmInp wmLe wmRead wmRight wmSrc wmStart wmTr wmWrite)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMDown WMDst WMInp WMLe WMRead WMRight WMSetLe WMSrc WMStart WMTr WMWrite WPoint wideData wpAttr wpInp wpLe wpMark wpPosn)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (TMData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

/-!
# The wide machine: a machine addressed by the subsets of its instance

The machine model of the exponential classes. A `DescriptiveComplexity.TMData`
read over the instance itself is a machine with polynomially many cells, and the
library's bounds are unary by construction, so `DescriptiveComplexity.NTMAccept`
lands in NP and `DescriptiveComplexity.NTMAcceptSpace` in PSPACE. The **wide
machine** is the same model with one exponent added *in the semantics of the
problem*, and nowhere else:

> its tape is addressed by the **subsets** of the instance, while its control –
> the transitions, the states, the symbols – stays an ordinary part of the
> instance.

So an instance of size `n` describes a machine with `2^n` cells and `2^n` time
steps, and the two resource variants land one exponential up:
`DescriptiveComplexity.WideAccept` in NEXPTIME and
`DescriptiveComplexity.WideAcceptSpace` in EXPSPACE
(`DescriptiveComplexity.Problems.Wide.Membership`). A reduction of dimension `d`
buys itself `2^(nᵈ)` cells exactly as a reduction into
`DescriptiveComplexity.NTMAccept` buys itself `nᵈ`.

## The universe of the machine

The machine runs over `DescriptiveComplexity.WPoint`, the disjoint union of

* the **addresses** `A → Prop` – the subsets of the instance, which are the tape
  cells and equally the time steps; and
* the **control elements**, the elements of the instance themselves, which are
  its states, its symbols and its transitions.

That is exactly the universe an exponential expansion of the instance has, with
one tag for each summand (`DescriptiveComplexity.Problems.Wide.Expansion`), and
it is why the membership proofs are the composition `NTMAccept ∘ expansion`
rather than an argument about resources.

## Where the order comes from

`DescriptiveComplexity.TMData` needs a linear order on its universe, and a
decision problem may not read the ambient order of its instance. So the
instance carries its own order `wmLe`, and the order on addresses is the
**binary-number order** it induces: one subset is below another when, at the
`wmLe`-least element where they differ, the second contains it and the first
does not (`DescriptiveComplexity.WMSetLe`). Addresses come below control
elements, so the least *position* is the empty address. That the resulting
relation is linear is a promise, folded into the yes-instances through
`DescriptiveComplexity.TMData.WellFormed` exactly as for
`DescriptiveComplexity.NTMAccept`.

## Where the input goes

The initial tape is described by the binary symbol `wmInp` of the instance, read
at the **initial-segment addresses**: the address `{y | y ≤ x}` holds the input
symbol of `x`, and every other address – including the empty one, where the head
starts – holds the blank. Initial segments are ordered like the elements they
come from, so the input appears along the tape in the instance's own order, and
the whole of it is first-order describable over the instance, which is what the
expansion needs.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax822549.WideMachines.wide.Structure A]

end Shorthands

/-! ### The universe and the machine -/

section Machine

variable (A : Type)

variable {A} [Lax822549.WideMachines.wide.Structure A]

end Machine

/-! ### Isomorphism-invariance -/

section Transport

variable {A B : Type} [Lax822549.WideMachines.wide.Structure A] [Lax822549.WideMachines.wide.Structure B]

/-- **An isomorphism of instances is a bijection of the machines' universes**:
addresses transport by taking preimages, control elements by the isomorphism
itself. -/
def wpointEquiv (e : A ≃[Lax822549.WideMachines.wide] B) : Lax822549.WideMachines.WPoint A ≃ Lax822549.WideMachines.WPoint B where
  toFun := Sum.map (fun s y => s (e.toEquiv.symm y)) e.toEquiv
  invFun := Sum.map (fun t x => t (e.toEquiv x)) e.toEquiv.symm
  left_inv := by
    rintro (s | x)
    · exact congrArg Sum.inl (funext fun x =>
        congrArg s (e.toEquiv.symm_apply_apply x))
    · exact congrArg Sum.inr (e.toEquiv.symm_apply_apply x)
  right_inv := by
    rintro (t | y)
    · exact congrArg Sum.inl (funext fun y => congrArg t (e.toEquiv.apply_symm_apply y))
    · exact congrArg Sum.inr (e.toEquiv.apply_symm_apply y)

@[simp]
theorem wpointEquiv_addr (e : A ≃[Lax822549.WideMachines.wide] B) (s : A → Prop) :
    wpointEquiv e (Sum.inl s) = Sum.inl fun y => s (e.symm y) :=
  rfl

@[simp]
theorem wpointEquiv_ctrl (e : A ≃[Lax822549.WideMachines.wide] B) (x : A) :
    wpointEquiv e (Sum.inr x) = Sum.inr (e x) :=
  rfl

/-- **An isomorphism makes the two wide machines agree**, fieldwise: every
symbol of the vocabulary transports, and the two derived notions – the order on
addresses and the initial segment of an element – transport by
`DescriptiveComplexity.wmSetLe_congr` and
`DescriptiveComplexity.wmDown_congr`. -/
theorem wideData_agree (e : A ≃[Lax822549.WideMachines.wide] B) :
    TMData.Agree (wpointEquiv e) (Lax822549.WideMachines.wideData A) (Lax822549.WideMachines.wideData B) := by
  have hle : ∀ x y : A, Lax822549.WideMachines.WMLe x y ↔ Lax822549.WideMachines.WMLe (e x) (e y) := fun x y =>
    relMap_equiv₂ e Lax822549.WideMachines.wmLe x y
  have hmark : ∀ (r : Lax822549.WideMachines.wide.Relations 1) (x : A),
      (RelMap r ![x] : Prop) ↔ RelMap r ![(e x : B)] := fun r x => relMap_equiv₁ e r x
  have hattr : ∀ (r : Lax822549.WideMachines.wide.Relations 2) (x y : A),
      (RelMap r ![x, y] : Prop) ↔ RelMap r ![(e x : B), (e y : B)] := fun r x y =>
    relMap_equiv₂ e r x y
  refine ⟨?_, ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro (s | x) <;> exact Iff.rfl
  · rintro (s | x) <;> rintro (t | y)
    · exact wmSetLe_congr e.toEquiv hle s t
    · exact Iff.rfl
    · exact Iff.rfl
    · exact hle x y
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark Lax822549.WideMachines.wmTr x
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark Lax822549.WideMachines.wmStart x
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark Lax822549.WideMachines.wmAcc x
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark Lax822549.WideMachines.wmBlank x
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark Lax822549.WideMachines.wmRight x
  · rintro (s | x) <;> rintro (t | y) <;> first
      | exact Iff.rfl
      | exact hattr Lax822549.WideMachines.wmSrc x y
  · rintro (s | x) <;> rintro (t | y) <;> first
      | exact Iff.rfl
      | exact hattr Lax822549.WideMachines.wmRead x y
  · rintro (s | x) <;> rintro (t | y) <;> first
      | exact Iff.rfl
      | exact hattr Lax822549.WideMachines.wmDst x y
  · rintro (s | x) <;> rintro (t | y) <;> first
      | exact Iff.rfl
      | exact hattr Lax822549.WideMachines.wmWrite x y
  · rintro (s | x) <;> rintro (t | y) <;> try exact Iff.rfl
    constructor
    · rintro ⟨z, hd, hi⟩
      exact ⟨e.toEquiv z, (wmDown_congr e.toEquiv hle s z).mp hd, (hattr Lax822549.WideMachines.wmInp z y).mp hi⟩
    · rintro ⟨z, hd, hi⟩
      have hinp : ∀ x y : A, Lax822549.WideMachines.WMInp x y ↔ Lax822549.WideMachines.WMInp (e.toEquiv x) (e.toEquiv y) := fun x y =>
        relMap_equiv₂ e Lax822549.WideMachines.wmInp x y
      refine ⟨e.toEquiv.symm z, ?_, (hinp _ y).mpr ?_⟩
      · rw [wmDown_congr e.toEquiv hle, Equiv.apply_symm_apply]
        exact hd
      · rw [Equiv.apply_symm_apply]
        exact hi

end Transport

/-! ### The problems -/

section Problems

/-- **Wide machine acceptance.** Does the machine described by the instance –
its tape addressed by the *subsets* of the instance – accept its input within as
many steps as there are addresses? The well-formedness promises of
`DescriptiveComplexity.TMData.WellFormed` are folded into the yes-instances, as
for `DescriptiveComplexity.NTMAccept`; here they amount to the instance's order
being linear, its input functional and its blank unique. -/
def WideAccept : Lax904597.Problems.DecisionProblem Lax822549.WideMachines.wide where
  Holds := fun A _ => (Lax822549.WideMachines.wideData A).WellFormed ∧ (Lax822549.WideMachines.wideData A).Accepts
  iso_invariant := fun {A B} _ _ e => by
    have h := wideData_agree e
    exact and_congr h.wellFormed h.accepts

/-- **Wide machine acceptance in bounded space**: the same question with the
step bound dropped. The space is still bounded by construction – the tape is
indexed by the addresses – but a run may now visit doubly exponentially many
configurations. -/
def WideAcceptSpace : Lax904597.Problems.DecisionProblem Lax822549.WideMachines.wide where
  Holds := fun A _ => (Lax822549.WideMachines.wideData A).WellFormed ∧ (Lax822549.WideMachines.wideData A).AcceptsSpace
  iso_invariant := fun {A B} _ _ e => by
    have h := wideData_agree e
    exact and_congr h.wellFormed h.acceptsSpace

/-- **Deterministic wide machine acceptance in bounded space**, with determinism
folded into the yes-instances as in `DescriptiveComplexity.DTMAcceptSpace`. -/
def DWideAcceptSpace : Lax904597.Problems.DecisionProblem Lax822549.WideMachines.wide where
  Holds := fun A _ => (Lax822549.WideMachines.wideData A).WellFormed ∧ (Lax822549.WideMachines.wideData A).Deterministic ∧
    (Lax822549.WideMachines.wideData A).AcceptsSpace
  iso_invariant := fun {A B} _ _ e => by
    have h := wideData_agree e
    exact and_congr h.wellFormed (and_congr h.deterministic h.acceptsSpace)

end Problems

end Lax822549Proofs.DescriptiveComplexity


