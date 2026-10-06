/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.FixedPointInflationary
import Lax945089Proofs.DescriptiveComplexity.TransitiveClosure
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax945089.TransitiveClosureReductions
end Lax945089.TransitiveClosureReductions

namespace Lax945089Proofs.DescriptiveComplexity.ParamTCSpec
end Lax945089Proofs.DescriptiveComplexity.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity.TCFamily
end Lax945089Proofs.DescriptiveComplexity.TCFamily

namespace Lax945089Proofs.DescriptiveComplexity.TCSpec
end Lax945089Proofs.DescriptiveComplexity.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.TransitiveClosureReductions (ParamTCSpec TCFamily)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCSpec)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Transitive closures with parameters, as relations a formula may read

`DescriptiveComplexity.TCSpec` defines a *sentence*: a walk on tuples, and the
question whether an accepting node is reachable from a starting one. A
reduction needs more than that – its defining formulas have free variables, so
what they may consult is a **relation**, not an answer. This file provides it:
a `DescriptiveComplexity.ParamTCSpec` is a walk whose step formula may mention
`par` parameters besides its two tuples, and the relation it defines is
reachability itself,

`R[m,m'](x̄, ȳ, z̄)` – “from the node `(m, x̄)` the node `(m', ȳ)` is reachable,
the parameters being `z̄`” –

one relation per ordered pair of modes. A finite family of such walks
(`DescriptiveComplexity.TCFamily`) is a block of relation variables
(`DescriptiveComplexity.TCFamily.block`) whose assignment is fixed, not
guessed: `DescriptiveComplexity.TCFamily.reachAssign`. A structure expanded by
it is what the formulas of an FO(TC) reduction are read over
(`DescriptiveComplexity.TransitiveClosureReduction`).

## Reachability is an inflationary induction

The theorem of this file is
`DescriptiveComplexity.TCFamily.inflLimit_toStepDef`: the reachability
relations of a family are the value of one simultaneous inflationary induction
(`DescriptiveComplexity.TCFamily.toStepDef`), namely the rules

* `R[m,m](x̄, x̄, z̄)`, and
* `R[m,m'](x̄, ȳ, z̄) ← R[m,m''](x̄, ȳ', z̄) ∧ step[m'',m'](ȳ', ȳ, z̄)`.

They are *positive* in the relation variables, so the inflationary iteration
computes the least fixed point, which is `Relation.ReflTransGen` of the step –
the mode pairs being static, each rule is one step formula, and no clausal
apparatus is needed.

That theorem is what makes an FO(TC) reduction an FO(LFP) reduction, and so
what gives the FO(TC) reductions their closure properties without a second
development. It is also the honest statement of where FO(TC) sits: a walk is a
fixed point of a very restricted shape.

## Reading an FO(TC) *sentence* off the relations

`DescriptiveComplexity.TCSpec.acceptsF` turns any existing
`DescriptiveComplexity.TCSpec` into a formula over the expansion by its own
reachability relations: “some accepting node is reachable from some starting
node”, with the walk itself now an atom rather than an operator
(`DescriptiveComplexity.TCSpec.realize_acceptsF`). Every FO(TC) definable
property is thereby available to an FO(TC) reduction as a formula, which is how
`DescriptiveComplexity.EVEN` enters `DescriptiveComplexity.TCReduction`.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Walks with parameters -/

attribute [instance] Lax945089.TransitiveClosureReductions.ParamTCSpec.modeFinite

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L) {A : Type} [L.Structure A]

/-! #### Packing a tuple, two endpoints and the parameters -/

variable {s}

/-- The tuple assembled from two endpoints and a valuation of the
parameters. -/
def pack {V : Type} (x y : Fin s.k → V) (z : Fin s.par → V) : Fin (s.k + s.k + s.par) → V :=
  fun j =>
    if h : (j : ℕ) < s.k then x ⟨j, h⟩
    else if h2 : (j : ℕ) < s.k + s.k then y ⟨(j : ℕ) - s.k, by omega⟩
    else z ⟨(j : ℕ) - (s.k + s.k), by have := j.isLt; omega⟩

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (pack)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L) {A : Type} [L.Structure A]

variable {s}

@[simp]
theorem pack_left {V : Type} (x y : Fin s.k → V) (z : Fin s.par → V) (i : Fin s.k) :
    pack x y z (s.leftIx i) = x i := by
  have hi : ((s.leftIx i : Fin (s.k + s.k + s.par)) : ℕ) < s.k := i.isLt
  simp only [pack]
  rw [dif_pos hi]
  exact congrArg x (Fin.ext rfl)

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (pack_left)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L) {A : Type} [L.Structure A]

variable {s}

@[simp]
theorem pack_right {V : Type} (x y : Fin s.k → V) (z : Fin s.par → V) (i : Fin s.k) :
    pack x y z (s.rightIx i) = y i := by
  have hi := i.isLt
  have h1 : ¬(((s.rightIx i : Fin (s.k + s.k + s.par)) : ℕ) < s.k) := by
    simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.rightIx]; omega
  have h2 : ((s.rightIx i : Fin (s.k + s.k + s.par)) : ℕ) < s.k + s.k := by
    simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.rightIx]; omega
  simp only [pack]
  rw [dif_neg h1, dif_pos h2]
  exact congrArg y (Fin.ext (by simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.rightIx]; omega))

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (pack_right)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L) {A : Type} [L.Structure A]

variable {s}

@[simp]
theorem pack_par {V : Type} (x y : Fin s.k → V) (z : Fin s.par → V) (j : Fin s.par) :
    pack x y z (s.parIx j) = z j := by
  have hj := j.isLt
  have h1 : ¬(((s.parIx j : Fin (s.k + s.k + s.par)) : ℕ) < s.k) := by
    simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.parIx]; omega
  have h2 : ¬(((s.parIx j : Fin (s.k + s.k + s.par)) : ℕ) < s.k + s.k) := by
    simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.parIx]; omega
  simp only [pack]
  rw [dif_neg h1, dif_neg h2]
  exact congrArg z (Fin.ext (by simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.parIx]; omega))

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (pack_par)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L) {A : Type} [L.Structure A]

variable {s}

/-- Post-composing a packed tuple with a function packs the components. -/
theorem pack_comp {V W : Type} (f : V → W) (x y : Fin s.k → V) (z : Fin s.par → V) :
    (fun j => f (pack x y z j)) =
      pack (fun t => f (x t)) (fun t => f (y t)) (fun t => f (z t)) := by
  funext j
  have hj := j.isLt
  rcases Nat.lt_or_ge (j : ℕ) s.k with h | h
  · have hje : j = s.leftIx ⟨j, h⟩ := Fin.ext rfl
    rw [hje, pack_left, pack_left]
  · rcases Nat.lt_or_ge (j : ℕ) (s.k + s.k) with h2 | h2
    · have hje : j = s.rightIx ⟨(j : ℕ) - s.k, by omega⟩ :=
        Fin.ext (by simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.rightIx]; omega)
      rw [hje, pack_right, pack_right]
    · have hje : j = s.parIx ⟨(j : ℕ) - (s.k + s.k), by omega⟩ :=
        Fin.ext (by simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.parIx]; omega)
      rw [hje, pack_par, pack_par]

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (pack_comp)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L) {A : Type} [L.Structure A]

variable {s}

end ParamTCSpec

/-! ### A family of walks, as a block of relation variables -/

attribute [instance] Lax945089.TransitiveClosureReductions.TCFamily.ixFinite

namespace TCFamily

variable {L : Language.{0, 0}} (F : Lax945089.TransitiveClosureReductions.TCFamily L)

variable {F} {A : Type} [L.Structure A]

theorem reachAssign_pack (q : F.block.ι) (x y : Fin (F.spec q.1).k → A)
    (z : Fin (F.spec q.1).par → A) :
    F.reachAssign A q (ParamTCSpec.pack x y z) ↔
      (F.spec q.1).ReachAt z (q.2.1, x) (q.2.2, y) := by
  simp only [Lax945089.TransitiveClosureReductions.TCFamily.reachAssign, ParamTCSpec.pack_left, ParamTCSpec.pack_right,
    ParamTCSpec.pack_par]

end TCFamily

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.TCFamily

export Lax945089Proofs.DescriptiveComplexity.TCFamily (reachAssign_pack)

end Lax945089.TransitiveClosureReductions.TCFamily

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCFamily

variable {L : Language.{0, 0}} (F : Lax945089.TransitiveClosureReductions.TCFamily L)

variable {F} {A : Type} [L.Structure A]

/-! ### The induction that computes reachability -/

section StepFormulas

end StepFormulas

/-! ### Realization of the step formulas -/

section Realize

end Realize

/-! ### The value of the induction is the reachability relations -/

section Limit

end Limit

end TCFamily

/-! ### An FO(TC) sentence, as a formula over the reachability relations -/

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

/-- A `DescriptiveComplexity.TCSpec` read as a parameterized walk with no
parameters, over the ordered expansion its formulas already live in.

Reducible, so that the modes and the arity of the reading are those of the
specification transparently – a node of one *is* a node of the other. -/
@[reducible]
noncomputable def toParam : Lax945089.TransitiveClosureReductions.ParamTCSpec (L₀.sum Language.order) where
  Mode := spec.Mode
  k := spec.k
  par := 0
  step := fun m m' => (spec.step m m').relabel Sum.inl

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (toParam)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

/-- The one-element family of walks of a `DescriptiveComplexity.TCSpec`. -/
@[reducible]
noncomputable def toFamily : Lax945089.TransitiveClosureReductions.TCFamily (L₀.sum Language.order) where
  Ix := Unit
  spec := fun _ => spec.toParam

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (toFamily)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

variable {A : Type} [L₀.Structure A] [LinearOrder A]

theorem stepAt_toParam (z : Fin 0 → A) (a b : spec.Node A) :
    spec.toParam.StepAt z a b ↔ spec.Step a b := by
  simp only [Lax945089.TransitiveClosureReductions.ParamTCSpec.StepAt, Lax485149.TransitiveClosure.TCSpec.Step, toParam, Formula.realize_relabel]
  exact iff_of_eq (congrArg (spec.step a.1 b.1).Realize (funext fun v => rfl))

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (stepAt_toParam)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

variable {A : Type} [L₀.Structure A] [LinearOrder A]

theorem reachAt_toParam (z : Fin 0 → A) (a b : spec.Node A) :
    spec.toParam.ReachAt z a b ↔ spec.Reach a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((spec.stepAt_toParam z c d).mp hcd)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((spec.stepAt_toParam z c d).mpr hcd)

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (reachAt_toParam)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

variable {A : Type} [L₀.Structure A] [LinearOrder A]

/-- The reachability atom of the walk, with both endpoints quantified. -/
noncomputable def reachAtomAcc (p : spec.Mode × spec.Mode) :
    ((L₀.sum Language.order).sum spec.toFamily.block.lang).Formula
      (Empty ⊕ (Fin spec.k ⊕ Fin spec.k)) :=
  Relations.formula (varInSym (L₀.sum Language.order) spec.toFamily.block ⟨(), p⟩) fun j =>
    Term.var (ParamTCSpec.pack (V := Empty ⊕ (Fin spec.k ⊕ Fin spec.k))
      (fun t => Sum.inr (Sum.inl t)) (fun t => Sum.inr (Sum.inr t)) Fin.elim0 j)

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (reachAtomAcc)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

variable {A : Type} [L₀.Structure A] [LinearOrder A]

theorem realize_reachAtomAcc (p : spec.Mode × spec.Mode)
    (v : (Empty ⊕ (Fin spec.k ⊕ Fin spec.k)) → A) :
    (@Formula.Realize _ A
      (spec.toFamily.block.structure₁ (L := L₀.sum Language.order)
        (spec.toFamily.reachAssign A)) _ (spec.reachAtomAcc p) v) ↔
      spec.Reach (p.1, fun t => v (Sum.inr (Sum.inl t)))
        (p.2, fun t => v (Sum.inr (Sum.inr t))) := by
  let := spec.toFamily.block.structure₁ (L := L₀.sum Language.order) (spec.toFamily.reachAssign A)
  rw [reachAtomAcc, Formula.realize_rel]
  refine Iff.trans (iff_of_eq (congrArg (spec.toFamily.reachAssign A ⟨(), p⟩)
    (ParamTCSpec.pack_comp (s := spec.toParam) v _ _ _))) ?_
  refine Iff.trans (TCFamily.reachAssign_pack (F := spec.toFamily) ⟨(), p⟩ _ _ _) ?_
  exact spec.reachAt_toParam _ _ _

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (realize_reachAtomAcc)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

variable {A : Type} [L₀.Structure A] [LinearOrder A]

open Classical in
/-- **The walk as an atom**: “some accepting node is reachable from some
starting node”, written over the vocabulary expanded by the walk's own
reachability relations. This is what makes every FO(TC) definable property
available to an FO(TC) reduction. -/
noncomputable def acceptsF :
    ((L₀.sum Language.order).sum spec.toFamily.block.lang).Sentence :=
  Formula.iSup fun p : spec.Mode × spec.Mode =>
    Formula.iExs (Fin spec.k ⊕ Fin spec.k)
      (((LHom.sumInl.onFormula (spec.src p.1)).relabel fun t => Sum.inr (Sum.inl t)) ⊓
        spec.reachAtomAcc p ⊓
        ((LHom.sumInl.onFormula (spec.tgt p.2)).relabel fun t => Sum.inr (Sum.inr t)))

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (acceptsF)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

variable {A : Type} [L₀.Structure A] [LinearOrder A]

/-- **The walk-as-an-atom formula says acceptance**, when the relation
variables hold the reachability relations they are meant to. -/
theorem realize_acceptsF :
    (@Sentence.Realize _ A
      (spec.toFamily.block.structure₁ (L := L₀.sum Language.order)
        (spec.toFamily.reachAssign A)) spec.acceptsF) ↔ spec.Accepts A := by
  classical
  let := spec.toFamily.block.structure₁ (L := L₀.sum Language.order)
    (spec.toFamily.reachAssign A)
  rw [Sentence.Realize, acceptsF, Formula.realize_iSup]
  constructor
  · rintro ⟨p, hp⟩
    rw [Formula.realize_iExs] at hp
    obtain ⟨v, hv⟩ := hp
    rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_relabel,
      Formula.realize_relabel, LHom.realize_onFormula, LHom.realize_onFormula,
      spec.realize_reachAtomAcc p] at hv
    exact ⟨(p.1, fun t => v (Sum.inl t)), (p.2, fun t => v (Sum.inr t)),
      hv.1.1, hv.2, hv.1.2⟩
  · rintro ⟨u, w, hu, hw, huw⟩
    refine ⟨(u.1, w.1), ?_⟩
    rw [Formula.realize_iExs]
    refine ⟨Sum.elim u.2 w.2, ?_⟩
    rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_relabel,
      Formula.realize_relabel, LHom.realize_onFormula, LHom.realize_onFormula,
      spec.realize_reachAtomAcc (u.1, w.1)]
    exact ⟨⟨hu, huw⟩, hw⟩

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (realize_acceptsF)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀)

variable {A : Type} [L₀.Structure A] [LinearOrder A]

end TCSpec

end Lax945089Proofs.DescriptiveComplexity


