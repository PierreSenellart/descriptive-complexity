/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.FixedPointPartial
import Lax822549Proofs.DescriptiveComplexity.PSpace
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

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.PFPDefinable
end Lax822549Proofs.DescriptiveComplexity.PFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity.SOBlock
end Lax822549Proofs.DescriptiveComplexity.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.StepDef
end Lax822549Proofs.DescriptiveComplexity.StepDef

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (PFPDefinable)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (PFPHolds partStage)
end Lax535992.InflationaryFixedPoint.StepDef

/-!
# FO(≤, PFP) is contained in SO(TC)

The easy half of the capture theorem FO(≤, PFP) = PSPACE ([Abiteboul–Vianu
1989][abiteboul1989fixpoint]; [Ebbinghaus–Flum 1995][ebbinghaus1995finite],
ch. 7): a partial fixed-point iteration *is* a deterministic walk on the
state space SO(TC) walks on – the assignments of the block – so a
`DescriptiveComplexity.StepDef` read partially translates into a
`DescriptiveComplexity.SOTCSpec` verbatim
(`DescriptiveComplexity.StepDef.toSOTCSpec`):

* the walk's states are the assignments of the same block;
* its transition sentence says «the second copy is one application of the
  step formulas to the first» (`DescriptiveComplexity.StepDef.nextSentence`);
* its source is the empty assignment
  (`DescriptiveComplexity.StepDef.botSentence`);
* its target says «the state is a fixed point of the step, and the output
  holds» (`DescriptiveComplexity.StepDef.isFixedPtF`, conjoined with the
  output).

The states reachable from the source along the deterministic transition are
exactly the partial stages, so acceptance is
`DescriptiveComplexity.StepDef.PFPHolds`
(`DescriptiveComplexity.StepDef.accepts_toSOTCSpec`) – with **no divergence
detection**: under the convergence-requiring semantics of
`DescriptiveComplexity.FixedPointPartial`, a diverging iteration simply
reaches no target state. This is what the divergence convention buys; the
textbook convention would need a step counter to make divergence positively
detectable, and a counter is the one thing this translation would otherwise
need the order for.

Whence FO(≤, PFP) ⊆ PSPACE: `DescriptiveComplexity.PFPDefinable.sotcDefinable`
and `DescriptiveComplexity.mem_PSPACE_of_pfpDefinable`. The converse
inclusion – PSPACE ⊆ FO(≤, PFP), completing the capture – iterates the
PSPACE-complete deterministic machine problem and is built in
`DescriptiveComplexity.FixedPointPartialMachine`.

`DescriptiveComplexity.StepDef.isFixedPtF` is also the guard that reads a
definition of this library in the textbook divergence convention – see the
divergence discussion in `DescriptiveComplexity.FixedPointPartial`.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

/-! ### Enumerating the variables of a block -/

open Classical in
/-- The relation variables of a block, as a list: the sentences below conjoin
one clause per variable. -/
noncomputable def SOBlock.idxList (B : Lax904597.SecondOrder.SOBlock) : List B.ι :=
  letI : Fintype B.ι := Fintype.ofFinite B.ι
  (Finset.univ : Finset B.ι).toList

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (idxList)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

open Classical in
theorem SOBlock.mem_idxList (B : Lax904597.SecondOrder.SOBlock) (i : B.ι) : i ∈ B.idxList := by
  let : Fintype B.ι := Fintype.ofFinite B.ι
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (mem_idxList)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

/-! ### The three sentences of the walk -/

/-- The atom of a block variable in the *second* copy of the block, over two
copies. -/
abbrev newVarSym (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) (i : B.ι) :
    ((L.sum B.lang).sum B.lang).Relations (B.arity i) :=
  Sum.inr (varSym B i)

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (newVarSym)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

/-- «The second copy of the block is one application of the step formulas to
the first»: the transition sentence of the walk. -/
noncomputable def nextSentence : ((L.sum d.B.lang).sum d.B.lang).Sentence :=
  listInf (d.B.idxList.map fun i =>
    Formula.iAlls (Fin (d.B.arity i))
      (((Relations.formula (newVarSym L d.B i) fun j => Term.var (Sum.inr j)).iff
          ((LHom.sumInl.onFormula (d.step i)).relabel Sum.inr) :
        ((L.sum d.B.lang).sum d.B.lang).Formula (Empty ⊕ Fin (d.B.arity i)))))

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (nextSentence)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

/-- «Every relation of the block is empty»: the source sentence of the
walk. -/
noncomputable def botSentence : (L.sum d.B.lang).Sentence :=
  listInf (d.B.idxList.map fun i =>
    Formula.iAlls (Fin (d.B.arity i))
      ((∼(Relations.formula (varInSym L d.B i) fun j => Term.var (Sum.inr j)) :
        (L.sum d.B.lang).Formula (Empty ⊕ Fin (d.B.arity i)))))

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (botSentence)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

/-- «The state is a fixed point of the step formulas», as a sentence over one
copy of the block. Also the guard that transfers a definition between the two
divergence conventions – see `DescriptiveComplexity.FixedPointPartial`. -/
noncomputable def isFixedPtF : (L.sum d.B.lang).Sentence :=
  listInf (d.B.idxList.map fun i =>
    Formula.iAlls (Fin (d.B.arity i))
      (((Relations.formula (varInSym L d.B i) fun j => Term.var (Sum.inr j)).iff
          ((d.step i).relabel Sum.inr) :
        (L.sum d.B.lang).Formula (Empty ⊕ Fin (d.B.arity i)))))

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (isFixedPtF)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

/-! ### Their semantics -/

section Realize

variable {A : Type} [L.Structure A]

theorem realize_nextSentence (ρ σ : d.B.Assignment A) :
    (@Sentence.Realize _ A (d.B.structure₂ (L := L) ρ σ) d.nextSentence) ↔
      σ = d.next ρ := by
  let := d.B.structure σ
  let := d.B.structure₁ (L := L) ρ
  rw [nextSentence]
  simp only [Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i x
    have hi := h _ (List.mem_map_of_mem (d.B.mem_idxList i))
    rw [Formula.realize_iAlls] at hi
    have hx := hi x
    rw [Formula.realize_iff, Formula.realize_rel, Formula.realize_relabel,
      LHom.realize_onFormula] at hx
    exact propext hx
  · rintro rfl ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_iAlls]
    intro x
    rw [Formula.realize_iff, Formula.realize_rel, Formula.realize_relabel,
      LHom.realize_onFormula]
    exact Iff.rfl

end Realize

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (realize_nextSentence)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Realize

variable {A : Type} [L.Structure A]

theorem realize_botSentence (ρ : d.B.Assignment A) :
    (@Sentence.Realize _ A (d.B.structure₁ (L := L) ρ) d.botSentence) ↔
      ρ = d.B.botAssign A := by
  let := d.B.structure ρ
  rw [botSentence]
  simp only [Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i x
    have hi := h _ (List.mem_map_of_mem (d.B.mem_idxList i))
    rw [Formula.realize_iAlls] at hi
    have hx := hi x
    rw [Formula.realize_not, Formula.realize_rel] at hx
    exact propext (iff_false_intro hx)
  · rintro rfl ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_iAlls]
    intro x
    rw [Formula.realize_not, Formula.realize_rel]
    exact fun h => h

end Realize

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (realize_botSentence)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Realize

variable {A : Type} [L.Structure A]

theorem realize_isFixedPtF (ρ : d.B.Assignment A) :
    (@Sentence.Realize _ A (d.B.structure₁ (L := L) ρ) d.isFixedPtF) ↔
      IsFixedPt d.next ρ := by
  let := d.B.structure ρ
  rw [isFixedPtF]
  simp only [Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i x
    have hi := h _ (List.mem_map_of_mem (d.B.mem_idxList i))
    rw [Formula.realize_iAlls] at hi
    have hx := hi x
    rw [Formula.realize_iff, Formula.realize_rel, Formula.realize_relabel] at hx
    exact propext hx.symm
  · rintro hfix ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_iAlls]
    intro x
    rw [Formula.realize_iff, Formula.realize_rel, Formula.realize_relabel]
    exact (iff_of_eq (congrFun (congrFun hfix i) x)).symm

end Realize

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (realize_isFixedPtF)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Realize

variable {A : Type} [L.Structure A]

end Realize

end StepDef

/-! ### The walk of a partial iteration -/

section ToSOTC

variable (d : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order))

/-- The SO(TC) specification of a partial fixed-point definition: walk the
deterministic iteration of the step formulas from the empty assignment, and
accept at a stable stage satisfying the output. -/
noncomputable def StepDef.toSOTCSpec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L where
  B := d.B
  step := d.nextSentence
  src := d.botSentence
  tgt := d.isFixedPtF ⊓ d.out

end ToSOTC

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (toSOTCSpec)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section ToSOTC

variable (d : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order))

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem StepDef.toSOTCSpec_step_iff (ρ σ : d.B.Assignment A) :
    d.toSOTCSpec.Step ρ σ ↔ σ = d.next ρ :=
  d.realize_nextSentence ρ σ

end ToSOTC

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (toSOTCSpec_step_iff)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section ToSOTC

variable (d : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order))

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem StepDef.toSOTCSpec_isSrc_iff (ρ : d.B.Assignment A) :
    d.toSOTCSpec.IsSrc ρ ↔ ρ = d.B.botAssign A :=
  d.realize_botSentence ρ

end ToSOTC

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (toSOTCSpec_isSrc_iff)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section ToSOTC

variable (d : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order))

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem StepDef.toSOTCSpec_isTgt_iff (ρ : d.B.Assignment A) :
    d.toSOTCSpec.IsTgt ρ ↔ IsFixedPt d.next ρ ∧
      @Sentence.Realize _ A (d.B.structure₁ (L := L.sum Language.order) ρ) d.out := by
  let := d.B.structure ρ
  have h : (@Sentence.Realize _ A (d.B.structure₁ (L := L.sum Language.order) ρ)
        (d.isFixedPtF ⊓ d.out)) ↔
      (@Sentence.Realize _ A (d.B.structure₁ (L := L.sum Language.order) ρ)
          d.isFixedPtF ∧
        @Sentence.Realize _ A (d.B.structure₁ (L := L.sum Language.order) ρ) d.out) :=
    BoundedFormula.realize_inf
  exact h.trans (and_congr (d.realize_isFixedPtF ρ) Iff.rfl)

end ToSOTC

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (toSOTCSpec_isTgt_iff)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section ToSOTC

variable (d : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order))

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The states reachable from the empty assignment are exactly the partial
stages. -/
theorem StepDef.reach_toSOTCSpec (σ : d.B.Assignment A) :
    d.toSOTCSpec.Reach (d.B.botAssign A) σ ↔ ∃ n, σ = d.partStage A n := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail τ υ _ hstep ih =>
      obtain ⟨n, rfl⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [d.partStage_succ]
      exact ((d.toSOTCSpec_step_iff _ _).mp hstep : υ = _)
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
      refine ih.tail ((d.toSOTCSpec_step_iff _ _).mpr ?_)
      exact d.partStage_succ n

end ToSOTC

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (reach_toSOTCSpec)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section ToSOTC

variable (d : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order))

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **Acceptance of the walk is the value of the partial definition**: a
stable stage satisfying the output is reachable from the empty assignment
exactly when the iteration converges to a limit satisfying the output. -/
theorem StepDef.accepts_toSOTCSpec :
    d.toSOTCSpec.Accepts A ↔ d.PFPHolds A := by
  constructor
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    have hρ : ρ = d.B.botAssign A := (d.toSOTCSpec_isSrc_iff ρ).mp hsrc
    subst hρ
    obtain ⟨n, rfl⟩ := (d.reach_toSOTCSpec σ).mp hreach
    obtain ⟨hfix, hout⟩ := (d.toSOTCSpec_isTgt_iff _).mp htgt
    exact ⟨n, hfix, hout⟩
  · rintro ⟨n, hfix, hout⟩
    refine ⟨d.B.botAssign A, d.partStage A n, (d.toSOTCSpec_isSrc_iff _).mpr rfl,
      (d.toSOTCSpec_isTgt_iff _).mpr ⟨hfix, hout⟩, (d.reach_toSOTCSpec _).mpr ⟨n, rfl⟩⟩

end ToSOTC

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (accepts_toSOTCSpec)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section ToSOTC

variable (d : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order))

variable {A : Type} [L.Structure A] [LinearOrder A]

end ToSOTC

/-! ### FO(≤, PFP) is contained in PSPACE -/

/-- **Every FO(≤, PFP) definable problem is SO(TC) definable**: the partial
iteration is a deterministic walk on the assignments of its own block. -/
theorem PFPDefinable.sotcDefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L} (h : Lax134656.PartialFixedPoint.PFPDefinable P) :
    Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.toSOTCSpec, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (d.accepts_toSOTCSpec (A := A)).symm

end Lax822549Proofs.DescriptiveComplexity

namespace Lax134656.PartialFixedPoint.PFPDefinable

export Lax822549Proofs.DescriptiveComplexity.PFPDefinable (sotcDefinable)

end Lax134656.PartialFixedPoint.PFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

/-- **FO(≤, PFP) is contained in PSPACE.** -/
theorem mem_PSPACE_of_pfpDefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L} (h : Lax134656.PartialFixedPoint.PFPDefinable P) :
    P ∈ PSPACE :=
  (mem_PSPACE_iff P).mpr h.sotcDefinable

end Lax822549Proofs.DescriptiveComplexity


