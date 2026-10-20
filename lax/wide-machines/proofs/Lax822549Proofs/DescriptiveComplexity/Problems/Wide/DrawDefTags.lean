/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawDefAcc
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawArgs
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

/-!
# What a gate's branch dispatches on

A gate block's branch checkpoint dispatches on the tag its witness flags
decode. The decoding itself
(`DescriptiveComplexity.Draw.Data.GateTagsAre`) is one-hotness of finitely
many control flags, so it is definable outright. The *total* dispatch
(`DspTagsAre`) adds a default branch for the block values no point encodes, and
that branch names a tag – which the interpretation may only do if the tag is
the same at every instance.

`DescriptiveComplexity.Draw.Data.defTag` is chosen from a *nonemptiness* of
the tags rather than from a point, exactly so that it is – by proof
irrelevance, the structure that witnessed the tags inhabited does not survive
into the value – and `DescriptiveComplexity.Draw.Data.uConst_defTag` is that
fact: one environment is all it takes, and every other names the same tag.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : Data L} [Fintype dt.SlotIx]

/-- **A gate's decoding is definable**: one-hotness of the witness flags. -/
theorem uGDefinable_gateTagsAre (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (t : dt.X.Tag) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.GateTagsAre e.one hc t f :=
  (uGDefinable_forall fun t' : dt.X.Tag =>
    (uGDefinable_ctlBit (dt.gateTagC hc t')).iff
      (uGDefinable_const (t' = t))).congr fun _ _ _ => Iff.rfl

omit [Fintype dt.SlotIx] in
/-- **The default tag is the same at every instance**: it is `Classical`'s
choice at a `Prop`, so which structure witnessed the tags inhabited does not
survive into it. One environment is all it takes to name it. -/
theorem uConst_defTag (e₀ : Env L) :
    UConst fun e : Env L => dt.defTag (A := e.α) :=
  ⟨dt.defTag (A := e₀.α), fun _ => rfl⟩

/-- **The total dispatch is definable**: its genuine branch is the decoding,
and its default branch names a tag no instance can move. -/
theorem uGDefinable_dspTagsAre (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (e₀ : Env L) (t : dt.X.Tag) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.DspTagsAre e.one hc t f := by
  obtain ⟨t₀, hd0⟩ := uConst_defTag (dt := dt) e₀
  have hd : ∀ e : Env L, dt.defTag (A := e.α) = t₀ := hd0
  refine ((uGDefinable_gateTagsAre hc t).or
    ((uGDefinable_const (t = t₀)).and
      (uGDefinable_forall fun t' : dt.X.Tag =>
        (uGDefinable_gateTagsAre hc t').not))).congr fun e f g => ?_
  rw [DspTagsAre, hd e]

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


