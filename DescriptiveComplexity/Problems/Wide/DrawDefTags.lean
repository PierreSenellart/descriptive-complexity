/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefAcc
import DescriptiveComplexity.Problems.Wide.DrawArgs

/-!
# What a gate's branch dispatches on

A gate block's branch checkpoint dispatches on the tag its witness flags
decode. The decoding itself
(`DescriptiveComplexity.Draw.DrawData.GateTagsAre`) is one-hotness of finitely
many control flags, so it is definable outright. The *total* dispatch
(`DspTagsAre`) adds a default branch for the block values no point encodes, and
that branch names a tag – which the interpretation may only do if the tag is
the same at every instance.

`DescriptiveComplexity.Draw.DrawData.defTag` is chosen from a *nonemptiness* of
the tags rather than from a point, exactly so that it is – by proof
irrelevance, the structure that witnessed the tags inhabited does not survive
into the value – and `DescriptiveComplexity.Draw.DrawData.uConst_defTag` is that
fact: one environment is all it takes, and every other names the same tag.
-/

namespace DescriptiveComplexity

namespace Draw

namespace DrawData

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : DrawData L} [Fintype dt.SlotIx]

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

end DrawData

end Draw

end DescriptiveComplexity
