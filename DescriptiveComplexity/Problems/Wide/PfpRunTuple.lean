/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTuple
import DescriptiveComplexity.Problems.Wide.PfpRunElem

/-!
# The tuple loop's run

The run theorem of `DescriptiveComplexity.Pfp.tupleRule`: per enumerated
tuple, a read trip at the source cell, the bit stored into the control, a
write trip at the destination cell reading it back, and the advance – so the
loop **copies** a bit per round, and the destination track evolves.

That evolution is what distinguishes this statement from the element loop's:
the background is a *family* over the enumeration, each round's write moving
the destination track from `mD a` to
`DescriptiveComplexity.Pfp.tuplePost` – the update at the round's
destination cell with the round's source bit – and the next round's
background carrying exactly that. Everything else follows the established
shape: an abstract finite linear order for the enumeration, control families
`fs0`/`fs1` around the store, and the loop closed by
`DescriptiveComplexity.Pfp.reflTransGen_of_ordLoop`.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

section TupleRun

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}
variable {wk rg : W} {emb : ChainPh 3 TuplePS → P}
variable {tSrc tDst : W}
variable {MatchS MatchD : (Q → A) → (W → A) → Prop}
variable {bitFlag : (Q → A) → Prop}
variable {setBit : Bool → (Q → A) → (W → A) → (Q → A)}
variable {initLv advLv : (Q → A) → (W → A) → (Q → A)}
variable {IsMaxLv : (Q → A) → Prop}
variable {exitPh : P}
variable {rEmb : ∀ i : ChainSite 3 TupleSS, ChainSh 3 TupleSS TupleSh i → R}
variable (hrules : ∀ (i : ChainSite 3 TupleSS) (ρ : ChainSh 3 TupleSS TupleSh i),
  PR.rules (rEmb i ρ) = tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS
    MatchD bitFlag setBit initLv advLv IsMaxLv exitPh i ρ)

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [LinearOrder K] [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A rule of the loop with a true guard is a `HasRight` witness. -/
private theorem hasRight_of_rule {i : ChainSite 3 TupleSS}
    {ρ : ChainSh 3 TupleSS TupleSh i}
    {f f' : Q → A} {g g' : W → A} {p p' : P}
    (hg : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).guard f g)
    (hp : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).srcPh = p)
    (hp' : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).dstPh = p')
    (hf' : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).dstSt f g = f')
    (hg' : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).wr f g = g')
    (hmr : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).moveRight) :
    PR.HasRight p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'], by rw [hrules]; exact hmr⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [LinearOrder K] [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A rule of the loop with a true guard is a `HasLeft` witness. -/
private theorem hasLeft_of_rule {i : ChainSite 3 TupleSS}
    {ρ : ChainSh 3 TupleSS TupleSh i}
    {f f' : Q → A} {g g' : W → A} {p p' : P}
    (hg : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).guard f g)
    (hp : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).srcPh = p)
    (hp' : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).dstPh = p')
    (hf' : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).dstSt f g = f')
    (hg' : (tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).wr f g = g')
    (hml : ¬(tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS MatchD bitFlag
      setBit initLv advLv IsMaxLv exitPh i ρ).moveRight) :
    PR.HasLeft p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'],
    fun hc => hml (by rw [hrules] at hc; exact hc)⟩

variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable {gbot : Univ A R P K dd} (hbot : ∀ y, WMLe gbot y)
variable {v v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (wmSeg gbot))
variable (hvi : WMIncr WMLe v v')
variable {ι : Type} [LinearOrder ι] [Finite ι] {a₀ aT : ι}
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)
variable {restOf : ι → (Univ A R P K dd → Prop) → W → A}
variable {mSrc : Univ A R P K dd → Prop} {mD : ι → Univ A R P K dd → Prop}
variable (hwkS : ∀ a r, restOf a r wk = bitVal PR.zero PR.one (r = v))
variable (hrg : ∀ a r, restOf a r rg =
  bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hsrc : ∀ a r, restOf a r tSrc =
  bitVal PR.zero PR.one (regBit mSrc r))
variable (hdst : ∀ a r, restOf a r tDst =
  bitVal PR.zero PR.one (regBit (mD a) r))
variable (hwkSrc : wk ≠ tSrc) (hwkDst : wk ≠ tDst)
variable (hrgSrc : rg ≠ tSrc) (hrgDst : rg ≠ tDst)
variable (hSD : tSrc ≠ tDst)
variable (xS xD : ι → Univ A R P K dd)

/-- **The destination track after a round's write**: the round's source bit
at its destination cell, everything else untouched. -/
def tuplePost (mSrc : Univ A R P K dd → Prop) (mD : ι → Univ A R P K dd → Prop)
    (xS xD : ι → Univ A R P K dd) (a : ι) : Univ A R P K dd → Prop :=
  fun y => (y = xD a ∧ mSrc (xS a)) ∨ (y ≠ xD a ∧ mD a y)

variable (fs0 fs1 : ι → Q → A)
variable (hnameS : ∀ a, MatchS (fs0 a)
  (PR.passTracks tSrc (restOf a) mSrc (wmSeg (xS a))))
variable (huniqS : ∀ (a : ι) (r : Univ A R P K dd → Prop),
  MatchS (fs0 a) (PR.passTracks tSrc (restOf a) mSrc r) → r = wmSeg (xS a))
variable (hnameD : ∀ a, MatchD (fs1 a)
  (PR.passTracks tDst (restOf a) (mD a) (wmSeg (xD a))))
variable (huniqD : ∀ (a : ι) (r : Univ A R P K dd → Prop),
  MatchD (fs1 a) (PR.passTracks tDst (restOf a) (mD a) r) → r = wmSeg (xD a))
variable (hstoreT : ∀ a, mSrc (xS a) →
  fs1 a = setBit true (fs0 a) (restOf a v))
variable (hstoreF : ∀ a, ¬mSrc (xS a) →
  fs1 a = setBit false (fs0 a) (restOf a v))
variable (hbitFlag : ∀ a, bitFlag (fs1 a) ↔ mSrc (xS a))
variable (hadv : ∀ a a' : ι, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  advLv (fs1 a) (restOf a v) = fs0 a')
variable (hcov : ∀ a a' : ι, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  ∀ y, mD a' y ↔ tuplePost mSrc mD xS xD a y)
variable (hagree : ∀ a a' : ι, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  ∀ r s, s ≠ tDst → restOf a' r s = restOf a r s)
variable (hmaxT : IsMaxLv (fs1 aT))
variable (hmaxF : ∀ a, a < aT → ¬IsMaxLv (fs1 a))

omit [LinearOrder ι] [Finite ι] hSD in
include hrules hR hlin hbot hv hvi hwkS hrg hsrc hdst hwkSrc hwkDst hrgSrc
  hrgDst hnameS huniqS hnameD huniqD hstoreT hstoreF hbitFlag in
/-- **One round of the tuple loop**: from the read trip's start phase at the
marker to the post-write checkpoint, the bit copied from the round's source
cell to its destination cell. -/
private theorem tuple_round (a : ι) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inl .start))) (fs0 a)), Sum.inl v,
        wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 a)), Sum.inl v,
        wideTape (PR.trackTape tDst (restOf a) (tuplePost mSrc mD xS xD a))
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  -- kit rule injections
  have hrulesR : ∀ ρ : ReadRule,
      PR.rules (rEmb (.sub false) (Sum.inl ρ)) =
        (ReadKit.mk tSrc wk MatchS
          (fun rp => emb (.sub (Sum.inl rp)))).rule PR.one ρ :=
    fun ρ => hrules (.sub false) (Sum.inl ρ)
  have hrulesW : ∀ ρ : WriteRule,
      PR.rules (rEmb (.sub true) (Sum.inl ρ)) =
        (WriteKit.mk tDst wk MatchD bitFlag
          (fun wp => emb (.sub (Sum.inr wp)))).rule PR.zero PR.one ρ :=
    fun ρ => hrules (.sub true) (Sum.inl ρ)
  -- guard facts at the marker, per presentation
  have hgwkS : PR.passTracks tSrc (restOf a) mSrc v wk = PR.one := by
    rw [Prog.passTracks_of_ne hwkSrc, hwkS]
    exact bitVal_pos rfl
  have hgrgS : PR.passTracks tSrc (restOf a) mSrc v rg ≠ PR.one := by
    rw [Prog.passTracks_of_ne hrgSrc, hrg,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact PR.zero_ne_one
  have hgwkD : ∀ mAny, PR.passTracks tDst (restOf a) mAny v wk = PR.one := by
    intro mAny
    rw [Prog.passTracks_of_ne hwkDst, hwkS]
    exact bitVal_pos rfl
  have hgrgD : ∀ mAny, PR.passTracks tDst (restOf a) mAny v rg ≠ PR.one := by
    intro mAny
    rw [Prog.passTracks_of_ne hrgDst, hrg,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact PR.zero_ne_one
  have hgwkS' : PR.passTracks tSrc (restOf a) mSrc v' wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hwkSrc, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  have hgwkD' : ∀ mAny, PR.passTracks tDst (restOf a) mAny v' wk ≠ PR.one := by
    intro mAny
    rw [Prog.passTracks_of_ne hwkDst, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  -- the marker symbol in the source presentation is the background's
  have hsymS : PR.passTracks tSrc (restOf a) mSrc v = restOf a v :=
    passTracks_of_back (hsrc a) v
  -- the tape, in the two presentations
  have hswap : PR.trackTape tSrc (restOf a) mSrc =
      PR.trackTape tDst (restOf a) (mD a) :=
    (trackTape_of_back (hsrc a)).trans (trackTape_of_back (hdst a)).symm
  -- the store step after the read's verdict
  have hstore : ∀ b : Bool,
      fs1 a = setBit b (fs0 a) (restOf a v) →
      (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inl (if b then .ry else .rn))))
            (fs0 a)), Sum.inl v,
          wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.chk ⟨1, by omega⟩)) (fs1 a)), Sum.inl v',
          wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩ := by
    intro b hb
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule hrules (i := .sub false) (ρ := Sum.inr b)
      ⟨hgwkS, hgrgS⟩ rfl rfl ?_ rfl trivial
    change setBit b (fs0 a) (PR.passTracks tSrc (restOf a) mSrc v) = fs1 a
    rw [hsymS, hb]
  -- the walk back at the between checkpoint
  have hback1 : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨1, by omega⟩)) (fs1 a)), Sum.inl v',
        wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨1, by omega⟩)) (fs1 a)), Sum.inl v,
        wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    exact hasLeft_of_rule hrules (i := .chk ⟨1, by omega⟩) (ρ := .stay)
      hgwkS' rfl rfl rfl rfl not_false
  -- the dispatch into the write trip
  have hdsp1 : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨1, by omega⟩)) (fs1 a)), Sum.inl v,
        wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inr .start))) (fs1 a)), Sum.inl v',
        wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    exact hasRight_of_rule hrules (i := .chk ⟨1, by omega⟩) (ρ := .dspA)
      ⟨hgwkS, hgrgS⟩ rfl rfl rfl rfl trivial
  -- the walk back at the write trip's start
  have hback2 : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inr .start))) (fs1 a)), Sum.inl v',
        wideTape (PR.trackTape tDst (restOf a) (mD a)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inr .start))) (fs1 a)), Sum.inl v,
        wideTape (PR.trackTape tDst (restOf a) (mD a)) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    exact hasLeft_of_rule hrules (i := .sub true) (ρ := Sum.inl .stayS)
      (hgwkD' (mD a)) rfl rfl rfl rfl not_false
  -- the write trip
  have hwrite := WriteKit.reaches (κ := WriteKit.mk tDst wk MatchD bitFlag
      (fun wp => emb (.sub (Sum.inr wp)))) hrulesW hR hlin hwkDst hbot hv
    (hwkS a) (hnameD a) (huniqD a)
  -- its written track is the round's post track
  have hpost : (fun y => (y = xD a ∧ bitFlag (fs1 a)) ∨ (y ≠ xD a ∧ mD a y)) =
      tuplePost mSrc mD xS xD a := by
    funext y
    exact propext (or_congr (and_congr_right fun _ => hbitFlag a) Iff.rfl)
  rw [hpost] at hwrite
  -- the write trip's exit into the post-write checkpoint
  have hexit2 : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inr .back))) (fs1 a)), Sum.inl v,
        wideTape (PR.trackTape tDst (restOf a) (tuplePost mSrc mD xS xD a))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 a)), Sum.inl v',
        wideTape (PR.trackTape tDst (restOf a) (tuplePost mSrc mD xS xD a))
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    exact hasRight_of_rule hrules (i := .sub true) (ρ := Sum.inr ())
      ⟨hgwkD _, hgrgD _⟩ rfl rfl rfl rfl trivial
  -- the walk back at the post-write checkpoint
  have hback3 : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 a)), Sum.inl v',
        wideTape (PR.trackTape tDst (restOf a) (tuplePost mSrc mD xS xD a))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 a)), Sum.inl v,
        wideTape (PR.trackTape tDst (restOf a) (tuplePost mSrc mD xS xD a))
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    exact hasLeft_of_rule hrules (i := .chk ⟨2, by omega⟩) (ρ := .stay)
      (hgwkD' _) rfl rfl rfl rfl not_false
  -- the read trip, then the whole chain
  by_cases hbit : mSrc (xS a)
  · refine Relation.ReflTransGen.trans
      (ReadKit.reaches_pos hrulesR hR hlin hwkSrc hbot hv (hwkS a)
        (hnameS a) (huniqS a) hbit) ?_
    refine (Relation.ReflTransGen.single (hstore true (hstoreT a hbit))).trans ?_
    refine (Relation.ReflTransGen.single hback1).trans ?_
    refine (Relation.ReflTransGen.single hdsp1).trans ?_
    rw [show wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank) =
      wideTape (PR.trackTape tDst (restOf a) (mD a)) (PR.syElt PR.blank) from
      congrArg (wideTape · (PR.syElt PR.blank)) hswap]
    refine (Relation.ReflTransGen.single hback2).trans ?_
    refine hwrite.trans ?_
    exact (Relation.ReflTransGen.single hexit2).trans
      (Relation.ReflTransGen.single hback3)
  · refine Relation.ReflTransGen.trans
      (ReadKit.reaches_neg hrulesR hR hlin hwkSrc hbot hv (hwkS a)
        (hnameS a) (huniqS a) hbit) ?_
    refine (Relation.ReflTransGen.single (hstore false (hstoreF a hbit))).trans ?_
    refine (Relation.ReflTransGen.single hback1).trans ?_
    refine (Relation.ReflTransGen.single hdsp1).trans ?_
    rw [show wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank) =
      wideTape (PR.trackTape tDst (restOf a) (mD a)) (PR.syElt PR.blank) from
      congrArg (wideTape · (PR.syElt PR.blank)) hswap]
    refine (Relation.ReflTransGen.single hback2).trans ?_
    refine hwrite.trans ?_
    exact (Relation.ReflTransGen.single hexit2).trans
      (Relation.ReflTransGen.single hback3)

omit hSD in
include hrules hR hlin hbot hv hvi hwkS hrg hsrc hdst hwkSrc hwkDst hrgSrc
  hrgDst hbotI htopI hnameS huniqS hnameD huniqD hstoreT hstoreF hbitFlag
  hadv hcov hagree hmaxT hmaxF in
/-- **The tuple loop's run**: from the entry checkpoint at the marker to the
exit phase one cell to its right, the destination track holding – round by
round – the source track's bits at the enumerated cells. -/
theorem tuple_run {f₀ : Q → A}
    (hinit : initLv f₀ (restOf a₀ v) = fs0 a₀) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨0, by omega⟩)) f₀), Sum.inl v,
        wideTape (PR.trackTape tSrc (restOf a₀) mSrc) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (fs1 aT)), Sum.inl v',
        wideTape (PR.trackTape tDst (restOf aT) (tuplePost mSrc mD xS xD aT))
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  -- guard facts, per round
  have hgwkS : ∀ a, PR.passTracks tSrc (restOf a) mSrc v wk = PR.one := by
    intro a
    rw [Prog.passTracks_of_ne hwkSrc, hwkS]
    exact bitVal_pos rfl
  have hgrgS : ∀ a, PR.passTracks tSrc (restOf a) mSrc v rg ≠ PR.one := by
    intro a
    rw [Prog.passTracks_of_ne hrgSrc, hrg,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact PR.zero_ne_one
  have hgwkD : ∀ a mAny, PR.passTracks tDst (restOf a) mAny v wk = PR.one := by
    intro a mAny
    rw [Prog.passTracks_of_ne hwkDst, hwkS]
    exact bitVal_pos rfl
  have hgrgD : ∀ a mAny, PR.passTracks tDst (restOf a) mAny v rg ≠ PR.one := by
    intro a mAny
    rw [Prog.passTracks_of_ne hrgDst, hrg,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact PR.zero_ne_one
  have hgwkS' : ∀ a, PR.passTracks tSrc (restOf a) mSrc v' wk ≠ PR.one := by
    intro a
    rw [Prog.passTracks_of_ne hwkSrc, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  -- the post-write symbol at the marker is the background's
  have hsymD : ∀ a mAny, regBit mAny v = False →
      PR.passTracks tDst (restOf a) mAny v = restOf a v := by
    intro a mAny hreg
    funext s
    by_cases hs : s = tDst
    · rw [hs]
      change (if tDst = tDst then bitVal PR.zero PR.one (regBit mAny v)
        else restOf a v tDst) = restOf a v tDst
      rw [if_pos rfl, hreg, bitVal_neg not_false, hdst a v,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec.1)]
    · exact Prog.passTracks_of_ne hs mAny v
  have hnoreg : ∀ mAny : Univ A R P K dd → Prop, regBit mAny v = False := by
    intro mAny
    refine propext ⟨fun hc => hvnr hc.choose hc.choose_spec.1, False.elim⟩
  -- swap from a round's post-write presentation to the next round's source one
  have hswapNext : ∀ a a' : ι, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      PR.trackTape tDst (restOf a) (tuplePost mSrc mD xS xD a) =
        PR.trackTape tSrc (restOf a') mSrc := by
    intro a a' hlt hnb
    have hpost : tuplePost mSrc mD xS xD a = mD a' := by
      funext y
      exact propext ((hcov a a' hlt hnb y).symm)
    rw [hpost]
    refine Eq.trans ?_ ((trackTape_of_back (hsrc a')).trans
      (trackTape_of_back (hdst a')).symm).symm
    refine funext fun r => ?_
    change PR.syElt (fun s => if s = tDst
        then bitVal PR.zero PR.one (regBit (mD a') r) else restOf a r s) =
      PR.syElt (fun s => if s = tDst
        then bitVal PR.zero PR.one (regBit (mD a') r) else restOf a' r s)
    refine congrArg _ (funext fun s => ?_)
    by_cases hs : s = tDst
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      exact (hagree a a' hlt hnb r s hs).symm
  -- one round from the marker, opened by a caller step into the read's start
  have hround : ∀ (a : ι) {p : P} {f : Q → A},
      (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl v,
          wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inl .start))) (fs0 a)), Sum.inl v',
          wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩ →
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl v,
          wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 a)), Sum.inl v,
          wideTape (PR.trackTape tDst (restOf a) (tuplePost mSrc mD xS xD a))
            (PR.syElt PR.blank)⟩ := by
    intro a p f hstep
    have hback : (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inl .start))) (fs0 a)), Sum.inl v',
          wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inl .start))) (fs0 a)), Sum.inl v,
          wideTape (PR.trackTape tSrc (restOf a) mSrc) (PR.syElt PR.blank)⟩ := by
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      exact hasLeft_of_rule hrules (i := .sub false) (ρ := Sum.inl .stayS)
        (hgwkS' a) rfl rfl rfl rfl not_false
    exact ((Relation.ReflTransGen.single hstep).trans
      (Relation.ReflTransGen.single hback)).trans
      (tuple_round hrules hR hlin hbot hv hvi hwkS hrg hsrc hdst hwkSrc hwkDst
        hrgSrc hrgDst xS xD fs0 fs1 hnameS huniqS hnameD huniqD hstoreT
        hstoreF hbitFlag a)
  -- the entry dispatch, and the first round
  have hentry := hround a₀ (p := emb (.chk ⟨0, by omega⟩)) (f := f₀) (by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule hrules (i := .chk ⟨0, by omega⟩) (ρ := .dspA)
      ⟨hgwkS a₀, hgrgS a₀⟩ rfl rfl ?_ rfl trivial
    change initLv f₀ (PR.passTracks tSrc (restOf a₀) mSrc v) = fs0 a₀
    rw [passTracks_of_back (hsrc a₀) v]
    exact hinit)
  -- the loop
  have hloop : Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 a₀)), Sum.inl v,
        wideTape (PR.trackTape tDst (restOf a₀) (tuplePost mSrc mD xS xD a₀))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 aT)), Sum.inl v,
        wideTape (PR.trackTape tDst (restOf aT) (tuplePost mSrc mD xS xD aT))
          (PR.syElt PR.blank)⟩ := by
    refine reflTransGen_of_ordLoop (conf := fun a =>
      (⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 a)), Sum.inl v,
        wideTape (PR.trackTape tDst (restOf a) (tuplePost mSrc mD xS xD a))
          (PR.syElt PR.blank)⟩ :
          Config (WPoint (Univ A R P K dd)))) ?_ hbotI aT
    intro a a' hlt hnb
    have hmax : ¬IsMaxLv (fs1 a) := hmaxF a (lt_of_lt_of_le hlt (htopI a'))
    have hstep : (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 a)), Sum.inl v,
          wideTape (PR.trackTape tDst (restOf a)
            (tuplePost mSrc mD xS xD a)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.sub (Sum.inl .start))) (fs0 a')), Sum.inl v',
          wideTape (PR.trackTape tDst (restOf a)
            (tuplePost mSrc mD xS xD a)) (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      refine hasRight_of_rule hrules (i := .chk ⟨2, by omega⟩) (ρ := .dspA)
        ⟨⟨hgwkD a _, hgrgD a _⟩, hmax⟩ rfl rfl ?_ rfl trivial
      change advLv (fs1 a) (PR.passTracks tDst (restOf a)
        (tuplePost mSrc mD xS xD a) v) = fs0 a'
      rw [hsymD a _ (hnoreg _)]
      exact hadv a a' hlt hnb
    have hswap := hswapNext a a' hlt hnb
    rw [show wideTape (PR.trackTape tDst (restOf a)
        (tuplePost mSrc mD xS xD a)) (PR.syElt PR.blank) =
      wideTape (PR.trackTape tSrc (restOf a') mSrc) (PR.syElt PR.blank) from
      congrArg (wideTape · (PR.syElt PR.blank)) hswap] at hstep ⊢
    exact hround a' hstep
  -- the exit dispatch
  have hexit : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨2, by omega⟩)) (fs1 aT)), Sum.inl v,
        wideTape (PR.trackTape tDst (restOf aT) (tuplePost mSrc mD xS xD aT))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (fs1 aT)), Sum.inl v',
        wideTape (PR.trackTape tDst (restOf aT) (tuplePost mSrc mD xS xD aT))
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    exact hasRight_of_rule hrules (i := .chk ⟨2, by omega⟩) (ρ := .dspB)
      ⟨⟨hgwkD aT _, hgrgD aT _⟩, hmaxT⟩ rfl rfl rfl rfl trivial
  exact (hentry.trans hloop).trans (Relation.ReflTransGen.single hexit)

end TupleRun

end Pfp

end DescriptiveComplexity
