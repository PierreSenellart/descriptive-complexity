/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxSpineSem

/-!
# The sweep's fold over the addresses, at an arbitrary file

The half of `DescriptiveComplexity.Problems.Wide.DrawIxSpineSem` that only a
*space-bounded* program has: the sweep that runs the spine once per address,
its dictionary and its stage tracks. Everything below it – what one spine
leaves on the tape, and the semantic packs the positions are run with – is
generic in the outer phase and stays there, because a clocked program needs it
too and has no sweep.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace DrawData

variable {L : Language.{0, 0}} (dt : DrawData L) {A R : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable {P : Type}
variable [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
variable [Language.wide.Structure
  (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
variable {PR : Prog A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}
variable {I : Type} [Finite I]
variable (F : LaidFile dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
variable {elt : I → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)
variable {e₀ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
variable (he₀ : ∀ y, WMLe e₀ y)
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
  Use u → WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]
-- The marks-to-shapes bridge at a coarse file (see `DrawIxRoundSem`).
variable (hpassEnc : ∀ (vi : dt.VarIx)
    (stV : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (ℓ : Fin (dt.nIn vi)),
  dt.ixIGPassP (elt := elt) F PR.zero PR.one vi stV ℓ ↔
    IsEnc dt.ly PR.zero PR.one (wmBlk (ixAddr elt stV.val)
      (DrawTag.arg (toLex (dt.igBlk vi ℓ)) :
        DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)))
-- The gates' marks-to-shapes bridge at a coarse file: a position is gated
-- exactly when the blocks of its mirror's **address** below the variable's
-- arity are encodings. Free at the elementwise file
-- (`DescriptiveComplexity.Draw.DrawData.isEnc_of_gatedAt` and its converse).
variable (hgateEnc : ∀ (j : Fin dt.nv)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I),
  dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st ↔
    ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      IsEnc dt.ly PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (DrawTag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)))
variable [Finite dt.KIx]


section SweepFamily

variable [LinearOrder (dt.X.Map A)]
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}
variable (mV : ιV → I → Prop)
variable (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)
variable (semOf : ∀ (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
  (j : Fin dt.nv) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st (mV a))
      elt (dt.kindOf (dt.varAt j) b))
variable (tOf : ∀ (_st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
  (j : Fin dt.nv), Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)

/-- **The state one address's spine ends in**, from the pair it starts
with. -/
noncomputable def ixStEnd
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I :=
  dt.ixSpineStOf (elt := elt) (v := w) (aT := aT) F hinj hhasP heltP mV st f (semOf st) (tOf st)
    (Fin.last dt.nv)

/-- **The control one address's spine ends in.** -/
noncomputable def ixFsEnd
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.ixSpineFsOf (elt := elt) (v := w) (aT := aT) F hinj hhasP heltP mV st f (semOf st) (tOf st)
    (Fin.last dt.nv)

/-! ### The threaded per-address evaluation

The mirror is normalized to the address the evaluation is run at. It is
already there — the advance sets it, and `ixSweepSWG_mir` proves it — but
writing it makes the equation **definitional**, which is what lets the
pack family be indexed by the address rather than quantified over
arbitrary states. That is the same move as `ixVarRdSt` one scale down, and
for the same reason: a pack at a state whose mirror holds junk does not
exist, so the mirror has to be pinned before the pack is asked for. -/

variable (semAt : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
    dt.dd → Prop)
  (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) (j : Fin dt.nv)
  (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
      (dt.ixRoundSt { st with mir := ixMark elt w } (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixRoundSt { st with mir := ixMark elt w } (mV a)) elt (dt.kindOf (dt.varAt j) b))
variable (tAt : ∀ (_w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
    dt.dd → Prop)
  (_st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) (j : Fin dt.nv),
  Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)

/-- **The state one address's spine ends in, threaded**, with the mirror
pinned at the address. -/
noncomputable def ixStEndT
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I :=
  dt.ixSpineStOfT (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV { st with mir := ixMark elt w } f (semAt w st)
    (tAt w st) (Fin.last dt.nv)

/-- **The control one address's spine ends in, threaded.** -/
noncomputable def ixFsEndT
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.ixSpineFsOfT (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV { st with mir := ixMark elt w } f (semAt w st)
    (tAt w st) (Fin.last dt.nv)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [Finite ιV] [LinearOrder (dt.X.Map A)] in
omit [Finite I] in
/-- **The mirror the threaded evaluation ends at is the address**, by
construction — `reaches_sweep`'s `hmirE` through `ixSweepStEG_mir'`. -/
theorem ixStEndT_mir
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) :
    (dt.ixStEndT (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semAt tAt w st f).mir = ixMark elt w :=
  dt.ixSpineStOfT_mir (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV { st with mir := ixMark elt w } f (semAt w st)
    (tAt w st) (Fin.last dt.nv)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **What the threaded evaluation leaves alone**: the marker, the bottom
and end marks and the stage dictionary — `reaches_sweep`'s `hwkE` and
`hltpE` through `ixSweepStEG_wk` and `ixSweepStEG_ltp`. -/
theorem ixStEndT_ride {β : Sort _}
    (G : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I → β)
    (hFmir : ∀ (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) m,
      G { st with mir := ixMark elt m } = G st)
    (hFleg : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
        dt.dd → Prop)
      (j : Fin dt.nv) (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
      (tOf' : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
      (semT : ∀ (p : IxScratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
        (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
            (dt.ixVarRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.IxKindSem PR.zero PR.one (dt.varAt j)
            (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
            elt (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      G (dt.ixLegStT (elt := elt)
        (v := w) (aT := aT) F hinj hhasP heltP mV j st tOf' semT f) = G st)
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) :
    G (dt.ixStEndT (elt := elt) (aT := aT) F hinj hhasP heltP mV semAt tAt w st f) = G st :=
  (dt.ixSpineRideT (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV { st with mir := ixMark elt w } f (semAt w st)
    (tAt w st) G (fun j st' tOf' semT f' => hFleg w j st' tOf' semT f')
    (Fin.last dt.nv)).trans (hFmir st w)

/-! The branched evaluation's semantic parameter is the conditioned family
of `DescriptiveComplexity.Draw.DrawData.ixGatedSem`, quantified over the address
as well: `DescriptiveComplexity.Draw.DrawData.ixStEndB` runs the spine at
`v := w` for an address bound after it. -/

variable (semAtB : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
    dt.dd → Prop) (j : Fin dt.nv)
  (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I),
  dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
  ∀ (p : IxScratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b))

/-- **The state one address's evaluation ends in**, with each position
taking whichever leg its gates call for and the mirror pinned at the
address — what a sweep over *every* address needs, gated or junk. -/
noncomputable def ixStEndB
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I :=
  dt.ixSpineStOfB (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV { st with mir := ixMark elt w } f semAtB
    (Fin.last dt.nv)

/-- **The control one address's evaluation ends in**, branched. -/
noncomputable def ixFsEndB
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.ixSpineFsOfB (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV { st with mir := ixMark elt w } f semAtB
    (Fin.last dt.nv)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **`reaches_sweep`'s `hmirE`** for the branched evaluation, by
construction — through `ixSweepStEG_mir'`. -/
theorem ixStEndB_mir
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) :
    (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semAtB w st f).mir = ixMark elt w :=
  dt.ixSpineStOfB_mir (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV { st with mir := ixMark elt w } f semAtB
    (Fin.last dt.nv)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **What the branched evaluation leaves alone** — `reaches_sweep`'s
`hwkE` and `hltpE` through `ixSweepStEG_wk` and `ixSweepStEG_ltp`. -/
theorem ixStEndB_ride {β : Sort _}
    (G : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I → β)
    (hFmir : ∀ (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) m,
      G { st with mir := ixMark elt m } = G st)
    (hFleg : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
        dt.dd → Prop)
      (j : Fin dt.nv) (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
      (semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
        ∀ (p : IxScratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
            (dt.ixVarRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.IxKindSem PR.zero PR.one (dt.varAt j)
            (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
            elt (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      G (dt.ixLegStB (elt := elt) (v := w) (aT := aT) F hinj hhasP heltP mV j st semT f) = G st)
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) :
    G (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semAtB w st f) = G st :=
  (dt.ixSpineRideB (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV { st with mir := ixMark elt w } f semAtB
    G (fun j st' semT f' => hFleg w j st' semT f')
    (Fin.last dt.nv)).trans (hFmir st w)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **Off the address it is run at, the branched evaluation leaves the stage
tracks alone** — a position writes its own cell only
(`ixSpine_new_off`). -/
theorem ixStEndB_new_off
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (f : dt.CtlIx → A) (i : dt.d.B.ι)
    {r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hr : r ≠ w) :
    (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semAtB w st f).new i r ↔ st.new i r :=
  dt.ixSpine_new_off (dt.ixSpineStOfB_writesNew (elt := elt)
    (v := w) (aT := aT) F hinj hhasP heltP mV
    { st with mir := ixMark elt w } f semAtB) (Fin.last dt.nv) i hr

variable (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
variable (st₀ : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
variable (f₀ : dt.CtlIx → A)

/-- **The pair the sweep arrives at each address with**: the base at the
empty address, and at every increment the previous address's spine exit —
its marker moved on and its mirror set to the new address, exactly the
shape `DescriptiveComplexity.Draw.DrawData.reaches_sweep` demands. -/
noncomputable def ixSweepPair
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I × (dt.CtlIx → A) :=
  addrIter (isLinOrd_wmSetLe hlin) (st₀, f₀)
    (fun u p =>
      ({ dt.atSt (dt.ixStEnd (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf u p.1 p.2)
            (wmNext hlin u) with mir := ixMark elt (wmNext hlin u) },
        dt.ixFsEnd (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf u p.1 p.2)) w

/-- The sweep's tape family — `reaches_sweep`'s `SW`. -/
noncomputable def ixSweepSW
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I :=
  (dt.ixSweepPair (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w).1

/-- The sweep's control family — `reaches_sweep`'s `FS`. -/
noncomputable def ixSweepFS
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  (dt.ixSweepPair (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w).2

/-- The state the sweep leaves each address in — `reaches_sweep`'s
`stE`. -/
noncomputable def ixSweepStE
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I :=
  dt.ixStEnd (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf w
    (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w)
    (dt.ixSweepFS (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w)

/-- The control the sweep leaves each address in — `reaches_sweep`'s
`fsE`. -/
noncomputable def ixSweepFsE
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  dt.ixFsEnd (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf w
    (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w)
    (dt.ixSweepFS (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w)

omit [Finite I] [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem ixSweepSW_bot :
    dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ (fun _ => False) = st₀ :=
  congrArg Prod.fst
    (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)

omit [Finite I] [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem ixSweepFS_bot :
    dt.ixSweepFS (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ (fun _ => False) = f₀ :=
  congrArg Prod.snd
    (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)

omit [Finite I] [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The tape's cover equation** — `reaches_sweep`'s `hSW`, on the nose:
the next address's entry state is this one's spine exit, its marker moved
on and its mirror at the new address. -/
theorem ixSweepSW_incr
    {w w' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w' =
      { dt.atSt (dt.ixSweepStE (elt := elt) (aT := aT) F hinj hhasP heltP
        mV semOf tOf hlin st₀ f₀ w) w' with
        mir := ixMark elt w' } := by
  have h := congrArg Prod.fst
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (dt.ixStEnd (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf u p.1 p.2)
              (wmNext hlin u) with mir := ixMark elt (wmNext hlin u) },
          dt.ixFsEnd (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf u p.1 p.2)))
  rw [wmNext_eq hlin hi] at h
  exact h

omit [Finite I] [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The control's cover equation** — `reaches_sweep`'s `hFS`: the next
address's entry control is this one's spine exit control. -/
theorem ixSweepFS_incr
    {w w' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.ixSweepFS (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w' =
      dt.ixSweepFsE (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w :=
  congrArg Prod.snd
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (dt.ixStEnd (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf u p.1 p.2)
              (wmNext hlin u) with mir := ixMark elt (wmNext hlin u) },
          dt.ixFsEnd (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf u p.1 p.2)))

/-! ### What the sweep's entry and exit states hold -/

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **A field a leg's write leaves alone rides one address's spine.** -/
theorem ixSweepStE_ride {β : Sort _}
    (G : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I → β)
    (hF : ∀ (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
      st m i b, G (dt.ixPostVarSt u st m i b) = G st)
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    G (dt.ixSweepStE (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w) =
      G (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w) :=
  dt.ixSpineRide
    (hst := fun j => dt.ixSpineStOf_succ (elt := elt) (v := w) (aT := aT) F hinj hhasP heltP mV
      (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w)
      (dt.ixSweepFS (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w)
      (semOf (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w))
      (tOf (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ w)) j)
    G (fun st _ i b => hF w st _ i b) (Fin.last dt.nv)

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **A field neither a leg nor the advance writes rides the whole
sweep.** -/
theorem ixSweepSW_ride {β : Sort _}
    (G : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I → β)
    (hF : ∀ (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
      st m i b, G (dt.ixPostVarSt u st m i b) = G st)
    (hFa : ∀ st u, G { dt.atSt st u with mir := ixMark elt u } = G st)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    G (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ w) = G st₀ := by
  refine holds_of_wideRounds hlin
    (Q := fun u => G (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ u) =
      G st₀) ?_ ?_ w hlb hub
  · rw [dt.ixSweepSW_bot (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀]
  · intro u u' hi _ _ ih
    rw [dt.ixSweepSW_incr (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ hi, hFa,
      dt.ixSweepStE_ride (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ G hF u]
    exact ih

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **The marker is at the address**, at every entry state of the sweep. -/
theorem ixSweepSW_wk (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ w).wk = fun r => r = w := by
  refine holds_of_wideRounds hlin
    (Q := fun u => (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ u).wk =
      fun r => r = u) ?_ ?_ w hlb hub
  · rw [dt.ixSweepSW_bot (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀]
    exact hwk₀
  · intro u u' hi _ _ _
    rw [dt.ixSweepSW_incr (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ hi]
    rfl

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **The mirror is at the address**, at every entry state of the sweep. -/
theorem ixSweepSW_mir (hmir₀ : st₀.mir = fun _ => False)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ w).mir = ixMark elt w := by
  refine holds_of_wideRounds hlin
    (Q := fun u => (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ u).mir = ixMark elt u)
    ?_ ?_ w hlb hub
  · rw [dt.ixSweepSW_bot (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀]
    exact hmir₀
  · intro u u' hi _ _ _
    rw [dt.ixSweepSW_incr (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀ hi]

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **`DescriptiveComplexity.Draw.DrawData.reaches_sweep`'s `hwkE`**: the
marker is still at the address when the address's spine ends. -/
theorem ixSweepStE_wk (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepStE (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ w).wk = fun r => r = w :=
  (dt.ixSweepStE_ride (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀
    (fun st => st.wk) (fun _ _ _ _ _ => rfl) w).trans
    (dt.ixSweepSW_wk (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ hwk₀ (s₁ := s₁) w hlb hub)

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **`reaches_sweep`'s `hmirE`**: so is the mirror. -/
theorem ixSweepStE_mir (hmir₀ : st₀.mir = fun _ => False)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepStE (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ w).mir = ixMark elt w :=
  (dt.ixSweepStE_ride (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀
    (fun st => st.mir) (fun _ _ _ _ _ => rfl) w).trans
    (dt.ixSweepSW_mir (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ hmir₀ (s₁ := s₁) w hlb hub)

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **The permanent `ltp` mark rides the sweep**: neither a leg nor the
advance writes it. -/
theorem ixSweepStE_ltp_eq
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepStE (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ w).ltp = st₀.ltp :=
  (dt.ixSweepStE_ride (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf hlin st₀ f₀
    (fun st => st.ltp) (fun _ _ _ _ _ => rfl) w).trans
    (dt.ixSweepSW_ride (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ (fun st => st.ltp)
      (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (s₁ := s₁) w hlb hub)

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **`reaches_sweep`'s `hltpE`**: the address is not the marked end, the
mark being where the reduction planted it. -/
theorem ixSweepStE_ltp
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁)
    (hltp₀ : ¬st₀.ltp w) :
    ¬(dt.ixSweepStE (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ w).ltp w := by
  rw [dt.ixSweepStE_ltp_eq (elt := elt) (aT := aT) F hinj hhasP heltP
    mV semOf tOf hlin st₀ f₀ (s₁ := s₁) w
    hlb hub]
  exact hltp₀

/-! ### The SAV/TGT gap

`DescriptiveComplexity.Draw.DrawData.ixEvalSpine_run` asks, at every address, for
`hsavOf`/`htgtOf` — the SAV and TARGET registers holding *that address* —
because `DescriptiveComplexity.Draw.DrawData.ixMatrix_run` reads them there. But
the advance refreshes only the marker and the mirror (`reaches_sweep`'s
`hSW` is `atSt … with mir := …`), so those two registers **ride** the whole
sweep, and the requirement is met at one address at most. The two lemmas
below are that statement, not a workaround: whichever way the gap is closed
— the advance copying the mirror into SAV and TARGET, the evaluation
refreshing them at its entry, or `ixMatrix_run` reading the mirror instead —
the fix is in the *program*, not here. -/

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **SAV rides the sweep.** -/
theorem ixSweepSW_sav
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semOf tOf hlin st₀ f₀ w).sav = st₀.sav :=
  dt.ixSweepSW_ride (elt := elt) (aT := aT) F hinj hhasP heltP
    mV semOf tOf hlin st₀ f₀ (fun st => st.sav)
    (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (s₁ := s₁) w hlb hub

omit [Finite I] [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **So SAV can hold the address at one address only**: the spine's
requirement `(SW w).sav = w` forces the sweep's range to be a single
cell. -/
theorem ixEq_of_sweepSW_sav
    {s₁ w₁ w₂ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hlb₁ : WMSetLe WMLe (fun _ => False) w₁) (hub₁ : WMSetLe WMLe w₁ s₁)
    (hlb₂ : WMSetLe WMLe (fun _ => False) w₂) (hub₂ : WMSetLe WMLe w₂ s₁)
    (hh₁ : IxHolds elt Use w₁) (hh₂ : IxHolds elt Use w₂)
    (h₁ : (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf
      hlin st₀ f₀ w₁).sav = ixMark elt w₁)
    (h₂ : (dt.ixSweepSW (elt := elt) (aT := aT) F hinj hhasP heltP mV semOf tOf
      hlin st₀ f₀ w₂).sav = ixMark elt w₂) :
    w₁ = w₂ := by
  have e₁ := (dt.ixSweepSW_sav (elt := elt) (aT := aT) F hinj hhasP heltP mV
    semOf tOf hlin st₀ f₀ (s₁ := s₁) w₁ hlb₁ hub₁).symm.trans h₁
  have e₂ := (dt.ixSweepSW_sav (elt := elt) (aT := aT) F hinj hhasP heltP mV
    semOf tOf hlin st₀ f₀ (s₁ := s₁) w₂ hlb₂ hub₂).symm.trans h₂
  exact (ixAddr_ixMark hh₁).symm.trans
    ((congrArg (ixAddr elt) (e₁.symm.trans e₂)).trans (ixAddr_ixMark hh₂))

/-! ### The sweep's per-address run

`reaches_sweep` asks for the evaluation's run at each address of the
interval, from the pair the sweep arrives with to the pair it leaves. With
the branched evaluation that is now provable outright: the entry state's
mirror *is* the address (`ixSweepSWG_mir`, which the advance guarantees), so
pinning it changes nothing, and the marker and the bottom mark ride from
the sweep's base. -/

/-! ### What a whole sweep leaves, in dictionary form

`ixSweep_new` at the branched evaluation: each address's own reading is
`ixNew_last_trackOf_B`, everything else it leaves alone is `ixSpine_new_off`,
and the next address's entry state is the sweep's own cover equation. Below
the address reached, every stage track holds the dictionary of the *next*
stage; elsewhere it still holds what the sweep started with. -/

set_option maxHeartbeats 1000000 in
-- the sweep's fold is stated over the branched evaluation's own families, so
-- every unification here carries the whole per-address spine
omit [Finite I] in
include hix hinj hhasP heltP hblkP hmono hup hpassEnc hgateEnc hUse in
/-- **A sweep rewrites the stage tracks of exactly the addresses it has
passed**, at the concrete branched evaluation. -/
theorem ixSweep_new_trackOf
    (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {Use' : I → Prop}
    {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
      (w : Fin dt.dd → A), ixAddr elt (mV a) (t, w) →
        ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {Below : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict₀ : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R)
        (P := OuterPh (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st₀.old iv (tupAddr dt.ly PR.zero PR.one (R := R)
        (P := OuterPh (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
      (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      Below (ixAddr elt (dt.ixStageTgt F hhasP (dt.varAt j) ts
        { dt.ixRoundSt st (mV a) with sav := ixMark elt w }
        (dt.d.B.arity iv))))
    {gbot : I} (hbot : ∀ y, F.le gbot y)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hs₁ : WMSetLt WMLe s₁ (F.cell gbot))
    -- the addresses the sweep visits are ones the file can hold
    (hHold : ∀ w, WMSetLe WMLe w s₁ → IxHolds elt Use' w) :
    ∀ w, WMSetLe WMLe (fun _ => False) w → WMSetLe WMLe w s₁ →
      (∀ (i : dt.d.B.ι)
          (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
        WMSetLe WMLe (fun _ => False) r → WMSetLt WMLe r w →
          ((dt.ixSweepSWG (elt := elt)
              (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV
                (fun w' j st hg =>
                  dt.ixGatedSem (elt := elt)
                    F hpassEnc hgateEnc PR.zero_ne_one hlin mV (v := w') j st hg))
              (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV
                (fun w' j st hg =>
                  dt.ixGatedSem (elt := elt)
                    F hpassEnc hgateEnc PR.zero_ne_one hlin mV (v := w') j st hg))
              hlin st₀ f₀ w).new i r ↔
            trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i))
              (dt.d.next σ) r)) ∧
      (∀ (i : dt.d.B.ι)
          (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
        ¬(WMSetLe WMLe (fun _ => False) r ∧ WMSetLt WMLe r w) →
          ((dt.ixSweepSWG (elt := elt)
              (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV
                (fun w' j st hg =>
                  dt.ixGatedSem (elt := elt)
                    F hpassEnc hgateEnc PR.zero_ne_one hlin mV (v := w') j st hg))
              (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV
                (fun w' j st hg =>
                  dt.ixGatedSem (elt := elt)
                    F hpassEnc hgateEnc PR.zero_ne_one hlin mV (v := w') j st hg))
              hlin st₀ f₀ w).new i r ↔ st₀.new i r)) := by
  classical
  set semG : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) (j : Fin dt.nv)
      (st : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I),
      dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st → _ :=
    fun w j st hg => dt.ixGatedSem (elt := elt)
      F hpassEnc hgateEnc PR.zero_ne_one hlin mV (v := w) j st hg
    with hsemG
  have hset := isLinOrd_wmSetLe hlin
  set stEG := dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semG
    with hstEG
  set fsEG := dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semG
    with hfsEG
  -- the stage dictionary rides the sweep
  have hold : ∀ w, WMSetLe WMLe (fun _ => False) w → WMSetLe WMLe w s₁ →
      (dt.ixSweepSWG (elt := elt) stEG fsEG hlin st₀ f₀ w).old = st₀.old :=
    fun w hlb hub => dt.ixSweepSWG_ride _ _ hlin st₀ f₀ (fun st => st.old)
      (fun u st f => dt.ixStEndB_ride (elt := elt) (aT := aT) F hinj hhasP heltP
        mV semG (fun st => st.old)
        (fun _ _ => rfl)
        (fun _ _ _ _ _ =>
          (dt.ixLegStB_fields (elt := elt) (aT := aT) F hinj hhasP heltP
            mV _ _ _ _).2.2.2.1) u st f)
      (fun _ _ => rfl) (s₁ := s₁) w hlb hub
  -- every address of the stretch lies below the register file
  have hreg : ∀ w, WMSetLe WMLe w s₁ →
      ¬∃ u : I, w = F.cell u := by
    intro w hub
    refine F.toIxFile.not_exists_cell_of_lt_bot hix hbot ((wmSetLt_iff _ _).mpr
      ⟨hset.2.1 w s₁ (F.cell gbot) hub ((wmSetLt_iff _ _).mp hs₁).1, fun hc => ?_⟩)
    exact ((wmSetLt_iff _ _).mp hs₁).2
      (hset.2.2.1 s₁ (F.cell gbot) ((wmSetLt_iff _ _).mp hs₁).1
        ((show w = F.cell gbot from hc) ▸ hub))
  have key := dt.ixSweep_new hlin
    (s₀ := fun _ => False) (s₁ := s₁)
    (SW := dt.ixSweepSWG (elt := elt) stEG fsEG hlin st₀ f₀)
    (stE := dt.ixSweepStEG (elt := elt) stEG fsEG hlin st₀ f₀)
    (N := fun i r =>
      trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i)) (dt.d.next σ) r)
    (fun w hlb hub i => ?_) (fun w hlb hub i r hr => ?_)
    (fun w w' hi _ _ => dt.ixSweepSWG_incr _ _ hlin st₀ f₀ hi)
  · intro w hlb hub
    refine ⟨(key w hlb hub).1, fun i r hr => ((key w hlb hub).2 i r hr).trans ?_⟩
    rw [dt.ixSweepSWG_bot (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semG)
      (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semG) hlin st₀ f₀]
  · -- the address's own cell, by the branched spine's dictionary
    have hub' : WMSetLe WMLe w s₁ := ((wmSetLt_iff _ _).mp hub).1
    exact ixNew_last_trackOf_B (dt := dt) (elt := elt) (F := F) (hinj := hinj)
      (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
      (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc)
      (hgateEnc := hgateEnc) (mV := mV) (hUse := hUse)
      (st₀ := { dt.ixSweepSWG (elt := elt)
          (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semG)
          (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semG)
          hlin st₀ f₀ w with mir := ixMark elt w })
      (f₀ := dt.ixSweepFSG (elt := elt)
        (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semG)
        (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semG)
        hlin st₀ f₀ w)
      (hlin := hlin) (hord := hord) (hbotV := hbotV) (hmV0 := hmV0)
      (hIncr := hIncr) (hKin := hKin) (hTop := hTop) (hreg := hreg w hub')
        (hordP := hordP) (σ := σ) (hmir₀ := ixAddr_ixMark (hHold w hub'))
      (hdict := fun iv x hs =>
        (iff_of_eq (congrFun (congrFun (hold w hlb hub') iv) _)).trans
          (hdict₀ iv x hs))
      (hbelow := fun j a iv ts st => hbelow j a iv ts st w) (i := i)
  · -- every other cell rides the address's own evaluation
    exact dt.ixStEndB_new_off (elt := elt) (aT := aT) F hinj hhasP heltP mV semG w _ _ i hr

section SweepRun

variable {v' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {rEmb : ∀ i : dt.SEF, dt.SESh i → R}
variable {a₀ : ιV}

set_option maxHeartbeats 4000000 in
-- the per-address run instantiates the whole spine at the sweep's families,
-- and the widths' four bounds are unified against them one by one
omit [LinearOrder (dt.X.Map A)] in
include hlin hinj hhasP heltP hsepP hix he₀ hmono hup in
/-- **`DescriptiveComplexity.Draw.DrawData.reaches_sweep`'s `hspine`, at one
address**: the whole per-address evaluation runs, whichever legs each
position's gates call for. -/
theorem ixReaches_spineB_reachesIn
    (hrules : ∀ (i : dt.SEF) (ρ : dt.SESh i),
      PR.rules (rEmb i ρ) =
        dt.evalRuleF PR.zero PR.one
          (fun w => dt.varArgsOf PR.zero PR.one w) i ρ)
    (hR : PR.table.Reads)
    (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : I}
    (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
    (hwork : ∀ {r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop},
      (∀ x, r x → ∃ i : dt.KIx, x.1 = DrawTag.arg i) →
      ∀ u : I, WMSetLt WMLe r (F.cell u))
    -- the widths a clocked stage atom of any position is priced at
    {wA wG wP wR wK : ℕ}
    (hgap : ∀ u u' : I, IxSucc F.le u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
    (hwP : wideRank (F.cell gtop) + 2 +
      ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
      wideRank (F.cell gbot) ≤ wP)
    (hwR : ∀ s : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop,
      WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
    (hwK : ∀ T : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop,
      WMSetLt WMLe T (F.cell gbot) →
      wideRank T *
          (1 + (wideRank (F.cell gtop) + 3 +
              (ixRank F.le gtop - ixRank F.le gbot) * wG +
              wideRank (F.cell gbot)) +
            (wideRank (F.cell gtop) +
              ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
              wideRank (F.cell gbot) + 4)) + 1 +
        (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) ≤ wK)
    -- every named register of the file is within `wA` of the marker, wherever
    -- the sweep has put it
    (hcostR : ∀ (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
        (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      2 * (wideRank (F.cell (F.toLayout.reg hhasP b c)) - wideRank u) + 2 ≤ wA)
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    -- the exhaustion test the machine runs, at the registers
    (hTestT : ∀ u : I, dt.InnerFull F.blk (mV aT) u)
    (hTestF : ∀ a, a < aT → ∃ u : I, ¬dt.InnerFull F.blk (mV a) u)
    (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    (hmir₀ : st₀.mir = fun _ => False)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    {s₁ w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁)
    (hv : WMSetLt WMLe w (F.cell gbot)) (hvi : WMIncr WMLe w v')
    -- the address is one the file can hold, and its stage registers are the
    -- file's own
    (hvh : IxHolds elt Use w)
    (hxdUse : ∀ {iv : dt.d.B.ι} (ℓ : Fin (dt.d.B.arity iv))
      (b : Lex (Fin dt.dd0 → A)), Use (dt.ixStageXD F hhasP ℓ b)) :
    (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      ((dt.ixLegCost A wA wP wR wK (Nat.card ιV) + 2) * dt.nv)
      ⟨Sum.inr (PR.stElt (.evalP (.chk 0))
          (dt.ixSweepFSG (elt := elt) (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP
            mV semAtB)
            (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP
              mV semAtB) hlin st₀ f₀ w)), Sum.inl w,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixSweepSWG (elt := elt) (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP
              mV semAtB)
              (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semAtB) hlin st₀ f₀ w))
          (dt.ixSweepSWG (elt := elt) (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP
            mV semAtB)
            (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semAtB) hlin st₀ f₀ w).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last dt.nv)))
          (dt.ixSweepFsEG (elt := elt) (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP
            mV semAtB)
            (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP
              mV semAtB) hlin st₀ f₀ w)), Sum.inl w,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixSweepStEG (elt := elt) (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP
              mV semAtB)
              (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semAtB) hlin st₀ f₀ w))
          (dt.ixSweepStEG (elt := elt) (dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP
            mV semAtB)
            (dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semAtB) hlin st₀ f₀ w).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  set stEB := dt.ixStEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semAtB
    with hstEB
  set fsEB := dt.ixFsEndB (elt := elt) (aT := aT) F hinj hhasP heltP mV semAtB
    with hfsEB
  set SW0 := dt.ixSweepSWG (elt := elt) stEB fsEB hlin st₀ f₀ w with hSW0
  set FS0 := dt.ixSweepFSG (elt := elt) stEB fsEB hlin st₀ f₀ w with hFS0
  have hmirSW : SW0.mir = ixMark elt w :=
    dt.ixSweepSWG_mir _ _ hlin st₀ f₀ hmir₀ (s₁ := s₁) w hlb hub
  have hwkSW : SW0.wk = fun r => r = w :=
    dt.ixSweepSWG_wk _ _ hlin st₀ f₀ hwk₀ (s₁ := s₁) w hlb hub
  have hbotSW : SW0.bot = fun r => r = (fun _ => False) := by
    refine Eq.trans (dt.ixSweepSWG_ride _ _ hlin st₀ f₀ (fun st => st.bot) ?_
      (fun _ _ => rfl) (s₁ := s₁) w hlb hub) hbot₀
    exact fun u st f => dt.ixStEndB_ride (elt := elt) (aT := aT) F hinj hhasP heltP
      mV semAtB (fun st => st.bot)
      (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.ixLegStB_fields (elt := elt) (aT := aT) F hinj hhasP heltP
        mV _ _ _ _).2.2.1) u st f
  -- pinning the mirror at the address is the identity on the entry state
  have hpin : ∀ X : TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I,
      X.mir = ixMark elt w →
        ({ X with mir := ixMark elt w } :
          TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) = X := by
    intro X hX
    rw [← hX]
  rw [← hpin _ hmirSW]
  refine ixEvalSpineB_reachesIn (dt := dt) (elt := elt) (F := F) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hsepP := hsepP) (hix := hix)
    (he₀ := he₀) (hord := hord) (hmono := hmono) (hup := hup)
    (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
    (hwork := hwork) (hv := hv) (hvi := hvi) (hbotV := hbotV) (htopV := htopV)
    (hvh := hvh) (hxdUse := hxdUse)
    (w := wA) (wG := wG) (wP := wP) (wR := wR) (wK := wK)
    (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
    (hcostR := fun b c => hcostR w b c)
    (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (hTestF := hTestF)
    (stOf := dt.ixSpineStOfB (elt := elt) (v := w) (aT := aT) F hinj hhasP heltP
      mV { SW0 with mir := ixMark elt w } FS0 semAtB)
    (fsOf := dt.ixSpineFsOfB (elt := elt) (v := w) (aT := aT) F hinj hhasP heltP
      mV { SW0 with mir := ixMark elt w } FS0 semAtB)
    (semTJ := dt.ixSpineSemOfB (elt := elt) (v := w) (aT := aT) F hinj hhasP
      heltP mV _ _ _)
    (hst := fun j => dt.ixSpineStOfB_succ (elt := elt) (v := w) (aT := aT) F
      hinj hhasP heltP mV _ _ _ j)
    (hfs := fun j => dt.ixSpineFsOfB_succ (elt := elt) (v := w) (aT := aT) F
      hinj hhasP heltP mV _ _ _ j)
    ?_ ?_ ?_
  · intro k
    refine Eq.trans (dt.ixSpineRideB (elt := elt) (v := w) (aT := aT) F hinj hhasP heltP mV _ _ _
      (fun st => st.wk)
      (fun _ _ _ _ => (dt.ixLegStB_fields (elt := elt) (aT := aT) F hinj hhasP heltP
        mV _ _ _ _).2.1) k) hwkSW
  · intro j
    exact dt.ixSpineStOfB_mir (elt := elt)
      (v := w) (aT := aT) F hinj hhasP heltP mV _ _ _ j.castSucc
  · intro j
    refine Eq.trans (dt.ixSpineRideB (elt := elt) (v := w) (aT := aT) F hinj hhasP heltP mV _ _ _
      (fun st => st.bot)
      (fun _ _ _ _ => (dt.ixLegStB_fields (elt := elt) (aT := aT) F hinj hhasP heltP
        mV _ _ _ _).2.2.1)
      j.castSucc) hbotSW

end SweepRun

end SweepFamily

end DrawData

end Draw

end DescriptiveComplexity
