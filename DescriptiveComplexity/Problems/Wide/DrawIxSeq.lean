/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxMat
import DescriptiveComplexity.Problems.Wide.DrawInstSeq

/-!
# The matrix's sequencer at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawInstSeq` read at a coarse file: the
uniform stage discharge (`ixKind_hStage`), the control the sequencer folds
(`ixKindExitCtl`, `ixMatFs`), the matrix's run and the gates' run, all at the
registers of an arbitrary file rather than the elements of the universe.

The runs here are `Relation.ReflTransGen`: the atoms below them carry their
budgets, and the counting of the layers above the matrix is one pass, to be
made once the conversion reaches the evaluation.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {I : Type} [Finite I] (F : LaidFile dt A R P I)
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
variable {e₀ : Univ A R P dt.KIx dt.dd} (he₀ : ∀ y, WMLe e₀ y)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

section KindStage

variable (zero one : A)
variable (hhas : F.toLayout.HasName zero)
variable (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))
variable (vi : dt.VarIx) (av : Fin dt.natMax)
variable (st : TapeSt dt A R P I) (v : Univ A R P dt.KIx dt.dd → Prop)

/-- **The semantic data of one atom's run**: an expansion atom needs the
points its levels' registers encode; the other kinds need nothing. -/
noncomputable def IxKindSem (elt : I → Univ A R P dt.KIx dt.dd) :
    MatAtom dt.X dt.d.B (dt.nOf vi) → Type
  | .eq _ _ => PUnit
  | .ord _ _ => PUnit
  | .stage _ _ => PUnit
  | @MatAtom.exp _ _ _ _ k _ ts =>
    { pts : Fin k → dt.X.Map A //
      ∀ ℓ : Fin k,
        wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
          (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
          encMap dt.ly zero one (pts ℓ) }

/-- **A semantic pack transports along the registers it reads.**
`DescriptiveComplexity.Draw.Data.KindSem` sees the tape state only
through the levels' register sets, so a pack at one state is a pack at
every state with the same mirror and VAL. This is what lets *one* pack —
built at an address's entry state — serve every position of the spine and
every round of the VAL loop, whose states differ from it in the tracks
they have written and in the two scratch registers. -/
noncomputable def ixKindSemCast (zero one : A) (vi : dt.VarIx)
    {st st' : TapeSt dt A R P I}
    (hmir : st.mir = st'.mir) (hval : st.val = st'.val)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (s : dt.IxKindSem (elt := elt) zero one vi st κ) :
    dt.IxKindSem (elt := elt) zero one vi st' κ :=
  match κ, s with
  | .eq _ _, s => s
  | .ord _ _, s => s
  | .stage _ _, s => s
  | @MatAtom.exp _ _ _ _ _ _ ts, s =>
    ⟨s.1, fun ℓ => by
      rw [← dt.lvSet_congr vi hmir hval (ts ℓ)]
      exact s.2 ℓ⟩

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Nonempty A] [L.IsRelational] in
/-- **Transporting twice is transporting once**: the pack's content is its
points, and the proof it carries is irrelevant. -/
theorem ixKindSemCast_ixKindSemCast (zero one : A) (vi : dt.VarIx)
    {st st' st'' : TapeSt dt A R P I}
    (h1 : st.mir = st'.mir) (h2 : st.val = st'.val)
    (h3 : st'.mir = st''.mir) (h4 : st'.val = st''.val)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi)) (s : dt.IxKindSem (elt := elt) zero one vi st κ) :
    dt.ixKindSemCast zero one vi h3 h4 κ (dt.ixKindSemCast zero one vi h1 h2 κ s) =
      dt.ixKindSemCast zero one vi (h1.trans h3) (h2.trans h4) κ s := by
  cases κ <;> rfl

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Nonempty A] [L.IsRelational] in
/-- **A round trip of transports is the identity** — the shape the VAL
loop's bridge closes with: the pack leaves the round state, travels to the
round's own state and to the state its matrix threads, and comes back. -/
theorem ixKindSemCast_triple (zero one : A) (vi : dt.VarIx)
    {st₁ st₂ st₃ : TapeSt dt A R P I}
    (h1 : st₁.mir = st₂.mir) (h2 : st₁.val = st₂.val)
    (h3 : st₂.mir = st₃.mir) (h4 : st₂.val = st₃.val)
    (h5 : st₃.mir = st₁.mir) (h6 : st₃.val = st₁.val)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi)) (s : dt.IxKindSem (elt := elt) zero one vi st₁ κ) :
    dt.ixKindSemCast zero one vi h5 h6 κ
        (dt.ixKindSemCast zero one vi h3 h4 κ
          (dt.ixKindSemCast zero one vi h1 h2 κ s)) = s := by
  cases κ <;> rfl

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Nonempty A] [L.IsRelational] in
/-- **Transporting to the same state is doing nothing.** -/
theorem ixKindSemCast_self (zero one : A) (vi : dt.VarIx)
    {st : TapeSt dt A R P I} (h1 : st.mir = st.mir) (h2 : st.val = st.val)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi)) (s : dt.IxKindSem (elt := elt) zero one vi st κ) :
    dt.ixKindSemCast zero one vi h1 h2 κ s = s := by
  cases κ <;> rfl

open Classical in
/-- **The control one atom's machinery leaves behind**, by kind: the fold's
exit at the comparison's or the expansion atom's family, the verdict store
at the stage atom's read bit. -/
noncomputable def ixKindExitCtl :
    ∀ κ : MatAtom dt.X dt.d.B (dt.nOf vi),
      dt.IxKindSem (elt := elt) zero one vi st κ →
      dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim →
      dt.kindDepth κ ≤ dt.eDim → dt.kindReads κ ≤ dt.nfDim →
      (dt.CtlIx → A) → dt.CtlIx → A
  | .eq j₁ j₂, _, _, _, hrd, f =>
    (dt.cmpArgs zero one vi av hrd true j₁ j₂).exitSt
      (dt.cmpFam F zero one hhas vi av hrd true j₁ j₂ st v f (toLex topTup)
        (Fin.last 2))
      (dt.ixBack F.toLayout zero one dt.dd0Le st v)
  | .ord j₁ j₂, _, _, _, hrd, f =>
    (dt.cmpArgs zero one vi av hrd false j₁ j₂).exitSt
      (dt.cmpFam F zero one hhas vi av hrd false j₁ j₂ st v f (toLex topTup)
        (Fin.last 2))
      (dt.ixBack F.toLayout zero one dt.dd0Le st v)
  | .stage i ts, _, _, _, _, f =>
    (dt.stageArgs zero one vi i ts av).setAv
      (if st.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i)))
        then true else false)
      (dt.ixStageFAt F hhas one vi ts av st elt v f (dt.d.B.arity i))
      (dt.ixBack F.toLayout zero one dt.dd0Le
        (dt.ixStageAtSt st elt v
          (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i))))
        (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i))))
  | @MatAtom.exp _ _ _ _ k e ts, sem, hk, hn, hrd, f =>
    letI := Fintype.ofFinite dt.X.Tag
    (dt.expArgs zero one vi ts e av hk
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (dt.relPk e τ').n) (Finset.mem_univ τ)) hn)
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)).exitSt
      (fun ℓ => (sem.1 ℓ).1.1)
      (dt.ixExpFam F hhas one vi ts e av st (fun ℓ => (sem.1 ℓ).1.1) hk
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n) (Finset.mem_univ τ)) hn)
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd) v
        (dt.ixExpTagFam F hhas one vi ts e av st hk
          (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (dt.relPk e τ').n) (Finset.mem_univ τ)) hn)
          (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
          v f (Fin.last (k * Fintype.card dt.X.Tag)))
        (toLex topTup)
        (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1))))
      (dt.ixBack F.toLayout zero one dt.dd0Le st v)

variable {dt zero one vi av st v}

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **An atom's machinery is blind to the two scratch registers**: each
kind's loop reads the levels' register sets and its background at the
working cell, and each kind's exit reads the control alone
(`DescriptiveComplexity.Draw.Data.cmpArgs_exitSt_congr` and its two
siblings). The pack travels by
`DescriptiveComplexity.Draw.Data.kindSemCast`, which keeps its points.
This is the brick the whole threaded-versus-unthreaded bridge is built
from. -/
theorem ixKindExitCtl_congr_scratch {st' : TapeSt dt A R P I}
    (h : dt.ScratchEq st st')
    (hreg : ¬∃ u : I, v = F.cell u)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi)) (sem : dt.IxKindSem (elt := elt) zero one vi st κ)
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (f : dt.CtlIx → A) :
    dt.ixKindExitCtl F zero one hhas vi av st v κ sem hk hn hrd f =
      dt.ixKindExitCtl F zero one hhas vi av st' v κ
        (dt.ixKindSemCast zero one vi h.2.1 h.2.2.1 κ sem) hk hn hrd f := by
  classical
  cases κ with
  | eq j₁ j₂ =>
    refine Eq.trans (dt.cmpArgs_exitSt_congr zero one vi av hrd true j₁ j₂ _ _
      (dt.ixBack F.toLayout zero one dt.dd0Le st' v)) ?_
    rw [dt.cmpFam_congr_scratch F hrd h hreg]
    rfl
  | ord j₁ j₂ =>
    refine Eq.trans (dt.cmpArgs_exitSt_congr zero one vi av hrd false j₁ j₂ _ _
      (dt.ixBack F.toLayout zero one dt.dd0Le st' v)) ?_
    rw [dt.cmpFam_congr_scratch F hrd h hreg]
    rfl
  | stage i ts =>
    have hold : st.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i))) =
        st'.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st' with sav := ixMark elt v } (dt.d.B.arity i))) := by
      rw [← ixStageTgt_congr_scratch dt F hhas vi ts (v := v) (elt := elt) h
        (dt.d.B.arity i)]
      exact congrFun (congrFun h.2.2.2.1 i) _
    refine Eq.trans (dt.stageArgs_setAv_congr zero one vi i ts av _ _ _
      (dt.ixBack F.toLayout zero one dt.dd0Le
        (dt.ixStageAtSt st' elt v
          (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st' with sav := ixMark elt v } (dt.d.B.arity i))))
        (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st' with sav := ixMark elt v } (dt.d.B.arity i))))) ?_
    rw [if_congr (iff_of_eq hold) rfl rfl,
      ixStageFAt_congr_scratch dt F hhas vi ts one av (elt := elt) (v := v) h
        hreg f (dt.d.B.arity i)]
    rfl
  | @exp k e ts =>
    refine Eq.trans (dt.expArgs_exitSt_congr zero one vi ts e av hk _ _ _ _ _
      (dt.ixBack F.toLayout zero one dt.dd0Le st' v)) ?_
    rw [ixExpTagFam_congr_scratch (F := F) (hhas := hhas) (k := k) (hk := hk) h hreg,
      ixExpFam_congr_scratch (F := F) (hhas := hhas) (k := k) (hk := hk) h hreg]
    rfl

section Run

variable [Finite dt.KIx]
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = ixMark elt v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hsav : st.sav = ixMark elt v) (htgt : st.tgt = ixMark elt v)
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd), Use u →
  WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
variable (hvh : IxHolds elt Use v)
variable (hxdUse : ∀ {iv : dt.d.B.ι} (ℓ : Fin (dt.d.B.arity iv))
  (b : Lex (Fin dt.dd0 → A)), Use (dt.ixStageXD F hhasP ℓ b))
-- The widths a clocked stage atom is priced at: one for the copy rounds' read
-- and write trips, one for a step of the file, and the three the atom's passes,
-- resets and seeks are bounded by.
variable (w wG wP wR wK : ℕ)
variable (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
-- The reset and the seek are charged against the working area, not the tape:
-- both run at the marker or at the built TARGET, which lie below the file.
variable (hwR : ∀ s : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
variable (hwK : ∀ T : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe T (F.cell gbot) →
  wideRank T *
      (1 + (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) +
        (wideRank (F.cell gtop) + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
          wideRank (F.cell gbot) + 4)) + 1 +
    (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
      wideRank (F.cell gbot)) ≤ wK)
-- Every named register of the file is within `w` of the marker: the width a
-- walk to a cell is charged, uniform over the blocks and the tuples, and what
-- every atom's reads and the stage's copy loops are priced at.
variable (hcostR : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  2 * (wideRank (F.cell (F.toLayout.reg hhasP b c)) - wideRank v) + 2 ≤ w)

/-- **The state an atom leaves**: a stage atom normalizes SAV and TARGET to
the home address (its random access writes them whatever they held), every
other kind leaves the state alone. -/
noncomputable def ixKindEndSt (dt : Data L) {A R P I : Type}
    {elt : I → Univ A R P dt.KIx dt.dd}
    (vi : dt.VarIx) (v : Univ A R P dt.KIx dt.dd → Prop)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi)) (st : TapeSt dt A R P I) :
    TapeSt dt A R P I :=
  match κ with
  | .stage _ _ => dt.ixStageEndSt st elt v
  | _ => st

/-- **What one atom's machinery is charged**, by kind. A comparison walks its
two coordinate loops once per tuple, an expansion its tag flags and then its
leaf reads once per point of the evaluation order, both at the width `w` a walk
to a named register costs; a stage atom pays its nine trips and thirteen
dispatches over one copy loop per argument, at the widths the caller supplies.
The bound is uniform in the atom's data – the expansion's are bounded by
`ntgDim` and `nfDim` – which is what makes the sequencer's fold a single
width. -/
noncomputable def ixKindCost (dt : Data L) (A : Type)
    (vi : dt.VarIx) (w wP wR wK : ℕ) :
    MatAtom dt.X dt.d.B (dt.nOf vi) → ℕ
  | .eq _ _ => 1 + ((2 + (w + 2) * 2) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1)
  | .ord _ _ => 1 + ((2 + (w + 2) * 2) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1)
  | .exp _ _ => 1 + ((w + 2) * dt.ntgDim + 2 +
      ((2 + (w + 2) * dt.nfDim) * (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1))
  | .stage iv _ => 5 * wP + 2 * wR + 2 * wK +
      (((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 + 1) *
        dt.d.B.arity iv) + 13

include hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi hwkSt hmirSt
  hbotSt hmono hup he₀ hvh hxdUse hgap hwP hwR hwK hcostR in
/-- **The uniform stage discharge, threaded, on a clock**: as
`DescriptiveComplexity.Draw.Data.ixKind_hStage_thread` with the atom's cost
counted – `DescriptiveComplexity.Draw.Data.ixKindCost`, whatever the kind. -/
theorem ixKind_hStage_thread_reachesIn
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (sem : dt.IxKindSem (elt := elt) PR.zero PR.one vi st κ)
    {emb : dt.KindPh κ → P} {exitPh : P}
    {rEmb : ∀ s : dt.KindSite κ, dt.KindSh κ s → R}
    (hrules : ∀ (s : dt.KindSite κ) (ρ : dt.KindSh κ s),
      PR.rules (rEmb s ρ) = dt.kindRule PR.zero PR.one κ
        (dt.kindArgsOf PR.zero PR.one vi av κ hk hnd hrd) emb exitPh s ρ)
    (f : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (dt.ixKindCost A vi w wP wR wK κ)
      ⟨Sum.inr (PR.stElt (emb (dt.kindEntry κ)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixKindExitCtl F PR.zero PR.one hhasP vi av st v κ sem hk hnd hrd f)),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixKindEndSt (elt := elt) vi v κ st))
          (dt.ixKindEndSt (elt := elt) vi v κ st).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  cases κ with
  | eq j₁ j₂ =>
    exact dt.ixCmp_hStage F hhasP hsepP hix vi av hrd true j₁ j₂ hrules hR hlin hbot
      hv hvi hwkSt f w (fun b k => hcostR _ _)
  | ord j₁ j₂ =>
    exact dt.ixCmp_hStage F hhasP hsepP hix vi av hrd false j₁ j₂ hrules hR hlin hbot
      hv hvi hwkSt f w (fun b k => hcostR _ _)
  | stage i ts =>
    refine dt.ixStage_hStage_thread (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (hmono := hmono) (hup := hup) (helt := heltP)
      (vi := vi) (ts := ts) (av := av) (hrules := hrules) (hR := hR) (hlin := hlin)
      (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
      (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hmirSt := hmirSt)
      (hbotSt := hbotSt) (hvh := hvh) (hxdUse := fun ℓ b => hxdUse ℓ b)
      (b := _) (w := w) (wG := wG) (wP := wP) (wR := wR) (wK := wK)
      (hcost := fun _ _ => ⟨hcostR _ _, hcostR _ _⟩) (hgap := hgap)
      (hwP := hwP) (hwR := hwR) (hwK := hwK) (hb := ?_) (f := f)
    by_cases hbb : st.old i
      (ixAddr elt (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (dt.d.B.arity i)))
    · rw [if_pos hbb]
      exact ⟨fun _ => rfl, fun _ => hbb⟩
    · rw [if_neg hbb]
      exact ⟨fun h => absurd h hbb, fun h => nomatch h⟩
  | @exp k e ts =>
    obtain ⟨pts, hENC⟩ := sem
    have hent : emb (dt.kindEntry (MatAtom.exp e ts)) = tagFirstRd emb := by
      by_cases h : 0 < k * Fintype.card dt.X.Tag
      · rw [show dt.kindEntry (MatAtom.exp e ts) =
            TagPh.tagRdP ⟨0, h⟩ ReadPh.start from by
            rw [kindEntry]; exact dif_pos h,
          show (tagFirstRd emb : P) =
            emb (TagPh.tagRdP ⟨0, h⟩ ReadPh.start) from dif_pos h]
      · rw [show dt.kindEntry (MatAtom.exp e ts) = TagPh.brP from by
            rw [kindEntry]; exact dif_neg h,
          show (tagFirstRd emb : P) = emb TagPh.brP from dif_neg h]
    rw [hent]
    have hrd' : dt.relNr e (fun ℓ => (pts ℓ).1.1) ≤ dt.nfDim :=
      le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ _)) hrd
    have hk' : k * Fintype.card dt.X.Tag ≤ dt.ntgDim := hk
    refine TMData.ReachesIn.mono ?_
      (dt.ixExp_hStage F hhasP hsepP hix hinj heltP vi ts e av hk
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
      hrules hR hlin hbot hv hvi hwkSt pts hENC f w
      (fun _ => hcostR _ _) (fun _ _ => hcostR _ _))
    simp only [ixKindCost]
    gcongr

include hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi hwkSt hmirSt
  hbotSt hmono hup he₀ hvh hxdUse hgap hwP hwR hwK hcostR in
/-- **The uniform stage discharge, threaded**: as
`DescriptiveComplexity.Draw.Data.kind_hStage` but with no boundary
discipline assumed — the atom's exit state is
`DescriptiveComplexity.Draw.Data.kindEndSt`, which normalizes SAV and
TARGET exactly when the atom is a stage atom. -/
theorem ixKind_hStage_thread
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (sem : dt.IxKindSem (elt := elt) PR.zero PR.one vi st κ)
    {emb : dt.KindPh κ → P} {exitPh : P}
    {rEmb : ∀ s : dt.KindSite κ, dt.KindSh κ s → R}
    (hrules : ∀ (s : dt.KindSite κ) (ρ : dt.KindSh κ s),
      PR.rules (rEmb s ρ) = dt.kindRule PR.zero PR.one κ
        (dt.kindArgsOf PR.zero PR.one vi av κ hk hnd hrd) emb exitPh s ρ)
    (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (dt.kindEntry κ)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixKindExitCtl F PR.zero PR.one hhasP vi av st v κ sem hk hnd hrd f)),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixKindEndSt (elt := elt) vi v κ st))
          (dt.ixKindEndSt (elt := elt) vi v κ st).val)
          (PR.syElt PR.blank)⟩ :=
  (ixKind_hStage_thread_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
    (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup) (hvh := hvh)
    (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
    (hcostR := hcostR) (hwkSt := hwkSt) (hmirSt := hmirSt) (hbotSt := hbotSt)
    (κ := κ) (hk := hk) (hnd := hnd) (hrd := hrd) (sem := sem)
    (hrules := hrules) (f := f)).reflTransGen

include hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi hwkSt hmirSt
  hbotSt hsav htgt hmono hup he₀ hvh hxdUse hgap hwP hwR hwK hcostR in
/-- **The uniform stage discharge, on a clock**: as
`DescriptiveComplexity.Draw.Data.ixKind_hStage` with the atom's cost counted –
`DescriptiveComplexity.Draw.Data.ixKindCost`, whatever the kind. -/
theorem ixKind_hStage_reachesIn
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (sem : dt.IxKindSem (elt := elt) PR.zero PR.one vi st κ)
    {emb : dt.KindPh κ → P} {exitPh : P}
    {rEmb : ∀ s : dt.KindSite κ, dt.KindSh κ s → R}
    (hrules : ∀ (s : dt.KindSite κ) (ρ : dt.KindSh κ s),
      PR.rules (rEmb s ρ) = dt.kindRule PR.zero PR.one κ
        (dt.kindArgsOf PR.zero PR.one vi av κ hk hnd hrd) emb exitPh s ρ)
    (f : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (dt.ixKindCost A vi w wP wR wK κ)
      ⟨Sum.inr (PR.stElt (emb (dt.kindEntry κ)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixKindExitCtl F PR.zero PR.one hhasP vi av st v κ sem hk hnd hrd f)),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  cases κ with
  | eq j₁ j₂ =>
    exact dt.ixCmp_hStage F hhasP hsepP hix vi av hrd true j₁ j₂ hrules hR hlin hbot
      hv hvi hwkSt f w (fun b k => hcostR _ _)
  | ord j₁ j₂ =>
    exact dt.ixCmp_hStage F hhasP hsepP hix vi av hrd false j₁ j₂ hrules hR hlin hbot
      hv hvi hwkSt f w (fun b k => hcostR _ _)
  | stage i ts =>
    refine dt.ixStage_hStage (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (hmono := hmono) (hup := hup) (helt := heltP)
      (vi := vi) (ts := ts) (av := av) (hrules := hrules) (hR := hR) (hlin := hlin)
      (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
      (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hmirSt := hmirSt)
      (hbotSt := hbotSt) (hsav := hsav) (htgt := htgt) (hvh := hvh)
      (hxdUse := fun ℓ b => hxdUse ℓ b) (b := _) (w := w) (wG := wG) (wP := wP)
      (wR := wR) (wK := wK) (hcost := fun _ _ => ⟨hcostR _ _, hcostR _ _⟩)
      (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK) (hb := ?_) (f := f)
    by_cases hbb : st.old i
      (ixAddr elt (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (dt.d.B.arity i)))
    · rw [if_pos hbb]
      exact ⟨fun _ => rfl, fun _ => hbb⟩
    · rw [if_neg hbb]
      exact ⟨fun h => absurd h hbb, fun h => nomatch h⟩
  | @exp k e ts =>
    obtain ⟨pts, hENC⟩ := sem
    have hent : emb (dt.kindEntry (MatAtom.exp e ts)) = tagFirstRd emb := by
      by_cases h : 0 < k * Fintype.card dt.X.Tag
      · rw [show dt.kindEntry (MatAtom.exp e ts) =
            TagPh.tagRdP ⟨0, h⟩ ReadPh.start from by
            rw [kindEntry]; exact dif_pos h,
          show (tagFirstRd emb : P) =
            emb (TagPh.tagRdP ⟨0, h⟩ ReadPh.start) from dif_pos h]
      · rw [show dt.kindEntry (MatAtom.exp e ts) = TagPh.brP from by
            rw [kindEntry]; exact dif_neg h,
          show (tagFirstRd emb : P) = emb TagPh.brP from dif_neg h]
    rw [hent]
    have hrd' : dt.relNr e (fun ℓ => (pts ℓ).1.1) ≤ dt.nfDim :=
      le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ _)) hrd
    have hk' : k * Fintype.card dt.X.Tag ≤ dt.ntgDim := hk
    refine TMData.ReachesIn.mono ?_
      (dt.ixExp_hStage F hhasP hsepP hix hinj heltP vi ts e av hk
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
      hrules hR hlin hbot hv hvi hwkSt pts hENC f w
      (fun _ => hcostR _ _) (fun _ _ => hcostR _ _))
    simp only [ixKindCost]
    gcongr

include hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi hwkSt hmirSt
  hbotSt hsav htgt hmono hup he₀ hvh hxdUse hgap hwP hwR hwK hcostR in
/-- **The uniform stage discharge**: whatever the kind, the atom's machinery
runs from its entry phase one cell right of the marker to the exit phase
back there, leaving `DescriptiveComplexity.Draw.Data.kindExitCtl` in the
control and the tape untouched. -/
theorem ixKind_hStage
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (sem : dt.IxKindSem (elt := elt) PR.zero PR.one vi st κ)
    {emb : dt.KindPh κ → P} {exitPh : P}
    {rEmb : ∀ s : dt.KindSite κ, dt.KindSh κ s → R}
    (hrules : ∀ (s : dt.KindSite κ) (ρ : dt.KindSh κ s),
      PR.rules (rEmb s ρ) = dt.kindRule PR.zero PR.one κ
        (dt.kindArgsOf PR.zero PR.one vi av κ hk hnd hrd) emb exitPh s ρ)
    (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (dt.kindEntry κ)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixKindExitCtl F PR.zero PR.one hhasP vi av st v κ sem hk hnd hrd f)),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ :=
  (ixKind_hStage_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
    (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup) (hvh := hvh)
    (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
    (hcostR := hcostR) (hwkSt := hwkSt) (hmirSt := hmirSt) (hbotSt := hbotSt)
    (hsav := hsav) (htgt := htgt) (κ := κ) (hk := hk) (hnd := hnd) (hrd := hrd)
    (sem := sem) (hrules := hrules) (f := f)).reflTransGen

end Run

/-! ### The matrix, assembled -/

/-- **What the matrix charges one atom**: the largest of its atoms' costs.
A clocked caller that has no reason to prefer a coarser width takes this
one, and the fold's `(w + 2) * natOf vi + 1` is then a closed expression in
the file's widths. -/
noncomputable def ixMatCost (dt : Data L) (A : Type) (vi : dt.VarIx)
    (w wP wR wK : ℕ) : ℕ :=
  Finset.univ.sup fun a : Fin (dt.natOf vi) =>
    dt.ixKindCost A vi w wP wR wK (dt.kindOf vi a)

variable (dt zero one vi st v) in
/-- **The control thread across the matrix's atoms**: each atom's machinery
entered through the dispatch's `enterSt`, its exit control the next
atom's input. -/
noncomputable def ixMatFs
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (sem : ∀ a : Fin (dt.natOf vi),
      dt.IxKindSem (elt := elt) zero one vi st (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) : ℕ → dt.CtlIx → A
  | 0 => f₀
  | n + 1 =>
    if h : n < dt.natOf vi then
      dt.ixKindExitCtl F zero one hhas vi
        (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, h⟩) st v
        (dt.kindOf vi ⟨n, h⟩) (sem ⟨n, h⟩)
        (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, h⟩)
        (dt.kindDepth_le_eDim vi ⟨n, h⟩)
        (dt.kindReads_le_nfDim vi ⟨n, h⟩)
        (enterSt ⟨n, h⟩ (ixMatFs enterSt sem f₀ n)
          (dt.ixBack F.toLayout zero one dt.dd0Le st v))
    else ixMatFs enterSt sem f₀ n

/-! ### The threaded states of the matrix -/

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- An atom's exit state keeps the marker, the mirror, the bottom mark and
the VAL register: only SAV and TARGET can move. -/
theorem ixKindEndSt_fields (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (st : TapeSt dt A R P I) :
    (dt.ixKindEndSt (elt := elt) vi v κ st).wk = st.wk ∧
      (dt.ixKindEndSt (elt := elt) vi v κ st).mir = st.mir ∧
      (dt.ixKindEndSt (elt := elt) vi v κ st).bot = st.bot ∧
      (dt.ixKindEndSt (elt := elt) vi v κ st).val = st.val ∧
      (dt.ixKindEndSt (elt := elt) vi v κ st).old = st.old := by
  cases κ <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

variable (dt vi st v) in
/-- **The state after the matrix's first `n` atoms**: each stage atom
normalizes SAV and TARGET, the other kinds change nothing. -/
noncomputable def ixMatSt : ℕ → TapeSt dt A R P I
  | 0 => st
  | n + 1 =>
    if h : n < dt.natOf vi then
      dt.ixKindEndSt (elt := elt) vi v (dt.kindOf vi ⟨n, h⟩) (ixMatSt n)
    else ixMatSt n

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **The threaded states differ from the entry state in SAV and TARGET
alone** — so every hypothesis the atoms need at them is the entry state's.
-/
theorem ixMatSt_fields (n : ℕ) :
    (dt.ixMatSt (elt := elt) vi st v n).wk = st.wk ∧
      (dt.ixMatSt (elt := elt) vi st v n).mir = st.mir ∧
      (dt.ixMatSt (elt := elt) vi st v n).bot = st.bot ∧
      (dt.ixMatSt (elt := elt) vi st v n).val = st.val ∧
      (dt.ixMatSt (elt := elt) vi st v n).old = st.old := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [ixMatSt]
    split
    · obtain ⟨h1, h2, h3, h4, h5⟩ :=
        ixKindEndSt_fields (elt := elt) (v := v) (dt.kindOf vi _)
          (dt.ixMatSt (elt := elt) vi st v n)
      exact ⟨h1.trans ih.1, h2.trans ih.2.1, h3.trans ih.2.2.1,
        h4.trans ih.2.2.2.1, h5.trans ih.2.2.2.2⟩
    · exact ih

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **A tape state is determined by its two scratch registers**, given the
other seven — the shape every threaded state of the machinery has against
the state it started from. -/
theorem ixTapeSt_eq_savTgt {X Y : TapeSt dt A R P I} (hmir : X.mir = Y.mir)
    (hval : X.val = Y.val) (hold : X.old = Y.old) (hnew : X.new = Y.new)
    (hwk : X.wk = Y.wk) (hbot : X.bot = Y.bot) (hltp : X.ltp = Y.ltp) :
    X = { Y with sav := X.sav, tgt := X.tgt } := by
  obtain ⟨mir, tgt, sav, val, old, new, wk, bot, ltp⟩ := X
  obtain ⟨mir', tgt', sav', val', old', new', wk', bot', ltp'⟩ := Y
  simp only at hmir hval hold hnew hwk hbot hltp
  subst hmir; subst hval; subst hold; subst hnew; subst hwk; subst hbot
  subst hltp
  rfl

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **The remaining registers an atom leaves alone** — the three
`DescriptiveComplexity.Draw.Data.kindEndSt_fields` does not list, so
that the seven together pin the state down to its SAV and TARGET. -/
theorem ixKindEndSt_fields' (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (st : TapeSt dt A R P I) :
    (dt.ixKindEndSt (elt := elt) vi v κ st).new = st.new ∧
      (dt.ixKindEndSt (elt := elt) vi v κ st).ltp = st.ltp := by
  cases κ <;> exact ⟨rfl, rfl⟩

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- The same two, along the matrix's whole chain of atoms. -/
theorem ixMatSt_fields' (n : ℕ) :
    (dt.ixMatSt (elt := elt) vi st v n).new = st.new ∧
      (dt.ixMatSt (elt := elt) vi st v n).ltp = st.ltp := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [ixMatSt]
    split
    · obtain ⟨h1, h2⟩ :=
        ixKindEndSt_fields' (elt := elt) (v := v) (dt.kindOf vi _)
          (dt.ixMatSt (elt := elt) vi st v n)
      exact ⟨h1.trans ih.1, h2.trans ih.2⟩
    · exact ih

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **The matrix's threaded state is its entry state with the two scratch
registers rewritten** — the sharpening of
`DescriptiveComplexity.Draw.Data.matSt_fields` that lets the loop above
thread the two registers instead of the whole state, and with them keep
every semantic pack at the state it was built for. -/
theorem ixMatSt_eq (n : ℕ) :
    dt.ixMatSt (elt := elt) vi st v n =
      { st with
        sav := (dt.ixMatSt (elt := elt) vi st v n).sav
        tgt := (dt.ixMatSt (elt := elt) vi st v n).tgt } :=
  dt.ixTapeSt_eq_savTgt (ixMatSt_fields (elt := elt) (v := v) (st := st) n).2.1
    (ixMatSt_fields (elt := elt) (v := v) (st := st) n).2.2.2.1
    (ixMatSt_fields (elt := elt) (v := v) (st := st) n).2.2.2.2
    (ixMatSt_fields' (elt := elt) (v := v) (st := st) n).1
    (ixMatSt_fields (elt := elt) (v := v) (st := st) n).1
    (ixMatSt_fields (elt := elt) (v := v) (st := st) n).2.2.1
    (ixMatSt_fields' (elt := elt) (v := v) (st := st) n).2

section AvcRide

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A foreign verdict slot survives one atom's machinery**: whatever the
kind, its exit control writes its own verdict slot and scratch, never
another atom's. -/
theorem ixKindExitCtl_apply_avC
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (sem : dt.IxKindSem (elt := elt) zero one vi st κ)
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (f : dt.CtlIx → A) {a' : Fin dt.natMax}
    (hne : dt.avC a' ≠ dt.avC av) :
    dt.ixKindExitCtl F zero one hhas vi av st v κ sem hk hnd hrd f (dt.avC a') =
      f (dt.avC a') := by
  classical
  have hAcc : dt.avC a' ≠ dt.cmpAccC := fun h => nomatch h
  have hDec : dt.avC a' ≠ dt.cmpDecC := fun h => nomatch h
  have hVal : dt.avC a' ≠ dt.cmpValC := fun h => nomatch h
  have hSub : dt.avC a' ≠ dt.subLeafC := fun h => nomatch h
  have hBit : dt.avC a' ≠ dt.bitFlagC := fun h => nomatch h
  have hNotSac : ∀ j : Fin dt.eDim, dt.avC a' ≠ dt.sacC j :=
    fun j h => nomatch h
  have hcmpFold : ∀ (hnf : 2 ≤ dt.nfDim) (fc : dt.CtlIx → A),
      dt.cmpFold zero one hnf fc (dt.avC a') = fc (dt.avC a') := by
    intro hnf fc
    rw [cmpFold, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal]
  have hcmpFam : ∀ (hnf : 2 ≤ dt.nfDim) (isEq : Bool)
      (j₁ j₂ : Fin (dt.nOf vi)) (fc : dt.CtlIx → A),
      dt.cmpFam F zero one hhas vi av hnf isEq j₁ j₂ st v fc (toLex topTup)
        (Fin.last 2) (dt.avC a') = fc (dt.avC a') := by
    intro hnf isEq j₁ j₂ fc
    rw [cmpFam]
    refine elemFam_apply_of (dt.avC a') ?_ ?_ ?_ _ _ _ _
    · intro k bb fd g
      change dt.setCtl zero one (dt.cmpRdC hnf k) (bb = true) fd
        (dt.avC a') = _
      exact setCtl_of_ne
        (show dt.avC a' ≠ dt.cmpRdC hnf k from fun h => nomatch h) _ _
    · intro fd g
      change dt.cmpInit zero one (dt.initLvN fd) (dt.avC a') = _
      rw [cmpInit, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal,
        initLvN, putLv_av]
    · intro fd g
      change dt.advLvN (dt.cmpFold zero one hnf fd) (dt.avC a') = _
      rw [advLvN, putLv_av]
      exact hcmpFold hnf fd
  cases κ with
  | eq j₁ j₂ =>
    change dt.setCtl zero one (dt.avC av) _
      (dt.cmpFold zero one hrd
        (dt.cmpFam F zero one hhas vi av hrd true j₁ j₂ st v f (toLex topTup)
          (Fin.last 2))) (dt.avC a') = _
    rw [setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd true j₁ j₂ f)
  | ord j₁ j₂ =>
    change dt.setCtl zero one (dt.avC av) _
      (dt.cmpFold zero one hrd
        (dt.cmpFam F zero one hhas vi av hrd false j₁ j₂ st v f (toLex topTup)
          (Fin.last 2))) (dt.avC a') = _
    rw [setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd false j₁ j₂ f)
  | stage i ts =>
    change dt.setCtl zero one (dt.avC av) _
      (dt.ixStageFAt F hhas one vi ts av st elt v f (dt.d.B.arity i))
      (dt.avC a') = _
    rw [setCtl_of_ne hne]
    have hstage : ∀ n : ℕ,
        dt.ixStageFAt F hhas one vi ts av st elt v f n (dt.avC a') =
          f (dt.avC a') := by
      intro n
      induction n with
      | zero =>
        change dt.initLvN f (dt.avC a') = _
        rw [initLvN, putLv_av]
      | succ n ih =>
        by_cases h : n < dt.d.B.arity i
        · have hstep : dt.ixStageFAt F hhas one vi ts av st elt v f (n + 1) =
              tupleIter1 (dt.stageArgs zero one vi i ts av).setBit
                (dt.stageArgs zero one vi i ts av).initLv
                (dt.stageArgs zero one vi i ts av).advLv
                (dt.lvSet { st with sav := ixMark elt v } vi (ts ⟨n, h⟩)) v
                (dt.ixStageRestF F zero one { st with sav := ixMark elt v })
                (dt.ixStageXS F hhas vi ts ⟨n, h⟩) (dt.ixStageXD F hhas ⟨n, h⟩)
                (dt.ixStageTgt F hhas vi ts { st with sav := ixMark elt v } n)
                (dt.ixStageFAt F hhas one vi ts av st elt v f n)
                (toLex topTup) := by
            simp only [ixStageFAt]
            rw [dif_pos h]
          rw [hstep]
          refine (tupleIter1_apply_of (dt.avC a') ?_ ?_ ?_ _ _ _ _ _).trans ih
          · intro bb fd g
            change dt.setCtl zero one dt.bitFlagC (bb = true) fd
              (dt.avC a') = _
            exact setCtl_of_ne hBit _ _
          · intro fd g
            change dt.initLvN fd (dt.avC a') = _
            rw [initLvN, putLv_av]
          · intro fd g
            change dt.advLvN fd (dt.avC a') = _
            rw [advLvN, putLv_av]
        · have hstep : dt.ixStageFAt F hhas one vi ts av st elt v f (n + 1) =
              dt.ixStageFAt F hhas one vi ts av st elt v f n := by
            simp only [ixStageFAt]
            rw [dif_neg h]
          rw [hstep]
          exact ih
    exact hstage _
  | @exp k e ts =>
    change dt.setCtl zero one (dt.avC av) _
      (dt.setSubLeaf zero one _
        (dt.ixExpFam F hhas one vi ts e av st (fun ℓ => (sem.1 ℓ).1.1) hk _ _ v
          (dt.ixExpTagFam F hhas one vi ts e av st hk _ _ v f
            (Fin.last (k * Fintype.card dt.X.Tag)))
          (toLex topTup)
          (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))))
      (dt.avC a') = _
    rw [setCtl_of_ne hne, setSubLeaf, setCtl_of_ne hSub]
    refine Eq.trans (elemFam_apply_of (dt.avC a') ?_ ?_ ?_
      (dt.ixExpECell F hhas one vi ts e (fun ℓ => (sem.1 ℓ).1.1)
        (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n)
          (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hnd))
      (dt.ixExpTagFam F hhas one vi ts e av st hk
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
        v f (Fin.last (k * Fintype.card dt.X.Tag)))
      (toLex topTup)
      (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))) ?_
    · intro r bb fd g
      change dt.setCtl zero one
        (dt.rdfC (Fin.castLE
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hrd) r))
        (bb = true) fd (dt.avC a') = _
      exact setCtl_of_ne
        (show dt.avC a' ≠ dt.rdfC _ from fun h => nomatch h) _ _
    · intro fd g
      change dt.expInit zero one e (fun ℓ => (sem.1 ℓ).1.1) fd (dt.avC a')
        = _
      rw [expInit, initSac, putSac_of_not_sac hNotSac, initLvE, putLvE_av]
    · intro fd g
      change dt.expAdv zero one e (fun ℓ => (sem.1 ℓ).1.1) _ _ fd
        (dt.avC a') = _
      rw [expAdv, advLvE, putLvE_av, carrySac, putSac_of_not_sac hNotSac,
        setSubLeaf, setCtl_of_ne hSub]
    · refine chainSt_apply_of (dt.avC a') _ _ ?_ f
        ((Fin.last (k * Fintype.card dt.X.Tag) :
          Fin (k * Fintype.card dt.X.Tag + 1)) : ℕ)
      intro i bb fd
      change dt.setCtl zero one
        (dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2) (bb = true) fd
        (dt.avC a') = _
      exact setCtl_of_ne
        (show dt.avC a' ≠ dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2 from
          fun h => nomatch h) _ _

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- An expansion atom's exit at a foreign slot: the value rides through. -/
private theorem expExit_apply_of {k : ℕ} {e : dt.X.E.Relations k}
    {τ : Fin k → dt.X.Tag} {hn' : (dt.relPk e τ).n ≤ dt.eDim}
    {hrd' : dt.relNr e τ ≤ dt.nfDim} {a : Fin dt.natMax}
    {f' : dt.CtlIx → A} {q : dt.CtlIx}
    (hqa : q ≠ dt.avC a) (hqs : q ≠ dt.subLeafC) :
    dt.expExit zero one e τ hn' hrd' a f' q = f' q := by
  rw [expExit, setCtl_of_ne hqa, setSubLeaf, setCtl_of_ne hqs]

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **An accumulator slot survives one atom's machinery**: no atom's exit
control ever writes the inner fold's vector. -/
theorem ixKindExitCtl_apply_accC
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (sem : dt.IxKindSem (elt := elt) zero one vi st κ)
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (f : dt.CtlIx → A) (jj : Fin dt.naDim) :
    dt.ixKindExitCtl F zero one hhas vi av st v κ sem hk hnd hrd f (dt.accC jj) =
      f (dt.accC jj) := by
  classical
  have hne : dt.accC jj ≠ dt.avC av := fun h => nomatch h
  have hAcc : dt.accC jj ≠ dt.cmpAccC := fun h => nomatch h
  have hDec : dt.accC jj ≠ dt.cmpDecC := fun h => nomatch h
  have hVal : dt.accC jj ≠ dt.cmpValC := fun h => nomatch h
  have hSub : dt.accC jj ≠ dt.subLeafC := fun h => nomatch h
  have hBit : dt.accC jj ≠ dt.bitFlagC := fun h => nomatch h
  have hNotSac : ∀ j : Fin dt.eDim, dt.accC jj ≠ dt.sacC j :=
    fun j h => nomatch h
  have hcmpFold : ∀ (hnf : 2 ≤ dt.nfDim) (fc : dt.CtlIx → A),
      dt.cmpFold zero one hnf fc (dt.accC jj) = fc (dt.accC jj) := by
    intro hnf fc
    rw [cmpFold, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal]
  have hcmpFam : ∀ (hnf : 2 ≤ dt.nfDim) (isEq : Bool)
      (j₁ j₂ : Fin (dt.nOf vi)) (fc : dt.CtlIx → A),
      dt.cmpFam F zero one hhas vi av hnf isEq j₁ j₂ st v fc (toLex topTup)
        (Fin.last 2) (dt.accC jj) = fc (dt.accC jj) := by
    intro hnf isEq j₁ j₂ fc
    rw [cmpFam]
    refine elemFam_apply_of (dt.accC jj) ?_ ?_ ?_ _ _ _ _
    · intro k bb fd g
      change dt.setCtl zero one (dt.cmpRdC hnf k) (bb = true) fd
        (dt.accC jj) = _
      exact setCtl_of_ne
        (show dt.accC jj ≠ dt.cmpRdC hnf k from fun h => nomatch h) _ _
    · intro fd g
      change dt.cmpInit zero one (dt.initLvN fd) (dt.accC jj) = _
      rw [cmpInit, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal,
        initLvN, putLv_acc]
    · intro fd g
      change dt.advLvN (dt.cmpFold zero one hnf fd) (dt.accC jj) = _
      rw [advLvN, putLv_acc]
      exact hcmpFold hnf fd
  cases κ with
  | eq j₁ j₂ =>
    have hK : dt.ixKindExitCtl F zero one hhas vi av st v (.eq j₁ j₂) sem hk hnd hrd
        f =
        dt.setCtl zero one (dt.avC av)
          (dt.cmpVerdict one true (dt.cmpFold zero one hrd
            (dt.cmpFam F zero one hhas vi av hrd true j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))))
          (dt.cmpFold zero one hrd
            (dt.cmpFam F zero one hhas vi av hrd true j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))) := rfl
    rw [hK, setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd true j₁ j₂ f)
  | ord j₁ j₂ =>
    have hK : dt.ixKindExitCtl F zero one hhas vi av st v (.ord j₁ j₂) sem hk hnd hrd
        f =
        dt.setCtl zero one (dt.avC av)
          (dt.cmpVerdict one false (dt.cmpFold zero one hrd
            (dt.cmpFam F zero one hhas vi av hrd false j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))))
          (dt.cmpFold zero one hrd
            (dt.cmpFam F zero one hhas vi av hrd false j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))) := rfl
    rw [hK, setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd false j₁ j₂ f)
  | stage i ts =>
    have hstage : ∀ n : ℕ,
        dt.ixStageFAt F hhas one vi ts av st elt v f n (dt.accC jj) =
          f (dt.accC jj) := by
      intro n
      induction n with
      | zero =>
        change dt.initLvN f (dt.accC jj) = _
        rw [initLvN, putLv_acc]
      | succ n ih =>
        by_cases h : n < dt.d.B.arity i
        · have hstep : dt.ixStageFAt F hhas one vi ts av st elt v f (n + 1) =
              tupleIter1 (dt.stageArgs zero one vi i ts av).setBit
                (dt.stageArgs zero one vi i ts av).initLv
                (dt.stageArgs zero one vi i ts av).advLv
                (dt.lvSet { st with sav := ixMark elt v } vi (ts ⟨n, h⟩)) v
                (dt.ixStageRestF F zero one { st with sav := ixMark elt v })
                (dt.ixStageXS F hhas vi ts ⟨n, h⟩) (dt.ixStageXD F hhas ⟨n, h⟩)
                (dt.ixStageTgt F hhas vi ts { st with sav := ixMark elt v } n)
                (dt.ixStageFAt F hhas one vi ts av st elt v f n)
                (toLex topTup) := by
            simp only [ixStageFAt]
            rw [dif_pos h]
          rw [hstep]
          refine (tupleIter1_apply_of (dt.accC jj) ?_ ?_ ?_ _ _ _ _ _).trans ih
          · intro bb fd g
            change dt.setCtl zero one dt.bitFlagC (bb = true) fd
              (dt.accC jj) = _
            exact setCtl_of_ne hBit _ _
          · intro fd g
            change dt.initLvN fd (dt.accC jj) = _
            rw [initLvN, putLv_acc]
          · intro fd g
            change dt.advLvN fd (dt.accC jj) = _
            rw [advLvN, putLv_acc]
        · have hstep : dt.ixStageFAt F hhas one vi ts av st elt v f (n + 1) =
              dt.ixStageFAt F hhas one vi ts av st elt v f n := by
            simp only [ixStageFAt]
            rw [dif_neg h]
          rw [hstep]
          exact ih
    have hK : dt.ixKindExitCtl F zero one hhas vi av st v (.stage i ts) sem hk hnd
        hrd f =
        dt.setCtl zero one (dt.avC av)
          ((if st.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i)))
            then true else false) = true)
          (dt.ixStageFAt F hhas one vi ts av st elt v f (dt.d.B.arity i)) := rfl
    rw [hK, setCtl_of_ne hne]
    exact hstage _
  | @exp k e ts =>
    have hK : dt.ixKindExitCtl F zero one hhas vi av st v (.exp e ts) sem hk hnd hrd
        f =
        dt.expExit zero one e (fun ℓ => (sem.1 ℓ).1.1)
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (dt.relPk e τ').n)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hnd)
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hrd)
          av
          (dt.ixExpFam F hhas one vi ts e av st (fun ℓ => (sem.1 ℓ).1.1) hk
            (fun τ' => le_trans (Finset.le_sup
              (f := fun τ'' : Fin k → dt.X.Tag => (dt.relPk e τ'').n)
              (Finset.mem_univ τ')) hnd)
            (fun τ' => le_trans (Finset.le_sup
              (f := fun τ'' : Fin k → dt.X.Tag =>
                (blkAtoms (dt.relPk e τ'').mat).length)
              (Finset.mem_univ τ')) hrd) v
            (dt.ixExpTagFam F hhas one vi ts e av st hk
              (fun τ' => le_trans (Finset.le_sup
                (f := fun τ'' : Fin k → dt.X.Tag => (dt.relPk e τ'').n)
                (Finset.mem_univ τ')) hnd)
              (fun τ' => le_trans (Finset.le_sup
                (f := fun τ'' : Fin k → dt.X.Tag =>
                  (blkAtoms (dt.relPk e τ'').mat).length)
                (Finset.mem_univ τ')) hrd)
              v f (Fin.last (k * Fintype.card dt.X.Tag)))
            (toLex topTup)
            (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))) := rfl
    rw [hK, expExit_apply_of hne hSub]
    refine Eq.trans (elemFam_apply_of (dt.accC jj) ?_ ?_ ?_
      (dt.ixExpECell F hhas one vi ts e (fun ℓ => (sem.1 ℓ).1.1)
        (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n)
          (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hnd))
      (dt.ixExpTagFam F hhas one vi ts e av st hk
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
        v f (Fin.last (k * Fintype.card dt.X.Tag)))
      (toLex topTup)
      (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))) ?_
    · intro r bb fd g
      change dt.setCtl zero one
        (dt.rdfC (Fin.castLE
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hrd) r))
        (bb = true) fd (dt.accC jj) = _
      exact setCtl_of_ne
        (show dt.accC jj ≠ dt.rdfC _ from fun h => nomatch h) _ _
    · intro fd g
      change dt.expInit zero one e (fun ℓ => (sem.1 ℓ).1.1) fd (dt.accC jj)
        = _
      rw [expInit, initSac, putSac_of_not_sac hNotSac, initLvE, putLvE_acc]
    · intro fd g
      change dt.expAdv zero one e (fun ℓ => (sem.1 ℓ).1.1) _ _ fd
        (dt.accC jj) = _
      rw [expAdv, advLvE, putLvE_acc, carrySac, putSac_of_not_sac hNotSac,
        setSubLeaf, setCtl_of_ne hSub]
    · refine chainSt_apply_of (dt.accC jj) _ _ ?_ f
        ((Fin.last (k * Fintype.card dt.X.Tag) :
          Fin (k * Fintype.card dt.X.Tag + 1)) : ℕ)
      intro i bb fd
      change dt.setCtl zero one
        (dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2) (bb = true) fd
        (dt.accC jj) = _
      exact setCtl_of_ne
        (show dt.accC jj ≠ dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2 from
          fun h => nomatch h) _ _

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The inner fold's vector survives the whole matrix**: no atom writes
it, so the thread's accumulators after all atoms are the entry's. -/
theorem ixMatFs_apply_accC
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (hEnterAcc : ∀ (b : Fin (dt.natOf vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A) (jj : Fin dt.naDim),
      enterSt b f g (dt.accC jj) = f (dt.accC jj))
    (sem : ∀ b : Fin (dt.natOf vi),
      dt.IxKindSem (elt := elt) zero one vi st (dt.kindOf vi b))
    (f₀ : dt.CtlIx → A) (jj : Fin dt.naDim) (n : ℕ) :
    dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ n (dt.accC jj) =
      f₀ (dt.accC jj) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < dt.natOf vi
    · have hFa : dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ (n + 1) =
          dt.ixKindExitCtl F zero one hhas vi
            (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩) st v
            (dt.kindOf vi ⟨n, hn⟩) (sem ⟨n, hn⟩)
            (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, hn⟩)
            (dt.kindDepth_le_eDim vi ⟨n, hn⟩)
            (dt.kindReads_le_nfDim vi ⟨n, hn⟩)
            (enterSt ⟨n, hn⟩
              (dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ n)
              (dt.ixBack F.toLayout zero one dt.dd0Le st v)) := by
        simp only [ixMatFs]
        rw [dif_pos hn]
      rw [hFa, ixKindExitCtl_apply_accC F hhas _ _ _ _ _ _ jj, hEnterAcc]
      exact ih
    · have hFa : dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ (n + 1) =
          dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ n := by
        simp only [ixMatFs]
        rw [dif_neg hn]
      rw [hFa]
      exact ih


omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **An atom's verdict bit survives the rest of the matrix**: the thread's
value at atom `a`'s slot after all atoms is what atom `a`'s own machinery
wrote. -/
theorem ixMatFs_apply_avC
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (hEnterAv : ∀ (b : Fin (dt.natOf vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A) (a' : Fin dt.natMax),
      enterSt b f g (dt.avC a') = f (dt.avC a'))
    (sem : ∀ b : Fin (dt.natOf vi),
      dt.IxKindSem (elt := elt) zero one vi st (dt.kindOf vi b))
    (f₀ : dt.CtlIx → A) (a : Fin (dt.natOf vi)) :
    dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ (dt.natOf vi)
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) =
      dt.ixKindExitCtl F zero one hhas vi
        (Fin.castLE (dt.natOf_le_natMax vi) a) st v
        (dt.kindOf vi a) (sem a)
        (dt.kindArgs_mul_card_le_ntgDim vi a)
        (dt.kindDepth_le_eDim vi a)
        (dt.kindReads_le_nfDim vi a)
        (enterSt a (dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ (a : ℕ))
          (dt.ixBack F.toLayout zero one dt.dd0Le st v))
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) := by
  classical
  suffices h : ∀ n : ℕ, (a : ℕ) + 1 ≤ n → n ≤ dt.natOf vi →
      dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ n
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) =
      dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ ((a : ℕ) + 1)
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) by
    rw [h (dt.natOf vi) a.isLt le_rfl]
    simp only [ixMatFs]
    rw [dif_pos a.isLt]
  intro n h1 h2
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hstep : (a : ℕ) + 1 ≤ n
    · have hn : n < dt.natOf vi := by omega
      have hne : dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a) ≠
          dt.avC (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩) := by
        intro h
        have hcast : Fin.castLE (dt.natOf_le_natMax vi) a =
            Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩ := by
          injection h
        have hval := congrArg Fin.val hcast
        simp only [Fin.val_castLE] at hval
        omega
      have hFa : dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ (n + 1) =
          dt.ixKindExitCtl F zero one hhas vi
            (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩) st v
            (dt.kindOf vi ⟨n, hn⟩) (sem ⟨n, hn⟩)
            (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, hn⟩)
            (dt.kindDepth_le_eDim vi ⟨n, hn⟩)
            (dt.kindReads_le_nfDim vi ⟨n, hn⟩)
            (enterSt ⟨n, hn⟩
              (dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ n)
              (dt.ixBack F.toLayout zero one dt.dd0Le st v)) := by
        simp only [ixMatFs]
        rw [dif_pos hn]
      rw [hFa, ixKindExitCtl_apply_avC F hhas _ _ _ _ _ _ hne, hEnterAv]
      exact ih hstep (by omega)
    · have hn : n = (a : ℕ) := by omega
      subst hn
      rfl

end AvcRide

section PointVerdict

variable (dt zero one vi st) in
/-- **The semantic data of every atom, from one encoded valuation**: the
expansion atoms' points are the valuation's, everything else needs
nothing. -/
noncomputable def ixMkKindSem {elt : I → Univ A R P dt.KIx dt.dd}
    (w : Fin (dt.nOf vi) → dt.X.Map A)
    (hENC : ∀ j : Fin (dt.nOf vi),
      wmBlk (ixAddr elt (dt.lvSet st vi j))
        (Tag.arg (toLex (dt.lvBlk vi j)) : Tag R P dt.KIx) =
        encMap dt.ly zero one (w j)) :
    ∀ κ : MatAtom dt.X dt.d.B (dt.nOf vi), dt.IxKindSem (elt := elt) zero one vi st κ
  | .eq _ _ => PUnit.unit
  | .ord _ _ => PUnit.unit
  | .stage _ _ => PUnit.unit
  | @MatAtom.exp _ _ _ _ _ _ ts => ⟨fun ℓ => w (ts ℓ), fun ℓ => hENC (ts ℓ)⟩

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational] in
/-- **The transport of a built pack is the built pack**: `mkKindSem` puts
the valuation's points in and nothing else, and the proof components are
irrelevant. -/
theorem ixKindSemCast_ixMkKindSem (zero one : A) (vi : dt.VarIx)
    {st st' : TapeSt dt A R P I}
    (hmir : st.mir = st'.mir) (hval : st.val = st'.val)
    {w w' : Fin (dt.nOf vi) → dt.X.Map A} (hww : w = w')
    (hENC : ∀ j : Fin (dt.nOf vi),
      wmBlk (ixAddr elt (dt.lvSet st vi j))
        (Tag.arg (toLex (dt.lvBlk vi j)) : Tag R P dt.KIx) =
        encMap dt.ly zero one (w j))
    (hENC' : ∀ j : Fin (dt.nOf vi),
      wmBlk (ixAddr elt (dt.lvSet st' vi j))
        (Tag.arg (toLex (dt.lvBlk vi j)) : Tag R P dt.KIx) =
        encMap dt.ly zero one (w' j))
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi)) :
    dt.ixKindSemCast zero one vi hmir hval κ
        (ixMkKindSem (elt := elt) dt zero one vi st w hENC κ) =
      ixMkKindSem (elt := elt) dt zero one vi st' w' hENC' κ := by
  subst hww
  cases κ <;> rfl

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] in
include hinj helt in
/-- **One round's agreement is the padded bits'**: given the two registers
hold encodings, the machine's per-tuple question is the encodings'. -/
theorem ixCmpAgr_iff_padBits {j₁ j₂ : Fin (dt.nOf vi)} {p q : dt.X.Map A}
    (h1 : wmBlk (ixAddr elt (dt.lvSet st vi j₁))
      (Tag.arg (toLex (dt.lvBlk vi j₁)) : Tag R P dt.KIx) =
      encMap dt.ly zero one p)
    (h2 : wmBlk (ixAddr elt (dt.lvSet st vi j₂))
      (Tag.arg (toLex (dt.lvBlk vi j₂)) : Tag R P dt.KIx) =
      encMap dt.ly zero one q)
    (u : Lex (Fin dt.dd0 → A)) :
    dt.CmpAgr F zero hhas vi
        j₁ j₂ st u ↔
      (dt.padBits zero (encMap dt.ly zero one p) (ofLex u) ↔
        dt.padBits zero (encMap dt.ly zero one q) (ofLex u)) :=
  by
  rw [CmpAgr, cmpSet, cmpSet, cmpCell, cmpCell, if_pos rfl, if_pos rfl,
    if_neg (by decide : ¬(1 : Fin 2) = 0), if_neg (by decide : ¬(1 : Fin 2) = 0),
    ← ixAddr_elt hinj (dt.lvSet st vi j₁)
      (F.toLayout.reg hhas (dt.lvBlk vi j₁) (ofLex u)),
    ← ixAddr_elt hinj (dt.lvSet st vi j₂)
      (F.toLayout.reg hhas (dt.lvBlk vi j₂) (ofLex u)),
    helt, helt]
  exact iff_congr (iff_of_eq (congrFun h1 (pad zero (ofLex u))))
    (iff_of_eq (congrFun h2 (pad zero (ofLex u))))

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] in
include hinj helt in
/-- **The equality atom's verdict is point equality**: agreement at every
tuple decides the two encoded points. -/
theorem ixCmpAgr_all_iff (hzo : zero ≠ one)
    {j₁ j₂ : Fin (dt.nOf vi)} {p q : dt.X.Map A}
    (h1 : wmBlk (ixAddr elt (dt.lvSet st vi j₁))
      (Tag.arg (toLex (dt.lvBlk vi j₁)) : Tag R P dt.KIx) =
      encMap dt.ly zero one p)
    (h2 : wmBlk (ixAddr elt (dt.lvSet st vi j₂))
      (Tag.arg (toLex (dt.lvBlk vi j₂)) : Tag R P dt.KIx) =
      encMap dt.ly zero one q) :
    (∀ u : Lex (Fin dt.dd0 → A), dt.CmpAgr F zero hhas vi j₁ j₂ st u) ↔
      p = q := by
  rw [dt.encMap_eq_iff_padBits (zero := zero) (one := one) hzo]
  exact ⟨fun h w' => (ixCmpAgr_iff_padBits (F := F) (hinj := hinj) (hhas := hhas) (helt := helt)
      (h1 := h1) (h2 := h2) (toLex w')).mp (h _),
    fun h u => (ixCmpAgr_iff_padBits (F := F) (hinj := hinj) (hhas := hhas) (helt := helt)
      (h1 := h1) (h2 := h2) u).mpr (h _)⟩

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] in
include hinj helt in
/-- **The order atom's verdict is the chosen order**: agreement everywhere,
or a first difference with the second block holding the cell, is exactly
the binary order of the two encodings – the order the reduction puts on the
points. -/
theorem ixCmp_ord_iff (hzo : zero ≠ one)
    {j₁ j₂ : Fin (dt.nOf vi)} {p q : dt.X.Map A}
    (h1 : wmBlk (ixAddr elt (dt.lvSet st vi j₁))
      (Tag.arg (toLex (dt.lvBlk vi j₁)) : Tag R P dt.KIx) =
      encMap dt.ly zero one p)
    (h2 : wmBlk (ixAddr elt (dt.lvSet st vi j₂))
      (Tag.arg (toLex (dt.lvBlk vi j₂)) : Tag R P dt.KIx) =
      encMap dt.ly zero one q) :
    ((∀ u : Lex (Fin dt.dd0 → A), dt.CmpAgr F zero hhas vi j₁ j₂ st u) ∨
      ∃ u : Lex (Fin dt.dd0 → A), dt.CmpFst F zero hhas vi j₁ j₂ st u) ↔
      (encOrder dt.ly zero one hzo).le p q := by
  rw [dt.encOrder_le_iff_padBits hzo]
  simp only [CmpFst, cmpSet, cmpCell,
    ← ixAddr_elt hinj _ (F.toLayout.reg hhas _ _), helt]
  refine or_congr
    ⟨fun h w' => (ixCmpAgr_iff_padBits (F := F) (hinj := hinj) (hhas := hhas) (helt := helt)
      (h1 := h1) (h2 := h2) (toLex w')).mp (h _),
      fun h u => (ixCmpAgr_iff_padBits (F := F) (hinj := hinj) (hhas := hhas) (helt := helt)
      (h1 := h1) (h2 := h2) u).mpr (h _)⟩ ?_
  constructor
  · rintro ⟨u, ⟨hne, hlt⟩, hall⟩
    refine ⟨ofLex u, fun w' hw' => ?_, ?_, ?_⟩
    · have hlex : toLex w' < u := lex_lt_iff.mpr hw'
      exact (ixCmpAgr_iff_padBits (F := F) (hinj := hinj) (hhas := hhas) (helt := helt)
      (h1 := h1) (h2 := h2) (toLex w')).mp (hall _ hlex)
    · exact fun hc => hne ((iff_of_eq
        (congrFun h1 (pad zero (ofLex u)))).mpr hc)
    · exact (iff_of_eq (congrFun h2 (pad zero (ofLex u)))).mp hlt
  · rintro ⟨w', hall, hnp, hq⟩
    refine ⟨toLex w', ⟨?_, ?_⟩, fun u' hu' => ?_⟩
    · exact fun hc => hnp ((iff_of_eq
        (congrFun h1 (pad zero w'))).mp hc)
    · exact (iff_of_eq (congrFun h2 (pad zero w'))).mpr hq
    · exact (ixCmpAgr_iff_padBits (F := F) (hinj := hinj) (hhas := hhas) (helt := helt)
      (h1 := h1) (h2 := h2) u').mpr
        (hall (ofLex u') (lex_lt_iff.mp hu'))

section SelfRead

variable [LinearOrder (dt.X.Map A)]

set_option maxHeartbeats 1000000 in
-- the `exp` branch's defeq, the kind dispatch against the pack, is deep
omit [Finite I] in
omit [Fintype dt.SlotIx] in
include hinj helt in
/-- **One atom's own verdict bit is its truth**: whatever the kind, the bit
the exit control writes in the atom's slot is `MatAtom.holds` at the
encoded valuation. -/
theorem ctlBit_ixKindExitCtl_self (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (w : Fin (dt.nOf vi) → dt.X.Map A)
    (hENC : ∀ j : Fin (dt.nOf vi),
      wmBlk (ixAddr elt (dt.lvSet st vi j))
        (Tag.arg (toLex (dt.lvBlk vi j)) : Tag R P dt.KIx) =
        encMap dt.ly zero one (w j))
    (hOld : ∀ (i : dt.d.B.ι) (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf vi)),
      st.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i))) ↔
        σ i fun q => w (ts q))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (f : dt.CtlIx → A) :
    dt.ctlBit one
        (dt.ixKindExitCtl F zero one hhas vi av st v κ
          (ixMkKindSem (elt := elt) dt zero one vi st w hENC κ) hk hnd hrd f)
        (dt.avC av) ↔
      κ.holds σ w := by
  classical
  cases κ with
  | eq j₁ j₂ =>
    exact (dt.ctlBit_avC_cmp_exit F hrd hzo f _).trans
      (ixCmpAgr_all_iff (F := F) (hhas := hhas) (hinj := hinj) (helt := helt) hzo
        (hENC j₁) (hENC j₂))
  | ord j₁ j₂ =>
    refine (dt.ctlBit_avC_cmp_exit F hrd hzo f _).trans ?_
    exact (ixCmp_ord_iff (F := F) (hhas := hhas) (hinj := hinj) (helt := helt) hzo
        (hENC j₁) (hENC j₂)).trans
      (hordP (w j₁) (w j₂)).symm
  | stage i ts =>
    change dt.ctlBit one (dt.setCtl zero one (dt.avC av)
      ((if st.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i)))
        then true else false) = true)
      (dt.ixStageFAt F hhas one vi ts av st elt v f (dt.d.B.arity i)))
      (dt.avC av) ↔ _
    rw [ctlBit_setCtl_self hzo]
    refine Iff.trans ?_ (hOld i ts)
    by_cases hb : st.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i)))
    · rw [if_pos hb]
      exact ⟨fun _ => hb, fun _ => rfl⟩
    · rw [if_neg hb]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h hb⟩
  | @exp k e ts =>
    simp only [ixMkKindSem, ixKindExitCtl, MatAtom.holds]
    exact ctlBit_avC_ixExp_relMap (dt := dt) (F := F) (hhas := hhas) (one := one)
      (vi := vi) (ts := ts) (e := e) (av := av) (st := st) (hk := hk)
      (hn := fun τ => le_trans (Finset.le_sup
        (f := fun τ' : Fin k → dt.X.Tag => (dt.relPk e τ').n)
        (Finset.mem_univ τ)) hnd)
      (hrd := fun τ => le_trans (Finset.le_sup
        (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length)
        (Finset.mem_univ τ)) hrd)
      (vAdr := v) (hinj := hinj) (helt := helt) (hzo := hzo) (hlin := hlin)
      (pts := fun ℓ => w (ts ℓ)) (hENC := fun ℓ => hENC (ts ℓ))
      (dt.ixExpTagFam F hhas one vi ts e av st hk
        (fun τ => le_trans (Finset.le_sup
          (f := fun τ' : Fin k → dt.X.Tag => (dt.relPk e τ').n)
          (Finset.mem_univ τ)) hnd)
        (fun τ => le_trans (Finset.le_sup
          (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
          (Finset.mem_univ τ)) hrd)
        v f (Fin.last (k * Fintype.card dt.X.Tag)))

omit [Finite I] in
omit [Fintype dt.SlotIx] in
include hinj helt in
/-- **The matrix's verdicts, at the points**: after the whole matrix, atom
`a`'s slot holds `MatAtom.holds` of its kind at the encoded valuation –
the `hav` input of `DescriptiveComplexity.Draw.Data.postLeaf_iff_qfValue`
on the nose. -/
theorem ctlBit_avC_ixMatFs_holds (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (w : Fin (dt.nOf vi) → dt.X.Map A)
    (hENC : ∀ j : Fin (dt.nOf vi),
      wmBlk (ixAddr elt (dt.lvSet st vi j))
        (Tag.arg (toLex (dt.lvBlk vi j)) : Tag R P dt.KIx) =
        encMap dt.ly zero one (w j))
    (hOld : ∀ (i : dt.d.B.ι) (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf vi)),
      st.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
          { st with sav := ixMark elt v } (dt.d.B.arity i))) ↔
        σ i fun q => w (ts q))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (hEnterAv : ∀ (b : Fin (dt.natOf vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A) (a' : Fin dt.natMax),
      enterSt b f g (dt.avC a') = f (dt.avC a'))
    (f₀ : dt.CtlIx → A) (a : Fin (dt.natOf vi)) :
    dt.ctlBit one
        (dt.ixMatFs F zero one hhas vi st v enterSt
          (fun b => ixMkKindSem (elt := elt) dt zero one vi st w hENC (dt.kindOf vi b))
          f₀ (dt.natOf vi))
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) ↔
      (dt.kindOf vi a).holds σ w := by
  rw [ctlBit, ixMatFs_apply_avC (F := F) (hhas := hhas) (enterSt := enterSt) hEnterAv
    (fun b => ixMkKindSem (elt := elt) dt zero one vi st w hENC (dt.kindOf vi b)) f₀ a]
  exact ctlBit_ixKindExitCtl_self (F := F) (hhas := hhas) (hinj := hinj)
    (helt := helt) hzo hlin σ w hENC hOld hordP
    (dt.kindOf vi a)
    (dt.kindArgs_mul_card_le_ntgDim vi a)
    (dt.kindDepth_le_eDim vi a)
    (dt.kindReads_le_nfDim vi a)
    (enterSt a (dt.ixMatFs F zero one hhas vi st v enterSt
      (fun b => ixMkKindSem (elt := elt) dt zero one vi st w hENC (dt.kindOf vi b))
      f₀ (a : ℕ))
      (dt.ixBack F.toLayout zero one dt.dd0Le st v))

end SelfRead

end PointVerdict

section MatrixRun

variable [Finite dt.KIx]
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = ixMark elt v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hsav : st.sav = ixMark elt v) (htgt : st.tgt = ixMark elt v)
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd), Use u →
  WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
variable (hvh : IxHolds elt Use v)
variable (hxdUse : ∀ {iv : dt.d.B.ι} (ℓ : Fin (dt.d.B.arity iv))
  (b : Lex (Fin dt.dd0 → A)), Use (dt.ixStageXD F hhasP ℓ b))
-- The widths a clocked stage atom is priced at.
variable (w wG wP wR wK : ℕ)
variable (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
-- The reset and the seek are charged against the working area, not the tape:
-- both run at the marker or at the built TARGET, which lie below the file.
variable (hwR : ∀ s : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
variable (hwK : ∀ T : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe T (F.cell gbot) →
  wideRank T *
      (1 + (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) +
        (wideRank (F.cell gtop) + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
          wideRank (F.cell gbot) + 4)) + 1 +
    (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
      wideRank (F.cell gbot)) ≤ wK)
-- Every named register of the file is within `w` of the marker: the width a
-- walk to a cell is charged, uniform over the blocks and the tuples, and what
-- every atom's reads and the stage's copy loops are priced at.
variable (hcostR : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  2 * (wideRank (F.cell (F.toLayout.reg hhasP b c)) - wideRank v) + 2 ≤ w)
variable {emb : dt.MatrixPh vi → P} {exitPh : P}
variable {rEmb : ∀ i : dt.MatrixSite vi, dt.MatrixSh vi i → R}
variable (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
  dt.CtlIx → A)
variable (hrules : ∀ (i : dt.MatrixSite vi) (ρ : dt.MatrixSh vi i),
  PR.rules (rEmb i ρ) = dt.matrixRule PR.zero PR.one vi emb
    (fun a => dt.atomArgs PR.zero PR.one vi a) enterSt exitPh i ρ)
variable (sem : ∀ a : Fin (dt.natOf vi),
  dt.IxKindSem (elt := elt) PR.zero PR.one vi st (dt.kindOf vi a))
-- The width one atom of *this* matrix is charged: the largest of the four
-- kinds' costs, which a clocked caller supplies and a space-bounded one takes
-- as the finite supremum (`ixMatrix_run`).
variable (wA : ℕ)
variable (hwA : ∀ a : Fin (dt.natOf vi),
  dt.ixKindCost A vi w wP wR wK (dt.kindOf vi a) ≤ wA)

variable (dt zero one vi st v) in
/-- **The control thread across the matrix's atoms, threaded**: as
`DescriptiveComplexity.Draw.Data.matFs`, with each atom's exit control
computed at the state that atom actually runs at. -/
noncomputable def ixMatFsT
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (sem : ∀ a : Fin (dt.natOf vi),
      dt.IxKindSem (elt := elt) zero one vi (dt.ixMatSt (elt := elt) vi st v (a : ℕ))
        (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) : ℕ → dt.CtlIx → A
  | 0 => f₀
  | n + 1 =>
    if h : n < dt.natOf vi then
      dt.ixKindExitCtl F zero one hhas vi
        (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, h⟩)
        (dt.ixMatSt (elt := elt) vi st v n) v
        (dt.kindOf vi ⟨n, h⟩) (sem ⟨n, h⟩)
        (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, h⟩)
        (dt.kindDepth_le_eDim vi ⟨n, h⟩)
        (dt.kindReads_le_nfDim vi ⟨n, h⟩)
        (enterSt ⟨n, h⟩ (ixMatFsT enterSt sem f₀ n)
          (dt.ixBack F.toLayout zero one dt.dd0Le (dt.ixMatSt (elt := elt) vi st v n) v))
    else ixMatFsT enterSt sem f₀ n

omit [Finite I] in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- **A threaded state of the matrix is the entry state up to the two
scratch registers** — `matSt_eq` in the form the congruences take. -/
theorem ixScratchEq_matSt (n : ℕ) : dt.ScratchEq (dt.ixMatSt (elt := elt) vi st v n) st :=
  ⟨(ixMatSt_fields (elt := elt) (v := v) (st := st) n).1,
    (ixMatSt_fields (elt := elt) (v := v) (st := st) n).2.1,
    (ixMatSt_fields (elt := elt) (v := v) (st := st) n).2.2.2.1,
    (ixMatSt_fields (elt := elt) (v := v) (st := st) n).2.2.2.2,
    (ixMatSt_fields' (elt := elt) (v := v) (st := st) n).1,
    (ixMatSt_fields (elt := elt) (v := v) (st := st) n).2.2.1,
    (ixMatSt_fields' (elt := elt) (v := v) (st := st) n).2⟩

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite dt.KIx] in
/-- **The matrix is blind to the two scratch registers**: atom by atom,
`kindExitCtl_congr_scratch`. -/
theorem ixMatFs_congr_scratch {st' : TapeSt dt A R P I} (h : dt.ScratchEq st st')
    (hreg : ¬∃ u : I, v = F.cell u)
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (sem : ∀ a : Fin (dt.natOf vi), dt.IxKindSem (elt := elt) zero one vi st (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.ixMatFs F zero one hhas vi st v enterSt sem f₀ n =
      dt.ixMatFs F zero one hhas vi st' v enterSt
        (fun a => dt.ixKindSemCast zero one vi h.2.1 h.2.2.1 (dt.kindOf vi a)
          (sem a)) f₀ n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ixMatFs, ixMatFs]
    by_cases hn : n < dt.natOf vi
    · rw [dif_pos hn, dif_pos hn, ih, h.ixBack hreg]
      exact ixKindExitCtl_congr_scratch (F := F) (hhas := hhas) (h := h)
        (hreg := hreg) (κ := dt.kindOf vi ⟨n, hn⟩) (sem := sem ⟨n, hn⟩) _ _ _ _
    · rw [dif_neg hn, dif_neg hn, ih]

omit [Finite I] in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite dt.KIx] in
/-- **The threaded matrix is the unthreaded one**: an atom's machinery
reads the levels' registers and its background at the working cell
(`kindExitCtl_congr_scratch`), and the threading rewrites SAV and TARGET
alone. This is the bridge between the control the *run* produces and the
control the *semantics* is stated at. -/
theorem ixMatFsT_eq_ixMatFs (hreg : ¬∃ u : I, v = F.cell u)
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (semT : ∀ a : Fin (dt.natOf vi),
      dt.IxKindSem (elt := elt) zero one vi (dt.ixMatSt (elt := elt) vi st v (a : ℕ))
        (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.ixMatFsT F zero one hhas vi st v enterSt semT f₀ n =
      dt.ixMatFs F zero one hhas vi st v enterSt
        (fun a => dt.ixKindSemCast zero one vi
          (ixScratchEq_matSt (elt := elt) (a : ℕ)).2.1
          (ixScratchEq_matSt (elt := elt) (a : ℕ)).2.2.1
          (dt.kindOf vi a) (semT a)) f₀ n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ixMatFsT, ixMatFs]
    by_cases hn : n < dt.natOf vi
    · rw [dif_pos hn, dif_pos hn, ih,
        (ixScratchEq_matSt (elt := elt) n).ixBack hreg]
      exact ixKindExitCtl_congr_scratch (F := F) (hhas := hhas)
        (h := ixScratchEq_matSt (elt := elt) n) (hreg := hreg)
        (κ := dt.kindOf vi ⟨n, hn⟩) (sem := semT ⟨n, hn⟩) _ _ _ _
    · rw [dif_neg hn, dif_neg hn, ih]

include hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi hwkSt hmirSt
  hbotSt hrules hmono hup he₀ hvh hxdUse hgap hwP hwR hwK hcostR hwA in
/-- **The matrix's run, threaded, on a clock**: as
`DescriptiveComplexity.Draw.Data.ixMatrix_run_thread` with the atoms
counted – one atom's width, one dispatch and one step back per atom, and one
step to leave. -/
theorem ixMatrix_run_thread_reachesIn
    (semT : ∀ a : Fin (dt.natOf vi),
      dt.IxKindSem (elt := elt) PR.zero PR.one vi (dt.ixMatSt (elt := elt) vi st v (a : ℕ))
        (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn ((wA + 2) * dt.natOf vi + 1)
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixMatFsT F PR.zero PR.one hhasP vi st v enterSt semT f₀ (dt.natOf vi))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixMatSt (elt := elt) vi st v (dt.natOf vi)))
          (dt.ixMatSt (elt := elt) vi st v (dt.natOf vi)).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ (n : ℕ) r,
      dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixMatSt (elt := elt) vi st v n) r Slot.wk =
        bitVal PR.zero PR.one (r = v) := by
    intro n r
    rw [ixBack_wk, (ixMatSt_fields (elt := elt) (v := v) (st := st) n).1, hwkSt]
  have hchain := seq_reachesIn F.toIxFile hrules hR hlin hix hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun k => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixMatSt (elt := elt) vi st v (k : ℕ)))
    (mOf := fun k => (dt.ixMatSt (elt := elt) vi st v (k : ℕ)).val)
    (fun k r => hwkOf (k : ℕ) r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.ixMatFsT F PR.zero PR.one hhasP vi st v enterSt semT f₀ (j : ℕ))
    wA ?_
  · exact hchain
  · intro a
    refine TMData.ReachesIn.mono (hwA a) ?_
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hFa : dt.ixMatFsT F PR.zero PR.one hhasP vi st v enterSt semT f₀
          ((a : ℕ) + 1) =
        dt.ixKindExitCtl F PR.zero PR.one hhasP vi
          (Fin.castLE (dt.natOf_le_natMax vi) a)
          (dt.ixMatSt (elt := elt) vi st v (a : ℕ)) v
          (dt.kindOf vi a) (semT a)
          (dt.kindArgs_mul_card_le_ntgDim vi a)
          (dt.kindDepth_le_eDim vi a)
          (dt.kindReads_le_nfDim vi a)
          (enterSt a (dt.ixMatFsT F PR.zero PR.one hhasP vi st v enterSt semT f₀
              (a : ℕ))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              (dt.ixMatSt (elt := elt) vi st v (a : ℕ)) v)) := by
      simp only [ixMatFsT]
      rw [dif_pos a.isLt]
    have hSt : dt.ixMatSt (elt := elt) vi st v ((a : ℕ) + 1) =
        dt.ixKindEndSt (elt := elt) vi v (dt.kindOf vi a)
          (dt.ixMatSt (elt := elt) vi st v (a : ℕ)) := by
      simp only [ixMatSt]
      rw [dif_pos a.isLt]
    rw [hFa, hSt]
    obtain ⟨hw, hm, hb, -, -⟩ := ixMatSt_fields (elt := elt) (v := v) (st := st) (a : ℕ)
    exact ixKind_hStage_thread_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (heltP := heltP) (hR := hR) (hlin := hlin)
      (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
      (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup) (hvh := hvh)
      (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
      (hcostR := hcostR) (hwkSt := hw.trans hwkSt) (hmirSt := hm.trans hmirSt)
      (hbotSt := hb.trans hbotSt) (κ := dt.kindOf vi a)
      (hk := dt.kindArgs_mul_card_le_ntgDim vi a)
      (hnd := dt.kindDepth_le_eDim vi a)
      (hrd := dt.kindReads_le_nfDim vi a) (sem := semT a)
      (hrules := fun s ρ => hrules (.sub a s) ρ) (f :=
      enterSt a (dt.ixMatFsT F PR.zero PR.one hhasP vi st v enterSt semT f₀ (a : ℕ))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixMatSt (elt := elt) vi st v (a : ℕ)) v))

omit hwA in
include hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi hwkSt hmirSt
  hbotSt hrules hmono hup he₀ hvh hxdUse hgap hwP hwR hwK hcostR in
/-- **The matrix's run, threaded**: as
`DescriptiveComplexity.Draw.Data.ixMatrix_run` with no boundary discipline
assumed — the tape ends in the threaded state
`DescriptiveComplexity.Draw.Data.ixMatSt`, which differs from the entry
state in SAV and TARGET alone, and only if the matrix has a stage atom. -/
theorem ixMatrix_run_thread
    (semT : ∀ a : Fin (dt.natOf vi),
      dt.IxKindSem (elt := elt) PR.zero PR.one vi (dt.ixMatSt (elt := elt) vi st v (a : ℕ))
        (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixMatFsT F PR.zero PR.one hhasP vi st v enterSt semT f₀ (dt.natOf vi))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixMatSt (elt := elt) vi st v (dt.natOf vi)))
          (dt.ixMatSt (elt := elt) vi st v (dt.natOf vi)).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  exact (ixMatrix_run_thread_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
    (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup) (hvh := hvh)
    (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
    (hcostR := hcostR) (hwkSt := hwkSt) (hmirSt := hmirSt) (hbotSt := hbotSt)
    (hrules := hrules) (enterSt := enterSt)
    (wA := dt.ixMatCost A vi w wP wR wK)
    (hwA := fun a => Finset.le_sup (f := fun a' : Fin (dt.natOf vi) =>
      dt.ixKindCost A vi w wP wR wK (dt.kindOf vi a')) (Finset.mem_univ a))
    (semT := semT) (f₀ := f₀)).reflTransGen

include hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi hwkSt hmirSt
  hbotSt hsav htgt hrules hmono hup he₀ hvh hxdUse hgap hwP hwR hwK hcostR hwA in
/-- **The matrix's run, on a clock**: as
`DescriptiveComplexity.Draw.Data.ixMatrix_run` with the atoms counted – one
atom's width, one dispatch and one step back per atom, and one step to
leave. -/
theorem ixMatrix_reachesIn (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn ((wA + 2) * dt.natOf vi + 1)
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixMatFs F PR.zero PR.one hhasP vi st v enterSt sem f₀ (dt.natOf vi))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  have hchain := seq_reachesIn F.toIxFile hrules hR hlin hix hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun _ => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (mOf := fun _ => st.val)
    (fun _ r => hwkOf r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.ixMatFs F PR.zero PR.one hhasP vi st v enterSt sem f₀ (j : ℕ))
    wA ?_
  · exact hchain
  · intro a
    refine TMData.ReachesIn.mono (hwA a) ?_
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hFa : dt.ixMatFs F PR.zero PR.one hhasP vi st v enterSt sem f₀ ((a : ℕ) + 1) =
        dt.ixKindExitCtl F PR.zero PR.one hhasP vi
          (Fin.castLE (dt.natOf_le_natMax vi) a) st v
          (dt.kindOf vi a) (sem a)
          (dt.kindArgs_mul_card_le_ntgDim vi a)
          (dt.kindDepth_le_eDim vi a)
          (dt.kindReads_le_nfDim vi a)
          (enterSt a (dt.ixMatFs F PR.zero PR.one hhasP vi st v enterSt sem f₀ (a : ℕ))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)) := by
      simp only [ixMatFs]
      rw [dif_pos a.isLt]
    rw [hFa]
    exact ixKind_hStage_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix)
      (hinj := hinj) (heltP := heltP) (hR := hR) (hlin := hlin) (hord := hord)
      (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork) (hv := hv)
      (hvi := hvi) (hmono := hmono) (hup := hup) (hvh := hvh) (hxdUse := hxdUse)
      (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK) (hcostR := hcostR)
      (hwkSt := hwkSt) (hmirSt := hmirSt) (hbotSt := hbotSt) (hsav := hsav)
      (htgt := htgt) (κ := dt.kindOf vi a)
      (hk := dt.kindArgs_mul_card_le_ntgDim vi a)
      (hnd := dt.kindDepth_le_eDim vi a)
      (hrd := dt.kindReads_le_nfDim vi a) (sem := sem a)
      (hrules := fun s ρ => hrules (.sub a s) ρ)
      (f := enterSt a (dt.ixMatFs F PR.zero PR.one hhasP vi st v enterSt sem f₀ (a : ℕ))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))

omit hwA in
include hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi hwkSt hmirSt
  hbotSt hsav htgt hrules hmono hup he₀ hvh hxdUse hgap hwP hwR hwK hcostR in
/-- **The matrix's run**: from the checkpoint before the first atom at the
marker to the exit phase one cell to its right after the last, the verdict
slots holding each atom's fold, the tape untouched. -/
theorem ixMatrix_run (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixMatFs F PR.zero PR.one hhasP vi st v enterSt sem f₀ (dt.natOf vi))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  exact (ixMatrix_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
    (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup) (hvh := hvh)
    (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
    (hcostR := hcostR) (hwkSt := hwkSt) (hmirSt := hmirSt) (hbotSt := hbotSt)
    (hsav := hsav) (htgt := htgt) (hrules := hrules) (enterSt := enterSt)
    (wA := dt.ixMatCost A vi w wP wR wK)
    (hwA := fun a => Finset.le_sup (f := fun a' : Fin (dt.natOf vi) =>
      dt.ixKindCost A vi w wP wR wK (dt.kindOf vi a')) (Finset.mem_univ a))
    (sem := sem) (f₀ := f₀)).reflTransGen

end MatrixRun

/-! ### The gates, assembled -/

/-- **What one gate block's machinery is charged**: the file test's sweep of
the registers, the passing dispatch, the walk back and the tag flags, then the
domain evaluation's leaf reads once per point of the evaluation order. Uniform
in the block – the tag count and the read count are bounded by `ntgDim` and
`nfDim` – so the gate sequence's fold is a single width. -/
noncomputable def ixGateCost (dt : Data L) (A : Type) (w wP : ℕ) : ℕ :=
  wP + (1 + (1 + ((w + 2) * dt.ntgDim + 2 +
    ((2 + (w + 2) * dt.nfDim) * (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1))))

section GatesRun

variable (dt zero one vi st v) in
/-- **The control thread across the gates' blocks** (the all-pass path):
each block's machinery entered through the dispatch's `enterSt`, its
conjoining exit the next block's input. -/
noncomputable def ixGatesFs
    (bOf : Fin (dt.arOf vi) → Fin dt.ko ⊕ Fin dt.ki)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnG : ∀ t' : dt.X.Tag, (dt.domPk t').n ≤ dt.eDim)
    (hrdG : ∀ t' : dt.X.Tag, dt.domNr t' ≤ dt.nfDim)
    (tOf : Fin (dt.arOf vi) → dt.X.Tag)
    (enterSt : Fin (dt.arOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (f₀ : dt.CtlIx → A) : ℕ → dt.CtlIx → A
  | 0 => f₀
  | n + 1 =>
    if h : n < dt.arOf vi then
      (dt.gateArgs zero one (bOf ⟨n, h⟩) hc hnG hrdG).exitSt (tOf ⟨n, h⟩)
        (dt.ixGateFam F hhas one (bOf ⟨n, h⟩) st (tOf ⟨n, h⟩) hc hnG hrdG v
          (dt.ixGateTagFam F hhas one (bOf ⟨n, h⟩) st hc hnG hrdG v
            (enterSt ⟨n, h⟩ (ixGatesFs bOf hc hnG hrdG tOf enterSt f₀ n)
              (dt.ixBack F.toLayout zero one dt.dd0Le st v))
            (Fin.last (Fintype.card dt.X.Tag)))
          (toLex topTup) (Fin.last (dt.domNr (tOf ⟨n, h⟩))))
        (dt.ixBack F.toLayout zero one dt.dd0Le st v)
    else ixGatesFs bOf hc hnG hrdG tOf enterSt f₀ n

variable [Finite dt.KIx]
variable (bOf : Fin (dt.arOf vi) → Fin dt.ko ⊕ Fin dt.ki)
variable (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hnG : ∀ t' : dt.X.Tag, (dt.domPk t').n ≤ dt.eDim)
variable (hrdG : ∀ t' : dt.X.Tag, dt.domNr t' ≤ dt.nfDim)
variable (wellGOf : Fin (dt.arOf vi) → (dt.SlotIx → A) → Prop)
variable (setFail : (dt.CtlIx → A) → (dt.SlotIx → A) → dt.CtlIx → A)
variable {emb : dt.GatesPh vi → P} {failPh exitPh : P}
variable {rEmb : ∀ i : dt.GatesSite vi, dt.GatesSh vi i → R}
variable (enterSt : Fin (dt.arOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
  dt.CtlIx → A)
variable (hrules : ∀ (i : dt.GatesSite vi) (ρ : dt.GatesSh vi i),
  PR.rules (rEmb i ρ) = dt.gatesRule (one := PR.one) (v := vi) (emb := emb)
    (argsG := fun ℓ => dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG)
    (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
    (failPh := failPh) (exitPh := exitPh) i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v)
variable (TestOf : Fin (dt.arOf vi) → I → Prop)
variable (hcompatOf : ∀ (ℓ : Fin (dt.arOf vi)) (u : I),
  wellGOf ℓ (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    st.mir (F.cell u)) ↔ TestOf ℓ u)
variable {wG : ℕ} (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
-- The widths a clocked gate block is priced at: a walk to a named register,
-- and the sweep of the file its shape test makes.
variable (w wP : ℕ)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
variable (hcostR : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  2 * (wideRank (F.cell (F.toLayout.reg hhasP b c)) - wideRank v) + 2 ≤ w)
variable (tOf : Fin (dt.arOf vi) → dt.X.Tag)
variable (htagOf : ∀ ℓ : Fin (dt.arOf vi),
  dt.dspTagOf PR.zero PR.one
    (wmBlk (ixAddr elt st.mir) (Tag.arg (toLex (bOf ℓ)) : Tag R P dt.KIx)) =
  tOf ℓ)

omit hord in
include hrules hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hwkSt
  hcompatOf htagOf hgap hwP hcostR in
/-- **The gates' run at a gated address, on a clock**: as
`DescriptiveComplexity.Draw.Data.ixGates_run` with the blocks counted – one
block's width, its dispatch and the step back per block, and one step to
leave. -/
theorem ixGates_reachesIn (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((dt.ixGateCost A w wP + 2) * dt.arOf vi + 1)
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt f₀
            (dt.arOf vi))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  have hchain := seq_reachesIn F.toIxFile hrules hR hlin hix hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun _ => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (mOf := fun _ => st.val)
    (fun _ r => hwkOf r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt
      f₀ (j : ℕ))
    (dt.ixGateCost A w wP) ?_
  · exact hchain
  · intro ℓ
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hFa : dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt
        f₀ ((ℓ : ℕ) + 1) =
        (dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG).exitSt (tOf ℓ)
          (dt.ixGateFam F hhasP PR.one (bOf ℓ) st (tOf ℓ) hc hnG hrdG v
            (dt.ixGateTagFam F hhasP PR.one (bOf ℓ) st hc hnG hrdG v
              (enterSt ℓ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG
                tOf enterSt f₀ (ℓ : ℕ))
                (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup) (Fin.last (dt.domNr (tOf ℓ))))
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v) := by
      simp only [ixGatesFs]
      rw [dif_pos ℓ.isLt]
    rw [hFa]
    have hrules' : ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
        PR.rules (rEmb (.sub ℓ i) ρ) =
          dt.gateBlockRule (one := PR.one)
            (emb := fun p => emb (.sub ℓ p))
            (args := dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG)
            (wellG := wellGOf ℓ) (setFail := setFail)
            (failPh := failPh) (exitPh := emb (.chk ℓ.succ)) i ρ :=
      fun i ρ => hrules (.sub ℓ i) ρ
    have hrdt := hrdG (tOf ℓ)
    have hwPt := hwP
    refine TMData.ReachesIn.mono ?_
      (ixGateBlock_hStage_pos (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (helt := heltP) (b := bOf ℓ) (hc := hc)
      (hn := hnG) (hrd := hrdG) (wellG := wellGOf ℓ) (setFail := setFail)
      (hrules := hrules') (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
      (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (Test := TestOf ℓ)
      (hcompat := hcompatOf ℓ) (hgap := hgap) (t := tOf ℓ) (htag := htagOf ℓ)
      (hTest := hTestOf ℓ)
      (f := enterSt ℓ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG
        tOf enterSt f₀ (ℓ : ℕ))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
      (w := w) (hcostT := fun _ => hcostR _ _) (hcostE := fun _ _ => hcostR _ _))
    simp only [ixGateCost]
    gcongr

omit hord in
include hrules hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hwkSt
  hcompatOf htagOf hgap hwP hcostR in
/-- **The gates' run at a gated address**: every block passes its shape
test, every domain evaluation runs on its block's decoded tag, and the
sequence exits with the conjoined verdict in the flag. -/
theorem ixGates_run (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt f₀
            (dt.arOf vi))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ :=
  (ixGates_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
    (hinj := hinj) (heltP := heltP) (hrules := hrules) (hR := hR) (hlin := hlin)
    (htop := htop) (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt)
    (hcompatOf := hcompatOf) (htagOf := htagOf) (hgap := hgap) (hwP := hwP)
    (hcostR := hcostR) (hTestOf := hTestOf) (f₀ := f₀)).reflTransGen

omit hord in
include hrules hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hwkSt
  hcompatOf htagOf hgap hwP hcostR in
/-- **The gates' run at a junk address, on a clock**: as
`DescriptiveComplexity.Draw.Data.ixGates_run_fail` with the passing prefix
counted, the failing dispatch and the failing block's sweep on top. -/
theorem ixGates_reachesIn_fail (ℓ₀ : Fin (dt.arOf vi))
    (hTestLt : ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < (ℓ₀ : ℕ) → ∀ u, TestOf ℓ u)
    {u₀ : I} (hfail : ¬TestOf ℓ₀ u₀)
    (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((dt.ixGateCost A w wP + 2) * (ℓ₀ : ℕ) + (1 + (wP + 1)))
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt failPh
          (setFail
            (enterSt ℓ₀ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG
              tOf enterSt f₀ (ℓ₀ : ℕ))
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot F.toIxFile hlin hix hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  -- the passing prefix, up to the failing block's checkpoint
  have hpre := seq_reachesIn_prefix F.toIxFile hrules hR hlin hix hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun _ => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (mOf := fun _ => st.val)
    (fun _ r => hwkOf r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt
      f₀ (j : ℕ))
    (dt.ixGateCost A w wP) ℓ₀.castSucc ?_
  · refine hpre.trans ?_
    -- the dispatch into the failing block
    have hdsp : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.chk ℓ₀.castSucc))
            (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt
              f₀ ((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ))), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.sub ℓ₀ (Sum.inl .up)))
            (enterSt ℓ₀ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG
              tOf enterSt f₀ (ℓ₀ : ℕ))
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules (.chk ℓ₀.castSucc) .dspA
      have hlt : ((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ) < dt.arOf vi :=
        ℓ₀.isLt
      have hrule : dt.gatesRule (one := PR.one) (v := vi) (emb := emb)
          (argsG := fun ℓ => dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG)
          (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
          (failPh := failPh) (exitPh := exitPh) (.chk ℓ₀.castSucc) .dspA =
          { guard := fun _ g => g Slot.wk = PR.one ∧ g Slot.reg ≠ PR.one
            srcPh := emb (.chk ℓ₀.castSucc)
            dstPh := emb (.sub
              ⟨((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ), hlt⟩
              (Sum.inl .up))
            dstSt := enterSt
              ⟨((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ), hlt⟩
            wr := fun _ g => g
            moveRight := True } := dif_pos hlt
      rw [hrule] at h
      refine ⟨rEmb (.chk ℓ₀.castSucc) .dspA, ?_, by rw [h], by rw [h]; rfl,
        ?_, by rw [h], by rw [h]; trivial⟩
      · rw [h]
        constructor
        · rw [Prog.passTracks_of_ne hne_wk_val, hwkOf]
          exact bitVal_pos rfl
        · rw [Prog.passTracks_of_ne hne_rg_val,
            show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v Slot.reg =
              bitVal PR.zero PR.one
                (∃ u : I, v = F.cell u) from rfl,
            bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
          exact PR.zero_ne_one
      · rw [h]
        change enterSt ⟨((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ), hlt⟩ _
          (PR.passTracksAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val v) = _
        rw [passTracks_of_back (t := Slot.val)
          (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (m := st.val)
          F.toIxFile (fun r => rfl) v]
        rfl
    refine (TMData.reachesIn_of_step hdsp).trans ?_
    have hrules' : ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
        PR.rules (rEmb (.sub ℓ₀ i) ρ) =
          dt.gateBlockRule (one := PR.one)
            (emb := fun p => emb (.sub ℓ₀ p))
            (args := dt.gateArgs PR.zero PR.one (bOf ℓ₀) hc hnG hrdG)
            (wellG := wellGOf ℓ₀) (setFail := setFail)
            (failPh := failPh) (exitPh := emb (.chk ℓ₀.succ)) i ρ :=
      fun i ρ => hrules (.sub ℓ₀ i) ρ
    exact TMData.ReachesIn.mono (Nat.add_le_add_right hwP 1)
      (ixGateBlock_hStage_neg (F := F) (hix := hix)
      (b := bOf ℓ₀) (hc := hc) (hn := hnG) (hrd := hrdG) (wellG := wellGOf ℓ₀)
      (setFail := setFail) (hrules := hrules') (hR := hR) (hlin := hlin)
      (htop := htop) (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt)
      (Test := TestOf ℓ₀) (hcompat := hcompatOf ℓ₀) (hgap := hgap) (u := u₀)
      (hTest := hfail)
      (f := enterSt ℓ₀ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG
        tOf enterSt f₀ (ℓ₀ : ℕ))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))
  · -- the passing stages strictly below the failing block
    intro ℓ hℓ
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hFa : dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt
        f₀ ((ℓ : ℕ) + 1) =
        (dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG).exitSt (tOf ℓ)
          (dt.ixGateFam F hhasP PR.one (bOf ℓ) st (tOf ℓ) hc hnG hrdG v
            (dt.ixGateTagFam F hhasP PR.one (bOf ℓ) st hc hnG hrdG v
              (enterSt ℓ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG
                tOf enterSt f₀ (ℓ : ℕ))
                (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup) (Fin.last (dt.domNr (tOf ℓ))))
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v) := by
      simp only [ixGatesFs]
      rw [dif_pos ℓ.isLt]
    rw [hFa]
    have hrules' : ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
        PR.rules (rEmb (.sub ℓ i) ρ) =
          dt.gateBlockRule (one := PR.one)
            (emb := fun p => emb (.sub ℓ p))
            (args := dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG)
            (wellG := wellGOf ℓ) (setFail := setFail)
            (failPh := failPh) (exitPh := emb (.chk ℓ.succ)) i ρ :=
      fun i ρ => hrules (.sub ℓ i) ρ
    have hrdt := hrdG (tOf ℓ)
    have hwPt := hwP
    refine TMData.ReachesIn.mono ?_
      (ixGateBlock_hStage_pos (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (helt := heltP) (b := bOf ℓ) (hc := hc)
      (hn := hnG) (hrd := hrdG) (wellG := wellGOf ℓ) (setFail := setFail)
      (hrules := hrules') (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
      (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (Test := TestOf ℓ)
      (hcompat := hcompatOf ℓ) (hgap := hgap) (t := tOf ℓ) (htag := htagOf ℓ)
      (hTest := hTestLt ℓ hℓ)
      (f := enterSt ℓ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG
        tOf enterSt f₀ (ℓ : ℕ))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
      (w := w) (hcostT := fun _ => hcostR _ _) (hcostE := fun _ _ => hcostR _ _))
    simp only [ixGateCost]
    gcongr

omit hord in
include hrules hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hwkSt
  hcompatOf htagOf hgap hwP hcostR in
/-- **The gates' run at a junk address**: the blocks below `ℓ₀` pass, block
`ℓ₀`'s shape test fails, and the run leaves the whole gate sequence through
the failing exit with the fail store applied. -/
theorem ixGates_run_fail (ℓ₀ : Fin (dt.arOf vi))
    (hTestLt : ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < (ℓ₀ : ℕ) → ∀ u, TestOf ℓ u)
    {u₀ : I} (hfail : ¬TestOf ℓ₀ u₀)
    (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt failPh
          (setFail
            (enterSt ℓ₀ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG
              tOf enterSt f₀ (ℓ₀ : ℕ))
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ :=
  (ixGates_reachesIn_fail (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
    (hinj := hinj) (heltP := heltP) (hrules := hrules) (hR := hR) (hlin := hlin)
    (htop := htop) (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt)
    (hcompatOf := hcompatOf) (htagOf := htagOf) (hgap := hgap) (hwP := hwP)
    (hcostR := hcostR) (ℓ₀ := ℓ₀) (hTestLt := hTestLt) (hfail := hfail)
    (f₀ := f₀)).reflTransGen

omit [Finite dt.KIx] [Finite R] [Finite P] [Finite I] hrules hR hlin hord htop
  hbot hv hvi hwkSt hcompatOf htagOf hgap in
include hinj heltP in
/-- **The gates' verdict, characterized**: after the first `n` blocks of
the all-pass path, the flag holds exactly when it held at entry and every
gated block's decoded assignment satisfies its tag's domain sentence. -/
theorem ctlBit_gateFlagC_ixGatesFs (hzo : PR.zero ≠ PR.one)
    (hEnter : ∀ (ℓ : Fin (dt.arOf vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A),
      dt.ctlBit PR.one (enterSt ℓ f g) dt.gateFlagC ↔
        dt.ctlBit PR.one f dt.gateFlagC)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.ctlBit PR.one
        (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt f₀ n)
        dt.gateFlagC ↔
      (dt.ctlBit PR.one f₀ dt.gateFlagC ∧
        ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < n →
          ((∀ t' : dt.X.Tag,
            wmBlk (ixAddr elt st.mir) (Tag.arg (toLex (bOf ℓ)) : Tag R P dt.KIx)
              (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ) ∧
          ExpExpansion.DomHolds (X := dt.X)
            (tOf ℓ, decRho dt.ly PR.zero PR.one
              (wmBlk (ixAddr elt st.mir)
                (Tag.arg (toLex (bOf ℓ)) : Tag R P dt.KIx))))) := by
  induction n with
  | zero =>
    exact ⟨fun h => ⟨h, fun ℓ hℓ => absurd hℓ (Nat.not_lt_zero _)⟩,
      fun h => h.1⟩
  | succ n ih =>
    by_cases hlt : n < dt.arOf vi
    · have hstep : dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf
          enterSt f₀ (n + 1) =
          (dt.gateArgs PR.zero PR.one (bOf ⟨n, hlt⟩) hc hnG hrdG).exitSt
            (tOf ⟨n, hlt⟩)
            (dt.ixGateFam F hhasP PR.one (bOf ⟨n, hlt⟩) st (tOf ⟨n, hlt⟩) hc
              hnG hrdG v
              (dt.ixGateTagFam F hhasP PR.one (bOf ⟨n, hlt⟩) st hc hnG hrdG v
                (enterSt ⟨n, hlt⟩ (dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc
                  hnG hrdG tOf enterSt f₀ n)
                  (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup) (Fin.last (dt.domNr (tOf ⟨n, hlt⟩))))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v) := by
        simp only [ixGatesFs]
        rw [dif_pos hlt]
      rw [hstep, ctlBit_gateFlagC_ixGate_domHolds (F := F) (hhas := hhasP) (hinj := hinj)
        (helt := heltP) (b := bOf ⟨n, hlt⟩) (st := st) (t := tOf ⟨n, hlt⟩)
        (hc := hc) (hn := hnG) (hrd := hrdG) (vAdr := v) hzo _, hEnter, ih]
      constructor
      · rintro ⟨⟨h0, hall⟩, hn⟩
        refine ⟨h0, fun ℓ hℓ => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ with hℓn | hℓn
        · exact hall ℓ hℓn
        · have hℓeq : ℓ = ⟨n, hlt⟩ := Fin.ext hℓn
          rw [hℓeq]
          exact hn
      · rintro ⟨h0, hall⟩
        exact ⟨⟨h0, fun ℓ hℓ => hall ℓ (Nat.lt_succ_of_lt hℓ)⟩,
          hall ⟨n, hlt⟩ (Nat.lt_succ_self n)⟩
    · have hstep : dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf
          enterSt f₀ (n + 1) =
          dt.ixGatesFs F PR.zero PR.one hhasP vi st v bOf hc hnG hrdG tOf enterSt
            f₀ n := by
        simp only [ixGatesFs]
        rw [dif_neg hlt]
      rw [hstep, ih]
      refine and_congr Iff.rfl (forall_congr' fun ℓ => ?_)
      constructor
      · intro h hℓ
        exact h (lt_of_lt_of_le ℓ.isLt (Nat.le_of_not_lt hlt))
      · intro h hℓ
        exact h (Nat.lt_succ_of_lt hℓ)

end GatesRun

end KindStage

end Data

end Draw

end DescriptiveComplexity
