/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexSpine
import DescriptiveComplexity.Problems.Wide.BlkBridge
import DescriptiveComplexity.Problems.Wide.PfpIxWidth
import DescriptiveComplexity.Problems.Wide.PfpIxSpineSem

/-!
# The clocked evaluation at the file the program lays

`DescriptiveComplexity.Pfp.PfpData.nexIxEvalB_reachesIn` runs the clocked
evaluation at an *arbitrary* coarse file, and carries the file's coherences as
hypotheses: that its registers stand for elements, that their marks tell them
apart, that a walk to a named register costs `w`, and so on. Every one of those
is proved of the file a clocked program lays
(`DescriptiveComplexity.Pfp.PfpData.blkLaid`), so this file discharges them all
at once: `nexIxEvalB_blkLaid_reachesIn` asks only for what is genuinely the
*program's* – its rules, its marker, its VAL enumeration and its semantic packs
– and charges the run the file's own numbers, `blkW`, `blkWP`, `blkWR`, `blkWK`,
each of them the *stretch* `base + R` and not the tape.

The two hypotheses that had to be reshaped on the way are `hwork` – restated for
a *logical* address, which is what the stage atom proves of the TARGET it builds
(`workArg_blkLaid`) – and the reset's and the seek's widths, which are charged
against the working area below the file (`wR_blkLaid`, `wK_blkLaid`).
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

section Laid

variable {L : Language.{0, 0}} (dt : PfpData L) {A R B : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable [LinearOrder (NexPh B (EvalPh dt.nv dt.PMF))]
variable [Language.wide.Structure
  (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (NexPh B (EvalPh dt.nv dt.PMF))]
variable [Finite (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable [Finite dt.KIx]

/-! ### The four widths, in the file's own numbers -/

/-- **A walk to a named register**, out and back inside the stretch. -/
def blkW (base R : ℕ) : ℕ := 2 * (base + R) + 2

/-- **A sweep of the file**, up and back with the gap width one. -/
def blkWP (base R : ℕ) : ℕ := 2 * base + 3 * R + 3

/-- **A reset**: the scan below the marker, which is below the file. -/
def blkWR (base R : ℕ) : ℕ := base + R + 4

/-- **A seek**: a sweep of the file per bit of the target, the target and the
marker both below the file. -/
def blkWK (base R : ℕ) : ℕ :=
  (base + R) * (4 * (base + R) + 2 * R + 9) + 2 * (base + R) + R + 4

/-- **One number above all four widths of the laid file**: the stretch squared,
with room for the constants. The seek is the quadratic one – a sweep of the file
per bit of its target – and the other three are linear in the stretch. -/
def blkWidthBound (base R : ℕ) : ℕ := 16 * (base + R + 16) ^ 2

variable {dt}

/-! ### The widths against the clock -/

section WidthBound

variable {base R : ℕ}

theorem blkW_le : blkW base R ≤ blkWidthBound base R := by
  simp only [blkW, blkWidthBound, pow_two]
  nlinarith

theorem blkWP_le : blkWP base R ≤ blkWidthBound base R := by
  simp only [blkWP, blkWidthBound, pow_two]
  nlinarith

theorem blkWR_le : blkWR base R ≤ blkWidthBound base R := by
  simp only [blkWR, blkWidthBound, pow_two]
  nlinarith

theorem blkWK_le : blkWK base R ≤ blkWidthBound base R := by
  simp only [blkWK, blkWidthBound, pow_two]
  nlinarith

end WidthBound

omit [Fintype dt.SlotIx] [LinearOrder A] [Finite A] [Nonempty A] [L.IsRelational]
  [L.Structure A] [Finite dt.KIx] in
/-- **The tower's costs at the laid file are polynomial in one number**: the
`IxWidthBd` of `DescriptiveComplexity.Pfp.PfpData.ixLegWidth_le`, at the four
widths the laid file is charged. With it, the spine's width times its positions
is at most `q ^ 25`, and what an instantiation owes of the clock's first factor
is `q ^ 25 ≤ 2 ^ (k · m)`. -/
theorem ixWidthBd_blkLaid {base R q : ℕ} (hq : 16 ≤ q)
    (hwidth : blkWidthBound base R ≤ q)
    (hd0 : Nat.card (Lex (Fin dt.dd0 → A)) + 1 ≤ q)
    (heDim : Nat.card (Lex (Fin dt.eDim → A)) + 1 ≤ q)
    (hntg : dt.ntgDim ≤ q) (hnf : dt.nfDim ≤ q)
    (hnat : ∀ vi : dt.VarIx, dt.natOf vi ≤ q)
    (hnIn : ∀ vi : dt.VarIx, dt.nIn vi ≤ q)
    (harOf : ∀ vi : dt.VarIx, dt.arOf vi ≤ q)
    (harity : ∀ iv : dt.d.B.ι, dt.d.B.arity iv ≤ q)
    (hnv : dt.nv ≤ q) :
    dt.IxWidthBd A (blkW base R) (blkWP base R) (blkWR base R) (blkWK base R) q where
  cst := hq
  wLe := le_trans blkW_le hwidth
  wPLe := le_trans blkWP_le hwidth
  wRLe := le_trans blkWR_le hwidth
  wKLe := le_trans blkWK_le hwidth
  dd0Le := hd0
  eDimLe := heDim
  ntgLe := hntg
  nfLe := hnf
  natOfLe := hnat
  nInLe := hnIn
  arOfLe := harOf
  arityLe := harity
  nvLe := hnv

/-- **The clocked evaluation at the laid file**: the walk-back the opening's
dispatch owes, the branched spine over the spine's positions, and the exit into
the accepting phase, charged the file's own widths. This is
`DescriptiveComplexity.Pfp.PfpData.nexIxEvalB_reachesIn` with every coherence of
the file discharged; what is left is the program's own. -/
theorem nexIxEvalB_blkLaid_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    {rEmb : ∀ i : dt.SEF, dt.NexSESh i → R}
    (hrules : ∀ (i : dt.SEF) (ρ : dt.NexSESh i),
      PR.rules (rEmb i ρ) =
        dt.nexEvalRuleF (B := B) PR.zero PR.one
          (fun w => dt.varArgsOf PR.zero PR.one w) i ρ)
    (hR : PR.table.Reads)
    (hord : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {e₀ : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (he₀ : ∀ y, WMLe e₀ y)
    -- The file is based above the program's own data.
    (hlog : wideRank (logicalTop (R := R) (P := NexPh B (EvalPh dt.nv dt.PMF))
      (K := dt.KIx) (V := Fin dt.dd → A)) < base)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)))
    -- The marker is a *logical* address, so the registers of the file hold it.
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = PfpTag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → Wide.BlkIx dt.KIx A dt.dd → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.blkLaid h hpos hbase).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.blkLaid h hpos hbase).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.blkLaid h hpos hbase).blk (mV a) u)
    (stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).mir = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv),
      dt.ixGatedAt (PR := PR) (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
        (F := dt.blkLaid h hpos hbase) j (stOf j.castSucc) →
      ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF))
          (Wide.BlkIx dt.KIx A dt.dd)) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
          (dt.blkLaid h hpos hbase) PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
            (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v (b : ℕ))
          (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStB (PR := PR) (v := v)
        (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) (aT := aT)
        (dt.blkLaid h hpos hbase) blkIxElt_injective
        (hasName_blkLaid PR.zero h hpos hbase)
        (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlB (PR := PR) (v := v)
        (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) (aT := aT)
        (dt.blkLaid h hpos hbase) blkIxElt_injective
        (hasName_blkLaid PR.zero h hpos hbase)
        (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    -- The output's machinery: its rules, what its blocks look like at the state
    -- the spine leaves, and the verdict itself.
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → Wide.BlkIx dt.KIx A dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
        (u : Wide.BlkIx dt.KIx A dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt (dt.blkLaid h hpos hbase).cell Slot.mir
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one dt.dd0Le
            (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).mir ((dt.blkLaid h hpos hbase).cell u)) ↔
        TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
          (stOf (Fin.last dt.nv)).mir)
        (PfpTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          PfpTag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmirL : (stOf (Fin.last dt.nv)).mir =
      ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (hbotL : (stOf (Fin.last dt.nv)).bot = fun r => r = (fun _ => False))
    (hsavL : (stOf (Fin.last dt.nv)).sav =
      ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (htgtL : (stOf (Fin.last dt.nv)).tgt =
      ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
          (dt.blkLaid h hpos hbase) PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a))
          (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
              (stOf (Fin.last dt.nv)).mir)
            (PfpTag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              PfpTag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (hacc : (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.ixOutCtl (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
        (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
        (hasName_blkLaid PR.zero h hpos hbase)
        (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
        mV (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))) :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (blkW base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWP base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWR base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWK base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (blkW base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWP base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWR base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWK base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.val
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one dt.dd0Le
            (stOf 0)) (stOf 0).val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.acceptP
          (dt.ixOutCtl (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
            (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
            (hasName_blkLaid PR.zero h hpos hbase)
            (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
            mV (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))),
        Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.val
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV aT))) (mV aT))
          (PR.syElt PR.blank)⟩ :=
  dt.nexIxEvalOutB_reachesIn (F := dt.blkLaid h hpos hbase)
    (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
    (hinj := blkIxElt_injective)
    (hhasP := hasName_blkLaid PR.zero h hpos hbase)
    (heltP := fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
    (hsepP := nameSep_blkLaid PR.zero h hpos hbase dt.dd0Le)
    (hix := isLinOrd_blkLaid_le h hpos hbase)
    (he₀ := he₀) (hord := hord) (hrules := hrules) (hR := hR) (hlin := h)
    (gtop := blkTop A dt.KIx dt.dd) (gbot := blkBot A dt.KIx dt.dd)
    (htop := blkLe_blkTop A dt.KIx dt.dd)
    (hbot := blkLe_blkBot A dt.KIx dt.dd)
    (hwork := fun harg u => dt.workArg_blkLaid h hpos hbase hord hlog harg u)
    (hv := hv) (hvi := hvi) (Use := BlkIxUse A dt.KIx dt.dd)
    (hmono := fun u u' =>
      blkIxElt_mono (R := R) (P := NexPh B (EvalPh dt.nv dt.PMF)) (dd := dt.dd) hord u u')
    (hup := fun _ _ hu hlt =>
      blkIxElt_up (R := R) (P := NexPh B (EvalPh dt.nv dt.PMF)) (dd := dt.dd) hord hu hlt)
    (hvh := ixHolds_blkLaid hvlog)
    (hxdUse := fun _ _ => blkIxUse_reg_blkLaid PR.zero h hpos hbase _ _ _)
    (wG := 1) (hgap := fun _ _ hs => dt.gap_blkLaid h hpos hbase hs)
    (hwP := dt.wP_blkLaid h hpos hbase)
    (hwR := fun s hs => dt.wR_blkLaid h hpos hbase s hs)
    (hwK := fun T hT => dt.wK_blkLaid h hpos hbase T hT)
    (hcostR := fun b c => dt.costR_blkLaid h hpos hbase PR.zero _ v b c)
    (hbotV := hbotV) (htopV := htopV) (mV := mV) (hmV0 := hmV0) (hIncr := hIncr)
    (hTestT := hTestT) (hTestF := hTestF) (stOf := stOf) (fsOf := fsOf)
    (hwkOf := hwkOf) (hmirOf := hmirOf) (hbotOf := hbotOf) (semTJ := semTJ)
    (hst := hst) (hfs := hfs) (hrulesOut := hrulesOut) (TestOf := TestOf)
    (hcompatOf := hcompatOf) (tOf := tOf) (hwitOf := hwitOf) (hmirL := hmirL)
    (hbotL := hbotL) (hsavL := hsavL) (htgtL := htgtL) (semOf := semOf)
    (hDom := hDom) (hTestOf := hTestOf) (hacc := hacc)

/-! ### The thread at the laid file, with its packs supplied

What the theorem above still asks of the caller – the tape and control families
and their cover equations – is a *construction*, not a hypothesis: the generic
branched thread (`DescriptiveComplexity.Pfp.PfpData.ixSpineStOfB`) run with the
packs the two bridges build. This section supplies both, so that a clocked
program has only to name its entry state. -/

section Thread

variable {base : ℕ}

/-- **The packs at the laid file, built**: the conditioned family the branched
thread takes as a parameter, from the gates' bridge and the inner gates'
(`gateEnc_blkLaid`, `passEnc_blkLaid`) rather than assumed. -/
noncomputable def blkGatedSem
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    (hzo : PR.zero ≠ PR.one)
    {ιV : Type} (mV : ιV → Wide.BlkIx dt.KIx A dt.dd → Prop) :
    ∀ (w : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
      (j : Fin dt.nv)
      (st : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd)),
    dt.ixGatedAt (PR := PR) (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (F := dt.blkLaid h hpos hbase) j st →
    ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF))
        (Wide.BlkIx dt.KIx A dt.dd)) (a : ιV),
    (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
        (dt.blkLaid h hpos hbase) PR.zero PR.one (dt.varAt j)
        (dt.ixVarRdSt st p (mV a)) ℓ) →
    ∀ b : Fin (dt.natOf (dt.varAt j)),
      dt.IxKindSem PR.zero PR.one (dt.varAt j)
        (dt.ixMatSt (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
          (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
        (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) (dt.kindOf (dt.varAt j) b) :=
  fun w j st hg p a hp b =>
    dt.ixGatedSem (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (dt.blkLaid h hpos hbase)
      (fun vi stV ℓ => passEnc_blkLaid h hpos hbase hzo vi stV ℓ)
      (fun j' st' => gateEnc_blkLaid h hpos hbase hzo j' st')
      hzo h mV (v := w) j st hg p a hp b


/-- **The clocked evaluation at the laid file, with its thread**: the same run
as `nexIxEvalB_blkLaid_reachesIn` with the tape and control families
*constructed* – the branched thread at the packs the bridges build – so that a
program has only to name the state it enters the evaluation in. -/
theorem nexIxEvalB_blkLaid_thread_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    {rEmb : ∀ i : dt.SEF, dt.NexSESh i → R}
    (hrules : ∀ (i : dt.SEF) (ρ : dt.NexSESh i),
      PR.rules (rEmb i ρ) =
        dt.nexEvalRuleF (B := B) PR.zero PR.one
          (fun w => dt.varArgsOf PR.zero PR.one w) i ρ)
    (hR : PR.table.Reads) (hzo : PR.zero ≠ PR.one)
    (hord : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {e₀ : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (he₀ : ∀ y, WMLe e₀ y)
    (hlog : wideRank (logicalTop (R := R) (P := NexPh B (EvalPh dt.nv dt.PMF))
      (K := dt.KIx) (V := Fin dt.dd → A)) < base)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)))
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = PfpTag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → Wide.BlkIx dt.KIx A dt.dd → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.blkLaid h hpos hbase).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.blkLaid h hpos hbase).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.blkLaid h hpos hbase).blk (mV a) u)
    (st₀ : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (f₀ : dt.CtlIx → A)
    (hwk₀ : st₀.wk = fun r => r = v)
    (hmir₀ : st₀.mir = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    -- The state and the control the thread ends in, named so that the output's
    -- leg can be spoken of without spelling the thread out again.
    (stL : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid PR.zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
      mV st₀ f₀ (blkGatedSem h hpos hbase hzo mV) (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid PR.zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
      mV st₀ f₀ (blkGatedSem h hpos hbase hzo mV) (Fin.last dt.nv))
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → Wide.BlkIx dt.KIx A dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
        (u : Wide.BlkIx dt.KIx A dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt (dt.blkLaid h hpos hbase).cell Slot.mir
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one dt.dd0Le stL)
          stL.mir ((dt.blkLaid h hpos hbase).cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) stL.mir)
        (PfpTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          PfpTag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmirL : stL.mir = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (htgtL : stL.tgt = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
          (dt.blkLaid h hpos hbase) PR.zero PR.one none
          (dt.ixRoundSt stL (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none (dt.ixRoundSt stL (mV a))
          (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) stL.mir)
            (PfpTag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              PfpTag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (hacc : (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.ixOutCtl (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
        (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
        (hasName_blkLaid PR.zero h hpos hbase)
        (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
        mV stL tOf semOf fsL)) :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (blkW base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWP base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWR base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWK base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (blkW base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWP base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWR base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWK base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.val
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one dt.dd0Le st₀)
          st₀.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.acceptP
          (dt.ixOutCtl (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
            (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
            (hasName_blkLaid PR.zero h hpos hbase)
            (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
            mV stL tOf semOf fsL)),
        Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.val
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt stL (mV aT))) (mV aT)) (PR.syElt PR.blank)⟩ := by
  subst hstL
  subst hfsL
  exact nexIxEvalB_blkLaid_reachesIn h hpos hbase hrules hR hord he₀ hlog hv hvlog hvi
    hbotV htopV mV hmV0 hIncr hTestT hTestF
    (stOf := dt.ixSpineStOfB (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid PR.zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
      mV st₀ f₀ (blkGatedSem h hpos hbase hzo mV))
    (fsOf := dt.ixSpineFsOfB (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid PR.zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
      mV st₀ f₀ (blkGatedSem h hpos hbase hzo mV))
    (hwkOf := fun k => (dt.ixSpineStOfB_wk (elt := blkIxElt R _ dt.dd) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ k).trans hwk₀)
    (hmirOf := fun j => (dt.ixSpineStOfB_mir (elt := blkIxElt R _ dt.dd) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j.castSucc).trans hmir₀)
    (hbotOf := fun j => (dt.ixSpineStOfB_bot (elt := blkIxElt R _ dt.dd) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j.castSucc).trans hbot₀)
    (semTJ := fun j => dt.ixSpineSemOfB (elt := blkIxElt R _ dt.dd) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hst := fun j => dt.ixSpineStOfB_succ (elt := blkIxElt R _ dt.dd) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hfs := fun j => dt.ixSpineFsOfB_succ (elt := blkIxElt R _ dt.dd) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hrulesOut := hrulesOut) (TestOf := TestOf) (hcompatOf := hcompatOf)
    (tOf := tOf) (hwitOf := hwitOf) (hmirL := hmirL) (hbotL := hbotL)
    (hsavL := hsavL) (htgtL := htgtL) (semOf := semOf) (hDom := hDom)
    (hTestOf := hTestOf) (hacc := hacc)


section Realize

variable [LinearOrder (dt.X.Map A)]

/-- **The clocked evaluation at the laid file, from the sentence alone**: the
run above with the output's leg discharged. The output variable is *nullary*, so
everything its leg asks about argument blocks is vacuous – there are none – and
the one thing left is its verdict, which `ixOutAcc_iff_out` reads as the
expansion's output sentence at the stage the tracks hold. So what a program has
to bring to its own evaluation is the entry state, the enumeration, the stage
its guess wrote, and the sentence being true. -/
theorem nexIxEvalOut_blkLaid_realize_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    {rEmb : ∀ i : dt.SEF, dt.NexSESh i → R}
    (hrules : ∀ (i : dt.SEF) (ρ : dt.NexSESh i),
      PR.rules (rEmb i ρ) =
        dt.nexEvalRuleF (B := B) PR.zero PR.one
          (fun w => dt.varArgsOf PR.zero PR.one w) i ρ)
    (hR : PR.table.Reads) (hzo : PR.zero ≠ PR.one)
    (hord : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {e₀ : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (he₀ : ∀ y, WMLe e₀ y)
    (hlog : wideRank (logicalTop (R := R) (P := NexPh B (EvalPh dt.nv dt.PMF))
      (K := dt.KIx) (V := Fin dt.dd → A)) < base)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)))
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = PfpTag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → Wide.BlkIx dt.KIx A dt.dd → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.blkLaid h hpos hbase).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.blkLaid h hpos hbase).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.blkLaid h hpos hbase).blk (mV a) u)
    (st₀ : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (f₀ : dt.CtlIx → A)
    (hwk₀ : st₀.wk = fun r => r = v)
    (hmir₀ : st₀.mir = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    (stL : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid PR.zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
      mV st₀ f₀ (blkGatedSem h hpos hbase hzo mV) (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid PR.zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
      mV st₀ f₀ (blkGatedSem h hpos hbase hzo mV) (Fin.last dt.nv))
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (hmirL : stL.mir = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (htgtL : stL.tgt = ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v)
    -- What the verdict is read against: the stage the guess wrote, the
    -- enumeration's own facts, and the order on the expanded universe.
    {Use : Wide.BlkIx dt.KIx A dt.dd → Prop}
    (hUse : ∀ (a : ιV) (u : Wide.BlkIx dt.KIx A dt.dd), mV a u → Use u)
    (hmono : ∀ u u', WMLt (dt.blkLaid h hpos hbase).le u u' ↔
      WMLt WMLe (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd u)
        (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd u'))
    (hup : ∀ (u : Wide.BlkIx dt.KIx A dt.dd)
        (x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      Use u → WMLt WMLe (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd u) x →
      ∃ u', Use u' ∧ blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd u' = x)
    (hKin : ∀ (a : ιV) (t : PfpTag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (w : Fin dt.dd → A),
      ixAddr (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) (mV a) (t, w) →
        ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1)
      (ixAddr (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {Below : (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R)
        (P := NexPh B (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (stL.old iv (tupAddr dt.ly PR.zero PR.one (R := R)
        (P := NexPh B (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
        (dt.ixStageTgt (dt.blkLaid h hpos hbase) (hasName_blkLaid PR.zero h hpos hbase)
          none ts
          { dt.ixRoundSt stL (mV a) with
            sav := ixMark (blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd) v }
          (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hout : @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out) :
    ∃ (fq : dt.CtlIx → A) (cT : Config (WPoint (Univ A R
      (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))),
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (blkW base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWP base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWR base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (blkWK base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (blkW base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWP base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWR base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (blkWK base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.val
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one dt.dd0Le st₀)
          st₀.val) (PR.syElt PR.blank)⟩
      cT ∧ cT.state = Sum.inr (PR.stElt NexPh.acceptP fq) ∧
      (dt.varArgsOf PR.zero PR.one none).accBit fq := by
  have hA := (dt.ixOutAcc_iff_out (elt := blkIxElt R _ dt.dd)
      (F := dt.blkLaid h hpos hbase) (hinj := blkIxElt_injective)
      (hhasP := hasName_blkLaid PR.zero h hpos hbase)
      (heltP := fun b c => blkIxElt_reg_blkLaid PR.zero h hpos hbase _ b c)
      (hix := isLinOrd_blkLaid_le h hpos hbase)
      (hblkP := dt.blk_blkLaid_eq_tagBlk h hpos hbase) (hmono := hmono)
      (hup := hup)
      (hpassEnc := fun vi stV ℓ => passEnc_blkLaid h hpos hbase hzo vi stV ℓ)
      (mV := mV) (hUse := hUse) (v := v) (hlin := h) (hord := hord)
      (hbotV := hbotV) (hmV0 := hmV0) (hIncr := hIncr) (hKin := hKin)
      (hTop := hTop) (σ := σ) (st := stL) (hdict := hdict) (hbelow := hbelow)
      (hordP := hordP) (tOf := Fin.elim0) (f₀ := fsL)).mpr hout
  exact ⟨_, _, nexIxEvalB_blkLaid_thread_reachesIn h hpos hbase hrules hR hzo hord he₀ hlog hv
    hvlog hvi hbotV htopV mV hmV0 hIncr hTestT hTestF st₀ f₀ hwk₀ hmir₀ hbot₀
    stL fsL hstL hfsL (hrulesOut := hrulesOut) (TestOf := fun ℓ _ => ℓ.elim0)
    (hcompatOf := fun ℓ _ => ℓ.elim0) (tOf := Fin.elim0)
    (hwitOf := fun ℓ _ => ℓ.elim0) (hmirL := hmirL) (hbotL := hbotL)
    (hsavL := hsavL) (htgtL := htgtL)
    (semOf := fun a hp b => dt.ixPassSem
      (elt := blkIxElt R (NexPh B (EvalPh dt.nv dt.PMF)) dt.dd)
      (F := dt.blkLaid h hpos hbase)
      (hpassEnc := fun vi stV ℓ => passEnc_blkLaid h hpos hbase hzo vi stV ℓ)
      none (dt.ixRoundSt stL (mV a)) hp (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) b)
    (hDom := fun ℓ => ℓ.elim0) (hTestOf := fun ℓ _ => ℓ.elim0) (hacc := hA),
    rfl, hA⟩

end Realize

end Thread

end Laid

end PfpData

end Pfp

end DescriptiveComplexity
