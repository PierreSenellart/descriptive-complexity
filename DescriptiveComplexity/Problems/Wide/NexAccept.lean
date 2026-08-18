/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexLaid
import DescriptiveComplexity.Problems.Wide.NexRun
import DescriptiveComplexity.Problems.Wide.NexInterp

/-!
# The clocked program's run, at the program itself

The opening and the evaluation are proved of an *arbitrary* program whose rules
are the clocked ones; here they are read at
`DescriptiveComplexity.Draw.Data.nexProg` – the program a reduction actually
emits – so that what is left of each is what the *instance* decides and nothing
about rule names.

Three things are discharged in passing: the rule hypotheses (the program's rules
at a rule name are the rules the run lemmas name – `nexProg_rules` and its two
specializations, all `rfl`), the file-laying sweep's bottom block (the layout's
least block is the blockless one, `fst_blkBot`, so the *constant* `none` a
definable rule set needs is the block the sweep resets to), and the state the
program enters its opening in (`nexEntrySt`, whose fields the evaluation's entry
hypotheses ask about).
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

section OpeningAt

variable {L : Language.{0, 0}} {dt : Data L} {A : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [Nonempty A] [Finite A] [Finite dt.KIx] [Nonempty dt.KIx]
variable [L.IsRelational] [L.Structure A] [LinearOrder (dt.X.Map A)]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [LinearOrder (dt.NexRIx (G := dt.d.B.ι → Bool))]
variable [Finite (dt.NexRIx (G := dt.d.B.ι → Bool))]
variable [Language.wide.Structure (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {zero one : A}

variable (dt) in
/-- **The program a clocked reduction emits**: the outer layer at the
file-laying sweep and the region-guessing one, over the shared tower's
evaluation, resetting to the blockless register (`fst_blkBot`). -/
@[reducible] noncomputable def nexProgAt (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (coord : Fin dt.dd → dt.CtlIx) :
    Prog A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      dt.CtlIx dt.SlotIx dt.KIx dt.dd :=
  dt.nexProg zero one hzo hpl coord (dt.buildSpec zero one coord)
    (dt.regionSpec zero one) (fun w => dt.varArgsOf zero one w) none

omit [LinearOrder (dt.X.Map A)] in
/-- **The clocked program's opening, at the program**: `reachesIn_openingRegion_entry`
with the rule hypothesis discharged (`nexProg_rules`), the sweep's bottom block
read as the constant `none` (`fst_blkBot`), the head starting on the empty
address and the pointer on the file's first register. What is left is what the
*guess* decides – the tracks `σ` it writes, empty outside the region – and the
region facts of the layout. -/
theorem nexProg_reachesIn_opening (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx} (hcoord : Function.Injective coord)
    (hR : (dt.nexProgAt hzo hpl coord).table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    {v' v₁ x s₀ top : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hle : WMSetLe WMLe (fun _ => False)
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkTop A dt.KIx dt.dd)))
    (hvi₁ : WMIncr WMLe (fun _ => False) v₁) (hwalk : WMSetLe WMLe v₁ x)
    (hxb : WMIncr WMLe x
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)))
    (hs₀ : WMIncr WMLe (fun _ => False) s₀)
    (hvi' : WMIncr WMLe (fun _ => False) v')
    (σ : dt.d.B.ι →
      (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) → Prop)
    (htop : WMSetLe WMLe s₀ top)
    (htopne : ∃ y, top y)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r top → ¬σ i r)
    (hexB : dt.exitG one ((dt.nexProgAt hzo hpl coord).passTracksAt
      (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
      (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout zero one
        dt.dd0Le (dt.nexEntrySt (fun _ => False))) (fun _ => False)
      (fun _ => False)))
    (hexG : dt.exitG one ((dt.nexProgAt hzo hpl coord).passTracksAt
      (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
      (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout zero one
        dt.dd0Le { dt.nexEntrySt (fun _ => False) with old := σ })
      (fun _ => False) (fun _ => False))) :
    (wideData (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (2 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 2 * base +
        ((wideRank top - wideRank s₀) + wideRank top) + 4)
      ⟨Sum.inr ((dt.nexProgAt hzo hpl coord).stElt NexPh.start
          (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)),
        Sum.inl fun _ => False,
        wideTape ((dt.nexProgAt hzo hpl coord).trackTapeAt
          (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
          (fun _ _ => zero) (fun _ => False))
          ((dt.nexProgAt hzo hpl coord).syElt
            (dt.nexProgAt hzo hpl coord).blank)⟩
      ⟨Sum.inr ((dt.nexProgAt hzo hpl coord).stElt
          (NexPh.evalP (.chk 0))
          (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)),
        Sum.inl v',
        wideTape ((dt.nexProgAt hzo hpl coord).trackTapeAt
          (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
          (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout zero one
            dt.dd0Le { dt.nexEntrySt (fun _ => False) with old := σ })
            (fun _ => False))
          ((dt.nexProgAt hzo hpl coord).syElt
            (dt.nexProgAt hzo hpl coord).blank)⟩ :=
  dt.reachesIn_openingRegion_entry (f₀ := fun _ => zero)
    (ruleE := dt.nexEvalRuleF zero one (fun w => dt.varArgsOf zero one w)) (evalEntry := .chk 0)
    hcoord hR h hpos hbase (wideRank_bot h) hle hvi₁ hwalk hxb hs₀ hvi' σ htop
    htopne hout (by exact hexB) (by exact hexG)
    (rEmb0 := fun i ρ => ⟨i, ρ⟩)
    (fun i ρ => by
      rw [fst_blkBot]
      exact nexProg_rules hzo hpl i ρ)


/-- **The packs at the laid file, at the emitted program**: `blkGatedSem` with
the program named in the *type*, so that a statement mentioning it carries no
metavariable. Without this the elaborator has nothing to pin the program with
inside a hypothesis, the program occurring there only under `Prog.zero` and
`Prog.one`, which reduce. -/
noncomputable def blkGatedSemAt (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (coord : Fin dt.dd → dt.CtlIx)
    (h : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    {ιV : Type} (mV : ιV → Wide.BlkIx dt.KIx A dt.dd → Prop) :
    ∀ (w : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
      (j : Fin dt.nv)
      (st : TapeSt dt A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd)),
    dt.ixGatedAt (PR := dt.nexProgAt hzo hpl coord)
      (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
      (F := dt.blkLaid h hpos hbase) j st →
    ∀ (p : IxScratch dt A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (Wide.BlkIx dt.KIx A dt.dd)) (a : ιV),
    (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
        (dt.blkLaid h hpos hbase) zero one (dt.varAt j)
        (dt.ixVarRdSt st p (mV a)) ℓ) →
    ∀ b : Fin (dt.natOf (dt.varAt j)),
      dt.IxKindSem zero one (dt.varAt j)
        (dt.ixMatSt (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
          (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
        (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
        (dt.kindOf (dt.varAt j) b) :=
  blkGatedSem h hpos hbase hzo mV


omit [Nonempty dt.KIx] in
/-- **The clocked evaluation, at the program**: the run at the laid file with
its two rule hypotheses discharged – the program's rule at an evaluation site is
the spine's, and at the output machinery's sites the output variable's, both by
`rfl` – and the verdict stated: the control it stops in is one the program's
accepting predicate holds of. -/
theorem nexProg_reachesIn_eval {base : ℕ} (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (coord : Fin dt.dd → dt.CtlIx)
    (h : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    (hR : (dt.nexProgAt hzo hpl coord).table.Reads)
    (hord : ∀ x y : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {e₀ : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (he₀ : ∀ y, WMLe e₀ y)
    (hlog : wideRank (logicalTop (R := dt.NexRIx (G := dt.d.B.ι → Bool))
      (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (K := dt.KIx) (V := Fin dt.dd → A)) < base)
    {v v' : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)))
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = Tag.arg i)
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
    (st₀ : TapeSt dt A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (f₀ : dt.CtlIx → A)
    (hwk₀ : st₀.wk = fun r => r = v)
    (hmir₀ : st₀.mir = ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    (stL : TapeSt dt A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid zero h hpos hbase _ b c)
      mV st₀ f₀ (dt.blkGatedSemAt hzo hpl coord h hpos hbase mV) (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := v) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid zero h hpos hbase _ b c)
      mV st₀ f₀ (dt.blkGatedSemAt hzo hpl coord h hpos hbase mV) (Fin.last dt.nv))
    (hmirL : stL.mir = ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) v)
    (htgtL : stL.tgt = ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) v)
    -- What the verdict is read against: the stage the guess wrote, the
    -- enumeration's own facts, and the order on the expanded universe.
    {Use : Wide.BlkIx dt.KIx A dt.dd → Prop}
    (hUse : ∀ (a : ιV) (u : Wide.BlkIx dt.KIx A dt.dd), mV a u → Use u)
    (hmono : ∀ u u', WMLt (dt.blkLaid h hpos hbase).le u u' ↔
      WMLt WMLe (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd u)
        (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd u'))
    (hup : ∀ (u : Wide.BlkIx dt.KIx A dt.dd)
        (x : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      Use u → WMLt WMLe (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd u) x →
      ∃ u', Use u' ∧ blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd u' = x)
    (hKin : ∀ (a : ιV) (t : Tag (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx)
        (w : Fin dt.dd → A),
      ixAddr (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) (mV a) (t, w) →
        ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1)
      (ixAddr (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {Below : (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly zero one (R := dt.NexRIx (G := dt.d.B.ι → Bool))
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (stL.old iv (tupAddr dt.ly zero one (R := dt.NexRIx (G := dt.d.B.ι → Bool))
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
        (dt.ixStageTgt (dt.blkLaid h hpos hbase) (hasName_blkLaid zero h hpos hbase)
          none ts
          { dt.ixRoundSt stL (mV a) with
            sav := ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) v }
          (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hout : @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out) :
    ∃ (fq : dt.CtlIx → A) (cT : Config (WPoint (Univ A
      (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))),
    (wideData (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
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
      ⟨Sum.inr ((dt.nexProgAt hzo hpl coord).stElt (NexPh.evalP (.chk 0)) f₀),
        Sum.inl v',
        wideTape ((dt.nexProgAt hzo hpl coord).trackTapeAt
          (dt.blkLaid h hpos hbase).cell Slot.val
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout
            (dt.nexProgAt hzo hpl coord).zero (dt.nexProgAt hzo hpl coord).one
            dt.dd0Le st₀)
          st₀.val) ((dt.nexProgAt hzo hpl coord).syElt
            (dt.nexProgAt hzo hpl coord).blank)⟩
      cT ∧ cT.state = Sum.inr
        ((dt.nexProgAt hzo hpl coord).stElt NexPh.acceptP fq) ∧
      (dt.varArgsOf (dt.nexProgAt hzo hpl coord).zero
        (dt.nexProgAt hzo hpl coord).one none).accBit fq :=
  dt.nexIxEvalOut_blkLaid_realize_reachesIn h hpos hbase
    (rEmb := fun i ρ => ⟨.eval i, ρ⟩) (fun _ _ => rfl) hR hzo hord he₀ hlog hv
    hvlog hvi hbotV htopV mV hmV0 hIncr hTestT hTestF st₀ f₀ hwk₀ hmir₀ hbot₀
    stL fsL hstL hfsL (rEmbO := fun i ρ => ⟨.eval (.sub (Sum.inr i)), ρ⟩)
    (hrulesOut := fun _ _ => rfl) (hmirL := hmirL) (hbotL := hbotL)
    (hsavL := hsavL) (htgtL := htgtL) (hUse := hUse) (hmono := hmono)
    (hup := hup) (hKin := hKin) (hTop := hTop) σ (hdict := hdict)
    (hbelow := hbelow) (hordP := hordP) (hout := hout)

/-! ### The evaluation

The evaluation's own run (`nexIxEvalOut_blkLaid_realize_reachesIn`) is *not*
restated here. Its rule hypotheses are discharged at the program by `rfl` –
`(rEmb := fun i ρ => ⟨.eval i, ρ⟩)` for the spine and
`(rEmbO := fun i ρ => ⟨.eval (.sub (Sum.inr i)), ρ⟩)` for the output machinery,
because `nexProg`'s rule at a name *is* the rule the run lemma names – but the
program itself is best left to the *caller's* expected type: a statement that
names it in its own hypotheses has to pin the program inside terms whose type
mentions it (`blkGatedSem`, `ixSpineStOfB`), and the elaborator has nothing to
pin it with there. Instantiated from `nexProg_wideAccept_legs`, whose `heval`
argument carries the program, the same terms elaborate with no annotation at
all.
-/

/-- **The clocked program accepts, at the file it lays**: the opening and the
evaluation at one laid file, joined by `nexProg_wideAccept_legs`. The guess
writes an assignment's tracks inside the stretch it sweeps
(`guessTracks`), which is what makes the opening's frame condition true and the
evaluation's dictionary the assignment's; the clock is met by three numbers –
the region's size, the evaluation's width and its rounds – and nothing else is
left of the run. -/
theorem nexProg_wideAccept_blkLaid (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx} (hcoord : Function.Injective coord)
    (hR : (dt.nexProgAt hzo hpl coord).table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    {v' v₁ x s₀ top : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hle : WMSetLe WMLe (fun _ => False)
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkTop A dt.KIx dt.dd)))
    (hvi₁ : WMIncr WMLe (fun _ => False) v₁) (hwalk : WMSetLe WMLe v₁ x)
    (hxb : WMIncr WMLe x
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)))
    (hs₀ : WMIncr WMLe (fun _ => False) s₀)
    (hvi' : WMIncr WMLe (fun _ => False) v')
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (htop : WMSetLe WMLe s₀ top)
    (htopne : ∃ y, top y)
    (hexB : dt.exitG one ((dt.nexProgAt hzo hpl coord).passTracksAt
      (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
      (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout zero one
        dt.dd0Le (dt.nexEntrySt (fun _ => False))) (fun _ => False)
      (fun _ => False)))
    (hexG : dt.exitG one ((dt.nexProgAt hzo hpl coord).passTracksAt
      (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
      (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout zero one
        dt.dd0Le { dt.nexEntrySt (fun _ => False) with old := dt.guessTracks zero one σ s₀ top })
      (fun _ => False) (fun _ => False)))
    (hord : ∀ x y : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {e₀ : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (he₀ : ∀ y, WMLe e₀ y)
    (hlog : wideRank (logicalTop (R := dt.NexRIx (G := dt.d.B.ι → Bool))
      (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (K := dt.KIx) (V := Fin dt.dd → A)) < base)
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → Wide.BlkIx dt.KIx A dt.dd → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.blkLaid h hpos (le_of_lt hbase)).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.blkLaid h hpos (le_of_lt hbase)).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.blkLaid h hpos (le_of_lt hbase)).blk (mV a) u)
    (stL : TapeSt dt A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := (fun _ => False)) (aT := aT) (dt.blkLaid h hpos (le_of_lt hbase)) blkIxElt_injective
      (hasName_blkLaid zero h hpos (le_of_lt hbase))
      (fun b c => blkIxElt_reg_blkLaid zero h hpos (le_of_lt hbase) _ b c)
      mV { dt.nexEntrySt (fun _ => False) with
        old := dt.guessTracks zero one σ s₀ top }
      (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)
      (dt.blkGatedSemAt hzo hpl coord h hpos (le_of_lt hbase) mV)
      (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := (fun _ => False)) (aT := aT) (dt.blkLaid h hpos (le_of_lt hbase)) blkIxElt_injective
      (hasName_blkLaid zero h hpos (le_of_lt hbase))
      (fun b c => blkIxElt_reg_blkLaid zero h hpos (le_of_lt hbase) _ b c)
      mV { dt.nexEntrySt (fun _ => False) with
        old := dt.guessTracks zero one σ s₀ top }
      (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)
      (dt.blkGatedSemAt hzo hpl coord h hpos (le_of_lt hbase) mV)
      (Fin.last dt.nv))
    (hmirL : stL.mir = ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) (fun _ => False))
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) (fun _ => False))
    (htgtL : stL.tgt = ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) (fun _ => False))
    -- What the verdict is read against: the stage the guess wrote, the
    -- enumeration's own facts, and the order on the expanded universe.
    {Use : Wide.BlkIx dt.KIx A dt.dd → Prop}
    (hUse : ∀ (a : ιV) (u : Wide.BlkIx dt.KIx A dt.dd), mV a u → Use u)
    (hmono : ∀ u u', WMLt (dt.blkLaid h hpos (le_of_lt hbase)).le u u' ↔
      WMLt WMLe (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd u)
        (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd u'))
    (hup : ∀ (u : Wide.BlkIx dt.KIx A dt.dd)
        (x : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      Use u → WMLt WMLe (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd u) x →
      ∃ u', Use u' ∧ blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd u' = x)
    (hKin : ∀ (a : ιV) (t : Tag (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx)
        (w : Fin dt.dd → A),
      ixAddr (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) (mV a) (t, w) →
        ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1)
      (ixAddr (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) (mV aT)) u)
    {Below : (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly zero one (R := dt.NexRIx (G := dt.d.B.ι → Bool))
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (stL.old iv (tupAddr dt.ly zero one (R := dt.NexRIx (G := dt.d.B.ι → Bool))
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
        (dt.ixStageTgt (dt.blkLaid h hpos (le_of_lt hbase))
          (hasName_blkLaid zero h hpos (le_of_lt hbase)) none ts
          { dt.ixRoundSt stL (mV a) with
            sav := ixMark (blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd) (fun _ => False) }
          (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hout : @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out)    {a b k j m : ℕ}
    (hk : 1 ≤ k) (hkj : k + 1 < j) (hm : 0 < m)
    (hcard : (k + j) * m ≤ Nat.card (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (ha : dt.ixEvalWidth A (blkW base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
      (blkWP base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
      (blkWR base (Nat.card (Wide.BlkIx dt.KIx A dt.dd)))
      (blkWK base (Nat.card (Wide.BlkIx dt.KIx A dt.dd))) ≤ a)
    (haa : a ≤ 2 ^ (k * m)) (hb : Nat.card ιV + 1 ≤ b) (hbb : b ≤ 2 ^ (k * m))
    (hopenle : 2 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 2 * base +
      ((wideRank top - wideRank s₀) + wideRank top) + 4 + 1 ≤ 2 ^ ((k + 1) * m)) :
    WideAccept (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) := by
  obtain ⟨fq, cT, hrun, hstate, hacc⟩ :=
    dt.nexProg_reachesIn_eval hzo hpl coord h hpos (le_of_lt hbase) hR hord he₀
      hlog
      ((dt.blkLaid h hpos (le_of_lt hbase)).toIxFile.wmSetLt_empty_cell
        (ha := h) _)
      (fun x hx => hx.elim) hvi' hbotV htopV mV hmV0 hIncr hTestT hTestF _ _ rfl
      rfl rfl stL fsL hstL hfsL hmirL hbotL hsavL htgtL hUse hmono hup hKin hTop
      σ hdict hbelow hordP hout
  refine nexProg_wideAccept_legs hzo hpl hR h (st := { dt.nexEntrySt (fun _ => False) with
      old := dt.guessTracks zero one σ s₀ top }) rfl
    (dt.nexProg_reachesIn_opening hzo hpl hcoord hR h hpos hbase hle hvi₁ hwalk
      hxb hs₀ hvi' _ htop htopne
      (fun i r hr => not_guessTracks_out h hr i) hexB hexG)
    hrun hk hkj hm hcard ?_ haa hbb hopenle hstate
    hacc
  exact le_trans (dt.ixEvalCost_le_mul _ _ _ _ _) (Nat.mul_le_mul ha hb)

omit [Nonempty dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (dt.NexRIx (G := dt.d.B.ι → Bool))] in
/-- **The dictionary the evaluation reads is the assignment the guess wrote**:
the `hdict` of the evaluation, at the state the opening leaves. No leg of the
spine writes the `old` tracks (`ixSpineStOfB_old`), so the stage the verdict is
read against is the entry stage, and inside the stretch the guess's tracks are
the assignment's (`guessTracks_iff_of_lt`). What it asks of the reduction is
that every fixed-point variable have an argument – a nullary one would have the
empty address for its entry, which is the marker's own cell and below every
stretch the machine writes. -/
theorem hdict_guessTracks (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (coord : Fin dt.dd → dt.CtlIx)
    (h : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) //
        (wideData (Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Posn p})
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}
    (mV : ιV → Wide.BlkIx dt.KIx A dt.dd → Prop)
    {s₀ top : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (stL : TapeSt dt A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (Wide.BlkIx dt.KIx A dt.dd))
    (k : Fin (dt.nv + 1))
    (hstL : stL = dt.ixSpineStOfB (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
      (v := fun _ => False) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
      (hasName_blkLaid zero h hpos hbase)
      (fun b c => blkIxElt_reg_blkLaid zero h hpos hbase _ b c)
      mV { dt.nexEntrySt (fun _ => False) with
        old := dt.guessTracks zero one σ s₀ top }
      (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)
      (dt.blkGatedSemAt hzo hpl coord h hpos hbase mV) k)
    (hs₀ : WMIncr WMLe (fun _ => False) s₀)
    (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (iv : dt.d.B.ι)
    (s : Univ A (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hs : WMSetLt WMLe s top) :
    stL.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ s := by
  subst hstL
  rw [dt.ixSpineStOfB_old (elt := blkIxElt (dt.NexRIx (G := dt.d.B.ι → Bool))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.dd)
    (v := fun _ => False) (aT := aT) (dt.blkLaid h hpos hbase) blkIxElt_injective
    (hasName_blkLaid zero h hpos hbase)
    (fun b c => blkIxElt_reg_blkLaid zero h hpos hbase _ b c)
    mV { dt.nexEntrySt (fun _ => False) with
      old := dt.guessTracks zero one σ s₀ top }
    (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)
    (dt.blkGatedSemAt hzo hpl coord h hpos hbase mV) k]
  exact dt.guessTracks_iff_of_lt h hs₀ harity hs iv


end OpeningAt

end Data

end Draw

end DescriptiveComplexity
