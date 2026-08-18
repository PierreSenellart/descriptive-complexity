/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelYes
import DescriptiveComplexity.Problems.Wide.RegChannelBack

/-!
# The handed program on a no-instance

`DescriptiveComplexity.Pfp.PfpData.wideRegAccept_of_out_of_rules` is the
forward half of the machine's correctness: a sentence true at the guessed stage
makes the emitted instance a yes-instance. This file is the other half – if the
sentence is true at *no* stage, the machine does not accept – and it is where the
backward reading of an accepting run is used.

The shape of the argument is the yes-direction's turned round. An accepting run
starts where the channel wrote (`exists_stepsIn_of_wideRegAccept`); read as a
sequence, it has a first post-guess configuration whose tape is a tape state
(`exists_entry_state`) and whose phase is the walk home; the evaluation from
there returns the verdict as the sentence's own value at the stage the guess
left, which is `assignOfTrack` of the tracks the reading recovered; and a false
verdict cannot stand beside an accepting run (`not_acc_of_entry_verdict`).

Everything else – the marking, the file's ends, the rounds, the exits, the parked
scratch and the region the atoms stay inside – is what the yes-direction
supplies, and is supplied here the same way.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

section No

variable {L : Language.{0, 0}} {dt : PfpData L} {A : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [Nonempty A] [Finite A] [Finite dt.KIx] [Nonempty dt.KIx]
variable [L.IsRelational] [L.Structure A] [LinearOrder (dt.X.Map A)]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable {R' : Type} [LinearOrder R'] [Finite R']
variable [Language.wide.Structure (Univ A (R')
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite (Univ A (R')
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd}

/-- **The handed program does not accept when no stage makes the sentence
true.** The backward direction of the machine's correctness, assembled: the run
is read back to the configuration where the guess is spent, the evaluation is run
forward from there, and its verdict – the sentence's value at the stage the
reading recovered – is false, so the run cannot have accepted. -/
theorem nexProgHanded_not_wideRegAccept_of_not_out {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hdd : dt.dd0 < dt.dd)
    (hordP : ∀ p q : dt.X.Map A, p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hnotout : ∀ σ : dt.d.B.Assignment (dt.X.Map A),
      ¬@Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out) :
    ¬WideRegAccept (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) := by
  classical
  intro hW
  have hlin := PR.table.isLinOrd_wmLe hR
  -- what the marking gives
  obtain ⟨harg, hargall, hupinp, botE, hbotm, hleast, hbotarg⟩ :=
    regFacts_of_marked hR hE.marked
  obtain ⟨gtop, htopF⟩ := dt.exists_regTop hlin hR.le ⟨botE, hbotm⟩
  obtain ⟨gbot, hbotF⟩ := dt.exists_regBot hlin hR.le ⟨botE, hbotm⟩
  obtain ⟨nV, mV, hmV0, hIncr, hTestT, hTestF, hKin, hUse, hTop, hnb⟩ :=
    dt.exists_regValEnum hlin hR.le hargall
  have hcellne : ∀ u : dt.RegIx (A := A) (R' := R')
      (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)),
      (fun _ => False) ≠ (dt.regLaid hlin hR.le).cell u := by
    intro u hc
    obtain ⟨w, hw⟩ := wmRegSeg_nonempty hlin u.2
    exact (congrFun hc w ▸ hw : ((fun _ => False) : Univ A
      (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) w).elim
  obtain ⟨e₀, -, he₀⟩ := exists_least hlin
    (P := fun _ : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd => True)
    ⟨(PfpTag.sym, fun _ => Classical.arbitrary A), trivial⟩
  -- the marker is the empty address, and it has a successor
  obtain ⟨v', hvi'⟩ := exists_wmIncr hlin
    (s := fun _ : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd => False)
    ⟨(PfpTag.sym, fun _ => Classical.arbitrary A), not_false⟩
  -- the accepting run, as a sequence
  obtain ⟨n, cfg, hrun, hcacc⟩ :=
    Prog.exists_stepsIn_of_wideRegAccept hR hlin (t₀ := Slot.mir)
      (fun x => by rw [hE.mark x]; rfl) (hE.blank Slot.mir) hW
  obtain ⟨g, hg0, hgn, hgs⟩ := TMData.exists_seq_of_stepsIn hrun
  have hhead : ∀ i, ∃ v, (g i).head = Sum.inl v := by
    intro i
    induction i with
    | zero => exact ⟨_, by rw [hg0]⟩
    | succ j ih =>
      by_cases hj : j < n
      · exact head_isAddr_of_step (hgs j hj)
      · rw [hgn (j + 1) (by omega), ← hgn j (by omega)]
        exact ih
  -- the entry, and the tape state it carries
  have hhead0 : (g 0).head = Sum.inl (fun _ => False) := by rw [hg0]
  have hstate0 : (g 0).state = Sum.inr (PR.stElt
      NexPh.start (fun _ => PR.zero)) := by
    rw [hg0, hE.startPh, hE.startSt]
  have htape0 : (g 0).tape = wideTape (PR.trackTapeAt
      (dt.regLaid hlin hR.le).cell Slot.mir
      PR.initBackReg (fun _ => False))
      (PR.syElt
        PR.blank) := by
    rw [hg0]
    exact congrArg (fun f => wideTape f _)
      (PfpData.trackTape_empty_congr (PR := PR)
        (cell := wmRegSeg) (cell' := (dt.regLaid hlin hR.le).cell)
        (t := Slot.mir)
        (rest := PR.initBackReg))
  obtain ⟨m, hmn, st, htape, hwk, hmirS, htgtS, hsavS, hvalS, hbotS, hpg, fm,
    hstateM⟩ :=
    exists_entry_state hE hR hlin hR.le
      (v₀ := fun _ => False)
      (fun x hx hc => hcellne
        ⟨x, (Table.wmHasInp_iff_marked hR x).mpr ((hE.marked x).mpr hx)⟩ hc)
      g hhead hhead0 hstate0 htape0 n hgs
      (by rw [hgn n le_rfl]; exact hcacc)
  -- the evaluation from the state the reading recovered, and its verdict
  obtain ⟨fq, cT, heval, hstateT, hiff⟩ :=
    dt.nexProgHanded_reachesIn_eval_verdict hE hlin hR hR.le
      (fun y => he₀ y trivial) harg hargall hupinp hbotm hleast hbotarg
      gtop gbot htopF hbotF
      (dt.work_regLaid hbotm hleast hbotarg (fun _ hz => hz.elim) gbot)
      (fun z hz => hz.elim) hvi'
      (a₀ := 0) (aT := Fin.last nV) (fun c => Fin.zero_le c) (fun c => Fin.le_last c)
      mV hmV0 hIncr hTestT hTestF st fm hwk
      (by rw [hmirS]; rfl) hbotS _ _ rfl rfl
      ((dt.ixSpineStOfB_mir _ _ _ _ mV _ _ _ (Fin.last dt.nv)).trans
        (by rw [hmirS]; rfl))
      ((dt.ixSpineStOfB_bot _ _ _ _ mV _ _ _ (Fin.last dt.nv)).trans hbotS)
      ((dt.parked_ixSpineStOfB _ _ _ _ mV ⟨by rw [hsavS]; rfl, by rw [htgtS]; rfl⟩
        (Fin.last dt.nv)).1)
      ((dt.parked_ixSpineStOfB _ _ _ _ mV ⟨by rw [hsavS]; rfl, by rw [htgtS]; rfl⟩
        (Fin.last dt.nv)).2)
      hUse (fun u u' => dt.mono_regLaid u u')
      (fun _ _ hu hlt => dt.up_regLaid (hord := hR.le) hargall hu hlt) hKin hTop
      (assignOfTrack dt.ly PR.zero PR.one (fun i => dt.arOf_le_ko (some i)) st.old)
      (Below := fun s => WMSetLt WMLe s logicalTop)
      (hdict := fun iv x _ => Iff.rfl)
      (hbelow := fun c iv ts => belowTop_regLaid hlin hR.le hdd harg ts _ _)
      hordP
  -- the verdict is false, so the run cannot have accepted
  obtain ⟨y, hy⟩ := hhead m
  exact not_acc_of_entry_verdict hE hR hlin hR.le
    (st := st) (v₀ := fun _ => False) (y := y) (v' := v')
    hwk hmirS (wmSetLe_of_empty hlin (fun _ hc => hc) y) hvi' fm
    (exitG_at_marker (PR' := PR) (by rw [hwk]) hcellne)
    heval hstateT (fun hb => hnotout _ (hiff.mp hb))
    hstateM hy htape
    (TMData.reflTransGen_of_seq g hgs hmn)
    (by rw [hgn n le_rfl]; exact hcacc)

/-! ### The machine decides the guess-and-check, at the record -/

/-- **The emitted instance is a yes-instance exactly when some stage makes the
sentence true.** The two directions joined: a stage that works is run into the
accepting phase on the clock (`wideRegAccept_of_out_of_rules`), and if none
does, no run accepts (`nexProgHanded_not_wideRegAccept_of_not_out`). This is the
nondeterministic counterpart of
`DescriptiveComplexity.Pfp.PfpData.dwideAcceptSpace_iff_pfpHolds`, and what a
reduction's correctness is read off. -/
theorem wideRegAccept_iff_exists_out
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hdd : dt.dd0 < dt.dd) (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (hordP : ∀ p q : dt.X.Map A, p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    {a b k j m : ℕ} (hk : 1 ≤ k) (hkj : k + 1 < j) (hm : 0 < m)
    (hcard : (k + j) * m ≤ Nat.card (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (ha : dt.ixEvalWidth A (dt.nexRegW A (R') (Option dt.KIx))
      (dt.nexRegWP A (R') (Option dt.KIx))
      (dt.nexRegWR A (R') (Option dt.KIx))
      (dt.nexRegWK A (R') (Option dt.KIx)) ≤ a)
    (haa : a ≤ 2 ^ (k * m))
    (hb : dt.regBound (A := A) (R' := (R'))
        (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) + 1 ≤ b)
    (hbb : b ≤ 2 ^ (k * m))
    (hopenle : 4 * dt.regBound (A := A) (R' := (R'))
        (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) + 8 ≤ 2 ^ ((k + 1) * m)) :
    WideRegAccept (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) ↔
      ∃ σ : dt.d.B.Assignment (dt.X.Map A),
        @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out := by
  classical
  refine ⟨fun hW => by_contra fun hno => ?_, fun ⟨σ, hout⟩ =>
    dt.wideRegAccept_of_out_of_rules hpl hE hR hdd harity σ hordP hout
      hk hkj hm hcard ha haa hb hbb hopenle⟩
  push Not at hno
  exact dt.nexProgHanded_not_wideRegAccept_of_not_out hE hR hdd hordP hno hW

/-! ### The clock, instantiated -/

/-- **The clock's five numbers, from one width bound and one counting fact.**
The parameters of `wideRegAccept_iff_exists_out` are related by nothing but
powers of two, so a single choice discharges them: take the block size `m := 1`,
the working exponent `k` as the larger of the evaluation's own width exponent
and `|RegIx| + 3`, and `j := k + 2`. Then the evaluation fits in `2 ^ k` steps,
the file's stretch and the opening fit in `2 ^ k` and `2 ^ (k + 1)`, and all the
clock asks of the *drawing* is that its universe have `2 k + 2` elements to
spare.

That is the shape §2.1's «`|Tag|` is the reduction's to choose» takes here: one
inequality between the tag count and the evaluation's width exponent, and
nothing else. -/
theorem wideRegAccept_iff_exists_out_of_width
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hdd : dt.dd0 < dt.dd) (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (hordP : ∀ p q : dt.X.Map A, p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    {w : ℕ}
    (hW : dt.ixEvalWidth A (dt.nexRegW A (R') (Option dt.KIx))
      (dt.nexRegWP A (R') (Option dt.KIx))
      (dt.nexRegWR A (R') (Option dt.KIx))
      (dt.nexRegWK A (R') (Option dt.KIx)) ≤ 2 ^ w)
    (hcount : 2 * max w (Nat.card (dt.RegIx (A := A)
        (R' := R')
        (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 3) + 2 ≤
      Nat.card (Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)) :
    WideRegAccept (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) ↔
      ∃ σ : dt.d.B.Assignment (dt.X.Map A),
        @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out := by
  classical
  -- the number of registers, and the exponent the clock runs at
  set N := Nat.card (dt.RegIx (A := A) (R' := R')
    (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) with hN
  set k := max w (N + 3) with hk
  have hbound : dt.regBound (A := A) (R' := R')
      (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) = 2 ^ N := rfl
  have hwk : w ≤ k := le_max_left _ _
  have hNk : N + 3 ≤ k := le_max_right _ _
  refine dt.wideRegAccept_iff_exists_out hpl hE hR hdd harity hordP
    (a := 2 ^ k) (b := 2 ^ k) (k := k) (j := k + 2) (m := 1)
    (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.mul_one]
    exact le_trans (by omega) hcount
  · exact le_trans hW (Nat.pow_le_pow_right (by omega) hwk)
  · rw [Nat.mul_one]
  · rw [hbound]
    have h1 : (2 : ℕ) ^ N + 1 ≤ 2 ^ (N + 1) := by
      have := Nat.one_le_two_pow (n := N)
      rw [pow_succ]
      omega
    exact le_trans h1 (Nat.pow_le_pow_right (by omega) (by omega))
  · rw [Nat.mul_one]
  · rw [hbound, Nat.mul_one]
    have h2 : 4 * (2 : ℕ) ^ N + 8 ≤ 2 ^ (N + 4) := by
      have h3 : (2 : ℕ) ^ (N + 4) = 16 * 2 ^ N := by
        rw [pow_add]
        ring
      have := Nat.one_le_two_pow (n := N)
      omega
    exact le_trans h2 (Nat.pow_le_pow_right (by omega) (by omega))

/-- **The clock, with the width supplied too**: the evaluation's own bound
(`ixEvalWidth_le_two_pow_evalQ`) put in front of
`wideRegAccept_iff_exists_out_of_width`, so that what a reduction owes the clock
is one inequality between the drawing's size and the exponent the record's
dimensions make. -/
theorem wideRegAccept_iff_exists_out_of_card
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hdd : dt.dd0 < dt.dd) (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (hordP : ∀ p q : dt.X.Map A, p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hcount : 2 * max (26 * (Nat.log 2 (dt.evalQ A
          (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 1))
        (Nat.card (dt.RegIx (A := A)
          (R' := R')
          (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 3) + 2 ≤
      Nat.card (Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)) :
    WideRegAccept (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) ↔
      ∃ σ : dt.d.B.Assignment (dt.X.Map A),
        @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out :=
  dt.wideRegAccept_iff_exists_out_of_width hpl hE hR hdd harity hordP
    (w := 26 * (Nat.log 2 (dt.evalQ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 1))
    (dt.ixEvalWidth_le_two_pow_evalQ (A := A)
      (R' := R')
      (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) hcount

/-- **The machine decides the guess-and-check, with only the drawing's size left
to check.** `wideRegAccept_iff_exists_out_of_card` with the clock's inequality
discharged by `clock_count_of_tags`: what is left is that the emitted program has
more rule names than a number built from the kernel alone – its loop budget, its
dimensions and its argument blocks – which a reduction gets by padding the
guessed block (`SOBlock.pad`, `two_pow_card_le_card_nexRIx`). -/
theorem wideRegAccept_iff_exists_out_of_tags
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hdd : dt.dd0 < dt.dd) (hdd0 : 1 ≤ dt.dd0)
    (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (hordP : ∀ p q : dt.X.Map A, p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((PfpTag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hmk : ∀ x : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp x ↔ ((∃ k, x.1 = PfpTag.arg k) ∨ IsTopNonArg x))
    (htags : 52 * (4 + dt.eDim) * Nat.card dt.KIx + 52 * (4 + dt.eDim) +
        52 * (15 + dt.dimC) + 2 ≤
      Nat.card (R')) :
    WideRegAccept (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) ↔
      ∃ σ : dt.d.B.Assignment (dt.X.Map A),
        @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out :=
  dt.wideRegAccept_iff_exists_out_of_card hpl hE hR hdd harity hordP
    (dt.clock_count_of_tags A R' hdd0 harg hmk htags)

end No

end PfpData

end Pfp

end DescriptiveComplexity
