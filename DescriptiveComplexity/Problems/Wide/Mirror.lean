/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Walk

/-!
# Incrementing the mirror

The first real subroutine of a space-bounded wide machine, and the one every
address computation goes through. A program keeps a **mirror** of the address it
is working on – one bit per element, in a track over the cells the input channel
marked (`DescriptiveComplexity.Problems.Wide.Marks`) – because the head cannot
read the digits of its own address. Moving the working cell one to the right
means adding one to the mirror, and adding one is:

> walk the register file **downwards**, clearing the digits that are set; at the
> first digit that is clear, set it and stop clearing.

That is the binary increment of `DescriptiveComplexity.Problems.Wide.Increment`,
whose least significant digit is the `WMLe`-*greatest* element – which is why the
walk runs downwards – and `DescriptiveComplexity.reaches_mirrorIncr` says the
program computes it: from the last register in the carrying state with the mirror
at `s`, the machine arrives below the first register in the stopped state with
the mirror at `t`, for the unique `t` with `WMIncr WMLe s t`.

## What a caller supplies

The tape is given as a function **of the mirror**, `tapeOf m`, with one coherence
condition: changing the mirror at one element changes the tape at that element's
cell and nowhere else. Everything else a program keeps on its tape is therefore
carried along untouched, and no track discipline has to be fixed here. Three
transition families do the work – clear a set digit and keep carrying, set a
clear digit and stop, rewrite anything once stopped – plus the scanning
transitions that carry the head between consecutive registers.

The states are the caller's: `qc` for carrying, and a *family* `qd` for stopped.
The family is the point – the machine ends in `qd u₀` where `u₀` is the **carry
position**, the digit the increment set, and the conclusion says so along with its
characterization. A state may hold an element, so reporting the carry costs
nothing in the control, and it is what the fold of
`DescriptiveComplexity.Problems.Wide.Fold` needs: which block rolled over decides
which accumulators reset. So the caller reads both "the increment is finished" and
"here is where it carried" off the state, and neither off the tape.

## The other writing pass

`DescriptiveComplexity.reaches_fileWrite` is the same walk with nothing
accumulated: one state throughout, and every register simply given its new digit.
Copying the mirror into a spare register, clearing a track and loading a computed
value are all that pass. Together with the read-only pass of
`DescriptiveComplexity.Problems.Wide.Test` these are the three shapes a program's
register work comes in – write with an accumulator, write without one, read with
one – and nothing below them is ever a case split again.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Mirror

variable {A : Type} [Language.wide.Structure A]

/-! ### The mirror during the walk -/

/-- The mirror as it stands when the walk has come down to `u`: incremented
strictly above `u`, untouched at `u` and below. -/
private def midMirror (s t : A → Prop) (u v : A) : Prop :=
  (WMLt WMLe u v ∧ t v) ∨ (¬WMLt WMLe u v ∧ s v)

variable {s t : A → Prop}

/-- At the last register nothing has been touched yet. -/
private theorem midMirror_top {m : A} (hm : ∀ v : A, WMLe v m) : midMirror s t m = s :=
  funext fun v => propext
    ⟨fun hc => hc.elim (fun hc' => absurd (hm v) hc'.1.2) fun hc' => hc'.2,
      fun hs => Or.inr ⟨fun hlt => hlt.2 (hm v), hs⟩⟩

/-- Off the register just processed, the mirror does not change. -/
private theorem midMirror_agree (h : IsLinOrd (WMLe (A := A))) {u u' : A} (hs : WMSucc A u u')
    {v : A} (hv : v ≠ u') : midMirror s t u v ↔ midMirror s t u' v := by
  have hiff : WMLt WMLe u v ↔ WMLt WMLe u' v := by
    refine ⟨fun hlt => ⟨hs.2 v hlt, fun hc => hv (h.2.2.1 v u' hc (hs.2 v hlt))⟩,
      fun hlt => ⟨h.2.1 u u' v hs.1.1 hlt.1, fun hc => hs.1.2 (h.2.1 u' v u hlt.1 hc)⟩⟩
  unfold midMirror
  rw [hiff]

/-- At the register just processed the mirror holds its new digit. -/
private theorem midMirror_at {u u' : A} (hs : WMSucc A u u') :
    midMirror s t u u' ↔ t u' :=
  ⟨fun hc => hc.elim (fun hc' => hc'.2) fun hc' => absurd hs.1 hc'.1,
    fun ht => Or.inl ⟨hs.1, ht⟩⟩

/-- At the register about to be processed the mirror still holds its old
digit. -/
private theorem midMirror_at' (h : IsLinOrd (WMLe (A := A))) {u : A} :
    midMirror s t u u ↔ s u :=
  ⟨fun hc => hc.elim (fun hc' => absurd (h.1 u) hc'.1.2) fun hc' => hc'.2,
    fun hs => Or.inr ⟨fun hlt => hlt.2 (h.1 u), hs⟩⟩

/-! ### What the increment does to a digit -/

/-- Above the carry position every digit of the increment is clear. -/
private theorem not_incr_of_lt (h : IsLinOrd (WMLe (A := A))) (hi : WMIncr WMLe s t) {u₀ : A}
    (hu₀ : ¬s u₀) (hab : ∀ v : A, WMLt WMLe u₀ v → s v) {v : A} (hlt : WMLt WMLe u₀ v) :
    ¬t v := by
  obtain ⟨w, hw, haw, ht⟩ := hi
  rw [wmIncr_carry_unique h hw haw hu₀ hab] at ht
  refine fun hc => ((ht v).mp hc).elim (fun he => hlt.2 ?_) fun hc' => hc'.2 hlt
  rw [he]
  exact h.1 u₀

/-- Below the carry position the increment leaves every digit alone. -/
private theorem incr_iff_of_lt (h : IsLinOrd (WMLe (A := A))) (hi : WMIncr WMLe s t) {u₀ : A}
    (hu₀ : ¬s u₀) (hab : ∀ v : A, WMLt WMLe u₀ v → s v) {v : A} (hlt : WMLt WMLe v u₀) :
    t v ↔ s v := by
  obtain ⟨w, hw, haw, ht⟩ := hi
  rw [wmIncr_carry_unique h hw haw hu₀ hab] at ht
  refine (ht v).trans ⟨fun hc => hc.elim (fun he => absurd ?_ hlt.2) fun hc' => hc'.1,
    fun hsv => Or.inr ⟨hsv, fun hc => hlt.2 hc.1⟩⟩
  rw [← he]
  exact h.1 v

/-- At the carry position the increment sets the digit. -/
private theorem incr_carry (h : IsLinOrd (WMLe (A := A))) (hi : WMIncr WMLe s t) {u₀ : A}
    (hu₀ : ¬s u₀) (hab : ∀ v : A, WMLt WMLe u₀ v → s v) : t u₀ := by
  obtain ⟨w, hw, haw, ht⟩ := hi
  rw [wmIncr_carry_unique h hw haw hu₀ hab] at ht
  exact (ht u₀).mpr (Or.inl rfl)

/-! ### Processing one register

The whole case analysis of the subroutine happens here, once: what the machine
does at the register of `w` depends only on whether every digit above `w` is set
and on whether the digit at `w` is. Everything after this is bookkeeping, and
none of it is a case split. -/

/-- The mirror after the register of `w` has been processed. -/
private def procMirror (s t : A → Prop) (w : A) : A → Prop :=
  fun v => (v = w ∧ t v) ∨ (v ≠ w ∧ midMirror s t w v)

variable {qc : A} {qd : A → A}

/-- The mirror after processing one register is the mirror on arriving at the
next one down. -/
private theorem procMirror_succ (h : IsLinOrd (WMLe (A := A))) {u u' : A} (hs : WMSucc A u u') :
    procMirror s t u' = midMirror s t u := by
  refine funext fun v => propext ⟨fun hc => ?_, fun hc => ?_⟩
  · rcases hc with ⟨rfl, ht⟩ | ⟨hne, hm⟩
    · exact (midMirror_at hs).mpr ht
    · exact (midMirror_agree h hs hne).mpr hm
  · rcases eq_or_ne v u' with rfl | hne
    · exact Or.inl ⟨rfl, (midMirror_at hs).mp hc⟩
    · exact Or.inr ⟨hne, (midMirror_agree h hs hne).mp hc⟩

/-- Processing the first register finishes the increment. -/
private theorem procMirror_bot (h : IsLinOrd (WMLe (A := A))) {l : A} (hl : ∀ v : A, WMLe l v) :
    procMirror s t l = t := by
  refine funext fun v => propext ⟨fun hc => ?_, fun ht => ?_⟩
  · rcases hc with ⟨-, ht⟩ | ⟨hne, hm⟩
    · exact ht
    · exact (hm.resolve_right fun hc' => hc'.1 ⟨hl v, fun hcon => hne (h.2.2.1 v l hcon (hl v))⟩).2
  · rcases eq_or_ne v l with rfl | hne
    · exact Or.inl ⟨rfl, ht⟩
    · exact Or.inr ⟨hne, Or.inl ⟨⟨hl v, fun hcon => hne (h.2.2.1 v l hcon (hl v))⟩, ht⟩⟩

variable {tapeOf : (A → Prop) → (A → Prop) → A}

/-- **What the machine does at one register.** Reading the mirror's digit at `w`
in the state it arrived in, it writes the digit the increment puts there, moves
left, and goes to the state it leaves in. The three transition families of the
caller cover the three cases, and this is the only place they are distinguished:
carry on through a set digit, stop at a clear one, and rewrite once stopped. -/
private theorem incr_process (h : IsLinOrd (WMLe (A := A))) (hi : WMIncr WMLe s t)
    {u₀ : A} (hu₀ : ¬s u₀) (hab : ∀ v : A, WMLt WMLe u₀ v → s v)
    (hone : ∀ (m : A → Prop) (u : A), m u → ∃ τ : A, WMTr τ ∧ WMSrc τ qc ∧
      WMRead τ (tapeOf m (wmSeg u)) ∧ WMDst τ qc ∧
      WMWrite τ (tapeOf (fun v => m v ∧ v ≠ u) (wmSeg u)) ∧ ¬WMRight τ)
    (hzero : ∀ (m : A → Prop) (u : A), ¬m u → ∃ τ : A, WMTr τ ∧ WMSrc τ qc ∧
      WMRead τ (tapeOf m (wmSeg u)) ∧ WMDst τ (qd u) ∧
      WMWrite τ (tapeOf (fun v => m v ∨ v = u) (wmSeg u)) ∧ ¬WMRight τ)
    (hkeep : ∀ (u : A) (m : A → Prop) (w : A), ∃ τ : A, WMTr τ ∧ WMSrc τ (qd u) ∧
      WMRead τ (tapeOf m (wmSeg w)) ∧ WMDst τ (qd u) ∧ WMWrite τ (tapeOf m (wmSeg w)) ∧
      ¬WMRight τ)
    (w : A) :
    ∃ τ : A, WMTr τ ∧ WMSrc τ (accState s qc (qd u₀) w) ∧
      WMRead τ (tapeOf (midMirror s t w) (wmSeg w)) ∧ WMDst τ (accStateAfter s qc (qd u₀) w) ∧
      WMWrite τ (tapeOf (procMirror s t w) (wmSeg w)) ∧ ¬WMRight τ := by
  by_cases hcar : ∀ v : A, WMLt WMLe w v → s v
  · rw [accState, if_pos hcar]
    by_cases hbit : s w
    · -- a set digit: clear it and carry on
      have hge : ∀ v : A, WMLe w v → s v := fun v hle => by
        rcases eq_or_ne w v with rfl | hne
        · exact hbit
        · exact hcar v ⟨hle, fun hc => hne (h.2.2.1 w v hle hc)⟩
      have hlt : WMLt WMLe u₀ w := by
        refine ⟨(h.2.2.2 u₀ w).resolve_right fun hc => hu₀ (hge u₀ hc), fun hc => hu₀ ?_⟩
        exact hge u₀ hc
      have heq : procMirror s t w = fun v => midMirror s t w v ∧ v ≠ w := by
        refine funext fun v => propext ⟨fun hc => ?_, fun hc => Or.inr ⟨hc.2, hc.1⟩⟩
        rcases hc with ⟨rfl, ht⟩ | ⟨hne, hm⟩
        · exact absurd ht (not_incr_of_lt h hi hu₀ hab hlt)
        · exact ⟨hm, hne⟩
      rw [accStateAfter, if_pos hge, heq]
      exact hone _ w ((midMirror_at' h).mpr hbit)
    · -- a clear digit: set it and stop
      have hw : w = u₀ := wmIncr_carry_unique h hbit hcar hu₀ hab
      have heq : procMirror s t w = fun v => midMirror s t w v ∨ v = w := by
        refine funext fun v => propext ⟨fun hc => ?_, fun hc => ?_⟩
        · exact hc.elim (fun hc' => Or.inr hc'.1) fun hc' => Or.inl hc'.2
        · rcases eq_or_ne v w with rfl | hne
          · exact Or.inl ⟨rfl, hw ▸ incr_carry h hi hu₀ hab⟩
          · exact Or.inr ⟨hne, hc.resolve_right hne⟩
      rw [accStateAfter, if_neg fun hall => hbit (hall w (h.1 w)), heq, ← hw]
      exact hzero _ w fun hc => hbit ((midMirror_at' h).mp hc)
  · -- already stopped: rewrite the symbol and walk on
    obtain ⟨v₀, hv₀⟩ : ∃ v : A, ¬(WMLt WMLe w v → s v) := by
      by_contra hc
      exact hcar fun v hlt => not_not.mp fun hcon => hc ⟨v, fun hi' => hcon (hi' hlt)⟩
    have hlt : WMLt WMLe w u₀ := by
      have hwv : WMLt WMLe w v₀ := (Classical.not_imp.mp hv₀).1
      have hnv : ¬s v₀ := (Classical.not_imp.mp hv₀).2
      have hvu : WMLe v₀ u₀ := by
        by_contra hc
        exact hnv (hab v₀ ⟨(h.2.2.2 u₀ v₀).resolve_right hc, hc⟩)
      exact ⟨h.2.1 w v₀ u₀ hwv.1 hvu, fun hc => hwv.2 (h.2.1 v₀ u₀ w hvu hc)⟩
    have heq : procMirror s t w = midMirror s t w := by
      refine funext fun v => propext ⟨fun hc => ?_, fun hc => ?_⟩
      · rcases hc with ⟨rfl, ht⟩ | ⟨-, hm⟩
        · exact (midMirror_at' h).mpr ((incr_iff_of_lt h hi hu₀ hab hlt).mp ht)
        · exact hm
      · rcases eq_or_ne v w with rfl | hne
        · exact Or.inl ⟨rfl, (incr_iff_of_lt h hi hu₀ hab hlt).mpr ((midMirror_at' h).mp hc)⟩
        · exact Or.inr ⟨hne, hc⟩
    rw [accState, if_neg hcar, accStateAfter,
      if_neg fun hall => hcar fun v hvlt => hall v hvlt.1, heq]
    exact hkeep u₀ _ _

/-! ### The subroutine -/

variable [Finite A]

/-- **The mirror increment.** From the last register of the file, carrying, with
the mirror at `s`, the machine walks down the file and arrives just below the
first register, stopped, with the mirror at the increment of `s`.

The three transition families do the arithmetic and the scanning ones carry the
head between consecutive registers; the coherence condition `hcoh` is what says
the rest of the tape – whatever else the program keeps there – comes through
untouched. -/
theorem reaches_mirrorIncr (h : IsLinOrd (WMLe (A := A))) (hi : WMIncr WMLe s t)
    {b : A} {tapeOf : (A → Prop) → (A → Prop) → A}
    (hcoh : ∀ (m m' : A → Prop) (u : A), (∀ v : A, v ≠ u → (m v ↔ m' v)) →
      ∀ r : A → Prop, r ≠ wmSeg u → tapeOf m r = tapeOf m' r)
    (hone : ∀ (m : A → Prop) (u : A), m u → ∃ τ : A, WMTr τ ∧ WMSrc τ qc ∧
      WMRead τ (tapeOf m (wmSeg u)) ∧ WMDst τ qc ∧
      WMWrite τ (tapeOf (fun v => m v ∧ v ≠ u) (wmSeg u)) ∧ ¬WMRight τ)
    (hzero : ∀ (m : A → Prop) (u : A), ¬m u → ∃ τ : A, WMTr τ ∧ WMSrc τ qc ∧
      WMRead τ (tapeOf m (wmSeg u)) ∧ WMDst τ (qd u) ∧
      WMWrite τ (tapeOf (fun v => m v ∨ v = u) (wmSeg u)) ∧ ¬WMRight τ)
    (hkeep : ∀ (u : A) (m : A → Prop) (w : A), ∃ τ : A, WMTr τ ∧ WMSrc τ (qd u) ∧
      WMRead τ (tapeOf m (wmSeg w)) ∧ WMDst τ (qd u) ∧ WMWrite τ (tapeOf m (wmSeg w)) ∧
      ¬WMRight τ)
    (hskip : ∀ q : A, (q = qc ∨ ∃ u : A, q = qd u) → ∀ m r : A → Prop,
      (∃ x : A, WMSetLe WMLe (wmSeg x) r) → (∀ x : A, r ≠ wmSeg x) →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (tapeOf m r) ∧ WMDst τ q ∧
        WMWrite τ (tapeOf m r) ∧ ¬WMRight τ)
    {top bot : A} (htop : ∀ v : A, WMLe v top) (hbot : ∀ v : A, WMLe bot v) :
    ∃ (u₀ : A) (p : A → Prop), (¬s u₀ ∧ ∀ v : A, WMLt WMLe u₀ v → s v) ∧
      WMIncr WMLe p (wmSeg bot) ∧
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr qc, Sum.inl (wmSeg top), wideTape (tapeOf s) b⟩
        ⟨Sum.inr (qd u₀), Sum.inl p, wideTape (tapeOf t) b⟩ := by
  obtain ⟨u₀, hu₀, hab, -⟩ := id hi
  -- The walk down the file, one register at a time.
  have hwalk := reaches_regWalkBack h (b := b) (st := accState s qc (qd u₀))
    (tp := fun u => tapeOf (midMirror s t u)) (u₁ := top) (fun u u' hs _ => ?_) bot (hbot top)
  · -- The last write, at the first register, and the step off the file.
    obtain ⟨p, hp⟩ := exists_wmPred h (s := wmSeg bot) ⟨bot, h.1 bot⟩
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      incr_process h hi hu₀ hab hone hzero hkeep bot
    rw [accStateAfter_bot_neg hbot hu₀] at hdst
    rw [procMirror_bot h hbot] at hwrite
    refine ⟨u₀, p, ⟨hu₀, hab⟩, hp, Relation.ReflTransGen.tail ?_
      (step_wideTape_left h hp htr hsrc hread hdst hwrite hright fun r hr =>
        hcoh t (midMirror s t bot) bot (fun v hv => ?_) r hr)⟩
    · rw [show accState s qc (qd u₀) top = qc from accState_top htop,
        show midMirror s t top = s from midMirror_top htop] at hwalk
      exact hwalk
    · exact ⟨fun ht => Or.inl ⟨⟨hbot v, fun hc => hv (h.2.2.1 v bot hc (hbot v))⟩, ht⟩,
        fun hm => (hm.resolve_right fun hc =>
          hc.1 ⟨hbot v, fun hc' => hv (h.2.2.1 v bot hc' (hbot v))⟩).2⟩
  · -- One register: what to write is `incr_process`, where to go next is the walk.
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      incr_process h hi hu₀ hab hone hzero hkeep u'
    rw [accStateAfter_succ h hs] at hdst
    rw [procMirror_succ h hs] at hwrite
    refine reaches_regStepBack h hs ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩
      (fun r hr => hcoh _ _ u' (fun v hv => midMirror_agree h hs hv) r hr) fun r hbnd hr => ?_
    exact hskip _ ((accState_cases u).imp id fun hc => ⟨u₀, hc⟩) _ r hbnd hr

/-! ### Overwriting a track

The same walk with nothing accumulated: the state never changes, and every
register is simply given its new digit. Copying the mirror into a spare register,
clearing a track and loading a computed value are all this pass. -/

/-- **Overwriting a track.** A pass down the file in a single state, replacing the
track's digit at every register: the machine starts at the last register with the
track at `s` and arrives just below the first register with it at `t`.

Since nothing is accumulated, `t` is arbitrary – the caller's transitions say what
to write at each register, and may read the old digit to decide. -/
theorem reaches_fileWrite (h : IsLinOrd (WMLe (A := A))) {b q : A}
    {tapeOf : (A → Prop) → (A → Prop) → A}
    (hcoh : ∀ (m m' : A → Prop) (u : A), (∀ v : A, v ≠ u → (m v ↔ m' v)) →
      ∀ r : A → Prop, r ≠ wmSeg u → tapeOf m r = tapeOf m' r)
    (hstep : ∀ (m : A → Prop) (u : A), ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧
      WMRead τ (tapeOf m (wmSeg u)) ∧ WMDst τ q ∧
      WMWrite τ (tapeOf (fun v => (v = u ∧ t v) ∨ (v ≠ u ∧ m v)) (wmSeg u)) ∧ ¬WMRight τ)
    (hskip : ∀ m r : A → Prop, (∃ x : A, WMSetLe WMLe (wmSeg x) r) →
      (∀ x : A, r ≠ wmSeg x) →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (tapeOf m r) ∧ WMDst τ q ∧
        WMWrite τ (tapeOf m r) ∧ ¬WMRight τ)
    {top bot : A} (htop : ∀ v : A, WMLe v top) (hbot : ∀ v : A, WMLe bot v) :
    ∃ p : A → Prop, WMIncr WMLe p (wmSeg bot) ∧
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr q, Sum.inl (wmSeg top), wideTape (tapeOf s) b⟩
        ⟨Sum.inr q, Sum.inl p, wideTape (tapeOf t) b⟩ := by
  have hwalk := reaches_regWalkBack h (b := b) (st := fun _ => q)
    (tp := fun u => tapeOf (midMirror s t u)) (u₁ := top) (fun u u' hs _ => ?_) bot (hbot top)
  · obtain ⟨p, hp⟩ := exists_wmPred h (s := wmSeg bot) ⟨bot, h.1 bot⟩
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep (midMirror s t bot) bot
    rw [show (fun v => (v = bot ∧ t v) ∨ (v ≠ bot ∧ midMirror s t bot v)) = t from
      procMirror_bot h hbot] at hwrite
    refine ⟨p, hp, Relation.ReflTransGen.tail ?_
      (step_wideTape_left h hp htr hsrc hread hdst hwrite hright fun r hr =>
        hcoh t (midMirror s t bot) bot (fun v hv => ?_) r hr)⟩
    · rw [show midMirror s t top = s from midMirror_top htop] at hwalk
      exact hwalk
    · exact ⟨fun ht => Or.inl ⟨⟨hbot v, fun hc => hv (h.2.2.1 v bot hc (hbot v))⟩, ht⟩,
        fun hm => (hm.resolve_right fun hc =>
          hc.1 ⟨hbot v, fun hc' => hv (h.2.2.1 v bot hc' (hbot v))⟩).2⟩
  · obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep (midMirror s t u') u'
    rw [show (fun v => (v = u' ∧ t v) ∨ (v ≠ u' ∧ midMirror s t u' v)) = midMirror s t u from
      procMirror_succ h hs] at hwrite
    exact reaches_regStepBack h hs ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩
      (fun r hr => hcoh _ _ u' (fun v hv => midMirror_agree h hs hv) r hr)
      fun r hbnd hr => hskip _ r hbnd hr

end Mirror

end DescriptiveComplexity
