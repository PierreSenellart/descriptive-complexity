/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInstStage
import DescriptiveComplexity.Problems.Wide.IxAddr

/-!
# The address a stage atom builds, at an arbitrary file

The random access of a stage atom copies each argument position's source block
into the TARGET register and then seeks to the address TARGET spells. At the
elementwise file that address *is* the register set, and the copy's two cells
are elements of the universe
(`DescriptiveComplexity.Draw.Data.stageXS`/`stageXD`). At a coarser file they
are **registers**, named by a block and a tuple
(`DescriptiveComplexity.Draw.Layout.reg`), what the copy builds is a **mark**,
and the address is `DescriptiveComplexity.ixAddr` of it.

This file is that reading, from the data up to the run: the two named registers,
the mark the loops build (`ixStageTgt`) with its closed form, the facts that
place the address it stands for in the logical interval, the copy loop's run
(`ixStageTuple_reachesIn`), the loops chained (`ixStageChain_reachesIn`) and the
whole random access (`ixStageAtom_reachesIn`), each on the clock a NEXPTIME
machine is held to. The hypothesis that carries everything across is one
**coherence** condition on the file – the element a register holds the bit of is
the element its name spells:

  `elt (F.toLayout.reg hhas b c) = dt.blkElt b (padTup zero c)`

With it the address `ixAddr elt (ixStageTgt …)` has the same blocks as the
elementwise one, so the semantics of the atom – the dictionary, `trackOf`, the
logical interval – says of a clocked program's run exactly what it says of a
space-bounded one.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P] [Nonempty A]
variable {I : Type} (F : LaidFile dt A R P I)
variable {zero : A} (hhas : F.toLayout.HasName zero)
variable (vi : dt.VarIx) {iv : dt.d.B.ι}
variable (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))

/-! ### The two registers a copy round names -/

/-- **The source register of a copy round**: the register named by the round's
tuple in the position's source block. -/
noncomputable def ixStageXS (ℓ : Fin (dt.d.B.arity iv)) (b : Lex (Fin dt.dd0 → A)) : I :=
  F.toLayout.reg hhas (dt.lvBlk vi (ts ℓ)) (ofLex b)

/-- **The destination register of a copy round**: the register named by the
round's tuple in the TARGET block of the position. -/
noncomputable def ixStageXD (ℓ : Fin (dt.d.B.arity iv)) (b : Lex (Fin dt.dd0 → A)) : I :=
  F.toLayout.reg hhas (Sum.inl (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ)) (ofLex b)

omit [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- **Distinct tuples name distinct registers**: a register carries its own
name, and the name determines the tuple. -/
theorem ixStageXD_injective {ℓ : Fin (dt.d.B.arity iv)}
    {b b' : Lex (Fin dt.dd0 → A)}
    (h : dt.ixStageXD F hhas ℓ b = dt.ixStageXD F hhas ℓ b') : b = b' := by
  have ha : F.toLayout.arg (dt.ixStageXD F hhas ℓ b) =
      F.toLayout.arg (dt.ixStageXD F hhas ℓ b') := congrArg _ h
  rw [ixStageXD, ixStageXD, Layout.arg_reg hhas, Layout.arg_reg hhas] at ha
  refine congrArg toLex (funext fun j => ?_)
  have hj := congrFun ha (Fin.castLE dt.dd0Le j)
  rwa [dt.padTup_coord zero (ofLex b) dt.dd0Le j,
    dt.padTup_coord zero (ofLex b') dt.dd0Le j] at hj

omit [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- **Distinct positions write distinct blocks**: a register carries its block,
and the block names the position that wrote it. -/
theorem ixStageXD_pos_eq {ℓ ℓ' : Fin (dt.d.B.arity iv)}
    {b b' : Lex (Fin dt.dd0 → A)}
    (h : dt.ixStageXD F hhas ℓ b = dt.ixStageXD F hhas ℓ' b') : ℓ = ℓ' := by
  have hblk : F.toLayout.blk (dt.ixStageXD F hhas ℓ b) =
      F.toLayout.blk (dt.ixStageXD F hhas ℓ' b') := congrArg _ h
  rw [ixStageXD, ixStageXD, Layout.blk_reg hhas, Layout.blk_reg hhas] at hblk
  exact Fin.castLE_injective _ (Sum.inl_injective (Option.some.inj hblk))

/-! ### The mark the copy loops build -/

/-- **The TARGET after the first `n` copy loops**: each position's loop writes
its source bits at its destination registers over what the earlier positions
built. -/
noncomputable def ixStageTgt (st : TapeSt dt A R P I) : ℕ → I → Prop
  | 0 => fun _ => False
  | n + 1 =>
    if h : n < dt.d.B.arity iv then
      tuplePost (dt.lvSet st vi (ts ⟨n, h⟩))
        (tupleIterD (dt.lvSet st vi (ts ⟨n, h⟩))
          (dt.ixStageXS F hhas vi ts ⟨n, h⟩) (dt.ixStageXD F hhas ⟨n, h⟩)
          (ixStageTgt st n))
        (dt.ixStageXS F hhas vi ts ⟨n, h⟩) (dt.ixStageXD F hhas ⟨n, h⟩)
        (toLex topTup)
    else ixStageTgt st n

omit [Finite R] [Finite P] in
/-- **The composed TARGET, in closed form**: a register holds a bit exactly when
some position below `n` copied it there – the source block's bit at the same
tuple. Distinct positions write distinct blocks, so the loops never collide and
the disjunction is honest. -/
theorem ixStageTgt_iff (st : TapeSt dt A R P I) (n : ℕ) (y : I) :
    dt.ixStageTgt F hhas vi ts st n y ↔
      ∃ (ℓ : Fin (dt.d.B.arity iv)) (b : Lex (Fin dt.dd0 → A)),
        (ℓ : ℕ) < n ∧ y = dt.ixStageXD F hhas ℓ b ∧
          dt.lvSet st vi (ts ℓ) (dt.ixStageXS F hhas vi ts ℓ b) := by
  induction n with
  | zero =>
    exact ⟨fun h => h.elim, fun ⟨_, _, hℓ, _⟩ => absurd hℓ (Nat.not_lt_zero _)⟩
  | succ n ih =>
    by_cases hlt : n < dt.d.B.arity iv
    · have hstep : dt.ixStageTgt F hhas vi ts st (n + 1) =
          tuplePost (dt.lvSet st vi (ts ⟨n, hlt⟩))
            (tupleIterD (dt.lvSet st vi (ts ⟨n, hlt⟩))
              (dt.ixStageXS F hhas vi ts ⟨n, hlt⟩) (dt.ixStageXD F hhas ⟨n, hlt⟩)
              (dt.ixStageTgt F hhas vi ts st n))
            (dt.ixStageXS F hhas vi ts ⟨n, hlt⟩) (dt.ixStageXD F hhas ⟨n, hlt⟩)
            (toLex topTup) := by
        simp only [ixStageTgt]
        rw [dif_pos hlt]
      rw [hstep]
      constructor
      · rintro (⟨hy, hsrc⟩ | ⟨hne, hD⟩)
        · exact ⟨⟨n, hlt⟩, toLex topTup, Nat.lt_succ_self n, hy, hsrc⟩
        · rcases (tupleIterD_iff
              (fun u₁ u₂ hh => dt.ixStageXD_injective F hhas hh) _ y).mp hD with
            ⟨u, -, hy, hsrc⟩ | ⟨-, hm⟩
          · exact ⟨⟨n, hlt⟩, u, Nat.lt_succ_self n, hy, hsrc⟩
          · obtain ⟨ℓ, u, hℓ, hy, hsrc⟩ := ih.mp hm
            exact ⟨ℓ, u, Nat.lt_succ_of_lt hℓ, hy, hsrc⟩
      · rintro ⟨ℓ, u, hℓ, hy, hsrc⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ with hℓn | hℓn
        · have hne : ∀ u' : Lex (Fin dt.dd0 → A),
              y ≠ dt.ixStageXD F hhas ⟨n, hlt⟩ u' := by
            intro u' hc
            rw [hy] at hc
            exact absurd (congrArg Fin.val (dt.ixStageXD_pos_eq F hhas hc))
              (Nat.ne_of_lt hℓn)
          exact Or.inr ⟨hne _, (tupleIterD_iff
            (fun u₁ u₂ hh => dt.ixStageXD_injective F hhas hh) _ y).mpr
            (Or.inr ⟨fun u' _ => hne u', ih.mpr ⟨ℓ, u, hℓn, hy, hsrc⟩⟩)⟩
        · have hℓeq : ℓ = ⟨n, hlt⟩ := Fin.ext hℓn
          subst hℓeq
          by_cases hu : u = toLex topTup
          · subst hu
            exact Or.inl ⟨hy, hsrc⟩
          · have hult : u < toLex topTup :=
              lt_of_le_of_ne (tup_isTop_iff.mpr (fun p a => le_topTup p a) u) hu
            refine Or.inr ⟨?_, (tupleIterD_iff
              (fun u₁ u₂ hh => dt.ixStageXD_injective F hhas hh) _ y).mpr
              (Or.inl ⟨u, hult, hy, hsrc⟩)⟩
            intro hc
            rw [hy] at hc
            exact hu (dt.ixStageXD_injective F hhas hc)
    · have hstep : dt.ixStageTgt F hhas vi ts st (n + 1) =
          dt.ixStageTgt F hhas vi ts st n := by
        simp only [ixStageTgt]
        rw [dif_neg hlt]
      rw [hstep, ih]
      constructor
      · rintro ⟨ℓ, u, hℓ, hy, hsrc⟩
        exact ⟨ℓ, u, Nat.lt_succ_of_lt hℓ, hy, hsrc⟩
      · rintro ⟨ℓ, u, hℓ, hy, hsrc⟩
        refine ⟨ℓ, u, ?_, hy, hsrc⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ with h | h
        · exact h
        · exact absurd (h ▸ ℓ.isLt) hlt

/-! ### The copy loop at an arbitrary file

The loop's background, its generated controls and its run, all as the
elementwise instantiation has them – the only difference being that the two
cells it names are registers and the marks are the index's.
-/

section IxLoop

variable [Fintype dt.SlotIx] [Finite dt.KIx]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (one : A) (av : Fin dt.natMax) (ℓ : Fin (dt.d.B.arity iv))
variable (st : TapeSt dt A R P I)
variable (hix : IsLinOrd F.le)
variable (hsep : F.toLayout.NameSep zero dt.dd0Le)
variable {vAdr : Univ A R P dt.KIx dt.dd → Prop}
variable {mD₀ : I → Prop} {f₀ : dt.CtlIx → A}

/-- **The background of a copy loop, as a function of the destination
content**: the state with the TARGET register at the given track. -/
noncomputable def ixStageRestF {I : Type} (F : LaidFile dt A R P I)
    (zero one : A) (st : TapeSt dt A R P I) (m' : I → Prop) :
    (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A :=
  dt.ixBack F.toLayout zero one dt.dd0Le { st with tgt := m' }


omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [Finite dt.KIx] in
/-- The destination-dependent background moves only at the TARGET slot. -/
theorem ixStageRestF_off {I : Type} (F : LaidFile dt A R P I) (zero one : A)
    (st : TapeSt dt A R P I) (m₁ m₂ : I → Prop)
    (r : Univ A R P dt.KIx dt.dd → Prop) (s : dt.SlotIx)
    (hs : s ≠ Slot.tgt) :
    dt.ixStageRestF F zero one st m₁ r s = dt.ixStageRestF F zero one st m₂ r s := by
  match s with
  | .tgt => exact absurd rfl hs
  | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .sav
  | .wk | .val | .bot | .ltp | .old _ | .new _ => rfl

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite dt.KIx] in
/-- The copy loop's generated round tuples: the pre-store control's loop
element is the round's tuple. -/
theorem ixReadLv_stageIter0 (b : Lex (Fin dt.dd0 → A)) :
    dt.readLv (tupleIter0
      (dt.stageArgs zero one vi iv ts av).setBit
      (dt.stageArgs zero one vi iv ts av).initLv
      (dt.stageArgs zero one vi iv ts av).advLv
      (dt.lvSet st vi (ts ℓ)) vAdr (dt.ixStageRestF F zero one st)
      (dt.ixStageXS F hhas vi ts ℓ) (dt.ixStageXD F hhas ℓ) mD₀ f₀ b) =
      ofLex b := by
  induction b using order_induction with
  | hmin z hz =>
    have hz0 : tupleIter0
        (dt.stageArgs zero one vi iv ts av).setBit
        (dt.stageArgs zero one vi iv ts av).initLv
        (dt.stageArgs zero one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) vAdr (dt.ixStageRestF F zero one st)
        (dt.ixStageXS F hhas vi ts ℓ) (dt.ixStageXD F hhas ℓ) mD₀ f₀ z =
        (dt.stageArgs zero one vi iv ts av).initLv f₀
          (dt.ixStageRestF F zero one st mD₀ vAdr) :=
      iterOrd_bot hz
    rw [hz0]
    have hinit : dt.readLv ((dt.stageArgs zero one vi iv ts av).initLv f₀
        (dt.ixStageRestF F zero one st mD₀ vAdr)) = botTup := by
      change dt.readLv (dt.initLvN f₀) = botTup
      rw [initLvN, readLv_putLv]
    rw [hinit, ofLex_eq_botTup_of_bot hz]
  | hstep w z hwz hnb ih =>
    classical
    have hz2 : tupleIter0
        (dt.stageArgs zero one vi iv ts av).setBit
        (dt.stageArgs zero one vi iv ts av).initLv
        (dt.stageArgs zero one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) vAdr (dt.ixStageRestF F zero one st)
        (dt.ixStageXS F hhas vi ts ℓ) (dt.ixStageXD F hhas ℓ) mD₀ f₀ z =
        (dt.stageArgs zero one vi iv ts av).advLv
          (if dt.lvSet st vi (ts ℓ) (dt.ixStageXS F hhas vi ts ℓ w) then
            (dt.stageArgs zero one vi iv ts av).setBit true
              (tupleIter0 (dt.stageArgs zero one vi iv ts av).setBit
                (dt.stageArgs zero one vi iv ts av).initLv
                (dt.stageArgs zero one vi iv ts av).advLv
                (dt.lvSet st vi (ts ℓ)) vAdr (dt.ixStageRestF F zero one st)
                (dt.ixStageXS F hhas vi ts ℓ) (dt.ixStageXD F hhas ℓ) mD₀ f₀ w)
              (dt.ixStageRestF F zero one st
                (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhas vi ts ℓ)
                  (dt.ixStageXD F hhas ℓ) mD₀ w) vAdr)
          else
            (dt.stageArgs zero one vi iv ts av).setBit false
              (tupleIter0 (dt.stageArgs zero one vi iv ts av).setBit
                (dt.stageArgs zero one vi iv ts av).initLv
                (dt.stageArgs zero one vi iv ts av).advLv
                (dt.lvSet st vi (ts ℓ)) vAdr (dt.ixStageRestF F zero one st)
                (dt.ixStageXS F hhas vi ts ℓ) (dt.ixStageXD F hhas ℓ) mD₀ f₀ w)
              (dt.ixStageRestF F zero one st
                (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhas vi ts ℓ)
                  (dt.ixStageXD F hhas ℓ) mD₀ w) vAdr))
          (dt.ixStageRestF F zero one st
            (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhas vi ts ℓ)
              (dt.ixStageXD F hhas ℓ) mD₀ w) vAdr) :=
      iterOrd_covers hwz hnb
    rw [hz2]
    have hadv : ∀ (q : dt.CtlIx → A) (g : dt.SlotIx → A),
        dt.readLv ((dt.stageArgs zero one vi iv ts av).advLv q g) =
          tupNext (dt.readLv q) := by
      intro q g
      change dt.readLv (dt.advLvN q) = _
      rw [advLvN, readLv_putLv]
    have hset : ∀ (bb : Bool) (q : dt.CtlIx → A) (g : dt.SlotIx → A),
        dt.readLv ((dt.stageArgs zero one vi iv ts av).setBit bb q g) =
          dt.readLv q := by
      intro bb q g
      change dt.readLv (dt.setCtl zero one dt.bitFlagC (bb = true) q) = _
      rw [readLv_setCtl_bitFlagC]
    rw [hadv]
    by_cases hb : dt.lvSet st vi (ts ℓ) (dt.ixStageXS F hhas vi ts ℓ w)
    · rw [if_pos hb, hset, ih, ofLex_eq_tupNext_of_covers hwz hnb]
    · rw [if_neg hb, hset, ih, ofLex_eq_tupNext_of_covers hwz hnb]

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite dt.KIx] in
/-- The post-store control's loop element is still the round's tuple. -/
theorem ixReadLv_stageIter1 (b : Lex (Fin dt.dd0 → A)) :
    dt.readLv (tupleIter1
      (dt.stageArgs zero one vi iv ts av).setBit
      (dt.stageArgs zero one vi iv ts av).initLv
      (dt.stageArgs zero one vi iv ts av).advLv
      (dt.lvSet st vi (ts ℓ)) vAdr (dt.ixStageRestF F zero one st)
      (dt.ixStageXS F hhas vi ts ℓ) (dt.ixStageXD F hhas ℓ) mD₀ f₀ b) =
      ofLex b := by
  classical
  have hset : ∀ (bb : Bool) (q : dt.CtlIx → A) (g : dt.SlotIx → A),
      dt.readLv ((dt.stageArgs zero one vi iv ts av).setBit bb q g) =
        dt.readLv q := by
    intro bb q g
    change dt.readLv (dt.setCtl zero one dt.bitFlagC (bb = true) q) = _
    rw [readLv_setCtl_bitFlagC]
  rw [tupleIter1]
  by_cases hb : dt.lvSet st vi (ts ℓ) (dt.ixStageXS F hhas vi ts ℓ b)
  · rw [if_pos hb, hset]
    exact dt.ixReadLv_stageIter0 F hhas vi ts one av ℓ st b
  · rw [if_neg hb, hset]
    exact dt.ixReadLv_stageIter0 F hhas vi ts one av ℓ st b

section StageTupleRun

variable {emb : ChainPh 3 TuplePS → P} {exitPh : P}
variable {rEmb : ∀ i : ChainSite 3 TupleSS, ChainSh 3 TupleSS TupleSh i → R}
variable (hhasP : F.toLayout.HasName PR.zero)
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le)
variable (hrules : ∀ (i : ChainSite 3 TupleSS) (ρ : ChainSh 3 TupleSS TupleSh i),
  PR.rules (rEmb i ρ) = tupleRule PR.zero PR.one Slot.wk Slot.reg emb
    ((dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ) Slot.tgt
    (dt.nameG PR.one ((dt.stageArgs PR.zero PR.one vi iv ts av).srcBlk ℓ)
      dt.lvC)
    (dt.nameG PR.one ((dt.stageArgs PR.zero PR.one vi iv ts av).dstBlk ℓ)
      dt.lvC)
    (dt.stageArgs PR.zero PR.one vi iv ts av).bitFlag
    (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
    (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).IsMaxLv exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gbot : I} (hbot : ∀ y, F.le gbot y)
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v)
variable (mD₀' : I → Prop) (f₀' : dt.CtlIx → A)

include hrules hR hlin hix hsepP hhasP hbot hv hvi hwkSt in
/-- **One copy loop's run, on a clock**: from its entry checkpoint at the
marker to the exit phase one cell to its right, the TARGET block of the
position holding the source block's bits at every tuple's cell, a round's width
paid once per tuple. -/
theorem ixStageTuple_reachesIn (w : ℕ)
    (hcost : ∀ a : Lex (Fin dt.dd0 → A),
      2 * (wideRank (F.cell (dt.ixStageXS F hhasP vi ts ℓ a)) - wideRank v) + 2 ≤ w ∧
        2 * (wideRank (F.cell (dt.ixStageXD F hhasP ℓ a)) - wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1)
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨0, by omega⟩)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell
          ((dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
          (dt.ixStageRestF F PR.zero PR.one st
            (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
              (dt.ixStageXD F hhasP ℓ) mD₀ (toLex botTup)))
          (dt.lvSet st vi (ts ℓ))) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (tupleIter1 (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
            (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
            (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
            (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
            (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀
            (toLex topTup))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.tgt
          (dt.ixStageRestF F PR.zero PR.one st
            (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
              (dt.ixStageXD F hhasP ℓ) mD₀ (toLex topTup)))
          (tuplePost (dt.lvSet st vi (ts ℓ))
            (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
              (dt.ixStageXD F hhasP ℓ) mD₀)
            (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
            (toLex topTup))) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hne_wk_tgt : (Slot.wk : dt.SlotIx) ≠ Slot.tgt := fun h => nomatch h
  have hne_reg_tgt : (Slot.reg : dt.SlotIx) ≠ Slot.tgt := fun h => nomatch h
  refine tuple_reachesIn_iter F.toIxFile hrules hR hlin hix hbot hv hvi
    (tup_isBot_iff.mpr botTup_le)
    (tup_isTop_iff.mpr fun p a => le_topTup p a)
    (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀
    (fun m' r => by
      rw [show dt.ixStageRestF F PR.zero PR.one st m' r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkSt])
    (fun m' r => rfl)
    (fun m' r => dt.back_lvTrack F PR.zero PR.one { st with tgt := m' } vi
      (ts ℓ) r)
    (fun m' r => rfl)
    (fun m₁ m₂ r s hs => dt.ixStageRestF_off F PR.zero PR.one st m₁ m₂ r s hs)
    (dt.wk_ne_lvTrack vi (ts ℓ)) hne_wk_tgt
    (dt.reg_ne_lvTrack vi (ts ℓ)) hne_reg_tgt
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ w hcost
  · -- the source read's name guard
    intro a
    rw [passTracks_of_back F.toIxFile
      (t := (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
      (rest := dt.ixStageRestF F PR.zero PR.one st
        (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
          (dt.ixStageXD F hhasP ℓ) mD₀ a))
      (m := dt.lvSet st vi (ts ℓ))
      (fun r => dt.back_lvTrack F PR.zero PR.one _ vi (ts ℓ) r) _]
    have hrd : (fun j => tupleIter0
        (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
        (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
        (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
        (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀ a
        (dt.lvC j)) = ofLex a :=
      dt.ixReadLv_stageIter0 F hhasP vi ts PR.one av ℓ st a
    refine (dt.ixNameG_iff hzo (F.toIxFile.injective hix) hsepP hhasP _ dt.lvC _
      (dt.ixStageXS F hhasP vi ts ℓ a)).mpr ?_
    rw [ixStageXS, hrd]
    rfl
  · -- the source guard identifies the cell
    intro a r hM
    rw [passTracks_of_back F.toIxFile
      (t := (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
      (rest := dt.ixStageRestF F PR.zero PR.one st
        (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
          (dt.ixStageXD F hhasP ℓ) mD₀ a))
      (m := dt.lvSet st vi (ts ℓ))
      (fun r' => dt.back_lvTrack F PR.zero PR.one _ vi (ts ℓ) r') _] at hM
    by_cases hreg : ∃ u : I, r = F.cell u
    · obtain ⟨u, rfl⟩ := hreg
      have hu := (dt.ixNameG_iff hzo (F.toIxFile.injective hix) hsepP hhasP _ dt.lvC _ u).mp hM
      have hrd : (fun j => tupleIter0
          (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀ a
          (dt.lvC j)) = ofLex a :=
        dt.ixReadLv_stageIter0 F hhasP vi ts PR.one av ℓ st a
      rw [hrd] at hu
      rw [hu]
      rfl
    · exact absurd hM (dt.ixNot_nameGF_of_not_reg hzo
        (fun u hc => hreg ⟨u, hc⟩))
  · -- the destination write's name guard
    intro a
    rw [passTracks_of_back F.toIxFile (t := Slot.tgt)
      (rest := dt.ixStageRestF F PR.zero PR.one st
        (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
          (dt.ixStageXD F hhasP ℓ) mD₀ a))
      (m := tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
        (dt.ixStageXD F hhasP ℓ) mD₀ a)
      (fun r => rfl) _]
    have hrd : (fun j => tupleIter1
        (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
        (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
        (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
        (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀ a
        (dt.lvC j)) = ofLex a :=
      dt.ixReadLv_stageIter1 F hhasP vi ts PR.one av ℓ st a
    refine (dt.ixNameG_iff hzo (F.toIxFile.injective hix) hsepP hhasP _ dt.lvC _
      (dt.ixStageXD F hhasP ℓ a)).mpr ?_
    rw [ixStageXD, hrd]
    rfl
  · -- the destination guard identifies the cell
    intro a r hM
    rw [passTracks_of_back F.toIxFile (t := Slot.tgt)
      (rest := dt.ixStageRestF F PR.zero PR.one st
        (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
          (dt.ixStageXD F hhasP ℓ) mD₀ a))
      (m := tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.ixStageXS F hhasP vi ts ℓ)
        (dt.ixStageXD F hhasP ℓ) mD₀ a)
      (fun r' => rfl) _] at hM
    by_cases hreg : ∃ u : I, r = F.cell u
    · obtain ⟨u, rfl⟩ := hreg
      have hu := (dt.ixNameG_iff hzo (F.toIxFile.injective hix) hsepP hhasP _ dt.lvC _ u).mp hM
      have hrd : (fun j => tupleIter1
          (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀ a
          (dt.lvC j)) = ofLex a :=
        dt.ixReadLv_stageIter1 F hhasP vi ts PR.one av ℓ st a
      rw [hrd] at hu
      rw [hu]
      rfl
    · exact absurd hM (dt.ixNot_nameGF_of_not_reg hzo
        (fun u hc => hreg ⟨u, hc⟩))
  · -- the copied bit reads back
    intro a
    rw [tupleIter1]
    by_cases hb : dt.lvSet st vi (ts ℓ) (dt.ixStageXS F hhasP vi ts ℓ a)
    · rw [if_pos hb]
      change dt.ctlBit PR.one (dt.setCtl PR.zero PR.one dt.bitFlagC
        (true = true)
        (tupleIter0 (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀ a))
        dt.bitFlagC ↔ _
      rw [ctlBit_setCtl_self hzo]
      exact ⟨fun _ => hb, fun _ => rfl⟩
    · rw [if_neg hb]
      change dt.ctlBit PR.one (dt.setCtl PR.zero PR.one dt.bitFlagC
        (false = true)
        (tupleIter0 (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀ a))
        dt.bitFlagC ↔ _
      rw [ctlBit_setCtl_self hzo]
      exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc hb⟩
  · -- exhausted at the top
    change dt.IsMaxLvN _
    have hrd : dt.readLv (tupleIter1
        (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
        (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
        (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
        (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀
        (toLex topTup)) = ofLex (toLex topTup) :=
      dt.ixReadLv_stageIter1 F hhasP vi ts PR.one av ℓ st (toLex topTup)
    change IsMaxTup (dt.readLv (tupleIter1
      (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
      (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
      (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
      (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
      (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀
      (toLex topTup)))
    rw [hrd]
    exact isMaxTup_topTup
  · -- not exhausted below the top
    intro a ha hc
    have hrd : dt.readLv (tupleIter1
        (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
        (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
        (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
        (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀ a) =
        ofLex a :=
      dt.ixReadLv_stageIter1 F hhasP vi ts PR.one av ℓ st a
    have hmax : IsMaxTup (ofLex a) := by
      have hc2 : IsMaxTup (dt.readLv (tupleIter1
          (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.ixStageRestF F PR.zero PR.one st)
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ) mD₀ f₀
          a)) := hc
      rw [hrd] at hc2
      exact hc2
    exact absurd (tup_isTop_iff.mpr hmax (toLex topTup)) (not_le_of_gt ha)


end StageTupleRun

end IxLoop

section IxChain

variable [Fintype dt.SlotIx]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (hix : IsLinOrd F.le)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le)
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (av : Fin dt.natMax) (st : TapeSt dt A R P I)
variable {v : Univ A R P dt.KIx dt.dd → Prop}

/-- **The control after the first `n` copy loops.** -/
noncomputable def ixStageFAt {I : Type} (F : LaidFile dt A R P I) {zero : A}
    (hhas : F.toLayout.HasName zero) (one : A) (vi : dt.VarIx) {iv : dt.d.B.ι}
    (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi)) (av : Fin dt.natMax)
    (st : TapeSt dt A R P I) (elt : I → Univ A R P dt.KIx dt.dd)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A) : ℕ → dt.CtlIx → A
  | 0 =>
    (dt.stageArgs zero one vi iv ts av).initLv f₀
      (dt.ixBack F.toLayout zero one dt.dd0Le
        { st with sav := ixMark elt v, tgt := fun _ => False } v)
  | n + 1 =>
    if h : n < dt.d.B.arity iv then
      tupleIter1 (dt.stageArgs zero one vi iv ts av).setBit
        (dt.stageArgs zero one vi iv ts av).initLv
        (dt.stageArgs zero one vi iv ts av).advLv
        (dt.lvSet { st with sav := ixMark elt v } vi (ts ⟨n, h⟩)) v
        (dt.ixStageRestF F zero one { st with sav := ixMark elt v })
        (dt.ixStageXS F hhas vi ts ⟨n, h⟩) (dt.ixStageXD F hhas ⟨n, h⟩)
        (dt.ixStageTgt F hhas vi ts { st with sav := ixMark elt v } n)
          (ixStageFAt F hhas one vi ts av st elt v f₀ n) (toLex topTup)
    else ixStageFAt F hhas one vi ts av st elt v f₀ n


variable {emb : StagePh (dt.d.B.arity iv) → P} {exitPh : P}
variable {rEmb : ∀ i : StageSite (dt.d.B.arity iv),
  StageSh (dt.d.B.arity iv) i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : StageSite (dt.d.B.arity iv))
    (ρ : StageSh (dt.d.B.arity iv) i),
  PR.rules (rEmb i ρ) = dt.stageRule PR.zero PR.one emb
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).dstBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).coord
    (dt.stageArgs PR.zero PR.one vi iv ts av).bitFlag
    (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
    (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).IsMaxLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).oldSlot
    (dt.stageArgs PR.zero PR.one vi iv ts av).setAv
    exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gbot : I} (hbot : ∀ y, F.le gbot y)
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = ixMark elt v)
variable (f₀ : dt.CtlIx → A)

include hrules hR hlin hix hsepP hhasP hbot hv hvi hwkSt hmirSt in
/-- **The copy loops of a stage atom, chained and instantiated, on a clock**:
from the phase entering the first loop to the first reset's checkpoint, the
TARGET holding the composed content of every position – exactly the `hLoopsIn`
leg of `DescriptiveComplexity.Draw.Data.stage_reachesIn`, at one loop and one
walk-back per position. -/
theorem ixStageChain_reachesIn (w : ℕ)
    (hcost : ∀ (ℓ : Fin (dt.d.B.arity iv)) (a : Lex (Fin dt.dd0 → A)),
      2 * (wideRank (F.cell (dt.ixStageXS F hhasP vi ts ℓ a)) - wideRank v) + 2 ≤ w ∧
        2 * (wideRank (F.cell (dt.ixStageXD F hhasP ℓ a)) - wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 + 1) *
        dt.d.B.arity iv)
      ⟨Sum.inr (PR.stElt (stageFirstTup emb)
          ((dt.stageArgs PR.zero PR.one vi iv ts av).initLv f₀
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              { st with sav := ixMark elt v, tgt := fun _ => False } v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            { st with sav := ixMark elt v, tgt := fun _ => False }) (ixMark elt v))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .cR1)
          (dt.ixStageFAt F hhasP PR.one vi ts av st elt v f₀
            (dt.d.B.arity iv))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            { st with sav := ixMark elt v,
                      tgt := dt.ixStageTgt F hhasP vi ts
                        { st with sav := ixMark elt v } (dt.d.B.arity iv) })
          (ixMark elt v)) (PR.syElt PR.blank)⟩ := by
  classical
  have hLoop : ∀ ℓ : Fin (dt.d.B.arity iv),
      (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
        ((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1)
        ⟨Sum.inr (PR.stElt (emb (.tupP ℓ (.chk ⟨0, by omega⟩)))
            (dt.ixStageFAt F hhasP PR.one vi ts av st elt v f₀ (ℓ : ℕ))),
          Sum.inl v,
          wideTape (PR.trackTapeAt F.cell Slot.mir
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              { st with sav := ixMark elt v,
                        tgt := dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                          (ℓ : ℕ) }) (ixMark elt v))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (stageNextTup emb ℓ)
            (dt.ixStageFAt F hhasP PR.one vi ts av st elt v f₀ ((ℓ : ℕ) + 1))),
          Sum.inl v',
          wideTape (PR.trackTapeAt F.cell Slot.mir
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              { st with sav := ixMark elt v,
                        tgt := dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                          ((ℓ : ℕ) + 1) })
            (ixMark elt v)) (PR.syElt PR.blank)⟩ := by
    intro ℓ
    -- the content and the control after position `ℓ`, unfolded once
    have hD1 : dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } ((ℓ : ℕ) + 1) =
        tuplePost (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ))
          (tupleIterD (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ))
            (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
            (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ)))
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
          (toLex topTup) := by
      simp only [ixStageTgt]
      rw [dif_pos ℓ.isLt]
    have hFa1 : dt.ixStageFAt F hhasP PR.one vi ts av st elt v f₀
        ((ℓ : ℕ) + 1) =
        tupleIter1 (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ)) v
          (dt.ixStageRestF F PR.zero PR.one { st with sav := ixMark elt v })
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
          (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ))
          (dt.ixStageFAt F hhasP PR.one vi ts av st elt v f₀ (ℓ : ℕ))
          (toLex topTup) := by
      simp only [ixStageFAt]
      rw [dif_pos ℓ.isLt]
    -- the entry tape, re-walked at the source track
    have htin : PR.trackTapeAt F.cell Slot.mir
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          { st with sav := ixMark elt v,
                    tgt := dt.ixStageTgt F hhasP vi ts
                      { st with sav := ixMark elt v } (ℓ : ℕ) }) (ixMark elt v) =
      PR.trackTapeAt F.cell ((dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
        (dt.ixStageRestF F PR.zero PR.one { st with sav := ixMark elt v }
          (tupleIterD (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ))
            (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
            (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ)) (toLex botTup)))
        (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ)) := by
      have hb0 : tupleIterD (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ))
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
          (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ)) (toLex botTup) =
          dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ) :=
        iterOrd_bot (fun b => tup_isBot_iff.mpr (fun p a => botTup_le p a) b)
      rw [hb0]
      refine (trackTape_of_back F.toIxFile (t := Slot.mir) (m := ixMark elt v) ?_).trans
        (trackTape_of_back F.toIxFile
          (t := (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
          (m := dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ)) ?_).symm
      · intro r
        rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            { st with sav := ixMark elt v,
                      tgt := dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ) } r
            Slot.mir = bitVal PR.zero PR.one (bitAtOf F.cell st.mir r) from rfl,
          hmirSt]
      · intro r
        exact dt.back_lvTrack F PR.zero PR.one _ vi (ts ℓ) r
    -- the exit tape, walked back to the mirror
    have htout : PR.trackTapeAt F.cell Slot.tgt
        (dt.ixStageRestF F PR.zero PR.one { st with sav := ixMark elt v }
          (tupleIterD (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ))
            (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
            (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ)) (toLex topTup)))
        (tuplePost (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ))
          (tupleIterD (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ))
            (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
            (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ)))
          (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
          (toLex topTup)) =
      PR.trackTapeAt F.cell Slot.mir
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          { st with sav := ixMark elt v,
                    tgt := dt.ixStageTgt F hhasP vi ts
                      { st with sav := ixMark elt v } ((ℓ : ℕ) + 1) }) (ixMark elt v) := by
      refine (dt.trackTape_back_gen F
        (stA := { st with sav := ixMark elt v,
                          tgt := tupleIterD (dt.lvSet { st with sav := ixMark elt v } vi (ts ℓ))
                                   (dt.ixStageXS F hhasP vi ts ℓ) (dt.ixStageXD F hhasP ℓ)
                                   (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                                     (ℓ : ℕ)) (toLex topTup) })
        (stB := { st with sav := ixMark elt v,
                          tgt := dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                            ((ℓ : ℕ) + 1) })
        ?_ ?_).trans
        (trackTape_of_back F.toIxFile (t := Slot.mir) (m := ixMark elt v) ?_).symm
      · intro r s hs
        exact dt.ixStageRestF_off F PR.zero PR.one { st with sav := ixMark elt v } _ _ r s hs
      · intro r
        rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            { st with sav := ixMark elt v,
                      tgt := dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                        ((ℓ : ℕ) + 1) } r
            Slot.tgt = bitVal PR.zero PR.one
              (bitAtOf F.cell (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                ((ℓ : ℕ) + 1)) r)
            from rfl, hD1]
      · intro r
        rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            { st with sav := ixMark elt v,
                      tgt := dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                        ((ℓ : ℕ) + 1) } r
            Slot.mir = bitVal PR.zero PR.one (bitAtOf F.cell st.mir r) from rfl,
          hmirSt]
    rw [htin, hFa1, ← htout]
    exact dt.ixStageTuple_reachesIn
      (emb := fun p => emb (.tupP ℓ p)) (exitPh := stageNextTup emb ℓ)
      (rEmb := fun i ρ => rEmb (.tup ℓ i) ρ)
      F vi ts av ℓ { st with sav := ixMark elt v } hix hhasP hsepP
      (fun i ρ => hrules (.tup ℓ i) ρ) hR hlin hbot hv hvi hwkSt
      (mD₀ := dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v } (ℓ : ℕ))
      (f₀ := dt.ixStageFAt F hhasP PR.one vi ts av st elt v f₀ (ℓ : ℕ))
      w (hcost ℓ)
  have hchain := dt.stage_loops_reachesIn F hrules hR hlin hvi
    (fun _ => Slot.mir)
    (fun j => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      { st with sav := ixMark elt v,
                tgt := dt.ixStageTgt F hhasP vi ts
                  { st with sav := ixMark elt v } (j : ℕ) })
    (fun _ => ixMark elt v)
    (fun j r => by
      rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          { st with sav := ixMark elt v,
                    tgt := dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                      (j : ℕ) } r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkSt])
    (fun _ h => nomatch h)
    (fun j => dt.ixStageFAt F hhasP PR.one vi ts av st elt v f₀ (j : ℕ))
    _ hLoop
  exact hchain



end IxChain

/-! ### Where the address sits -/

section IxWhere

variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))

include helt in
omit [Finite R] [Finite P] in
/-- **The target of a random access is an address of argument cells alone**:
every register it holds was written by a copy round, at that round's
destination – in an argument block – over the empty mark. -/
theorem ixStageTgt_arg (st : TapeSt dt A R P I) (n : ℕ) {u : I}
    (hy : dt.ixStageTgt F hhas vi ts st n u) :
    ∃ i : dt.KIx, (elt u).1 = Tag.arg i := by
  classical
  induction n generalizing u with
  | zero => exact hy.elim
  | succ n ih =>
    rw [ixStageTgt] at hy
    split at hy
    · simp only [tuplePost] at hy
      rcases hy with ⟨hy1, -⟩ | ⟨-, hw⟩
      · exact ⟨_, by rw [hy1, ixStageXD, helt]; rfl⟩
      · exact tupleIterD_of_mem (fun u => ∃ i : dt.KIx, (elt u).1 = Tag.arg i)
          (fun _ => ⟨_, by rw [ixStageXD, helt]; rfl⟩) (fun _ hy' => ih hy') _ hw
    · exact ih hy

include helt in
omit [Finite R] [Finite P] in
/-- **The target of a random access is padded**: every register it holds is a
destination register, and those carry the round's tuple in the name slots and
`zero` beyond them. -/
theorem ixStageTgt_isPad (st : TapeSt dt A R P I) (n : ℕ) {u : I}
    (hy : dt.ixStageTgt F hhas vi ts st n u) : IsPad dt.dd0 zero (elt u).2 := by
  classical
  induction n generalizing u with
  | zero => exact hy.elim
  | succ n ih =>
    rw [ixStageTgt] at hy
    split at hy
    · simp only [tuplePost] at hy
      rcases hy with ⟨hy1, -⟩ | ⟨-, hw⟩
      · rw [hy1, ixStageXD, helt]
        exact isPad_pad
      · exact tupleIterD_of_mem (fun u => IsPad dt.dd0 zero (elt u).2)
          (fun _ => by rw [ixStageXD, helt]; exact isPad_pad)
          (fun _ hy' => ih hy') _ hw
    · exact ih hy

include helt in
/-- **The address a stage atom reads lies in the logical interval**: it is
built from padded destination registers in argument blocks alone, which is
`wmSetLt_logicalTop_of_isPad`'s hypothesis. -/
theorem wmSetLt_ixStageTgt_logicalTop {one : A} (hne : zero ≠ one)
    (hV : IsLinOrd (tupLeLex (A := A) (d := dt.dd))) (hd : dt.dd0 < dt.dd)
    (i : dt.KIx) (st : TapeSt dt A R P I) (n : ℕ) :
    WMSetLt (lexRel (· ≤ · : Tag R P dt.KIx → Tag R P dt.KIx → Prop)
      (tupLeLex (A := A) (d := dt.dd)))
      (ixAddr elt (dt.ixStageTgt F hhas vi ts st n)) logicalTop :=
  wmSetLt_logicalTop_of_isPad hne hV hd i
    (fun τ ht w hs => hs.elim fun u hu =>
      (dt.ixStageTgt_arg F hhas vi ts helt st n hu.2).elim fun i hi =>
        ht i (by
          have he : (elt u).1 = τ := congrArg Prod.fst hu.1
          rw [← he]; exact hi))
    (fun y hs => hs.elim fun u hu => by
      rw [← show elt u = y from hu.1]
      exact dt.ixStageTgt_isPad F hhas vi ts helt st n hu.2)

end IxWhere

/-! ### The stage atom's run at an arbitrary file

The random access, end to end: the save, the clear, the copy loops of
`ixStageChain_reachesIn`, the reset–clear–seek out to the address the marks stand
for, the read under the head, the restore and the seek home. Everything below
it is `DescriptiveComplexity.Draw.Data.stage_run`, which takes the file as a
parameter; what this adds is the instantiation – the built target, and the two
facts that put it in the working area.
-/

section IxAtomRun

variable [Fintype dt.SlotIx] [Finite dt.KIx] [Finite I]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (av : Fin dt.natMax) (st : TapeSt dt A R P I)
variable (hix : IsLinOrd F.le)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le)
variable {elt : I → Univ A R P dt.KIx dt.dd} {Use : I → Prop}
variable (hinj : Function.Injective elt)
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd), Use u →
  WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable {emb : StagePh (dt.d.B.arity iv) → P} {exitPh : P}
variable {rEmb : ∀ i : StageSite (dt.d.B.arity iv), StageSh (dt.d.B.arity iv) i → R}
variable (hrules : ∀ (i : StageSite (dt.d.B.arity iv))
    (ρ : StageSh (dt.d.B.arity iv) i),
  PR.rules (rEmb i ρ) = dt.stageRule PR.zero PR.one emb
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).dstBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).coord
    (dt.stageArgs PR.zero PR.one vi iv ts av).bitFlag
    (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
    (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).IsMaxLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).oldSlot
    (dt.stageArgs PR.zero PR.one vi iv ts av).setAv
    exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gtop gbot : I} (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
variable {e₀ : Univ A R P dt.KIx dt.dd} (he₀ : ∀ y, WMLe e₀ y)
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = ixMark elt v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hvh : IxHolds elt Use v)
variable (hxdUse : ∀ (ℓ : Fin (dt.d.B.arity iv)) (b : Lex (Fin dt.dd0 → A)),
  Use (dt.ixStageXD F hhasP ℓ b))
variable (f₀ : dt.CtlIx → A)

include hrules hR hlin hix hhasP hsepP hinj hmono hup heltP hord htop hbot he₀
  hwork hv hvi hwkSt hmirSt hbotSt hvh hxdUse in
/-- **The stage atom's run at an arbitrary file, on a clock**: from its entry
phase to the exit phase, the verdict – the `old` track's bit at the address the
built TARGET stands for – stored in the atom's control slot, the marker, mirror
and save restored at the home address. The cost is the atom's nine trips and
thirteen dispatches over the copy loops' own. -/
theorem ixStageAtom_reachesIn (b : Bool) (w wG wP wR wK : ℕ)
    (hcost : ∀ (ℓ : Fin (dt.d.B.arity iv)) (a : Lex (Fin dt.dd0 → A)),
      2 * (wideRank (F.cell (dt.ixStageXS F hhasP vi ts ℓ a)) - wideRank v) + 2 ≤ w ∧
        2 * (wideRank (F.cell (dt.ixStageXD F hhasP ℓ a)) - wideRank v) + 2 ≤ w)
    (hgap : ∀ u u' : I, IxSucc F.le u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
    (hwP : wideRank (F.cell gtop) + 2 +
      ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
    (hwR : ∀ s : Univ A R P dt.KIx dt.dd → Prop,
      WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
    (hwK : ∀ T : Univ A R P dt.KIx dt.dd → Prop,
      WMSetLt WMLe T (F.cell gbot) →
      wideRank T *
          (1 + (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
              wideRank (F.cell gbot)) +
            (wideRank (F.cell gtop) + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
              wideRank (F.cell gbot) + 4)) + 1 +
        (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) ≤ wK)
    (hb : st.old iv (ixAddr elt
        (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
          (dt.d.B.arity iv))) ↔ b = true) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (5 * wP + 2 * wR + 2 * wK +
        (((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 + 1) *
          dt.d.B.arity iv) + 13)
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.stageArgs PR.zero PR.one vi iv ts av).setAv b
            (dt.ixStageFAt F hhasP PR.one vi ts av st elt v f₀ (dt.d.B.arity iv))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              (dt.ixStageAtSt st elt v (ixAddr elt
                (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                  (dt.d.B.arity iv))))
              (ixAddr elt (dt.ixStageTgt F hhasP vi ts
                { st with sav := ixMark elt v } (dt.d.B.arity iv)))))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixStageEndSt st elt v))
          (dt.ixStageEndSt st elt v).mir) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  -- the built TARGET is an address over argument elements alone, hence sits in
  -- the working area; in particular it misses the least element, which has no
  -- block
  have hargTb : ∀ x, ixAddr elt (dt.ixStageTgt F hhasP vi ts
      { st with sav := ixMark elt v } (dt.d.B.arity iv)) x →
      ∃ i : dt.KIx, x.1 = Tag.arg i := by
    rintro x ⟨u, he, hm⟩
    obtain ⟨i, hi⟩ := dt.ixStageTgt_arg F hhasP vi ts heltP _ _ hm
    rw [he] at hi
    exact ⟨i, hi⟩
  have hmTb : ¬ixAddr elt (dt.ixStageTgt F hhasP vi ts
      { st with sav := ixMark elt v } (dt.d.B.arity iv)) e₀ := by
    intro hc
    obtain ⟨i, hi⟩ := hargTb e₀ hc
    have hnone := tagBlk_eq_none_of_least (R := R) (P := P)
      (fun y => (hord e₀ y).mp (he₀ y))
    rw [hi] at hnone
    exact nomatch hnone
  have hT : WMSetLt WMLe (ixAddr elt (dt.ixStageTgt F hhasP vi ts
      { st with sav := ixMark elt v } (dt.d.B.arity iv))) (F.cell gbot) :=
    hwork hargTb gbot
  obtain ⟨T', hTi⟩ := exists_wmIncr hlin ⟨e₀, hmTb⟩
  refine dt.stage_reachesIn (F := F) (hinj := hinj) (hmono := hmono) (hup := hup)
    (hrules := hrules) (hR := hR) (hlin := hlin) (hix := hix) (htop := htop)
    (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hmirSt := hmirSt)
    (hbotSt := hbotSt) (hTh := ixHolds_ixAddr (fun u hu => ?_)) (hvh := hvh)
    (hT := hT) (hTi := hTi) (hgap := hgap) (wP := wP) (wR := wR) (wK := wK)
    (hwP := hwP) (hwR := hwR) (hwK := hwK) (hbT := ?_) (holdmir := ?_)
    (hLoopsIn := ?_)
  · obtain ⟨ℓ, b, -, rfl, -⟩ :=
      (dt.ixStageTgt_iff F hhasP vi ts { st with sav := ixMark elt v } _ u).mp hu
    exact hxdUse ℓ b
  · change bitVal PR.zero PR.one
      (st.old iv (ixAddr elt (dt.ixStageTgt F hhasP vi ts
        { st with sav := ixMark elt v } (dt.d.B.arity iv)))) = PR.one ↔ b = true
    exact (bitVal_iff hzo).trans hb
  · exact fun h => nomatch h
  · rw [ixMark_ixAddr hinj]
    exact dt.ixStageChain_reachesIn F vi ts hix hhasP hsepP av st
      hrules hR hlin hbot hv hvi hwkSt hmirSt f₀ w hcost

end IxAtomRun

/-! ### The address the marks stand for, block by block

The one place the file's naming and the encoding have to agree, and the reason
they can: with the coherence hypothesis, the address a clocked program's TARGET
spells has the *same blocks* as the address a space-bounded one builds, so every
statement of the semantics about that address – the dictionary, `trackOf`, the
logical interval – holds of the clocked run with no restatement.
-/

variable {elt : I → Univ A R P dt.KIx dt.dd}
variable [L.Structure A]

omit [Finite R] [Finite P] in
/-- **The composed TARGET's argument blocks are the sources'**: after all copy
loops, block `ℓ` of the address the marks stand for is the position's source
block – the copy is faithful on the named registers, and an encoding holds no
other tuples. -/
theorem wmBlk_ixStageTgt_eq_encMap {one : A} (hinj : Function.Injective elt)
    (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))
    (st : TapeSt dt A R P I) {p : Fin (dt.d.B.arity iv) → dt.X.Map A}
    (hsrc : ∀ ℓ : Fin (dt.d.B.arity iv),
      wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (p ℓ))
    (ℓ : Fin (dt.d.B.arity iv)) :
    wmBlk (ixAddr elt (dt.ixStageTgt F hhas vi ts st (dt.d.B.arity iv)))
        (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx) =
      encMap dt.ly zero one (p ℓ) := by
  classical
  funext w
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨u, he, hm⟩ := h
    obtain ⟨ℓ', b, -, hy, hsrcbit⟩ :=
      (dt.ixStageTgt_iff F hhas vi ts st (dt.d.B.arity iv) u).mp hm
    rw [hy, ixStageXD, helt] at he
    have htag := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    have hℓ : ℓ' = ℓ := by
      have h1 : (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ') :
          Fin dt.ko ⊕ Fin dt.ki)) : Lex (Fin dt.ko ⊕ Fin dt.ki)) =
          toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki)) := by
        injection htag
      exact Fin.castLE_injective _ (Sum.inl.inj (congrArg ofLex h1))
    subst hℓ
    rw [show w = pad (dd := dt.dd) zero (ofLex b) from hsnd.symm]
    have hbit : wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ')))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ'))) : Tag R P dt.KIx)
        (pad (dd := dt.dd) zero (ofLex b)) :=
      ⟨dt.ixStageXS F hhas vi ts ℓ' b, by rw [ixStageXS, helt]; rfl, hsrcbit⟩
    rw [hsrc ℓ'] at hbit
    exact hbit
  · have hpadded : w = pad (dd := dt.dd) zero (unpad dt.dd0Le w) :=
      (pad_unpad dt.dd0Le fun j hj => isPad_of_encMap h j hj).symm
    have hsrcbit : wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) w := by
      rw [hsrc ℓ]; exact h
    obtain ⟨u, he, hm⟩ := hsrcbit
    have hxs : elt (dt.ixStageXS F hhas vi ts ℓ (toLex (unpad dt.dd0Le w))) =
        ((Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx), w) := by
      rw [ixStageXS, helt, ofLex_toLex, ← hpadded]
      rfl
    refine ⟨dt.ixStageXD F hhas ℓ (toLex (unpad dt.dd0Le w)), ?_, ?_⟩
    · rw [ixStageXD, helt, ofLex_toLex, ← hpadded]
      rfl
    · refine (dt.ixStageTgt_iff F hhas vi ts st (dt.d.B.arity iv) _).mpr
        ⟨ℓ, toLex (unpad dt.dd0Le w), ℓ.isLt, rfl, ?_⟩
      have hu : dt.ixStageXS F hhas vi ts ℓ (toLex (unpad dt.dd0Le w)) = u :=
        hinj (hxs.trans he.symm)
      rw [hu]
      exact hm

/-! ### Blindness to the two scratch registers -/

section IxScratch

variable [Fintype dt.SlotIx] [Finite dt.KIx]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (one : A) (av : Fin dt.natMax) {elt : I → Univ A R P dt.KIx dt.dd}
variable {st : TapeSt dt A R P I} {v : Univ A R P dt.KIx dt.dd → Prop}

omit [Finite R] [Finite P] [L.Structure A] [Fintype dt.SlotIx] [Finite dt.KIx] in
/-- **The TARGET a random access builds is blind to the two scratch
registers**, at an arbitrary file: every copy round reads a level's register
set, and the loop pins SAV at the home address itself. -/
theorem ixStageTgt_congr_scratch {st' : TapeSt dt A R P I}
    (h : dt.ScratchEq st st') (n : ℕ) :
    dt.ixStageTgt F hhas vi ts { st with sav := ixMark elt v } n =
      dt.ixStageTgt F hhas vi ts { st' with sav := ixMark elt v } n := by
  have hlv : ∀ j : Fin (dt.nOf vi),
      dt.lvSet { st with sav := ixMark elt v } vi j =
        dt.lvSet { st' with sav := ixMark elt v } vi j := by
    intro j
    simp only [lvSet, h.2.1, h.2.2.1]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ixStageTgt]
    by_cases hn : n < dt.d.B.arity iv
    · rw [dif_pos hn, dif_pos hn, hlv, ih]
    · rw [dif_neg hn, dif_neg hn, ih]

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [L.Structure A] [Finite dt.KIx] in
/-- **The control of the copy loops is blind to them too**, at an arbitrary
file: the destination-dependent background overwrites TARGET, and the loop
reads it at the home cell alone. -/
theorem ixStageFAt_congr_scratch {st' : TapeSt dt A R P I}
    (h : dt.ScratchEq st st') (hreg : ¬∃ u : I, v = F.cell u)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.ixStageFAt F hhas one vi ts av st elt v f₀ n =
      dt.ixStageFAt F hhas one vi ts av st' elt v f₀ n := by
  have hlv : ∀ j : Fin (dt.nOf vi),
      dt.lvSet { st with sav := ixMark elt v } vi j =
        dt.lvSet { st' with sav := ixMark elt v } vi j := by
    intro j
    simp only [lvSet, h.2.1, h.2.2.1]
  have hrest : ∀ m' : I → Prop,
      dt.ixStageRestF F zero one { st with sav := ixMark elt v } m' v =
        dt.ixStageRestF F zero one { st' with sav := ixMark elt v } m' v :=
    fun m' => (h.ixScratch (ixMark elt v) m').ixBack hreg
  induction n with
  | zero =>
    exact congrArg _ ((h.ixScratch (ixMark elt v) (fun _ => False)).ixBack hreg)
  | succ n ih =>
    simp only [ixStageFAt]
    by_cases hn : n < dt.d.B.arity iv
    · rw [dif_pos hn, dif_pos hn, hlv, ih,
        ixStageTgt_congr_scratch (dt := dt) F hhas vi ts h n]
      exact tupleIter1_congr_restF hrest _ _ _ _ _
    · rw [dif_neg hn, dif_neg hn, ih]

end IxScratch


end Data

end Draw

end DescriptiveComplexity
