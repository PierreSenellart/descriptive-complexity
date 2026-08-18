/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawArgs
import DescriptiveComplexity.Problems.Wide.DrawRunIter
import DescriptiveComplexity.Problems.Wide.DrawRunStage

/-!
# The comparison atoms, instantiated

The first semantic instantiation: the element loop's run at the comparison
pack `DescriptiveComplexity.Draw.Data.cmpArgs`. The enumeration is the
lexicographic order on the narrow tuples, the generated family of
`DescriptiveComplexity.Draw.elemFam` carries the loop element and the three
bookkeeping flags, and the two inductions this file contributes are the
loop's two invariants:

* **the loop element is the round's tuple**
  (`DescriptiveComplexity.Draw.Data.readLv_cmpFam`), so the name guards
  stop at the padded cell of the enumerated tuple and the read bits are the
  two block values' membership bits there;
* **the flags fold the strict prefix**
  (`DescriptiveComplexity.Draw.Data.cmpFlags_cmpIter`): agreement so far,
  a difference seen, and the first difference's verdict, over the tuples
  strictly below the round's.

`DescriptiveComplexity.Draw.Data.cmp_run` is the machine run; the final
control's verdict bit is characterized against the two tracks' padded bits
(`DescriptiveComplexity.Draw.Data.ctlBit_avC_cmp_run`), which is the form
`DescriptiveComplexity.Problems.Wide.DrawCmp` turns into the equality and
order atoms.
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
variable {I : Type}
variable (RF : LaidFile dt A R P I)

/-! ### The register a level reads, and its backing -/

/-- **The register set a level's track holds**: the working address for a
free level, the VAL register for a quantified one – the contents behind
`DescriptiveComplexity.Draw.Data.lvTrack`. -/
noncomputable def lvSet (st : TapeSt dt A R P I) (v : dt.VarIx)
    (j : Fin (dt.nOf v)) : I → Prop :=
  if (j : ℕ) < dt.arOf v then st.mir else st.val

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] in
/-- A level's track is backed by its register set. -/
theorem back_lvTrack (zero one : A) (st : TapeSt dt A R P I) (v : dt.VarIx)
    (j : Fin (dt.nOf v)) (r : Univ A R P dt.KIx dt.dd → Prop) :
    dt.ixBack RF.toLayout zero one dt.dd0Le st r (dt.lvTrack v j) =
      bitVal zero one (bitAtOf RF.cell (dt.lvSet st v j) r) := by
  rw [lvTrack, lvSet]
  by_cases h : (j : ℕ) < dt.arOf v
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] in
/-- **A level's track is backed by its register set, at the elementwise file**:
the same statement read at `DescriptiveComplexity.Draw.Data.back`, which is
what a space-bounded program's files say. -/
theorem back_lvTrackD (F : RegFile (Univ A R P dt.KIx dt.dd))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    (zero one : A) (st : TapeStD dt A R P) (v : dt.VarIx)
    (j : Fin (dt.nOf v)) (r : Univ A R P dt.KIx dt.dd → Prop) :
    dt.back F.cell zero one dt.dd0Le st r (dt.lvTrack v j) =
      bitVal zero one (bitAtOf F.cell (dt.lvSet st v j) r) :=
  dt.back_lvTrack (laidFile F hord) zero one st v j r

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
/-- **A level's register set depends on the mirror and VAL alone** — which
is what lets everything read through it be transported between states that
share those two registers. -/
theorem lvSet_congr (vi : dt.VarIx) {st st' : TapeSt dt A R P I}
    (hmir : st.mir = st'.mir) (hval : st.val = st'.val)
    (j : Fin (dt.nOf vi)) : dt.lvSet st vi j = dt.lvSet st' vi j := by
  rw [lvSet, lvSet, hmir, hval]

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
/-- The marker slot is not a level's track. -/
theorem wk_ne_lvTrack (v : dt.VarIx) (j : Fin (dt.nOf v)) :
    (Slot.wk : dt.SlotIx) ≠ dt.lvTrack v j := by
  rw [lvTrack]
  by_cases h : (j : ℕ) < dt.arOf v
  · rw [if_pos h]
    exact fun hc => nomatch hc
  · rw [if_neg h]
    exact fun hc => nomatch hc

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
/-- The register mark is not a level's track. -/
theorem reg_ne_lvTrack (v : dt.VarIx) (j : Fin (dt.nOf v)) :
    (Slot.reg : dt.SlotIx) ≠ dt.lvTrack v j := by
  rw [lvTrack]
  by_cases h : (j : ℕ) < dt.arOf v
  · rw [if_pos h]
    exact fun hc => nomatch hc
  · rw [if_neg h]
    exact fun hc => nomatch hc

/-! ### The loop element through the comparison's operations -/

variable {dt}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
/-- The loop element rides along `cmpInit`. -/
theorem readLv_cmpInit {zero one : A} (f : dt.CtlIx → A) :
    dt.readLv (dt.cmpInit zero one f) = dt.readLv f := by
  funext j
  rw [readLv, readLv, cmpInit, setCtl_of_ne (lvC_ne_cmpAccC (dt := dt) j),
    setCtl_of_ne (lvC_ne_cmpDecC (dt := dt) j),
    setCtl_of_ne (lvC_ne_cmpValC (dt := dt) j)]

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
/-- The loop element rides along a read's store. -/
theorem readLv_setCtl_cmpRdC {zero one : A} (hnf : 2 ≤ dt.nfDim) (k : Fin 2)
    (b : Prop) (f : dt.CtlIx → A) :
    dt.readLv (dt.setCtl zero one (dt.cmpRdC hnf k) b f) = dt.readLv f := by
  funext j
  rw [readLv, readLv, setCtl_of_ne (show dt.lvC j ≠ dt.cmpRdC hnf k from
    fun h => nomatch h)]

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
/-- The loop element after an advance is the next tuple. -/
theorem readLv_advLvN [Finite A] [Nonempty A] (f : dt.CtlIx → A) :
    dt.readLv (dt.advLvN f) = tupNext (dt.readLv f) :=
  readLv_putLv f _

/-! ### The comparison's generated family -/

section CmpFam

variable [Nonempty A]
variable (zero one : A)
variable (hhas : RF.toLayout.HasName zero)
variable (vi : dt.VarIx) (av : Fin dt.natMax) (hnf : 2 ≤ dt.nfDim)
variable (isEq : Bool) (j₁ j₂ : Fin (dt.nOf vi))
variable (st : TapeSt dt A R P I)
variable (vAdr : Univ A R P dt.KIx dt.dd → Prop)

/-- **The two register sets a comparison reads**: the level's register per
paired read. -/
noncomputable def cmpSet : Fin 2 → I → Prop :=
  fun k => if k = 0 then dt.lvSet st vi j₁ else dt.lvSet st vi j₂

/-- **The cell of a comparison's round**: the padded cell of the round's
tuple, in the read's block. -/
noncomputable def cmpCell (b : Lex (Fin dt.dd0 → A)) (k : Fin 2) : I :=
  RF.toLayout.reg hhas (if k = 0 then dt.lvBlk vi j₁ else dt.lvBlk vi j₂)
    (ofLex b)

/-- **The comparison's generated family**, at its pack. -/
noncomputable def cmpFam (f₀ : dt.CtlIx → A) (b : Lex (Fin dt.dd0 → A))
    (j : Fin 3) : dt.CtlIx → A :=
  elemFam (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag
    (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).initEl
    (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).advEl
    (dt.ixBack RF.toLayout zero one dt.dd0Le st) vAdr (dt.cmpSet vi j₁ j₂ st)
    (dt.cmpCell RF zero hhas vi j₁ j₂) f₀ b j

variable {zero one hhas vi av isEq j₁ j₂ st vAdr}

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A comparison is blind to the two scratch registers**: it reads the
levels' register sets, which are the mirror and VAL
(`DescriptiveComplexity.Draw.Data.lvSet`), and its background at the
working cell alone. -/
theorem cmpFam_congr_scratch {st' : TapeSt dt A R P I}
    (h : dt.ScratchEq st st')
    (hreg : ¬∃ u : I, vAdr = RF.cell u)
    (f₀ : dt.CtlIx → A) (b : Lex (Fin dt.dd0 → A)) (j : Fin 3) :
    dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ b j =
      dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st' vAdr f₀ b j := by
  have hset : dt.cmpSet vi j₁ j₂ st = dt.cmpSet vi j₁ j₂ st' := by
    funext k
    simp only [cmpSet, lvSet, h.2.1, h.2.2.1]
  rw [cmpFam, cmpFam, hset]
  exact elemFam_congr_rest (h.ixBack (lay := RF.toLayout) hreg) _ _ _ _

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- The read tracks are backed by the register sets. -/
theorem back_cmpSet (k : Fin 2) (r : Univ A R P dt.KIx dt.dd → Prop) :
    dt.ixBack RF.toLayout zero one dt.dd0Le st r
        ((dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k) =
      bitVal zero one (bitAtOf RF.cell (dt.cmpSet vi j₁ j₂ st k) r) := by
  by_cases hk : k = 0
  · rw [show (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k =
      dt.lvTrack vi j₁ from by rw [cmpArgs]; exact if_pos hk,
      show dt.cmpSet vi j₁ j₂ st k = dt.lvSet st vi j₁ from if_pos hk]
    exact dt.back_lvTrack RF zero one st vi j₁ r
  · rw [show (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k =
      dt.lvTrack vi j₂ from by rw [cmpArgs]; exact if_neg hk,
      show dt.cmpSet vi j₁ j₂ st k = dt.lvSet st vi j₂ from if_neg hk]
    exact dt.back_lvTrack RF zero one st vi j₂ r

omit [Fintype dt.SlotIx] in
/-- The marker slot is no read track. -/
theorem wk_ne_cmp_rdTrack (k : Fin 2) :
    (Slot.wk : dt.SlotIx) ≠
      (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k := by
  by_cases hk : k = 0
  · rw [show (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k =
      dt.lvTrack vi j₁ from by rw [cmpArgs]; exact if_pos hk]
    exact dt.wk_ne_lvTrack vi j₁
  · rw [show (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k =
      dt.lvTrack vi j₂ from by rw [cmpArgs]; exact if_neg hk]
    exact dt.wk_ne_lvTrack vi j₂

omit [Fintype dt.SlotIx] in
/-- The register mark is no read track. -/
theorem reg_ne_cmp_rdTrack (k : Fin 2) :
    (Slot.reg : dt.SlotIx) ≠
      (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k := by
  by_cases hk : k = 0
  · rw [show (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k =
      dt.lvTrack vi j₁ from by rw [cmpArgs]; exact if_pos hk]
    exact dt.reg_ne_lvTrack vi j₁
  · rw [show (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).rdTrack k =
      dt.lvTrack vi j₂ from by rw [cmpArgs]; exact if_neg hk]
    exact dt.reg_ne_lvTrack vi j₂

/-! ### The loop element is the round's tuple -/

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- The loop element rides along a stored read. -/
theorem readLv_cmp_setFlag (k : Fin 2) (bb : Bool) (q : dt.CtlIx → A)
    (g : dt.SlotIx → A) :
    dt.readLv ((dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag k bb q g) =
      dt.readLv q := by
  change dt.readLv (dt.setCtl zero one (dt.cmpRdC hnf k) (bb = true) q) = _
  rw [readLv_setCtl_cmpRdC]

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- The loop starts at the least tuple. -/
theorem readLv_cmp_init (q : dt.CtlIx → A) (g : dt.SlotIx → A) :
    dt.readLv ((dt.cmpArgs zero one vi av hnf isEq j₁ j₂).initEl q g) =
      botTup := by
  change dt.readLv (dt.cmpInit zero one (dt.initLvN q)) = _
  rw [readLv_cmpInit, initLvN, readLv_putLv]

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- An advance steps the tuple. -/
theorem readLv_cmp_adv (q : dt.CtlIx → A) (g : dt.SlotIx → A) :
    dt.readLv ((dt.cmpArgs zero one vi av hnf isEq j₁ j₂).advEl q g) =
      tupNext (dt.readLv q) := by
  change dt.readLv (dt.advLvN (dt.cmpFold zero one hnf q)) = _
  rw [readLv_advLvN, readLv_cmpFold]

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- The loop element rides along a whole round's reads. -/
theorem readLv_cmp_chain (bit : Fin 2 → Prop) (base : dt.CtlIx → A)
    (g : dt.SlotIx → A) : ∀ n : ℕ,
    dt.readLv (chainSt bit
      (fun j' b q' =>
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' b q' g)
      base n) = dt.readLv base := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n < 2
    · by_cases hb : bit ⟨n, h⟩
      · rw [chainSt_succ_pos h hb, readLv_cmp_setFlag, ih]
      · rw [chainSt_succ_neg h hb, readLv_cmp_setFlag, ih]
    · have hskip : chainSt bit
          (fun j' b q' =>
            (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' b q' g)
          base (n + 1) = chainSt bit
          (fun j' b q' =>
            (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' b q' g)
          base n := by
        simp only [chainSt]
        rw [dif_neg h]
      rw [hskip]
      exact ih

omit [Fintype dt.SlotIx] [Nonempty A] in
/-- **A cover in the lexicographic order steps to the next tuple.** -/
theorem ofLex_eq_tupNext_of_covers {D : ℕ} {w z : Lex (Fin D → A)}
    (hwz : w < z) (hnb : ∀ c, ¬(w < c ∧ c < z)) :
    ofLex z = tupNext (ofLex w) := by
  have hmax : ¬IsMaxTup (ofLex w) := by
    intro hc
    exact absurd (tup_isTop_iff.mpr hc z) (not_le_of_gt hwz)
  have h2 : w ⋖ toLex (tupNext (ofLex w)) :=
    tupSucc_iff_covBy.mp (tupSucc_tupNext hmax)
  have h1 : w ⋖ z := ⟨hwz, fun c hc1 hc2 => hnb c ⟨hc1, hc2⟩⟩
  rcases lt_trichotomy z (toLex (tupNext (ofLex w))) with h | h | h
  · exact absurd h (h2.2 h1.1)
  · exact congrArg ofLex h
  · exact absurd h (fun hgt => h1.2 h2.1 hgt)

/-- The bottom of the lexicographic order is the least tuple. -/
theorem ofLex_eq_botTup_of_bot {D : ℕ} {z : Lex (Fin D → A)}
    (hz : ∀ b, z ≤ b) : ofLex z = botTup := by
  have h1 : z ≤ toLex botTup := hz _
  have h2 : toLex (botTup : Fin D → A) ≤ z := tup_isBot_iff.mpr botTup_le z
  exact congrArg ofLex (le_antisymm h1 h2)

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The loop element is the round's tuple**, at every stage of the
family. -/
theorem readLv_cmpFam (f₀ : dt.CtlIx → A) (b : Lex (Fin dt.dd0 → A))
    (j : Fin 3) :
    dt.readLv (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ b j) =
      ofLex b := by
  have hiter : ∀ b' : Lex (Fin dt.dd0 → A),
      dt.readLv (elemIter
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).initEl
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).advEl
        (dt.ixBack RF.toLayout zero one dt.dd0Le st) vAdr (dt.cmpSet vi j₁ j₂ st)
        (dt.cmpCell RF zero hhas vi j₁ j₂) f₀ b') = ofLex b' := by
    intro b'
    induction b' using order_induction with
    | hmin z hz =>
      rw [elemIter, iterOrd_bot hz, readLv_cmp_init,
        ofLex_eq_botTup_of_bot hz]
    | hstep w z hwz hnb ih =>
      have hz2 : elemIter
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).initEl
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).advEl
          (dt.ixBack RF.toLayout zero one dt.dd0Le st) vAdr (dt.cmpSet vi j₁ j₂ st)
          (dt.cmpCell RF zero hhas vi j₁ j₂) f₀ z =
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).advEl
          (chainSt
            (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ w j'))
            (fun j' bb q' =>
              (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
                (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
            (elemIter (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag
              (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).initEl
              (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).advEl
              (dt.ixBack RF.toLayout zero one dt.dd0Le st) vAdr (dt.cmpSet vi j₁ j₂ st)
              (dt.cmpCell RF zero hhas vi j₁ j₂) f₀ w) 2)
          (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr) :=
        iterOrd_covers hwz hnb
      rw [hz2, readLv_cmp_adv, readLv_cmp_chain, ih,
        ofLex_eq_tupNext_of_covers hwz hnb]
  rw [cmpFam, elemFam, readLv_cmp_chain]
  exact hiter b

/-! ### The flags fold the strict prefix -/

variable (zero hhas vi j₁ j₂ st) in
/-- **The two blocks agree at a tuple**: the two reads' bits coincide. -/
def CmpAgr (b : Lex (Fin dt.dd0 → A)) : Prop :=
  dt.cmpSet vi j₁ j₂ st 0 (dt.cmpCell RF zero hhas vi j₁ j₂ b 0) ↔
    dt.cmpSet vi j₁ j₂ st 1 (dt.cmpCell RF zero hhas vi j₁ j₂ b 1)

variable (zero hhas vi j₁ j₂ st) in
/-- **The first difference is at this tuple, the second block holding it**:
everything below agrees, and here only the second block holds the cell. -/
def CmpFst (b : Lex (Fin dt.dd0 → A)) : Prop :=
  (¬dt.cmpSet vi j₁ j₂ st 0 (dt.cmpCell RF zero hhas vi j₁ j₂ b 0) ∧
    dt.cmpSet vi j₁ j₂ st 1 (dt.cmpCell RF zero hhas vi j₁ j₂ b 1)) ∧
  ∀ u < b, dt.CmpAgr RF zero hhas vi j₁ j₂ st u

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- A slot off the paired reads rides along the whole chain. -/
theorem cmp_chain_apply_ne {bit : Fin 2 → Prop} {base : dt.CtlIx → A}
    {g : dt.SlotIx → A} {q : dt.CtlIx}
    (hq : ∀ k : Fin 2, q ≠ dt.cmpRdC hnf k) : ∀ n : ℕ,
    chainSt bit
      (fun j' b q' =>
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' b q' g)
      base n q = base q := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n < 2
    · have hupd : ∀ (k : Fin 2) (bb : Bool) (x : dt.CtlIx → A),
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag k bb x g q =
            x q := by
        intro k bb x
        change dt.setCtl zero one (dt.cmpRdC hnf k) (bb = true) x q = x q
        exact setCtl_of_ne (hq k) _ _
      by_cases hb : bit ⟨n, h⟩
      · rw [chainSt_succ_pos h hb, hupd, ih]
      · rw [chainSt_succ_neg h hb, hupd, ih]
    · have hskip : chainSt bit
          (fun j' b q' =>
            (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' b q' g)
          base (n + 1) = chainSt bit
          (fun j' b q' =>
            (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' b q' g)
          base n := by
        simp only [chainSt]
        rw [dif_neg h]
      rw [hskip]
      exact ih

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- **A stored-read chain reads back**, slot by slot: the chain writing each
read into its own control slot delivers every bit already written. -/
theorem ctlBit_chain_setCtl {zero one : A} (hzo : zero ≠ one) {nr : ℕ}
    (slotOf : Fin nr → dt.CtlIx)
    (hinj : ∀ j j' : Fin nr, slotOf j = slotOf j' → j = j')
    (bit : Fin nr → Prop) (base : dt.CtlIx → A) :
    ∀ (n : ℕ) (j : Fin nr), (j : ℕ) < n →
      (dt.ctlBit one (chainSt bit
        (fun j' b q' => dt.setCtl zero one (slotOf j') (b = true) q')
        base n) (slotOf j) ↔ bit j) := by
  classical
  intro n
  induction n with
  | zero => exact fun j hj => absurd hj (by omega)
  | succ n ih =>
    intro j hj
    by_cases h : n < nr
    · have hcase : ∀ bb : Bool,
          ((if bit ⟨n, h⟩ then true else false) = bb) →
          (dt.ctlBit one (dt.setCtl zero one (slotOf ⟨n, h⟩) (bb = true)
            (chainSt bit
              (fun j' b q' => dt.setCtl zero one (slotOf j') (b = true) q')
              base n)) (slotOf j) ↔ bit j) := by
        intro bb hbb
        by_cases hjn : (j : ℕ) = n
        · have hjeq : j = ⟨n, h⟩ := Fin.ext hjn
          rw [hjeq, ctlBit_setCtl_self hzo]
          rw [← hbb]
          by_cases hb : bit ⟨n, h⟩
          · rw [if_pos hb]
            exact ⟨fun _ => hb, fun _ => rfl⟩
          · rw [if_neg hb]
            exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc hb⟩
        · have hne : slotOf j ≠ slotOf ⟨n, h⟩ := fun hc =>
            absurd (congrArg Fin.val (hinj _ _ hc)) hjn
          rw [ctlBit_setCtl_of_ne hne]
          exact ih j (by omega)
      by_cases hb : bit ⟨n, h⟩
      · rw [chainSt_succ_pos h hb]
        exact hcase true (by rw [if_pos hb])
      · rw [chainSt_succ_neg h hb]
        exact hcase false (by rw [if_neg hb])
    · have hskip : chainSt bit
          (fun j' b q' => dt.setCtl zero one (slotOf j') (b = true) q')
          base (n + 1) = chainSt bit
          (fun j' b q' => dt.setCtl zero one (slotOf j') (b = true) q')
          base n := by
        simp only [chainSt]
        rw [dif_neg h]
      rw [hskip]
      have hjn : (j : ℕ) < n := lt_of_lt_of_le j.isLt (Nat.le_of_not_lt h)
      exact ih j hjn

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- **The whole chain's stored reads**: the two bits of the round. -/
theorem ctlBit_cmp_chain_rd (hzo : zero ≠ one) {bit : Fin 2 → Prop}
    {base : dt.CtlIx → A} {g : dt.SlotIx → A} (k : Fin 2) :
    dt.ctlBit one
      (chainSt bit
        (fun j' b q' =>
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' b q' g)
        base 2) (dt.cmpRdC hnf k) ↔ bit k :=
  dt.ctlBit_chain_setCtl hzo (fun k' => dt.cmpRdC hnf k')
    (fun j j' hc => by
      have h2 : Fin.castLE hnf j = Fin.castLE hnf j' := dt.rdfC_injective hc
      have hval := congrArg Fin.val h2
      exact Fin.ext hval)
    bit base 2 k k.isLt

omit [Fintype dt.SlotIx] in
/-- A control slot off the loop variables rides along an advance, showing
the fold's value. -/
theorem ctlBit_cmp_advEl {q : dt.CtlIx} (hq : ∀ j : Fin dt.dd0, q ≠ dt.lvC j)
    (f : dt.CtlIx → A) (g : dt.SlotIx → A) :
    dt.ctlBit one ((dt.cmpArgs zero one vi av hnf isEq j₁ j₂).advEl f g) q ↔
      dt.ctlBit one (dt.cmpFold zero one hnf f) q := by
  change dt.ctlBit one (dt.advLvN (dt.cmpFold zero one hnf f)) q ↔ _
  rw [ctlBit, ctlBit, advLvN, putLv_of_not_lv hq]

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The flags fold the strict prefix**: at every round's entry, the three
bookkeeping bits are agreement everywhere below, a difference seen below,
and a first difference below with the second block holding it. -/
theorem cmpFlags_cmpFam (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (b : Lex (Fin dt.dd0 → A)) :
    (dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ b 0)
        dt.cmpAccC ↔ ∀ u < b, dt.CmpAgr RF zero hhas vi j₁ j₂ st u) ∧
    (dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ b 0)
        dt.cmpDecC ↔ ∃ u < b, ¬dt.CmpAgr RF zero hhas vi j₁ j₂ st u) ∧
    (dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ b 0)
        dt.cmpValC ↔ ∃ u < b, dt.CmpFst RF zero hhas vi j₁ j₂ st u) := by
  induction b using order_induction with
  | hmin z hz =>
    have hz0 : dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ z 0 =
        dt.cmpInit zero one (dt.initLvN f₀) :=
      iterOrd_bot hz
    rw [hz0]
    have hnou : ∀ u : Lex (Fin dt.dd0 → A), ¬u < z := fun u hu =>
      absurd (hz u) (not_le_of_gt hu)
    refine ⟨⟨fun _ u hu => absurd hu (hnou u), fun _ =>
        ctlBit_cmpAccC_cmpInit hzo _⟩,
      ⟨fun hc => absurd hc (ctlBit_cmpDecC_cmpInit hzo _), ?_⟩,
      ⟨fun hc => absurd hc (ctlBit_cmpValC_cmpInit hzo _), ?_⟩⟩
    · rintro ⟨u, hu, -⟩
      exact absurd hu (hnou u)
    · rintro ⟨u, hu, -⟩
      exact absurd hu (hnou u)
  | hstep w z hwz hnb ih =>
    have hz2 : dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ z 0 =
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).advEl
          (chainSt
            (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ w j'))
            (fun j' bb q' =>
              (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
                (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
            (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0) 2)
          (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr) :=
      iterOrd_covers hwz hnb
    rw [hz2]
    obtain ⟨ihA, ihD, ihV⟩ := ih
    -- the cover's order facts
    have hltz : ∀ u : Lex (Fin dt.dd0 → A), u < z ↔ u ≤ w := fun u =>
      ⟨fun h => le_of_not_gt fun hgt => hnb u ⟨hgt, h⟩,
        fun h => lt_of_le_of_lt h hwz⟩
    -- the flags through the chain
    have hchA : dt.ctlBit one (chainSt
        (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ w j'))
        (fun j' bb q' =>
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
            (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0) 2)
        dt.cmpAccC ↔
        dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0)
          dt.cmpAccC := by
      rw [ctlBit, ctlBit, cmp_chain_apply_ne hnf
        (fun k => (cmpRdC_ne_cmpAccC hnf k).symm) 2]
    have hchD : dt.ctlBit one (chainSt
        (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ w j'))
        (fun j' bb q' =>
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
            (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0) 2)
        dt.cmpDecC ↔
        dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0)
          dt.cmpDecC := by
      rw [ctlBit, ctlBit, cmp_chain_apply_ne hnf
        (fun k => (cmpRdC_ne_cmpDecC hnf k).symm) 2]
    have hchV : dt.ctlBit one (chainSt
        (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ w j'))
        (fun j' bb q' =>
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
            (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0) 2)
        dt.cmpValC ↔
        dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0)
          dt.cmpValC := by
      rw [ctlBit, ctlBit, cmp_chain_apply_ne hnf
        (fun k => (cmpRdC_ne_cmpValC hnf k).symm) 2]
    -- the round's two bits
    have hrd0 := ctlBit_cmp_chain_rd (vi := vi) (av := av) (isEq := isEq)
      (j₁ := j₁) (j₂ := j₂) hnf hzo
      (bit := fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ w j'))
      (base := dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0)
      (g := dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr) 0
    have hrd1 := ctlBit_cmp_chain_rd (vi := vi) (av := av) (isEq := isEq)
      (j₁ := j₁) (j₂ := j₂) hnf hzo
      (bit := fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ w j'))
      (base := dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ w 0)
      (g := dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr) 1
    -- the flags off the loop variables
    have hqA : ∀ j : Fin dt.dd0, dt.cmpAccC ≠ dt.lvC j :=
      fun j => (lvC_ne_cmpAccC j).symm
    have hqD : ∀ j : Fin dt.dd0, dt.cmpDecC ≠ dt.lvC j :=
      fun j => (lvC_ne_cmpDecC j).symm
    have hqV : ∀ j : Fin dt.dd0, dt.cmpValC ≠ dt.lvC j :=
      fun j => (lvC_ne_cmpValC j).symm
    refine ⟨?_, ?_, ?_⟩
    · rw [ctlBit_cmp_advEl hnf hqA, ctlBit_cmpAccC_cmpFold hzo hnf,
        hchA, hrd0, hrd1, ihA]
      constructor
      · rintro ⟨hall, hAgr⟩ u hu
        rcases lt_or_eq_of_le ((hltz u).mp hu) with h | h
        · exact hall u h
        · rw [h]
          exact hAgr
      · intro hall
        exact ⟨fun u hu => hall u ((hltz u).mpr hu.le),
          hall w ((hltz w).mpr le_rfl)⟩
    · rw [ctlBit_cmp_advEl hnf hqD, ctlBit_cmpDecC_cmpFold hzo hnf,
        hchD, hrd0, hrd1, ihD]
      constructor
      · rintro (⟨u, hu, hnA⟩ | hnA)
        · exact ⟨u, lt_trans hu hwz, hnA⟩
        · exact ⟨w, hwz, hnA⟩
      · rintro ⟨u, hu, hnA⟩
        rcases lt_or_eq_of_le ((hltz u).mp hu) with h | h
        · exact Or.inl ⟨u, h, hnA⟩
        · rw [h] at hnA
          exact Or.inr hnA
    · rw [ctlBit_cmp_advEl hnf hqV, ctlBit_cmpValC_cmpFold hzo hnf,
        hchD, hchV, hrd0, hrd1, ihD, ihV]
      constructor
      · rintro (⟨-, u, hu, hF⟩ | ⟨hnd, hb0, hb1⟩)
        · exact ⟨u, lt_trans hu hwz, hF⟩
        · refine ⟨w, hwz, ⟨hb0, hb1⟩, fun u hu => ?_⟩
          by_contra hc
          exact hnd ⟨u, hu, hc⟩
      · rintro ⟨u, hu, ⟨hb0, hb1⟩, hall⟩
        rcases lt_or_eq_of_le ((hltz u).mp hu) with h | h
        · refine Or.inl ⟨⟨u, h, fun hIff => hb0 (hIff.mpr hb1)⟩,
            u, h, ⟨hb0, hb1⟩, hall⟩
        · subst h
          refine Or.inr ⟨?_, hb0, hb1⟩
          rintro ⟨u', hu', hnA⟩
          exact hnA (hall u' hu')

end CmpFam

/-! ### The greatest tuple -/

section TopTup

variable {D : ℕ} {B : Type} [LinearOrder B] [Finite B] [Nonempty B]

/-- **The last tuple**: every coordinate the greatest element. -/
noncomputable def topTup : Fin D → B :=
  letI := Fintype.ofFinite B
  fun _ => Finset.univ.max' Finset.univ_nonempty

/-- Every element is below the last tuple's coordinates. -/
theorem le_topTup (p : Fin D) (a : B) : a ≤ (topTup : Fin D → B) p :=
  letI := Fintype.ofFinite B
  Finset.le_max' _ a (Finset.mem_univ a)

/-- The last tuple is exhausted. -/
theorem isMaxTup_topTup : IsMaxTup (topTup : Fin D → B) :=
  fun p a => le_topTup p a

end TopTup

/-! ### The comparison's machine run -/

section CmpRun

variable [Nonempty A]
variable (hhasP : RF.toLayout.HasName PR.zero)
variable (hsepP : RF.toLayout.NameSep PR.zero dt.dd0Le)
variable (vi : dt.VarIx) (av : Fin dt.natMax) (hnf : 2 ≤ dt.nfDim)
variable (isEq : Bool) (j₁ j₂ : Fin (dt.nOf vi))
variable {emb : ElemPh 2 → P} {exitPh : P}
variable {rEmb : ∀ i : ElemSite 2, ElemSh 2 i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : ElemSite 2) (ρ : ElemSh 2 i),
  PR.rules (rEmb i ρ) = elemRule PR.one Slot.wk Slot.reg emb
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).rdTrack
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).MatchOf
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).setFlag
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).initEl
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).advEl
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).exitSt
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).IsMaxEl exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable (hix : IsLinOrd RF.le)
variable {gbot : I} (hbot : ∀ y, RF.le gbot y)
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeSt dt A R P I}
variable (hwkSt : st.wk = fun r => r = v)

include hrules hR hlin hix hbot hv hvi hwkSt hhasP hsepP in
/-- **The comparison atom's machine run, on a clock**: from the loop's entry
checkpoint at the marker to the exit phase one cell to its right, the control
carrying the whole enumeration's fold, two read trips paid per tuple. -/
theorem cmp_reachesIn (f₀ : dt.CtlIx → A) (w : ℕ)
    (hcost : ∀ (b : Lex (Fin dt.dd0 → A)) (k : Fin 2),
      2 * (wideRank (RF.cell (dt.cmpCell RF PR.zero hhasP vi j₁ j₂ b k)) -
        wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((2 + (w + 2) * 2) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1)
      ⟨Sum.inr (PR.stElt (emb .e0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.mir
          (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).exitSt
            (dt.cmpFam RF PR.zero PR.one hhasP vi av hnf isEq j₁ j₂ st v f₀
              (toLex topTup) (Fin.last 2))
            (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.mir
          (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) st.mir)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hwkS : ∀ r, dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  refine elem_reachesIn_iter RF.toIxFile hrules hR hlin hix hbot hv hvi hwkS (fun _ => rfl)
    (fun k r => dt.back_cmpSet RF hnf k r)
    (fun k => dt.wk_ne_cmp_rdTrack hnf k)
    (fun k => dt.reg_ne_cmp_rdTrack hnf k)
    (t₀ := Slot.mir) (m₀ := st.mir) (fun _ => rfl)
    (fun h => nomatch h) (fun h => nomatch h)
    (a₀ := toLex botTup) (aT := toLex topTup)
    (tup_isBot_iff.mpr botTup_le)
    (tup_isTop_iff.mpr fun p a => le_topTup p a)
    (dt.cmpCell RF PR.zero hhasP vi j₁ j₂) f₀ ?_ ?_ ?_ ?_ w hcost
  · -- the name guards, at the generated states
    intro b k
    rw [passTracks_of_back RF.toIxFile (fun r => dt.back_cmpSet RF hnf k r) _]
    have hrd : (fun j => elemFam
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).setFlag
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).initEl
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).advEl
        (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) v (dt.cmpSet vi j₁ j₂ st)
        (dt.cmpCell RF PR.zero hhasP vi j₁ j₂) f₀ b k.castSucc (dt.lvC j)) =
        ofLex b :=
      readLv_cmpFam RF hnf f₀ b k.castSucc
    refine (dt.ixNameG_iff hzo (RF.toIxFile.injective hix) hsepP hhasP _ dt.lvC _
      (dt.cmpCell RF PR.zero hhasP vi j₁ j₂ b k)).mpr ?_
    rw [cmpCell, hrd]
  · -- the guard identifies the cell
    intro b k r hM
    rw [passTracks_of_back RF.toIxFile (fun r' => dt.back_cmpSet RF hnf k r') _] at hM
    by_cases hreg : ∃ u : I, r = RF.cell u
    · obtain ⟨u, rfl⟩ := hreg
      have hu := (dt.ixNameG_iff hzo (RF.toIxFile.injective hix) hsepP hhasP _ dt.lvC _ u).mp hM
      have hrd : (fun j => elemFam
          (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).setFlag
          (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).initEl
          (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).advEl
          (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) v (dt.cmpSet vi j₁ j₂ st)
          (dt.cmpCell RF PR.zero hhasP vi j₁ j₂) f₀ b k.castSucc (dt.lvC j)) =
          ofLex b :=
        readLv_cmpFam RF hnf f₀ b k.castSucc
      rw [hrd] at hu
      rw [hu]
      rfl
    · exact absurd hM (dt.ixNot_nameG_of_not_reg (lay := RF.toLayout) (stI := st) hzo
        (fun u hc => hreg ⟨u, hc⟩))
  · -- exhausted at the top
    change dt.IsMaxLvN (elemFam _ _ _ _ _ _ _ f₀ (toLex topTup) (Fin.last 2))
    have hrd : dt.readLv (elemFam
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).setFlag
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).initEl
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).advEl
        (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) v (dt.cmpSet vi j₁ j₂ st)
        (dt.cmpCell RF PR.zero hhasP vi j₁ j₂) f₀ (toLex topTup) (Fin.last 2)) =
        ofLex (toLex topTup) :=
      readLv_cmpFam RF hnf f₀ (toLex topTup) (Fin.last 2)
    change IsMaxTup (dt.readLv (elemFam
      (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).setFlag
      (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).initEl
      (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).advEl
      (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) v (dt.cmpSet vi j₁ j₂ st)
      (dt.cmpCell RF PR.zero hhasP vi j₁ j₂) f₀ (toLex topTup) (Fin.last 2)))
    rw [hrd]
    exact isMaxTup_topTup
  · -- not exhausted below the top
    intro b hb hc
    have hrd : dt.readLv (elemFam
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).setFlag
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).initEl
        (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).advEl
        (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) v (dt.cmpSet vi j₁ j₂ st)
        (dt.cmpCell RF PR.zero hhasP vi j₁ j₂) f₀ b (Fin.last 2)) = ofLex b :=
      readLv_cmpFam RF hnf f₀ b (Fin.last 2)
    have hmax : IsMaxTup (ofLex b) := by
      have hc2 : IsMaxTup (dt.readLv (elemFam
          (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).setFlag
          (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).initEl
          (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).advEl
          (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) v (dt.cmpSet vi j₁ j₂ st)
          (dt.cmpCell RF PR.zero hhasP vi j₁ j₂) f₀ b (Fin.last 2))) := hc
      rw [hrd] at hc2
      exact hc2
    exact absurd (tup_isTop_iff.mpr hmax (toLex topTup)) (not_le_of_gt hb)

include hrules hR hlin hix hbot hv hvi hwkSt hhasP hsepP in
/-- **The comparison atom's machine run**, the budget forgotten. -/
theorem cmp_run (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .e0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.mir
          (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).exitSt
            (dt.cmpFam RF PR.zero PR.one hhasP vi av hnf isEq j₁ j₂ st v f₀
              (toLex topTup) (Fin.last 2))
            (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.mir
          (dt.ixBack RF.toLayout PR.zero PR.one dt.dd0Le st) st.mir)
          (PR.syElt PR.blank)⟩ :=
  (dt.cmp_reachesIn RF hhasP hsepP vi av hnf isEq j₁ j₂ hrules hR hlin hix hbot hv
    hvi hwkSt f₀
    (2 * Nat.card {q : WPoint (Univ A R P dt.KIx dt.dd) //
      (wideData (Univ A R P dt.KIx dt.dd)).Posn q} + 2)
    (fun b k => by
      have := wideRank_lt_card (A := Univ A R P dt.KIx dt.dd)
        (RF.cell (dt.cmpCell RF PR.zero hhasP vi j₁ j₂ b k))
      omega)).reflTransGen

end CmpRun

/-! ### The verdict, characterized -/

section CmpVerdict

variable [Nonempty A]
variable {vi : dt.VarIx} {av : Fin dt.natMax} (hnf : 2 ≤ dt.nfDim)
variable {isEq : Bool} {j₁ j₂ : Fin (dt.nOf vi)}
variable {st : TapeSt dt A R P I}
variable {vAdr : Univ A R P dt.KIx dt.dd → Prop}
variable {zero one : A}
variable {hhas : RF.toLayout.HasName zero}

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The verdict the exit control carries**: agreement everywhere for an
equality atom; agreement everywhere or a first difference the second
block's, for an order atom. This is exactly the shape
`DescriptiveComplexity.Draw.encMap_eq_iff_padBits` and
`DescriptiveComplexity.Draw.encOrder_le_iff_padBits` decide against the two
registers' contents. -/
theorem ctlBit_avC_cmp_exit (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (g : dt.SlotIx → A) :
    dt.ctlBit one
      ((dt.cmpArgs zero one vi av hnf isEq j₁ j₂).exitSt
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀
          (toLex topTup) (Fin.last 2)) g) (dt.avC av) ↔
      (if isEq = true then ∀ u, dt.CmpAgr RF zero hhas vi j₁ j₂ st u
        else ((∀ u, dt.CmpAgr RF zero hhas vi j₁ j₂ st u) ∨
          ∃ u, dt.CmpFst RF zero hhas vi j₁ j₂ st u)) := by
  classical
  set aT : Lex (Fin dt.dd0 → A) := toLex topTup with haT
  -- the exit's stored verdict
  have hself : dt.ctlBit one
      ((dt.cmpArgs zero one vi av hnf isEq j₁ j₂).exitSt
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT
          (Fin.last 2)) g) (dt.avC av) ↔
      dt.cmpVerdict one isEq (dt.cmpFold zero one hnf
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT
          (Fin.last 2))) := by
    change dt.ctlBit one (dt.setCtl zero one (dt.avC av)
      (dt.cmpVerdict one isEq (dt.cmpFold zero one hnf
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT
          (Fin.last 2))))
      (dt.cmpFold zero one hnf
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT
          (Fin.last 2)))) (dt.avC av) ↔ _
    exact ctlBit_setCtl_self hzo _ _ _
  rw [hself]
  -- the last round's family is the chain over its entry
  have hlast : dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT
      (Fin.last 2) =
      chainSt
        (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ aT j'))
        (fun j' bb q' =>
          (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
            (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
        (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0) 2 := rfl
  -- the flags and reads feeding the final fold
  obtain ⟨ihA, ihD, ihV⟩ := cmpFlags_cmpFam (vi := vi) (av := av)
    (isEq := isEq) (j₁ := j₁) (j₂ := j₂) (st := st) (vAdr := vAdr)
    RF hnf hzo f₀ aT
  have hchA : dt.ctlBit one (chainSt
      (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ aT j'))
      (fun j' bb q' =>
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
          (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
      (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0) 2)
      dt.cmpAccC ↔
      dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0)
        dt.cmpAccC := by
    rw [ctlBit, ctlBit, cmp_chain_apply_ne hnf
      (fun k => (cmpRdC_ne_cmpAccC hnf k).symm) 2]
  have hchD : dt.ctlBit one (chainSt
      (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ aT j'))
      (fun j' bb q' =>
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
          (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
      (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0) 2)
      dt.cmpDecC ↔
      dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0)
        dt.cmpDecC := by
    rw [ctlBit, ctlBit, cmp_chain_apply_ne hnf
      (fun k => (cmpRdC_ne_cmpDecC hnf k).symm) 2]
  have hchV : dt.ctlBit one (chainSt
      (fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ aT j'))
      (fun j' bb q' =>
        (dt.cmpArgs zero one vi av hnf isEq j₁ j₂).setFlag j' bb q'
          (dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr))
      (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0) 2)
      dt.cmpValC ↔
      dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0)
        dt.cmpValC := by
    rw [ctlBit, ctlBit, cmp_chain_apply_ne hnf
      (fun k => (cmpRdC_ne_cmpValC hnf k).symm) 2]
  have hrd0 := ctlBit_cmp_chain_rd (vi := vi) (av := av) (isEq := isEq)
    (j₁ := j₁) (j₂ := j₂) hnf hzo
    (bit := fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ aT j'))
    (base := dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0)
    (g := dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr) 0
  have hrd1 := ctlBit_cmp_chain_rd (vi := vi) (av := av) (isEq := isEq)
    (j₁ := j₁) (j₂ := j₂) hnf hzo
    (bit := fun j' => dt.cmpSet vi j₁ j₂ st j' (dt.cmpCell RF zero hhas vi j₁ j₂ aT j'))
    (base := dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0)
    (g := dt.ixBack RF.toLayout zero one dt.dd0Le st vAdr) 1
  -- every tuple is at or below the top
  have hleT : ∀ u : Lex (Fin dt.dd0 → A), u ≤ aT :=
    tup_isTop_iff.mpr fun p a => le_topTup p a
  have hcase : ∀ u : Lex (Fin dt.dd0 → A), u < aT ∨ u = aT := fun u =>
    lt_or_eq_of_le (hleT u)
  -- the folded flags, against the whole enumeration
  have hAccAll : (dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st
        vAdr f₀ aT 0) dt.cmpAccC ∧
      dt.CmpAgr RF zero hhas vi j₁ j₂ st aT) ↔
      ∀ u, dt.CmpAgr RF zero hhas vi j₁ j₂ st u := by
    rw [ihA]
    constructor
    · rintro ⟨hall, hAgr⟩ u
      rcases hcase u with h | h
      · exact hall u h
      · rw [h]
        exact hAgr
    · intro hall
      exact ⟨fun u _ => hall u, hall aT⟩
  have hValAll : ((dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st
          vAdr f₀ aT 0) dt.cmpDecC ∧
        dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0)
          dt.cmpValC) ∨
      (¬dt.ctlBit one (dt.cmpFam RF zero one hhas vi av hnf isEq j₁ j₂ st vAdr f₀ aT 0)
          dt.cmpDecC ∧
        ¬dt.cmpSet vi j₁ j₂ st 0 (dt.cmpCell RF zero hhas vi j₁ j₂ aT 0) ∧
        dt.cmpSet vi j₁ j₂ st 1 (dt.cmpCell RF zero hhas vi j₁ j₂ aT 1))) ↔
      ∃ u, dt.CmpFst RF zero hhas vi j₁ j₂ st u := by
    rw [ihD, ihV]
    constructor
    · rintro (⟨-, u, -, hF⟩ | ⟨hnd, hb0, hb1⟩)
      · exact ⟨u, hF⟩
      · refine ⟨aT, ⟨hb0, hb1⟩, fun u hu => ?_⟩
        by_contra hc
        exact hnd ⟨u, hu, hc⟩
    · rintro ⟨u, ⟨hb0, hb1⟩, hall⟩
      rcases hcase u with h | h
      · refine Or.inl ⟨⟨u, h, fun hIff => hb0 (hIff.mpr hb1)⟩,
          u, h, ⟨hb0, hb1⟩, hall⟩
      · subst h
        refine Or.inr ⟨?_, hb0, hb1⟩
        rintro ⟨u', hu', hnA⟩
        exact hnA (hall u' hu')
  -- assemble, per polarity
  rw [cmpVerdict]
  by_cases hEq : isEq = true
  · rw [if_pos hEq, if_pos hEq, hlast, ctlBit_cmpAccC_cmpFold hzo hnf,
      hchA, hrd0, hrd1]
    exact hAccAll
  · rw [if_neg hEq, if_neg hEq, hlast, ctlBit_cmpAccC_cmpFold hzo hnf,
      ctlBit_cmpValC_cmpFold hzo hnf, hchA, hchD, hchV, hrd0, hrd1]
    exact or_congr hAccAll hValAll

end CmpVerdict

end Data

end Draw

end DescriptiveComplexity
