/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpDefTags
import DescriptiveComplexity.Problems.Wide.PfpName

/-!
# The names a trip walks to are definable

Every trip of the program is aimed by a **naming guard**: this cell is the
canonically padded cell of the element whose block is `b` and whose first `dd₀`
coordinates spell a given tuple. The coordinate loops spell it from the control
directly (`DescriptiveComplexity.Pfp.PfpData.nameG`); the leaf reads of the
element loops spell an *encoded* tuple
(`DescriptiveComplexity.Pfp.PfpData.encCoord`), and this file says that is a
naming guard the interpretation can write down too.

The reason is the layout, not the data: at each coordinate an encoded tuple
holds a component of the one-hot code – one of the two designated elements – or
a payload position, or the clear element, and *which* it holds is decided by
`DescriptiveComplexity.EncLayout` when the formula is built. So an encoded
coordinate is `DescriptiveComplexity.Pfp.UReadable` as soon as the payload is,
and every payload the program spells is a control slot or the clear element.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational] {dt : PfpData L} {Q : Type}
variable [Fintype Q] [Fintype dt.SlotIx]

/-! ### An encoded coordinate -/

omit [L.IsRelational] in
/-- **A coordinate of an encoded tuple is readable**: the code coordinates hold
a designated element, the payload coordinates the payload, the rest the clear
element – three cases the layout decides, not the data. -/
theorem uReadable_encTup {c : PtCode dt.X}
    {pay : ∀ e : Env L, (Q → e.α) → Fin (blockArityBound dt.X.B) → e.α}
    (hpay : ∀ p : Fin (blockArityBound dt.X.B),
      UReadable fun e f (_ : dt.SlotIx → e.α) => pay e f p) (k : Fin dt.dd) :
    UReadable (L := L) (Q := Q) (W := dt.SlotIx) fun e f _ =>
      encTup dt.ly e.zero e.one c (pay e f) k := by
  classical
  by_cases hc : ∃ q : PtCode dt.X, dt.ly.cIx q = k
  · obtain ⟨q, rfl⟩ := hc
    by_cases hq : q = c
    · exact (uReadable_one (L := L) (Q := Q) (W := dt.SlotIx)).congr fun _ _ _ => by
        rw [encTup_cIx, if_pos hq]
    · exact (uReadable_zero (L := L) (Q := Q) (W := dt.SlotIx)).congr fun _ _ _ => by
        rw [encTup_cIx, if_neg hq]
  · by_cases hp : ∃ p : Fin (blockArityBound dt.X.B), dt.ly.pIx p = k
    · obtain ⟨p, rfl⟩ := hp
      exact (hpay p).congr fun _ _ _ => by rw [encTup_pIx]
    · push Not at hc hp
      exact (uReadable_zero (L := L) (Q := Q) (W := dt.SlotIx)).congr fun _ _ _ => by
        rw [encTup_of_ne _ _ hc hp]

omit [L.IsRelational] in
/-- **A name coordinate the control computes is readable.** -/
theorem uReadable_encCoord (c : PtCode dt.X)
    {pay : ∀ e : Env L, (Q → e.α) → Fin (blockArityBound dt.X.B) → e.α}
    (hpay : ∀ p : Fin (blockArityBound dt.X.B),
      UReadable fun e f (_ : dt.SlotIx → e.α) => pay e f p) (j : Fin dt.dd0) :
    UReadable (L := L) (Q := Q) (W := dt.SlotIx) fun e f _ =>
      dt.encCoord e.zero e.one c (pay e) f j :=
  uReadable_encTup hpay (Fin.castLE dt.dd0Le j)

/-! ### The naming guard, from readable coordinates -/

omit [L.IsRelational] in
/-- **A naming guard whose coordinates are readable is definable.** This is
`DescriptiveComplexity.Pfp.PfpData.uGDefinable_nameGF` with its hypothesis in
the form the encoded names supply it. -/
theorem uGDefinable_nameGF_of_readable {b : Fin dt.ko ⊕ Fin dt.ki}
    {cf : ∀ e : Env L, (Q → e.α) → Fin dt.dd0 → e.α}
    (hcf : ∀ j : Fin dt.dd0,
      UReadable fun e f (_ : dt.SlotIx → e.α) => cf e f j) :
    UGDefinable (L := L) fun e (f : Q → e.α) g => dt.nameGF e.one b (cf e) f g :=
  uGDefinable_nameGF fun j => hcf j (Slot.name j)

omit [L.IsRelational] in
/-- **A witness read's name is definable**: the tag's encoded tuple, whose
payload is the clear element throughout. -/
theorem uGDefinable_tagWitnessMatch (b : Fin dt.ko ⊕ Fin dt.ki) (t : dt.X.Tag) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f g =>
      dt.tagWitnessMatch e.zero e.one b t f g :=
  uGDefinable_nameGF_of_readable fun j =>
    uReadable_encCoord (Sum.inl t) (fun _ => uReadable_zero) j

/-! ### The payload a read leaf spells -/

omit [L.IsRelational] in
/-- **A padded payload of control slots is readable**, position by position:
below the arity a slot of the control, beyond it the clear element – and which
is which the arity decides. -/
theorem uReadable_pad_ctl {c : ℕ} {q : Fin c → dt.CtlIx}
    (p : Fin (blockArityBound dt.X.B)) :
    UReadable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f _ =>
      pad (dd := blockArityBound dt.X.B) e.zero (fun i => f (q i)) p := by
  by_cases hp : (p : ℕ) < c
  · exact (uReadable_ctl (L := L) (W := dt.SlotIx) (q ⟨(p : ℕ), hp⟩)).congr
      fun _ _ _ => pad_of_lt p hp
  · exact (uReadable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
      fun _ _ _ => pad_of_ge p (Nat.not_lt.mp hp)

/-- **A domain read leaf's name is definable**: its payload is the loop
element at the levels the leaf's atom reads, padded. -/
theorem uGDefinable_domMatch (b : Fin dt.ko ⊕ Fin dt.ki) (t : dt.X.Tag)
    (r : Fin (dt.domNr t)) (hn : (dt.domPk t).n ≤ dt.eDim) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f g =>
      dt.domMatch e.zero e.one b t r hn f g :=
  uGDefinable_nameGF_of_readable fun j =>
    uReadable_encCoord (Sum.inr (domLeafData t r).1)
      (fun p => uReadable_pad_ctl
        (q := fun i => dt.lvE (Fin.castLE hn ((domLeafData t r).2 i))) p) j

/-! ### The well-shapedness questions

The gates' file test asks of a cell that its name slots spell an encoded tuple:
the witness of some tag, or a member of some relation variable. The first is a
disjunction over a finite type of tags; the second quantifies a **tuple of the
instance**, which no combinator covers – so the existential has to go, and the
layout is what removes it. At a coordinate the encoding does not read from the
payload the value is pinned; at one it does, the tuple is free, and a witness
can be read straight off the cell. -/

section WellShaped

variable (dt)

/-- **A name coordinate the payload reaches**: the encoded tuple is free
there, so a well-shapedness test must not ask anything of it. -/
def PayCoord (i : dt.X.B.ι) (j : Fin dt.dd0) : Prop :=
  ∃ p : Fin (blockArityBound dt.X.B),
    (p : ℕ) < dt.X.B.arity i ∧ dt.ly.pIx p = Fin.castLE dt.dd0Le j

variable {dt}

omit [L.IsRelational] [Fintype Q] [Fintype dt.SlotIx] in
/-- **Away from the payload the encoded tuple does not depend on it.** -/
theorem encAsgTup_congr_of_not_payCoord {A : Type} {zero one : A}
    {i : dt.X.B.ι} {j : Fin dt.dd0} (h : ¬dt.PayCoord i j)
    (w w' : Fin (dt.X.B.arity i) → A) :
    encAsgTup dt.ly zero one i w (Fin.castLE dt.dd0Le j) =
      encAsgTup dt.ly zero one i w' (Fin.castLE dt.dd0Le j) := by
  classical
  by_cases hc : ∃ q : PtCode dt.X, dt.ly.cIx q = Fin.castLE dt.dd0Le j
  · obtain ⟨q, hq⟩ := hc
    rw [encAsgTup, encAsgTup, ← hq, encTup_cIx, encTup_cIx]
  · by_cases hp : ∃ p : Fin (blockArityBound dt.X.B),
        dt.ly.pIx p = Fin.castLE dt.dd0Le j
    · obtain ⟨p, hp⟩ := hp
      have hge : ¬((p : ℕ) < dt.X.B.arity i) := fun hlt => h ⟨p, hlt, hp⟩
      rw [encAsgTup, encAsgTup, ← hp, encTup_pIx, encTup_pIx,
        pad_of_ge p (Nat.not_lt.mp hge), pad_of_ge p (Nat.not_lt.mp hge)]
    · push Not at hc hp
      rw [encAsgTup, encAsgTup, encTup_of_ne _ _ hc hp, encTup_of_ne _ _ hc hp]

omit [L.IsRelational] in
open Classical in
/-- **A member of a relation variable is a definable question of the cell**:
the payload coordinates carry no condition – a witness is read off the cell
there – and every other coordinate is pinned by the code and the padding. -/
theorem uGDefinable_exists_encAsgTup (i : dt.X.B.ι) :
    UGDefinable (L := L) (Q := Q) (W := dt.SlotIx) fun e _ g =>
      ∃ w : Fin (dt.X.B.arity i) → e.α, ∀ j : Fin dt.dd0,
        g (Slot.name j) = encAsgTup dt.ly e.zero e.one i w (Fin.castLE dt.dd0Le j) := by
  refine (uGDefinable_forall fun j : Fin dt.dd0 =>
    UGDefinable.ite (p := dt.PayCoord i j) uGDefinable_true
      (uReadable_encTup (Q := Q) (c := Sum.inr i)
        (pay := fun e _ (p : Fin (blockArityBound dt.X.B)) =>
          pad (dd := blockArityBound dt.X.B) e.zero
            (fun _ : Fin (dt.X.B.arity i) => e.zero) p)
        (fun p => (uReadable_zero (L := L) (Q := Q) (W := dt.SlotIx)).congr
          fun e _ _ => by
            by_cases hp : (p : ℕ) < dt.X.B.arity i
            · exact pad_of_lt p hp
            · exact pad_of_ge p (Nat.not_lt.mp hp))
        (Fin.castLE dt.dd0Le j) (Slot.name j))).congr fun e f g => ?_
  constructor
  · rintro ⟨w, hw⟩ j
    by_cases hj : dt.PayCoord i j
    · rw [if_pos hj]
      trivial
    · rw [if_neg hj, hw j]
      exact encAsgTup_congr_of_not_payCoord hj w fun _ => e.zero
  · intro hall
    refine ⟨fun p' : Fin (dt.X.B.arity i) =>
      if h : ∃ j : Fin dt.dd0,
          dt.ly.pIx (Fin.castLE (arity_le_blockArityBound dt.X.B i) p') =
            Fin.castLE dt.dd0Le j then g (Slot.name h.choose) else e.zero,
      fun j => ?_⟩
    by_cases hj : dt.PayCoord i j
    · obtain ⟨p, hlt, hpj⟩ := hj
      have hex : ∃ j' : Fin dt.dd0, dt.ly.pIx p = Fin.castLE dt.dd0Le j' := ⟨j, hpj⟩
      have hjj : hex.choose = j :=
        Fin.castLE_injective dt.dd0Le (hex.choose_spec.symm.trans hpj)
      rw [encAsgTup, ← hpj, encTup_pIx, pad_of_lt p hlt]
      change g (Slot.name j) =
        (if h : ∃ j' : Fin dt.dd0, dt.ly.pIx p = Fin.castLE dt.dd0Le j'
          then g (Slot.name h.choose) else e.zero)
      rw [dif_pos hex, hjj]
    · rw [encAsgTup_congr_of_not_payCoord hj _ fun _ => e.zero]
      have h1 := hall j
      rw [if_neg hj] at h1
      exact h1

omit [L.IsRelational] in
/-- **The tag witness is a definable question of the cell.** -/
theorem uGDefinable_eq_encTagTup (t : dt.X.Tag) (j : Fin dt.dd0) :
    UGDefinable (L := L) (Q := Q) (W := dt.SlotIx) fun e _ g =>
      g (Slot.name j) = encTagTup dt.ly e.zero e.one t (Fin.castLE dt.dd0Le j) :=
  uReadable_encTup (Q := Q) (c := Sum.inl t)
    (pay := fun e _ (_ : Fin (blockArityBound dt.X.B)) => e.zero)
    (fun _ => uReadable_zero) (Fin.castLE dt.dd0Le j) (Slot.name j)

omit [L.IsRelational] in
/-- **A gate's well-shapedness question is definable.** -/
theorem uGDefinable_wellShapedG (b : Fin dt.ko ⊕ Fin dt.ki) :
    UGDefinable (L := L) (Q := Q) (W := dt.SlotIx) fun e _ g =>
      dt.wellShapedG e.zero e.one b g :=
  ((uGDefinable_trkOne (L := L) (Q := Q) (Slot.blk (some b) : dt.SlotIx)).imp
    ((uGDefinable_trkOne (L := L) (Q := Q) (Slot.mir : dt.SlotIx)).imp
      ((uGDefinable_trkOne (L := L) (Q := Q) (Slot.pdd : dt.SlotIx)).and
        ((uGDefinable_exists fun t : dt.X.Tag =>
            uGDefinable_forall fun j : Fin dt.dd0 => uGDefinable_eq_encTagTup t j).or
          (uGDefinable_exists fun i : dt.X.B.ι =>
            uGDefinable_exists_encAsgTup i))))).congr fun _ _ _ => Iff.rfl

omit [L.IsRelational] in
/-- **And so is an inner gate's**, the digit read off the VAL register. -/
theorem uGDefinable_wellShapedIG (b : Fin dt.ko ⊕ Fin dt.ki) :
    UGDefinable (L := L) (Q := Q) (W := dt.SlotIx) fun e _ g =>
      dt.wellShapedIG e.zero e.one b g :=
  ((uGDefinable_trkOne (L := L) (Q := Q) (Slot.blk (some b) : dt.SlotIx)).imp
    ((uGDefinable_trkOne (L := L) (Q := Q) (Slot.val : dt.SlotIx)).imp
      ((uGDefinable_trkOne (L := L) (Q := Q) (Slot.pdd : dt.SlotIx)).and
        ((uGDefinable_exists fun t : dt.X.Tag =>
            uGDefinable_forall fun j : Fin dt.dd0 => uGDefinable_eq_encTagTup t j).or
          (uGDefinable_exists fun i : dt.X.B.ι =>
            uGDefinable_exists_encAsgTup i))))).congr fun _ _ _ => Iff.rfl

end WellShaped

/-! ### The leaf of a domain sentence -/

open Classical in
/-- **The value of a domain sentence's matrix from the control is definable**:
its block atoms are read flags, and its other atoms are the questions a guard
may ask of the instance – an equality, an order comparison, a relation of the
source vocabulary – at the loop element. -/
theorem uGDefinable_domLeafVal (t : dt.X.Tag) (hn : (dt.domPk t).n ≤ dt.eDim)
    (hrd : dt.domNr t ≤ dt.nfDim) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f _ =>
      dt.domLeafVal e.one t hn hrd f := by
  refine uGDefinable_qfValue (dt.domPk t).mat _ fun a => ?_
  refine UGDefinable.ite (p := isBlkAtom a = true) ?_ ?_
  · exact uGDefinable_exists fun r : Fin (dt.domNr t) =>
      (uGDefinable_const ((blkAtoms (dt.domPk t).mat).get r = a)).and
        (uGDefinable_ctlBit (dt.rdfC (Fin.castLE hrd r)))
  · match hb : blkAtom? a with
    | none =>
      exact (uGDefinable_false (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
        fun _ _ _ => Iff.rfl
    | some κ =>
      exact (uGDefinable_blkAtomHolds (fun j => dt.lvE (Fin.castLE hn j)) κ).congr
        fun _ _ _ => Iff.rfl

end PfpData

end Pfp

end DescriptiveComplexity
