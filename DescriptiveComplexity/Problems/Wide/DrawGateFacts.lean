/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInstRound

/-!
# The gates' facts, from the marks

What the gate machinery asks – the file tests' per-cell questions, the
witness one-hotness, the domain conditions – read off
`DescriptiveComplexity.Draw.Data.back`'s marks and answered by the
encoding. The marks of a register cell spell the cell's own coordinates
(`name`), its padding (`pdd`) and its tag's block (`blk`), so a file
test's question is a statement about the cell, and a block value's
answers are statements about the value:

* `wellShapedG_back_iff` / `igTest_iff` – the per-cell question **is**
  «if the cell is of the gated block and in the register, its tuple is a
  witness or a member shape», at MIRROR and at VAL;
* `testOf_of_encMap`, `wit_of_encMap`, `domHolds_of_encMap`,
  `dspTagOf_encMap` – at a block value that **is** an encoding, every
  gated hypothesis of `DescriptiveComplexity.Draw.Data.varMachine_run`
  holds, and the dispatch is the point's tag;
* `gate_trichotomy` – every block value is an encoding, has an
  ill-shaped register cell, or is all-shaped with the one-hot-and-domain
  conjunct failing at the dispatched tag: the three legs
  `DescriptiveComplexity.Draw.Data.varLeg_run` /
  `varLegFail_run` / `varLegUngated_run` are exhaustive;
* `igPassP_iff_isEnc` – the inner loop's per-level verdict **is**
  `DescriptiveComplexity.Draw.IsEnc` of the level's block value, the
  marks-to-shapes bridge the two-flag characterization was stated
  against.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable (RF : RegFile (Univ A R P dt.KIx dt.dd))
variable [Nonempty A] [L.IsRelational] [L.Structure A]

section GateFacts

variable (zero one : A)

/-! ### Encoded tuples against the marks -/

variable {zero one} in
omit [LinearOrder A] [Finite A] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite R] [Finite P] in
/-- **An encoded tuple is canonically padded**: the layout inhabits the
first `dd₀` coordinates, so everything above them is the designated
zero. -/
theorem encTup_pdd (d : PtCode dt.X)
    (pay : Fin (blockArityBound dt.X.B) → A) {j : Fin dt.dd}
    (hj : dt.dd0 ≤ (j : ℕ)) :
    encTup dt.ly zero one d pay j = zero := by
  refine encTup_of_ne d pay (fun q hq => ?_) (fun p hp => ?_)
  · exact absurd (dt.lyLt j (Or.inl ⟨q, hq⟩)) (by omega)
  · exact absurd (dt.lyLt j (Or.inr ⟨p, hp⟩)) (by omega)

variable {zero one} in
omit [LinearOrder A] [Finite A] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **A padded tuple whose name coordinates spell an encoded tuple is that
tuple**: the coordinates above `dd₀` agree because both sides are zero
there. -/
theorem eq_encTup_of_marks {u2 : Fin dt.dd → A} {d : PtCode dt.X}
    {pay : Fin (blockArityBound dt.X.B) → A}
    (hpdd : ∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u2 j = zero)
    (hname : ∀ j : Fin dt.dd0,
      u2 (Fin.castLE dt.dd0Le j) =
        encTup dt.ly zero one d pay (Fin.castLE dt.dd0Le j)) :
    u2 = encTup dt.ly zero one d pay := by
  funext j
  by_cases hj : (j : ℕ) < dt.dd0
  · have h := hname ⟨(j : ℕ), hj⟩
    have hcast : Fin.castLE dt.dd0Le ⟨(j : ℕ), hj⟩ = j := Fin.ext rfl
    rwa [hcast] at h
  · rw [hpdd j (Nat.le_of_not_lt hj), dt.encTup_pdd d pay (Nat.le_of_not_lt hj)]

/-! ### The per-cell questions, read -/

variable {zero one} in
omit [Nonempty A] [L.IsRelational] [L.Structure A] [Finite A] [Finite R] [Finite P] in
/-- **The shape clause of the marks is the shape of the cell's tuple**:
the padding mark together with a name-coordinate match is full equality
with the encoded tuple. -/
theorem shape_marks_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (st : TapeStD dt A R P) (u : Univ A R P dt.KIx dt.dd) :
    (dt.back RF.cell zero one dt.dd0Le st (RF.cell u) .pdd = one ∧
      ((∃ t : dt.X.Tag, ∀ j : Fin dt.dd0,
          dt.back RF.cell zero one dt.dd0Le st (RF.cell u) (.name j) =
            encTagTup dt.ly zero one t (Fin.castLE dt.dd0Le j)) ∨
        ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A),
          ∀ j : Fin dt.dd0,
            dt.back RF.cell zero one dt.dd0Le st (RF.cell u) (.name j) =
              encAsgTup dt.ly zero one i w (Fin.castLE dt.dd0Le j))) ↔
      ((∃ t : dt.X.Tag, u.2 = encTagTup dt.ly zero one t) ∨
        ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A),
          u.2 = encAsgTup dt.ly zero one i w) := by
  rw [dt.back_pdd_cell (RF.injective hlin), bitVal_iff hzo]
  constructor
  · rintro ⟨hpdd, ⟨t, hn⟩ | ⟨i, w, hn⟩⟩
    · exact Or.inl ⟨t, dt.eq_encTup_of_marks hpdd (fun j => by
        rw [← dt.back_name_cell (RF.injective hlin)]
        exact hn j)⟩
    · exact Or.inr ⟨i, w, dt.eq_encTup_of_marks hpdd (fun j => by
        rw [← dt.back_name_cell (RF.injective hlin)]
        exact hn j)⟩
  · intro hsh
    have hpdd : ∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u.2 j = zero := by
      rcases hsh with ⟨t, ht⟩ | ⟨i, w, hw⟩
      · rw [ht]
        exact fun j hj => dt.encTup_pdd _ _ hj
      · rw [hw]
        exact fun j hj => dt.encTup_pdd _ _ hj
    refine ⟨hpdd, ?_⟩
    rcases hsh with ⟨t, ht⟩ | ⟨i, w, hw⟩
    · exact Or.inl ⟨t, fun j => by
        rw [dt.back_name_cell (RF.injective hlin), ht]⟩
    · exact Or.inr ⟨i, w, fun j => by
        rw [dt.back_name_cell (RF.injective hlin), hw]⟩

variable {zero one} in
omit [Nonempty A] [L.IsRelational] [L.Structure A] [Finite A] [Finite R] [Finite P] in
/-- **The outer file test's question, read off the marks**: if the cell is
of the gated block and belongs to MIRROR, its tuple is a witness or a
member shape. -/
theorem wellShapedG_back_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (st : TapeStD dt A R P) (b' : Fin dt.ko ⊕ Fin dt.ki)
    (u : Univ A R P dt.KIx dt.dd) :
    dt.wellShapedG zero one b'
        (dt.back RF.cell zero one dt.dd0Le st (RF.cell u)) ↔
      (u.1 = (Tag.arg (toLex b') : Tag R P dt.KIx) → st.mir u →
        ((∃ t : dt.X.Tag, u.2 = encTagTup dt.ly zero one t) ∨
          ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A),
            u.2 = encAsgTup dt.ly zero one i w)) := by
  rw [wellShapedG]
  have hblk : dt.back RF.cell zero one dt.dd0Le st (RF.cell u) (.blk (some b')) =
      one ↔ u.1 = Tag.arg (toLex b') := by
    rw [dt.back_blk_cell (RF.injective hlin), bitVal_iff hzo, tagBlk_eq_some_iff]
  have hmir : dt.back RF.cell zero one dt.dd0Le st (RF.cell u) Slot.mir = one ↔
      st.mir u := by
    rw [show dt.back RF.cell zero one dt.dd0Le st (RF.cell u) Slot.mir =
        bitVal zero one (bitAtOf RF.cell st.mir (RF.cell u)) from rfl,
      bitVal_iff hzo]
    constructor
    · rintro ⟨u', hu', hm⟩
      rwa [RF.injective hlin hu']
    · exact fun h => ⟨u, rfl, h⟩
  rw [hblk, hmir]
  exact imp_congr Iff.rfl (imp_congr Iff.rfl
    (dt.shape_marks_iff RF hzo hlin st u))

variable {zero one} in
omit [Nonempty A] [L.IsRelational] [L.Structure A] [Finite A] [Finite R] [Finite P] in
/-- **The inner file test's question, read off the marks**: the same at the
VAL register. -/
theorem igTest_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (stV : TapeStD dt A R P) (b' : Fin dt.ko ⊕ Fin dt.ki)
    (u : Univ A R P dt.KIx dt.dd) :
    dt.igTest RF zero one stV b' u ↔
      (u.1 = (Tag.arg (toLex b') : Tag R P dt.KIx) → stV.val u →
        ((∃ t : dt.X.Tag, u.2 = encTagTup dt.ly zero one t) ∨
          ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A),
            u.2 = encAsgTup dt.ly zero one i w)) := by
  rw [igTest, wellShapedIG]
  have hblk : dt.back RF.cell zero one dt.dd0Le stV (RF.cell u) (.blk (some b')) =
      one ↔ u.1 = Tag.arg (toLex b') := by
    rw [dt.back_blk_cell (RF.injective hlin), bitVal_iff hzo, tagBlk_eq_some_iff]
  have hval : dt.back RF.cell zero one dt.dd0Le stV (RF.cell u) Slot.val = one ↔
      stV.val u := by
    rw [show dt.back RF.cell zero one dt.dd0Le stV (RF.cell u) Slot.val =
        bitVal zero one (bitAtOf RF.cell stV.val (RF.cell u)) from rfl,
      bitVal_iff hzo]
    constructor
    · rintro ⟨u', hu', hm⟩
      rwa [RF.injective hlin hu']
    · exact fun h => ⟨u, rfl, h⟩
  rw [hblk, hval]
  exact imp_congr Iff.rfl (imp_congr Iff.rfl
    (dt.shape_marks_iff RF hzo hlin stV u))

/-! ### The shape clause of a block value -/

variable {zero one} in
omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **The per-cell questions of a block answer for its value**: every cell
of block `b'` in the register is well-shaped exactly when every member of
the block value is a witness or a member shape. -/
theorem forall_shape_iff_of_cells
    {m : Univ A R P dt.KIx dt.dd → Prop} {b' : Fin dt.ko ⊕ Fin dt.ki}
    (hcell : ∀ u : Univ A R P dt.KIx dt.dd,
      (u.1 = (Tag.arg (toLex b') : Tag R P dt.KIx) → m u →
        ((∃ t : dt.X.Tag, u.2 = encTagTup dt.ly zero one t) ∨
          ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A),
            u.2 = encAsgTup dt.ly zero one i w))) :
    ∀ w : Fin dt.dd → A,
      wmBlk m (Tag.arg (toLex b') : Tag R P dt.KIx) w →
        ((∃ t : dt.X.Tag, w = encTagTup dt.ly zero one t) ∨
          ∃ (i : dt.X.B.ι) (w' : Fin (dt.X.B.arity i) → A),
            w = encAsgTup dt.ly zero one i w') :=
  fun w hw =>
    hcell ((Tag.arg (toLex b') : Tag R P dt.KIx), w) rfl hw

/-! ### The gated facts: at a block value that is an encoding -/

variable {zero one} in
omit [Nonempty A] [L.IsRelational] [Finite A] [Finite R] [Finite P] in
/-- **At an encoding every cell passes the outer file test.** -/
theorem testOf_of_encMap (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    {st : TapeStD dt A R P} {b' : Fin dt.ko ⊕ Fin dt.ki} {p : dt.X.Map A}
    (hS : wmBlk st.mir (Tag.arg (toLex b') : Tag R P dt.KIx) =
      encMap dt.ly zero one p)
    (u : Univ A R P dt.KIx dt.dd) :
    dt.wellShapedG zero one b'
      (dt.back RF.cell zero one dt.dd0Le st (RF.cell u)) := by
  rw [dt.wellShapedG_back_iff RF hzo hlin]
  intro h1 hm
  have hmem : encMap dt.ly zero one p u.2 := by
    rw [← hS]
    change st.mir (Tag.arg (toLex b'), u.2)
    rwa [← h1, Prod.mk.eta]
  rcases hmem with h | ⟨i, w, -, h⟩
  · exact Or.inl ⟨p.1.1, h⟩
  · exact Or.inr ⟨i, w, h⟩

variable {zero one} in
omit [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational] in
/-- **At an encoding the witness is one-hot at the point's tag.** -/
theorem wit_of_encMap (hzo : zero ≠ one)
    {m : Univ A R P dt.KIx dt.dd → Prop} {b' : Fin dt.ko ⊕ Fin dt.ki}
    {p : dt.X.Map A}
    (hS : wmBlk m (Tag.arg (toLex b') : Tag R P dt.KIx) =
      encMap dt.ly zero one p)
    (t' : dt.X.Tag) :
    wmBlk m (Tag.arg (toLex b') : Tag R P dt.KIx)
        (encTagTup dt.ly zero one t') ↔ t' = p.1.1 := by
  rw [hS]
  exact (mem_encPt_tag dt.ly hzo p.1 t').trans eq_comm

variable {zero one} in
omit [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] [L.IsRelational] in
/-- **At an encoding the dispatch is the point's tag.** -/
theorem dspTagOf_encMap (hzo : zero ≠ one)
    {m : Univ A R P dt.KIx dt.dd → Prop} {b' : Fin dt.ko ⊕ Fin dt.ki}
    {p : dt.X.Map A}
    (hS : wmBlk m (Tag.arg (toLex b') : Tag R P dt.KIx) =
      encMap dt.ly zero one p) :
    dt.dspTagOf zero one
      (wmBlk m (Tag.arg (toLex b') : Tag R P dt.KIx)) = p.1.1 :=
  dspTagOf_eq_of_onehot (dt.wit_of_encMap hzo hS)

variable {zero one} in
omit [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational] in
/-- **At an encoding the domain condition holds of the decoded
assignment** – the point carries it. -/
theorem domHolds_of_encMap (hzo : zero ≠ one)
    {m : Univ A R P dt.KIx dt.dd → Prop} {b' : Fin dt.ko ⊕ Fin dt.ki}
    {p : dt.X.Map A}
    (hS : wmBlk m (Tag.arg (toLex b') : Tag R P dt.KIx) =
      encMap dt.ly zero one p) :
    ExpExpansion.DomHolds (X := dt.X)
      (p.1.1, decRho dt.ly zero one
        (wmBlk m (Tag.arg (toLex b') : Tag R P dt.KIx))) := by
  rw [hS, show decRho dt.ly zero one (encMap dt.ly zero one p) = p.1.2 from
    decRho_encPt dt.ly hzo p.1]
  exact p.2

/-! ### The trichotomy: the three legs are exhaustive -/

variable {zero one} in
omit [L.IsRelational] [Finite R] [Finite P] in
/-- **Every block value makes one of three landings**: it is an encoding
(the gated leg), some register cell of its block is ill-shaped (the
shape-failing leg), or every cell is well-shaped and the
one-hot-and-domain conjunct fails at the dispatched tag (the ungated
leg). -/
theorem gate_trichotomy (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (st : TapeStD dt A R P) (b' : Fin dt.ko ⊕ Fin dt.ki) :
    IsEnc dt.ly zero one
        (wmBlk st.mir (Tag.arg (toLex b') : Tag R P dt.KIx)) ∨
      (∃ u₀ : Univ A R P dt.KIx dt.dd,
        ¬dt.wellShapedG zero one b'
          (dt.back RF.cell zero one dt.dd0Le st (RF.cell u₀))) ∨
      ((∀ u : Univ A R P dt.KIx dt.dd,
          dt.wellShapedG zero one b'
            (dt.back RF.cell zero one dt.dd0Le st (RF.cell u))) ∧
        ¬((∀ t' : dt.X.Tag,
            wmBlk st.mir (Tag.arg (toLex b') : Tag R P dt.KIx)
              (encTagTup dt.ly zero one t') ↔
            t' = dt.dspTagOf zero one
              (wmBlk st.mir
                (Tag.arg (toLex b') : Tag R P dt.KIx))) ∧
          ExpExpansion.DomHolds (X := dt.X)
            (dt.dspTagOf zero one
                (wmBlk st.mir
                  (Tag.arg (toLex b') : Tag R P dt.KIx)),
              decRho dt.ly zero one
                (wmBlk st.mir
                  (Tag.arg (toLex b') : Tag R P dt.KIx))))) := by
  classical
  by_cases hE : IsEnc dt.ly zero one
      (wmBlk st.mir (Tag.arg (toLex b') : Tag R P dt.KIx))
  · exact Or.inl hE
  by_cases hsh : ∀ u : Univ A R P dt.KIx dt.dd,
      dt.wellShapedG zero one b'
        (dt.back RF.cell zero one dt.dd0Le st (RF.cell u))
  · refine Or.inr (Or.inr ⟨hsh, fun hc => hE ?_⟩)
    have hshape := dt.forall_shape_iff_of_cells
      (m := st.mir) (b' := b')
      (fun u => (dt.wellShapedG_back_iff RF hzo hlin st b' u).mp (hsh u))
    exact (dt.igVerdict_iff_isEnc hzo hshape).mp hc
  · exact Or.inr (Or.inl (not_forall.mp hsh))

/-! ### The inner loop's bridge: the per-level verdict is the gate -/

variable {zero one} in
omit [Nonempty A] [L.IsRelational] [Finite A] [Finite R] [Finite P] in
/-- **Every cell of an encoded VAL block passes the inner file test.** -/
theorem igTest_of_encMap (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    {stV : TapeStD dt A R P} {b' : Fin dt.ko ⊕ Fin dt.ki} {p : dt.X.Map A}
    (hS : wmBlk stV.val (Tag.arg (toLex b') : Tag R P dt.KIx) =
      encMap dt.ly zero one p)
    (u : Univ A R P dt.KIx dt.dd) :
    dt.igTest RF zero one stV b' u := by
  rw [dt.igTest_iff RF hzo hlin]
  intro h1 hm
  have hmem : encMap dt.ly zero one p u.2 := by
    rw [← hS]
    change stV.val (Tag.arg (toLex b'), u.2)
    rwa [← h1, Prod.mk.eta]
  rcases hmem with h | ⟨i, w, -, h⟩
  · exact Or.inl ⟨p.1.1, h⟩
  · exact Or.inr ⟨i, w, h⟩

omit [L.IsRelational] [Finite R] [Finite P] in
/-- **The inner loop's per-level verdict is the gate**: a level passes –
its file test, the one-hot witness at the dispatched tag and the domain
condition there – exactly when its block value **is** an encoding. The
marks-to-shapes bridge of the two-flag characterization. -/
theorem igPassP_iff_isEnc (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (vi : dt.VarIx) (stV : TapeStD dt A R P) (ℓ : Fin (dt.nIn vi)) :
    dt.igPassP RF zero one vi stV ℓ ↔
      IsEnc dt.ly zero one
        (wmBlk stV.val
          (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)) := by
  rw [igPassP]
  constructor
  · rintro ⟨htest, hone, hdom⟩
    have hshape := dt.forall_shape_iff_of_cells
      (m := stV.val) (b' := dt.igBlk vi ℓ)
      (fun u => (dt.igTest_iff RF hzo hlin stV (dt.igBlk vi ℓ) u).mp (htest u))
    exact (dt.igVerdict_iff_isEnc hzo hshape).mp ⟨hone, hdom⟩
  · rintro ⟨p, hS⟩
    refine ⟨fun u => dt.igTest_of_encMap RF hzo hlin hS u, ?_⟩
    have hshape := dt.forall_shape_iff_of_cells
      (m := stV.val) (b' := dt.igBlk vi ℓ)
      (fun u => (dt.igTest_iff RF hzo hlin stV (dt.igBlk vi ℓ) u).mp
        (dt.igTest_of_encMap RF hzo hlin hS u))
    exact (dt.igVerdict_iff_isEnc hzo hshape).mpr ⟨p, hS⟩

end GateFacts

end Data

end Draw

end DescriptiveComplexity
