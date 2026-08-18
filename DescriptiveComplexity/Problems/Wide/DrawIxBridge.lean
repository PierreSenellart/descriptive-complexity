/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawGateFacts
import DescriptiveComplexity.Problems.Wide.IxAddr

/-!
# What a coarse file's gate test is, elementwise

The gates' shape test reads four slots of the background – the block one-hot,
the mirror bit, the padding flag and the name coordinates – and **none of the
address-side ones**. Each of the four is a fact about the register's own index,
and at a file whose registers stand for elements each is the same fact about the
element: the block is the element's tag's (`hblkP`), the tuple is the element's
(`hargP`), and the mirror bit at the register is the mirror's *address* at the
element (`ixAddr_elt`).

So a coarse file's shape test at a register **is** the elementwise test at the
element it stands for, which is the step the two bridges `hpassEnc` and
`hgateEnc` need: `DescriptiveComplexity.Draw.Data.gate_trichotomy` is stated
elementwise and reaches a coarse file through this file.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P']
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable {I : Type} {lay : Layout dt A R' P' I}
variable {elt : I → Univ A R' P' dt.KIx dt.dd}
variable {zero one : A}

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A] in
/-- **A coarse background's block one-hot, at a register**: the register's own
block, which by `hblkP` is the block of the element it stands for. -/
theorem ixBack_blk_cell_eq (hinj : Function.Injective lay.cell)
    (st : TapeSt dt A R' P' I) (u : I) (b : Option (Fin dt.ko ⊕ Fin dt.ki)) :
    dt.ixBack lay zero one dt.dd0Le st (lay.cell u) (Slot.blk b) =
      bitVal zero one (lay.blk u = b) :=
  congrArg (bitVal zero one)
    (propext ⟨fun ⟨_u', he, hb⟩ => hinj he ▸ hb, fun h => ⟨u, rfl, h⟩⟩)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A] in
/-- **A coarse background's mirror bit, at a register**: the mirror at that
register. -/
theorem ixBack_mir_cell_eq (hinj : Function.Injective lay.cell)
    (st : TapeSt dt A R' P' I) (u : I) :
    dt.ixBack lay zero one dt.dd0Le st (lay.cell u) Slot.mir =
      bitVal zero one (st.mir u) :=
  congrArg (bitVal zero one)
    (propext ⟨fun ⟨_u', he, hm⟩ => hinj he ▸ hm, fun h => ⟨u, rfl, h⟩⟩)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A] in
/-- **A coarse background's padding flag, at a register**: the register's tuple
is `zero` above `dd₀`. -/
theorem ixBack_pdd_cell_eq (hinj : Function.Injective lay.cell)
    (st : TapeSt dt A R' P' I) (u : I) :
    dt.ixBack lay zero one dt.dd0Le st (lay.cell u) Slot.pdd =
      bitVal zero one (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → lay.arg u j = zero) :=
  congrArg (bitVal zero one)
    (propext ⟨fun ⟨_u', he, hp⟩ => hinj he ▸ hp, fun h => ⟨u, rfl, h⟩⟩)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A] in
/-- **A coarse background's name slots, at a register**: the register's own
tuple. -/
theorem ixBack_name_cell_eq (hinj : Function.Injective lay.cell)
    (st : TapeSt dt A R' P' I) (u : I) (j : Fin dt.dd0) :
    dt.ixBack lay zero one dt.dd0Le st (lay.cell u) (Slot.name j) =
      lay.arg u (Fin.castLE dt.dd0Le j) := by
  classical
  have hex : ∃ u' : I, lay.cell u = lay.cell u' := ⟨u, rfl⟩
  change (if h : ∃ u' : I, lay.cell u = lay.cell u' then
    lay.arg h.choose (Fin.castLE dt.dd0Le j) else zero) = _
  rw [dif_pos hex]
  exact congrArg (fun u' => lay.arg u' (Fin.castLE dt.dd0Le j)) (hinj hex.choose_spec).symm

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A] in
/-- **A coarse background's VAL bit, at a register**: VAL at that register. -/
theorem ixBack_val_cell_eq (hinj : Function.Injective lay.cell)
    (st : TapeSt dt A R' P' I) (u : I) :
    dt.ixBack lay zero one dt.dd0Le st (lay.cell u) Slot.val =
      bitVal zero one (st.val u) :=
  congrArg (bitVal zero one)
    (propext ⟨fun ⟨_u', he, hm⟩ => hinj he ▸ hm, fun h => ⟨u, rfl, h⟩⟩)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A] in
/-- **A coarse file's shape test is the elementwise one**: the gate's four slots
are the register's block, mirror bit, padding and tuple, and each of them is the
same fact about the element the register stands for. So a program whose
registers are not the elements asks exactly the question
`DescriptiveComplexity.Draw.Data.gate_trichotomy` answers. -/
theorem wellShapedG_ixBack_iff (hinj : Function.Injective lay.cell)
    (heltInj : Function.Injective elt)
    (hblkP : ∀ u : I, lay.blk u = tagBlk (elt u).1)
    (hargP : ∀ u : I, lay.arg u = (elt u).2)
    (hzo : zero ≠ one)
    (st : TapeSt dt A R' P' I) (b : Fin dt.ko ⊕ Fin dt.ki) (u : I) :
    dt.wellShapedG zero one b
        (dt.ixBack lay zero one dt.dd0Le st (lay.cell u)) ↔
      (tagBlk (elt u).1 = some b → ixAddr elt st.mir (elt u) →
        ((∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → (elt u).2 j = zero) ∧
          ((∃ t : dt.X.Tag, ∀ j : Fin dt.dd0,
              (elt u).2 (Fin.castLE dt.dd0Le j) =
                encTagTup dt.ly zero one t (Fin.castLE dt.dd0Le j)) ∨
            ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A), ∀ j : Fin dt.dd0,
              (elt u).2 (Fin.castLE dt.dd0Le j) =
                encAsgTup dt.ly zero one i w (Fin.castLE dt.dd0Le j)))) := by
  classical
  have hmirU : ixAddr elt st.mir (elt u) ↔ st.mir u :=
    ixAddr_elt heltInj st.mir u
  constructor
  · intro h hb hmir
    have hb' : dt.ixBack lay zero one dt.dd0Le st (lay.cell u)
        (Slot.blk (some b)) = one := by
      rw [ixBack_blk_cell_eq hinj st u (some b), hblkP u, hb]
      exact bitVal_pos rfl
    have hm' : dt.ixBack lay zero one dt.dd0Le st (lay.cell u) Slot.mir = one := by
      rw [ixBack_mir_cell_eq hinj st u]
      exact bitVal_pos (hmirU.mp hmir)
    obtain ⟨hpdd, hname⟩ := h hb' hm'
    refine ⟨?_, ?_⟩
    · rw [ixBack_pdd_cell_eq hinj st u] at hpdd
      have := (bitVal_iff hzo).mp hpdd
      intro j hj
      rw [← hargP u]
      exact this j hj
    · rcases hname with ⟨t, ht⟩ | ⟨i, w, hw⟩
      · refine Or.inl ⟨t, fun j => ?_⟩
        rw [← hargP u, ← ixBack_name_cell_eq hinj st u j]
        exact ht j
      · refine Or.inr ⟨i, w, fun j => ?_⟩
        rw [← hargP u, ← ixBack_name_cell_eq hinj st u j]
        exact hw j
  · intro h hb' hm'
    have hb : tagBlk (elt u).1 = some b := by
      rw [← hblkP u]
      rw [ixBack_blk_cell_eq hinj st u (some b)] at hb'
      exact (bitVal_iff hzo).mp hb'
    have hmir : ixAddr elt st.mir (elt u) := by
      rw [ixBack_mir_cell_eq hinj st u] at hm'
      exact hmirU.mpr ((bitVal_iff hzo).mp hm')
    obtain ⟨hpdd, hname⟩ := h hb hmir
    refine ⟨?_, ?_⟩
    · rw [ixBack_pdd_cell_eq hinj st u]
      refine bitVal_pos fun j hj => ?_
      rw [hargP u]
      exact hpdd j hj
    · rcases hname with ⟨t, ht⟩ | ⟨i, w, hw⟩
      · refine Or.inl ⟨t, fun j => ?_⟩
        rw [ixBack_name_cell_eq hinj st u j, hargP u]
        exact ht j
      · refine Or.inr ⟨i, w, fun j => ?_⟩
        rw [ixBack_name_cell_eq hinj st u j, hargP u]
        exact hw j

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A] in
/-- **An inner gate's shape test is the elementwise one too**: the same four
slots, with VAL where the outer gate reads the mirror. -/
theorem wellShapedIG_ixBack_iff (hinj : Function.Injective lay.cell)
    (heltInj : Function.Injective elt)
    (hblkP : ∀ u : I, lay.blk u = tagBlk (elt u).1)
    (hargP : ∀ u : I, lay.arg u = (elt u).2)
    (hzo : zero ≠ one)
    (st : TapeSt dt A R' P' I) (b : Fin dt.ko ⊕ Fin dt.ki) (u : I) :
    dt.wellShapedIG zero one b
        (dt.ixBack lay zero one dt.dd0Le st (lay.cell u)) ↔
      (tagBlk (elt u).1 = some b → ixAddr elt st.val (elt u) →
        ((∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → (elt u).2 j = zero) ∧
          ((∃ t : dt.X.Tag, ∀ j : Fin dt.dd0,
              (elt u).2 (Fin.castLE dt.dd0Le j) =
                encTagTup dt.ly zero one t (Fin.castLE dt.dd0Le j)) ∨
            ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A), ∀ j : Fin dt.dd0,
              (elt u).2 (Fin.castLE dt.dd0Le j) =
                encAsgTup dt.ly zero one i w (Fin.castLE dt.dd0Le j)))) := by
  classical
  have hvalU : ixAddr elt st.val (elt u) ↔ st.val u :=
    ixAddr_elt heltInj st.val u
  constructor
  · intro h hb hval
    have hb' : dt.ixBack lay zero one dt.dd0Le st (lay.cell u)
        (Slot.blk (some b)) = one := by
      rw [ixBack_blk_cell_eq hinj st u (some b), hblkP u, hb]
      exact bitVal_pos rfl
    have hv' : dt.ixBack lay zero one dt.dd0Le st (lay.cell u) Slot.val = one := by
      rw [ixBack_val_cell_eq hinj st u]
      exact bitVal_pos (hvalU.mp hval)
    obtain ⟨hpdd, hname⟩ := h hb' hv'
    refine ⟨?_, ?_⟩
    · rw [ixBack_pdd_cell_eq hinj st u] at hpdd
      have := (bitVal_iff hzo).mp hpdd
      intro j hj
      rw [← hargP u]
      exact this j hj
    · rcases hname with ⟨t, ht⟩ | ⟨i, w, hw⟩
      · refine Or.inl ⟨t, fun j => ?_⟩
        rw [← hargP u, ← ixBack_name_cell_eq hinj st u j]
        exact ht j
      · refine Or.inr ⟨i, w, fun j => ?_⟩
        rw [← hargP u, ← ixBack_name_cell_eq hinj st u j]
        exact hw j
  · intro h hb' hv'
    have hb : tagBlk (elt u).1 = some b := by
      rw [← hblkP u]
      rw [ixBack_blk_cell_eq hinj st u (some b)] at hb'
      exact (bitVal_iff hzo).mp hb'
    have hval : ixAddr elt st.val (elt u) := by
      rw [ixBack_val_cell_eq hinj st u] at hv'
      exact hvalU.mpr ((bitVal_iff hzo).mp hv')
    obtain ⟨hpdd, hname⟩ := h hb hval
    refine ⟨?_, ?_⟩
    · rw [ixBack_pdd_cell_eq hinj st u]
      refine bitVal_pos fun j hj => ?_
      rw [hargP u]
      exact hpdd j hj
    · rcases hname with ⟨t, ht⟩ | ⟨i, w, hw⟩
      · refine Or.inl ⟨t, fun j => ?_⟩
        rw [ixBack_name_cell_eq hinj st u j, hargP u]
        exact ht j
      · refine Or.inr ⟨i, w, fun j => ?_⟩
        rw [ixBack_name_cell_eq hinj st u j, hargP u]
        exact hw j

omit [Finite R'] [Finite P'] [L.IsRelational] in
/-- **The gates' trichotomy at a coarse file**: either the block of the
mirror's *address* is an encoding, or some register fails the shape test, or
every register passes it and the tag half fails. This is
`DescriptiveComplexity.Draw.Data.gate_trichotomy` read at a file whose
registers are not the elements: the shape test is the same question
(`wellShapedG_ixBack_iff`), and what carries the failing witness across costs
nothing: an element that fails the shape test is one the *address* holds, so it
is a register's element already, and no file has to have a register for every
element of a block. -/
theorem ix_gate_trichotomy (RF : RegFile (Univ A R' P' dt.KIx dt.dd))
    (hinj : Function.Injective lay.cell) (heltInj : Function.Injective elt)
    (hblkP : ∀ u : I, lay.blk u = tagBlk (elt u).1)
    (hargP : ∀ u : I, lay.arg u = (elt u).2)
    (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    (st : TapeSt dt A R' P' I) (b' : Fin dt.ko ⊕ Fin dt.ki) :
    IsEnc dt.ly zero one
        (wmBlk (ixAddr elt st.mir) (Tag.arg (toLex b') : Tag R' P' dt.KIx)) ∨
      (∃ u₀ : I, ¬dt.wellShapedG zero one b'
        (dt.ixBack lay zero one dt.dd0Le st (lay.cell u₀))) ∨
      ((∀ u : I, dt.wellShapedG zero one b'
          (dt.ixBack lay zero one dt.dd0Le st (lay.cell u))) ∧
        ¬((∀ t' : dt.X.Tag,
            wmBlk (ixAddr elt st.mir)
                (Tag.arg (toLex b') : Tag R' P' dt.KIx)
                (encTagTup dt.ly zero one t') ↔
              t' = dt.dspTagOf zero one
                (wmBlk (ixAddr elt st.mir)
                  (Tag.arg (toLex b') : Tag R' P' dt.KIx))) ∧
          ExpExpansion.DomHolds (X := dt.X)
            (dt.dspTagOf zero one
                (wmBlk (ixAddr elt st.mir)
                  (Tag.arg (toLex b') : Tag R' P' dt.KIx)),
              decRho dt.ly zero one
                (wmBlk (ixAddr elt st.mir)
                  (Tag.arg (toLex b') : Tag R' P' dt.KIx))))) := by
  classical
  -- the elementwise state the coarse one stands for: only its mirror is read
  set stD : TapeStD dt A R' P' :=
    { mir := ixAddr elt st.mir, tgt := ixAddr elt st.tgt, sav := ixAddr elt st.sav,
      val := ixAddr elt st.val, old := st.old, new := st.new, wk := st.wk,
      bot := st.bot, ltp := st.ltp } with hstD
  have hcellinj : Function.Injective RF.cell := RF.injective hlin
  -- the two readings of the shape test, coarse and elementwise
  have hcoarse := fun u : I => wellShapedG_ixBack_iff (lay := lay) (elt := elt)
    hinj heltInj hblkP hargP hzo st b' u
  have hdiag := fun x : Univ A R' P' dt.KIx dt.dd =>
    wellShapedG_ixBack_iff (lay := dt.diagLayout RF.cell) (elt := id)
      hcellinj Function.injective_id (fun _ => rfl) (fun _ => rfl) hzo stD b' x
  have hmirD : ∀ x : Univ A R' P' dt.KIx dt.dd,
      ixAddr (id : Univ A R' P' dt.KIx dt.dd → _) stD.mir x ↔ ixAddr elt st.mir x := by
    intro x
    rw [ixAddr_id]
  rcases dt.gate_trichotomy RF hzo hlin stD b' with h | ⟨x₀, hbad⟩ | ⟨hall, hbad⟩
  · exact Or.inl h
  · -- the failing element is one the address holds, so it is a register's
    refine Or.inr (Or.inl ?_)
    have hQ : ¬(tagBlk x₀.1 = some b' → ixAddr elt st.mir x₀ →
        ((∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → x₀.2 j = zero) ∧
          ((∃ t : dt.X.Tag, ∀ j : Fin dt.dd0,
              x₀.2 (Fin.castLE dt.dd0Le j) =
                encTagTup dt.ly zero one t (Fin.castLE dt.dd0Le j)) ∨
            ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A), ∀ j : Fin dt.dd0,
              x₀.2 (Fin.castLE dt.dd0Le j) =
                encAsgTup dt.ly zero one i w (Fin.castLE dt.dd0Le j)))) := by
      intro hc
      refine hbad ((hdiag x₀).mpr ?_)
      intro hb hm
      exact hc hb ((hmirD x₀).mp hm)
    have hmir : ixAddr elt st.mir x₀ := by
      by_contra hc
      exact hQ (fun _ hm => absurd hm hc)
    obtain ⟨u₀, rfl, -⟩ := hmir
    exact ⟨u₀, fun hc => hQ ((hcoarse u₀).mp hc)⟩
  · refine Or.inr (Or.inr ⟨fun u => (hcoarse u).mpr ?_, hbad⟩)
    intro hb hm
    exact ((hdiag (elt u)).mp (hall (elt u))) hb ((hmirD (elt u)).mpr hm)

end Data

end Draw

end DescriptiveComplexity
