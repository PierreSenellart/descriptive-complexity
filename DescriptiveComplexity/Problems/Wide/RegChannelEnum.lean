/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelEntry
import DescriptiveComplexity.Problems.Wide.DrawValEnum

/-!
# The rounds of the evaluation, counted over the handed file

`DescriptiveComplexity.Draw.exists_valEnum` builds the VAL loop's enumeration over
the *universe*, where a space-bounded machine's registers are the elements
themselves. A clocked machine counts the same rounds over the **index of its
file**, so this file rebuilds the enumeration there: a chain of increments in the
file's own order, from the empty address to the registers standing for inner
elements.

Everything it needs is generic (`DescriptiveComplexity.exists_wmChainOf`,
`wmChainOf_lt`) or a fact about the tags: the inner blocks are a final segment
(`DescriptiveComplexity.Draw.kinSeg`), so above a register standing for an inner
element every register does, and a marked address holds inner elements alone –
which is what the semantic layer reads a round through.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

section RegEnum

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [instFR : Finite R'] [instFP : Finite P'] [Finite dt.KIx]
variable {h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd))}
variable {hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y}

variable (dt) in
/-- **The registers the rounds end at**: those standing for an element of an
inner block. -/
def RegKin (u : dt.RegIx (A := A) (R' := R') (P' := P')) : Prop :=
  ∃ j : Fin dt.ki, tagBlk (u.1).1 = some (Sum.inr j)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] [Finite A] [Finite R']
  [Finite P'] [Finite dt.KIx] in
/-- **A register of an inner block stands for an inner argument element.** -/
theorem argIn_of_regKin {u : dt.RegIx (A := A) (R' := R') (P' := P')}
    (hu : dt.RegKin u) : ∃ j : Fin dt.ki, (u.1).1 = argIn dt.ko j := by
  obtain ⟨j, hj⟩ := hu
  exact ⟨j, (tagBlk_eq_some_iff _ _).mp hj⟩

/-- **The inner registers are upward closed**: the inner blocks are a final
segment of the tag order (`DescriptiveComplexity.Draw.kinSeg`), so above a
register of an inner block every register is one. -/
theorem regKin_up {u v : dt.RegIx (A := A) (R' := R') (P' := P')}
    (hu : dt.RegKin u)
    (hlt : WMLt (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le u v) :
    dt.RegKin v := by
  obtain ⟨j, hj⟩ := argIn_of_regKin hu
  rcases hlt.1 with htag | ⟨htag, -⟩
  · obtain ⟨j', hj'⟩ := kinSeg.final j (v.1).1 (hj ▸ wmLt_le_iff.mpr htag)
    exact ⟨j', by rw [hj']; rfl⟩
  · exact ⟨j, by rw [← htag, hj]; rfl⟩

variable (dt h hord) in
/-- **The rounds of the evaluation, over the handed file**: a chain of
increments in the file's own order from the empty address to the inner
registers, in exactly the forms the clocked run demands – the covers are
increments, the last round passes the exhaustion test everywhere, every earlier
one fails it somewhere, every round holds inner registers alone, and every
register it marks is one the addresses use. -/
theorem exists_regValEnum
    (hargall : ∀ x : Univ A R' P' dt.KIx dt.dd,
      (∃ i : dt.KIx, x.1 = Tag.arg i) → WMHasInp x) :
    ∃ (n : ℕ) (mV : Fin (n + 1) → (dt.RegIx (A := A) (R' := R') (P' := P') → Prop)),
      mV 0 = (fun _ => False) ∧
      (∀ a a' : Fin (n + 1), a < a' → (∀ b, ¬(a < b ∧ b < a')) →
        WMIncr (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le (mV a) (mV a')) ∧
      (∀ u, dt.InnerFull (dt.regLaid (A := A) (R' := R') (P' := P') h hord).blk
        (mV (Fin.last n)) u) ∧
      (∀ a, a < Fin.last n → ∃ u,
        ¬dt.InnerFull (dt.regLaid (A := A) (R' := R') (P' := P') h hord).blk (mV a) u) ∧
      (∀ (a : Fin (n + 1)) (t : Tag R' P' dt.KIx) (w : Fin dt.dd → A),
        ixAddr (fun u : dt.RegIx (A := A) (R' := R') (P' := P') => (u.1 : _))
          (mV a) (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j) ∧
      (∀ (a : Fin (n + 1)) (u : dt.RegIx (A := A) (R' := R') (P' := P')),
        mV a u → dt.RegUse u) ∧
      (∀ u : Univ A R' P' dt.KIx dt.dd,
        dt.InnerFull (fun x : Univ A R' P' dt.KIx dt.dd => tagBlk x.1)
          (ixAddr (fun v : dt.RegIx (A := A) (R' := R') (P' := P') => (v.1 : _))
            (mV (Fin.last n))) u) ∧
      n + 1 ≤ 2 ^ Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) := by
  classical
  have hix := isLinOrd_regLaid_le (dt := dt) (A := A) (R' := R') (P' := P')
    (h := h) (hord := hord)
  obtain ⟨n, mV, h0, hlast, hchain⟩ := exists_wmChainOf hix (dt.RegKin)
  -- every round is at or below the last one, hence inside the inner registers
  have hsub : ∀ (a : Fin (n + 1)) (u : dt.RegIx (A := A) (R' := R') (P' := P')),
      mV a u → dt.RegKin u := by
    intro a u hu
    have hle : WMSetLe (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le
        (mV a) (dt.RegKin) := by
      rcases eq_or_lt_of_le (Fin.le_last a) with rfl | hlt
      · exact hlast ▸ Or.inl fun _ => Iff.rfl
      · exact hlast ▸ Or.inr (wmChainOf_lt hix hchain hlt)
    exact subset_of_wmSetLe hix (fun _ _ hx hxy => regKin_up hx hxy) hle hu
  refine ⟨n, mV, h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- adjacency in `Fin (n + 1)` is the chain's cover
    intro a a' hlt hnb
    have hava : (a : ℕ) < (a' : ℕ) := hlt
    have ha' := a'.isLt
    have hsucc : (a' : ℕ) = (a : ℕ) + 1 := by
      by_contra hc
      exact hnb ⟨(a : ℕ) + 1, by omega⟩
        ⟨show (a : ℕ) < (a : ℕ) + 1 by omega,
          show (a : ℕ) + 1 < (a' : ℕ) by omega⟩
    have han : (a : ℕ) < n := by omega
    have e1 : mV a = mV (Fin.castSucc (⟨(a : ℕ), han⟩ : Fin n)) :=
      congrArg mV (Fin.ext rfl)
    have e2 : mV a' = mV (Fin.succ (⟨(a : ℕ), han⟩ : Fin n)) :=
      congrArg mV (Fin.ext hsucc)
    rw [e1, e2]
    exact hchain _
  · -- the last round passes the exhaustion test everywhere
    intro u
    change mV (Fin.last n) u ↔ _
    rw [hlast]
    exact Iff.rfl
  · -- every earlier round fails it somewhere
    intro a ha
    by_contra hc
    push Not at hc
    have heq : mV a = dt.RegKin :=
      funext fun u => propext (hc u)
    have hne := (wmSetLt_iff _ _).mp (wmChainOf_lt hix hchain ha)
    rw [heq, ← hlast] at hne
    exact hne.2 rfl
  · -- a marked address holds inner elements alone
    rintro a t w ⟨u, hu, hmu⟩
    obtain ⟨j, hj⟩ := argIn_of_regKin (hsub a u hmu)
    refine ⟨j, ?_⟩
    have htu : t = (u.1).1 := (congrArg Prod.fst hu).symm
    rw [htu, hj]
  · -- every marked register is one an address uses
    intro a u hu
    obtain ⟨j, hj⟩ := argIn_of_regKin (hsub a u hu)
    exact ⟨Sum.inrₗ j, hj⟩
  · -- read at the universe, the last round is exactly the inner elements
    intro u
    constructor
    · rintro ⟨v, rfl, hv⟩
      rw [hlast] at hv
      exact hv
    · rintro ⟨j, hj⟩
      have huarg : ∃ i : dt.KIx, u.1 = Tag.arg i :=
        ⟨Sum.inrₗ j, (tagBlk_eq_some_iff _ _).mp hj⟩
      refine ⟨⟨u, hargall u huarg⟩, rfl, ?_⟩
      rw [hlast]
      exact ⟨j, hj⟩
  · -- the rounds are as many as the addresses of the file, at most
    have hinj : Function.Injective mV := by
      intro a a' hEq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact ((wmSetLt_iff _ _).mp (wmChainOf_lt hix hchain hlt)).2 hEq
      · exact ((wmSetLt_iff _ _).mp (wmChainOf_lt hix hchain hlt)).2 hEq.symm
    have hcard := Nat.card_le_card_of_injective mV hinj
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    refine le_trans hcard (le_of_eq ?_)
    have : Fintype (dt.RegIx (A := A) (R' := R') (P' := P')) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simp

/-! ### How many elements there are, and how many the channel marks

The clock is met by comparing three numbers with `2 ^ (k · m)`, and two of them
are sizes of the drawing: how many elements the universe has, and how many the
channel writes for. Both are counted here, once, so that a reduction choosing
`k`, `j` and `m` argues about its own tags and nothing else. -/

section Counting

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable (A R' P') in
/-- **The universe's size**: a tag and a tuple. -/
theorem card_univ :
    Nat.card (Univ A R' P' dt.KIx dt.dd) =
      Nat.card (Tag R' P' dt.KIx) * Nat.card A ^ dt.dd := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have : Fintype (Tag R' P' dt.KIx) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp [Fintype.card_prod]

omit [LinearOrder R'] [LinearOrder P'] in
variable (R' P') in
/-- **The tags**: one per rule name, one per phase, one per argument block, and
the alphabet's own. -/
theorem card_drawTag :
    Nat.card (Tag R' P' dt.KIx) =
      Nat.card R' + 1 + Nat.card P' + Nat.card dt.KIx := by
  classical
  have : Fintype R' := Fintype.ofFinite R'
  have : Fintype P' := Fintype.ofFinite P'
  have : Fintype dt.KIx := Fintype.ofFinite _
  have : Fintype (Tag R' P' dt.KIx) := Fintype.ofFinite _
  have hequiv : Tag R' P' dt.KIx ≃ R' ⊕ Unit ⊕ P' ⊕ dt.KIx :=
    { toFun := fun t => match t with
        | .ctrl r => Sum.inl r
        | .sym => Sum.inr (Sum.inl ())
        | .phase p => Sum.inr (Sum.inr (Sum.inl p))
        | .arg i => Sum.inr (Sum.inr (Sum.inr i))
      invFun := fun s => match s with
        | Sum.inl r => .ctrl r
        | Sum.inr (Sum.inl ()) => .sym
        | Sum.inr (Sum.inr (Sum.inl p)) => .phase p
        | Sum.inr (Sum.inr (Sum.inr i)) => .arg i
      left_inv := fun t => by cases t <;> rfl
      right_inv := fun s => by rcases s with r | s' <;> [rfl; rcases s' with u | s'' <;>
        [cases u; rcases s'' with p | i] ] <;> rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr hequiv]
  simp [Nat.card_eq_fintype_card]
  omega

set_option linter.unusedSectionVars false in
variable (A R' P') in
/-- **The channel writes for the argument elements and one more**: so the file
has at most as many registers as there are argument elements, plus one, and the
bound the walks are charged against is `2 ^` that. -/
theorem card_regIx_le
    (hmk : ∀ x : Univ A R' P' dt.KIx dt.dd, WMHasInp x ↔
      ((∃ k, x.1 = Tag.arg k) ∨ IsTopNonArg x)) :
    Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) ≤
      Nat.card dt.KIx * Nat.card A ^ dt.dd + 1 := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have : Fintype dt.KIx := Fintype.ofFinite _
  have : Fintype (dt.RegIx (A := A) (R' := R') (P' := P')) := Fintype.ofFinite _
  refine le_trans (Nat.card_le_card_of_injective
    (f := fun u : dt.RegIx (A := A) (R' := R') (P' := P') =>
      (match (u.1).1, (u.1).2 with
        | Tag.arg k, w => some (k, w)
        | _, _ => none : Option (dt.KIx × (Fin dt.dd → A))))
    ?_) (le_of_eq ?_)
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hEq
    rcases (hmk x).mp hx with ⟨k, hk⟩ | htx
    · rcases (hmk y).mp hy with ⟨k', hk'⟩ | hty
      · obtain ⟨tx, wx⟩ := x
        obtain ⟨ty, wy⟩ := y
        simp only at hk hk'
        subst hk
        subst hk'
        simp only [Option.some.injEq, Prod.mk.injEq] at hEq
        exact Subtype.ext (Prod.ext (congrArg Tag.arg hEq.1) hEq.2)
      · exfalso
        obtain ⟨tx, wx⟩ := x
        obtain ⟨ty, wy⟩ := y
        simp only at hk
        subst hk
        match hty' : ty with
        | Tag.arg k'' => exact hty.1 k'' rfl
        | Tag.ctrl r => subst hty'; exact absurd hEq (by simp)
        | Tag.sym => subst hty'; exact absurd hEq (by simp)
        | Tag.phase p => subst hty'; exact absurd hEq (by simp)
    · rcases (hmk y).mp hy with ⟨k', hk'⟩ | hty
      · exfalso
        obtain ⟨tx, wx⟩ := x
        obtain ⟨ty, wy⟩ := y
        simp only at hk'
        subst hk'
        match htx' : tx with
        | Tag.arg k'' => exact htx.1 k'' rfl
        | Tag.ctrl r => subst htx'; exact absurd hEq (by simp)
        | Tag.sym => subst htx'; exact absurd hEq (by simp)
        | Tag.phase p => subst htx'; exact absurd hEq (by simp)
      · exact Subtype.ext (htx.unique hty)
  · have : Fintype (dt.RegIx (A := A) (R' := R') (P' := P')) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_option, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] in
/-- **The file has at least one register per padded argument cell**: the channel
writes for every argument element, and the padded tuples of the encoding's width
are that many. This is the *lower* bound the clock's exponent is measured
against – the record's tuple counts are below the register count, so they are
below the file's own bound. -/
theorem card_regIx_ge {zero : A}
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
        Univ A R' P' dt.KIx dt.dd)) :
    Nat.card dt.KIx * Nat.card A ^ dt.dd0 ≤
      Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have : Fintype dt.KIx := Fintype.ofFinite _
  have : Fintype (dt.RegIx (A := A) (R' := R') (P' := P')) := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun p : dt.KIx × (Fin dt.dd0 → A) =>
        (⟨(Tag.arg p.1, padTup (dt := dt) zero p.2), harg (ofLex p.1) p.2⟩ :
          dt.RegIx (A := A) (R' := R') (P' := P'))) := by
    rintro ⟨k, c⟩ ⟨k', c'⟩ hEq
    have h := congrArg Subtype.val hEq
    have h1 : (Tag.arg k : Tag R' P' dt.KIx) = Tag.arg k' :=
      congrArg Prod.fst h
    have h2 : padTup (dt := dt) (A := A) zero c = padTup (dt := dt) zero c' :=
      congrArg Prod.snd h
    refine Prod.ext (Tag.arg.inj h1) ?_
    funext j
    have hj := congrFun h2 (Fin.castLE dt.dd0Le j)
    rwa [padTup_coord (dt := dt) (A := A) zero c dt.dd0Le j,
      padTup_coord (dt := dt) (A := A) zero c' dt.dd0Le j] at hj
  have hcard : Nat.card (dt.KIx × (Fin dt.dd0 → A)) =
      Nat.card dt.KIx * Nat.card A ^ dt.dd0 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← hcard]
  exact Nat.card_le_card_of_injective _ hinj

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] [Finite A]
  [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable (dt) in
/-- **The drawing has at least one tag per assignment of the guessed block**:
the guessing site's rule names carry a block of the sweep and a certificate
value, so the assignments of the block inject into the rule names.

This is the *lower* bound the clock's counting hypothesis is met by, and it is
why a reduction can buy tags by padding its kernel's block
(`DescriptiveComplexity.SOBlock.pad`): one extra relation variable doubles the
count. -/
theorem two_pow_card_le_card_nexRIx [Finite dt.d.B.ι]
    [Finite (dt.NexRIx (G := dt.d.B.ι → Bool))] :
    2 ^ Nat.card dt.d.B.ι ≤ Nat.card (dt.NexRIx (G := dt.d.B.ι → Bool)) := by
  classical
  have : Fintype dt.d.B.ι := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun x : dt.d.B.ι → Bool =>
        (⟨NexSite.guess, Sum.inl ((none : Option dt.KIx), x)⟩ :
          dt.NexRIx (G := dt.d.B.ι → Bool))) := by
    intro x y hxy
    injection hxy with _hfst hsnd
    exact congrArg Prod.snd (Sum.inl.inj hsnd)
  have hcard : Nat.card (dt.d.B.ι → Bool) = 2 ^ Nat.card dt.d.B.ι := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_bool]
  rw [← hcard]
  exact Nat.card_le_card_of_injective _ hinj

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] in
variable (A R' P') in
/-- **The clock's exponent, counted**: every dimension the evaluation's width is
measured against is under a power of two whose exponent is *linear in the number
of registers*, with the kernel's own dimensions as the additive constant. The
file's widths give `4 N + 14` (`regWidthBd_le_two_pow`), the padded cells give
`N` – a register per cell, `card_regIx_ge` – and the loop budget gives
`eDim · N`, the universe being no bigger than the file.

This is where the clock stops depending on the instance: `N` grows with
`|A| ^ dd`, and so does the drawing, so what a reduction owes is a comparison
between two *constants*. -/
theorem evalQ_le_two_pow [Nonempty dt.KIx] [Nonempty A] (hdd0 : 1 ≤ dt.dd0)
    {zero : A}
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
        Univ A R' P' dt.KIx dt.dd)) :
    dt.evalQ A R' P' ≤
      2 ^ (4 * Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) + 14 +
        dt.eDim * Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) + dt.dimC) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  set N := Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) with hN
  -- the padded cells are registers, so the universe is no bigger than the file
  have hcell : Nat.card A ^ dt.dd0 ≤ N := by
    refine le_trans ?_ (dt.card_regIx_ge (R' := R') (P' := P') harg)
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  have hA : Nat.card A ≤ N := by
    refine le_trans ?_ hcell
    calc Nat.card A = Nat.card A ^ 1 := (pow_one _).symm
      _ ≤ Nat.card A ^ dt.dd0 := Nat.pow_le_pow_right Nat.card_pos hdd0
  have hNle : N ≤ 2 ^ N := le_of_lt Nat.lt_two_pow_self
  have hNpos : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  -- the four parts, each under the exponent
  have h16 : (16 : ℕ) ≤ 2 ^ (4 * N + 14 + dt.eDim * N + dt.dimC) := by
    calc (16 : ℕ) = 2 ^ 4 := rfl
      _ ≤ 2 ^ (4 * N + 14 + dt.eDim * N + dt.dimC) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hW : dt.regWidthBd A R' P' ≤ 2 ^ (4 * N + 14 + dt.eDim * N + dt.dimC) :=
    le_trans (dt.regWidthBd_le_two_pow A R' P')
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hD0 : Nat.card (Lex (Fin dt.dd0 → A)) + 1 ≤
      2 ^ (4 * N + 14 + dt.eDim * N + dt.dimC) := by
    have hcard : Nat.card (Lex (Fin dt.dd0 → A)) = Nat.card A ^ dt.dd0 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      simp
    rw [hcard]
    calc Nat.card A ^ dt.dd0 + 1 ≤ N + 1 := by omega
      _ ≤ 2 ^ N + 2 ^ N := by omega
      _ = 2 ^ (N + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (4 * N + 14 + dt.eDim * N + dt.dimC) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hE : Nat.card (Lex (Fin dt.eDim → A)) + 1 ≤
      2 ^ (4 * N + 14 + dt.eDim * N + dt.dimC) := by
    have hcard : Nat.card (Lex (Fin dt.eDim → A)) = Nat.card A ^ dt.eDim := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      simp
    have hpow : Nat.card A ^ dt.eDim ≤ 2 ^ (dt.eDim * N) := by
      calc Nat.card A ^ dt.eDim ≤ (2 ^ N) ^ dt.eDim :=
            Nat.pow_le_pow_left (le_trans hA hNle) _
        _ = 2 ^ (dt.eDim * N) := by rw [← pow_mul, Nat.mul_comm]
    rw [hcard]
    calc Nat.card A ^ dt.eDim + 1 ≤ 2 ^ (dt.eDim * N) + 2 ^ (dt.eDim * N) := by
          have := Nat.one_le_two_pow (n := dt.eDim * N)
          omega
      _ = 2 ^ (dt.eDim * N + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (4 * N + 14 + dt.eDim * N + dt.dimC) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hC : dt.dimC ≤ 2 ^ (4 * N + 14 + dt.eDim * N + dt.dimC) :=
    le_trans (le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by omega) (by omega))
  simp only [Data.evalQ, max_le_iff]
  exact ⟨h16, hW, hD0, hE, hC⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] in
variable (A R' P') in
/-- **And its logarithm**, which is the number the clock actually compares. -/
theorem log_evalQ_le [Nonempty dt.KIx] [Nonempty A] (hdd0 : 1 ≤ dt.dd0)
    {zero : A}
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
        Univ A R' P' dt.KIx dt.dd)) :
    Nat.log 2 (dt.evalQ A R' P') ≤
      4 * Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) + 14 +
        dt.eDim * Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) + dt.dimC := by
  have h := dt.evalQ_le_two_pow A R' P' hdd0 harg
  calc Nat.log 2 (dt.evalQ A R' P')
      ≤ Nat.log 2 (2 ^ (4 * Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) + 14 +
        dt.eDim * Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) + dt.dimC)) :=
        Nat.log_mono_right h
    _ = _ := Nat.log_pow (by omega) _

variable (dt A R') in
/-- **The clock's one inequality, met by a constant of the kernel.** The
exponent is linear in the register count (`log_evalQ_le`), the register count is
linear in `|A| ^ dd` (`card_regIx_le`), and the universe is `|Tag| · |A| ^ dd`
– so the two sides scale together and what is left is a comparison between the
drawing's rule names and a number built from the kernel alone: its guessed
variables' arities and counts (`dimC`), its loop budget (`eDim`) and its argument
blocks (`KIx`).

A reduction meets it by padding its kernel's block until the rule names clear
that number, each extra variable doubling them
(`two_pow_card_le_card_nexRIx`). -/
theorem clock_count_of_tags [Nonempty dt.KIx] [Nonempty A]
    [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
    [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
    [Language.wide.Structure (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
    (hdd0 : 1 ≤ dt.dd0) {zero : A}
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
        Univ A (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hmk : ∀ x : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp x ↔ ((∃ k, x.1 = Tag.arg k) ∨ IsTopNonArg x))
    (htags : 52 * (4 + dt.eDim) * Nat.card dt.KIx + 52 * (4 + dt.eDim) +
        52 * (15 + dt.dimC) + 2 ≤
      Nat.card (R')) :
    2 * max (26 * (Nat.log 2 (dt.evalQ A (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 1))
        (Nat.card (dt.RegIx (A := A)
          (R' := R')
          (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 3) + 2 ≤
      Nat.card (Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) := by
  classical
  set N := Nat.card (dt.RegIx (A := A) (R' := R')
    (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) with hN
  set T := Nat.card (R') with hT
  set n := Nat.card A ^ dt.dd with hn
  -- the exponent, and the register count
  have hlog := dt.log_evalQ_le A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) hdd0 harg
  rw [← hN] at hlog
  have hreg : N ≤ Nat.card dt.KIx * n + 1 := by
    rw [hN, hn]
    exact card_regIx_le (dt := dt) A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) hmk
  have hn1 : 1 ≤ n := Nat.one_le_pow _ _ Nat.card_pos
  -- the universe, and its tags
  have huniv : Nat.card (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) =
      (T + 1 + Nat.card (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) +
        Nat.card dt.KIx) * n := by
    rw [card_univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)),
      card_drawTag (dt := dt) (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  rw [huniv]
  -- the left-hand side, linear in the register count
  have hleft : 2 * max (26 * (Nat.log 2 (dt.evalQ A
        (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 1)) (N + 3) + 2 ≤
      52 * (4 + dt.eDim) * N + 52 * (15 + dt.dimC) + 2 := by
    have hmulE : (4 + dt.eDim) * N = 4 * N + dt.eDim * N := by ring
    have hb : Nat.log 2 (dt.evalQ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 1 ≤
        (4 + dt.eDim) * N + 15 + dt.dimC := by omega
    have h1 : 26 * (Nat.log 2 (dt.evalQ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 1) ≤
        26 * ((4 + dt.eDim) * N + 15 + dt.dimC) := Nat.mul_le_mul_left _ hb
    have hle : N ≤ (4 + dt.eDim) * N := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : N + 3 ≤ 26 * ((4 + dt.eDim) * N + 15 + dt.dimC) := by
      have hstep : N + 3 ≤ (4 + dt.eDim) * N + 15 + dt.dimC := by omega
      exact le_trans hstep (Nat.le_mul_of_pos_left _ (by omega))
    have hmax : max (26 * (Nat.log 2 (dt.evalQ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 1)) (N + 3) ≤
        26 * ((4 + dt.eDim) * N + 15 + dt.dimC) := max_le h1 h2
    calc 2 * max (26 * (Nat.log 2 (dt.evalQ A (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) + 1)) (N + 3) + 2
        ≤ 2 * (26 * ((4 + dt.eDim) * N + 15 + dt.dimC)) + 2 := by omega
      _ = 52 * (4 + dt.eDim) * N + 52 * (15 + dt.dimC) + 2 := by ring
  refine le_trans hleft ?_
  -- and the right-hand side, linear in the same
  have hstep : 52 * (4 + dt.eDim) * N + 52 * (15 + dt.dimC) + 2 ≤
      (52 * (4 + dt.eDim) * Nat.card dt.KIx + 52 * (4 + dt.eDim) +
        52 * (15 + dt.dimC) + 2) * n := by
    have hmul : 52 * (4 + dt.eDim) * N ≤
        52 * (4 + dt.eDim) * (Nat.card dt.KIx * n + 1) :=
      Nat.mul_le_mul_left _ hreg
    calc 52 * (4 + dt.eDim) * N + 52 * (15 + dt.dimC) + 2
        ≤ 52 * (4 + dt.eDim) * (Nat.card dt.KIx * n + 1) +
            52 * (15 + dt.dimC) + 2 := by omega
      _ = 52 * (4 + dt.eDim) * Nat.card dt.KIx * n + 52 * (4 + dt.eDim) +
            52 * (15 + dt.dimC) + 2 := by ring
      _ ≤ 52 * (4 + dt.eDim) * Nat.card dt.KIx * n + 52 * (4 + dt.eDim) * n +
            (52 * (15 + dt.dimC) + 2) * n := by
          have hc1 : 52 * (4 + dt.eDim) ≤ 52 * (4 + dt.eDim) * n :=
            Nat.le_mul_of_pos_right _ (by omega)
          have hc2 : 52 * (15 + dt.dimC) + 2 ≤ (52 * (15 + dt.dimC) + 2) * n :=
            Nat.le_mul_of_pos_right _ (by omega)
          omega
      _ = (52 * (4 + dt.eDim) * Nat.card dt.KIx + 52 * (4 + dt.eDim) +
            52 * (15 + dt.dimC) + 2) * n := by ring
  refine le_trans hstep (Nat.mul_le_mul_right _ ?_)
  omega

end Counting

end RegEnum

end Data

end Draw

end DescriptiveComplexity
