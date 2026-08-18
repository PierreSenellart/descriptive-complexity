/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelLaid
import DescriptiveComplexity.Problems.Wide.NexSpine
import DescriptiveComplexity.Problems.Wide.DrawIxPack
import DescriptiveComplexity.Problems.Wide.BlkLayout
import DescriptiveComplexity.Problems.Wide.DrawIxWidth
import DescriptiveComplexity.Problems.Wide.DrawIxSpineSem

/-!
# The clocked evaluation at the file the channel hands over

A program that *lays* its file puts the registers at consecutive addresses, each
one bit above the last. This file prices the clocked evaluation at the file the
**register channel** hands over instead, where the registers are the cells the
channel writes and a step of a walk across the file can cost as much as the whole
file (`DescriptiveComplexity.Draw.Data.nexIxEvalB_regLaid_reachesIn`).

The four widths are `regW`, `regWP`, `regWR`, `regWK`
(`DescriptiveComplexity.Draw.Data.regW` and its neighbors), each bounded by
one number, `regWidthBound`: three of the four are linear in the file's own
bound, and the seek is quadratic, being a pass of the file per bit of its
target.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

/-! ### One number above the register file's four widths -/

section WidthBound

/-- **One number above all four widths of the handed file**: the file's bound
and the walk across it, squared, with room for the constants. -/
def regWidthBound (t B : ℕ) : ℕ := 16 * (B + t * B + 16) ^ 2

/-- **The width bound, as a power of two**: at the file's own bound `2 ^ N` and
its `N` registers, the widths are below `2 ^ (4 N + 14)`. Every clock argument
wants the widths as an *exponent*, and this is where the polynomial becomes
one. -/
theorem regWidthBound_le_two_pow (N : ℕ) :
    regWidthBound N (2 ^ N) ≤ 2 ^ (4 * N + 14) := by
  have h1 : N + 1 ≤ 2 ^ N := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have hp : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
  have h2 : 2 ^ N + N * 2 ^ N ≤ 2 ^ (2 * N) := by
    have hmul : (N + 1) * 2 ^ N ≤ 2 ^ N * 2 ^ N := Nat.mul_le_mul_right _ h1
    have hsq : (2 : ℕ) ^ N * 2 ^ N = 2 ^ (2 * N) := by
      rw [← pow_add]
      ring_nf
    calc 2 ^ N + N * 2 ^ N = (N + 1) * 2 ^ N := by ring
      _ ≤ 2 ^ N * 2 ^ N := hmul
      _ = 2 ^ (2 * N) := hsq
  have h3 : 2 ^ N + N * 2 ^ N + 16 ≤ 2 ^ (2 * N + 5) := by
    have hq : (0 : ℕ) < 2 ^ (2 * N) := Nat.two_pow_pos (2 * N)
    have h32 : (2 : ℕ) ^ (2 * N + 5) = 32 * 2 ^ (2 * N) := by
      rw [pow_add]
      ring
    omega
  have h4 : (2 ^ N + N * 2 ^ N + 16) ^ 2 ≤ 2 ^ (4 * N + 10) := by
    have hsq : ((2 : ℕ) ^ (2 * N + 5)) ^ 2 = 2 ^ (4 * N + 10) := by
      rw [← pow_mul]
      ring_nf
    calc (2 ^ N + N * 2 ^ N + 16) ^ 2 ≤ (2 ^ (2 * N + 5)) ^ 2 :=
          Nat.pow_le_pow_left h3 2
      _ = 2 ^ (4 * N + 10) := hsq
  have h5 : (16 : ℕ) * 2 ^ (4 * N + 10) = 2 ^ (4 * N + 14) := by
    rw [show (4 : ℕ) * N + 14 = (4 * N + 10) + 4 from by omega, pow_add]
    ring
  calc regWidthBound N (2 ^ N) = 16 * (2 ^ N + N * 2 ^ N + 16) ^ 2 := rfl
    _ ≤ 16 * 2 ^ (4 * N + 10) := Nat.mul_le_mul_left _ h4
    _ = 2 ^ (4 * N + 14) := h5

variable {t B : ℕ}

theorem regW_le : 2 * B + 2 ≤ regWidthBound t B := by
  have hB : B ≤ B + t * B + 16 := by omega
  have hT : t * B ≤ B + t * B + 16 := by omega
  have h16 : 16 ≤ B + t * B + 16 := by omega
  simp only [regWidthBound, pow_two]
  nlinarith [hB, hT, h16]

theorem regWP_le : 2 * B + t * B + 3 ≤ regWidthBound t B := by
  have hB : B ≤ B + t * B + 16 := by omega
  have hT : t * B ≤ B + t * B + 16 := by omega
  have h16 : 16 ≤ B + t * B + 16 := by omega
  simp only [regWidthBound, pow_two]
  nlinarith [hB, hT, h16]

theorem regWR_le : B + 4 ≤ regWidthBound t B := by
  have hB : B ≤ B + t * B + 16 := by omega
  have hT : t * B ≤ B + t * B + 16 := by omega
  have h16 : 16 ≤ B + t * B + 16 := by omega
  simp only [regWidthBound, pow_two]
  nlinarith [hB, hT, h16]

theorem regWK_le :
    B * (1 + (2 * B + 3 + t * B) + (2 * B + 5 + t * B)) + 1 + (2 * B + 3 + t * B) ≤
      regWidthBound t B := by
  have hB : B ≤ B + t * B + 16 := by omega
  have hT : t * B ≤ B + t * B + 16 := by omega
  have h16 : 16 ≤ B + t * B + 16 := by omega
  simp only [regWidthBound, pow_two]
  nlinarith [hB, hT, h16]

end WidthBound

section Laid

variable {L : Language.{0, 0}} (dt : Data L) {A R' P' : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P']
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable [Finite dt.KIx]

variable (A R' P') in
/-- **The register file's widths, under one number**: the bound every address of
the file is under, and the number of registers. -/
noncomputable abbrev regWidthBd : ℕ :=
  regWidthBound (Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')))
    (dt.regBound (A := A) (R' := R') (P' := P'))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
theorem regW_le_bound :
    dt.regW (A := A) (R' := R') (P' := P') ≤ dt.regWidthBd A R' P' := regW_le

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
theorem regWP_le_bound :
    dt.regWP (A := A) (R' := R') (P' := P') ≤ dt.regWidthBd A R' P' := regWP_le

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
theorem regWR_le_bound :
    dt.regWR (A := A) (R' := R') (P' := P') ≤ dt.regWidthBd A R' P' := regWR_le

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
theorem regWK_le_bound :
    dt.regWK (A := A) (R' := R') (P' := P') ≤ dt.regWidthBd A R' P' := regWK_le

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P'] [Finite A]
  [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **The tower's costs at the handed file are polynomial in one number**: the
`IxWidthBd` of `DescriptiveComplexity.Draw.Data.ixLegWidth_le`, at the four
widths the register channel's file is charged; what an instantiation owes of
the clock is again `q ^ 25 ≤ 2 ^ (k · m)`. -/
theorem ixWidthBd_regLaid {q : ℕ} (hq : 16 ≤ q)
    (hwidth : dt.regWidthBd A R' P' ≤ q)
    (hd0 : Nat.card (Lex (Fin dt.dd0 → A)) + 1 ≤ q)
    (heDim : Nat.card (Lex (Fin dt.eDim → A)) + 1 ≤ q)
    (hntg : dt.ntgDim ≤ q) (hnf : dt.nfDim ≤ q)
    (hnat : ∀ vi : dt.VarIx, dt.natOf vi ≤ q)
    (hnIn : ∀ vi : dt.VarIx, dt.nIn vi ≤ q)
    (harOf : ∀ vi : dt.VarIx, dt.arOf vi ≤ q)
    (harity : ∀ iv : dt.d.B.ι, dt.d.B.arity iv ≤ q)
    (hnv : dt.nv ≤ q) :
    dt.IxWidthBd A (dt.regW (A := A) (R' := R') (P' := P'))
      (dt.regWP (A := A) (R' := R') (P' := P'))
      (dt.regWR (A := A) (R' := R') (P' := P'))
      (dt.regWK (A := A) (R' := R') (P' := P')) q where
  cst := hq
  wLe := le_trans (dt.regW_le_bound) hwidth
  wPLe := le_trans (dt.regWP_le_bound) hwidth
  wRLe := le_trans (dt.regWR_le_bound) hwidth
  wKLe := le_trans (dt.regWK_le_bound) hwidth
  dd0Le := hd0
  eDimLe := heDim
  ntgLe := hntg
  nfLe := hnf
  natOfLe := hnat
  nInLe := hnIn
  arOfLe := harOf
  arityLe := harity
  nvLe := hnv

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
variable (A R' P') in
/-- **The file's widths, under a power of two of its register count**: the file
bounds every address by `2 ^ N` at `N` registers, and the widths are quadratic in
that. This is the first of the two places the clock's exponent comes from – the
other is the record's own dimensions. -/
theorem regWidthBd_le_two_pow :
    dt.regWidthBd A R' P' ≤
      2 ^ (4 * Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) + 14) :=
  regWidthBound_le_two_pow _

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **The evaluation's width at the handed file is polynomial in one number**:
`DescriptiveComplexity.Draw.Data.ixEvalWidth_le` at `ixWidthBd_regLaid`. This
is the `a` of the clock – what one round of the evaluation costs – and what an
instantiation owes is `q ^ 26 ≤ 2 ^ (k · m)`. -/
theorem ixEvalWidth_le_regLaid {q : ℕ} (hq : 16 ≤ q)
    (hwidth : dt.regWidthBd A R' P' ≤ q)
    (hd0 : Nat.card (Lex (Fin dt.dd0 → A)) + 1 ≤ q)
    (heDim : Nat.card (Lex (Fin dt.eDim → A)) + 1 ≤ q)
    (hntg : dt.ntgDim ≤ q) (hnf : dt.nfDim ≤ q)
    (hnat : ∀ vi : dt.VarIx, dt.natOf vi ≤ q)
    (hnIn : ∀ vi : dt.VarIx, dt.nIn vi ≤ q)
    (harOf : ∀ vi : dt.VarIx, dt.arOf vi ≤ q)
    (harity : ∀ iv : dt.d.B.ι, dt.d.B.arity iv ≤ q)
    (hnv : dt.nv ≤ q) :
    dt.ixEvalWidth A (dt.regW (A := A) (R' := R') (P' := P'))
        (dt.regWP (A := A) (R' := R') (P' := P'))
        (dt.regWR (A := A) (R' := R') (P' := P'))
        (dt.regWK (A := A) (R' := R') (P' := P')) ≤ q ^ 26 :=
  ixEvalWidth_le (dt.ixWidthBd_regLaid hq hwidth hd0 heDim hntg hnf hnat hnIn
    harOf harity hnv)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **The evaluation's width, as a power of two**: `ixEvalWidth_le_regLaid` read
against the clock, which compares with `2 ^ (k · m)` and not with a
polynomial. A number is below the next power of two above it
(`Nat.lt_pow_succ_log_self`), so twenty-six of them are below its twenty-sixth,
and that is the exponent `w` a reduction hands the clock. -/
theorem ixEvalWidth_le_two_pow_regLaid {q : ℕ} (hq : 16 ≤ q)
    (hwidth : dt.regWidthBd A R' P' ≤ q)
    (hd0 : Nat.card (Lex (Fin dt.dd0 → A)) + 1 ≤ q)
    (heDim : Nat.card (Lex (Fin dt.eDim → A)) + 1 ≤ q)
    (hntg : dt.ntgDim ≤ q) (hnf : dt.nfDim ≤ q)
    (hnat : ∀ vi : dt.VarIx, dt.natOf vi ≤ q)
    (hnIn : ∀ vi : dt.VarIx, dt.nIn vi ≤ q)
    (harOf : ∀ vi : dt.VarIx, dt.arOf vi ≤ q)
    (harity : ∀ iv : dt.d.B.ι, dt.d.B.arity iv ≤ q)
    (hnv : dt.nv ≤ q) :
    dt.ixEvalWidth A (dt.regW (A := A) (R' := R') (P' := P'))
        (dt.regWP (A := A) (R' := R') (P' := P'))
        (dt.regWR (A := A) (R' := R') (P' := P'))
        (dt.regWK (A := A) (R' := R') (P' := P')) ≤
      2 ^ (26 * (Nat.log 2 q + 1)) := by
  refine le_trans (dt.ixEvalWidth_le_regLaid hq hwidth hd0 heDim hntg hnf hnat
    hnIn harOf harity hnv) ?_
  have hlt : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by omega) q
  calc q ^ 26 ≤ (2 ^ (Nat.log 2 q + 1)) ^ 26 :=
        Nat.pow_le_pow_left (le_of_lt hlt) 26
    _ = 2 ^ (26 * (Nat.log 2 q + 1)) := by
        rw [← pow_mul, Nat.mul_comm]

/-- **The dimensions that do not depend on the instance**: the tag and formula
budgets, the number of variables, and the atom, gate, argument and arity counts.
They are the kernel's own, so a clock's exponent carries them as an additive
constant. -/
noncomputable def dimC : ℕ :=
  max dt.ntgDim (max dt.nfDim (max dt.nv
    (max (⨆ vi : dt.VarIx, max (dt.natOf vi) (max (dt.nIn vi) (dt.arOf vi)))
      (⨆ iv : dt.d.B.ι, dt.d.B.arity iv))))

variable (A R' P') in
/-- **One number dominating every dimension the width bound compares against**:
the pass widths, the two tuple counts, and the kernel's own dimensions
(`dimC`). It is a maximum and nothing else, so each of the ten comparisons
`ixEvalWidth_le_regLaid` asks for is one `le_max` away. -/
noncomputable def evalQ : ℕ :=
  max 16 (max (dt.regWidthBd A R' P')
    (max (Nat.card (Lex (Fin dt.dd0 → A)) + 1)
      (max (Nat.card (Lex (Fin dt.eDim → A)) + 1) dt.dimC)))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **The evaluation's width at the handed file, with nothing to discharge**:
`ixEvalWidth_le_two_pow_regLaid` at `evalQ`, whose ten comparisons hold by
construction. This is the `w` of the clock, and it mentions the record alone. -/
theorem ixEvalWidth_le_two_pow_evalQ :
    dt.ixEvalWidth A (dt.regW (A := A) (R' := R') (P' := P'))
        (dt.regWP (A := A) (R' := R') (P' := P'))
        (dt.regWR (A := A) (R' := R') (P' := P'))
        (dt.regWK (A := A) (R' := R') (P' := P')) ≤
      2 ^ (26 * (Nat.log 2 (dt.evalQ A R' P') + 1)) := by
  classical
  have hsupV : ∀ vi : dt.VarIx,
      max (dt.natOf vi) (max (dt.nIn vi) (dt.arOf vi)) ≤
        ⨆ vi : dt.VarIx, max (dt.natOf vi) (max (dt.nIn vi) (dt.arOf vi)) := by
    intro vi
    exact le_ciSup (f := fun vi : dt.VarIx =>
        max (dt.natOf vi) (max (dt.nIn vi) (dt.arOf vi)))
      (Set.Finite.bddAbove (Set.finite_range _)) vi
  have hsupI : ∀ iv : dt.d.B.ι,
      dt.d.B.arity iv ≤ ⨆ iv : dt.d.B.ι, dt.d.B.arity iv := by
    intro iv
    exact le_ciSup (f := fun iv : dt.d.B.ι => dt.d.B.arity iv)
      (Set.Finite.bddAbove (Set.finite_range _)) iv
  have h16 : 16 ≤ dt.evalQ A R' P' := le_max_left _ _
  have hW : dt.regWidthBd A R' P' ≤ dt.evalQ A R' P' :=
    le_max_of_le_right (le_max_left _ _)
  have hD0 : Nat.card (Lex (Fin dt.dd0 → A)) + 1 ≤ dt.evalQ A R' P' :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hE : Nat.card (Lex (Fin dt.eDim → A)) + 1 ≤ dt.evalQ A R' P' :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hC : dt.dimC ≤ dt.evalQ A R' P' :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  have hNTG : dt.ntgDim ≤ dt.evalQ A R' P' := le_trans (le_max_left _ _) hC
  have hNF : dt.nfDim ≤ dt.evalQ A R' P' :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hNV : dt.nv ≤ dt.evalQ A R' P' :=
    le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hC
  have hSV : (⨆ vi : dt.VarIx, max (dt.natOf vi) (max (dt.nIn vi) (dt.arOf vi))) ≤
      dt.evalQ A R' P' :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hC
  have hSI : (⨆ iv : dt.d.B.ι, dt.d.B.arity iv) ≤ dt.evalQ A R' P' :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hC
  exact dt.ixEvalWidth_le_two_pow_regLaid h16 hW hD0 hE hNTG hNF
    (fun vi => le_trans (le_trans (le_max_left _ _) (hsupV vi)) hSV)
    (fun vi => le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (hsupV vi)) hSV)
    (fun vi => le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (hsupV vi)) hSV)
    (fun iv => le_trans (hsupI iv) hSI) hNV

end Laid

/-! ### The two bridges at the handed file

`DescriptiveComplexity.Draw.Data.passEnc_regLaid` and `gateEnc_regLaid`
discharge the gates' bridges at the file the channel hands over. The generic
lemmas they come from ask only that the registers stand for distinct elements,
that the layout order is linear, and that a register's block and tuple are its
element's – all of which the handed file has. -/

section Bridges

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] [Nonempty A]
variable [L.IsRelational] [L.Structure A]
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite (Univ A R' P' dt.KIx dt.dd)]
variable {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)

omit [L.IsRelational] [Finite (Univ A R' P' dt.KIx dt.dd)] in
/-- **The inner gates' bridge at the handed file**: `hpassEnc`, discharged. -/
theorem passEnc_regLaid (hzo : PR.zero ≠ PR.one) (vi : dt.VarIx)
    (stV : TapeSt dt A R' P' (dt.RegIx (A := A) (R' := R') (P' := P')))
    (ℓ : Fin (dt.nIn vi)) :
    dt.ixIGPassP (elt := fun u : dt.RegIx (A := A) (R' := R') (P' := P') => (u.1 : _))
        (dt.regLaid h hord) PR.zero PR.one vi stV ℓ ↔
      IsEnc dt.ly PR.zero PR.one
        (wmBlk (ixAddr (fun u : dt.RegIx (A := A) (R' := R') (P' := P') => (u.1 : _)) stV.val)
          (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R' P' dt.KIx)) :=
  dt.ixIGPassP_iff_isEnc (F := dt.regLaid h hord) Subtype.val_injective
    isLinOrd_regLaid_le (fun u => dt.blk_regLaid_eq_tagBlk u) (fun _ => rfl) hzo vi stV ℓ

omit [L.IsRelational] in
/-- **The gates' bridge at the handed file**: `hgateEnc`, discharged. -/
theorem gateEnc_regLaid (hzo : PR.zero ≠ PR.one) (j : Fin dt.nv)
    (st : TapeSt dt A R' P' (dt.RegIx (A := A) (R' := R') (P' := P'))) :
    dt.ixGatedAt (PR := PR)
        (elt := fun u : dt.RegIx (A := A) (R' := R') (P' := P') => (u.1 : _))
        (F := dt.regLaid h hord) j st ↔
      ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        IsEnc dt.ly PR.zero PR.one
          (wmBlk (ixAddr (fun u : dt.RegIx (A := A) (R' := R') (P' := P') => (u.1 : _)) st.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) : Tag R' P' dt.KIx)) :=
  dt.ixGatedAt_iff_isEnc (F := dt.regLaid h hord) Subtype.val_injective
    isLinOrd_regLaid_le (fun u => dt.blk_regLaid_eq_tagBlk u) (wmSegFile h)
    (fun _ => rfl) hzo h j st

end Bridges

/-! ### The evaluation itself -/

section Eval

variable {L : Language.{0, 0}} (dt : Data L) {A R B : Type}
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

variable (A R B) in
/-- **The handed file's index at the clocked phases**. -/
abbrev NexRegIx : Type :=
  dt.RegIx (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF))

variable (A R B) in
/-- **The element a register stands for**: itself. -/
abbrev regElt (u : dt.NexRegIx A R B) :
    Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd := u.1

variable (A R B) in
/-- The handed file's four widths, at the clocked phases. -/
noncomputable abbrev nexRegW : ℕ := dt.regW (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF))

variable (A R B) in
@[inherit_doc nexRegW]
noncomputable abbrev nexRegWP : ℕ :=
  dt.regWP (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF))

variable (A R B) in
@[inherit_doc nexRegW]
noncomputable abbrev nexRegWR : ℕ :=
  dt.regWR (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF))

variable (A R B) in
@[inherit_doc nexRegW]
noncomputable abbrev nexRegWK : ℕ :=
  dt.regWK (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (NexPh B (EvalPh dt.nv dt.PMF))] [Finite A] [Finite R]
  [Finite (NexPh B (EvalPh dt.nv dt.PMF))]
  [Finite (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] [Nonempty A]
  [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
variable (A R B) in
/-- **Distinct registers stand for distinct elements.** -/
theorem regElt_injective : Function.Injective (dt.regElt A R B) := Subtype.val_injective

/-- **The clocked evaluation at the handed file**: the walk-back the opening's
dispatch owes, the branched spine over the spine's positions, and the exit into
the accepting phase, charged the handed file's own widths. This is
`DescriptiveComplexity.Draw.Data.nexIxEvalB_reachesIn` with every coherence of
the register channel's file discharged; what is left is the program's own, and
what the *reduction* still owes is its marking – the arguments, one element
below them, and nothing else. -/
theorem nexIxEvalB_regLaid_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
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
    -- What the reduction owes its own marking: every argument element carries an
    -- input symbol, one further element below them does too, and nothing else
    -- does. Together these put the file directly above the working area.
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hargall : ∀ x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      (∃ i : dt.KIx, x.1 = Tag.arg i) → WMHasInp x)
    (hupinp : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y → WMHasInp x → WMHasInp y)
    {bot : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd} (hbotm : WMHasInp bot)
    (hleast : ∀ y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp y → WMLe bot y)
    (hbotarg : ∀ i : dt.KIx, bot.1 ≠ Tag.arg i)
    -- The file's two ends (`exists_regTop`, `exists_regBot`).
    (gtop gbot : dt.NexRegIx A R B)
    (htopF : ∀ u, (dt.regLaid h hord).le u gtop)
    (hbotF : ∀ u, (dt.regLaid h hord).le gbot u)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.regLaid h hord).cell gbot))
    -- The marker is a *logical* address, so the registers of the file hold it.
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → dt.NexRegIx A R B → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.regLaid h hord).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.regLaid h hord).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.regLaid h hord).blk (mV a) u)
    (stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).mir = ixMark (dt.regElt A R B) v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv),
      dt.ixGatedAt (PR := PR) (elt := dt.regElt A R B)
        (F := dt.regLaid h hord) j (stOf j.castSucc) →
      ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF))
          (dt.NexRegIx A R B)) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := dt.regElt A R B)
          (dt.regLaid h hord) PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := dt.regElt A R B)
            (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v (b : ℕ))
          (dt.regElt A R B) (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStB (PR := PR) (v := v)
        (elt := dt.regElt A R B) (aT := aT)
        (dt.regLaid h hord) (dt.regElt_injective A R B)
        (dt.hasName_regLaid PR.zero harg)
        (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlB (PR := PR) (v := v)
        (elt := dt.regElt A R B) (aT := aT)
        (dt.regLaid h hord) (dt.regElt_injective A R B)
        (dt.hasName_regLaid PR.zero harg)
        (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
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
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → dt.NexRegIx A R B → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
        (u : dt.NexRegIx A R B),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt (dt.regLaid h hord).cell Slot.mir
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
            (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).mir ((dt.regLaid h hord).cell u)) ↔
        TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr (dt.regElt A R B)
          (stOf (Fin.last dt.nv)).mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmirL : (stOf (Fin.last dt.nv)).mir =
      ixMark (dt.regElt A R B) v)
    (hbotL : (stOf (Fin.last dt.nv)).bot = fun r => r = (fun _ => False))
    (hsavL : (stOf (Fin.last dt.nv)).sav =
      ixMark (dt.regElt A R B) v)
    (htgtL : (stOf (Fin.last dt.nv)).tgt =
      ixMark (dt.regElt A R B) v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := dt.regElt A R B)
          (dt.regLaid h hord) PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a))
          (dt.regElt A R B) (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr (dt.regElt A R B)
              (stOf (Fin.last dt.nv)).mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (hacc : (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.ixOutCtl (elt := dt.regElt A R B)
        (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
        (dt.hasName_regLaid PR.zero harg)
        (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
        mV (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))) :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (dt.nexRegW A R B)
        (dt.nexRegWP A R B)
        (dt.nexRegWR A R B)
        (dt.nexRegWK A R B)
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (dt.nexRegW A R B)
          (dt.nexRegWP A R B)
          (dt.nexRegWR A R B)
          (dt.nexRegWK A R B)
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
            (stOf 0)) (stOf 0).val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.acceptP
          (dt.ixOutCtl (elt := dt.regElt A R B)
            (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
            (dt.hasName_regLaid PR.zero harg)
            (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
            mV (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))),
        Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV aT))) (mV aT))
          (PR.syElt PR.blank)⟩ :=
  dt.nexIxEvalOutB_reachesIn (F := dt.regLaid h hord)
    (elt := dt.regElt A R B)
    (hinj := (dt.regElt_injective A R B))
    (hhasP := dt.hasName_regLaid PR.zero harg)
    (heltP := fun b c => dt.elt_reg_regLaid PR.zero harg b c)
    (hsepP := dt.nameSep_regLaid PR.zero dt.dd0Le)
    (hix := isLinOrd_regLaid_le)
    (he₀ := he₀) (hord := hord) (hrules := hrules) (hR := hR) (hlin := h)
    (gtop := gtop) (gbot := gbot) (htop := htopF) (hbot := hbotF)
    (hwork := fun hg u => dt.work_regLaid hbotm hleast hbotarg hg u)
    (hv := hv) (hvi := hvi)
    (Use := dt.RegUse (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF)))
    (hmono := fun u u' => dt.mono_regLaid u u')
    (hup := fun _ _ hu hlt => dt.up_regLaid (hord := hord) hargall hu hlt)
    (hvh := dt.ixHolds_regLaid hargall hvlog)
    (hxdUse := fun _ _ => dt.regUse_reg_regLaid PR.zero harg _ _)
    (wG := dt.regBound (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF)))
    (hgap := fun u u' _ => dt.gap_regLaid h hord hupinp u u')
    (hwP := dt.hwP_regLaid h hord hupinp gtop gbot)
    (hwR := fun s hs => dt.hwR_regLaid h hord hupinp _ s hs)
    (hwK := fun T hT => dt.hwK_regLaid h hord hupinp gtop gbot T hT)
    (hcostR := fun b c => dt.hcostR_regLaid h hord hupinp PR.zero harg v b c)
    (hbotV := hbotV) (htopV := htopV) (mV := mV) (hmV0 := hmV0) (hIncr := hIncr)
    (hTestT := hTestT) (hTestF := hTestF) (stOf := stOf) (fsOf := fsOf)
    (hwkOf := hwkOf) (hmirOf := hmirOf) (hbotOf := hbotOf) (semTJ := semTJ)
    (hst := hst) (hfs := hfs) (hrulesOut := hrulesOut) (TestOf := TestOf)
    (hcompatOf := hcompatOf) (tOf := tOf) (hwitOf := hwitOf) (hmirL := hmirL)
    (hbotL := hbotL) (hsavL := hsavL) (htgtL := htgtL) (semOf := semOf)
    (hDom := hDom) (hTestOf := hTestOf) (hacc := hacc)

open Classical in
/-- **The clocked evaluation at the handed file, whatever the verdict**:
`nexIxEvalB_regLaid_reachesIn` with the verdict not assumed
(`nexIxEvalOutB_any_reachesIn`). -/
theorem nexIxEvalB_regLaid_any_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
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
    -- What the reduction owes its own marking: every argument element carries an
    -- input symbol, one further element below them does too, and nothing else
    -- does. Together these put the file directly above the working area.
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hargall : ∀ x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      (∃ i : dt.KIx, x.1 = Tag.arg i) → WMHasInp x)
    (hupinp : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y → WMHasInp x → WMHasInp y)
    {bot : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd} (hbotm : WMHasInp bot)
    (hleast : ∀ y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp y → WMLe bot y)
    (hbotarg : ∀ i : dt.KIx, bot.1 ≠ Tag.arg i)
    -- The file's two ends (`exists_regTop`, `exists_regBot`).
    (gtop gbot : dt.NexRegIx A R B)
    (htopF : ∀ u, (dt.regLaid h hord).le u gtop)
    (hbotF : ∀ u, (dt.regLaid h hord).le gbot u)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.regLaid h hord).cell gbot))
    -- The marker is a *logical* address, so the registers of the file hold it.
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → dt.NexRegIx A R B → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.regLaid h hord).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.regLaid h hord).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.regLaid h hord).blk (mV a) u)
    (stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).mir = ixMark (dt.regElt A R B) v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv),
      dt.ixGatedAt (PR := PR) (elt := dt.regElt A R B)
        (F := dt.regLaid h hord) j (stOf j.castSucc) →
      ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF))
          (dt.NexRegIx A R B)) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := dt.regElt A R B)
          (dt.regLaid h hord) PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := dt.regElt A R B)
            (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v (b : ℕ))
          (dt.regElt A R B) (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStB (PR := PR) (v := v)
        (elt := dt.regElt A R B) (aT := aT)
        (dt.regLaid h hord) (dt.regElt_injective A R B)
        (dt.hasName_regLaid PR.zero harg)
        (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlB (PR := PR) (v := v)
        (elt := dt.regElt A R B) (aT := aT)
        (dt.regLaid h hord) (dt.regElt_injective A R B)
        (dt.hasName_regLaid PR.zero harg)
        (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
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
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → dt.NexRegIx A R B → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
        (u : dt.NexRegIx A R B),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt (dt.regLaid h hord).cell Slot.mir
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
            (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).mir ((dt.regLaid h hord).cell u)) ↔
        TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr (dt.regElt A R B)
          (stOf (Fin.last dt.nv)).mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmirL : (stOf (Fin.last dt.nv)).mir =
      ixMark (dt.regElt A R B) v)
    (hbotL : (stOf (Fin.last dt.nv)).bot = fun r => r = (fun _ => False))
    (hsavL : (stOf (Fin.last dt.nv)).sav =
      ixMark (dt.regElt A R B) v)
    (htgtL : (stOf (Fin.last dt.nv)).tgt =
      ixMark (dt.regElt A R B) v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := dt.regElt A R B)
          (dt.regLaid h hord) PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a))
          (dt.regElt A R B) (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr (dt.regElt A R B)
              (stOf (Fin.last dt.nv)).mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (dt.nexRegW A R B)
        (dt.nexRegWP A R B)
        (dt.nexRegWR A R B)
        (dt.nexRegWK A R B)
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (dt.nexRegW A R B)
          (dt.nexRegWP A R B)
          (dt.nexRegWR A R B)
          (dt.nexRegWK A R B)
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
            (stOf 0)) (stOf 0).val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.acceptP
          (dt.ixOutCtl (elt := dt.regElt A R B)
            (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
            (dt.hasName_regLaid PR.zero harg)
            (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
            mV (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))),
        Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (fun r => if r = v then
              Function.update
                (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
                  (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV aT)) v)
                (dt.varArgsOf PR.zero PR.one none).newSlot
                (bitVal PR.zero PR.one
                  ((dt.varArgsOf PR.zero PR.one none).accBit
                    (dt.ixOutCtl (elt := dt.regElt A R B) (v := v) (aT := aT)
                      (dt.regLaid h hord) (dt.regElt_injective A R B)
                      (dt.hasName_regLaid PR.zero harg)
                      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
                      mV (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))))
            else dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
              (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV aT)) r) (mV aT))
          (PR.syElt PR.blank)⟩ :=
  dt.nexIxEvalOutB_any_reachesIn (F := dt.regLaid h hord)
    (elt := dt.regElt A R B)
    (hinj := (dt.regElt_injective A R B))
    (hhasP := dt.hasName_regLaid PR.zero harg)
    (heltP := fun b c => dt.elt_reg_regLaid PR.zero harg b c)
    (hsepP := dt.nameSep_regLaid PR.zero dt.dd0Le)
    (hix := isLinOrd_regLaid_le)
    (he₀ := he₀) (hord := hord) (hrules := hrules) (hR := hR) (hlin := h)
    (gtop := gtop) (gbot := gbot) (htop := htopF) (hbot := hbotF)
    (hwork := fun hg u => dt.work_regLaid hbotm hleast hbotarg hg u)
    (hv := hv) (hvi := hvi)
    (Use := dt.RegUse (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF)))
    (hmono := fun u u' => dt.mono_regLaid u u')
    (hup := fun _ _ hu hlt => dt.up_regLaid (hord := hord) hargall hu hlt)
    (hvh := dt.ixHolds_regLaid hargall hvlog)
    (hxdUse := fun _ _ => dt.regUse_reg_regLaid PR.zero harg _ _)
    (wG := dt.regBound (A := A) (R' := R) (P' := NexPh B (EvalPh dt.nv dt.PMF)))
    (hgap := fun u u' _ => dt.gap_regLaid h hord hupinp u u')
    (hwP := dt.hwP_regLaid h hord hupinp gtop gbot)
    (hwR := fun s hs => dt.hwR_regLaid h hord hupinp _ s hs)
    (hwK := fun T hT => dt.hwK_regLaid h hord hupinp gtop gbot T hT)
    (hcostR := fun b c => dt.hcostR_regLaid h hord hupinp PR.zero harg v b c)
    (hbotV := hbotV) (htopV := htopV) (mV := mV) (hmV0 := hmV0) (hIncr := hIncr)
    (hTestT := hTestT) (hTestF := hTestF) (stOf := stOf) (fsOf := fsOf)
    (hwkOf := hwkOf) (hmirOf := hmirOf) (hbotOf := hbotOf) (semTJ := semTJ)
    (hst := hst) (hfs := hfs) (hrulesOut := hrulesOut) (TestOf := TestOf)
    (hcompatOf := hcompatOf) (tOf := tOf) (hwitOf := hwitOf) (hmirL := hmirL)
    (hbotL := hbotL) (hsavL := hsavL) (htgtL := htgtL) (semOf := semOf)
    (hDom := hDom) (hTestOf := hTestOf)

/-! ### The thread, and the run from the sentence alone -/

section Thread

/-- **The packs at the handed file, built**: the conditioned family the branched
thread takes as a parameter, from the gates' bridge and the inner gates'
(`gateEnc_regLaid`, `passEnc_regLaid`) rather than assumed. -/
noncomputable def regGatedSem
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    (hzo : PR.zero ≠ PR.one)
    {ιV : Type} (mV : ιV → dt.NexRegIx A R B → Prop) :
    ∀ (w : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
      (j : Fin dt.nv)
      (st : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B)),
    dt.ixGatedAt (PR := PR) (elt := dt.regElt A R B)
      (F := dt.regLaid h hord) j st →
    ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF))
        (dt.NexRegIx A R B)) (a : ιV),
    (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := dt.regElt A R B)
        (dt.regLaid h hord) PR.zero PR.one (dt.varAt j)
        (dt.ixVarRdSt st p (mV a)) ℓ) →
    ∀ b : Fin (dt.natOf (dt.varAt j)),
      dt.IxKindSem PR.zero PR.one (dt.varAt j)
        (dt.ixMatSt (elt := dt.regElt A R B)
          (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
        (dt.regElt A R B) (dt.kindOf (dt.varAt j) b) :=
  fun w j st hg p a hp b =>
    dt.ixGatedSem (elt := dt.regElt A R B)
      (dt.regLaid h hord)
      (fun vi stV ℓ => dt.passEnc_regLaid h hord hzo vi stV ℓ)
      (fun j' st' => dt.gateEnc_regLaid h hord hzo j' st')
      hzo h mV (v := w) j st hg p a hp b

/-- **The clocked evaluation at the handed file, with its thread**: the same run
as `nexIxEvalB_regLaid_reachesIn` with the tape and control families
*constructed* – the branched thread at the packs the bridges build – so that a
program has only to name the state it enters the evaluation in. -/
theorem nexIxEvalB_regLaid_thread_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
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
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hargall : ∀ x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      (∃ i : dt.KIx, x.1 = Tag.arg i) → WMHasInp x)
    (hupinp : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y → WMHasInp x → WMHasInp y)
    {bot : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd} (hbotm : WMHasInp bot)
    (hleast : ∀ y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp y → WMLe bot y)
    (hbotarg : ∀ i : dt.KIx, bot.1 ≠ Tag.arg i)
    (gtop gbot : dt.NexRegIx A R B)
    (htopF : ∀ u, (dt.regLaid h hord).le u gtop)
    (hbotF : ∀ u, (dt.regLaid h hord).le gbot u)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.regLaid h hord).cell gbot))
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → dt.NexRegIx A R B → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.regLaid h hord).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.regLaid h hord).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.regLaid h hord).blk (mV a) u)
    (st₀ : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (f₀ : dt.CtlIx → A)
    (hwk₀ : st₀.wk = fun r => r = v)
    (hmir₀ : st₀.mir = ixMark (dt.regElt A R B) v)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    -- The state and the control the thread ends in, named so that the output's
    -- leg can be spoken of without spelling the thread out again.
    (stL : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV) (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV) (Fin.last dt.nv))
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → dt.NexRegIx A R B → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
        (u : dt.NexRegIx A R B),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt (dt.regLaid h hord).cell Slot.mir
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le stL)
          stL.mir ((dt.regLaid h hord).cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr (dt.regElt A R B) stL.mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmirL : stL.mir = ixMark (dt.regElt A R B) v)
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (dt.regElt A R B) v)
    (htgtL : stL.tgt = ixMark (dt.regElt A R B) v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := dt.regElt A R B)
          (dt.regLaid h hord) PR.zero PR.one none
          (dt.ixRoundSt stL (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none (dt.ixRoundSt stL (mV a))
          (dt.regElt A R B) (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr (dt.regElt A R B) stL.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (hacc : (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.ixOutCtl (elt := dt.regElt A R B)
        (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
        (dt.hasName_regLaid PR.zero harg)
        (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
        mV stL tOf semOf fsL)) :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (dt.nexRegW A R B)
        (dt.nexRegWP A R B)
        (dt.nexRegWR A R B)
        (dt.nexRegWK A R B)
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (dt.nexRegW A R B)
          (dt.nexRegWP A R B)
          (dt.nexRegWR A R B)
          (dt.nexRegWK A R B)
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le st₀)
          st₀.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.acceptP
          (dt.ixOutCtl (elt := dt.regElt A R B)
            (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
            (dt.hasName_regLaid PR.zero harg)
            (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
            mV stL tOf semOf fsL)),
        Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt stL (mV aT))) (mV aT)) (PR.syElt PR.blank)⟩ := by
  subst hstL
  subst hfsL
  exact dt.nexIxEvalB_regLaid_reachesIn h hrules hR hord he₀ harg hargall hupinp hbotm
    hleast hbotarg gtop gbot htopF hbotF hv hvlog hvi
    hbotV htopV mV hmV0 hIncr hTestT hTestF
    (stOf := dt.ixSpineStOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV))
    (fsOf := dt.ixSpineFsOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV))
    (hwkOf := fun k => (dt.ixSpineStOfB_wk (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ k).trans hwk₀)
    (hmirOf := fun j => (dt.ixSpineStOfB_mir (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j.castSucc).trans hmir₀)
    (hbotOf := fun j => (dt.ixSpineStOfB_bot (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j.castSucc).trans hbot₀)
    (semTJ := fun j => dt.ixSpineSemOfB (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hst := fun j => dt.ixSpineStOfB_succ (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hfs := fun j => dt.ixSpineFsOfB_succ (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hrulesOut := hrulesOut) (TestOf := TestOf) (hcompatOf := hcompatOf)
    (tOf := tOf) (hwitOf := hwitOf) (hmirL := hmirL) (hbotL := hbotL)
    (hsavL := hsavL) (htgtL := htgtL) (semOf := semOf) (hDom := hDom)
    (hTestOf := hTestOf) (hacc := hacc)

open Classical in
/-- **The clocked evaluation at the handed file, with its thread, whatever the
verdict**: the same run
as `nexIxEvalB_regLaid_reachesIn` with the tape and control families
*constructed* – the branched thread at the packs the bridges build – so that a
program has only to name the state it enters the evaluation in. -/
theorem nexIxEvalB_regLaid_thread_any_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
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
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hargall : ∀ x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      (∃ i : dt.KIx, x.1 = Tag.arg i) → WMHasInp x)
    (hupinp : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y → WMHasInp x → WMHasInp y)
    {bot : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd} (hbotm : WMHasInp bot)
    (hleast : ∀ y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp y → WMLe bot y)
    (hbotarg : ∀ i : dt.KIx, bot.1 ≠ Tag.arg i)
    (gtop gbot : dt.NexRegIx A R B)
    (htopF : ∀ u, (dt.regLaid h hord).le u gtop)
    (hbotF : ∀ u, (dt.regLaid h hord).le gbot u)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.regLaid h hord).cell gbot))
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → dt.NexRegIx A R B → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.regLaid h hord).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.regLaid h hord).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.regLaid h hord).blk (mV a) u)
    (st₀ : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (f₀ : dt.CtlIx → A)
    (hwk₀ : st₀.wk = fun r => r = v)
    (hmir₀ : st₀.mir = ixMark (dt.regElt A R B) v)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    -- The state and the control the thread ends in, named so that the output's
    -- leg can be spoken of without spelling the thread out again.
    (stL : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV) (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV) (Fin.last dt.nv))
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → dt.NexRegIx A R B → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
        (u : dt.NexRegIx A R B),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt (dt.regLaid h hord).cell Slot.mir
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le stL)
          stL.mir ((dt.regLaid h hord).cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr (dt.regElt A R B) stL.mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmirL : stL.mir = ixMark (dt.regElt A R B) v)
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (dt.regElt A R B) v)
    (htgtL : stL.tgt = ixMark (dt.regElt A R B) v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := dt.regElt A R B)
          (dt.regLaid h hord) PR.zero PR.one none
          (dt.ixRoundSt stL (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none (dt.ixRoundSt stL (mV a))
          (dt.regElt A R B) (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr (dt.regElt A R B) stL.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (dt.nexRegW A R B)
        (dt.nexRegWP A R B)
        (dt.nexRegWR A R B)
        (dt.nexRegWK A R B)
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (dt.nexRegW A R B)
          (dt.nexRegWP A R B)
          (dt.nexRegWR A R B)
          (dt.nexRegWK A R B)
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le st₀)
          st₀.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.acceptP
          (dt.ixOutCtl (elt := dt.regElt A R B)
            (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
            (dt.hasName_regLaid PR.zero harg)
            (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
            mV stL tOf semOf fsL)),
        Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (fun r => if r = v then
              Function.update
                (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
                  (dt.ixRoundSt stL (mV aT)) v)
                (dt.varArgsOf PR.zero PR.one none).newSlot
                (bitVal PR.zero PR.one
                  ((dt.varArgsOf PR.zero PR.one none).accBit
                    (dt.ixOutCtl (elt := dt.regElt A R B) (v := v) (aT := aT)
                      (dt.regLaid h hord) (dt.regElt_injective A R B)
                      (dt.hasName_regLaid PR.zero harg)
                      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
                      mV stL tOf semOf fsL)))
            else dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le
              (dt.ixRoundSt stL (mV aT)) r) (mV aT)) (PR.syElt PR.blank)⟩ := by
  subst hstL
  subst hfsL
  exact dt.nexIxEvalB_regLaid_any_reachesIn h hrules hR hord he₀ harg hargall hupinp hbotm
    hleast hbotarg gtop gbot htopF hbotF hv hvlog hvi
    hbotV htopV mV hmV0 hIncr hTestT hTestF
    (stOf := dt.ixSpineStOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV))
    (fsOf := dt.ixSpineFsOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV))
    (hwkOf := fun k => (dt.ixSpineStOfB_wk (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ k).trans hwk₀)
    (hmirOf := fun j => (dt.ixSpineStOfB_mir (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j.castSucc).trans hmir₀)
    (hbotOf := fun j => (dt.ixSpineStOfB_bot (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j.castSucc).trans hbot₀)
    (semTJ := fun j => dt.ixSpineSemOfB (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hst := fun j => dt.ixSpineStOfB_succ (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hfs := fun j => dt.ixSpineFsOfB_succ (elt := dt.regElt A R B) (v := v) (aT := aT)
      _ _ _ _ mV st₀ f₀ _ j)
    (hrulesOut := hrulesOut) (TestOf := TestOf) (hcompatOf := hcompatOf)
    (tOf := tOf) (hwitOf := hwitOf) (hmirL := hmirL) (hbotL := hbotL)
    (hsavL := hsavL) (htgtL := htgtL) (semOf := semOf) (hDom := hDom)
    (hTestOf := hTestOf)

section Realize

variable [LinearOrder (dt.X.Map A)]

/-- **The clocked evaluation at the handed file, from the sentence alone**: the
run above with the output's leg discharged. The output variable is *nullary*, so
everything its leg asks about argument blocks is vacuous – there are none – and
the one thing left is its verdict, which `ixOutAcc_iff_out` reads as the
expansion's output sentence at the stage the tracks hold. So what a program has
to bring to its own evaluation is the entry state, the enumeration, the stage
its guess wrote, and the sentence being true. -/
theorem nexIxEvalOut_regLaid_realize_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
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
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hargall : ∀ x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      (∃ i : dt.KIx, x.1 = Tag.arg i) → WMHasInp x)
    (hupinp : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y → WMHasInp x → WMHasInp y)
    {bot : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd} (hbotm : WMHasInp bot)
    (hleast : ∀ y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp y → WMLe bot y)
    (hbotarg : ∀ i : dt.KIx, bot.1 ≠ Tag.arg i)
    (gtop gbot : dt.NexRegIx A R B)
    (htopF : ∀ u, (dt.regLaid h hord).le u gtop)
    (hbotF : ∀ u, (dt.regLaid h hord).le gbot u)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.regLaid h hord).cell gbot))
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → dt.NexRegIx A R B → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.regLaid h hord).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.regLaid h hord).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.regLaid h hord).blk (mV a) u)
    (st₀ : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (f₀ : dt.CtlIx → A)
    (hwk₀ : st₀.wk = fun r => r = v)
    (hmir₀ : st₀.mir = ixMark (dt.regElt A R B) v)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    (stL : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV) (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV) (Fin.last dt.nv))
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (hmirL : stL.mir = ixMark (dt.regElt A R B) v)
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (dt.regElt A R B) v)
    (htgtL : stL.tgt = ixMark (dt.regElt A R B) v)
    -- What the verdict is read against: the stage the guess wrote, the
    -- enumeration's own facts, and the order on the expanded universe.
    {Use : dt.NexRegIx A R B → Prop}
    (hUse : ∀ (a : ιV) (u : dt.NexRegIx A R B), mV a u → Use u)
    (hmono : ∀ u u', WMLt (dt.regLaid h hord).le u u' ↔
      WMLt WMLe (dt.regElt A R B u)
        (dt.regElt A R B u'))
    (hup : ∀ (u : dt.NexRegIx A R B)
        (x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      Use u → WMLt WMLe (dt.regElt A R B u) x →
      ∃ u', Use u' ∧ dt.regElt A R B u' = x)
    (hKin : ∀ (a : ιV) (t : Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (w : Fin dt.dd → A),
      ixAddr (dt.regElt A R B) (mV a) (t, w) →
        ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1)
      (ixAddr (dt.regElt A R B) (mV aT)) u)
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
      Below (ixAddr (dt.regElt A R B)
        (dt.ixStageTgt (dt.regLaid h hord) (dt.hasName_regLaid PR.zero harg)
          none ts
          { dt.ixRoundSt stL (mV a) with
            sav := ixMark (dt.regElt A R B) v }
          (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hout : @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out) :
    ∃ (fq : dt.CtlIx → A) (cT : Config (WPoint (Univ A R
      (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))),
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (dt.nexRegW A R B)
        (dt.nexRegWP A R B)
        (dt.nexRegWR A R B)
        (dt.nexRegWK A R B)
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (dt.nexRegW A R B)
          (dt.nexRegWP A R B)
          (dt.nexRegWR A R B)
          (dt.nexRegWK A R B)
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le st₀)
          st₀.val) (PR.syElt PR.blank)⟩
      cT ∧ cT.state = Sum.inr (PR.stElt NexPh.acceptP fq) ∧
      (dt.varArgsOf PR.zero PR.one none).accBit fq := by
  have hA := (dt.ixOutAcc_iff_out (elt := dt.regElt A R B)
      (F := dt.regLaid h hord) (hinj := (dt.regElt_injective A R B))
      (hhasP := dt.hasName_regLaid PR.zero harg)
      (heltP := fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      (hix := isLinOrd_regLaid_le)
      (hblkP := (fun u => dt.blk_regLaid_eq_tagBlk u)) (hmono := hmono)
      (hup := hup)
      (hpassEnc := fun vi stV ℓ => dt.passEnc_regLaid h hord hzo vi stV ℓ)
      (mV := mV) (hUse := hUse) (v := v) (hlin := h) (hord := hord)
      (hbotV := hbotV) (hmV0 := hmV0) (hIncr := hIncr) (hKin := hKin)
      (hTop := hTop) (σ := σ) (st := stL) (hdict := hdict) (hbelow := hbelow)
      (hordP := hordP) (tOf := Fin.elim0) (f₀ := fsL)).mpr hout
  exact ⟨_, _, dt.nexIxEvalB_regLaid_thread_reachesIn h hrules hR hzo hord he₀ harg hargall
    hupinp hbotm hleast hbotarg gtop gbot htopF hbotF hv
    hvlog hvi hbotV htopV mV hmV0 hIncr hTestT hTestF st₀ f₀ hwk₀ hmir₀ hbot₀
    stL fsL hstL hfsL (hrulesOut := hrulesOut) (TestOf := fun ℓ _ => ℓ.elim0)
    (hcompatOf := fun ℓ _ => ℓ.elim0) (tOf := Fin.elim0)
    (hwitOf := fun ℓ _ => ℓ.elim0) (hmirL := hmirL) (hbotL := hbotL)
    (hsavL := hsavL) (htgtL := htgtL)
    (semOf := fun a hp b => dt.ixPassSem
      (elt := dt.regElt A R B)
      (F := dt.regLaid h hord)
      (hpassEnc := fun vi stV ℓ => dt.passEnc_regLaid h hord hzo vi stV ℓ)
      none (dt.ixRoundSt stL (mV a)) hp (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) b)
    (hDom := fun ℓ => ℓ.elim0) (hTestOf := fun ℓ _ => ℓ.elim0) (hacc := hA),
    rfl, hA⟩

open Classical in
/-- **The clocked evaluation at the handed file, and the verdict it leaves**:
the run above with the sentence *not* assumed, and the accepting bit read as
what it is – the sentence's own value (`ixOutAcc_iff_out`). A backward reading
uses this: the run exists whatever the verdict, and the bit says which. -/
theorem nexIxEvalOut_regLaid_verdict_reachesIn
    (h : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
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
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hargall : ∀ x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      (∃ i : dt.KIx, x.1 = Tag.arg i) → WMHasInp x)
    (hupinp : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y → WMHasInp x → WMHasInp y)
    {bot : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd} (hbotm : WMHasInp bot)
    (hleast : ∀ y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp y → WMLe bot y)
    (hbotarg : ∀ i : dt.KIx, bot.1 ≠ Tag.arg i)
    (gtop gbot : dt.NexRegIx A R B)
    (htopF : ∀ u, (dt.regLaid h hord).le u gtop)
    (hbotF : ∀ u, (dt.regLaid h hord).le gbot u)
    {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v
      ((dt.regLaid h hord).cell gbot))
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → dt.NexRegIx A R B → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.regLaid h hord).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.regLaid h hord).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.regLaid h hord).blk (mV a) u)
    (st₀ : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (f₀ : dt.CtlIx → A)
    (hwk₀ : st₀.wk = fun r => r = v)
    (hmir₀ : st₀.mir = ixMark (dt.regElt A R B) v)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    (stL : TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) (dt.NexRegIx A R B))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV) (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := dt.regElt A R B)
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A R B)
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSem h hord hzo mV) (Fin.last dt.nv))
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (hmirL : stL.mir = ixMark (dt.regElt A R B) v)
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (dt.regElt A R B) v)
    (htgtL : stL.tgt = ixMark (dt.regElt A R B) v)
    -- What the verdict is read against: the stage the guess wrote, the
    -- enumeration's own facts, and the order on the expanded universe.
    {Use : dt.NexRegIx A R B → Prop}
    (hUse : ∀ (a : ιV) (u : dt.NexRegIx A R B), mV a u → Use u)
    (hmono : ∀ u u', WMLt (dt.regLaid h hord).le u u' ↔
      WMLt WMLe (dt.regElt A R B u)
        (dt.regElt A R B u'))
    (hup : ∀ (u : dt.NexRegIx A R B)
        (x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      Use u → WMLt WMLe (dt.regElt A R B u) x →
      ∃ u', Use u' ∧ dt.regElt A R B u' = x)
    (hKin : ∀ (a : ιV) (t : Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (w : Fin dt.dd → A),
      ixAddr (dt.regElt A R B) (mV a) (t, w) →
        ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1)
      (ixAddr (dt.regElt A R B) (mV aT)) u)
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
      Below (ixAddr (dt.regElt A R B)
        (dt.ixStageTgt (dt.regLaid h hord) (dt.hasName_regLaid PR.zero harg)
          none ts
          { dt.ixRoundSt stL (mV a) with
            sav := ixMark (dt.regElt A R B) v }
          (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    :
    ∃ (fq : dt.CtlIx → A) (cT : Config (WPoint (Univ A R
      (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))),
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (dt.nexRegW A R B)
        (dt.nexRegWP A R B)
        (dt.nexRegWR A R B)
        (dt.nexRegWK A R B)
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (dt.nexRegW A R B)
          (dt.nexRegWP A R B)
          (dt.nexRegWR A R B)
          (dt.nexRegWK A R B)
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one dt.dd0Le st₀)
          st₀.val) (PR.syElt PR.blank)⟩
      cT ∧ cT.state = Sum.inr (PR.stElt NexPh.acceptP fq) ∧
      ((dt.varArgsOf PR.zero PR.one none).accBit fq ↔
        @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out) := by
  have hA := (dt.ixOutAcc_iff_out (elt := dt.regElt A R B)
      (F := dt.regLaid h hord) (hinj := (dt.regElt_injective A R B))
      (hhasP := dt.hasName_regLaid PR.zero harg)
      (heltP := fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      (hix := isLinOrd_regLaid_le)
      (hblkP := (fun u => dt.blk_regLaid_eq_tagBlk u)) (hmono := hmono)
      (hup := hup)
      (hpassEnc := fun vi stV ℓ => dt.passEnc_regLaid h hord hzo vi stV ℓ)
      (mV := mV) (hUse := hUse) (v := v) (hlin := h) (hord := hord)
      (hbotV := hbotV) (hmV0 := hmV0) (hIncr := hIncr) (hKin := hKin)
      (hTop := hTop) (σ := σ) (st := stL) (hdict := hdict) (hbelow := hbelow)
      (hordP := hordP) (tOf := Fin.elim0) (f₀ := fsL))
  exact ⟨_, _, dt.nexIxEvalB_regLaid_thread_any_reachesIn h hrules hR hzo hord he₀ harg hargall
    hupinp hbotm hleast hbotarg gtop gbot htopF hbotF hv
    hvlog hvi hbotV htopV mV hmV0 hIncr hTestT hTestF st₀ f₀ hwk₀ hmir₀ hbot₀
    stL fsL hstL hfsL (hrulesOut := hrulesOut) (TestOf := fun ℓ _ => ℓ.elim0)
    (hcompatOf := fun ℓ _ => ℓ.elim0) (tOf := Fin.elim0)
    (hwitOf := fun ℓ _ => ℓ.elim0) (hmirL := hmirL) (hbotL := hbotL)
    (hsavL := hsavL) (htgtL := htgtL)
    (semOf := fun a hp b => dt.ixPassSem
      (elt := dt.regElt A R B)
      (F := dt.regLaid h hord)
      (hpassEnc := fun vi stV ℓ => dt.passEnc_regLaid h hord hzo vi stV ℓ)
      none (dt.ixRoundSt stL (mV a)) hp (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) b)
    (hDom := fun ℓ => ℓ.elim0) (hTestOf := fun ℓ _ => ℓ.elim0), rfl, hA⟩

end Realize

end Thread

end Eval

end Data

end Draw

end DescriptiveComplexity
