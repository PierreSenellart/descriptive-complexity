/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxEval

/-!
# The evaluation's width is polynomial

The clock of the wide machines compares a *product*: the evaluation is charged
`a * b` with `a` a width and `b` a number of rounds, and
`DescriptiveComplexity.Draw.Data.nexTotal_lt_two_pow'` asks for each factor
below `2 ^ (k * m)`. The rounds are bounded elsewhere: the VAL loop is an
increment chain, injective into the subsets of the registers it is supported
on. This file bounds the other factor, the width
`DescriptiveComplexity.Draw.Data.ixLegWidth` times the number of spine
positions.

Every layer's cost – an atom's, a matrix's, a gate block's, a round's, a
variable's machinery's, a leg's – is built from the widths the legs are charged
against and from the file's own numbers by addition and multiplication alone. So
each is *polynomial* in a single bound `q` on all of them, and the bound proved
here is `q ^ 25`: crude, and deliberately so, since what an instantiation has to
show is `q ^ 25 ≤ 2 ^ (k * m)` with `q` polynomial in the drawn universe and `m`
its size – room the exponent does not eat into.

The three combinators (`add_le_pow`, `mul_le_pow`, `le_pow_of_le`) are the whole
method: a sum of two things below `q ^ i` is below `q ^ (i + 1)` because `q` is
at least two, and a product adds the exponents. Written that way, each layer's
bound is one line per node of its defining expression. The target exponent of a
raised or constant bound is written explicitly, since neither the goal nor the
argument determines it.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### Bounding a polynomial by a power -/

section Arith

variable {a b q i : ℕ}

/-- **A sum costs one exponent**, both summands being below a power of a `q`
that is at least two. -/
theorem add_le_pow {j k : ℕ} (hq : 2 ≤ q) (ha : a ≤ q ^ i) (hb : b ≤ q ^ j)
    (hi : i < k) (hj : j < k) : a + b ≤ q ^ k := by
  have hqi : q ^ i ≤ q ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hqj : q ^ j ≤ q ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hk : q ^ (k - 1) * 2 ≤ q ^ (k - 1) * q := Nat.mul_le_mul_left _ hq
  have : q ^ (k - 1) * q = q ^ k := by
    rw [← pow_succ]
    congr 1
    omega
  omega

/-- **A product adds the exponents.** -/
theorem mul_le_pow {j k : ℕ} (hq : 1 ≤ q) (ha : a ≤ q ^ i) (hb : b ≤ q ^ j)
    (hk : i + j ≤ k) : a * b ≤ q ^ k :=
  le_trans (le_trans (Nat.mul_le_mul ha hb) (le_of_eq (pow_add q i j).symm))
    (Nat.pow_le_pow_right hq hk)

/-- **A bound is a first power.** -/
theorem le_pow_one (ha : a ≤ q) : a ≤ q ^ 1 := by simpa using ha

/-- **Raising the exponent of a bound.** -/
theorem le_pow_of_le (k : ℕ) (hq : 1 ≤ q) (ha : a ≤ q ^ i) (hk : i ≤ k) : a ≤ q ^ k :=
  le_trans ha (Nat.pow_le_pow_right hq hk)

/-- **A constant of the program is below every positive power**, the bound being
at least sixteen and every constant written in these costs at most that. -/
theorem cst_le_pow (k : ℕ) (hq : 16 ≤ q) (ha : a ≤ 16) (hk : 1 ≤ k) : a ≤ q ^ k :=
  le_pow_of_le k (by omega) (le_pow_one (le_trans ha hq)) hk

/-! The three shapes a layer of the tower is assembled in, stated over fresh
naturals: the arithmetic is proved away from the machine's terms, as everything
else in this budget pass is. -/

/-- **The shape of a round of the VAL loop**: two loops and five dispatches. -/
theorem round_shape (hq16 : 16 ≤ q) {g m : ℕ} (hg : g ≤ q ^ 13) (hm : m ≤ q ^ 13) :
    1 + g + 1 + 1 + 1 + m + 1 ≤ q ^ 19 := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have a1 : 1 + g ≤ q ^ 14 :=
    add_le_pow hq2 (cst_le_pow 13 hq16 (by norm_num) (by norm_num)) hg
      (by norm_num) (by norm_num)
  have a2 : 1 + g + 1 ≤ q ^ 15 :=
    add_le_pow hq2 a1 (cst_le_pow 14 hq16 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have a3 : 1 + g + 1 + 1 ≤ q ^ 16 :=
    add_le_pow hq2 a2 (cst_le_pow 15 hq16 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have a4 : 1 + g + 1 + 1 + 1 ≤ q ^ 17 :=
    add_le_pow hq2 a3 (cst_le_pow 16 hq16 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have a5 : 1 + g + 1 + 1 + 1 + m ≤ q ^ 18 :=
    add_le_pow hq2 a4 (le_pow_of_le 17 hq1 hm (by norm_num)) (by norm_num) (by norm_num)
  exact add_le_pow hq2 a5 (cst_le_pow 18 hq16 (by norm_num) (by norm_num))
    (by norm_num) (by norm_num)

/-- **The shape of a gates' leg**: one loop between two dispatches. -/
theorem gates_shape (hq16 : 16 ≤ q) {g : ℕ} (hg : g ≤ q ^ 13) :
    1 + g + 1 ≤ q ^ 15 := by
  have hq2 : 2 ≤ q := by omega
  have a1 : 1 + g ≤ q ^ 14 :=
    add_le_pow hq2 (cst_le_pow 13 hq16 (by norm_num) (by norm_num)) hg
      (by norm_num) (by norm_num)
  exact add_le_pow hq2 a1 (cst_le_pow 14 hq16 (by norm_num) (by norm_num))
    (by norm_num) (by norm_num)

/-- **The shape of a variable's machinery as one width**: what it pays once, and
what it pays per round of the VAL loop. -/
theorem varCD_shape (hq16 : 16 ≤ q) {vg rc p : ℕ} (hvg : vg ≤ q ^ 15)
    (hrc : rc ≤ q ^ 19) (hp : p ≤ q) :
    vg + rc + 3 * p + 6 + (2 * p + rc + 3) ≤ q ^ 23 := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have b1 : vg + rc ≤ q ^ 20 :=
    add_le_pow hq2 (le_pow_of_le 19 hq1 hvg (by norm_num)) hrc (by norm_num) (by norm_num)
  have b2 : 3 * p ≤ q ^ 2 :=
    mul_le_pow hq1 (cst_le_pow 1 hq16 (by norm_num) (by norm_num)) (le_pow_one hp)
      (by norm_num)
  have b3 : vg + rc + 3 * p ≤ q ^ 21 :=
    add_le_pow hq2 b1 (le_pow_of_le 20 hq1 b2 (by norm_num)) (by norm_num) (by norm_num)
  have b4 : vg + rc + 3 * p + 6 ≤ q ^ 22 :=
    add_le_pow hq2 b3 (cst_le_pow 21 hq16 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have b5 : 2 * p ≤ q ^ 2 :=
    mul_le_pow hq1 (cst_le_pow 1 hq16 (by norm_num) (by norm_num)) (le_pow_one hp)
      (by norm_num)
  have b6 : 2 * p + rc ≤ q ^ 20 :=
    add_le_pow hq2 (le_pow_of_le 19 hq1 b5 (by norm_num)) hrc (by norm_num) (by norm_num)
  have b7 : 2 * p + rc + 3 ≤ q ^ 21 :=
    add_le_pow hq2 b6 (cst_le_pow 20 hq16 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  exact add_le_pow hq2 b4 (le_pow_of_le 22 hq1 b7 (by norm_num))
    (by norm_num) (by norm_num)

end Arith

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A : Type}

/-! ### One bound for every number a leg's cost is built from -/

/-- **Every number the tower's costs are built from, below one bound.** The four
widths the legs are charged against (`w` for a walk to a named register, `wP`
for a sweep of the file, `wR` for a reset, `wK` for a seek), the two
enumerations an atom loops over, and the dimensions and arities of the data. The
bound is asked to be at least sixteen so that the constants written into the
costs – the thirteen dispatches of a stage atom, the largest of them – are below
it too. -/
structure IxWidthBd (dt : Data L) (A : Type) (w wP wR wK q : ℕ) : Prop where
  /-- The bound dominates the constants the costs are written with. -/
  cst : 16 ≤ q
  /-- A walk to a named register. -/
  wLe : w ≤ q
  /-- A sweep of the file. -/
  wPLe : wP ≤ q
  /-- A reset. -/
  wRLe : wR ≤ q
  /-- A seek. -/
  wKLe : wK ≤ q
  /-- The tuples an atom's comparison loops over. -/
  dd0Le : Nat.card (Lex (Fin dt.dd0 → A)) + 1 ≤ q
  /-- The tuples an expansion's leaf loops over. -/
  eDimLe : Nat.card (Lex (Fin dt.eDim → A)) + 1 ≤ q
  /-- The width of an expansion's tag walk. -/
  ntgLe : dt.ntgDim ≤ q
  /-- The width of an expansion's leaf walk. -/
  nfLe : dt.nfDim ≤ q
  /-- The number of atoms of a variable's matrix. -/
  natOfLe : ∀ vi : dt.VarIx, dt.natOf vi ≤ q
  /-- The number of inner gates of a variable. -/
  nInLe : ∀ vi : dt.VarIx, dt.nIn vi ≤ q
  /-- The number of outer gates of a variable. -/
  arOfLe : ∀ vi : dt.VarIx, dt.arOf vi ≤ q
  /-- The arity of a stage relation. -/
  arityLe : ∀ iv : dt.d.B.ι, dt.d.B.arity iv ≤ q
  /-- The number of positions of the spine. -/
  nvLe : dt.nv ≤ q

variable {dt} {w wP wR wK q : ℕ}

/-! ### The layers, bottom-up -/

/-- **The read of an expansion is polynomial**: the walk down the tags, then the
loop over the leaf's tuples. It is the body of an `exp` atom and of a gate
block alike. -/
theorem ixExpBody_le (h : dt.IxWidthBd A w wP wR wK q) :
    (w + 2) * dt.ntgDim + 2 +
      ((2 + (w + 2) * dt.nfDim) * (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1) ≤ q ^ 7 := by
  have hq1 : 1 ≤ q := by have := h.cst; omega
  have hq2 : 2 ≤ q := by have := h.cst; omega
  have hw2 : w + 2 ≤ q ^ 2 :=
    add_le_pow hq2 (le_pow_one h.wLe) (cst_le_pow 1 h.cst (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have h1 : (w + 2) * dt.ntgDim ≤ q ^ 3 :=
    mul_le_pow hq1 hw2 (le_pow_one h.ntgLe) (by norm_num)
  have h2 : (w + 2) * dt.ntgDim + 2 ≤ q ^ 4 :=
    add_le_pow hq2 h1 (cst_le_pow 3 h.cst (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have h3 : (w + 2) * dt.nfDim ≤ q ^ 3 :=
    mul_le_pow hq1 hw2 (le_pow_one h.nfLe) (by norm_num)
  have h4 : 2 + (w + 2) * dt.nfDim ≤ q ^ 4 :=
    add_le_pow hq2 (cst_le_pow 3 h.cst (by norm_num) (by norm_num)) h3
      (by norm_num) (by norm_num)
  have h5 : (2 + (w + 2) * dt.nfDim) * (Nat.card (Lex (Fin dt.eDim → A)) + 1) ≤ q ^ 5 :=
    mul_le_pow hq1 h4 (le_pow_one h.eDimLe) (by norm_num)
  have h6 : (2 + (w + 2) * dt.nfDim) * (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1 ≤ q ^ 6 :=
    add_le_pow hq2 h5 (cst_le_pow 5 h.cst (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  exact add_le_pow hq2 h2 h6 (by norm_num) (by norm_num)

/-- **An atom's cost is polynomial**, whatever its kind: a comparison, an
expansion's read, or a stage atom's random access. -/
theorem ixKindCost_le (h : dt.IxWidthBd A w wP wR wK q) (vi : dt.VarIx)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi)) :
    dt.ixKindCost A vi w wP wR wK κ ≤ q ^ 10 := by
  have hq1 : 1 ≤ q := by have := h.cst; omega
  have hq2 : 2 ≤ q := by have := h.cst; omega
  -- The walk to a named register appears in every kind.
  have hw2 : w + 2 ≤ q ^ 2 :=
    add_le_pow hq2 (le_pow_one h.wLe) (cst_le_pow 1 h.cst (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  -- The comparison's loop, shared by `eq` and `ord`.
  have hcmp : 1 + ((2 + (w + 2) * 2) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1) ≤ q ^ 10 := by
    have h1 : (w + 2) * 2 ≤ q ^ 3 :=
      mul_le_pow hq1 hw2 (cst_le_pow 1 h.cst (by norm_num) (by norm_num)) (by norm_num)
    have h2 : 2 + (w + 2) * 2 ≤ q ^ 4 :=
      add_le_pow hq2 (cst_le_pow 3 h.cst (by norm_num) (by norm_num)) h1
        (by norm_num) (by norm_num)
    have h3 : (2 + (w + 2) * 2) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) ≤ q ^ 5 :=
      mul_le_pow hq1 h2 (le_pow_one h.dd0Le) (by norm_num)
    have h4 : (2 + (w + 2) * 2) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 ≤ q ^ 6 :=
      add_le_pow hq2 h3 (cst_le_pow 5 h.cst (by norm_num) (by norm_num))
        (by norm_num) (by norm_num)
    exact add_le_pow hq2 (cst_le_pow 9 h.cst (by norm_num) (by norm_num)) h4
      (by norm_num) (by norm_num)
  cases κ with
  | eq _ _ => exact hcmp
  | ord _ _ => exact hcmp
  | exp _ _ =>
    simp only [ixKindCost]
    exact add_le_pow hq2 (cst_le_pow 9 h.cst (by norm_num) (by norm_num)) (ixExpBody_le h)
      (by norm_num) (by norm_num)
  | stage iv _ =>
    simp only [ixKindCost]
    -- The five sweeps, the two resets and the two seeks.
    have h1 : 5 * wP ≤ q ^ 2 :=
      mul_le_pow hq1 (cst_le_pow 1 h.cst (by norm_num) (by norm_num))
        (le_pow_one h.wPLe) (by norm_num)
    have h2 : 2 * wR ≤ q ^ 2 :=
      mul_le_pow hq1 (cst_le_pow 1 h.cst (by norm_num) (by norm_num))
        (le_pow_one h.wRLe) (by norm_num)
    have h3 : 2 * wK ≤ q ^ 2 :=
      mul_le_pow hq1 (cst_le_pow 1 h.cst (by norm_num) (by norm_num))
        (le_pow_one h.wKLe) (by norm_num)
    have h4 : 5 * wP + 2 * wR ≤ q ^ 3 :=
      add_le_pow hq2 h1 h2 (by norm_num) (by norm_num)
    have h5 : 5 * wP + 2 * wR + 2 * wK ≤ q ^ 4 :=
      add_le_pow hq2 h4 h3 (by norm_num) (by norm_num)
    -- The copy loop, once per position of the relation's tuple.
    have hmw : 2 * w ≤ q ^ 2 :=
      mul_le_pow hq1 (cst_le_pow 1 h.cst (by norm_num) (by norm_num))
        (le_pow_one h.wLe) (by norm_num)
    have h6 : 2 * w + 8 ≤ q ^ 3 :=
      add_le_pow hq2 hmw (cst_le_pow 2 h.cst (by norm_num) (by norm_num))
        (by norm_num) (by norm_num)
    have h7 : (2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) ≤ q ^ 4 :=
      mul_le_pow hq1 h6 (le_pow_one h.dd0Le) (by norm_num)
    have h8a : (2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 ≤ q ^ 5 :=
      add_le_pow hq2 h7 (cst_le_pow 4 h.cst (by norm_num) (by norm_num))
        (by norm_num) (by norm_num)
    have h8 : (2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 + 1 ≤ q ^ 6 :=
      add_le_pow hq2 h8a (cst_le_pow 5 h.cst (by norm_num) (by norm_num))
        (by norm_num) (by norm_num)
    have h9 : ((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 + 1) *
        dt.d.B.arity iv ≤ q ^ 7 :=
      mul_le_pow hq1 h8 (le_pow_one (h.arityLe iv)) (by norm_num)
    have h10 : 5 * wP + 2 * wR + 2 * wK +
        ((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 + 1) *
          dt.d.B.arity iv ≤ q ^ 8 :=
      add_le_pow hq2 h5 h9 (by norm_num) (by norm_num)
    exact add_le_pow hq2 h10 (cst_le_pow 8 h.cst (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)

/-- **A matrix's cost is polynomial**: it is the largest of its atoms'. -/
theorem ixMatCost_le (h : dt.IxWidthBd A w wP wR wK q) (vi : dt.VarIx) :
    dt.ixMatCost A vi w wP wR wK ≤ q ^ 10 :=
  Finset.sup_le fun a _ => ixKindCost_le h vi (dt.kindOf vi a)

/-- **A gate block's cost is polynomial**: a sweep of the file and an
expansion's read. -/
theorem ixGateCost_le (h : dt.IxWidthBd A w wP wR wK q) :
    dt.ixGateCost A w wP ≤ q ^ 10 := by
  have hq2 : 2 ≤ q := by have := h.cst; omega
  have h1 : 1 + ((w + 2) * dt.ntgDim + 2 +
      ((2 + (w + 2) * dt.nfDim) * (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1)) ≤ q ^ 8 :=
    add_le_pow hq2 (cst_le_pow 7 h.cst (by norm_num) (by norm_num)) (ixExpBody_le h)
      (by norm_num) (by norm_num)
  have h2 : 1 + (1 + ((w + 2) * dt.ntgDim + 2 +
      ((2 + (w + 2) * dt.nfDim) * (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1))) ≤ q ^ 9 :=
    add_le_pow hq2 (cst_le_pow 8 h.cst (by norm_num) (by norm_num)) h1
      (by norm_num) (by norm_num)
  simp only [ixGateCost]
  exact add_le_pow hq2 (le_pow_one h.wPLe) h2 (by norm_num) (by norm_num)

/-- **A loop over a gate block is polynomial**: what a variable's gates leg and
a round of the VAL loop both pay, at their own number of gates. -/
theorem ixGateLoop_le (h : dt.IxWidthBd A w wP wR wK q) (n : ℕ) (hn : n ≤ q) :
    (dt.ixGateCost A w wP + 2) * n + 1 ≤ q ^ 13 := by
  have hq1 : 1 ≤ q := by have := h.cst; omega
  have hq2 : 2 ≤ q := by have := h.cst; omega
  have h1 : dt.ixGateCost A w wP + 2 ≤ q ^ 11 :=
    add_le_pow hq2 (ixGateCost_le h) (cst_le_pow 10 h.cst (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have h2 : (dt.ixGateCost A w wP + 2) * n ≤ q ^ 12 :=
    mul_le_pow hq1 h1 (le_pow_one hn) (by norm_num)
  exact add_le_pow hq2 h2 (cst_le_pow 12 h.cst (by norm_num) (by norm_num))
    (by norm_num) (by norm_num)

/-- **A round of the VAL loop is polynomial**: the inner gates and the matrix,
each looped over once. -/
theorem ixRoundCost_le (h : dt.IxWidthBd A w wP wR wK q) (vi : dt.VarIx) :
    dt.ixRoundCost A vi w wP wR wK ≤ q ^ 19 := by
  have hq1 : 1 ≤ q := by have := h.cst; omega
  have hq2 : 2 ≤ q := by have := h.cst; omega
  have hg : (dt.ixGateCost A w wP + 2) * dt.nIn vi + 1 ≤ q ^ 13 :=
    ixGateLoop_le h _ (h.nInLe vi)
  have hm1 : dt.ixMatCost A vi w wP wR wK + 2 ≤ q ^ 11 :=
    add_le_pow hq2 (ixMatCost_le h vi) (cst_le_pow 10 h.cst (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have hm2 : (dt.ixMatCost A vi w wP wR wK + 2) * dt.natOf vi ≤ q ^ 12 :=
    mul_le_pow hq1 hm1 (le_pow_one (h.natOfLe vi)) (by norm_num)
  have hm : (dt.ixMatCost A vi w wP wR wK + 2) * dt.natOf vi + 1 ≤ q ^ 13 :=
    add_le_pow hq2 hm2 (cst_le_pow 12 h.cst (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  simp only [ixRoundCost]
  exact round_shape h.cst hg hm

/-- **The gates' leg of a variable is polynomial.** -/
theorem ixVarGatesCost_le (h : dt.IxWidthBd A w wP wR wK q) (vi : dt.VarIx) :
    dt.ixVarGatesCost A vi w wP ≤ q ^ 15 := by
  have hq2 : 2 ≤ q := by have := h.cst; omega
  have hg : (dt.ixGateCost A w wP + 2) * dt.arOf vi + 1 ≤ q ^ 13 :=
    ixGateLoop_le h _ (h.arOfLe vi)
  simp only [ixVarGatesCost]
  exact gates_shape h.cst hg

/-- **A variable's machinery, as one width, is polynomial.** -/
theorem ixVarCD_le (h : dt.IxWidthBd A w wP wR wK q) (vi : dt.VarIx) :
    dt.ixVarCD A vi w wP wR wK ≤ q ^ 23 := by
  simp only [ixVarCD]
  exact varCD_shape h.cst (ixVarGatesCost_le h vi) (ixRoundCost_le h vi) h.wPLe

/-- **The width the clock is handed is polynomial in the file's own numbers**:
the spine's width, times its number of positions, is below `q ^ 25` whenever `q`
bounds the four walk widths, the two enumerations, and the data's dimensions and
arities.

This is the first of the two factors the clocked evaluation is charged
(`DescriptiveComplexity.Draw.Data.ixSpineCost_le_mul`); the second is the
number of VAL rounds. -/
theorem ixLegWidth_le (h : dt.IxWidthBd A w wP wR wK q) :
    dt.ixLegWidth A w wP wR wK * dt.nv ≤ q ^ 25 := by
  classical
  have hq1 : 1 ≤ q := by have := h.cst; omega
  have hq2 : 2 ≤ q := by have := h.cst; omega
  have hsup : (Finset.univ.sup fun j : Fin dt.nv => dt.ixVarCD A (dt.varAt j) w wP wR wK) ≤
      q ^ 23 := Finset.sup_le fun j _ => ixVarCD_le h (dt.varAt j)
  have hwidth : dt.ixLegWidth A w wP wR wK ≤ q ^ 24 := by
    simp only [ixLegWidth]
    exact add_le_pow hq2 (cst_le_pow 23 h.cst (by norm_num) (by norm_num)) hsup
      (by norm_num) (by norm_num)
  exact mul_le_pow hq1 hwidth (le_pow_one h.nvLe) (by norm_num)

/-- **The clocked evaluation's whole width is polynomial too**: the spine's,
the output machinery's and the four joining steps, all below `q ^ 26`. What an
instantiation owes of the clock's first factor is therefore
`q ^ 26 ≤ 2 ^ (k · m)`, and of the second the number of VAL rounds. -/
theorem ixEvalWidth_le (h : dt.IxWidthBd A w wP wR wK q) :
    dt.ixEvalWidth A w wP wR wK ≤ q ^ 26 := by
  have hq2 : 2 ≤ q := by have := h.cst; omega
  have hspine : dt.ixLegWidth A w wP wR wK * dt.nv ≤ q ^ 25 := ixLegWidth_le h
  have hout : dt.ixVarCD A none w wP wR wK ≤ q ^ 23 := ixVarCD_le h none
  have hsum : dt.ixLegWidth A w wP wR wK * dt.nv +
      dt.ixVarCD A none w wP wR wK ≤ q ^ 25 + q ^ 23 := by omega
  have hfour : (4 : ℕ) ≤ q ^ 2 := le_trans (by norm_num)
    (Nat.pow_le_pow_left hq2 2)
  have hstep : q ^ 25 + q ^ 23 + q ^ 2 ≤ q ^ 26 := by
    have h1 : q ^ 23 ≤ q ^ 24 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : q ^ 2 ≤ q ^ 24 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h3 : q ^ 24 + q ^ 24 ≤ q ^ 25 := by
      have : q ^ 24 * 2 ≤ q ^ 24 * q := Nat.mul_le_mul_left _ hq2
      have hq : q ^ 24 * q = q ^ 25 := by rw [← pow_succ]
      omega
    have h4 : q ^ 25 + q ^ 25 ≤ q ^ 26 := by
      have : q ^ 25 * 2 ≤ q ^ 25 * q := Nat.mul_le_mul_left _ hq2
      have hq : q ^ 25 * q = q ^ 26 := by rw [← pow_succ]
      omega
    omega
  simp only [ixEvalWidth]
  omega

end Data

end Draw

end DescriptiveComplexity
