/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Class
import DescriptiveComplexity.FixedPointHorn
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Quantitative first-order logic, and the class FP

The quantitative logic of
[Arenas, Muñoz, Riveros 2020][arenas2020descriptive], in its first-order
fragment QFO: above a layer of Boolean formulas, a layer of terms denoting
natural numbers,

`α ::= φ | s | α + α | α · α | Σx. α | Πx. α`,

a formula counting `1` when it holds and `0` when it does not, and the two
quantifiers being the sum and the product over the elements of the structure
(`DescriptiveComplexity.QTerm`, `DescriptiveComplexity.QTerm.eval`). The
logic, its semantics and the idea of separating a Boolean level from a
quantitative one are theirs; QSO, the full logic of the paper, has
second-order sums and products as well, which are not formalized here.

**FP**, the class of the functions computable in polynomial time – here those
with natural-number values, which is what a
`DescriptiveComplexity.CountingProblem` is – is *defined* by this logic over a
Boolean layer of least fixed points: a problem is in FP when it is the value
of a QFO term over the vocabulary expanded by the relations of a least fixed
point, on every ordered finite
structure (`DescriptiveComplexity.FPDefinable`). That QFO(LFP) captures FP over
ordered structures is Theorem 4.4 of the paper; it is cited, not proved, as the
capture theorems behind the other logically defined classes of the library
are where no machine characterization is given.

A term over the plain ordered vocabulary, with no fixed point, defines a
problem of FP (`DescriptiveComplexity.fpDefinable_of_qfo`): this is the case of
most concrete functions, the fixed point being what makes the class all of FP.

## Positivity is first-order

Whether a term is positive is a *formula* (`DescriptiveComplexity.QTerm.pos`):
a sum is positive when some summand is, a product when every factor is. So
the support of a problem of FP is in PTIME
(`DescriptiveComplexity.support_mem_PTIME_of_fpDefinable`), as the support of
a problem of `#P` is in NP; and a parsimoniously `#P`-hard problem cannot be
in FP unless `NP ⊆ PTIME`
(`DescriptiveComplexity.NP_subset_PTIME_of_parsimoniousHard_of_fpDefinable`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Terms -/

/-- The terms of quantitative first-order logic over a Boolean layer of
first-order formulas, with free variables in `α`
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], grammar (3.1),
restricted to first-order quantifiers). A quantifier binds a block of `n`
variables at once, the variables `Sum.inr i` of `α ⊕ Fin n`; the quantifiers
`Σx` and `Πx` of the paper are the case `n = 1`. -/
inductive QTerm (L : Language.{0, 0}) : Type → Type 1
  /-- A formula: `1` when it holds, `0` when it does not. -/
  | ind {α : Type} (φ : L.Formula α) : QTerm L α
  /-- A constant. -/
  | const {α : Type} (s : ℕ) : QTerm L α
  /-- A sum. -/
  | add {α : Type} (s t : QTerm L α) : QTerm L α
  /-- A product. -/
  | mul {α : Type} (s t : QTerm L α) : QTerm L α
  /-- `Σx̄. t`: the sum over the `n`-tuples of elements of the structure. -/
  | sum {α : Type} (n : ℕ) (t : QTerm L (α ⊕ Fin n)) : QTerm L α
  /-- `Πx̄. t`: the product over the `n`-tuples of elements of the structure. -/
  | prod {α : Type} (n : ℕ) (t : QTerm L (α ⊕ Fin n)) : QTerm L α

namespace QTerm

variable {L L' : Language.{0, 0}}

open Classical in
/-- The value of a term in a structure, under a valuation (Table 1 of the
paper). -/
noncomputable def eval {A : Type} [L.Structure A] : ∀ {α : Type}, QTerm L α → (α → A) → ℕ
  | _, ind φ, v => if φ.Realize v then 1 else 0
  | _, const s, _ => s
  | _, add s t, v => s.eval v + t.eval v
  | _, mul s t, v => s.eval v * t.eval v
  | _, sum _ t, v => ∑ᶠ w : Fin _ → A, t.eval (Sum.elim v w)
  | _, prod _ t, v => ∏ᶠ w : Fin _ → A, t.eval (Sum.elim v w)

/-- The value of a closed term. -/
noncomputable def value (t : QTerm L Empty) (A : Type) [L.Structure A] : ℕ :=
  t.eval (A := A) default

/-- Reading a term in a larger vocabulary. -/
def onTerm (Φ : L →ᴸ L') : ∀ {α : Type}, QTerm L α → QTerm L' α
  | _, ind φ => ind (Φ.onFormula φ)
  | _, const s => const s
  | _, add s t => add (s.onTerm Φ) (t.onTerm Φ)
  | _, mul s t => mul (s.onTerm Φ) (t.onTerm Φ)
  | _, sum n t => sum n (t.onTerm Φ)
  | _, prod n t => prod n (t.onTerm Φ)

theorem eval_onTerm (Φ : L →ᴸ L') {A : Type} [L.Structure A] [L'.Structure A]
    [Φ.IsExpansionOn A] {α : Type} (t : QTerm L α) (v : α → A) :
    (t.onTerm Φ).eval v = t.eval v := by
  induction t with
  | ind φ =>
    by_cases h : φ.Realize v <;> simp [onTerm, eval, LHom.realize_onFormula, h]
  | const s => rfl
  | add s t hs ht => simp only [onTerm, eval, hs, ht]
  | mul s t hs ht => simp only [onTerm, eval, hs, ht]
  | sum n t ht => simp only [onTerm, eval, ht]
  | prod n t ht => simp only [onTerm, eval, ht]

/-- Renaming the free variables of a term. -/
def relabel : ∀ {α : Type}, QTerm L α → ∀ {β : Type}, (α → β) → QTerm L β
  | _, ind φ, _, f => ind (φ.relabel f)
  | _, const s, _, _ => const s
  | _, add s t, _, f => add (s.relabel f) (t.relabel f)
  | _, mul s t, _, f => mul (s.relabel f) (t.relabel f)
  | _, sum n t, _, f => sum n (t.relabel (Sum.map f id))
  | _, prod n t, _, f => prod n (t.relabel (Sum.map f id))

theorem eval_relabel {A : Type} [L.Structure A] {α : Type} (t : QTerm L α) :
    ∀ {β : Type} (f : α → β) (v : β → A), (t.relabel f).eval v = t.eval (v ∘ f) := by
  induction t with
  | ind φ =>
    intro β f v
    by_cases h : φ.Realize (v ∘ f) <;> simp [relabel, eval, Formula.realize_relabel, h]
  | const s => intro β f v; rfl
  | add s t hs ht => intro β f v; simp only [relabel, eval, hs, ht]
  | mul s t hs ht => intro β f v; simp only [relabel, eval, hs, ht]
  | sum n t ht =>
    intro β f v
    simp only [relabel, eval, ht, Sum.elim_comp_map, Function.comp_id]
  | prod n t ht =>
    intro β f v
    simp only [relabel, eval, ht, Sum.elim_comp_map, Function.comp_id]

/-- **The value of a term is isomorphism-invariant.** -/
theorem eval_equiv {A B : Type} [L.Structure A] [L.Structure B] (e : A ≃[L] B) {α : Type}
    (t : QTerm L α) (v : α → A) : t.eval (e ∘ v) = t.eval v := by
  induction t with
  | ind φ =>
    have h := StrongHomClass.realize_formula e φ (v := v)
    by_cases hφ : φ.Realize v <;> simp [eval, h, hφ]
  | const s => rfl
  | add s t hs ht => simp only [eval, hs, ht]
  | mul s t hs ht => simp only [eval, hs, ht]
  | sum n t ht =>
    simp only [eval]
    refine (finsum_comp_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) e.toEquiv)).symm.trans
      (finsum_congr fun w => ?_)
    rw [← ht (Sum.elim v w)]
    exact congrArg t.eval (funext fun x => by cases x <;> rfl)
  | prod n t ht =>
    simp only [eval]
    refine (finprod_comp_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) e.toEquiv)).symm.trans
      (finprod_congr fun w => ?_)
    rw [← ht (Sum.elim v w)]
    exact congrArg t.eval (funext fun x => by cases x <;> rfl)

/-! ### Positivity -/

/-- **“The term is positive”, as a formula**: a formula is positive when it
holds, a sum when some summand is, a product when every factor is. -/
noncomputable def pos : ∀ {α : Type}, QTerm L α → L.Formula α
  | _, ind φ => φ
  | _, const s => if s = 0 then ⊥ else ⊤
  | _, add s t => s.pos ⊔ t.pos
  | _, mul s t => s.pos ⊓ t.pos
  | _, sum n t => Formula.iExs (Fin n) t.pos
  | _, prod n t => Formula.iAlls (Fin n) t.pos

theorem realize_pos {A : Type} [L.Structure A] [Finite A] {α : Type} (t : QTerm L α)
    (v : α → A) : t.pos.Realize v ↔ t.eval v ≠ 0 := by
  classical
  let := Fintype.ofFinite A
  induction t with
  | ind φ =>
    by_cases h : φ.Realize v <;> simp [pos, eval, h]
  | const s =>
    by_cases h : s = 0 <;> simp [pos, eval, h]
  | add s t hs ht =>
    simp only [pos, eval, Formula.realize_sup, hs, ht]
    omega
  | mul s t hs ht =>
    simp only [pos, eval, Formula.realize_inf, hs, ht, Nat.mul_ne_zero_iff]
  | sum n t ht =>
    simp only [pos, eval, Formula.realize_iExs, ht, finsum_eq_sum_of_fintype]
    rw [Ne, Finset.sum_eq_zero_iff]
    simp
  | prod n t ht =>
    simp only [pos, eval, Formula.realize_iAlls, ht, finprod_eq_prod_of_fintype]
    rw [Finset.prod_ne_zero_iff]
    simp

end QTerm

/-! ### FP -/

/-- A definition in QFO(LFP): a least fixed point, as for
`DescriptiveComplexity.LFPDef`, and a quantitative term over the vocabulary
expanded by its relations, read at the fixed point. -/
structure QLFPDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the fixed point. -/
  B : SOBlock
  /-- The number of first-order variables shared by the rules. -/
  k : ℕ
  /-- The rules defining the variables. -/
  rules : List (HornClause (L.sum Language.order) B k)
  /-- The quantitative output. -/
  out : QTerm ((L.sum Language.order).sum B.lang) Empty

/-- The value of a definition on an ordered structure: the output, read at
the least fixed point of the rules. -/
noncomputable def QLFPDef.value {L : Language.{0, 0}} (d : QLFPDef L) (A : Type)
    [L.Structure A] [LinearOrder A] : ℕ :=
  @QTerm.value ((L.sum Language.order).sum d.B.lang) d.out A
    (@sumStructure _ _ A _ (d.B.structure (lfpAssign d.rules)))

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A counting problem is **in FP** when, on nonempty finite structures, it is
the value of a definition in QFO(LFP), whatever the linear order
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], Theorem 4.4). -/
def FPDefinable (C : CountingProblem L) : Prop :=
  ∃ d : QLFPDef L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = d.value A

theorem fpDefinable_congr {C C' : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = C' A) (hC : FPDefinable C) :
    FPDefinable C' := by
  obtain ⟨d, hd⟩ := hC
  exact ⟨d, fun A _ _ _ _ => (h A).symm.trans (hd A)⟩

/-- **A term with no fixed point defines a problem of FP**: a counting problem
that is the value of a QFO term over the ordered vocabulary is in FP.
Registered in the Lax archive as
[`Lax366625.FPByDigits.fpDefinable_of_qfo`](https://laxarchive.org/lax-366625/Lax366625.FPByDigits.html#s-Lax366625.FPByDigits.fpDefinable_of_qfo). -/
theorem fpDefinable_of_qfo {C : CountingProblem L} (t : QTerm (L.sum Language.order) Empty)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = t.value A) : FPDefinable C := by
  refine ⟨⟨⟨Empty, fun e => e.elim⟩, 0, [], t.onTerm LHom.sumInl⟩, fun A _ _ _ _ => ?_⟩
  let := (⟨Empty, fun e => e.elim⟩ : SOBlock).structure
    (lfpAssign (A := A) ([] : List (HornClause (L.sum Language.order) ⟨Empty, fun e => e.elim⟩ 0)))
  exact (h A).trans (QTerm.eval_onTerm LHom.sumInl t default).symm

/-- **The support of a problem of FP is in PTIME**: positivity of the output
term is a first-order formula over the fixed point. -/
theorem support_mem_PTIME_of_fpDefinable {C : CountingProblem L} (h : FPDefinable C) :
    C.support ∈ PTIME := by
  obtain ⟨d, hd⟩ := h
  refine (lfpDefinable_iff_mem_PTIME _).mp ⟨⟨d.B, d.k, d.rules, d.out.pos⟩, ?_⟩
  intro A _ _ _ _
  let := d.B.structure (lfpAssign (A := A) d.rules)
  rw [CountingProblem.support_iff, hd A]
  exact Nat.pos_iff_ne_zero.trans (QTerm.realize_pos d.out (default : Empty → A)).symm

/-- **A problem of FP is not parsimoniously `#P`-hard, unless `NP ⊆ PTIME`.** -/
theorem NP_subset_PTIME_of_parsimoniousHard_of_fpDefinable {C : CountingProblem L}
    (hard : SharpP.ParsimoniousHard C) (h : FPDefinable C) : NP ⊆ PTIME :=
  NP_subset_PTIME_of_sharpP_parsimoniousHard hard (support_mem_PTIME_of_fpDefinable h)

end DescriptiveComplexity
