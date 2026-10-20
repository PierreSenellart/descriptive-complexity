/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Permanents of rectangular matrices, and their Laplace expansion

The permanent of a matrix is the sum, over the bijections between its rows
and its columns, of the products of the entries picked. Stated between two
finite types rather than for square matrices (`DescriptiveComplexity.bperm`),
it is the quantity every gadget argument about cycle covers or perfect
matchings computes with: the number of perfect matchings of a bipartite graph
is the permanent of its 0-1 biadjacency matrix
(`DescriptiveComplexity.bperm_boole`), and the number of cycle covers of a
digraph the permanent of its adjacency matrix.

The one tool the gadget arguments need is the **Laplace expansion along a set
of rows** (`DescriptiveComplexity.bperm_laplace`): the permanent is the sum,
over the sets `S` of columns of the right size, of the permanent of the rows
on `S` times the permanent of the other rows on the other columns. Its
consequences here: the vanishing when a row or a column is zero, the
restriction of the expansion to the columns the rows are supported on
(`DescriptiveComplexity.bperm_laplace_of_support`), and the factorization
when a set of rows is supported on as many columns
(`DescriptiveComplexity.bperm_block`).
-/

namespace DescriptiveComplexity

open Finset

section Def

variable {R : Type} [CommSemiring R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
  [DecidableEq β]

/-- **The permanent of a rectangular matrix**: the sum over the bijections
between rows and columns of the products of the entries picked. It is `0`
when the numbers of rows and columns differ. -/
noncomputable def bperm (M : α → β → R) : R :=
  ∑ e : α ≃ β, ∏ a, M a (e a)

theorem bperm_eq_zero_of_isEmpty [IsEmpty (α ≃ β)] (M : α → β → R) : bperm M = 0 := by
  simp [bperm]

/-- The permanent of a matrix without rows nor columns is `1`. -/
theorem bperm_of_isEmpty [IsEmpty α] [IsEmpty β] (M : α → β → R) : bperm M = 1 := by
  have : Unique (α ≃ β) := ⟨⟨Equiv.equivOfIsEmpty α β⟩, fun e => Equiv.ext fun a => isEmptyElim a⟩
  rw [bperm, Fintype.sum_unique]
  exact Fintype.prod_empty _

/-- The permanent of a `1 × 1` matrix is its entry. -/
theorem bperm_of_unique [Unique α] [Unique β] (M : α → β → R) :
    bperm M = M default default := by
  have : Unique (α ≃ β) :=
    ⟨⟨Equiv.ofUnique α β⟩, fun e => Equiv.ext fun a => Subsingleton.elim _ _⟩
  rw [bperm, Fintype.sum_unique, Fintype.prod_unique]
  exact congrArg (M default) (Subsingleton.elim _ _)

/-- Reindexing rows and columns. -/
theorem bperm_reindex {α' β' : Type} [Fintype α'] [Fintype β'] [DecidableEq α'] [DecidableEq β']
    (eα : α ≃ α') (eβ : β ≃ β')
    (M : α → β → R) : bperm (fun a' b' => M (eα.symm a') (eβ.symm b')) = bperm M := by
  rw [bperm, bperm]
  refine Fintype.sum_equiv (Equiv.equivCongr eα.symm eβ.symm) _ _ fun e => ?_
  refine Fintype.prod_equiv eα.symm _ _ fun a' => ?_
  simp

/-- The permanent of the transpose. -/
theorem bperm_flip (M : α → β → R) : bperm (fun b a => M a b) = bperm M := by
  rw [bperm, bperm]
  refine Fintype.sum_equiv ⟨Equiv.symm, Equiv.symm, fun _ => rfl, fun _ => rfl⟩ _ _ fun e => ?_
  exact Fintype.prod_equiv e _ _ fun b => by simp

/-- A matrix with a zero row has permanent `0`. -/
theorem bperm_eq_zero_of_zero_row (M : α → β → R) (a : α) (h : ∀ b, M a b = 0) :
    bperm M = 0 :=
  Finset.sum_eq_zero fun e _ => Finset.prod_eq_zero (Finset.mem_univ a) (h (e a))

/-- A matrix with a zero column has permanent `0`. -/
theorem bperm_eq_zero_of_zero_col (M : α → β → R) (b : β) (h : ∀ a, M a b = 0) :
    bperm M = 0 := by
  rw [← bperm_flip]
  exact bperm_eq_zero_of_zero_row _ b h

/-- The permanent of a 0-1 matrix counts the bijections it contains. -/
theorem bperm_boole (P : α → β → Prop) [DecidableRel P] :
    bperm (fun a b => if P a b then (1 : R) else 0) =
      Fintype.card {e : α ≃ β // ∀ a, P a (e a)} := by
  rw [bperm, Fintype.card_subtype, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.prod_boole]
  simp

end Def

/-! ### The Laplace expansion along a set of rows -/

section Glue

variable {α β : Type} [DecidableEq α] [DecidableEq β]

/-- A bijection from the rows in `I` to the columns in `S` and one between the
complements, assembled into a bijection between all rows and all columns. -/
def glue (I : Finset α) (S : Finset β) (e₁ : I ≃ S) (e₂ : {a // a ∉ I} ≃ {b // b ∉ S}) :
    α ≃ β :=
  (Equiv.sumCompl (· ∈ I)).symm.trans ((e₁.sumCongr e₂).trans (Equiv.sumCompl (· ∈ S)))

theorem glue_apply_of_mem {I : Finset α} {S : Finset β} (e₁ : I ≃ S)
    (e₂ : {a // a ∉ I} ≃ {b // b ∉ S}) {a : α} (ha : a ∈ I) :
    glue I S e₁ e₂ a = e₁ ⟨a, ha⟩ := by
  simp [glue, Equiv.sumCompl_symm_apply_of_pos ha]

theorem glue_apply_of_not_mem {I : Finset α} {S : Finset β} (e₁ : I ≃ S)
    (e₂ : {a // a ∉ I} ≃ {b // b ∉ S}) {a : α} (ha : a ∉ I) :
    glue I S e₁ e₂ a = e₂ ⟨a, ha⟩ := by
  simp [glue, Equiv.sumCompl_symm_apply_of_neg ha]

theorem glue_mem_iff {I : Finset α} {S : Finset β} (e₁ : I ≃ S)
    (e₂ : {a // a ∉ I} ≃ {b // b ∉ S}) (a : α) : a ∈ I ↔ glue I S e₁ e₂ a ∈ S := by
  by_cases ha : a ∈ I
  · rw [glue_apply_of_mem e₁ e₂ ha]
    exact iff_of_true ha (e₁ ⟨a, ha⟩).2
  · rw [glue_apply_of_not_mem e₁ e₂ ha]
    exact iff_of_false ha (e₂ ⟨a, ha⟩).2

omit [DecidableEq α] in
/-- A bijection sends the rows in `I` exactly to the columns in `S` when
membership is preserved and reflected. -/
theorem image_eq_iff (I : Finset α) (S : Finset β) (e : α ≃ β) :
    I.image e = S ↔ ∀ a, a ∈ I ↔ e a ∈ S := by
  constructor
  · intro h a
    rw [← h, Finset.mem_image]
    exact ⟨fun ha => ⟨a, ha, rfl⟩, fun ⟨a', ha', h'⟩ => e.injective h' ▸ ha'⟩
  · intro h
    ext b
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).mp ha
    · intro hb
      exact ⟨e.symm b, (h _).mpr (by simpa using hb), e.apply_symm_apply b⟩

end Glue

section Laplace

variable {R : Type} [CommSemiring R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
  [DecidableEq β]

/-- **The Laplace expansion of the permanent along the rows in `I`**: the sum,
over the sets `S` of as many columns, of the permanent of the rows `I` on
the columns `S` times the permanent of the other rows on the other columns. -/
theorem bperm_laplace (M : α → β → R) (I : Finset α) :
    bperm M = ∑ S ∈ (univ : Finset β).powersetCard I.card,
      bperm (fun (a : I) (b : S) => M a b) *
        bperm (fun (a : {a // a ∉ I}) (b : {b // b ∉ S}) => M a b) := by
  have key : ∀ e : α ≃ β, I.image e ∈ (univ : Finset β).powersetCard I.card := fun e => by
    rw [mem_powersetCard]
    exact ⟨subset_univ _, card_image_of_injective _ e.injective⟩
  rw [bperm, ← Finset.sum_fiberwise_of_maps_to (fun e _ => key e)]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [bperm, bperm, Finset.sum_mul_sum]
  refine Eq.trans ?_ (Finset.sum_product' _ _ _)
  refine Finset.sum_bij'
    (fun e he => (e.subtypeEquiv ((image_eq_iff I S e).mp (mem_filter.mp he).2),
      e.subtypeEquiv fun a => not_congr ((image_eq_iff I S e).mp (mem_filter.mp he).2 a)))
    (fun p _ => glue I S p.1 p.2) (fun e he => mem_product.mpr ⟨mem_univ _, mem_univ _⟩)
    (fun p _ => ?_) (fun e he => ?_)
    (fun p _ => ?_) (fun e he => ?_)
  · rw [mem_filter]
    exact ⟨mem_univ _, (image_eq_iff I S _).mpr (glue_mem_iff p.1 p.2)⟩
  · ext a
    by_cases ha : a ∈ I
    · rw [glue_apply_of_mem _ _ ha]
      rfl
    · rw [glue_apply_of_not_mem _ _ ha]
      rfl
  · refine Prod.ext (Equiv.ext fun a => Subtype.ext ?_) (Equiv.ext fun a => Subtype.ext ?_)
    · exact (glue_apply_of_mem p.1 p.2 a.2).trans (congrArg (fun x => (p.1 x : β)) rfl)
    · exact (glue_apply_of_not_mem p.1 p.2 a.2).trans (congrArg (fun x => (p.2 x : β)) rfl)
  · convert (Fintype.prod_subtype_mul_prod_subtype (· ∈ I) fun a => M a (e a)).symm using 2 <;>
      exact Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun a _ => rfl

/-- The Laplace expansion, restricted to the columns the rows in `I` are
supported on: the other column sets contribute nothing. -/
theorem bperm_laplace_of_support (M : α → β → R) (I : Finset α) (T : Finset β)
    (hT : ∀ a ∈ I, ∀ b, b ∉ T → M a b = 0) :
    bperm M = ∑ S ∈ T.powersetCard I.card,
      bperm (fun (a : I) (b : S) => M a b) *
        bperm (fun (a : {a // a ∉ I}) (b : {b // b ∉ S}) => M a b) := by
  rw [bperm_laplace M I]
  symm
  refine Finset.sum_subset (powersetCard_mono (subset_univ T)) fun S hS hST => ?_
  obtain ⟨b, hbS, hbT⟩ : ∃ b ∈ S, b ∉ T := by
    by_contra h
    push Not at h
    exact hST ((mem_powersetCard.mpr ⟨h, (mem_powersetCard.mp hS).2⟩))
  rw [bperm_eq_zero_of_zero_col (fun (a : I) (b : S) => M a b) ⟨b, hbS⟩
    fun a => hT a a.2 b hbT, zero_mul]

/-- **Block factorization**: when the rows in `I` are supported on as many
columns `J`, the permanent is the permanent of the block `I × J` times the
one of the complementary block. -/
theorem bperm_block (M : α → β → R) (I : Finset α) (J : Finset β) (hJ : J.card = I.card)
    (hT : ∀ a ∈ I, ∀ b, b ∉ J → M a b = 0) :
    bperm M = bperm (fun (a : I) (b : J) => M a b) *
      bperm (fun (a : {a // a ∉ I}) (b : {b // b ∉ J}) => M a b) := by
  rw [bperm_laplace_of_support M I J hT, ← hJ, powersetCard_self, Finset.sum_singleton]

end Laplace

/-! ### Casting -/

section Cast

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The permanent of a natural-number matrix, as an integer. -/
theorem bperm_natCast (M : α → β → ℕ) :
    ((bperm M : ℕ) : ℤ) = bperm fun a b => (M a b : ℤ) := by
  rw [bperm, bperm, Nat.cast_sum]
  exact Finset.sum_congr rfl fun e _ => Nat.cast_prod _ _

/-- **Permanents of matrices congruent entrywise are congruent.** -/
theorem bperm_modEq (M M' : α → β → ℤ) (m : ℤ) (h : ∀ a b, M a b ≡ M' a b [ZMOD m]) :
    bperm M ≡ bperm M' [ZMOD m] := by
  exact Int.ModEq.sum fun e _ => Int.ModEq.prod fun a _ => h a (e a)

end Cast

end DescriptiveComplexity
