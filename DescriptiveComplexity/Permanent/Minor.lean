/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Permanent.Basic

/-!
# Minors of the permanent

`DescriptiveComplexity.pdel M A B` is the permanent of the matrix `M` with the
rows in `A` and the columns in `B` deleted. Stating the expansions of the
permanent on minors indexed by *sets* of deleted rows and columns, rather
than on nested subtypes, is what lets two expansions in different orders meet:
deleting the row `u` then the row `u'` is deleting `{u, u'}`.

* `DescriptiveComplexity.pdel_laplace_of_support`: the Laplace expansion along
  a set of rows, restricted to the columns they are supported on, on minors.
* `DescriptiveComplexity.pdel_row` and `DescriptiveComplexity.pdel_col`: the
  expansion along one row or column; `DescriptiveComplexity.pdel_row_single`
  and `DescriptiveComplexity.pdel_col_single` when the line has a single
  nonzero entry; `DescriptiveComplexity.pdel_row_zero` and
  `DescriptiveComplexity.pdel_col_zero` when it has none.
* `DescriptiveComplexity.pdel_block`: the factorization when a set of rows is
  supported on as many columns.
-/

namespace DescriptiveComplexity

open Finset

section Equivs

variable {α : Type} [DecidableEq α] {p : α → Prop} [DecidablePred p]

/-- The elements of a set of elements satisfying `p`, as elements of the
subtype. -/
def subtypeSubtypeEquiv (s : Finset α) (hs : ∀ a ∈ s, p a) :
    {x : {a // p a} // x ∈ s.subtype p} ≃ s where
  toFun x := ⟨x.1.1, mem_subtype.mp x.2⟩
  invFun a := ⟨⟨a.1, hs a a.2⟩, mem_subtype.mpr a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A set of elements of the subtype, as a set of elements. -/
def subtypeMapEquiv (S : Finset {a // p a}) :
    S ≃ (S.map (Function.Embedding.subtype p) : Finset α) where
  toFun y := ⟨y.1.1, mem_map_of_mem _ y.2⟩
  invFun b := ⟨⟨b.1, Finset.property_of_mem_map_subtype S b.2⟩, by
    have hb := b.2
    rw [mem_map] at hb
    obtain ⟨y, hy, h⟩ := hb
    rw [show (⟨b.1, Finset.property_of_mem_map_subtype S b.2⟩ : {a // p a}) = y from
      Subtype.ext h.symm]
    exact hy⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complement, in the subtype, of a set of elements. -/
def subtypeNotEquiv (s : Finset α) :
    {x : {a // p a} // x ∉ s.subtype p} ≃ {a // p a ∧ a ∉ s} where
  toFun x := ⟨x.1.1, x.1.2, fun h => x.2 (mem_subtype.mpr h)⟩
  invFun a := ⟨⟨a.1, a.2.1⟩, fun h => a.2.2 ((Finset.mem_subtype (a := ⟨a.1, a.2.1⟩)).mp h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complement, in the subtype, of a set of elements of the subtype. -/
def subtypeNotMapEquiv (S : Finset {a // p a}) :
    {y : {b // p b} // y ∉ S} ≃ {b // p b ∧ b ∉ S.map (Function.Embedding.subtype p)} where
  toFun y := ⟨y.1.1, y.1.2, fun h => y.2 ((Finset.mem_map' _).mp h)⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, fun h => b.2.2 ((Finset.mem_map' _).mpr h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Equivs

section Minor

variable {R : Type} [CommSemiring R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
  [DecidableEq β]

/-- **The permanent of a minor**: the matrix with the rows in `A` and the
columns in `B` deleted. -/
noncomputable def pdel (M : α → β → R) (A : Finset α) (B : Finset β) : R :=
  bperm fun (a : {a // a ∉ A}) (b : {b // b ∉ B}) => M a b

theorem pdel_empty (M : α → β → R) : pdel M ∅ ∅ = bperm M := by
  unfold pdel
  exact (bperm_reindex (Equiv.subtypeUnivEquiv fun a => Finset.notMem_empty a)
    (Equiv.subtypeUnivEquiv fun b => Finset.notMem_empty b)
    fun (a : {a // a ∉ (∅ : Finset α)}) (b : {b // b ∉ (∅ : Finset β)}) => M a b).symm

theorem pdel_flip (M : α → β → R) (A : Finset α) (B : Finset β) :
    pdel (fun b a => M a b) B A = pdel M A B :=
  bperm_flip _

/-- Deleting the same sets gives the same minor. -/
theorem pdel_congr (M : α → β → R) {A A' : Finset α} {B B' : Finset β} (hA : A = A')
    (hB : B = B') : pdel M A B = pdel M A' B' := by
  subst hA hB
  rfl

/-- **The Laplace expansion of a minor along the rows in `I`**, restricted to
the columns `T` those rows are supported on. -/
theorem pdel_laplace_of_support (M : α → β → R) (A : Finset α) (B : Finset β) (I : Finset α)
    (T : Finset β) (hIA : ∀ a ∈ I, a ∉ A) (hTB : ∀ b ∈ T, b ∉ B)
    (hT : ∀ a ∈ I, ∀ b, b ∉ B → b ∉ T → M a b = 0) :
    pdel M A B = ∑ S ∈ T.powersetCard I.card,
      bperm (fun (x : I) (y : S) => M x y) * pdel M (A ∪ I) (B ∪ S) := by
  rw [pdel, bperm_laplace_of_support _ (I.subtype (· ∉ A)) (T.subtype (· ∉ B))
    fun a ha b hb => hT a (mem_subtype.mp ha) b b.2 fun h => hb (mem_subtype.mpr h)]
  have hcard : (I.subtype (· ∉ A)).card = I.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem hIA]
  have hTmap : T = (T.subtype (· ∉ B)).map (Function.Embedding.subtype _) := by
    rw [Finset.subtype_map, Finset.filter_true_of_mem hTB]
  rw [hcard]
  conv_rhs => rw [hTmap, powersetCard_map, Finset.sum_map]
  refine Finset.sum_congr rfl fun S' _ => ?_
  rw [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
  congr 1
  · exact (bperm_reindex (subtypeSubtypeEquiv I hIA) (subtypeMapEquiv S') _).symm
  · rw [pdel]
    refine (bperm_reindex ((subtypeNotEquiv I).trans (Equiv.subtypeEquivRight fun a => ?_))
      ((subtypeNotMapEquiv S').trans (Equiv.subtypeEquivRight fun b => ?_)) _).symm
    · rw [Finset.mem_union, not_or]
    · rw [Finset.mem_union, not_or]

/-- **Block factorization**: rows supported on as many columns. -/
theorem pdel_block (M : α → β → R) (A : Finset α) (B : Finset β) (I : Finset α) (J : Finset β)
    (hIA : ∀ a ∈ I, a ∉ A) (hJB : ∀ b ∈ J, b ∉ B) (hJ : J.card = I.card)
    (hT : ∀ a ∈ I, ∀ b, b ∉ B → b ∉ J → M a b = 0) :
    pdel M A B = bperm (fun (x : I) (y : J) => M x y) * pdel M (A ∪ I) (B ∪ J) := by
  rw [pdel_laplace_of_support M A B I J hIA hJB hT, ← hJ, powersetCard_self, Finset.sum_singleton]

omit [Fintype α] [Fintype β] in
/-- The permanent of a `1 × 1` block is its entry. -/
theorem bperm_singleton (M : α → β → R) (a : α) (b : β) :
    bperm (fun (x : ({a} : Finset α)) (y : ({b} : Finset β)) => M x y) = M a b := by
  have : Unique {x // x ∈ ({a} : Finset α)} :=
    ⟨⟨⟨a, mem_singleton_self a⟩⟩, fun x => Subtype.ext (mem_singleton.mp x.2)⟩
  have : Unique {y // y ∈ ({b} : Finset β)} :=
    ⟨⟨⟨b, mem_singleton_self b⟩⟩, fun y => Subtype.ext (mem_singleton.mp y.2)⟩
  rw [bperm_of_unique]
  exact congrArg₂ M (mem_singleton.mp (Subtype.mem _)) (mem_singleton.mp (Subtype.mem _))

/-- **Expansion along a row.** -/
theorem pdel_row (M : α → β → R) (A : Finset α) (B : Finset β) {a : α} (ha : a ∉ A) :
    pdel M A B = ∑ b ∈ Bᶜ, M a b * pdel M (insert a A) (insert b B) := by
  rw [pdel_laplace_of_support M A B {a} Bᶜ (fun x hx => (mem_singleton.mp hx) ▸ ha)
    (fun b hb => mem_compl.mp hb) (fun _ _ b hb hb' => absurd (mem_compl.mpr hb) hb'),
    card_singleton, powersetCard_one, Finset.sum_map]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Function.Embedding.coeFn_mk, bperm_singleton, Finset.union_comm, ← Finset.insert_eq,
    Finset.union_comm, ← Finset.insert_eq]

/-- **Expansion along a column.** -/
theorem pdel_col (M : α → β → R) (A : Finset α) (B : Finset β) {b : β} (hb : b ∉ B) :
    pdel M A B = ∑ a ∈ Aᶜ, M a b * pdel M (insert a A) (insert b B) := by
  rw [← pdel_flip, pdel_row _ _ _ hb]
  exact Finset.sum_congr rfl fun a _ => by rw [pdel_flip]

/-- A row with a single nonzero entry. -/
theorem pdel_row_single (M : α → β → R) (A : Finset α) (B : Finset β) {a : α} (ha : a ∉ A)
    {b : β} (hb : b ∉ B) (h : ∀ b', b' ∉ B → b' ≠ b → M a b' = 0) :
    pdel M A B = M a b * pdel M (insert a A) (insert b B) := by
  rw [pdel_row M A B ha]
  exact Finset.sum_eq_single b (fun b' hb' hne => by rw [h b' (mem_compl.mp hb') hne, zero_mul])
    fun hb' => absurd (mem_compl.mpr hb) hb'

/-- A column with a single nonzero entry. -/
theorem pdel_col_single (M : α → β → R) (A : Finset α) (B : Finset β) {b : β} (hb : b ∉ B)
    {a : α} (ha : a ∉ A) (h : ∀ a', a' ∉ A → a' ≠ a → M a' b = 0) :
    pdel M A B = M a b * pdel M (insert a A) (insert b B) := by
  rw [pdel_col M A B hb]
  exact Finset.sum_eq_single a (fun a' ha' hne => by rw [h a' (mem_compl.mp ha') hne, zero_mul])
    fun ha' => absurd (mem_compl.mpr ha) ha'

/-- A zero row. -/
theorem pdel_row_zero (M : α → β → R) (A : Finset α) (B : Finset β) {a : α} (ha : a ∉ A)
    (h : ∀ b, b ∉ B → M a b = 0) : pdel M A B = 0 := by
  rw [pdel_row M A B ha]
  exact Finset.sum_eq_zero fun b hb => by rw [h b (mem_compl.mp hb), zero_mul]

/-- A zero column. -/
theorem pdel_col_zero (M : α → β → R) (A : Finset α) (B : Finset β) {b : β} (hb : b ∉ B)
    (h : ∀ a, a ∉ A → M a b = 0) : pdel M A B = 0 := by
  rw [pdel_col M A B hb]
  exact Finset.sum_eq_zero fun a ha => by rw [h a (mem_compl.mp ha), zero_mul]

/-! ### An isolated node with a self-loop -/

/-- The nodes other than the extra one. -/
def notExtraEquiv : {a : α ⊕ Unit // a ∉ ({Sum.inr ()} : Finset (α ⊕ Unit))} ≃ α where
  toFun a :=
    match a with
    | ⟨Sum.inl a, _⟩ => a
    | ⟨Sum.inr (), h⟩ => absurd (mem_singleton_self _) h
  invFun a := ⟨Sum.inl a, by simp⟩
  left_inv a := by
    obtain ⟨a | ⟨⟩, h⟩ := a
    · rfl
    · exact absurd (mem_singleton_self _) h
  right_inv _ := rfl

omit [Fintype β] [DecidableEq β] in
/-- **Adding a node with a self-loop and no other outgoing edge does not
change the permanent.** -/
theorem bperm_extend_loop (M : α → α → R) (N : α ⊕ Unit → α ⊕ Unit → R)
    (hN : ∀ a b, N (Sum.inl a) (Sum.inl b) = M a b) (hloop : N (Sum.inr ()) (Sum.inr ()) = 1)
    (hrow : ∀ b, N (Sum.inr ()) (Sum.inl b) = 0) :
    bperm N = bperm M := by
  rw [bperm_block N {Sum.inr ()} {Sum.inr ()} rfl (fun a ha b hb => by
    rw [mem_singleton.mp ha]
    rcases b with b | ⟨⟩
    · exact hrow b
    · exact absurd (mem_singleton_self _) hb), bperm_singleton, hloop, one_mul,
    ← bperm_reindex notExtraEquiv.symm notExtraEquiv.symm M]
  refine congrArg bperm (funext fun a => funext fun b => ?_)
  obtain ⟨a | ⟨⟩, ha⟩ := a
  · obtain ⟨b | ⟨⟩, hb⟩ := b
    · exact hN a b
    · exact absurd (mem_singleton_self _) hb
  · exact absurd (mem_singleton_self _) ha

end Minor

end DescriptiveComplexity
