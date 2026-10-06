/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Permanent.Minor
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

/-!
# Attaching a gadget to a matrix

A **gadget** attached to a matrix `M₀` on `V` is a matrix `D` on its own
nodes `X`, with *in-edges* from rows of `V` to columns of `X` and *out-edges*
from rows of `X` to columns of `V` (`DescriptiveComplexity.attach`). The
permanent of the result expands, by the Laplace expansion along the rows of
the gadget, into a sum over the **patterns** – which in-ports are entered,
which out-ports are left – of the permanent of the corresponding minor of
the gadget times the permanent of the corresponding minor of `M₀`.

This file states that expansion for the gadget shape of Valiant's XOR
gadget: two in-ports `xin`, `xin'` reached from two base rows `u`, `u'`, and
two out-ports `o`, `o'` leaving to two base columns `v`, `v'`
(`DescriptiveComplexity.pdel_attachXor`). It is stated on minors, so that it
can be applied to one gadget at a time when several are attached.
-/

namespace DescriptiveComplexity

open Finset

section Attach

variable {R : Type} [CommSemiring R] {V X : Type} [Fintype V] [Fintype X] [DecidableEq V]
  [DecidableEq X]

/-- **A gadget attached to a matrix**: the base matrix `M₀` on `V`, the
gadget `D` on `X`, the in-edges `ins` from `V` to `X` and the out-edges
`outs` from `X` to `V`. -/
def attach (M₀ : V → V → R) (D : X → X → R) (ins : V → X → R) (outs : X → V → R) :
    V ⊕ X → V ⊕ X → R
  | Sum.inl a, Sum.inl b => M₀ a b
  | Sum.inl a, Sum.inr x => ins a x
  | Sum.inr x, Sum.inl b => outs x b
  | Sum.inr x, Sum.inr y => D x y

/-- The indicator of one in-edge, from `u` to `x`. -/
def inEdge (u : V) (x : X) : V → X → R :=
  fun a y => if a = u ∧ y = x then 1 else 0

/-- The indicator of one out-edge, from `x` to `v`. -/
def outEdge (x : X) (v : V) : X → V → R :=
  fun y b => if y = x ∧ b = v then 1 else 0

variable (M₀ : V → V → R) (D : X → X → R) (ins : V → X → R) (outs : X → V → R)

/-- The rows of the gadget are deleted together with those in `A`. -/
def withGadget (A : Finset V) : Finset (V ⊕ X) :=
  A.map Function.Embedding.inl ∪ univ.map Function.Embedding.inr

omit [Fintype V] in
theorem mem_withGadget (A : Finset V) (w : V ⊕ X) :
    w ∈ withGadget (X := X) A ↔ (∃ a ∈ A, w = Sum.inl a) ∨ ∃ x, w = Sum.inr x := by
  simp only [withGadget, mem_union, mem_map, Function.Embedding.inl_apply,
    Function.Embedding.inr_apply, mem_univ, true_and]
  exact or_congr (exists_congr fun a => and_congr_right fun _ => eq_comm)
    (exists_congr fun x => eq_comm)

/-- The rows left when the gadget rows and those in `A` are deleted are the
base rows outside `A`. -/
def notWithGadgetEquiv (A : Finset V) : {w // w ∉ withGadget (X := X) A} ≃ {a // a ∉ A} where
  toFun w :=
    match w with
    | ⟨Sum.inl a, h⟩ => ⟨a, fun ha => h ((mem_withGadget A _).mpr (Or.inl ⟨a, ha, rfl⟩))⟩
    | ⟨Sum.inr x, h⟩ => absurd ((mem_withGadget A _).mpr (Or.inr ⟨x, rfl⟩)) h
  invFun a := ⟨Sum.inl a.1, fun h => by
    rcases (mem_withGadget A _).mp h with ⟨a', ha', h⟩ | ⟨x, h⟩
    · exact a.2 (Sum.inl.inj h ▸ ha')
    · exact Sum.inl_ne_inr h⟩
  left_inv w := by
    obtain ⟨w, h⟩ := w
    cases w with
    | inl a => rfl
    | inr x => exact absurd ((mem_withGadget A _).mpr (Or.inr ⟨x, rfl⟩)) h
  right_inv _ := rfl

/-- Deleting all the gadget rows and columns leaves a minor of the base
matrix. -/
theorem pdel_attach_withGadget (A B : Finset V) :
    pdel (attach M₀ D ins outs) (withGadget A) (withGadget B) = pdel M₀ A B := by
  unfold pdel
  refine (bperm_reindex (notWithGadgetEquiv A) (notWithGadgetEquiv B) _).symm.trans ?_
  rfl

/-! ### Local blocks and the base part of an expansion -/

/-- The gadget rows outside `O`, as a set of rows of the attached matrix. -/
def gadgetRows (O : Finset X) : Finset (V ⊕ X) :=
  (univ.filter (· ∉ O)).map Function.Embedding.inr

omit [Fintype V] [DecidableEq V] in
theorem mem_gadgetRows (O : Finset X) (w : V ⊕ X) :
    w ∈ gadgetRows (V := V) O ↔ ∃ x, w = Sum.inr x ∧ x ∉ O := by
  simp only [gadgetRows, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.inr_apply]
  exact exists_congr fun x => ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩

omit [Fintype V] [DecidableEq V] in
theorem card_gadgetRows (O : Finset X) :
    (gadgetRows (V := V) O).card = (univ.filter (· ∉ O)).card :=
  card_map _

omit [Fintype V] in
/-- The gadget rows outside `O`, as elements of `X`. -/
def gadgetRowsEquiv (O : Finset X) : gadgetRows (V := V) O ≃ {x // x ∉ O} where
  toFun w :=
    match w with
    | ⟨Sum.inl _, h⟩ => absurd ((mem_gadgetRows O _).mp h) (by simp)
    | ⟨Sum.inr x, h⟩ => ⟨x, by
        obtain ⟨x', hx', hx⟩ := (mem_gadgetRows O _).mp h
        exact Sum.inr.inj hx' ▸ hx⟩
  invFun x := ⟨Sum.inr x.1, (mem_gadgetRows O _).mpr ⟨x.1, rfl, x.2⟩⟩
  left_inv w := by
    obtain ⟨w, h⟩ := w
    cases w with
    | inl a => exact absurd ((mem_gadgetRows O _).mp h) (by simp)
    | inr x => rfl
  right_inv _ := rfl

omit [Fintype V] in
/-- A block of the gadget, read as a minor of `D`. -/
theorem bperm_gadgetRows (O Y : Finset X) (S : Finset (V ⊕ X))
    (hS : ∀ w, w ∈ S ↔ ∃ y, w = Sum.inr y ∧ y ∉ Y) :
    bperm (fun (x : gadgetRows (V := V) O) (y : S) => attach M₀ D ins outs x y) = pdel D O Y := by
  have hSe : S = gadgetRows Y := Finset.ext fun w => (hS w).trans (mem_gadgetRows Y w).symm
  subst hSe
  unfold pdel
  refine (bperm_reindex (gadgetRowsEquiv O) (gadgetRowsEquiv Y) _).symm.trans ?_
  rfl

/-- A sum over the rows of the attached matrix outside the base rows `A`. -/
theorem sum_compl_map_inl (A : Finset V) (f : V ⊕ X → R) :
    ∑ w ∈ (A.map Function.Embedding.inl)ᶜ, f w = ∑ a ∈ Aᶜ, f (Sum.inl a) + ∑ x, f (Sum.inr x) := by
  rw [← Finset.sum_disjSum]
  refine Finset.sum_congr (Finset.ext fun w => ?_) fun _ _ => rfl
  cases w <;> simp

omit [Fintype V] [Fintype X] [DecidableEq V] [DecidableEq X] in
theorem notMem_map_inl_of_inr (A : Finset V) (x : X) :
    Sum.inr x ∉ A.map (Function.Embedding.inl : V ↪ V ⊕ X) := by
  simp

omit [Fintype V] [DecidableEq V] in
theorem gadgetRows_subset (O : Finset X) : gadgetRows (V := V) O ⊆ gadgetRows ∅ := by
  intro w hw
  obtain ⟨x, rfl, -⟩ := (mem_gadgetRows O w).mp hw
  exact (mem_gadgetRows ∅ _).mpr ⟨x, rfl, Finset.notMem_empty x⟩

/-- Deleting all the gadget rows and columns, in whichever presentation,
leaves a minor of the base matrix. -/
theorem pdel_attach_of_mem (A B : Finset V) (A' B' : Finset (V ⊕ X))
    (hA : ∀ w, w ∈ A' ↔ (∃ a ∈ A, w = Sum.inl a) ∨ ∃ x, w = Sum.inr x)
    (hB : ∀ w, w ∈ B' ↔ (∃ b ∈ B, w = Sum.inl b) ∨ ∃ x, w = Sum.inr x) :
    pdel (attach M₀ D ins outs) A' B' = pdel M₀ A B := by
  have hA' : A' = withGadget A := Finset.ext fun w => (hA w).trans (mem_withGadget A w).symm
  have hB' : B' = withGadget B := Finset.ext fun w => (hB w).trans (mem_withGadget B w).symm
  rw [hA', hB', pdel_attach_withGadget]

/-! ### The expansion of Valiant's gadget shape -/

section Xor

variable (u u' v v' : V) (xin xin' o o' : X)

/-- **The XOR gadget shape**: two in-edges, from `u` to `xin` and from `u'` to
`xin'`, and two out-edges, from `o` to `v` and from `o'` to `v'`. -/
abbrev attachXor : V ⊕ X → V ⊕ X → R :=
  attach M₀ D (fun a x => inEdge u xin a x + inEdge u' xin' a x)
    fun x b => outEdge o v x b + outEdge o' v' x b

variable {M₀ D u u' v v' xin xin' o o'}

omit [Fintype V] [Fintype X] in
theorem attachXor_inl_inl (a b : V) :
    attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl a) (Sum.inl b) = M₀ a b :=
  rfl

omit [Fintype V] [Fintype X] in
theorem attachXor_inr_inr (x y : X) :
    attachXor M₀ D u u' v v' xin xin' o o' (Sum.inr x) (Sum.inr y) = D x y :=
  rfl

omit [Fintype V] [Fintype X] in
theorem attachXor_inr_inl (x : X) (b : V) :
    attachXor M₀ D u u' v v' xin xin' o o' (Sum.inr x) (Sum.inl b) =
      (if x = o ∧ b = v then 1 else 0) + if x = o' ∧ b = v' then 1 else 0 :=
  rfl

omit [Fintype V] [Fintype X] in
theorem attachXor_inl_inr (a : V) (x : X) :
    attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl a) (Sum.inr x) =
      (if a = u ∧ x = xin then 1 else 0) + if a = u' ∧ x = xin' then 1 else 0 :=
  rfl

omit [Fintype V] [Fintype X] in
/-- An out-edge to a deleted column vanishes. -/
theorem attachXor_inr_inl_eq_zero {B : Finset V} (hv : v ∈ B) (hv' : v' ∈ B) (x : X) {b : V}
    (hb : b ∉ B) : attachXor M₀ D u u' v v' xin xin' o o' (Sum.inr x) (Sum.inl b) = 0 := by
  rw [attachXor_inr_inl, ite_eq_right fun (h : x = o ∧ b = v) => hb (h.2 ▸ hv),
    ite_eq_right fun (h : x = o' ∧ b = v') => hb (h.2 ▸ hv'), add_zero]

omit [Fintype V] [Fintype X] in
/-- An in-edge to a column that is no in-port vanishes. -/
theorem attachXor_inl_inr_eq_zero (a : V) {x : X} (hx : x ≠ xin) (hx' : x ≠ xin') :
    attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl a) (Sum.inr x) = 0 := by
  rw [attachXor_inl_inr, ite_eq_right fun (h : a = u ∧ x = xin) => hx h.2,
    ite_eq_right fun (h : a = u' ∧ x = xin') => hx' h.2, add_zero]

variable (hxx' : xin ≠ xin')

omit [Fintype V] [Fintype X] in
include hxx' in
theorem attachXor_inl_inr_xin {a : V} (ha : a ≠ u) :
    attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl a) (Sum.inr xin) = 0 := by
  rw [attachXor_inl_inr, ite_eq_right fun (h : a = u ∧ xin = xin) => ha h.1,
    ite_eq_right fun (h : a = u' ∧ xin = xin') => hxx' h.2, add_zero]

omit [Fintype V] [Fintype X] in
include hxx' in
theorem attachXor_inl_inr_xin' {a : V} (ha : a ≠ u') :
    attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl a) (Sum.inr xin') = 0 := by
  rw [attachXor_inl_inr, ite_eq_right fun (h : a = u ∧ xin' = xin) => hxx' h.2.symm,
    ite_eq_right fun (h : a = u' ∧ xin' = xin') => ha h.1, add_zero]

omit [Fintype V] [Fintype X] in
include hxx' in
theorem attachXor_u_xin : attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl u) (Sum.inr xin) = 1 := by
  rw [attachXor_inl_inr, ite_eq_left ⟨rfl, rfl⟩,
    ite_eq_right fun (h : u = u' ∧ xin = xin') => hxx' h.2, add_zero]

omit [Fintype V] [Fintype X] in
include hxx' in
theorem attachXor_u'_xin' :
    attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl u') (Sum.inr xin') = 1 := by
  rw [attachXor_inl_inr, ite_eq_right fun (h : u' = u ∧ xin' = xin) => hxx' h.2.symm,
    ite_eq_left ⟨rfl, rfl⟩, zero_add]

omit [Fintype V] in
/-- The deleted rows after a base row `a` reaches a gadget column: all the
gadget rows, and the base rows in `insert a A`. -/
theorem mem_insert_inl_union_gadgetRows (A : Finset V) (a : V) (o₀ : X) (w : V ⊕ X) :
    w ∈ insert (Sum.inl a) (insert (Sum.inr o₀) (A.map Function.Embedding.inl) ∪
        gadgetRows (V := V) {o₀}) ↔
      (∃ a' ∈ insert a A, w = Sum.inl a') ∨ ∃ x, w = Sum.inr x := by
  cases w with
  | inl b => simp [mem_gadgetRows, eq_comm]
  | inr x =>
    refine iff_of_true ?_ (Or.inr ⟨x, rfl⟩)
    by_cases h : x = o₀
    · subst h
      exact mem_insert_of_mem (mem_union_left _ (mem_insert_self _ _))
    · exact mem_insert_of_mem (mem_union_right _ ((mem_gadgetRows _ _).mpr
        ⟨x, rfl, fun hm => h (mem_singleton.mp hm)⟩))

omit [Fintype V] in
/-- The deleted columns after the in-port `x` has been reached: all the gadget
columns, and the base columns in `B`. -/
theorem mem_insert_inr_union_gadgetRows (B : Finset V) (x : X) (w : V ⊕ X) :
    w ∈ insert (Sum.inr x) (B.map Function.Embedding.inl ∪ gadgetRows (V := V) {x}) ↔
      (∃ b ∈ B, w = Sum.inl b) ∨ ∃ y, w = Sum.inr y := by
  cases w with
  | inl b => simp [mem_gadgetRows, eq_comm]
  | inr y =>
    refine iff_of_true ?_ (Or.inr ⟨y, rfl⟩)
    by_cases h : y = x
    · subst h
      exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_union_right _ ((mem_gadgetRows _ _).mpr
        ⟨y, rfl, fun hm => h (mem_singleton.mp hm)⟩))

omit [Fintype V] in
/-- The support condition of the gadget rows, once the out-columns are
deleted. -/
theorem attachXor_support {B : Finset V} (hv : v ∈ B) (hv' : v' ∈ B) (O : Finset X) :
    ∀ w ∈ gadgetRows (V := V) O, ∀ b, b ∉ B.map Function.Embedding.inl → b ∉ gadgetRows ∅ →
      attachXor M₀ D u u' v v' xin xin' o o' w b = 0 := by
  intro w hw b hb hb'
  obtain ⟨x, rfl, -⟩ := (mem_gadgetRows O w).mp hw
  cases b with
  | inl c =>
    refine attachXor_inr_inl_eq_zero hv hv' x fun hc => hb ?_
    exact mem_map_of_mem _ hc
  | inr y => exact absurd ((mem_gadgetRows ∅ _).mpr ⟨y, rfl, Finset.notMem_empty y⟩) hb'

/-- **No gadget row deleted**: with the out-columns deleted, the gadget is a
block of its own. -/
theorem pdel_attachXor_block (A B : Finset V) (hv : v ∈ B) (hv' : v' ∈ B) :
    pdel (attachXor M₀ D u u' v v' xin xin' o o') (A.map Function.Embedding.inl)
      (B.map Function.Embedding.inl) = pdel D ∅ ∅ * pdel M₀ A B := by
  rw [pdel_block _ _ _ (gadgetRows ∅) (gadgetRows ∅)
    (fun w hw => by
      obtain ⟨x, rfl, -⟩ := (mem_gadgetRows ∅ w).mp hw
      exact notMem_map_inl_of_inr A x)
    (fun w hw => by
      obtain ⟨x, rfl, -⟩ := (mem_gadgetRows ∅ w).mp hw
      exact notMem_map_inl_of_inr B x)
    rfl (attachXor_support hv hv' ∅), bperm_gadgetRows _ _ _ _ ∅ ∅ _ (mem_gadgetRows ∅)]
  congr 1
  refine pdel_attach_of_mem _ _ _ _ A B _ _ (fun w => ?_) fun w => ?_ <;>
    simp only [mem_union, mem_map, Function.Embedding.inl_apply, mem_gadgetRows,
      Finset.notMem_empty, not_false_eq_true, and_true] <;>
    exact or_congr (exists_congr fun a => and_congr_right fun _ => eq_comm) Iff.rfl

omit [Fintype V] [DecidableEq V] in
theorem card_gadgetRows_singleton (x : X) :
    (gadgetRows (V := V) {x}).card = Fintype.card X - 1 := by
  rw [card_gadgetRows]
  simp only [mem_singleton]
  rw [Finset.filter_ne', card_erase_of_mem (mem_univ x), card_univ]

omit [Fintype V] [DecidableEq V] in
theorem card_gadgetRows_pair {x y : X} (hxy : x ≠ y) :
    (gadgetRows (V := V) {x, y}).card = Fintype.card X - 2 := by
  rw [card_gadgetRows, show univ.filter (fun z => z ∉ ({x, y} : Finset X)) = (univ.erase x).erase y
    from by ext z; simp [and_comm], card_erase_of_mem (mem_erase.mpr ⟨hxy.symm, mem_univ y⟩),
    card_erase_of_mem (mem_univ x), card_univ]
  omega

omit [Fintype V] [DecidableEq V] in
theorem card_gadgetRows_empty : (gadgetRows (V := V) (∅ : Finset X)).card = Fintype.card X := by
  rw [card_gadgetRows]
  simp

omit [Fintype V] [DecidableEq V] in
/-- A set of gadget rows missing the row `inr x` lies outside `x`. -/
theorem subset_gadgetRows_singleton {S : Finset (V ⊕ X)} (hS : S ⊆ gadgetRows ∅) {x : X}
    (hx : Sum.inr x ∉ S) : S ⊆ gadgetRows {x} := by
  intro w hw
  obtain ⟨y, rfl, -⟩ := (mem_gadgetRows ∅ w).mp (hS hw)
  exact (mem_gadgetRows {x} _).mpr ⟨y, rfl, fun h => hx ((mem_singleton.mp h) ▸ hw)⟩

omit [Fintype V] [DecidableEq V] in
/-- Among the sets of gadget rows of size one less than all, one not missing
two given rows is determined by the one row it misses. -/
theorem exists_notMem_of_ne {S : Finset (V ⊕ X)} (hS : S ⊆ gadgetRows ∅)
    (hcard : S.card = Fintype.card X - 1) {x x' : X} (h : S ≠ gadgetRows {x})
    (h' : S ≠ gadgetRows {x'}) : ∃ z, Sum.inr z ∉ S ∧ z ≠ x ∧ z ≠ x' := by
  have : Nonempty X := ⟨x⟩
  have hlt : S.card < (gadgetRows (V := V) (∅ : Finset X)).card := by
    rw [hcard, card_gadgetRows_empty]
    exact Nat.sub_one_lt Fintype.card_ne_zero
  obtain ⟨w, hw, hwS⟩ := exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨z, rfl, -⟩ := (mem_gadgetRows ∅ w).mp hw
  refine ⟨z, hwS, fun hz => h ?_, fun hz => h' ?_⟩
  · subst hz
    exact eq_of_subset_of_card_le (subset_gadgetRows_singleton hS hwS)
      (by rw [hcard, card_gadgetRows_singleton])
  · subst hz
    exact eq_of_subset_of_card_le (subset_gadgetRows_singleton hS hwS)
      (by rw [hcard, card_gadgetRows_singleton])

omit [Fintype V] [DecidableEq V] in
/-- Among the sets of gadget rows of size two less than all, one that is not
the set outside `{x, x'}` misses some other row. -/
theorem exists_notMem_of_ne_pair {S : Finset (V ⊕ X)} (_hS : S ⊆ gadgetRows ∅)
    (hcard : S.card = Fintype.card X - 2) {x x' : X} (hxx' : x ≠ x')
    (h : S ≠ gadgetRows {x, x'}) : ∃ z, Sum.inr z ∉ S ∧ z ≠ x ∧ z ≠ x' := by
  by_contra hcon
  push Not at hcon
  refine h (eq_of_subset_of_card_le (fun w hw => ?_)
    (by rw [hcard, card_gadgetRows_pair hxx']) ).symm
  obtain ⟨y, rfl, hy⟩ := (mem_gadgetRows {x, x'} w).mp hw
  by_contra hyS
  by_cases hyx : y = x
  · exact hy (hyx ▸ mem_insert_self _ _)
  · exact hy ((hcon y hyS hyx) ▸ mem_insert_of_mem (mem_singleton_self _))

omit [Fintype V] [Fintype X] [DecidableEq V] [DecidableEq X] in
/-- The rows outside a set of deleted rows that contains every gadget row are
base rows. -/
theorem eq_inl_of_notMem {C : Finset (V ⊕ X)} (hC : ∀ x, Sum.inr x ∈ C) {w : V ⊕ X} (hw : w ∉ C) :
    ∃ a, w = Sum.inl a := by
  cases w with
  | inl a => exact ⟨a, rfl⟩
  | inr x => exact absurd (hC x) hw

include hxx' in
/-- **One gadget row deleted**, the out-columns deleted: the row's out-port
has left, and some in-port is entered from outside – from `u` through `xin`
or from `u'` through `xin'`. -/
theorem pdel_attachXor_one (A B : Finset V) (hv : v ∈ B) (hv' : v' ∈ B) (o₀ : X) :
    pdel (attachXor M₀ D u u' v v' xin xin' o o')
      (insert (Sum.inr o₀) (A.map Function.Embedding.inl))
      (B.map Function.Embedding.inl) =
      pdel D {o₀} {xin} * (if u ∈ A then 0 else pdel M₀ (insert u A) B) +
        pdel D {o₀} {xin'} * (if u' ∈ A then 0 else pdel M₀ (insert u' A) B) := by
  have hdel : ∀ x, Sum.inr x ∈ insert (Sum.inr o₀) (A.map Function.Embedding.inl) ∪
      gadgetRows (V := V) {o₀} := fun x => by
    rw [mem_union, mem_insert]
    by_cases hx : x = o₀
    · exact Or.inl (Or.inl (congrArg _ hx))
    · exact Or.inr ((mem_gadgetRows _ _).mpr ⟨x, rfl, fun h => hx (mem_singleton.mp h)⟩)
  rw [pdel_laplace_of_support _ _ _ (gadgetRows {o₀}) (gadgetRows ∅)
    (fun w hw => by
      obtain ⟨x, rfl, hx⟩ := (mem_gadgetRows {o₀} w).mp hw
      rw [mem_insert, not_or]
      exact ⟨fun h => hx (mem_singleton.mpr (Sum.inr.inj h)), notMem_map_inl_of_inr A x⟩)
    (fun w hw => by
      obtain ⟨x, rfl, -⟩ := (mem_gadgetRows ∅ w).mp hw
      exact notMem_map_inl_of_inr B x)
    (attachXor_support hv hv' {o₀})]
  -- only the column sets missing an in-port survive
  have hout : ∀ (S : Finset (V ⊕ X)) (z : X), z ≠ xin → z ≠ xin' → Sum.inr z ∉ S →
      pdel (attachXor M₀ D u u' v v' xin xin' o o')
        (insert (Sum.inr o₀) (A.map Function.Embedding.inl) ∪ gadgetRows {o₀})
        (B.map Function.Embedding.inl ∪ S) = 0 := by
    intro S z hz hz' hzS
    refine pdel_col_zero _ _ _ (b := Sum.inr z) ?_ fun w hw => ?_
    · rw [mem_union, not_or]
      exact ⟨notMem_map_inl_of_inr B z, hzS⟩
    · obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
      exact attachXor_inl_inr_eq_zero a hz hz'
  have hmem : ∀ x : X, gadgetRows (V := V) {x} ∈
      (gadgetRows ∅).powersetCard (gadgetRows (V := V) {o₀}).card := fun x =>
    mem_powersetCard.mpr ⟨gadgetRows_subset _, by
      rw [card_gadgetRows_singleton, card_gadgetRows_singleton]⟩
  have hne : gadgetRows (V := V) {xin} ≠ gadgetRows {xin'} := fun h => by
    have := (mem_gadgetRows (V := V) {xin} (Sum.inr xin')).mpr
      ⟨xin', rfl, fun h' => hxx' (mem_singleton.mp h').symm⟩
    rw [h, mem_gadgetRows] at this
    obtain ⟨y, hy, hy'⟩ := this
    exact hy' (mem_singleton.mpr (Sum.inr.inj hy).symm)
  rw [Finset.sum_eq_add (gadgetRows (V := V) {xin}) (gadgetRows {xin'}) hne ?_
    (fun h => absurd (hmem xin) h)
    (fun h => absurd (hmem xin') h), bperm_gadgetRows _ _ _ _ {o₀} {xin} _ (mem_gadgetRows {xin}),
    bperm_gadgetRows _ _ _ _ {o₀} {xin'} _ (mem_gadgetRows {xin'})]
  swap
  · intro S hS hne
    obtain ⟨z, hzS, hz, hz'⟩ := exists_notMem_of_ne (mem_powersetCard.mp hS).1
      (by rw [(mem_powersetCard.mp hS).2, card_gadgetRows_singleton]) hne.1 hne.2
    rw [hout S z hz hz' hzS, mul_zero]
  congr 1
  · congr 1
    by_cases hu : u ∈ A
    · rw [ite_eq_left hu]
      refine pdel_col_zero _ _ _ (b := Sum.inr xin) ?_ fun w hw => ?_
      · rw [mem_union, not_or]
        exact ⟨notMem_map_inl_of_inr B xin, fun h => by
          obtain ⟨y, hy, hy'⟩ := (mem_gadgetRows {xin} _).mp h
          exact hy' (mem_singleton.mpr (Sum.inr.inj hy).symm)⟩
      · obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
        refine attachXor_inl_inr_xin hxx' fun hau => hw ?_
        rw [hau, mem_union, mem_insert]
        exact Or.inl (Or.inr (mem_map_of_mem _ hu))
    · rw [ite_eq_right hu, pdel_col_single _ _ _ (b := Sum.inr xin) ?_ (a := Sum.inl u) ?_ ?_,
        attachXor_u_xin hxx', one_mul]
      · exact pdel_attach_of_mem _ _ _ _ (insert u A) B _ _
          (mem_insert_inl_union_gadgetRows A u o₀) (mem_insert_inr_union_gadgetRows B xin)
      · rw [mem_union, not_or]
        exact ⟨notMem_map_inl_of_inr B xin, fun h => by
          obtain ⟨y, hy, hy'⟩ := (mem_gadgetRows {xin} _).mp h
          exact hy' (mem_singleton.mpr (Sum.inr.inj hy).symm)⟩
      · rw [mem_union, mem_insert, not_or, not_or]
        refine ⟨⟨by simp, fun h => hu (by simpa using h)⟩, fun h => ?_⟩
        obtain ⟨x, hx, -⟩ := (mem_gadgetRows {o₀} _).mp h
        exact Sum.inl_ne_inr hx
      · intro w hw hne
        obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
        exact attachXor_inl_inr_xin hxx' fun h => hne (congrArg _ h)
  · congr 1
    by_cases hu : u' ∈ A
    · rw [ite_eq_left hu]
      refine pdel_col_zero _ _ _ (b := Sum.inr xin') ?_ fun w hw => ?_
      · rw [mem_union, not_or]
        exact ⟨notMem_map_inl_of_inr B xin', fun h => by
          obtain ⟨y, hy, hy'⟩ := (mem_gadgetRows {xin'} _).mp h
          exact hy' (mem_singleton.mpr (Sum.inr.inj hy).symm)⟩
      · obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
        refine attachXor_inl_inr_xin' hxx' fun hau => hw ?_
        rw [hau, mem_union, mem_insert]
        exact Or.inl (Or.inr (mem_map_of_mem _ hu))
    · rw [ite_eq_right hu, pdel_col_single _ _ _ (b := Sum.inr xin') ?_ (a := Sum.inl u') ?_ ?_,
        attachXor_u'_xin' hxx', one_mul]
      · exact pdel_attach_of_mem _ _ _ _ (insert u' A) B _ _
          (mem_insert_inl_union_gadgetRows A u' o₀) (mem_insert_inr_union_gadgetRows B xin')
      · rw [mem_union, not_or]
        exact ⟨notMem_map_inl_of_inr B xin', fun h => by
          obtain ⟨y, hy, hy'⟩ := (mem_gadgetRows {xin'} _).mp h
          exact hy' (mem_singleton.mpr (Sum.inr.inj hy).symm)⟩
      · rw [mem_union, mem_insert, not_or, not_or]
        refine ⟨⟨by simp, fun h => hu (by simpa using h)⟩, fun h => ?_⟩
        obtain ⟨x, hx, -⟩ := (mem_gadgetRows {o₀} _).mp h
        exact Sum.inl_ne_inr hx
      · intro w hw hne
        obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
        exact attachXor_inl_inr_xin' hxx' fun h => hne (congrArg _ h)

omit [Fintype V] in
theorem mem_insert_inl_inl_union_gadgetRows (A : Finset V) (a a' : V) (o₀ o₁ : X) (w : V ⊕ X) :
    w ∈ insert (Sum.inl a') (insert (Sum.inl a) (insert (Sum.inr o₀) (insert (Sum.inr o₁)
        (A.map Function.Embedding.inl)) ∪ gadgetRows (V := V) {o₀, o₁})) ↔
      (∃ a'' ∈ insert a (insert a' A), w = Sum.inl a'') ∨ ∃ x, w = Sum.inr x := by
  cases w with
  | inl b =>
    simp [mem_gadgetRows, eq_comm]
    tauto
  | inr x =>
    simp [mem_gadgetRows]
    tauto

omit [Fintype V] in
theorem mem_insert_inr_inr_union_gadgetRows (B : Finset V) (x x' : X) (w : V ⊕ X) :
    w ∈ insert (Sum.inr x') (insert (Sum.inr x) (B.map Function.Embedding.inl ∪
        gadgetRows (V := V) {x, x'})) ↔
      (∃ b ∈ B, w = Sum.inl b) ∨ ∃ y, w = Sum.inr y := by
  cases w with
  | inl b => simp [mem_gadgetRows, eq_comm]
  | inr y =>
    simp [mem_gadgetRows]
    tauto

include hxx' in
/-- **Both gadget rows `o`, `o'` deleted**, the out-columns deleted: both
in-ports are entered from outside. -/
theorem pdel_attachXor_two (A B : Finset V) (hv : v ∈ B) (hv' : v' ∈ B) (hoo' : o ≠ o')
    (huu' : u ≠ u') :
    pdel (attachXor M₀ D u u' v v' xin xin' o o')
      (insert (Sum.inr o) (insert (Sum.inr o') (A.map Function.Embedding.inl)))
      (B.map Function.Embedding.inl) =
      pdel D {o, o'} {xin, xin'} *
        (if u ∈ A ∨ u' ∈ A then 0 else pdel M₀ (insert u (insert u' A)) B) := by
  have hdel : ∀ x, Sum.inr x ∈
      insert (Sum.inr o) (insert (Sum.inr o') (A.map Function.Embedding.inl)) ∪
      gadgetRows (V := V) {o, o'} := fun x => by
    rw [mem_union, mem_insert, mem_insert]
    by_cases hx : x = o
    · exact Or.inl (Or.inl (congrArg _ hx))
    by_cases hx' : x = o'
    · exact Or.inl (Or.inr (Or.inl (congrArg _ hx')))
    · exact Or.inr ((mem_gadgetRows _ _).mpr ⟨x, rfl, by simp [hx, hx']⟩)
  rw [pdel_laplace_of_support _ _ _ (gadgetRows {o, o'}) (gadgetRows ∅)
    (fun w hw => by
      obtain ⟨x, rfl, hx⟩ := (mem_gadgetRows {o, o'} w).mp hw
      simp only [mem_insert, mem_singleton, not_or] at hx
      rw [mem_insert, mem_insert, not_or, not_or]
      exact ⟨fun h => hx.1 (Sum.inr.inj h), fun h => hx.2 (Sum.inr.inj h),
        notMem_map_inl_of_inr A x⟩)
    (fun w hw => by
      obtain ⟨x, rfl, -⟩ := (mem_gadgetRows ∅ w).mp hw
      exact notMem_map_inl_of_inr B x)
    (attachXor_support hv hv' {o, o'})]
  have hout : ∀ (S : Finset (V ⊕ X)) (z : X), z ≠ xin → z ≠ xin' → Sum.inr z ∉ S →
      pdel (attachXor M₀ D u u' v v' xin xin' o o')
        (insert (Sum.inr o) (insert (Sum.inr o') (A.map Function.Embedding.inl)) ∪
          gadgetRows {o, o'}) (B.map Function.Embedding.inl ∪ S) = 0 := by
    intro S z hz hz' hzS
    refine pdel_col_zero _ _ _ (b := Sum.inr z) ?_ fun w hw => ?_
    · rw [mem_union, not_or]
      exact ⟨notMem_map_inl_of_inr B z, hzS⟩
    · obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
      exact attachXor_inl_inr_eq_zero a hz hz'
  have hmem : gadgetRows (V := V) {xin, xin'} ∈
      (gadgetRows ∅).powersetCard (gadgetRows (V := V) {o, o'}).card :=
    mem_powersetCard.mpr ⟨gadgetRows_subset _, by
      rw [card_gadgetRows_pair hxx', card_gadgetRows_pair hoo']⟩
  rw [Finset.sum_eq_single (gadgetRows (V := V) {xin, xin'}) ?_ (fun h => absurd hmem h),
    bperm_gadgetRows _ _ _ _ {o, o'} {xin, xin'} _ (mem_gadgetRows {xin, xin'})]
  swap
  · intro S hS hne
    obtain ⟨z, hzS, hz, hz'⟩ := exists_notMem_of_ne_pair (mem_powersetCard.mp hS).1
      (by rw [(mem_powersetCard.mp hS).2, card_gadgetRows_pair hoo']) hxx' hne
    rw [hout S z hz hz' hzS, mul_zero]
  congr 1
  have hcol : ∀ x ∈ ({xin, xin'} : Finset X), Sum.inr x ∉
      B.map (Function.Embedding.inl : V ↪ V ⊕ X) ∪ gadgetRows {xin, xin'} := fun x hx => by
    rw [mem_union, not_or]
    exact ⟨notMem_map_inl_of_inr B x, fun h => by
      obtain ⟨y, hy, hy'⟩ := (mem_gadgetRows {xin, xin'} _).mp h
      exact hy' ((Sum.inr.inj hy) ▸ hx)⟩
  by_cases hA : u ∈ A ∨ u' ∈ A
  · rw [ite_eq_left hA]
    rcases hA with hu | hu'
    · refine pdel_col_zero _ _ _ (hcol xin (mem_insert_self _ _)) fun w hw => ?_
      obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
      refine attachXor_inl_inr_xin hxx' fun hau => hw ?_
      rw [hau, mem_union, mem_insert, mem_insert]
      exact Or.inl (Or.inr (Or.inr (mem_map_of_mem _ hu)))
    · refine pdel_col_zero _ _ _ (hcol xin' (mem_insert_of_mem (mem_singleton_self _)))
        fun w hw => ?_
      obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
      refine attachXor_inl_inr_xin' hxx' fun hau => hw ?_
      rw [hau, mem_union, mem_insert, mem_insert]
      exact Or.inl (Or.inr (Or.inr (mem_map_of_mem _ hu')))
  rw [ite_eq_right hA]
  rw [not_or] at hA
  obtain ⟨hu, hu'⟩ := hA
  rw [pdel_col_single _ _ _ (b := Sum.inr xin) (hcol xin (mem_insert_self _ _)) (a := Sum.inl u)
    ?_ ?_, attachXor_u_xin hxx', one_mul,
    pdel_col_single _ _ _ (b := Sum.inr xin') ?_ (a := Sum.inl u') ?_ ?_, attachXor_u'_xin' hxx',
    one_mul]
  · exact pdel_attach_of_mem _ _ _ _ (insert u (insert u' A)) B _ _
      (mem_insert_inl_inl_union_gadgetRows A u u' o o')
      (mem_insert_inr_inr_union_gadgetRows B xin xin')
  · rw [mem_insert, not_or]
    exact ⟨fun h => hxx' (Sum.inr.inj h).symm, hcol xin' (mem_insert_of_mem (mem_singleton_self _))⟩
  · rw [mem_insert, mem_union, mem_insert, mem_insert, not_or, not_or, not_or, not_or]
    refine ⟨fun h => huu' (Sum.inl.inj h).symm, ⟨by simp, by simp, fun h => hu' (by simpa using h)⟩,
      fun h => ?_⟩
    obtain ⟨x, hx, -⟩ := (mem_gadgetRows {o, o'} _).mp h
    exact Sum.inl_ne_inr hx
  · intro w hw hne
    have hw' : w ∉ insert (Sum.inr o) (insert (Sum.inr o') (A.map Function.Embedding.inl)) ∪
        gadgetRows {o, o'} := fun h => hw (mem_insert_of_mem h)
    obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw'
    exact attachXor_inl_inr_xin' hxx' fun h => hne (congrArg _ h)
  · rw [mem_union, mem_insert, mem_insert, not_or, not_or, not_or]
    refine ⟨⟨by simp, by simp, fun h => hu (by simpa using h)⟩, fun h => ?_⟩
    obtain ⟨x, hx, -⟩ := (mem_gadgetRows {o, o'} _).mp h
    exact Sum.inl_ne_inr hx
  · intro w hw hne
    obtain ⟨a, rfl⟩ := eq_inl_of_notMem hdel hw
    exact attachXor_inl_inr_xin hxx' fun h => hne (congrArg _ h)

/-- A sum over the rows outside a deleted set made of base rows and gadget
rows. -/
theorem sum_compl_of_mem (C : Finset (V ⊕ X)) (A : Finset V) (O : Finset X)
    (hC : ∀ w, w ∈ C ↔ (∃ a ∈ A, w = Sum.inl a) ∨ ∃ x ∈ O, w = Sum.inr x) (f : V ⊕ X → R) :
    ∑ w ∈ Cᶜ, f w = ∑ a ∈ Aᶜ, f (Sum.inl a) + ∑ x ∈ Oᶜ, f (Sum.inr x) := by
  rw [← Finset.sum_disjSum]
  refine Finset.sum_congr (Finset.ext fun w => ?_) fun _ _ => rfl
  rw [mem_compl, hC w]
  cases w <;> simp

/-- The sum over the rows outside `A` of a term vanishing at `u` is the sum
over the rows outside `insert u A`. -/
theorem sum_ite_insert (A : Finset V) {u : V} (hu : u ∉ A) (g : V → R) :
    ∑ a ∈ Aᶜ, (if u ∈ insert a A then 0 else g a) = ∑ a ∈ (insert u A)ᶜ, g a := by
  rw [Finset.compl_insert, ← Finset.sum_erase_add _ _ (mem_compl.mpr hu),
    ite_eq_left (mem_insert_self u A), add_zero]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [ite_eq_right]
  rw [mem_insert, not_or]
  exact ⟨fun h => (mem_erase.mp ha).1 h.symm, hu⟩

omit [Fintype V] [Fintype X] in
theorem insert_inl_map (a : V) (A : Finset V) :
    insert (Sum.inl a) (A.map Function.Embedding.inl) =
      (insert a A).map (Function.Embedding.inl : V ↪ V ⊕ X) := by
  rw [Finset.map_insert]
  rfl

/-- The expansion of a base minor along a column, with the row entering
excluded by the condition of the pattern. -/
theorem sum_expand_ite (A B' : Finset V) {u b : V} (hb : b ∉ B') (P : R) :
    ∑ a ∈ Aᶜ, M₀ a b * (P * (if u ∈ insert a A then 0
      else pdel M₀ (insert u (insert a A)) (insert b B'))) =
      P * (if u ∈ A then 0 else pdel M₀ (insert u A) B') := by
  by_cases hu : u ∈ A
  · simp [hu]
  rw [ite_eq_right hu, pdel_col M₀ (insert u A) B' hb, Finset.mul_sum, ← sum_ite_insert A hu]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hc : u ∈ insert a A
  · simp only [hc, ↓reduceIte]
    ring
  · simp only [hc, ↓reduceIte, pdel_congr M₀ (Finset.insert_comm u a A) rfl]
    ring

include hxx' in
/-- **The expansion of the XOR gadget shape.** The permanent of the matrix with
the gadget is the sum, over the patterns of use of its ports, of the
permanent of the gadget minor of the pattern times the permanent of the base
minor with the rows entering and the columns left: no port used; the first
in-port entered from `u` and the first out-port left to `v`, or the second
out-port left to `v'`; the second in-port entered from `u'` likewise; both
in-ports entered and both out-ports left. -/
theorem pdel_attachXor (A B : Finset V) (hoo' : o ≠ o') (huu' : u ≠ u') (hvv' : v ≠ v')
    (hv : v ∉ B) (hv' : v' ∉ B) :
    pdel (attachXor M₀ D u u' v v' xin xin' o o') (A.map Function.Embedding.inl)
      (B.map Function.Embedding.inl) =
      pdel D ∅ ∅ * pdel M₀ A B
      + pdel D {o} {xin} * (if u ∈ A then 0 else pdel M₀ (insert u A) (insert v B))
      + pdel D {o} {xin'} * (if u' ∈ A then 0 else pdel M₀ (insert u' A) (insert v B))
      + pdel D {o'} {xin} * (if u ∈ A then 0 else pdel M₀ (insert u A) (insert v' B))
      + pdel D {o'} {xin'} * (if u' ∈ A then 0 else pdel M₀ (insert u' A) (insert v' B))
      + pdel D {o, o'} {xin, xin'} * (if u ∈ A ∨ u' ∈ A then 0
          else pdel M₀ (insert u (insert u' A)) (insert v (insert v' B))) := by
  have hcolv : ∀ x, x ≠ o → attachXor M₀ D u u' v v' xin xin' o o' (Sum.inr x) (Sum.inl v) = 0 :=
    fun x hx => by
    rw [attachXor_inr_inl, ite_eq_right fun (h : x = o ∧ v = v) => hx h.1,
      ite_eq_right fun (h : x = o' ∧ v = v') => hvv' h.2, add_zero]
  have hcolv' : ∀ x, x ≠ o' →
      attachXor M₀ D u u' v v' xin xin' o o' (Sum.inr x) (Sum.inl v') = 0 := fun x hx => by
    rw [attachXor_inr_inl, ite_eq_right fun (h : x = o ∧ v' = v) => hvv' h.2.symm,
      ite_eq_right fun (h : x = o' ∧ v' = v') => hx h.1, add_zero]
  have hov : attachXor M₀ D u u' v v' xin xin' o o' (Sum.inr o) (Sum.inl v) = 1 := by
    rw [attachXor_inr_inl, ite_eq_left ⟨rfl, rfl⟩,
      ite_eq_right fun (h : o = o' ∧ v = v') => hvv' h.2, add_zero]
  have hov' : attachXor M₀ D u u' v v' xin xin' o o' (Sum.inr o') (Sum.inl v') = 1 := by
    rw [attachXor_inr_inl, ite_eq_right fun (h : o' = o ∧ v' = v) => hvv' h.2.symm,
      ite_eq_left ⟨rfl, rfl⟩, zero_add]
  have hvB : Sum.inl v ∉ B.map (Function.Embedding.inl : V ↪ V ⊕ X) := by
    rw [mem_map]
    rintro ⟨b, hb, hb'⟩
    exact hv (Sum.inl.inj hb' ▸ hb)
  have hv'B : Sum.inl v' ∉ (insert v B).map (Function.Embedding.inl : V ↪ V ⊕ X) := by
    rw [mem_map]
    rintro ⟨b, hb, hb'⟩
    exact (mem_insert.mp hb).elim (fun h => hvv' (h ▸ Sum.inl.inj hb'))
      fun h => hv' (Sum.inl.inj hb' ▸ h)
  have hvv'B : v' ∉ insert v B := by
    rw [mem_insert, not_or]
    exact ⟨hvv'.symm, hv'⟩
  have hv'vB : v ∉ insert v' B := by
    rw [mem_insert, not_or]
    exact ⟨hvv', hv⟩
  -- the base part: a base row `a` takes the column `v`
  have base : ∀ a ∈ Aᶜ, pdel (attachXor M₀ D u u' v v' xin xin' o o')
      ((insert a A).map Function.Embedding.inl)
      ((insert v B).map Function.Embedding.inl) =
      pdel D ∅ ∅ * pdel M₀ (insert a A) (insert v B)
      + pdel D {o'} {xin} * (if u ∈ insert a A then 0
          else pdel M₀ (insert u (insert a A)) (insert v' (insert v B)))
      + pdel D {o'} {xin'} * (if u' ∈ insert a A then 0
          else pdel M₀ (insert u' (insert a A)) (insert v' (insert v B))) := by
    intro a _
    rw [pdel_col _ _ _ (b := Sum.inl v') hv'B,
      sum_compl_of_mem _ (insert a A) ∅ (fun w => by simp [eq_comm]) _,
      Finset.sum_eq_single o' (fun x _ hx => by rw [hcolv' x hx, zero_mul])
        (fun h => absurd (mem_compl.mpr (Finset.notMem_empty o')) h), hov', one_mul,
      insert_inl_map, pdel_attachXor_one hxx' _ _ (mem_insert_of_mem (mem_insert_self _ _))
        (mem_insert_self _ _) o', pdel_col M₀ (insert a A) (insert v B) hvv'B, Finset.mul_sum,
      ← add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [insert_inl_map, pdel_attachXor_block _ _
      (mem_insert_of_mem (mem_insert_self _ _)) (mem_insert_self _ _)]
    change M₀ a' v' * _ = _
    ring
  -- the gadget part: the row `o` takes the column `v`
  have gadget : pdel (attachXor M₀ D u u' v v' xin xin' o o')
      (insert (Sum.inr o) (A.map Function.Embedding.inl))
      ((insert v B).map Function.Embedding.inl) =
      pdel D {o} {xin} * (if u ∈ A then 0 else pdel M₀ (insert u A) (insert v B))
      + pdel D {o} {xin'} * (if u' ∈ A then 0 else pdel M₀ (insert u' A) (insert v B))
      + pdel D {o, o'} {xin, xin'} * (if u ∈ A ∨ u' ∈ A then 0
          else pdel M₀ (insert u (insert u' A)) (insert v (insert v' B))) := by
    rw [pdel_col _ _ _ (b := Sum.inl v') hv'B,
      sum_compl_of_mem _ A {o} (fun w => by simp [eq_comm, or_comm]) _,
      Finset.sum_eq_single o' (fun x _ hx => by rw [hcolv' x hx, zero_mul])
        (fun h => absurd (mem_compl.mpr (by simpa using hoo'.symm)) h), hov', one_mul,
      Finset.insert_comm (Sum.inr o') (Sum.inr o), insert_inl_map, pdel_attachXor_two hxx' A _
        (mem_insert_of_mem (mem_insert_self _ _)) (mem_insert_self _ _) hoo' huu',
      pdel_congr M₀ rfl (Finset.insert_comm v' v B)]
    congr 1
    have : ∀ a ∈ Aᶜ, attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl a) (Sum.inl v') *
        pdel (attachXor M₀ D u u' v v' xin xin' o o')
          (insert (Sum.inl a) (insert (Sum.inr o) (A.map Function.Embedding.inl)))
          ((insert v' (insert v B)).map Function.Embedding.inl) =
        M₀ a v' * (pdel D {o} {xin} * (if u ∈ insert a A then 0
          else pdel M₀ (insert u (insert a A)) (insert v' (insert v B)))
        + pdel D {o} {xin'} * (if u' ∈ insert a A then 0
          else pdel M₀ (insert u' (insert a A)) (insert v' (insert v B)))) := by
      intro a _
      rw [Finset.insert_comm (Sum.inl a) (Sum.inr o), insert_inl_map,
        pdel_attachXor_one hxx' _ _ (mem_insert_of_mem (mem_insert_self _ _))
          (mem_insert_self _ _) o]
      rfl
    rw [Finset.sum_congr rfl this]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [sum_expand_ite A (insert v B) hvv'B, sum_expand_ite A (insert v B) hvv'B]
  rw [pdel_col _ _ _ (b := Sum.inl v) hvB, sum_compl_of_mem _ A ∅ (fun w => by simp [eq_comm]) _,
    Finset.sum_eq_single o (fun x _ hx => by rw [hcolv x hx, zero_mul])
      (fun h => absurd (mem_compl.mpr (Finset.notMem_empty o)) h), hov, one_mul, insert_inl_map,
    gadget]
  have : ∀ a ∈ Aᶜ, attachXor M₀ D u u' v v' xin xin' o o' (Sum.inl a) (Sum.inl v) *
      pdel (attachXor M₀ D u u' v v' xin xin' o o')
        (insert (Sum.inl a) (A.map Function.Embedding.inl))
        ((insert v B).map Function.Embedding.inl) =
      M₀ a v * (pdel D ∅ ∅ * pdel M₀ (insert a A) (insert v B)
      + pdel D {o'} {xin} * (if u ∈ insert a A then 0
          else pdel M₀ (insert u (insert a A)) (insert v (insert v' B)))
      + pdel D {o'} {xin'} * (if u' ∈ insert a A then 0
          else pdel M₀ (insert u' (insert a A)) (insert v (insert v' B)))) := by
    intro a ha
    rw [insert_inl_map, base a ha]
    simp only [Finset.insert_comm v' v B]
    rfl
  rw [Finset.sum_congr rfl this]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_expand_ite A (insert v' B) hv'vB, sum_expand_ite A (insert v' B) hv'vB]
  have e0 : ∑ a ∈ Aᶜ, M₀ a v * (pdel D ∅ ∅ * pdel M₀ (insert a A) (insert v B)) =
      pdel D ∅ ∅ * pdel M₀ A B := by
    rw [pdel_col M₀ A B hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e0]
  ring

end Xor

end Attach


end DescriptiveComplexity
