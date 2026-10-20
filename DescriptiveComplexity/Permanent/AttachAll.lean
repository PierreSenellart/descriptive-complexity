/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Permanent.Xor

/-!
# Attaching Valiant's gadget at every site of a list

A **site** is a pair of edges `u → v`, `u' → v'` of a base matrix
(`DescriptiveComplexity.Site`). Attaching Valiant's gadget at every site of a
list `l` (`DescriptiveComplexity.Site.attachAll`, on the node type
`DescriptiveComplexity.Site.AttachType V l` that adds four nodes per site)
multiplies the permanent by `4` per site and leaves the **XOR sum**
(`DescriptiveComplexity.Site.xorSum`): the sum, over the choices of one edge
per site, of the permanent of the base minor with the rows and columns of
the chosen edges deleted, a choice contributing nothing when it deletes a
row twice (`DescriptiveComplexity.Site.pdel_attachAll`). The columns of the
sites must be pairwise distinct and the two rows of a site distinct; the
rows of different sites may coincide, which is what the vanishing of the
repeated choices is for.

The XOR sum is the number of cycle covers of the base graph with the pair
edges in place that use exactly one edge of each site, weighted by the base
entries (`DescriptiveComplexity.Site.xorSum_eq_sum`, as a sum over the choice
functions).
-/

namespace DescriptiveComplexity

open Finset

/-- **A site**: the two edges `u → v` and `u' → v'` a gadget replaces. -/
structure Site (V : Type) where
  /-- The row of the first edge. -/
  u : V
  /-- The row of the second edge. -/
  u' : V
  /-- The column of the first edge. -/
  v : V
  /-- The column of the second edge. -/
  v' : V
  deriving DecidableEq

namespace Site

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The nodes after attaching a gadget at every site of the list: four more
per site. -/
abbrev AttachType (V : Type) : List (Site V) → Type
  | [] => V
  | _ :: l => AttachType V l ⊕ Fin 4

instance instFintypeAttachType : ∀ l : List (Site V), Fintype (AttachType V l)
  | [] => inferInstanceAs (Fintype V)
  | _ :: l => @instFintypeSum _ _ (instFintypeAttachType l) _

instance instDecidableEqAttachType : ∀ l : List (Site V), DecidableEq (AttachType V l)
  | [] => inferInstanceAs (DecidableEq V)
  | _ :: l => @instDecidableEqSum _ _ (instDecidableEqAttachType l) _

/-- The base nodes, among the nodes after the attachments. -/
def base : ∀ l : List (Site V), V → AttachType V l
  | [], a => a
  | _ :: l, a => Sum.inl (base l a)

omit [Fintype V] [DecidableEq V] in
theorem base_injective : ∀ l : List (Site V), Function.Injective (base l)
  | [] => fun _ _ h => h
  | _ :: l => fun _ _ h => base_injective l (Sum.inl.inj h)

/-- The base nodes, as an embedding. -/
def baseEmb (l : List (Site V)) : V ↪ AttachType V l :=
  ⟨base l, base_injective l⟩

omit [Fintype V] [DecidableEq V] in
theorem map_baseEmb_cons (s : Site V) (l : List (Site V)) (A : Finset V) :
    A.map (baseEmb (s :: l)) = (A.map (baseEmb l)).map Function.Embedding.inl :=
  (Finset.map_map (baseEmb l) Function.Embedding.inl A).symm

omit [Fintype V] [DecidableEq V] in
theorem map_baseEmb_nil (A : Finset V) : A.map (baseEmb []) = A :=
  Finset.map_refl

/-- **The gadgets attached at every site of the list.** -/
def attachAll (M₀ : V → V → ℤ) : ∀ l : List (Site V), AttachType V l → AttachType V l → ℤ
  | [] => M₀
  | s :: l => attachValiant (attachAll M₀ l) (baseEmb l s.u) (baseEmb l s.u') (baseEmb l s.v)
      (baseEmb l s.v')

/-- **The XOR sum**: one edge chosen per site, its row and column deleted, a
choice deleting a row twice contributing nothing. -/
noncomputable def xorSum (M₀ : V → V → ℤ) : List (Site V) → Finset V → Finset V → ℤ
  | [], A, B => pdel M₀ A B
  | s :: l, A, B =>
      (if s.u ∈ A then 0 else xorSum M₀ l (insert s.u A) (insert s.v B)) +
        if s.u' ∈ A then 0 else xorSum M₀ l (insert s.u' A) (insert s.v' B)

/-- The columns of the sites of a list. -/
def cols : List (Site V) → List V
  | [] => []
  | s :: l => s.v :: s.v' :: cols l

omit [Fintype V] [DecidableEq V] in
theorem mem_cols_v (l : List (Site V)) (t : Site V) (ht : t ∈ l) : t.v ∈ cols l := by
  induction l with
  | nil => simp at ht
  | cons s l ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih ht))

omit [Fintype V] [DecidableEq V] in
theorem mem_cols_v' (l : List (Site V)) (t : Site V) (ht : t ∈ l) : t.v' ∈ cols l := by
  induction l with
  | nil => simp at ht
  | cons s l ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih ht))

/-- **Attaching a gadget at every site multiplies the permanent by `4` per
site and leaves the XOR sum.** -/
theorem pdel_attachAll (M₀ : V → V → ℤ) :
    ∀ (l : List (Site V)) (A B : Finset V), (∀ s ∈ l, s.u ≠ s.u') → (cols l).Nodup →
      (∀ s ∈ l, s.v ∉ B ∧ s.v' ∉ B) →
      pdel (attachAll M₀ l) (A.map (baseEmb l)) (B.map (baseEmb l)) =
        4 ^ l.length * xorSum M₀ l A B
  | [], A, B, _, _, _ => by
    rw [attachAll, xorSum, List.length_nil, pow_zero, one_mul, map_baseEmb_nil, map_baseEmb_nil]
  | s :: l, A, B, hu, hcols, hB => by
    have hnd := List.nodup_cons.mp hcols
    have hnd' := List.nodup_cons.mp hnd.2
    have hBl : ∀ t ∈ l, t.v ∉ insert s.v B ∧ t.v' ∉ insert s.v B := fun t ht => by
      obtain ⟨h1, h2⟩ := hB t (List.mem_cons_of_mem s ht)
      refine ⟨?_, ?_⟩ <;> rw [mem_insert, not_or]
      · exact ⟨fun h => hnd.1 (by rw [← h]; exact List.mem_cons_of_mem _ (mem_cols_v l t ht)), h1⟩
      · exact ⟨fun h => hnd.1 (by rw [← h]; exact List.mem_cons_of_mem _ (mem_cols_v' l t ht)), h2⟩
    have hBl' : ∀ t ∈ l, t.v ∉ insert s.v' B ∧ t.v' ∉ insert s.v' B := fun t ht => by
      obtain ⟨h1, h2⟩ := hB t (List.mem_cons_of_mem s ht)
      refine ⟨?_, ?_⟩ <;> rw [mem_insert, not_or]
      · exact ⟨fun h => hnd'.1 (by rw [← h]; exact mem_cols_v l t ht), h1⟩
      · exact ⟨fun h => hnd'.1 (by rw [← h]; exact mem_cols_v' l t ht), h2⟩
    rw [attachAll, map_baseEmb_cons, map_baseEmb_cons, pdel_attachValiant _ _ _ _ _ _ _
      (fun h => hu s List.mem_cons_self ((baseEmb l).injective h))
      (fun h => hnd.1 (by rw [(baseEmb l).injective h]; exact List.mem_cons_self))
      (by rw [Finset.mem_map']; exact (hB s List.mem_cons_self).1)
      (by rw [Finset.mem_map']; exact (hB s List.mem_cons_self).2),
      xorSum, List.length_cons, pow_succ, ← Finset.map_insert, ← Finset.map_insert,
      ← Finset.map_insert, ← Finset.map_insert,
      pdel_attachAll M₀ l _ _ (fun t ht => hu t (List.mem_cons_of_mem s ht)) hnd'.2 hBl,
      pdel_attachAll M₀ l _ _ (fun t ht => hu t (List.mem_cons_of_mem s ht)) hnd'.2 hBl']
    simp only [Finset.mem_map']
    split_ifs <;> ring

/-! ### The XOR sum of self-loop sites, as a sum over the subsets of sites -/

/-- The rows deleted by a choice of one edge per site: the first row of the
sites in `T`, the second row of the others. -/
def delRows (l : List (Site V)) (T : Finset (Site V)) : Finset V :=
  l.toFinset.image fun s => if s ∈ T then s.u else s.u'

omit [Fintype V] in
theorem delRows_nil (T : Finset (Site V)) : delRows [] T = ∅ := by
  simp [delRows]

omit [Fintype V] in
theorem delRows_cons (s : Site V) (l : List (Site V)) (T : Finset (Site V)) :
    delRows (s :: l) T = insert (if s ∈ T then s.u else s.u') (delRows l T) := by
  rw [delRows, delRows, List.toFinset_cons, Finset.image_insert]

omit [Fintype V] in
theorem delRows_insert_of_notMem {s : Site V} {l : List (Site V)} (hs : s ∉ l)
    (T : Finset (Site V)) : delRows l (insert s T) = delRows l T :=
  Finset.image_congr fun t ht => by
    have hne : t ≠ s := fun h => hs (h ▸ List.mem_toFinset.mp ht)
    simp only [Finset.mem_insert, hne, false_or]

/-- **The XOR sum of self-loop sites**: when every site pairs two self-loops,
the sum is over the subsets `T` of the sites, the first loop chosen at the
sites of `T` and the second elsewhere, of the principal minor of the base
matrix with the chosen rows deleted. -/
theorem xorSum_eq_sum (M₀ : V → V → ℤ) :
    ∀ (l : List (Site V)), (cols l).Nodup → (∀ s ∈ l, s.v = s.u ∧ s.v' = s.u') →
      ∀ A : Finset V, (∀ s ∈ l, s.u ∉ A ∧ s.u' ∉ A) →
        xorSum M₀ l A A = ∑ T ∈ l.toFinset.powerset, pdel M₀ (A ∪ delRows l T) (A ∪ delRows l T)
  | [], _, _, A, _ => by
    rw [xorSum, List.toFinset_nil, Finset.powerset_empty, Finset.sum_singleton, delRows_nil,
      Finset.union_empty]
  | s :: l, hcols, hself, A, hA => by
    have hnd := List.nodup_cons.mp hcols
    have hnd' := List.nodup_cons.mp hnd.2
    have hs := hself s List.mem_cons_self
    have hsA := hA s List.mem_cons_self
    have hl' : ∀ t ∈ l, t.v = t.u ∧ t.v' = t.u' := fun t ht => hself t (List.mem_cons_of_mem s ht)
    have hsl : s ∉ l := fun h => hnd.1 (List.mem_cons_of_mem _ (mem_cols_v l s h))
    have hAu : ∀ t ∈ l, t.u ∉ insert s.u A ∧ t.u' ∉ insert s.u A := fun t ht => by
      obtain ⟨h1, h2⟩ := hA t (List.mem_cons_of_mem s ht)
      obtain ⟨ht1, ht2⟩ := hl' t ht
      refine ⟨?_, ?_⟩ <;> rw [Finset.mem_insert, not_or]
      · exact ⟨fun h => hnd.1 (by
          rw [← hs.1, ← ht1] at h
          rw [← h]
          exact List.mem_cons_of_mem _ (mem_cols_v l t ht)), h1⟩
      · exact ⟨fun h => hnd.1 (by
          rw [← hs.1, ← ht2] at h
          rw [← h]
          exact List.mem_cons_of_mem _ (mem_cols_v' l t ht)), h2⟩
    have hAu' : ∀ t ∈ l, t.u ∉ insert s.u' A ∧ t.u' ∉ insert s.u' A := fun t ht => by
      obtain ⟨h1, h2⟩ := hA t (List.mem_cons_of_mem s ht)
      obtain ⟨ht1, ht2⟩ := hl' t ht
      refine ⟨?_, ?_⟩ <;> rw [Finset.mem_insert, not_or]
      · exact ⟨fun h => hnd'.1 (by
          rw [← hs.2, ← ht1] at h
          rw [← h]
          exact mem_cols_v l t ht), h1⟩
      · exact ⟨fun h => hnd'.1 (by
          rw [← hs.2, ← ht2] at h
          rw [← h]
          exact mem_cols_v' l t ht), h2⟩
    rw [xorSum, hs.1, hs.2, ite_eq_right hsA.1, ite_eq_right hsA.2,
      xorSum_eq_sum M₀ l hnd'.2 hl' _ hAu, xorSum_eq_sum M₀ l hnd'.2 hl' _ hAu',
      List.toFinset_cons, Finset.powerset_insert, Finset.sum_union, Finset.sum_image, add_comm]
    · refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun T hT => ?_)
        (Finset.sum_congr rfl fun T hT => ?_)
      · have hsT : s ∉ T := fun h => hsl (List.mem_toFinset.mp (Finset.mem_powerset.mp hT h))
        rw [delRows_cons, ite_eq_right hsT, Finset.union_insert, Finset.insert_union]
      · rw [delRows_cons, ite_eq_left (Finset.mem_insert_self s T), delRows_insert_of_notMem hsl,
          Finset.union_insert, Finset.insert_union]
    · intro T hT T' hT' h
      have hsT : s ∉ T := fun h => hsl (List.mem_toFinset.mp (Finset.mem_powerset.mp hT h))
      have hsT' : s ∉ T' := fun h => hsl (List.mem_toFinset.mp (Finset.mem_powerset.mp hT' h))
      rw [← Finset.erase_insert hsT, h, Finset.erase_insert hsT']
    · rw [Finset.disjoint_left]
      intro T hT hT'
      obtain ⟨T', -, rfl⟩ := Finset.mem_image.mp hT'
      exact hsl (List.mem_toFinset.mp (Finset.mem_powerset.mp hT (Finset.mem_insert_self s T')))

end Site

end DescriptiveComplexity
