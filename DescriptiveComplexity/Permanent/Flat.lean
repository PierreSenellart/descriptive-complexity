/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Permanent.AttachAll

/-!
# The gadgets attached at every site, flattened

`DescriptiveComplexity.Site.attachAll` attaches Valiant's gadget at the
sites of a list, one sum type `⊕ Fin 4` at a time; the reductions draw the
same matrix on the **flat** node type `V ⊕ (S × Fin 4)`, the gadget nodes
indexed by the sites themselves (`DescriptiveComplexity.Site.flatAttach`).
The two have the same permanent (`DescriptiveComplexity.Site.bperm_flatAttach`):
the nested type and the flat one are in bijection, entry by entry.
-/

namespace DescriptiveComplexity

open Finset

namespace Site

variable {V S : Type} [Fintype V] [DecidableEq V] [DecidableEq S]

/-- **The gadgets attached at every site, on the flat node type**: the base
matrix on `V`, and four gadget nodes per site. The first edge of a site
enters its gadget at node `0` and leaves from node `3`, the second enters
at `3` and leaves from `0`, as in `DescriptiveComplexity.attachValiant`. -/
def flatAttach (M₀ : V → V → ℤ) (site : S → Site V) :
    V ⊕ (S × Fin 4) → V ⊕ (S × Fin 4) → ℤ
  | Sum.inl a, Sum.inl b => M₀ a b
  | Sum.inl a, Sum.inr (s, x) =>
      (if a = (site s).u ∧ x = 0 then 1 else 0) + if a = (site s).u' ∧ x = 3 then 1 else 0
  | Sum.inr (s, x), Sum.inl b =>
      (if x = 3 ∧ b = (site s).v then 1 else 0) + if x = 0 ∧ b = (site s).v' then 1 else 0
  | Sum.inr (s, x), Sum.inr (s', y) => if s = s' then xorGadget x y else 0

omit [Fintype V] in
/-- The flat matrix only depends on the sites through the sites themselves:
it is invariant under an injective reindexing of the sites. -/
theorem flatAttach_map {S' : Type} [DecidableEq S'] (M₀ : V → V → ℤ) (site : S → Site V)
    (site' : S' → Site V) (f : S → S') (hf : Function.Injective f)
    (hsite : ∀ s, site' (f s) = site s) (n n' : V ⊕ (S × Fin 4)) :
    flatAttach M₀ site' (n.map id (Prod.map f id)) (n'.map id (Prod.map f id)) =
      flatAttach M₀ site n n' := by
  rcases n with a | ⟨s, x⟩ <;> rcases n' with b | ⟨s', y⟩
  · rfl
  · simp only [Sum.map_inl, Sum.map_inr, Prod.map_apply, id, flatAttach, hsite]
  · simp only [Sum.map_inl, Sum.map_inr, Prod.map_apply, id, flatAttach, hsite]
  · simp only [Sum.map_inr, Prod.map_apply, id, flatAttach, hf.eq_iff]

/-! ### The nested node type, flattened -/

variable (site : S → Site V)

/-- The nested node type of the attachments along a list, read on the flat
node type. -/
def toFlat : ∀ l : List S, AttachType V (l.map site) → V ⊕ ({s // s ∈ l} × Fin 4)
  | [], a => Sum.inl a
  | s₀ :: l, Sum.inl n =>
      (toFlat l n).map id (Prod.map (fun s => ⟨s.1, List.mem_cons_of_mem s₀ s.2⟩) id)
  | _ :: _, Sum.inr x => Sum.inr (⟨_, List.mem_cons_self⟩, x)

/-- The flat node type, read on the nested one. -/
def ofFlat : ∀ l : List S, V ⊕ ({s // s ∈ l} × Fin 4) → AttachType V (l.map site)
  | [], Sum.inl a => a
  | [], Sum.inr (s, _) => absurd s.2 (List.not_mem_nil)
  | _ :: l, Sum.inl a => Sum.inl (ofFlat l (Sum.inl a))
  | s₀ :: l, Sum.inr (s, x) =>
      if h : s.1 = s₀ then Sum.inr x
      else Sum.inl (ofFlat l (Sum.inr (⟨s.1, (List.mem_cons.mp s.2).resolve_left h⟩, x)))

omit [Fintype V] [DecidableEq V] [DecidableEq S] in
theorem toFlat_base : ∀ (l : List S) (a : V), toFlat site l (base (l.map site) a) = Sum.inl a
  | [], _ => rfl
  | s₀ :: l, a => by
    rw [show base ((s₀ :: l).map site) a = Sum.inl (base (l.map site) a) from rfl, toFlat,
      toFlat_base l a]
    rfl

omit [Fintype V] [DecidableEq V] in
theorem ofFlat_inl : ∀ (l : List S) (a : V), ofFlat site l (Sum.inl a) = base (l.map site) a
  | [], _ => rfl
  | _ :: l, a => by
    rw [ofFlat, ofFlat_inl l a]
    rfl

omit [Fintype V] [DecidableEq V] in
theorem ofFlat_toFlat : ∀ (l : List S), l.Nodup → ∀ n : AttachType V (l.map site),
    ofFlat site l (toFlat site l n) = n
  | [], _, _ => rfl
  | s₀ :: l, hl, Sum.inl n => by
    have ih := ofFlat_toFlat l (List.nodup_cons.mp hl).2 n
    rw [toFlat]
    generalize toFlat site l n = m at ih ⊢
    rcases m with a | ⟨s, x⟩
    · rw [ofFlat_inl] at ih
      simp only [Sum.map_inl, id]
      rw [ofFlat, ofFlat_inl, ih]
    · simp only [Sum.map_inr, Prod.map_apply, id]
      rw [ofFlat, dite_eq_right fun h : s.1 = s₀ => (List.nodup_cons.mp hl).1 (h ▸ s.2)]
      exact congrArg Sum.inl ih
  | _ :: _, _, Sum.inr _ => by
    rw [toFlat, ofFlat, dite_eq_left rfl]

omit [Fintype V] [DecidableEq V] in
theorem toFlat_ofFlat : ∀ (l : List S) (n : V ⊕ ({s // s ∈ l} × Fin 4)),
    toFlat site l (ofFlat site l n) = n
  | [], Sum.inl _ => rfl
  | [], Sum.inr (s, _) => absurd s.2 (List.not_mem_nil)
  | _ :: l, Sum.inl a => by
    rw [ofFlat, toFlat, toFlat_ofFlat l]
    rfl
  | s₀ :: l, Sum.inr (s, x) => by
    rw [ofFlat]
    by_cases h : s.1 = s₀
    · rw [dite_eq_left h, toFlat]
      exact congrArg Sum.inr (Prod.ext (Subtype.ext h.symm) rfl)
    · rw [dite_eq_right h, toFlat, toFlat_ofFlat l]
      rfl

/-- **The nested and the flat node types are in bijection.** -/
def flatEquiv (l : List S) (hl : l.Nodup) :
    AttachType V (l.map site) ≃ V ⊕ ({s // s ∈ l} × Fin 4) where
  toFun := toFlat site l
  invFun := ofFlat site l
  left_inv := ofFlat_toFlat site l hl
  right_inv := toFlat_ofFlat site l

omit [Fintype V] [DecidableEq V] [DecidableEq S] in
theorem toFlat_injective (l : List S) (hl : l.Nodup) : Function.Injective (toFlat site l) := by
  classical
  exact (flatEquiv site l hl).injective

omit [Fintype V] [DecidableEq V] [DecidableEq S] in
theorem toFlat_eq_inl_iff (l : List S) (hl : l.Nodup) (n : AttachType V (l.map site)) (a : V) :
    toFlat site l n = Sum.inl a ↔ n = base (l.map site) a :=
  ⟨fun h => toFlat_injective site l hl (h.trans (toFlat_base site l a).symm),
    fun h => h ▸ toFlat_base site l a⟩

omit [Fintype V] in
/-- **The attached matrix, entry by entry, is the flat one.** -/
theorem attachAll_eq_flatAttach (M₀ : V → V → ℤ) :
    ∀ (l : List S), l.Nodup → ∀ n n' : AttachType V (l.map site),
      attachAll M₀ (l.map site) n n' =
        flatAttach M₀ (fun s : {s // s ∈ l} => site s.1) (toFlat site l n) (toFlat site l n')
  | [], _, _, _ => rfl
  | s₀ :: l, hl, n, n' => by
    have hnd := List.nodup_cons.mp hl
    have ih := attachAll_eq_flatAttach M₀ l hnd.2
    have hinj : Function.Injective fun s : {s // s ∈ l} =>
        (⟨s.1, List.mem_cons_of_mem s₀ s.2⟩ : {s // s ∈ s₀ :: l}) :=
      fun s s' h => Subtype.ext (congrArg (fun t : {s // s ∈ s₀ :: l} => t.1) h)
    have hA : attachAll M₀ ((s₀ :: l).map site) = attachValiant (attachAll M₀ (l.map site))
        (baseEmb (l.map site) (site s₀).u) (baseEmb (l.map site) (site s₀).u')
        (baseEmb (l.map site) (site s₀).v) (baseEmb (l.map site) (site s₀).v') := rfl
    rcases n with n | x <;> rcases n' with n' | y
    · rw [hA, attachValiant, attachXor_inl_inl, ih n n', toFlat, toFlat,
        flatAttach_map M₀ _ _ _ hinj fun _ => rfl]
    · rw [hA, attachValiant, attachXor_inl_inr, toFlat, toFlat]
      generalize hm : toFlat site l n = m
      rcases m with a | ⟨s, z⟩
      · rw [toFlat_eq_inl_iff site l hnd.2] at hm
        subst hm
        simp only [Sum.map_inl, flatAttach, baseEmb, Function.Embedding.coeFn_mk,
          (base_injective _).eq_iff, id]
      · have h1 : n ≠ baseEmb (l.map site) (site s₀).u := fun h => by
          rw [h, baseEmb, Function.Embedding.coeFn_mk, toFlat_base] at hm
          exact Sum.inl_ne_inr hm
        have h2 : n ≠ baseEmb (l.map site) (site s₀).u' := fun h => by
          rw [h, baseEmb, Function.Embedding.coeFn_mk, toFlat_base] at hm
          exact Sum.inl_ne_inr hm
        simp only [Sum.map_inr, Prod.map_apply, id, flatAttach, h1, h2, false_and, ↓reduceIte,
          add_zero]
        rw [ite_eq_right fun h : (⟨s.1, List.mem_cons_of_mem s₀ s.2⟩ : {s // s ∈ s₀ :: l}) =
          ⟨s₀, List.mem_cons_self⟩ => hnd.1 (by
            have h' : s.1 = s₀ := congrArg Subtype.val h
            exact h' ▸ s.2)]
    · rw [hA, attachValiant, attachXor_inr_inl, toFlat, toFlat]
      generalize hm : toFlat site l n' = m
      rcases m with b | ⟨s, z⟩
      · rw [toFlat_eq_inl_iff site l hnd.2] at hm
        subst hm
        simp only [Sum.map_inl, flatAttach, baseEmb, Function.Embedding.coeFn_mk,
          (base_injective _).eq_iff, id]
      · have h1 : n' ≠ baseEmb (l.map site) (site s₀).v := fun h => by
          rw [h, baseEmb, Function.Embedding.coeFn_mk, toFlat_base] at hm
          exact Sum.inl_ne_inr hm
        have h2 : n' ≠ baseEmb (l.map site) (site s₀).v' := fun h => by
          rw [h, baseEmb, Function.Embedding.coeFn_mk, toFlat_base] at hm
          exact Sum.inl_ne_inr hm
        simp only [Sum.map_inr, Prod.map_apply, id, flatAttach, h1, h2, and_false, ↓reduceIte,
          add_zero]
        rw [ite_eq_right fun h : (⟨s₀, List.mem_cons_self⟩ : {s // s ∈ s₀ :: l}) =
          ⟨s.1, List.mem_cons_of_mem s₀ s.2⟩ => hnd.1 (by
            have h' : s₀ = s.1 := congrArg Subtype.val h
            exact h' ▸ s.2)]
    · rw [hA, attachValiant, attachXor_inr_inr, toFlat, toFlat]
      simp only [flatAttach, ↓reduceIte]

/-- The permanent of the flat attachment along a list is that of the nested
one. -/
theorem bperm_flatAttach_list (M₀ : V → V → ℤ) (l : List S) (hl : l.Nodup) :
    bperm (flatAttach M₀ fun s : {s // s ∈ l} => site s.1) =
      bperm (attachAll M₀ (l.map site)) := by
  refine (congrArg bperm (funext fun n => funext fun n' => ?_)).trans
    (bperm_reindex (flatEquiv site l hl) (flatEquiv site l hl) (attachAll M₀ (l.map site)))
  rw [attachAll_eq_flatAttach site M₀ l hl]
  exact (congrArg₂ _ ((flatEquiv site l hl).apply_symm_apply n)
    ((flatEquiv site l hl).apply_symm_apply n')).symm

/-- **The permanent of the flat attachment is that of the nested one**, the
sites enumerated in any order. -/
theorem bperm_flatAttach [Fintype S] (M₀ : V → V → ℤ) :
    bperm (flatAttach M₀ site) = bperm (attachAll M₀ (univ.toList.map site)) := by
  rw [← bperm_flatAttach_list site M₀ univ.toList (Finset.nodup_toList _)]
  let e : V ⊕ ({s // s ∈ (univ : Finset S).toList} × Fin 4) ≃ V ⊕ (S × Fin 4) :=
    Equiv.sumCongr (Equiv.refl V) (Equiv.prodCongr
      (Equiv.subtypeUnivEquiv fun s => Finset.mem_toList.mpr (mem_univ s)) (Equiv.refl _))
  refine (congrArg bperm (funext fun n => funext fun n' => ?_)).trans (bperm_reindex e e _)
  exact (flatAttach_map M₀ site (fun s : {s // s ∈ (univ : Finset S).toList} => site s.1)
    (fun s => ⟨s, Finset.mem_toList.mpr (mem_univ s)⟩)
    (fun _ _ h => congrArg Subtype.val h) (fun _ => rfl) n n').symm

end Site

end DescriptiveComplexity
