/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Counting
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Circuits, locally and from a potential

Two readings of a Hamilton circuit (`DescriptiveComplexity.IsCircuit`) that never
mention the linear order it is a cut of, for the two halves of a reduction
into a circuit problem.

* **What a circuit gives** (`DescriptiveComplexity.IsCircuit.local`): every vertex is
  left once and reached once, along the relation, and two vertices that follow
  each other both ways are the whole universe. That is all a gadget argument
  uses: which arc leaves a vertex is settled by which arcs can still reach its
  neighbours.
* **What makes a circuit** (`DescriptiveComplexity.isCircuit_of_potential`): a
  relation along which every vertex is left once and reached once is a circuit
  as soon as some *potential* strictly increases along it at every vertex but
  one. An orbit avoiding that vertex could never close, so there is one orbit.
  The order is then read off the powers of the permutation, and the potential
  is checked arc by arc: no enumeration of the circuit has to be written.
-/

namespace DescriptiveComplexity

open FirstOrder

section Circuit

variable {V : Type}

theorem nextIdx_injective {n : ℕ} : Function.Injective (nextIdx : Fin n → Fin n) := by
  intro i j h
  have h' : ((i : ℕ) + 1) % n = ((j : ℕ) + 1) % n := congrArg Fin.val h
  have h'' : (i : ℕ) % n = (j : ℕ) % n := Nat.ModEq.add_right_cancel' 1 h'
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at h''
  exact Fin.ext h''

theorem nextIdx_iterate {n : ℕ} (k : ℕ) (i : Fin n) :
    ((nextIdx^[k] i : Fin n) : ℕ) = ((i : ℕ) + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((nextIdx^[k] i : ℕ) + 1) % n = _
    rw [ih, Nat.mod_add_mod, Nat.add_assoc]

/-- The cyclic successor of the reverse order is the cyclic predecessor. -/
theorem cycSucc_reverse {Le : V → V → Prop} {x y : V} :
    CycSucc (fun a b => Le b a) x y ↔ CycSucc Le y x := by
  constructor
  · rintro (⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩)
    · exact Or.inl ⟨h₁, Ne.symm h₂, fun z hz hz' => (h₃ z hz' hz).symm⟩
    · exact Or.inr ⟨h₂, h₁⟩
  · rintro (⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩)
    · exact Or.inl ⟨h₁, Ne.symm h₂, fun z hz hz' => (h₃ z hz' hz).symm⟩
    · exact Or.inr ⟨h₂, h₁⟩

/-- A circuit of a symmetric relation, traversed backwards, is a circuit. -/
theorem IsCircuit.reverse {R Nxt : V → V → Prop} (hsym : ∀ x y, R x y → R y x)
    (h : IsCircuit R Nxt) : IsCircuit R fun x y => Nxt y x := by
  obtain ⟨Le, hlin, hiff, hR⟩ := h
  exact ⟨fun a b => Le b a, hlin.reverse, fun x y => (hiff y x).trans cycSucc_reverse.symm,
    fun x y hxy => hsym _ _ (hR _ _ hxy)⟩

variable [Finite V]

/-- **Induction along a circuit**: a property of one vertex that passes to the
next vertex holds of every vertex. -/
theorem IsCircuit.induction {R Nxt : V → V → Prop} (h : IsCircuit R Nxt) {P : V → Prop}
    (x₀ : V) (h0 : P x₀) (hstep : ∀ x y, Nxt x y → P x → P y) : ∀ x, P x := by
  obtain ⟨Le, hlin, hiff, -⟩ := h
  obtain ⟨f, hf⟩ := exists_mono_enum hlin
  have hN : ∀ x y, Nxt x y ↔ y = f (nextIdx (f.symm x)) := fun x y =>
    (hiff x y).trans (cycSucc_iff f hf x y)
  have hk : ∀ k : ℕ, P (f (nextIdx^[k] (f.symm x₀))) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ _ ((hN _ _).mpr (by simp)) ih
  intro x
  have hx := (f.symm x).isLt
  have hx₀ := (f.symm x₀).isLt
  have he : nextIdx^[(f.symm x : ℕ) + (Nat.card V - (f.symm x₀ : ℕ))] (f.symm x₀) = f.symm x := by
    refine Fin.ext ?_
    rw [nextIdx_iterate]
    have : (f.symm x₀ : ℕ) + ((f.symm x : ℕ) + (Nat.card V - (f.symm x₀ : ℕ))) =
        (f.symm x : ℕ) + Nat.card V := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  have h := hk ((f.symm x : ℕ) + (Nat.card V - (f.symm x₀ : ℕ)))
  rw [he] at h
  simpa using h

/-- **A circuit, read locally**: every vertex is left once and reached once,
along the relation, and two vertices following each other both ways are the
whole universe. -/
theorem IsCircuit.local {R Nxt : V → V → Prop} (h : IsCircuit R Nxt) :
    (∀ x, ∃ y, Nxt x y) ∧ (∀ x y y', Nxt x y → Nxt x y' → y = y') ∧
      (∀ y, ∃ x, Nxt x y) ∧ (∀ x x' y, Nxt x y → Nxt x' y → x = x') ∧
      (∀ x y, Nxt x y → R x y) ∧ ∀ x y, Nxt x y → Nxt y x → ∀ z, z = x ∨ z = y := by
  obtain ⟨Le, hlin, hiff, hR⟩ := h
  obtain ⟨f, hf⟩ := exists_mono_enum hlin
  have hN : ∀ x y, Nxt x y ↔ y = f (nextIdx (f.symm x)) := fun x y =>
    (hiff x y).trans (cycSucc_iff f hf x y)
  have hsurj : Function.Surjective (nextIdx : Fin (Nat.card V) → Fin (Nat.card V)) :=
    Finite.injective_iff_surjective.mp nextIdx_injective
  refine ⟨fun x => ⟨_, (hN x _).mpr rfl⟩,
    fun x y y' hy hy' => ((hN x y).mp hy).trans ((hN x y').mp hy').symm, fun y => ?_,
    fun x x' y hx hx' => ?_, hR, fun x y hxy hyx z => ?_⟩
  · obtain ⟨i, hi⟩ := hsurj (f.symm y)
    exact ⟨f i, (hN _ _).mpr (by simp [hi])⟩
  · have e := ((hN x y).mp hx).symm.trans ((hN x' y).mp hx')
    exact f.symm.injective (nextIdx_injective (f.injective e))
  · have h₁ := (hN x y).mp hxy
    have h₂ := (hN y x).mp hyx
    have h₃ : f.symm y = nextIdx (f.symm x) := by simp [h₁]
    have h₄ : f.symm x = nextIdx (f.symm y) := by simp [h₂]
    have hzx : z = x ↔ f.symm z = f.symm x := f.symm.injective.eq_iff.symm
    have hzy : z = y ↔ f.symm z = f.symm y := f.symm.injective.eq_iff.symm
    rw [hzx, hzy, Fin.ext_iff, Fin.ext_iff]
    have v₃ : ((f.symm y : Fin (Nat.card V)) : ℕ) = ((f.symm x : ℕ) + 1) % Nat.card V :=
      congrArg Fin.val h₃
    have v₄ : ((f.symm x : Fin (Nat.card V)) : ℕ) = ((f.symm y : ℕ) + 1) % Nat.card V :=
      congrArg Fin.val h₄
    have hx := (f.symm x).isLt
    have hy := (f.symm y).isLt
    have hz := (f.symm z).isLt
    rcases Nat.lt_or_ge ((f.symm x : ℕ) + 1) (Nat.card V) with h | h
    · rw [Nat.mod_eq_of_lt h] at v₃
      rcases Nat.lt_or_ge ((f.symm y : ℕ) + 1) (Nat.card V) with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at v₄
        omega
      · have hc : (f.symm y : ℕ) + 1 = Nat.card V := by omega
        rw [hc, Nat.mod_self] at v₄
        omega
    · have hc : (f.symm x : ℕ) + 1 = Nat.card V := by omega
      rw [hc, Nat.mod_self] at v₃
      rw [v₃] at v₄
      rcases Nat.lt_or_ge 1 (Nat.card V) with h' | h'
      · rw [Nat.mod_eq_of_lt (by omega)] at v₄
        omega
      · omega

/-- **A circuit from a potential**: a relation along which every vertex is
left once and reached once, included in `R`, is a Hamilton circuit of `R` as
soon as some potential strictly increases along it at every vertex but one. -/
theorem isCircuit_of_potential {K : Type} [Preorder K] {R Nxt : V → V → Prop}
    (htot : ∀ x, ∃ y, Nxt x y) (hfun : ∀ x y y', Nxt x y → Nxt x y' → y = y')
    (hsurj : ∀ y, ∃ x, Nxt x y) (hR : ∀ x y, Nxt x y → R x y) (key : V → K) (v₀ : V)
    (hkey : ∀ x y, Nxt x y → x ≠ v₀ → key x < key y) : IsCircuit R Nxt := by
  classical
  choose s hs using htot
  have hNs : ∀ x y, Nxt x y ↔ y = s x := fun x y =>
    ⟨fun h => hfun x y (s x) h (hs x), fun h => h ▸ hs x⟩
  have hssurj : Function.Surjective s := fun y => by
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, ((hNs x y).mp hx).symm⟩
  let σ : Equiv.Perm V :=
    Equiv.ofBijective s ⟨Finite.injective_iff_surjective.mpr hssurj, hssurj⟩
  have hσ : ∀ x, σ x = s x := fun _ => rfl
  have hstep : ∀ (j : ℕ) (u : V), (σ ^ (j + 1)) u = s ((σ ^ j) u) := fun j u => by
    rw [pow_succ', Equiv.Perm.mul_apply, hσ]
  -- every vertex reaches the exceptional one
  have hreach : ∀ u, ∃ j : ℕ, (σ ^ j) u = v₀ := by
    intro u
    by_contra hcon
    have hne : ∀ j : ℕ, (σ ^ j) u ≠ v₀ := fun j hj => hcon ⟨j, hj⟩
    have hinc : ∀ j : ℕ, key u < key ((σ ^ (j + 1)) u) := by
      intro j
      induction j with
      | zero =>
        have h := hkey _ _ (hs ((σ ^ 0) u)) (hne 0)
        rw [← hstep] at h
        simpa using h
      | succ j ih =>
        have h := hkey _ _ (hs ((σ ^ (j + 1)) u)) (hne (j + 1))
        rw [← hstep] at h
        exact ih.trans h
    have hpos : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
    have h := hinc (orderOf σ - 1)
    rw [Nat.sub_add_cancel hpos, pow_orderOf_eq_one] at h
    exact lt_irrefl _ h
  have hsame : ∀ u u', σ.SameCycle u u' := by
    have h₀ : ∀ u, σ.SameCycle u v₀ := fun u => by
      obtain ⟨j, hj⟩ := hreach u
      exact ⟨(j : ℤ), by rw [zpow_natCast]; exact hj⟩
    exact fun u u' => (h₀ u).trans (h₀ u').symm
  have := Fintype.ofFinite V
  have hcyc : σ.IsCycleOn ((Finset.univ : Finset V) : Set V) :=
    ⟨by simp, fun x _ y _ => hsame x y⟩
  have hcard : (Finset.univ : Finset V).card = Nat.card V := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  let F : Fin (Nat.card V) → V := fun i => (σ ^ (i : ℕ)) v₀
  have hFsurj : Function.Surjective F := fun u => by
    obtain ⟨n, hn, hnu⟩ := hcyc.exists_pow_eq (Finset.mem_univ v₀) (Finset.mem_univ u)
    exact ⟨⟨n, hcard ▸ hn⟩, hnu⟩
  have hFbij : Function.Bijective F := hFsurj.bijective_of_nat_card_le (by simp)
  let f : Fin (Nat.card V) ≃ V := Equiv.ofBijective F hFbij
  have hf : ∀ i : Fin (Nat.card V), f i = (σ ^ (i : ℕ)) v₀ := fun _ => rfl
  have hfstep : ∀ i : Fin (Nat.card V), f (nextIdx i) = s (f i) := by
    intro i
    rw [hf, hf, ← hstep]
    by_cases hlt : (i : ℕ) + 1 < Nat.card V
    · rw [nextIdx_of_lt hlt]
    · have hc : (i : ℕ) + 1 = Nat.card V := by
        have := i.isLt
        omega
      rw [nextIdx_of_last hc, hc, ← hcard, hcyc.pow_card_apply (Finset.mem_univ v₀)]
      rfl
  have hmono : ∀ j k : Fin (Nat.card V),
      (fun x y => f.symm x ≤ f.symm y) (f j) (f k) ↔ j ≤ k := fun j k => by simp
  refine ⟨fun x y => f.symm x ≤ f.symm y,
    (tour_of_enum (R := fun _ _ => True) f fun _ => trivial).1, fun x y => ?_, hR⟩
  rw [cycSucc_iff f hmono, hfstep, Equiv.apply_symm_apply]
  exact hNs x y

end Circuit

end DescriptiveComplexity
