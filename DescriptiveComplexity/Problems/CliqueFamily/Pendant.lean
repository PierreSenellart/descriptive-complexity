/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Set.Card
import DescriptiveComplexity.Numbers.DigitExtract

/-!
# Pendant leaves: the independent sets of one size, read off a digit

The combinatorial core of the reduction from counting the independent sets of
a given size to counting all of them. Attach to every vertex of a graph on `n`
vertices `n` new vertices, its *leaves*, adjacent to it alone
(`DescriptiveComplexity.pendAdj`). An independent set of the new graph is an
independent set `S` of the old one together with any set of leaves of the
vertices outside `S` (`DescriptiveComplexity.indepSet_pend_iff`), so there are

`∑ S, (2 ^ n) ^ (n - |S|)`

of them, `S` ranging over the independent sets of the old graph. Fewer than
`2 ^ n` sets have each size (`n` being positive), so this is a number in base
`2 ^ n` whose digit of rank `n - k` is the number of independent sets of size
`k` (`DescriptiveComplexity.card_indepSet_pend_digit`).
-/

namespace DescriptiveComplexity

/-- The set `S` is independent for `Adj`: no two distinct elements of it are
related. -/
def IndepSet {T : Type} (Adj : T → T → Prop) (S : T → Prop) : Prop :=
  ∀ x y, S x → S y → x ≠ y → ¬Adj x y

/-- Independence transports along an equivalence respecting adjacency. -/
theorem indepSet_equiv_iff {T T' : Type} {Adj : T → T → Prop} {Adj' : T' → T' → Prop}
    (E : T ≃ T') (hadj : ∀ x y, Adj x y ↔ Adj' (E x) (E y)) (S : T → Prop) :
    IndepSet Adj S ↔ IndepSet Adj' fun y => S (E.symm y) := by
  constructor
  · intro h x y hx hy hxy hadj'
    refine h (E.symm x) (E.symm y) hx hy (fun e => hxy (E.symm.injective e)) ?_
    rw [hadj]
    simpa using hadj'
  · intro h x y hx hy hxy hadj'
    exact h (E x) (E y) (by simpa using hx) (by simpa using hy)
      (fun e => hxy (E.injective e)) ((hadj x y).mp hadj')

variable {V : Type}

/-- Adjacency of the graph with pendant leaves: the vertices are those of `V`
with the adjacency they had, and a leaf `(a, i)` is adjacent to `a` alone. -/
def pendAdj (Adj : V → V → Prop) : V ⊕ V × V → V ⊕ V × V → Prop
  | .inl a, .inl b => Adj a b
  | .inl a, .inr p => a = p.1
  | .inr p, .inl b => p.1 = b
  | .inr _, .inr _ => False

/-- An independent set of the graph with leaves is an independent set of the
graph, and leaves of vertices outside it. -/
theorem indepSet_pend_iff (Adj : V → V → Prop) (T : V ⊕ V × V → Prop) :
    IndepSet (pendAdj Adj) T ↔
      IndepSet Adj (fun a => T (.inl a)) ∧ ∀ p : V × V, T (.inr p) → ¬T (.inl p.1) := by
  constructor
  · intro h
    exact ⟨fun a b ha hb hab => h (.inl a) (.inl b) ha hb fun e => hab (Sum.inl.inj e),
      fun p hp hv => h (.inr p) (.inl p.1) hp hv (by simp) rfl⟩
  · rintro ⟨h1, h2⟩ x y hx hy hxy hadj
    rcases x with a | p <;> rcases y with b | q
    · exact h1 a b hx hy (fun e => hxy (congrArg _ e)) hadj
    · have hq : a = q.1 := hadj
      subst hq
      exact h2 q hy hx
    · have hq : p.1 = b := hadj
      subst hq
      exact h2 p hx hy
    · exact hadj

/-- The elements outside a set and those inside it share out the universe. -/
theorem card_not_add_card [Finite V] (S : V → Prop) :
    Nat.card {v // ¬S v} + Nat.card {v // S v} = Nat.card V := by
  classical
  rw [← Nat.card_sum, Nat.card_congr ((Equiv.sumComm _ _).trans (Equiv.sumCompl S))]

/-- **The independent sets of one size, as a digit.** In a graph on `n ≥ 1`
vertices with `n` leaves at every vertex, the number of independent sets,
divided by `(2 ^ n) ^ (n - k)` and reduced modulo `2 ^ n`, is the number of
independent sets of size `k` of the graph; here `k` is the size of a set `Kp`,
and `n - k` the number of elements outside it. -/
theorem card_indepSet_pend_digit [Finite V] [Nonempty V] (Adj : V → V → Prop)
    (Kp : V → Prop) :
    Nat.card {T : V ⊕ V × V → Prop // IndepSet (pendAdj Adj) T} /
        2 ^ (Nat.card V * Nat.card {v // ¬Kp v}) % 2 ^ Nat.card V =
      Nat.card {S : V → Prop // IndepSet Adj S ∧ {x | S x}.ncard = {x | Kp x}.ncard} := by
  classical
  let := Fintype.ofFinite {S : V → Prop // IndepSet Adj S}
  let := Fintype.ofFinite (V → Prop)
  have hn : 0 < Nat.card V := Nat.card_pos
  have hcount : Nat.card {T : V ⊕ V × V → Prop // IndepSet (pendAdj Adj) T} =
      ∑ s : {S : V → Prop // IndepSet Adj S}, (2 ^ Nat.card V) ^ Nat.card {v // ¬s.1 v} := by
    have e1 : {T : V ⊕ V × V → Prop // IndepSet (pendAdj Adj) T} ≃
        {q : (V → Prop) × (V × V → Prop) // IndepSet Adj q.1 ∧ ∀ p, q.2 p → ¬q.1 p.1} :=
      Equiv.subtypeEquiv (Equiv.sumArrowEquivProdArrow V (V × V) Prop)
        fun T => indepSet_pend_iff Adj T
    have e2 : {q : (V → Prop) × (V × V → Prop) // IndepSet Adj q.1 ∧ ∀ p, q.2 p → ¬q.1 p.1} ≃
        Σ s : {S : V → Prop // IndepSet Adj S}, {F : V × V → Prop // ∀ p, F p → ¬s.1 p.1} :=
      { toFun := fun q => ⟨⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩⟩
        invFun := fun x => ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr (e1.trans e2), Nat.card_sigma]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e3 : {p : V × V // ¬s.1 p.1} ≃ V × {v // ¬s.1 v} :=
      { toFun := fun p => (p.1.2, ⟨p.1.1, p.2⟩)
        invFun := fun x => ⟨(x.2.1, x.1), x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [card_subsets_eq_two_pow fun p : V × V => ¬s.1 p.1, Nat.card_congr e3, Nat.card_prod,
      pow_mul]
  have hbound : ∀ q, (Finset.univ.filter fun s : {S : V → Prop // IndepSet Adj S} =>
      Nat.card {v // ¬s.1 v} = q).card < 2 ^ Nat.card V := by
    intro q
    have hpow : Fintype.card (V → Prop) = 2 ^ Nat.card V := by
      rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_eq_fintype_card,
        Fintype.card_prop]
    rw [← Fintype.card_subtype, ← hpow]
    refine Fintype.card_lt_of_injective_of_notMem
      (fun x : {s : {S : V → Prop // IndepSet Adj S} // Nat.card {v // ¬s.1 v} = q} => x.1.1)
      (fun x y h => Subtype.ext (Subtype.ext h))
      (b := if q = Nat.card V then fun _ => True else fun _ => False) ?_
    rintro ⟨x, hx⟩
    have hx2 := x.2
    have hx' : x.1.1 = if q = Nat.card V then fun _ => True else fun _ => False := hx
    by_cases hq : q = Nat.card V
    · simp only [hq, ↓reduceIte] at hx'
      have h0 : Nat.card {v // ¬x.1.1 v} = 0 := by
        have : IsEmpty {v // ¬x.1.1 v} := ⟨fun v => v.2 ((congrFun hx' v.1).mpr trivial)⟩
        exact Nat.card_of_isEmpty
      omega
    · simp only [hq, ↓reduceIte] at hx'
      have h1 : Nat.card {v // ¬x.1.1 v} = Nat.card V :=
        Nat.card_congr (Equiv.subtypeUnivEquiv fun v h => (congrFun hx' v).mp h)
      omega
  have hiff : ∀ S : V → Prop, Nat.card {v // ¬S v} = Nat.card {v // ¬Kp v} ↔
      {x | S x}.ncard = {x | Kp x}.ncard := by
    intro S
    have h1 := card_not_add_card S
    have h2 := card_not_add_card Kp
    have h3 : {x | S x}.ncard = Nat.card {v // S v} := (Nat.card_coe_set_eq {x | S x}).symm
    have h4 : {x | Kp x}.ncard = Nat.card {v // Kp v} := (Nat.card_coe_set_eq {x | Kp x}).symm
    omega
  rw [hcount, pow_mul, sum_pow_div_mod _ (Nat.pow_pos (by norm_num)) hbound,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, (hiff x.1.1).mp x.2⟩
      invFun := fun S => ⟨⟨S.1, S.2.1⟩, (hiff S.1).mpr S.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end DescriptiveComplexity
