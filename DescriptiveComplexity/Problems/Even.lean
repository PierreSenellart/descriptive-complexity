/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Games.Bare
import DescriptiveComplexity.Games.LinearOrder
import DescriptiveComplexity.TransitiveClosureFO
import DescriptiveComplexity.ImmermanSzelepcsenyi

/-!
# EVEN: the parity of a bare set

The textbook inexpressibility example ([Ebbinghaus–Flum 1995][ebbinghaus1995finite],
ch. 2; [Immerman 1999][immerman1999descriptive], §6.1): over the *empty*
vocabulary – a structure is nothing but a finite set – decide whether the
universe has an even number of elements.

Nothing could be easier to compute, and nothing is further from first-order
logic. No sentence defines it
(`DescriptiveComplexity.even_not_foDefinableFree`) – one line of
Ehrenfeucht–Fraïssé given the strategy on bare sets
(`DescriptiveComplexity.exists_card_bound_of_foDefinableFree`): a sentence of
quantifier rank `n` cannot tell a set with `2n + 2` elements from one with
`2n + 3`, the duplicator's supply of fresh elements outlasting the spoiler's
rounds on both sides. And no sentence defines it *with a linear order in hand*
either (`DescriptiveComplexity.even_not_foDefinable`), which is the theorem
with content: the structure then determines the position of every point, and
the duplicator still wins, for `2 ^ n` rounds' worth of elements
(`DescriptiveComplexity.efEquiv_linearOrder`).

Deciding it, on the other hand, is one walk along that same order – step to
the immediate successor, flip a bit – so EVEN *is* FO(≤, TC) definable
(`DescriptiveComplexity.even_tcDefinable`), hence in
`DescriptiveComplexity.NL`. The two halves together give `FO ⊊ FO(TC)`
(`DescriptiveComplexity.exists_tcDefinable_not_foDefinable`): a *strict*
inclusion between two logics of this library, proved outright.

This is the first *unconditional* separation of the library – no complexity
assumption enters, in contrast with everything the completeness results say,
which is why the game layer is worth its cost.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-! ### The problem -/

/-- **EVEN**: the universe has an even number of elements. The vocabulary is
empty, so a yes-instance is nothing but a finite set of even size, and the
problem is invariant for the strongest possible reason – isomorphic bare sets
are equinumerous. -/
def EVEN : DecisionProblem Language.empty where
  Holds := fun A _ => Even (Nat.card A)
  iso_invariant := fun e => by rw [Nat.card_congr e.toEquiv]

/-- The value of EVEN at a bare set, unfolded. -/
theorem even_holds_iff (A : Type) [Language.empty.Structure A] :
    EVEN A ↔ Even (Nat.card A) :=
  Iff.rfl

/-! ### EVEN is not first-order

The two witnesses are `Fin (2 * n + 2)` and `Fin (2 * n + 3)`: of different
parity, and both larger than the quantifier rank `n` that would have to tell
them apart. -/

/-- **EVEN is not first-order definable.** A defining sentence of quantifier
rank `n` would have to separate two bare sets of at least `n` elements each,
which the duplicator's strategy (`DescriptiveComplexity.efEquiv_bare`)
forbids. -/
theorem even_not_foDefinableFree : ¬FODefinableFree EVEN := by
  intro h
  obtain ⟨N, hN⟩ := exists_card_bound_of_foDefinableFree h
  letI : Language.empty.Structure (Fin (2 * N + 2)) := Language.emptyStructure
  letI : Language.empty.Structure (Fin (2 * N + 3)) := Language.emptyStructure
  have hcard₁ : Nat.card (Fin (2 * N + 2)) = 2 * N + 2 := by simp
  have hcard₂ : Nat.card (Fin (2 * N + 3)) = 2 * N + 3 := by simp
  have hiff := hN (Fin (2 * N + 2)) (Fin (2 * N + 3)) (by omega) (by omega)
  rw [even_holds_iff, even_holds_iff, hcard₁, hcard₂] at hiff
  have h₁ : Even (2 * N + 2) := ⟨N + 1, by omega⟩
  have h₂ : ¬Even (2 * N + 3) := by
    rintro ⟨m, hm⟩
    omega
  exact h₂ (hiff.mp h₁)

/-! ### EVEN is not first-order even with an order

The order-free result above says little on its own: a bare set carries no
information beyond its size, and a sentence of quantifier rank `n` sees that
size only up to `n`. The order-invariant statement is the real theorem – the
structure now *does* determine every point's position, and the sentence may
speak about it – and it needs Ehrenfeucht's theorem
(`DescriptiveComplexity.efEquiv_linearOrder`), whose bound is exponential
rather than linear in the quantifier rank. -/

/-- **EVEN is not first-order definable, even order-invariantly**: no sentence
over the ordered expansion defines it, however it uses the order. A defining
sentence of quantifier rank `n` would have to separate two finite linear
orders of `2 ^ n * 2` and `2 ^ n * 2 + 1` elements, which the duplicator's
strategy on a line (`DescriptiveComplexity.efEquiv_linearOrder`) forbids.

Together with `DescriptiveComplexity.even_tcDefinable` below, this is the
unconditional strict inclusion `FO ⊊ FO(TC)`, and, through the inclusions the
library proves for the classes above `DescriptiveComplexity.NL`, the statement
that first-order logic is strictly weaker than every logic here. -/
theorem even_not_foDefinable : ¬FODefinable EVEN := by
  rintro ⟨φ, hφ⟩
  set n := qdepth φ with hn
  have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
  letI : Language.empty.Structure (Fin (2 ^ n * 2)) := Language.emptyStructure
  letI : Language.empty.Structure (Fin (2 ^ n * 2 + 1)) := Language.emptyStructure
  haveI : Nonempty (Fin (2 ^ n * 2)) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin (2 ^ n * 2 + 1)) := ⟨⟨0, by omega⟩⟩
  have hcard₁ : Nat.card (Fin (2 ^ n * 2)) = 2 ^ n * 2 := by simp
  have hcard₂ : Nat.card (Fin (2 ^ n * 2 + 1)) = 2 ^ n * 2 + 1 := by simp
  have hEF : EFEquiv (Language.empty.sum Language.order)
      (Fin (2 ^ n * 2)) (Fin (2 ^ n * 2 + 1)) n :=
    efEquiv_linearOrder n (by omega) (by omega)
  have hiff := realize_sentence_of_efEquiv hEF φ le_rfl
  rw [← hφ (Fin (2 ^ n * 2)), ← hφ (Fin (2 ^ n * 2 + 1)), even_holds_iff, even_holds_iff,
    hcard₁, hcard₂] at hiff
  have h₁ : Even (2 ^ n * 2) := ⟨2 ^ n, by omega⟩
  have h₂ : ¬Even (2 ^ n * 2 + 1) := by
    rintro ⟨m, hm⟩
    omega
  exact h₂ (hiff.mp h₁)

/-! ### EVEN is a transitive closure

The other half of the separation: parity is trivially *computable*, and with a
linear order at hand it is a single walk – step to the immediate successor,
flip a bit. Written as a `DescriptiveComplexity.TCSpec`, the walk carries the
bit as its mode and the current element as its (one-element) tuple. -/

section Membership

variable {A : Type} [Language.empty.Structure A] [LinearOrder A]

/-- The parity mode carried at an element: `true` where the rank is even, that
is, after an odd number of elements has been visited. -/
noncomputable def parityMode [Finite A] (x : A) : Bool :=
  decide (Even (orank x))

/-- The transition of the parity walk: step to the immediate successor,
flipping the mode. Between modes that are not opposite there is no
transition. -/
noncomputable def evenStep (m m' : Bool) :
    (Language.empty.sum Language.order).Formula (Fin 1 ⊕ Fin 1) :=
  if m' = !m then succF (Sum.inl 0) (Sum.inr 0) else ⊥

/-- The walk starts at the minimum, in the mode of a set with one element
visited. -/
noncomputable def evenSrc (m : Bool) : (Language.empty.sum Language.order).Formula (Fin 1) :=
  if m then minF 0 else ⊥

/-- The walk accepts at the maximum, in the opposite mode: an even number of
elements has been visited. -/
noncomputable def evenTgt (m : Bool) : (Language.empty.sum Language.order).Formula (Fin 1) :=
  if m then ⊥ else maxF 0

/-- **EVEN as a single transitive closure**: one element walking the order,
one bit of parity. -/
noncomputable def evenSpec : TCSpec Language.empty where
  Mode := Bool
  k := 1
  step := evenStep
  src := evenSrc
  tgt := evenTgt

theorem realize_evenStep (m m' : Bool) (x y : Fin 1 → A) :
    (evenStep m m').Realize (Sum.elim x y) ↔ m' = !m ∧ x 0 ⋖ y 0 := by
  rw [evenStep]
  split_ifs with h
  · rw [realize_succF]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun hx => ⟨h, hx.1, fun _ h₁ h₂ => hx.2 _ ⟨h₁, h₂⟩⟩,
      fun hx => ⟨hx.2.1, fun _ ha => hx.2.2 ha.1 ha.2⟩⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

theorem step_evenSpec_iff (m m' : Bool) (x y : Fin 1 → A) :
    evenSpec.Step (m, x) (m', y) ↔ m' = !m ∧ x 0 ⋖ y 0 :=
  realize_evenStep m m' x y

theorem isSrc_evenSpec_iff (m : Bool) (x : Fin 1 → A) :
    evenSpec.IsSrc (m, x) ↔ m = true ∧ ∀ a : A, x 0 ≤ a := by
  change (evenSrc m).Realize x ↔ _
  cases m <;> simp [evenSrc]

theorem isTgt_evenSpec_iff (m : Bool) (x : Fin 1 → A) :
    evenSpec.IsTgt (m, x) ↔ m = false ∧ ∀ a : A, a ≤ x 0 := by
  change (evenTgt m).Realize x ↔ _
  cases m <;> simp [evenTgt]

variable [Finite A]

omit [Language.empty.Structure A] in
/-- The mode flips along a cover, since the rank increases by one. -/
theorem parityMode_covBy {w z : A} (h : w ⋖ z) : parityMode z = !parityMode w := by
  rw [parityMode, parityMode, orank_covBy h]
  cases Nat.even_or_odd (orank w) with
  | inl he => simp [he, Nat.even_add_one]
  | inr ho => simp [Nat.even_add_one, Nat.not_even_iff_odd.mpr ho]

/-- **The walk reaches every element**, in the mode its rank prescribes. -/
theorem reach_evenSpec {x₀ : A} (h₀ : ∀ a : A, x₀ ≤ a) (x : A) :
    evenSpec.Reach (true, fun _ => x₀) (parityMode x, fun _ => x) := by
  induction x using order_induction with
  | hmin z hz =>
    have hzx : z = x₀ := le_antisymm (hz x₀) (h₀ z)
    subst hzx
    have : parityMode z = true := by
      rw [parityMode, orank_eq_zero hz]
      simp
    rw [this]
  | hstep w z hwz hnb ih =>
    have hcov : w ⋖ z := ⟨hwz, fun _ h₁ h₂ => hnb _ ⟨h₁, h₂⟩⟩
    refine ih.tail ?_
    exact (step_evenSpec_iff _ _ _ _).mpr ⟨parityMode_covBy hcov, hcov⟩

/-- **The mode of a reachable node is the parity of its rank**: the invariant
that reads the walk backwards. -/
theorem parityMode_of_reach {x₀ : A} (h₀ : ∀ a : A, x₀ ≤ a) :
    ∀ p : evenSpec.Node A, evenSpec.Reach (true, fun _ => x₀) p →
      p.1 = parityMode (p.2 (0 : Fin 1)) := by
  intro p h
  induction h with
  | refl =>
    have : parityMode x₀ = true := by
      rw [parityMode, orank_eq_zero h₀]
      simp
    rw [this]
  | @tail b c _ hbc ih =>
    obtain ⟨hm, hcov⟩ := (step_evenSpec_iff b.1 c.1 b.2 c.2).mp (by
      rw [Prod.mk.eta, Prod.mk.eta]; exact hbc)
    rw [hm, ih, ← parityMode_covBy hcov]

variable [Nonempty A]

/-- **The walk accepts exactly the sets of even size**: it visits every
element once, from the minimum to the maximum, so the mode it ends in is the
parity of the cardinality. -/
theorem accepts_evenSpec_iff : evenSpec.Accepts A ↔ Even (Nat.card A) := by
  have hcard : 0 < Nat.card A := Nat.card_pos
  obtain ⟨x₀, -, h₀'⟩ := Set.exists_min_image (Set.univ : Set A) id (Set.toFinite _)
    ⟨Classical.arbitrary A, trivial⟩
  obtain ⟨x₁, -, h₁'⟩ := Set.exists_max_image (Set.univ : Set A) id (Set.toFinite _)
    ⟨Classical.arbitrary A, trivial⟩
  have h₀ : ∀ a : A, x₀ ≤ a := fun a => h₀' a trivial
  have h₁ : ∀ a : A, a ≤ x₁ := fun a => h₁' a trivial
  have hrank₁ : orank x₁ = Nat.card A - 1 := orank_isTop h₁
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    obtain ⟨hu₁, hu₂⟩ := (isSrc_evenSpec_iff u.1 u.2).mp hu
    obtain ⟨hv₁, hv₂⟩ := (isTgt_evenSpec_iff v.1 v.2).mp hv
    have hueq : u = (true, fun _ => u.2 (0 : Fin 1)) := by
      refine Prod.ext hu₁ (funext fun i => ?_)
      rw [show i = (0 : Fin 1) from Subsingleton.elim (α := Fin 1) i 0]
    rw [hueq] at huv
    have := parityMode_of_reach hu₂ _ huv
    rw [hv₁, parityMode] at this
    have hnot : ¬Even (orank (v.2 (0 : Fin 1))) := by
      intro he
      rw [decide_eq_true he] at this
      exact Bool.noConfusion this
    have hveq : orank (v.2 (0 : Fin 1)) = Nat.card A - 1 := orank_isTop hv₂
    rw [hveq] at hnot
    rcases Nat.even_or_odd (Nat.card A) with he | ho
    · exact he
    · obtain ⟨m, hm⟩ := ho
      exact absurd ⟨m, by omega⟩ hnot
  · intro hev
    refine ⟨(true, fun _ => x₀), (parityMode x₁, fun _ => x₁), ?_, ?_, reach_evenSpec h₀ x₁⟩
    · exact (isSrc_evenSpec_iff _ _).mpr ⟨rfl, h₀⟩
    · refine (isTgt_evenSpec_iff _ _).mpr ⟨?_, h₁⟩
      rw [parityMode, hrank₁, decide_eq_false_iff_not]
      rintro ⟨m, hm⟩
      obtain ⟨m', hm'⟩ := hev
      omega

end Membership

/-- **EVEN is FO(≤, TC) definable**, by the parity walk. -/
theorem even_tcDefinable : TCDefinable EVEN :=
  ⟨evenSpec, fun _ _ _ _ _ => accepts_evenSpec_iff.symm⟩

/-- **`FO ⊊ FO(TC)`, unconditionally.** First-order logic with a transitive
closure is *strictly* stronger than first-order logic on ordered finite
structures: the inclusion is `DescriptiveComplexity.FODefinable.tcDefinable`,
and EVEN separates the two – a single walk along the order defines it, and no
sentence does. No complexity-theoretic assumption enters either half. -/
theorem exists_tcDefinable_not_foDefinable :
    ∃ P : DecisionProblem Language.empty, TCDefinable P ∧ ¬FODefinable P :=
  ⟨EVEN, even_tcDefinable, even_not_foDefinable⟩

/-- **EVEN is in NL** – as far from first-order logic as it is easy to
compute. -/
theorem even_mem_NL : EVEN ∈ NL :=
  (tcDefinable_iff_mem_NL EVEN).mp even_tcDefinable

end DescriptiveComplexity
