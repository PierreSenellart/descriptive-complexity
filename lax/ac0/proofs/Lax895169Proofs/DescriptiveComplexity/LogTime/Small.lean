/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.LogTime.BitLogic
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Small universes are transparent: how to drop a size condition

Every packing argument of Immerman's mutual definability needs the universe to
be above a concrete size – there is no room to lay a certificate out in a
universe of three elements – and a statement gated by `n ≥ N` is a statement
that has to carry `n ≥ N` for ever after. This file is what discharges such a
hypothesis, and it is stated once for both logics:

> A **numeric** relation – one that depends only on the size of the universe and
> on the ranks of its arguments – is definable on universes of at most `k`
> elements, whatever it is (`DescriptiveComplexity.arithDef_of_card_le`,
> `DescriptiveComplexity.bitDef_of_card_le`). So a numeric relation definable on
> the *large* universes is definable outright
> (`DescriptiveComplexity.ArithDef.of_large`,
> `DescriptiveComplexity.BitDef.of_large`).

The reason is that an order **names** its elements: `orank x = j` is first-order
for each numeral `j` (`DescriptiveComplexity.arithDef_orankEq`, by `j`
successors), and `Nat.card A = n` is first-order for each numeral `n`
(`DescriptiveComplexity.arithDef_cardEq`). Below a fixed size there are finitely
many (size, tuple of ranks) cases, so the relation *is* an explicit finite
disjunction, one disjunct per case, each disjunct a conjunction of namings and a
truth value decided outside the structure.

## What it is for

A construction that lays out a certificate says what it needs of `n` and proves
its statement for those `n` only; this turns that into the statement with no
side condition. It is the shared prerequisite of two developments – the Bit Sum
Lemma (`LogTime/BitSum/`, whose packing levels each need `n` above a bound) and
the tuple arithmetic of AC⁰ class-hood (whose half-width splitting needs
`n ≥ 3`) – and it is deliberately built before either.

The finiteness hypothesis is on the *variables*, not on anything else: a
disjunction over the rank assignments of infinitely many variables is not a
formula. Every consumer has finitely many, and states them as a `Fin m`.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-! ### Naming an element by its rank -/

/-- The same, in the bit logic. -/
theorem bitDef_orankEq : ∀ (j : ℕ) {α : Type} (x : α),
    BitDef (L := L) (α := α) fun _ _ _ _ _ v => Lax895169.BitPredicate.orank (v x) = j := by
  intro j
  induction j with
  | zero => exact fun x => bitDef_isZero x
  | succ j ih =>
    intro α x
    refine (((ih (Sum.inr 0 : α ⊕ Fin 2)).and
      ((bitDef_isOne (Sum.inr 1)).and
        (bitDef_plus (Sum.inr 0) (Sum.inr 1) (Sum.inl x)))).exs).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨w, hw, hone, hsum⟩
      omega
    · intro hx
      have hlt : j + 1 < Nat.card A := by rw [← hx]; exact orank_lt_card (v x)
      obtain ⟨y, hy⟩ := exists_orank_eq (A := A) (m := j) (by omega)
      obtain ⟨u, hu⟩ := exists_orank_eq (A := A) (m := 1) (by omega)
      refine ⟨![y, u], hy, hu, ?_⟩
      change Lax895169.BitPredicate.orank y + Lax895169.BitPredicate.orank u = Lax895169.BitPredicate.orank (v x)
      rw [hy, hu, hx]

/-! ### Naming the size of the universe -/

/-- The same, in the bit logic. -/
theorem bitDef_cardGt (k : ℕ) :
    BitDef (L := L) (α := α) fun A _ _ _ _ _ => k < Nat.card A :=
  ((bitDef_orankEq k (Sum.inr 0 : α ⊕ Fin 1)).ex).congr fun A _ _ _ _ v => by
    simp only [Sum.elim_inr]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ orank_lt_card y, fun h => exists_orank_eq h⟩

/-- The same, in the bit logic. -/
theorem bitDef_cardEq (n : ℕ) :
    BitDef (L := L) (α := α) fun A _ _ _ _ _ => Nat.card A = n := by
  rcases n with _ | n
  · exact (BitDef.bot (L := L) (α := α)).congr fun A _ _ _ _ v =>
      ⟨False.elim, fun h => absurd h (by have := Nat.card_pos (α := A); omega)⟩
  · exact ((bitDef_cardGt n).and (bitDef_cardGt (n + 1)).not).congr
      fun A _ _ _ _ v => by omega

/-! ### Numeric relations -/

/-- A family of relations is **numeric** when it is a function of the size of
the universe and of the ranks of its arguments – which is what every statement
of arithmetic is, and what an input relation is not. -/
def IsNumeric {α : Type} (R : ArithRel L α) : Prop :=
  ∃ f : ℕ → (α → ℕ) → Prop,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A),
      R A v ↔ f (Nat.card A) fun a => Lax895169.BitPredicate.orank (v a)

/-- The relations a construction actually meets are numeric by inspection; this
is the one that says so for an arithmetic statement of three variables. -/
theorem isNumeric_of_ranks {f : ℕ → (α → ℕ) → Prop} :
    IsNumeric (L := L) (α := α) (fun A _ _ _ _ v => f (Nat.card A) fun a => Lax895169.BitPredicate.orank (v a)) :=
  ⟨f, fun _ _ _ _ _ _ => Iff.rfl⟩

/-! ### Transparency -/

section Transparency

variable [Finite α]

/-- The same, in the bit logic. -/
theorem bitDef_of_card_le {R : ArithRel L α} (k : ℕ) (h : IsNumeric R) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => Nat.card A ≤ k ∧ R A v := by
  obtain ⟨f, hf⟩ := h
  have hcase : ∀ c : Fin (k + 1) × (α → Fin (k + 1)),
      BitDef (L := L) (α := α) fun A _ _ _ _ v =>
        Nat.card A = (c.1 : ℕ) ∧ (∀ a, Lax895169.BitPredicate.orank (v a) = (c.2 a : ℕ)) ∧ f c.1 fun a => (c.2 a : ℕ) :=
    fun c => (bitDef_cardEq (c.1 : ℕ)).and
      ((BitDef.forallFinite fun a => bitDef_orankEq (c.2 a : ℕ) a).and
        (BitDef.prop _))
  refine (BitDef.existsFinite hcase).congr fun A _ _ _ _ v => ?_
  constructor
  · rintro ⟨c, hcard, hrank, hval⟩
    refine ⟨by omega, (hf A v).mpr ?_⟩
    rw [hcard]
    exact (funext fun a => hrank a) ▸ hval
  · rintro ⟨hle, hR⟩
    have hpos : 0 < Nat.card A := Nat.card_pos
    refine ⟨⟨⟨Nat.card A, by omega⟩, fun a => ⟨Lax895169.BitPredicate.orank (v a), by
      have := orank_lt_card (v a); omega⟩⟩, rfl, fun a => rfl, (hf A v).mp hR⟩

/-- The same, in the bit logic. -/
theorem BitDef.of_large {R : ArithRel L α} (k : ℕ) (hnum : IsNumeric R)
    (h : BitDef (L := L) (α := α) fun A _ _ _ _ v => k < Nat.card A ∧ R A v) :
    BitDef R :=
  (h.or (bitDef_of_card_le k hnum)).congr fun A _ _ _ _ v =>
    ⟨fun hc => hc.elim (fun h => h.2) fun h => h.2, fun hR => by
      rcases Nat.lt_or_ge k (Nat.card A) with hlt | hge
      · exact Or.inl ⟨hlt, hR⟩
      · exact Or.inr ⟨hge, hR⟩⟩

end Transparency

end Lax895169Proofs.DescriptiveComplexity


