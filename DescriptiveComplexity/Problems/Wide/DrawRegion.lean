/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawTable
import DescriptiveComplexity.Problems.Wide.Roam

/-!
# The region a clocked program works in, and its size

The universe a `Draw.Data` reduction draws is `Draw.Tag R P K × (Fin dd → A)`, and a
**logical** address – one whose non-argument blocks are empty
(`DescriptiveComplexity.Draw.logicalTop`) – is exactly an address of the working
region: the non-argument tags are the most significant, so the logical addresses
are an initial stretch of the tape (`DescriptiveComplexity.wmAvoids_of_wmSetLe`).

What a clocked program needs of that region is its *size*, since every phase it
runs inside it is charged against it and a bound by the number of addresses is a
bound by the clock itself. `wideRank_lt_two_pow_logical` is that size: a logical
address has rank below `2 ^ (k · m)`, with `k` the number of argument blocks and
`m` the number of tuples – the two numbers the clock's own arithmetic is written
in (`DescriptiveComplexity.Draw.Data.nexTotal_lt_two_pow'`).
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

section Region

variable {A R P K : Type} {dd : ℕ}
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable [Language.wide.Structure (Univ A R P K dd)]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite A]
  [Finite R] [Finite P] [Finite K] [Language.wide.Structure (Univ A R P K dd)] in
/-- **The argument blocks are as many as the fixed-point's own indices**: the
`k` of the clock's arithmetic. -/
theorem card_argTag :
    Nat.card {τ : Tag R P K // ∃ i : K, τ = Tag.arg i} = Nat.card K :=
  Nat.card_congr
    { toFun := fun τ => τ.2.choose
      invFun := fun i => ⟨Tag.arg i, i, rfl⟩
      left_inv := by
        rintro ⟨τ, hτ⟩
        exact Subtype.ext hτ.choose_spec.symm
      right_inv := by
        intro i
        exact Tag.arg.inj (Exists.choose_spec (⟨i, rfl⟩ :
          ∃ i' : K, (Tag.arg i : Tag R P K) = Tag.arg i')).symm }

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite A]
  [Language.wide.Structure (Univ A R P K dd)] in
/-- **The tags are the program's rules, its alphabet, its phases and its
blocks**, so the universe is `(|R| + 1 + |P| + k) · m` points. The clock's own
arithmetic reads that as `k` working blocks and `|R| + 1 + |P|` surplus ones –
the surplus a clocked program has for free, since its rule names and its phases
are tags whether it writes in them or not. -/
theorem card_drawTag :
    Nat.card (Tag R P K) = Nat.card R + 1 + Nat.card P + Nat.card K := by
  classical
  have e : Tag R P K ≃ R ⊕ (Unit ⊕ (P ⊕ K)) :=
    { toFun := fun τ => match τ with
        | .ctrl r => Sum.inl r
        | .sym => Sum.inr (Sum.inl ())
        | .phase p => Sum.inr (Sum.inr (Sum.inl p))
        | .arg i => Sum.inr (Sum.inr (Sum.inr i))
      invFun := fun x => match x with
        | Sum.inl r => .ctrl r
        | Sum.inr (Sum.inl _) => .sym
        | Sum.inr (Sum.inr (Sum.inl p)) => .phase p
        | Sum.inr (Sum.inr (Sum.inr i)) => .arg i
      left_inv := by rintro (r | - | p | i) <;> rfl
      right_inv := by rintro (r | ⟨⟩ | p | i) <;> rfl }
  rw [Nat.card_congr e, Nat.card_sum, Nat.card_sum, Nat.card_sum,
    show Nat.card Unit = 1 from Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨()⟩⟩]
  omega

/-- **A logical address lies in a region of `2 ^ (k · m)` addresses**: its rank
is below that number, `k` being the argument blocks and `m` the tuples. This is
the bound every phase of a clocked program run inside the region is charged
against; the counting behind it is
`DescriptiveComplexity.wideRank_lt_two_pow_avoids`. -/
theorem wideRank_lt_two_pow_logical
    (hord : ∀ x y : Univ A R P K dd, WMLe x y ↔ tagTupleLe x y)
    {s : Univ A R P K dd → Prop}
    (hjunk : ∀ τ : Tag R P K, (∀ i : K, τ ≠ Tag.arg i) →
      ∀ v : Fin dd → A, ¬s (τ, v)) :
    wideRank s < 2 ^ (Nat.card K * Nat.card (Fin dd → A)) := by
  classical
  have hcount : Nat.card {p : Univ A R P K dd //
      ¬(fun τ : Tag R P K => ∀ i : K, τ ≠ Tag.arg i) p.1} =
      Nat.card K * Nat.card (Fin dd → A) := by
    rw [card_avoid_positions (V := Fin dd → A)
      (fun τ : Tag R P K => ∀ i : K, τ ≠ Tag.arg i)]
    refine congrArg (fun n => n * Nat.card (Fin dd → A)) ?_
    rw [← card_argTag (R := R) (P := P) (K := K)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => by
      simp only [not_forall, not_not])
  rw [← hcount]
  refine wideRank_lt_two_pow_avoids isLinOrd_le Wide.isLinOrd_tupLeLex
    (fun x y => ?_) nonArg_downward (logical_iff_wmAvoids.mp hjunk)
  rw [hord x y]
  exact Wide.tagTupleLe_iff_lexRel x y

end Region

end Draw

end DescriptiveComplexity
