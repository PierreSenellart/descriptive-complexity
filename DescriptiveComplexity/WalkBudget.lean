/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OrderWalk

/-!
# Budgets for deterministic walks

A deterministic machine that simulates a *functional* walk – one where every
node has at most one successor – cannot afford to follow it forever: the walk
may cycle, and the machine would then never come back to try anything else. It
must give up after a number of steps it can count, and the two halves of that
argument are here, both independent of any machine.

## The walk is an iterated function

A functional relation is a partial function, and
`DescriptiveComplexity.stepNext` makes it total by leaving a node without successor
where it is. Reachability is then iteration
(`DescriptiveComplexity.reach_iff_iterate`), and the budget is the pigeonhole:
**a reachable node is reachable in fewer steps than the type has elements**
(`DescriptiveComplexity.exists_iterate_lt_card`), because a shortest walk cannot
visit a node twice – splicing out the loop would shorten it.

## The counter can count that far

The counter a machine can afford is an element of a finite linear order walked
along covers, so what it must be shown is that enough covers are available:
`DescriptiveComplexity.Ticks n z` says `n` of them are, and
`DescriptiveComplexity.ticks_of_orank` says that this holds as soon as
`DescriptiveComplexity.orank z + n` is less than the number of elements – at the
bottom, one cover short of the whole order. Matching the two halves is then a
matter of counting the nodes and the counter values with the same number.
-/

namespace DescriptiveComplexity

/-! ### A functional relation, walked as a function -/

section Functional

variable {N : Type} {R : N → N → Prop} {a b : N}

open Classical in
/-- **The successor along a functional relation**, a node without one being left
where it is: the walk as a total function, so that reachability becomes
iteration. -/
noncomputable def stepNext (R : N → N → Prop) (a : N) : N :=
  if h : ∃ b, R a b then h.choose else a

theorem step_stepNext (h : ∃ b, R a b) : R a (stepNext R a) := by
  classical
  rw [stepNext, dif_pos h]
  exact h.choose_spec

theorem stepNext_eq_self (h : ¬∃ b, R a b) : stepNext R a = a := by
  classical
  rw [stepNext, dif_neg h]

/-- On a functional relation the walk follows the only step there is. -/
theorem stepNext_eq (hfun : ∀ u v w : N, R u v → R u w → v = w) (h : R a b) :
    stepNext R a = b :=
  hfun a _ _ (step_stepNext ⟨b, h⟩) h

/-- **Reachability along a functional relation is iteration.** -/
theorem reach_iff_iterate (hfun : ∀ u v w : N, R u v → R u w → v = w) (a b : N) :
    Relation.ReflTransGen R a b ↔ ∃ n, (stepNext R)^[n] a = b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail c d _ hcd ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn, stepNext_eq hfun hcd]⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      by_cases hs : ∃ c, R ((stepNext R)^[m] a) c
      · exact ih.tail (step_stepNext hs)
      · rw [stepNext_eq_self hs]
        exact ih

/-- **The step budget**: a node reachable along a functional relation is
reachable in fewer steps than the type has elements. A shortest walk visits
distinct nodes – a repeat could be spliced out. -/
theorem exists_iterate_lt_card [Finite N] {a b : N} (h : ∃ n, (stepNext R)^[n] a = b) :
    ∃ n, n < Nat.card N ∧ (stepNext R)^[n] a = b := by
  classical
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  set n := Nat.find h with hn
  have key : ∀ p q : Fin (n + 1), (p : ℕ) < (q : ℕ) →
      (stepNext R)^[(p : ℕ)] a = (stepNext R)^[(q : ℕ)] a → False := by
    intro p q hpq hval
    have hq : (q : ℕ) ≤ n := Nat.lt_succ_iff.mp q.isLt
    have hsplice : (stepNext R)^[n - (q : ℕ) + (p : ℕ)] a = b := by
      have hh : (stepNext R)^[n - (q : ℕ)] ((stepNext R)^[(p : ℕ)] a) =
          (stepNext R)^[n - (q : ℕ)] ((stepNext R)^[(q : ℕ)] a) := by rw [hval]
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hq] at hh
      rw [hh]
      exact Nat.find_spec h
    exact absurd hsplice (Nat.find_min h (by omega))
  have hinj : Function.Injective fun i : Fin (n + 1) => (stepNext R)^[(i : ℕ)] a := by
    intro i j hij
    by_contra hne
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun he => hne (Fin.ext he)
    rcases lt_or_gt_of_ne hne' with hl | hl
    · exact key i j hl hij
    · exact key j i hl hij.symm
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega

end Functional

/-! ### How far a counter can count -/

section Ticks

variable {C : Type} [LinearOrder C]

/-- **`n` covers are available above `z`**: what a counter must have left for a
machine to afford `n` more steps. -/
def Ticks : ℕ → C → Prop
  | 0, _ => True
  | n + 1, z => ∃ z', z ⋖ z' ∧ Ticks n z'

theorem ticks_succ {n : ℕ} {z z' : C} (h : z ⋖ z') (ht : Ticks n z') : Ticks (n + 1) z :=
  ⟨z', h, ht⟩

variable [Finite C]

/-- **A counter can tick as often as its rank leaves room**: at the bottom, one
tick short of the whole order. -/
theorem ticks_of_orank {z : C} {n : ℕ} (h : orank z + n < Nat.card C) : Ticks n z := by
  induction n generalizing z with
  | zero => trivial
  | succ n ih =>
    have hne : Nonempty C := ⟨z⟩
    have hnottop : ¬∀ a : C, a ≤ z := by
      intro htop
      rw [orank_isTop htop] at h
      have := Nat.card_pos (α := C)
      omega
    obtain ⟨z', hlt, hnb⟩ := exists_gt_of_not_max hnottop
    have hcov : z ⋖ z' := ⟨hlt, fun c h1 h2 => hnb c ⟨h1, h2⟩⟩
    refine ticks_succ hcov (ih ?_)
    rw [orank_covBy hcov]
    omega

/-- The bottom of the order can tick through all of it. -/
theorem ticks_bot {z : C} {n : ℕ} (hz : ∀ a : C, z ≤ a) (h : n < Nat.card C) : Ticks n z := by
  refine ticks_of_orank ?_
  rw [orank_eq_zero hz]
  omega

end Ticks

end DescriptiveComplexity
