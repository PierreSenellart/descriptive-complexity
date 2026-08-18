/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Machines
import DescriptiveComplexity.OrderWalk
import Mathlib.Logic.Relation

/-!
# Loops in the control: runs indexed by a finite linear order

The element loops of the EXPSPACE program enumerate tuples of source elements
in the machine's control, one lexicographic successor per round. The register
loops have their induction principle already
(`DescriptiveComplexity.reaches_of_wideRounds`, driven by the address rank);
the control loops get theirs here, driven by
`DescriptiveComplexity.order_induction`:

* `DescriptiveComplexity.Pfp.reflTransGen_of_ordLoop` – a run per immediate
  successor of a finite linear order carries the machine from the bottom to
  anywhere;
* `DescriptiveComplexity.Pfp.reflTransGen_of_tupLoop` – the same over tuples in
  the lexicographic order, the rounds indexed by
  `DescriptiveComplexity.TupSucc`, which is the shape of the guards the
  advancing rules read (`DescriptiveComplexity.succTupF`).

Both are stated for an arbitrary relation on an arbitrary configuration type:
nothing here is about wide machines, and the reachability they produce is fed
to `Relation.ReflTransGen.trans` like any other phase.

Both also have a **budgeted** form – `reachesIn_of_ordLoop` and
`reachesIn_of_tupLoop`, with `reachesIn_of_ordLoop_card` for the crude bound –
which keeps the count a clocked program has to compare with its clock: one
round's budget, once per element of the enumeration. A space-bounded program
throws the count away and uses the two above.
-/

namespace DescriptiveComplexity

namespace Pfp

section Loop

variable {C : Type} {Step : C → C → Prop}

/-- **A loop over a finite linear order**: one run per immediate successor
carries the machine from the configuration of the bottom element to the
configuration of any element. -/
theorem reflTransGen_of_ordLoop {A : Type} [LinearOrder A] [Finite A] {conf : A → C}
    (hstep : ∀ w z : A, w < z → (∀ a : A, ¬(w < a ∧ a < z)) →
      Relation.ReflTransGen Step (conf w) (conf z))
    {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a) (a : A) :
    Relation.ReflTransGen Step (conf a₀) (conf a) := by
  induction a using order_induction with
  | hmin z hz => rw [le_antisymm (hbot z) (hz a₀)]
  | hstep w z hwz hnb ih => exact ih.trans (hstep w z hwz hnb)

/-- **A loop over a finite linear order, on a clock**: one *budgeted* run per
immediate successor, and the machine reaches the configuration of any element
paying that budget once per element it crossed. The count is `orank`, the
number of elements strictly below the target, so a whole loop costs
`w · (card − 1)` and a clocked program can compare it with its clock.

This is `DescriptiveComplexity.Pfp.reflTransGen_of_ordLoop` with the budget
kept, and it is what turns every element and tag loop of the evaluation into a
cost. -/
theorem reachesIn_of_ordLoop {A : Type} [LinearOrder A] [Finite A]
    {S : Type} {M : TMData S} {conf : A → Config S} {w : ℕ}
    (hstep : ∀ x z : A, x < z → (∀ a : A, ¬(x < a ∧ a < z)) →
      M.ReachesIn w (conf x) (conf z))
    {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a) (a : A) :
    M.ReachesIn (w * orank a) (conf a₀) (conf a) := by
  induction a using order_induction with
  | hmin z hz =>
    rw [le_antisymm (hbot z) (hz a₀), orank_eq_zero hz, Nat.mul_zero]
    exact TMData.reachesIn_refl
  | hstep x z hxz hnb ih =>
    have hcov : x ⋖ z := ⟨hxz, fun c h₁ h₂ => hnb c ⟨h₁, h₂⟩⟩
    rw [orank_covBy hcov, Nat.mul_succ]
    exact ih.trans (hstep x z hxz hnb)

/-- **A loop over a finite linear order, at the crude bound**: the whole loop
costs at most the budget of one round times the number of elements. What a
clock is compared with. -/
theorem reachesIn_of_ordLoop_card {A : Type} [LinearOrder A] [Finite A]
    {S : Type} {M : TMData S} {conf : A → Config S} {w : ℕ}
    (hstep : ∀ x z : A, x < z → (∀ a : A, ¬(x < a ∧ a < z)) →
      M.ReachesIn w (conf x) (conf z))
    {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a) (a : A) :
    M.ReachesIn (w * Nat.card A) (conf a₀) (conf a) :=
  (reachesIn_of_ordLoop hstep hbot a).mono
    (Nat.mul_le_mul_left w (Nat.le_of_lt (orank_lt_card a)))

/-- **A loop over tuples in the lexicographic order**: one run per
coordinatewise successor (`DescriptiveComplexity.TupSucc`, the shape the
advancing guards read) carries the machine from the all-minimal tuple to any
tuple. -/
theorem reflTransGen_of_tupLoop {A : Type} [LinearOrder A] [Finite A] {e : ℕ}
    {conf : (Fin e → A) → C}
    (hstep : ∀ v v' : Fin e → A, TupSucc v v' →
      Relation.ReflTransGen Step (conf v) (conf v'))
    {v₀ : Fin e → A} (hbot : ∀ (j : Fin e) (a : A), v₀ j ≤ a) (v : Fin e → A) :
    Relation.ReflTransGen Step (conf v₀) (conf v) := by
  have key : ∀ z : Lex (Fin e → A),
      Relation.ReflTransGen Step (conf v₀) (conf (ofLex z)) := by
    intro z
    induction z using order_induction with
    | hmin z hz =>
      have hb : ∀ u : Lex (Fin e → A), toLex v₀ ≤ u := tup_isBot_iff.mpr hbot
      rw [show v₀ = ofLex z from congrArg ofLex (le_antisymm (hb z) (hz (toLex v₀)))]
    | hstep w z hwz hnb ih =>
      refine ih.trans (hstep (ofLex w) (ofLex z) (tupSucc_iff_covBy.mpr ⟨hwz, ?_⟩))
      intro c hwc hcz
      exact hnb c ⟨hwc, hcz⟩
  exact key (toLex v)

/-- **A loop over tuples in the lexicographic order, on a clock**: one budgeted
run per coordinatewise successor, and the whole enumeration costs that budget
once per tuple. This is the cost of every coordinate loop of the evaluation. -/
theorem reachesIn_of_tupLoop {A : Type} [LinearOrder A] [Finite A] {e : ℕ}
    {S : Type} {M : TMData S} {conf : (Fin e → A) → Config S} {w : ℕ}
    (hstep : ∀ v v' : Fin e → A, TupSucc v v' → M.ReachesIn w (conf v) (conf v'))
    {v₀ : Fin e → A} (hbot : ∀ (j : Fin e) (a : A), v₀ j ≤ a) (v : Fin e → A) :
    M.ReachesIn (w * Nat.card (Lex (Fin e → A))) (conf v₀) (conf v) := by
  refine reachesIn_of_ordLoop_card (conf := fun z : Lex (Fin e → A) => conf (ofLex z))
    (fun x z hxz hnb => ?_) (tup_isBot_iff.mpr hbot) (toLex v)
  exact hstep (ofLex x) (ofLex z)
    (tupSucc_iff_covBy.mpr ⟨hxz, fun c hxc hcz => hnb c ⟨hxc, hcz⟩⟩)

end Loop

end Pfp

end DescriptiveComplexity
