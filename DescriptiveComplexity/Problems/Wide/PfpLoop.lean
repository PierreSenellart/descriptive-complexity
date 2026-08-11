/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
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

end Loop

end Pfp

end DescriptiveComplexity
