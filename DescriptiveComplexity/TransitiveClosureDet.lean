/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosure

/-!
# FO(DTC): first-order logic with deterministic transitive closure

The logic that captures *deterministic* logarithmic space on ordered
structures ([Immerman 1987][immerman1987languages]): first-order logic with a
transitive-closure operator that may only follow a step when it is the *only*
step available. `DescriptiveComplexity.LOGSPACE` is defined by it, exactly as
`DescriptiveComplexity.NL` is defined by the Krom fragment and
`DescriptiveComplexity.PTIME` by the Horn one.

## Determinism as a formula, not as a side condition

There are two ways to say "the walk is deterministic". One is to carry a
proof: a specification together with the hypothesis that its `Step` relation is
functional on every structure. That is the wrong choice here – the hypothesis is
not first-order data, and it would have to be re-established after every
pullback, at which point closure under reductions stops being a syntactic
argument.

The other is Immerman's own: keep an arbitrary
`DescriptiveComplexity.TCSpec` and read its transition formula through its
*determinization*

```
detStep(x̄, ȳ)  :=  step(x̄, ȳ)  ∧  ∀ z̄. step(x̄, z̄) → z̄ = ȳ
```

which is again first-order. Every specification then denotes a legitimate
deterministic walk (`DescriptiveComplexity.TCSpec.det_functional`), nothing has to be
preserved, and nothing is lost: on a specification whose steps are already
functional the determinization is equivalent to it
(`DescriptiveComplexity.TCSpec.det_step_of_functional`).

The one wrinkle the textbook formula does not show is **modes**. A node of a
`DescriptiveComplexity.TCSpec` is a mode together with a tuple
(`DescriptiveComplexity.TCSpec.Node`), so "the only step available" has to quantify
over successor *nodes*, not successor tuples: the uniqueness clause is a finite
conjunction over the modes, in which the mode comparison is resolved at
formula-construction time (`⊥` for a mode other than the intended target, so
that a step into it refutes the guard). This is the same static/dynamic split
as the tag comparisons of `DescriptiveComplexity.lexLeF`.

## What is here

`DescriptiveComplexity.TCSpec.det` and its semantics
(`DescriptiveComplexity.TCSpec.det_step_iff`: a determinized step is a step with no
competitor), the resulting definability notion
`DescriptiveComplexity.DTCDefinable`, and the inclusion at the level of definability,
`DescriptiveComplexity.DTCDefinable.tcDefinable` – the future `L ⊆ NL`, a one-liner
because a determinized specification *is* a specification.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

/-! ### Determinizing the transition formula -/

section Det

variable (spec : TCSpec L)

/-- The renaming used by the uniqueness clause: the transition formula is
re-read with its first tuple still the current one and its second tuple the
freshly quantified `z̄`. -/
def detVar : Fin spec.k ⊕ Fin spec.k → (Fin spec.k ⊕ Fin spec.k) ⊕ Fin spec.k :=
  Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr

open Classical in
/-- **The determinized transition formula** at a pair of modes: this step, and
no other step out of the current node. The competing successors are quantified
as a tuple `z̄` and a *mode* `m'`; the mode is compared statically, so the
uniqueness clause has one conjunct per mode, asserting `z̄ = ȳ` at the intended
one and refuting the step at every other. -/
noncomputable def detStep (m n : spec.Mode) :
    (L.sum Language.order).Formula (Fin spec.k ⊕ Fin spec.k) :=
  spec.step m n ⊓
    Formula.iInf fun m' : spec.Mode =>
      Formula.iAlls (Fin spec.k)
        (((spec.step m m').relabel spec.detVar).imp
          (if m' = n then
            Formula.iInf fun i : Fin spec.k =>
              Term.equal (Term.var (Sum.inr i)) (Term.var (Sum.inl (Sum.inr i)))
          else ⊥))

/-- **The deterministic reading of a specification**: the same modes, arity and
endpoints, with the transition formula replaced by its determinization.

Marked `@[reducible]` so that the modes and the arity of `spec.det` are those of
`spec` transparently: a node of the deterministic reading *is* a node, and
numerals at `Fin spec.det.k` elaborate as they do at `Fin spec.k`. -/
@[reducible]
noncomputable def det : TCSpec L where
  Mode := spec.Mode
  k := spec.k
  step := spec.detStep
  src := spec.src
  tgt := spec.tgt

@[simp]
theorem det_mode : spec.det.Mode = spec.Mode := rfl

@[simp]
theorem det_k : spec.det.k = spec.k := rfl

end Det

/-! ### Semantics of the determinization -/

section DetSemantics

variable (spec : TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_detStep (m n : spec.Mode) (x y : Fin spec.k → A) :
    (spec.detStep m n).Realize (Sum.elim x y) ↔
      (spec.step m n).Realize (Sum.elim x y) ∧
        ∀ (m' : spec.Mode) (z : Fin spec.k → A),
          (spec.step m m').Realize (Sum.elim x z) → m' = n ∧ z = y := by
  classical
  rw [detStep, Formula.realize_inf, Formula.realize_iInf]
  refine and_congr Iff.rfl ⟨fun h m' z hz => ?_, fun h m' => ?_⟩
  · have hm := (Formula.realize_iAlls).mp (h m') z
    rw [Formula.realize_imp, Formula.realize_relabel] at hm
    have hrel : (Sum.elim (Sum.elim x y) z) ∘ spec.detVar = Sum.elim x z := by
      funext i
      rcases i with i | i <;> rfl
    rw [hrel] at hm
    have hc := hm hz
    by_cases hmn : m' = n
    · refine ⟨hmn, ?_⟩
      rw [if_pos hmn, Formula.realize_iInf] at hc
      funext i
      have := hc i
      rw [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
      exact this
    · rw [if_neg hmn, Formula.realize_bot] at hc
      exact hc.elim
  · refine Formula.realize_iAlls.mpr fun z => ?_
    rw [Formula.realize_imp, Formula.realize_relabel]
    have hrel : (Sum.elim (Sum.elim x y) z) ∘ spec.detVar = Sum.elim x z := by
      funext i
      rcases i with i | i <;> rfl
    rw [hrel]
    intro hz
    obtain ⟨hmn, hzy⟩ := h m' z hz
    rw [if_pos hmn, Formula.realize_iInf]
    intro i
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact congrFun hzy i

/-- **A determinized step is a step with no competitor**: the node `b` is
reached from `a` in the deterministic walk exactly when it is reached in the
original one and is the only node so reached. -/
theorem det_step_iff (a b : spec.Node A) :
    spec.det.Step a b ↔ spec.Step a b ∧ ∀ c : spec.Node A, spec.Step a c → c = b := by
  change (spec.detStep a.1 b.1).Realize (Sum.elim a.2 b.2) ↔ _
  rw [realize_detStep]
  refine and_congr Iff.rfl ⟨fun h c hc => ?_, fun h m' z hz => ?_⟩
  · obtain ⟨hm, hz⟩ := h c.1 c.2 hc
    exact Prod.ext_iff.mpr ⟨hm, hz⟩
  · have := h (m', z) hz
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- The source nodes of the deterministic reading are those of the original. -/
@[simp]
theorem det_isSrc (a : spec.Node A) : spec.det.IsSrc a ↔ spec.IsSrc a := Iff.rfl

/-- The accepting nodes of the deterministic reading are those of the
original. -/
@[simp]
theorem det_isTgt (a : spec.Node A) : spec.det.IsTgt a ↔ spec.IsTgt a := Iff.rfl

end DetSemantics

/-! ### Functional specifications -/

section Functional

variable (spec : TCSpec L) (A : Type) [L.Structure A] [LinearOrder A]

/-- A specification is *functional* on a structure when every node has at most
one successor: the walk it describes is deterministic on the nose. -/
def Functional : Prop :=
  ∀ a b c : spec.Node A, spec.Step a b → spec.Step a c → b = c

variable {spec A}

/-- **The deterministic reading is functional**, whatever the specification it
comes from: this is what makes determinization the right packaging, there
being nothing left to assume. -/
theorem det_functional : spec.det.Functional A := by
  intro a b c hb hc
  obtain ⟨-, hu⟩ := (spec.det_step_iff a b).mp hb
  exact (hu c ((spec.det_step_iff a c).mp hc).1).symm

/-- **Determinizing a functional specification changes nothing**: no step had
a competitor to begin with. -/
theorem det_step_of_functional (h : spec.Functional A) (a b : spec.Node A) :
    spec.det.Step a b ↔ spec.Step a b := by
  rw [spec.det_step_iff a b]
  exact ⟨And.left, fun hab => ⟨hab, fun c hc => h a c b hc hab⟩⟩

end Functional

end TCSpec

/-! ### FO(DTC) definability -/

/-- A decision problem is *FO(DTC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single **deterministic** transitive closure:
there is a `DescriptiveComplexity.TCSpec` whose accepting nodes are reachable from
its starting nodes *along its determinization* exactly on the yes-instances.

As for `DescriptiveComplexity.TCDefinable`, the equivalence is required for every
linear order on the universe, so this is order-invariant FO(DTC) definability:
the problem itself does not see the order, while the transition and endpoint
formulas may. The order cannot be guessed away here either
(`DescriptiveComplexity.sotcDefinable_iff_free` is what SO(TC) can do and this
logic cannot): a deterministic walk has nothing to guess with. -/
def DTCDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : TCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.det.Accepts A

/-- FO(DTC) definability only depends on the finite instances of a problem. -/
theorem dtcDefinable_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    DTCDefinable P ↔ DTCDefinable Q := by
  constructor <;> rintro ⟨spec, hspec⟩ <;> refine ⟨spec, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hspec A)
  · exact (h A).trans (hspec A)

/-- **FO(DTC) ⊆ FO(TC)**, the definability-level `L ⊆ NL`: a determinized
specification is a specification like any other. -/
theorem DTCDefinable.tcDefinable [L.IsRelational] {P : DecisionProblem L} (h : DTCDefinable P) :
    TCDefinable P := by
  obtain ⟨spec, hspec⟩ := h
  exact ⟨spec.det, hspec⟩

end DescriptiveComplexity
