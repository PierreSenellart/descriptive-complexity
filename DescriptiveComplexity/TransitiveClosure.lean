/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Ordered
import DescriptiveComplexity.Complexity

/-!
# FO(TC): first-order logic with transitive closure

The logic that captures nondeterministic logarithmic space on ordered
structures ([Immerman 1987][immerman1987languages]): first-order logic extended
with a *transitive-closure* operator. If `φ(x̄, ȳ)` defines a binary relation on
`k`-tuples, then `TC[x̄, ȳ. φ](ū, v̄)` says that `v̄` is reachable from `ū` in the
`φ`-graph.

## The operator as data

As everywhere in this library, the operator is *not* added to Mathlib's
`FirstOrder.Language.BoundedFormula` as a new constructor – that would mean
redoing relabelling, substitution and realization for an extended syntax, and
losing every existing lemma. It is kept at the Lean level instead: a
`DescriptiveComplexity.TCSpec` bundles the arity `k`, a *first-order* transition
formula over the ordered expansion with two `k`-tuples of free variables, and
the two endpoint formulas; reachability itself is `Relation.ReflTransGen`,
whose induction principles then do the work in proofs. This is the same move as
`DescriptiveComplexity.HornProgram` for SO-Horn and `DescriptiveComplexity.KromProgram` for
SO-Krom.

A single application of `TC` in front of a first-order matrix is not a
restriction on ordered structures: Immerman's normal form makes every
FO(posTC) formula equivalent to one, just as a single existential block
suffices for `DescriptiveComplexity.SigmaSODefinable`. The library takes that normal
form as the *definition* (`DescriptiveComplexity.TCDefinable`), exactly as it takes
`Σ₁`-definability as the definition of NP rather than proving Fagin's theorem
against a machine.

## What this is for

`DescriptiveComplexity.NL` is already defined, by the Krom fragment
(`DescriptiveComplexity.LogSpace`), and the two coincide
(`DescriptiveComplexity.tcDefinable_iff_mem_NL`), so FO(TC) is not set up as a
second complexity class; the modes are what would make that possible, should it
become useful. A walk whose state were only a tuple of elements could not be
pulled back through an interpretation, whose tags vary from node to node, and
could not carry the finite data a translation needs (the atom index and sign of
a literal, say); carrying it in coordinates would fail on a one-element
universe. FO(TC) is here as the logic in which two things are naturally stated:

* the translation to the Krom fragment, which goes through the *complement* –
  a clausal fragment states closure and rejection, so it defines
  non-reachability head-on, exactly as `DescriptiveComplexity.unreach_mem_NL` does for
  the concrete case;
* **Immerman–Szelepcsényi**, closure of FO(TC) under complement
  (`DescriptiveComplexity.TCDefinable.compl` in
  `DescriptiveComplexity.TransitiveClosureCompl`), whose inductive-counting proof is a
  walk on configurations – a phase, a flag and eight registers, each a node or
  a count – and so lives inside a single `TC`. That theorem turns the above
  translation into an equivalence and gives `REACH ∈ NL`.

The canonical example is `DescriptiveComplexity.reach_tcDefinable` – REACH *is* a `TC`,
at arity one and with a single mode, over the edge relation between the marked
sources and the marked targets.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

/-! ### Specifications -/

/-- A single-`TC` definition: the transition formula of a graph on `k`-tuples,
together with formulas for the admissible start and end tuples. All three are
first-order over the ordered expansion of the vocabulary, so that they may
mention the linear order, as the ordered setting of the capture theorem
allows. -/
structure TCSpec (L : Language.{0, 0}) where
  /-- The *modes*: a finite amount of state the walk carries besides its tuple
  of elements. Tuples of elements cannot hold finite data of their own – a
  one-element universe has only one tuple – so, exactly as tags replace the
  order-encoded sorts of a textbook interpretation in
  `DescriptiveComplexity.FOInterpretation`, a mode carries what the tuple cannot. -/
  Mode : Type
  /-- Modes are finite. -/
  [modeFinite : Finite Mode]
  /-- The arity: the walk runs on `k`-tuples of elements. -/
  k : ℕ
  /-- The transition formula, one per pair of modes, with two `k`-tuples of
  free variables: the current tuple on the left, the next one on the right. -/
  step : Mode → Mode → (L.sum Language.order).Formula (Fin k ⊕ Fin k)
  /-- The formula defining the admissible starting tuples, per mode. -/
  src : Mode → (L.sum Language.order).Formula (Fin k)
  /-- The formula defining the accepting tuples, per mode. -/
  tgt : Mode → (L.sum Language.order).Formula (Fin k)

attribute [instance] TCSpec.modeFinite

namespace TCSpec

section Semantics

variable (spec : TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

variable (A) in
/-- A node of the walk: a mode together with a `k`-tuple of elements. -/
abbrev Node : Type := spec.Mode × (Fin spec.k → A)

/-- One step of the walk: the transition formula of the two modes, read with
the current tuple on the left and the next one on the right. -/
def Step (a b : spec.Node A) : Prop :=
  (spec.step a.1 b.1).Realize (Sum.elim a.2 b.2)

/-- Reachability in the walk: the reflexive-transitive closure of
`DescriptiveComplexity.TCSpec.Step`. -/
abbrev Reach : spec.Node A → spec.Node A → Prop :=
  Relation.ReflTransGen spec.Step

/-- A node is a starting node when its tuple satisfies the source formula of
its mode. -/
def IsSrc (a : spec.Node A) : Prop := (spec.src a.1).Realize a.2

/-- A node is accepting when its tuple satisfies the target formula of its
mode. -/
def IsTgt (a : spec.Node A) : Prop := (spec.tgt a.1).Realize a.2

variable (A) in
/-- The structure is accepted: some accepting node is reachable from some
starting node. -/
def Accepts : Prop :=
  ∃ u v : spec.Node A, spec.IsSrc u ∧ spec.IsTgt v ∧ spec.Reach u v

end Semantics

/-! ### Isomorphism-invariance -/

section Iso

variable (spec : TCSpec L) {A B : Type} [L.Structure A] [LinearOrder A]
variable [L.Structure B] [LinearOrder B]

/-- The image of a node under an isomorphism: same mode, transported tuple. -/
def mapNode (e : A ≃[L.sum Language.order] B) (a : spec.Node A) : spec.Node B :=
  (a.1, fun i => e (a.2 i))

/-- One step is preserved by an isomorphism of the ordered expansions. -/
theorem step_equiv (e : A ≃[L.sum Language.order] B) (a b : spec.Node A) :
    spec.Step (spec.mapNode e a) (spec.mapNode e b) ↔ spec.Step a b := by
  rw [Step, Step, mapNode, mapNode, ← StrongHomClass.realize_formula
    (φ := spec.step a.1 b.1) e]
  refine iff_of_eq (congrArg (spec.step a.1 b.1).Realize (funext fun i => ?_))
  cases i <;> rfl

/-- Reachability is preserved by an isomorphism of the ordered expansions. -/
theorem reach_equiv (e : A ≃[L.sum Language.order] B) {a b : spec.Node A}
    (h : spec.Reach a b) : spec.Reach (spec.mapNode e a) (spec.mapNode e b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail ((spec.step_equiv e c d).mpr hcd)

private theorem accepts_of_equiv (e : A ≃[L.sum Language.order] B) (h : spec.Accepts A) :
    spec.Accepts B := by
  obtain ⟨u, v, hu, hv, huv⟩ := h
  refine ⟨spec.mapNode e u, spec.mapNode e v, ?_, ?_, spec.reach_equiv e huv⟩
  · change (spec.src u.1).Realize (⇑e ∘ u.2)
    rw [StrongHomClass.realize_formula (φ := spec.src u.1) e]
    exact hu
  · change (spec.tgt v.1).Realize (⇑e ∘ v.2)
    rw [StrongHomClass.realize_formula (φ := spec.tgt v.1) e]
    exact hv

/-- **Acceptance is isomorphism-invariant** (for isomorphisms of the ordered
expansions, the order being visible to the formulas). -/
theorem accepts_equiv (e : A ≃[L.sum Language.order] B) : spec.Accepts A ↔ spec.Accepts B :=
  ⟨spec.accepts_of_equiv e, spec.accepts_of_equiv e.symm⟩

end Iso

end TCSpec

/-! ### FO(TC) definability -/

/-- A decision problem is *FO(TC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single transitive closure: there is a
`DescriptiveComplexity.TCSpec` whose accepting tuples are reachable from its starting
tuples exactly on the yes-instances.

As for `DescriptiveComplexity.SigmaSOHornDefinable`, the equivalence is required for
*every* linear order on the universe, so this is order-invariant FO(TC)
definability: the problem itself does not see the order, while the transition
and endpoint formulas may. -/
def TCDefinable (P : DecisionProblem L) : Prop :=
  ∃ spec : TCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A

/-- FO(TC) definability only depends on the finite instances of a problem. -/
theorem tcDefinable_congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    TCDefinable P ↔ TCDefinable Q := by
  constructor <;> rintro ⟨spec, hspec⟩ <;> refine ⟨spec, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hspec A)
  · exact (h A).trans (hspec A)

end DescriptiveComplexity
