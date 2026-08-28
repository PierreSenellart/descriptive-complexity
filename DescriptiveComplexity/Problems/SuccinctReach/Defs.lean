/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Vocabulary
import DescriptiveComplexity.PSpace

/-!
# SUCCINCT-REACH: reachability in a propositionally described transition system

The vocabulary and semantics of the canonical PSPACE problem of this library:
reachability in a graph whose vertices are the truth assignments to a set of
*state variables* and whose edges, source set and target set are described by
three CNF formulas rather than listed. The graph has exponentially many
vertices in the size of the instance – it is *succinctly represented* – which
is exactly why walking it costs polynomial space and not polynomial time.

Under other names the same problem is propositional STRIPS **plan existence**,
and it is the reachability query at the heart of symbolic model checking.

## The instance

An instance is a `FirstOrder.Language.transSys`-structure. Its elements are
propositional variables and clauses at once, as in
`FirstOrder.Language.sat`, with

* `stateVar x`: `x` is a state variable – a bit of the vertex being walked;
* `next x y`: `y` is the *next-state copy* of the state variable `x`, so that
  one clause set can talk about a state and its successor at once;
* `stepCl c`, `srcCl c`, `tgtCl c`: `c` is a clause of the transition, of the
  source or of the target formula;
* `posIn c x`, `negIn c x`: the variable `x` occurs positively (negatively) in
  the clause `c`, as for SAT.

Variables that are neither state variables nor next-state copies are
*auxiliary*: they are quantified existentially inside each clause group, which
is what lets a CNF describe an arbitrary transition relation (a Tseitin
encoding introduces exactly such variables for its gates).

## The semantics

A *state* is an arbitrary predicate on the universe; only its restriction to
the state variables matters, since that is all the clause groups can read
(`DescriptiveComplexity.ReadsCur`). There is a transition from `S` to `S'` when
some assignment satisfies every transition clause while reading `S` on the
state variables and writing `S'` on their next-state copies
(`DescriptiveComplexity.StepRel`). The instance is a yes-instance when some target
state is reachable from some source state
(`DescriptiveComplexity.SuccinctReachable`).

This is the *syntactic image* of SO(TC), in the same sense that a CNF is the
syntactic image of an existential second-order block: a state is a monadic
relation variable, a transition is a first-order condition on two consecutive
states, and reachability is the transitive closure. That is what makes the
membership half cheap (`DescriptiveComplexity.Problems.SuccinctReach.Membership`) and
the hardness half a Tseitin translation.
-/

/- The language of succinctly described transition systems lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.sat` and `Language.order`. -/
namespace FirstOrder

namespace Language

/-- The relational vocabulary of succinctly described transition systems: the
state variables and their next-state copies, three groups of clauses, and the
two literal-occurrence predicates of `FirstOrder.Language.sat`. -/
fo_language transSys with ts where
  /-- `stateVar x`: the element `x` is a state variable. -/
  stateVar : 1
  /-- `next x y`: the element `y` is the next-state copy of the state
  variable `x`. -/
  next : 2
  /-- `stepCl c`: the element `c` is a clause of the transition formula. -/
  stepCl : 1
  /-- `srcCl c`: the element `c` is a clause of the source formula. -/
  srcCl : 1
  /-- `tgtCl c`: the element `c` is a clause of the target formula. -/
  tgtCl : 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  posIn : 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  negIn : 2

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Semantics

variable (A : Type) [Language.transSys.Structure A]

/-- A valuation satisfies a group of clauses when every clause of the group
contains a literal it makes true. Elements that are not clauses of the group
impose nothing, exactly as in `DescriptiveComplexity.Satisfiable`. -/
def ClausesHold (ν : A → Prop) (grp : Language.transSys.Relations 1) : Prop :=
  ∀ c : A, RelMap grp ![c] →
    ∃ x : A, (RelMap tsPosIn ![c, x] ∧ ν x) ∨ (RelMap tsNegIn ![c, x] ∧ ¬ν x)

/-- The valuation `ν` *reads* the state `S`: on every state variable it agrees
with `S`. This is the only way a clause group sees the current state. -/
def ReadsCur (ν : A → Prop) (S : A → Prop) : Prop :=
  ∀ x : A, RelMap tsStateVar ![x] → (ν x ↔ S x)

/-- The valuation `ν` *writes* the state `S'`: on the next-state copy of every
state variable it holds exactly the value `S'` gives to that variable. -/
def WritesNext (ν : A → Prop) (S' : A → Prop) : Prop :=
  ∀ x y : A, RelMap tsStateVar ![x] → RelMap tsNext ![x, y] → (ν y ↔ S' x)

/-- One transition of the system: some valuation satisfies every transition
clause while reading `S` on the state variables and writing `S'` on their
next-state copies. The valuation is existentially quantified, so the auxiliary
variables of the transition formula are free to take whatever values the
clauses need. -/
def StepRel (S S' : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsStepCl ∧ ReadsCur A ν S ∧ WritesNext A ν S'

/-- A state is a source state when some valuation reading it satisfies every
clause of the source formula. -/
def IsStart (S : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsSrcCl ∧ ReadsCur A ν S

/-- A state is a target state when some valuation reading it satisfies every
clause of the target formula. -/
def IsGoal (S : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsTgtCl ∧ ReadsCur A ν S

/-- **The yes-instances of SUCCINCT-REACH**: some target state is reachable
from some source state along the transitions described by the clauses. -/
def SuccinctReachable : Prop :=
  ∃ S S' : A → Prop, IsStart A S ∧ IsGoal A S' ∧ Relation.ReflTransGen (StepRel A) S S'

end Semantics

/-! ### Isomorphism-invariance

Everything transports along the push-forward of a predicate through the
isomorphism; each piece of the semantics is pushed in one direction only, and
the equivalence comes from applying the result to the inverse isomorphism. -/

section Iso

variable {A B : Type} [Language.transSys.Structure A] [Language.transSys.Structure B]

/-- The push-forward of a predicate along an isomorphism. -/
private def pushPred (e : A ≃[Language.transSys] B) (ν : A → Prop) : B → Prop :=
  fun b => ν (e.symm b)

private theorem clausesHold_push (e : A ≃[Language.transSys] B) {ν : A → Prop}
    {grp : Language.transSys.Relations 1} (h : ClausesHold A ν grp) :
    ClausesHold B (pushPred e ν) grp := by
  intro c hc
  obtain ⟨x, hx⟩ := h (e.symm c) ((relMap_equiv₁ e.symm grp c).mp hc)
  refine ⟨e x, ?_⟩
  have hpush : pushPred e ν (e x) ↔ ν x := by
    rw [pushPred]
    exact iff_of_eq (congrArg ν (e.symm_apply_apply x))
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · refine Or.inl ⟨?_, hpush.mpr hT⟩
    simpa using (relMap_equiv₂ e tsPosIn (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, fun hv => hT (hpush.mp hv)⟩
    simpa using (relMap_equiv₂ e tsNegIn (e.symm c) x).mp hn

private theorem readsCur_push (e : A ≃[Language.transSys] B) {ν S : A → Prop}
    (h : ReadsCur A ν S) : ReadsCur B (pushPred e ν) (pushPred e S) :=
  fun y hy => h (e.symm y) ((relMap_equiv₁ e.symm tsStateVar y).mp hy)

private theorem writesNext_push (e : A ≃[Language.transSys] B) {ν S' : A → Prop}
    (h : WritesNext A ν S') : WritesNext B (pushPred e ν) (pushPred e S') := by
  intro x y hx hxy
  refine h (e.symm x) (e.symm y) ((relMap_equiv₁ e.symm tsStateVar x).mp hx) ?_
  exact (relMap_equiv₂ e.symm tsNext x y).mp hxy

private theorem stepRel_push (e : A ≃[Language.transSys] B) {S S' : A → Prop}
    (h : StepRel A S S') : StepRel B (pushPred e S) (pushPred e S') := by
  obtain ⟨ν, hcl, hr, hw⟩ := h
  exact ⟨pushPred e ν, clausesHold_push e hcl, readsCur_push e hr, writesNext_push e hw⟩

private theorem reach_push (e : A ≃[Language.transSys] B) {S S' : A → Prop}
    (h : Relation.ReflTransGen (StepRel A) S S') :
    Relation.ReflTransGen (StepRel B) (pushPred e S) (pushPred e S') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail (stepRel_push e hcd)

private theorem succinctReachable_of_iso (e : A ≃[Language.transSys] B)
    (h : SuccinctReachable A) : SuccinctReachable B := by
  obtain ⟨S, S', ⟨ν, hcl, hr⟩, ⟨μ, hcl', hr'⟩, hreach⟩ := h
  exact ⟨pushPred e S, pushPred e S',
    ⟨pushPred e ν, clausesHold_push e hcl, readsCur_push e hr⟩,
    ⟨pushPred e μ, clausesHold_push e hcl', readsCur_push e hr'⟩, reach_push e hreach⟩

/-- Reachability in a succinctly described transition system is
isomorphism-invariant. -/
theorem succinctReachable_iso (e : A ≃[Language.transSys] B) :
    SuccinctReachable A ↔ SuccinctReachable B :=
  ⟨succinctReachable_of_iso e, succinctReachable_of_iso e.symm⟩

end Iso

/-- **SUCCINCT-REACH**, as a problem on `FirstOrder.Language.transSys`-structures:
is some target state reachable from some source state in the transition system
described by the three clause groups? -/
def SUCCINCTREACH : DecisionProblem Language.transSys where
  Holds := fun A inst => @SuccinctReachable A inst
  iso_invariant := fun e => succinctReachable_iso e

end DescriptiveComplexity
