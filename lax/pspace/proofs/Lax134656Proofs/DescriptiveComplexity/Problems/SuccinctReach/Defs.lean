/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.Vocabulary
import Lax134656Proofs.DescriptiveComplexity.PSpace
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SuccinctReach
end Lax134656.SuccinctReach

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax134656Proofs.DescriptiveComplexity
export Lax134656.SuccinctReach (ClausesHold IsGoal IsStart ReadsCur StepRel SuccinctReachable WritesNext)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax134656.SuccinctReach (transSys tsNegIn tsNext tsPosIn tsSrcCl tsStateVar tsStepCl tsTgtCl)
end FirstOrder.Language

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

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Semantics

variable (A : Type) [Lax134656.SuccinctReach.transSys.Structure A]

end Semantics

/-! ### Isomorphism-invariance

Everything transports along the push-forward of a predicate through the
isomorphism; each piece of the semantics is pushed in one direction only, and
the equivalence comes from applying the result to the inverse isomorphism. -/

section Iso

variable {A B : Type} [Lax134656.SuccinctReach.transSys.Structure A] [Lax134656.SuccinctReach.transSys.Structure B]

/-- The push-forward of a predicate along an isomorphism. -/
private def pushPred (e : A ≃[Lax134656.SuccinctReach.transSys] B) (ν : A → Prop) : B → Prop :=
  fun b => ν (e.symm b)

private theorem clausesHold_push (e : A ≃[Lax134656.SuccinctReach.transSys] B) {ν : A → Prop}
    {grp : Lax134656.SuccinctReach.transSys.Relations 1} (h : Lax134656.SuccinctReach.ClausesHold A ν grp) :
    Lax134656.SuccinctReach.ClausesHold B (pushPred e ν) grp := by
  intro c hc
  obtain ⟨x, hx⟩ := h (e.symm c) ((relMap_equiv₁ e.symm grp c).mp hc)
  refine ⟨e x, ?_⟩
  have hpush : pushPred e ν (e x) ↔ ν x := by
    rw [pushPred]
    exact iff_of_eq (congrArg ν (e.symm_apply_apply x))
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · refine Or.inl ⟨?_, hpush.mpr hT⟩
    simpa using (relMap_equiv₂ e Lax134656.SuccinctReach.tsPosIn (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, fun hv => hT (hpush.mp hv)⟩
    simpa using (relMap_equiv₂ e Lax134656.SuccinctReach.tsNegIn (e.symm c) x).mp hn

private theorem readsCur_push (e : A ≃[Lax134656.SuccinctReach.transSys] B) {ν S : A → Prop}
    (h : Lax134656.SuccinctReach.ReadsCur A ν S) : Lax134656.SuccinctReach.ReadsCur B (pushPred e ν) (pushPred e S) :=
  fun y hy => h (e.symm y) ((relMap_equiv₁ e.symm Lax134656.SuccinctReach.tsStateVar y).mp hy)

private theorem writesNext_push (e : A ≃[Lax134656.SuccinctReach.transSys] B) {ν S' : A → Prop}
    (h : Lax134656.SuccinctReach.WritesNext A ν S') : Lax134656.SuccinctReach.WritesNext B (pushPred e ν) (pushPred e S') := by
  intro x y hx hxy
  refine h (e.symm x) (e.symm y) ((relMap_equiv₁ e.symm Lax134656.SuccinctReach.tsStateVar x).mp hx) ?_
  exact (relMap_equiv₂ e.symm Lax134656.SuccinctReach.tsNext x y).mp hxy

private theorem stepRel_push (e : A ≃[Lax134656.SuccinctReach.transSys] B) {S S' : A → Prop}
    (h : Lax134656.SuccinctReach.StepRel A S S') : Lax134656.SuccinctReach.StepRel B (pushPred e S) (pushPred e S') := by
  obtain ⟨ν, hcl, hr, hw⟩ := h
  exact ⟨pushPred e ν, clausesHold_push e hcl, readsCur_push e hr, writesNext_push e hw⟩

private theorem reach_push (e : A ≃[Lax134656.SuccinctReach.transSys] B) {S S' : A → Prop}
    (h : Relation.ReflTransGen (Lax134656.SuccinctReach.StepRel A) S S') :
    Relation.ReflTransGen (Lax134656.SuccinctReach.StepRel B) (pushPred e S) (pushPred e S') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail (stepRel_push e hcd)

private theorem succinctReachable_of_iso (e : A ≃[Lax134656.SuccinctReach.transSys] B)
    (h : Lax134656.SuccinctReach.SuccinctReachable A) : Lax134656.SuccinctReach.SuccinctReachable B := by
  obtain ⟨S, S', ⟨ν, hcl, hr⟩, ⟨μ, hcl', hr'⟩, hreach⟩ := h
  exact ⟨pushPred e S, pushPred e S',
    ⟨pushPred e ν, clausesHold_push e hcl, readsCur_push e hr⟩,
    ⟨pushPred e μ, clausesHold_push e hcl', readsCur_push e hr'⟩, reach_push e hreach⟩

/-- Reachability in a succinctly described transition system is
isomorphism-invariant. -/
theorem succinctReachable_iso (e : A ≃[Lax134656.SuccinctReach.transSys] B) :
    Lax134656.SuccinctReach.SuccinctReachable A ↔ Lax134656.SuccinctReach.SuccinctReachable B :=
  ⟨succinctReachable_of_iso e, succinctReachable_of_iso e.symm⟩

end Iso

/-- **SUCCINCT-REACH**, as a problem on `FirstOrder.Language.transSys`-structures:
is some target state reachable from some source state in the transition system
described by the three clause groups? -/
def SUCCINCTREACH : Lax904597.Problems.DecisionProblem Lax134656.SuccinctReach.transSys where
  Holds := fun A inst => @Lax134656.SuccinctReach.SuccinctReachable A inst
  iso_invariant := fun e => succinctReachable_iso e

end Lax134656Proofs.DescriptiveComplexity


