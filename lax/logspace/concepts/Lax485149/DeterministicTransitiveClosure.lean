import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax485149.TransitiveClosure
import Lax904597.Problems
import Lax904597.Interpretations

/-!
---
title: First-order logic with a deterministic transitive closure
type: definition
---
The determinization of a transitive-closure specification keeps its modes,
arity, source and target formulas, and replaces each transition formula
$\varphi_{m,n}(\bar x, \bar y)$ by
$$\varphi_{m,n}(\bar x, \bar y) \wedge \bigwedge_{m'} \forall \bar z\,
\bigl(\varphi_{m,m'}(\bar x, \bar z) \to m' = n \wedge \bar z = \bar y\bigr),$$
the comparison of modes being resolved statically. In the graph it defines,
a node has an outgoing edge exactly when it had a single one in the original
graph: the walk follows the forced steps only.

A decision problem $P$ over a vocabulary $L$ is FO(DTC) definable when the
determinization of some specification accepts, for every nonempty finite
$L$-structure $A$ and every linear order on $A$, exactly when $A$ is a
yes-instance of $P$. This is first-order logic with a deterministic
transitive closure operator on ordered structures, in the normal form of a
single application.
-/

namespace Lax485149.DeterministicTransitiveClosure

open Lax485149.TransitiveClosure Lax904597.Problems

open FirstOrder

open Language Structure

namespace TCSpec

section Det

variable {L : Language.{0, 0}} (spec : TCSpec L)

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
        (((spec.step m m').relabel (detVar spec)).imp
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
  step := detStep spec
  src := spec.src
  tgt := spec.tgt

end Det

end TCSpec

/-- A decision problem is *FO(DTC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single **deterministic** transitive closure:
there is a `TCSpec` whose accepting nodes are reachable from its starting
nodes *along its determinization* exactly on the yes-instances.

As for `TCDefinable`, the equivalence is required for every linear order on
the universe, so this is order-invariant FO(DTC) definability. -/
def DTCDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : TCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ (TCSpec.det spec).Accepts A

end Lax485149.DeterministicTransitiveClosure
