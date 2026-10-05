import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Lax904597.Problems
import Lax904597.Interpretations

/-!
---
title: First-order logic with a transitive closure
type: definition
---
A transitive-closure specification over a vocabulary $L$ consists of a finite
set of modes, an arity $k$, and first-order formulas over $L \cup \{\le\}$:
a transition formula $\varphi_{m,n}(\bar x, \bar y)$ for each pair of modes
and, for each mode $m$, a source formula $\sigma_m(\bar x)$ and a target
formula $\tau_m(\bar x)$, with $\bar x$ and $\bar y$ tuples of $k$
variables. On a linearly ordered $L$-structure $A$ it defines a directed
graph whose nodes are the pairs $(m, \bar a)$ of a mode and a $k$-tuple of
elements, with an edge from $(m, \bar a)$ to $(n, \bar b)$ when
$A \models \varphi_{m,n}(\bar a, \bar b)$. The specification accepts $A$
when some node satisfying its target formula is reachable, by a possibly
empty path, from some node satisfying its source formula.

A decision problem $P$ over $L$ is FO(TC) definable when some specification
accepts, for every nonempty finite $L$-structure $A$ and every linear order
on $A$, exactly when $A$ is a yes-instance of $P$. This is the normal form
of first-order logic with a transitive closure operator on ordered
structures, a single positive application of the operator; the modes play
the role of a bounded amount of extra state, which tuples of elements cannot
carry on small universes.
-/

namespace Lax485149.TransitiveClosure

open Lax904597.Problems

open FirstOrder

open Language

/-- A single-`TC` definition: the transition formula of a graph on `k`-tuples,
together with formulas for the admissible start and end tuples. All three are
first-order over the ordered expansion of the vocabulary, so that they may
mention the linear order, as the ordered setting of the capture theorem
allows. -/
structure TCSpec (L : Language.{0, 0}) where
  /-- The *modes*: a finite amount of state the walk carries besides its tuple
  of elements. Tuples of elements cannot hold finite data of their own – a
  one-element universe has only one tuple – so, exactly as tags replace the
  order-encoded sorts of a textbook interpretation in `FOInterpretation`, a
  mode carries what the tuple cannot. -/
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

variable {L : Language.{0, 0}} (spec : TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

variable (A) in
/-- A node of the walk: a mode together with a `k`-tuple of elements. -/
abbrev Node : Type := spec.Mode × (Fin spec.k → A)

/-- One step of the walk: the transition formula of the two modes, read with
the current tuple on the left and the next one on the right. -/
def Step (a b : spec.Node A) : Prop :=
  (spec.step a.1 b.1).Realize (Sum.elim a.2 b.2)

/-- Reachability in the walk: the reflexive-transitive closure of
`TCSpec.Step`. -/
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

end TCSpec

/-- A decision problem is *FO(TC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single transitive closure: there is a `TCSpec`
whose accepting tuples are reachable from its starting tuples exactly on the
yes-instances.

The equivalence is required for *every* linear order on the universe, so this
is order-invariant FO(TC) definability: the problem itself does not see the
order, while the transition and endpoint formulas may. -/
def TCDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : TCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A

end Lax485149.TransitiveClosure
