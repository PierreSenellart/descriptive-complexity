/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax485149Proofs.DescriptiveComplexity.Vocabulary
import Lax485149Proofs.DescriptiveComplexity.Problems.HornSat.Hardness
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Order.Lattice.Nat
import Lax485149Proofs.DescriptiveComplexity.Padding
import Lax485149Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax485149Proofs.DescriptiveComplexity.SecondOrderHornPull
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lax485149Proofs.DescriptiveComplexity.Hierarchy
import Lax485149Proofs.DescriptiveComplexity.OrderWalk
import Lax485149Proofs.DescriptiveComplexity.LogSpace
import Lax485149Proofs.DescriptiveComplexity.TransitiveClosure
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax485149.Reachability
end Lax485149.Reachability

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax485149Proofs.Foreign.FirstOrder.Language
end Lax485149Proofs.Foreign.FirstOrder.Language

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax485149Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax485149.KromFragment (KromClause KromLit KromProgram SigmaSOKromDefinable)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCDefinable TCSpec)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax485149.Reachability (Reachable SGEdge SGSource SGTarget)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax485149Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax485149.Reachability (sgEdge sgSource sgTarget stGraph)
end FirstOrder.Language

/-!
# Reachability, and the Horn fragment at work

The problem REACH – is some marked target reachable from some marked source in
a directed graph? – and its complement UNREACH, over the vocabulary
`FirstOrder.Language.stGraph` of graphs with marked sources and targets.

The point of this file is UNREACH: it is the worked instance of the SO-Horn
fragment of `DescriptiveComplexity.SecondOrderHorn`. Its Horn program guesses a binary
relation `T` and forces it, by two rules, to contain the transitive closure of
the edge relation, then rules out with a goal clause the case of a marked
target lying in `T` (or being itself a marked source):

```
             edge(x, y) → T(x, y)
  T(x, y) ∧  edge(y, z) → T(x, z)
  T(x, y) ∧ source(x) ∧ target(y) → ⊥
            source(x) ∧ target(x) → ⊥
```

Such a program is satisfiable exactly when its *least* model – here the
transitive closure – already satisfies the goal clauses, which is why the
existential second-order quantifier in front of a Horn kernel expresses a
polynomial-time property rather than a nondeterministic guess. That is the
content of `DescriptiveComplexity.unreach_sigmaSOHornDefinable`, and with the Horn
discharge it gives `DescriptiveComplexity.unreach_le_hornSat`: UNREACH first-order
reduces to HORN-SAT.

Note that it is the *complement* that the fragment defines: goal clauses can
only rule models out. This is the usual state of affairs for SO-Horn, and
harmless, both problems being in polynomial time.

The same file also places UNREACH one level lower, in
`DescriptiveComplexity.NL`: the Krom fragment defines it by a *two-literal*
program guessing the set `U` of vertices from which a marked target is
reachable,

```
              target(x) → U(x)
  edge(x, y)            → ¬U(y) ∨ U(x)
              source(x) → ¬U(x)
```

and the same asymmetry appears one level down, for the same reason. A clausal
fragment states closure and rejection, so it defines UNREACH head-on
(`DescriptiveComplexity.unreach_mem_NL`) while REACH would need the guessed set to be
*contained* in the true reachable set – a minimality condition no clause can
impose. At the Horn level the way out was the equivalence with FO(LFP), a full
logic closed under negation; at the Krom level the corresponding statement is
`NL = coNL`, i.e., Immerman–Szelepcsényi, and it is what carries
`DescriptiveComplexity.unreach_mem_NL` over to `REACH ∈ NL`
(`DescriptiveComplexity.reach_mem_NL`, in
`DescriptiveComplexity.ImmermanSzelepcsenyi`).
-/

namespace FirstOrder

namespace Language

open Lax485149Proofs.Foreign.FirstOrder.Language in
/-- The edge symbol in the ordered expansion. -/
abbrev _root_.Lax485149Proofs.Foreign.FirstOrder.Language.sgEdgeO : (Lax485149.Reachability.stGraph.sum Language.order).Relations 2 := Sum.inl Lax485149.Reachability.sgEdge

export Lax485149Proofs.Foreign.FirstOrder.Language (sgEdgeO)

open Lax485149Proofs.Foreign.FirstOrder.Language in
/-- The marked-source symbol in the ordered expansion. -/
abbrev _root_.Lax485149Proofs.Foreign.FirstOrder.Language.sgSourceO : (Lax485149.Reachability.stGraph.sum Language.order).Relations 1 := Sum.inl Lax485149.Reachability.sgSource

export Lax485149Proofs.Foreign.FirstOrder.Language (sgSourceO)

open Lax485149Proofs.Foreign.FirstOrder.Language in
/-- The marked-target symbol in the ordered expansion. -/
abbrev _root_.Lax485149Proofs.Foreign.FirstOrder.Language.sgTargetO : (Lax485149.Reachability.stGraph.sum Language.order).Relations 1 := Sum.inl Lax485149.Reachability.sgTarget

export Lax485149Proofs.Foreign.FirstOrder.Language (sgTargetO)

end Language

end FirstOrder

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Defs

variable {A : Type} [Lax485149.Reachability.stGraph.Structure A]

end Defs

section Iso

variable {A B : Type} [Lax485149.Reachability.stGraph.Structure A] [Lax485149.Reachability.stGraph.Structure B]

private theorem sgEdge_map (e : A ≃[Lax485149.Reachability.stGraph] B) (a b : A) :
    Lax485149.Reachability.SGEdge a b ↔ Lax485149.Reachability.SGEdge (e a) (e b) :=
  relMap_equiv₂ e Lax485149.Reachability.sgEdge a b

private theorem reflTransGen_map (e : A ≃[Lax485149.Reachability.stGraph] B) {a b : A}
    (h : Relation.ReflTransGen Lax485149.Reachability.SGEdge a b) :
    Relation.ReflTransGen Lax485149.Reachability.SGEdge (e a) (e b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ((sgEdge_map e _ _).mp hbc)

private theorem reachable_of_iso (e : A ≃[Lax485149.Reachability.stGraph] B) (h : Lax485149.Reachability.Reachable A) :
    Lax485149.Reachability.Reachable B := by
  obtain ⟨s, t, hs, ht, hpath⟩ := h
  exact ⟨e s, e t, (relMap_equiv₁ e Lax485149.Reachability.sgSource s).mp hs,
    (relMap_equiv₁ e Lax485149.Reachability.sgTarget t).mp ht, reflTransGen_map e hpath⟩

/-- Reachability is isomorphism-invariant. -/
theorem reachable_iso (e : A ≃[Lax485149.Reachability.stGraph] B) : Lax485149.Reachability.Reachable A ↔ Lax485149.Reachability.Reachable B :=
  ⟨reachable_of_iso e, reachable_of_iso e.symm⟩

end Iso

/-- REACH, as a problem on graphs with marked sources and targets. -/
def REACH : Lax904597.Problems.DecisionProblem Lax485149.Reachability.stGraph where
  Holds := fun A inst => @Lax485149.Reachability.Reachable A inst
  iso_invariant := fun e => reachable_iso e

/-- UNREACH, the complement of REACH: no marked target is reachable from a
marked source. -/
def UNREACH : Lax904597.Problems.DecisionProblem Lax485149.Reachability.stGraph := REACHᶜ

/-! ### The Horn program -/

/-- The guard `edge (xᵢ, xⱼ)`. Guards live over the ordered expansion of the
vocabulary, as `DescriptiveComplexity.SigmaSOHornDefinable` requires; this program
happens not to need the order. -/
noncomputable def edgeG (i j : Fin 3) :
    (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₂ Lax485149Proofs.Foreign.FirstOrder.Language.sgEdgeO (Term.var i) (Term.var j)

/-- The guard `source xᵢ`. -/
noncomputable def sourceG (i : Fin 3) :
    (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₁ Lax485149Proofs.Foreign.FirstOrder.Language.sgSourceO (Term.var i)

/-- The guard `target xᵢ`. -/
noncomputable def targetG (i : Fin 3) :
    (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₁ Lax485149Proofs.Foreign.FirstOrder.Language.sgTargetO (Term.var i)

/-! ### Correctness of the program -/

section Program

variable {A : Type} [Lax485149.Reachability.stGraph.Structure A] [LinearOrder A]

end Program

/-! ### UNREACH is SO-Horn definable -/

/-! ### UNREACH is SO-Krom definable, hence in NL

The Krom fragment needs no transitive closure: it guesses the set of vertices
from which a marked target is reachable, closes it under *predecessors* – a
two-literal implication – and forbids a marked source to belong to it. -/

/-- The block of the SO-Krom definition of UNREACH: one unary relation
variable, the set of vertices from which a marked target is reachable. -/
def uBlock : Lax904597.SecondOrder.SOBlock where
  ι := Unit
  arity := fun _ => 1

/-- The atom `U xᵢ` of the guessed set. -/
def uAtom (i : Fin 3) : Lax485149.SecondOrderAtoms.SOAtom uBlock 3 :=
  ⟨(), ![i]⟩

/-- The literal `U xᵢ`, positive or negated. -/
def uLit (i : Fin 3) (pos : Bool) : Lax485149.KromFragment.KromLit uBlock 3 :=
  ⟨uAtom i, pos⟩

/-- A marked target belongs to `U`. -/
noncomputable def unreachK1 :
    Lax485149.KromFragment.KromClause (Lax485149.Reachability.stGraph.sum Language.order) uBlock 3 :=
  { guard := targetG 0, lit₁ := some (uLit 0 true), lit₂ := none }

/-- `U` is closed under predecessors: an edge into `U` starts in `U`. -/
noncomputable def unreachK2 :
    Lax485149.KromFragment.KromClause (Lax485149.Reachability.stGraph.sum Language.order) uBlock 3 :=
  { guard := edgeG 0 1, lit₁ := some (uLit 1 false), lit₂ := some (uLit 0 true) }

/-- No marked source belongs to `U`. -/
noncomputable def unreachK3 :
    Lax485149.KromFragment.KromClause (Lax485149.Reachability.stGraph.sum Language.order) uBlock 3 :=
  { guard := sourceG 0, lit₁ := some (uLit 0 false), lit₂ := none }

/-- The Krom program defining UNREACH. -/
noncomputable def unreachKromProgram :
    Lax485149.KromFragment.KromProgram (Lax485149.Reachability.stGraph.sum Language.order) uBlock 3 :=
  [unreachK1, unreachK2, unreachK3]

section KromProgram

variable {A : Type} [Lax485149.Reachability.stGraph.Structure A] [LinearOrder A]

/-- The set guessed by an assignment of the block. -/
def URel (ρ : uBlock.Assignment A) (x : A) : Prop := ρ () ![x]

omit [Lax485149.Reachability.stGraph.Structure A] [LinearOrder A] in
private theorem uLit_holds (ρ : uBlock.Assignment A) (v : Fin 3 → A) (i : Fin 3)
    (pos : Bool) : (uLit i pos).Holds ρ v ↔ (if pos then URel ρ (v i) else ¬URel ρ (v i)) := by
  have hatom : (uAtom i).Holds ρ v ↔ URel ρ (v i) := by
    refine iff_of_eq (congrArg (ρ ()) (funext fun l => ?_))
    fin_cases l
    rfl
  cases pos with
  | false => exact not_congr hatom
  | true => exact hatom

private theorem realize_edgeG' (v : Fin 3 → A) (i j : Fin 3) :
    (edgeG i j).Realize v ↔ Lax485149.Reachability.SGEdge (v i) (v j) := by
  rw [edgeG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

private theorem realize_sourceG' (v : Fin 3 → A) (i : Fin 3) :
    (sourceG i).Realize v ↔ Lax485149.Reachability.SGSource (v i) := by
  rw [sourceG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

private theorem realize_targetG' (v : Fin 3 → A) (i : Fin 3) :
    (targetG i).Realize v ↔ Lax485149.Reachability.SGTarget (v i) := by
  rw [targetG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

/-- What it means for an assignment to satisfy the Krom program: the guessed
set contains the marked targets, is closed under predecessors, and avoids the
marked sources. -/
theorem unreachKromProgram_holds_iff (ρ : uBlock.Assignment A) :
    unreachKromProgram.Holds ρ ↔
      (∀ x : A, Lax485149.Reachability.SGTarget x → URel ρ x) ∧
      (∀ x y : A, Lax485149.Reachability.SGEdge x y → URel ρ y → URel ρ x) ∧
      (∀ x : A, Lax485149.Reachability.SGSource x → ¬URel ρ x) := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x y hxy hy => ?_, fun x hx hu => ?_⟩
    · have hcl := h ![x, x, x] unreachK1 (by simp [unreachKromProgram])
      have := hcl ((realize_targetG' _ 0).mpr hx)
      simp only [unreachK1, Lax485149.KromFragment.KromLit.slotHolds, Option.elim_some, Option.elim_none,
        or_false] at this
      simpa using (uLit_holds ρ _ 0 true).mp this
    · have hcl := h ![x, y, x] unreachK2 (by simp [unreachKromProgram])
      have := hcl ((realize_edgeG' _ 0 1).mpr hxy)
      simp only [unreachK2, Lax485149.KromFragment.KromLit.slotHolds, Option.elim_some] at this
      rcases this with hneg | hpos
      · exact absurd (by simpa using hy) ((uLit_holds ρ _ 1 false).mp hneg)
      · simpa using (uLit_holds ρ _ 0 true).mp hpos
    · have hcl := h ![x, x, x] unreachK3 (by simp [unreachKromProgram])
      have := hcl ((realize_sourceG' _ 0).mpr hx)
      simp only [unreachK3, Lax485149.KromFragment.KromLit.slotHolds, Option.elim_some, Option.elim_none,
        or_false] at this
      exact (uLit_holds ρ _ 0 false).mp this (by simpa using hu)
  · rintro ⟨h1, h2, h3⟩ v c hc
    simp only [unreachKromProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · intro hg
      refine Or.inl ?_
      simp only [unreachK1, Lax485149.KromFragment.KromLit.slotHolds, Option.elim_some]
      exact (uLit_holds ρ _ 0 true).mpr (h1 _ ((realize_targetG' _ 0).mp hg))
    · intro hg
      by_cases hy : URel ρ (v 1)
      · refine Or.inr ?_
        simp only [unreachK2, Lax485149.KromFragment.KromLit.slotHolds, Option.elim_some]
        exact (uLit_holds ρ _ 0 true).mpr (h2 _ _ ((realize_edgeG' _ 0 1).mp hg) hy)
      · refine Or.inl ?_
        simp only [unreachK2, Lax485149.KromFragment.KromLit.slotHolds, Option.elim_some]
        exact (uLit_holds ρ _ 1 false).mpr hy
    · intro hg
      refine Or.inl ?_
      simp only [unreachK3, Lax485149.KromFragment.KromLit.slotHolds, Option.elim_some]
      exact (uLit_holds ρ _ 0 false).mpr (h3 _ ((realize_sourceG' _ 0).mp hg))

/-- The set of vertices from which a marked target is reachable: the witness
of the nontrivial direction. -/
def coReachAssign : uBlock.Assignment A :=
  fun _ w => ∃ t : A, Lax485149.Reachability.SGTarget t ∧ Relation.ReflTransGen Lax485149.Reachability.SGEdge (w ⟨0, Nat.zero_lt_one⟩) t

omit [LinearOrder A] in
@[simp]
theorem uRel_coReachAssign (x : A) :
    URel (coReachAssign (A := A)) x ↔ ∃ t : A, Lax485149.Reachability.SGTarget t ∧ Relation.ReflTransGen Lax485149.Reachability.SGEdge x t :=
  Iff.rfl

omit [LinearOrder A] in
/-- A set closed under predecessors and containing the marked targets contains
every vertex from which a marked target is reachable. -/
theorem uRel_of_reflTransGen {ρ : uBlock.Assignment A}
    (h2 : ∀ x y : A, Lax485149.Reachability.SGEdge x y → URel ρ y → URel ρ x) {x y : A}
    (h : Relation.ReflTransGen Lax485149.Reachability.SGEdge x y) : URel ρ y → URel ρ x := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hc => ih (h2 _ _ hbc hc)

end KromProgram

/-- **UNREACH is SO-Krom definable**: guess the set of vertices from which a
marked target is reachable. The clauses are two-literal – the closure rule is
`¬U(y) ∨ U(x)` – so no transitive closure has to be built, unlike in the Horn
program above. -/
theorem unreach_sigmaSOKromDefinable : Lax485149.KromFragment.SigmaSOKromDefinable UNREACH := by
  refine ⟨uBlock, 3, unreachKromProgram, ?_⟩
  intro A _ _ _ _
  constructor
  · intro h
    refine ⟨coReachAssign, (unreachKromProgram_holds_iff _).mpr
      ⟨fun x hx => ⟨x, hx, Relation.ReflTransGen.refl⟩, fun x y hxy hy => ?_, fun x hx hu => ?_⟩⟩
    · obtain ⟨t, ht, hpath⟩ := hy
      exact ⟨t, ht, Relation.ReflTransGen.head hxy hpath⟩
    · obtain ⟨t, ht, hpath⟩ := hu
      exact h ⟨x, t, hx, ht, hpath⟩
  · rintro ⟨ρ, hρ⟩ ⟨s, t, hs, ht, hpath⟩
    obtain ⟨h1, h2, h3⟩ := (unreachKromProgram_holds_iff ρ).mp hρ
    exact h3 s hs (uRel_of_reflTransGen h2 hpath (h1 t ht))

/-- **UNREACH is in NL**, by definition of the class as SO-Krom
definability. -/
theorem unreach_mem_NL : UNREACH ∈ NL :=
  unreach_sigmaSOKromDefinable

/-! ### REACH is FO(TC) definable

The canonical example of `DescriptiveComplexity.TCDefinable`, and the one the logic is
shaped after: REACH *is* a transitive closure, at arity one, of the edge
relation between the marked sources and the marked targets. Note the contrast
with the two clausal fragments above, which define the *complement* head-on:
here it is reachability itself that is stated, which is why closing FO(TC)
under complement (Immerman–Szelepcsényi) is what `REACH ∈ NL` waits on. -/

/-- The transition formula of the walk: an edge from the current vertex to the
next one. -/
noncomputable def tcEdgeF :
    (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 1 ⊕ Fin 1) :=
  Relations.formula₂ Lax485149Proofs.Foreign.FirstOrder.Language.sgEdgeO (Term.var (Sum.inl 0)) (Term.var (Sum.inr 0))

/-- The starting tuples of the walk: the marked sources. -/
noncomputable def tcSourceF : (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 1) :=
  Relations.formula₁ Lax485149Proofs.Foreign.FirstOrder.Language.sgSourceO (Term.var 0)

/-- The accepting tuples of the walk: the marked targets. -/
noncomputable def tcTargetF : (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 1) :=
  Relations.formula₁ Lax485149Proofs.Foreign.FirstOrder.Language.sgTargetO (Term.var 0)

/-- REACH as a single transitive closure: a walk along edges, from a marked
source to a marked target. -/
noncomputable abbrev reachSpec : Lax485149.TransitiveClosure.TCSpec Lax485149.Reachability.stGraph where
  Mode := Unit
  k := 1
  step := fun _ _ => tcEdgeF
  src := fun _ => tcSourceF
  tgt := fun _ => tcTargetF

section TCProgram

variable {A : Type} [Lax485149.Reachability.stGraph.Structure A] [LinearOrder A]

@[simp]
theorem step_reachSpec (a b : reachSpec.Node A) :
    reachSpec.Step a b ↔ Lax485149.Reachability.SGEdge (a.2 0) (b.2 0) := by
  change tcEdgeF.Realize (Sum.elim a.2 b.2) ↔ _
  rw [tcEdgeF, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_tcSourceF (v : Fin 1 → A) : tcSourceF.Realize v ↔ Lax485149.Reachability.SGSource (v 0) := by
  rw [tcSourceF, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_tcTargetF (v : Fin 1 → A) : tcTargetF.Realize v ↔ Lax485149.Reachability.SGTarget (v 0) := by
  rw [tcTargetF, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

/-- A path in the graph is a walk of the specification. -/
theorem reach_of_reflTransGen {x y : A} (h : Relation.ReflTransGen Lax485149.Reachability.SGEdge x y) :
    reachSpec.Reach ((), fun _ => x) ((), fun _ => y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    exact ih.tail ((step_reachSpec ((), fun _ => b) ((), fun _ => c)).mpr hbc)

/-- A walk of the specification is a path in the graph. -/
theorem reflTransGen_of_reach {u v : reachSpec.Node A} (h : reachSpec.Reach u v) :
    Relation.ReflTransGen Lax485149.Reachability.SGEdge (u.2 0) (v.2 0) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail ((step_reachSpec b c).mp hbc)

end TCProgram

/-- **REACH is FO(TC) definable**: it is a single transitive closure of the
edge relation, at arity one. -/
theorem reach_tcDefinable : Lax485149.TransitiveClosure.TCDefinable REACH := by
  refine ⟨reachSpec, ?_⟩
  intro A _ _ _ _
  constructor
  · rintro ⟨s, t, hs, ht, hpath⟩
    exact ⟨((), fun _ => s), ((), fun _ => t), (realize_tcSourceF _).mpr hs,
      (realize_tcTargetF _).mpr ht, reach_of_reflTransGen hpath⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨u.2 0, v.2 0, (realize_tcSourceF u.2).mp hu, (realize_tcTargetF v.2).mp hv,
      reflTransGen_of_reach huv⟩

end Lax485149Proofs.DescriptiveComplexity


