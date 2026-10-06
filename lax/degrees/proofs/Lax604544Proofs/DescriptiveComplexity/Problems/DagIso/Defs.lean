/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.Vocabulary
import Lax604544Proofs.DescriptiveComplexity.Problems.DigraphIso
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Lax604544Proofs.DescriptiveComplexity.Interpretation
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
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
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

namespace Lax604544.DagIsomorphism
end Lax604544.DagIsomorphism

namespace Lax604544.RelationIsomorphism
end Lax604544.RelationIsomorphism

namespace Lax604544Proofs.DescriptiveComplexity.TopoOn
end Lax604544Proofs.DescriptiveComplexity.TopoOn

namespace Lax799700.Feedback
end Lax799700.Feedback

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.RelationIsomorphism (RelIsoOn)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.DagIsomorphism (HasDagIso TDHostArc TDHostLt TDHostV TDPatArc TDPatLt TDPatV TopoOn)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax799700.Feedback (AcyclicRel)
end Lax604544Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax604544.DagIsomorphism (tdHostArc tdHostLt tdHostV tdPatArc tdPatLt tdPatV twoDags)
end FirstOrder.Language

/-!
# DAG Isomorphism: vocabulary and semantics

DAG ISOMORPHISM: are the two directed acyclic graphs of the instance
isomorphic? This file fixes the vocabulary and the yes-instance predicate; the
two halves of GI-completeness live in
`DescriptiveComplexity.Problems.DagIso.ToDigraphIso` and
`DescriptiveComplexity.Problems.DagIso.FromDigraphIso`.

## Why the instances carry a topological order

Acyclicity is **not first-order definable**, so a problem whose yes-instances
are “both sides acyclic *and* isomorphic” could not be reduced back to
`DescriptiveComplexity.DigraphIso`: the reduction would have to decide acyclicity
first-order, and no first-order interpretation can (a directed cycle is a
reachability question). A classical polynomial-time reduction simply tests
acyclicity and maps a cyclic instance to a fixed no-instance; an FO reduction,
computable in AC⁰, cannot.

The instances therefore *carry* their acyclicity witness: besides the two arc
relations, each side has a relation asked to be a strict partial order
containing its arcs (`DescriptiveComplexity.TopoOn`) – a topological order of
the DAG, in the partial-order form, which is exactly what
`DescriptiveComplexity.acyclicRel_iff_exists_order` certifies acyclicity by.
Being a strict partial order containing the arcs is first-order, so a reduction
*can* test it, and the well-formed instances are precisely the pairs of DAGs
(`DescriptiveComplexity.acyclicOn_iff_exists_topoOn`: a finite relation admits
such a witness exactly when it is acyclic). The witness is data of the
instance, not of the problem: the isomorphism asked for by
`DescriptiveComplexity.HasDagIso` relates the *arcs* only and may ignore the two
orders entirely, so this is DAG isomorphism and not isomorphism of ordered
DAGs.

This is the same “junk is ignorable” discipline as everywhere in the catalog,
one level up: elements outside both marks are junk, and instances whose order
relation is not a witness are no-instances.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The acyclicity witness -/

section Topo

variable {A : Type}

variable {B : Type}

/-- `TopoOn` transports along an equivalence commuting with the three
predicates. -/
theorem TopoOn.of_equiv (u : B ≃ A) {VB : B → Prop} {LtB ArcB : B → B → Prop}
    {VA : A → Prop} {LtA ArcA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hLt : ∀ b b', LtB b b' ↔ LtA (u b) (u b'))
    (hArc : ∀ b b', ArcB b b' ↔ ArcA (u b) (u b'))
    (h : Lax604544.DagIsomorphism.TopoOn VB LtB ArcB) : Lax604544.DagIsomorphism.TopoOn VA LtA ArcA := by
  obtain ⟨hirr, htrans, hmono⟩ := h
  refine ⟨fun x hx hlt => ?_, fun x y z hx hy hz h₁ h₂ => ?_, fun x y hx hy harc => ?_⟩
  · exact hirr (u.symm x) ((hV _).mpr (by simpa using hx)) ((hLt _ _).mpr (by simpa using hlt))
  · have := htrans (u.symm x) (u.symm y) (u.symm z) ((hV _).mpr (by simpa using hx))
      ((hV _).mpr (by simpa using hy)) ((hV _).mpr (by simpa using hz))
      ((hLt _ _).mpr (by simpa using h₁)) ((hLt _ _).mpr (by simpa using h₂))
    simpa using (hLt (u.symm x) (u.symm z)).mp this
  · have := hmono (u.symm x) (u.symm y) ((hV _).mpr (by simpa using hx))
      ((hV _).mpr (by simpa using hy)) ((hArc _ _).mpr (by simpa using harc))
    simpa using (hLt (u.symm x) (u.symm y)).mp this

end Topo

end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544.DagIsomorphism.TopoOn

export Lax604544Proofs.DescriptiveComplexity.TopoOn (of_equiv)

end Lax604544.DagIsomorphism.TopoOn

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Topo

variable {A : Type}

variable {B : Type}

/-- `TopoOn` transports along an equivalence, iff version. -/
theorem TopoOn.equiv_iff (u : B ≃ A) {VB : B → Prop} {LtB ArcB : B → B → Prop}
    {VA : A → Prop} {LtA ArcA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hLt : ∀ b b', LtB b b' ↔ LtA (u b) (u b'))
    (hArc : ∀ b b', ArcB b b' ↔ ArcA (u b) (u b')) :
    Lax604544.DagIsomorphism.TopoOn VB LtB ArcB ↔ Lax604544.DagIsomorphism.TopoOn VA LtA ArcA :=
  ⟨TopoOn.of_equiv u hV hLt hArc,
    TopoOn.of_equiv u.symm (fun a => by rw [hV]; simp) (fun a a' => by rw [hLt]; simp)
      fun a a' => by rw [hArc]; simp⟩

end Topo

end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544.DagIsomorphism.TopoOn

export Lax604544Proofs.DescriptiveComplexity.TopoOn (equiv_iff)

end Lax604544.DagIsomorphism.TopoOn

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Topo

variable {A : Type}

variable {B : Type}

end Topo

/-! ### The problem -/

section Shorthands

variable {A : Type} [Lax604544.DagIsomorphism.twoDags.Structure A]

end Shorthands

section Problem

variable (A : Type) [Lax604544.DagIsomorphism.twoDags.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax604544.DagIsomorphism.twoDags.Structure A] [Lax604544.DagIsomorphism.twoDags.Structure B]

/-- The DAG-isomorphism property is isomorphism-invariant. -/
theorem hasDagIso_iso (e : A ≃[Lax604544.DagIsomorphism.twoDags] B) :
    Lax604544.DagIsomorphism.HasDagIso A ↔ Lax604544.DagIsomorphism.HasDagIso B :=
  and_congr e.toEquiv.finite_iff
    (and_congr
      (TopoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e Lax604544.DagIsomorphism.tdPatV a)
        (fun a b => relMap_equiv₂ e Lax604544.DagIsomorphism.tdPatLt a b) fun a b => relMap_equiv₂ e Lax604544.DagIsomorphism.tdPatArc a b)
      (and_congr
        (TopoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e Lax604544.DagIsomorphism.tdHostV a)
          (fun a b => relMap_equiv₂ e Lax604544.DagIsomorphism.tdHostLt a b) fun a b => relMap_equiv₂ e Lax604544.DagIsomorphism.tdHostArc a b)
        (RelIsoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e Lax604544.DagIsomorphism.tdPatV a)
          (fun a => relMap_equiv₁ e Lax604544.DagIsomorphism.tdHostV a) (fun a b => relMap_equiv₂ e Lax604544.DagIsomorphism.tdPatArc a b)
          fun a b => relMap_equiv₂ e Lax604544.DagIsomorphism.tdHostArc a b)))

end Iso

/-- DAG ISOMORPHISM, as a problem on two-DAG structures: are the two marked
DAGs isomorphic? Well-formedness – each side's order relation being a
topological order of its arcs – is part of the yes-condition, and is
first-order, unlike acyclicity itself. -/
def DagIso : Lax904597.Problems.DecisionProblem Lax604544.DagIsomorphism.twoDags where
  Holds := fun A inst => @Lax604544.DagIsomorphism.HasDagIso A inst
  iso_invariant := fun e => hasDagIso_iso e

end Lax604544Proofs.DescriptiveComplexity


