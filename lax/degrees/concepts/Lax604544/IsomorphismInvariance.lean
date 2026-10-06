import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.Classes
import Lax904597.Sat
import Lax799700.SubgraphIso
import Lax485149.Problems
import Lax485149.TwoSat
import Lax485149.ClassNL
import Lax535992.HornSat
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.Tautology
import Lax624099.ClassRE
import Lax624099.FiniteSatisfiability
import Lax604544.Degrees
import Lax604544.RelationIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.DagIsomorphism

/-!
---
title: Invariance and characterization of the isomorphism problems
type: lemma
---
Having isomorphic marked graphs, having isomorphic simple marked graphs and
having isomorphic acyclic marked graphs with valid witnesses are invariant
under isomorphism of instances, and an instance is a yes-instance of
Digraph Isomorphism, Graph Isomorphism or DAG Isomorphism exactly when it
has the corresponding property.
-/

namespace Lax604544.IsomorphismInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Sat Lax799700.SubgraphIso
open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability
open Lax604544.Degrees Lax604544.RelationIsomorphism
open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

/-- Having isomorphic marked graphs is isomorphism-invariant. -/
axiom hasDigraphIso_iso : ∀ {A B : Type} [twoGraphs.Structure A] [twoGraphs.Structure B],
  (A ≃[twoGraphs] B) → (HasDigraphIso A ↔ HasDigraphIso B)

/-- The yes-instances are exactly the instances with the defining property. -/
axiom digraphIso_iff : ∀ (A : Type) [twoGraphs.Structure A], DigraphIso A ↔ HasDigraphIso A

/-- Having isomorphic simple marked graphs is isomorphism-invariant. -/
axiom hasGraphIso_iso : ∀ {A B : Type} [twoGraphs.Structure A] [twoGraphs.Structure B],
  (A ≃[twoGraphs] B) → (HasGraphIso A ↔ HasGraphIso B)

/-- The yes-instances are exactly the instances with the defining property. -/
axiom graphIso_iff : ∀ (A : Type) [twoGraphs.Structure A], GraphIso A ↔ HasGraphIso A

/-- Having isomorphic marked acyclic graphs is isomorphism-invariant. -/
axiom hasDagIso_iso : ∀ {A B : Type} [twoDags.Structure A] [twoDags.Structure B],
  (A ≃[twoDags] B) → (HasDagIso A ↔ HasDagIso B)

/-- The yes-instances are exactly the instances with the defining property. -/
axiom dagIso_iff : ∀ (A : Type) [twoDags.Structure A], DagIso A ↔ HasDagIso A

end Lax604544.IsomorphismInvariance
