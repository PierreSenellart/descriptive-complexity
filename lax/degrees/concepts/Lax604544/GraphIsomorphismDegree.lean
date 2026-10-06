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
title: Digraph, DAG and graph isomorphism are GI-complete
type: theorem
---
Graph Isomorphism is GI-complete, being complete for its own degree, and so
are Digraph Isomorphism and DAG Isomorphism: the three problems reduce to
one another by first-order reductions, and GI is also the degree of Digraph
Isomorphism. A directed graph becomes a simple graph by subdividing every
arc three times and attaching a pendant that carries its direction; a
directed graph becomes an acyclic one by subdividing every arc twice, the
direction surviving as the difference of the two levels. In the other
direction simplicity and the validity of the acyclicity witnesses are
first-order, so a reduction only tests them. These are problems complete
for a class defined by no logic, and conjectured to be neither in PTIME nor
NP-complete.
-/

namespace Lax604544.GraphIsomorphismDegree

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Sat Lax799700.SubgraphIso
open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability
open Lax604544.Degrees Lax604544.RelationIsomorphism
open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

/-- Graph Isomorphism is GI-complete. -/
axiom graphIso_GI_complete : GI.Complete GraphIso

/-- Digraph Isomorphism is GI-complete. -/
axiom digraphIso_GI_complete : GI.Complete DigraphIso

/-- DAG Isomorphism is GI-complete. -/
axiom dagIso_GI_complete : GI.Complete DagIso

/-- GI is also the degree of Digraph Isomorphism. -/
axiom GI_eq_below_digraphIso : GI = below DigraphIso

end Lax604544.GraphIsomorphismDegree
