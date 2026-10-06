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
title: The isomorphism problems are in NP
type: theorem
---
Digraph Isomorphism, Graph Isomorphism, and DAG Isomorphism are in NP, by an
existential second-order sentence guessing the bijection, with no order and
no counting; and every problem of GI is in NP.
-/

namespace Lax604544.IsomorphismInNP

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Sat Lax799700.SubgraphIso
open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability
open Lax604544.Degrees Lax604544.RelationIsomorphism
open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

/-- Digraph Isomorphism is in NP. -/
axiom digraphIso_mem_NP : NP.Mem DigraphIso

/-- Graph Isomorphism is in NP. -/
axiom graphIso_mem_NP : NP.Mem GraphIso

/-- DAG Isomorphism is in NP. -/
axiom dagIso_mem_NP : NP.Mem DagIso

/-- GI is contained in NP. -/
axiom GI_subset_NP : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  GI.Mem P → NP.Mem P

end Lax604544.IsomorphismInNP
