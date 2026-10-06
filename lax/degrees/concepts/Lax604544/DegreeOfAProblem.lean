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
title: Completeness for a degree is mutual reducibility
type: theorem
---
Every problem $Q_0$ is complete for its own degree. A problem $P$ is
complete for the degree of $Q_0$ if and only if $P$ reduces to $Q_0$ by an
ordered first-order reduction and $Q_0$ reduces to $P$ by a relativized
ordered first-order reduction. And two problems that reduce to each other
by ordered first-order reductions have the same degree.
-/

namespace Lax604544.DegreeOfAProblem

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Sat Lax799700.SubgraphIso
open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability
open Lax604544.Degrees Lax604544.RelationIsomorphism
open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

/-- A problem is complete for its own degree. -/
axiom below_complete_self : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q₀ : DecisionProblem L₀),
  (below Q₀).Complete Q₀

/-- Completeness for the degree of `Q₀` is mutual reducibility with `Q₀`. -/
axiom complete_below_iff :
  ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] {L : Language.{0, 0}} [L.IsRelational]
    {Q₀ : DecisionProblem L₀} (P : DecisionProblem L),
  (below Q₀).Complete P ↔
    Nonempty (OrderedFOReduction P Q₀) ∧ Nonempty (RelOrderedFOReduction Q₀ P)

/-- Mutually reducible problems have the same degree. -/
axiom below_congr :
  ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] {L₁ : Language.{0, 0}} [L₁.IsRelational]
  {Q₀ : DecisionProblem L₀} {Q₁ : DecisionProblem L₁},
  Nonempty (OrderedFOReduction Q₀ Q₁) → Nonempty (OrderedFOReduction Q₁ Q₀) → below Q₀ = below Q₁

end Lax604544.DegreeOfAProblem
