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
title: The classes with a complete problem are degrees
type: theorem
---
Each logically defined class with a complete problem is the degree of that
problem: NP is the degree of SAT, coNP of TAUT, PTIME of HORN-SAT, NL of
2SAT and RE of FINSAT. Every member of the class reduces to the problem by
an ordered first-order reduction, the generic reduction that reads a
definition, and the class is closed under such reductions. Hardness for a
complete problem is therefore hardness for the class: SAT-hardness is
NP-hardness.
-/

namespace Lax604544.ClassesAsDegrees

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Sat Lax799700.SubgraphIso
open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability
open Lax604544.Degrees Lax604544.RelationIsomorphism
open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

/-- NP is the degree of SAT. -/
axiom NP_eq_below_sat : NP = below SAT

/-- coNP is the degree of TAUT. -/
axiom coNP_eq_below_taut : coNP = below TAUT

/-- PTIME is the degree of HORN-SAT. -/
axiom PTIME_eq_below_hornSat : PTIME = below HORNSAT

/-- NL is the degree of 2SAT. -/
axiom NL_eq_below_twoSat : NL = below TwoSAT

/-- RE is the degree of FINSAT. -/
axiom RE_eq_below_finsat : RE = below FINSAT

end Lax604544.ClassesAsDegrees
