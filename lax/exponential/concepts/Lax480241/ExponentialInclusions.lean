import Lax904597.Problems
import Lax904597.Classes
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.ClassNL
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.AlternatingMachines
import Lax134656.ClassPSPACE
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax480241.AlternatingSpace
import Lax480241.ExponentialClasses

/-!
---
title: Inclusions between the polynomial and exponential classes
type: theorem
---
PTIME ⊆ PSPACE ⊆ EXPTIME ⊆ NEXPTIME ⊆ EXPSPACE, with NP ⊆ NEXPTIME, PSPACE ⊆
EXPSPACE, PH ⊆ EXPTIME, and NL$^{\exp}$ ⊆ EXPTIME. The inclusions one
exponential up are those below carried by the exponential of classes; PSPACE
⊆ EXPTIME reads the configurations of a space-bounded computation as the
points of an expansion.
-/

namespace Lax480241.ExponentialInclusions

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax485149.Complement Lax485149.ClassNL
open Lax535992.ClassPTIME Lax564036.Hierarchy Lax564036.AlternatingMachines Lax134656.ClassPSPACE
open Lax480241.Expansions Lax480241.SecondOrderFixedPoints Lax480241.AlternatingSpace
    Lax480241.ExponentialClasses

/-- PSPACE ⊆ EXPTIME. -/
axiom PSPACE_subset_EXPTIME :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    PSPACE.Mem P → EXPTIME.Mem P

/-- EXPTIME ⊆ NEXPTIME. -/
axiom EXPTIME_subset_NEXPTIME :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    EXPTIME.Mem P → NEXPTIME.Mem P

/-- NEXPTIME ⊆ EXPSPACE. -/
axiom NEXPTIME_subset_EXPSPACE :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    NEXPTIME.Mem P → EXPSPACE.Mem P

/-- EXPTIME ⊆ EXPSPACE. -/
axiom EXPTIME_subset_EXPSPACE :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    EXPTIME.Mem P → EXPSPACE.Mem P

/-- PTIME ⊆ EXPTIME. -/
axiom PTIME_subset_EXPTIME :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    PTIME.Mem P → EXPTIME.Mem P

/-- NP ⊆ NEXPTIME. -/
axiom NP_subset_NEXPTIME :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    NP.Mem P → NEXPTIME.Mem P

/-- PSPACE ⊆ EXPSPACE. -/
axiom PSPACE_subset_EXPSPACE :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    PSPACE.Mem P → EXPSPACE.Mem P

/-- PH ⊆ EXPTIME. -/
axiom PH_subset_EXPTIME :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    PH.Mem P → EXPTIME.Mem P

/-- NL one exponential up is in EXPTIME. -/
axiom NL_exp_subset_EXPTIME :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    (expClass NL).Mem P → EXPTIME.Mem P

end Lax480241.ExponentialInclusions
