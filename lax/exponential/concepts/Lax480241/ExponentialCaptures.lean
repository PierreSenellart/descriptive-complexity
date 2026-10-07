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
title: EXPTIME and EXPSPACE as PTIME and PSPACE read exponentially
type: theorem
---
EXPTIME is PTIME one exponential up and EXPSPACE is PSPACE one exponential
up: these are the capture theorems FO(≤, LFP) = PTIME and FO(≤, PFP) =
PSPACE read on the expanded universe. The order that the expansion's
sentences read can be removed from both definitions, the expansion guessing
it into its block.
-/

namespace Lax480241.ExponentialCaptures

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax485149.Complement Lax485149.ClassNL
open Lax535992.ClassPTIME Lax564036.Hierarchy Lax564036.AlternatingMachines Lax134656.ClassPSPACE
open Lax480241.Expansions Lax480241.SecondOrderFixedPoints Lax480241.AlternatingSpace
    Lax480241.ExponentialClasses

/-- EXPTIME is PTIME one exponential up. -/
axiom EXPTIME_eq_PTIME_exp :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    EXPTIME.Mem P ↔ (expClass PTIME).Mem P

/-- EXPSPACE is PSPACE one exponential up. -/
axiom EXPSPACE_eq_PSPACE_exp :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    EXPSPACE.Mem P ↔ (expClass PSPACE).Mem P

/-- EXPTIME without the order. -/
axiom mem_EXPTIME_iff_solfpDefinableFree :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    EXPTIME.Mem P ↔ SOLFPDefinableFree P

/-- EXPSPACE without the order. -/
axiom mem_EXPSPACE_iff_sopfpDefinableFree :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    EXPSPACE.Mem P ↔ SOPFPDefinableFree P

end Lax480241.ExponentialCaptures
