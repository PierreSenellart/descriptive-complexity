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
title: EXPTIME = coEXPTIME and EXPSPACE = coEXPSPACE
type: theorem
---
EXPTIME and EXPSPACE are closed under complement: complementation commutes
with reading a class one exponential up, and PTIME and PSPACE are closed
under complement.
-/

namespace Lax480241.ExponentialComplements

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax485149.Complement Lax485149.ClassNL
open Lax535992.ClassPTIME Lax564036.Hierarchy Lax564036.AlternatingMachines Lax134656.ClassPSPACE
open Lax480241.Expansions Lax480241.SecondOrderFixedPoints Lax480241.AlternatingSpace
    Lax480241.ExponentialClasses

/-- EXPTIME is closed under complement. -/
axiom mem_EXPTIME_compl_iff :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    EXPTIME.Mem (DecisionProblem.compl P) ↔ EXPTIME.Mem P

/-- EXPSPACE is closed under complement. -/
axiom mem_EXPSPACE_compl_iff :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    EXPSPACE.Mem (DecisionProblem.compl P) ↔ EXPSPACE.Mem P

/-- coEXPTIME is EXPTIME. -/
axiom mem_coEXPTIME_iff :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    coEXPTIME.Mem P ↔ EXPTIME.Mem P

/-- coEXPSPACE is EXPSPACE. -/
axiom mem_coEXPSPACE_iff :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    coEXPSPACE.Mem P ↔ EXPSPACE.Mem P

end Lax480241.ExponentialComplements
