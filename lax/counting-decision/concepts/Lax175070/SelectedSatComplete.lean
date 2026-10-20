import Lax904597.Problems
import Lax485149.Problems
import Lax485149.Complement
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Interpretations
import Lax904597.Machines
import Lax564036.Hierarchy
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax366625.CountingRuns
import Lax175070.CountDefinability
import Lax175070.SelectedSat

/-!
---
title: SelMajSAT is PP-complete and SelEqSAT is C₌P-complete
type: theorem
---
SelMajSAT is PP-complete and SelEqSAT is C$_=$P-complete. Membership
compares the two counts of #SelSAT, both in #P. Hardness pairs the two
kernels of a problem of the class into one Tseitin formula, with the
selected variable choosing the kernel, so that the two counts of the formula
are those of the problem.
-/

namespace Lax175070.SelectedSatComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Sat Lax904597.Interpretations
    Lax904597.Machines Lax564036.Hierarchy
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax366625.CountingRuns Lax175070.CountDefinability Lax175070.SelectedSat Lax485149.Problems
open Lax485149.Complement

/-- SelMajSAT is PP-complete. -/
axiom selMajSat_PP_complete :
  PP.Complete SelMajSAT

/-- SelEqSAT is C₌P-complete. -/
axiom selEqSat_CeqP_complete :
  CeqP.Complete SelEqSAT

end Lax175070.SelectedSatComplete
