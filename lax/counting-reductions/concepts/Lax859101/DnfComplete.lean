import Lax904597.Problems
import Lax904597.Sat
import Mathlib.ModelTheory.Graph
import Lax799700.SetFamily
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite

/-!
---
title: #DNF is #P-complete, by one call and by subtraction
type: theorem
---
#SAT reduces to #DNF by a subtraction: the models of a CNF formula are the
assignments of its variables, $2^n$ of them, minus the models of the DNF
formula of its negation, as Durand, Hermann, and Kolaitis showed and as
Durand, Haak, Kontinen, and Vollmer used for #AC$^0$. Hence #DNF is
#P-complete under subtractive reductions, and one-call #P-complete, although
its support, the satisfiability of a DNF formula, is easy.
-/

namespace Lax859101.DnfComplete

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- #SAT reduces to #DNF by a subtractive reduction. -/
axiom sharpSat_subtractive_sharpDnf :
  SubtractiveReducible SharpSAT SharpDNF

/-- #DNF is #P-complete under subtractive reductions. -/
axiom sharpDnf_sharpP_complete :
  SubtractiveComplete SharpP SharpDNF

/-- #DNF is one-call #P-complete. -/
axiom sharpDnf_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpDNF

end Lax859101.DnfComplete
