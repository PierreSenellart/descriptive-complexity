/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.Problems.Sat.Hardness
import FOReduction.Problems.ThreeSat.ToSat
import FOReduction.Problems.ThreeSat.FromSat

/-!
# 3SAT is NP-complete

Umbrella file for the problem 3SAT (`FirstOrder.ThreeSAT`, defined in
`FOReduction.Problems.ThreeSat.Defs`), collecting its two first-order
reductions —

* `FirstOrder.threeSat_fo_reduction_sat : ThreeSAT ≤ᶠᵒ SAT` (order-free,
  identity-like, gated on the first-order width check;
  `FOReduction.Problems.ThreeSat.ToSat`), and
* `FirstOrder.sat_ordered_fo_reduction_threeSat : SAT ≤ᶠᵒ[≤] ThreeSAT`
  (ordered, clause splitting along the occurrence order;
  `FOReduction.Problems.ThreeSat.FromSat`) —

and deriving its NP-completeness from the Cook–Levin axiom
(`FirstOrder.SAT_NP_complete`), with no machine model anywhere. As with any
complexity-theoretic statement, these results are about finite CNF structures
only (`ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace FirstOrder

/-- 3SAT is in NP: it FO-reduces to SAT, which is in NP. -/
theorem threeSat_mem_NP : ThreeSAT ∈ NP :=
  NP.mem_of_foReduction threeSat_fo_reduction_sat sat_mem_NP

/-- 3SAT is NP-hard: SAT, which is NP-hard, reduces to it by an ordered FO
reduction. -/
theorem threeSat_NP_hard : NP.Hard ThreeSAT :=
  NP.hard_of_orderedReduction sat_ordered_fo_reduction_threeSat sat_NP_hard

/-- **3SAT is NP-complete**, derived from the two first-order reductions of
this library and the Cook–Levin axiom. -/
theorem threeSat_NP_complete : NP.Complete ThreeSAT :=
  ⟨threeSat_mem_NP, threeSat_NP_hard⟩

end FirstOrder
