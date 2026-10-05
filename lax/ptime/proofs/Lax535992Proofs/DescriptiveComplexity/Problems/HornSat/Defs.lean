/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax535992Proofs.DescriptiveComplexity.Problems.Sat
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992.HornSat
end Lax535992.HornSat

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax535992Proofs.DescriptiveComplexity
export Lax535992.HornSat (AtMostOnePositive HornSatisfiable)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Sat (Satisfiable)
end Lax535992Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satPosIn)
end FirstOrder.Language

/-!
# HORN-SAT: definition

The problem HORN-SAT, over the same vocabulary `FirstOrder.Language.sat` as SAT:
a CNF structure is a yes-instance iff every clause contains at most one
positive literal (`DescriptiveComplexity.AtMostOnePositive`) *and* the CNF is
satisfiable (`DescriptiveComplexity.HornSatisfiable`, bundled as
`DescriptiveComplexity.HORNSAT`).

Folding the Horn condition into the yes-instances rather than into the
vocabulary is the same choice as for 3SAT and its width bound
(`DescriptiveComplexity.WidthAtMostThree`): it keeps HORN-SAT a decision problem on
arbitrary `Language.sat`-structures, so that it lives in the same catalog and
composes with the same reductions.

Horn formulas are the tractable case of propositional satisfiability – a
satisfiable Horn formula has a *least* model, computed by unit propagation in
linear time ([Dowling & Gallier 1984][dowling1984linear]) – and HORN-SAT is the
canonical complete problem for polynomial time. The corresponding hardness
statement, machine-free and one level below the Cook–Levin discharge, is in
`DescriptiveComplexity.Problems.HornSat.Hardness`.
-/

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section HornSat

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end HornSat

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

variable {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]

private theorem atMostOnePositive_of_iso (e : A ≃[Lax904597.Sat.sat] B)
    (h : Lax535992.HornSat.AtMostOnePositive A) : Lax535992.HornSat.AtMostOnePositive B := by
  intro c x y hc hx hy
  have hx' := (relMap_equiv₂ e Lax904597.Sat.satPosIn (e.symm c) (e.symm x)).mpr (by simpa using hx)
  have hy' := (relMap_equiv₂ e Lax904597.Sat.satPosIn (e.symm c) (e.symm y)).mpr (by simpa using hy)
  have := h (e.symm c) (e.symm x) (e.symm y)
    ((relMap_equiv₁ e.symm Lax904597.Sat.satIsClause c).mp hc) hx' hy'
  simpa using congrArg e this

/-- Horn satisfiability is isomorphism-invariant. -/
theorem hornSatisfiable_iso (e : A ≃[Lax904597.Sat.sat] B) :
    Lax535992.HornSat.HornSatisfiable A ↔ Lax535992.HornSat.HornSatisfiable B :=
  and_congr ⟨atMostOnePositive_of_iso e, atMostOnePositive_of_iso e.symm⟩
    (satisfiable_iso e)

end Iso

/-- HORN-SAT, as a problem on `Language.sat`-structures: the same vocabulary as
SAT, with the Horn condition folded into the yes-instances. -/
def HORNSAT : Lax904597.Problems.DecisionProblem Lax904597.Sat.sat where
  Holds := fun A inst => @Lax535992.HornSat.HornSatisfiable A inst
  iso_invariant := fun e => hornSatisfiable_iso e

end Lax535992Proofs.DescriptiveComplexity


