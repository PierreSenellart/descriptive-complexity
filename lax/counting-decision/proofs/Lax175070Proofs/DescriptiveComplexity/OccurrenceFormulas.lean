/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.OccurrenceOrder
import Lax175070Proofs.DescriptiveComplexity.Ordered
import Lax175070.CountDefinability
import Lax175070.SelectedSat
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149.TwoSat.SatOcc
end Lax485149.TwoSat.SatOcc

namespace Lax904597.Sat
end Lax904597.Sat

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax175070Proofs.DescriptiveComplexity.SatOcc
export Lax485149.TwoSat.SatOcc (IsCl NegIn OccIn PosIn)
end Lax175070Proofs.DescriptiveComplexity.SatOcc

/-!
# First-order formulas for literal occurrences, over the ordered expansion

First-order counterpart of `DescriptiveComplexity.OccurrenceOrder`, shared by the
reductions *from* SAT (to 3-colorability, to 3SAT…): parameterized formula
builders over the ordered expansion `Language.sat.sum Language.order`
(`DescriptiveComplexity.SatOcc.satOrd`) mirroring the semantic predicates on literal
occurrences – `occF` for `OccIn`, `minOccF`/`maxOccF` for `MinOcc`/`MaxOcc`,
`succOccF` for `SuccOcc`, `chainedF` for `Chained`, `emptyClF` for `EmptyCl`,
… – together with their realization lemmas (`realize_occF`…).

All builders are parameterized by the indices of their free variables, so that
they can be instantiated at any variable type (in particular under
quantifiers). Occurrence *signs* are static (Lean-level) `Bool` parameters:
a quantification over signs becomes a finite conjunction or disjunction of
formulas.
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

/-- The ordered expansion of the language of CNF instances. -/
abbrev satOrd : Language := Lax904597.Sat.sat.sum Language.order

/-- The symbol for “is a clause” in the ordered expansion. -/
abbrev clSym : satOrd.Relations 1 := Sum.inl Lax904597.Sat.satIsClause

/-- The symbol for “occurs positively in” in the ordered expansion. -/
abbrev posSym : satOrd.Relations 2 := Sum.inl Lax904597.Sat.satPosIn

/-- The symbol for “occurs negatively in” in the ordered expansion. -/
abbrev negSym : satOrd.Relations 2 := Sum.inl Lax904597.Sat.satNegIn

/-! ### Formula builders -/

section Builders

variable {α : Type}

/-- `c` is a clause, as a formula. -/
def clF (c : α) : satOrd.Formula α :=
  Relations.formula₁ clSym (Term.var c)

/-- `x` occurs positively in `c`, as a formula. -/
def posF (c x : α) : satOrd.Formula α :=
  Relations.formula₂ posSym (Term.var c) (Term.var x)

/-- `x` occurs negatively in `c`, as a formula. -/
def negF (c x : α) : satOrd.Formula α :=
  Relations.formula₂ negSym (Term.var c) (Term.var x)

/-- `x ≤ y`, as a formula. -/
def leF (x y : α) : satOrd.Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x = y`, as a formula. -/
def eqF (x y : α) : satOrd.Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- `x < y`, as a formula. -/
def ltF (x y : α) : satOrd.Formula α :=
  leF x y ⊓ ∼(eqF x y)

end Builders

/-! ### Realization lemmas -/

section Realize

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

@[simp]
theorem realize_clF {c : α} : (clF c).Realize v ↔ Lax485149.TwoSat.SatOcc.IsCl (v c) := by
  rw [clF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_posF {c x : α} : (posF c x).Realize v ↔ Lax485149.TwoSat.SatOcc.PosIn (v c) (v x) := by
  rw [posF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_negF {c x : α} : (negF c x).Realize v ↔ Lax485149.TwoSat.SatOcc.NegIn (v c) (v x) := by
  rw [negF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_leF {x y : α} : (leF x y).Realize v ↔ v x ≤ v y := by
  simp [leF, Formula.realize_rel₂]

@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]

@[simp]
theorem realize_ltF {x y : α} : (ltF x y).Realize v ↔ v x < v y := by
  simp [ltF, lt_iff_le_and_ne]

end Realize

end SatOcc

end Lax175070Proofs.DescriptiveComplexity


