/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.OccurrenceOrder
import Lax604544Proofs.DescriptiveComplexity.Ordered
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
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax904597.Sat
end Lax904597.Sat

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax604544Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl NegIn OccIn PosIn)
end Lax604544Proofs.DescriptiveComplexity.SatOcc

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

namespace Lax604544Proofs.DescriptiveComplexity

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

/-- `x = y`, as a formula. -/
def eqF (x y : α) : satOrd.Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- The literal `(x, s)` occurs in the clause `c`, as a formula. -/
def occF (s : Bool) (c x : α) : satOrd.Formula α :=
  clF c ⊓ if s then posF c x else negF c x

/-- `c` is an empty clause, as a formula. -/
noncomputable def emptyClF (c : α) : satOrd.Formula α :=
  clF c ⊓ ∼((occF false (.inl c) (.inr ()) ⊔ occF true (.inl c) (.inr ())).iExs Unit)

end Builders

/-! ### Realization lemmas -/

section Realize

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

@[simp]
theorem realize_clF {c : α} : (clF c).Realize v ↔ Lax799700.Common.SatOcc.IsCl (v c) := by
  rw [clF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_posF {c x : α} : (posF c x).Realize v ↔ Lax799700.Common.SatOcc.PosIn (v c) (v x) := by
  rw [posF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_negF {c x : α} : (negF c x).Realize v ↔ Lax799700.Common.SatOcc.NegIn (v c) (v x) := by
  rw [negF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]

@[simp]
theorem realize_occF {s : Bool} {c x : α} :
    (occF s c x).Realize v ↔ Lax799700.Common.SatOcc.OccIn (v c) (v x) s := by
  cases s <;> simp [occF, Lax799700.Common.SatOcc.OccIn]

@[simp]
theorem realize_emptyClF {c : α} : (emptyClF c).Realize v ↔ EmptyCl (v c) := by
  simp only [emptyClF, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    Formula.realize_sup, realize_clF, realize_occF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x s hxs => h2 ?_⟩
    cases s
    exacts [⟨fun _ => x, Or.inl hxs⟩, ⟨fun _ => x, Or.inr hxs⟩]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨i, h | h⟩
    exacts [h2 (i ()) false h, h2 (i ()) true h]

end Realize

end SatOcc

end Lax604544Proofs.DescriptiveComplexity


