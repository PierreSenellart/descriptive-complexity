/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.OrdFormula
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (replicate replicateAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Extending an expansion with its own order

`DescriptiveComplexity.ExpExpansion.ordExtend` adds the order symbol to the
expanded vocabulary, defined by the sentence of
`DescriptiveComplexity.Exponential.OrdFormula`, and
`DescriptiveComplexity.ExpExpansion.ordExtendLEquiv` says the result is exactly
the original expansion carrying
`DescriptiveComplexity.ExpExpansion.mapLinearOrder`.

This is the analogue, one level up, of
`DescriptiveComplexity.FOInterpretation.ordExtend` and its `ordExtendLEquiv`,
and it plays the same role: an interpretation whose formulas mention the order
of the structure they read can only be composed with an expansion once that
expansion *defines* its order. It is the prerequisite of the outer composition
that is about the order rather than about quantifiers.

The tag comparison is **static**, exactly as in
`DescriptiveComplexity.lexLeF`: two points with different tags are ordered by
their tags alone, so the defining sentence at such a pair is `⊤` or `⊥`, and
only the equal-tag case emits a real comparison.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-! ### The defining sentence of the order -/

open Classical in
/-- The defining sentence of the order at a pair of tags: the tags are compared
statically, and at equal tags the assignments are compared as binary numbers. -/
noncomputable def ordSentence (t₁ t₂ : X.Tag) :
    ((L.sum Language.order).sum (X.B.replicate 2).lang).Sentence :=
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  if t₁ = t₂ then X.B.ordLeF L else if t₁ < t₂ then ⊤ else ⊥

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (ordSentence)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The defining sentence is the order on points.** -/
theorem realize_ordSentence (t₁ t₂ : X.Tag) (ρs : Fin 2 → X.B.Assignment A) :
    (@Sentence.Realize _ A
        ((X.B.replicate 2).structure₁ (L := L.sum Language.order) (X.B.replicateAssign ρs))
        (X.ordSentence t₁ t₂) ↔
      (X.pointLinearOrder A).le (t₁, ρs 0) (t₂, ρs 1)) := by
  let : LinearOrder X.Tag := finiteLinearOrder X.Tag
  let := X.B.atomIxLinearOrder A
  let := setLinearOrder (X.B.AtomIx A)
  let := (X.B.replicate 2).structure₁ (L := L.sum Language.order) (X.B.replicateAssign ρs)
  have hle : (X.pointLinearOrder A).le (t₁, ρs 0) (t₂, ρs 1) ↔
      t₁ < t₂ ∨ (t₁ = t₂ ∧
        (setLinearOrder (X.B.AtomIx A)).le (X.B.atomSet (ρs 0)) (X.B.atomSet (ρs 1))) :=
    prodLex_le_iff
  rcases eq_or_ne t₁ t₂ with rfl | hne
  · rw [ordSentence, if_pos rfl, X.B.realize_ordLeF ρs, hle]
    simp
  · rw [ordSentence, if_neg hne, hle]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [if_pos hlt]
      simp only [Sentence.Realize, Formula.realize_top, true_iff]
      exact Or.inl hlt
    · rw [if_neg (not_lt_of_gt hgt)]
      simp only [Sentence.Realize, Formula.realize_bot, false_iff]
      rintro (h | ⟨he, -⟩)
      · exact absurd h (not_lt_of_gt hgt)
      · exact hne he

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_ordSentence)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The extended expansion -/

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


