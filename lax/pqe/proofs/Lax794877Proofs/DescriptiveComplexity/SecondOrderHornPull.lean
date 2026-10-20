/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax794877Proofs.DescriptiveComplexity.SecondOrderPull
import Lax794877Proofs.DescriptiveComplexity.OrderedComposition
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax794877Proofs.DescriptiveComplexity.HornClause
end Lax794877Proofs.DescriptiveComplexity.HornClause

namespace Lax794877Proofs.DescriptiveComplexity.HornProgram
end Lax794877Proofs.DescriptiveComplexity.HornProgram

namespace Lax794877Proofs.DescriptiveComplexity.SigmaSOHornDefinable
end Lax794877Proofs.DescriptiveComplexity.SigmaSOHornDefinable

namespace Lax859101.SubtractiveReductions.FOInterpretation
end Lax859101.SubtractiveReductions.FOInterpretation

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause HornProgram SigmaSOHornDefinable)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation
export Lax859101.SubtractiveReductions.FOInterpretation (ordExtend)
end Lax904597.Interpretations.FOInterpretation

/-!
# Pulling SO-Horn definability back through an interpretation

SO-Horn definability is closed under (ordered) first-order reductions
(`DescriptiveComplexity.SigmaSOHornDefinable.of_orderedReduction`). This is what makes
the fragment a `DescriptiveComplexity.ComplexityClass` – the class
`DescriptiveComplexity.PTIME` – rather than a mere definability predicate.

The closure is *not* an instance of the general pullback of
`DescriptiveComplexity.SecondOrderPull`, which only says that the pulled-back kernel is
some first-order formula: here the pulled-back kernel has to stay *Horn*. It
does, and for a structural reason worth stating, since it is exactly what the
Horn condition is careful about: the condition constrains the occurrences of
the *second-order* variables only, while an interpretation rewrites the
*input-vocabulary* atoms – which live in the guard, where anything is allowed.
Concretely, pulling a clause back through a `d`-dimensional interpretation
with tag type `Tag`:

* the block is pulled as in `DescriptiveComplexity.SOBlock.pull`: an `n`-ary relation
  variable on `Tag × A^d` becomes one `(n·d)`-ary relation variable on `A` per
  `n`-tuple of tags;
* a clause becomes one clause per assignment `t : Fin k → Tag` of tags to its
  universally quantified variables (`DescriptiveComplexity.HornClause.pull`), with the
  `k` variables replaced by `k · d` coordinates;
* its guard becomes the ordinary formula pullback
  `DescriptiveComplexity.FOInterpretation.pull` at the tag assignment `t` – an arbitrary
  first-order formula, which is fine, guards being unconstrained;
* each body and head atom becomes the atom of the corresponding pulled
  relation variable (`DescriptiveComplexity.SOAtom.pull`) – *still an atom*, which is
  what keeps the clause Horn.

The one place the order is needed is that the guards of the target may mention
it: the pullback interprets the target's order by the lexicographic order on
tagged tuples (`DescriptiveComplexity.FOInterpretation.ordExtend`), which is why the
definability notion quantifies over ordered structures in the first place.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

/-! ### Pulling back a clause and a program -/

/-- The pullback of a Horn clause at a tag assignment: guards pull back as
formulas, atoms as atoms – so the result is again a Horn clause. -/
noncomputable def HornClause.pull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    (c : Lax535992.HornFragment.HornClause L₂ B k) (t : Fin k → Tag) : Lax535992.HornFragment.HornClause L₁ (B.pull Tag d) (k * d) where
  guard := guardPull I c.guard t
  body := c.body.map fun a => a.pull d t
  head := c.head.map fun a => a.pull d t

end Lax794877Proofs.DescriptiveComplexity

namespace Lax535992.HornFragment.HornClause

export Lax794877Proofs.DescriptiveComplexity.HornClause (pull)

end Lax535992.HornFragment.HornClause

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

theorem HornClause.pull_holds {A : Type} [L₁.Structure A]
    (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (c : Lax535992.HornFragment.HornClause L₂ B k) (t : Fin k → Tag)
    (ρ : B.Assignment (I.Map A)) (w : Fin (k * d) → A) :
    (c.pull I t).Holds (B.pullAssign ρ) w ↔ c.Holds ρ (tagVal I t w) := by
  have hhead : (c.pull I t).HeadHolds (B.pullAssign ρ) w ↔ c.HeadHolds ρ (tagVal I t w) := by
    rw [Lax535992.HornFragment.HornClause.HeadHolds, Lax535992.HornFragment.HornClause.HeadHolds, HornClause.pull]
    cases c.head with
    | none => exact Iff.rfl
    | some a => exact a.pull_holds I t ρ w
  refine imp_congr (and_congr ?_ ?_) hhead
  · exact realize_guardPull I c.guard t w
  · rw [HornClause.pull]
    constructor
    · intro h a ha
      exact (a.pull_holds I t ρ w).mp (h _ (List.mem_map_of_mem ha))
    · intro h a' ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      exact (a.pull_holds I t ρ w).mpr (h a ha)

end Lax794877Proofs.DescriptiveComplexity

namespace Lax535992.HornFragment.HornClause

export Lax794877Proofs.DescriptiveComplexity.HornClause (pull_holds)

end Lax535992.HornFragment.HornClause

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

/-- The pullback of a Horn program: one clause per clause of the program and
per assignment of tags to its universally quantified variables. -/
noncomputable def HornProgram.pull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    (prog : Lax535992.HornFragment.HornProgram L₂ B k) : Lax535992.HornFragment.HornProgram L₁ (B.pull Tag d) (k * d) :=
  prog.flatMap fun c => (allTagAssign Tag k).map fun t => c.pull I t

end Lax794877Proofs.DescriptiveComplexity

namespace Lax535992.HornFragment.HornProgram

export Lax794877Proofs.DescriptiveComplexity.HornProgram (pull)

end Lax535992.HornFragment.HornProgram

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

theorem HornProgram.pull_mem (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    {prog : Lax535992.HornFragment.HornProgram L₂ B k} {c : Lax535992.HornFragment.HornClause L₂ B k} (hc : c ∈ prog)
    (t : Fin k → Tag) : c.pull I t ∈ prog.pull I := by
  rw [HornProgram.pull, List.mem_flatMap]
  exact ⟨c, hc, List.mem_map.mpr ⟨t, mem_allTagAssign t, rfl⟩⟩

end Lax794877Proofs.DescriptiveComplexity

namespace Lax535992.HornFragment.HornProgram

export Lax794877Proofs.DescriptiveComplexity.HornProgram (pull_mem)

end Lax535992.HornFragment.HornProgram

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

theorem HornProgram.pull_cases (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    {prog : Lax535992.HornFragment.HornProgram L₂ B k} {c' : Lax535992.HornFragment.HornClause L₁ (B.pull Tag d) (k * d)}
    (hc' : c' ∈ prog.pull I) : ∃ c ∈ prog, ∃ t : Fin k → Tag, c' = c.pull I t := by
  rw [HornProgram.pull, List.mem_flatMap] at hc'
  obtain ⟨c, hc, hmem⟩ := hc'
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hmem
  exact ⟨c, hc, t, rfl⟩

end Lax794877Proofs.DescriptiveComplexity

namespace Lax535992.HornFragment.HornProgram

export Lax794877Proofs.DescriptiveComplexity.HornProgram (pull_cases)

end Lax535992.HornFragment.HornProgram

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

/-! ### Correctness of the pullback -/

section Correctness

end Correctness

/-! ### Closure under reductions -/

section Closure

end Closure

end Lax794877Proofs.DescriptiveComplexity


