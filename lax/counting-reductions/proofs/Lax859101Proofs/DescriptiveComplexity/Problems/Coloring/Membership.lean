/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.ModelTheory.Graph
import Lax859101Proofs.DescriptiveComplexity.Interpretation
import Lax859101Proofs.DescriptiveComplexity.OccurrenceFormulas
import Lax859101Proofs.DescriptiveComplexity.OccurrenceOrder
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax859101Proofs.DescriptiveComplexity.SecondOrder
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

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.Coloring
end Lax799700.Coloring

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (MGAdj MGMarked)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.Coloring (HasSmallChromaticNumber HasSmallCliqueCover)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph)
end FirstOrder.Language

/-!
# The coloring family is existential second-order definable

Membership for the three problems, in two flavors dictated by where the
number of colors lives.

* For `DescriptiveComplexity.KCol k`, the number `k` is fixed by the problem, so the
  definition can guess the `k` color classes as `k` unary relation variables
  and check first-order that they cover the vertices and that no edge stays
  inside a class (`DescriptiveComplexity.kCol_sigmaSODefinable`); the kernel is built
  with `Formula.iSup`/`iInf` over `Fin k`.
* For `DescriptiveComplexity.ChromaticNumber` and `DescriptiveComplexity.CliqueCover`, the
  number is the size of the marked set, so it is *not* available to the
  formulas – there is no “`k` classes” to write down. The palette form
  (`DescriptiveComplexity.paletteColorableOn_iff`) removes the problem: coloring with
  as many colors as the marked set has elements is coloring *by* the marked
  set, which a single binary relation variable `Col x y`, read as “`x` has
  color `y`”, expresses. The kernel then has two clauses: every vertex gets
  some marked color, and two conflicting vertices never share a color. Note
  that the guessed relation need not be functional: choosing one color per
  vertex is enough, and the second clause already forbids a shared one.

The two threshold problems differ only in the sign of the adjacency atom in
that second clause, so their kernels come from one builder
(`DescriptiveComplexity.paletteProperClause`) parameterized by that sign.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

/-! ### Membership: the color classes as guessed relations -/

section SigmaOne

/-- The single existential block of the `Σ₁` definition of `k`-colorability:
one unary relation variable per color. -/
def colorGuessBlock (k : ℕ) : Lax904597.SecondOrder.SOBlock where
  ι := Fin k
  arity := fun _ => 1

/-- The symbol of the `i`-th color class. -/
def cgColorSym {k : ℕ} (i : Fin k) : (colorGuessBlock k).lang.Relations 1 := ⟨i, rfl⟩

/-- The vocabulary of the kernel: graphs together with the guessed color
classes. -/
abbrev kColSOLang (k : ℕ) : Language := Language.graph.sum (colorGuessBlock k).lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev kcAdjSym (k : ℕ) : (kColSOLang k).Relations 2 := Sum.inl adj

/-- The symbol of the `i`-th color class in the kernel's vocabulary. -/
abbrev kcColorSym {k : ℕ} (i : Fin k) : (kColSOLang k).Relations 1 := Sum.inr (cgColorSym i)

/-- The first-order kernel of the `Σ₁` definition of `k`-colorability: every
vertex belongs to some color class, and no edge has both endpoints in the
same class. -/
noncomputable def kColKernel (k : ℕ) : (kColSOLang k).Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.Formula.iSup
          (fun i : Fin k =>
            FirstOrder.Language.Relations.formula₁ (kcColorSym i) (FirstOrder.Language.Term.var (Sum.inr 0)))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 2)
        ((FirstOrder.Language.Relations.formula₂ (kcAdjSym k) (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          (FirstOrder.Language.Formula.iInf
            (fun i : Fin k =>
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₁ (kcColorSym i) (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                  FirstOrder.Language.Relations.formula₁ (kcColorSym i) (FirstOrder.Language.Term.var (Sum.inr 1))))))

end SigmaOne

/-! ### Chromatic Number and Clique Cover: the palette as a binary relation -/

section Palette

end Palette

end Lax859101Proofs.DescriptiveComplexity


