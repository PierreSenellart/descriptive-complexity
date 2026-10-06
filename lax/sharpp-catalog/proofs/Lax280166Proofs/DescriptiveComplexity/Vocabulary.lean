/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
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

/-!
# Declaring a vocabulary

A relational vocabulary is always declared the same way: an inductive of
relation symbols indexed by arity, a `Language` whose function symbols are
`Empty`, its `IsRelational` instance, one abbreviation naming each symbol at
its arity, and one predicate reading each symbol off a structure. Only the
names and the arities differ.

`fo_language` takes those and writes the rest:

```
/-- The relational language of pattern-and-host graphs. -/
fo_language twoGraphs with tg where
  /-- `patV a`: `a` is a vertex of the pattern graph. -/
  patV : 1
  /-- `hostV a`: `a` is a vertex of the host graph. -/
  hostV : 1
```

declares `twoGraphsRel` (with `DecidableEq`), `Language.twoGraphs` with its
`IsRelational` instance, and the symbols `tgPatV` and `tgHostV`. The prefix is
the one the library's convention asks for, `tg` naming the symbols of
`Language.twoGraphs`. The docstring of the command becomes the docstring of the
language, and each symbol's becomes that of its constructor and its
abbreviation.

A vocabulary lives in `namespace FirstOrder.Language`, next to Mathlib's, while
the predicates reading it off a structure live with the problem, in
`namespace DescriptiveComplexity`. So they are two commands, and
`fo_predicates Language.twoGraphs tg` writes the second half:

```
def TGPatV {A : Type} [Language.twoGraphs.Structure A] (a₀ : A) : Prop :=
  RelMap tgPatV ![a₀]
```

one predicate per symbol, named by the prefix in upper case, as the catalog
names them throughout. It reads the symbols out of the environment, so it takes
no list; the vocabulary must have been declared by `fo_language`, or by hand
following the same convention.

The generated declarations are the hand-written ones, so a vocabulary
converted to these commands changes nothing that reads it.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open Lean Elab Command

/-- One symbol of a vocabulary: `patV : 1`. -/
syntax foSymDecl := (docComment)? ident " : " num

/-- Declare a relational language and its symbols; see the module docstring. -/
syntax (name := foLanguage) (docComment)?
  "fo_language " ident " with " ident " where" manyIndent(ppLine foSymDecl) : command

/-- Declare the predicates reading a vocabulary's symbols off a structure; see
the module docstring. -/
syntax (name := foPredicates) "fo_predicates " ident ident : command

namespace FOVocabulary

end FOVocabulary

end Lax280166Proofs.DescriptiveComplexity


