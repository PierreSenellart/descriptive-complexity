/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax117614Proofs.DescriptiveComplexity.Ordered
import Lax117614.CrawlInstances
import Lax117614.GraphCrawlingProblem
import Lax117614.WebsiteGraphs
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

/-!
# Relativized first-order interpretations (definable target universes)

An `Lax117614Proofs.DescriptiveComplexity.FOInterpretation` fixes the target universe to all of
`Tag × A^dim`. That is convenient for *subset*-style problems – a yes-witness
lives on part of the universe and junk elements sit isolated and unused – but
it cannot target a **spanning** problem such as HAMILTON CIRCUIT, where a
yes-witness (a tour) must visit *every* universe element: junk points with no
valid incident edges make every interpreted instance a no-instance.

The textbook remedy ([Immerman 1999][immerman1999descriptive]) is a **domain
formula**: the target universe is a *definable subset* of `Tag × A^dim`. This
file adds it as a layer *on top of* `FOInterpretation`, so that no existing
interpretation, reduction or problem file changes:

* `Lax117614Proofs.DescriptiveComplexity.RelFOInterpretation` extends `FOInterpretation` with a
  `domFormula : Tag → L.Formula (Fin dim)`;
* `Lax117614Proofs.DescriptiveComplexity.RelFOInterpretation.MapRel` is the interpreted structure carried by
  the subtype `{x : Tag × A^dim // domFormula holds of x}`;
* `Lax117614Proofs.DescriptiveComplexity.RelOrderedFOReduction` (notation `≤ʳᶠᵒ[≤]`) is the ordered reduction
  through such an interpretation, carrying the extra obligation
  `dom_nonempty` – a definable domain can be empty on a nonempty structure, so
  `Nonempty Tag` does not by itself guarantee a nonempty output;
* `Lax117614Proofs.DescriptiveComplexity.OrderedFOReduction.toRel` embeds an ordinary ordered reduction as a
  relativized one with `domFormula := ⊤`, the transparency of the whole-universe
  case being an isomorphism (`Lax117614Proofs.DescriptiveComplexity.FOInterpretation.toRelLEquiv`) rather than
  a definitional equality.

This is the hardness-side machinery of relativized reductions; it is what a
hardness proof for a spanning problem needs. Membership closure under
relativized reductions lives in `Lax117614Proofs.DescriptiveComplexity.FixedPointStepRel`, and is
not needed when membership is a direct second-order sentence.
-/

namespace Lax117614Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

namespace RelFOInterpretation

variable (I : Lax904597.Relativized.RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end RelFOInterpretation

/-! ### Functoriality on isomorphisms -/

namespace RelFOInterpretation

variable [L'.IsRelational] (I : Lax904597.Relativized.RelFOInterpretation L L' Tag dim)
  {M N : Type} [L.Structure M] [L.Structure N]

end RelFOInterpretation

/-! ### The whole-universe case is an ordinary interpretation -/

/-! ### Relativized ordered reductions -/

@[inherit_doc]
scoped notation:50 P:51 " ≤ʳᶠᵒ[≤] " Q:51 => Lax904597.Relativized.RelOrderedFOReduction P Q

namespace RelOrderedFOReduction

variable [L.IsRelational] [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}

end RelOrderedFOReduction

end Lax117614Proofs.DescriptiveComplexity


