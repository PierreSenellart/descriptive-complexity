/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.Problems.Taut
import DescriptiveComplexity.Problems.HornSat
import DescriptiveComplexity.Problems.Reachability
import DescriptiveComplexity.Problems.ThreeColorability
import DescriptiveComplexity.Problems.KColorability
import DescriptiveComplexity.Problems.ThreeSat
import DescriptiveComplexity.Problems.CliqueFamily
import DescriptiveComplexity.Problems.SetFamily
import DescriptiveComplexity.Problems.FeedbackVertexSet
import DescriptiveComplexity.Problems.Qbf

/-!
# The problem catalog

Umbrella file importing every decision problem of the library. Each problem
lives in its own file (or directory) under `DescriptiveComplexity/Problems/`,
containing its vocabulary, its semantic definition, the bundled
`DescriptiveComplexity.DecisionProblem`, its first-order reductions, and its
completeness theorems.
-/
