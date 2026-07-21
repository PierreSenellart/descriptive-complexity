/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.Problems.Sat
import FOReduction.Problems.ThreeColorability
import FOReduction.Problems.ThreeSat
import FOReduction.Problems.CliqueFamily

/-!
# The problem catalog

Umbrella file importing every decision problem of the library. Each problem
lives in its own file (or directory) under `FOReduction/Problems/`,
containing its vocabulary, its semantic definition, the bundled
`FirstOrder.DecisionProblem`, its first-order reductions, and its
completeness theorems.
-/
