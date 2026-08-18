/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Tiling.Defs
import DescriptiveComplexity.Problems.Tiling.Membership
import DescriptiveComplexity.Problems.Tiling.CorridorMem

/-!
# TILING and CORRIDOR, the umbrella

The two questions a tile system is asked: tiling the square whose sides are the
positions of the instance (`DescriptiveComplexity.Problems.Tiling.Defs`, with
its membership in `DescriptiveComplexity.Problems.Tiling.Membership`), and
tiling the *corridor* of that width and unbounded height
(`DescriptiveComplexity.Problems.Tiling.Corridor`, with its membership in
`DescriptiveComplexity.Problems.Tiling.CorridorMem`).

The point of the two is what they become one exponential up: read over an
exponential expansion, the same definitions ask about a `2ⁿ × 2ⁿ` square and a
corridor of width `2ⁿ`, which are the classical second complete problems of
NEXPTIME and of EXPSPACE beside a machine.
-/
