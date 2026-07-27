/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Machine
import DescriptiveComplexity.Counting.Order
import DescriptiveComplexity.Counting.Sound
import DescriptiveComplexity.Counting.Complete

/-!
# Inductive counting

Umbrella file for the combinatorial core of Immerman–Szelepcsényi: a
nondeterministic machine on a finite graph that accepts exactly when no target
is reachable from a source, by counting the nodes of every layer
(`DescriptiveComplexity.Counting.Machine`), and the two directions of its correctness
(`DescriptiveComplexity.Counting.Sound`, `DescriptiveComplexity.Counting.Complete`). Nothing
here is first-order; `DescriptiveComplexity.TransitiveClosureCompl` is what runs the
machine inside a single `TC`.
-/
