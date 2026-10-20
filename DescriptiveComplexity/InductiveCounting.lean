/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import DescriptiveComplexity.InductiveCounting.Machine
public import DescriptiveComplexity.InductiveCounting.Order
public import DescriptiveComplexity.InductiveCounting.Sound
public import DescriptiveComplexity.InductiveCounting.Complete

/-!
# Inductive counting

Umbrella file for the combinatorial core of Immerman–Szelepcsényi: a
nondeterministic machine on a finite graph that accepts exactly when no target
is reachable from a source, by counting the nodes of every layer
(`DescriptiveComplexity.InductiveCounting.Machine`), and the two directions of
its correctness (`DescriptiveComplexity.InductiveCounting.Sound`,
`DescriptiveComplexity.InductiveCounting.Complete`). Nothing here is
first-order; `DescriptiveComplexity.TransitiveClosureCompl` is what runs the
machine inside a single `TC`.
-/

@[expose] public section
