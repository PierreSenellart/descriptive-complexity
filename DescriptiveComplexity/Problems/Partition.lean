/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Partition.Defs
import DescriptiveComplexity.Problems.Partition.Membership

/-!
# Partition

Umbrella file for `DescriptiveComplexity.Partition`, Karp's PARTITION – can a
family of numbers, written in *binary*, be split into two parts of equal sum?

So far it collects the definition and its isomorphism-invariance, and the
first-order kernel of the `Σ₁` definition
(`DescriptiveComplexity.partitionKernel`): the certificate guesses the split and two
ripple-carry walks – one along the chosen items, one along the others – on the
*wide* positions of `DescriptiveComplexity.Numbers.Wide`, and requires them to agree
at the last item. The semantic half of the membership proof, and the hardness
reduction from NAE-3SAT, are under construction – see `ROADMAP.md`.
-/
