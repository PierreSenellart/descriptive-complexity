# DescriptiveComplexity

A Lean 4 library for descriptive complexity on top of Mathlib's
`ModelTheory` library: machine-model-free hardness reductions in the style
of Immerman (*Descriptive Complexity*, ch. 3). All declarations live in the
`DescriptiveComplexity` namespace; the top-level module is
`DescriptiveComplexity`.

Complexity theory is essentially absent from Lean/Mathlib because formalizing
a model of computation with resource bounds is hard. But many classical
NP-hardness reductions do not need the full power of PTIME: they are
*first-order expressible*. An FO reduction is computable in AC⁰ ⊆ LOGSPACE ⊆
PTIME, so exhibiting one is strictly stronger than exhibiting a Karp
reduction, while requiring no machine model at all: only first-order logic,
which Mathlib already has.

As far as we know this is the first use of FO-expressible reductions in a
proof assistant (the closest prior work is the “cookbook reductions” of
Grange, Vehlken, Vortmeier and Zeume, MFCS 2024, which uses FO-definable
reductions in an automated-verification/teaching setting, not an ITP).

Both directions between SAT and 3-colorability are formalized: an order-free,
quantifier-free reduction 3COL → SAT, and an ordered FO reduction SAT → 3COL
(the classical gadget construction, which genuinely needs a linear order on
the input structure to thread each clause's OR-gadget chain). SAT and
3-colorability are thus FO-interreducible.

## Overview

The library is organized in three layers:

* **A reduction framework** over `ModelTheory`: decision problems as
  isomorphism-invariant properties of finite structures, tagged first-order
  interpretations between languages, and FO reductions `≤ᶠᵒ` – with their
  order-invariant variant `≤ᶠᵒ[≤]` for gadgets that genuinely need a linear
  order – closed under composition.
* **An abstract complexity layer**: complexity classes closed under FO
  reductions, and the polynomial hierarchy *defined* logically – `NP = Σ₁ᵖ` by
  second-order quantifier alternation, with the level inclusions and the
  duality `Πₖᵖ = co-Σₖᵖ` as theorems, and level 0, `PTIME`, by the Horn
  fragment SO-Horn of existential second-order logic – equivalent to the logic
  FO(LFP) by a formalized Grädel translation, so that PTIME is closed under
  complement (`Π₀ᵖ = Σ₀ᵖ`) as a theorem. Everything is a definition or a
  theorem: the library declares no axioms.
* **A problem catalog and worked examples**: SAT (with a machine-free
  Cook–Levin theorem), 3-colorability and `k`-colorability for every `k ≥ 3`,
  3SAT and NAE-SAT, Chromatic Number and Clique Cover, the clique family
  (Clique / Independent Set / Vertex Cover), Subgraph Isomorphism, Set Cover,
  Hitting Set and Set Packing, Feedback Vertex Set and Feedback Arc Set,
  Steiner Tree, TAUT (coNP-complete),
  `QBF k` – quantified Boolean formulas with `k` alternating blocks, complete
  for the `k`-th level of the polynomial hierarchy – and HORN-SAT, complete for
  PTIME by the analogous machine-free discharge one level down; plus a tutorial
  on conjunctive queries. Each comes with its vocabulary, FO reductions and
  completeness theorems.

## Use as a dependency

The library tracks one Mathlib release at a time: a given version works with
the Mathlib version it is named after, and `master` follows the latest stable
Mathlib. Your project and this one must resolve to the **same** Mathlib
version, since Lake builds a single Mathlib per workspace.

In a `lakefile.lean`:

```lean
require "descriptive-complexity" from git
  "https://github.com/PierreSenellart/descriptive-complexity" @ "master"
```

or, in a `lakefile.toml`:

```toml
[[require]]
name = "descriptive-complexity"
git = "https://github.com/PierreSenellart/descriptive-complexity"
rev = "master"
```

The revision can be a branch, a tag or a commit hash; pin a version tag (such
as `v4.33.0`) or a commit hash rather than `master`, for reproducible builds.
Then

```lean
import DescriptiveComplexity
```

brings in the whole library; import individual modules (for instance
`DescriptiveComplexity.Problems.Sat`) to keep build times down.

## Documentation

* **API reference**:
  <https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>
  – the `DescriptiveComplexity` module page is a part-by-part map of the
  library, and every declaration is documented on its own page.
* **Tutorial**: `DescriptiveComplexity/Examples/ConjunctiveQueries.lean` is a
  worked example read top to bottom – it walks through adding a new problem
  domain (vocabulary → semantics → invariance → membership → hardness →
  completeness) and is meant to serve as a template.

## Building

The library tracks a stable Mathlib release; the toolchain in `lean-toolchain`
must match the pinned Mathlib version.

```
lake exe cache get   # fetch Mathlib build cache
lake build
```
