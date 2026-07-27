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
* **A problem catalog and worked examples**: one decision problem per file,
  each with its vocabulary, FO reductions and a completeness theorem, plus
  tutorial-style worked examples. Highlights: a machine-free Cook–Levin theorem
  for SAT, **all of Karp's 21 problems**, PTIME-completeness of HORN-SAT by the
  analogous machine-free discharge one level down, and the *machine bridge* –
  acceptance by a nondeterministic polynomial-time Turing machine is
  NP-complete (`ntmAccept_NP_complete`), acceptance by a deterministic one
  PTIME-complete (`dtmAccept_PTIME_complete`), so a problem is in the
  library's NP (resp. PTIME) exactly when it ordered-FO-reduces to Turing
  machine acceptance (`mem_NP_iff_le_ntmAccept`,
  `mem_PTIME_iff_le_dtmAccept`): both halves of Fagin's theorem and its
  Grädel / Immerman–Vardi analogue, and the logically defined classes *are*
  the machine ones. The classes these problems populate, their logical characterizations,
  and the problems proved complete for each are collected in the table below.

## Complexity classes and complete problems

Every class is *defined* logically – no machine model, no axioms. Each problem
listed is proved **complete** for its class: both a member and hard for it
under FO reductions. Karp's 21 NP-complete problems are all present.

| Complexity class | Logical characterization | Problems proved complete |
| --- | --- | --- |
| **PTIME** = Σ₀ᵖ = Π₀ᵖ | SO-Horn (existential second-order Horn), proved equivalent to FO(LFP) – Grädel; Immerman–Vardi; equivalently acceptance by a deterministic polynomial-time Turing machine | HORN-SAT · acceptance by a deterministic polynomial-time Turing machine |
| **NP** = Σ₁ᵖ | ∃SO, existential second-order logic (Fagin); equivalently acceptance by a nondeterministic polynomial-time Turing machine | **SAT-family:** SAT · 3SAT · NAE-SAT · NAE-3SAT · 1-in-SAT<br>**Coloring:** 3-Colorability · `k`-Colorability (`k ≥ 3`) · Chromatic Number · Clique Cover<br>**Cliques & subgraphs:** Clique · Independent Set · Vertex Cover · Subgraph Isomorphism<br>**Sets & hypergraphs:** Set Cover · Hitting Set · Set Packing · Exact Cover · Set Splitting · Dominating Set · 3-Dimensional Matching<br>**Graphs:** Feedback Vertex Set · Feedback Arc Set · Steiner Tree (node- & edge-weighted) · Max Cut · Hamilton Circuit (directed & undirected)<br>**Numbers (in binary):** Knapsack · Partition · 0-1 Integer Programming · Job Sequencing<br>**Machines:** acceptance by a nondeterministic polynomial-time Turing machine<br>**Queries:** Conjunctive Query Evaluation · CQ Containment |
| **coNP** = Π₁ᵖ | ∀SO, universal second-order logic | TAUT (and QBF∀ at one block) |
| **Σₖᵖ** (`k ≥ 1`) | Σₖ¹: `k` alternating second-order blocks, existential first (Stockmeyer) | `QBF k` (quantified Boolean formulas, `k` blocks) – at `k = 1`, NP |
| **Πₖᵖ** (`k ≥ 1`) | Πₖ¹: `k` alternating second-order blocks, universal first | `QBF∀ k` (universal-first, `k` blocks) – at `k = 1`, coNP |
| **PH** | full second-order logic | — |

The characterizations are the logical *definitions* of the classes (see the
Overview above); the inclusions and dualities relating them are theorems.
REACH/UNREACH is given as a further worked instance in PTIME – a membership
example, not proved complete.

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
