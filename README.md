# DescriptiveComplexity

A Lean 4 library for descriptive complexity on top of Mathlib's
`ModelTheory` library, in the style of Immerman (*Descriptive Complexity*,
ch. 3). Its main goal is to let users **formalize membership, hardness, and
completeness proofs for common complexity classes** — NP and coNP, PTIME, and
the levels `Σₖᵖ`/`Πₖᵖ` of the polynomial hierarchy — with no machine model:
each class is *defined* logically, so a completeness proof is a definability
witness for membership together with a first-order reduction for hardness,
which the framework closes into a `Complete` theorem. Along the way the library
also **proves a number of results of complexity and descriptive complexity
themselves** — a machine-free Cook–Levin theorem, Fagin's theorem, the Grädel /
Immerman–Vardi capture of PTIME, and the machine bridges that identify these
logically defined classes with the machine ones. All declarations live in the
`DescriptiveComplexity` namespace; the top-level module is
`DescriptiveComplexity`.

Complexity theory is essentially absent from Lean/Mathlib because formalizing
a model of computation with resource bounds is hard. But most classical
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
  order – closed under composition. You can also bring your own concrete
  instance types: a bundled `Encoding` cannot be constructed without proving
  polynomial size bounds in both directions (no padding, no compression), so
  an encoding cannot silently cheat on instance size – and a theorem shows the
  bounds have teeth (no unary encoding of subset-sum passes them). The
  converse direction is covered too: computable `Decoding`s read well-formed
  structures back into concrete instances, and completeness theorems restrict
  to the well-formed (non-junk) instances with one-line upgrades.
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
| **NL** | SO-Krom (existential second-order Krom: at most two second-order literals per clause, either sign) – Grädel; equivalently the complements of the FO(TC) definable problems (FO(TC) itself would need Immerman–Szelepcsényi) | 2SAT |
| **PTIME** = Σ₀ᵖ = Π₀ᵖ | SO-Horn (existential second-order Horn), proved equivalent to FO(LFP) – Grädel; Immerman–Vardi; equivalently acceptance by a deterministic polynomial-time Turing machine | HORN-SAT · acceptance by a deterministic polynomial-time Turing machine |
| **NP** = Σ₁ᵖ | ∃SO, existential second-order logic (Fagin); equivalently acceptance by a nondeterministic polynomial-time Turing machine | **SAT-family:** SAT · 3SAT · NAE-SAT · NAE-3SAT · 1-in-SAT<br>**Coloring:** 3-Colorability · `k`-Colorability (`k ≥ 3`) · Chromatic Number · Clique Cover<br>**Cliques & subgraphs:** Clique · Independent Set · Vertex Cover · Subgraph Isomorphism<br>**Sets & hypergraphs:** Set Cover · Hitting Set · Set Packing · Exact Cover · Set Splitting · Dominating Set · 3-Dimensional Matching<br>**Graphs:** Feedback Vertex Set · Feedback Arc Set · Steiner Tree (node- & edge-weighted) · Max Cut · Hamilton Circuit (directed & undirected)<br>**Numbers (in binary):** Knapsack · Partition · 0-1 Integer Programming · Job Sequencing<br>**Machines:** acceptance by a nondeterministic polynomial-time Turing machine |
| **coNP** = Π₁ᵖ | ∀SO, universal second-order logic | TAUT · 3-DNF-TAUT · 3-UNSAT (and QBF∀ at one block) |
| **Σₖᵖ** (`k ≥ 1`) | Σₖ¹: `k` alternating second-order blocks, existential first (Stockmeyer) | `QBF k` (quantified Boolean formulas, `k` blocks) – at `k = 1`, NP |
| **Πₖᵖ** (`k ≥ 1`) | Πₖ¹: `k` alternating second-order blocks, universal first | `QBF∀ k` (universal-first, `k` blocks) – at `k = 1`, coNP |
| **PH** | full second-order logic | — |

The characterizations are the logical *definitions* of the classes (see the
Overview above); the inclusions and dualities relating them are theorems.
REACH/UNREACH is given as a further worked instance – a membership example, not
proved complete.

## Scope and limitations

These are *intrinsic* to the descriptive, machine-free approach — the price of
needing no model of computation. They are the nature of the framework, not a
backlog; for capabilities that are simply not built yet, see *On the roadmap*
below.

* **Complexity of problems, not of algorithms.** Complexity is attributed to a
  decision *problem* (is it in / hard for / complete for a class), never to a
  procedure. There is no cost model, no running-time or space bound as a number,
  **no `O(·)`, and no fine-grained complexity**: the framework cannot separate
  `O(n)` from `O(n²)`, track polynomial degrees, or reason about a particular
  algorithm's resource use. What you prove is membership, hardness and
  completeness for the coarse classes above.
* **Instances are finite relational structures, not strings.** Every problem is
  modeled by choosing a vocabulary and encoding its inputs as finite structures
  (numbers via the integer representations of `ROADMAP.md §0`, size honesty of
  user-supplied encodings via the bundled `Encoding` bounds), and yes-instance
  sets must be isomorphism-invariant. Reasoning is about **finite** structures
  only; nothing is claimed about infinite ones. The identification with the
  textbook *string*-based classes rests on the machine-bridge theorems plus the
  fact that FO reductions are AC⁰-computable.
* **Hardness is an FO reduction; membership is a logical definition.** You show
  hardness by exhibiting a first-order (or order-invariant FO) reduction, and
  membership by a definability witness (∃SO for NP, SO-Horn / FO(LFP) for
  PTIME, …) — not by describing a polynomial-time algorithm. This is *stronger*
  than a Karp reduction, but the reduction must be expressible in logic: a
  poly-time reduction that is not FO-expressible cannot be used, gadget
  constructions must be encoded (often needing a linear order, tags, or extra
  dimensions), and arithmetic inside formulas is limited (addition and
  comparison are FO(≤); multiplication is not FO).
* **Completeness and structure, not separations.** The library proves
  completeness, inclusions and logical characterizations. Whether the classes
  are *distinct* (P vs NP, and the like) is open mathematics the framework does
  not decide. Unconditional *inexpressibility* results — a genuine strength of
  the descriptive approach — are a planned direction, not yet present (below).

## On the roadmap

The following are *feasible* within this framework and planned, but **not yet
implemented**. `ROADMAP.md` is the detailed version; the highlights a typical
user is most likely to want:

* **Complexity classes beyond the polynomial hierarchy.** L, PSPACE, and up
  toward EXPTIME/EXPSPACE, via the transitive-closure and fixpoint logics that
  capture them (FO(DTC), SO(TC), FO(PFP)/SO(LFP)) and their complete problems
  (REACHd, QSAT), each with a machine bridge as for NP and PTIME. Below NP this
  also brings the P-complete problems (Circuit Value, alternating
  reachability). `NL = coNL` (Immerman–Szelepcsényi) is not done either, and it
  is what `REACH ∈ NL` waits on.
* **Counting and optimization problems.** Only decision problems are modeled
  today. Planned: #P via counting second-order assignments (#SAT, #3COL, the
  permanent) and MaxSNP-style optimization classes — i.e. function and search
  problems, not just yes/no ones.
* **Unconditional lower bounds (inexpressibility).** The payoff unique to the
  descriptive approach, impossible in the machine world: Ehrenfeucht–Fraïssé
  games, EVEN and reachability not being FO-definable, `FO ⊊ FO(TC)` as a strict
  inclusion, locality, 0-1 laws, and eventually PARITY ∉ AC⁰.
* **Structural / capture theorems.** Immerman–Szelepcsényi (NL = coNL),
  Immerman–Vardi (P = order-invariant FO(LFP)), Grädel's capture theorems, and
  Fagin's spectra connection.
* **A broader catalog and finer reductions.** More complete problems, and the
  finer reduction notions descriptive complexity uses (quantifier-free
  projections; FO(≤, BIT) = uniform AC⁰ as the bottom of the ordered world).

One caveat within this list: the `Δₖᵖ` levels of the polynomial hierarchy
(`Δₖᵖ = P^{Σₖ₋₁ᵖ}`, e.g. `Δ₂ᵖ = P^NP`). The `Σₖᵖ`/`Πₖᵖ` levels are in scope —
they are *defined* here by second-order quantifier alternation — but `Δₖᵖ` has
no such logical characterization: it is a deterministic class defined by bounded
oracle access, so capturing it faithfully would need the oracle-machine model
the framework deliberately avoids, and it may stay out of reach.

## Use as a dependency

The library tracks one Mathlib release at a time: a version works with the
Mathlib version it is named after, and `master` follows the latest Mathlib pin.
Your project and this one must resolve to the **same** Mathlib version, since
Lake builds a single Mathlib per workspace. The current release is
`v4.33.0-rc1`, for Mathlib `v4.33.0-rc1` and toolchain
`leanprover/lean4:v4.33.0-rc1`.

In a `lakefile.lean`:

```lean
require "descriptive-complexity" from git
  "https://github.com/PierreSenellart/descriptive-complexity" @ "v4.33.0-rc1"
```

or, in a `lakefile.toml`:

```toml
[[require]]
name = "descriptive-complexity"
git = "https://github.com/PierreSenellart/descriptive-complexity"
rev = "v4.33.0-rc1"
```

The revision can be a branch, a tag or a commit hash; pin a version tag or a
commit hash rather than `master`, for reproducible builds. Then

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
* **Tutorials**: `DescriptiveComplexity/Examples/ConjunctiveQueries.lean` and
  `DescriptiveComplexity/Examples/GraphCrawling.lean` are worked examples read
  top to bottom – each walks through adding a new problem domain in the order
  a user meets it (concrete problem → encoding, size bounds discharged at
  construction → vocabulary and semantics → faithfulness → membership →
  hardness → completeness) and is meant to serve as a template.

## Building

The library tracks a stable Mathlib release; the toolchain in `lean-toolchain`
must match the pinned Mathlib version.

```
lake exe cache get   # fetch Mathlib build cache
lake build
```
