# DescriptiveComplexity

A Lean 4 library for descriptive complexity on top of Mathlib's
`ModelTheory` library, in the style of Immerman (*Descriptive Complexity*,
ch. 3). Its main goal is to let users **formalize membership, hardness, and
completeness proofs for common complexity classes** — NP and coNP, PTIME,
PSPACE, and the levels `Σₖᵖ`/`Πₖᵖ` of the polynomial hierarchy — with no machine
model required:
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

Every class is *defined* logically – machine models, when they exist, are
additional characterizations. Each problem listed is proved **complete**
for its class: both a member and hard for it under FO reductions. Karp's
21 NP-complete problems are all present.

| Complexity class | Logical characterization | Machine model | Problems proved complete |
| --- | --- | --- | --- |
| **L** = LOGSPACE | FO(DTC): first-order logic with a deterministic transitive closure | deterministic two-way `k`-head automaton | REACHd · UNREACHd |
| **NL** | SO-Krom: ∃SO with a Krom kernel, at most two second-order literals per clause; equivalently FO(TC), first-order logic with a transitive closure | two-way `k`-head automaton | REACH · UNREACH · 2SAT |
| **PTIME** = Σ₀ᵖ = Π₀ᵖ | SO-Horn: ∃SO with a Horn kernel; equivalently FO(LFP), first-order logic with a least fixed point | deterministic polynomial-time Turing machine | HORN-SAT · acceptance by a deterministic polynomial-time Turing machine |
| **NP** = Σ₁ᵖ | ∃SO: existential second-order logic | nondeterministic polynomial-time Turing machine | **SAT-family:** SAT · 3SAT · NAE-SAT · NAE-3SAT · 1-in-SAT<br>**Coloring:** 3-Colorability · `k`-Colorability (`k ≥ 3`) · Chromatic Number · Clique Cover<br>**Cliques & subgraphs:** Clique · Independent Set · Vertex Cover · Subgraph Isomorphism<br>**Sets & hypergraphs:** Set Cover · Hitting Set · Set Packing · Exact Cover · Set Splitting · Dominating Set · 3-Dimensional Matching<br>**Graphs:** Feedback Vertex Set · Feedback Arc Set · Steiner Tree (node- & edge-weighted) · Max Cut · Hamilton Circuit (directed & undirected)<br>**Numbers (in binary):** Knapsack · Partition · 0-1 Integer Programming · Job Sequencing<br>**Machines:** acceptance by a nondeterministic polynomial-time Turing machine |
| **coNP** = Π₁ᵖ | ∀SO: universal second-order logic | — | TAUT · 3-DNF-TAUT · 3-UNSAT (and QBF∀ at one block) |
| **DP** | a Σ₁ and a Π₁ sentence conjoined | — | SAT-UNSAT |
| **Σₖᵖ** (`k ≥ 1`) | Σₖ¹: `k` alternating second-order quantifier blocks, existential first | — | `QBF k` (quantified Boolean formulas, `k` blocks) – at `k = 1`, NP |
| **Πₖᵖ** (`k ≥ 1`) | Πₖ¹: `k` alternating second-order quantifier blocks, universal first | — | `QBF∀ k` (universal-first, `k` blocks) – at `k = 1`, coNP |
| **PH** | full second-order logic | — | — |
| **PSPACE** | SO(TC): second-order logic with a transitive closure taken over assignments of a block of relation variables | — | SUCCINCT-REACH (reachability in a transition system given by three CNF formulas over marked state variables) · QSAT (quantified Boolean formulas, the prefix carried by the instance) |
| **RE** | ∃SO[new]: ∃SO with value invention, the relation variables ranging over the universe extended by finitely many invented values | — | — |

The characterizations are the logical *definitions* of the classes (see the
Overview above).

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

* **More complete problems for PSPACE.** The class exists, defined by SO(TC)
  like the others and closed under FO reductions like the others, with
  `NP ⊆ PSPACE`, two complete problems (SUCCINCT-REACH and QSAT), `PSPACE =
  coPSPACE` and `PH ⊆ PSPACE`. What is planned next is the machine bridge for
  the class, plus the game problems (Generalized Geography…).
* **Complexity classes beyond PSPACE**, up toward EXPTIME/EXPSPACE, via the
  fixpoint logics that capture them (FO(PFP)/SO(LFP)) and their complete
  problems, each with a machine bridge as for NP and PTIME – the
  logarithmic-space classes already have theirs, in both directions. Below NP
  this also brings the P-complete problems (Circuit Value, alternating
  reachability).
* **Undecidability, by reduction.** The class RE exists today, defined
  logically like the others as `∃SO[new]` (table above) and closed under FO
  reductions like the others. What is planned is its complete problems — finite
  satisfiability (Trakhtenbrot's theorem) and Post's correspondence problem — so
  that incomputability results become ordinary first-order reductions, together
  with the bridge to Mathlib's computability layer that would let RE-hardness be
  read as undecidability.
* **Counting and optimization problems.** Only decision problems are modeled
  today. Planned: #P via counting second-order assignments (#SAT, #3COL, the
  permanent) and MaxSNP-style optimization classes — i.e. function and search
  problems, not just yes/no ones.
* **Unconditional lower bounds (inexpressibility).** The payoff unique to the
  descriptive approach, impossible in the machine world: Ehrenfeucht–Fraïssé
  games, EVEN and reachability not being FO-definable, `FO ⊊ FO(TC)` as a strict
  inclusion, locality, 0-1 laws, and eventually PARITY ∉ AC⁰.
* **Structural / capture theorems.** Immerman–Vardi (P = order-invariant
  FO(LFP)), Grädel's capture theorems, and Fagin's spectra connection.
* **A broader catalog and finer reductions.** More complete problems, and the
  finer reduction notions descriptive complexity uses (quantifier-free
  projections; FO(≤, BIT) = uniform AC⁰ as the bottom of the ordered world).

One caveat within this list: the `Δₖᵖ` levels of the polynomial hierarchy
(`Δₖᵖ = P^{Σₖ₋₁ᵖ}`, e.g. `Δ₂ᵖ = P^NP`). The `Σₖᵖ`/`Πₖᵖ` levels are in scope —
they are *defined* here by second-order quantifier alternation — but `Δₖᵖ` has
no such logical characterization: it is a deterministic class defined by bounded
oracle access, so capturing it faithfully would need the oracle-machine model
the framework deliberately avoids, and it may stay out of reach.

## Related projects

Other formalizations of complexity theory, and how they differ:

* **[Complexitylib](https://github.com/SamuelSchlesinger/complexitylib)** (Lean 4
  and Mathlib) is machine-model-first: `P` and `NP` are defined by time-bounded
  multi-tape Turing machines, and hardness is a polynomial-time many-one
  reduction whose reducing function is exhibited as a machine. It reaches
  results out of scope here, notably the deterministic time hierarchy theorem
  and a body of circuit lower bounds; its complete problems are SAT and 3SAT. It
  also contains a descriptive-complexity component, developed independently of
  this library and on its own foundations rather than Mathlib's `ModelTheory`.
* **[Karp21](https://github.com/wimmers/poly-reductions)** (Isabelle/HOL)
  formalizes polynomial-time reductions between Karp's problems, with running
  times accounted for in NREST; the public repository covers about eight of the
  21 (3CNF-SAT, Independent Set, Vertex Cover, Set Cover, Clique, Feedback Node
  Set, and the two Hamiltonian Cycle variants).
* **The Cook–Levin theorem** is mechanized against concrete models of
  computation by [Gäher and Kunze, ITP 2021](https://uds-psl.github.io/cook-levin/)
  in Coq/Rocq (call-by-value λ-calculus) and [Balbach, AFP
  2023](https://www.isa-afp.org/entries/Cook_Levin.html) in Isabelle/HOL
  (two-tape oblivious Turing machines). Here (`SAT_NP_complete`) it is proved
  for the logically defined `NP`, the identification with the machine class
  being a separate theorem.
* **[Cookbook reductions](https://doi.org/10.4230/LIPIcs.MFCS.2024.56)** (Grange,
  Vehlken, Vortmeier and Zeume, MFCS 2024) also specify reductions in
  first-order logic, but check them automatically in a teaching setting rather
  than in an interactive theorem prover.

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
