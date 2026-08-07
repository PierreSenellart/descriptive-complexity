# DescriptiveComplexity

[![CI](https://github.com/PierreSenellart/descriptive-complexity/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/PierreSenellart/descriptive-complexity/actions/workflows/ci.yml)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.33.0--rc1-blue)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.33.0-rc1)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21678423-007ec6)](https://doi.org/10.5281/zenodo.21678423)
[![Archived in Software Heritage](https://archive.softwareheritage.org/badge/origin/https://github.com/PierreSenellart/descriptive-complexity/)](https://archive.softwareheritage.org/browse/origin/?origin_url=https://github.com/PierreSenellart/descriptive-complexity)

A Lean 4 library for descriptive complexity on top of Mathlib's `ModelTheory`,
in the style of Immerman (*Descriptive Complexity*, ch. 3). Every complexity
class is *defined* logically, so membership, hardness and completeness proofs
need no machine model: a definability witness for membership, a first-order
reduction for hardness, and the framework closes them into a `Complete`
theorem. Along the way the library proves a number of results of complexity and
descriptive complexity themselves. All declarations live in the
`DescriptiveComplexity` namespace.

Complexity theory is essentially absent from Mathlib because formalizing a
model of computation with resource bounds is hard. But most classical hardness
reductions do not need the full power of PTIME: they are *first-order
expressible*. An FO reduction is computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, so
exhibiting one is strictly stronger than exhibiting a Karp reduction, while
requiring only first-order logic, which Mathlib already has.

## Three layers

* **Model theory.** A decision problem is an isomorphism-invariant property of
  finite structures over a chosen vocabulary. You can also bring your own
  concrete instance types: a bundled `Encoding` cannot be constructed without
  proving polynomial size bounds in both directions (no padding, no
  compression), and computable `Decoding`s read well-formed structures back, so
  completeness theorems restrict to the non-junk instances in one line.
* **Complexity classes.** Classes are logically defined and closed under FO
  reductions by construction: the polynomial hierarchy by second-order
  quantifier alternation, PTIME by the Horn fragment, NL by the Krom fragment,
  PSPACE by second-order transitive closure, RE by value invention, with the
  fixed-point logics FO(LFP)/FO(IFP)/FO(PFP) alongside. Machine models are
  *theorems* here, not definitions (see the table below). Completeness without
  a class is available too: the downward closure `below Q₀` of a fixed problem
  is itself a class, so “GI-complete” is expressible with no logic anywhere.
* **Reductions.** Tagged `dim`-dimensional first-order interpretations between
  languages give the reduction `≤ᶠᵒ`, with its order-invariant variant `≤ᶠᵒ[≤]`
  for gadgets that genuinely need a linear order and a relativized variant
  `≤ʳᶠᵒ[≤]` for problems whose target domain is definable; all are closed under
  composition. The problem catalog is one problem per file – vocabulary,
  reductions, completeness theorem – with tutorial-style worked examples.

Highlights: a machine-free **Cook–Levin** theorem, **all of Karp's 21
problems**, the **Immerman–Vardi** theorem (`lfpDefinable_iff_mem_PTIME`), the
**Abiteboul–Vianu** theorem
(`ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace`), and the *machine
bridge*: a problem is in the library's NP (resp. PTIME) exactly when it
ordered-FO-reduces to acceptance by a nondeterministic (resp. deterministic)
polynomial-time Turing machine (`mem_NP_iff_le_ntmAccept`,
`mem_PTIME_iff_le_dtmAccept`).

And the payoff no machine-first development has, **unconditional lower
bounds**: Ehrenfeucht–Fraïssé games on finite structures, and the
inexpressibility of EVEN even when the sentence is handed a linear order
(`even_not_foDefinable`), whence **`FO ⊊ FO(TC)`** proved outright
(`exists_tcDefinable_not_foDefinable`). The same problem shows, by the
`k`-pebble game, that **order-free FO(IFP) does not capture PTIME**
(`exists_mem_PTIME_not_ifpDefinableFree`), so the linear order in the capture
theorems is not a convenience. No complexity assumption enters any of this.

## Complexity classes and complete problems

Each problem listed is proved **complete** for its class: both a member, and
hard for it under FO reductions.

| Complexity class | Logical characterization | Machine model | Problems proved complete |
| --- | --- | --- | --- |
| **L** = LOGSPACE | FO(≤, DTC) | deterministic two-way `k`-head automaton, walking a linear order of the universe | REACHd · UNREACHd |
| **NL** | SO-Krom(≤); equivalently FO(≤, TC) | two-way `k`-head automaton, walking a linear order of the universe | REACH · UNREACH · 2SAT |
| **PTIME** = Σ₀ᵖ = Π₀ᵖ | SO-Horn(≤); equivalently FO(≤, LFP) or FO(≤, IFP) | deterministic polynomial-time Turing machine | HORN-SAT · CVP (circuit value) · acceptance by a deterministic polynomial-time Turing machine |
| **NP** = Σ₁ᵖ | ∃SO | nondeterministic polynomial-time Turing machine | **SAT-family:** SAT · 3SAT · NAE-SAT · NAE-3SAT · 1-in-SAT<br>**Coloring:** 3-Colorability · `k`-Colorability (`k ≥ 3`) · Chromatic Number · Clique Cover<br>**Cliques & subgraphs:** Clique · Independent Set · Vertex Cover · Subgraph Isomorphism<br>**Sets & hypergraphs:** Set Cover · Hitting Set · Set Packing · Exact Cover · Set Splitting · Dominating Set · 3-Dimensional Matching<br>**Graphs:** Feedback Vertex Set · Feedback Arc Set · Steiner Tree (node- & edge-weighted) · Max Cut · Hamilton Circuit (directed & undirected)<br>**Numbers (in binary):** Knapsack · Partition · 0-1 Integer Programming · Job Sequencing<br>**Machines:** acceptance by a nondeterministic polynomial-time Turing machine |
| **coNP** = Π₁ᵖ | ∀SO | nondeterministic polynomial-time Turing machine, accepting when *every* run does | TAUT · 3-DNF-TAUT · 3-UNSAT · acceptance by such a machine |
| **DP** | a Σ₁ and a Π₁ sentence conjoined | – | SAT-UNSAT |
| **Σₖᵖ** (`k ≥ 1`) | Σₖ¹: `k` alternating second-order quantifier blocks, existential first | alternating polynomial-time Turing machine with `k` blocks, existential first | `QBF k` (quantified Boolean formulas, `k` blocks) · acceptance by such a machine |
| **Πₖᵖ** (`k ≥ 1`) | Πₖ¹: `k` alternating second-order quantifier blocks, universal first | the same machine, universal first | `QBF∀ k` (universal-first, `k` blocks) · acceptance by such a machine |
| **PH** | SO | – | – |
| **PSPACE** | SO(TC); equivalently FO(≤, PFP) | polynomial-space Turing machine, deterministic or not | SUCCINCT-REACH · QSAT · acceptance by a space-bounded Turing machine (deterministic & not) |
| **EXPTIME** | SO(≤, LFP), i.e. PTIME read over an exponential expansion | – | – |
| **NEXPTIME** | ∃SO over an exponential expansion (NP read there) | – | – |
| **EXPSPACE** | SO(≤, PFP), i.e. PSPACE read over an exponential expansion | – | – |
| **RE** | ∃SO[new] (∃SO with value invention) | Turing machine with no step bound and no space bound | FINSAT (Trakhtenbrot's theorem) · CODEHALT · HALT · PCP (Post's correspondence problem) |
| **the degree of a problem** – `below Q₀`, e.g. **GI** | none: a downward closure under FO reductions rather than a logic | – | for GI: Graph Isomorphism · Digraph Isomorphism · DAG Isomorphism |

The three exponential classes are read over a universe that is one exponential
larger – a definable set of assignments of a second-order block – and their
structural theorems are inherited rather than reproved: `EXPTIME = coEXPTIME`
and `EXPSPACE = coEXPSPACE` come from closure of PTIME and PSPACE under
complement, and `PSPACE ⊆ EXPTIME ⊆ NEXPTIME ⊆ EXPSPACE` from the corresponding
polynomial-level inclusions. Complete problems for them are not built yet.

Each entry of the machine column is an equivalence *proved here* between the
logical definition and acceptance by that model. The classes are also matched
against Mathlib's computability layer: RE *is* recursive enumerability, every
RE-hard problem is undecidable, and RE ≠ co-RE.

The last row states completeness against a *problem* instead of a logic, which
is what “GI-complete” means. It agrees with the logical definitions where both
apply: `NP = below SAT`, `PTIME = below HORN-SAT` and their siblings are
theorems, so SAT-hardness *is* NP-hardness.

## Scope

These limitations are *intrinsic* to the machine-free approach; for what is
merely not built yet, see `ROADMAP.md`.

* **Complexity of problems, not of algorithms.** No cost model, no `O(·)`, no
  fine-grained complexity: what you prove is membership, hardness and
  completeness for the coarse classes above.
* **Instances are finite relational structures, not strings.** The machine
  bridges characterize the classes from inside the framework, by acceptance
  problems whose instances carry the machine; their agreement with the usual
  presentations over string encodings is classical (Fagin; Immerman–Vardi) and
  is not formalized here.
* **The reduction must be expressible in logic.** A poly-time reduction that is
  not FO-expressible cannot be used; gadgets often need a linear order, tags or
  extra dimensions, and arithmetic inside formulas is limited (addition and
  comparison are FO(≤); multiplication is not FO).
* **Completeness and structure, not class separations.** Whether P = NP and the
  like is open mathematics the framework does not decide. Separations between
  *logics* are in scope, and proved (see above).

## Related projects

* **[Complexitylib](https://github.com/SamuelSchlesinger/complexitylib)** (Lean 4
  and Mathlib) is machine-model-first: `P` and `NP` are defined by time-bounded
  multi-tape Turing machines, and hardness is a polynomial-time many-one
  reduction exhibited as a machine. It reaches results out of scope here, notably
  the deterministic time hierarchy theorem and circuit lower bounds; its complete
  problems are SAT and 3SAT. Its descriptive-complexity component was developed
  independently of this library, on its own foundations rather than Mathlib's
  `ModelTheory`.
* **[Karp21](https://github.com/wimmers/poly-reductions)** (Isabelle/HOL)
  formalizes polynomial-time reductions between Karp's problems, with running
  times accounted for in NREST; the public repository covers about eight of the 21.
* **The Cook–Levin theorem** is mechanized against concrete models of computation
  by [Gäher and Kunze, ITP 2021](https://uds-psl.github.io/cook-levin/) in
  Coq/Rocq (call-by-value λ-calculus) and [Balbach, AFP
  2023](https://www.isa-afp.org/entries/Cook_Levin.html) in Isabelle/HOL
  (two-tape oblivious Turing machines). Here (`SAT_NP_complete`) it is proved for
  the logically defined `NP`, the identification with the machine class being a
  separate theorem.
* **[Cookbook reductions](https://doi.org/10.4230/LIPIcs.MFCS.2024.56)** (Grange,
  Vehlken, Vortmeier and Zeume, MFCS 2024) also specify reductions in first-order
  logic, but check them automatically in a teaching setting rather than in an
  interactive theorem prover.

## Use as a dependency

Lake builds a single Mathlib per workspace, so pick the release whose Mathlib
pin is the *same* as your project's, not merely a compatible one.

| DescriptiveComplexity | Mathlib | Toolchain |
| --- | --- | --- |
| `v1.1.0` | `v4.33.0-rc1` | `leanprover/lean4:v4.33.0-rc1` |
| `v1.0.0` | `v4.33.0-rc1` | `leanprover/lean4:v4.33.0-rc1` |
| `master` | latest pin, moves | see `lean-toolchain` |

Version numbers are the library's own and follow [semantic
versioning](https://semver.org/); the `lean-toolchain` file at each tag is
authoritative for the pin. A **patch** release keeps the Mathlib pin it was cut
against, and **a new pin always takes at least a minor bump** – so depend on
`~1.0.0`, which stays within a single pin, rather than on `^1.0.0`.

In a `lakefile.toml`:

```toml
[[require]]
name = "descriptive-complexity"
git = "https://github.com/PierreSenellart/descriptive-complexity"
rev = "v1.1.0"
```

or, in a `lakefile.lean`:

```lean
require "descriptive-complexity" from git
  "https://github.com/PierreSenellart/descriptive-complexity" @ "v1.1.0"
```

Pin a version tag or a commit hash rather than `master`, for reproducible
builds. Then `import DescriptiveComplexity` brings in the whole library; import
individual modules (for instance `DescriptiveComplexity.Problems.Sat`) to keep
build times down.

## Documentation

* **API reference**:
  <https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>
  – the `DescriptiveComplexity` module page is a part-by-part map of the library,
  and every declaration is documented on its own page. Rebuilt from `master` on
  every push.
* **Tutorials**: `DescriptiveComplexity/Examples/ConjunctiveQueries.lean` and
  `DescriptiveComplexity/Examples/GraphCrawling.lean`, worked examples read top
  to bottom, each walking through a new problem domain in the order a user meets
  it (concrete problem → encoding → vocabulary and semantics → faithfulness →
  membership → hardness → completeness).
* **Planned work**: `ROADMAP.md` – classes beyond PSPACE, counting and
  optimization problems, more inexpressibility results, finer reduction notions.

## Building

The toolchain in `lean-toolchain` must match the pinned Mathlib version.

```
lake exe cache get   # fetch Mathlib build cache
lake build
```
