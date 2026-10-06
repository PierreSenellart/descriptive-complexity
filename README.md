# DescriptiveComplexity

[![CI](https://github.com/PierreSenellart/descriptive-complexity/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/PierreSenellart/descriptive-complexity/actions/workflows/ci.yml)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.34.0-blue)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.34.0)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21678423-007ec6)](https://doi.org/10.5281/zenodo.21678423)
[![arXiv](https://img.shields.io/badge/arXiv-2609.18261-b31b1b)](https://arxiv.org/abs/2609.18261)
[![Lax archive](https://img.shields.io/badge/Lax_archive-registered-555)](#lax-archive)
[![Archived in Software Heritage](https://archive.softwareheritage.org/badge/origin/https://github.com/PierreSenellart/descriptive-complexity/)](https://archive.softwareheritage.org/browse/origin/?origin_url=https://github.com/PierreSenellart/descriptive-complexity)

A Lean 4 library for descriptive complexity on top of Mathlib's `ModelTheory`,
in the style of Immerman (*Descriptive Complexity*, ch. 3). It rests on four
notions: a decision problem is an isomorphism-invariant predicate on finite
structures; a complexity class is defined by its logical characterization;
membership is shown by a definability witness; hardness is shown by a
first-order reduction from a known hard problem. No machine model is needed
for any of them, and a witness together with a reduction is a `Complete`
theorem. All declarations live in the `DescriptiveComplexity` namespace.

Complexity theory is essentially absent from general-purpose proof assistant
libraries because
its classical proofs are anchored to a machine model under resource bounds,
and such models resist mechanization: even once Cook–Levin is proved against
one, each further completeness result needs a proof that its reduction runs
within bounded resources. Descriptive complexity sidesteps this. Most
classical hardness reductions are first-order expressible, and a first-order
reduction is a Karp reduction, strictly weaker than the general one, so
hardness proved through it is the stronger statement; and it needs only
first-order logic, which Mathlib already has.

## Three layers

* **Problems and reductions.** A decision problem over a vocabulary is an
  isomorphism-invariant predicate on its structures; finiteness is a
  hypothesis of the theorems, not part of the semantics. A reduction is a
  tagged `dim`-dimensional first-order interpretation with a proof that it
  preserves the answer on finite nonempty structures. Tags supply the disjoint
  copies that textbook reductions take from an order, so the plain `≤ᶠᵒ` is
  order-free; `≤ᶠᵒ[≤]` may use a linear order, for gadgets that lay numbers
  along it, and the relativized `≤ʳᶠᵒ[≤]` also cuts the output universe down by
  domain formulas, for spanning problems. All three compose. Concrete instance
  types enter through a bundled `Encoding`, which requires polynomial size
  bounds in both directions; a computable `Decoding` reads well-formed
  structures back, so that hardness can be restricted to non-junk instances.
* **Complexity classes.** A class is built from a membership predicate by
  `ComplexityClass.ofMem`, against a proof that membership travels backward
  along reductions: a pullback lemma of the class's logic, one per logic,
  turning a relation variable over the output universe into a block of
  relation variables over the input, one per assignment of tags. The rewriting
  is atom by atom, so it preserves the Horn and Krom fragments: PTIME and NL
  close without leaving their logics. Hardness is then cofinality, and
  completeness the pair of a witness and a reduction. The degree `below Q₀` of
  a fixed problem is a class too, which expresses “GI-complete” without any
  logic.
* **Machines.** Machine models are theorems here, not definitions (see the
  table below). No machine is a Lean type: a machine is data in an instance of
  an acceptance problem, and its budget is a count of universe elements, the
  polynomial coming from the dimension of the reduction that built the
  instance.

## Results

* Cook–Levin, without a machine model (`SAT_NP_complete`) and in its textbook
  form (`SAT_complete_for_ntmAccept`), and all of Karp's 21 problems. Hardness
  enters the NP catalog once, at ∃SO → SAT (`sat_hard_of_sigmaSODefinable`);
  every other problem inherits it by composing reductions, membership being a
  separate definability witness per problem.
* Relations between classes, proved inside the logic rather than by machine
  simulation: the Immerman–Vardi theorem (`lfpDefinable_iff_mem_PTIME`), via
  Grädel's SO-Horn = FO(LFP); FO(PFP) = SO(TC) (`pfpDefinable_iff_mem_PSPACE`);
  NL = coNL by inductive counting (`NL_eq_coNL`), and `PSPACE_eq_coPSPACE`;
  each exponential class as the one below read over an exponential expansion
  (`PSPACE_eq_NL_exp` and its siblings); and the Abiteboul–Vianu theorem
  (`ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace`).
* Machine bridges: a problem is in the library's NP (resp. PTIME) exactly when
  it ordered-FO-reduces to acceptance by a nondeterministic (resp.
  deterministic) polynomial-time Turing machine (`mem_NP_iff_le_ntmAccept`,
  `mem_PTIME_iff_le_dtmAccept`); the other classes are matched against their
  machines in the table below.
* Counting: `#P` as the number of witnesses of an ∃SO sentence, with #SAT
  *parsimoniously* complete for it (`sharpSat_sharpP_parsimoniousComplete`), a
  stronger statement than the Turing completeness of the literature; under
  one-call reductions, the permanent (`sharpCycleCover_sharpP_oneCallComplete`,
  Valiant's theorem) and query evaluation over probabilistic databases. FP is
  defined by the quantitative logic of Arenas, Muñoz and Riveros, with its own
  complete problems. Both classes have their machine bridge.
* Lower bounds, none of them conditional on a complexity assumption:
  Ehrenfeucht–Fraïssé games on finite structures, and the inexpressibility of
  EVEN even when the sentence is given a linear order (`even_not_foDefinable`),
  whence `FO ⊊ FO(TC)` (`exists_tcDefinable_not_foDefinable`) and, since EVEN is
  definable once formulas may add ranks, `FO(≤) ⊊ AC⁰`
  (`exists_ac0Definable_not_foDefinable`). The same problem shows, by the
  `k`-pebble game, that order-free FO(IFP) does not capture PTIME
  (`exists_mem_PTIME_not_ifpDefinableFree`), so the linear order in the capture
  theorems cannot be dropped.
* First-order reductions are strictly weaker than the logarithmic-space ones,
  already at the deterministic many-one notion
  (`exists_dtcReduction_not_orderedReduction`); completeness under the weaker
  reduction is the stronger statement.
* AC⁰ is read here as the logic `FO(≤, +, ×)`; no circuit model is involved. It
  is proved to sit inside L (`ac0Definable_mem_LOGSPACE`), and to equal both
  `FO(≤, BIT)` and its machine model, logarithmic time with constantly many
  alternations (`ac0Definable_iff_ltDecidable`, both halves of Immerman's
  Thm 1.17), i.e., the logarithmic-time hierarchy rather than ALOGTIME.

## Complexity classes and complete problems

Each problem listed is proved complete for its class: both a member, and hard
for it under FO reductions.

| Complexity class | Logical characterization | Machine model | Problems proved complete |
| --- | --- | --- | --- |
| **L** = LOGSPACE | FO(≤, DTC) | deterministic two-way `k`-head automaton | REACHd · UNREACHd |
| **NL** | SO-Krom(≤); equivalently FO(≤, TC) | two-way `k`-head automaton | REACH · UNREACH · 2SAT |
| **PTIME** = Σ₀ᵖ = Π₀ᵖ | SO-Horn(≤); equivalently FO(≤, LFP) or FO(≤, IFP) | deterministic polynomial-time Turing machine | HORN-SAT · CVP (circuit value) · GAME (alternating reachability) · acceptance by a deterministic polynomial-time Turing machine |
| **NP** = Σ₁ᵖ | ∃SO; equivalently ∃SO[new, d], value invention bounded by the instance's `d`-tuples | nondeterministic polynomial-time Turing machine | **SAT-family:** SAT · 3SAT · NAE-SAT · NAE-3SAT · 1-in-SAT<br>**Coloring:** 3-Colorability · `k`-Colorability (`k ≥ 3`) · Chromatic Number · Clique Cover<br>**Cliques & subgraphs:** Clique · Independent Set · Vertex Cover · Subgraph Isomorphism<br>**Sets & hypergraphs:** Set Cover · Hitting Set · Set Packing · Exact Cover · Set Splitting · Dominating Set · 3-Dimensional Matching<br>**Graphs:** Feedback Vertex Set · Feedback Arc Set · Steiner Tree (node- & edge-weighted) · Max Cut · Hamilton Circuit (directed & undirected)<br>**Numbers (in binary):** Knapsack · Partition · 0-1 Integer Programming · Job Sequencing<br>**Machines:** acceptance by a nondeterministic polynomial-time Turing machine |
| **coNP** = Π₁ᵖ | ∀SO | the same machine, accepting when *every* run does | TAUT · 3-DNF-TAUT · 3-UNSAT · acceptance by such a machine |
| **DP** | a Σ₁ and a Π₁ sentence conjoined | – | SAT-UNSAT |
| **Σₖᵖ** (`k ≥ 1`) | Σₖ¹: `k` alternating second-order quantifier blocks, existential first | alternating polynomial-time Turing machine, `k` blocks, existential first | `QBF k` (quantified Boolean formulas, `k` blocks) · acceptance by such a machine |
| **Πₖᵖ** (`k ≥ 1`) | Πₖ¹: `k` alternating second-order quantifier blocks, universal first | the same machine, universal first | `QBF∀ k` (universal-first, `k` blocks) · acceptance by such a machine |
| **PH** | SO | – | – |
| **PSPACE** | SO(TC); equivalently FO(≤, PFP) | polynomial-space Turing machine, deterministic or not | SUCCINCT-REACH · QSAT · acceptance by a space-bounded Turing machine (deterministic & not) |
| **EXPTIME** | SO(LFP), i.e., PTIME read over an exponential expansion; equivalently SO-GAME, a second-order alternating game | alternating polynomial-space Turing machine | acceptance by such a machine (`APSPACE = EXPTIME`) |
| **NEXPTIME** | ∃SO over an exponential expansion (NP read there); equivalently ∃SO[new, exp], value invention bounded exponentially | wide machine, clocked | acceptance by such a machine within its clock · tiling a wide square (the `2ⁿ × 2ⁿ` tiling) |
| **EXPSPACE** | SO(PFP), i.e., PSPACE read over an exponential expansion | wide machine, space-bounded | acceptance by such a machine in bounded space (deterministic & not) · tiling a wide corridor (width `2ⁿ`, unbounded height) |
| **RE** | ∃SO[new] (∃SO with value invention, unbounded) | Turing machine, no step or space bound | FINSAT (Trakhtenbrot's theorem) · CODEHALT · HALT · PCP (Post's correspondence problem) |
| **the degree of a problem** – `below Q₀`, e.g., **GI** | none: a downward closure under FO reductions rather than a logic | – | for GI: Graph Isomorphism · Digraph Isomorphism · DAG Isomorphism |

Two of the models are named rather than described: both head automata walk a
linear order of the universe, and a *wide* machine carries its control in the
instance while its tape is addressed by an exponential expansion of it. Each
entry of the machine column is an equivalence proved here between the logical
definition and acceptance by that model. The classes are also matched against
Mathlib's computability layer: RE is recursive enumerability, every RE-hard
problem is undecidable, and RE ≠ co-RE.

The last row states completeness against a problem instead of a logic, which is
what “GI-complete” means. It agrees with the logical definitions where both
apply: `NP = below SAT`, `PTIME = below HORN-SAT` and their siblings are
theorems, so SAT-hardness is NP-hardness.

### Classes of functions

Here a problem attaches a number to each instance. Completeness is under
*parsimonious* reductions, which preserve the number, unless stated otherwise.

| Class | Logical characterization | Machine model | Problems proved complete |
| --- | --- | --- | --- |
| **FP** | QFO(LFP): sums and products of polynomial-time conditions; equivalently, binary digits computed by a least fixed point | deterministic polynomial-time Turing machine writing a number | the number written by a circuit · by unit propagation on a Horn formula · by such a machine |
| **#P** | the number of witnesses of an ∃SO sentence, equivalently a term of ΣQSO(FO) | nondeterministic polynomial-time Turing machine, counting its accepting runs | **SAT-family:** #SAT · #3SAT · #1-in-SAT<br>**Solutions of the threshold size:** #Clique · #Independent Set · #Vertex Cover · #Set Packing · #Set Cover · #Hitting Set · #Dominating Set · #Feedback Vertex Set · #Feedback Arc Set · #Steiner Tree<br>**Others:** #Exact Cover · #Knapsack · #0-1 Integer Programming · #Hamilton Circuit (directed & undirected) · counting the accepting runs of such a machine<br>**Under weaker reductions:** #DNF · #2SAT · #HORN-SAT · #Monotone-2SAT · #NAE-SAT · #Set Splitting · #3-Colorability · counting all independent sets or vertex covers · #BIS · #PP2DNF · the permanent (#Cycle Cover) |

The decision classes defined by a property of such a count, ⊕P, Mod_k P, PP,
C₌P and UP, are defined too, with the inclusions between them and NP, coNP,
and one complete problem each where one is known (⊕SAT, Mod_k-SAT, and for
PP and C₌P the comparison of the models of a CNF formula by the value of a
selected variable).

## Scope

These limitations are *intrinsic* to the machine-free approach; for what is
merely not built yet, see `ROADMAP.md`.

* **Complexity of problems, not of algorithms.** No cost model, hence no
  `O(·)`, no fine-grained complexity, no Δₖᵖ, and no hierarchy theorem:
  separating DTIME(f) from DTIME(2^f) is a statement about a clock, and there
  is none here to diagonalize against. What you prove is membership, hardness
  and completeness for the coarse classes above.
* **Instances are finite relational structures, not strings.** Strings come
  ordered and structures do not, so order-invariance is an explicit variant
  here, and theorems whose whole content is the *absence* of an order become
  statable. The machine bridges characterize the classes from inside the
  framework: from PTIME up by acceptance problems whose instances carry the
  machine, at L, NL and AC⁰ by a single machine, fixed once, deciding every
  instance. Their agreement with the usual presentations over string encodings
  is classical (Fagin; Immerman–Vardi) and is not formalized here – except for
  RE, where `mem_RE_iff_rePred` identifies the class with Mathlib's `REPred` on
  an encoding of finite structures.
* **The reduction must be expressible in logic.** A poly-time reduction that is
  not FO-expressible cannot be used; gadgets often need a linear order, tags or
  extra dimensions, and arithmetic inside formulas is limited (addition and
  comparison are FO(≤); multiplication is not FO, being as hard as majority
  under constant-depth reductions, Vollmer 1999, Cor. 1.39 and 3.34). In
  practice no problem had to be dropped for this reason.

## Authorship, sources, and axioms

Almost none of the mathematics here is new. Most theorems are classical
and each module docstring names the source it follows. What is original
is the Lean formalization. **If a result here is traceable to a paper or
a textbook whose citation is missing, that is an oversight: please open
an issue.**

Lean code, including most proofs and docstrings, was written with the
assistance of various generative models from Anthropic (*Claude*).
Formalization choices, the library architecture, the main definitions and
theorems, and their alignment with the standard ones, were designed and
written or reviewed by the author. Responsibility for the whole rests
with the author.

All proofs are checked by Lean, locally and in continuous integration.
The library does not depend on any axioms apart from standard Lean ones:
`propext`, `Classical.choice` and `Quot.sound`. Neither `sorry`,
`admit`, nor `native_decide` is used.

## Related projects

* **[Complexitylib](https://github.com/SamuelSchlesinger/complexitylib)** (Lean 4
  and Mathlib) is machine-model-first: its classes are defined by resource-bounded
  multi-tape Turing machines, and hardness is a polynomial-time many-one
  reduction exhibited as a machine. It reaches results out of scope here,
  notably the deterministic time hierarchy theorem and circuit lower bounds;
  its complete problems are SAT and 3SAT for NP and the complement of SAT for
  coNP. Its descriptive-complexity component, first- and second-order syntax
  with one-dimensional first-order reductions, stands on its own foundations
  rather than Mathlib's `ModelTheory`, and no class is defined through it.
* **[poly-reductions](https://github.com/rosskopfs/poly-reductions)**
  (Isabelle/HOL, formerly Karp21) formalizes polynomial-time reductions between
  26 problems, all of Karp's 21 among them, with running times accounted for in
  NREST; the tree is rooted at SAT, whose NP-hardness is assumed rather than
  proved.
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
| `v1.3.0` | `v4.34.0` | `leanprover/lean4:v4.34.0` |
| `v1.2.2` | `v4.33.0` | `leanprover/lean4:v4.33.0` |
| `v1.2.1` | `v4.33.0` | `leanprover/lean4:v4.33.0` |
| `v1.2.0` | `v4.33.0` | `leanprover/lean4:v4.33.0` |
| `v1.1.0` | `v4.33.0-rc1` | `leanprover/lean4:v4.33.0-rc1` |
| `v1.0.0` | `v4.33.0-rc1` | `leanprover/lean4:v4.33.0-rc1` |
| `master` | latest pin, moves | see `lean-toolchain` |

Version numbers are the library's own and follow [semantic
versioning](https://semver.org/); the `lean-toolchain` file at each tag is
authoritative for the pin. A **patch** release keeps the Mathlib pin it was cut
against, and **a new pin always takes at least a minor bump** – so depend on
`~1.0.0`, which stays within a single pin, rather than on `^1.0.0`.

The package is indexed on
[Reservoir](https://reservoir.lean-lang.org/@PierreSenellart/descriptive-complexity),
so it can be required by name. In a `lakefile.toml`:

```toml
[[require]]
name = "descriptive-complexity"
scope = "PierreSenellart"
version = "~1.3.0"
```

or, in a `lakefile.lean`:

```lean
require "PierreSenellart" / "descriptive-complexity" @ "~1.3.0"
```

What follows `@` is a version *range*, not a version: Lake rejects a bare
number there.

To pin a commit, or to follow `master`, require it from git instead:

```toml
[[require]]
name = "descriptive-complexity"
git = "https://github.com/PierreSenellart/descriptive-complexity"
rev = "v1.3.0"
```

```lean
require "descriptive-complexity" from git
  "https://github.com/PierreSenellart/descriptive-complexity" @ "v1.3.0"
```

Pin a version tag or a commit hash rather than `master`, for reproducible
builds. Then `import DescriptiveComplexity` brings in the whole library; import
individual modules (for instance `DescriptiveComplexity.Problems.Sat`) to keep
build times down.

## Documentation

* **Paper**: P. Senellart and A. Gnatenko, *Descriptive Complexity in Lean:
  Completeness by First-Order Reductions*, September 2026,
  [arXiv:2609.18261](https://arxiv.org/abs/2609.18261) – the design of the
  library and its main results. To cite the library, cite this paper;
  `CITATION.cff` has the metadata, and the DOI above identifies the software
  itself.
* **API reference**:
  <https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>
  – the `DescriptiveComplexity` module page is a part-by-part map of the library,
  and every declaration is documented on its own page. Rebuilt from `master` on
  every push.
* **Tutorials**: `DescriptiveComplexity/Examples/ConjunctiveQueries.lean` and
  `DescriptiveComplexity/Examples/GraphCrawling.lean`, worked examples read top
  to bottom, each walking through a new problem domain in the order a user meets
  it (concrete problem → encoding → vocabulary and semantics → faithfulness →
  membership → hardness → completeness). The shortest instance of the same
  loop is `DescriptiveComplexity/Problems/SubgraphIso.lean` with its
  `SubgraphIso/Encoding.lean`: a catalog problem, then its concrete encoding
  and a decoder with no well-formedness condition.
  A third one, `DescriptiveComplexity/Examples/ProbabilisticQueries.lean`, does
  the same for a counting problem, query evaluation over probabilistic
  databases, ending with a concrete database type, its computed weighted
  count, its faithful encoding and a decoder, and closing on a query of the
  easy side, in FP.
* **Planned work**: `ROADMAP.md` – locality theorems and 0-1 laws for the
  inexpressibility track, the graph-isomorphism degree, counting problems and
  `#P`, finer reduction notions, and further complete problems for PTIME,
  PSPACE and the exponential classes.

## Lax archive

Parts of the library are registered in the [Lax
archive](https://laxarchive.org/), the archive for machine-checked mathematics,
as submissions whose concepts restate the library's definitions and state its
theorems, and whose proofs are the library's own, sliced to what those
statements use. Each submission is frozen at one library version on the
archive's Lean environment of the time; the commit it was registered from
carries the submission's id as a tag.

| Submission | Statements | Library | Environment |
| --- | --- | --- | --- |
| [lax-904597](https://laxarchive.org/lax-904597/) | The Cook–Levin theorem ([`CookLevin`](https://laxarchive.org/lax-904597/Lax904597.CookLevin.html)), its machine form ([`MachineForm`](https://laxarchive.org/lax-904597/Lax904597.MachineForm.html)), the closure laws of NP ([`NPClass`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html)); concepts for decision problems, first-order interpretations and reductions, second-order definability, complexity classes with cofinal hardness, SAT and machine acceptance | `v1.2.2` | Lean `v4.33.0` |
| [lax-799700](https://laxarchive.org/lax-799700/) | A catalog of thirty NP-complete problems, one concept module per family with the problem, its invariance, its characterization and its NP-completeness as statements: Karp's twenty-one (SAT in the core), 3SAT, NAE-SAT, NAE-3SAT, 1-in-SAT, Independent Set, Dominating Set, Subgraph Isomorphism, Set Splitting, the edge-weighted Steiner tree, 3-colorability and `k`-colorability ([the module list](https://laxarchive.org/lax-799700/)); the proofs assume the core's statements, so the archive's proof network is the reduction tree | `v1.2.2` | Lean `v4.33.0` |
| [lax-117614](https://laxarchive.org/lax-117614/) | Graph crawling is NP-complete ([`GraphCrawlingNPComplete`](https://laxarchive.org/lax-117614/Lax117614.GraphCrawlingNPComplete.html)), Proposition 4 of the EDBT 2026 paper, whose extended version is carried and marked; the packaged instances, their faithful and size-honest encoding, the decoder, and NP-completeness on well-formed websites ([`CrawlDecoding`](https://laxarchive.org/lax-117614/Lax117614.CrawlDecoding.html)) | `v1.2.2` | Lean `v4.33.0` |
| [lax-624099](https://laxarchive.org/lax-624099/) | RE as the class definable with value invention; FINSAT, CODEHALT, HALT and PCP RE-complete ([`FinsatREComplete`](https://laxarchive.org/lax-624099/Lax624099.FinsatREComplete.html) and siblings); RE as Mathlib's recursive enumerability ([`REIsRecursivelyEnumerable`](https://laxarchive.org/lax-624099/Lax624099.REIsRecursivelyEnumerable.html)); RE-hard problems undecidable, Trakhtenbrot's theorem ([`Trakhtenbrot`](https://laxarchive.org/lax-624099/Lax624099.Trakhtenbrot.html)), the halting problems and PCP undecidable, RE ≠ co-RE, NP ⊆ RE; 26 concepts, one per statement | `v1.2.2` | Lean `v4.33.0` |
| [lax-420092](https://laxarchive.org/lax-420092/) | Boolean conjunctive query evaluation and containment are NP-complete ([`EvaluationNPComplete`](https://laxarchive.org/lax-420092/Lax420092.EvaluationNPComplete.html), [`ContainmentNPComplete`](https://laxarchive.org/lax-420092/Lax420092.ContainmentNPComplete.html)), the Chandra–Merlin theorem ([`ChandraMerlin`](https://laxarchive.org/lax-420092/Lax420092.ChandraMerlin.html)), the reductions between the two problems, the faithful encoding of packaged instances, the decoder and completeness on well-formed instances; 12 concepts, one per statement | `v1.2.2` | Lean `v4.33.0` |
| [lax-485149](https://laxarchive.org/lax-485149/) | NL as the class definable in the Krom fragment and L as the class definable in FO(DTC); the Immerman–Szelepcsényi theorem for FO(TC) ([`ImmermanSzelepcsenyi`](https://laxarchive.org/lax-485149/Lax485149.ImmermanSzelepcsenyi.html)), NL = FO(TC) ([`NLIsTransitiveClosure`](https://laxarchive.org/lax-485149/Lax485149.NLIsTransitiveClosure.html)), NL = coNL ([`NLEqCoNL`](https://laxarchive.org/lax-485149/Lax485149.NLEqCoNL.html)), L = coL, L ⊆ NL ⊆ NP; REACH, UNREACH and 2SAT NL-complete ([`ReachNLComplete`](https://laxarchive.org/lax-485149/Lax485149.ReachNLComplete.html) and siblings), REACHd and UNREACHd L-complete; NL and L as acceptance by two-way multihead automata ([`NLByAutomata`](https://laxarchive.org/lax-485149/Lax485149.NLByAutomata.html), [`LByAutomata`](https://laxarchive.org/lax-485149/Lax485149.LByAutomata.html)); 34 concepts, one per statement | `v1.2.2` | Lean `v4.33.0` |
| [lax-535992](https://laxarchive.org/lax-535992/) | PTIME as the class definable in the Horn fragment; SO-Horn = FO(LFP) and the Immerman–Vardi theorem ([`ImmermanVardi`](https://laxarchive.org/lax-535992/Lax535992.ImmermanVardi.html)), FO(LFP) closed under complement, PTIME = coPTIME, FO(≤, IFP) = PTIME ([`InflationaryIsLeastFixedPoint`](https://laxarchive.org/lax-535992/Lax535992.InflationaryIsLeastFixedPoint.html)); HORN-SAT, CVP and GAME PTIME-complete ([`HornSatPTIMEComplete`](https://laxarchive.org/lax-535992/Lax535992.HornSatPTIMEComplete.html) and siblings), deterministic machine acceptance PTIME-complete with PTIME as reducibility to it ([`DeterministicMachinePTIMEComplete`](https://laxarchive.org/lax-535992/Lax535992.DeterministicMachinePTIMEComplete.html)); PTIME ⊆ NP, L ⊆ NL ⊆ PTIME; 24 concepts, one per statement | `v1.2.2` | Lean `v4.33.0` |
| [lax-564036](https://laxarchive.org/lax-564036/) | The polynomial hierarchy as logically defined levels, with PTIME and coPTIME at level 0, coNP, PH and DP; Πₖ = co-Σₖ ([`HierarchyDuality`](https://laxarchive.org/lax-564036/Lax564036.HierarchyDuality.html)), the levels nested ([`HierarchyInclusions`](https://laxarchive.org/lax-564036/Lax564036.HierarchyInclusions.html)), PTIME ⊆ coNP ([`PolynomialTimeInHierarchy`](https://laxarchive.org/lax-564036/Lax564036.PolynomialTimeInHierarchy.html)), NP ∪ coNP ⊆ DP ⊆ Σ₂ ∩ Π₂; TAUT, 3-DNF-TAUT and 3-UNSAT coNP-complete, SAT-UNSAT DP-complete, QBF with k blocks complete for each level ([`QbfComplete`](https://laxarchive.org/lax-564036/Lax564036.QbfComplete.html)); each level by alternating Turing machines ([`AlternatingMachineComplete`](https://laxarchive.org/lax-564036/Lax564036.AlternatingMachineComplete.html)); 23 concepts, one per statement | `v1.2.2` | Lean `v4.33.0` |
| [lax-895169](https://laxarchive.org/lax-895169/) | AC⁰ as definability in FO(≤, +, ×); FO(≤, +, ×) = FO(≤, +, BIT) ([`ACZeroIsBitLogic`](https://laxarchive.org/lax-895169/Lax895169.ACZeroIsBitLogic.html)), AC⁰ as the logarithmic-time hierarchy ([`ACZeroIsLogTime`](https://laxarchive.org/lax-895169/Lax895169.ACZeroIsLogTime.html)), closure under complement, FO(≤) ⊆ AC⁰, AC⁰ ⊆ L ⊆ NL ([`ACZeroInLogSpace`](https://laxarchive.org/lax-895169/Lax895169.ACZeroInLogSpace.html)) and AC⁰ ⊆ PTIME through FO(LFP) and FO(≤, IFP) ([`ACZeroInPTIME`](https://laxarchive.org/lax-895169/Lax895169.ACZeroInPTIME.html)); 11 concepts, one per statement | `v1.2.2` | Lean `v4.33.0` |

A submission building on these notions can require the concept package of
the earlier one instead of restating them. The submissions live under `lax/`
in this repository, one folder each, which the archive reads at a commit and
a path; the folder is kept out of release archives. Each is generated by
[lax-export](https://github.com/PierreSenellart/lax-export) from its
`export.yaml`, the concept and bridge modules being written by hand, and the
docstring of a registered theorem names its statement in the archive.

## Building

The toolchain in `lean-toolchain` must match the pinned Mathlib version.

```
lake exe cache get   # fetch Mathlib build cache
lake build
```
