/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Ordered
import DescriptiveComplexity.Composition
import DescriptiveComplexity.OrderedComposition
import DescriptiveComplexity.Complexity
import DescriptiveComplexity.SecondOrder
import DescriptiveComplexity.SecondOrderLift
import DescriptiveComplexity.SecondOrderPull
import DescriptiveComplexity.SecondOrderOrdered
import DescriptiveComplexity.SecondOrderMerge
import DescriptiveComplexity.SecondOrderHorn
import DescriptiveComplexity.SecondOrderHornPull
import DescriptiveComplexity.FixedPoint
import DescriptiveComplexity.OrderWalk
import DescriptiveComplexity.FixedPointHorn
import DescriptiveComplexity.Hierarchy
import DescriptiveComplexity.Padding
import DescriptiveComplexity.OccurrenceOrder
import DescriptiveComplexity.OccurrenceFormulas
import DescriptiveComplexity.OccurrenceSlack
import DescriptiveComplexity.OccurrenceVar
import DescriptiveComplexity.Numbers
import DescriptiveComplexity.Machines
import DescriptiveComplexity.Problems
import DescriptiveComplexity.Examples

/-!
# Descriptive complexity in Lean 4

A library for descriptive complexity built on Mathlib's `ModelTheory`:
machine-model-free hardness reductions and a logically-defined polynomial
hierarchy, in the style of Immerman's *Descriptive Complexity*
([Immerman 1999][immerman1999descriptive]).

Complexity theory is largely absent from Mathlib because formalizing a model
of computation with resource bounds is hard. The observation this library
rests on is that many classical NP-hardness reductions do not need the full
strength of a Turing machine: they are *first-order expressible*. An FO
reduction is computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, so exhibiting one is
strictly stronger than exhibiting a Karp reduction
([Karp 1972][karp1972reducibility]), while needing no machine model at all –
only first-order logic, which Mathlib already provides.

This page is the high-level map of the library, part by part. The `README`
gives the general pitch; the worked example in
`DescriptiveComplexity.Examples.ConjunctiveQueries` is the hands-on tutorial;
individual declarations are documented on their own pages.

## The framework: problems, interpretations, reductions

* `DescriptiveComplexity.Interpretation` – a `DescriptiveComplexity.DecisionProblem`
  is an isomorphism-invariant property of finite structures of a language
  (invariance is baked into the notion, as is standard in descriptive
  complexity). A `DescriptiveComplexity.FOInterpretation` is a tagged,
  `dim`-dimensional first-order interpretation of one language in another,
  and a `DescriptiveComplexity.FOReduction` (notation `P ≤ᶠᵒ Q`) is one that
  maps yes-instances exactly to yes-instances. Tags replace the linear order
  that textbook FO reductions use to encode constantly-many sorts of
  elements.
* `DescriptiveComplexity.Composition` – the pullback of a formula through an
  interpretation and the composition of interpretations, giving reflexivity
  and transitivity of `≤ᶠᵒ` (a `Preorder` on problems, usable in `calc`).
* `DescriptiveComplexity.Ordered` and
  `DescriptiveComplexity.OrderedComposition` – reductions over the ordered
  expansion of the source language, `DescriptiveComplexity.OrderedFOReduction`
  (notation `P ≤ᶠᵒ[≤] Q`): order-invariant FO(≤) reductions, correct on every
  finite linearly ordered input. This is the standard notion of the field and
  the home of gadget constructions that genuinely need an order.

## The abstract complexity layer

* `DescriptiveComplexity.Complexity` – `DescriptiveComplexity.ComplexityClass`,
  with membership, hardness and completeness, closed by construction under
  (ordered) FO reductions. Membership and hardness depend only on the
  *finite* instances of a problem, making explicit that these statements say
  nothing about infinite structures.

## The polynomial hierarchy, defined logically

* `DescriptiveComplexity.SecondOrder` (with `…Lift`, `…Pull`, `…Ordered`) –
  existential/universal second-order definability with `k` quantifier-block
  alternations.
* `DescriptiveComplexity.Hierarchy` – the levels `Σₖᵖ`/`Πₖᵖ` and `PH` as
  complexity classes, via Fagin's ([Fagin 1974][fagin1974generalized]) and
  Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems. The
  level inclusions and the duality `Πₖᵖ = co-Σₖᵖ` are proved, not assumed.
  Level 0 is `DescriptiveComplexity.PTIME`, polynomial time, defined by the Horn
  fragment SO-Horn (below); the level-0 statements that would amount to
  closure under complement are the one thing the fragment does not give, and
  are restricted to levels `≥ 1`. Everything remains a definition or a
  theorem: the library declares **no axioms** (check with `#print axioms`).

## Polynomial time, by the Horn fragment

* `DescriptiveComplexity.SecondOrderHorn` – SO-Horn ([Grädel
  1992][gradel1992capturing]): existential second-order logic whose kernel is a
  conjunction of Horn clauses in the quantified relation variables, the
  fragment that captures polynomial time on ordered structures. The kernel is
  represented as *data* (`DescriptiveComplexity.HornProgram`, a list of clauses with a
  first-order guard over the ordered expansion, body atoms and an optional
  head), which is Grädel's clausal normal form and what a reduction consuming
  such a definition needs to read.
* `DescriptiveComplexity.SecondOrderHornPull` – the pullback of an SO-Horn definition
  through an interpretation *stays Horn*: the Horn condition constrains only
  the second-order atoms, and an interpretation rewrites the
  input-vocabulary ones, which live in the guard. This closure is what makes
  `DescriptiveComplexity.PTIME` (in `DescriptiveComplexity.Hierarchy`) a genuine complexity
  class, and hence level 0 of the hierarchy, *defined* by SO-Horn definability
  just as NP is defined by `Σ₁`-definability. HORN-SAT is PTIME-complete – hard
  by the Horn discharge, and a member by the Horn program that computes unit
  propagation along the order – which also yields the four inclusions of level
  0 into level 1. See `DescriptiveComplexity.Problems.HornSat` for what is and is not
  claimed.

* `DescriptiveComplexity.FixedPoint` – FO(LFP) ([Immerman
  1986][immerman1986relational]; [Vardi 1982][vardi1982complexity]), in the same
  clausal style: a rule system defining a least fixed point, plus an
  *unrestricted* first-order output sentence read at it. Because the output may
  negate fixed-point atoms, FO(LFP) definability is closed under complement by
  construction (`DescriptiveComplexity.LFPDefinable.compl`) – the one thing the Horn
  fragment cannot do head-on – and every SO-Horn definition transports into it
  (`DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable`).

* `DescriptiveComplexity.FixedPointHorn` – the converse translation, the hard half of
  Grädel's equivalence: every FO(LFP) definition compiles back into the Horn
  fragment, by deriving the *complement* of the fixed point stage by stage
  along the order and evaluating the output sentence clausewise
  (`DescriptiveComplexity.LFPDefinable.sigmaSOHornDefinable`). The two formalisms are
  therefore interchangeable
  (`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`), SO-Horn definability
  is closed under complement (`DescriptiveComplexity.SigmaSOHornDefinable.compl`), and
  level 0 of the hierarchy collapses: `PiP 0 = SigmaP 0`
  (`DescriptiveComplexity.piP_zero_eq`), polynomial time closed under complement. The
  order-walking machinery shared with the HORN-SAT program lives in
  `DescriptiveComplexity.OrderWalk`.

## Shared encodings

* `DescriptiveComplexity.SecondOrderMerge` – merging a second-order quantifier
  prefix into a single block (and back), so that constructions stated for one
  block can read the kernel of a `k`-block sentence.
* `DescriptiveComplexity.Padding` – canonically padded tuples: the convention
  by which a single interpretation dimension can carry tuples of different
  lengths (pad with a minimum of the input order), together with the FO(≤)
  formulas expressing it. This is the one place where the SAT-family
  reductions need their input to be ordered.
* `DescriptiveComplexity.OccurrenceOrder` and
  `DescriptiveComplexity.OccurrenceFormulas` – machinery for encoding
  occurrences of literals in clauses, shared across the SAT-family reductions.
* `DescriptiveComplexity.OrderWalk` – walking a finite linear order (or the
  lexicographic order on tuples) first-order: min/max/successor guards and
  their tuple analogues, induction along covers, and the rank of an element.
  Shared between the HORN-SAT program and the FO(LFP) → SO-Horn translation.
* `DescriptiveComplexity.Numbers` – unary and binary encodings of numbers as
  finite structures, for threshold and weight parameters of problems.
* `DescriptiveComplexity.Machines` – Turing machines as relations on a
  universe, with no vocabulary: configurations, steps, and acceptance within a
  budget counted in universe elements. The semantics the machine bridge reads
  off an instance.

## The problem catalog

`DescriptiveComplexity.Problems` holds one decision problem per file, each with
its vocabulary, FO reductions and a completeness theorem. Every class in the
table below is *defined* logically; each problem listed is proved **complete**
for it – both a member and hard under FO reductions. The catalog covers all of
Karp's 21 NP-complete problems. Each problem's own module page documents its
reduction and certificate in full.

| Complexity class | Logical characterization | Problems proved complete |
| --- | --- | --- |
| `PTIME` = `Σ₀ᵖ` = `Π₀ᵖ` | SO-Horn (existential second-order Horn), proved equivalent to FO(LFP) – [Grädel 1992][gradel1992capturing]; [Immerman 1986][immerman1986relational], [Vardi 1982][vardi1982complexity] | HORN-SAT |
| `NP` = `Σ₁ᵖ` | ∃SO, existential second-order logic ([Fagin 1974][fagin1974generalized]); equivalently acceptance by a nondeterministic polynomial-time Turing machine | **SAT-family:** SAT · 3SAT · NAE-SAT · NAE-3SAT · 1-in-SAT<br>**Coloring:** 3-Colorability · `k`-Colorability (`k ≥ 3`) · Chromatic Number · Clique Cover<br>**Cliques & subgraphs:** Clique · Independent Set · Vertex Cover · Subgraph Isomorphism<br>**Sets & hypergraphs:** Set Cover · Hitting Set · Set Packing · Exact Cover · Set Splitting · Dominating Set · 3-Dimensional Matching<br>**Graphs:** Feedback Vertex Set · Feedback Arc Set · Steiner Tree (node- & edge-weighted) · Max Cut · Hamilton Circuit (directed & undirected)<br>**Numbers (in binary):** Knapsack · Partition · 0-1 Integer Programming · Job Sequencing<br>**Machines:** acceptance by a nondeterministic polynomial-time Turing machine<br>**Queries:** Conjunctive Query Evaluation · CQ Containment |
| `coNP` = `Π₁ᵖ` | ∀SO, universal second-order logic | TAUT (and QBF∀ at one block) |
| `Σₖᵖ` (`k ≥ 1`) | `Σₖ¹`: `k` alternating second-order blocks, existential first ([Stockmeyer 1976][stockmeyer1976polynomial]) | `QBF k` – at `k = 1`, NP |
| `Πₖᵖ` (`k ≥ 1`) | `Πₖ¹`: `k` alternating second-order blocks, universal first | `QBF∀ k` – at `k = 1`, coNP |
| `PH` | full second-order logic | — |

Headline results and cross-references:

* **Cook–Levin, machine-free** (`DescriptiveComplexity.SAT_NP_complete`;
  [Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal]): SAT is
  NP-complete by a Tseitin discharge, no machine model. 3-colorability is
  FO-interreducible with SAT in both directions.
* **The machine bridge**: machine acceptance
  (`DescriptiveComplexity.NTMAccept`) – does this nondeterministic Turing
  machine, carried as data by the instance, accept its input within a
  polynomial step budget (as many steps as there are tape positions)? – is
  NP-complete
  (`DescriptiveComplexity.ntmAccept_NP_complete`), so a problem is in the
  library's NP exactly when it ordered-FO-reduces to it
  (`DescriptiveComplexity.mem_NP_iff_le_ntmAccept`): the logically defined
  class *is* the machine one. The textbook Cook–Levin – machine acceptance
  reduces to SAT – is `DescriptiveComplexity.ntmAccept_reduces_to_sat`. One
  level down, the *deterministic* restriction
  (`DescriptiveComplexity.DTMAccept`, a functional transition table folded into
  the yes-instances) is PTIME-complete
  (`DescriptiveComplexity.dtmAccept_PTIME_complete`): membership because a
  deterministic run is a least fixed point, read through the formalized
  FO(LFP) → SO-Horn translation, and hardness by a unit-propagation machine
  built inside the HORN-SAT instance – so PTIME, too, is the machine class
  (`DescriptiveComplexity.mem_PTIME_iff_le_dtmAccept`), with the Grädel-side
  textbook discharge `DescriptiveComplexity.dtmAccept_reduces_to_hornSat`.
* **All of Karp's 21** ([Karp 1972][karp1972reducibility]): the SAT, clique,
  set, coloring, graph and number families above, closed by the two Hamilton
  circuit problems – a circuit read as a linear order of the universe, hard
  from Vertex Cover by Karp's twelve-vertex cover-testing gadget.
* **PTIME by the Horn fragment**: HORN-SAT is PTIME-complete
  (`DescriptiveComplexity.HORNSAT_PTIME_complete`) by the Horn discharge and a
  Horn program for unit propagation – the P-level analogue of Cook–Levin,
  equally machine-free. REACH/UNREACH is a second worked instance of the
  fragment (a membership example, not proved complete).
* **Above NP**: TAUT (DNF tautology) is coNP-complete by complementing the
  Cook–Levin discharge; `QBF k`, quantified Boolean formulas with `k`
  alternating blocks, is complete for the `k`-th level of the hierarchy
  ([Stockmeyer 1976][stockmeyer1976polynomial]; [Wrathall
  1976][wrathall1976complete]) by the same Tseitin discharge carrying block
  marks.

## Worked examples

* `DescriptiveComplexity.Examples` – tutorial-style, domain-specific
  walkthroughs of the full recipe (vocabulary → semantics → invariance →
  membership → hardness → completeness). Currently Boolean conjunctive
  queries – evaluation and containment, both NP-complete via Chandra–Merlin
  ([Chandra & Merlin 1977][chandra1977optimal]).
-/
