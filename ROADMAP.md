# Roadmap

Long-term catalog of things worth incorporating. Organized by theme;
each item carries a rough scale of the effort ([S] short, [M] medium,
[L] long, [R] research-level, i.e., the Lean proof would itself be a
contribution) and its prerequisites. Main source: Immerman,
“Descriptive Complexity” (DC below); also Garey–Johnson and Karp's 21
problems for the catalog.

## 0. Integer representations (referenced as (A)–(D) below)

How numbers in problem instances are encoded as finite structures; a
per-problem choice. The *semantics* of numbers (sums, comparisons) is
always computed in Lean inside `Holds`; the representation only
constrains which reductions are FO-expressible, whether the problem
keeps its intended complexity (unary vs binary genuinely changes it),
and iso-invariance of the decoding.

- **(A) Cardinalities of marked sets** (unary): threshold k = |K| for
  a unary predicate K; weight w(e) = |{x : W(e, x)}| for binary W.
  Order-free, iso-invariant for free, lives in the quantifier-free
  fragment; the tagged framework does cardinality arithmetic natively
  (disjoint union via tags adds, dimension multiplies, complement
  subtracts). Only for numbers that are honestly polynomial: unary
  SubsetSum-style problems are in P, hence not NP-hard under (A).
  *In use*: the clique family's thresholds are the `Set.ncard` of the
  marked set (`Problems/CliqueFamily/Defs.lean`), with the arithmetic –
  reversal of comparisons under complementation, and the equivalence
  between comparing decoded numbers and exhibiting an injection – in
  `Numbers/Unary.lean`.
- **(B) Positions in an order** that is part of the problem's own
  vocabulary (“≤ is linear” folded into `Holds`); buys FO comparison
  of numbers, still unary; forces every reduction *into* the problem
  to construct the order.
- **(C) Binary via bit relations**: universe = items ∪ positions
  (separated by unary predicates), linear order (or successor) on
  positions, Bit(e, p); `Holds` decodes ∑ 2^i in Lean. The honest
  encoding for SubsetSum-like problems (weights up to 2^n). If a
  reduction needs arithmetic inside formulas: comparison and addition
  are FO(≤)-definable; multiplication is TC⁰, not FO – avoid
  reductions that must multiply.
- **(D) Built-in arithmetic FO(≤, BIT)** (DC's standard setting):
  every instance ordered, BIT primitive. Needed for the
  descriptive-complexity endgame (§3) but a tax on every reduction;
  not the default.

(A) and (C) are complements, not rivals: (A) where numbers are
polynomially bounded, (C) where they must be exponential. Reductions
from (C)-problems to (A)-problems are unproblematic: FO formulas only
read bits, never sum them.

## 1. NP-complete problems (catalog growth)

Current: SAT, 3SAT, 3COL (both directions), and the full
NP-completeness of the clique family (Clique/IS/VC), via the
SAT → Clique ordered reduction, the Σ₁ membership of Clique, and the
existing Clique/IS/VC inter-reductions.

- **Set Cover / Hitting Set** [S]: from VC; bipartite incidence
  vocabulary, quantifier-free.
- **Dominating Set** [S]: from VC by edge subdivision;
  quantifier-free, 2-dimensional.
- **Graph k-colorability, fixed k ≥ 3** [S]: from 3COL by adding k−3
  universal vertices (tags). Chromatic-number threshold version via
  representation (A).
- **NAE-3SAT and 1-in-3SAT** [M]: Schaefer-style variants; valuable as
  reduction *sources* (their gadgets are more local than 3SAT's).
- **Max Cut** [M]: from NAE-3SAT; threshold via (A).
- **Feedback Vertex Set / Feedback Arc Set** [M]: from VC.
- **Subgraph Isomorphism** [S]: generalizes Clique; two-graphs-in-one
  vocabulary via `Language.markedGraph`-style unary marks.
- **Hamiltonian Cycle (directed and undirected)** [L]: from VC or 3SAT;
  the gadget chaining almost certainly needs the order (ordered
  reduction, like SAT → 3COL). Prerequisite for TSP.
- **TSP** [M after HC]: from Hamiltonian Cycle, with weights in
  {1, 2} via representation (A); that variant is NP-hard and needs no
  arithmetic.
- **Longest Path / Longest Cycle** [S after HC].
- **Exact Cover, X3C, 3-Dimensional Matching** [M–L]: from 3SAT; local
  gadgets, probably ordered.
- **Steiner Tree** [M]: from X3C or VC; threshold via (A).
- **SubsetSum / Partition / Knapsack** [M]: representation (C), with a
  shared “weighted items” vocabulary (unary Item/Pos marks, order on
  positions, binary Bit) carrying a well-formedness predicate and a
  decode to `Multiset ℕ`. The classical SAT ≤ SubsetSum reduction
  defines the output *digits* combinatorially (“clause j contains
  literal ℓ”), so the Bit formulas are easy FO.
- **0-1 Integer Programming** [M]: from 3SAT; representation (C) for
  coefficients.
- **3-Partition** [L]: strongly NP-complete, so representation (A)
  (unary) suffices and the hardness claim is honest; the classical
  source for packing/scheduling reductions (Bin Packing [M after it]).
  Warning: the 3DM → 3-Partition reduction is arithmetic-heavy; check
  FO-expressibility carefully before committing.
- **Milestone: Karp's 21** – a recognizable public target for catalog
  completeness (cf. the Isabelle/AFP efforts around Karp's problems);
  the list above covers most of it.

## 2. Complete problems for other classes

**Discharge symmetry** (guiding principle): each class-defining
fragment (§3) has a canonical complete problem that is essentially its
*syntactic image*, so each hardness discharge is a Tseitin-style
translation of the defining logic into the problem's vocabulary, i.e. a
variation on `sat_hard_of_sigmaSODefinable` with a shape invariant
carried through:

| fragment | complete problem | note |
|---|---|---|
| ∃SO | SAT | done (Cook–Levin discharge) |
| SO alternation, level k | QBF_k | done (same construction + block marks) |
| SO-Horn (P) | HORN-SAT | Horn kernel ⇒ Horn clauses; easier than Cook–Levin |
| SO-Krom (NL) | 2SAT | Krom kernel ⇒ binary clauses |
| SO(TC) (PSPACE) | QSAT | least mechanical: natural image is a succinct/game reachability, QSAT via the standard alternation argument |

Consequence: do HORN-SAT while the Cook–Levin machinery is warm (QBF_k
is done, and its merging/transfer infrastructure is reusable); CVP and alternating reachability then enter the catalog as
ordinary reductions *from* HORN-SAT rather than as primary discharges.

- **QBF_k (Σₖ/Πₖ-QSAT)** [M, *done*]: quantified Boolean formulas with k
  alternation blocks. `QBF k` is `Σₖᵖ`-complete (`QBF_complete`) and the
  dual `QBFPi k`, with a universal outermost block, is `Πₖᵖ`-complete
  (`QBFPi_complete`); both come from the *same* reduction
  (`qbfReduction`), parameterized by the starting polarity. Vocabulary =
  sat plus k unary block marks on variables (`Language.qbf k`),
  semantics = alternating quantification `altQuant` over k truth
  assignments. Landed in `Problems/Qbf/` (`Defs`, `Membership`,
  `Transfer`, `Hardness`) plus the reusable `SecondOrderMerge.lean`;
  axiom-free. At k = 1 the two specialize to NP- and coNP-completeness
  (`QBF_one_NP_complete`, `QBFPi_one_coNP_complete`).
  - **The matrix shape follows the parity of k** – forced, and the
    standard form of the Σₖᵖ-complete QBF problems. Tseitin introduces
    *gate* variables; they are functionally determined
    (`∃ gates. CNF(atoms, gates) ↔ φ(atoms)`, `exists_gates`), so the
    gate quantifier can be absorbed into the innermost quantifier of the
    prefix *only when that quantifier is existential* – a universal
    player would otherwise falsify a gate clause and collapse the
    instance. With an existential outermost block the innermost is
    existential iff k is odd, so `QBF k` takes a conjunctive matrix for
    odd k and a disjunctive one for even k, linked by
    `dnfSat_iff_not_cnfSatWith_true` (negation plus a swap of all literal
    signs — *not* a complementation of the assignments, which would only
    be correct on instances whose block marks partition the variables).
    Choosing the interpretation's literal signs by the same flag makes
    the parity vanish from the correctness proof: the literal a satisfied
    clause must make true is always the positive Tseitin one. The
    parity flips with the starting polarity, so `QBFPi k` has the mirror
    convention (conjunctive for even k). This CNF/DNF-by-parity normal
    form is the classical one (Wrathall 1976).
  - Reusable pieces worth knowing about for the other discharges of this
    section: `SecondOrderMerge.lean` (merge a prefix into one block and
    back; enlarge the innermost block by an auxiliary one, so a
    quantifier can range over a pair) and `Problems/Qbf/Transfer.lean`
    (move an alternating prefix between truth assignments and block
    assignments, given a reading that is surjective at every block).
    `qbfT_clauses_iff` is the `∃`-free form of `tseitin_satisfiable_iff`
    — the shape any *alternating* discharge needs, since the prefix
    supplies the assignment rather than quantifying it.

- **TAUT** [S, *done*]: coNP-complete (`TAUT_coNP_complete`, in
  `Problems/Taut.lean`) via the complement machinery. Same vocabulary as
  SAT, read disjunctively; both halves come from the single sign-swapping
  interpretation `swapSignInterp` (De Morgan: a DNF is a tautology iff the
  sign-swapped CNF is unsatisfiable), together with the observation that a
  reduction complements – `FOReduction.compl` / `OrderedFOReduction.compl`
  in `Complexity.lean`, which turns a `Σ`-level discharge into the dual
  `Π`-level one for free.
  - **The 3-DNF variant does not come for free** [M]: 3SAT folds its width
    bound into the yes-instances (`ThreeSatisfiable = WidthAtMostThree ∧
    Satisfiable`), so its complement is a disjunction and the sign swap does
    not transfer. 3-DNF-TAUT hardness needs the *invariant* that the
    SAT → 3SAT reduction always outputs width-≤ 3 instances, which the
    `≤ᶠᵒ` interface hides; it would have to be exposed alongside the
    reduction.
- **P-hardness family** [M–L]: statements of the form “every
  SO-Horn-definable (or FO(LFP)-definable) problem FO-reduces to X”,
  mirroring the SAT discharge one level down (meaningful even before
  PTIME is defined):
  - HORN-SAT: the primary discharge, per the symmetry table above;
  - Circuit Value Problem, Monotone CVP, and alternating reachability
    (DC's canonical P-complete problem, with quantifier-free
    projection hardness in the book): as catalog reductions from
    HORN-SAT.
- **NL: REACH** [M]: directed st-reachability, the canonical
  NL-complete problem; hardness = “every FO(TC)-definable problem
  FO-reduces to REACH”. Also **2SAT** [M after REACH] (via implication
  graphs; mind the complementation, Immerman–Szelepcsényi territory).
- **L: REACHd** [M]: outdegree-≤1 reachability, complete for FO(DTC).
- **PSPACE: QSAT** [L]: unbounded-alternation QBF; hardness = “every
  SO(TC)-definable (equivalently FO(PFP)-definable) problem
  ordered-FO-reduces to QSAT”. Downstream: game problems (Generalized
  Geography…) [L each, gadget-heavy].
- Horizon: EXPTIME/NEXPTIME via SO(LFP)/SO(TC) and succinct-input
  problems [R]; Δₖᵖ and oracle classes are blocked on machine models,
  presumably forever out of scope.

## 3. Logics and framework extensions

- **SO-Horn and SO-Krom (Grädel)** [M–L]: existential SO with
  Horn (resp. Krom) FO kernel captures P (resp. NL) on ordered
  structures. Key observation: this fits the existing framework far
  more cheaply than fixpoint logics, since SO quantifiers are already
  Lean-level and only the kernel shape (Horn/Krom, already close to
  `Mathlib.ModelTheory.Complexity`'s formula-shape predicates) is
  object-level. Likely the cheapest path to an axiom-free definition
  of PTIME, ahead of FO(LFP).
- **FO(LFP)** [L]: syntax and semantics of least fixed points;
  order-invariant FO(LFP) as the *definition* of PTIME
  (Immerman–Vardi), filling level 0 of the hierarchy (currently an
  empty placeholder class, since PTIME and its axioms were removed);
  hardness discharges for HORN-SAT/CVP (§2). Design cost: fixpoint
  operator syntax, positivity, stages.
- **SO(TC) for PSPACE** [L]: second-order transitive closure logic,
  TC taken over tuples of *relation* variables (reachability in the
  exponential configuration graph); captures PSPACE on ordered
  structures (DC: FO(PFP) = SO(TC) = PSPACE). Same cheapness argument
  as SO-Horn: the TC can be Lean-level (`Relation.TransGen` over SO
  assignments) with only the FO transition formula over a doubled
  block-language object-level, so no fixpoint syntax, positivity or
  stage machinery. Preferred path to PSPACE, ahead of FO(PFP).
  Note: no fragment of *plain* SO can play this role: SO = PH
  (Fagin/Stockmeyer), so an SO fragment capturing PSPACE would
  collapse PH; some iteration/recursion operator is unavoidable.
- **FO(PFP), FO(TC), FO(DTC)** [L, sharing infrastructure with LFP]:
  definitions of PSPACE, NL, L on ordered structures (DC ch. 9–10);
  for PSPACE, SO(TC) above is the cheaper route and FO(PFP) becomes a
  textbook-faithfulness layer.
- **BIT and FO(≤, BIT)** [L]: representation (D); FO-definability of
  + and × from BIT, `FO(≤, BIT)` = uniform AC⁰ as the bottom of the
  ordered world; **quantifier-free projections** as the finest
  reduction notion (DC uses them for almost all completeness results);
  SAT complete under first-order projections.
- **Reduction-notion refinements** [M]: track quantifier-free /
  projection / dimension-1 status through composition (currently only
  `IsQuantifierFree` exists); “problem X is complete under qfps” is
  the DC-faithful statement.
- **FO(COUNT) / counting quantifiers** [L]: with BIT, captures uniform
  TC⁰; relevant to the representation-(C) arithmetic boundary
  (multiplication is TC⁰, not FO).

## 4. Capture and structural theorems (DC's greatest hits)

- **Immerman–Szelepcsényi as a logic theorem** [L–R]: FO(TC) is closed
  under complement on finite ordered structures (NL = coNL). Self-
  contained once FO(TC) exists, spectacular, and the inductive-counting
  proof is well suited to formalization. Flagship target; a major
  milestone on its own.
- **Immerman–Vardi** [L]: P = order-invariant FO(LFP); in this
  library's definitional style it is the pair (definition, HORN-SAT/
  CVP hardness discharge) rather than a machine-model equivalence.
- **Abiteboul–Vianu** [R]: LFP = PFP on unordered structures iff
  P = PSPACE. Deep; needs both fixpoint logics plus the stage-
  comparison machinery. Long-range flagship.
- **Grädel's theorems** [M–L]: SO-Horn = P, SO-Krom = NL on ordered
  structures (see §3; the capture statements relative to the library's
  own class definitions).
- **Spectra** [M]: Fagin's connection between generalized spectra and
  NP; mostly definitional given the SO layer, historically resonant.
- **Machine bridge: bounded NTM acceptance is NP-complete** [L]:
  the problem “the NTM M accepts x within t steps” (t unary; unary is
  what keeps this NP- rather than NEXP-complete), with the machine as
  *data*: universe = time/tape positions (order in the problem's own
  vocabulary, representation (B)) ∪ states ∪ symbols; transition table
  a relation; `Holds` = a bespoke Lean operational semantics
  (configurations, step, accepting run – Mathlib's
  `Computability.TuringMachine` does not help: fixed machines as
  types, not machines-as-data). Three parts:
  - problem definition + iso-invariance [M];
  - membership (the tableau half of Fagin's theorem): guess the run
    relations by `SigmaSODefinable`, FO kernel checks steps by lookup
    in the δ-relation [M];
  - hardness: SAT (better: 3SAT, bounded width avoids tape-scanning
    pain) `≤ᶠᵒ[≤]` BoundedAcceptance via a *CNF-specific* machine M_φ
    (states = tagged clause/occurrence elements, transitions
    FO-defined from posIn/negIn, time O(n·m) in a dimension-2 lex
    universe); correctness is genuine operational reasoning
    (configuration invariants, induction on steps) – the machine-model
    tax paid exactly once, in miniature [L].
  Payoff: both halves of Fagin's theorem inside the library (“P ∈ NP
  iff P FO-reduces to machine acceptance”), making the identification
  with machine NP a theorem rather than a citation; the remaining gap
  with textbook NP (structures vs strings) is thin and honestly
  statable in prose.

## 5. Inexpressibility toolkit (unconditional results)

The unique payoff of the descriptive approach: *unconditional*
separations and non-reducibility, impossible in the machine world.

- **Ehrenfeucht–Fraïssé games on finite structures** [L]: build on
  Mathlib's `ModelTheory/PartialEquiv.lean` (back-and-forth) and
  `Fraisse.lean`; what is missing is the finite, graded (quantifier-
  rank) version and the methodology lemmas (“same rank-k type ⇒ agree
  on rank-k sentences”).
- **First applications** [M after EF]: EVEN is not FO-definable (even
  order-invariantly); REACH/connectivity is not FO-definable. Library
  payoff: FO ⊊ FO(TC) as an unconditional strict inclusion, and
  non-existence of FO reductions in specific cases.
- **Locality (Hanf, Gaifman)** [L]: the workhorse for graph
  inexpressibility; gives connectivity/acyclicity results without
  bespoke games.
- **0-1 laws (Glebskii et al., Fagin)** [L]: FO 0-1 law on random
  structures; Mathlib's probability is ample. Fun, self-contained,
  good student project.
- **Order-necessity results** [R]: candidate research question the
  framework makes precise: show some catalog reduction (e.g.
  SAT → 3COL) provably has no order-free FO counterpart, separating
  `≤ᶠᵒ` from `≤ᶠᵒ[≤]` on concrete problems.
- Horizon: PARITY not in FO(≤, BIT) (Håstad/Ajtai/FSS, i.e. uniform
  AC⁰ lower bounds) [R]: a switching-lemma formalization is a major
  standalone project.

## 6. Further horizons

- **Counting: #P via counting SO assignments** [R]: the
  Saluja–Subrahmanyam–Thakur #FO framework; #SAT, permanent, #3COL.
  Direct bridge to provenance-lean: counting provenance semantics of a
  query is exactly a model count, so the two libraries would meet here
  (semiring provenance as the common generalization).
- **Optimization: MaxSNP** [R]: Papadimitriou–Yannakakis's
  syntactically defined optimization classes (Π₁-definable objective),
  L-reductions, MAX-3SAT completeness. The syntactic layer fits this
  framework natively; PCP-based hardness of approximation stays out of
  scope.
- **Teaching material** [M]: the `Examples/` directory now holds the
  first tutorial-style worked example (Boolean conjunctive queries,
  evaluation and containment, Chandra–Merlin), walking through the full
  recipe as a template. Remaining: grow this into a curated “reduction
  cookbook” example set (cf. Grange et al., MFCS 2024) as the catalog
  broadens, so the library doubles as a complexity-course companion.

## Suggested ordering (value vs. prerequisite chains)

1. Cheap catalog wins: Set Cover, Dominating Set, k-COL (TAUT is done).
1bis. Machine bridge (bounded NTM acceptance NP-complete, §4): high
   foundational value; schedule early.
2. SO-Horn path to an axiom-free PTIME; HORN-SAT hardness.
3. EF games + EVEN/REACH inexpressibility (opens §5).
4. FO(TC)/REACH, then Immerman–Szelepcsényi as the flagship theorem.
5. SO(TC) and QSAT for PSPACE; then FO(LFP)/FO(PFP) as the
   textbook-faithfulness layer and the rest of §4.
