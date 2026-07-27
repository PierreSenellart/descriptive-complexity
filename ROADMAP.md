# Roadmap

Forward-looking catalog of work **not yet done** — completed items have been
removed, and the record of what already exists in the library is `git log`
together with the module docstrings. Organized by theme; each item carries a
rough scale of effort ([S] short, [M] medium, [L] long, [R] research-level,
i.e., the Lean proof would itself be a contribution) and its prerequisites.
Main source: Immerman, "Descriptive Complexity" (DC below); also Garey–Johnson
and Karp's 21 problems for the catalog.

## 0. Integer representations (referenced as (A)–(D) below)

Reference taxonomy for how numbers in problem instances are encoded as finite
structures; a per-problem choice. The *semantics* of numbers (sums, comparisons)
is always computed in Lean inside `Holds`; the representation only constrains
which reductions are FO-expressible, whether the problem keeps its intended
complexity (unary vs binary genuinely changes it), and iso-invariance of the
decoding. (A)–(C) are in use across the catalog; (D) is the one still to build.

- **(A) Cardinalities of marked sets** (unary): threshold `k = |K|` for a unary
  predicate `K`; weight `w(e) = |{x : W(e, x)}|` for binary `W`. Order-free,
  iso-invariant for free, quantifier-free; also available *at arity 2* — the
  threshold as the cardinality of a marked binary relation, which is what
  objectives counting arcs need. The tagged framework does cardinality
  arithmetic natively (disjoint union via tags adds, dimension multiplies,
  complement subtracts). Only for numbers that are honestly polynomial: unary
  SubsetSum-style problems are in P, hence not NP-hard under (A).
- **(B) Positions in an order** that is part of the problem's own vocabulary
  ("≤ is linear" folded into `Holds`): buys FO comparison of numbers, still
  unary; forces every reduction *into* the problem to construct the order.
- **(C) Binary via bit relations**: universe = items ∪ positions (separated by
  unary predicates), linear order (or successor) on positions, `Bit(e, p)`;
  `Holds` decodes `∑ 2^i` in Lean. The honest encoding for SubsetSum-like
  problems (weights up to `2^n`). If a reduction needs arithmetic inside
  formulas: comparison and addition are FO(≤)-definable; multiplication is TC⁰,
  not FO — avoid reductions that must multiply.
- **(D) Built-in arithmetic FO(≤, BIT)** (DC's standard setting) [L]: every
  instance ordered, BIT primitive. Needed for the descriptive-complexity
  endgame (§3) but a tax on every reduction; not the default.

(A) and (C) are complements, not rivals: (A) where numbers are polynomially
bounded, (C) where they must be exponential. Reductions from (C)-problems to
(A)-problems are unproblematic: FO formulas only read bits, never sum them.

## 1. NP-complete problems (catalog growth)

Karp's 21 are complete (reached 2026-07-25). Remaining catalog growth:

- **X3C** [M–L]: exact cover by 3-sets, from 3-Dimensional Matching (now hard)
  or from Exact Cover; local gadgets, probably ordered.
- **3-Partition** [L]: strongly NP-complete, so representation (A) (unary)
  suffices and the hardness claim is honest; the classical source for
  packing/scheduling reductions. Warning: the 3DM → 3-Partition reduction is
  arithmetic-heavy; check FO-expressibility carefully before committing.
- **Bin Packing** [M after 3-Partition]: the standard downstream of
  3-Partition.

## 2. Complete problems for other classes

**Discharge symmetry** (guiding principle): each class-defining fragment (§3)
has a canonical complete problem that is essentially its *syntactic image*, so
each hardness discharge is a Tseitin-style translation of the defining logic
into the problem's vocabulary, i.e. a variation on
`sat_hard_of_sigmaSODefinable` with a shape invariant carried through. The
pattern is already instantiated by ∃SO → SAT, SO-alternation-level-`k` → QBF_k,
and SO-Horn → HORN-SAT; the discharges still to do:

| fragment | complete problem | note |
|---|---|---|
| SO-Krom (NL) | 2SAT | Krom kernel ⇒ binary clauses |
| SO(TC) (PSPACE) | QSAT | least mechanical: natural image is a succinct/game reachability, QSAT via the standard alternation argument |

- **3-DNF-TAUT** [M]: the width-three variant of TAUT does not come for free.
  3SAT folds its width bound into the yes-instances
  (`ThreeSatisfiable = WidthAtMostThree ∧ Satisfiable`), so its complement is a
  disjunction and the sign swap that gives plain TAUT does not transfer. 3-DNF-
  TAUT hardness needs the *invariant* that the SAT → 3SAT reduction always
  outputs width-≤ 3 instances, which the `≤ᶠᵒ` interface hides; it would have to
  be exposed alongside the reduction.
- **P-complete reductions from HORN-SAT** [M]: Circuit Value Problem, Monotone
  CVP, and alternating reachability (DC's canonical P-complete problem, with
  quantifier-free-projection hardness in the book), entering the catalog as
  ordinary catalog reductions *from* HORN-SAT rather than as primary discharges.
- **NL: REACH** [M]: directed st-reachability, the canonical NL-complete
  problem; hardness = "every FO(TC)-definable problem FO-reduces to REACH". Also
  **2SAT** [M after REACH] (via implication graphs; mind the complementation,
  Immerman–Szelepcsényi territory).
- **L: REACHd** [M]: outdegree-≤1 reachability, complete for FO(DTC).
- **PSPACE: QSAT** [L]: unbounded-alternation QBF; hardness = "every
  SO(TC)-definable (equivalently FO(PFP)-definable) problem ordered-FO-reduces
  to QSAT". Downstream: game problems (Generalized Geography…) [L each,
  gadget-heavy].
- Horizon: EXPTIME/NEXPTIME via SO(LFP)/SO(TC) and succinct-input problems [R];
  Δₖᵖ and oracle classes are blocked on machine models, presumably forever out
  of scope.

## 3. Logics and framework extensions

- **SO-Krom (Grädel)** [M–L]: existential SO with a Krom FO kernel captures NL
  on ordered structures, the NL analogue of the (done) SO-Horn = P. By the same
  recipe as SO-Horn: the Krom shape (at most two second-order atoms per clause,
  of either sign) is another clause-list datatype, and its discharge to 2SAT
  should be the same construction with the literal signs read off the clause.
- **FO(LFP) ⊆ NP, directly** [M]: by guessing the fixed point and the derivation
  order and checking both first-order against the certificate interface
  (`derives_eq_of_closed_of_wf`). No new mathematics — the inclusion already
  follows by composing the FO(LFP) → SO-Horn translation with the Horn discharge
  — but the direct `Σ₁` definition would be textbook-faithful; the work is
  formula building, made tedious by the varying arities of a block's atoms.
- **SO(TC) for PSPACE** [L]: second-order transitive closure logic, TC taken
  over tuples of *relation* variables (reachability in the exponential
  configuration graph); captures PSPACE on ordered structures
  (DC: FO(PFP) = SO(TC) = PSPACE). Same cheapness argument as SO-Horn: the TC can
  be Lean-level (`Relation.TransGen` over SO assignments) with only the FO
  transition formula over a doubled block-language object-level, so no fixpoint
  syntax, positivity or stage machinery. Preferred path to PSPACE, ahead of
  FO(PFP). Note: no fragment of *plain* SO can play this role: SO = PH
  (Fagin/Stockmeyer), so an SO fragment capturing PSPACE would collapse PH; some
  iteration/recursion operator is unavoidable.
- **FO(PFP), FO(TC), FO(DTC)** [L, sharing infrastructure with LFP]: definitions
  of PSPACE, NL, L on ordered structures (DC ch. 9–10); for PSPACE, SO(TC) above
  is the cheaper route and FO(PFP) becomes a textbook-faithfulness layer.
- **BIT and FO(≤, BIT)** [L]: representation (D); FO-definability of `+` and `×`
  from BIT, `FO(≤, BIT)` = uniform AC⁰ as the bottom of the ordered world;
  **quantifier-free projections** as the finest reduction notion (DC uses them
  for almost all completeness results); SAT complete under first-order
  projections.
- **Reduction-notion refinements** [M]: track quantifier-free / projection /
  dimension-1 status through composition (currently only `IsQuantifierFree`
  exists); "problem X is complete under qfps" is the DC-faithful statement.
- **FO(COUNT) / counting quantifiers** [L]: with BIT, captures uniform TC⁰;
  relevant to the representation-(C) arithmetic boundary (multiplication is TC⁰,
  not FO).
- **Relativized (domain-formula) reductions — membership closure** [M]:
  Immerman's textbook FO reduction restricts the target universe to a definable
  subset via a **domain formula**, needed for *spanning* problems (Hamilton
  circuit: a tour visits every element, so junk points with no valid incident
  edges must be excluded). The **hardness** side is already in place
  (`Relativized.lean`, `RelComposition.lean`: `RelFOInterpretation` with a
  `domFormula` field and its `MapRel` subtype universe, `RelOrderedFOReduction`
  with notation `≤ʳᶠᵒ[≤]`, wired into `Complexity`/`Hierarchy` as the
  `hard_of_relOrderedReduction` field), which is all a spanning problem's
  NP-hardness needs while its membership is a direct second-order sentence.
  Remaining — the symmetric **membership** closure `mem_of_relOrderedReduction`,
  deferred because nothing yet needs it:
  - `RelSecondOrderPull.lean` (~700 lines): `SOBlock.pull` is reused verbatim
    (a relation variable on the subtype pulls to one `(n·d)`-ary variable per
    tag tuple), but the assignment-transfer layer is rewritten **flipped** — on
    subtypes `pullAssign (mergeAssign σ) = σ` fails (extend-then-restrict loses
    off-domain data) while `mergeAssignRel (pullAssignRel ρ) = ρ` is exact, so
    stating the `sorealize_pullSO_aux` transfer in the flipped direction closes
    all four ∃/∀ alternation cases with only the exact round trip (no
    off-domain-invariance lemma, no guards on the pulled SO atoms). `extendSORel`
    extends `extendSO` with `domFormula := LHom.sumInl.onFormula ∘ domFormula`,
    its equivalence a `Equiv.subtypeEquiv` (the two subtype predicates are
    propositionally, not definitionally, equal). The order-requantification
    apparatus (`SOBlock.withOrder`, `linearGuard`, `orderElimLHom`) is reused
    verbatim; the two ordered closure theorems are near-copies with
    `pullSO → pullSORel`, `map_nonempty → dom_nonempty`,
    `map_finite → Subtype.finite`.
  - `RelSecondOrderHornPull.lean` (~300 lines): domain guards conjoin into each
    clause's FO guard; domain formulas are pure FO (no SO variables), so the
    Horn shape survives. Needed only for `PTIME.mem_of_relOrderedReduction`.
  - Then the `mem_of_relOrderedReduction` field and the six class-literal
    updates (`empty`, `compl`, `sigmaLevel`, `piLevel`, `PTIME`, `PH`).

## 4. Capture and structural theorems (DC's greatest hits)

- **Immerman–Szelepcsényi as a logic theorem** [L–R]: FO(TC) is closed under
  complement on finite ordered structures (NL = coNL). Self-contained once
  FO(TC) exists, spectacular, and the inductive-counting proof is well suited to
  formalization. Flagship target; a major milestone on its own.
- **Immerman–Vardi** [L]: P = order-invariant FO(LFP); in this library's
  definitional style it is the pair (definition, HORN-SAT/CVP hardness
  discharge) rather than a machine-model equivalence.
- **Abiteboul–Vianu** [R]: LFP = PFP on unordered structures iff P = PSPACE.
  Deep; needs both fixpoint logics plus the stage-comparison machinery.
  Long-range flagship.
- **Grädel's theorems** [M–L]: SO-Horn = P, SO-Krom = NL on ordered structures
  (see §3; the capture statements relative to the library's own class
  definitions).
- **Spectra** [M]: Fagin's connection between generalized spectra and NP; mostly
  definitional given the SO layer, historically resonant.

## 5. Inexpressibility toolkit (unconditional results)

The unique payoff of the descriptive approach: *unconditional* separations and
non-reducibility, impossible in the machine world.

- **Ehrenfeucht–Fraïssé games on finite structures** [L]: build on Mathlib's
  `ModelTheory/PartialEquiv.lean` (back-and-forth) and `Fraisse.lean`; what is
  missing is the finite, graded (quantifier-rank) version and the methodology
  lemmas ("same rank-k type ⇒ agree on rank-k sentences").
- **First applications** [M after EF]: EVEN is not FO-definable (even
  order-invariantly); REACH/connectivity is not FO-definable. Library payoff:
  FO ⊊ FO(TC) as an unconditional strict inclusion, and non-existence of FO
  reductions in specific cases.
- **Locality (Hanf, Gaifman)** [L]: the workhorse for graph inexpressibility;
  gives connectivity/acyclicity results without bespoke games.
- **0-1 laws (Glebskii et al., Fagin)** [L]: FO 0-1 law on random structures;
  Mathlib's probability is ample. Fun, self-contained, good student project.
- **Order-necessity results** [R]: candidate research question the framework
  makes precise: show some catalog reduction (e.g. SAT → 3COL) provably has no
  order-free FO counterpart, separating `≤ᶠᵒ` from `≤ᶠᵒ[≤]` on concrete
  problems.
- Horizon: PARITY not in FO(≤, BIT) (Håstad/Ajtai/FSS, i.e. uniform AC⁰ lower
  bounds) [R]: a switching-lemma formalization is a major standalone project.

## 6. Further horizons

- **Counting: #P via counting SO assignments** [R]: the
  Saluja–Subrahmanyam–Thakur #FO framework; #SAT, permanent, #3COL. Direct
  bridge to provenance-lean: counting provenance semantics of a query is exactly
  a model count, so the two libraries would meet here (semiring provenance as
  the common generalization).
- **Optimization: MaxSNP** [R]: Papadimitriou–Yannakakis's syntactically defined
  optimization classes (Π₁-definable objective), L-reductions, MAX-3SAT
  completeness. The syntactic layer fits this framework natively; PCP-based
  hardness of approximation stays out of scope.
- **Teaching material** [M]: grow the `Examples/` directory (which now holds the
  first tutorial-style worked example, Boolean conjunctive queries) into a
  curated "reduction cookbook" example set (cf. Grange et al., MFCS 2024) as the
  catalog broadens, so the library doubles as a complexity-course companion.

## Suggested ordering (value vs. prerequisite chains)

1. EF games + EVEN/REACH inexpressibility (opens §5).
2. FO(TC)/REACH, then Immerman–Szelepcsényi as the flagship theorem.
3. SO(TC) and QSAT for PSPACE; then FO(LFP)/FO(PFP) as the
   textbook-faithfulness layer and the rest of §4.
4. Remaining catalog growth (X3C, 3-Partition, Bin Packing) and the
   other-class discharges (SO-Krom/2SAT, REACH, REACHd) as they become useful
   worked instances of the fragments above.
