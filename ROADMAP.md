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
complexity (unary vs binary genuinely changes it — now a theorem:
`no_unary_encoding` in `DescriptiveComplexity/Encoding/UnaryBlowup.lean` shows
no bit-length-sized encoding of subset-sum can be unary, with the honest
binary encoding as the positive contrast), and iso-invariance of the
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
  of scope (§7 refines both judgments).

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
  from BIT, `FO(≤, BIT)` = uniform AC⁰ as the bottom of the ordered world
  (formalizing that *capture* — against a circuit model — is the separate §4
  item **FO(≤, BIT) = AC⁰**); **quantifier-free projections** as the finest
  reduction notion (DC uses them for almost all completeness results); SAT
  complete under first-order projections.
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
- **FO(≤, BIT) = AC⁰** [R]: the bottom-level capture theorem (Immerman;
  Barrington–Immerman–Straubing) — first-order logic with a linear order and
  BIT is exactly (DLOGTIME-)uniform AC⁰. Unlike the other captures here, this
  one needs a *model of computation* on the far side: uniform AC⁰ circuit
  families (bounded depth, polynomial size, unbounded fan-in) plus a uniformity
  condition — introduced only to prove the bridge, exactly as the NP and PTIME
  machine bridges introduce Turing machines as data. Two payoffs justify the
  cost. The `FO ⊆ AC⁰` half turns the library's currently *by-inspection* claim
  that FO reductions are AC⁰-computable — the structures-vs-strings bridge of §7
  and of the README's *Scope and limitations* — into a theorem; and a formal
  AC⁰ is the prerequisite for the PARITY ∉ AC⁰ lower bound of §5. The converse
  `AC⁰ ⊆ FO(≤, BIT)`, simulating a uniform circuit family by an FO(≤, BIT)
  sentence, is the harder half. Depends on the BIT layer of §3; cf. the
  circuit-family-bridge remark in §7.
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

## 7. Machine bridges beyond NP and PTIME

The machine bridge is done for NP and PTIME (`ntmAccept_NP_complete`,
`dtmAccept_PTIME_complete`, and the characterizations
`mem_NP_iff_le_ntmAccept` / `mem_PTIME_iff_le_dtmAccept` — see the
`Problems/Machine.lean` docstring). This section is the design analysis for
extending it, with the class-defining logic assumed to exist (§3 work).

**Standing scope limit.** Textbook `NP = NTIME(nᵏ)` over string encodings
needs the converse compilation — that an FO interpretation or a `Σ₁` kernel is
*evaluated* by a polynomial-time machine: a verified compiler with a step
count, plus string encodings of structures [R]. Nothing in the bridge claims
it; the residual gap (FO reductions are AC⁰-computable, by inspection) is
documented in the README. Instances carry their own transition table, so
reduction-built machines have polynomially many states — standard for an
acceptance problem; the constant-alphabet simulation is never needed.

A further application of the same machinery, once step-counted machines can
run over string encodings: bounding the *encoders and decoders* of the
concrete-instance layer. The `Encoding`/`Decoding` bundles enforce that
`relBool` and `dec` are computations, but not that they are cheap (a decoder
may brute-force the answer; see the "what this does not buy" notes in
`DescriptiveComplexity/Encoding.lean` and `DescriptiveComplexity/Decoding.lean`).
With the bridge, "computed by a polynomial-time machine" becomes a statable
side condition on both, closing the last gap in reading completeness theorems
as statements about concrete data. [R], and only worthwhile after the
compilation direction above exists.

**Cost of a bridge, given the logic:**

| class | logic | membership | hardness | total |
|---|---|---|---|---|
| L | FO(DTC) | S | S | ~1–1.7k [M], but see below |
| NL | FO(TC) | S | S | ~1–1.7k [M], but see below |
| Σₖᵖ, Πₖᵖ | `Σₖ`-SO | M (reuses the NP membership) | M (reuses the SAT machine) | +0.6–1.2k [M] |
| PSPACE | SO(TC) | S | L–XL | ~3–5.5k |
| EXPTIME | SO(LFP) | L | XL | ~4–7k |
| EXPSPACE | SO(PFP) | M | XL (shared) | ~3–6k |

Three rules govern the table:

1. **Membership is cheap when the logic is a reachability/fixpoint logic, dear
   when it quantifies.** For DTC/TC/LFP/SO(TC) the machine problem is the
   *syntactic image* of the logic and membership is unfolding plus an encoding
   bijection; for ∃SO/`Σₖ` the run must be guessed and checked (Fagin's
   tableau). So PSPACE has one of the cheapest memberships and NP one of the
   dearest: space-bounded acceptance is to SO(TC) what SAT is to ∃SO — tape as
   a relation variable, the step clause of `Machine/Membership.lean` as the
   transition formula, acceptance its TC, no budget hence no walk lemma
   (400–700 lines).
2. **Hardness is cheap when the class has a one-loop complete problem** (REACH
   "guess a neighbour", HORN-SAT "propagate", SAT "guess then sweep").
   Otherwise the discharge must compile arbitrary formulas of the logic into a
   machine — the **evaluator** (static quantifier nesting → nested loops), in
   three variants of increasing cost: *state-registers* (loop counters as
   elements in the state; what PSPACE needs), *tape-registers with logarithmic
   addresses* (honest fixed-control logspace), *tape-registers with
   exponential addresses* (EXPTIME/EXPSPACE). Consequences: for PSPACE the
   direct SO(TC) discharge is easier than routing through QSAT (a QBF
   evaluator needs a stack for the input-given prefix); a
   *nondeterministically* stated space-bounded problem avoids Savitch
   entirely.
3. **Budget regimes.** Unary (NP, P, PH) needs the walk lemma
   (`accepts_iff_exists_walk`); no budget (L, NL, PSPACE, EXPSPACE) needs only
   `Relation.ReflTransGen`, strictly cheaper; exponential (EXPTIME) needs a
   walk along the lexicographic order of subsets, whose successor is
   FO-definable by ripple-carry (`Numbers/Binary.lean`,
   `Problems/Knapsack/Chain.lean` supply most of it).

The concrete items:

- **The polynomial hierarchy, the one cheap add-on** [M, +0.6–1.2k]:
  `Language.turing` plus `k` unary block marks on states (the state marks are
  deliberately a family for this), transitions non-decreasing in block index —
  a *local*, hence first-order condition, which is what makes "at most `k−1`
  alternations" checkable. Alternating acceptance is a Lean-level recursion on
  the budget. Membership in `Σₖᵖ` reuses the membership clauses per phase with
  `SecondOrderMerge.lean` as block bookkeeping; hardness from `QBF k` by the
  SAT machine with `k` guess sweeps; `Πₖᵖ` free by swapping the marks.
- **L and NL: the Turing model is the wrong one** [L, ~2.5–4.5k for both].
  As machine-as-data these are cheap for a bad reason: a logspace
  configuration is a constant-length tuple of elements, the configuration
  space is polynomial, and acceptance is REACH up to renaming — true, easy,
  contentless. A telling bridge needs storage matching what the logic's
  variables range over and *local* input access (else the FO-definable table
  smuggles in the whole input). The right model: a **fixed finite control
  with `k` two-way heads** on universe elements, no work tape, reading only
  the atomic type of its head tuple; determinism vs. nondeterminism is then L
  vs. NL, mirroring FO(DTC) vs. FO(TC). The machine is Lean-level data, so
  the statement is a **capture theorem**
  (`TCDefinable P ↔ ∃ k s (M : Automaton L k s), ∀ A, P A ↔ M.Accepts A`) —
  no reductions, no string encoding. Machine → logic is near-trivial (the
  configuration graph is FO-definable, acceptance its TC); logic → machine is
  the evaluator in its friendliest form (heads only, no addressing).
  Rejected models: registers (must legislate arithmetic; a head move *is* a
  step in the order), JAGs/pointer machines (lower-bound devices), branching
  programs (nonuniform). With BIT (§3), a circuit-family bridge (FO-uniform
  AC⁰ = FO(≤, BIT)) is more natural than any machine at that level.
- **Capture vs. completeness, the choice forced by the evaluator.** A capture
  theorem is also available at NP (fixed control, input heads, poly work
  tape) but is not taken: logic → machine there needs the evaluator *with*
  tape addressing (lockstep address computation to test a guessed relation) —
  exactly the cost the existing bridge dodges by routing hardness through
  SAT/HORN-SAT. So: capture at L/NL (evaluator cheap, model first-order),
  completeness at P/NP/`Σₖᵖ`/PSPACE and above (evaluator dear).
- **The exponential classes are not blocked by the framework**: the machine
  description stays polynomial (a reduction can write it) and only the run is
  exponential, living in Lean just as `SigmaSODefinable` quantifies over
  exponential-size assignment types; tape cells indexed by subsets of the
  positions, budget `2 ^ |pos|`, a legitimate iso-invariant problem. The
  expensive pair: the exponential-order walk (feasible) and the
  exponential-address evaluator (the real cost).
- **Limits that survive every variant**: the string-encoding layer (above);
  Savitch, if *deterministic* PSPACE machines are wanted complete; oracle and
  `Δₖᵖ` classes — the bridge would make them definable, but by a machine,
  against the library's classes-are-logic principle (a decision, not a
  drift); `#P` as "number of accepting runs" is easy to state but needs a
  parsimonious-reduction notion the framework lacks (§6).

## Suggested ordering (value vs. prerequisite chains)

1. EF games + EVEN/REACH inexpressibility (opens §5).
2. FO(TC)/REACH, then Immerman–Szelepcsényi as the flagship theorem.
3. SO(TC) and QSAT for PSPACE; then FO(LFP)/FO(PFP) as the
   textbook-faithfulness layer and the rest of §4.
4. Remaining catalog growth (X3C, 3-Partition, Bin Packing) and the
   other-class discharges (SO-Krom/2SAT, REACH, REACHd) as they become useful
   worked instances of the fragments above.
