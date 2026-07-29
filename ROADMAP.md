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
pattern is instantiated for every fragment the library defines: ∃SO → SAT,
SO-alternation-level-`k` → QBF_k, SO-Horn → HORN-SAT, SO-Krom → 2SAT (the last
two sharing their scaffolding in `ClauseDischarge.lean`), SO(TC) →
SUCCINCT-REACH and ∃SO[new] → FINSAT, so no discharge is outstanding; what
remains below are ordinary catalog reductions and machine bridges.

- **P-complete reductions from HORN-SAT** [M]: Circuit Value Problem, Monotone
  CVP, and alternating reachability (DC's canonical P-complete problem, with
  quantifier-free-projection hardness in the book), entering the catalog as
  ordinary catalog reductions *from* HORN-SAT rather than as primary discharges.
- **PSPACE, downstream of QSAT** [L each, gadget-heavy]: the **hardness half of
  the machine bridge**, `QSAT ≤ᶠᵒ[≤] DTMAcceptSpace` – a deterministic
  QBF-evaluation machine written inside a QSAT instance, which also gives
  `PSPACE = NPSPACE`; in progress – and the
  game problems (Generalized Geography…).
- Horizon: EXPTIME/NEXPTIME via SO(LFP)/SO(TC) and succinct-input problems [R];
  Δₖᵖ and oracle classes are blocked on machine models, presumably forever out
  of scope (§7 refines both judgments).

## 3. Logics and framework extensions

- **FO(LFP) ⊆ NP, directly** [M]: by guessing the fixed point and the derivation
  order and checking both first-order against the certificate interface
  (`derives_eq_of_closed_of_wf`). No new mathematics — the inclusion already
  follows by composing the FO(LFP) → SO-Horn translation with the Horn discharge
  — but the direct `Σ₁` definition would be textbook-faithful; the work is
  formula building, made tedious by the varying arities of a block's atoms.
- **Housekeeping in the shared machinery** [S]: `lexLtF`/`lexLeF`, which decide
  the lexicographic order of two tuples first-order, sit in
  `Problems/FinSat/Nodes.lean` for a build reason only; they belong in
  `OrderWalk.lean` next to `succTupF`. Open beside it, and a design decision
  rather than a refactor: giving `extBase` (`SecondOrderNew.lean`) an
  *equivariant* junk convention – the value on a tuple with an invented argument
  is its first invented argument – which would remove `[L.IsRelational]` from
  `extEquiv` and `[Nonempty A]` from `extBase`.
- **FO(PFP)** [L, sharing infrastructure with LFP]: PSPACE on ordered
  structures (DC ch. 9–10); SO(TC), which already captures the class, is the
  cheaper route, so this is a textbook-faithfulness layer.
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

## 6. Beyond decision problems: counting and optimization

Everything above measures *decision* problems. The non-decision world repeats
the same pattern, a syntactic class matching a computational one, with a number
or a relation in place of the yes/no answer: Saluja–Subrahmanyam–Thakur (1995)
prove `#FO = #P` with the hierarchy `#Σ₀ ⊊ #Σ₁ ⊊ #Π₁ ⊊ #Σ₂ ⊊ #Π₂ = #FO`;
Arenas–Muñoz–Riveros (LICS 2017; LMCS 16(1), 2020) give a cleaner framework,
**QSO** (Quantitative Second-Order logic), a restriction of Droste–Gastin
weighted logics to the semiring ℕ; on the optimization side there is
Papadimitriou–Yannakakis's **MAX SNP** (1991), and for numeric output
Grädel–Gurevich metafinite model theory.

Two observations set the design. First, the **core generalization is cheap**: a
decision problem is an iso-invariant `Structure → Prop`, a counting problem an
iso-invariant `Structure → ℕ`, and vocabularies, tagged interpretations and the
invariance discipline transport unchanged. Second, **QSO is already this
library's idiom**, so prefer ΣQSO over raw #FO as the object-level logic. QSO
has a two-layer syntax: the Boolean layer is an ordinary SO formula evaluating
to 1 or 0 (Mathlib's `BoundedFormula` untouched), the quantitative layer is
built from `+`, `·` and the quantifiers `Σx`, `Πx`, `ΣX`, `ΠX` (`Σx` sums a
subformula's value over domain elements, `ΣX` over all relations of the
relevant arity). That is exactly "kernel as data rather than a shape carved out
of `BoundedFormula`", the way SO-Horn is a `HornProgram` clause list and
FO(LFP) a rule system. Formulas transcribe the mathematics directly; the
permanent of a 0-1 matrix is

```
ΣS. permut(S) · Πx.(∃y. S(x,y) ∧ M(x,y))
```

a second-order sum over binary relations, `permut(S)` acting as a filter and
the product computing `∏ A[i, σ(i)]`.

The capture results, all over ordered structures, are what the class
definitions should be read against (as in §4, the library would *define* its
classes by these fragments rather than prove machine equivalences):

| fragment | class |
|---|---|
| ΣQSO(FO) | #P (`#FO = #P` is inherited; #FO sits inside ΣQSO(FO)) |
| ΣQSO(∃SO) | SpanP (the paper captures SpanP, not SpanL; #L appears only via a support-based quantitative least fixed point) |
| QFO(LFP) | FP |
| QSO(PFP) / QFO(PFP) | FPSPACE / FPSPACE(poly) |
| ΣQSO with ℤ constants | GapP |
| MaxQSO(FO) / MinQSO(FO) | MaxP / MinP |

The FP row is the methodologically interesting one: FP is *not* reachable by
counting satisfying tuples of any FO fragment (`#Σ₁` already encodes such
`#P`-complete problems as #3-DNF, and dropping second-order free variables
loses `2ⁿ`). Products rescue it, `Πȳ.((ȳ < x̄) ↦ 2)` yielding `2^m`, which lets
a formula reconstruct a machine's binary output bit by bit.

The concrete items, in dependency order:

- **Parsimonious reductions** [M]: the real framework work. `≤ᶠᵒ` preserves
  membership (`A ∈ P ↔ I(A) ∈ Q`); counting needs `f A = g (I A)`: same
  interpretations, the iff replaced by an equation. Composition closure mirrors
  `Complexity.lean`, so the quantitative classes are again closed under
  reduction by construction. Depends on nothing beyond what exists today.
- **ΣQSO evaluator** [M–L]: a fresh inductive for the quantitative layer (~8
  constructors) over the existing Boolean layer, with a recursive evaluator
  into ℕ whose semantics is Mathlib-native (`⟦Σx.α⟧ = Finset.sum`,
  `⟦Πx.α⟧ = Finset.prod`). Recover #FO as the prenex fragment `ΣX̄.Σx̄.φ`.
- **`#P := ΣQSO(FO)`** [M after the two above]: as with `NP = Σ₁ᵖ` and
  PTIME = SO-Horn, the class is a definition and the theorem content is closure
  under parsimonious reductions plus completeness, not a machine equivalence.
  The discharge symmetry of §2 extends unchanged, each quantitative fragment
  getting the complete problem that is its syntactic image (ΣQSO(FO) ↔ #SAT,
  QFO(LFP) ↔ FP). Note that the output number lives in Lean, computed by the
  evaluator, so the representation taxonomy of §0 constrains only the numbers
  inside *instances*, never the value of a counting problem.
- **#SAT complete for ΣQSO(FO)** [M–L]: the high-value target, and probably the
  cheapest route to a headline result. Tseitin gates preserve solution counts
  precisely because they are functionally determined, and `exists_gates`
  (`∃ gates. CNF(atoms, gates) ↔ φ(atoms)`) already exists in the QBF
  development; strengthen it to `ExistsUnique` and the Cook–Levin discharge
  becomes parsimonious.
- **The free catalog entries** [S each]: reductions already bijective on
  solutions are parsimonious almost by inspection, notably 1-in-3-SAT → Exact
  Cover (no order, no gadget, no counting, dimension 1: covering `x` once *is*
  an assignment) and Set Splitting. Also #3COL and the permanent as new
  entries.
- **Structure inside #P** [R]: the ΣQSO(FO)-hierarchy tracks the #FO one but
  diverges at the bottom (`#Σᵢ ⊊ ΣQSO(Σᵢ)` for `i = 0, 1`, coinciding from Π₁
  up; ΣQSO(Σ₀) and #Σ₁ incomparable), and the gap is the point: #Σ₁ has an
  FPRAS but is not closed under sum; ΣQSO(Σ₁) is, but subtraction by one is
  open (conjectured to fail); ΣQSO(Σ₁[FO]), allowing FO subformulas as atoms,
  is closed under sum, product and subtraction by one, sits in TotP and has an
  FPRAS everywhere (that subtraction proof is the paper's hardest, turning on
  logarithmic-size witnesses a fixed formula can identify and delete). A
  Grädel-style Horn restriction ΣQSO(Σ₂-Horn) has #DisjHornSAT as a natural
  complete problem under parsimonious reductions, rhyming with the SO-Horn
  layer already in the library.
- **Quantitative least fixed point** [R, deferred]: the support-based `lsfp`
  needed for QFO(LFP) = FP and for #L. It needs its own monotonicity and
  termination argument; `derivesIn`/`depth` in the FO(LFP) layer is the right
  precedent.
- **Optimization: MaxSNP** [R, deferred furthest]: Papadimitriou–Yannakakis's
  syntactically defined optimization classes (Π₁-definable objective),
  L-reductions, MAX-3SAT completeness; MaxQSO/MinQSO is the definitional route
  to the same territory. L-reductions are approximation-preserving and far more
  delicate than parsimonious ones, which is also why PCP-based hardness of
  approximation stays out of scope.

Beyond the library, the counting track is the direct bridge to provenance-lean:
the counting provenance semantics of a query is exactly a model count, so the
two libraries would meet here, with semiring provenance as the common
generalization (and QSO's weighted-logic ancestry is the same idea from the
other side).

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
| L | FO(DTC) | S | S | done, as a capture theorem – see below |
| NL | FO(TC) | S | S | done, as a capture theorem – see below |
| Σₖᵖ, Πₖᵖ | `Σₖ`-SO | M (reuses the NP membership) | M (reuses the SAT machine) | +0.6–1.2k [M] |
| PSPACE | SO(TC) | S [done] | L–XL [done, ~3.2k] | ~3–5.5k |
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
   (400–700 lines). Confirmed by `Problems/Machine/Space.lean`, which came in at
   ~840: the estimate missed only the sentence-builder layer, an `SOTCSpec`
   wanting *sentences* rather than formulas with parameters.
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
- **L and NL: the Turing model is the wrong one** [done, kept for the judgment
  it records]. As machine-as-data, logspace Turing machines are cheap for a bad
  reason: a logspace configuration is a constant-length tuple of elements, the
  configuration space is polynomial, and acceptance is REACH up to renaming –
  true, easy, contentless. The model that says something is a fixed finite
  control with `k` two-way heads on universe elements, reading only
  quantifier-free tests of its head tuple, so that determinism vs.
  nondeterminism is L vs. NL, mirroring FO(DTC) vs. FO(TC); it is Lean-level
  data, so both halves are *capture* theorems (`mem_LOGSPACE_iff_automaton`,
  `mem_NL_iff_automaton`) rather than completeness results. Rejected models:
  registers (must legislate arithmetic; a head move *is* a step in the order),
  JAGs/pointer machines (lower-bound devices), branching programs (nonuniform).
  With BIT (§3), a circuit-family bridge (FO-uniform AC⁰ = FO(≤, BIT)) is more
  natural than any machine at that level.
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
  drift); `#P` as "number of accepting runs" is easy to state but needs the
  parsimonious-reduction notion the framework still lacks (§6, first item);
  the classes-are-logic principle points at `ΣQSO(FO)` for the definition
  either way, with the machine count as a bridge statement.

## 8. Undecidability: RE, by value invention

The one class here whose problems are not decidable at all, and the entry point
to incomputability results proved the same way as everything else: by a
first-order reduction from a complete problem. The defining logic is
**`∃SO[new]`**, existential second-order logic over a universe extended by
finitely many *invented* values ([Abiteboul–Hull–Vianu 1995]
[abiteboul1995foundations], ch. 18): the certificate is a finite extension
`A ⊕ Fin m` with `m` unbounded plus relations over it, checked by a fixed
first-order kernel over the base vocabulary plus a predicate `old` marking the
original elements. Unbounding `m` is the *only* change from `Σ₁`, and it is
exactly the step from "search a space exponential in `|A|`" (NP) to "search an
unbounded space of finite witnesses" (RE).

Built: `SecondOrderNew.lean` (the extended structure, `SigmaSONewDefinable`,
`Σ₁ ⊆ ∃SO[new]`), `Relativize.lean`, the two closure files
(`SecondOrderNewPull.lean` for FO reductions, `SecondOrderNewOrdered.lean` for
ordered ones), `RecursivelyEnumerable.lean` (the class `RE`, with `coRE` and
`NP ⊆ RE`; nothing relates RE and co-RE, by design – `∃SO[new]` has no dual
reading, and the separation is a machine-bridge statement, the last item below),
`Relationalize.lean` (every `∃SO[new]`-definable problem reduces to one over a
relational vocabulary, which is how source vocabularies with function symbols
are handled), Trakhtenbrot's theorem `FINSAT_RE_complete`, and `halt_mem_RE`, whence `halt_le_finsat` – Trakhtenbrot's
theorem in the form it is usually stated, the reduction from the halting
problem. What remains:

- **PCP (Post's correspondence problem)**: the classical target for
  undecidability by reduction. **Defined** (`Problems/Pcp/Defs.lean`): the
  instance is a marked list of domino pairs over an alphabet, ordered by the
  order of the positions of its own words, and a match is a nonempty sequence of
  marked dominoes whose top and bottom words have the same concatenation.

  The [M–L] estimate this item used to carry was wrong, and splitting it is the
  point:
  - **membership** [M, ~2–2.5k]: the match is invented. Four relation variables
    – the slots, their order, the domino at a slot, and a 4-ary variable holding
    the letter-preserving order isomorphism between the two parses – with the
    common word *not* invented at all, its positions being the pairs (slot,
    position in the top word) in lexicographic order. The mathematical content
    is the bridge `pcpOn_iff_cert`, whose one real lemma is that the sorted
    enumeration of a lexicographic sum is the `flatMap` of the sorted
    enumerations (by uniqueness of sorted enumerations, not by induction).
    Four files: the sorted-enumeration layer, `pcpOn_iff_cert` with its
    relabelling to `Fin m`, the block and guarded kernel, and an umbrella;
  - **hardness** [XL]: *not a catalog item*. PCP is not the syntactic image of
    any logic – a certificate of `∃SO[new]` is a structure with relations, a
    certificate of PCP is a string with two parses – and a PCP instance is
    really a *program*: reading a solution left to right and keeping the
    unmatched overhang makes it a nondeterministic queue machine whose
    transitions the reduction writes. So RE-hardness of PCP *is* the RE machine
    bridge: the discharge must guess a block assignment on unbounded storage and
    then evaluate a first-order kernel against it, every atom test being a random
    access into the guessed table – the “evaluator with tape addressing” priced
    at XL in §7. The honest decomposition is `HALT` (unbounded tape, no step
    bound) as a catalog problem and `HALT ∈ RE` – both done – then `HALT`
    RE-hard [XL, the whole cost] and `HALT ≤ᶠᵒ[≤] PCP` by the classical
    computation-history dominoes [L]. Only the third is blocked, and on effort
    rather than on an idea.

    Three shortcuts fail, and are worth not rediscovering. `HeadEval` does not
    apply: its heads range over the elements of a *structure* and its guards are
    atoms of that structure, so it presupposes the certificate as something
    queryable, whereas a PCP solution is a string and supplying the query is
    exactly the work to be avoided. Laying the certificate out as a grid and
    checking it locally makes the *fan-in* local – partial conjunctions carried
    along the order – but not the **shared atoms**: the value of `R(x₁, x₂)`
    occurs in every cell whose tuple extends it, at a stride of `nʲ` in any
    lexicographic layout, and a stride is not a bounded distance. And reducing
    from FINSAT instead is harder, not easier: the sentence would be input
    rather than parameter, so the instance would have to be a *universal* model
    checker.
- **`RE.Hard HALT`**, i.e. “RE is the class of semi-decidable problems”
  [XL, the same item as the PCP hardness above]: the converse half of the RE
  machine bridge. It needs the evaluator with addressed storage (§7), and it
  buys no statement about any catalog problem – whereas the easy half,
  `halt_mem_RE`, already buys `halt_le_finsat`, and buys the same for every
  future problem shown to be in RE.
- **Undecidability: the bridge to Mathlib's computability layer** [L–XL]. This
  is all that stands between `halt_le_finsat` and Trakhtenbrot's theorem as
  everyone states it; until it exists the honest reading of every result here is
  "complete for the logically defined class RE".

  `ComputablePred` is a predicate on a `Primcodable` type while a
  `DecisionProblem` is a property of finite structures up to isomorphism, so
  something must name instances concretely. **Not** the `Encoding`/`Decoding`
  bundles: what they guarantee is size-honesty, which undecidability does not
  need, and a concrete instance type per problem would be ceremony over data
  that is already a relational structure. The right object is generic: over a
  *finite relational vocabulary* – every vocabulary in the catalog – a finite
  structure is a universe `Fin n` plus a Boolean table, so one `Primcodable`
  type serves the whole catalog at once. In dependency order:

  - **decidable realization** [S]: `Decidable (φ.Realize v xs)` on a finite
    structure with decidable relations, by recursion on the formula. Mathlib has
    no such instance. No dependencies, and it is the first formal justification
    of the README's by-inspection claim that FO reductions are effective;
  - **the concrete instances** [S–M]: `Fin n` plus the table, with its
    `Primcodable` instance. State the table as nested `List`s and *not* as a
    dependent function `(Fin k → Fin n) → Bool`, which is pleasant semantically
    and painful to prove `Primrec` facts about; `Fin n` is already linearly
    ordered, so an *ordered* reduction instantiates with no order to encode;
  - **`RE ⊆ RePred`** [M, and it needs no machine at all – the cheapest real
    payoff here]: for a fixed `m` the extended universe is finite, so there are
    finitely many assignments and the kernel is decidable by the first item;
    unbounded search over `m` makes any `P ∈ RE` an `REPred`. This turns the
    class's name into a theorem, and with `halting_problem_not_re` it is what
    lets a problem be shown *not* to be in RE – the co-RE separation this
    section has always lacked;
  - **FO reductions are computable** [M], whence `¬ComputablePred` transfers
    backwards along `≤ᶠᵒ`, `≤ᶠᵒ[≤]` and `≤ʳᶠᵒ[≤]`. The `Primrec` work
    concentrates not in the interpretation but in the *renumbering* a
    relativized reduction forces: the image universe is a subtype, so the
    surviving points must be listed and re-indexed, `iso_invariant` carrying
    correctness across;
  - **the halting link** [L–XL, the piece that can slip]: a computable map from
    an undecidable set into the concrete instances of `HALT`.
    `ComputablePred.halting_problem` is about `Nat.Partrec.Code.eval` and
    `Mathlib/Computability/TMToPartrec.lean` is the meeting point with a machine
    model – check which direction of that chain it gives before committing. The
    page-structured tape helps: take the positions to be the `|w|` input cells
    and the tape is *blanks · w · blanks*, an ordinary two-way tape, so the
    simulation is a renaming of cells. Three details bite: Mathlib's TM0 halts by
    having *no* transition apply while `AcceptsU` wants an accepting state;
    `Turing.Tape` is a `ListBlank` on each side, so its correspondence with a
    finitely supported `ℤ → Γ` is a lemma; and `WellFormed` has to be
    established of the built instance.

  Then `HALT` is undecidable and `FINSAT` with it, and every future
  `HALT ≤ᶠᵒ[≤] X` makes `X` undecidable – in particular **Post's problem**,
  whose classical theorem therefore needs the dominoes of the PCP item above but
  *not* RE-hardness of PCP.
- **Housekeeping left by the FINSAT build** [S each]: `lexLtF`/`lexLeF`, which
  decide the lexicographic order on `D`-tuples, sit in `Problems/FinSat/Nodes.lean`
  but belong in `OrderWalk.lean` next to `succTupF`, which walks that order
  without deciding it; `Nodes.lean` imports `Sat/Tseitin.lean` for `NodeAt`, and
  if that cross-problem dependency ever grates the node machinery is generic and
  belongs at top level; and `extBase` could be given an *equivariant* junk
  convention – the value on a tuple with an invented argument is its first
  invented argument – which would remove the `[L.IsRelational]` hypothesis from
  `extEquiv` and the `[Nonempty A]` from `extBase`. The last is a change to
  `SecondOrderNew.lean` and its three dependents, so a decision rather than a
  chore.

## 9. Teaching material

- **Reduction cookbook** [M]: grow the `Examples/` directory (which now holds
  the first tutorial-style worked example, Boolean conjunctive queries) into a
  curated example set (cf. Grange et al., MFCS 2024) as the catalog broadens,
  so the library doubles as a complexity-course companion.

## Suggested ordering (value vs. prerequisite chains)

Ordered for headline theorems not yet formalized anywhere, maximal reuse of
machinery that already exists, and low risk of an item turning out to be
blocked.

**The serial line:**

1. **A sharpening pass on what is already public** (each [M], no
   prerequisites, no new surface): the **PH machine bridge** (§7), closing the
   visible asymmetry of a bridge that exists for NP and PTIME but not for the
   hierarchy they sit in; **quantifier-free / projection / dimension tracking
   through composition** (§3's reduction-notion refinements), which upgrades
   catalog statements to the DC-faithful "complete under qfps"; **Spectra**
   (§4) and **CVP from HORN-SAT** (§2), two near-free recognizable names, the
   latter also the discharge Immerman–Vardi wants. Note what 3-DNF-TAUT (done)
   taught about the first of these: a discharge that needs an *image* invariant
   the `≤ᶠᵒ` interface hides does not force a general invariant-tracking layer,
   because building the reduction from the complement side keeps the promise in
   hand where it is proved. Reach for tracking when a second consumer appears,
   not before.
2. **PSPACE, the one open piece**: SO(TC), the class, SUCCINCT-REACH, QSAT,
   `PSPACE = coPSPACE` and `PH ⊆ PSPACE` are done, as is the membership half of
   the machine bridge; what is left is its hardness half
   (`QSAT ≤ᶠᵒ[≤] DTMAcceptSpace`, in progress), and after
   it FO(PFP)/FO(LFP) as the textbook-faithfulness layer and Immerman–Vardi.

**Running alongside, from the start:**

- **The counting track of §6**, as far as #SAT plus the free catalog entries.
  Promoted above PSPACE deliberately: PSPACE repeats a shape the library
  already executes (define a fragment, discharge to its syntactic image),
  whereas counting descriptive complexity has no formalization anywhere and
  ΣQSO's two-layer syntax fits the kernel-as-data idiom unusually well. It
  depends on nothing unbuilt, so it cannot be blocked by the chain above; a
  cheap headline (#SAT complete for ΣQSO(FO)) sits one `exists_gates`
  strengthening in; and it is the meeting point with provenance-lean. Internal
  order: parsimonious reductions → evaluator → `#P := ΣQSO(FO)` → #SAT → the
  free entries; stop there (structure inside #P, the quantitative fixed point
  and MaxSNP are genuine research).
- **EF games + EVEN/connectivity inexpressibility** (§5), as a parallel and
  delegable line rather than the serial next step: it unblocks nothing else,
  and it is the most Mathlib-facing item here, hence where an estimate is
  likeliest to slip. Its own headline `FO ⊊ FO(TC)` is blocked on nothing –
  the FO(TC) layer exists – only on the games themselves. Also the best student
  project in the document.

**Deferred, and deliberately so:**

- Catalog growth (§1) as opportunistic filler now that Karp's 21 is done. Check
  FO-expressibility of the 3DM → 3-Partition arithmetic *before* committing: it
  is the one item with a real chance of being unbuildable.
- Relativized membership closure and FO(LFP) ⊆ NP directly: correctly parked,
  neither buys a new statement.
- The BIT / FO(≤, BIT) / AC⁰ / PARITY chain: a multi-year project with three
  [R] items and a switching lemma at the end, to be decided as a whole rather
  than drifted into via representation (D). Until then the by-inspection AC⁰
  claim in the README stays an honest, documented gap.
- Abiteboul–Vianu and the exponential classes.

This weighting assumes the goal is research output and formalization firsts. If
the near-term goal is the course companion of §9, the cookbook and catalog
growth move up and PSPACE slides down: students meet NL, P-completeness and
reductions long before they meet SO(TC).


## The PSPACE machine bridge, as built (2026-07-29)

~4.1k lines over nine files; the §7 estimate of L–XL for hardness was right.
What the plan did not anticipate:

* **Prove hardness for the deterministic problem, not the nondeterministic
  one.** Hardness travels *forward* along reductions, and
  `DTMAcceptSpace ≤ᶠᵒ NTMAcceptSpace` is nearly free (the identity
  interpretation with the accepting predicate guarded by the determinism
  sentence). Proving `NTMAcceptSpace` hard first would have forced Savitch on
  the machine side — a recursive-doubling machine with a stack. Avoided
  entirely; the only Savitch in the library stays the logical one, inside
  `Problems/Qsat`.
* **Reduce from QSAT, not SUCCINCT-REACH.** A deterministic machine has to run
  an algorithm; QBF evaluation is one, succinct reachability has none.
* **The evaluator is not needed.** §7 predicted the PSPACE discharge would need
  an evaluator compiling arbitrary formulas of the logic into a machine. It did
  not: reducing from QSAT means compiling *one fixed* algorithm, exactly as the
  SAT machine compiles one fixed clause check.
* **No step budget is a real saving.** `AcceptsSpace` is `ReflTransGen`, so the
  `bitRank` arithmetic and filler cells of the NP bridge disappear, and the
  converse half is free from `Relation.ReflTransGen.total_of_right_unique`
  (`Problems/Machine/DetRun.lean`): exhibit one run ending stuck and
  non-accepting, and non-acceptance follows.
