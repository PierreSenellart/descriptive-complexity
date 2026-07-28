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
SO-Horn → HORN-SAT and SO-Krom → 2SAT (the last two sharing their scaffolding
in `ClauseDischarge.lean`); the discharges still to do:

| fragment | complete problem | note |
|---|---|---|
| SO(TC) (PSPACE) | SUCCINCT-REACH [done], then QSAT | the fragment, the class and the syntactic image are done: SUCCINCT-REACH is PSPACE-complete (`Problems/SuccinctReach/`), its discharge being the Tseitin translation of the three sentences of an `SOTCSpec` over the *doubled* block, so that the block's atoms are shared propositional variables across the three clause groups; QSAT then follows by the standard alternation argument |

- **P-complete reductions from HORN-SAT** [M]: Circuit Value Problem, Monotone
  CVP, and alternating reachability (DC's canonical P-complete problem, with
  quantifier-free-projection hardness in the book), entering the catalog as
  ordinary catalog reductions *from* HORN-SAT rather than as primary discharges.
- **PSPACE: SUCCINCT-REACH** [done]: the syntactic image of SO(TC) – a
  transition system given by three CNFs over marked state variables and their
  next-state copies – is PSPACE-complete (`SUCCINCTREACH_PSPACE_complete`).
  Membership is the four-variable specification `srSpec` (state, transition
  witness, and *two* endpoint witnesses – two rather than one because a
  zero-length walk must meet both endpoint conditions at one state). Hardness
  (`succinctReach_hard_of_sotcDefinable`) is the Tseitin translation run three
  times, over the *doubled* block in all three cases so that the block's atoms
  are shared variables: `Sat/Tseitin.lean`'s semantic interface
  (`satCond_iff_gates`, `gates_realize`, `gates_canonVal`) and
  `Sat/TseitinFormulas.lean`'s builders turned out to be generic enough to be
  reused unchanged — no refactor of `Sat/Hardness.lean` was needed, only a new
  interpretation into `Language.transSys` with the same defining formulas, plus
  three language renamings (`Problems/SuccinctReach/Double.lean`): two block
  copies into the doubled block, one copy into its first half, and a merge of
  the two order symbols the Tseitin builders leave behind when their base
  vocabulary is already ordered.
- **PSPACE: QSAT** [L]: unbounded-alternation QBF, downstream of the above by
  the recursive-doubling (Savitch) construction as an FO interpretation, which
  is why it is no longer the first target. Downstream in turn: game problems
  (Generalized Geography…) [L each, gadget-heavy].
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
- **SO(TC) for PSPACE** [done]: second-order transitive closure logic, TC taken
  over assignments of a block of *relation* variables (reachability in the
  exponential configuration graph); captures PSPACE on ordered structures
  (DC: FO(PFP) = SO(TC) = PSPACE). The cheapness argument of SO-Horn held: the
  TC is Lean-level (`Relation.ReflTransGen` over SO assignments,
  `SecondOrderTransitiveClosure.lean`) with only the FO transition *sentence*
  over the doubled block language object-level, so no fixpoint syntax,
  positivity or stage machinery — and no modes or element tuples either, since a
  relation variable of arity 0 is a bit and one of arity 1 is an element
  register, which is what makes the pullback
  (`SecondOrderTransitiveClosurePull.lean`,
  `SOTCDefinable.of_orderedReduction`) purely the block pullback of
  `SecondOrderPull.lean`. The class is `PSPACE` in `PSpace.lean`, with
  `NP ⊆ PSPACE` (an existential block is the walk that guesses and stops) and
  the discharge shape `PSPACE_hard_of_sotcDefinable`. Still open and *not*
  free: `PSPACE = coPSPACE` (Savitch) and `PH ⊆ PSPACE`, neither of which is a
  syntactic inclusion; the latter is expected to come through QSAT. Note: no
  fragment of *plain* SO can play this role: SO = PH (Fagin/Stockmeyer), so an
  SO fragment capturing PSPACE would collapse PH; some iteration/recursion
  operator is unavoidable.
- **FO(TC), the layer as it stands** [done]: the definability layer exists
  (`TransitiveClosure.lean`: `TCSpec`/`TCDefinable`, a single TC over a
  first-order transition formula on `k`-tuples, with `reach_tcDefinable` as the
  canonical instance; a `TCSpec` carries a finite *mode* component beside its
  tuple, the analogue of an interpretation's tags, without which neither the
  translations nor closure under reductions can be stated), and so do both
  translations against the Krom fragment: `co-NL(Krom) = NL(TC)`, i.e.
  `mem_NL_iff_tcDefinable_compl` (`SigmaSOKromDefinable.compl_of_tcDefinable` in
  `TransitiveClosureKrom.lean`, `TCDefinable.compl_of_sigmaSOKromDefinable` in
  `KromTransitiveClosure.lean`), sharpened to `NL(Krom) = NL(TC)` by the
  complementation of FO(TC) (`tcDefinable_iff_mem_NL`). **Closure of
  `TCDefinable` under ordered FO reductions** is done too
  (`TransitiveClosurePull.lean`, `TCDefinable.of_orderedReduction`: the spec is
  pulled back with modes `spec.Mode × (Fin k → Tag)` and tuples of length
  `k · d`), so FO(TC) could be a `ComplexityClass` in its own right – with
  little point, since it coincides with NL through the translations above.
  Nothing is outstanding in this item; it is kept as the map of what the layer
  contains.
- **FO(PFP)** [L, sharing infrastructure with LFP]: PSPACE on ordered
  structures (DC ch. 9–10); SO(TC) above is the cheaper route to the class, so
  this is a textbook-faithfulness layer.
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
- **L and NL: the Turing model is the wrong one** [done].
  As machine-as-data these are cheap for a bad reason: a logspace
  configuration is a constant-length tuple of elements, the configuration
  space is polynomial, and acceptance is REACH up to renaming — true, easy,
  contentless. A telling bridge needs storage matching what the logic's
  variables range over and *local* input access (else the FO-definable table
  smuggles in the whole input). The right model: a **fixed finite control
  with `k` two-way heads** on universe elements, no work tape, reading only
  quantifier-free tests of its head tuple; determinism vs. nondeterminism is
  then L vs. NL, mirroring FO(DTC) vs. FO(TC). The machine is Lean-level data,
  so the statement is a **capture theorem**
  (`TCDefinable P ↔ ∃ k (M : HeadAutomaton L k), ∀ A, P A ↔ M.Accepts A`) —
  no reductions, no string encoding.
  **Done: machine → logic** (`HeadAutomaton.lean`): the model, and
  `tcDefinable_of_automaton` / `dtcDefinable_of_automaton` with their
  `mem_NL_of_automaton` / `mem_LOGSPACE_of_automaton` corollaries. It is
  near-trivial as predicted — a configuration *is* a `TCSpec.Node`, the control
  being the mode — and determinism of the control lands on `TCSpec.det` through
  `functional_toSpec`.
  **Done: logic → machine, nondeterministically** — so the NL half is a capture
  theorem on the nose: `tcDefinable_iff_automaton` and `mem_NL_iff_automaton`
  (`HeadCapture.lean`), on top of two reusable layers.
  1. `HeadProgram.lean` — the *assembly language*: the same machines with their
     transitions presented one at a time, each with its own quantifier-free
     guard, and with two exits so that fragments compose. A fragment's spec is
     `Runs` (exact soundness, completeness up to the scratch heads); everything
     is assembled with one combinator, `wireP` (a finite family of fragments,
     one per node of a control graph), whose lemma `runs_wireP` reduces runs to
     a *walk in the control graph*. The workhorse under it is
     `Embeds.reach_cases`: a run that starts inside a fragment either is still
     inside it or has left it by one of its exits. Two compilations back to
     `HeadAutomaton` (all enabled transitions, or only the first — the latter
     syntactically deterministic).
  2. `HeadEval.lean` — the *evaluator*, and the surprise is how cheap it is once
     quantifiers are *walked* rather than read: `decides_evalP` is a structural
     recursion on the `BoundedFormula`, atoms being guards, implication a branch
     (`iteP`), and a quantifier a sweep (`scanP`) of **two** fresh heads. Two,
     not one, is the design point: the sweep must know when to stop, and "this
     head is at the greatest element" is not a quantifier-free fact of one head,
     while "these two heads are equal" is an atom — so one head walks and one is
     parked at the maximum. No subroutine calculus was needed, and no
     normalization to prenex or to quantifier-free specifications; the sweep is
     proved by `order_induction_down` (added to `OrderWalk.lean`), the direction
     that knows about the elements a walker has not yet reached. The evaluator
     is deterministic, which is what makes it reusable for L.
  The driver in `HeadCapture.lean` is then a control graph: pick a source mode
  (a chain of free choices, since `wireP`'s wiring is a function of the exit
  bool — that chain is how a nondeterministic *mode* choice is expressed), guess
  the tuple and test the source formula, then loop {test the target formula and
  accept; else pick a candidate mode, guess the candidate tuple, test the
  transition formula, commit by copying}. Soundness is an invariant along the
  control walk, completeness an induction along `TCSpec.Reach` with an escape
  clause (if the target formula holds early, the machine has already accepted).
  **Done: the deterministic capture** — `dtcDefinable_iff_automaton` and
  `mem_LOGSPACE_iff_automaton`, `DTCDefinable P ↔ ∃ k (M) (hdet :
  M.IsDeterministic), …`. What a deterministic driver adds is *search where the
  nondeterministic one guesses*, and a bound on its own walk. Four layers:
  - `WalkBudget.lean` — the two counting facts, both machine-free.
    `stepNext`/`reach_iff_iterate` walk a functional relation as an iterated
    function, and `exists_iterate_lt_card` is the pigeonhole that bounds it: a
    reachable node is reachable in fewer steps than the type has elements, since
    a shortest walk cannot repeat. `Ticks n z` says `n` covers are available
    above `z` in a finite linear order, and `ticks_of_orank`/`ticks_bot` supply
    them from `orank` — at the bottom, one tick short of the whole order. The
    two meet by counting nodes and counter values with the same number.
  - `HeadLex.lean` — the **odometer** `lexNextP`: the lexicographic successor of
    the tuple on a block of heads, exiting `false` at the greatest tuple. The
    chain walks the positions from the last and steps the first one that is not
    at its greatest value, resetting those after it. Since "this head is at the
    greatest element" is not a quantifier-free fact of one head, the block comes
    with a **marker head** parked there and the test is the atom "these two heads
    are equal"; accordingly `lexRel` is stated by the marker's *value*, an honest
    description whatever the marker holds, and `tupSucc_of_lexRel` turns it into
    `OrderWalk`'s `TupSucc` where the marker is known to be at the top — so the
    scan becomes a walk along covers of `Lex (Fin n → A)` like any other.
  - `HeadCaptureDet.lean` — **the machine, its soundness and its
    completeness**. The machine: the control graph
    `DetNode` (source scan, walk, candidate scan, commit, tick), its fragments
    `dFam`, its arcs `dWire`, the four-block head layout (current tuple,
    candidate, source, counter) with `dHeadAgree_iff` (the protected heads are
    exactly the blocks and the marker), the relations `dRel` its fragments run —
    all of them proved (`runs_dFam`) and local (`headLocal2_dRel`) — and the
    invariant `dInv`: at any node of the walk phase the first block holds a node
    reachable from a source, and at `commit` the candidate is one deterministic
    step away. It is carried along every arc (`dInv_of_walk`), and at the
    accepting arc it says the specification accepts (`accepts_of_dExit`). So the
    machine provably never lies.
    The **search for the successor** is proved in full, both ways. Over the
    tuples of one mode: `scanFound` (if the current node's successor — unique, by
    `det_step_iff` — is in the mode being tried, with a tuple at or above the
    block's, the scan walks the block up to it and reaches `commit` holding it)
    and `scanNone` (if there is none in that mode, the scan runs the block to its
    greatest tuple and moves on), both inductions downwards along the
    lexicographic order in the style of `decides_scanP`, resting on
    `HeadLex.exists_lexRel_succ` and `lexRel_top` — that the odometer can always
    step below the greatest tuple and exactly fails at it. Over the modes:
    `modeFound` and `modeNone`, inductions on the number of mode indices left. So
    from `candMode` the machine provably reaches `commit` holding the successor
    when there is one and `srcNext` when there is none, leaving the current
    tuple, the source and the counter alone in both cases.
    One **step of the simulated walk** follows: `walkStep` — at a node that is
    not accepting but has a successor, with a counter block that can still be
    stepped, the machine tests the target formula, searches out the successor,
    commits it onto the current block and ticks, arriving at `tgtTest` one node
    along with the counter advanced by one in the lexicographic order.
  - **Completeness**, and the one idea that made it short: read the counter as a
    value of a *single* finite linear order, `dcount` — the index of its mode
    lexicographically above the tuple on its block (`OrderWalk`'s
    `prodLex_covBy_iff` and `finCovBy_iff` are that order's covering lemmas).
    Then a tick *is* a cover (`dcount_covBy_tup` inside a mode,
    `dcount_covBy_mode` across one), the order has exactly as many values as the
    specification has nodes (`card_dcount`), and both inductions run along it.
    `dTick` packages one tick; `walkAcc` — the walk reaching an accepting node
    within the budget makes the machine accept — is an induction on the steps
    left, `Ticks` supplying the cover at each; `walkOut` — whatever happens, the
    machine accepts or comes back to `srcNext` with its source block untouched —
    is an induction *downwards along the counter*, which is the termination
    argument, with `dcount_of_isTop` (at the top the tuple is greatest and the
    mode last, so `tickReset` falls through to the next source) and `walkStuck`
    (nowhere to go: the chain of candidate modes is exhausted) as its two ends.
    `srcEnum` then enumerates the sources downwards along the *same* order,
    `srcTried` (`walkOut` with the `start` arc in front) returning to `srcNext`
    and the odometer advancing the position by one cover. `accepts_dP` conjoins
    the halves, and `compile true` — syntactically deterministic whatever the
    guards, and agreeing with the program where they are exclusive, which
    `deterministic_dP` says they are — gives the automaton.
    Two notes for the next machine built this way. The budget is *exactly* tight:
    a walk visits at most `card Node` nodes, so it takes at most `card Node - 1`
    steps, and a counter with `card Node` values ticks exactly that often — there
    is no slack to spend, which is why the counter has to carry a mode as well as
    a tuple. And phrasing both inductions as `order_induction_down` over one
    order, rather than as nested inductions over modes and tuples, is what keeps
    the two walk arguments to a page each.
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

Done so far:

- `DescriptiveComplexity/SecondOrderNew.lean` — the extended structure, the
  definability notion `SigmaSONewDefinable`, functoriality in the base
  isomorphism, congruence on finite instances, and `Σ₁ ⊆ ∃SO[new]`
  (`SigmaSODefinable.toNew`, the future `NP ⊆ RE`), whose kernel is guarded by
  "nothing was invented" so that the `∃m` cannot be satisfied spuriously.
- `DescriptiveComplexity/Relativize.lean` — relativization of a formula to a
  unary relation symbol (`relativizeTo`), correct against the `Substructure`
  the symbol defines (so it covers vocabularies with function symbols, which
  the `ComplexityClass` interface forces since the *source* language of a
  reduction is arbitrary); `relOld` is its instance at the marker `old`.
  Reusable for the relativized *membership* pullback of §3.
- `DescriptiveComplexity/SecondOrderNewPull.lean` — **closure under FO
  reductions** (`SigmaSONewDefinable.of_foReduction`). The construction worth
  not rediscovering: *do not* guess an isomorphism, and do not reach for
  `RelSecondOrderPull` (§3). With the **same** number of invented values, the
  target's extended universe `I.Map A ⊕ Fin m` is *definable inside* the
  source's `A ⊕ Fin m` — an interpreted point is a tag with `dim` original
  coordinates, an invented value is itself — so it is the universe of a
  `RelFOInterpretation` with tags `Tag ⊕ Unit` and dimension `dim + 1`, and the
  existing guarded pullback `RelFOInterpretation.pullRel` does the translation,
  relativizing quantifiers and substituting the defining formulas in one pass.
  Two details that are not optional: the spare coordinate of an interpreted
  point must be pinned to a **guessed canonical element** (a unary variable with
  a uniqueness guard) — pinning it to a coordinate of the tuple fails at
  `dim = 0`, where `I.Map A` is constant-size; and the interpretation's own
  defining formulas, which quantify over `A`, must be read through `relOld`.
  The block transfer is the *flipped* one a definable universe forces
  (`targetAssign` restricting, `sourceAssign` extending by junk, exact in that
  order), which is enough because the block is existential.

- `DescriptiveComplexity/SecondOrderNewOrdered.lean` — closure under **ordered**
  FO reductions, by re-quantifying the order inside the guessed block as in
  `SecondOrderOrdered`, with the guard **relativized to `old`**
  (`extLinearGuard`): the order symbol of an extended structure relates original
  elements only, so an unrelativized linear-order guard is unsatisfiable as soon
  as something is invented. `sigmaSONewDefinable_of_orderPull` is the
  order-elimination step on its own, the `∃SO[new]` analogue of
  `sigmaSODefinable_of_orderPull`.
- `DescriptiveComplexity/RecursivelyEnumerable.lean` — **the class `RE`**, a
  `ComplexityClass` by the two closures, with `coRE`, `NP ⊆ RE`
  (`NP_subset_RE`), `coNP ⊆ coRE`, and `hard_RE_iff` (cofinal hardness is the
  usual notion over a relational vocabulary). Nothing relates RE and co-RE, by
  design: `∃SO[new]` has no dual reading, and the separation is a machine-bridge
  statement (last item below).
- **Trakhtenbrot's theorem** [L, the next step]: finite satisfiability of a
  first-order sentence is RE-complete. Membership is nearly definitional —
  invent the model and check satisfaction — but "check satisfaction" is the
  catch: satisfaction of an *input* sentence is not first-order in the sentence,
  so the instance vocabulary must present the sentence as a structure (a parse
  forest) and the kernel must verify a guessed satisfaction relation over
  subformula/valuation pairs, in the style of the FO(LFP) rule systems. This is
  the file that decides whether the sentence-as-instance encoding is shared with
  §7's machine layer. Hardness is the `∃SO[new]` discharge: the syntactic image
  of the logic, exactly as SAT is the image of `Σ₁`.
- **PCP (Post's correspondence problem)** [M–L, after Trakhtenbrot]: the
  classical target for undecidability by reduction, and the natural second
  complete problem; instance is a marked list of domino pairs over an alphabet,
  a solution an invented sequence of indices with the two concatenations
  guessed as invented strings and matched position by position.
- **What incomputability actually needs** [R, separate]: RE-hardness alone does
  not yet say "undecidable" inside this library — that statement needs the
  other side, RE ⊆ (Mathlib's) `RePred` through an encoding of finite
  structures, plus a co-RE problem shown not to be RE. Mathlib's computability
  layer (`Nat.Partrec`, `ComputablePred`, the halting problem) is the target,
  and the `Encoding`/`Decoding` bundles are the bridge; this is the same
  standing-scope question as §7's converse compilation, and the honest reading
  until it exists is "complete for the logically defined class RE".

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
2. **The NL layer, cheapest piece first**: **SO-Krom** before FO(TC). Done —
   the fragment, its closure under reductions, the class `NL`, **2SAT
   NL-complete** (membership by a Krom program, hardness by the Krom
   discharge), the inclusions `NL ⊆ PTIME` and `NL ⊆ NP` (through 2SAT, since a
   Krom kernel is not a Horn kernel), UNREACH defined in the Krom fragment, the
   **FO(TC)** definability layer with its two translations against the Krom
   fragment, **Immerman–Szelepcsényi** on top of them, and **REACH
   NL-complete** (membership through the complementation of FO(TC), hardness by
   the FO(TC) discharge, whose interpretation is the graph of the walk itself).
   This step is complete: **FO(DTC)**, the class **LOGSPACE** and **REACHd**
   closed it (`TransitiveClosureDet.lean`, `TransitiveClosurePull.lean`,
   `DetLogSpace.lean`, `Problems/ReachabilityDet.lean`).
3. **PSPACE**: SO(TC), the class, and SUCCINCT-REACH's PSPACE-completeness are
   **done**; next is QSAT by recursive doubling (as a reduction from
   SUCCINCT-REACH, both sides being concrete propositional objects), then
   `PH ⊆ PSPACE` through it, and `PSPACE = coPSPACE` (Savitch) which no
   syntactic argument gives; afterwards FO(PFP)/FO(LFP) as the
   textbook-faithfulness layer and Immerman–Vardi.

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
  its own headline `FO ⊊ FO(TC)` waits on step 2 anyway, and it is the most
  Mathlib-facing item here, hence where an estimate is likeliest to slip. Also
  the best student project in the document.

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
