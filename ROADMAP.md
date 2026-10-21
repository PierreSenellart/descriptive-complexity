# Roadmap

Catalog of work **not yet done**, and of nothing else: an item is deleted when
it is built, never annotated as finished, the record of what the library
contains being `git log` together with the module docstrings. Organized by
theme; each item carries a rough scale of effort ([S] short, [M] medium, [L]
long, [R] research-level, i.e., the Lean proof would itself be a contribution)
and its prerequisites.
Main source: Immerman, *Descriptive Complexity* (DC below); also Garey–Johnson
and Karp's 21 problems for the catalog.

## 1. NP-complete problems (catalog growth)

Beyond Karp's 21:

- **X3C** [M–L]: exact cover by 3-sets, from 3-Dimensional Matching or from
  Exact Cover; local gadgets, probably ordered.
- **3-Partition** [L]: strongly NP-complete, so the unary representation
  suffices and the hardness claim is honest; the classical source for
  packing/scheduling reductions. Warning: the 3DM → 3-Partition reduction is
  arithmetic-heavy; check FO-expressibility carefully before committing.
- **Bin Packing** [M after 3-Partition]: the standard downstream of
  3-Partition.

## 2. Complete problems for other classes

**Discharge symmetry** (guiding principle): each class-defining fragment (§3)
has a canonical complete problem that is essentially its *syntactic image*, so
each hardness discharge is a Tseitin-style translation of the defining logic
into the problem's vocabulary, i.e., a variation on
`sat_hard_of_sigmaSODefinable` with a shape invariant carried through. The
pattern is instantiated for every fragment the library defines: ∃SO → SAT,
SO-alternation-level-`k` → QBF_k, SO-Horn → HORN-SAT, SO-Krom → 2SAT (the last
two sharing their scaffolding in `ClauseDischarge.lean`), SO(TC) →
SUCCINCT-REACH and ∃SO[new] → FINSAT, so no discharge is outstanding; what
remains below are ordinary catalog reductions, drawings out of a machine, and
machine bridges.

- **Monotone CVP** [M]: the unit-propagation circuit is monotone as drawn, so
  this is a matter of restricting the vocabulary rather than of a new gadget.
  The textbook route, [Vollmer 1999][vollmer1999introduction] Thm 4.87, is a
  dual-rail doubling of CVP (every gate becomes `g⁰, g¹`; dimension 1, two tags,
  order-free), and CVP's semantics being dual-rail already (`GateVal`), its
  correctness is nearly the semantics itself. **NAND-CVP / NOR-CVP** (Thm 4.88)
  are the same kind of vocabulary restriction.
- **The rest of the classical PTIME catalog** (Vollmer §4.6, Fig. 4.5), each
  with the shape its textbook reduction takes here:
  - **GEN** [M] – is `t` in the closure of `S ⊆ X` under a binary operation?
    Vocabulary: a ternary `∘`, a unary `S`, a marked target. Membership is a
    direct LFP. Do **not** take the book's `UNIT → GEN` step (Thm 4.93), whose
    universe is “all subclauses”, exponential in the clause width; reduce from
    HORN-SAT with binary bodies instead, where `x ∧ y → z` *is* `x ∘ y = z`, so
    GEN is nearly the syntactic image of the Horn closure.
  - **UNIT** (unit resolution derives the empty clause) [M]: Tseitin clauses
    per gate of a CVP instance (Thm 4.92), order-free; the node machinery of
    `Sat/Tseitin.lean` is what it needs.
  - **LFMIS** (lexicographically first maximal independent set, the classical
    “greedy is P-complete” problem) [M–L]: ordered by nature, and the reduction
    (Thm 4.90, from NOR-CVP) needs a *topological* order of the gates, which the
    library's CVP carries no trace of – reduce from HORN-SAT's propagation
    order or from an ordered CVP variant instead.
  - CFGMEM (context-free membership, Thm 4.94) needs the grammar-and-word layer
    ruled out below; skip.
- **PSPACE, downstream of QSAT** [L, gadget-heavy]: the game problems
  (Generalized Geography…), the only PSPACE entries still missing.
- **Succinct problems, drawn out of the wide machine** [L each]: the classical
  second complete problems of the exponential classes are the succinct forms of
  polynomial ones, and the route to them is the machine, not the logic. A
  problem carrying its own locality is *drawn* by a reduction from a wide
  machine's run – which is how both tilings were reached
  (`Problems/Wide/TilingHard.lean`, `Problems/Wide/CorridorHard.lean`) – whereas
  proving it hard from the class's logic directly is a second construction of
  the same size. The generic succinctness theorem is **not** available as a
  route (§3), so each succinct problem is its own drawing.
  - **Succinct GAME** [L]: `GAME` is complete for PTIME already
    (`game_PTIME_complete`), and its succinct form is the classical
    EXPTIME-complete game problem. Bibliography to fetch from DBLP when the item
    is built – nothing from memory, nothing from a search snippet:
    `veith1997formulas` (Veith, *Languages represented by Boolean formulas*,
    IPL 1997), `gottlob1999succinctness` (Gottlob, Leone, Veith, *Succinctness
    as a source of complexity in logical formalisms*, APAL 97, 1999) and
    `balcazar1992succinct` (Balcázar, Lozano, Torán, *The complexity of
    algorithmic problems on succinct instances*, 1992, a survey).
- **EPR's hardness** [XL, low confidence]: `∃*∀*` satisfiability is
  NEXPTIME-hard ([Lewis 1980][lewis1980complexity]). The problem, its
  small-model property and its membership are built (`Problems/Epr/`); what is
  left is Lewis's simulation, and it is the real cost. Three things settle its
  shape, each paid for by the membership. **Reduce from a machine, not from a
  tiling**: a universally quantified matrix cannot say “*some* cell carries an
  accepting tile”, an existential over exponentially many cells, while a
  machine's acceptance pads the run to the clock and reads the *last* row, whose
  coordinates are a fixed bit-vector, so the condition is a guarded clause.
  **Coordinates are bit-vectors indexed by the instance**, one universal
  variable per element per coordinate, so an emitted symbol has arity `2n+1` –
  unbounded arity is what the encoding is for, and `sig` already carries it.
  **The increment of a coordinate needs auxiliary relations**, defined by
  clauses along the order of the instance: a carry chain is a disjunction of
  conjunctions and no single clause is that, whereas “agree above `k`” and “all
  ones below `k`” are forced upward by implications of fixed width, and upward
  is the direction the reduction needs.
- **Ruled out for these classes, and why** – do not re-propose: Datalog combined
  complexity (EXPTIME) is too domain-specific for a catalog meant to read as
  general complexity theory; regular-expression inequivalence with squaring
  (EXPSPACE, Meyer–Stockmeyer) needs an automata-and-regex layer that does not
  exist; Petri net coverability (Rackoff) and the commutative semigroup word
  problem (Mayr–Meyer) are counter machines, and unbounded counters fail the
  “numbers must be bitwise definable” rule; generalized chess, checkers and Go
  (EXPTIME) are tiling-scale simulations with a board layer on top.
- Δₖᵖ and oracle classes are blocked on machine models, presumably forever out
  of scope (§6 refines both judgments).

## 3. Logics and framework extensions

- **Exposure, and the `import all` inventory** [M, after the module system has
  settled]: public definitions are all exposed, so clients and the library's
  own files can unfold them. Opacity is the remaining knob of the module system,
  and it is sharper than it looks: a public definition without `@[expose]` is
  opaque even to the public theorems of its own file, so hiding the body of an
  interpretation or a gadget formula requires that every theorem stating a
  definitional fact about it be private too. Pick the definitions whose bodies
  are genuinely implementation (the formulas of a reduction, the encodings)
  and give them `@[no_expose]` together with that discipline, in one pass per
  layer with a full build each. Alongside, the two thousand `import all` edges
  record every cross-file use of a private declaration; where a cluster of
  files shares the same helpers, the helpers are an internal API and should
  become public in a module of their own, which also shrinks the private
  oleans a module loads.
- **FO(LFP) ⊆ NP, directly** [M]: by guessing the fixed point and the derivation
  order and checking both first-order against the certificate interface
  (`derives_eq_of_closed_of_wf`). No new mathematics – the inclusion already
  follows by composing the FO(LFP) → SO-Horn translation with the Horn discharge
  – but the direct `Σ₁` definition would be textbook-faithful; the work is
  formula building, made tedious by the varying arities of a block's atoms.
- **Housekeeping in the shared machinery** [S]:
  `Problems/FinSat/Nodes.lean` imports `Sat/Tseitin.lean` for `NodeAt`, so if that
  cross-problem dependency ever grates, the node machinery is generic and
  belongs at top level. Beside it: `blockSym` / `repAssign` /
  `altAssign_qbfBlocks` in `Problems/Qbf/Membership.lean` are the monadic
  special case of `SecondOrderReplicate.lean` and should be folded into it –
  noticed while building the PH bridge, left alone because it touches a working
  file and bought that bridge nothing.
- **Composing an expansion with an interpretation, the outer way** [settled –
  do not reopen]: `DescriptiveComplexity.ExpExpansion.pullOrdered` composes an
  interpretation *before* an expansion (`A ↦ X.Map (I.Map A)`) and is what makes
  `ComplexityClass.exp` a class. The **other** order – an interpretation applied
  to an expanded structure, `A ↦ J.MapRel (X.Map A)` – is what a complete
  problem for an exponential class would need, and it is *not* an expansion:
  an expansion's defining sentences are first-order over the base with the block
  copies as parameters, while a quantifier of `J` ranges over the *points* of
  `X.Map A`, i.e., over block assignments, which is a second-order quantifier
  over the base. So the composite's relations are `Σₖ` over the base, not FO,
  and neither the plain composition nor a Tseitin description of the composite
  exists.
  **Quantifiers are the only obstruction**: an atom `R(x̄)` of `J` translates to
  `X.relSentence`, `x = y` to equality of tagged assignments, and `x ≤ y` to a
  definable order on the expanded universe, all first-order over the base;
  Boolean combinations compose. So the fix is quantifier-freeness, and it is the
  library's version of the side condition the succinctness literature has always
  attached ([Veith 1998][veith1998succinct] states the upgrade theorem for
  *projection* reductions) – though quantifier-freeness alone suffices here,
  projections being a strictly stronger property this framework does not need.
  The order on the expanded universe, the translation lemma and the gate
  `PSPACE = NL.exp` are **built**. Restricting *hardness* to match is
  nevertheless **abandoned**, and the reason is structural rather than
  incidental: every hardness discharge in this library is a Tseitin-style
  translation of a *logic* into the problem's vocabulary, so its defining
  formulas inherit that logic's quantifiers – `hornInterp`'s `guardF` relabels
  an arbitrary carried `L.Formula`, and no engineering removes it. So do not
  build `compQF`, `HardQF`, or the generic succinctness theorem. The honest
  framing: in the literature SAT is complete under first-order projections
  because Cook–Levin is a **machine** simulation, each output bit one cell of a
  tableau at an address computed from the position alone; this library
  discharges from logics and is machine-free by design, which is what costs it
  the succinctness upgrade – a coherent trade, not a defect. §2's succinct
  problems take the machine route instead.
- **`SigmaExpExpansion`, an expansion described by `Σₖ` sentences** [XL,
  optional]: an expansion whose defining sentences are `Σₖ` over the base is
  still computable within polynomial space, so `PSPACE.expΣ = EXPSPACE` and the
  outer composition exists unconditionally *there* – succinct QSAT becomes
  EXPSPACE-complete and the Tseitin discharge above applies, at EXPSPACE and
  nowhere else. §2 reaches the classes without it, so build it only if the
  succinct family is wanted for its own sake. **Never widen `ExpExpansion`
  itself**: `PTIME.exp = EXPTIME` depends on the defining sentences being
  first-order, a `Σₖ`-described instance not being readable in polynomial time,
  so the relaxation is a *second* notion beside the first and not a
  generalization of it.
- **`LOGSPACE.exp = PSPACE`** [M–L]: `LOGSPACE.exp ⊆ PSPACE` is monotonicity,
  but the converse is not the `Exponential/Reach.lean` argument, which asks
  REACH of the graph a walk draws and so lands in NL. It wants that graph read
  *deterministically* – Savitch, or the determinization of the QSAT walk, one
  exponential up.
- **What is left of the BIT layer** [L]: the arithmetic vocabulary and the class
  it defines are **built** (`Arithmetic.lean`, `ArithmeticDefinable.lean`,
  `ArithmeticFixedPoint.lean`, `Problems/Parity.lean`: `AC0Definable`,
  `FO(≤) ⊊ AC⁰`, `AC⁰ ⊆ PTIME`, PARITY in LOGSPACE and not in FO(≤)). `+` and
  `×` are primitive rather than BIT; either choice faces the same closure
  obligation below, schoolbook base-`n` digits for them, base conversion for BIT.
  The sharp bound `AC⁰ ⊆ LOGSPACE` is **built** as well
  (`HeadArith.lean`, `HeadEvalArith.lean`: `plusP` and `timesP` decide the two
  numeric predicates with heads, and `evalArithP` evaluates a sentence over
  them, computing the arithmetic atoms where `HeadEval.evalP` reads its
  atoms), and so is Immerman's Thm 1.17 in both directions (`powArithDef`,
  `timesBitDef`), which makes `FO(≤, +, ×) = FO(≤, BIT)` and its machine model
  a theorem. One item remains.
  * **AC⁰ as a `ComplexityClass`** [XL]: closure under `≤ᶠᵒ` needs the numeric
    predicates of an interpreted universe – lex-ordered tagged tuples, whose
    `tagTupleOrder` rank is a mixed-radix value – defined from those of the
    base. No choice of definable order escapes that: an order is a bijection
    onto `0 … N-1`, so reading such a rank is a base conversion either way, and
    trading `×` for `BIT` renames the crux rather than removing it.

    Why this is not the free closure every class above enjoys, in plain terms.
    The pullback of a sentence along an interpretation substitutes the
    interpretation's formulas for the atoms *of the instance* and relativizes
    the quantifiers; it has nothing to say about `plus`, `times` and `≤`, which
    are not relations of the instance but functions of the target's order, on a
    target universe that is a different set. For `≤` the pullback is the
    lexicographic comparison of tuples, quantifier-free in the base's `≤`, and
    that one line is the whole reason `FO(≤)`, `SO-Horn(≤)`, `FO(≤, LFP)` and
    every other ordered class are closed under `≤ᶠᵒ[≤]` for free. For `plus`
    it is carry propagation over a constant number `d` of base-`n` digits,
    still a fixed formula. For `times` it is schoolbook multiplication of
    `d`-digit base-`n` numbers, and a digit product reaches `(n-1)²`, which no
    element of the base represents: the base's `times` is truncated, so the
    digits must first be split into half-digits in base `⌊√n⌋` (with `⌊√n⌋`
    defined as the greatest element with a square) and `2d` of those multiplied
    – Schweikardt's appendix, below. In one sentence: for the classes above,
    “the logic is closed under interpretations” reduces to “`FO(≤)` defines the
    lex order of `n^d`”, a triviality; for AC⁰ it reduces to “`FO(+, ×)` on
    `n` defines the arithmetic of `n^d`”, a theorem, and one the literature has
    not written out. Circuit complexity never meets it because its reductions
    ([Vollmer 1999][vollmer1999introduction] §1.4, §4.6) are constant-depth
    reductions between *strings*, composed at the circuit level, with the
    uniformity of the composite left to a DLOGTIME machine doing arithmetic on
    `log n`-bit indices – cheap for a machine, dear for a formula, which is
    what recommends the bit-side route below.

    Two routes, priced against each other from the code at ≈ 4 000–7 000 lines
    each; a wash on size, so the decision is risk shape.
    - *FO side*, with `×`: addition by carry-lookahead on `d` base-`n` digits in
      the truncated `PLUS` (`no_plus_iff_card_le` is exactly `x + y ≥ n`),
      multiplication schoolbook, whose double-width digit product needs a
      half-width (base-`⌊√n⌋`) splitting – `M` itself definable as the greatest
      element with a square. That crux is a proof to *transcribe* rather than
      invent ([Schweikardt 2005][schweikardt2005arithmetic] Thm. 3.4, proved in
      an appendix precisely because she knows of no complete published one), but
      it also wants a semantic layer for `2d`-digit vectors – values with no
      `orank` meaning – that the library does not have. Before transcribing,
      check whether `FO(+, Squares) = FO(+, ×)` (Thm. 3.2(f), “not so
      difficult”) lets `arithExtend` define only tuple *squaring*, the product
      following by polarization: half a day, large payoff, if it survives
      truncated arithmetic on tuples.
    - *Bit side*, **preferred**: prove closure for `LTDecidable` at the machine
      level and transport it along `ac0Definable_iff_ltDecidable`. Carry every
      target register in two representations – its `d` source components, and
      its rank's binary chunks, one per source element. The base then runs on
      the binary side (`le` a comparison sweep, `plus` a ripple carry, `bit` a
      read, a target sweep being `d` chained sweeps with the boundary states
      guessed) while the interpretation's `FO(≤)` queries are evaluated on the
      component side through `LogTime/Translate.lean`. All that is new is
      **`Conv`**, the agreement of the two representations, which by Horner is
      `d` rounds of “accumulator times `n` plus a digit” – the exact shape of
      `LogTime/BitSum/Times.lean`'s column sum at `d`-fold width, certificates
      widening from one element to a constant family. Preferred because every
      hard piece re-instantiates an in-house device whose estimate-vs-actual is
      calibrated, because it consumes the machine model just built, and because
      its `d`-chunk element families are the “big number as a family of
      elements” layer FO(COUNT) / TC⁰ would want anyway.

    Two unknowns to burn down first, half a day each: fields tiled across a
    *family* of elements, the one variation of the packing devices never
    exercised (write `LogTime/BitSum/Sizes.lean`'s arithmetic at width `d`,
    check it at `d = 2` on paper), and whether Horner's `d` dependent steps
    collapse into a single `2d`-column convolution. Either route needs the
    **`orank` bridge** – that the rank of a tagged tuple in `tagTupleOrder`
    *is* the mixed-radix value, stated nowhere yet – and both `LEquiv`s are
    against it;
    `LogTime/Small.lean`'s `ArithDef.of_large` already covers the degenerate
    sizes the splitting excludes. The one place this could be *unsound* rather
    than merely incomplete is `arithExtendLEquiv`, the proof that the formulas
    realize the **canonical** arithmetic of that order: “the formula obviously
    says addition” is not an argument, and `ordExtendLEquiv` is the template.
    Note what class-hood does *not* gate: a problem reducing to an AC⁰ problem
    is already in PTIME – indeed in LOGSPACE, by that class's own closure – so
    build it for a consumer and not before. Until then AC⁰ gets **no row** in
    the README's class table, every row there being a `ComplexityClass` closed
    under `≤ᶠᵒ`; the row lands in the same commit as the closure.
- **Quantifier-free projections** [L]: the finest reduction notion (DC uses them
  for almost all completeness results); SAT complete under first-order
  projections.
- **Reduction-notion refinements** [M]: track quantifier-free / projection /
  dimension-1 status through composition (`IsQuantifierFree` is the only status
  tracked); “problem X is complete under qfps” is the DC-faithful statement.
- **FO(COUNT) / counting quantifiers** [L]: with BIT, captures uniform TC⁰;
  relevant to the arithmetic boundary of the binary representation
  (multiplication is TC⁰, not FO: [Vollmer 1999][vollmer1999introduction]
  Cor 1.39 and 3.34). The formulation to adopt is his Cor 4.77: TC⁰ is
  `FO[MAJ; <, BIT]` with a majority quantifier over `k`-tuples, ACC⁰ is
  `FO[∃^{=p}; <, BIT]`, and NC¹ would need a group quantifier for a non-solvable
  group (Cor 4.76) – a Lindström quantifier with no consumer, which settles
  that NC¹ stays out. Its inclusion in LOGSPACE would follow the
  pattern of `HeadEvalArith.lean`: a counting head fragment, evaluated in place
  of an atom. Better, and [M] on top: build the **substitution lemma** the
  counting fragment then plugs into – if each relation symbol of a language `Lx`
  is assigned a deterministic head-program fragment computing it from the heads
  holding its arguments, then every `(L.sum Lx)` formula of the head positions is
  computed by a deterministic head program, hence every sentence over it is
  `DTCDefinable`. `evalArithP` is the `Lx = Language.arith` instance and
  `HeadEval.evalP` the empty one, so `FO(COUNT) ⊆ LOGSPACE` becomes an instance
  rather than a second evaluator. Generalize `evalArithP`, **not** `evalP` (its
  four-way atom split already has the shape, and editing a module 100+ files
  depend on is the trap), keep the arithmetic instance definitionally what it is
  so `ac0Definable_mem_LOGSPACE` need not be reproved, and plan for the full
  downstream rebuild rather than discovering it: `HeadCapture`, `HeadCaptureDet`
  and every consumer of `Runs` re-elaborate.
- **Relativized reductions – the class field** [S–M]: membership closure under
  `≤ʳᶠᵒ[≤]` holds for the classes that have it stated (`SecondOrderRelPull.lean`
  for the hierarchy levels, `FixedPointStepRel.lean` for the fixed-point logics,
  the three corollaries in `FixedPointReductionClosure.lean`), but
  `ComplexityClass` still has no `mem_of_relOrderedReduction` *field*, so nothing
  generic can consume them. Adding it means the field plus the six class-literal
  updates (`empty`, `compl`, `sigmaLevel`, `piLevel`, `PTIME`, `PH`) – note
  `PTIME` no longer needs a Horn-side pullback, the capture theorem routing it
  through `IFPDefinable.of_relOrderedReduction`. Two consumers wait on it: the
  *generic* `C = below Q₀` (the per-class instances in `ClassDegrees.lean` each
  use their own non-relativized hardness discharge, while `cofinalHard_iff`
  yields only `≤ʳᶠᵒ[≤]`), and turning `le_dtmAcceptSpace_of_mem_PSPACE` into the
  `iff` that `mem_NP_iff_le_ntmAccept` has (`Problems/Machine/SpaceHard.lean`
  records why it stops short).
- **FO(LFP) reductions: the classes above PSPACE** [M–L]: `≤ˡᶠᵖ` closes every
  class from PTIME to PSPACE, the levels of the polynomial hierarchy included
  (`FixedPointReductionSpace.lean`, `FixedPointReductionHierarchy.lean`). Above
  that the question is open per class, and the pattern to look for is the one
  that worked twice: find the *iteration* the class's own logic runs, pull it
  back through the interpretation, and gate it on an inflationary stratum that
  computes the reduction's induction (`StepDef.stratifyPFP`). For the
  exponential classes that means SO(LFP) and SO(PFP) over an expansion, where
  the pullback is the part to price – `Exponential/` composes an interpretation
  with an expansion only in one order (§ “Composing an expansion with an
  interpretation”), and this is the other. RE, defined by `∃SO[new]`, is the
  odd one out: its witness is a guess rather than an iteration, so the NP
  argument is the one to copy, with `SecondOrderNewPull.lean` in place of
  `SecondOrderRelPull.lean`.
## 4. Capture and structural theorems (DC's greatest hits)

Three pieces built for Abiteboul–Vianu are the ones to reach for in any capture
attempted here: the order-relativization transfer
(`FixedPointOrderTransfer.lean`, for every statement that moves an order
between instance and vocabulary), stratification of inflationary inductions
(`FixedPointStratify.lean`, for any “define X by induction, then induct over
X”), and the two formula compilers along a definable quotient
(`Invariant/Simulation.lean`, `Invariant/Backward.lean` – the missing dual of
`Relativized.lean`).

- **Circuits, non-uniform, as the consumer of the AC⁰ lower bound** [L]: the
  one reason to build a circuit model here is the §5 separation PARITY ∉ AC⁰,
  and a lower bound holds *non-uniformly*, so the model is a circuit family
  indexed by the size of the structure – a DAG per `n` with unbounded fan-in
  gates, polynomial size, constant depth – and no uniformity machinery at all.
  What it needs from the logic is the **easy** direction only: an
  `AC0Definable` sentence compiles to such a family by structural induction,
  quantifiers becoming gates of fan-in `n`, numeric predicates becoming
  hardwired constants ([Vollmer 1999][vollmer1999introduction] Thm 4.69, `⊆`).
  If the capture theorem is wanted on top [L], the book also settles its shape:
  at constant depth the right uniformity is a condition on the *direct
  connection language* – gate kinds and predecessors decidable in DLOGTIME
  (Def 4.28, Thm 4.31) – and `ac0Definable_iff_ltDecidable` makes that a
  definability condition here, so `Uniform` is a predicate on the same
  `CircuitFamily`: gates are tagged `k`-tuples, the `I.Map` universe of an
  interpretation, and the kind and predecessor relations are `AC0Definable`.
  No machine and no gate-numbering scheme. Both directions are then formula
  plumbing: sentence → family with gates (subformula, assignment) and a
  quantifier-free predecessor relation; family → sentence by `Acc_d` nested
  to the constant depth (Thm 4.69, `⊇`), a finite nesting with no fixpoint.
  Note what neither discharges: the structures-vs-strings bridge of §6 and of
  the README's *Scope* is about string encodings, and no bridge inside this
  framework closes it (the input gates are the tuples of the structure's
  relations, a definition made here rather than transported); and the closure
  of AC⁰ under `≤ᶠᵒ` (§3), which circuit complexity never meets because its
  reductions are constant-depth reductions between strings, composed at the
  circuit level with a machine doing the index arithmetic.
- **Spectra** [M]: Fagin's connection between generalized spectra and NP; mostly
  definitional given the SO layer, historically resonant.
- **`PTIME ≠ EXPTIME` by diagonalization** [R, 5–10k lines, with a real chance of
  being larger]: the sketch, for the record. Let `HORNEVAL` be “the SO-Horn
  program encoded in this instance holds of the structure encoded in this
  instance”. It is in EXPTIME (evaluating a Horn program of arity `a` on `n`
  elements is `n^{O(a)}`, i.e., polynomial *on the expansion*);
  `D A := ¬ HORNEVAL A A` is iso-invariant and in EXPTIME by
  `EXPTIME = coEXPTIME`; if `D ∈ PTIME` it is SO-Horn definable by some `π₀`,
  and `A := ⟨π₀⟩` contradicts. Steps 1 and 3 need **compiling the logic** – a
  Gödel numbering of the syntax as finite structures, a definable satisfaction
  predicate written as an SO-Horn program over the expansion with its
  correctness theorem, and surjectivity of the encoding. Two notes for whoever
  picks it up: that evaluator would *also* discharge the machine bridge's
  simulator and the AC⁰ item of §3, so its cost is shared across three items;
  and the same diagonal separates PSPACE from EXPSPACE verbatim (SO(TC) for
  SO-Horn, `PSPACE = coPSPACE`), so one construction yields two separations.
  Bibliography when built: `hartmanis1965computational` (Hartmanis, Stearns,
  1965), for the classical time hierarchy this is the descriptive form of.

## 5. Inexpressibility toolkit (unconditional results)

The unique payoff of the descriptive approach: *unconditional* separations and
non-reducibility, impossible in the machine world.

- **Further applications of the games** [M]: REACH/connectivity is not
  FO-definable, and non-existence of FO reductions in specific cases. The
  games are also the natural route to separating `≤ᶠᵒ` from `≤ᶠᵒ[≤]` below.
- **Locality (Hanf, Gaifman)** [L]: the workhorse for graph inexpressibility;
  gives connectivity/acyclicity results without bespoke games.
- **0-1 laws (Glebskii et al., Fagin)** [L]: FO 0-1 law on random structures;
  Mathlib's probability is ample. Fun, self-contained, good student project.
- **Order-necessity results** [R]: candidate research question the framework
  makes precise: show some catalog reduction (e.g., SAT → 3COL) provably has no
  order-free FO counterpart, separating `≤ᶠᵒ` from `≤ᶠᵒ[≤]` on concrete
  problems.
- **PARITY not in AC⁰** ([Ajtai 1983][ajtai1983sigma11];
  [Furst, Saxe & Sipser 1984][furst1984parity];
  [Håstad 1986][hastad1986almost]) [XL]: everything around it is in place –
  PARITY is in the catalog and in LOGSPACE (`parity_mem_LOGSPACE`), AC⁰ is a
  logic and sits inside PTIME – so this single theorem is what
  `AC⁰ ⊊ LOGSPACE` waits on. The route is **not** the switching lemma but the
  polynomial method, as [Vollmer 1999][vollmer1999introduction] §3.3 presents
  it: depth reduction to probabilistic `MOD_p`-∧ circuits (Thm 3.20, 3.23),
  their representation by low-degree polynomials over `GF(p)` (Thm 3.25), a
  count of low-degree multilinear monomials (Lemma 3.27) and Smolensky's
  theorem (3.31), whence `MOD_p ∉ AC⁰` (Cor 3.32) and PARITY with it. That is
  algebra Mathlib has – `MvPolynomial` over `ZMod p`, the dimension of the
  bounded-degree multilinear polynomials, a counting argument – where the
  switching lemma is bespoke combinatorics. The circuit model it is stated
  against is the non-uniform one of §4, plus the easy compile direction there;
  together the two items are one project. The same theorem gives
  `MOD_q ∉ AC⁰[p]` for coprime `p, q`, hence the strict chain
  `AC⁰ ⊊ AC⁰[p] ⊊ TC⁰` (Cor 4.35), which is the separation the FO(COUNT) item
  of §3 would want, mirroring `exists_ac0Definable_not_foDefinable` one level
  up. Do not confuse PARITY with EVEN, the parity of the *universe*, which
  **is** AC⁰ (`even_ac0Definable`) and is what separates `FO(≤)` from AC⁰.
- **`FO(≤, +) ⊊ FO(≤, +, ×)`** [L]: classically true, and *not* out of reach in
  the way PARITY is – primality of the universe is definable in the latter and
  not in the former, by Ginsburg and Spanier's semilinearity of `FO(+)` spectra
  ([Schweikardt 2005][schweikardt2005arithmetic] §3.2, which also collects the
  sources for `FO(<) ⊊ FO(+)`). That is a quantifier-elimination argument rather
  than a switching lemma, but Presburger quantifier elimination is not in the
  library either; re-price only against a concrete plan for it.
- Not a defect, an open question worth flagging as one: **expect no complete
  problem for AC⁰**. The library's reductions are `FO(≤)`, strictly *weaker*
  than AC⁰ reductions – that strictness is
  `exists_ac0Definable_not_foDefinable` – so an AC⁰-complete problem under
  `≤ᶠᵒ[≤]` would need a reduction that builds the arithmetic, which the
  separation suggests `FO(≤)` cannot do. Suggests, not proves.

## 6. Machine bridges beyond NP and PTIME

Design analysis for the one direction the machine bridge does not reach – the
string-encoding layer – and pricing rules for any machine problem added later.
The bridges already in the library are documented in the `Problems/Machine.lean`
and `Problems/MachineAlt.lean` docstrings, and the exponential ones in
`Problems/Wide.lean`; that is where their shape should be read off before
building another.

**Standing scope limit.** Textbook `NP = NTIME(nᵏ)` over string encodings
needs the converse compilation – that an FO interpretation or a `Σ₁` kernel is
*evaluated* by a polynomial-time machine: a verified compiler with a step
count, plus string encodings of structures [R]. Nothing in the bridge claims
it; the residual gap – two classical facts taken by inspection: that FO
reductions are AC⁰-computable, and that a definability witness is evaluated
within its class's bound – is documented in the README. Instances carry their
own transition table, so reduction-built machines have polynomially many
states – standard for an acceptance problem; the constant-alphabet simulation
is never needed.

**And it is an interface obligation, not a soundness debt** – which is what
sets its priority. The classes here are defined logically and the bridges
characterize them from inside the framework, so the string presentations are
never the referent (the classes-are-logic principle, below), and the structural
presentation is not the weaker of the two: Fagin needs no order, the order tax
bites only at P and below where the library already works over ordered
structures, isomorphism-invariance holds by construction, and the one place a
structural presentation could state something false – the *size measure* – is
discharged in both directions by `Encoding.lean`. What the string layer would
buy is legibility to a reader arriving with the textbook definition, plus the
inherited robustness of a model whose invariance results have been accumulating
for decades – worth having, worth not confusing with a hole in the foundations.

A further application of the same machinery, once step-counted machines can
run over string encodings: bounding the *encoders and decoders* of the
concrete-instance layer. The `Encoding`/`Decoding` bundles enforce that
`relBool` and `dec` are computations, but not that they are cheap (a decoder
may brute-force the answer; see the “what this does not buy” notes in
`DescriptiveComplexity/Encoding.lean` and `DescriptiveComplexity/Decoding.lean`).
With the bridge, “computed by a polynomial-time machine” becomes a statable
side condition on both, closing the last gap in reading completeness theorems
as statements about concrete data. [R], and only worthwhile after the
compilation direction above exists.

Four rules price a bridge, and with it any machine problem added later:

1. **Membership is cheap when the logic is a reachability/fixpoint logic, dear
   when it quantifies.** For DTC/TC/LFP/SO(TC) the machine problem is the
   *syntactic image* of the logic and membership is unfolding plus an encoding
   bijection; for ∃SO/`Σₖ` the run must be guessed and checked (Fagin's
   tableau). Budget a sentence-builder layer on top of the transition formula:
   an `SOTCSpec`-style interface wants *sentences*, not formulas with
   parameters, and that gap is what a naive estimate misses.
2. **Hardness is cheap when the class has a one-loop complete problem** (REACH
   “guess a neighbor”, HORN-SAT “propagate”, SAT “guess then sweep”).
   Otherwise the discharge must compile arbitrary formulas of the logic into a
   machine – the **evaluator** (static quantifier nesting → nested loops), in
   three variants of increasing cost: *state-registers* (loop counters as
   elements in the state), *tape-registers with logarithmic addresses* (honest
   fixed-control logspace), *tape-registers with exponential addresses*
   (EXPTIME/EXPSPACE). The way out, and the rule to apply before pricing an
   evaluator: **pick the source problem so that the algorithm is fixed** – one
   compiled algorithm, as the SAT machine compiles one clause check – **and
   prove the deterministic side hard**, letting hardness travel forward along a
   nearly-free reduction to the nondeterministic problem rather than
   simulating.
3. **A machine reused at a new polarity is not a machine reused.** Adding
   universal rounds to a nondeterministic machine costs an order of magnitude
   more than the guess sweeps suggest, because a universal round needs the
   converse of every existence statement: that whatever the machine does during
   a round is the intended run of *some* assignment (the read-off), that it
   always has a move, that it terminates, and that its checking phase proves
   the matrix rather than merely being able to.
4. **Budget regimes.** Unary (NP, P, PH) needs the walk lemma
   (`accepts_iff_exists_walk`); no budget (L, NL, PSPACE, EXPSPACE) needs only
   `Relation.ReflTransGen`, strictly cheaper – and buys the converse half free,
   since a deterministic machine's reachable configurations are linearly ordered
   (`Problems/Machine/DetRun.lean`), so one run ending stuck and non-accepting
   settles a no-instance with no second induction; exponential (EXPTIME) needs a
   walk along the lexicographic order of subsets, whose successor is
   FO-definable by ripple-carry (`Numbers/Binary.lean`,
   `Problems/Knapsack/Chain.lean` supply most of it).

The concrete items:

- **Capture vs. completeness, the choice forced by the evaluator.** A capture
  theorem is available at NP (fixed control, input heads, poly work tape) but
  is not worth taking: logic → machine there needs the evaluator *with* tape
  addressing (lockstep address computation to test a guessed relation) –
  exactly the cost routing hardness through SAT/HORN-SAT avoids. So: capture
  where the evaluator is cheap and the model first-order (as at L/NL, where a
  `k`-head automaton walking the order mirrors FO(DTC) vs. FO(TC) and rules out
  registers, JAGs and branching programs as models), completeness where it is
  dear (P/NP/`Σₖᵖ`/PSPACE and above). The rule to carry into any new bridge:
  never compile the logic; pick a target whose programs already exist – a fixed
  algorithm named by the source problem, or a code model like
  `Nat.Partrec.Code` where Mathlib's `exists_code` hands over the program.
- **Limits that survive every variant**: the string-encoding layer (above);
  oracle and `Δₖᵖ` classes – the bridge would make them definable, but by a machine,
  against the library's classes-are-logic principle (a decision, not a
  drift).

## 7. Teaching material

- **Reduction cookbook** [M]: grow the `Examples/` directory into a curated,
  tutorial-style example set (cf. Grange et al., MFCS 2024) as the catalog
  broadens, so the library doubles as a complexity-course companion.

## 8. Populating the GI degree, and reduction theories without a class

The degree machinery itself is built (`DescriptiveComplexity.Degree`:
`ComplexityClass.below`, completeness for a degree as mutual reducibility, and
the check that the logically defined classes *are* the degrees of their
complete problems), and so is the doubling lemma every entry of the degree goes
through (`DescriptiveComplexity.isoReflecting_fo_reduction`, below). What is
left is populating the degree, and the two reduction theories not organized
around a class: CSP templates, and the W-hierarchy, which is a degree as well.

- **Hardness for isomorphism problems must be order-free** – a design-triage
  rule, beside the choice of number encoding
  (`DescriptiveComplexity/Numbers.lean`). The classical arc is a gadget `F` on
  single graphs with `G ≅ H ↔ F G ≅ F H`, and the forward half is *free* here
  because an interpretation is functorial, i.e., commutes with isomorphisms
  (`relMap_equiv₁/₂`). An *ordered* reduction destroys that: order-invariance
  makes the yes/no answer order-independent, not the constructed structure
  independent up to isomorphism, so every gadget would owe a structure-level
  argument. Order-free is available because `twoGraphs` carries its own “this
  element is real” marks, and running `F` relativized to each side's mark
  inside one order-free interpretation, leaving junk unmarked, is what
  `DescriptiveComplexity.FOInterpretation.double` does
  (`DescriptiveComplexity/GadgetDouble.lean`). Side benefit – both sides are
  built by the same gadget out of the same universe, so they come out
  size-balanced and the padding step most textbook GI reductions need
  disappears. What an entry then owes is its gadget and
  `DescriptiveComplexity.IsoReflecting` of it – isomorphic values come from
  isomorphic arguments, a statement about *single* structures with no
  pattern/host distinction in it – which
  `DescriptiveComplexity.isoReflecting_fo_reduction` turns into the reduction.
  That is what keeps every entry below short.
- **The GI degree, in order of cost** [M each]: hypergraph / set-system
  isomorphism first, since `Problems/SetFamily/FromGraphs.lean` already builds
  set systems from graphs and the incidence construction is order-free; then
  colored-graph isomorphism (colored → plain is the content – the *directed*
  case needs no entry, `twoGraphs` carrying two arbitrary binary relations);
  then bipartite-graph isomorphism, the first entry with a real rigidity
  argument (incidence graph, dimension 2, tags `{V, E}`, and the isomorphism
  must be prevented from swapping the two sides); finite-automaton isomorphism
  as a re-reading of `Machines.lean`. Excluded: line graphs (Whitney's theorem,
  with its K₃/K₁,₃ exception) and Latin-square isotopy / Steiner-system
  isomorphism (Miller's reductions are arithmetic-heavy and would fail the
  bitwise-definability check the binary representation imposes). Companions that
  populate the degree without completing it: Graph Automorphism and Group
  Isomorphism (multiplication tables, one ternary relation), both below GI with
  the converse open – though `GA ≤ᶠᵒ GI` is not free, the classical reduction
  being genuinely clever.
  **Caution for the docstrings**: classical GI-completeness is stated under
  polynomial-time reductions, so no result here may be cited, only re-proved;
  under `≤ᶠᵒ` the degree is finer, which makes each statement *stronger* than
  the literature's, and some classically GI-complete problems will not survive.
- **CSP templates and pp-interpretations** [M for the reduction theory, R for
  the dichotomy]: a reduction theory not organized around a class, and a
  better fit for the framework than GI. For a fixed finite template `B`,
  `CSP(B)` is a decision problem in this library's sense, and the field's
  reduction notion – primitive-positive interpretations – *is* a first-order
  interpretation restricted to the existential-conjunctive fragment, so
  `FOInterpretation` is already the right object and `IsQuantifierFree` shows
  how a fragment gets tracked (§3, reduction-notion refinements). “`B'`
  pp-interprets `B` implies
  `CSP(B) ≤ᶠᵒ CSP(B')`” is directly formalizable. What makes it worth doing is
  **Schaefer's dichotomy**, a finite case analysis over Boolean templates whose
  tractable cases are already in the catalog – 2SAT, HORN-SAT and dual-Horn,
  1-in-3-SAT, NAE-SAT – with affine the only one missing. Also the item in this
  document closest to conjunctive-query evaluation and containment
  (`Examples/ConjunctiveQueries.lean`).
- **The W-hierarchy as degrees** [M for the framework, L for the generic Σ₁
  reduction, S per entry]: parameterized complexity is the third reduction
  theory that belongs here, and the one whose problems the library already
  has. A parameterized problem is a decision problem with an iso-invariant
  parameter, and the natural choice is the cardinality of a designated unary
  mark – which is how Clique, Independent Set, Dominating Set and Vertex Cover
  already carry their threshold, so the same Lean objects are the
  parameterized problems, and an existing reduction that transports the mark
  unchanged (Clique to Independent Set by `complEdgeInterp`) is already an
  fpt-reduction with identity parameter bound. Two things are new.
  * *Slicewise reductions.* An fpt-reduction is machine-defined, but every
    textbook W[1] reduction is an interpretation chosen knowing the parameter,
    with tags and dimension allowed to grow with it: a family of
    interpretations indexed by the parameter value, each correct on its
    slice, with the image parameter bounded by a function of the source's.
    Composition is `comp` slice by slice. Producing a mark of a prescribed
    size needs an order, so slices are ordered reductions.
  * *The class as a degree.* Defining W[1] by a logic and proving closure
    fails as it does for MaxSNP (§9): a Σ₁ sentence pulled back through an
    interpretation with quantified formulas is not Σ₁. Take instead the
    Downey–Fellows–Regan (1998) characterization as the definition – W[1] is
    the class of problems slicewise-reducible to Σ₁ model checking,
    equivalently the degree below Clique – and membership closure is
    composition, hardness is cofinality, both free as for the GI degree
    (`ComplexityClass.below`, over slicewise reductions). This also sidesteps
    the weft-1 normalization theorem of Downey–Fellows, the heavy step of the
    classical completeness of Clique.
  The one theorem of substance is the analog of the ∃SO → SAT discharge:
  every slicewise Σ₁-definable problem reduces to Clique. Per slice the kernel
  is a quantifier-free formula read as data, with one tag per variable and per
  literal, dimension the maximal arity of the vocabulary, and consistency
  edges between tags sharing a variable; the case split on the kernel is the
  one `EqPattern.lean` makes. No Tseitin nodes and no padding, so medium-large
  and well under Cook–Levin. It gives memberships in definability style:
  Clique at slice `k` is “`k` distinct pairwise adjacent elements”. The
  catalog after it is cheap: Multicolored Clique, Partial Vertex Cover, the
  bounded-parameter subgraph problems. W[2] is a separate decision: defining
  it by Σ₂,₁ model checking costs the same, but Dominating Set's completeness
  is the long reduction of Downey–Fellows–Regan [L].
  **Out of reach, to be written as such**: fixed-parameter tractability
  itself – the polynomial's degree must not depend on the parameter, which no
  family of formulas indexed by it controls, so “Vertex Cover is in FPT” needs
  a machine bridge or a bounded-variable fragment, and a literature check –
  and uniformity: without a computable family of interpretations the classes
  are the nonuniform variants. Mathlib's encodable formulas and the
  `Nat.Partrec.Code` machinery of the RE layer could express computability,
  at the price of concrete tag types and encodable symbols throughout; start
  without it and document the gap as the README does for the by-inspection
  claims. Check the exact statements of Flum–Grohe, *Describing parameterized
  complexity classes* (2003), and of Downey–Fellows–Regan before fixing the
  definitions; neither paper has a bibliography entry yet.
- **The negative half is §5.** A degree structure is only worth building if
  non-reducibility is provable, and Ehrenfeucht–Fraïssé games are exactly that.
  The two together give an *unconditional* degree structure at the FO level,
  where every machine-world degree statement is conjectural – a better framing
  for §5 than “inexpressibility results” standing alone.

## 9. Beyond decision problems: optimization and approximation

The syntactic theory of Papadimitriou–Yannakakis (1991) – MaxSNP, MaxNP,
L-reductions, MAX-3SAT complete – and the Kolaitis–Thakur hierarchy above it
(MaxΣ₀ ⊊ MaxΣ₁ ⊊ MaxΠ₁ ⊊ MaxΠ₂) fit the library's idiom, and reuse the block,
pullback and counting machinery. What they cannot deliver is the usual reading
of “approximation hardness”: “no PTAS unless P = NP” rests on the PCP theorem,
and APX as the closure of MaxSNP under PTAS-reductions
(Khanna–Motwani–Sudan–Vazirani 1998) is a machine statement; neither is in
reach, and nothing below may be presented as either. None of these papers has
a bibliography entry yet; fetch them from DBLP before the first file is
written.

What exists already: a solution is an assignment to an `SOBlock`, with its
isomorphism transport `SOBlock.mapAssign`; the objective of a MaxSNP problem
is the number of tuples satisfying a quantifier-free kernel, which the `ncard`
kit of `Numbers/Unary.lean` counts and transports; quantifier-freeness is
Mathlib's `IsQF`, already tracked for interpretations
(`FOInterpretation.IsQuantifierFree`). Max Cut is the test of fit: `MaxCutOn`
*is* “some `S` has at least `k` pairs in `CutRel`”, the MaxSNP form with a
threshold glued on, and most unary-threshold entries of the catalog are the
threshold version of a MaxSNP or MaxNP problem.

The first consumers need not be MaxSNP problems. A minimization problem such
as Set Cover, whose approximability is logarithmic rather than constant, or
the crawling problem of `Examples/GraphCrawling.lean` with a budget counting
only the non-target pages, already exercises everything below except the
syntactic classes. So the framework – problems, reductions, composition and
the transfer theorem – is written first and stands without any class; MaxSNP
and the Kolaitis–Thakur levels are a layer on top of it.

- **Optimization problems** [L, with the next item]: a block, a cost, a goal
  (max or min), and two iso-invariant predicates that must not be merged:
  * *feasibility* of a solution, a predicate on a structure and an assignment.
    MaxSNP problems have none – every assignment is a solution – but every
    minimization problem does: a cover must cover, a crawl must reach every
    target;
  * *validity* of an instance, the promise: at least “some feasible solution
    exists” for a minimization problem (a set system with an uncovered element
    has no cover), plus whatever the problem promises on top (a degree bound,
    see below).
  Neither is required to be first-order. Feasibility of a crawl is a
  reachability condition, and so is the existence of a feasible crawl; a
  problem is semantic and iso-invariant, and definability is something proved
  about it, as for `DecisionProblem`. Where a semantic condition has a
  certificate, the certificate enters the block as further relation variables
  (the order of `crawlOn_iff_certificate`), and the cost counts only the
  variable that matters. The cost is the number of tuples satisfying a kernel
  over the expanded structure: |S \ targets| is a quantifier-free kernel, and
  weighted costs stay out under the unary convention. The optimum exists on
  valid instances because assignments over a finite structure form a finite
  type, and polynomial boundedness is automatic when the cost counts tuples.
  The optimum *value* is an iso-invariant number, i.e., a `CountingProblem`,
  so the counting layer's reductions apply to values as they stand. A generic
  theorem – the threshold version of an optimization problem with an
  NP-checkable feasibility is in NP, by the injection certificate
  `nonempty_embedding_iff_ncard_le` – recovers the existing membership proofs.
  The tests of fit are the threshold versions, each shown equal to the
  existing decision problem by `DecisionProblem.ext`: Max Cut for a
  maximization problem without feasibility (`MaxCutOn` *is* “some `S` has at
  least `k` pairs in `CutRel`”), minimum Set Cover and minimum total-budget
  crawling (`SetCover`, `GraphCrawling`) for minimization problems with
  feasibility and validity.
- **L-reductions with an additive constant**: an interpretation (plain or
  ordered) plus a *solution reader*, formulas defining the source's relation
  variables from the target's solution. That solution lives on tagged tuples,
  and `SOBlock.pull` / `pullAssign` / `mergeAssign` (`SecondOrderPull.lean`)
  are exactly the bijection between such solutions and tuples of relations
  over the base, so the reader is a formula over `L.sum (B.pull Tag d).lang`.
  The reduction sends valid instances to valid ones, the reader sends feasible
  solutions to feasible ones, and on valid instances two inequalities hold,
  with constants `α β c : ℕ`:
  * `OPT_B ≤ α · OPT_A + c` – *affine*, not linear;
  * `err_A (read y) ≤ β · err_B y`, the error being cost minus optimum for a
    minimization problem and optimum minus cost for a maximization one, stated
    in ℕ, where truncated subtraction is exact because the optimum bounds
    every cost.
  On instances with `OPT_A ≥ 1` this is an L-reduction with constant `α + c`,
  so hardness under L-reductions is unchanged: the constant refines the
  numbers, not the class. It matters for the transfer theorem below. Set
  Cover reduces to non-target-budget crawling with `α = β = c = 1` (the root
  is the `+ 1`), which gives a ratio `ρ + (ρ − 1) / OPT_A` for Set Cover from
  a ratio `ρ` for crawling; folding `c` into `α = 2` gives `2ρ − 1` and loses
  the factor in front of `ln n` that a logarithmic hardness result needs.
  Avoiding `c` altogether would mean padding each set page into a path,
  dimension at least 2 and a definable successor, for the same theorem. The
  record is ordered from the start, the first consumer needing a canonical
  singleton as `crawlInterp` does: the reader may use the order, and the
  inequalities hold under every linear order. Junk points of the interpreted
  universe may occur in a target solution; the reader ignores them and the
  cost counts them, which the inequalities absorb. Transitivity composes
  readers through `FOInterpretation.extendSO`; the `α`s and `β`s multiply,
  and the constant becomes `α' · c + c'`. Asking for a first-order reader is
  stronger than the literature's polynomial-time one, in the way `≤ᶠᵒ` is
  stronger than Karp, and every textbook L-reduction has one. No separate
  record for AP-, PTAS- or strict reductions: every reduction in view proves
  these two inequalities, and the ratio-transfer form is a lemma about them.
  Add a second record when a reduction appears that cannot be stated this
  way.
- **The transfer theorem** [M–L]: for a minimization problem, a feasible `y`
  within ratio `ρ` of `OPT_B` reads back to a source solution of cost at most
  `OPT_A + β (ρ − 1) (α · OPT_A + c)` – stated additively, with the ratio
  `1 + β (ρ − 1) (α + c / OPT_A)` as a corollary under `OPT_A ≥ 1` (at
  `OPT_A = 0` a ratio means nothing, and such instances occur); the
  maximization case is the classical one. Ratios that grow with the instance,
  as for Set Cover, are functions of an iso-invariant *measure*, a
  `CountingProblem`, not of the universe size, and the theorem takes as a
  hypothesis how the target's measure relates to the source's. On the
  crawling reduction the number of target pages is `|U|` exactly, whereas
  the total number of pages, `|U| + m + 1`, would change the constant in
  front of `ln |U|`; stating ratios against the universe would build that
  mistake into the theorem.
- **Definable approximation** [L, the one approximation statement
  available]: for every linear order, a fixed FO(≤, LFP) formula defines a
  feasible solution within the ratio. This is polynomial-time approximation
  read through Immerman–Vardi for queries, so a hardness result the library
  cannot prove – a PCP-based one, say – can enter as a *hypothesis*, and the
  transfer theorem turns it into a conditional inapproximability statement
  for the target, machine-free, with the unformalized part named as such.
  Two things are new and are the cost. The formula defines a *relation*, not
  a sentence, and its value may depend on the order (an approximation
  algorithm sees an encoding), whereas `LFPDefinable` is sentence-level and
  order-invariant. And it must be pulled back through an interpretation and
  composed with the reader: PTIME's closure under `≤ᶠᵒ` does this for
  sentences, and the parameters-as-constants device of
  `TransitiveClosureDecideReach.lean` is the known route from sentences to
  relations. The machine reading would need a relation-level version of the
  bridge `mem_PTIME_iff_le_dtmAccept`; until then, the README states it as
  Immerman–Vardi's, not as a theorem here.
- **The class** [S once the two first items exist]: a sibling of
  `ComplexityClass`, not an instance of it – its fields are over
  `DecisionProblem`, and its membership closure is a requirement the theory
  does not make: a kernel pulled back through an interpretation with
  quantified formulas is not quantifier-free, the phenomenon §3's
  quantifier-free tracking is about. MaxSNP is a quantifier-free kernel with
  no feasibility, MaxNP an existential one, and the Kolaitis–Thakur levels add
  the universal and Π₂ kernels: all “kernel as data”, like a `HornProgram`.
  Membership is syntactic, hardness is cofinal under L-reductions, and only
  hardness needs a closure proof.
- **Memberships** [S each]: Max Cut (its kernel is `CutRel`), MAX-2SAT and
  MAX-k-SAT on tuple vocabularies (see the vocabulary decision below).
- **MAX-3SAT is MaxSNP-complete** [XL, the one large item]: the generic
  reduction from an arbitrary quantifier-free kernel, with three costs. The
  tuples whose kernel is unsatisfiable must be filtered first-order, which
  works because satisfiability at a tuple depends only on the pattern of base
  atoms there, of which there are finitely many (`EqPattern.lean` is the
  precedent). The optimum is at least a constant fraction of the live tuples –
  the first inequality needs it – by a double count over all assignments, a
  few hundred lines. Each live tuple becomes a Tseitin encoding of its kernel
  with one unit clause on the output node, so an optimal assignment loses
  exactly one clause per unsatisfied tuple (`Problems/Sat/Tseitin.lean` is
  the starting point). A fixed kernel arity means no padding, so this is
  probably order-free, and cheaper than the Cook–Levin discharge.
- **The L-reduction catalog** [M–L each]: MAX-2SAT, bounded-degree Independent
  Set and Vertex Cover, Max Cut; outside MaxSNP, minimum Set Cover to
  non-target-budget crawling, the first consumer of the additive constant and
  of the measure-based transfer theorem. Two quantitative bounds and a reader
  replace the one equivalence of a decision reduction; the charging map of
  `Problems/MaxCut/Reduction.lean` is about half of one such proof.
- **MaxSNP ⊊ MaxNP, and the strictness of the hierarchy** [R]:
  inexpressibility results; they belong with §5.

Two design decisions to take before the first file:

- **MAX-3SAT needs a clause-as-tuple vocabulary.** On `Language.sat`, where
  clauses are elements with occurrence relations, “some occurrence is
  satisfied” is an existential kernel, so Max SAT lands in MaxNP and not in
  MaxSNP. The classical statement uses ternary relations indexed by sign
  pattern; a new vocabulary with a reduction to the existing 3SAT is needed,
  and counting each clause once per tuple rules out working around this with
  an order.
- **Promise instances need a domain, and it is not feasibility.**
  Bounded-degree Independent Set is MaxSNP-complete on bounded-degree
  instances only, and an L-reduction's first inequality fails where junk
  instances have optimum zero. Hence the validity predicate above, with
  reductions required to send valid instances to valid ones. Decision
  problems fold promises into yes-instances (3SAT's width bound); that trick
  does not transfer. Keep it apart from feasibility: validity is about the
  instance and is the reductions' business, feasibility is about a solution
  and is the reader's.

## Suggested ordering (value vs. prerequisite chains)

Nothing here is a prerequisite of anything else here, so the order is a
weighting, not a chain: headline theorems not yet formalized anywhere, maximal
reuse of machinery that already exists, low risk of an item turning out to be
blocked, and a preference for results that make an existing design decision
provable rather than merely reasonable.

**Next, in this order:**

1. **Locality (Hanf, Gaifman)** (§5) [L]: with the two games in place, the
   next substantial piece of the inexpressibility track, and the one that
   gives connectivity and acyclicity without bespoke strategies. The 0-1 laws
   are its independent neighbor.
2. **Populating the GI degree** (§8) [M each]: with the degree machinery and
   the doubling lemma in place, an entry costs its gadget and an
   `IsoReflecting` proof and nothing besides, which makes this the cheapest
   result per line on the list. Hypergraph / set-system isomorphism first, its
   incidence construction being order-free and half-written in
   `Problems/SetFamily/FromGraphs.lean`. Taken after step 1 on purpose: a
   degree structure is worth building where non-reducibility is provable.

**Alongside, or after:**

- **The optimization track of §9**, framework first and classes after:
  problems with feasibility and validity, L-reductions with an additive
  constant, and the measure-based transfer theorem, tested on Max Cut and on
  minimum Set Cover to non-target-budget crawling before any syntactic class
  is defined. MaxSNP then reuses the block, pullback and counting machinery
  almost unchanged, Max Cut being already in its shape, and the two design
  decisions it needs (a tuple vocabulary for MAX-3SAT, a validity predicate
  kept apart from feasibility) are cheaper taken before the first file than
  after. Definable approximation is the costly part of the framework – a
  relation-level, order-dependent FO(LFP) notion and its pullback – and can
  follow the reductions. MAX-3SAT's completeness is the one large item and
  can wait; the strictness of the hierarchy is research.
- **The W-hierarchy of §8**, right after the GI degree: the same degree
  machinery, problems the catalog already has, one medium-large generic
  reduction (slicewise Σ₁ to Clique) and then an entry per gadget. It needs
  the honest framing its item spells out: nonuniform, and no FPT membership.
- **The rest of the sharpening pass** (each [M], no prerequisites, no new
  surface): **quantifier-free / projection / dimension tracking through
  composition** (§3's reduction-notion refinements), which upgrades catalog
  statements to the DC-faithful “complete under qfps”, and **Spectra** (§4).
  The lesson 3-DNF-TAUT taught about the first of these: a discharge that needs
  an *image* invariant the `≤ᶠᵒ` interface hides does not force a general
  invariant-tracking layer, because building the reduction from the complement
  side keeps the promise in hand where it is proved. Reach for tracking when a
  second consumer appears, not before.

**Deferred, and deliberately so:**

- Catalog growth (§1), as opportunistic filler. Check
  FO-expressibility of the 3DM → 3-Partition arithmetic *before* committing: it
  is the one item with a real chance of being unbuildable.
- FO(LFP) ⊆ NP directly: correctly parked, it buys no new statement.
  Relativized membership closure has two consumers (§3), so it moves up as
  soon as either is wanted.
- Of the BIT / AC⁰ / PARITY chain, only the far end: **PARITY ∉ AC⁰** (§5),
  [R]. Everything short of it is built – the logic, the machine model and
  their equality – and nothing above depends on it; the by-inspection claims
  in the README stay an honest, documented gap, being about string encodings
  (§6), which no bridge inside this framework closes. What is worth doing
  next in that area is, on demand, class-hood (§3, not [R]).
- The succinct problems of §2 and EPR's hardness. Both are drawings out of the
  wide machine, each about the size of the tilings that are built, and neither
  inhabits a class that is empty: the three exponential classes have complete
  problems already. `PTIME ≠ EXPTIME` (§4) is deferred harder still, being
  research-level and sharing its evaluator with two other items.

This weighting assumes the goal is research output and formalization firsts. If
the near-term goal is the course companion of §7, the cookbook and catalog
growth move up and the inexpressibility track slides down: students meet NL,
P-completeness and reductions long before they meet an Ehrenfeucht–Fraïssé
game.
