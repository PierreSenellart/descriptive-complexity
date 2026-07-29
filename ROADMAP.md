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
- **PSPACE, downstream of QSAT** [L, gadget-heavy]: the game problems
  (Generalized Geography…). The machine bridge is done: a deterministic
  QBF-evaluation machine written inside a QSAT instance makes `DTMAcceptSpace`
  PSPACE-hard, and `DTMAcceptSpace ≤ᶠᵒ NTMAcceptSpace` carries it to the
  nondeterministic problem, so both are complete – this framework's
  `PSPACE = NPSPACE`, with no machine-side Savitch.
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

- **The quantitative framework layer** [M]: the real framework work, and it
  depends on nothing beyond what exists today. A `CountingProblem` is an
  iso-invariant `Count : Structure → ℕ`; the reductions reuse
  `FOInterpretation`, `Tag`, `dim` and the finite/nonempty side conditions of
  `FOReduction` verbatim, only the `correct` field changing. The names
  `Counting.lean` / `Counting/` are free for this layer (the
  Immerman–Szelepcsényi module having become `InductiveCounting`), with the
  ΣQSO syntax and evaluator in `Quantitative.lean` / `QSO/`: the same split
  between framework and defining logic that `Complexity.lean` and the
  `SecondOrder*` / `FixedPoint*` files already make on the decision side.
- **The reduction ladder** [M for levels 0–1, L for level 2]: three notions,
  each a special case of the next, so a hardness result proved low transports
  up.
  - *Parsimonious* (`≤ᵖ`): `P.Count A = Q.Count (I A)`, the iff of
    `FOReduction.correct` replaced by an equation. Composition is
    `FOInterpretation.comp` plus `compLEquiv`, with `iso_invariant` where the
    decision proof rewrites with it.
  - *Counting, one oracle call* (`≤ᶜ`):
    `(P.Count A : ℤ) = scale A * Q.Count (I A) + shift A`. Typing the equation
    in ℤ is not a convenience: the monotone sources need subtraction (the
    independent sets of a bipartite graph are exactly the worlds where no edge
    is fully selected, `#IS = 2^{n+m} − #PP2DNF`), which is the
    ΣQSO-with-ℤ-constants/GapP phenomenon of the table above. Composing
    `c·Q∘I + d` with `c'·R∘J + d'` gives
    `(c · c'∘I)·R∘(J∘I) + (c · d'∘I + d)`, so the coefficients must be closed
    under sum, product and *pullback along an interpretation* – the last being
    the same `comp`/`compLEquiv` argument again, plus iso-invariance.
  - *Non-adaptive linear combinations* [L]:
    `divisor A * P.Count A = ∑ p ∈ paramSet A, coeff A p * Q.Count (I p A)`,
    i.e. polynomially many oracle calls at definable parameters, combined
    definably. It needs *parameterized* interpretations (thread `k` extra free
    variables through every defining formula and through `Map`), which is the
    level's main cost; the divisor on the left keeps Lagrange denominators out
    of the statement. Index sets multiply, parameters concatenate and divisors
    multiply, so composition still closes. This is the shape of every
    interpolation-based `#P`-hardness proof. *Adaptive* Turing reductions,
    where a later query depends on an earlier answer, stay out: that is the
    honest boundary of a machine-free framework, and `FP^#P` lives beyond it.
- **The coefficient budget** [S, but load-bearing]: coefficients must come from
  a class *strictly weaker* than the one being defined, exactly as the
  classical definition asks its post-processing to be polynomial-time.
  Otherwise the notion is vacuous: with arbitrary `#P` coefficients, take `Q`
  constantly `1` and `scale := P`, and every counting problem reduces to a
  trivial one. The principled budget is `QFO(LFP) = FP`, deferred below; the
  cheap interim one is the grammar
  `b ::= k ∈ ℤ | |{x̄ : φ}| | 2^{|{x̄ : φ}|} | b + b | b · b` with `φ ∈ FO(≤)`,
  which contains `n^k` and `2^n`, is closed under pullback for free (FO
  formulas pull back along interpretations, which is `relMap_map`), and sits
  comfortably inside FP.
- **`CountingClass`** [S]: `Mem`, `Hard` and `Complete` as in
  `Complexity.lean`, with one structural difference: closure is *asymmetric*.
  `Mem` is closed under `≤ᵖ` only, since `#P` is not closed under the
  subtractive correction (that is what GapP is for); `Hard` is closed under
  `≤ᶜ`, which needs only transitivity of the reduction, supplied by the
  composition above.
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

### Probabilistic query evaluation, and what "`#P`-hard" should mean

The intended consumer of this track is probability computation, where the
field's own "`#P`-hard" is an abuse: computing a probability is a map into ℚ,
so the honest classical statement is `FP^#P`-completeness under Turing
reductions, which the ladder above deliberately does not reach. The abuse is an
artifact of the *output type*, and it disappears by counting worlds instead:
for a fixed query `Q` and a TID instance whose probabilistic tuples `T` all
carry probability 1/2,

```
#PQE(Q) : Structure → ℕ,   #PQE(Q)(D) = P(Q on D) · 2^{|T|}
```

is an iso-invariant counting problem, and the normalization `2^{|T|}` is a
property of the instance, not of the answer, so it is definable and the two
formulations differ by a fixed factor rather than by an oracle protocol. Only
uniform 1/2 is covered; non-uniform dyadic probabilities are a *weighted* model
count, whose weight is a product over tuples, hence a `Π` that ΣQSO lacks by
design (the same reason FP is not reachable by counting) – bit-blasting
`a_t / 2^k` into `k` independent 1/2-tuples brings them back into the
unweighted setting at a `k`-fold blow-up, if ever needed.

- **Membership** [S]: `ΣX̄. φ_Q(X̄)` is #FO, and for a UCQ it lands at the very
  bottom, `#Σ₁` / `ΣQSO(Σ₁)`. Worth noting that the FPRAS story of that level –
  approximable, not closed under sum – *is* the probabilistic-database
  approximability story (Karp–Luby on the lineage DNF), so "structure inside
  `#P`" above is not an unrelated research item but this application's own
  fine print.
- **Tier 1, an FO query with negation** [S]: put the assignment in a
  probabilistic unary relation, the clauses in deterministic ones, and let `Q`
  say "this assignment satisfies the formula"; worlds satisfying `Q` are the
  satisfying assignments, on the nose. The reduction from #SAT is a dimension-1
  interpretation re-reading a SAT instance as a PQE instance, parsimonious
  because the correspondence is a bijection. Nearly free once #SAT is complete
  for ΣQSO(FO), and enough to state "probabilistic query evaluation is
  `#P`-complete" with no abuse at all. It says nothing about the queries the
  field cares about.
- **Tier 2, a UCQ** [L, gated on a literature check]: for
  `h₀ = ∃x∃y. R(x) ∧ S(x,y) ∧ T(y)` with `R`, `T` probabilistic, `#PQE(h₀)`
  *is* `#PP2DNF` up to renaming, by a bijection between worlds and assignments.
  So the difficulty is not in the database layer: proving it hard *is* proving
  Provan–Ball, which would have to be formalized. Tier 1's trick cannot help,
  because the query is monotone: fix one edge and let the other `|T| − 2`
  tuples vary, and the count is either 0 or `≥ 2^{|T|}/4`, so a parsimonious
  reduction from a formula with three models would force `|T| ≤ 3`, i.e. a
  logarithmic-size output instance, i.e. a reduction that counted by itself.
  This holds for every monotone query, which is why the field's own statements
  here are Turing-flavored. **Check before committing**: whether the classical
  proof is one oracle call plus arithmetic (level 1) or genuinely interpolates
  (level 2). If neither, the hardness would have to be imported as a hypothesis
  and only the bijection formalized.
- **The dichotomy itself** [R]: safe queries in PTIME needs the FP side
  (`QFO(LFP)`) and is a meta-theorem quantifying over queries rather than a
  completeness result about one problem. Much larger than the hardness half,
  and out of scope here.

Beyond the library, the counting track is the direct bridge to provenance-lean:
the counting provenance semantics of a query is exactly a model count, so the
two libraries would meet here, with semiring provenance as the common
generalization (and QSO's weighted-logic ancestry is the same idea from the
other side). PQE above is the concrete meeting point: `#PQE(Q)` is the model
count of the query's lineage.

## 7. Machine bridges beyond NP and PTIME

The machine bridge is done for NP, PTIME and PSPACE (`ntmAccept_NP_complete`,
`dtmAccept_PTIME_complete`, `dtmAcceptSpace_PSPACE_complete`,
`ntmAcceptSpace_PSPACE_complete`, and the characterizations
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
| PSPACE | SO(TC) | S [done] | L–XL [done, ~4.1k] | ~3–5.5k |
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
   exponential addresses* (EXPTIME/EXPSPACE). **Both consequences drawn here
   for PSPACE were wrong**, as the build showed. Routing through QSAT is what
   worked, and needs no evaluator at all: reducing *from* QSAT means compiling
   one fixed algorithm — iterative QBF evaluation, whose stack is one bit per
   variable in the variable's own cell — exactly as the SAT machine compiles
   one fixed clause check. And Savitch is avoided not by stating the problem
   nondeterministically but by proving hardness for the *deterministic*
   problem and transferring: hardness travels forward along reductions, and
   `DTMAcceptSpace ≤ᶠᵒ NTMAcceptSpace` is nearly free (the identity
   interpretation, with the accepting predicate guarded by the first-order
   determinism sentence). The lesson generalizes: pick the source problem so
   that the algorithm is fixed, and prove the deterministic side hard.
3. **Budget regimes.** Unary (NP, P, PH) needs the walk lemma
   (`accepts_iff_exists_walk`); no budget (L, NL, PSPACE, EXPSPACE) needs only
   `Relation.ReflTransGen`, strictly cheaper — and buys the converse half free,
   since a deterministic machine's reachable configurations are linearly
   ordered (`Problems/Machine/DetRun.lean`), so one run ending stuck and
   non-accepting settles a no-instance with no second induction; exponential (EXPTIME) needs a
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
  completeness at P/NP/`Σₖᵖ`/PSPACE and above (evaluator dear) — and at PSPACE
  the completeness route turned out to need no evaluator at all, only the one
  algorithm QSAT names. At RE the same escape exists in a stronger form: the
  target model can be chosen so that the program is *obtained* rather than
  written – `Nat.Partrec.Code`, where Mathlib's `exists_code` supplies it – so
  the addressed evaluator is avoided there too – and that is how §8 was
  closed, `orderedReduction_codehalt`. The rule the two cases share: never
  compile the logic; pick a target whose programs already exist.
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
`NP ⊆ RE`),
`Relationalize.lean` (every `∃SO[new]`-definable problem reduces to one over a
relational vocabulary, which is how source vocabularies with function symbols
are handled), Trakhtenbrot's theorem `FINSAT_RE_complete`, and `halt_mem_RE`, whence `halt_le_finsat` – Trakhtenbrot's
theorem in the form it is usually stated, the reduction from the halting
problem. The bridge to Mathlib's computability layer is built too
(`DescriptiveComplexity/Computability/`, `Problems/CodeHalt/`): RE-hard
problems are undecidable, and `finsat_not_computable` is Trakhtenbrot's theorem
as everyone states it.

**The converse half is built too, at the code model**
(`Problems/CodeHalt/Hardness/`, `Computability/CodeHaltComplete.lean`):
`orderedReduction_codehalt` reduces *any* problem whose concrete instances are
semi-decidable to `CODEHALT`, whence `codehalt_RE_complete`,
`mem_RE_iff_rePred` (`RE = REPred`, the class *is* recursive enumerability) and
`RE_ne_coRE`. What made it small, and is worth not rediscovering:

- the reduction *names* a program instead of building one: the drawn code is
  `comp cP (pair numeral nest)` with `cP` supplied by
  `Nat.Partrec.Code.exists_code`. This is what the machine model cannot offer
  (Mathlib's universal machine is not finite-state), and it is why the
  evaluator with addressed storage priced at XL in §7 is not needed here;
- every branch is evaluated at input `0`, so a constant is a tree of `pair`,
  `succ` and `zero` nodes and a bit is *one* node;
- the table is nested **by coordinate**, not numbered in a mixed radix: each
  level is then a plain walk of the input order (`succF`, `maxF`, canonical
  padding), so no arithmetic on positions has to be proved, and the decoder
  (`structOf`) follows the coordinates down the nests. The rank-of-a-tuple
  lemma a lexicographic layout would need is the whole cost the nesting avoids;
- the two leaves `succ` and `zero` are **shared** elements, so a bit of the
  input is read as an *edge* of the drawing rather than as a mark: every tag
  then has exactly one constructor (`ProgTag.mark`), and exclusivity of the
  marks – half of `CodeWF` – is immediate;
- the fixed code `cP` is drawn with one tag per node (`SubPos`, by recursion on
  the code), and `decodesTo_subPos` is one structural induction. Tags are free
  at any instance size, which is what makes this compatible with hardness being
  cofinal;
- a plain ordered reduction suffices, not a relativized one: junk tuples are
  unmarked, so they draw nothing and carry no root.

What remains:

- **PCP hardness, and with it the undecidability of Post's problem**
  [L; XL if attempted directly]: `CODEHALT ≤ᶠᵒ[≤] PCP` by the classical
  computation-history dominoes, after which hardness travels forward along the
  reduction – `CODEHALT` being RE-hard, this is now the *only* thing missing.
  These are the *same* dominoes that give **undecidability** of PCP – reachable
  independently of everything else, since first-order reductions are computable
  and `CODEHALT` is undecidable – so one construction serves both readings.

  Why the direct route is XL, and why it should not be taken: PCP is not the
  syntactic image of any logic – a certificate of `∃SO[new]` is a structure
  with relations, a certificate of PCP is a string with two parses – and a
  PCP instance is really a *program*: reading a solution left to right and
  keeping the unmatched overhang makes it a nondeterministic queue machine
  whose transitions the reduction writes. Discharging `∃SO[new]` into it
  directly means guessing a block assignment on unbounded storage and then
  evaluating a first-order kernel against it, every atom test being a random
  access into the guessed table – the “evaluator with tape addressing” priced
  at XL in §7. The code model is where that cost is avoided, which is the
  item above.

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
  checker – an objection that is about *building* one, and hence does not
  bite at `CODEHALT`, where the model checker is `finsat_rePred`, a theorem
  already proved, and the reduction only has to name it.
- **`RE.Hard HALT`** [last, and no longer the load-bearing item]: with
  `CODEHALT` RE-hard, the statement “RE is the class of semi-decidable
  problems” is *already* had, in the code model and in the sharper form
  `RE = REPred` (`mem_RE_iff_rePred`); what remains here is the same fact at
  the machine model, which is a statement about `Language.turing`, not about
  RE. Two routes, neither
  needing the evaluator with addressed storage: `CODEHALT ≤ᶠᵒ[≤] HALT`, a
  machine interpreting the code drawn in the instance, or `PCP ≤ᶠᵒ[≤] HALT`, a
  machine that guesses dominoes and keeps the overhang on the unbounded tape,
  its data read by the transition formulas – the regime of the SAT machine
  (`Machine/Hardness.lean`, ~2.7k with its tape and interpretation files)
  rather than of an evaluator. So [L–XL] and unblocked, but last: it buys the
  machine-model wording of a theorem the code model already states, whereas the
  easy half, `halt_mem_RE`, already buys `halt_le_finsat` and buys the same for
  every future problem shown to be in RE.
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

## 10. Completeness without a class: FO degrees and `ComplexityClass.below`

Every completeness result above measures a problem against a class *defined by
a logic*. The same machinery supports a second, orthogonal notion at almost no
cost, and it is not currently exploited: completeness for the degree of a fixed
*problem*, with no logic anywhere. "GI-complete" is the literature's standard
example. Nothing in `Complexity.lean` is specific to logically defined classes,
so the notion is expressible today.

- **`ComplexityClass.below`** [S, ~150 lines, no prerequisites]: the downward
  closure of a fixed relational problem, as a `ComplexityClass`.

  ```lean
  def ComplexityClass.below {L₀ : Language.{0,0}} [L₀.IsRelational]
      (Q₀ : DecisionProblem L₀) : ComplexityClass where
    Mem P := Nonempty (P ≤ᶠᵒ[≤] Q₀)
    Hard P := CofinalHard (fun Q => Nonempty (Q ≤ᶠᵒ[≤] Q₀)) P
    …
  ```

  The `Hard` side is *entirely free*: `CofinalHard` (`Hierarchy.lean`) is
  already parameterized by an arbitrary `Mem` predicate, and
  `CofinalHard.of_foReduction`, `.of_orderedReduction`,
  `.of_relOrderedReduction`, `.congr` are proved generically for it – the class
  literals of `Hierarchy.lean` and `LogSpace.lean` differ only in which
  predicate they pass. The `Mem` side is `FOReduction.toOrdered`,
  `OrderedFOReduction.trans` and `OrderedFOReduction.congrSource`; that
  `correct` quantifies over finite nonempty structures only is what makes
  `mem_congr_finite` go through. `(below Q₀).Complete P` is then literally
  "`P` is `Q₀`-complete", and mutual reducibility `≡ᶠᵒ` names the degree it
  lives in.
- **`C = below Q₀` when `Q₀` is complete for `C`** [S per instance; blocked in
  general]: the sanity check that the construction is the right one, and a
  theorem rather than a tautology. `ComplexityClass.ext` plus monotonicity of
  `CofinalHard` in its `Mem` argument reduce it to
  `C.Mem P ↔ Nonempty (P ≤ᶠᵒ[≤] Q₀)`, whose forward half is the class's own
  discharge and whose backward half is `mem_of_orderedReduction` applied to
  `Q₀ ∈ C`. So `NP = below SAT`, `PTIME = below HORNSAT`, `NL = below TwoSAT`
  and `coNP = below TAUT` are a few lines each, since
  `sat_hard_of_sigmaSODefinable`, `hornSat_hard_of_sigmaSOHornDefinable`,
  `twoSat_hard_of_sigmaSOKromDefinable` and `taut_hard_of_piSODefinable` all
  deliver a *non-relativized* ordered reduction. Payoff: "SAT-hardness is
  NP-hardness" stops being folklore and becomes a lemma. The *generic*
  statement, over an arbitrary class and its complete problem, is blocked, and
  instructively so: `cofinalHard_iff` yields only `≤ʳᶠᵒ[≤]`, so it needs the
  `mem_of_relOrderedReduction` closure that §3 parks as unmotivated – this is
  the first thing that would motivate it. RE is exactly the case that needs it
  (`finsat_hard_of_sigmaSONewDefinable` is relativized).
- **Graph Isomorphism, the point of the exercise** [S]: the vocabulary already
  exists, `Language.twoGraphs` from `Problems/SubgraphIso.lean` (marks
  `patV`/`hostV`, relations `patE`/`hostE`); GI is "the two marked subgraphs
  are isomorphic", with junk outside both marks ignorable as usual. Membership
  is a textbook `Σ₁` – guess a binary relation, check bijection-on-marks and
  both edge directions (`realize_rel₂`) – with no order, no counting and no
  threshold, hence cheaper than most of the NP catalog. It is the library's
  first NP problem conjecturally neither in P nor NP-complete, and the problem
  of deciding the very equivalence the framework quotients by, which is worth a
  sentence in its docstring.
- **Hardness for isomorphism problems must be order-free** – a triage rule to
  record beside those of §0. The classical arc is a gadget `F` on single graphs
  with `G ≅ H ↔ F G ≅ F H`, and the forward half is *free* here because an
  interpretation is functorial, i.e. commutes with isomorphisms
  (`relMap_equiv₁/₂`). An *ordered* reduction destroys that: order-invariance
  makes the yes/no answer order-independent, not the constructed structure
  independent up to isomorphism, so every gadget would owe a structure-level
  argument. Order-free is available because `twoGraphs` carries its own "this
  element is real" marks: run `F` relativized to `patV` and to `hostV` in
  parallel inside one order-free interpretation, leaving junk unmarked. Side
  benefit – both sides are built by the same gadget out of the same universe,
  so they come out size-balanced and the padding step most textbook GI
  reductions need disappears. The one reusable lemma, which is what makes each
  catalog entry short afterwards [M]:

  ```lean
  theorem gi_hard_of_isoReflecting (F : FOInterpretation Language.graph L' Tag d)
      (h : ∀ G H, … → Nonempty (F.Map G ≃[L'] F.Map H) → Nonempty (G ≃[Language.graph] H)) :
      GraphIso ≤ᶠᵒ GraphIso'
  ```
- **The GI degree, in order of cost** [M each]: hypergraph / set-system
  isomorphism first, since `Problems/SetFamily/FromGraphs.lean` already builds
  set systems from graphs and the incidence construction is order-free; then
  digraph and colored-graph isomorphism (colored → plain is the content); then
  bipartite-graph isomorphism, the first entry with a real rigidity argument
  (incidence graph, dimension 2, tags `{V, E}`, and the isomorphism must be
  prevented from swapping the two sides); finite-automaton isomorphism as a
  re-reading of `Machines.lean`. Excluded: line graphs (Whitney's theorem, with
  its K₃/K₁,₃ exception) and Latin-square isotopy / Steiner-system isomorphism
  (Miller's reductions are arithmetic-heavy and would fail the §0
  bitwise-definability check). Companions that populate the degree without
  completing it: Graph Automorphism and Group Isomorphism (multiplication
  tables, one ternary relation), both below GI with the converse open – though
  `GA ≤ᶠᵒ GI` is not free, the classical reduction being genuinely clever.
  **Caution for the docstrings**: classical GI-completeness is stated under
  polynomial-time reductions, so no result here may be cited, only re-proved;
  under `≤ᶠᵒ` the degree is finer, which makes each statement *stronger* than
  the literature's, and some classically GI-complete problems will not survive.
- **CSP templates and pp-interpretations** [M for the reduction theory, R for
  the dichotomy]: the other reduction theory not organized around a class, and
  the better fit of the two. For a fixed finite template `B`, `CSP(B)` is a
  decision problem in this library's sense, and the field's reduction notion –
  primitive-positive interpretations – *is* a first-order interpretation
  restricted to the existential-conjunctive fragment, so `FOInterpretation` is
  already the right object and `IsQuantifierFree` shows how a fragment gets
  tracked (§3, reduction-notion refinements). "`B'` pp-interprets `B` implies
  `CSP(B) ≤ᶠᵒ CSP(B')`" is directly formalizable. What makes it worth doing is
  **Schaefer's dichotomy**, a finite case analysis over Boolean templates whose
  tractable cases are already in the catalog – 2SAT, HORN-SAT and dual-Horn,
  1-in-3-SAT, NAE-SAT – with affine the only one missing. Also the item in this
  document closest to conjunctive-query evaluation and containment
  (`Examples/ConjunctiveQueries.lean`).
- **The negative half is §5.** A degree structure is only worth building if
  non-reducibility is provable, and Ehrenfeucht–Fraïssé games are exactly that.
  The two together give an *unconditional* degree structure at the FO level,
  where every machine-world degree statement is conjectural – a better framing
  for §5 than "inexpressibility results" standing alone.

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
2. **PCP hardness** [L] (§8), now that the RE bridge is closed at the code
   model: `CODEHALT ≤ᶠᵒ[≤] PCP` by the computation-history dominoes, which are
   the same dominoes the undecidability of Post's problem wants, so one
   construction serves both readings. The item that used to head this line –
   the instance-as-a-program reduction `P ≤ᶠᵒ[≤] CODEHALT` – is done, and with
   it `CODEHALT` RE-complete, `RE = REPred` and `RE ≠ coRE`; what it taught is
   recorded in §8 and generalizes: when an evaluator is the stated blocker,
   look for a target whose programs already exist rather than pay for the
   evaluator.
3. **The fixpoint logics, as textbook faithfulness**: FO(PFP) (§3) and
   Immerman–Vardi (§4), both [L]. Neither unblocks anything else and neither
   buys a class the library lacks – SO(TC) already captures PSPACE – so what
   they add is DC's own vocabulary for classes held here under other names,
   which is the first thing a reader arriving from the textbook looks for.
   The two share the fixpoint infrastructure, and Immerman–Vardi's hardness
   discharge is step 1's CVP from HORN-SAT, so take that one first.

**Running alongside, from the start:**

- **The counting track of §6**, as far as #SAT plus the free catalog entries.
  Promoted above PSPACE deliberately: PSPACE repeats a shape the library
  already executes (define a fragment, discharge to its syntactic image),
  whereas counting descriptive complexity has no formalization anywhere and
  ΣQSO's two-layer syntax fits the kernel-as-data idiom unusually well. It
  depends on nothing unbuilt, so it cannot be blocked by the chain above; a
  cheap headline (#SAT complete for ΣQSO(FO)) sits one `exists_gates`
  strengthening in; and it is the meeting point with provenance-lean. Internal
  order: framework layer and ladder levels 0–1 → evaluator →
  `#P := ΣQSO(FO)` → #SAT → the free entries and PQE tier 1; stop there
  (level 2 of the ladder, PQE tier 2, structure inside #P, the quantitative
  fixed point and MaxSNP are genuine research, or gated on a literature check).
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
growth move up and the fixpoint logics slide down: students meet NL,
P-completeness and reductions long before they meet FO(PFP).
