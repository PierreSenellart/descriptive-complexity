# Roadmap

Catalog of work **not yet done**, and of nothing else: an item is deleted when
it is built, never annotated as finished, the record of what the library
contains being `git log` together with the module docstrings. Organized by
theme; each item carries a
rough scale of effort ([S] short, [M] medium, [L] long, [R] research-level,
i.e., the Lean proof would itself be a contribution) and its prerequisites.
Main source: Immerman, "Descriptive Complexity" (DC below); also Garey–Johnson
and Karp's 21 problems for the catalog.

## 1. NP-complete problems (catalog growth)

Beyond Karp's 21:

- **X3C** [M–L]: exact cover by 3-sets, from 3-Dimensional Matching (now hard)
  or from Exact Cover; local gadgets, probably ordered.
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
into the problem's vocabulary, i.e. a variation on
`sat_hard_of_sigmaSODefinable` with a shape invariant carried through. The
pattern is instantiated for every fragment the library defines: ∃SO → SAT,
SO-alternation-level-`k` → QBF_k, SO-Horn → HORN-SAT, SO-Krom → 2SAT (the last
two sharing their scaffolding in `ClauseDischarge.lean`), SO(TC) →
SUCCINCT-REACH and ∃SO[new] → FINSAT, so no discharge is outstanding; what
remains below are ordinary catalog reductions and machine bridges.

- **Monotone CVP** [M]: the unit-propagation circuit is monotone as drawn, so
  this is a matter of restricting the vocabulary rather than of a new gadget.
- **Hardness of `ATMAcceptSpace` for EXPTIME** [XL, own project]: membership is
  proved (`atmAcceptSpace_mem_EXPTIME`), so EXPTIME has a natural *member*; what
  is missing is `EXPTIME ⊆ APSPACE`, the Chandra–Kozen–Stockmeyer simulation. It
  cannot be routed through the outer composition of §3 — `Q ≤ᶠᵒ[≤] DTMAccept`
  over `X.E` gives the blocked composite again — so it is a from-scratch
  simulation, but a well-shaped one: a point of the expansion is a block
  assignment, i.e. exactly one tape's worth, so the machine holds `O(1)` points
  and needs no addressing arithmetic; the operations it needs are
  `Exponential/Increment.lean`'s primitives at the *tape* level, which is what
  `Problems/Machine/QsatTape.lean` and `QsatRun.lean` already do for QBF
  assignments; and the control is the syntax tree of a **fixed** FO(LFP)
  definition, hence finite control and not an interpreter.
- **PSPACE, downstream of QSAT** [L, gadget-heavy]: the game problems
  (Generalized Geography…), the only PSPACE entries still missing.
- **The exponential classes, complete problems** [XL]: EXPTIME, NEXPTIME and
  EXPSPACE exist as logics and have their complement equalities and inclusions
  (`DescriptiveComplexity/Exponential.lean`), but **no complete problem**. The
  generic succinctness theorem that would supply them at one stroke – the
  succinct version of a `C`-complete problem is `C.exp`-complete – needs the
  outer composition of §3, whose three-piece fix is described there; the
  quantifier-free-completeness audit inside it is where the risk sits. A
  complete problem not routed through succinctness is the alternative:
  alternating space-bounded acceptance is in EXPTIME by definition, its
  hardness wanting `succinct GAME`, hence the outer composition above.
- Δₖᵖ and oracle classes are blocked on machine models, presumably forever out
  of scope (§7 refines both judgments).

## 3. Logics and framework extensions

- **FO(LFP) ⊆ NP, directly** [M]: by guessing the fixed point and the derivation
  order and checking both first-order against the certificate interface
  (`derives_eq_of_closed_of_wf`). No new mathematics — the inclusion already
  follows by composing the FO(LFP) → SO-Horn translation with the Horn discharge
  — but the direct `Σ₁` definition would be textbook-faithful; the work is
  formula building, made tedious by the varying arities of a block's atoms.
- **Housekeeping in the shared machinery** [S]:
  `Problems/FinSat/Nodes.lean` imports `Sat/Tseitin.lean` for `NodeAt`, so if that
  cross-problem dependency ever grates, the node machinery is generic and
  belongs at top level. Beside it: `blockSym` / `repAssign` /
  `altAssign_qbfBlocks` in `Problems/Qbf/Membership.lean` are the monadic
  special case of `SecondOrderReplicate.lean` and should be folded into it –
  noticed while building the PH bridge, left alone because it touches a working
  file and bought that bridge nothing.
- **Composing an expansion with an interpretation, the outer way** [XL, design
  work first]: `DescriptiveComplexity.ExpExpansion.pullOrdered` composes an
  interpretation *before* an expansion (`A ↦ X.Map (I.Map A)`) and is what makes
  `ComplexityClass.exp` a class. The **other** order — an interpretation applied
  to an expanded structure, `A ↦ J.MapRel (X.Map A)` — is what a complete
  problem for an exponential class would need, and it is *not* an expansion:
  an expansion's defining sentences are first-order over the base with the block
  copies as parameters, while a quantifier of `J` ranges over the *points* of
  `X.Map A`, i.e. over block assignments, which is a second-order quantifier
  over the base. So the composite's relations are `Σₖ` over the base, not FO,
  and neither the plain composition nor a Tseitin description of the composite
  exists.
  **Quantifiers are the only obstruction**: an atom `R(x̄)` of `J` translates to
  `X.relSentence`, `x = y` to equality of tagged assignments, and `x ≤ y` to a
  definable order on the expanded universe, all first-order over the base;
  Boolean combinations compose. So the fix is quantifier-freeness, and it is the
  library's version of the side condition the succinctness literature has always
  attached ([Veith 1998][veith1998succinct] states the upgrade theorem for
  *projection* reductions) — though quantifier-freeness alone suffices here,
  projections being a strictly stronger property this framework does not need.
  The order on the expanded universe, the translation lemma and the gate
  `PSPACE = NL.exp` are **built**, so what remains is
  **quantifier-free composition and quantifier-free hardness** [XL]: restrict
  the outer composition to `IsQuantifierFree` interpretations, where it does
  exist, and add a `HardQF` predicate *beside* `Hard` rather than a field of
  `ComplexityClass` (a field would touch `Complexity.lean` and force a full
  rebuild). The risk is not the definitions but re-proving one complete
  problem per class under quantifier-free reductions — HORN-SAT first.
- **`LOGSPACE.exp = PSPACE`** [M–L]: `LOGSPACE.exp ⊆ PSPACE` is monotonicity,
  but the converse is not the `Exponential/Reach.lean` argument, which asks
  REACH of the graph a walk draws and so lands in NL. It wants that graph read
  *deterministically* — Savitch, or the determinization of the QSAT walk, one
  exponential up.
- **What is left of the BIT layer** [L]: the arithmetic vocabulary and the class
  it defines are **built** (`Arithmetic.lean`, `ArithmeticDefinable.lean`,
  `ArithmeticFixedPoint.lean`, `Problems/Parity.lean`: `AC0Definable`,
  `FO(≤) ⊊ AC⁰`, `AC⁰ ⊆ PTIME`, PARITY in LOGSPACE and not in FO(≤)). `+` and
  `×` are primitive rather than BIT, and deliberately so: the closure obligation
  below is schoolbook base-`n` arithmetic for them and base conversion for BIT.
  Three items remain, in this order.
  * **`AC⁰ ⊆ LOGSPACE`** [L]: the sharp bound, which the fixed-point route
    cannot give (a `TCSpec` is one operator over first-order kernels, with no
    relation variables). It wants `plusP`/`timesP` as head-program fragments and
    a *substitution lemma*: FO over head-computable relations is
    head-computable, i.e. `HeadEval.evalP` generalized to a formula language
    larger than the machine's. That lemma is worth more than the bound: it also
    gives `FO(COUNT) ⊆ LOGSPACE` once a counting fragment exists.
  * **AC⁰ as a `ComplexityClass`** [XL]: closure under `≤ᶠᵒ` needs the numeric
    predicates of an interpreted universe – lex-ordered tagged tuples, hence
    base-`n` digits – defined from those of the base. Addition is
    carry-lookahead; multiplication needs a double-width digit product, which
    needs a half-width (base-`√n`) splitting. Note what it does *not* gate: a
    problem reducing to an AC⁰ problem is already known to be in PTIME.
  * **BIT itself** [M–L]: as a *derived* predicate (Immerman's mutual
    definability), not a primitive, so that the closure obligation above does
    not grow a base-conversion. On the fixed-point side it is cheap – two more
    induction variables, `pow2 (succ j) p' ← pow2 j p ∧ plus p p p'` and then
    `bit` – which buys `BIT` for membership proofs without touching the class.
- **Quantifier-free projections** [L]: the finest reduction notion (DC uses them
  for almost all completeness results); SAT complete under first-order
  projections.
- **Reduction-notion refinements** [M]: track quantifier-free / projection /
  dimension-1 status through composition (currently only `IsQuantifierFree`
  exists); "problem X is complete under qfps" is the DC-faithful statement.
- **FO(COUNT) / counting quantifiers** [L]: with BIT, captures uniform TC⁰;
  relevant to the arithmetic boundary of the binary representation
  (multiplication is TC⁰, not FO). Its inclusion in LOGSPACE would come free
  from the substitution lemma of the `AC⁰ ⊆ LOGSPACE` item above, given a
  counting head fragment.
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
  with two consumers: it would turn `le_dtmAcceptSpace_of_mem_PSPACE` into the
  missing `iff` (`Problems/Machine/SpaceHard.lean` records why PSPACE's machine
  characterization stops short of `mem_NP_iff_le_ntmAccept`'s shape), and the
  *generic* `C = below Q₀` is blocked on it – the per-class instances are
  proved in `ClassDegrees.lean`, each from its own non-relativized hardness
  discharge, but the statement over an arbitrary class and an arbitrary
  complete problem of it needs the closure, since `cofinalHard_iff` yields only
  `≤ʳᶠᵒ[≤]`:
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

Three pieces built for Abiteboul–Vianu are the ones to reach for in any capture
attempted here: the order-relativization transfer
(`FixedPointOrderTransfer.lean`, for every statement that moves an order
between instance and vocabulary), stratification of inflationary inductions
(`FixedPointStratify.lean`, for any "define X by induction, then induct over
X"), and the two formula compilers along a definable quotient
(`Invariant/Simulation.lean`, `Invariant/Backward.lean` – the missing dual of
`Relativized.lean`).

- **The circuit bridge for AC⁰** [R]: the class is built as the logic
  (`AC0Definable`, §3), so what is missing is the *bridge*: first-order logic
  with a linear order and the numeric predicates is exactly (DLOGTIME-)uniform
  AC⁰ ([Immerman 1999][immerman1999descriptive]; [Barrington, Immerman &
  Straubing 1990][barrington1990uniformity]). It is the one bridge here whose
  far side is a *circuit* model: uniform families (bounded depth, polynomial
  size, unbounded fan-in) plus a uniformity condition, introduced as data as
  the NP and PTIME machine bridges introduce Turing machines – so it is [R] for
  the machinery, not out of reach in kind. Two payoffs justify the cost. The
  `FO ⊆ AC⁰` half turns the library's currently *by-inspection* claim that FO
  reductions are AC⁰-computable – the structures-vs-strings bridge of §7 and of
  the README's *Scope* – into a theorem; and it is the prerequisite for the
  PARITY ∉ AC⁰ lower bound of §5. Note that it closes only the *reduction* half
  of that bridge: the membership half, that a definability witness is evaluated
  within its class's bound, needs the same FO evaluator at a coarser resource
  accounting, so neither half is worth building alone. The converse
  `AC⁰ ⊆ FO(≤, BIT)`, simulating a uniform circuit family by a sentence, is the
  harder half. Independent of the three remaining §3 items; cf. the
  circuit-family-bridge remark in §7.
- **Spectra** [M]: Fagin's connection between generalized spectra and NP; mostly
  definitional given the SO layer, historically resonant.

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
  makes precise: show some catalog reduction (e.g. SAT → 3COL) provably has no
  order-free FO counterpart, separating `≤ᶠᵒ` from `≤ᶠᵒ[≤]` on concrete
  problems.
- Horizon: **PARITY not in AC⁰** ([Ajtai 1983][ajtai1983sigma11];
  [Furst, Saxe & Sipser 1984][furst1984parity];
  [Håstad 1986][hastad1986almost]) [R]: a switching-lemma formalization is a
  major standalone project. Everything around it is now in place – PARITY is in
  the catalog and in LOGSPACE (`parity_mem_LOGSPACE`), AC⁰ is a logic and sits
  inside PTIME – so this single theorem is what `AC⁰ ⊊ LOGSPACE` waits on. Do
  not confuse it with EVEN, the parity of the *universe*, which **is** AC⁰
  (`even_ac0Definable`) and is what separates `FO(≤)` from AC⁰.

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
  evaluator, so the choice of number representation constrains only the numbers
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

Design analysis for extending the machine bridge past the classes it reaches
today – to EXPTIME and EXPSPACE, and to the string-encoding layer – with the
class-defining logic assumed to exist (§3 work). The bridges already in the
library are documented in the `Problems/Machine.lean` and
`Problems/MachineAlt.lean` docstrings, which is where their shape should be
read off before building another.

**Standing scope limit.** Textbook `NP = NTIME(nᵏ)` over string encodings
needs the converse compilation — that an FO interpretation or a `Σ₁` kernel is
*evaluated* by a polynomial-time machine: a verified compiler with a step
count, plus string encodings of structures [R]. Nothing in the bridge claims
it; the residual gap – two classical facts taken by inspection: that FO
reductions are AC⁰-computable, and that a definability witness is evaluated
within its class's bound – is documented in the README. Instances carry their
own transition table, so reduction-built machines have polynomially many
states — standard for an acceptance problem; the constant-alphabet simulation
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
may brute-force the answer; see the "what this does not buy" notes in
`DescriptiveComplexity/Encoding.lean` and `DescriptiveComplexity/Decoding.lean`).
With the bridge, "computed by a polynomial-time machine" becomes a statable
side condition on both, closing the last gap in reading completeness theorems
as statements about concrete data. [R], and only worthwhile after the
compilation direction above exists.

**Cost of a bridge, given the logic:**

| class | logic | membership | hardness | total |
|---|---|---|---|---|
| EXPTIME | SO(LFP) | L | XL | ~4–7k |
| EXPSPACE | SO(PFP) | M | XL (shared) | ~3–6k |

Four rules price such a bridge:

1. **Membership is cheap when the logic is a reachability/fixpoint logic, dear
   when it quantifies.** For DTC/TC/LFP/SO(TC) the machine problem is the
   *syntactic image* of the logic and membership is unfolding plus an encoding
   bijection; for ∃SO/`Σₖ` the run must be guessed and checked (Fagin's
   tableau). Budget a sentence-builder layer on top of the transition formula:
   an `SOTCSpec`-style interface wants *sentences*, not formulas with
   parameters, and that gap is what a naive estimate misses.
2. **Hardness is cheap when the class has a one-loop complete problem** (REACH
   "guess a neighbour", HORN-SAT "propagate", SAT "guess then sweep").
   Otherwise the discharge must compile arbitrary formulas of the logic into a
   machine — the **evaluator** (static quantifier nesting → nested loops), in
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
   the matrix rather than merely being able to. Budget the same asymmetry for
   EXPTIME and EXPSPACE.
4. **Budget regimes.** Unary (NP, P, PH) needs the walk lemma
   (`accepts_iff_exists_walk`); no budget (L, NL, PSPACE, EXPSPACE) needs only
   `Relation.ReflTransGen`, strictly cheaper — and buys the converse half free,
   since a deterministic machine's reachable configurations are linearly
   ordered (`Problems/Machine/DetRun.lean`), so one run ending stuck and
   non-accepting settles a no-instance with no second induction; exponential (EXPTIME) needs a
   walk along the lexicographic order of subsets, whose successor is
   FO-definable by ripple-carry (`Numbers/Binary.lean`,
   `Problems/Knapsack/Chain.lean` supply most of it).

The concrete items:

- **Capture vs. completeness, the choice forced by the evaluator.** A capture
  theorem is available at NP (fixed control, input heads, poly work tape) but
  is not worth taking: logic → machine there needs the evaluator *with* tape
  addressing (lockstep address computation to test a guessed relation) —
  exactly the cost routing hardness through SAT/HORN-SAT avoids. So: capture
  where the evaluator is cheap and the model first-order (as at L/NL, where a
  `k`-head automaton walking the order mirrors FO(DTC) vs. FO(TC) and rules out
  registers, JAGs and branching programs as models), completeness where it is
  dear (P/NP/`Σₖᵖ`/PSPACE and above). The rule to carry into any new bridge:
  never compile the logic; pick a target whose programs already exist – a fixed
  algorithm named by the source problem, or a code model like
  `Nat.Partrec.Code` where Mathlib's `exists_code` hands over the program.
- **The exponential classes are not blocked by the framework**: the machine
  description stays polynomial (a reduction can write it) and only the run is
  exponential, living in Lean just as `SigmaSODefinable` quantifies over
  exponential-size assignment types; tape cells indexed by subsets of the
  positions, budget `2 ^ |pos|`, a legitimate iso-invariant problem. The
  expensive pair: the exponential-order walk (feasible) and the
  exponential-address evaluator (the real cost).
- **Limits that survive every variant**: the string-encoding layer (above);
  oracle and `Δₖᵖ` classes — the bridge would make them definable, but by a machine,
  against the library's classes-are-logic principle (a decision, not a
  drift); `#P` as "number of accepting runs" is easy to state but needs the
  parsimonious-reduction notion the framework still lacks (§6, first item);
  the classes-are-logic principle points at `ΣQSO(FO)` for the definition
  either way, with the machine count as a bridge statement.

## 8. Teaching material

- **Reduction cookbook** [M]: grow the `Examples/` directory into a curated,
  tutorial-style example set (cf. Grange et al., MFCS 2024) as the catalog
  broadens, so the library doubles as a complexity-course companion.

## 9. Populating the GI degree, and reduction theories without a class

The degree machinery itself is built (`DescriptiveComplexity.Degree`:
`ComplexityClass.below`, completeness for a degree as mutual reducibility, and
the check that the logically defined classes *are* the degrees of their
complete problems), and Graph Isomorphism sits in it. What is left is
populating that degree, and the second reduction theory not organized around a
class.

- **Hardness for isomorphism problems must be order-free** – a design-triage
  rule, beside the choice of number encoding
  (`DescriptiveComplexity/Numbers.lean`). The classical arc is a gadget `F` on
  single graphs with `G ≅ H ↔ F G ≅ F H`, and the forward half is *free* here
  because an interpretation is functorial, i.e. commutes with isomorphisms
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
      DigraphIso ≤ᶠᵒ DigraphIso'
  ```
- **The GI degree, in order of cost** [M each]: hypergraph / set-system
  isomorphism first, since `Problems/SetFamily/FromGraphs.lean` already builds
  set systems from graphs and the incidence construction is order-free; then
  colored-graph isomorphism (colored → plain is the content – the *directed*
  case needs no entry, `twoGraphs` carrying two arbitrary binary relations);
  then
  bipartite-graph isomorphism, the first entry with a real rigidity argument
  (incidence graph, dimension 2, tags `{V, E}`, and the isomorphism must be
  prevented from swapping the two sides); finite-automaton isomorphism as a
  re-reading of `Machines.lean`. Excluded: line graphs (Whitney's theorem, with
  its K₃/K₁,₃ exception) and Latin-square isotopy / Steiner-system isomorphism
  (Miller's reductions are arithmetic-heavy and would fail the bitwise-
  definability check the binary representation imposes). Companions that populate the degree without
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

Nothing here is a prerequisite of anything else here, so the order is a
weighting, not a chain: headline theorems not yet formalized anywhere, maximal
reuse of machinery that already exists, low risk of an item turning out to be
blocked, and a preference for results that make an existing design decision
provable rather than merely reasonable.

**Next, in this order:**

1. **Locality (Hanf, Gaifman)** (§5) [L]: with the two games in place, the
   next substantial piece of the inexpressibility track, and the one that
   gives connectivity and acyclicity without bespoke strategies. The 0-1 laws
   are its independent neighbour.
2. **Populating the GI degree** (§9) [M each]: with `below` and Graph
   Isomorphism in place, the degree has one inhabitant and no companions.
   Hypergraph / set-system isomorphism first, and `gi_hard_of_isoReflecting`
   with it, since it is what makes every later entry short. Taken after step 1
   on purpose: a degree structure is worth building where non-reducibility is
   provable.

**Alongside, or after:**

- **The counting track of §6**, as far as #SAT plus the free catalog entries:
  counting descriptive complexity has no formalization anywhere, and ΣQSO's
  two-layer syntax fits the kernel-as-data idiom unusually well. It depends on
  nothing unbuilt, so nothing else here can block it; a cheap headline (#SAT
  complete for ΣQSO(FO)) sits one `exists_gates` strengthening in; and it is
  the meeting point with provenance-lean. Internal order: framework layer and
  ladder levels 0–1 → evaluator → `#P := ΣQSO(FO)` → #SAT → the free entries
  and PQE tier 1; stop there (level 2 of the ladder, PQE tier 2, structure
  inside #P, the quantitative fixed point and MaxSNP are genuine research, or
  gated on a literature check). Its size is what puts it beside the numbered
  line rather than in it.
- **The rest of the sharpening pass** (each [M], no prerequisites, no new
  surface): **quantifier-free / projection / dimension tracking through
  composition** (§3's reduction-notion refinements), which upgrades catalog
  statements to the DC-faithful "complete under qfps", and **Spectra** (§4).
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
- Of the BIT / AC⁰ / PARITY chain, only the two ends: the **circuit bridge**
  (§4) and **PARITY ∉ AC⁰** (§5), both [R]. The chain turned out to split rather
  than to stand or fall together – the arithmetic vocabulary, the class it
  defines, `FO(≤) ⊊ AC⁰`, `AC⁰ ⊆ PTIME` and PARITY in LOGSPACE cost about
  1 600 lines and are built (§3), but nothing above depends on the two ends,
  and until they exist the two by-inspection claims in the README stay an
  honest, documented gap. What is worth doing next in that area is the sharp
  bound `AC⁰ ⊆ LOGSPACE` and, on demand, class-hood: both §3, neither [R].
- Complete problems for the exponential classes, and with them the generic
  succinctness theorem. The design work is done (§3, the outer composition):
  the order on the expanded universe, the translation lemma and the gate
  `PSPACE = NL.exp` are built, so what is left is either the quantifier-free
  track for succinct problems or a natural problem whose membership is direct.

This weighting assumes the goal is research output and formalization firsts. If
the near-term goal is the course companion of §8, the cookbook and catalog
growth move up and the counting and inexpressibility tracks slide down:
students meet NL, P-completeness and reductions long before they meet ΣQSO or
an Ehrenfeucht–Fraïssé game.
