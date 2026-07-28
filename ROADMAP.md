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
| SO(TC) (PSPACE) | QSAT | least mechanical: natural image is a succinct/game reachability, QSAT via the standard alternation argument |

- **P-complete reductions from HORN-SAT** [M]: Circuit Value Problem, Monotone
  CVP, and alternating reachability (DC's canonical P-complete problem, with
  quantifier-free-projection hardness in the book), entering the catalog as
  ordinary catalog reductions *from* HORN-SAT rather than as primary discharges.
- **DP: SAT-UNSAT's hardness** [M–L, ~400–600 lines]: the class `DP` exists
  (`Difference.lean`), with `NP ∪ coNP ⊆ DP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`, and SAT-UNSAT is
  defined and *in* DP (`Problems/SatUnsat.lean`); what is missing is "every
  DP-definable problem ordered-FO-reduces to SAT-UNSAT". The construction: from
  `Q ≡ S ⊓ T` take the Cook–Levin discharge `f₁ : S ≤ᶠᵒ[≤] SAT` and
  `f₂ : Tᶜ ≤ᶠᵒ[≤] SAT` (`T` being `Π₁`, its complement is `Σ₁`), and pair them
  into one interpretation into `Language.satPair`: tags `f₁.Tag ⊕ f₂.Tag`,
  dimension `max f₁.dim f₂.dim`, each side's three relations defined by that
  side's formulas on its own tags and `⊥` on the other's.

  **The hazard, worked out and worth not rediscovering:** the extra coordinates
  of the shorter side must be pinned to a minimum with `Padding.lean`'s `Canon`
  / `canonF`, with junk excluded from all six relations. Simply letting the
  spare coordinates range freely is *unsound*, not merely wasteful: every
  clause and every variable then acquires `|A|^(dim−dᵢ)` copies, each clause
  copy containing *all* copies of each of its variables, and the blow-up can be
  satisfiable when the original is not – the unsatisfiable `{x}, {¬x}` blows up
  to `(x₁ ∨ x₂ ∨ …) ∧ (¬x₁ ∨ ¬x₂ ∨ …)`, satisfiable as soon as there are two
  copies. Canonical padding restores the bijection with the original points and
  the correctness proof goes through side by side.
- **L: REACHd** [M]: outdegree-≤1 reachability, complete for FO(DTC).
- **PSPACE: QSAT** [L]: unbounded-alternation QBF; hardness = "every
  SO(TC)-definable (equivalently FO(PFP)-definable) problem ordered-FO-reduces
  to QSAT". Downstream: game problems (Generalized Geography…) [L each,
  gadget-heavy].
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
- **FO(TC), the rest of it** [M]: the definability layer exists
  (`TransitiveClosure.lean`: `TCSpec`/`TCDefinable`, a single TC over a
  first-order transition formula on `k`-tuples, with `reach_tcDefinable` as the
  canonical instance; a `TCSpec` carries a finite *mode* component beside its
  tuple, the analogue of an interpretation's tags, without which neither the
  translations nor closure under reductions can be stated), and so do both
  translations against the Krom fragment: `co-NL(Krom) = NL(TC)`, i.e.
  `mem_NL_iff_tcDefinable_compl` (`SigmaSOKromDefinable.compl_of_tcDefinable` in
  `TransitiveClosureKrom.lean`, `TCDefinable.compl_of_sigmaSOKromDefinable` in
  `KromTransitiveClosure.lean`), sharpened to `NL(Krom) = NL(TC)` by the
  complementation of FO(TC) (`tcDefinable_iff_mem_NL`). What remains here is
  **closure of `TCDefinable` under ordered FO reductions** [M] – pull
  the spec back with modes `spec.Mode × (Fin k → Tag)` and tuples of length
  `k · d` – which would make FO(TC) a `ComplexityClass` in its own right if that
  is ever wanted; today it is a definability notion only, tied to NL through the
  translations above.
- **FO(DTC)** [M, after the above]: the deterministic variant, i.e. the same
  `TCSpec` with `step` replaced by its FO determinization
  `step(x̄, ȳ) ∧ ∀z̄. step(x̄, z̄) → z̄ = ȳ`; that formula is first-order, so
  `DTCDefinable P → TCDefinable P` (the definability-level `L ⊆ NL`) is a
  one-liner once the determinizing formula and its realization lemma exist.
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
  drift); `#P` as "number of accepting runs" is easy to state but needs the
  parsimonious-reduction notion the framework still lacks (§6, first item);
  the classes-are-logic principle points at `ΣQSO(FO)` for the definition
  either way, with the machine count as a bridge statement.

## 8. Teaching material

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
   What remains of this step: **FO(DTC)**/**REACHd**.
3. **PSPACE**: SO(TC), then QSAT; afterwards FO(PFP)/FO(LFP) as the
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
the near-term goal is the course companion of §8, the cookbook and catalog
growth move up and PSPACE slides down: students meet NL, P-completeness and
reductions long before they meet SO(TC).
