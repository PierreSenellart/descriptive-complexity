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
  fragment; also available *at arity 2* – the threshold as the cardinality of
  a marked binary relation, which is what objectives counting arcs need
  (`nonempty_embedding_iff_ncard_le₂`, `Language.markedArcGraph`). The tagged
  framework does cardinality arithmetic natively
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

Current: SAT, 3SAT, 3COL (both directions), the full
NP-completeness of the clique family (Clique/IS/VC), via the
SAT → Clique ordered reduction, the Σ₁ membership of Clique, and the
existing Clique/IS/VC inter-reductions; Set Cover / Hitting Set,
Set Packing, k-colorability and Feedback Vertex Set (see the items
below). `TODO.md` carries the running status table of Karp's 21 with a
proof plan for each problem still open.

- **Set Cover / Hitting Set / Set Packing** [S, *done*]: `Problems/SetFamily/`
  (`Defs`, `Reductions`, `FromGraphs`, `Membership`) plus the umbrella
  `Problems/SetFamily.lean`, laid out like `Problems/CliqueFamily/`:
  generic properties on predicates, inter-reductions inside the family, the
  hardness source, the `Σ₁` definitions, and completeness theorems in the
  umbrella. Vocabulary `Language.setSystem`: two unary
  marks separating ground elements from sets of the family, a binary
  incidence relation, and the threshold mark (representation (A)). The
  two problems are one generic property `CoversOn` read in the two
  directions of the incidence relation, so a single dimension-1
  quantifier-free interpretation (`transposeInterp`) reduces each to
  the other, as complementation does for Clique/IS. Hardness comes
  from VC by the textbook edge-incidence reading (`edgeIncidenceInterp`,
  dimension 2: off-diagonal adjacent pairs are the edge-elements,
  diagonal pairs the vertex-sets, everything else junk that no relation
  mentions), membership by the same `Σ₁` shape as Clique with the
  injection running *into* the marked set, the threshold being an upper
  bound here. Note the general lesson: junk tuples are free whenever
  the target vocabulary carries its own “this element is a real one”
  marks.
- **The coloring family** [M, *done*]: `Problems/Coloring/` (`Defs`,
  `Reductions`, `Membership`) plus the umbrella `Problems/Coloring.lean`,
  holding k-colorability for fixed k, Chromatic Number and Clique Cover on
  one generic property `ColorableOn` (a map into `Fin k` separating a
  *conflict* relation). `KColorable k`/`KCol k` for all k
  (`kCol_three : KCol 3 = ThreeCol`), `kCol_NP_complete (hk : 3 ≤ k)`.
  Membership guesses the k color classes as k unary relation variables
  (`Formula.iSup`/`iInf` over `Fin k` in the kernel); hardness pads
  3COL with m = k − 3 universal vertices, which an interpretation can
  only add as *tags*, hence as blown-up independent classes
  (`padColorInterp`, tag type `Option (Fin m)`). The blow-up is
  harmless: the classes take pairwise disjoint colors, all distinct
  from the original part's, which is what leaves exactly 3 colors for
  the input graph – a counting argument that needs the input structure
  nonempty (an empty class would eat no color).
  **Chromatic Number** (threshold k = |marked|) and **Clique Cover** are the
  other two members. Chromatic Number is hard by the catalog's first ordered
  reduction outside the SAT family (`chromInterp`, tag `Fin 4`): the marked
  set must have *exactly three* elements, which only an order can produce
  (three copies of the minimum, via `minF`), and the fourth tag turns each
  self-looped vertex into a `K₄`, since the threshold problems read their
  conflict relation off the diagonal while 3-colorability does not. Clique
  Cover is coloring of the complement, so `complEdgeInterp` of the clique
  family relates the two in both directions. Their membership uses the
  *palette* form of a threshold (`paletteColorableOn_iff`): with `k` unavailable
  to the formulas, colouring with `|marked|` colors is colouring *by* the
  marked set, which one binary relation variable expresses.
- **Set Packing** [S, *done*]: the third member of the family above,
  `PacksOn` (a pairwise disjoint subfamily at least as large as the marked
  set) and `setPacking_NP_complete`. Its hardness reduction is the *same*
  `edgeIncidenceInterp` as for Set Cover, read from Independent Set: two distinct vertices are non-adjacent exactly when their sets of
  incident edges are disjoint (`exists_elem_mem_both_iff`). Note the design
  point: disjointness is required of the *ground elements* only, and that
  guard is load-bearing – the junk pairs of the interpretation are incident
  to two vertex-sets each, and they are exactly the pairs that must not
  witness an intersection.
- **Feedback Vertex Set and Feedback Arc Set** [M, *done*]:
  `Problems/Feedback/` (`Defs`, `Reductions`, `Membership`) plus the umbrella
  `Problems/Feedback.lean`, `feedbackVertexSet_NP_complete` and
  `feedbackArcSet_NP_complete`. On marked graphs, whose adjacency is an
  arbitrary binary relation, i.e. a digraph; acyclicity of what survives the
  removal is `Relation.TransGen`-irreflexivity (`AcyclicOff`). Hardness is
  Vertex Cover with the arcs *symmetrized off the diagonal*
  (`symmetrizeInterp`, quantifier-free, dimension 1): every edge becomes a
  2-cycle, so killing all cycles is exactly meeting all edges, and the marked
  set is copied, so there is no counting step at all. Membership rests on
  `acyclic_iff_exists_order`: acyclicity is equivalent to the existence of a
  strict partial order containing every surviving arc, which is the
  first-order certificate the `Σ₁` block guesses (together with the removed
  set and the threshold injection). Feedback Arc Set follows by the classical
  vertex splitting (`splitInterp`, tag `Bool`): each vertex becomes an in-copy
  and an out-copy joined by an internal arc, cutting which is deleting the
  vertex. Its vocabulary is `Language.markedArcGraph`, whose threshold is the
  cardinality of a marked *binary* relation – representation (A) read at arity
  2, the extension §0 needed for arc-counting objectives – so its `Σ₁`
  definition guesses a 4-ary injection of pairs into pairs. Both directions of
  the splitting correctness *build an order* from another one, so the
  certificate form of acyclicity turns out to be the right tool for reductions
  and not only for membership; Steiner Tree and the Hamilton problems should
  reuse it.
- **Dominating Set** [M, *done*]: `Problems/DominatingSet/`,
  `dominatingSet_NP_complete`. On `Language.markedGraph` unchanged. The entry
  that used to stand here predicted an *ordered* reduction; that was wrong,
  and the correction is worth keeping. Domination does constrain every element
  of the universe, junk tuples included, so junk cannot be ignored the way the
  covering and packing conditions ignore it – the fix is simply to make the
  junk adjacent to all set-vertices, so that any nonempty solution dominates
  it. And the two degenerate cases that seemed to need a canonical extra
  vertex are both *first-order*, so gating on them suffices: “some element
  belongs to no set” (input and output both no-instances: the output is made
  edgeless with an empty threshold) and “there is no element at all” (both
  yes-instances: the output is made edgeless with everything marked). Outside
  those two cases every cover is nonempty, which is exactly what makes the
  clique of set-vertices dominated. The reduction is therefore order-free.
- **NAE-SAT** [M, *done*]: `Problems/NaeSat.lean`, `naeSat_NP_complete`. On
  the SAT vocabulary unchanged – only the notion of satisfaction differs
  (`NAEProper`: every clause has a true *and* a false literal), so this adds a
  problem, not a language. Hardness is the classical fresh-variable reduction
  from SAT, and it is *ordered* for a structural reason worth remembering: an
  interpretation adds elements only by tags, and a tag contributes a whole
  copy of the universe, so “one fresh variable” has to be picked out as the
  minimum of its copy (`minF`). One fresh variable *per clause* would make the
  reduction false, since a private `s` can always be set opposite to a
  literal. Membership reuses `realize_satKernel` verbatim: the NAE kernel is
  SAT's conjoined with its mirror image.
- **NAE-3SAT** [M, *done*]: `Problems/NaeThreeSat.lean`,
  `nae3Sat_NP_complete`. The width-3 variant, on the SAT vocabulary with
  3SAT's promise `WidthAtMostThree` folded into the yes-instances. Both
  reductions reuse the SAT/3SAT *interpretations verbatim* – the width-gated
  copy `threeSatToSat` for membership, the clause-splitting `satToThreeSat`
  for hardness – only the notion of satisfaction differing; the width promise
  `widthAtMostThree_map` is inherited as proved. Two corrections to the plan
  this item used to carry: the splitting auxiliary is *not* per clause but per
  *occurrence* (a clause of width k needs k−2 of them, each naming its
  position), so the reduction is ordered, not order-free – which is precisely
  why 3SAT's chain can be reused; and the chain works unchanged in the
  not-all-equal reading, `NAE(T_i, ℓ_i, ¬T_{i+1})` being the peeling identity
  `NAE(a, ℓ, ℓ', …) ↔ ∃ y, NAE(a, ℓ, y) ∧ NAE(¬y, ℓ', …)` applied along the
  occurrence order. Only the witnessing assignment is new (`LinkVal`: a
  linking variable carries the negation of the value common to all earlier
  occurrences while they agree, its own literal's value once they do not).
  The converse half needs nothing new: a not-all-equal assignment is in
  particular a satisfying one, so 3SAT's chain argument – isolated as
  `SatToThreeSat.exists_litTrue_of_map` – applies to it and, by the flip
  symmetry `NAEProper.not`, to its negation.
- **1-in-SAT** [M, *done*]: `Problems/OneInSat/`, `oneInSat_NP_complete`.
  Exactly-one satisfiability, on the SAT vocabulary unchanged – a third notion
  of satisfaction (`OneInProper`) rather than a new language. Membership
  reuses `realize_satKernel` and adds uniqueness as *three* clauses, one per
  sign pattern (positive/positive, negative/negative, and the mixed one simply
  forbidden); splitting the sign cases at the formula level, instead of a
  metalevel `if`, is what keeps the realization proof cheap – the `if` version
  blew past the heartbeat limit.

  The unrestricted version is deliberate: Exact Cover reduces from it at any
  clause width, so the width-three variant would be dead weight.

  Hardness is an ordered reduction from 3SAT whose point is the **three-slot
  normalization** (`Problems/OneInSat/Slots.lean`), which removes the width
  case analysis the textbook gadget forces. Every clause gets slots
  `sl₁, sl₂, sl₃` and, per slot, a link clause `{¬slᵢ} ∪ {the i-th occurrence,
  if there is one}`: read as exactly-one clauses this says `slᵢ ↔ (i-th
  literal)` when the occurrence exists and `slᵢ = false` when it does not,
  *the same clause description in both cases*, one literal shorter. The gadget
  proper is then always `1-in-3(¬sl₁, d, e)`, `1-in-3(sl₂, e, f)`,
  `1-in-3(¬sl₃, f, g)`, satisfiable iff some slot is true, with explicit
  witnesses `d = sl₁ ∧ sl₂`, `e = sl₁ ∧ ¬sl₂`, `f = ¬sl₁ ∧ ¬sl₂`,
  `g = (sl₁ ∨ sl₂) ∧ sl₃`. Clauses of width 0, 1 and 2 need no special case.
  Two engineering notes: with 14 tags, the defining formulas must *not* match
  on tag pairs (that would be ~200 cases in every characterization lemma) –
  `posPair`/`negPair` are `Bool`-valued functions instead, the characterization
  lemmas then need no tag case analysis at all, and the tag combinatorics is
  discharged later by `decide`; and the “exactly one true literal” obligations
  are best discharged by explicit defeq terms rather than `simp`, which
  requires making the helper's literal arguments explicit so that the slots
  are not metavariables.
- **Exact Cover** [M, *done*]: `ExactCover` and `exactCover_NP_complete`
  (`Problems/ExactCover.lean`), on `Language.setSystem` unchanged. Exactness
  is a new `…On` predicate, not a new vocabulary: `ExactlyCoversOn` is
  covering *plus* the disjointness Set Packing already asks for
  (`exactlyCoversOn_iff_unique` restates it as “exactly one covering set per
  element”), and the marked set plays no role – exactness replaces the
  threshold, so there is no injection to guess and the `Σ₁` kernel is three
  existing clauses conjoined (`sfFamClause ⊓ sfCoverClause ⊓ sfDisjClause`).

  Hardness is the cheapest reduction in the catalog: **no order, no gadget, no
  counting**, dimension 1. The ground elements are the variables and the
  clauses; the family has one set per literal `(x, s)`, namely `{x} ∪
  {clauses where (x, s) occurs}`. Covering the element `x` exactly once picks
  exactly one of the two literals of `x` – that *is* an assignment – and
  covering a clause exactly once *is* exactly-one satisfaction. Nothing
  depends on the clause width, which is why the source is unrestricted
  1-in-SAT.
- **Set Splitting** [S, *done*]: `Problems/SetSplitting.lean`,
  `setSplitting_NP_complete`. Hypergraph 2-colourability, on
  `Language.setSystem` unchanged and with no threshold: `SplitsOn` asks for a
  colour class meeting every set of the family and its complement, so the `Σ₁`
  definition guesses that class and checks two clauses. Hardness is the
  shortest reduction in the catalog: the ground elements are the *literals*,
  the family is one pair set `{x, ¬x}` per variable plus one set per clause.
  Splitting a pair set is exactly “the two literals of `x` get opposite
  colours”, i.e. an assignment; splitting a clause set is exactly not-all-equal
  satisfaction. Order-free, dimension 1, no gadget, no counting – the pair
  sets are the only thing the reduction adds.

- **X3C, 3-Dimensional Matching** [M–L]: from Exact Cover once it is hard;
  local gadgets, probably ordered.
- **Steiner Tree** [M, *both variants done*]: `Problems/Steiner/`
  (`Defs`, `Reductions`, `Membership`) plus the umbrella
  `Problems/Steiner.lean`, `steinerTree_NP_complete`. Vocabulary
  `Language.steinerGraph`: adjacency plus two unary marks, the terminals and
  the threshold. The formalized problem is the node-weighted one with unit
  weights – a connected set spanning the terminals with at most `k`
  non-terminals – hard from Vertex Cover by an ordered reduction (tag
  `SteinerTag`, dimension 2): edges become the terminals, vertices the
  available Steiner points, and the minimum of a spare copy the root joining
  them. Karp's **edge-weighted** reading is `EdgeSteinerTree`
  (`edgeSteinerTree_NP_complete`), on the same vocabulary – a threshold is a
  number, so it may bound a count of *pairs*
  (`nonempty_embedding_iff_ncard_le'`) – with the budget enlarged by one unit
  per edge point, marked by marking the edge points themselves so that no
  arithmetic enters the formulas. Its key ingredient is the `n − 1` edge bound
  `ncard_le_ncard_of_connected`, which follows from the certificate rather
  than from a spanning tree: each non-root member has a parent edge, and two
  members sharing an edge would be each other's parent, hence strictly below
  each other. Reusable output: the connectivity certificate
  (`connectedOn_iff_exists_root`), the bounded-reachability staging `reachIn`,
  and that edge bound, all stated for an arbitrary relation.
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
| SO-Horn (P) | HORN-SAT | done (no gates needed: guards are evaluated, not encoded) |
| SO-Krom (NL) | 2SAT | Krom kernel ⇒ binary clauses |
| SO(TC) (PSPACE) | QSAT | least mechanical: natural image is a succinct/game reachability, QSAT via the standard alternation argument |

HORN-SAT is done; CVP and alternating reachability now enter the catalog
as ordinary reductions *from* HORN-SAT rather than as primary discharges.
Note that the Horn discharge did **not** reuse the Tseitin machinery: a
Horn kernel needs no gates at all, only the canonical padding of
`Padding.lean` (factored out of the Tseitin files for the purpose).

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
    signs – *not* a complementation of the assignments, which would only
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
    – the shape any *alternating* discharge needs, since the prefix
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
  - HORN-SAT: the primary discharge, per the symmetry table above.
    **Done** (`hornSat_hard_of_sigmaSOHornDefinable`, in
    `Problems/HornSat/`): the Horn program is read as data, its guards
    are *evaluated* in the input structure rather than encoded, and each
    clause instance emits one propositional clause – no Tseitin gates,
    hence Horn output (`horn_atMostOnePositive`). Membership
    `HORNSAT ∈ NP` is there too (`hornSat_sigmaSODefinable`), and
    `Problems/Reachability.lean` gives the fragment its worked instance:
    UNREACH is SO-Horn definable, hence FO-reduces to HORN-SAT.
  - Circuit Value Problem, Monotone CVP, and alternating reachability
    (DC's canonical P-complete problem, with quantifier-free
    projection hardness in the book): as catalog reductions from
    HORN-SAT.
  - **The PTIME class is done** (`PTIME`, in `Hierarchy.lean`): guards
    live over the ordered expansion, and `SecondOrderHornPull.lean`
    proves the *shape-preserving* pullback – the Horn condition
    constrains only the second-order atoms, which an interpretation
    merely re-indexes, while the input-vocabulary atoms it rewrites live
    in the guards. Hence `hornSat_PTIME_hard` and `PTIME_subset_NP` (the
    latter for free: everything reduces to HORN-SAT, which is in NP), and
    `unreach_mem_PTIME`.
  - **HORN-SAT's own SO-Horn definability** [M–L, *done*]:
    `hornSat_mem_PTIME` in `Problems/HornSat/Definability.lean`, hence
    `HORNSAT_PTIME_complete`. An input clause has unboundedly many
    negative literals, which a program with a fixed number of body atoms
    cannot collect in one clause; the program walks them along the order
    with a derived relation `B c z` = “every negative literal of `c` up
    to `z` is forced”, four rules (base/step × literal/non-literal)
    assembling the unbounded body one element at a time, one rule
    deriving `T` from a complete body, and two goal clauses (an
    all-negative clause with complete body; two positive literals in one
    clause). The semantic half is the least-model theory of
    `Problems/HornSat/Unsat.lean` (stages `ForcedIn`, closure `Forced`,
    `forced_subset_model`).
  - **Level 0 of the hierarchy is `PTIME`** (`SigmaP 0 = PTIME`,
    `PiP 0 = PTIME.compl`), `mem_piP_iff` holds at every level, and all
    four inclusions into level 1 are proved: `PTIME_subset_NP`,
    `PTIME_subset_coNP`, `coPTIME_subset_NP`, `coPTIME_subset_coNP`. The
    two crossing ones go through **`HORNSAT ∈ coNP`**
    (`Problems/HornSat/Unsat.lean`, done): a `Σ₁` certificate of Horn
    *un*satisfiability – guess a strict order and a set `T`, check
    first-order that each element of `T` is derived by a clause whose
    negative literals are in `T` and strictly earlier (which pins `T`
    inside the propagation closure), and that some all-negative clause
    has all its literals in `T`. Soundness is a well-founded induction
    using the Horn condition; completeness is that the closure is
    otherwise a model.
  - **Level 0 closed under complement** [*done*]: the two zeroth levels
    coincide, `piP_zero_eq : PiP 0 = SigmaP 0`, via the logic-to-logic
    equivalence SO-Horn = FO(LFP) (§3, `FixedPointHorn.lean`): a full
    logic is closed under negation by construction, and the translation
    back into the fragment makes the two interchangeable
    (`lfpDefinable_iff_sigmaSOHornDefinable`,
    `SigmaSOHornDefinable.compl`). Concretely: Horn *un*satisfiability is
    SO-Horn definable (`hornSat_compl_mem_PTIME`) and
    `reach_mem_PTIME` – statements a goal clause could not supply
    head-on, since goal clauses carry no negative information about the
    least model.
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

- **SO-Horn and SO-Krom (Grädel)** [M–L, *SO-Horn done, SO-Krom open*]:
  existential SO with Horn (resp. Krom) FO kernel captures P (resp. NL)
  on ordered structures. Key observation: this fits the existing
  framework far more cheaply than fixpoint logics, since SO quantifiers
  are already Lean-level and only the kernel shape is object-level.
  Still the cheapest path to an axiom-free definition of PTIME, ahead
  of FO(LFP). Landed: `SecondOrderHorn.lean` – the kernel *as data*
  (`HornProgram`: a list of clauses, each a first-order guard over the
  input vocabulary, a list of body atoms and an optional head atom) and
  `SigmaSOHornDefinable`. Representing the kernel as a clause list
  rather than carving a shape predicate out of `BoundedFormula` is what
  keeps this cheap: it is Grädel's clausal normal form, and it is the
  form a consuming reduction has to see anyway. `SecondOrderHornPull.lean`
  adds the shape-preserving pullback, hence the class `PTIME`, and
  `Problems/HornSat/` its complete problem. Remaining: SO-Krom by the same
  recipe – the Krom shape (at most two second-order atoms per clause, of
  either sign) is another clause-list datatype, and its discharge to 2SAT
  should be the same construction with the literal signs read off the
  clause.
- **FO(LFP)** [L, *done*, including the equivalence with SO-Horn]:
  `FixedPoint.lean` defines it in the
  same clausal style as SO-Horn – a rule system whose least fixed point
  is the inductive predicate `Derives`, plus an **unrestricted**
  first-order output sentence read at that fixed point. No object-level
  fixpoint binder, no positivity predicate and no stage machinery were
  needed: positivity is built into the rule shape, and leastness comes
  from the inductive definition (`lfpAssign_rule`,
  `lfpAssign_least_of_closed`). Landed with it:
  - `LFPDefinable.compl` – closure under complement, *one line*: negate
    the output. This is precisely what SO-Horn cannot do, and why the
    logic is worth having.
  - `SigmaSOHornDefinable.lfpDefinable` – every SO-Horn definition is an
    FO(LFP) definition: keep the rules, turn the goal clauses into the
    output. Hence `PTIME ⊆ FO(LFP)` and, by complement, also
    `co-PTIME ⊆ FO(LFP)`; concretely `reach_lfpDefinable` and
    `hornSat_compl_lfpDefinable` are statements the fragment cannot make.
  - `LFPDefinable.of_orderedReduction` – closure under (ordered) FO
    reductions, so FO(LFP) definability is a class-worthy notion: the
    rules pull back as a Horn program, their fixed point commutes with
    the pullback (`lfpAssign_pull`, `lfpAssign_map`), and the output
    sentence pulls back through `extendSO`, the three views of the
    interpreted structure being identified by `extendSOEquiv` and
    `ordExtendLEquiv`.
  - `derivesIn`/`depth`/`derives_eq_of_closed_of_wf` – the stage theory
    and the **certificate characterization**: a relation closed under the
    rules and well-foundedly derivable *is* the least fixed point, with
    `derives_step_of_depth` supplying the order. Packaged for use as
    `LFPDef.holds_iff_of_certificate`. This is the semantic key to both
    remaining constructions.
  - **The converse translation FO(LFP) → SO-Horn** [*done*,
    `FixedPointHorn.lean`]: where a `Σ₁` version would *guess* the
    certificate, the Horn version *derives* it – the complement of the
    fixed point via stage-indexed derivations along the order (stages =
    lexicographic tuples times a static copy count, enough to exceed the
    stabilization point `derivesIn_iff_derives_of_card_le` on every
    nonempty structure, one-element universes included), the unbounded
    “nothing derives this” conjunctions assembled by order-walking
    accumulators (the technique of `Problems/HornSat/Definability.lean`,
    applied to a rule system rather than one clause body; the shared
    order-walk machinery now lives in `OrderWalk.lean`), and a clausal
    evaluator for the output formula over its subformula closure. With
    it: `lfpDefinable_iff_sigmaSOHornDefinable`,
    `SigmaSOHornDefinable.compl`, `piP_zero_eq`, and the option of
    *defining* PTIME by the logic.
  - **Remaining**: `FO(LFP) ⊆ NP` *directly* [M], by guessing the fixed
    point and the derivation order and checking both first-order against
    the certificate interface (`derives_eq_of_closed_of_wf`). No new
    mathematics – the inclusion already follows by composing the
    translation with the Horn discharge – but the direct `Σ₁` definition
    would be textbook-faithful; the work is formula building, made
    tedious by the varying arities of a block's atoms.
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

1. Cheap catalog wins: **done** (Set Cover / Hitting Set, Set Packing,
   k-COL, Chromatic Number, Clique Cover, Feedback Vertex Set, Feedback Arc
   Set, Subgraph Isomorphism, TAUT); next in the same
   vein: the Schaefer-style sources (NAE-SAT, NAE-3SAT, 1-in-SAT) are all
   done, and with them Max Cut and Exact Cover;
   Max Cut is done too (§1), so the Schaefer-style sources have paid off.
   Dominating Set has been reclassified as an ordered reduction (see §1).
1bis. Machine bridge (bounded NTM acceptance NP-complete, §4): high
   foundational value; schedule early.
2. SO-Horn path to an axiom-free PTIME: **done** – the class, its
   closure under reductions, HORN-SAT complete for it, and now
   `PiP 0 = SigmaP 0` (§2) through the equivalence SO-Horn = FO(LFP),
   Grädel's capture theorem in its machine-free form.
3. EF games + EVEN/REACH inexpressibility (opens §5).
4. FO(TC)/REACH, then Immerman–Szelepcsényi as the flagship theorem.
5. SO(TC) and QSAT for PSPACE; then FO(LFP)/FO(PFP) as the
   textbook-faithfulness layer and the rest of §4.
