/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Ordered
import DescriptiveComplexity.Composition
import DescriptiveComplexity.OrderedComposition
import DescriptiveComplexity.Complexity
import DescriptiveComplexity.Encoding
import DescriptiveComplexity.Encoding.UnaryBlowup
import DescriptiveComplexity.Decoding
import DescriptiveComplexity.SecondOrder
import DescriptiveComplexity.SecondOrderLift
import DescriptiveComplexity.SecondOrderPull
import DescriptiveComplexity.SecondOrderOrdered
import DescriptiveComplexity.SecondOrderMerge
import DescriptiveComplexity.SecondOrderHorn
import DescriptiveComplexity.SecondOrderHornPull
import DescriptiveComplexity.ClauseDischarge
import DescriptiveComplexity.SecondOrderKrom
import DescriptiveComplexity.SecondOrderKromPull
import DescriptiveComplexity.SecondOrderNew
import DescriptiveComplexity.Relativize
import DescriptiveComplexity.SecondOrderNewPull
import DescriptiveComplexity.SecondOrderNewOrdered
import DescriptiveComplexity.RecursivelyEnumerable
import DescriptiveComplexity.LogSpace
import DescriptiveComplexity.TwoCnf
import DescriptiveComplexity.TransitiveClosure
import DescriptiveComplexity.TransitiveClosureKrom
import DescriptiveComplexity.KromImplication
import DescriptiveComplexity.KromTransitiveClosure
import DescriptiveComplexity.Counting
import DescriptiveComplexity.TransitiveClosureCompl
import DescriptiveComplexity.ImmermanSzelepcsenyi
import DescriptiveComplexity.TransitiveClosureReach
import DescriptiveComplexity.TransitiveClosureDet
import DescriptiveComplexity.TransitiveClosurePull
import DescriptiveComplexity.DetLogSpace
import DescriptiveComplexity.HeadAutomaton
import DescriptiveComplexity.HeadProgram
import DescriptiveComplexity.HeadEval
import DescriptiveComplexity.HeadCapture
import DescriptiveComplexity.WalkBudget
import DescriptiveComplexity.HeadLex
import DescriptiveComplexity.HeadCaptureDet
import DescriptiveComplexity.FixedPoint
import DescriptiveComplexity.OrderWalk
import DescriptiveComplexity.FixedPointHorn
import DescriptiveComplexity.Hierarchy
import DescriptiveComplexity.SecondOrderTransitiveClosure
import DescriptiveComplexity.SecondOrderTransitiveClosurePull
import DescriptiveComplexity.PSpace
import DescriptiveComplexity.PSpaceCompl
import DescriptiveComplexity.PSpaceHierarchy
import DescriptiveComplexity.Relationalize
import DescriptiveComplexity.Difference
import DescriptiveComplexity.Padding
import DescriptiveComplexity.OccurrenceOrder
import DescriptiveComplexity.OccurrenceFormulas
import DescriptiveComplexity.OccurrenceSlack
import DescriptiveComplexity.OccurrenceVar
import DescriptiveComplexity.Numbers
import DescriptiveComplexity.Machines
import DescriptiveComplexity.Problems
import DescriptiveComplexity.Examples

-- The rows of the catalog table below cannot be broken across lines.
set_option linter.style.longLine false

/-!
# Descriptive complexity in Lean 4

A library for descriptive complexity built on Mathlib's `ModelTheory`:
machine-model-free hardness reductions and a logically-defined polynomial
hierarchy, in the style of Immerman's *Descriptive Complexity*
([Immerman 1999][immerman1999descriptive]).

Complexity theory is largely absent from Mathlib because formalizing a model
of computation with resource bounds is hard. The observation this library
rests on is that many classical NP-hardness reductions do not need the full
strength of a Turing machine: they are *first-order expressible*. An FO
reduction is computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, so exhibiting one is
strictly stronger than exhibiting a Karp reduction
([Karp 1972][karp1972reducibility]), while needing no machine model at all –
only first-order logic, which Mathlib already provides.

This page is the high-level map of the library, part by part. The `README`
gives the general pitch; the worked examples in
`DescriptiveComplexity.Examples.ConjunctiveQueries` (conjunctive-query
evaluation and containment) and `DescriptiveComplexity.Examples.GraphCrawling`
(Web data acquisition, with a cardinality threshold, a reachability
certificate and an ordered reduction) are the hands-on tutorials;
individual declarations are documented on their own pages.

## The framework: problems, interpretations, reductions

* `DescriptiveComplexity.Interpretation` – a `DescriptiveComplexity.DecisionProblem`
  is an isomorphism-invariant property of finite structures of a language
  (invariance is baked into the notion, as is standard in descriptive
  complexity). A `DescriptiveComplexity.FOInterpretation` is a tagged,
  `dim`-dimensional first-order interpretation of one language in another,
  and a `DescriptiveComplexity.FOReduction` (notation `P ≤ᶠᵒ Q`) is one that
  maps yes-instances exactly to yes-instances, on the *finite* nonempty
  structures – the only ones membership and hardness ever read. Tags replace
  the linear order that textbook FO reductions use to encode constantly-many
  sorts of elements.
* `DescriptiveComplexity.Composition` – the pullback of a formula through an
  interpretation and the composition of interpretations, giving reflexivity
  and transitivity of `≤ᶠᵒ` (a `Preorder` on problems, usable in `calc`).
* `DescriptiveComplexity.Ordered` and
  `DescriptiveComplexity.OrderedComposition` – reductions over the ordered
  expansion of the source language, `DescriptiveComplexity.OrderedFOReduction`
  (notation `P ≤ᶠᵒ[≤] Q`): order-invariant FO(≤) reductions, correct on every
  finite linearly ordered input. This is the standard notion of the field and
  the home of gadget constructions that genuinely need an order.

## The abstract complexity layer

* `DescriptiveComplexity.Complexity` – `DescriptiveComplexity.ComplexityClass`,
  with membership, hardness and completeness, closed by construction under
  (ordered) FO reductions. Membership and hardness depend only on the
  *finite* instances of a problem, making explicit that these statements say
  nothing about infinite structures.
* `DescriptiveComplexity.Encoding` – bringing your own instance types: a
  `DescriptiveComplexity.Encoding` bundles a concrete instance type, its declared
  size, a computable encoding into finite structures, and polynomial bounds
  *both ways* between size and universe – no padding, no compression – so an
  encoding cannot be built size-dishonest. Semantic agreement is the separate
  predicate `DescriptiveComplexity.Encoding.Faithful`. That the bounds have
  teeth is a theorem: no unary encoding of subset-sum passes them
  (`DescriptiveComplexity.no_unary_encoding`, in
  `DescriptiveComplexity.Encoding.UnaryBlowup`, with the honest binary encoding
  as the positive contrast).
* `DescriptiveComplexity.Decoding` – the decoding direction, for reading
  *hardness* concretely: well-formedness conditions as decision problems
  (`DescriptiveComplexity.DecisionProblem.ofSentence`, restricting a problem to
  its non-junk instances as `W ⊓ P` with one-line upgrades of existing
  completeness proofs), and computable decodings
  (`DescriptiveComplexity.Decoding`) from concretely presented structures back
  to concrete instances, with the same executable hygiene as the encoders.
  Both tutorials – `DescriptiveComplexity.Examples.ConjunctiveQueries` and
  `DescriptiveComplexity.Examples.GraphCrawling` – open with a concrete
  instance type and its bundled encoding, and close the loop with a decoder
  and a well-formed completeness theorem.

## The polynomial hierarchy, defined logically

* `DescriptiveComplexity.SecondOrder` (with `…Lift`, `…Pull`, `…Ordered`) –
  existential/universal second-order definability with `k` quantifier-block
  alternations.
* `DescriptiveComplexity.Hierarchy` – the levels `Σₖᵖ`/`Πₖᵖ` and `PH` as
  complexity classes, via Fagin's ([Fagin 1974][fagin1974generalized]) and
  Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems. The
  level inclusions and the duality `Πₖᵖ = co-Σₖᵖ` are proved, not assumed.
  Level 0 is `DescriptiveComplexity.PTIME`, polynomial time, defined by the Horn
  fragment SO-Horn (below); the level-0 statements that would amount to
  closure under complement are the one thing the fragment does not give, and
  are restricted to levels `≥ 1`. Everything remains a definition or a
  theorem: the library declares **no axioms** (check with `#print axioms`).

## Polynomial time, by the Horn fragment

* `DescriptiveComplexity.SecondOrderHorn` – SO-Horn ([Grädel
  1992][gradel1992capturing]): existential second-order logic whose kernel is a
  conjunction of Horn clauses in the quantified relation variables, the
  fragment that captures polynomial time on ordered structures. The kernel is
  represented as *data* (`DescriptiveComplexity.HornProgram`, a list of clauses with a
  first-order guard over the ordered expansion, body atoms and an optional
  head), which is Grädel's clausal normal form and what a reduction consuming
  such a definition needs to read.
* `DescriptiveComplexity.SecondOrderHornPull` – the pullback of an SO-Horn definition
  through an interpretation *stays Horn*: the Horn condition constrains only
  the second-order atoms, and an interpretation rewrites the
  input-vocabulary ones, which live in the guard. This closure is what makes
  `DescriptiveComplexity.PTIME` (in `DescriptiveComplexity.Hierarchy`) a genuine complexity
  class, and hence level 0 of the hierarchy, *defined* by SO-Horn definability
  just as NP is defined by `Σ₁`-definability. HORN-SAT is PTIME-complete – hard
  by the Horn discharge, and a member by the Horn program that computes unit
  propagation along the order – which also yields the four inclusions of level
  0 into level 1, and with them the monotonicity of the hierarchy
  (`DescriptiveComplexity.sigmaP_mono`, `DescriptiveComplexity.piP_mono`): the padding
  step of `DescriptiveComplexity.Hierarchy` climbs only from level 1 up, its level-0
  step being the Horn discharge. See `DescriptiveComplexity.Problems.HornSat` for what
  is and is not claimed.

* `DescriptiveComplexity.Difference` – **the class DP**
  (`DescriptiveComplexity.DP`), the conjunctions of an NP condition and a coNP one
  ([Papadimitriou & Yannakakis 1984][papadimitriou1984complexity]), with
  `NP ⊆ DP` and `coNP ⊆ DP`. Closure under reductions is the interesting part:
  the two halves of a DP definition are individually *not* order-invariant, so
  an ordered reduction cannot be pulled back half by half in the usual way. The
  order is instead quantified in opposite directions on the two sides –
  existentially on the `Σ` half, universally on the `Π` half – whose conjunction
  is again the pullback, each half then handled by the sentence-level order
  elimination of `DescriptiveComplexity.SecondOrderOrdered`. The upper bounds
  `DP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` merge the two kernels into one alternation, in either block
  order. SAT-UNSAT, the canonical DP problem, is defined in
  `DescriptiveComplexity.Problems.SatUnsat` and proved DP-complete: *in* DP by
  projecting each of its two sides onto a plain CNF instance and inheriting
  definability from SAT, and DP-hard in
  `DescriptiveComplexity.Problems.SatUnsat.Hardness` by running the Cook–Levin
  discharge of the `Σ₁` half and of the complement of the `Π₁` half side by side
  into one paired instance.

* `DescriptiveComplexity.FixedPoint` – FO(LFP) ([Immerman
  1986][immerman1986relational]; [Vardi 1982][vardi1982complexity]), in the same
  clausal style: a rule system defining a least fixed point, plus an
  *unrestricted* first-order output sentence read at it. Because the output may
  negate fixed-point atoms, FO(LFP) definability is closed under complement by
  construction (`DescriptiveComplexity.LFPDefinable.compl`) – the one thing the Horn
  fragment cannot do head-on – and every SO-Horn definition transports into it
  (`DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable`).

* `DescriptiveComplexity.FixedPointHorn` – the converse translation, the hard half of
  Grädel's equivalence: every FO(LFP) definition compiles back into the Horn
  fragment, by deriving the *complement* of the fixed point stage by stage
  along the order and evaluating the output sentence clausewise
  (`DescriptiveComplexity.LFPDefinable.sigmaSOHornDefinable`). The two formalisms are
  therefore interchangeable
  (`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`), SO-Horn definability
  is closed under complement (`DescriptiveComplexity.SigmaSOHornDefinable.compl`), and
  level 0 of the hierarchy collapses: `PiP 0 = SigmaP 0`
  (`DescriptiveComplexity.piP_zero_eq`), polynomial time closed under complement. The
  order-walking machinery shared with the HORN-SAT program lives in
  `DescriptiveComplexity.OrderWalk`.

## Nondeterministic logarithmic space, by the Krom fragment

* `DescriptiveComplexity.SecondOrderKrom` – SO-Krom ([Grädel
  1992][gradel1992capturing]): the same clausal style with the *Krom* (2-CNF)
  restriction in place of the Horn one, at most two second-order literals per
  clause and of either sign (`DescriptiveComplexity.KromProgram`, whose literals carry
  a sign and sit in two `Option` slots, so unit and goal clauses need no
  special case). It captures nondeterministic logarithmic space on ordered
  structures. Neither fragment contains the other: Horn clauses may be wide,
  Krom clauses may have two positive literals – and the difference is exactly
  determinism, a Horn program having a least model where a 2-CNF has none.
* `DescriptiveComplexity.SecondOrderKromPull` – the pullback stays Krom, for the reason
  it stays Horn (the shape constrains second-order atoms; an interpretation
  rewrites input-vocabulary ones, which live in the guard), so
  `DescriptiveComplexity.NL` in `DescriptiveComplexity.LogSpace` is a genuine complexity
  class. The pieces shared with the Horn pullback (atoms, guard pullback, tag
  assignments) live in `DescriptiveComplexity.SecondOrder` and
  `DescriptiveComplexity.SecondOrderPull`.
* `DescriptiveComplexity.LogSpace` – the class `DescriptiveComplexity.NL`. Its inclusion
  in the classes above is *not* syntactic (a Krom kernel is not a Horn kernel)
  and goes through the complete problem: `DescriptiveComplexity.NL_subset_PTIME` and
  `DescriptiveComplexity.NL_subset_NP`, both downstream with 2SAT. That the class is
  closed under complement – `NL = coNL` – is *not* the definitional duality
  that gives `PiP k` from `SigmaP k` but Immerman–Szelepcsényi, proved in
  `DescriptiveComplexity.ImmermanSzelepcsenyi` (`DescriptiveComplexity.NL_eq_coNL`).
* `DescriptiveComplexity.TransitiveClosure` – FO(TC) ([Immerman
  1987][immerman1987languages]), the logic that captures NL on ordered
  structures, in the same kernel-as-data style: a `DescriptiveComplexity.TCSpec` is an
  arity, a finite *mode* component, a first-order transition formula on
  `k`-tuples per pair of modes and two endpoint formulas, with
  `Relation.ReflTransGen` supplying the closure. Modes are what tuples of
  elements cannot supply – a one-element universe has one tuple – and play the
  role tags play in an interpretation. It is the logic in which REACH is stated
  head-on (`DescriptiveComplexity.reach_tcDefinable`) and in which
  Immerman–Szelepcsényi is proved, the bridge that gives `REACH ∈ NL`, the
  clausal fragments defining only the complement.
* `DescriptiveComplexity.TwoCnf` – the criterion for 2-satisfiability ([Aspvall,
  Plass & Tarjan 1979][aspvall1979linear]) with no logic in it at all: over a
  finite type of variables, a 2-CNF is satisfiable iff no literal reaches its
  own negation and back in the implication graph. It is needed once for CNF
  structures (2SAT ∈ PTIME) and once for the atoms of a Krom program (turning a
  Krom definition into a transitive closure); the two differ only in what plays
  the part of a variable.
* `DescriptiveComplexity.KromImplication` and
  `DescriptiveComplexity.KromTransitiveClosure` – **the converse translation**: the
  complement of an SO-Krom definable problem is FO(TC) definable
  (`DescriptiveComplexity.TCDefinable.compl_of_sigmaSOKromDefinable`). A Krom program
  instantiated in a structure *is* a 2-CNF, whose variables are the atoms of
  its block at tuples of elements, so it is satisfiable exactly when no goal
  clause fires and no literal reaches its own negation and back
  (`DescriptiveComplexity.KromImpl.exists_holds_iff`); the second file expresses the
  implication graph as first-order transition formulas
  (`DescriptiveComplexity.KromTC.realize_edgeF`) and walks the cycle-witnessing graph
  of `DescriptiveComplexity.TwoCnf.carryReach_iff`, the start literal, the current one
  and the flag being the mode and the two atoms' arguments the two halves of
  the tuple. With the direction below it gives `co-NL(Krom) = NL(TC)`
  (`DescriptiveComplexity.mem_NL_iff_tcDefinable_compl`); `NL(Krom) = NL(TC)`, and
  with it `REACH ∈ NL`, needs the complementation of FO(TC) itself, which is
  `DescriptiveComplexity.TCDefinable.compl`.
* `DescriptiveComplexity.TransitiveClosureKrom` – the translation that *is* free:
  the complement of an FO(TC) definable problem is SO-Krom definable
  (`DescriptiveComplexity.SigmaSOKromDefinable.compl_of_tcDefinable`), hence in NL, by
  the program guessing the nodes from which an accepting node is reachable, one
  `k`-ary relation variable per mode. `DescriptiveComplexity.unreach_mem_NL` is its
  single-mode, arity-one instance, written out by hand as a worked example.
* `DescriptiveComplexity.Counting` and `DescriptiveComplexity.TransitiveClosureCompl` –
  **FO(TC) is closed under complement** (`DescriptiveComplexity.TCDefinable.compl`), by
  inductive counting. The machine is combinatorial, on an abstract finite
  linearly ordered node set: eight registers, each a node or a count read as a
  rank, and four nested loops – the stages, the outer scan, the inner scan and
  a certifying walk – that compute `|Rset (d+1)|` from `|Rset d|`, the count
  check leaving a guessed set of layer nodes no room to be too small. The
  first-order layer stores a register as one `k`-tuple beside a mode kept in
  the control, so a configuration *is* a mode with an `8k`-tuple, and compiles
  every atomic constraint of the machine into a formula once the modes are
  known – mode-level conditions ("the least mode", "this mode covers that
  one") being decided outside the formula.
* `DescriptiveComplexity.ImmermanSzelepcsenyi` – **`NL = coNL`**
  (`DescriptiveComplexity.NL_eq_coNL`), assembled from the complementation of FO(TC)
  and the two translations against the Krom fragment. It also gives what those
  translations alone could not: NL *is* FO(TC)
  (`DescriptiveComplexity.tcDefinable_iff_mem_NL`), the Krom fragment is closed under
  complement, and `REACH ∈ NL` (`DescriptiveComplexity.reach_mem_NL`).
* `DescriptiveComplexity.TransitiveClosureReach` – **REACH is NL-complete**
  (`DescriptiveComplexity.REACH_NL_complete`), the discharge of FO(TC) into its
  canonical problem. Unlike the clausal discharges, this one emits nothing: the
  graph of the walk of a `DescriptiveComplexity.TCSpec` already *is* a marked graph –
  a node is a mode with a `k`-tuple, which is exactly the universe
  `Tag × A^dim` of a tagged interpretation – so the three defining formulas are
  the specification's own, relabelled
  (`DescriptiveComplexity.reach_hard_of_tcDefinable`). No junk arises, so the
  reduction needs no relativization; the one adjustment is
  `DescriptiveComplexity.TCSpec.pad`, adding a spare mode so that the tag type is
  nonempty, since a reduction must map nonempty structures to nonempty ones.
  UNREACH is complete too (`DescriptiveComplexity.UNREACH_NL_complete`), by
  complementing that reduction – which is again `NL = coNL`, each fragment
  defining only one of the two problems head-on.
* `DescriptiveComplexity.TransitiveClosureDet` and
  `DescriptiveComplexity.TransitiveClosurePull` – FO(DTC), and closure of both
  reachability logics under reductions. Determinism is a *formula*, not a side
  condition: a `DescriptiveComplexity.TCSpec` is read through
  `DescriptiveComplexity.TCSpec.det`, which conjoins to each transition the statement
  that no other transition leaves the current node – a finite conjunction over
  the modes, the mode comparison being static. Every specification then denotes
  a deterministic walk and nothing has to be preserved by a pullback, which is
  what makes the closure argument syntactic. The pullback itself
  (`DescriptiveComplexity.TCSpec.comap`) walks the interpreted structure while
  writing everything on the base one: `k` tags ride along in the mode, the
  coordinates flatten to a `k · d`-tuple, and the resulting bijection of nodes
  carries steps to steps – whence determinism travels for free, "no competing
  successor" being invariant under a bijection.
* `DescriptiveComplexity.DetLogSpace` – the class `DescriptiveComplexity.LOGSPACE`
  (named in full, `L` being a vocabulary everywhere in this development),
  defined by FO(DTC) definability. It is the first class here defined by an
  operator-as-data logic rather than by the shape of a kernel: no fragment of
  ∃SO comparable to SO-Horn or SO-Krom is known for deterministic logarithmic
  space. `DescriptiveComplexity.LOGSPACE_subset_NL` is a determinized walk being a
  walk, followed by the FO(TC)/SO-Krom translation.
* `DescriptiveComplexity.Problems.ReachabilityDet` – **REACHd is LOGSPACE-complete**
  (`DescriptiveComplexity.REACHd_LOGSPACE_complete`). The outdegree bound of the
  textbook statement is imposed semantically rather than as a promise: the walk
  follows an arc only when it is the only arc out of its source
  (`DescriptiveComplexity.DetEdge`), so every marked graph is a legal instance and
  invariance is free. Membership is `DescriptiveComplexity.reachSpec` read through its
  determinization; hardness reuses the FO(TC) interpretation verbatim, the graph
  of a determinized walk being functional, so that its forced arcs are all of
  its arcs. Both halves are cheaper than REACH's, whose membership needs
  Immerman–Szelepcsényi – the fragment asymmetry that forces it does not arise
  for an operator-based logic.
* `DescriptiveComplexity.HeadAutomaton` – **the machine model of the
  logarithmic-space level**, and the containment "machine ⊆ logic" for it. The
  model is a *two-way `k`-head automaton over the structure*: a finite control,
  `k` heads each holding an element of the universe, **no work tape**; a step
  reads the truth values of a fixed finite list of **quantifier-free** tests of
  the head positions (the `test_qf` field is what keeps the model a machine
  rather than first-order logic in disguise) and moves each head to the least or
  greatest element, to another head, or to the immediate successor or
  predecessor of another head – a head at the last element moving right having
  no successor, so the transition is disabled, as in
  `DescriptiveComplexity.TMData`. It is deliberately *not* a one-way `DFA`/`NFA` over
  an alphabet: the input is a structure and not a word, so such a machine would
  have to be given a serialization, and one-way single-head machines recognize
  only regular languages – the two-wayness and the `k` heads *are* the
  logarithmic-space bound. A configuration is a control state with a `k`-tuple,
  which is exactly a `DescriptiveComplexity.TCSpec.Node`, so an automaton compiles
  into a specification whose modes are its states
  (`DescriptiveComplexity.HeadAutomaton.toSpec`), whence
  `DescriptiveComplexity.mem_NL_of_automaton` and, for a deterministic control,
  `DescriptiveComplexity.mem_LOGSPACE_of_automaton`.
* `DescriptiveComplexity.HeadProgram` – **the assembly language of those
  machines**: the same model with its transitions presented one at a time, each
  with its own quantifier-free guard and with two *exits*, so that machines can
  be pasted together. A fragment's specification is
  `DescriptiveComplexity.HeadProgram.Runs` – which exits are reachable, with which
  head positions – split into an exact soundness half and a completeness half
  that is up to the *scratch* heads, the ones a fragment may leave dirty.
  Everything is built with one combinator,
  `DescriptiveComplexity.HeadProgram.wireP`: a finite family of fragments, one per
  node of a control graph. `DescriptiveComplexity.HeadProgram.runs_wireP` reduces the
  runs of the assembly to a *walk in the control graph* whose steps are the runs
  of the fragments, which is what every correctness proof downstream argues
  about; its engine is
  `DescriptiveComplexity.HeadProgram.Embeds.reach_cases`, that a run which starts
  inside a fragment either is still inside it or has left it by one of its
  exits. Two compilations back to `DescriptiveComplexity.HeadAutomaton` enable either
  every transition whose guard holds or only the first, the latter being
  syntactically deterministic whatever the guards.
* `DescriptiveComplexity.HeadEval` – **a machine can decide any fixed first-order
  formula of its head positions** (`DescriptiveComplexity.HeadProgram.decides_evalP`),
  by structural recursion on the formula: atoms are guards, implication is a
  branch, and a quantifier is a *sweep* of two fresh heads – one walking the
  order from the least element, one parked at the greatest so that "the sweep is
  over" is the atom "these two heads are equal". Quantifiers are thus not read
  but walked, which is why quantifier-free guards cost nothing in expressive
  power, and the sweep is deterministic
  (`DescriptiveComplexity.HeadProgram.deterministic_evalP`).
* `DescriptiveComplexity.HeadCapture` – **the capture theorem for NL**
  (`DescriptiveComplexity.tcDefinable_iff_automaton`,
  `DescriptiveComplexity.mem_NL_iff_automaton`): every FO(TC) definable problem is
  recognized by a two-way multi-head automaton, so the machine model and the
  logic define the same class. The machine keeps the walk's current tuple on one
  block of heads and a candidate on another, holds the *mode* in its control –
  where it must be, a one-element universe having only one tuple – and loops:
  guess a source, evaluate the target formula, else guess a candidate, evaluate
  the transition formula, commit. Guessing (a head walked up the order for a
  nondeterministic number of steps) is the only nondeterminism. Soundness is an
  invariant carried along the control walk – the current tuple is a node
  reachable from a source – and completeness an induction along
  `DescriptiveComplexity.TCSpec.Reach`.
* `DescriptiveComplexity.HeadCaptureDet` – **the capture theorem for L**
  (`DescriptiveComplexity.dtcDefinable_iff_automaton`,
  `DescriptiveComplexity.mem_LOGSPACE_iff_automaton`): the same statement for FO(DTC)
  and *deterministic* machines. A deterministic machine may not guess, so it
  **searches** – the candidate tuple, the source tuple and the counter are each
  a block of heads walked by the odometer of `DescriptiveComplexity.HeadLex`
  (`lexNextP`, the lexicographic successor of a block, tested against a head
  parked at the greatest element, since maximality of one head is not a
  quantifier-free fact) – and it **counts**, so that a walk leading nowhere is
  abandoned rather than followed around its cycle for ever. The budget is
  `DescriptiveComplexity.WalkBudget`: a node reachable along a *functional* relation
  is reachable in fewer steps than the type has elements, and a counter in a
  finite linear order can tick as often as its rank leaves room. The two meet
  because the machine's counter – a mode in the control above a tuple on a block –
  *is* a finite linear order, whose covers are exactly its ticks and which has
  exactly as many values as the specification has nodes. Soundness is again an
  invariant along the control walk; completeness is the walk (an induction on the
  steps left, on the budget) inside the source enumeration (an induction
  downwards along the same order, the walk lemma supplying the return to the next
  source when one leads nowhere).
* `DescriptiveComplexity.Problems.ReachabilityDet.Complement` – **`L = coL`**
  (`DescriptiveComplexity.LOGSPACE_eq_coLOGSPACE`) and **UNREACHd is
  LOGSPACE-complete** (`DescriptiveComplexity.UNREACHd_LOGSPACE_complete`). Everything
  rests on one membership statement: the complement of REACHd is itself a
  deterministic walk, which *scans* – it tries each vertex as a source in the
  order of the structure, following forced arcs from it with a budget, and
  accepts once the candidates are exhausted. The budget is a third coordinate
  holding a vertex, read through `DescriptiveComplexity.orank`, and it replaces cycle
  detection: a walk that has not arrived after `|A| - 1` steps never will, since
  a minimal number of steps visits distinct vertices
  (`DescriptiveComplexity.exists_iterate_lt_card`). The scan quantifies the sources
  itself because acceptance quantifies the *start* node existentially while a
  complement needs them universally. Given that one problem, closure of the
  class under complement is free: a reduction complements along with its two
  problems, and REACHd is hard.
* `DescriptiveComplexity.Problems.TwoSat` – **2SAT is NL-complete**
  (`DescriptiveComplexity.TwoSAT_NL_complete`), the NL-level analogue of HORN-SAT for
  PTIME. A member by a Krom program that guesses the truth assignment and reads
  each clause through a covering pair of occurrences, enforcing the width
  promise and the absence of an empty clause by *guards* – first-order over the
  input, so a promise costs one goal clause; NL-hard by the Krom discharge,
  which emits one propositional 2-clause per clause of the program and per
  instantiation satisfying its guard, the output being width-two by
  construction. The scaffolding shared with the Horn discharge (dimension,
  tags, guard and atom-occurrence formulas over the canonical padding) is
  `DescriptiveComplexity.ClauseDischarge`. 2SAT is *also* in PTIME
  (`DescriptiveComplexity.twoSat_mem_PTIME`), by a Horn program guessing reachability
  in the implication graph of the 2-clauses and rejecting a variable that
  reaches its own negation and back – the classical criterion of [Aspvall,
  Plass & Tarjan 1979][aspvall1979linear], formalized in
  `DescriptiveComplexity.Problems.TwoSat.Implication`; this is what yields the two
  inclusions of NL.

## Polynomial space, by second-order transitive closure

* `DescriptiveComplexity.SecondOrderTransitiveClosure` – **SO(TC)**, the logic
  that captures polynomial space on ordered structures ([Immerman
  1999][immerman1999descriptive], ch. 10): a transitive closure taken not over
  tuples of *elements*, as in `DescriptiveComplexity.TransitiveClosure`, but over
  assignments of a block of *relation* variables. A
  `DescriptiveComplexity.SOTCSpec` bundles the block, a transition sentence over
  two copies of it – the current state and the next – and two endpoint
  sentences; reachability itself is `Relation.ReflTransGen`, so no fixpoint
  syntax, positivity condition or stage machinery is needed, exactly as for
  SO-Horn and SO-Krom. A state is `2^(n^a)` bits remembered along a walk of
  possibly exponentially many first-order steps, which is what PSPACE measures.
  No modes or element tuples ride alongside the state: a relation variable of
  arity `0` is a bit and one of arity `1` holding a singleton is an element
  register, so a block already carries whatever finite control a walk needs.
  Note that no fragment of *plain* second-order logic could play this role –
  SO is PH, so such a fragment would collapse the hierarchy; an iteration
  operator is unavoidable.
* `DescriptiveComplexity.SecondOrderTransitiveClosurePull` – **SO(TC)
  definability is closed under (ordered) FO reductions**
  (`DescriptiveComplexity.SOTCDefinable.of_orderedReduction`). Since a state is an
  assignment, the pullback is entirely the block pullback of
  `DescriptiveComplexity.SecondOrderPull`: the states of the pulled walk are the
  states of the original walk on the interpreted structure
  (`DescriptiveComplexity.SOBlock.pullAssignEquiv`), and each sentence is pulled
  back through the interpretation extended with the order and along the block –
  twice for the transition sentence.
* `DescriptiveComplexity.PSpace` – **the class PSPACE**
  (`DescriptiveComplexity.PSPACE`), a `DescriptiveComplexity.ComplexityClass` by that
  closure, with the complement operator `DescriptiveComplexity.coPSPACE` and the
  hardness discharge `DescriptiveComplexity.PSPACE_hard_of_sotcDefinable`. What is
  immediate is `DescriptiveComplexity.NP_subset_PSPACE`: an existential block is
  the walk that guesses its state and takes no step. Two things are *not* free –
  `PSPACE = coPSPACE`, since the complement of a walk is not a walk, and
  `PH ⊆ PSPACE`, since a `Σₖ` sentence is not a walk either – and both are proved
  downstream, in the two files below.
* `DescriptiveComplexity.PSpaceCompl` – **`PSPACE = coPSPACE`**
  (`DescriptiveComplexity.PSPACE_eq_coPSPACE`), the first of those two, proved
  downstream once QSAT is available: every SO(TC) definable problem reduces to
  QSAT (through SUCCINCT-REACH and Savitch's recursive doubling), complementing
  an ordered reduction is free, and the walk that decides QSAT is
  *deterministic* – it computes the value of the formula rather than searching
  for a witness – so reading its answer the other way round decides the
  complement (`DescriptiveComplexity.qsatCompl_sotcDefinable`). That is the
  logical shadow of the machine-theoretic reason: space-bounded computation can
  be made deterministic, and a deterministic decider is complemented by flipping
  its answer.
* `DescriptiveComplexity.PSpaceHierarchy` – **`PH ⊆ PSPACE`**
  (`DescriptiveComplexity.PH_subset_PSPACE`), the other one, by alternating that
  complement with the second closure property of SO(TC): a walk can *guess a
  block into its own state and never touch it again*
  (`DescriptiveComplexity.SOTCDefinable.exBlock`), so `∃R̄` in front of an SO(TC)
  condition is again one. The state of the guessing walk is an assignment of the
  merged block, and its transition sentence adds one universally quantified
  equivalence per relation variable of the guessed block, saying that component
  is unchanged; a whole walk therefore keeps it fixed, which is what makes
  accepting mean “the inner walk accepts under some assignment of it”. Peeling
  the quantifier prefix one block at a time, existential blocks by that closure
  and universal ones by complementing twice around it, gives every `Σₖ` and every
  `Πₖ` level (`DescriptiveComplexity.sigmaP_subset_PSPACE`,
  `DescriptiveComplexity.piP_subset_PSPACE`).
* `DescriptiveComplexity.Problems.Machine.Space` – **the machines of the class,
  membership half**: the same Turing machines that give NP and PTIME their
  bridges, with the step bound simply dropped
  (`DescriptiveComplexity.NTMAcceptSpace`,
  `DescriptiveComplexity.DTMAcceptSpace`). A run may then be arbitrarily long,
  but it never leaves the positions of the instance, so a configuration is an
  assignment of a three-variable block – the tape a binary relation, the state
  and the head unary marks – one step is a first-order condition on two
  consecutive assignments, and acceptance is their transitive closure. That is
  an SO(TC) specification, so both problems are in PSPACE
  (`DescriptiveComplexity.ntmAcceptSpace_mem_PSPACE`,
  `DescriptiveComplexity.dtmAcceptSpace_mem_PSPACE`), hence both reduce to QSAT
  (`DescriptiveComplexity.ntmAcceptSpace_reduces_to_qsat`) – the machine-side
  reading of Savitch's theorem. The converse, PSPACE-hardness of these problems,
  is not proved yet; it would complete the bridge and give `PSPACE = NPSPACE`.

## Value invention, towards the recursively enumerable

* `DescriptiveComplexity.SecondOrderNew` – `∃SO[new]`, existential second-order
  logic whose relation variables range over the universe *extended by finitely
  many invented values*, in the style of the object-creating query languages of
  ([Abiteboul–Hull–Vianu 1995][abiteboul1995foundations], ch. 18). Every other
  logic here bounds its certificate by the instance – a `Σ₁` sentence guesses
  relations over `A`, so the search space is exponential in `|A|` and the class
  sits inside NP. Value invention removes that bound and nothing else: the
  certificate is a finite extension `A ⊕ Fin m` with `m` unbounded, together
  with relations over it, checked by a fixed first-order kernel over the base
  vocabulary plus one predicate `old` marking the original elements. A witness
  is still finite and the kernel still decidable on it, so definability in this
  logic is a machine-model-free reading of *recursive enumerability*.
  `DescriptiveComplexity.SigmaSODefinable.toNew` is `Σ₁ ⊆ ∃SO[new]`, by
  inventing nothing.
* `DescriptiveComplexity.Relativize` – relativization of a formula to a unary
  predicate (`DescriptiveComplexity.relativizeTo`), with its correctness against
  the substructure the predicate defines. Its instance here is
  `DescriptiveComplexity.relOld`: a formula about the instance, read in the
  extended universe with its quantifiers restricted to the original elements,
  says what it says in the instance.
* `DescriptiveComplexity.SecondOrderNewPull` – **`∃SO[new]` definability is
  closed under FO reductions** (`DescriptiveComplexity.SigmaSONewDefinable.of_foReduction`).
  The construction is the one value invention makes cheap: with the *same*
  number of invented values, the target's extended universe `I.Map A ⊕ Fin m` is
  **definable inside** the source's `A ⊕ Fin m` – an interpreted point is a tag
  with `dim` original coordinates, an invented value is itself – so it is the
  universe of a relativized interpretation with tags `Tag ⊕ Unit` and dimension
  `dim + 1`, and the kernel is pulled back through it by the guarded pullback of
  `DescriptiveComplexity.RelComposition`. The spare coordinate is pinned to a
  guessed canonical element, which is what makes the construction survive
  `dim = 0`.
* `DescriptiveComplexity.SecondOrderNewOrdered` – the same closure under
  *ordered* FO reductions: the order is re-quantified inside the block, guarded
  by `DescriptiveComplexity.extLinearGuard`, which must be **relativized** –
  the order symbol of an extended structure relates original elements only, so
  an unrelativized linear-order guard would be unsatisfiable as soon as
  something is invented.
* `DescriptiveComplexity.RecursivelyEnumerable` – **the class RE**
  (`DescriptiveComplexity.RE`), a `DescriptiveComplexity.ComplexityClass` by
  those two closures, with `NP ⊆ RE` (`DescriptiveComplexity.NP_subset_RE`) and
  the complement operator `DescriptiveComplexity.coRE`. Nothing here relates RE
  and co-RE: `∃SO[new]` has no dual reading, and the separation that turns
  RE-hardness into undecidability is a machine-bridge statement. Its first
  complete problem is finite satisfiability, by Trakhtenbrot's theorem
  (`DescriptiveComplexity.Problems.FinSat`); PCP is planned in `ROADMAP.md`.
* `DescriptiveComplexity.Relationalize` – **removing function symbols from a
  source**: every `∃SO[new]`-definable problem admits a first-order reduction to
  an `∃SO[new]`-definable problem over a *relational* vocabulary
  (`DescriptiveComplexity.exists_relational_of_sigmaSONewDefinable`), the
  **atomic diagram language** `DescriptiveComplexity.atomLang` – one relation
  symbol of arity `n` per atomic formula of the source in `n` variables. A
  hardness proof whose target must *name* what a function does, rather than read
  it off the source through a defining formula, needs this. Two things make it
  work: the junk element by which an extended universe interprets a function on
  an invented argument may be *guessed*, since transporting the instance along a
  transposition moves it (`DescriptiveComplexity.sigmaSONewDefinable_junk`), and
  the kernel is then translated atom by atom *in place*, each atom becoming a
  short existential block holding the coerced context, the guessed junk and the
  values of the arguments, so that no de Bruijn index is ever shifted.

## Shared encodings

* `DescriptiveComplexity.SecondOrderMerge` – merging a second-order quantifier
  prefix into a single block (and back), so that constructions stated for one
  block can read the kernel of a `k`-block sentence.
* `DescriptiveComplexity.Padding` – canonically padded tuples: the convention
  by which a single interpretation dimension can carry tuples of different
  lengths (pad with a minimum of the input order), together with the FO(≤)
  formulas expressing it. This is the one place where the SAT-family
  reductions need their input to be ordered.
* `DescriptiveComplexity.OccurrenceOrder` and
  `DescriptiveComplexity.OccurrenceFormulas` – machinery for encoding
  occurrences of literals in clauses, shared across the SAT-family reductions.
* `DescriptiveComplexity.OrderWalk` – walking a finite linear order (or the
  lexicographic order on tuples) first-order: min/max/successor guards and
  their tuple analogues, induction along covers, and the rank of an element.
  Shared between the HORN-SAT program, the FO(LFP) → SO-Horn translation and
  the counting machine, whose registers are exactly ranks and tuple walks.
* `DescriptiveComplexity.Numbers` – unary and binary encodings of numbers as
  finite structures, for threshold and weight parameters of problems.
* `DescriptiveComplexity.Machines` – Turing machines as relations on a
  universe, with no vocabulary: configurations, steps, and acceptance within a
  budget counted in universe elements. The semantics the machine bridge reads
  off an instance.

## The problem catalog

`DescriptiveComplexity.Problems` holds one decision problem per file, each with
its vocabulary, FO reductions and a completeness theorem. Every class in the
table below is *defined* logically; each problem listed is proved **complete**
for it – both a member and hard under FO reductions. The catalog covers all of
Karp's 21 NP-complete problems. Each problem's own module page documents its
reduction and certificate in full.

| Complexity class | Logical characterization | Machine model | Problems proved complete |
| --- | --- | --- | --- |
| `LOGSPACE` (`L`) | FO(DTC): first-order logic with a deterministic transitive closure | deterministic two-way `k`-head automaton † | REACHd · UNREACHd |
| `NL` | SO-Krom: ∃SO with a Krom kernel, at most two second-order literals per clause; equivalently FO(TC), first-order logic with a transitive closure | two-way `k`-head automaton † | REACH · UNREACH · 2SAT |
| `PTIME` = `Σ₀ᵖ` = `Π₀ᵖ` | SO-Horn: ∃SO with a Horn kernel; equivalently FO(LFP), first-order logic with a least fixed point | deterministic polynomial-time Turing machine | HORN-SAT |
| `NP` = `Σ₁ᵖ` | ∃SO: existential second-order logic | nondeterministic polynomial-time Turing machine | **SAT-family:** SAT · 3SAT · NAE-SAT · NAE-3SAT · 1-in-SAT<br>**Coloring:** 3-Colorability · `k`-Colorability (`k ≥ 3`) · Chromatic Number · Clique Cover<br>**Cliques & subgraphs:** Clique · Independent Set · Vertex Cover · Subgraph Isomorphism<br>**Sets & hypergraphs:** Set Cover · Hitting Set · Set Packing · Exact Cover · Set Splitting · Dominating Set · 3-Dimensional Matching<br>**Graphs:** Feedback Vertex Set · Feedback Arc Set · Steiner Tree (node- & edge-weighted) · Max Cut · Hamilton Circuit (directed & undirected)<br>**Numbers (in binary):** Knapsack · Partition · 0-1 Integer Programming · Job Sequencing<br>**Machines:** acceptance by a nondeterministic polynomial-time Turing machine |
| `coNP` = `Π₁ᵖ` | ∀SO: universal second-order logic | — | TAUT · 3-DNF-TAUT · 3-UNSAT (and QBF∀ at one block) |
| `DP` | a `Σ₁` and a `Π₁` sentence conjoined | — | SAT-UNSAT |
| `Σₖᵖ` (`k ≥ 1`) | `Σₖ¹`: `k` alternating second-order quantifier blocks, existential first | — | `QBF k` – at `k = 1`, NP |
| `Πₖᵖ` (`k ≥ 1`) | `Πₖ¹`: `k` alternating second-order quantifier blocks, universal first | — | `QBF∀ k` – at `k = 1`, coNP |
| `PH` | full second-order logic | — | — |
| `PSPACE` | SO(TC): second-order logic with a transitive closure over assignments of a block of relation variables | polynomial-space Turing machine, deterministic or not ‡ | SUCCINCT-REACH · QSAT |
| `RE` | ∃SO[new]: ∃SO with value invention, the relation variables ranging over the universe extended by finitely many invented values | — | FINSAT |

† Capture theorems, both directions: `DescriptiveComplexity.mem_NL_iff_automaton`
for `NL`, and `DescriptiveComplexity.mem_LOGSPACE_iff_automaton` for `LOGSPACE`,
where the machine is required to be deterministic.

‡ Membership only, so far: `DescriptiveComplexity.ntmAcceptSpace_mem_PSPACE` and
`DescriptiveComplexity.dtmAcceptSpace_mem_PSPACE`. Hardness for those problems –
the capture, which would also give `PSPACE = NPSPACE` – is not proved yet, so
they are not listed as complete.

Headline results and cross-references:

* **Cook–Levin, machine-free** (`DescriptiveComplexity.SAT_NP_complete`;
  [Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal]): SAT is
  NP-complete by a Tseitin discharge, no machine model. 3-colorability is
  FO-interreducible with SAT in both directions.
* **The machine bridge**: machine acceptance
  (`DescriptiveComplexity.NTMAccept`) – does this nondeterministic Turing
  machine, carried as data by the instance, accept its input within a
  polynomial step budget (as many steps as there are tape positions)? – is
  NP-complete
  (`DescriptiveComplexity.ntmAccept_NP_complete`), so a problem is in the
  library's NP exactly when it ordered-FO-reduces to it
  (`DescriptiveComplexity.mem_NP_iff_le_ntmAccept`): the logically defined
  class *is* the machine one. The textbook Cook–Levin – machine acceptance
  reduces to SAT – is `DescriptiveComplexity.ntmAccept_reduces_to_sat`. One
  level down, the *deterministic* restriction
  (`DescriptiveComplexity.DTMAccept`, a functional transition table folded into
  the yes-instances) is PTIME-complete
  (`DescriptiveComplexity.dtmAccept_PTIME_complete`): membership because a
  deterministic run is a least fixed point, read through the formalized
  FO(LFP) → SO-Horn translation, and hardness by a unit-propagation machine
  built inside the HORN-SAT instance – so PTIME, too, is the machine class
  (`DescriptiveComplexity.mem_PTIME_iff_le_dtmAccept`), with the Grädel-side
  textbook discharge `DescriptiveComplexity.dtmAccept_reduces_to_hornSat`.
* **All of Karp's 21** ([Karp 1972][karp1972reducibility]): the SAT, clique,
  set, coloring, graph and number families above, closed by the two Hamilton
  circuit problems – a circuit read as a linear order of the universe, hard
  from Vertex Cover by Karp's twelve-vertex cover-testing gadget.
* **PTIME by the Horn fragment**: HORN-SAT is PTIME-complete
  (`DescriptiveComplexity.HORNSAT_PTIME_complete`) by the Horn discharge and a
  Horn program for unit propagation – the P-level analogue of Cook–Levin,
  equally machine-free. REACH/UNREACH is a second worked instance of the
  fragment, and a third one of the Krom fragment:
  `DescriptiveComplexity.unreach_mem_NL` defines UNREACH by a two-literal
  program guessing the vertices from which a marked target is reachable. In
  both fragments it is the *complement* that is definable head-on, clauses
  being able to close and to reject but not to force minimality; REACH escapes
  at the Horn level through FO(LFP), and at the Krom level through `NL = coNL`
  (`DescriptiveComplexity.reach_mem_NL`).
* **L by deterministic transitive closure**: REACHd – reachability along
  *forced* arcs – is complete for `DescriptiveComplexity.LOGSPACE`
  (`DescriptiveComplexity.REACHd_LOGSPACE_complete`), the class defined by FO(DTC).
  Determinism is carried by a formula rather than by a hypothesis, which is what
  lets the class be closed under reductions syntactically; and both halves of
  the completeness proof are the same observation read in opposite directions,
  the graph of a deterministic walk being a deterministic-reachability instance
  and conversely.
* **`L = coL`, cheaply** (`DescriptiveComplexity.LOGSPACE_eq_coLOGSPACE`):
  deterministic logarithmic space is closed under complement, and UNREACHd is
  complete for it. Where `NL = coNL` needs Immerman–Szelepcsényi's inductive
  counting, a *deterministic* walk has only one thing to do at each node, so
  failing to arrive is witnessed by walking until a budget runs out – and the
  budget is just a vertex, counted by its rank in the order.
* **NL by the Krom fragment and FO(TC)**: 2SAT is NL-complete
  (`DescriptiveComplexity.TwoSAT_NL_complete`) by the Krom discharge, and so is
  REACH (`DescriptiveComplexity.REACH_NL_complete`), the canonical NL-complete
  problem ([Jones 1975][jones1975space]), whose hardness is the FO(TC)
  discharge – the interpretation *is* the graph of the walk of a
  `DescriptiveComplexity.TCSpec`. Both halves of REACH's completeness pass
  through Immerman–Szelepcsényi: membership because a clausal fragment defines
  only non-reachability, hardness because SO-Krom definability has to be turned
  into an FO(TC) definition of the problem itself. UNREACH is then complete as
  well (`DescriptiveComplexity.UNREACH_NL_complete`), the two problems trading
  which half is the easy one.
* **The logarithmic-space machine model, captured**
  (`DescriptiveComplexity.mem_NL_iff_automaton`,
  `DescriptiveComplexity.mem_LOGSPACE_iff_automaton`): a problem is in `NL` exactly
  when a two-way `k`-head automaton over the structure recognizes it, and in
  `LOGSPACE` exactly when a *deterministic* one does. There is no string
  encoding anywhere: the machine reads the structure through quantifier-free
  tests of its heads, and `k` head positions are the `k · log n` bits of
  storage. The logic-to-machine half is a compiler – quantifiers are *walked*
  by a two-head sweep rather than read – and its deterministic version is the
  same machine with search in place of guessing and a step budget in place of
  an oracle: the counter is a mode above a tuple, one finite linear order with
  exactly as many values as the specification has nodes.
* **Above NP**: TAUT (DNF tautology) is coNP-complete by complementing the
  Cook–Levin discharge, and its width-three restriction 3-DNF-TAUT
  (`DescriptiveComplexity.ThreeDnfTAUT_coNP_complete`) follows the same route
  through the CNF-side reading 3-UNSAT, which is where the width promise of the
  clause-splitting reduction is still in hand (`3SATᶜ` would not do: it is a
  disjunction, since 3SAT folds the width bound into its yes-instances);
  `QBF k`, quantified Boolean formulas with `k`
  alternating blocks, is complete for the `k`-th level of the hierarchy
  ([Stockmeyer 1976][stockmeyer1976polynomial]; [Wrathall
  1976][wrathall1976complete]) by the same Tseitin discharge carrying block
  marks.
* **At PSPACE**: SUCCINCT-REACH (`DescriptiveComplexity.Problems.SuccinctReach`)
  – reachability in a transition system whose states are the truth assignments
  to marked *state variables* and whose transitions, sources and targets are
  described by three CNF formulas rather than listed – is PSPACE-complete
  (`DescriptiveComplexity.SUCCINCTREACH_PSPACE_complete`). The two halves are the
  two readings of one identification, and they mirror the Cook–Levin pair
  exactly. Membership is cheap for the structural reason that makes every
  reachability logic's image cheap: the problem *is* the syntactic image of
  SO(TC), so the specification is a transcription. Its four monadic relation
  variables are the state being walked plus the three existential witnesses –
  one per clause group – that a transitive closure cannot quantify on its own;
  two endpoint witnesses rather than one, because a walk of length zero must
  meet both endpoint conditions at the same state. Hardness Tseitin-encodes the
  three sentences of a `DescriptiveComplexity.SOTCSpec` into the three clause
  groups, reusing the semantic core of the SAT discharge unchanged
  (`DescriptiveComplexity.Tseitin.satCond_iff_gates`); what is new is that the three
  encodings are taken over the *doubled* block
  (`DescriptiveComplexity.SOBlock.double`), so that the propositional variables for
  the atoms of the block are the same elements in all three – they are exactly
  the state variables, their second copies the next-state copies. A state of
  the interpreted system is therefore an assignment of the block and nothing
  else, and the two walks correspond step by step, with no initialization or
  finalization steps to peel off.
* **At PSPACE, again**: QSAT (`DescriptiveComplexity.Problems.Qsat`) – is a fully
  quantified Boolean formula true, when the quantifier prefix is *part of the
  instance* rather than fixed by the problem? – is PSPACE-complete
  (`DescriptiveComplexity.QSAT_PSPACE_complete`; [Stockmeyer–Meyer
  1973][stockmeyer1973word]). That an instance carries its own prefix is exactly
  the step from the polynomial hierarchy to PSPACE, and it is what the semantics
  has to pay for: a position is a set of already-quantified variables together
  with a valuation, the next variable to play is the least unplayed one, and the
  game value is an inductive predicate rather than a recursion, so that it is
  defined on infinite structures too. Membership walks that game tree
  depth-first, short-circuiting so that no accumulator is needed – four relation
  variables and four transitions. Hardness is Savitch's recursive doubling
  ([Savitch 1970][savitch1970relationships]) written as an interpretation:
  reachability in at most `2 ^ m` steps, `m` the number of state variables of a
  SUCCINCT-REACH instance, unfolds into a prefix of `m` blocks `∃Z_ℓ ∀b_ℓ
  ∃(U_ℓ, V_ℓ)`, the universal bit choosing which half of the level is checked and
  a *fresh copy* of the pair receiving it – which is what keeps the matrix
  clausal, so that no Tseitin encoding is needed anywhere. Two things make the
  proof go through: the vertices of the walk are states only up to their
  restriction to the state variables, which is why `DescriptiveComplexity.Savitch`
  is stated for a relation classified into a finite type; and the prefix is a
  lexicographic comparison of static keys, so that its blocks are the sets of
  variables sharing the first three components of a key and the peeling lemmas of
  `DescriptiveComplexity.Problems.Qsat.Blocks` apply level by level.
* **Between NP and the second level**: SAT-UNSAT – is the first of two CNF
  formulas satisfiable and the second not? – is DP-complete
  (`DescriptiveComplexity.SATUNSAT_DP_complete`; [Papadimitriou & Yannakakis
  1984][papadimitriou1984complexity]). Membership is the shape of the problem
  itself; hardness runs *two* Cook–Levin discharges, one for the `Σ₁` half and
  one for the complement of the `Π₁` half, side by side into a single paired
  instance. Pairing forces a common universe, so each side's tuples are pinned
  to canonically padded ones: with the spare coordinates left free, every clause
  and variable would acquire copies and an unsatisfiable formula could blow up
  into a satisfiable one.

* **At RE**: FINSAT (`DescriptiveComplexity.Problems.FinSat`) – does a
  first-order sentence, encoded as a finite structure, have a *finite* model? –
  is RE-complete (`DescriptiveComplexity.FINSAT_RE_complete`), which is
  Trakhtenbrot's theorem in the logical form. FINSAT is the syntactic image of
  `∃SO[new]` exactly as SAT is that of `Σ₁`: a certificate is “a finite
  extension of the universe plus relations on it satisfying a fixed first-order
  kernel”, a finite model is “a finite universe plus relations on it satisfying
  a given first-order sentence”, and the reduction translates the first into the
  second. Two decisions carry the encoding: the instance is a parse DAG **in
  negation normal form**, so that the value of a node is monotone in its
  children and satisfaction is a least fixed point rather than a well-founded
  recursion on a decoded parse tree – there is no decoding, the symbols of the
  encoded sentence being elements of the instance – and its ∧/∨ nodes are
  **n-ary**, so that the unbounded conjunctions of the reduction are single
  nodes. The encoded sentence carries its own quantifiers, so the reduction
  needs no context tuples, and its vocabulary is *only* the relation variables of
  the block: `old` and the symbols of the source are translated away into
  disjunctions indexed by the tuples the interpretation's own formulas select.
  Function symbols in the source are removed beforehand, by
  `DescriptiveComplexity.Relationalize`.

## Worked examples

* `DescriptiveComplexity.Examples` – tutorial-style, domain-specific
  walkthroughs of the full recipe (vocabulary → semantics → invariance →
  membership → hardness → completeness). Currently Boolean conjunctive
  queries – evaluation and containment, both NP-complete via Chandra–Merlin
  ([Chandra & Merlin 1977][chandra1977optimal]).
-/
