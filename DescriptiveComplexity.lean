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
import DescriptiveComplexity.Encoding.BinarySubsetSum
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
import DescriptiveComplexity.InductiveCounting
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
import DescriptiveComplexity.HeadArith
import DescriptiveComplexity.HeadEvalArith
import DescriptiveComplexity.Iterate
import DescriptiveComplexity.FixedPoint
import DescriptiveComplexity.OrderWalk
import DescriptiveComplexity.FixedPointHorn
import DescriptiveComplexity.FixedPointStep
import DescriptiveComplexity.SecondOrderBlockHom
import DescriptiveComplexity.FixedPointInflationary
import DescriptiveComplexity.FixedPointInflationaryLFP
import DescriptiveComplexity.FixedPointPartial
import DescriptiveComplexity.Hierarchy
import DescriptiveComplexity.SecondOrderTransitiveClosure
import DescriptiveComplexity.SecondOrderTransitiveClosurePull
import DescriptiveComplexity.PSpace
import DescriptiveComplexity.SecondOrderTransitiveClosureFree
import DescriptiveComplexity.FixedPointPartialSpace
import DescriptiveComplexity.FixedPointStepRel
import DescriptiveComplexity.FixedPointParam
import DescriptiveComplexity.FixedPointPartialMachine
import DescriptiveComplexity.AbiteboulVianuOrdered
import DescriptiveComplexity.Invariant.Pebble
import DescriptiveComplexity.Invariant.EquivK
import DescriptiveComplexity.Invariant.Stages
import DescriptiveComplexity.Invariant.OrderedPebble
import DescriptiveComplexity.Invariant.Structure
import DescriptiveComplexity.Invariant.Simulation
import DescriptiveComplexity.Invariant.OrderDef
import DescriptiveComplexity.Invariant.Backward
import DescriptiveComplexity.Invariant.Bare
import DescriptiveComplexity.Invariant.TwoPebble
import DescriptiveComplexity.Invariant.TwoInvariance
import DescriptiveComplexity.Invariant.TwoStages
import DescriptiveComplexity.FirstOrderDefinable
import DescriptiveComplexity.FirstOrderPull
import DescriptiveComplexity.Arithmetic
import DescriptiveComplexity.ArithmeticDefinable
import DescriptiveComplexity.ArithmeticFixedPoint
import DescriptiveComplexity.LogTime.Definable
import DescriptiveComplexity.LogTime.Bits
import DescriptiveComplexity.LogTime.Machine
import DescriptiveComplexity.LogTime.Simulate
import DescriptiveComplexity.LogTime.Arith
import DescriptiveComplexity.LogTime
import DescriptiveComplexity.Games.Ehrenfeucht
import DescriptiveComplexity.Games.Bare
import DescriptiveComplexity.Games.Distance
import DescriptiveComplexity.Games.LinearOrder
import DescriptiveComplexity.TransitiveClosureFO
import DescriptiveComplexity.FixedPointOrderTransfer
import DescriptiveComplexity.FixedPointStratify
import DescriptiveComplexity.AbiteboulVianu
import DescriptiveComplexity.PSpaceCompl
import DescriptiveComplexity.PSpaceHierarchy
import DescriptiveComplexity.Exponential
import DescriptiveComplexity.Difference
import DescriptiveComplexity.Padding
import DescriptiveComplexity.OccurrenceOrder
import DescriptiveComplexity.OccurrenceFormulas
import DescriptiveComplexity.OccurrenceSlack
import DescriptiveComplexity.OccurrenceVar
import DescriptiveComplexity.Numbers
import DescriptiveComplexity.Machines
import DescriptiveComplexity.IsoGadget
import DescriptiveComplexity.TwoCopies
import DescriptiveComplexity.GadgetDouble
import DescriptiveComplexity.Degree
import DescriptiveComplexity.Problems
import DescriptiveComplexity.ClassDegrees
import DescriptiveComplexity.Computability
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
strength of a Turing machine: they are *first-order expressible*. Classically,
an FO reduction is computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, so exhibiting one is
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
  is an isomorphism-invariant property of finite structures of a *relational*
  language (invariance is baked into the notion, as is standard in descriptive
  complexity; so is relationality, via an `IsRelational` instance argument –
  the standing convention of the field, so every class equality below is a
  statement about relational problems). A
  `DescriptiveComplexity.FOInterpretation` is a tagged,
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
  `DescriptiveComplexity.Encoding.UnaryBlowup`).
* `DescriptiveComplexity.Encoding.BinarySubsetSum` – the positive contrast,
  worked out in full and in both directions. The honest binary encoding of a
  list of weights and a target (`DescriptiveComplexity.binarySubsetSumEncoding`),
  its decoding lemmas and `DescriptiveComplexity.binarySubsetSumEncoding_faithful`
  make `DescriptiveComplexity.knapsack_NP_complete` a statement about concrete
  lists of binary-written numbers; `DescriptiveComplexity.bwDecoding` reads
  *hardness* back the same way, and needs no well-formedness condition, a
  structure whose order is not linear being a definite no-instance. Both rest
  on `DescriptiveComplexity.hasSubsetSum_iff_index`, which reads the problem
  along any injective indexing of the items, and on the
  `DescriptiveComplexity.selection_toIndex`/`selection_ofIndex` pair that any
  other problem quantifying over selections of items reuses.
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
* `DescriptiveComplexity.Degree` – completeness *without a class*: the downward
  closure `DescriptiveComplexity.ComplexityClass.below Q₀` of a fixed problem
  under ordered FO reductions is itself a `ComplexityClass`, so
  `(below Q₀).Complete P` is literally “`P` is `Q₀`-complete”, with no logic
  anywhere – the notion behind “GI-complete”
  (`DescriptiveComplexity.GI`, the degree of `DescriptiveComplexity.GraphIso`).
  Hardness needs no new proof: `DescriptiveComplexity.CofinalHard` is already
  parameterized by an arbitrary membership predicate. Completeness for a degree
  is mutual reducibility
  (`DescriptiveComplexity.ComplexityClass.complete_below_iff`), and the degree
  depends only on the degree
  (`DescriptiveComplexity.ComplexityClass.below_congr`). The construction is
  checked against the classes that have complete problems, in
  `DescriptiveComplexity.ClassDegrees`: `NP = below SAT`,
  `coNP = below TAUT`, `PTIME = below HORN-SAT`, `NL = below 2SAT` and
  `RE = below FINSAT` (`DescriptiveComplexity.NP_eq_below_sat` and siblings),
  so “SAT-hardness is NP-hardness” is a lemma rather than folklore.

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
  (`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`), which read against
  the definition of the class is **Immerman–Vardi**, `PTIME = FO(≤, LFP)`
  (`DescriptiveComplexity.lfpDefinable_iff_mem_PTIME`); SO-Horn definability
  is closed under complement (`DescriptiveComplexity.SigmaSOHornDefinable.compl`), and
  level 0 of the hierarchy collapses: `PiP 0 = SigmaP 0`
  (`DescriptiveComplexity.piP_zero_eq`), polynomial time closed under complement. The
  order-walking machinery shared with the HORN-SAT program lives in
  `DescriptiveComplexity.OrderWalk`.

## The inflationary and partial fixed points

* `DescriptiveComplexity.FixedPointStep` – **one iteration skeleton for
  FO(IFP) and FO(PFP)** (`DescriptiveComplexity.StepDef`): a block of relation
  variables, one unrestricted first-order step formula per variable, an output
  sentence. The two logics differ only in what a step does with the previous
  stage – accumulate into it or replace it – so the stages, their
  stabilization on finite structures (through the orbit pigeonholes of
  `DescriptiveComplexity.Iterate`, a file free of library concepts), their
  transport along isomorphisms and their pullback through an interpretation
  are all built once, on `DescriptiveComplexity.StepDef.next` alone.
* `DescriptiveComplexity.SecondOrderBlockHom` – **morphisms of blocks**: an
  arity-preserving map of relation variables induces a morphism of the
  blocks' vocabularies, along which sentences transport
  (`DescriptiveComplexity.SOBlock.realize_homSentence`) – the bookkeeping for
  reading a formula written for one block inside a larger block containing a
  copy of it, which the translations between the fixed-point logics need.
* `DescriptiveComplexity.FixedPointInflationary` – **FO(IFP)**
  ([Gurevich–Shelah 1986][gurevich1986fixed]; [Abiteboul–Vianu
  1989][abiteboul1989fixpoint]): iterate inflationarily, read the output at
  the limit. Ordered (`DescriptiveComplexity.IFPDefinable`) and order-free
  (`DescriptiveComplexity.IFPDefinableFree`) definability are kept apart – for
  the fixed-point logics, unlike for SO(TC), the two must differ or the
  Abiteboul–Vianu theorem would be trivial. Closed under complement by
  construction and under (ordered) reductions; FO(LFP) embeds by reading a
  rule system as one simultaneous step
  (`DescriptiveComplexity.LFPDefinable.ifpDefinable`), which needs no
  positivity because inflation supplies the monotonicity.
* `DescriptiveComplexity.FixedPointInflationaryLFP` – **FO(≤, IFP) = FO(LFP)**
  (`DescriptiveComplexity.ifpDefinable_iff_lfpDefinable`), whence the capture
  theorem **FO(≤, IFP) = PTIME**
  (`DescriptiveComplexity.ifpDefinable_iff_mem_PTIME`): an inflationary
  definition compiles back into FO(LFP) by walking the stages
  (`DescriptiveComplexity.FixedPointHorn`'s stage apparatus) with a *dual*
  positive evaluator deriving truth and falsity of the step formulas'
  subformulas per stage – inflation is what makes the complement of a stage
  advance positively, which is precisely why PFP admits no such translation
  and goes to SO(TC) instead. The output sentence survives unchanged modulo
  the block injection, which is why the target is FO(LFP) and not SO-Horn.
* `DescriptiveComplexity.FixedPointPartial` – **FO(PFP)** ([Abiteboul–Vianu
  1989][abiteboul1989fixpoint]): iterate by replacement, read the output at
  the first stable stage – requiring convergence, a divergence convention
  chosen deliberately and compared precisely with the textbook one
  (`DescriptiveComplexity.StepDef.realize_pfpValue_iff`). FO(IFP) is contained
  in it by disjoining each variable's own atom onto its step
  (`DescriptiveComplexity.StepDef.inflate`) – the easy inclusion of
  Abiteboul–Vianu, in both the ordered and the order-free form. The PSPACE
  capture lives with the other PSPACE files, below.
* `DescriptiveComplexity.Invariant.Pebble`,
  `DescriptiveComplexity.Invariant.EquivK`,
  `DescriptiveComplexity.Invariant.Stages` – **the `≡ᵏ`-invariant layer**:
  the `k`-pebble refinement over an abstract initial relation
  (`DescriptiveComplexity.EquivK`, a greatest fixed point with its coinduction
  principle `DescriptiveComplexity.le_equivK`, expansion lemma
  `DescriptiveComplexity.equivK_inf_eq` and pair-substructure closure
  `DescriptiveComplexity.equivK_of_pairSub`), its instantiation at agreement
  on the atomic type over a relational structure – relative to a family of
  relation symbols, since a definition only mentions finitely many
  (`DescriptiveComplexity.StepDef.exists_usesRels`) – the `k`-variable
  invariance lemma (`DescriptiveComplexity.realize_equivK` – a formula with
  enough room for its quantifier depth cannot separate `≡ᵏ`-equivalent
  tuples; no syntactic `k`-variable fragment is ever defined), and the
  `≡ᵏ`-invariance of every inflationary and partial stage of a `StepDef`
  within its variable budget
  (`DescriptiveComplexity.StepDef.inflLimit_invariant`,
  `DescriptiveComplexity.StepDef.partStage_invariant`).
* `DescriptiveComplexity.Invariant.OrderedPebble`,
  `DescriptiveComplexity.Invariant.OrderDef` – **the canonical order on
  `≡ᵏ`-classes**: the ordered pebble refinement, a strict order on `k`-tuples
  growing as the classes split, whose incomparability is stage by stage the
  pebble refinement (`DescriptiveComplexity.ordStage_invariant`) and at the
  limit `≡ᵏ` (`DescriptiveComplexity.incompRel_ordK_eq`) – a linear order on
  the classes, *inflationary by construction*, so computed by one relation
  variable of a simultaneous induction (`DescriptiveComplexity.ordStepDef`,
  with `DescriptiveComplexity.inflStage_ordStepDef` matching the two
  round for round) and canonical because inflationary stages transport along
  isomorphisms.
* `DescriptiveComplexity.Invariant.Structure`,
  `DescriptiveComplexity.Invariant.Simulation`,
  `DescriptiveComplexity.Invariant.Backward` – **the invariant structure
  `Iᵏ A`** (`DescriptiveComplexity.InvMap`: the `≡ᵏ`-classes of `k`-tuples,
  with atomic-type bits, substitution and rearrangement relations, and the
  linear order induced by the canonical order,
  `DescriptiveComplexity.invLinearOrder`) **and the two-way simulation**: the
  pebble compiler (`DescriptiveComplexity.pebbleCompile`) runs a `k`-variable
  induction over `A` on the classes –
  `DescriptiveComplexity.StepDef.pfpHolds_invStepDef`, every quantifier
  spending a pebble along a substitution relation – and the class compiler
  (`DescriptiveComplexity.backCompile`) runs an induction over the *ordered*
  invariant vocabulary back on `A`, each class variable becoming `k` element
  variables and the order read off the (frozen) order variable
  (`DescriptiveComplexity.StepDef.ifpHolds_backStepDef`).
* `DescriptiveComplexity.FixedPointStratify` – **stratification**: nested
  inflationary inductions are one induction
  (`DescriptiveComplexity.StepDef.ifpHolds_stratify`) – the second stratum,
  a `StepDef` over the base vocabulary *expanded by the first stratum's
  block*, is gated on an arity-`0` variable derived exactly when the first
  stratum's step formulas add nothing, so it replays its own stages over the
  frozen limit.
* `DescriptiveComplexity.FixedPointOrderTransfer` – **order relativization**:
  FO(≤, IFP)/FO(≤, PFP) definability of `P` is order-free definability of
  `DescriptiveComplexity.DecisionProblem.withOrder P` («the order symbol is a
  linear order, and `P` holds on the reduct») over the ordered expansion, and
  order-free definability implies ordered definability
  (`DescriptiveComplexity.StepDef.liftOrder`).

## Inexpressibility: Ehrenfeucht–Fraïssé games

The one part of the library that proves things logic *cannot* do, with no
complexity-theoretic assumption anywhere – the payoff a machine-first
development has no counterpart for.

* `DescriptiveComplexity.FirstOrderDefinable` – plain first-order
  definability of a decision problem, order-free
  (`DescriptiveComplexity.FODefinableFree`) and order-invariant
  (`DescriptiveComplexity.FODefinable`), the bottom of every ladder above and
  the notion these results refute.
* `DescriptiveComplexity.Games.Ehrenfeucht` – **the Ehrenfeucht–Fraïssé
  game** ([Ehrenfeucht 1961][ehrenfeucht1961application]) between two
  structures: legal positions (`DescriptiveComplexity.PartialIso`, agreement
  on the atomic type read across two structures), the graded refinement
  `DescriptiveComplexity.efStage` – whose rounds *append* a coordinate over
  two structures, which is why it is not an instance of the `≡ᵏ` pebble
  skeleton of `DescriptiveComplexity.Invariant.Pebble` – and **the
  methodology lemma** (`DescriptiveComplexity.realize_sentence_of_efEquiv`):
  `n`-round equivalent structures satisfy the same sentences of quantifier
  rank at most `n`, the measure being the `DescriptiveComplexity.qdepth`
  shared with the invariant layer. Everything below is a contrapositive of it.
* `DescriptiveComplexity.Games.Bare` – the strategy on **bare sets**: two
  sets with at least `n` elements each are `n`-round equivalent
  (`DescriptiveComplexity.efEquiv_bare`), so an order-free first-order
  definable property of a bare set is constant beyond a threshold
  (`DescriptiveComplexity.exists_card_bound_of_foDefinableFree`) – first-order
  logic counts up to its quantifier rank and no further.
* `DescriptiveComplexity.Games.Distance`,
  `DescriptiveComplexity.Games.LinearOrder` – **Ehrenfeucht's theorem on
  linear orders**: two finite linear orders with at least `2 ^ n` elements
  each are `n`-round equivalent (`DescriptiveComplexity.efEquiv_linearOrder`).
  The duplicator's invariant is one equation per pair of points – equal
  distances *up to truncation at* `2 ^ n` (`DescriptiveComplexity.truncAt`),
  with the two ends of the order joined to the position as sentinels so that
  distances to them are distances like any other – and a round is one
  application of the answer lemma `DescriptiveComplexity.exists_answer`, where
  the budget halves: copy the distance to the nearer neighbour, or, when both
  are far, land in the middle of a gap the invariant makes twice as wide on
  the other side.
* `DescriptiveComplexity.Invariant.Bare` – **the order no induction defines**:
  over the empty vocabulary `≡ᵏ` is the equality pattern
  (`DescriptiveComplexity.equivK_bare`, the pebble twin of
  `DescriptiveComplexity.efStage_bare`), so a transposition of the universe
  leaves it alone and every binary variable of an order-free inflationary
  limit is symmetric – whence
  `DescriptiveComplexity.not_isLinearOrder_inflLimit`: **no order-free
  `StepDef` defines a linear order on a bare set**. This is the
  order-invariance of the definability notions of this library as a theorem:
  the order they are handed is not a convenience but something no
  isomorphism-invariant logic can build. It is a statement about a defined
  *relation*; the class-level one needs the two-structure game below, since
  `≡ᵏ` relates tuples inside one structure.
* `DescriptiveComplexity.Invariant.TwoPebble`,
  `DescriptiveComplexity.Invariant.TwoInvariance`,
  `DescriptiveComplexity.Invariant.TwoStages` – **the `k`-pebble game between
  two structures**, the pebble counterpart of the round game above and the
  layer a *Boolean* query needs: the same chain, coinduction and stabilization
  with the two sides in different types (`DescriptiveComplexity.EquivK₂`), the
  `k`-variable invariance lemma across the pair
  (`DescriptiveComplexity.realize_equivK₂`), the collapse on bare sets
  (`DescriptiveComplexity.equivK₂_bare`: `k` pebbles cannot count past `k`,
  whatever the two sizes), and the transfer of an inflationary induction stage
  by stage (`DescriptiveComplexity.StepDef.inflStage_invariant₂`), so that its
  output sentence cannot separate the two structures
  (`DescriptiveComplexity.StepDef.ifpHolds_equivK₂`).
* `DescriptiveComplexity.Problems.Even` – **EVEN is not first-order
  definable** (`DescriptiveComplexity.even_not_foDefinableFree`), and **not
  even order-invariantly so** (`DescriptiveComplexity.even_not_foDefinable`):
  over the empty vocabulary, deciding the parity of the universe is beyond
  first-order logic however it is allowed to use a linear order. It is a
  single walk along that order, though – step to the successor, flip a bit –
  so it *is* FO(≤, TC) definable (`DescriptiveComplexity.even_tcDefinable`),
  hence in `DescriptiveComplexity.NL` (`DescriptiveComplexity.even_mem_NL`).
  Together with the trivial inclusion
  (`DescriptiveComplexity.FODefinable.tcDefinable`, in
  `DescriptiveComplexity.TransitiveClosureFO`: a sentence is the walk that
  takes no step – and a walk with no step is deterministic for want of a
  competitor, so the same construction gives
  `DescriptiveComplexity.FODefinable.dtcDefinable`, the `FO(≤) ⊆ L` end of the
  chain below) that is **`FO ⊊ FO(TC)`**, unconditionally
  (`DescriptiveComplexity.exists_tcDefinable_not_foDefinable`) – a strict
  inclusion proved outright, where every other separation in this library is
  conditional. The same problem separates the *arithmetic* logic from the bare
  order, in the other direction: EVEN **is** AC⁰ definable
  (`DescriptiveComplexity.even_ac0Definable`), the greatest element having rank
  `Nat.card A - 1`, whence **`FO(≤) ⊊ AC⁰`**
  (`DescriptiveComplexity.exists_ac0Definable_not_foDefinable`). That is the
  parity of the *universe*, i.e. of the input's length; the parity of a marked
  *subset* is PARITY, the problem outside AC⁰, about which nothing here is
  claimed – no AC⁰ lower bound is proved in this library. EVEN also settles the
  *unordered* fixed-point question:
  `DescriptiveComplexity.even_not_ifpDefinableFree`, whence
  `DescriptiveComplexity.exists_mem_PTIME_not_ifpDefinableFree` – **order-free
  FO(IFP) does not capture PTIME**, against
  `DescriptiveComplexity.lfpDefinable_iff_mem_PTIME`, which says it does over
  ordered structures. The order in every capture theorem here is doing real
  work.
* `DescriptiveComplexity.Problems.Parity` – **PARITY**, the parity of a *marked
  subset* rather than of the universe: the problem the AC⁰ lower bound is about,
  in the catalog so that the distinction from EVEN is a definition and not a
  warning. It is **in LOGSPACE** (`DescriptiveComplexity.parity_mem_LOGSPACE`) by
  one deterministic walk – carry a bit, flip it at each marked element, a walk
  functional on the nose so that determinizing is free – and **not first-order
  definable** (`DescriptiveComplexity.parity_not_foDefinable`), EVEN being the
  instance where everything is marked
  (`DescriptiveComplexity.even_fo_reduction_parity`). With
  `DescriptiveComplexity.even_ac0Definable` and
  `DescriptiveComplexity.ac0Definable_mem_PTIME` that is three sides of
  `AC⁰ ⊊ LOGSPACE`; the fourth, PARITY ∉ AC⁰, is the switching lemma
  ([Ajtai 1983][ajtai1983sigma11]; [Furst, Saxe & Sipser 1984][furst1984parity];
  [Håstad 1986][hastad1986almost]) and is not proved here – this library proves
  **no** AC⁰ lower bound.

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
* `DescriptiveComplexity.InductiveCounting` and `DescriptiveComplexity.TransitiveClosureCompl` –
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
* `DescriptiveComplexity.Problems.Game` – **GAME, alternating reachability**
  (`DescriptiveComplexity.GAME`), and `DescriptiveComplexity.game_mem_PTIME`.
  An AND/OR graph is a directed graph whose nodes are split between two players,
  with a set of nodes that win outright; a node is winning when it wins
  outright, or belongs to the existential player and *some* successor wins, or
  belongs to the universal player, *has* a successor and *all* its successors
  win. Read with the universal player removed those are the three clauses of
  `DescriptiveComplexity.REACH`, so this is reachability with alternation – one
  operator more, one class up. A universal node with no successor **loses**,
  which is the convention `DescriptiveComplexity.ATMData.AltWin` already uses,
  and matching them is what will let an alternating machine's configuration
  graph be an instance with nothing to adjust. Membership is FO(LFP)
  definability (`DescriptiveComplexity.game_lfpDefinable`) with one twist: the
  universal clause is not a Horn body, so a second relation variable computes
  “every successor at least `y` wins” by a scan of the order from its greatest
  element down (`DescriptiveComplexity.order_induction_down`). Hardness
  (`DescriptiveComplexity.game_PTIME_hard`) is unit propagation read as a game:
  variables are existential nodes, clauses universal ones, a clause with no
  negative literal wins outright, and the goal clauses are the marked starts, so
  the existential player wins exactly when the Horn formula is
  *un*satisfiable — hardness of the complement, carried back by
  `DescriptiveComplexity.piP_zero_eq`, the same last step CVP's hardness takes.
  Whence `DescriptiveComplexity.game_PTIME_complete`.
* `DescriptiveComplexity.MachinesAltSpace` and
  `DescriptiveComplexity.Problems.MachineAltSpace` – **alternating acceptance in
  bounded space** (`DescriptiveComplexity.ATMAcceptSpace`), the EXPTIME
  candidate. It is `DescriptiveComplexity.ATMData.AltAccepts` with the step
  budget dropped, exactly as `DescriptiveComplexity.TMData.AcceptsSpace` is
  `DescriptiveComplexity.TMData.Accepts` with it dropped, so winning becomes the
  least fixed point of the game operator – an inductive predicate
  (`DescriptiveComplexity.ATMData.AltWin`), agreeing with the budgeted
  definition over a finite configuration space
  (`DescriptiveComplexity.ATMData.altWin_iff_exists_altAcc`). The alternation is
  *unbounded*: `DescriptiveComplexity.ATMData.BlocksWellFormed` is dropped for
  `DescriptiveComplexity.ATMData.BlocksSplit`, which only asks that the two
  marks of `FirstOrder.Language.turingAlt 2` partition the states, so no second
  machine record and no restated transport lemma is needed. With no universal
  state the model is the space-bounded nondeterministic one
  (`DescriptiveComplexity.ATMData.altAcceptsSpace_true_iff_acceptsSpace`), so it
  is a conservative extension.
* `DescriptiveComplexity.Problems.MachineAltSpace.Membership` –
  **`ATMAcceptSpace ∈ EXPTIME`**
  (`DescriptiveComplexity.atmAcceptSpace_mem_EXPTIME`), EXPTIME's first natural
  problem and the half of `APSPACE = EXPTIME` ([Chandra–Kozen–Stockmeyer
  1981][chandra1981alternation]) that this design reaches. The machine is a
  `DescriptiveComplexity.SOGameSpec` at the block with one variable for the
  state, one for the head and one — binary — for the tape; its `move` sentence
  is `DescriptiveComplexity.TMData.Step` with seven elements of the *base*
  quantified (the transition, the two states, the two head positions, the symbol
  read and the symbol written) and one universal pair for the cells the head
  does not touch, so nothing quantifies over a configuration and the sentence is
  first-order over the base. The correspondence with
  `DescriptiveComplexity.ATMData.AltWin` is a bisimulation between two
  inductives of the same shape, needing only *a move lands on a configuration*
  and *a start is a configuration*, so the block's junk assignments are never
  reached. The two promises `DescriptiveComplexity.TMData.WellFormed` and
  `DescriptiveComplexity.ATMData.BlocksSplit` ride on the `start` sentence:
  `DescriptiveComplexity.ExpDefinable` compares `P A` with `Q (X.Map A)` and has
  nowhere else to put a condition on `A` alone. **Hardness is not proved** and is
  a separate project – see `ROADMAP.md` §2.
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

## The numeric predicates, and AC⁰

The bottom of the ordered world, and the only vocabulary here that is a
*function of the order* rather than part of an instance.

* `DescriptiveComplexity.Arithmetic` – the arithmetic expansion
  `FirstOrder.Language.arith`: a binary `≤` and two ternary symbols read on a
  finite linear order through the rank of an element
  (`DescriptiveComplexity.orank`), as `orank x + orank y = orank z` and
  `orank x * orank y = orank z`. Relations, not functions, hence *truncated*: a
  sum that does not fit has no witness, and overflow is the first-order
  `¬∃z, plus x y z` (`DescriptiveComplexity.no_plus_iff_card_le`). Since the
  interpretation is canonical, an FO(≤) sentence is read arithmetically by a
  language map (`DescriptiveComplexity.sumOrderToArith`), and – the smallest
  thing the numeric predicates buy over a bare order – the *size* of the
  universe becomes visible: `DescriptiveComplexity.evenCardSentence` says that
  it is even, by the parity of the top rank.
* `DescriptiveComplexity.ArithmeticDefinable` – **AC⁰** as a logic:
  `DescriptiveComplexity.AC0Definable`, one sentence over the arithmetic
  expansion deciding the problem on every finite ordered instance. Classically
  this is `FO(≤, +, ×) = FO(≤, BIT)` and (DLOGTIME-)uniform AC⁰ ([Immerman
  1999][immerman1999descriptive], Thm 1.17; [Barrington, Immerman & Straubing
  1990][barrington1990uniformity]); no circuit model is introduced, so
  that identification is a bridge this library does not (yet) build – unlike the
  machine bridges of the classes above, which are theorems here. `+` and `×`
  are primitive rather than `BIT` because it is *they* whose interpreted-universe
  analogue is schoolbook arithmetic on base-`n` digits, where `BIT`'s is base
  conversion. Two features distinguish this notion from every other definability
  notion here: there is **no order-free variant**, the numeric predicates being
  meaningless without an order; and closure under complement is free
  (`DescriptiveComplexity.AC0Definable.compl`), the defining object being a
  sentence, where NL needed Immerman–Szelepcsényi. `FO(≤) ⊆ AC⁰` is transport
  (`DescriptiveComplexity.FODefinable.ac0Definable`) and is **strict**, by EVEN
  (`DescriptiveComplexity.exists_ac0Definable_not_foDefinable`, below).
* `DescriptiveComplexity.ArithmeticFixedPoint` – **`AC⁰ ⊆ PTIME`**
  (`DescriptiveComplexity.ac0Definable_mem_PTIME`), because the numeric
  predicates are themselves an induction: two relation variables of arity 3,
  `plus` walking `y` and `z` down the order in lockstep and `times` peeling one
  copy of `x` off `y` and adding it back with `plus`, in *one simultaneous*
  `DescriptiveComplexity.StepDef` – no stratification, the occurrences being
  positive. Soundness is an induction on the stages, completeness needs no stage
  count at all, only that the limit is closed under the clauses
  (`DescriptiveComplexity.inflLimit_arith_iff` is the resulting identification of
  the limit with the arithmetic). What makes the last step free is that the
  numeric predicates are *symbols*: the translation of an AC⁰ sentence is a
  language map (`DescriptiveComplexity.arithToBlock`), not a recursion, and
  `StepDef` accepts an unrestricted first-order output – which is exactly what an
  AC⁰ sentence needs, its numeric atoms sitting under any number of negations.
  The route through `FO(DTC)` does not work in the same way: a
  `DescriptiveComplexity.TCSpec` is one operator over first-order kernels with no
  relation variables, so the sharper `AC⁰ ⊆ LOGSPACE` wants the multi-head
  automaton instead. `DescriptiveComplexity.HeadArith` is the beginning of that
  route: `DescriptiveComplexity.HeadProgram.plusP` **decides the addition of two
  ranks** (`DescriptiveComplexity.HeadProgram.decides_plusP`), by walking one
  scratch head up from the first summand while a second counts to the second
  summand. The design decision that makes its specification clean is that the
  overflow marker – needed because “this head is at the greatest element” is not
  a quantifier-free fact of one head, while “these two heads are equal” is – is
  **parked by the fragment itself**, as a third scratch head, rather than being
  an input the caller must have prepared: a marker sitting anywhere else gives a
  walk with three regimes (exit `false` early, answer, or run off the end with no
  exit at all), and a specification stated by the marker's value, as
  `DescriptiveComplexity.HeadProgram.lexRel` must be.
  `DescriptiveComplexity.HeadProgram.timesP` then **decides the multiplication**
  (`DescriptiveComplexity.HeadProgram.decides_timesP`) with an addition *inside*
  it: an outer loop counts the rounds, and in each round a **scan** walks a
  candidate up the order asking `plusP` whether it carries the accumulator plus
  the first factor – which is how a decider is made to compute. Its three-level
  head layout is what makes the composition work: interface, then the four
  working heads, then the addition's own scratch heads, the middle level being
  where `DescriptiveComplexity.HeadProgram.runs_wireP`'s locality requirement
  lives.
* `DescriptiveComplexity.HeadEvalArith` – **`AC⁰ ⊆ LOGSPACE`**
  (`DescriptiveComplexity.ac0Definable_mem_LOGSPACE`), the sharp bound, by
  evaluating the sentence with a deterministic multi-head automaton of
  `qdepthA φ + 7` heads. It is `DescriptiveComplexity.HeadProgram.evalP` with one
  case split four ways: an atom of the input vocabulary and an atom of `≤` stay
  quantifier-free **guards**, while `plus` and `times` become the two *programs*
  above – they are not relations of the instance at all, but functions of the
  order, so they must be computed and not read. The sweep, the branch and the
  head accounting are reused unchanged, which is why the file is short; what it
  adds is `DescriptiveComplexity.relVar` and `DescriptiveComplexity.relTerm`
  (over a relational vocabulary a term *is* a variable, which is how an atom's
  arguments become head indices) and the head layout
  `DescriptiveComplexity.HeadProgram.ArithScratch`, seven heads above the
  quantifier region. With this the bottom of the ladder is pinned:
  `FO(≤) ⊊ AC⁰ ⊆ LOGSPACE ⊆ NL ⊆ PTIME`, the first inclusion strict and the
  strictness of the second exactly the switching lemma.
* `DescriptiveComplexity.LogTime` – **a machine model for the bottom of the
  ladder**, in the shape the logarithmic-time hierarchy prescribes (Sipser 1983;
  [Barrington, Immerman & Straubing 1990][barrington1990uniformity]) rather than
  that of circuit families. A `DescriptiveComplexity.LTMachine` fills a list of
  registers, each by one of the two players – a register is an address of
  `DescriptiveComplexity.posCount A ≈ log n` bits, so filling one is the
  logarithmic block of guesses of the `Σₖ-TIME(log n)` normal form, and an
  alternation is a change of polarity along the list – and then runs a
  deterministic **bit-level** base: a Boolean combination of *queries* (an input
  relation at a tuple of registers, which is the random access of the model:
  reading the input at an address *is* evaluating a relation at a tuple) and of
  *sweeps*, single passes over the bit positions by a finite automaton reading
  one bit of each register at each position. Nothing in the base evaluates a
  numeric predicate, and that is the point: the arithmetic must be built, which
  `DescriptiveComplexity.leSweep_accepts` and
  `DescriptiveComplexity.plusSweep_accepts` do for `≤` and `plus` – the
  bit-level analogues of `DescriptiveComplexity.HeadProgram.plusP`. The
  inclusion proved is `DescriptiveComplexity.LTDecidable.ac0Definable`: a sweep
  carries a constant number of state bits past each of the `log n` positions, so
  its whole history is a constant number of *bit vectors over the positions*,
  and such a vector **is** an element of the universe – the sentence guesses
  those elements and pins them with the transition, determinism making the guess
  unique. The bit predicate that makes this first-order is
  `DescriptiveComplexity.BitAt`, `BIT` derived from `+` and `×` by naming a
  position by its *place value* rather than its exponent
  (`DescriptiveComplexity.IsPos`: a nonzero rank whose divisors are `1` or even),
  so that the next position is `p + p` and the bit of `x` at `p` is a division
  with remainder whose witnesses are all below `x`, hence ranks. The converse
  inclusion is **not** proved and is not an oversight: multiplication is not a
  constant number of sweeps, a base that revisits its positions unboundedly
  often leaves the trace budget the simulation lives on, and simulating such a
  base in the logic is the hard half of the classical `AC⁰ = LH` theorem.

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
* `DescriptiveComplexity.SecondOrderTransitiveClosureFree` – **SO(TC) needs no
  order** (`DescriptiveComplexity.sotcDefinable_iff_free`,
  `DescriptiveComplexity.mem_PSPACE_iff_sotcDefinableFree`). Unlike the clausal
  fragments and the reachability logics, this one can *guess* its order, for the
  reason Fagin's theorem can: a state of the walk is an assignment of relation
  variables, so one more binary variable holds a candidate order, the source
  condition checks that it is linear (`DescriptiveComplexity.linearGuard`,
  shared with the order elimination of
  `DescriptiveComplexity.SecondOrderOrdered`), every step freezes it, and the
  three sentences read it in place of the order symbol. The order is then a
  component of the certificate and nothing outside the specification sees it, so
  `DescriptiveComplexity.SOTCDefinableFree` – definability by a
  `DescriptiveComplexity.SOTCSpecFree`, stated on structures carrying **no
  order at all** – defines the same class. A deterministic fragment cannot do
  this, which is why `DescriptiveComplexity.PTIME`,
  `DescriptiveComplexity.NL` and `DescriptiveComplexity.LOGSPACE` keep the
  hypothesis.
* `DescriptiveComplexity.FixedPointPartialSpace` – **FO(≤, PFP) ⊆ PSPACE**
  (`DescriptiveComplexity.PFPDefinable.sotcDefinable`): a partial fixed-point
  iteration *is* a deterministic walk on the assignments of its own block, so
  it translates into an `DescriptiveComplexity.SOTCSpec` verbatim – source the
  empty assignment, step «the next copy is one application of the step
  formulas», target «a stable stage satisfying the output». No divergence
  detection is needed: under the convergence-requiring semantics a diverging
  iteration simply reaches no target state.
* `DescriptiveComplexity.FixedPointParam` – **an element, quantified in front
  of a fixed point** (`DescriptiveComplexity.mem_PTIME_exElement`): if a problem
  over the vocabulary extended by a mark is FO(≤, IFP) definable, so is “some
  element, marked, makes it hold”. A fixed point cannot be restarted once per
  element, so the construction runs all of them at once – every relation
  variable gains the parameter as a further argument, and the atom `old t`
  becomes `t = parameter`. It is the deterministic counterpart of
  `DescriptiveComplexity.SOTCDefinable.exBlock`, which prefixes a *walk* with a
  guessed relation: a walk may guess, a fixed point may not, and one element is
  what it can afford instead.
* `DescriptiveComplexity.FixedPointStepRel` – **membership closure under
  relativized ordered reductions** `≤ʳᶠᵒ[≤]`, which no definability notion of
  the library had needed before
  (`DescriptiveComplexity.IFPDefinable.of_relOrderedReduction`,
  `DescriptiveComplexity.PFPDefinable.of_relOrderedReduction`): the block is
  pulled back onto the definable domain with the step formulas gated by the
  domain formulas of their arguments, and the assignment transfer is a
  *bijection* onto the in-domain assignments – which is what a deterministic
  iteration needs where an existential block would settle for less. Required
  because all the library's hardness travels along relativized reductions, and
  the PSPACE capture below crosses one in the membership direction.
* `DescriptiveComplexity.FixedPointPartialMachine` – **PSPACE ⊆ FO(≤, PFP)**,
  completing the capture theorem **FO(≤, PFP) = PSPACE**
  (`DescriptiveComplexity.pfpDefinable_iff_mem_PSPACE`,
  [Abiteboul–Vianu 1989][abiteboul1989fixpoint]): a partial fixed point
  iterates the PSPACE-complete deterministic machine problem – load the
  initial configuration from the empty assignment, take the unique machine
  step while one exists, stutter on accepting or stuck configurations so that
  a halting run is exactly a converging iteration – and every PSPACE problem
  pulls that definition back along its relativized reduction to the machine
  problem.
* `DescriptiveComplexity.AbiteboulVianuOrdered` – **Abiteboul–Vianu, the
  ordered case**
  (`DescriptiveComplexity.ifpDefinable_eq_pfpDefinable_iff_ptime_eq_pspace`):
  on ordered structures the inflationary and partial fixed-point logics agree
  exactly when `PTIME = PSPACE` – a corollary of the two capture theorems.
* `DescriptiveComplexity.AbiteboulVianu` – **the Abiteboul–Vianu theorem**
  ([Abiteboul–Vianu 1991][abiteboul1991generic];
  [Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 7): the inflationary and
  partial fixed-point logics have the same expressive power **on unordered
  finite structures** exactly when `PTIME = PSPACE`
  (`DescriptiveComplexity.ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace`).
  Right to left through the order-relativization transfer and the two
  captures; left to right through the invariant structure: an order-free
  FO(PFP) computation is `≡ᵏ`-invariant, so it runs on `Iᵏ A`, where
  `PTIME = PSPACE` turns it into an ordered inflationary induction, pulled
  back along the quotient map and stratified over the canonical order's own
  induction. Stated for IFP versus PFP, as in the original – Gurevich–Shelah
  is deliberately not involved.
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
  reading of Savitch's theorem. Hardness is proved once, for the *deterministic*
  problem, by a machine that evaluates a quantified Boolean formula by the
  standard iterative algorithm – the recursion stack being one bit per variable,
  in the variable's own cell – and travels to the nondeterministic problem along
  a reduction that enforces determinism as a first-order promise. So both are
  PSPACE-complete (`DescriptiveComplexity.dtmAcceptSpace_PSPACE_complete`,
  `DescriptiveComplexity.ntmAcceptSpace_PSPACE_complete`), which is this
  framework's `PSPACE = NPSPACE`: nothing simulates a nondeterministic machine
  deterministically, Savitch having already been spent logically in
  `DescriptiveComplexity.Problems.Qsat`.

## The exponential classes, by expansion

* `DescriptiveComplexity.Exponential` – **EXPTIME, NEXPTIME and EXPSPACE**,
  obtained by reading the polynomial-level logics over a universe one
  exponential larger. An `DescriptiveComplexity.ExpExpansion` maps a finite
  ordered structure `A` to a structure whose universe is a *definable set of
  tagged assignments of a second-order block* – `2^(n^a)` points on a universe
  of size `n` – each relation being defined by a first-order sentence over the
  base vocabulary expanded by one copy of the block per argument. This is the
  same construction the library already carries for SUCCINCT-REACH, made into
  data and applied to an arbitrary vocabulary; it is also the standard
  type-lowering translation of higher-order logic into many-sorted first-order
  logic over the power type ([Henkin 1950][henkin1950completeness]), which is
  why a *second*-order fixed point over `A` is an ordinary first-order fixed
  point over the expansion, and why no third-order syntax is introduced.
* `DescriptiveComplexity.Exponential.Pull` – **an interpretation followed by an
  expansion is an expansion**
  (`DescriptiveComplexity.ExpExpansion.pullOrdered`), which is what makes the
  notion closed under (ordered) FO reductions. Everything it needs is already
  in the library: the order of an interpreted universe is definable
  (`DescriptiveComplexity.FOInterpretation.ordExtend`), a block pulls back
  through an interpretation (`DescriptiveComplexity.SOBlock.pull`), and
  replication commutes with that pullback definitionally
  (`DescriptiveComplexity.SOBlock.homAssign_replicatePullHom`) – so the
  defining sentences of the composite are the pulled ones read through a
  renaming of relation variables and nothing more.
* `DescriptiveComplexity.Exponential.Class` – the operator
  `DescriptiveComplexity.ComplexityClass.exp`, applied to an **abstract**
  class. That abstraction is the whole design: the succinctness upgrade
  ([Galperin–Wigderson 1983][galperin1983succinct];
  [Papadimitriou–Yannakakis 1986][papadimitriou1986note]; in general form
  [Veith 1998][veith1998succinct]) is proved once, as
  `DescriptiveComplexity.ComplexityClass.exp_compl` and
  `DescriptiveComplexity.ComplexityClass.exp_mono`, and every exponential-level
  statement is read off from its polynomial-level counterpart.
* `DescriptiveComplexity.Exponential.Classes` – the three classes.
  `EXPTIME` is *defined* as SO(≤, LFP) and `EXPSPACE` as SO(≤, PFP)
  (`DescriptiveComplexity.SOLFPDefinable`,
  `DescriptiveComplexity.SOPFPDefinable`), and each equals the exponential of
  its polynomial counterpart by theorem
  (`DescriptiveComplexity.EXPTIME_eq_PTIME_exp`,
  `DescriptiveComplexity.EXPSPACE_eq_PSPACE_exp`) – these are the library's own
  capture theorems FO(≤, LFP) = PTIME and FO(≤, PFP) = PSPACE, read on the
  expanded universe. Naming the classes after these logics follows
  [Abiteboul–Vardi–Vianu 1997][abiteboul1997fixpoint], cited for the *names*
  only: that work is stated in the relational, order-free setting, and here the
  logics are definitions, so no capture theorem is claimed. `NEXPTIME` is
  defined as `NP.exp`; its literature characterization is existential
  *third*-order logic ([Leivant 1989][leivant1989descriptive];
  [Hella–Turull-Torres 2006][hella2006higher]) and the library does not state
  that equivalence, having no third-order syntax – an honest and narrow gap,
  since NEXPTIME still gets its logical reading, guess a relation over the
  expanded universe and check a first-order condition there.
* `DescriptiveComplexity.Exponential.Inclusions` – **`EXPTIME = coEXPTIME`**
  and **`EXPSPACE = coEXPSPACE`**, inherited from
  `DescriptiveComplexity.piP_zero_eq` (Grädel's capture theorem at level 0) and
  `DescriptiveComplexity.PSPACE_eq_coPSPACE` (Savitch) through `exp_compl`.
  Read on the definitions they say that SO(LFP) and SO(PFP) are closed under
  complement. Nothing of those two developments is spent twice; no claim is
  made for NEXPTIME. The inclusions `PSPACE ⊆ EXPTIME ⊆ NEXPTIME ⊆ EXPSPACE`
  follow, all but the first by `exp_mono` on a polynomial-level inclusion.
* `DescriptiveComplexity.Exponential.Reach` – the one inclusion with content,
  `DescriptiveComplexity.PSPACE_subset_EXPTIME`: an
  `DescriptiveComplexity.SOTCSpec` *is* the graph REACH reads on the expansion
  whose points are its states, the two definitions being the same sentence up
  to the name of the universe. Since REACH is in every class from NL up, this
  gives `PSPACE ⊆ NL.exp` as well, and `NL.exp ⊆ EXPTIME` comes back by
  monotonicity. On the definitions the inclusion is **SO(TC) ⊆ SO(LFP)**, the
  second-order shadow of `NL ⊆ PTIME`.
* `DescriptiveComplexity.Exponential.Game` – the same construction one operator
  up, and the way into EXPTIME that needs no succinctness argument. A
  `DescriptiveComplexity.SOGameSpec` is four first-order sentences over a
  second-order block – which assignments the universal player owns, which win
  outright, which start the game, which moves are legal, the move sentence
  seeing two copies as an `DescriptiveComplexity.SOTCSpec`'s transition does –
  and it *is* the AND/OR graph `DescriptiveComplexity.GAME` reads on the
  expansion whose points are its states
  (`DescriptiveComplexity.SOGameSpec.gameWon_toExp_iff`). Since GAME is in
  PTIME, `DescriptiveComplexity.SOGameDefinable.mem_EXPTIME` follows: **SO-GAME
  ⊆ SO(LFP)**, the second-order shadow of `GAME ∈ PTIME`, exactly as the
  previous entry is the shadow of `REACH ∈ PTIME`. It is what an alternating
  space-bounded machine consumes, its configurations being the assignments of a
  block with one variable for the state, one for the head and one for the tape
  (`DescriptiveComplexity.atmAcceptSpace_soGameDefinable`).
* `DescriptiveComplexity.Exponential.GameExp` – the converse, and with it
  **`EXPTIME = SO-GAME`** (`DescriptiveComplexity.exptime_eq_soGame`): *the
  deterministic exponential class is second-order alternating reachability*.
  This is Chandra–Kozen–Stockmeyer ([Chandra–Kozen–Stockmeyer
  1981][chandra1981alternation]) with the machine removed. A problem of
  `SO(≤, LFP)` is a `PTIME` property of an expansion
  (`DescriptiveComplexity.solfpDefinable_iff_expDefinable`), hence `GameWon` of
  the AND/OR graph an interpretation draws *on the expanded universe*
  (`DescriptiveComplexity.game_hard_ordered`); its four defining relations are
  first-order there, so by the translation lemma they are alternating block
  prefixes over the base — and a prefix is a sequence of **moves**, which is
  precisely what the obstruction of `Exponential.Translate` does not forbid.
  `DescriptiveComplexity.ExpExpansion.graphGame` plays that graph, in six
  phases: the four node phases (`main`, `exStep`, `allCert`, `allStep`) and the
  prefix phases that decide the six questions
  (`DescriptiveComplexity.Sub`) about one or two nodes. Two conventions are
  load-bearing: a leaf whose kernel fails is existential and moveless, so an
  unprovable claim loses; and `allCert` certifies a successor *before* the
  universal player chooses one, since `DescriptiveComplexity.WinsOn.all` makes a
  stuck universal node lose.
* `DescriptiveComplexity.Exponential.Translate` – **the translation lemma**
  (`DescriptiveComplexity.ExpExpansion.exists_translate`): a first-order
  sentence *over an expansion* is a second-order sentence over the base, since
  a quantifier ranging over the points of the expanded universe ranges over
  block assignments. This is the type-lowering reading of [Henkin
  1950][henkin1950completeness] made into a theorem, and the honest statement
  of the obstruction that keeps an interpretation from being composed *after*
  an expansion. A quantified point is a block extended by tag bits, guarded to
  satisfy its tag's domain sentence; each quantifier peels into two blocks, one
  `∃` and one `∀`, of which one is real and the other vacuous, so that the
  prefix alternates strictly; and the induction runs on the
  `FirstOrder.Language.BoundedFormula.IsPrenex` proof, `∃` being encoded as
  `∼(∼φ).all` and so unreachable by a structural recursion.
* `DescriptiveComplexity.Exponential.Increment` – the **successor of an
  assignment**, as a first-order sentence over the base and two copies of the
  block: an assignment is a binary number, so the successor is the increment.
  The subtlety it settles is that `DescriptiveComplexity.SOBlock.atomSet` reads
  an assignment as a set of *padded* atoms, whose image is only the
  padding-invariant sets, so the increment has to be taken at the honest atoms
  `Σ i, Fin (B.arity i) → A` and matched to the padded order through least
  representatives. With
  `DescriptiveComplexity.ExpExpansion.trivialize` – which trades an expansion's
  domain sentence for a mark, carrying an FO(TC) walk along
  (`DescriptiveComplexity.ExpExpansion.accepts_relSpec`), so that a point is
  *every* tagged assignment – these are the order primitives a machine needs to
  walk an expanded universe.
* `DescriptiveComplexity.Exponential.PSpaceOn` – its payoff,
  `DescriptiveComplexity.ExpExpansion.mem_PSPACE_of_fo_on_expansion`: **every
  first-order property of an exponential expansion is in `PH`, hence in
  `PSPACE`**. This is one bound on the operator *from above*; most of what is
  proved about it validates it from below, `PSPACE ⊆ NL.exp ⊆ EXPTIME`.
* `DescriptiveComplexity.Exponential.Simulate` – **a machine that walks an
  expanded universe is a walk over the base**
  (`DescriptiveComplexity.ExpExpansion.autoSpec`,
  `DescriptiveComplexity.ExpExpansion.accepts_autoSpec`). A configuration of a
  two-way `k`-head automaton over an expansion is a control state and `k`
  points, i.e. one assignment of the block
  `(repMerged X.pointBlock k).withTag M.State` – a state of an
  `DescriptiveComplexity.SOTCSpec`. The automaton's tests are quantifier-free
  *by fiat* (`DescriptiveComplexity.HeadAutomaton.test_qf`), so
  `DescriptiveComplexity.ExpExpansion.translQF` translates them as they stand
  and no quantifier over the expanded universe is ever evaluated; its moves are
  the order primitives of `Exponential.Increment`, read at a
  `DescriptiveComplexity.ExpExpansion.PtSlot` – one interface for “a point sits
  here inside that block”, used both for one configuration and for the two a
  transition sentence compares. The correctness is a one-step bisimulation, the
  one hypothesis being that every tagged assignment is a point, which is what
  `DescriptiveComplexity.ExpExpansion.trivialize` arranges.
* `DescriptiveComplexity.Exponential.Gate` – **`PSPACE = NL.exp`**
  (`DescriptiveComplexity.PSPACE_eq_NL_exp`): polynomial space *is*
  nondeterministic logarithmic space read one exponential up. Both inclusions
  are theorems, so the exponential operator is pinned at the one level where
  this library independently knows the answer, and not merely bounded. The
  converse half chains three constructions – carry the walk to the trivialized
  expansion, compile it into an automaton
  (`DescriptiveComplexity.tcDefinable_iff_automaton`), simulate the automaton.
  `LOGSPACE.exp ⊆ PSPACE` follows by monotonicity; the reverse inclusion is not
  claimed, REACH not being known here to be in
  `DescriptiveComplexity.LOGSPACE`.
* `DescriptiveComplexity.Exponential.Free`, `.FreeCopy`, `.FreeSpace`,
  `.FreeTime` – **the exponential classes need no order**
  (`DescriptiveComplexity.mem_EXPTIME_iff_solfpDefinableFree`,
  `DescriptiveComplexity.mem_EXPSPACE_iff_sopfpDefinableFree`): the expansion's
  own sentences can be written over the bare vocabulary, so that the
  equivalence is asked of structures carrying no order at all, which is the
  setting of [Abiteboul–Vardi–Vianu 1997][abiteboul1997fixpoint]. The order is
  *guessed* into the block, exactly as
  `DescriptiveComplexity.sotcDefinable_iff_free` guesses it into the state of a
  walk – but the price is different: the expanded universe becomes the disjoint
  union, over the linear orders of the instance, of copies of the intended one,
  and the inner problem must be replaced by “**some copy answers yes**”, which
  is correct precisely because the problem is order-invariant. How that
  existential is paid for is what separates the two classes. `PSPACE` **guesses
  the copy** as a relation and freezes it in the state of a walk
  (`DescriptiveComplexity.ExpExpansion.someCls`, on
  `DescriptiveComplexity.SOTCDefinable.exBlock`, with the first-order guard that
  it *is* a copy conjoined by
  `DescriptiveComplexity.SOTCDefinable.and_sentence`). `PTIME` cannot guess, so
  it **names the copy by one of its points**
  (`DescriptiveComplexity.ExpExpansion.somePtCls`) and quantifies that point
  away by carrying it through every relation variable of the induction
  (`DescriptiveComplexity.mem_PTIME_exElement`). Both then read the problem
  inside the copy by a relativized ordered reduction. A nullary symbol has no
  copy of the block to read the guessed order from, so its content moves to a
  **unary shift** whose argument names the copy – which is what lets the
  construction carry no hypothesis on the arities.

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
  the complement operator `DescriptiveComplexity.coRE`. `∃SO[new]` has no dual
  reading, so nothing in that file relates RE and co-RE; the separation
  `DescriptiveComplexity.RE_ne_coRE` is proved where the class meets Mathlib's
  computability layer, in
  `DescriptiveComplexity.Computability.CodeHaltComplete`. Its first complete
  problem is finite satisfiability, by Trakhtenbrot's theorem
  (`DescriptiveComplexity.Problems.FinSat`), and Post's correspondence problem
  is a member of it (`DescriptiveComplexity.pcp_mem_RE`).

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
  finite structures, for threshold and weight parameters of problems; its
  module docstring argues the per-problem choice between the two.
* `DescriptiveComplexity.Machines` – Turing machines as relations on a
  universe, with no vocabulary: configurations, steps, and acceptance within a
  budget counted in universe elements. The semantics the machine bridge reads
  off an instance.

## The bridge to Mathlib's computability layer

Every class of this development is defined by a *logic*, and every problem is
an isomorphism-closed property of finite structures. `ComputablePred` and
`REPred`, on the other hand, are predicates on a `Primcodable` type, so
relating the two needs a passage from isomorphism classes to data. It is built
once for the catalog rather than once per problem.

* `DescriptiveComplexity.Computability` – the umbrella. A finite structure over
  a finitely presented relational vocabulary becomes a universe `Fin (n + 1)`
  and a list of Boolean tables (`FirstOrder.Language.FinStruct`, a
  `Primcodable` type, nonempty and linearly ordered by construction); a fixed
  first-order formula is evaluated on it *primitive recursively*
  (`FirstOrder.Language.FinStruct.primrec_evalBF`), and hence decidably on any
  finite structure at all (`FirstOrder.Language.BoundedFormula.decidableRealize`
  – the first formal justification of the claim, elsewhere by inspection, that
  first-order interpretations are effective).
* `DescriptiveComplexity.RE_subset_rePred` – **RE really is recursively
  enumerable**: the `∃SO[new]` certificate, a number of invented values and an
  assignment of the relation variables, is a finite object, so it is *searched
  for*, and the first-order kernel is checked on it by the evaluator. This makes
  the name of the class a theorem rather than a convention, and it needs no
  machine model. Read at the two problems of the machine bridge, it gives
  `DescriptiveComplexity.halt_rePred` and
  `DescriptiveComplexity.finsat_rePred`.

* `DescriptiveComplexity.not_computablePred_of_relOrderedReduction` – **first-order
  reductions are computable**: an interpretation induces a computable many-one
  reduction of the induced sets, so undecidability transfers backwards along
  `≤ᶠᵒ`, `≤ᶠᵒ[≤]` and `≤ʳᶠᵒ[≤]`. The order costs nothing (the universe of a
  concrete instance is already `Fin (n + 1)`); the work is the *renumbering* a
  definable target domain forces, and the run-time choice among the `|Tag|ⁿ`
  instances of a defining formula.

* `DescriptiveComplexity.not_computablePred_codehalt` – **the first problem of
  the catalog proved undecidable outright**. Mathlib's halting problem is
  carried in by making the *code the instance*: a `Nat.Partrec.Code` is drawn
  as its syntax tree (`DescriptiveComplexity.CODEHALT`,
  `DescriptiveComplexity.codeStruct`), so the map from codes to instances is a
  plain tree flattening and hence primitive recursive – which the simulation of
  a machine could not be, Mathlib's universal machine not being finite-state.

* `DescriptiveComplexity.not_computablePred_of_RE_hard` – **an RE-hard problem
  is undecidable**, once and for all. Hardness here is cofinal, so an RE-hard
  problem is in particular a target of CODEHALT, which is undecidable, and the
  reduction is computable. This is the leverage the layer exists for: a
  completeness theorem for RE now yields undecidability with no computability
  work of its own. Its first instance is
  `DescriptiveComplexity.finsat_not_computable`, **Trakhtenbrot's theorem**:
  whether a first-order sentence has a *finite* model is undecidable.

* `DescriptiveComplexity.mem_RE_iff_rePred` – **RE is exactly recursive
  enumerability**, the converse inclusion and with it the identity of the
  logically defined class with the machine one. A semi-decidable problem
  reduces to CODEHALT by drawing the instance as the *program* that runs a
  semi-decision procedure on it: the procedure is
  *obtained* from Mathlib (`Nat.Partrec.Code.exists_code`) rather than built,
  which is exactly what spares the layer the evaluator with addressed storage
  a machine target would need. Whence
  `DescriptiveComplexity.codehalt_RE_complete` and, by Post's theorem applied
  to the undecidability above, `DescriptiveComplexity.RE_ne_coRE`.

## The problem catalog

`DescriptiveComplexity.Problems` holds one decision problem per file, each with
its vocabulary, FO reductions and a completeness theorem. Every class in the
table below is *defined* logically; each problem listed is proved **complete**
for it – both a member and hard under FO reductions. The catalog covers all of
Karp's 21 NP-complete problems. Each problem's own module page documents its
reduction and certificate in full.

| Complexity class | Logical characterization | Machine model | Problems proved complete |
| --- | --- | --- | --- |
| `LOGSPACE` (`L`) | FO(≤, DTC): first-order logic with a deterministic transitive closure, over a linearly ordered universe | deterministic two-way `k`-head automaton, walking a linear order of the universe † | REACHd · UNREACHd |
| `NL` | SO-Krom(≤): ∃SO with a Krom kernel, at most two second-order literals per clause; equivalently FO(≤, TC), first-order logic with a transitive closure – both over a linearly ordered universe | two-way `k`-head automaton, walking a linear order of the universe † | REACH · UNREACH · 2SAT |
| `PTIME` = `Σ₀ᵖ` = `Π₀ᵖ` | SO-Horn(≤): ∃SO with a Horn kernel; equivalently FO(≤, LFP), first-order logic with a least fixed point – both over a linearly ordered universe | deterministic polynomial-time Turing machine | HORN-SAT · CVP |
| `NP` = `Σ₁ᵖ` | ∃SO: existential second-order logic | nondeterministic polynomial-time Turing machine | **SAT-family:** SAT · 3SAT · NAE-SAT · NAE-3SAT · 1-in-SAT<br>**Coloring:** 3-Colorability · `k`-Colorability (`k ≥ 3`) · Chromatic Number · Clique Cover<br>**Cliques & subgraphs:** Clique · Independent Set · Vertex Cover · Subgraph Isomorphism<br>**Sets & hypergraphs:** Set Cover · Hitting Set · Set Packing · Exact Cover · Set Splitting · Dominating Set · 3-Dimensional Matching<br>**Graphs:** Feedback Vertex Set · Feedback Arc Set · Steiner Tree (node- & edge-weighted) · Max Cut · Hamilton Circuit (directed & undirected)<br>**Numbers (in binary):** Knapsack · Partition · 0-1 Integer Programming · Job Sequencing<br>**Machines:** acceptance by a nondeterministic polynomial-time Turing machine |
| `coNP` = `Π₁ᵖ` | ∀SO: universal second-order logic | nondeterministic polynomial-time Turing machine, accepting when *every* run does | TAUT · 3-DNF-TAUT · 3-UNSAT (and QBF∀ at one block) · `ATMAccept 1 false` |
| `DP` | a `Σ₁` and a `Π₁` sentence conjoined | — | SAT-UNSAT |
| `Σₖᵖ` (`k ≥ 1`) | `Σₖ¹`: `k` alternating second-order quantifier blocks, existential first | alternating polynomial-time Turing machine, `k` blocks, existential first | `QBF k` – at `k = 1`, NP · `ATMAccept k true` |
| `Πₖᵖ` (`k ≥ 1`) | `Πₖ¹`: `k` alternating second-order quantifier blocks, universal first | the same machine, universal first | `QBF∀ k` – at `k = 1`, coNP · `ATMAccept k false` |
| `PH` | full second-order logic | — | — |
| `PSPACE` | SO(TC): second-order logic with a transitive closure over assignments of a block of relation variables | polynomial-space Turing machine, deterministic or not | SUCCINCT-REACH · QSAT · space-bounded machine acceptance (deterministic & not) |
| `RE` | ∃SO[new]: ∃SO with value invention, the relation variables ranging over the universe extended by finitely many invented values | Turing machine with no step bound and no space bound | FINSAT (Trakhtenbrot's theorem) · CODEHALT · HALT · PCP (Post's correspondence problem) |
| the degree of a problem: `DescriptiveComplexity.ComplexityClass.below Q₀`, e.g. `GI` | none – a downward closure under `≤ᶠᵒ[≤]` rather than a logic, which is the point of the construction | — | for `GI`: Graph Isomorphism · Digraph Isomorphism · DAG Isomorphism |

Each entry of the **machine model** column is an equivalence *proved here*
between the logical definition of the class and acceptance by that model:
`DescriptiveComplexity.mem_LOGSPACE_iff_automaton` and
`DescriptiveComplexity.mem_NL_iff_automaton` (†), and, through the completeness
of an acceptance problem, `DescriptiveComplexity.mem_PTIME_iff_le_dtmAccept`,
`DescriptiveComplexity.mem_NP_iff_le_ntmAccept`,
`DescriptiveComplexity.le_dtmAcceptSpace_of_mem_PSPACE` and
`DescriptiveComplexity.mem_RE_iff_rePred`. A dash marks a class for which no
such equivalence is proved here.

† Capture theorems, both directions: `DescriptiveComplexity.mem_NL_iff_automaton`
for `NL`, and `DescriptiveComplexity.mem_LOGSPACE_iff_automaton` for `LOGSPACE`,
where the machine is required to be deterministic.

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
* **The machine bridge for the hierarchy**: the same identification one level
  of alternation at a time. `DescriptiveComplexity.ATMAccept k start` – does
  this *alternating* machine, whose states carry `k` block marks entered in
  order, accept its input within the same unary budget? – is `Σₖᵖ`-complete for
  an existential first block
  (`DescriptiveComplexity.atmAccept_sigmaP_complete`) and `Πₖᵖ`-complete for a
  universal one (`DescriptiveComplexity.atmAccept_piP_complete`), so each level
  of the logically defined hierarchy is the corresponding level of the
  alternating-machine hierarchy of [Chandra–Kozen–Stockmeyer
  1981][chandra1981alternation]. At one block the two are the nondeterministic
  model and its dual, which is where coNP gets its machine
  (`DescriptiveComplexity.atmAccept_one_complete`,
  `DescriptiveComplexity.atmAccept_one_coNP_complete`) (`DescriptiveComplexity.mem_sigmaP_iff_le_atmAccept`,
  `DescriptiveComplexity.mem_piP_iff_le_atmAccept`). Membership reads a run as
  a `k`-round game, each round guessing one walk; hardness builds the machine
  `M_φ` of a quantified Boolean formula inside the instance – one sweep of the
  tape per quantifier block, whose only choice is which of its block's
  variables to set, so that the moves of a round *are* the truth assignments of
  its block, followed by a deterministic check phase walking the clauses.
* **All of Karp's 21** ([Karp 1972][karp1972reducibility]): the SAT, clique,
  set, coloring, graph and number families above, closed by the two Hamilton
  circuit problems – a circuit read as a linear order of the universe, hard
  from Vertex Cover by Karp's twelve-vertex cover-testing gadget.
* **CVP, the textbook `PTIME`-complete problem**
  (`DescriptiveComplexity.CVP_PTIME_complete`; [Ladner
  1975][ladner1975circuit]): membership is an FO(LFP) definition – the problem's
  semantics *is* a least fixed point, so the rule system is the gate rules
  transcribed and the output sentence is the one a Horn program cannot write,
  “the output gate is in the true rail”. Hardness draws the unit-propagation
  circuit inside a HORN-SAT instance and reports the *failure* of Horn
  satisfiability, which keeps the circuit monotone and costs nothing, polynomial
  time being closed under complement. The stages of the fixed point are unrolled
  along the order and the two unbounded quantifiers of a round become chains of
  fan-in-two gates; what makes it work is that the *wiring*, being defined by a
  formula, may test where a literal occurs, where a fixed circuit may not.
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
* **Immerman–Vardi, `PTIME = FO(≤, LFP)`**
  (`DescriptiveComplexity.lfpDefinable_iff_mem_PTIME`; [Vardi
  1982][vardi1982complexity]; [Immerman 1986][immerman1986relational]): a problem is
  in polynomial time exactly when a least-fixed-point definition computes it over a
  linearly ordered universe – order-*invariantly*, since
  `DescriptiveComplexity.LFPDefinable` asks for the equivalence at every linear order.
  The class being *defined* by the Horn fragment, the content is the pair of
  translations of `DescriptiveComplexity.FixedPointHorn`, so the theorem is
  machine-free like everything else here; the machine reading is the bridge
  `DescriptiveComplexity.mem_PTIME_iff_le_dtmAccept`. The inflationary variant
  `DescriptiveComplexity.ifpDefinable_iff_mem_PTIME` is the same statement for
  FO(≤, IFP), and `DescriptiveComplexity.hornSat_hard_of_lfpDefinable` is the
  hardness discharge from the logic – a hardness proof may start from a fixed-point
  definition, where negation is free, rather than from a Horn program.
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

* **Complete, but not for a class**: Digraph Isomorphism
  (`DescriptiveComplexity.Problems.DigraphIso`) – are the two marked directed
  graphs of the instance isomorphic? – is in NP by a textbook `Σ₁` guessing the bijection
  (`DescriptiveComplexity.digraphIso_mem_NP`), with no order, no counting and no
  threshold, and is the library's first problem conjecturally neither in P nor
  NP-complete ([Babai 2016][babai2016graph]; [Köbler, Schöning and Torán
  1993][kobler1993graph]). What it *is* complete for is its own degree
  (`DescriptiveComplexity.digraphIso_GI_complete`), which is the whole point of
  `DescriptiveComplexity.ComplexityClass.below`, and that degree lies inside NP
  (`DescriptiveComplexity.GI_subset_NP`). It is also the problem of deciding the
  very equivalence a `DescriptiveComplexity.DecisionProblem` is required to be
  invariant under: `DescriptiveComplexity.relIsoOn_iff_equiv` states the
  semantics as the existence of an equivalence between the two marked sets
  carrying one adjacency relation to the other. **DAG Isomorphism**
  (`DescriptiveComplexity.Problems.DagIso`) is the first companion in that
  degree, GI-complete (`DescriptiveComplexity.dagIso_GI_complete`): hardness
  subdivides every arc *twice*, so that its direction survives as the
  difference between the two subdivision levels, and membership forgets the
  topological order the instances carry. They carry one because acyclicity is
  not first-order definable, so a reduction could not otherwise test it – the
  place where the first-order setting genuinely constrains what a problem may
  be, and where a polynomial-time reduction would simply run a cycle check.
  **Graph Isomorphism** proper – the simple-graph problem the literature names
  GI (`DescriptiveComplexity.GraphIso`) – is **GI-complete**
  (`DescriptiveComplexity.graphIso_GI_complete`): simplicity is first-order, so
  one direction only tests it, and the other is the classical digraph-to-graph
  gadget – every arc subdivided three times, each vertex carrying a lollipop
  and each tail a pendant, so that the levels are recovered from adjacency
  alone and the pendant carries the arc's direction. The degree is *defined* on
  this problem – the literature's GI is the undirected one – and the directed
  problem is complete for it too
  (`DescriptiveComplexity.digraphIso_GI_complete`,
  `DescriptiveComplexity.GI_eq_below_digraphIso`). The shared layer for
  reductions between isomorphism problems is `DescriptiveComplexity.IsoGadget`:
  it reads a marked binary relation as a
  `FirstOrder.Language.graph`-structure in its own right, so that the semantic
  condition of every problem in the degree becomes an isomorphism of the two
  sides (`DescriptiveComplexity.relIsoOn_iff_nonempty_sideEquiv`) and a gadget's
  correctness can be stated on *single* graphs instead of twice over, once per
  side. `DescriptiveComplexity.TwoCopies` is the other half of that layer: the
  vocabulary `FirstOrder.Language.twoCopies L₁` – two marks and two copies of
  every symbol of `L₁` – together with the problem
  `DescriptiveComplexity.TwoCopiesIso` asking whether the two marked
  `L₁`-structures of an instance are isomorphic. A gadget can be *doubled* – run
  relativized to each mark – only against a target of that shape, the defining
  formulas having to be given symbol by symbol; problems joining the degree from
  here on are meant to be stated over it.
  `DescriptiveComplexity.GadgetDouble` closes the layer: it doubles a gadget –
  a construction on *single* structures – by renaming its atoms to each side's
  copy and relativizing its quantifiers to that side's mark, and identifies the
  sides of the result (`DescriptiveComplexity.patSideDoubleEquiv`: the pattern
  side of the doubled gadget is the gadget on the pattern side). What a client
  then owes is `DescriptiveComplexity.IsoReflecting`, “isomorphic values come
  from isomorphic arguments”, a statement about single structures with no
  pattern/host distinction in it; the converse is free by functoriality, and
  `DescriptiveComplexity.isoReflecting_fo_reduction` turns the pair into an
  order-free reduction.

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
  The source vocabulary is relational, as every vocabulary of a
  `DescriptiveComplexity.DecisionProblem` is.

  The **halting problem** (`DescriptiveComplexity.HALT`) is the same machine data
  as the NP and PSPACE bridges with *both* bounds dropped: the tape is an
  unbounded strip of pages, each a copy of the instance's positions, so no
  arithmetic enters the model and the input needs no placement. It is in RE
  (`DescriptiveComplexity.halt_mem_RE`) because a run – finite, but bounded by no
  function of the instance – is exactly what value invention guesses; and since
  FINSAT is already RE-hard, that yields
  `DescriptiveComplexity.halt_le_finsat` at once: the halting problem
  first-order-reduces to finite satisfiability, which is Trakhtenbrot's theorem in
  the form it is usually stated. RE-*hardness* of `HALT`
  (`DescriptiveComplexity.halt_RE_hard`, whence
  `DescriptiveComplexity.halt_RE_complete`) is the machine bridge: the
  reduction draws a **fixed** simulating machine – its states, symbols and
  transitions are tags, free at every instance size – and spells the
  instance's own relation tables as a chain of one-bit `comp` frames on the
  initial tape, folded at run time into the one number that a semi-decision
  code – named by `Turing.ToPartrec.Code.exists_code`, never built – decodes
  back into the instance. The simulation of the code model on one unbounded
  tape is a string-rewriting argument against the same configuration-word
  layer the PCP reduction uses, so the tape-function bookkeeping is paid for
  once (`DescriptiveComplexity.Problems.Machine.HaltHard`).

  **Post's correspondence problem** (`DescriptiveComplexity.PCP`,
  [Post 1946][post1946variant]) has the same membership half
  (`DescriptiveComplexity.pcp_mem_RE`, whence
  `DescriptiveComplexity.pcp_le_finsat`): a match is a nonempty sequence of
  marked dominoes whose top words and bottom words have the same concatenation,
  the words of a domino being its letters read in the order the instance
  carries on their positions. It is the first catalog problem whose certificate
  is a *sequence* rather than a structure, and the common word it spells is
  **never invented**: its letters are indexed by the pairs (slot, position of
  the word sitting there) in lexicographic order, once for each of the two
  parses, and what the certificate carries is a **matching** between the two
  index lists. A first-order kernel can ask of a relation variable only that it
  land in the two parses, be defined everywhere on both, reflect the two orders
  and preserve letters, and that is already enough
  (`DescriptiveComplexity.Pcp.forall₂_of_matching`): such a relation pairs the
  entries of two strictly sorted lists index by index, so the two
  concatenations agree letter by letter.

  Being a sequence is also why `PCP` is not a second syntactic image:
  RE-*hardness* is the classical computation-history construction
  (`DescriptiveComplexity.halt_ordered_fo_reduction_pcp`). A `HALT` instance
  carries its transitions as elements, so the interpretation emits one
  decorated domino per transition-attribute tuple – the words are data, read
  off one shared table – plus a start domino spelling the initial
  configuration, and a match is exactly a halting derivation of the machine's
  rewriting system. With `HALT` RE-hard this makes PCP **RE-complete**
  (`DescriptiveComplexity.pcp_RE_complete`) and Post's problem undecidable
  (`DescriptiveComplexity.pcp_not_computable`).

  **CODEHALT** (`DescriptiveComplexity.Problems.CodeHalt`) – does the
  `Nat.Partrec.Code` drawn as the syntax tree of the instance halt on `0`? – is
  **RE-complete** (`DescriptiveComplexity.codehalt_RE_complete`), and its
  hardness proof is general enough to give the identity of the class with its
  machine reading: `DescriptiveComplexity.mem_RE_iff_rePred`, a problem is in
  RE exactly when its concrete instances are semi-decidable. The reduction
  writes the instance *as a program*: the root of the drawn code is
  `comp cP (pair numeral nest)`, where `cP` is a code semi-deciding the source
  problem – supplied by `Nat.Partrec.Code.exists_code`, never built – and the
  rest is a constant that first-order formulas can draw. Since every branch is
  evaluated at input `0`, a constant is a tree of `pair`, `succ` and `zero`
  nodes, so a bit of the input instance is *one node*, and the table is nested
  by coordinate rather than numbered in a mixed radix: each level of the nest
  is then a plain walk of the input order, which is what a first-order guard
  can describe, and no arithmetic on positions appears anywhere. The two
  shared leaves `succ` and `zero` let a bit be read as an *edge* of the
  drawing rather than as a mark, so every element has exactly one constructor
  and the drawing is well formed by inspection. Three headlines come out of
  the one construction: RE-completeness of `CODEHALT`, `RE = REPred`, and –
  with Post's theorem and the undecidability of `CODEHALT` –
  `DescriptiveComplexity.RE_ne_coRE`.

## Worked examples

* `DescriptiveComplexity.Examples` – tutorial-style, domain-specific
  walkthroughs of the full recipe (vocabulary → semantics → invariance →
  membership → hardness → completeness). Currently Boolean conjunctive
  queries – evaluation and containment, both NP-complete via Chandra–Merlin
  ([Chandra & Merlin 1977][chandra1977optimal]).
-/
