# DescriptiveComplexity

A Lean 4 library for descriptive complexity on top of Mathlib's
`ModelTheory` library: machine-model-free hardness reductions in the style
of Immerman (*Descriptive Complexity*, ch. 3). All declarations live in the
`DescriptiveComplexity` namespace; the top-level module is
`DescriptiveComplexity`.

Complexity theory is essentially absent from Lean/Mathlib because formalizing
a model of computation with resource bounds is hard. But many classical
NP-hardness reductions do not need the full power of PTIME: they are
*first-order expressible*. An FO reduction is computable in AC⁰ ⊆ LOGSPACE ⊆
PTIME, so exhibiting one is strictly stronger than exhibiting a Karp
reduction, while requiring no machine model at all: only first-order logic,
which Mathlib already has.

As far as we know this is the first use of FO-expressible reductions in a
proof assistant (the closest prior work is the "cookbook reductions" of
Grange, Vehlken, Vortmeier and Zeume, MFCS 2024, which uses FO-definable
reductions in an automated-verification/teaching setting, not an ITP).

Both directions between SAT and 3-colorability are formalized: an order-free,
quantifier-free reduction 3COL → SAT, and an ordered FO reduction SAT → 3COL
(the classical gadget construction, which genuinely needs a linear order on
the input structure to thread each clause's OR-gadget chain). SAT and
3-colorability are thus FO-interreducible.

## Contents

* `DescriptiveComplexity/Interpretation.lean` — the framework:
  - `DescriptiveComplexity.DecisionProblem L`: a decision problem as an
    isomorphism-invariant property of `L`-structures (invariance is part of
    the notion, as in descriptive complexity);
  - `DescriptiveComplexity.FOInterpretation L L' Tag dim`: tagged `dim`-dimensional
    first-order interpretations of a relational language `L'` in `L`, sending
    an `L`-structure `A` to an `L'`-structure `I.Map A` on `Tag × A^dim`
    (tags replace the linear order used by textbook FO reductions to encode
    constantly many sorts of elements);
  - `DescriptiveComplexity.FOInterpretation.IsQuantifierFree`: quantifier-free
    interpretations;
  - `DescriptiveComplexity.FOReduction P Q`, with notation `P ≤ᶠᵒ Q`: FO reductions
    between problems, i.e. interpretations mapping yes-instances exactly to
    yes-instances;
  - `DescriptiveComplexity.FOInterpretation.map_finite`: finite structures map to finite
    structures.
* `DescriptiveComplexity/Problems/` — the problem catalog, one file (or directory) per
  problem, each holding vocabulary, semantic definition, the bundled
  `DecisionProblem`, its FO reductions and its completeness theorems
  (`DescriptiveComplexity/Problems.lean` is the umbrella):
  - `Problems/Sat.lean`: the language `FirstOrder.Language.sat` of CNF
    instances (`isClause`, `posIn`, `negIn`), satisfiability
    `DescriptiveComplexity.Satisfiable`, the problem `DescriptiveComplexity.SAT`, and the
    Cook–Levin theorem `DescriptiveComplexity.SAT_NP_complete` with its corollaries
    (`sat_mem_NP`, `sat_NP_hard`, `sat_compl_mem_coNP`);
  - `Problems/ThreeColorability/Defs.lean`: 3-colorability
    `DescriptiveComplexity.ThreeColorable` over Mathlib's `FirstOrder.Language.graph`
    and the problem `DescriptiveComplexity.ThreeCol`, shown to agree with Mathlib's
    `SimpleGraph.Colorable 3` on simple graphs.
* `DescriptiveComplexity/Composition.lean` — transitivity:
  - `DescriptiveComplexity.FOInterpretation.pull`: pullback of a formula through an
    interpretation (quantifiers over the interpreted universe become finite
    conjunctions over tags of blocks of quantifiers);
  - `DescriptiveComplexity.FOInterpretation.comp`: composition of FO interpretations,
    with `compLEquiv` identifying the composite universe with the
    twice-interpreted one;
  - `DescriptiveComplexity.FOReduction.refl` and `DescriptiveComplexity.FOReduction.trans`:
    FO reducibility is reflexive (identity interpretation) and transitive,
    with a `Trans` instance for `calc` chains and a `Preorder` instance on
    `DecisionProblem L` (for relational `L`) where `P ≤ Q` is the
    propositional truncation `Nonempty (P ≤ᶠᵒ Q)`.
* `DescriptiveComplexity/Ordered.lean` — ordered machinery:
  - an `(L.sum Language.order).Structure` instance on linearly ordered
    `L`-structures, and `DescriptiveComplexity.OrderedFOReduction P Q`, with notation
    `P ≤ᶠᵒ[≤] Q`: FO reductions over the ordered expansion of the source
    language, correct for every finite linearly ordered input structure
    (i.e. order-invariant FO(≤) reductions, the standard notion of
    descriptive complexity).
* `DescriptiveComplexity/Problems/ThreeColorability/ToSat.lean` — the reduction
  3COL ⟶ SAT:
  - `DescriptiveComplexity.threeColToSat`: the classical CNF encoding of 3-colorability
    (variables `xᵤᵢ` "vertex `u` gets color `i`"; per-vertex clauses
    `xᵤ₀ ∨ xᵤ₁ ∨ xᵤ₂`; per-edge, per-color clauses `¬xᵤᵢ ∨ ¬xᵥᵢ`) as a
    2-dimensional interpretation with 7 tags;
  - `DescriptiveComplexity.threeColorable_iff_satisfiable`: correctness, for
    arbitrary (not necessarily finite, simple or undirected) graph
    structures;
  - `DescriptiveComplexity.threeCol_fo_reduction_sat : ThreeCol ≤ᶠᵒ SAT` — the
    `fo_reduction` theorem;
  - `DescriptiveComplexity.threeColToSat_isQuantifierFree`: the reduction is even
    quantifier-free;
  - `DescriptiveComplexity.SimpleGraph.colorable_iff_satisfiable`: the corollary for
    Mathlib simple graphs.
* `DescriptiveComplexity/Complexity.lean` — abstract complexity:
  - `DescriptiveComplexity.ComplexityClass`: abstract complexity classes (membership
    `P ∈ 𝒞`, hardness `𝒞.Hard P`, completeness `𝒞.Complete P`, inclusion
    `𝒞 ⊆ 𝒟`), closed by definition under (ordered) FO reductions — closure
    is part of the structure since an axiom over all classes would be
    inconsistent; membership and hardness moreover only depend on the
    *finite* instances of a problem (`mem_congr_finite`/`hard_congr_finite`),
    making explicit that complexity statements say nothing about infinite
    structures;
  - the polynomial hierarchy, *defined* by second-order quantifier
    alternation (`DescriptiveComplexity/Hierarchy.lean`): `SigmaP k`/`PiP k`
    for `k ≥ 1` with `NP := SigmaP 1` and `coNP := PiP 1`, the level
    inclusions, `Πₖᵖ` = complements (`Pᶜ`) of `Σₖᵖ`, and `PH`; level 0
    (polynomial time) is left as an empty placeholder class — no known
    order-free logic captures PTIME — so the library declares no axioms:
    `#print axioms` shows nothing beyond Lean's built-in `propext`,
    `Classical.choice` and `Quot.sound`;
  - the Cook–Levin theorem and per-problem completeness theorems live with
    their problems under `DescriptiveComplexity/Problems/`; in particular
    **`DescriptiveComplexity.threeCol_NP_complete : NP.Complete ThreeCol`**
    (`Problems/ThreeColorability.lean`) — NP-completeness of 3-colorability
    from the two FO reductions, with no machine model.
* `DescriptiveComplexity/OccurrenceOrder.lean`,
  `DescriptiveComplexity/Problems/ThreeColorability/SatGadget.lean`,
  `DescriptiveComplexity/Problems/ThreeColorability/FromSat.lean` — the reverse
  reduction SAT ⟶ 3COL:
  - literal occurrences of a clause and their traversal along the order
    (first/last occurrence, immediate predecessor), with existence lemmas on
    finite universes;
  - the gadget graph (palette triangle with copy-rigidity, literal vertices,
    per-occurrence OR-gate chains, unit-clause forcing, empty-clause
    spoiler) and the combinatorial proof
    `SatToCol.satisfiable_iff_gadColoring` that it is 3-colorable iff the
    CNF is satisfiable;
  - FO(≤) formulas defining the gadget graph, their realization lemmas, and
    `DescriptiveComplexity.sat_ordered_fo_reduction_threeCol : SAT ≤ᶠᵒ[≤] ThreeCol` —
    the reverse `fo_reduction` theorem.

## Notes

* The direction 3COL → SAT is order-free and even quantifier-free; the gadget
  direction SAT → 3COL is *not* FO-expressible without a linear order on the
  input structure (clauses of unbounded width require an ordered traversal),
  so it is formalized as an ordered (order-invariant) FO reduction, correct
  for every finite linearly ordered input. Natural next steps: a catalog of
  classical NP-complete problems with their FO reductions (3SAT, Vertex
  Cover, Clique, Independent Set, …), composition involving ordered
  reductions, and `BIT`/arithmetic on ordered structures (under which SAT is
  complete for NP under FO reductions, Immerman).
* Junk elements of the interpreted universe (tags with non-diagonal or
  non-edge tuples) are excluded from all relations by the defining formulas,
  so no domain formula is needed.

## Building

```
lake exe cache get   # fetch Mathlib build cache
lake build
```
