# First-order reductions in Lean 4

Machine-model-free hardness reductions on top of Mathlib's `ModelTheory`
library, in the style of descriptive complexity (Immerman, *Descriptive
Complexity*, ch. 3).

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

## Contents

* `FOReduction/Interpretation.lean` — the framework:
  - `FirstOrder.StructureProp L`: a decision problem as a property of
    `L`-structures;
  - `FirstOrder.FOInterpretation L L' Tag dim`: tagged `dim`-dimensional
    first-order interpretations of a relational language `L'` in `L`, sending
    an `L`-structure `A` to an `L'`-structure `I.Map A` on `Tag × A^dim`
    (tags replace the linear order used by textbook FO reductions to encode
    constantly many sorts of elements);
  - `FirstOrder.FOInterpretation.IsQuantifierFree`: quantifier-free
    interpretations;
  - `FirstOrder.FOReduction P Q`: FO reductions between problems, i.e.
    interpretations mapping yes-instances exactly to yes-instances;
  - `FirstOrder.FOInterpretation.map_finite`: finite structures map to finite
    structures.
* `FOReduction/Problems.lean` — the problems:
  - the language `FirstOrder.Language.sat` of CNF instances (`isClause`,
    `posIn`, `negIn`) and satisfiability `FirstOrder.SatSatisfiable`;
  - 3-colorability `FirstOrder.ThreeColorableStructure` over Mathlib's
    `FirstOrder.Language.graph`, shown to agree with Mathlib's
    `SimpleGraph.Colorable 3` on simple graphs.
* `FOReduction/ThreeColToSat.lean` — the reduction 3COL ⟶ SAT:
  - `FirstOrder.colToSat`: the classical CNF encoding of 3-colorability
    (variables `xᵤᵢ` "vertex `u` gets color `i`"; per-vertex clauses
    `xᵤ₀ ∨ xᵤ₁ ∨ xᵤ₂`; per-edge, per-color clauses `¬xᵤᵢ ∨ ¬xᵥᵢ`) as a
    2-dimensional interpretation with 7 tags;
  - `FirstOrder.threeColorableStructure_iff_satSatisfiable`: correctness, for
    arbitrary (not necessarily finite, simple or undirected) graph
    structures;
  - `FirstOrder.threeCol_fo_reduction_sat : FOReduction ThreeCol SAT` — the
    `fo_reduction` theorem;
  - `FirstOrder.colToSat_isQuantifierFree`: the reduction is even
    quantifier-free;
  - `FirstOrder.SimpleGraph.colorable_iff_satSatisfiable`: the corollary for
    Mathlib simple graphs.

## Notes

* The reduction direction 3COL → SAT is the "encode into SAT" direction
  (what SAT solvers do); combined with NP-hardness of 3COL it transfers
  hardness to SAT. The gadget direction SAT → 3COL is *not* FO-expressible
  without a linear order on the input structure (clauses of unbounded width
  require an ordered traversal), which is why the SAT-solver direction is the
  natural first target; supporting ordered structures (and `BIT`), under
  which SAT is complete for NP under FO reductions (Immerman), is the natural
  next step, along with composition of FO reductions and further reductions
  (e.g. 3COL → k-COL, CLIQUE ↔ INDEPENDENT-SET).
* Junk elements of the interpreted universe (tags with non-diagonal or
  non-edge tuples) are excluded from all relations by the defining formulas,
  so no domain formula is needed.

## Building

```
lake exe cache get   # fetch Mathlib build cache
lake build
```
