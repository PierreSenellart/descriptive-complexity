/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Computability.REPred
import DescriptiveComplexity.Computability.Reduction
import DescriptiveComplexity.Problems.Machine
import DescriptiveComplexity.Problems.Machine.HaltMem
import DescriptiveComplexity.Problems.FinSat

/-!
# The catalog's vocabularies, presented

The vocabularies of the two problems the machine bridge is about, exhibited as
`FirstOrder.Language.FinVocab`s, and the concrete reading of
`DescriptiveComplexity.RE_subset_rePred` at them:

* `DescriptiveComplexity.halt_rePred` – the halting problem, as a set of
  concrete machine instances, is recursively enumerable in Mathlib's sense;
* `DescriptiveComplexity.finsat_rePred` – likewise for finite satisfiability.

Both are instances of one theorem and neither needs anything problem-specific
beyond listing the symbols of the vocabulary: this is the point of encoding
structures once for the catalog rather than once per problem.

Neither statement says *undecidable*. That reading needs one more thing, and
exactly one: a computable map of a known-undecidable set into concrete machine
instances (`ROADMAP.md` §8, not built). Everything that would follow from it is
here – `DescriptiveComplexity.finsat_not_computable_of_halt` is Trakhtenbrot's
theorem waiting on that single hypothesis.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

instance : DecidableEq ((n : ℕ) × Language.turing.Relations n) :=
  inferInstanceAs (DecidableEq ((n : ℕ) × turingRel n))

instance : DecidableEq ((n : ℕ) × Language.finsat.Relations n) :=
  inferInstanceAs (DecidableEq ((n : ℕ) × finsatRel n))

/-- **The vocabulary of machine instances, presented**: twelve symbols, six
unary and six binary. -/
def turingVocab : FinVocab Language.turing :=
  FinVocab.ofList
    [⟨1, .posn⟩, ⟨1, .tr⟩, ⟨1, .start⟩, ⟨1, .acc⟩, ⟨1, .blank⟩, ⟨1, .right⟩,
      ⟨2, .le⟩, ⟨2, .tsrc⟩, ⟨2, .tread⟩, ⟨2, .tdst⟩, ⟨2, .twrite⟩, ⟨2, .inp⟩]
    (by decide) (by rintro ⟨n, R⟩; cases R <;> simp)

/-- **The vocabulary of first-order sentences as instances, presented**:
fourteen symbols of arity at most three. -/
def finsatVocab : FinVocab Language.finsat :=
  FinVocab.ofList
    [⟨2, .le⟩, ⟨1, .andN⟩, ⟨1, .orN⟩, ⟨1, .allN⟩, ⟨1, .exN⟩, ⟨2, .child⟩,
      ⟨2, .bind⟩, ⟨3, .eqL⟩, ⟨3, .neqL⟩, ⟨2, .posL⟩, ⟨2, .negL⟩, ⟨3, .arg⟩,
      ⟨2, .sig⟩, ⟨1, .root⟩]
    (by decide) (by rintro ⟨n, R⟩; cases R <;> simp)

/-- **The halting problem is recursively enumerable** in Mathlib's sense, on
the concrete machine instances of `FirstOrder.Language.FinStruct`.

This is `DescriptiveComplexity.halt_mem_RE` – a purely logical statement, an
`∃SO[new]` definition of acceptance – read through the encoding, with no
machine model on either side. -/
theorem halt_rePred : REPred (HALT.toPred turingVocab) :=
  RE_subset_rePred turingVocab HALT halt_mem_RE

/-- **Finite satisfiability is recursively enumerable** in Mathlib's sense: the
easy half of Trakhtenbrot's theorem, on concrete instances. -/
theorem finsat_rePred : REPred (FINSAT.toPred finsatVocab) :=
  RE_subset_rePred finsatVocab FINSAT finsat_mem_RE

/-- **Trakhtenbrot's theorem, waiting on the halting link**: if the halting
problem is undecidable *as a set of concrete machine instances*, then finite
satisfiability is undecidable too.

The reduction is `DescriptiveComplexity.halt_le_finsat`, which exists because
FINSAT is RE-hard and `HALT` is in RE; that it is a *computable* many-one
reduction of the induced sets is
`DescriptiveComplexity.not_computablePred_of_relOrderedReduction`. The
hypothesis is the one thing the bridge still lacks, and it is about Mathlib's
halting problem, not about this library. -/
theorem finsat_not_computable_of_halt (h : ¬ComputablePred (HALT.toPred turingVocab)) :
    ¬ComputablePred (FINSAT.toPred finsatVocab) :=
  halt_le_finsat.elim fun f =>
    not_computablePred_of_relOrderedReduction f turingVocab finsatVocab h

end DescriptiveComplexity
