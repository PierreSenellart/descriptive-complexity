/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Lax624099Proofs.DescriptiveComplexity.Computability.FinStruct
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab
end Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab

/-!
# Presenting vocabularies as data

Ways of exhibiting a `FirstOrder.Language.FinVocab`, the finite presentation
of a relational vocabulary that `FirstOrder.Language.FinStruct` encodes
structures over.

A presentation is exactly a numbering of the symbols, i.e., an equivalence

```
Fin numSyms ≃ ((n : ℕ) × L.Relations n)
```

(`FirstOrder.Language.FinVocab.symEquiv` and
`FirstOrder.Language.FinVocab.ofEquivSigma` are mutually inverse constructions),
so a presentation can be built from any such numbering: from a duplicate-free
list of all the symbols (`FirstOrder.Language.FinVocab.ofList`, the way every
vocabulary of the catalog is presented), or by combining two presentations
(`FirstOrder.Language.FinVocab.sum`).

The sum is what makes the whole development go through: the vocabularies of
the second-order machinery are sums of an instance's vocabulary with a
quantifier block's, and everything about them is encoded by the same means as
an ordinary instance.
-/

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

/-- **A presentation is a numbering of the symbols.** -/
@[simps]
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.symEquiv (V : Lax624099.ConcreteInstances.FinVocab L) : Fin V.numSyms ≃ ((n : ℕ) × L.Relations n) where
  toFun := V.symOf
  invFun p := V.index p.2
  left_inv := V.index_symOf
  right_inv p := V.symOf_index p.2

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (symEquiv symEquiv_apply)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (symEquiv)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.numSyms_ofEquivSigma (k : ℕ) (e : Fin k ≃ ((n : ℕ) × L.Relations n)) :
    (Lax624099.ConcreteInstances.FinVocab.ofEquivSigma k e).numSyms = k := rfl

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (numSyms_ofEquivSigma)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (numSyms_ofEquivSigma)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.symOf_ofEquivSigma (k : ℕ) (e : Fin k ≃ ((n : ℕ) × L.Relations n))
    (i : Fin k) : (Lax624099.ConcreteInstances.FinVocab.ofEquivSigma k e).symOf i = e i := rfl

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (symOf_ofEquivSigma)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (symOf_ofEquivSigma)

/-- **Presentations combine along `Language.sum`**: a symbol of the sum
vocabulary is a symbol of one side or of the other. This is what lets the
vocabularies of the second-order machinery – an instance's vocabulary summed
with a quantifier block's – be encoded like any other. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.sum (V : Lax624099.ConcreteInstances.FinVocab L) (W : Lax624099.ConcreteInstances.FinVocab L') : Lax624099.ConcreteInstances.FinVocab (L.sum L') where
  numSyms := V.numSyms + W.numSyms
  symOf i := Fin.addCases (motive := fun _ => (n : ℕ) × (L.sum L').Relations n)
    (fun j => ⟨(V.symOf j).1, Sum.inl (V.symOf j).2⟩)
    (fun j => ⟨(W.symOf j).1, Sum.inr (W.symOf j).2⟩) i
  index R := Sum.elim (fun r => Fin.castAdd _ (V.index r)) (fun r => Fin.natAdd _ (W.index r)) R
  symOf_index R := by
    cases R with
    | inl r => simpa using congrArg (fun p : (n : ℕ) × L.Relations n => (⟨p.1, Sum.inl p.2⟩ :
        (n : ℕ) × (L.sum L').Relations n)) (V.symOf_index r)
    | inr r => simpa using congrArg (fun p : (n : ℕ) × L'.Relations n => (⟨p.1, Sum.inr p.2⟩ :
        (n : ℕ) × (L.sum L').Relations n)) (W.symOf_index r)
  index_symOf i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left]
      exact congrArg (Fin.castAdd W.numSyms) (V.index_symOf j)
    · rw [Fin.addCases_right]
      exact congrArg (Fin.natAdd V.numSyms) (W.index_symOf j)

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (sum)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (sum)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.numSyms_sum (V : Lax624099.ConcreteInstances.FinVocab L) (W : Lax624099.ConcreteInstances.FinVocab L') :
    (V.sum W).numSyms = V.numSyms + W.numSyms := rfl

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (numSyms_sum)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (numSyms_sum)

/-- **The numbering of a sum vocabulary**: the symbols of the left summand keep
their numbers, those of the right summand are shifted past them. This is the
only fact about `FirstOrder.Language.FinVocab.sum` anything downstream uses –
it is what fixes the layout of the table of an encoded structure. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.index_sum_inl (V : Lax624099.ConcreteInstances.FinVocab L) (W : Lax624099.ConcreteInstances.FinVocab L') {n : ℕ} (r : L.Relations n) :
    (V.sum W).index (Sum.inl r) = Fin.castAdd W.numSyms (V.index r) := rfl

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (index_sum_inl)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (index_sum_inl)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.index_sum_inr (V : Lax624099.ConcreteInstances.FinVocab L) (W : Lax624099.ConcreteInstances.FinVocab L') {n : ℕ} (r : L'.Relations n) :
    (V.sum W).index (Sum.inr r) = Fin.natAdd V.numSyms (W.index r) := rfl

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (index_sum_inr)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (index_sum_inr)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.val_index_sum_inl (V : Lax624099.ConcreteInstances.FinVocab L) (W : Lax624099.ConcreteInstances.FinVocab L') {n : ℕ}
    (r : L.Relations n) : (((V.sum W).index (Sum.inl r) : Fin _) : ℕ) = (V.index r : ℕ) := by
  rw [Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.index_sum_inl]; rfl

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (val_index_sum_inl)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (val_index_sum_inl)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.val_index_sum_inr (V : Lax624099.ConcreteInstances.FinVocab L) (W : Lax624099.ConcreteInstances.FinVocab L') {n : ℕ}
    (r : L'.Relations n) :
    (((V.sum W).index (Sum.inr r) : Fin _) : ℕ) = V.numSyms + (W.index r : ℕ) := by
  rw [Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.index_sum_inr]; rfl

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (val_index_sum_inr)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (val_index_sum_inr)

end FinVocab

end Language

end FirstOrder


