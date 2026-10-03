/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Computability.Vocab
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

namespace Lax624099Proofs.Foreign.FirstOrder.Language
end Lax624099Proofs.Foreign.FirstOrder.Language

namespace Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct
end Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct

/-!
# Evaluating a formula on a concrete structure is primitive recursive

The engine of the bridge: for every *fixed* first-order formula `φ` over a
finitely presented relational vocabulary, the function

```
(concrete structure, valuation) ↦ does φ hold?
```

is primitive recursive (`FirstOrder.Language.FinStruct.primrec_evalBF`) and
computes satisfaction (`FirstOrder.Language.FinStruct.evalBF_iff`).

Everything downstream is an application: an `∃SO[new]` definition becomes an
unbounded search whose test is this evaluation
(`Lax624099Proofs.DescriptiveComplexity.RE_subset_rePred`), and a first-order interpretation
becomes a computable map of concrete structures, because its image relations
*are* evaluations of fixed formulas.

## Why an explicit Boolean evaluator

`FirstOrder.Language.BoundedFormula.decidableRealize` already decides
satisfaction, but `Primrec` is a statement about a function, not about a
`Decidable` instance, and the quantifier case of that instance goes through
`Fintype.decidableForallFintype`, which is not in a shape any `Primrec`
combinator matches. `evalBF` is the same recursion written so that each case
*is* a combinator application: a list lookup for an atom, a Boolean
combinator for an implication, and a conjunction over `List.range` for a
quantifier.

Valuations are `List ℕ` – the values of the bound variables, in de Bruijn
order – rather than `Fin l → Univ`: a dependent function type would be
encoded, at every recursive call, into exactly this list.
-/

namespace FirstOrder

namespace Language

open Structure

/-! ### Two primitive recursive helpers -/

section Helpers

/-- The conjunction of a list of Booleans. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.andAll (l : List Bool) : Bool := l.foldr (· && ·) true

export Lax624099Proofs.Foreign.FirstOrder.Language (andAll)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.andAll_nil : Lax624099Proofs.Foreign.FirstOrder.Language.andAll [] = true := rfl

export Lax624099Proofs.Foreign.FirstOrder.Language (andAll_nil)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.andAll_cons (b : Bool) (l : List Bool) : Lax624099Proofs.Foreign.FirstOrder.Language.andAll (b :: l) = (b && Lax624099Proofs.Foreign.FirstOrder.Language.andAll l) := rfl

export Lax624099Proofs.Foreign.FirstOrder.Language (andAll_cons)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.andAll_eq_true {l : List Bool} : Lax624099Proofs.Foreign.FirstOrder.Language.andAll l = true ↔ ∀ b ∈ l, b = true := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

export Lax624099Proofs.Foreign.FirstOrder.Language (andAll_eq_true)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.primrec_andAll : Primrec Lax624099Proofs.Foreign.FirstOrder.Language.andAll :=
  (Primrec.list_foldr Primrec.id (Primrec.const true)
    (Primrec.and.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

export Lax624099Proofs.Foreign.FirstOrder.Language (primrec_andAll)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_eq_foldr (c : ℕ) (l : List ℕ) :
    Lax624099.ConcreteInstances.tupleIdx c l = l.foldr (fun a r => a + c * r) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_cons, ih]

export Lax624099Proofs.Foreign.FirstOrder.Language (tupleIdx_eq_foldr)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.primrec_tupleIdx : Primrec₂ Lax624099.ConcreteInstances.tupleIdx :=
  (Primrec.list_foldr Primrec.snd (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))).to₂).of_eq
    fun p => (Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_eq_foldr p.1 p.2).symm

export Lax624099Proofs.Foreign.FirstOrder.Language (primrec_tupleIdx)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.primrec_pow_const (j : ℕ) : Primrec fun c : ℕ => c ^ j := by
  induction j with
  | zero => simpa using Primrec.const 1
  | succ j ih => simpa [pow_succ] using Primrec.nat_mul.comp ih Primrec.id

export Lax624099Proofs.Foreign.FirstOrder.Language (primrec_pow_const)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.primrec_digitAt (j : ℕ) : Primrec₂ fun c t : ℕ => Lax624099.ConcreteInstances.digitAt c t j :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp Primrec.snd ((Lax624099Proofs.Foreign.FirstOrder.Language.primrec_pow_const j).comp Primrec.fst)) Primrec.fst

export Lax624099Proofs.Foreign.FirstOrder.Language (primrec_digitAt)

end Helpers

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

/-! ### Valuations as lists -/

/-- The value of the `i`-th bound variable, as a number: out-of-range
variables read `0`, and the reduction modulo the size of the universe makes
the reading total. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat (s : Lax624099.ConcreteInstances.FinStruct V) (xs : List ℕ) (i : ℕ) : ℕ := xs.getD i 0 % s.card

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (valNat)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (valNat)

/-- The value of the `i`-th bound variable, as an element of the universe. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf (s : Lax624099.ConcreteInstances.FinStruct V) (xs : List ℕ) (i : ℕ) : s.Univ :=
  ⟨Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat s xs i, Nat.mod_lt _ (Nat.succ_pos _)⟩

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (valOf)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (valOf)

omit [L.IsRelational] in
@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.val_valOf (s : Lax624099.ConcreteInstances.FinStruct V) (xs : List ℕ) (i : ℕ) :
    (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf s xs i : ℕ) = Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat s xs i := rfl

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (val_valOf)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (val_valOf)

omit [L.IsRelational] in
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_valNat (V : Lax624099.ConcreteInstances.FinVocab L) (k : ℕ) :
    Primrec fun p : Lax624099.ConcreteInstances.FinStruct V × List ℕ => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat p.1 p.2 k :=
  Primrec.nat_mod.comp ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const k))
    ((Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_card V).comp Primrec.fst)

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_valNat)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_valNat)

omit [L.IsRelational] in
/-- Appending a value to a valuation is `Fin.snoc` on the elements it
denotes. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf_append {l : ℕ} (s : Lax624099.ConcreteInstances.FinStruct V) (xs : List ℕ) (hlen : xs.length = l)
    (y : s.Univ) :
    (fun i : Fin (l + 1) => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf s (xs ++ [(y : ℕ)]) i) =
      Fin.snoc (fun i : Fin l => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf s xs i) y := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
    refine Fin.ext ?_
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.val_valOf, Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat, Fin.val_last]
    have : (xs ++ [(y : ℕ)]).getD l 0 = (y : ℕ) := by
      rw [← hlen]
      simp [List.getD_eq_getElem?_getD]
    rw [this, Nat.mod_eq_of_lt y.isLt]
  · intro j
    rw [Fin.snoc_castSucc]
    refine Fin.ext ?_
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.val_valOf, Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat, Fin.val_castSucc]
    have hj : (j : ℕ) < xs.length := by rw [hlen]; exact j.isLt
    have hgd : (xs ++ [(y : ℕ)]).getD (j : ℕ) 0 = xs.getD (j : ℕ) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    rw [hgd]

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (valOf_append)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (valOf_append)

/-! ### Terms

Over a relational vocabulary a term is a variable, so its value is the value
of a bound variable whose *number is fixed by the term*: nothing about a term
has to be computed at run time. -/

/-- The number of the bound variable a term is. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.termIdx {l : ℕ} : L.Term (Empty ⊕ Fin l) → ℕ
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr i) => (i : ℕ)
  | .func f _ => isEmptyElim f

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (termIdx)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (termIdx)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.realize_term {l : ℕ} (s : Lax624099.ConcreteInstances.FinStruct V) (xs : List ℕ) (t : L.Term (Empty ⊕ Fin l)) :
    t.realize (Sum.elim Empty.elim fun i : Fin l => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf s xs i) = Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf s xs (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.termIdx t) := by
  match t with
  | .var (Sum.inl e) => exact e.elim
  | .var (Sum.inr _) => rfl
  | .func f _ => exact isEmptyElim f

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (realize_term)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (realize_term)

/-! ### The evaluator -/

/-- **The Boolean evaluator**: the recursion on the formula that
`FirstOrder.Language.FinStruct.primrec_evalBF` shows to be primitive recursive
and `FirstOrder.Language.FinStruct.evalBF_iff` shows to compute satisfaction.

An atom is a lookup in the table of the instance, at the number of the tuple
of values; a quantifier is a conjunction over `List.range card`, the values a
variable can take. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF (V : Lax624099.ConcreteInstances.FinVocab L) : ∀ {l : ℕ}, L.BoundedFormula Empty l → Lax624099.ConcreteInstances.FinStruct V → List ℕ → Bool
  | _, .falsum, _, _ => false
  | _, .equal t₁ t₂, s, xs => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat s xs (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.termIdx t₁) == Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat s xs (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.termIdx t₂)
  | _, .rel R ts, s, xs =>
      (s.table.getD (V.index R) []).getD
        (Lax624099.ConcreteInstances.tupleIdx s.card (List.ofFn fun i => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valNat s xs (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.termIdx (ts i)))) false
  | _, .imp φ ψ, s, xs => !Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF V φ s xs || Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF V ψ s xs
  | _, .all φ, s, xs => Lax624099Proofs.Foreign.FirstOrder.Language.andAll ((List.range s.card).map fun x => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF V φ s (xs ++ [x]))

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (evalBF)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (evalBF)

/-- **The evaluator computes satisfaction.** -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF_iff (V : Lax624099.ConcreteInstances.FinVocab L) : ∀ {l : ℕ} (φ : L.BoundedFormula Empty l)
    (s : Lax624099.ConcreteInstances.FinStruct V) (xs : List ℕ), xs.length = l →
      (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF V φ s xs = true ↔ φ.Realize Empty.elim fun i : Fin l => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf s xs i)
  | _, .falsum, _, _, _ => by simp [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF, BoundedFormula.Realize]
  | _, .equal t₁ t₂, s, xs, _ => by
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF, beq_iff_eq, BoundedFormula.Realize, Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.realize_term]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  | _, .rel R ts, s, xs, _ => by
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF, BoundedFormula.Realize]
    rw [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.relMap_iff, Lax624099.ConcreteInstances.FinStruct.relMapBool]
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.realize_term, Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.val_valOf]
  | _, .imp φ ψ, s, xs, hlen => by
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF, BoundedFormula.Realize, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    rw [← Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF_iff V φ s xs hlen, ← Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF_iff V ψ s xs hlen]
    cases Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF V φ s xs <;> simp
  | _, .all φ, s, xs, hlen => by
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF, BoundedFormula.Realize, Lax624099Proofs.Foreign.FirstOrder.Language.andAll_eq_true, List.mem_map, List.mem_range]
    constructor
    · intro h y
      have := h _ ⟨(y : ℕ), y.isLt, rfl⟩
      rw [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF_iff V φ s (xs ++ [(y : ℕ)]) (by simp [hlen])] at this
      rwa [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf_append s xs hlen y] at this
    · rintro h b ⟨y, hy, rfl⟩
      have := h ⟨y, hy⟩
      rw [← Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.valOf_append s xs hlen ⟨y, hy⟩] at this
      exact (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF_iff V φ s (xs ++ [y]) (by simp [hlen])).mpr this

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (evalBF_iff)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (evalBF_iff)

/-- **The evaluator is primitive recursive**, uniformly in the instance and
the valuation, for each fixed formula. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_evalBF (V : Lax624099.ConcreteInstances.FinVocab L) : ∀ {l : ℕ} (φ : L.BoundedFormula Empty l),
    Primrec fun p : Lax624099.ConcreteInstances.FinStruct V × List ℕ => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF V φ p.1 p.2
  | _, .falsum => (Primrec.const false).of_eq fun _ => rfl
  | _, .equal t₁ t₂ =>
      (Primrec.beq.comp (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_valNat V (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.termIdx t₁)) (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_valNat V (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.termIdx t₂))).of_eq
        fun _ => rfl
  | _, .rel R ts =>
      ((Primrec.list_getD false).comp
        ((Primrec.list_getD []).comp ((Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_table V).comp Primrec.fst)
          (Primrec.const (V.index R : ℕ)))
        (Lax624099Proofs.Foreign.FirstOrder.Language.primrec_tupleIdx.comp ((Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_card V).comp Primrec.fst)
          (Primrec.list_ofFn fun i => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_valNat V (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.termIdx (ts i))))).of_eq fun _ => rfl
  | _, .imp φ ψ =>
      (Primrec.or.comp (Primrec.not.comp (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_evalBF V φ)) (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_evalBF V ψ)).of_eq
        fun _ => rfl
  | _, .all φ =>
      (Lax624099Proofs.Foreign.FirstOrder.Language.primrec_andAll.comp
        (Primrec.list_map (Primrec.list_range.comp ((Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_card V).comp Primrec.fst))
          (((Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_evalBF V φ).comp
            ((Primrec.fst.comp Primrec.fst).pair
              (Primrec.list_concat.comp (Primrec.snd.comp Primrec.fst)
                Primrec.snd))).to₂))).of_eq fun _ => rfl

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_evalBF)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_evalBF)

/-! ### Sentences

A sentence is the case `l = 0` of the evaluator, with the empty valuation. -/

/-- Deciding a fixed sentence on a concrete structure is primitive recursive. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_evalSentence (V : Lax624099.ConcreteInstances.FinVocab L) (φ : L.Sentence) :
    Primrec fun s : Lax624099.ConcreteInstances.FinStruct V => Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF V φ s [] :=
  (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_evalBF V φ).comp (Primrec.id.pair (Primrec.const []))

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_evalSentence)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_evalSentence)

/-- The evaluator decides a sentence. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalSentence_iff (V : Lax624099.ConcreteInstances.FinVocab L) (φ : L.Sentence) (s : Lax624099.ConcreteInstances.FinStruct V) :
    evalBF V φ s [] = true ↔ φ.Realize s.Univ := by
  refine Iff.trans (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.evalBF_iff V φ s [] rfl) (iff_of_eq ?_)
  refine congrArg₂ (fun (v : Empty → s.Univ) (xs : Fin 0 → s.Univ) =>
    BoundedFormula.Realize φ v xs) ?_ ?_
  · exact funext fun e => e.elim
  · exact funext fun i => Fin.elim0 i

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (evalSentence_iff)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (evalSentence_iff)

end FinStruct

end Language

end FirstOrder


