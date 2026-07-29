/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Computability.Vocab

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
(`DescriptiveComplexity.RE_subset_rePred`), and a first-order interpretation
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
def andAll (l : List Bool) : Bool := l.foldr (· && ·) true

@[simp] theorem andAll_nil : andAll [] = true := rfl

@[simp] theorem andAll_cons (b : Bool) (l : List Bool) : andAll (b :: l) = (b && andAll l) := rfl

theorem andAll_eq_true {l : List Bool} : andAll l = true ↔ ∀ b ∈ l, b = true := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem primrec_andAll : Primrec andAll :=
  (Primrec.list_foldr Primrec.id (Primrec.const true)
    (Primrec.and.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

theorem tupleIdx_eq_foldr (c : ℕ) (l : List ℕ) :
    tupleIdx c l = l.foldr (fun a r => a + c * r) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [tupleIdx_cons, ih]

theorem primrec_tupleIdx : Primrec₂ tupleIdx :=
  (Primrec.list_foldr Primrec.snd (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))).to₂).of_eq
    fun p => (tupleIdx_eq_foldr p.1 p.2).symm

theorem primrec_pow_const (j : ℕ) : Primrec fun c : ℕ => c ^ j := by
  induction j with
  | zero => simpa using Primrec.const 1
  | succ j ih => simpa [pow_succ] using Primrec.nat_mul.comp ih Primrec.id

theorem primrec_digitAt (j : ℕ) : Primrec₂ fun c t : ℕ => digitAt c t j :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp Primrec.snd ((primrec_pow_const j).comp Primrec.fst)) Primrec.fst

end Helpers

namespace FinStruct

variable {L : Language.{0, 0}} [L.IsRelational] {V : FinVocab L}

/-! ### Valuations as lists -/

/-- The value of the `i`-th bound variable, as a number: out-of-range
variables read `0`, and the reduction modulo the size of the universe makes
the reading total. -/
def valNat (s : FinStruct V) (xs : List ℕ) (i : ℕ) : ℕ := xs.getD i 0 % s.card

/-- The value of the `i`-th bound variable, as an element of the universe. -/
def valOf (s : FinStruct V) (xs : List ℕ) (i : ℕ) : s.Univ :=
  ⟨valNat s xs i, Nat.mod_lt _ (Nat.succ_pos _)⟩

omit [L.IsRelational] in
@[simp] theorem val_valOf (s : FinStruct V) (xs : List ℕ) (i : ℕ) :
    (valOf s xs i : ℕ) = valNat s xs i := rfl

omit [L.IsRelational] in
theorem primrec_valNat (V : FinVocab L) (k : ℕ) :
    Primrec fun p : FinStruct V × List ℕ => valNat p.1 p.2 k :=
  Primrec.nat_mod.comp ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const k))
    ((primrec_card V).comp Primrec.fst)

omit [L.IsRelational] in
/-- Appending a value to a valuation is `Fin.snoc` on the elements it
denotes. -/
theorem valOf_append {l : ℕ} (s : FinStruct V) (xs : List ℕ) (hlen : xs.length = l)
    (y : s.Univ) :
    (fun i : Fin (l + 1) => valOf s (xs ++ [(y : ℕ)]) i) =
      Fin.snoc (fun i : Fin l => valOf s xs i) y := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
    refine Fin.ext ?_
    simp only [val_valOf, valNat, Fin.val_last]
    have : (xs ++ [(y : ℕ)]).getD l 0 = (y : ℕ) := by
      rw [← hlen]
      simp [List.getD_eq_getElem?_getD]
    rw [this, Nat.mod_eq_of_lt y.isLt]
  · intro j
    rw [Fin.snoc_castSucc]
    refine Fin.ext ?_
    simp only [val_valOf, valNat, Fin.val_castSucc]
    have hj : (j : ℕ) < xs.length := by rw [hlen]; exact j.isLt
    have hgd : (xs ++ [(y : ℕ)]).getD (j : ℕ) 0 = xs.getD (j : ℕ) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    rw [hgd]

/-! ### Terms

Over a relational vocabulary a term is a variable, so its value is the value
of a bound variable whose *number is fixed by the term*: nothing about a term
has to be computed at run time. -/

/-- The number of the bound variable a term is. -/
def termIdx {l : ℕ} : L.Term (Empty ⊕ Fin l) → ℕ
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr i) => (i : ℕ)
  | .func f _ => isEmptyElim f

theorem realize_term {l : ℕ} (s : FinStruct V) (xs : List ℕ) (t : L.Term (Empty ⊕ Fin l)) :
    t.realize (Sum.elim Empty.elim fun i : Fin l => valOf s xs i) = valOf s xs (termIdx t) := by
  match t with
  | .var (Sum.inl e) => exact e.elim
  | .var (Sum.inr _) => rfl
  | .func f _ => exact isEmptyElim f

/-! ### The evaluator -/

/-- **The Boolean evaluator**: the recursion on the formula that
`FirstOrder.Language.FinStruct.primrec_evalBF` shows to be primitive recursive
and `FirstOrder.Language.FinStruct.evalBF_iff` shows to compute satisfaction.

An atom is a lookup in the table of the instance, at the number of the tuple
of values; a quantifier is a conjunction over `List.range card`, the values a
variable can take. -/
def evalBF (V : FinVocab L) : ∀ {l : ℕ}, L.BoundedFormula Empty l → FinStruct V → List ℕ → Bool
  | _, .falsum, _, _ => false
  | _, .equal t₁ t₂, s, xs => valNat s xs (termIdx t₁) == valNat s xs (termIdx t₂)
  | _, .rel R ts, s, xs =>
      (s.table.getD (V.index R) []).getD
        (tupleIdx s.card (List.ofFn fun i => valNat s xs (termIdx (ts i)))) false
  | _, .imp φ ψ, s, xs => !evalBF V φ s xs || evalBF V ψ s xs
  | _, .all φ, s, xs => andAll ((List.range s.card).map fun x => evalBF V φ s (xs ++ [x]))

/-- **The evaluator computes satisfaction.** -/
theorem evalBF_iff (V : FinVocab L) : ∀ {l : ℕ} (φ : L.BoundedFormula Empty l)
    (s : FinStruct V) (xs : List ℕ), xs.length = l →
      (evalBF V φ s xs = true ↔ φ.Realize Empty.elim fun i : Fin l => valOf s xs i)
  | _, .falsum, _, _, _ => by simp [evalBF, BoundedFormula.Realize]
  | _, .equal t₁ t₂, s, xs, _ => by
    simp only [evalBF, beq_iff_eq, BoundedFormula.Realize, realize_term]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  | _, .rel R ts, s, xs, _ => by
    simp only [evalBF, BoundedFormula.Realize]
    rw [relMap_iff, relMapBool]
    simp only [realize_term, val_valOf]
  | _, .imp φ ψ, s, xs, hlen => by
    simp only [evalBF, BoundedFormula.Realize, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    rw [← evalBF_iff V φ s xs hlen, ← evalBF_iff V ψ s xs hlen]
    cases evalBF V φ s xs <;> simp
  | _, .all φ, s, xs, hlen => by
    simp only [evalBF, BoundedFormula.Realize, andAll_eq_true, List.mem_map, List.mem_range]
    constructor
    · intro h y
      have := h _ ⟨(y : ℕ), y.isLt, rfl⟩
      rw [evalBF_iff V φ s (xs ++ [(y : ℕ)]) (by simp [hlen])] at this
      rwa [valOf_append s xs hlen y] at this
    · rintro h b ⟨y, hy, rfl⟩
      have := h ⟨y, hy⟩
      rw [← valOf_append s xs hlen ⟨y, hy⟩] at this
      exact (evalBF_iff V φ s (xs ++ [y]) (by simp [hlen])).mpr this

/-- **The evaluator is primitive recursive**, uniformly in the instance and
the valuation, for each fixed formula. -/
theorem primrec_evalBF (V : FinVocab L) : ∀ {l : ℕ} (φ : L.BoundedFormula Empty l),
    Primrec fun p : FinStruct V × List ℕ => evalBF V φ p.1 p.2
  | _, .falsum => (Primrec.const false).of_eq fun _ => rfl
  | _, .equal t₁ t₂ =>
      (Primrec.beq.comp (primrec_valNat V (termIdx t₁)) (primrec_valNat V (termIdx t₂))).of_eq
        fun _ => rfl
  | _, .rel R ts =>
      ((Primrec.list_getD false).comp
        ((Primrec.list_getD []).comp ((primrec_table V).comp Primrec.fst)
          (Primrec.const (V.index R : ℕ)))
        (primrec_tupleIdx.comp ((primrec_card V).comp Primrec.fst)
          (Primrec.list_ofFn fun i => primrec_valNat V (termIdx (ts i))))).of_eq fun _ => rfl
  | _, .imp φ ψ =>
      (Primrec.or.comp (Primrec.not.comp (primrec_evalBF V φ)) (primrec_evalBF V ψ)).of_eq
        fun _ => rfl
  | _, .all φ =>
      (primrec_andAll.comp
        (Primrec.list_map (Primrec.list_range.comp ((primrec_card V).comp Primrec.fst))
          (((primrec_evalBF V φ).comp
            ((Primrec.fst.comp Primrec.fst).pair
              (Primrec.list_concat.comp (Primrec.snd.comp Primrec.fst)
                Primrec.snd))).to₂))).of_eq fun _ => rfl

/-! ### Sentences

A sentence is the case `l = 0` of the evaluator, with the empty valuation. -/

/-- Deciding a fixed sentence on a concrete structure is primitive recursive. -/
theorem primrec_evalSentence (V : FinVocab L) (φ : L.Sentence) :
    Primrec fun s : FinStruct V => evalBF V φ s [] :=
  (primrec_evalBF V φ).comp (Primrec.id.pair (Primrec.const []))

/-- The evaluator decides a sentence. -/
theorem evalSentence_iff (V : FinVocab L) (φ : L.Sentence) (s : FinStruct V) :
    evalBF V φ s [] = true ↔ φ.Realize s.Univ := by
  refine Iff.trans (evalBF_iff V φ s [] rfl) (iff_of_eq ?_)
  refine congrArg₂ (fun (v : Empty → s.Univ) (xs : Fin 0 → s.Univ) =>
    BoundedFormula.Realize φ v xs) ?_ ?_
  · exact funext fun e => e.elim
  · exact funext fun i => Fin.elim0 i

end FinStruct

end Language

end FirstOrder
