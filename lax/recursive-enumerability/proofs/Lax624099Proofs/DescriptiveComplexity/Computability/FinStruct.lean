/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.Primrec.List
import Lax624099Proofs.DescriptiveComplexity.Computability.Realize
import Lax624099Proofs.DescriptiveComplexity.Interpretation
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

namespace Lax624099.ConcreteInstances.DecisionProblem
end Lax624099.ConcreteInstances.DecisionProblem

namespace Lax624099Proofs.Foreign.FirstOrder.Language
end Lax624099Proofs.Foreign.FirstOrder.Language

namespace Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct
end Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct

namespace Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab
end Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab

namespace Lax904597.Problems.DecisionProblem
export Lax624099.ConcreteInstances.DecisionProblem (toPred)
end Lax904597.Problems.DecisionProblem

/-!
# Finite structures as concrete data

`FirstOrder.Language.FinStruct`: a finite structure over a **finitely
presented relational vocabulary**, as a piece of data a machine can hold – a
universe `Fin (n + 1)` and a list of Boolean tables, one per relation symbol.
This is the passage from isomorphism classes to a `Primcodable` type that
`ComputablePred` needs, and it is built once for the whole catalog rather than
per problem.

## The two ingredients

* `FirstOrder.Language.FinVocab L`: the vocabulary `L` presented as data –
  finitely many relation symbols, numbered by `Fin numSyms`, with their
  arities. Every vocabulary of the catalog qualifies.
* `FirstOrder.Language.FinStruct V`: a universe size and a table. The universe
  is `Fin (univSize + 1)`, hence *nonempty by construction*: complexity
  notions in this library read a problem only on nonempty finite structures,
  and `Fin (n + 1)` is moreover already linearly ordered, which is what an
  *ordered* reduction needs (`≤ᶠᵒ[≤]`) with no order to encode.

## The representation decision

The table is a `List (List Bool)` – one row per symbol, one entry per tuple,
tuples numbered little-endian in base `card` – and *not* a dependent function
`(Fin k → Fin n) → Bool`. Dependent function tables are pleasant semantically
and painful to prove `Primrec` facts about, and everything downstream of this
file is `Primrec` facts. Out-of-range lookups return `false`, so *every* piece
of data denotes a structure and no well-formedness side condition ever has to
be carried.
-/

namespace FirstOrder

namespace Language

open Structure

/-! ### Numbering tuples -/

section Digits

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_nil (c : ℕ) : Lax624099.ConcreteInstances.tupleIdx c [] = 0 := rfl

export Lax624099Proofs.Foreign.FirstOrder.Language (tupleIdx_nil)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_cons (c a : ℕ) (l : List ℕ) :
    Lax624099.ConcreteInstances.tupleIdx c (a :: l) = a + c * Lax624099.ConcreteInstances.tupleIdx c l := rfl

export Lax624099Proofs.Foreign.FirstOrder.Language (tupleIdx_cons)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.digitAt_lt {c : ℕ} (hc : 0 < c) (t j : ℕ) : Lax624099.ConcreteInstances.digitAt c t j < c :=
  Nat.mod_lt _ hc

export Lax624099Proofs.Foreign.FirstOrder.Language (digitAt_lt)

/-- A tuple of digits in base `c` numbers below `c ^ length`. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_lt {c : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a < c) → Lax624099.ConcreteInstances.tupleIdx c l < c ^ l.length
  | [], _ => by simp
  | a :: l, h => by
    have hac : a < c := h a (by simp)
    have hl : Lax624099.ConcreteInstances.tupleIdx c l < c ^ l.length := Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_lt fun b hb => h b (by simp [hb])
    have hstep : c * Lax624099.ConcreteInstances.tupleIdx c l + c ≤ c * c ^ l.length := by
      have h1 : c * (Lax624099.ConcreteInstances.tupleIdx c l + 1) ≤ c * c ^ l.length := Nat.mul_le_mul_left _ hl
      rwa [Nat.mul_succ] at h1
    change a + c * Lax624099.ConcreteInstances.tupleIdx c l < c ^ (l.length + 1)
    rw [Nat.pow_succ, Nat.mul_comm (c ^ l.length) c]
    omega

export Lax624099Proofs.Foreign.FirstOrder.Language (tupleIdx_lt)

/-- The digits of the number of a tuple are the tuple back. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.digitAt_tupleIdx {c : ℕ} :
    ∀ {l : List ℕ}, (∀ a ∈ l, a < c) → ∀ {j : ℕ}, j < l.length →
      Lax624099.ConcreteInstances.digitAt c (Lax624099.ConcreteInstances.tupleIdx c l) j = l.getD j 0
  | [], _, _, hj => by simp at hj
  | a :: l, h, 0, _ => by
    have hac : a < c := h a (by simp)
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_cons, Lax624099.ConcreteInstances.digitAt, pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hac]
  | a :: l, h, j + 1, hj => by
    have hac : a < c := h a (by simp)
    have hdiv : (a + c * Lax624099.ConcreteInstances.tupleIdx c l) / c = Lax624099.ConcreteInstances.tupleIdx c l := by
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hac]
      omega
    have := Lax624099Proofs.Foreign.FirstOrder.Language.digitAt_tupleIdx (l := l) (fun b hb => h b (by simp [hb])) (j := j)
      (by simpa using hj)
    simp only [Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_cons, Lax624099.ConcreteInstances.digitAt, pow_succ, List.getD_cons_succ]
    rw [Nat.mul_comm (c ^ j) c, ← Nat.div_div_eq_div_mul, hdiv]
    exact this

export Lax624099Proofs.Foreign.FirstOrder.Language (digitAt_tupleIdx)

/-- Splitting a remainder along a product of moduli. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.mod_mul_split (c m v : ℕ) : v % (c * m) = v % c + c * (v / c % m) := by
  conv_lhs => rw [← Nat.mod_add_div (v % (c * m)) c]
  rw [Nat.mod_mod_of_dvd _ ⟨m, rfl⟩, Nat.mod_mul_right_div_self]

export Lax624099Proofs.Foreign.FirstOrder.Language (mod_mul_split)

/-- **The number of the tuple of the digits of `v` is `v`**, up to the number
of digits taken. The converse roundtrip of
`FirstOrder.Language.digitAt_tupleIdx`. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_ofFn_digitAt (c : ℕ) : ∀ d v : ℕ,
    Lax624099.ConcreteInstances.tupleIdx c (List.ofFn fun j : Fin d => Lax624099.ConcreteInstances.digitAt c v (j : ℕ)) = v % c ^ d
  | 0, _ => by simp [Nat.mod_one]
  | d + 1, v => by
    have hstep : ∀ j : Fin d,
        Lax624099.ConcreteInstances.digitAt c v ((Fin.succ j : Fin (d + 1)) : ℕ) = Lax624099.ConcreteInstances.digitAt c (v / c) (j : ℕ) := by
      intro j
      simp only [Lax624099.ConcreteInstances.digitAt, Fin.val_succ, pow_succ]
      rw [Nat.mul_comm (c ^ (j : ℕ)) c, ← Nat.div_div_eq_div_mul]
    rw [List.ofFn_succ]
    simp only [hstep]
    rw [Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_cons, Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_ofFn_digitAt c d (v / c)]
    simp only [Lax624099.ConcreteInstances.digitAt, Fin.val_zero, pow_zero, Nat.div_one, pow_succ]
    rw [Nat.mul_comm (c ^ d) c]
    exact (Lax624099Proofs.Foreign.FirstOrder.Language.mod_mul_split c (c ^ d) v).symm

export Lax624099Proofs.Foreign.FirstOrder.Language (tupleIdx_ofFn_digitAt)

end Digits

/-! ### Finitely presented vocabularies -/

namespace FinVocab

variable {L : Language.{0, 0}} (V : Lax624099.ConcreteInstances.FinVocab L)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.arity_index {n : ℕ} (R : L.Relations n) : V.arity (V.index R) = n :=
  congrArg Sigma.fst (V.symOf_index R)

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (arity_index)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

open Structure

namespace FinVocab

variable {L : Language.{0, 0}} (V : Lax624099.ConcreteInstances.FinVocab L)

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (arity_index)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.sym_index {n : ℕ} (R : L.Relations n) : HEq (V.sym (V.index R)) R := by
  change HEq (V.symOf (V.index R)).2 R
  rw [show V.symOf (V.index R) = ⟨n, R⟩ from V.symOf_index R]

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (sym_index)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

open Structure

namespace FinVocab

variable {L : Language.{0, 0}} (V : Lax624099.ConcreteInstances.FinVocab L)

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (sym_index)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab.index_sym (i : Fin V.numSyms) : V.index (V.sym i) = i :=
  V.index_symOf i

end FinVocab

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinVocab

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (index_sym)

end Lax624099.ConcreteInstances.FinVocab

namespace FirstOrder

namespace Language

open Structure

namespace FinVocab

variable {L : Language.{0, 0}} (V : Lax624099.ConcreteInstances.FinVocab L)

export Lax624099Proofs.Foreign.FirstOrder.Language.FinVocab (index_sym)

end FinVocab

/-! ### Concrete finite structures -/

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.relMapBool_eq (s : Lax624099.ConcreteInstances.FinStruct V) {n : ℕ} (R : L.Relations n) (x : Fin n → s.Univ) :
    s.relMapBool R x =
      (s.table.getD (V.index R) []).getD
        (Lax624099.ConcreteInstances.tupleIdx s.card (List.ofFn fun j => (x j : ℕ))) false := rfl

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (relMapBool_eq)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (relMapBool_eq)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.relMap_iff [L.IsRelational] (s : Lax624099.ConcreteInstances.FinStruct V) {n : ℕ} (R : L.Relations n)
    (x : Fin n → s.Univ) : RelMap R x ↔ s.relMapBool R x = true :=
  Iff.rfl

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (relMap_iff)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (relMap_iff)

instance _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.decidableRelMap [L.IsRelational] (s : Lax624099.ConcreteInstances.FinStruct V) {n : ℕ} (R : L.Relations n)
    (x : Fin n → s.Univ) : Decidable (RelMap R x) :=
  inferInstanceAs (Decidable (_ = true))

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (decidableRelMap)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (decidableRelMap)

/-! ### Building a concrete structure from a table -/

/-- **Reading a symbol through its number**: a Boolean reading of relations,
applied to the symbol read back from a number, is the reading of the symbol
itself – the one place the arity dependency of
`FirstOrder.Language.FinVocab` has to be discharged. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.heq_relArgs {α : Type} {m n : ℕ} (h : m = n) (R : L.Relations m) (R' : L.Relations n)
    (hR : HEq R R') (g : ∀ {k : ℕ}, L.Relations k → (Fin k → α) → Bool)
    (y : Fin m → α) (x : Fin n → α) (hy : ∀ j : Fin m, y j = x (Fin.cast h j)) :
    g R y = g R' x := by
  subst h
  have hyx : y = x := funext fun j => by simpa using hy j
  subst hyx
  rw [eq_of_heq hR]

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (heq_relArgs)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (heq_relArgs)

@[simp] theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.univSize_ofTable (V : Lax624099.ConcreteInstances.FinVocab L) (k : ℕ) (f) :
    (Lax624099.ConcreteInstances.FinStruct.ofTable V k f).univSize = k := rfl

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (univSize_ofTable)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (univSize_ofTable)

/-- **The table is read back as it was written.** -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.relMapBool_ofTable (V : Lax624099.ConcreteInstances.FinVocab L) (k : ℕ)
    (f : ∀ {n : ℕ}, L.Relations n → (Fin n → Fin (k + 1)) → Bool) {n : ℕ}
    (R : L.Relations n) (x : Fin n → Fin (k + 1)) :
    (Lax624099.ConcreteInstances.FinStruct.ofTable V k f).relMapBool R x = f R x := by
  have ha : V.arity (V.index R) = n := V.arity_index R
  have hall : ∀ a ∈ (List.ofFn fun j => (x j : ℕ)), a < k + 1 := by
    intro a hab
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hab
    exact (x j).isLt
  have hlen : (List.ofFn fun j => (x j : ℕ)).length = V.arity (V.index R) := by
    rw [List.length_ofFn, ha]
  have hlt : Lax624099.ConcreteInstances.tupleIdx (k + 1) (List.ofFn fun j => (x j : ℕ)) <
      (k + 1) ^ V.arity (V.index R) := by
    have := Lax624099Proofs.Foreign.FirstOrder.Language.tupleIdx_lt (c := k + 1) hall
    rwa [hlen] at this
  have hrow : ((Lax624099.ConcreteInstances.FinStruct.ofTable V k f).table).getD (V.index R) [] =
      (List.range ((k + 1) ^ V.arity (V.index R))).map fun t =>
        f (V.sym (V.index R)) fun j => ⟨Lax624099.ConcreteInstances.digitAt (k + 1) t j, Lax624099Proofs.Foreign.FirstOrder.Language.digitAt_lt (Nat.succ_pos k) t j⟩ := by
    rw [Lax624099.ConcreteInstances.FinStruct.ofTable, List.getD_eq_getElem _ _ (by simp)]
    simp
  simp only [Lax624099.ConcreteInstances.FinStruct.relMapBool, hrow, Lax624099.ConcreteInstances.FinStruct.card, Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.univSize_ofTable]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
  simp only [List.getElem_map, List.getElem_range]
  refine Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.heq_relArgs ha (V.sym (V.index R)) R (V.sym_index R) (fun {_} => f) _ x ?_
  intro j
  refine Fin.ext ?_
  have hj : (j : ℕ) < n := by have := j.isLt; omega
  have hd := Lax624099Proofs.Foreign.FirstOrder.Language.digitAt_tupleIdx (c := k + 1) hall (j := (j : ℕ)) (by rw [hlen]; exact j.isLt)
  simp only [hd, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj]
  rfl

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (relMapBool_ofTable)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (relMapBool_ofTable)

/-- **Every finite nonempty structure is presented by a table**, along a chosen
numbering of its universe: `ofTable` transported along `e`, with the numbering
itself an `L`-isomorphism. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.ofEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (V : Lax624099.ConcreteInstances.FinVocab L) (k : ℕ) (e : Fin (k + 1) ≃ A) : Lax624099.ConcreteInstances.FinStruct V :=
  Lax624099.ConcreteInstances.FinStruct.ofTable V k fun R x => decide (RelMap R fun j => e (x j))

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (ofEquiv)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (ofEquiv)

/-- The table of `FirstOrder.Language.FinStruct.ofEquiv` reads the relations of
the structure it was built from. -/
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.relMapBool_ofEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (V : Lax624099.ConcreteInstances.FinVocab L) (k : ℕ) (e : Fin (k + 1) ≃ A) {n : ℕ} (R : L.Relations n)
    (x : Fin n → (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.ofEquiv V k e).Univ) :
    (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.ofEquiv V k e).relMapBool R x = decide (RelMap R fun j => e (x j)) :=
  Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.relMapBool_ofTable V k _ R x

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (relMapBool_ofEquiv)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (relMapBool_ofEquiv)

/-- The numbering used by `FirstOrder.Language.FinStruct.ofEquiv` is an
isomorphism onto the structure it builds. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.equivOfEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (V : Lax624099.ConcreteInstances.FinVocab L) (k : ℕ) (e : Fin (k + 1) ≃ A) : (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.ofEquiv V k e).Univ ≃[L] A where
  toEquiv := e
  map_fun' f := isEmptyElim f
  map_rel' {n} R x := by
    change RelMap R (⇑e ∘ x) ↔ (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.ofEquiv V k e).relMapBool R x = true
    rw [Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.relMapBool_ofEquiv]
    simp only [decide_eq_true_eq]
    rfl

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (equivOfEquiv)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (equivOfEquiv)

/-! ### Concrete instances are a `Primcodable` type

Everything a machine has to hold about an instance is a natural number and a
list of lists of Booleans, so the coding is Mathlib's, with nothing to prove
beyond the three projections being primitive recursive. -/

section Coding

variable (V : Lax624099.ConcreteInstances.FinVocab L)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_equivProd : Primrec (Lax624099.ConcreteInstances.FinStruct.equivProd V) :=
  Primrec.of_equiv

end Coding

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_equivProd)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

section Coding

variable (V : Lax624099.ConcreteInstances.FinVocab L)

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_equivProd)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_univSize : Primrec fun s : Lax624099.ConcreteInstances.FinStruct V => s.univSize :=
  (Primrec.fst.comp (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_equivProd V)).of_eq fun _ => rfl

end Coding

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_univSize)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

section Coding

variable (V : Lax624099.ConcreteInstances.FinVocab L)

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_univSize)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_card : Primrec fun s : Lax624099.ConcreteInstances.FinStruct V => s.card :=
  Primrec.succ.comp (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_univSize V)

end Coding

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_card)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

section Coding

variable (V : Lax624099.ConcreteInstances.FinVocab L)

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_card)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_table : Primrec fun s : Lax624099.ConcreteInstances.FinStruct V => s.table :=
  (Primrec.snd.comp (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_equivProd V)).of_eq fun _ => rfl

end Coding

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_table)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

section Coding

variable (V : Lax624099.ConcreteInstances.FinVocab L)

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_table)

theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.primrec_mk :
    Primrec₂ fun (n : ℕ) (t : List (List Bool)) => (⟨n, t⟩ : Lax624099.ConcreteInstances.FinStruct V) :=
  (Primrec.of_equiv_iff (Lax624099.ConcreteInstances.FinStruct.equivProd V)).mp (Primrec.id.of_eq fun _ => rfl)

end Coding

end FinStruct

end Language

end FirstOrder

namespace Lax624099.ConcreteInstances.FinStruct

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_mk)

end Lax624099.ConcreteInstances.FinStruct

namespace FirstOrder

namespace Language

open Structure

namespace FinStruct

variable {L : Language.{0, 0}} {V : Lax624099.ConcreteInstances.FinVocab L}

section Coding

variable (V : Lax624099.ConcreteInstances.FinVocab L)

export Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct (primrec_mk)

end Coding

end FinStruct

end Language

end FirstOrder

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The concrete instances capture the problem**: a finite nonempty structure
is a yes-instance exactly when some – equivalently, any – numbering of it is.
Isomorphism-invariance of a decision problem is what makes this true. -/
theorem toPred_ofEquiv (P : Lax904597.Problems.DecisionProblem L) (V : Lax624099.ConcreteInstances.FinVocab L) {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (k : ℕ) (e : Fin (k + 1) ≃ A) :
    P.toPred V (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.ofEquiv V k e) ↔ P A :=
  P.iso_invariant (Lax624099Proofs.Foreign.FirstOrder.Language.FinStruct.equivOfEquiv V k e)

end Lax624099Proofs.DescriptiveComplexity


