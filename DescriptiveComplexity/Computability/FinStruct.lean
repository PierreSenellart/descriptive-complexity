/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.Primrec.List
import DescriptiveComplexity.Computability.Realize
import DescriptiveComplexity.Interpretation

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

/-- The number of a tuple of digits, little-endian in base `c`. -/
def tupleIdx (c : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + c * tupleIdx c l

/-- The `j`-th digit of `t` in base `c`. -/
def digitAt (c t j : ℕ) : ℕ := t / c ^ j % c

@[simp] theorem tupleIdx_nil (c : ℕ) : tupleIdx c [] = 0 := rfl

@[simp] theorem tupleIdx_cons (c a : ℕ) (l : List ℕ) :
    tupleIdx c (a :: l) = a + c * tupleIdx c l := rfl

theorem digitAt_lt {c : ℕ} (hc : 0 < c) (t j : ℕ) : digitAt c t j < c :=
  Nat.mod_lt _ hc

/-- A tuple of digits in base `c` numbers below `c ^ length`. -/
theorem tupleIdx_lt {c : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a < c) → tupleIdx c l < c ^ l.length
  | [], _ => by simp
  | a :: l, h => by
    have hac : a < c := h a (by simp)
    have hl : tupleIdx c l < c ^ l.length := tupleIdx_lt fun b hb => h b (by simp [hb])
    have hstep : c * tupleIdx c l + c ≤ c * c ^ l.length := by
      have h1 : c * (tupleIdx c l + 1) ≤ c * c ^ l.length := Nat.mul_le_mul_left _ hl
      rwa [Nat.mul_succ] at h1
    change a + c * tupleIdx c l < c ^ (l.length + 1)
    rw [Nat.pow_succ, Nat.mul_comm (c ^ l.length) c]
    omega

/-- The digits of the number of a tuple are the tuple back. -/
theorem digitAt_tupleIdx {c : ℕ} :
    ∀ {l : List ℕ}, (∀ a ∈ l, a < c) → ∀ {j : ℕ}, j < l.length →
      digitAt c (tupleIdx c l) j = l.getD j 0
  | [], _, _, hj => by simp at hj
  | a :: l, h, 0, _ => by
    have hac : a < c := h a (by simp)
    simp only [tupleIdx_cons, digitAt, pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hac]
  | a :: l, h, j + 1, hj => by
    have hac : a < c := h a (by simp)
    have hdiv : (a + c * tupleIdx c l) / c = tupleIdx c l := by
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hac]
      omega
    have := digitAt_tupleIdx (l := l) (fun b hb => h b (by simp [hb])) (j := j)
      (by simpa using hj)
    simp only [tupleIdx_cons, digitAt, pow_succ, List.getD_cons_succ]
    rw [Nat.mul_comm (c ^ j) c, ← Nat.div_div_eq_div_mul, hdiv]
    exact this

/-- Splitting a remainder along a product of moduli. -/
theorem mod_mul_split (c m v : ℕ) : v % (c * m) = v % c + c * (v / c % m) := by
  conv_lhs => rw [← Nat.mod_add_div (v % (c * m)) c]
  rw [Nat.mod_mod_of_dvd _ ⟨m, rfl⟩, Nat.mod_mul_right_div_self]

/-- **The number of the tuple of the digits of `v` is `v`**, up to the number
of digits taken. The converse roundtrip of
`FirstOrder.Language.digitAt_tupleIdx`. -/
theorem tupleIdx_ofFn_digitAt (c : ℕ) : ∀ d v : ℕ,
    tupleIdx c (List.ofFn fun j : Fin d => digitAt c v (j : ℕ)) = v % c ^ d
  | 0, _ => by simp [Nat.mod_one]
  | d + 1, v => by
    have hstep : ∀ j : Fin d,
        digitAt c v ((Fin.succ j : Fin (d + 1)) : ℕ) = digitAt c (v / c) (j : ℕ) := by
      intro j
      simp only [digitAt, Fin.val_succ, pow_succ]
      rw [Nat.mul_comm (c ^ (j : ℕ)) c, ← Nat.div_div_eq_div_mul]
    rw [List.ofFn_succ]
    simp only [hstep]
    rw [tupleIdx_cons, tupleIdx_ofFn_digitAt c d (v / c)]
    simp only [digitAt, Fin.val_zero, pow_zero, Nat.div_one, pow_succ]
    rw [Nat.mul_comm (c ^ d) c]
    exact (mod_mul_split c (c ^ d) v).symm

end Digits

/-! ### Finitely presented vocabularies -/

/-- A **finitely presented relational vocabulary**: the relation symbols of `L`
numbered by `Fin numSyms`, with their arities. Reading a symbol off its number
(`sym`) and numbering a symbol (`index`) are mutually inverse, so the
presentation loses nothing.

Every vocabulary of the catalog is of this shape: `Language.turing` has 12
symbols of arity at most 2, `Language.finsat` 14 of arity at most 3. The
presentations are closed under `Language.sum`
(`FirstOrder.Language.FinVocab.sum`), which is what lets the second-order
machinery – whose vocabularies are sums of the instance's with a block's – be
encoded by the same means. -/
structure FinVocab (L : Language.{0, 0}) where
  /-- The number of relation symbols. -/
  numSyms : ℕ
  /-- The symbol with a given number, together with its arity. -/
  symOf : Fin numSyms → ((n : ℕ) × L.Relations n)
  /-- The number of a symbol. -/
  index : ∀ {n : ℕ}, L.Relations n → Fin numSyms
  /-- Reading back the symbol with the number of a symbol gives it back. -/
  symOf_index : ∀ {n : ℕ} (R : L.Relations n), symOf (index R) = ⟨n, R⟩
  /-- Numbering the symbol with a given number gives that number back. -/
  index_symOf : ∀ i : Fin numSyms, index (symOf i).2 = i

namespace FinVocab

variable {L : Language.{0, 0}} (V : FinVocab L)

/-- The arity of the symbol with a given number. -/
abbrev arity (i : Fin V.numSyms) : ℕ := (V.symOf i).1

/-- The symbol with a given number. -/
abbrev sym (i : Fin V.numSyms) : L.Relations (V.arity i) := (V.symOf i).2

theorem arity_index {n : ℕ} (R : L.Relations n) : V.arity (V.index R) = n :=
  congrArg Sigma.fst (V.symOf_index R)

theorem sym_index {n : ℕ} (R : L.Relations n) : HEq (V.sym (V.index R)) R := by
  change HEq (V.symOf (V.index R)).2 R
  rw [show V.symOf (V.index R) = ⟨n, R⟩ from V.symOf_index R]

theorem index_sym (i : Fin V.numSyms) : V.index (V.sym i) = i :=
  V.index_symOf i

/-- The arity of a symbol, as read from its number, *is* its arity: the shape
in which the dependency is discharged in practice. -/
theorem sym_index_eq {n : ℕ} (R : L.Relations n) (h : V.arity (V.index R) = n) :
    h ▸ V.sym (V.index R) = R :=
  eq_of_heq ((eqRec_heq h (V.sym (V.index R))).trans (V.sym_index R))

end FinVocab

/-! ### Concrete finite structures -/

/-- A **concrete finite structure** over the finitely presented vocabulary
`V`: a universe size and a table of Booleans, one row per relation symbol.

The universe is `Fin (univSize + 1)`, so it is nonempty by construction; the
row of an `n`-ary symbol is read at the number of the tuple, little-endian in
base `card`. Anything out of range reads `false`, so every pair of a number
and a list of lists of Booleans denotes a structure. -/
structure FinStruct {L : Language.{0, 0}} (V : FinVocab L) where
  /-- One less than the size of the universe. -/
  univSize : ℕ
  /-- The tables of the relations, one row per symbol. -/
  table : List (List Bool)

namespace FinStruct

variable {L : Language.{0, 0}} {V : FinVocab L}

/-- The size of the universe of a concrete finite structure. -/
abbrev card (s : FinStruct V) : ℕ := s.univSize + 1

/-- The universe of a concrete finite structure: nonempty and linearly ordered
by construction. -/
abbrev Univ (s : FinStruct V) : Type := Fin s.card

/-- The table lookup: does the relation `R` hold of the tuple `x`? -/
def relMapBool (s : FinStruct V) {n : ℕ} (R : L.Relations n) (x : Fin n → s.Univ) : Bool :=
  (s.table.getD (V.index R) []).getD (tupleIdx s.card (List.ofFn fun j => (x j : ℕ))) false

theorem relMapBool_eq (s : FinStruct V) {n : ℕ} (R : L.Relations n) (x : Fin n → s.Univ) :
    s.relMapBool R x =
      (s.table.getD (V.index R) []).getD
        (tupleIdx s.card (List.ofFn fun j => (x j : ℕ))) false := rfl

/-- **The structure a piece of data denotes.** -/
instance instStructure [L.IsRelational] (s : FinStruct V) : L.Structure s.Univ where
  funMap f := isEmptyElim f
  RelMap R x := s.relMapBool R x = true

theorem relMap_iff [L.IsRelational] (s : FinStruct V) {n : ℕ} (R : L.Relations n)
    (x : Fin n → s.Univ) : RelMap R x ↔ s.relMapBool R x = true :=
  Iff.rfl

instance decidableRelMap [L.IsRelational] (s : FinStruct V) {n : ℕ} (R : L.Relations n)
    (x : Fin n → s.Univ) : Decidable (RelMap R x) :=
  inferInstanceAs (Decidable (_ = true))

/-! ### Building a concrete structure from a table -/

/-- **Reading a symbol through its number**: a Boolean reading of relations,
applied to the symbol read back from a number, is the reading of the symbol
itself – the one place the arity dependency of
`FirstOrder.Language.FinVocab` has to be discharged. -/
theorem heq_relArgs {α : Type} {m n : ℕ} (h : m = n) (R : L.Relations m) (R' : L.Relations n)
    (hR : HEq R R') (g : ∀ {k : ℕ}, L.Relations k → (Fin k → α) → Bool)
    (y : Fin m → α) (x : Fin n → α) (hy : ∀ j : Fin m, y j = x (Fin.cast h j)) :
    g R y = g R' x := by
  subst h
  have hyx : y = x := funext fun j => by simpa using hy j
  subst hyx
  rw [eq_of_heq hR]

/-- The concrete structure over a universe `Fin (k + 1)` whose relations are
given by the Boolean function `f`. -/
def ofTable (V : FinVocab L) (k : ℕ)
    (f : ∀ {n : ℕ}, L.Relations n → (Fin n → Fin (k + 1)) → Bool) : FinStruct V where
  univSize := k
  table := List.ofFn fun i : Fin V.numSyms =>
    (List.range ((k + 1) ^ V.arity i)).map fun t =>
      f (V.sym i) fun j => ⟨digitAt (k + 1) t j, digitAt_lt (Nat.succ_pos k) t j⟩

@[simp] theorem univSize_ofTable (V : FinVocab L) (k : ℕ) (f) :
    (ofTable V k f).univSize = k := rfl

/-- **The table is read back as it was written.** -/
theorem relMapBool_ofTable (V : FinVocab L) (k : ℕ)
    (f : ∀ {n : ℕ}, L.Relations n → (Fin n → Fin (k + 1)) → Bool) {n : ℕ}
    (R : L.Relations n) (x : Fin n → Fin (k + 1)) :
    (ofTable V k f).relMapBool R x = f R x := by
  have ha : V.arity (V.index R) = n := V.arity_index R
  have hall : ∀ a ∈ (List.ofFn fun j => (x j : ℕ)), a < k + 1 := by
    intro a hab
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hab
    exact (x j).isLt
  have hlen : (List.ofFn fun j => (x j : ℕ)).length = V.arity (V.index R) := by
    rw [List.length_ofFn, ha]
  have hlt : tupleIdx (k + 1) (List.ofFn fun j => (x j : ℕ)) <
      (k + 1) ^ V.arity (V.index R) := by
    have := tupleIdx_lt (c := k + 1) hall
    rwa [hlen] at this
  have hrow : ((ofTable V k f).table).getD (V.index R) [] =
      (List.range ((k + 1) ^ V.arity (V.index R))).map fun t =>
        f (V.sym (V.index R)) fun j => ⟨digitAt (k + 1) t j, digitAt_lt (Nat.succ_pos k) t j⟩ := by
    rw [ofTable, List.getD_eq_getElem _ _ (by simp)]
    simp
  simp only [relMapBool, hrow, card, univSize_ofTable]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
  simp only [List.getElem_map, List.getElem_range]
  refine heq_relArgs ha (V.sym (V.index R)) R (V.sym_index R) (fun {_} => f) _ x ?_
  intro j
  refine Fin.ext ?_
  have hj : (j : ℕ) < n := by have := j.isLt; omega
  have hd := digitAt_tupleIdx (c := k + 1) hall (j := (j : ℕ)) (by rw [hlen]; exact j.isLt)
  simp only [hd, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj]
  rfl

/-- **Every finite nonempty structure is presented by a table**, along a chosen
numbering of its universe: `ofTable` transported along `e`, with the numbering
itself an `L`-isomorphism. -/
def ofEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (V : FinVocab L) (k : ℕ) (e : Fin (k + 1) ≃ A) : FinStruct V :=
  ofTable V k fun R x => decide (RelMap R fun j => e (x j))

/-- The table of `FirstOrder.Language.FinStruct.ofEquiv` reads the relations of
the structure it was built from. -/
theorem relMapBool_ofEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (V : FinVocab L) (k : ℕ) (e : Fin (k + 1) ≃ A) {n : ℕ} (R : L.Relations n)
    (x : Fin n → (ofEquiv V k e).Univ) :
    (ofEquiv V k e).relMapBool R x = decide (RelMap R fun j => e (x j)) :=
  relMapBool_ofTable V k _ R x

/-- The numbering used by `FirstOrder.Language.FinStruct.ofEquiv` is an
isomorphism onto the structure it builds. -/
def equivOfEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (V : FinVocab L) (k : ℕ) (e : Fin (k + 1) ≃ A) : (ofEquiv V k e).Univ ≃[L] A where
  toEquiv := e
  map_fun' f := isEmptyElim f
  map_rel' {n} R x := by
    change RelMap R (⇑e ∘ x) ↔ (ofEquiv V k e).relMapBool R x = true
    rw [relMapBool_ofEquiv]
    simp only [decide_eq_true_eq]
    rfl

/-! ### Concrete instances are a `Primcodable` type

Everything a machine has to hold about an instance is a natural number and a
list of lists of Booleans, so the coding is Mathlib's, with nothing to prove
beyond the three projections being primitive recursive. -/

section Coding

variable (V : FinVocab L)

/-- The coding of a concrete finite structure as a pair. -/
def equivProd : FinStruct V ≃ ℕ × List (List Bool) where
  toFun s := (s.univSize, s.table)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

/-- **Concrete finite structures are a `Primcodable` type**: the object
`ComputablePred` and `REPred` are defined on. -/
instance instPrimcodable : Primcodable (FinStruct V) :=
  Primcodable.ofEquiv _ (equivProd V)

theorem primrec_equivProd : Primrec (equivProd V) :=
  Primrec.of_equiv

theorem primrec_univSize : Primrec fun s : FinStruct V => s.univSize :=
  (Primrec.fst.comp (primrec_equivProd V)).of_eq fun _ => rfl

theorem primrec_card : Primrec fun s : FinStruct V => s.card :=
  Primrec.succ.comp (primrec_univSize V)

theorem primrec_table : Primrec fun s : FinStruct V => s.table :=
  (Primrec.snd.comp (primrec_equivProd V)).of_eq fun _ => rfl

theorem primrec_mk :
    Primrec₂ fun (n : ℕ) (t : List (List Bool)) => (⟨n, t⟩ : FinStruct V) :=
  (Primrec.of_equiv_iff (equivProd V)).mp (Primrec.id.of_eq fun _ => rfl)

end Coding

end FinStruct

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The set of concrete instances a decision problem denotes.** This is the
object `ComputablePred` and `REPred` are about: a problem is an
isomorphism-closed property of finite structures, and the numbering of
`FirstOrder.Language.FinStruct` turns it into a property of a `Primcodable`
type, with nothing to write per problem. -/
def DecisionProblem.toPred (P : DecisionProblem L) (V : FinVocab L) :
    FinStruct V → Prop := fun s => P s.Univ

/-- **The concrete instances capture the problem**: a finite nonempty structure
is a yes-instance exactly when some – equivalently, any – numbering of it is.
Isomorphism-invariance of a decision problem is what makes this true. -/
theorem toPred_ofEquiv (P : DecisionProblem L) (V : FinVocab L) {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (k : ℕ) (e : Fin (k + 1) ≃ A) :
    P.toPred V (FinStruct.ofEquiv V k e) ↔ P A :=
  P.iso_invariant (FinStruct.equivOfEquiv V k e)

/-- Every finite nonempty structure is isomorphic to a concrete one. -/
theorem exists_finStruct (V : FinVocab L) (A : Type) [L.Structure A] [Finite A] [Nonempty A] :
    ∃ s : FinStruct V, Nonempty (s.Univ ≃[L] A) := by
  classical
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin A
  match k, e with
  | 0, e => exact ((e (Classical.arbitrary A)).elim0)
  | k + 1, e => exact ⟨FinStruct.ofEquiv V k e.symm, ⟨FinStruct.equivOfEquiv V k e.symm⟩⟩

end DescriptiveComplexity
