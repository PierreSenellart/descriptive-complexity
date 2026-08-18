/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.RE
import DescriptiveComplexity.Computability.Eval
import DescriptiveComplexity.RecursivelyEnumerable

/-!
# RE is recursively enumerable

**`DescriptiveComplexity.RE_subset_rePred`**: a problem in the logically
defined class `DescriptiveComplexity.RE` denotes, through the encoding of
`FirstOrder.Language.FinStruct`, an `REPred` in the sense of Mathlib's
computability layer. It is what makes the *name* of the class a theorem rather
than a convention, and it needs no machine model at all.

## The argument

`∃SO[new]`-definability says

```
P A ↔ ∃ m : ℕ, ∃ ρ : B.Assignment (A ⊕ Fin m), φ holds in the extended structure
```

with `φ` a *fixed* first-order sentence. Both existentials are absorbed into a
single unbounded search over a `Primcodable` witness: the number `m` of
invented values, and a list of Boolean tables standing for the assignment `ρ`.
Given the witness, the extended structure is *built as data*
(`DescriptiveComplexity.extStruct`) and `φ` is evaluated on it by the
primitive recursive evaluator of `DescriptiveComplexity.Computability.Eval`.
Unbounded search over a decidable test is exactly `REPred`.

Two facts carry the proof:

* every list of Booleans denotes an assignment and every assignment is denoted
  by one (`DescriptiveComplexity.exists_tab`), because the extended universe is
  finite – this is where the certificate being a *finite* object is used;
* the structure built from the witness is isomorphic to the extended structure
  of the logic (`DescriptiveComplexity.extIso`), so the fixed sentence says the
  same thing about both.

## The converse

That every `REPred` is in `RE` is proved one layer up, in
`DescriptiveComplexity.Computability.CodeHaltComplete`
(`DescriptiveComplexity.mem_RE_iff_rePred`). It needs a target whose programs
already exist, so that the reduction can draw a semi-decision procedure inside
the instance rather than build one.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Unbounded search over a coded witness -/

section Search

/-- **A predicate found by unbounded search over a coded witness is
recursively enumerable.** The witness type is any `Primcodable` type; the
search is Mathlib's `Nat.rfind` over its codes. -/
theorem rePred_of_exists {α β : Type} [Primcodable α] [Primcodable β] {p : α → Prop}
    {f : α → β → Bool} (hf : Primrec₂ f) (h : ∀ a, p a ↔ ∃ b, f a b = true) : REPred p := by
  have hg : Computable₂ fun (a : α) (n : ℕ) =>
      ((Encodable.decode (α := β) n).map (f a)).getD false :=
    (Primrec.option_getD.comp
      (Primrec.option_map (Primrec.decode.comp Primrec.snd)
        (hf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
      (Primrec.const false)).to₂.to_comp
  have hpart : Partrec fun a : α =>
      Nat.rfind fun n => Part.some (((Encodable.decode (α := β) n).map (f a)).getD false) :=
    Partrec.rfind hg.partrec₂
  refine hpart.dom_re.of_eq fun a => ?_
  constructor
  · intro hd
    obtain ⟨n, hn, -⟩ := Nat.rfind_dom.mp hd
    have hn' : ((Encodable.decode (α := β) n).map (f a)).getD false = true :=
      (Part.mem_some_iff.mp hn).symm
    rcases hd' : (Encodable.decode (α := β) n) with _ | b
    · rw [hd'] at hn'; simp at hn'
    · exact (h a).mpr ⟨b, by rw [hd'] at hn'; simpa using hn'⟩
  · intro hp
    obtain ⟨b, hb⟩ := (h a).mp hp
    exact Nat.rfind_dom.mpr ⟨Encodable.encode b, by simp [hb], by simp⟩

end Search

/-! ### The vocabularies of the second-order machinery -/

section Vocabularies

/-- The one-symbol vocabulary marking the original elements, presented. -/
def oldVocab : FinVocab Language.oldMark where
  numSyms := 1
  symOf _ := ⟨1, Language.oldSym⟩
  index _ := 0
  symOf_index R := by match R with | .old => rfl
  index_symOf _ := Subsingleton.elim _ _

/-- The number of relation variables of a block. -/
noncomputable def blockNum (B : SOBlock) : ℕ := (Finite.exists_equiv_fin B.ι).choose

/-- A numbering of the relation variables of a block. -/
noncomputable def blockEq (B : SOBlock) : Fin (blockNum B) ≃ B.ι :=
  (Finite.exists_equiv_fin B.ι).choose_spec.some.symm

/-- The vocabulary of a second-order quantifier block, presented: one symbol
per relation variable. -/
noncomputable def blockVocab (B : SOBlock) : FinVocab B.lang :=
  FinVocab.ofEquivSigma (blockNum B)
    ((blockEq B).trans (Equiv.sigmaFiberEquiv B.arity).symm)

/-- The vocabulary an `∃SO[new]` kernel is read over: the instance's, the mark
of the original elements, and the block's. -/
noncomputable def soVocab {L : Language.{0, 0}} (V : FinVocab L) (B : SOBlock) :
    FinVocab ((newLang L).sum B.lang) :=
  (V.sum oldVocab).sum (blockVocab B)

end Vocabularies

/-! ### The extended structure, as data -/

section Extended

variable {L : Language.{0, 0}} [L.IsRelational] {V : FinVocab L} {B : SOBlock}

/-- The numbering of the extended universe: the instance first, the invented
values after it. -/
def extEquivFin (s : FinStruct V) (m : ℕ) : (s.Univ ⊕ Fin m) ≃ Fin (s.univSize + m + 1) :=
  finSumFinEquiv.trans (finCongr (by change s.univSize + 1 + m = s.univSize + m + 1; omega))

omit [L.IsRelational] in
@[simp] theorem val_extEquivFin_inl (s : FinStruct V) (m : ℕ) (a : s.Univ) :
    ((extEquivFin s m (Sum.inl a) : Fin (s.univSize + m + 1)) : ℕ) = (a : ℕ) := rfl

omit [L.IsRelational] in
@[simp] theorem val_extEquivFin_inr (s : FinStruct V) (m : ℕ) (j : Fin m) :
    ((extEquivFin s m (Sum.inr j) : Fin (s.univSize + m + 1)) : ℕ) = s.card + (j : ℕ) := rfl

omit [L.IsRelational] in
theorem val_extEquivFin_lt (s : FinStruct V) (m : ℕ) (y : s.Univ ⊕ Fin m) :
    ((extEquivFin s m y : Fin (s.univSize + m + 1)) : ℕ) < s.card ↔ ∃ a, y = Sum.inl a := by
  cases y with
  | inl a => exact iff_of_true a.isLt ⟨a, rfl⟩
  | inr j =>
    refine iff_of_false ?_ ?_
    · rw [val_extEquivFin_inr]; omega
    · rintro ⟨a, ha⟩; simp at ha

/-- **The relations of the extended structure**, read off the instance and the
guessed table: an original symbol holds of a tuple of original elements
exactly where it holds in the instance, the mark holds of the original
elements, and a relation variable reads its guessed table. -/
noncomputable def extRel (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) :
    ∀ {n : ℕ}, ((newLang L).sum B.lang).Relations n →
      (Fin n → Fin (s.univSize + m + 1)) → Bool
  | _, Sum.inl (Sum.inl r), x =>
      andAll (List.ofFn fun j => decide ((x j : ℕ) < s.card)) &&
        (s.table.getD (V.index r) []).getD
          (tupleIdx s.card (List.ofFn fun j => (x j : ℕ))) false
  | _, Sum.inl (Sum.inr .old), x => decide ((x 0 : ℕ) < s.card)
  | _, Sum.inr br, x =>
      (tab.getD ((blockVocab B).index br) []).getD
        (tupleIdx (s.univSize + m + 1) (List.ofFn fun j => (x j : ℕ))) false

omit [L.IsRelational] in
@[simp] theorem extRel_inl_inl (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) {n : ℕ} (r : L.Relations n)
    (x : Fin n → Fin (s.univSize + m + 1)) :
    extRel V B s m tab (Sum.inl (Sum.inl r)) x =
      (andAll (List.ofFn fun j => decide ((x j : ℕ) < s.card)) &&
        (s.table.getD (V.index r) []).getD
          (tupleIdx s.card (List.ofFn fun j => (x j : ℕ))) false) := rfl

/-- The only symbol of the marking vocabulary has arity one. -/
theorem oldArity : ∀ {n : ℕ}, Language.oldMark.Relations n → n = 1
  | _, .old => rfl

omit [L.IsRelational] in
@[simp] theorem extRel_old (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) (x : Fin 1 → Fin (s.univSize + m + 1)) :
    extRel V B s m tab (Sum.inl (Sum.inr Language.oldSym)) x =
      decide ((x 0 : ℕ) < s.card) := rfl

omit [L.IsRelational] in
@[simp] theorem extRel_inr (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) {n : ℕ} (br : B.lang.Relations n)
    (x : Fin n → Fin (s.univSize + m + 1)) :
    extRel V B s m tab (Sum.inr br) x =
      (tab.getD ((blockVocab B).index br) []).getD
        (tupleIdx (s.univSize + m + 1) (List.ofFn fun j => (x j : ℕ))) false := rfl

omit [L.IsRelational] in
theorem extRel_old_eq (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) {n : ℕ} (o : Language.oldMark.Relations n)
    (x : Fin n → Fin (s.univSize + m + 1)) :
    extRel V B s m tab (Sum.inl (Sum.inr o)) x =
      decide ((x (Fin.cast (oldArity o).symm 0) : ℕ) < s.card) := by
  match n, o, x with
  | _, .old, _ => rfl

/-- **The extended structure as data**: the instance, `m` invented values, and
the guessed relations, encoded as one concrete finite structure over the
vocabulary the `∃SO[new]` kernel is read in. -/
noncomputable def extStruct (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) : FinStruct (soVocab V B) :=
  FinStruct.ofTable (soVocab V B) (s.univSize + m) fun R x => extRel V B s m tab R x

omit [L.IsRelational] in
@[simp] theorem relMapBool_extStruct (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) {n : ℕ} (R : ((newLang L).sum B.lang).Relations n)
    (x : Fin n → (extStruct V B s m tab).Univ) :
    (extStruct V B s m tab).relMapBool R x = extRel V B s m tab R x :=
  FinStruct.relMapBool_ofTable _ _ _ R x

/-- The assignment of the relation variables a guessed table denotes. -/
def tabAssign (B : SOBlock) (s : FinStruct V) (m : ℕ) (tab : List (List Bool)) :
    B.Assignment (s.Univ ⊕ Fin m) := fun i z =>
  (tab.getD ((blockVocab B).index (⟨i, rfl⟩ : B.lang.Relations (B.arity i))) []).getD
    (tupleIdx (s.univSize + m + 1)
      (List.ofFn fun j => ((extEquivFin s m (z j) : Fin (s.univSize + m + 1)) : ℕ))) false = true

/-! ### The data is the extended structure of the logic -/

omit [L.IsRelational] in
/-- The tuple of values of an original tuple. -/
theorem ofFn_extEquivFin {n : ℕ} (s : FinStruct V) (m : ℕ) {x : Fin n → s.Univ ⊕ Fin m}
    {y : Fin n → s.Univ} (hy : ∀ j, x j = Sum.inl (y j)) :
    (List.ofFn fun j => ((extEquivFin s m (x j) : Fin (s.univSize + m + 1)) : ℕ)) =
      List.ofFn fun j => ((y j : s.Univ) : ℕ) :=
  congrArg List.ofFn (funext fun j => by rw [hy j]; rfl)

/-- The original symbols of the extended structure read the instance, on
original elements only. -/
theorem extRel_inl_inl_iff {n : ℕ} (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) (r : L.Relations n) (x : Fin n → s.Univ ⊕ Fin m) :
    extRel V B s m tab (Sum.inl (Sum.inl r)) (fun j => extEquivFin s m (x j)) = true ↔
      ∃ y, (∀ j, x j = Sum.inl (y j)) ∧ (RelMap r y : Prop) := by
  rw [extRel_inl_inl, Bool.and_eq_true, andAll_eq_true]
  constructor
  · rintro ⟨hall, hlook⟩
    have hy : ∀ j, ∃ a, x j = Sum.inl a := fun j =>
      (val_extEquivFin_lt s m (x j)).mp (by
        have := hall _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
        simpa using this)
    choose y hy using hy
    refine ⟨y, hy, ?_⟩
    rw [FinStruct.relMap_iff, FinStruct.relMapBool, ← ofFn_extEquivFin s m hy]
    exact hlook
  · rintro ⟨y, hy, hr⟩
    rw [ofFn_extEquivFin s m hy]
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
      simp only [decide_eq_true_eq]
      rw [hy j]
      exact (y j).isLt
    · rw [FinStruct.relMap_iff, FinStruct.relMapBool] at hr
      exact hr

/-- **The extended structure as data is the extended structure of the logic**:
the numbering of `DescriptiveComplexity.extEquivFin` is an isomorphism, for
the assignment the guessed table denotes. -/
noncomputable def extIso (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (tab : List (List Bool)) :
    @Language.Equiv ((newLang L).sum B.lang) (s.Univ ⊕ Fin m) (extStruct V B s m tab).Univ
      (@sumStructure (newLang L) B.lang (s.Univ ⊕ Fin m) (extStructure L s.Univ m)
        (B.structure (tabAssign B s m tab)))
      (FinStruct.instStructure _) :=
  letI : ((newLang L).sum B.lang).Structure (s.Univ ⊕ Fin m) :=
    @sumStructure (newLang L) B.lang (s.Univ ⊕ Fin m) (extStructure L s.Univ m)
      (B.structure (tabAssign B s m tab))
  { toEquiv := extEquivFin s m
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      rw [FinStruct.relMap_iff, relMapBool_extStruct]
      cases R with
      | inl rr =>
        cases rr with
        | inl r => exact (extRel_inl_inl_iff V B s m tab r x).trans Iff.rfl
        | inr o =>
          cases o with
          | old =>
            change decide (((extEquivFin s m (x 0) : Fin (s.univSize + m + 1)) : ℕ) <
              s.card) = true ↔ IsOld (x 0)
            rw [decide_eq_true_eq]
            exact (val_extEquivFin_lt s m (x 0)).trans isOld_iff.symm
      | inr br =>
        obtain ⟨i, hb⟩ := br
        subst hb
        exact Iff.rfl }

/-! ### Every assignment is denoted by a table

The extended universe is finite, so an assignment of the relation variables is
a finite object: it is the reading of *some* list of Boolean tables. This is
the step that turns the second-order existential of `∃SO[new]` into a search
over a `Primcodable` witness. -/

omit [L.IsRelational] in
theorem exists_tab (V : FinVocab L) (B : SOBlock) (s : FinStruct V) (m : ℕ)
    (ρ : B.Assignment (s.Univ ⊕ Fin m)) : ∃ tab, tabAssign B s m tab = ρ := by
  classical
  refine ⟨List.ofFn fun k : Fin (blockNum B) =>
      (List.range ((s.univSize + m + 1) ^ B.arity (blockEq B k))).map fun t =>
        decide (ρ (blockEq B k) fun j =>
          (extEquivFin s m).symm ⟨digitAt (s.univSize + m + 1) t j,
            digitAt_lt (Nat.succ_pos _) t j⟩), ?_⟩
  funext i z
  refine propext ?_
  set C := s.univSize + m + 1 with hC
  set rowFor : B.ι → List Bool := fun i' =>
    (List.range (C ^ B.arity i')).map fun t =>
      decide (ρ i' fun j =>
        (extEquivFin s m).symm ⟨digitAt C t j, digitAt_lt (Nat.succ_pos _) t j⟩) with hrow
  have hidx : ((blockVocab B).index (⟨i, rfl⟩ : B.lang.Relations (B.arity i)) : ℕ) =
      ((blockEq B).symm i : ℕ) := rfl
  have hget : (List.ofFn fun k : Fin (blockNum B) => rowFor (blockEq B k)).getD
      ((blockVocab B).index (⟨i, rfl⟩ : B.lang.Relations (B.arity i))) [] = rowFor i := by
    rw [hidx, List.getD_eq_getElem _ _ (by simp)]
    simp
  have hall : ∀ a ∈ (List.ofFn fun j => ((extEquivFin s m (z j) : Fin C) : ℕ)), a < C := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact (extEquivFin s m (z j)).isLt
  have hlen : (List.ofFn fun j => ((extEquivFin s m (z j) : Fin C) : ℕ)).length = B.arity i := by
    simp
  have hlt : tupleIdx C (List.ofFn fun j => ((extEquivFin s m (z j) : Fin C) : ℕ)) <
      C ^ B.arity i := by
    have := tupleIdx_lt (c := C) hall
    rwa [hlen] at this
  rw [tabAssign, hget, hrow]
  simp only
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range,
    decide_eq_true_eq]
  refine iff_of_eq (congrArg (ρ i) (funext fun j => ?_))
  have hd := digitAt_tupleIdx (c := C) hall (j := (j : ℕ)) (by rw [hlen]; exact j.isLt)
  have hval : digitAt C (tupleIdx C (List.ofFn fun j' =>
      ((extEquivFin s m (z j') : Fin C) : ℕ))) (j : ℕ) =
      ((extEquivFin s m (z j) : Fin C) : ℕ) := by
    rw [hd]
    simp [List.getD_eq_getElem?_getD]
  have heq : (⟨digitAt C (tupleIdx C (List.ofFn fun j' =>
      ((extEquivFin s m (z j') : Fin C) : ℕ))) (j : ℕ),
      digitAt_lt (Nat.succ_pos _) _ _⟩ : Fin C) = extEquivFin s m (z j) := Fin.ext hval
  rw [heq, Equiv.symm_apply_apply]

/-! ### The witness is read primitive recursively -/

omit [L.IsRelational] in
theorem primrec_extStruct (V : FinVocab L) (B : SOBlock) :
    Primrec fun p : FinStruct V × (ℕ × List (List Bool)) =>
      extStruct V B p.1 p.2.1 p.2.2 := by
  have hk : Primrec fun p : FinStruct V × (ℕ × List (List Bool)) =>
      p.1.univSize + p.2.1 :=
    Primrec.nat_add.comp ((FinStruct.primrec_univSize V).comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  refine ((FinStruct.primrec_mk (soVocab V B)).comp hk (Primrec.list_ofFn ?_)).of_eq
    fun _ => rfl
  intro i
  have hC : Primrec fun q : (FinStruct V × (ℕ × List (List Bool))) × ℕ =>
      q.1.1.univSize + q.1.2.1 + 1 :=
    Primrec.succ.comp (hk.comp Primrec.fst)
  have hcard : Primrec fun q : (FinStruct V × (ℕ × List (List Bool))) × ℕ => q.1.1.card :=
    (FinStruct.primrec_card V).comp (Primrec.fst.comp Primrec.fst)
  have hdig : ∀ j : ℕ, Primrec fun q : (FinStruct V × (ℕ × List (List Bool))) × ℕ =>
      digitAt (q.1.1.univSize + q.1.2.1 + 1) q.2 j :=
    fun j => (FirstOrder.Language.primrec_digitAt j).comp hC Primrec.snd
  have hlt : ∀ j : ℕ, Primrec fun q : (FinStruct V × (ℕ × List (List Bool))) × ℕ =>
      decide (digitAt (q.1.1.univSize + q.1.2.1 + 1) q.2 j < q.1.1.card) :=
    fun j => (Primrec.nat_lt.comp (hdig j) hcard).decide
  have htup : Primrec fun q : (FinStruct V × (ℕ × List (List Bool))) × ℕ =>
      List.ofFn fun j : Fin ((soVocab V B).arity i) =>
        digitAt (q.1.1.univSize + q.1.2.1 + 1) q.2 (j : ℕ) :=
    Primrec.list_ofFn fun j => hdig (j : ℕ)
  refine Primrec.list_map
    (Primrec.list_range.comp
      ((FirstOrder.Language.primrec_pow_const
        ((soVocab V B).arity i)).comp (Primrec.succ.comp hk))) ?_
  rcases hsym : (soVocab V B).sym i with (r | o) | br
  · have h := Primrec.and.comp
      (primrec_andAll.comp
        (Primrec.list_ofFn fun j : Fin ((soVocab V B).arity i) => hlt (j : ℕ)))
      ((Primrec.list_getD false).comp
        ((Primrec.list_getD []).comp
          ((FinStruct.primrec_table V).comp (Primrec.fst.comp Primrec.fst))
          (Primrec.const (V.index r : ℕ)))
        (primrec_tupleIdx.comp hcard htup))
    exact h.of_eq fun _ => rfl
  · have h := hlt ((Fin.cast (oldArity o).symm 0 : Fin ((soVocab V B).arity i)) : ℕ)
    exact h.of_eq fun q => (extRel_old_eq V B q.1.1 q.1.2.1 q.1.2.2 o
      (fun j => ⟨digitAt (q.1.1.univSize + q.1.2.1 + 1) q.2 (j : ℕ),
        digitAt_lt (Nat.succ_pos _) _ _⟩)).symm
  · have h := (Primrec.list_getD false).comp
      ((Primrec.list_getD []).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const ((blockVocab B).index br : ℕ)))
      (primrec_tupleIdx.comp hC htup)
    exact h.of_eq fun _ => rfl

end Extended

/-! ### The theorem -/

/-- **A recursively enumerable problem denotes a recursively enumerable set of
concrete instances.** The class `DescriptiveComplexity.RE` is defined by a
logic – definability in `∃SO[new]` – and this is the statement that the name is
honest: through the encoding of `FirstOrder.Language.FinStruct`, its problems
are exactly semi-decidable in Mathlib's sense.

No machine model is involved. The `∃SO[new]` witness – a number of invented
values and an assignment of the relation variables – is a finite object, so it
is searched for; the first-order kernel is checked on it by the primitive
recursive evaluator of `DescriptiveComplexity.Computability.Eval`. -/
theorem RE_subset_rePred {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) (hP : P ∈ RE) : REPred (P.toPred V) := by
  obtain ⟨B, φ₀, hφ⟩ := hP
  -- `soLang (newLang L) [B]` *is* `(newLang L).sum B.lang`; name the kernel at that type
  let φ : ((newLang L).sum B.lang).Sentence := φ₀
  refine rePred_of_exists (β := ℕ × List (List Bool))
    (f := fun (s : FinStruct V) (w : ℕ × List (List Bool)) =>
      FinStruct.evalBF (soVocab V B) φ (extStruct V B s w.1 w.2) [])
    ((FinStruct.primrec_evalSentence (soVocab V B) φ).comp (primrec_extStruct V B)) ?_
  intro s
  have key : ∀ (m : ℕ) (tab : List (List Bool)),
      FinStruct.evalBF (soVocab V B) φ (extStruct V B s m tab) [] = true ↔
        @Sentence.Realize ((newLang L).sum B.lang) (s.Univ ⊕ Fin m)
          (@sumStructure (newLang L) B.lang (s.Univ ⊕ Fin m) (extStructure L s.Univ m)
            (B.structure (tabAssign B s m tab))) φ := by
    intro m tab
    letI : ((newLang L).sum B.lang).Structure (s.Univ ⊕ Fin m) :=
      @sumStructure (newLang L) B.lang (s.Univ ⊕ Fin m) (extStructure L s.Univ m)
        (B.structure (tabAssign B s m tab))
    exact (FinStruct.evalSentence_iff (soVocab V B) φ (extStruct V B s m tab)).trans
      (StrongHomClass.realize_sentence (extIso V B s m tab) φ).symm
  refine Iff.trans (hφ s.Univ) ?_
  constructor
  · rintro ⟨m, ρ, hρ⟩
    obtain ⟨tab, htab⟩ := exists_tab V B s m ρ
    refine ⟨(m, tab), (key m tab).mpr ?_⟩
    rw [htab]
    exact hρ
  · rintro ⟨⟨m, tab⟩, hw⟩
    exact ⟨m, tabAssign B s m tab, (key m tab).mp hw⟩

end DescriptiveComplexity
