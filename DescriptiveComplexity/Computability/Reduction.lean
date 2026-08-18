/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Computability.Eval
import Mathlib.Computability.RE
import Mathlib.Logic.Equiv.Fin.Basic
import DescriptiveComplexity.Relativized
import DescriptiveComplexity.OrderedComposition

/-!
# First-order reductions are computable

The last step of the bridge that does not need a machine:
a first-order interpretation induces a **computable** map of concrete
structures, so `¬ComputablePred` transfers backwards along every reduction
notion of the library – `≤ᶠᵒ`, `≤ᶠᵒ[≤]` and `≤ʳᶠᵒ[≤]`.

Everything is proved for the most general notion, the *relativized ordered*
reduction; the other two are special cases of it
(`DescriptiveComplexity.FOReduction.toOrdered`,
`DescriptiveComplexity.OrderedFOReduction.toRel`).

## What has to be computed

Three things, in this order.

* **The order.** An ordered reduction reads its input over `L.sum
  Language.order`. The universe of a concrete instance is `Fin (n + 1)`, which
  is *already* linearly ordered, so the ordered expansion is built by appending
  one row to the table (`DescriptiveComplexity.ordStruct`) – there is no order
  to choose and none to encode.
* **The renumbering.** The target universe of a relativized interpretation is
  the *subtype* of `Tag × (Fin dim → A)` cut out by the domain formula, so the
  surviving points have to be listed (`DescriptiveComplexity.goodList`) and
  re-indexed into an initial segment of `ℕ`. This is where the `Primrec` work
  concentrates, exactly as the design predicted.
* **The tags.** A defining formula depends on the tags of its arguments, which
  are known only at run time. There are finitely many tag tuples, so the row of
  a target symbol evaluates *all* `|Tag|ⁿ` fixed formulas and selects by an
  index computed from the decoded tags.

The defining formulas have free variables indexed by `Fin n × Fin dim`, while
the evaluator of `DescriptiveComplexity.Computability.Eval` is written for
sentences; `DescriptiveComplexity.flatFormula` flattens the former into the
latter through `Fin.finProdFinEquiv` and
`FirstOrder.Language.BoundedFormula.relabel`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The ordered expansion of an instance, as data -/

section Order

/-- The one-symbol vocabulary of the order, presented. -/
def orderVocab : FinVocab Language.order where
  numSyms := 1
  symOf _ := ⟨2, orderRel.le⟩
  index _ := 0
  symOf_index R := by match R with | .le => rfl
  index_symOf _ := Subsingleton.elim _ _

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)

/-- The rows of the table of an instance, cut to exactly one row per symbol.
Appending anything to a raw table could otherwise be read as the row of a
symbol whose row was missing. -/
def rowsOf (s : FinStruct V) : List (List Bool) :=
  (List.range V.numSyms).map fun k => s.table.getD k []

omit [L.IsRelational] in
theorem getD_rowsOf (s : FinStruct V) {k : ℕ} (hk : k < V.numSyms) :
    (rowsOf V s).getD k [] = s.table.getD k [] := by
  rw [rowsOf, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

omit [L.IsRelational] in
@[simp] theorem length_rowsOf (s : FinStruct V) : (rowsOf V s).length = V.numSyms := by
  simp [rowsOf]

/-- **The ordered expansion of an instance, as data**: the same universe, the
same rows, and one more row for the order of `Fin (n + 1)`. -/
def ordStruct (s : FinStruct V) : FinStruct (V.sum orderVocab) :=
  ⟨s.univSize, rowsOf V s ++
    [(List.range (s.card * s.card)).map fun t =>
      decide (digitAt s.card t 0 ≤ digitAt s.card t 1)]⟩

omit [L.IsRelational] in
@[simp] theorem univSize_ordStruct (s : FinStruct V) : (ordStruct V s).univSize = s.univSize :=
  rfl

omit [L.IsRelational] in
@[simp] theorem card_ordStruct (s : FinStruct V) : (ordStruct V s).card = s.card := rfl

omit [L.IsRelational] in
theorem relMapBool_ordStruct_inl (s : FinStruct V) {n : ℕ} (r : L.Relations n)
    (x : Fin n → (ordStruct V s).Univ) :
    (ordStruct V s).relMapBool (Sum.inl r) x = s.relMapBool r x := by
  have h1 := FinStruct.relMapBool_eq (ordStruct V s)
    (Sum.inl r : (L.sum Language.order).Relations n) x
  have h2 := FinStruct.relMapBool_eq s r x
  rw [h1, h2, FinVocab.val_index_sum_inl]
  congr 1
  rw [ordStruct]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_left (by simp)]
  rw [← List.getD_eq_getElem _ _ (by simp)]
  exact getD_rowsOf V s (V.index r).isLt

omit [L.IsRelational] in
theorem relMapBool_ordStruct_le (s : FinStruct V) (x : Fin 2 → (ordStruct V s).Univ) :
    (ordStruct V s).relMapBool (Sum.inr orderRel.le) x = decide (x 0 ≤ x 1) := by
  have hlt : ∀ i : Fin 2, ((x i : Fin s.card) : ℕ) < s.card := fun i => (x i).isLt
  have hall : ∀ a ∈ (List.ofFn fun j => ((x j : Fin s.card) : ℕ)), a < s.card := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact hlt j
  have hlen : (List.ofFn fun j => ((x j : Fin s.card) : ℕ)).length = 2 := by simp
  have hidx : tupleIdx s.card (List.ofFn fun j => ((x j : Fin s.card) : ℕ)) < s.card * s.card := by
    have := tupleIdx_lt (c := s.card) hall
    rw [hlen] at this
    simpa [pow_two] using this
  have h1 := FinStruct.relMapBool_eq (ordStruct V s)
    (Sum.inr orderRel.le : (L.sum Language.order).Relations 2) x
  have hix : (((V.sum orderVocab).index
      (Sum.inr orderRel.le : (L.sum Language.order).Relations 2) : Fin _) : ℕ) =
      V.numSyms + 0 := FinVocab.val_index_sum_inr V orderVocab orderRel.le
  have hc : tupleIdx (ordStruct V s).card
      (List.ofFn fun j => ((x j : Fin (ordStruct V s).card) : ℕ)) =
      tupleIdx s.card (List.ofFn fun j => ((x j : Fin s.card) : ℕ)) := rfl
  rw [h1, hix, hc]
  have hrow : ((ordStruct V s).table).getD (V.numSyms + 0) [] =
      (List.range (s.card * s.card)).map fun t =>
        decide (digitAt s.card t 0 ≤ digitAt s.card t 1) := by
    rw [ordStruct]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  rw [hrow, List.getD_eq_getElem _ _ (by simpa using hidx)]
  simp only [List.getElem_map, List.getElem_range]
  have h0 := digitAt_tupleIdx (c := s.card) hall (j := 0) (by rw [hlen]; omega)
  have h1 := digitAt_tupleIdx (c := s.card) hall (j := 1) (by rw [hlen]; omega)
  rw [h0, h1]
  simp [List.getD_eq_getElem?_getD, Fin.le_def]

/-- **The data is the ordered expansion**: the identity is an isomorphism from
the encoded ordered expansion to the instance's universe with its own linear
order. -/
def ordIso (s : FinStruct V) :
    @Language.Equiv (L.sum Language.order) (ordStruct V s).Univ s.Univ
      (FinStruct.instStructure _) (sumOrderStructure L s.Univ) where
  toEquiv := Equiv.refl _
  map_fun' f := isEmptyElim f
  map_rel' {n} R x := by
    rw [FinStruct.relMap_iff]
    cases R with
    | inl r =>
      rw [relMapBool_ordStruct_inl]
      exact (FinStruct.relMap_iff s r x).symm
    | inr r =>
      cases r with
      | le =>
        rw [relMapBool_ordStruct_le, decide_eq_true_eq]
        exact Iff.rfl

omit [L.IsRelational] in
theorem primrec_ordStruct : Primrec fun s : FinStruct V => ordStruct V s := by
  have hrows : Primrec fun s : FinStruct V => rowsOf V s :=
    Primrec.list_map (Primrec.const (List.range V.numSyms))
      ((Primrec.list_getD []).comp ((FinStruct.primrec_table V).comp Primrec.fst)
        Primrec.snd).to₂
  have hcard : Primrec fun s : FinStruct V => s.card := FinStruct.primrec_card V
  have hrow : Primrec fun s : FinStruct V =>
      (List.range (s.card * s.card)).map fun t =>
        decide (digitAt s.card t 0 ≤ digitAt s.card t 1) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp hcard hcard))
      ((Primrec.nat_le.comp
        ((FirstOrder.Language.primrec_digitAt 0).comp
          (hcard.comp Primrec.fst) Primrec.snd)
        ((FirstOrder.Language.primrec_digitAt 1).comp
          (hcard.comp Primrec.fst) Primrec.snd)).decide).to₂
  exact ((FinStruct.primrec_mk (V.sum orderVocab)).comp (FinStruct.primrec_univSize V)
    (Primrec.list_append.comp hrows
      (Primrec.list_cons.comp hrow (Primrec.const [])))).of_eq fun _ => rfl

end Order

/-! ### Numbering the tagged tuples

A point of the target universe of an interpretation is a tag together with a
`dim`-tuple of elements of the instance. It is numbered by putting the tag in
the units digit, base `|Tag|`, and the tuple above it. -/

section Points

variable {L : Language.{0, 0}} [L.IsRelational] {V : FinVocab L} {Tag : Type} {dim : ℕ}

/-- The number of a tagged tuple. -/
def ptIdx (T : ℕ) (tagEq : Fin (T + 1) ≃ Tag) (s : FinStruct V)
    (p : Tag × (Fin dim → s.Univ)) : ℕ :=
  ((tagEq.symm p.1 : Fin (T + 1)) : ℕ) +
    (T + 1) * tupleIdx s.card (List.ofFn fun j => ((p.2 j : s.Univ) : ℕ))

/-- The tagged tuple with a given number. -/
def ptOfIdx (T : ℕ) (tagEq : Fin (T + 1) ≃ Tag) (dim : ℕ) (s : FinStruct V) (u : ℕ) :
    Tag × (Fin dim → s.Univ) :=
  (tagEq ⟨u % (T + 1), Nat.mod_lt _ (Nat.succ_pos T)⟩,
    fun j => ⟨digitAt s.card (u / (T + 1)) (j : ℕ), digitAt_lt (Nat.succ_pos _) _ _⟩)

omit [L.IsRelational] in
theorem ptIdx_lt (T : ℕ) (tagEq : Fin (T + 1) ≃ Tag) (s : FinStruct V)
    (p : Tag × (Fin dim → s.Univ)) : ptIdx T tagEq s p < (T + 1) * s.card ^ dim := by
  have hall : ∀ a ∈ (List.ofFn fun j => ((p.2 j : s.Univ) : ℕ)), a < s.card := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact (p.2 j).isLt
  have hlt : tupleIdx s.card (List.ofFn fun j => ((p.2 j : s.Univ) : ℕ)) < s.card ^ dim := by
    have := tupleIdx_lt (c := s.card) hall
    simpa using this
  have ht : ((tagEq.symm p.1 : Fin (T + 1)) : ℕ) < T + 1 := (tagEq.symm p.1).isLt
  have hstep : (T + 1) * tupleIdx s.card (List.ofFn fun j => ((p.2 j : s.Univ) : ℕ)) + (T + 1) ≤
      (T + 1) * s.card ^ dim := by
    have h1 : (T + 1) * (tupleIdx s.card (List.ofFn fun j => ((p.2 j : s.Univ) : ℕ)) + 1) ≤
        (T + 1) * s.card ^ dim := Nat.mul_le_mul_left _ hlt
    rwa [Nat.mul_succ] at h1
  rw [ptIdx]
  omega

omit [L.IsRelational] in
theorem ptOfIdx_ptIdx (T : ℕ) (tagEq : Fin (T + 1) ≃ Tag) (s : FinStruct V)
    (p : Tag × (Fin dim → s.Univ)) : ptOfIdx T tagEq dim s (ptIdx T tagEq s p) = p := by
  have hall : ∀ a ∈ (List.ofFn fun j => ((p.2 j : s.Univ) : ℕ)), a < s.card := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact (p.2 j).isLt
  have hlen : (List.ofFn fun j => ((p.2 j : s.Univ) : ℕ)).length = dim := by simp
  have ht : ((tagEq.symm p.1 : Fin (T + 1)) : ℕ) < T + 1 := (tagEq.symm p.1).isLt
  have hmod : ptIdx T tagEq s p % (T + 1) = ((tagEq.symm p.1 : Fin (T + 1)) : ℕ) := by
    rw [ptIdx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  have hdiv : ptIdx T tagEq s p / (T + 1) =
      tupleIdx s.card (List.ofFn fun j => ((p.2 j : s.Univ) : ℕ)) := by
    rw [ptIdx, Nat.add_mul_div_left _ _ (Nat.succ_pos T), Nat.div_eq_of_lt ht]
    omega
  refine Prod.ext ?_ ?_
  · rw [ptOfIdx]
    refine Eq.trans (congrArg tagEq (Fin.ext ?_)) (tagEq.apply_symm_apply p.1)
    exact hmod
  · funext j
    refine Fin.ext ?_
    change digitAt s.card (ptIdx T tagEq s p / (T + 1)) (j : ℕ) = ((p.2 j : s.Univ) : ℕ)
    rw [hdiv, digitAt_tupleIdx (c := s.card) hall (j := (j : ℕ)) (by rw [hlen]; exact j.isLt)]
    simp [List.getD_eq_getElem?_getD]

omit [L.IsRelational] in
theorem ptIdx_ptOfIdx (T : ℕ) (tagEq : Fin (T + 1) ≃ Tag) (s : FinStruct V) {u : ℕ}
    (hu : u < (T + 1) * s.card ^ dim) : ptIdx T tagEq s (ptOfIdx T tagEq dim s u) = u := by
  have hdiv : u / (T + 1) < s.card ^ dim := by
    rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos T), Nat.mul_comm]
    exact hu
  have h1 : ((tagEq.symm (tagEq ⟨u % (T + 1), Nat.mod_lt _ (Nat.succ_pos T)⟩) :
      Fin (T + 1)) : ℕ) = u % (T + 1) := by rw [Equiv.symm_apply_apply]
  rw [ptIdx, ptOfIdx]
  simp only [h1]
  rw [show (List.ofFn fun j : Fin dim =>
      ((⟨digitAt s.card (u / (T + 1)) (j : ℕ), digitAt_lt (Nat.succ_pos _) _ _⟩ :
        s.Univ) : ℕ)) = List.ofFn fun j : Fin dim => digitAt s.card (u / (T + 1)) (j : ℕ) from rfl,
    tupleIdx_ofFn_digitAt, Nat.mod_eq_of_lt hdiv, Nat.mod_add_div]

end Points

/-! ### Flattening the defining formulas

The evaluator of `DescriptiveComplexity.Computability.Eval` is written for
formulas with no free variables, while a defining formula has free variables
indexed by `Fin n × Fin dim` and a domain formula by `Fin dim`. Both are
relabelled into bound variables, the pairs through `finProdFinEquiv`. -/

section Flatten

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}
  (I : RelFOInterpretation (L.sum Language.order) L' Tag dim)

/-- A defining formula, with its free variables turned into bound ones. -/
def flatRel {n : ℕ} (R : L'.Relations n) (τ : Fin n → Tag) :
    (L.sum Language.order).BoundedFormula Empty (n * dim) :=
  BoundedFormula.relabel Sum.inr (Formula.relabel finProdFinEquiv (I.relFormula R τ))

/-- A domain formula, with its free variables turned into bound ones. -/
def flatDom (t : Tag) : (L.sum Language.order).BoundedFormula Empty dim :=
  BoundedFormula.relabel Sum.inr (I.domFormula t)

variable {M : Type} [(L.sum Language.order).Structure M]

theorem realize_flatRel {n : ℕ} (R : L'.Relations n) (τ : Fin n → Tag)
    (v : Empty → M) (x : Fin (n * dim) → M) :
    (flatRel I R τ).Realize v x ↔ (I.relFormula R τ).Realize (x ∘ finProdFinEquiv) :=
  (Formula.realize_relabel_sumInr _).trans Formula.realize_relabel

theorem realize_flatDom (t : Tag) (v : Empty → M) (x : Fin dim → M) :
    (flatDom I t).Realize v x ↔ (I.domFormula t).Realize x :=
  Formula.realize_relabel_sumInr _

end Flatten

/-! ### Evaluating the defining formulas at numbered points -/

section Eval

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {Tag : Type} {dim : ℕ} (I : RelFOInterpretation (L.sum Language.order) L' Tag dim)
  (T : ℕ) (tagEq : Fin (T + 1) ≃ Tag) (V : FinVocab L)

omit [L'.IsRelational] in
/-- Evaluating a formula on the encoded ordered expansion is realizing it on
the instance's universe with its own linear order. -/
theorem evalBF_ord_iff (s : FinStruct V) {l : ℕ}
    (φ : (L.sum Language.order).BoundedFormula Empty l) (xs : List ℕ) (h : xs.length = l) :
    FinStruct.evalBF (V.sum orderVocab) φ (ordStruct V s) xs = true ↔
      @BoundedFormula.Realize (L.sum Language.order) s.Univ (sumOrderStructure L s.Univ) Empty l
        φ Empty.elim (fun i : Fin l => FinStruct.valOf (ordStruct V s) xs (i : ℕ)) := by
  rw [FinStruct.evalBF_iff _ φ _ xs h]
  have key := StrongHomClass.realize_boundedFormula (L := L.sum Language.order)
    (g := ordIso V s) φ (v := Empty.elim)
    (xs := fun i : Fin l => FinStruct.valOf (ordStruct V s) xs (i : ℕ))
  have h1 : (⇑(ordIso V s) ∘ (Empty.elim : Empty → (ordStruct V s).Univ)) = Empty.elim :=
    funext fun e => e.elim
  have h2 : (⇑(ordIso V s) ∘ fun i : Fin l => FinStruct.valOf (ordStruct V s) xs (i : ℕ)) =
      fun i : Fin l => FinStruct.valOf (ordStruct V s) xs (i : ℕ) := rfl
  rw [h1, h2] at key
  exact key.symm

omit [L.IsRelational] [L'.IsRelational] in
/-- The valuation read off a list of digits is the tuple those digits are. -/
theorem valOf_ofFn_digitAt (s : FinStruct V) {d : ℕ} (v : ℕ) (i : Fin d) :
    FinStruct.valOf (ordStruct V s)
        (List.ofFn fun j : Fin d => digitAt s.card v (j : ℕ)) (i : ℕ) =
      (⟨digitAt s.card v (i : ℕ), digitAt_lt (Nat.succ_pos _) _ _⟩ : s.Univ) := by
  refine Fin.ext ?_
  change (List.ofFn fun j : Fin d => digitAt s.card v (j : ℕ)).getD (i : ℕ) 0 %
    (ordStruct V s).card = digitAt s.card v (i : ℕ)
  have hg : (List.ofFn fun j : Fin d => digitAt s.card v (j : ℕ)).getD (i : ℕ) 0 =
      digitAt s.card v (i : ℕ) := by
    simp [List.getD_eq_getElem?_getD, i.isLt]
  rw [hg]
  exact Nat.mod_eq_of_lt (digitAt_lt (Nat.succ_pos _) _ _)

/-- **Does the point numbered `u` survive the domain formula?** The tag is only
known at run time, so all `|Tag|` domain formulas are evaluated and the right
one is selected. -/
def domBool (s : FinStruct V) (u : ℕ) : Bool :=
  (List.ofFn fun m : Fin (T + 1) =>
      FinStruct.evalBF (V.sum orderVocab) (flatDom I (tagEq m)) (ordStruct V s)
        (List.ofFn fun j : Fin dim => digitAt s.card (u / (T + 1)) (j : ℕ))).getD
    (u % (T + 1)) false

omit [L'.IsRelational] in
theorem domBool_iff (s : FinStruct V) (u : ℕ) :
    domBool I T tagEq V s u = true ↔
      @Formula.Realize (L.sum Language.order) s.Univ (sumOrderStructure L s.Univ) (Fin dim)
        (I.domFormula (ptOfIdx T tagEq dim s u).1) (ptOfIdx T tagEq dim s u).2 := by
  have hlt : u % (T + 1) < T + 1 := Nat.mod_lt _ (Nat.succ_pos T)
  rw [domBool, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
  refine Iff.trans (evalBF_ord_iff V s _ _ (by simp)) ?_
  refine Iff.trans (realize_flatDom I _ _ _) ?_
  exact iff_of_eq (congrArg _ (funext fun i => valOf_ofFn_digitAt V s _ i))

/-- **The value of a defining formula at a tuple of numbered points.** The tags
are only known at run time, so all `|Tag|ⁿ` instances of the formula are
evaluated and the right one is selected. -/
def relBool (s : FinStruct V) {n : ℕ} (R : L'.Relations n) (p : List ℕ) : Bool :=
  (List.ofFn fun m : Fin ((T + 1) ^ n) =>
      FinStruct.evalBF (V.sum orderVocab)
        (flatRel I R fun i : Fin n =>
          tagEq ⟨digitAt (T + 1) (m : ℕ) (i : ℕ), digitAt_lt (Nat.succ_pos T) _ _⟩)
        (ordStruct V s)
        (List.ofFn fun q : Fin (n * dim) =>
          digitAt s.card (p.getD ((finProdFinEquiv.symm q).1 : ℕ) 0 / (T + 1))
            ((finProdFinEquiv.symm q).2 : ℕ))).getD
    (tupleIdx (T + 1) (List.ofFn fun i : Fin n => p.getD (i : ℕ) 0 % (T + 1))) false

omit [L.IsRelational] [L'.IsRelational] in
/-- The valuation read off the pair-indexed list of digits. -/
theorem valOf_ofFn_pair (s : FinStruct V) {n : ℕ} (p : List ℕ) (q : Fin n × Fin dim) :
    FinStruct.valOf (ordStruct V s)
        (List.ofFn fun q' : Fin (n * dim) =>
          digitAt s.card (p.getD ((finProdFinEquiv.symm q').1 : ℕ) 0 / (T + 1))
            ((finProdFinEquiv.symm q').2 : ℕ))
        ((finProdFinEquiv q : Fin (n * dim)) : ℕ) =
      (⟨digitAt s.card (p.getD (q.1 : ℕ) 0 / (T + 1)) (q.2 : ℕ),
        digitAt_lt (Nat.succ_pos _) _ _⟩ : s.Univ) := by
  refine Fin.ext ?_
  have hg : (List.ofFn fun q' : Fin (n * dim) =>
      digitAt s.card (p.getD ((finProdFinEquiv.symm q').1 : ℕ) 0 / (T + 1))
        ((finProdFinEquiv.symm q').2 : ℕ)).getD ((finProdFinEquiv q : Fin (n * dim)) : ℕ) 0 =
      digitAt s.card (p.getD (q.1 : ℕ) 0 / (T + 1)) (q.2 : ℕ) := by
    rw [List.getD_eq_getElem _ _ (by simpa using (finProdFinEquiv q).isLt), List.getElem_ofFn]
    change digitAt s.card
      (p.getD ((finProdFinEquiv.symm (finProdFinEquiv q)).1 : ℕ) 0 / (T + 1))
      ((finProdFinEquiv.symm (finProdFinEquiv q)).2 : ℕ) = _
    rw [Equiv.symm_apply_apply]
  change (List.ofFn _).getD _ 0 % (ordStruct V s).card = _
  rw [hg]
  exact Nat.mod_eq_of_lt (digitAt_lt (Nat.succ_pos _) _ _)

omit [L'.IsRelational] in
theorem relBool_iff (s : FinStruct V) {n : ℕ} (R : L'.Relations n) (p : List ℕ) :
    relBool I T tagEq V s R p = true ↔
      @Formula.Realize (L.sum Language.order) s.Univ (sumOrderStructure L s.Univ)
        (Fin n × Fin dim)
        (I.relFormula R fun i => (ptOfIdx T tagEq dim s (p.getD (i : ℕ) 0)).1)
        (fun q => (ptOfIdx T tagEq dim s (p.getD (q.1 : ℕ) 0)).2 q.2) := by
  have hall : ∀ a ∈ (List.ofFn fun i : Fin n => p.getD (i : ℕ) 0 % (T + 1)), a < T + 1 := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Nat.mod_lt _ (Nat.succ_pos T)
  have hlen : (List.ofFn fun i : Fin n => p.getD (i : ℕ) 0 % (T + 1)).length = n := by simp
  have hlt : tupleIdx (T + 1) (List.ofFn fun i : Fin n => p.getD (i : ℕ) 0 % (T + 1)) <
      (T + 1) ^ n := by
    have := tupleIdx_lt (c := T + 1) hall
    rwa [hlen] at this
  rw [relBool, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
  have htag : (fun i : Fin n =>
      tagEq ⟨digitAt (T + 1)
        ((⟨tupleIdx (T + 1) (List.ofFn fun i : Fin n => p.getD (i : ℕ) 0 % (T + 1)),
          by simpa using hlt⟩ : Fin ((T + 1) ^ n)) : ℕ) (i : ℕ),
        digitAt_lt (Nat.succ_pos T) _ _⟩) =
      fun i : Fin n => (ptOfIdx T tagEq dim s (p.getD (i : ℕ) 0)).1 := by
    funext i
    refine congrArg tagEq (Fin.ext ?_)
    change digitAt (T + 1)
      (tupleIdx (T + 1) (List.ofFn fun i : Fin n => p.getD (i : ℕ) 0 % (T + 1))) (i : ℕ) =
      p.getD (i : ℕ) 0 % (T + 1)
    rw [digitAt_tupleIdx (c := T + 1) hall (j := (i : ℕ)) (by rw [hlen]; exact i.isLt)]
    simp [List.getD_eq_getElem?_getD]
  rw [htag]
  refine Iff.trans (evalBF_ord_iff V s _ _ (by simp)) ?_
  refine Iff.trans (realize_flatRel I R _ _ _) ?_
  exact iff_of_eq (congrArg _ (funext fun q => valOf_ofFn_pair T V s p q))

/-! ### The surviving points, and the image instance -/

variable (V' : FinVocab L')

omit [L'.IsRelational] in
/-- **The numbers of the points that survive the domain formula**, in
increasing order: the renumbering of the target universe is the position in
this list. -/
def goodList (s : FinStruct V) : List ℕ :=
  (List.range ((T + 1) * s.card ^ dim)).filter (domBool I T tagEq V s)

omit [L'.IsRelational] in
theorem mem_goodList (s : FinStruct V) (u : ℕ) :
    u ∈ goodList I T tagEq V s ↔
      u < (T + 1) * s.card ^ dim ∧ domBool I T tagEq V s u = true := by
  simp [goodList, List.mem_filter]

omit [L'.IsRelational] in
theorem nodup_goodList (s : FinStruct V) : (goodList I T tagEq V s).Nodup :=
  (List.nodup_range).filter _

omit [L'.IsRelational] in
theorem getD_goodList_mem (s : FinStruct V) {j : ℕ} (hj : j < (goodList I T tagEq V s).length) :
    (goodList I T tagEq V s).getD j 0 ∈ goodList I T tagEq V s := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

/-- **The image of an instance under a relativized interpretation, as data.**
The universe is the list of surviving points, renumbered by position; a
relation holds of a tuple exactly when the defining formula does of the points
it names. -/
noncomputable def mapStruct (s : FinStruct V) : FinStruct V' :=
  FinStruct.ofTable V' ((goodList I T tagEq V s).length - 1) fun R' x =>
    relBool I T tagEq V s R'
      (List.ofFn fun j => (goodList I T tagEq V s).getD ((x j : ℕ)) 0)

omit [L'.IsRelational] in
@[simp] theorem card_mapStruct (s : FinStruct V) :
    (mapStruct I T tagEq V V' s).card = (goodList I T tagEq V s).length - 1 + 1 := rfl

omit [L'.IsRelational] in
theorem relMapBool_mapStruct (s : FinStruct V) {a : ℕ} (R' : L'.Relations a)
    (x : Fin a → (mapStruct I T tagEq V V' s).Univ) :
    (mapStruct I T tagEq V V' s).relMapBool R' x =
      relBool I T tagEq V s R'
        (List.ofFn fun j => (goodList I T tagEq V s).getD ((x j : ℕ)) 0) :=
  FinStruct.relMapBool_ofTable _ _ _ R' x

/-! ### Everything above is primitive recursive -/

theorem filter_eq_flatMap (p : ℕ → Bool) (l : List ℕ) :
    l.filter p = l.flatMap fun a => bif p a then [a] else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih]

omit [L'.IsRelational] in
theorem primrec_domBool :
    Primrec fun q : FinStruct V × ℕ => domBool I T tagEq V q.1 q.2 := by
  have hcard : Primrec fun q : FinStruct V × ℕ => q.1.card :=
    (FinStruct.primrec_card V).comp Primrec.fst
  have hval : Primrec fun q : FinStruct V × ℕ =>
      List.ofFn fun j : Fin dim => digitAt q.1.card (q.2 / (T + 1)) (j : ℕ) :=
    Primrec.list_ofFn fun j =>
      (FirstOrder.Language.primrec_digitAt (j : ℕ)).comp hcard
        (Primrec.nat_div.comp Primrec.snd (Primrec.const (T + 1)))
  have hord : Primrec fun q : FinStruct V × ℕ => ordStruct V q.1 :=
    (primrec_ordStruct V).comp Primrec.fst
  exact ((Primrec.list_getD false).comp
    (Primrec.list_ofFn fun m : Fin (T + 1) =>
      (FinStruct.primrec_evalBF (V.sum orderVocab) (flatDom I (tagEq m))).comp
        (hord.pair hval))
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const (T + 1)))).of_eq fun _ => rfl

omit [L'.IsRelational] in
theorem primrec_relBool {n : ℕ} (R : L'.Relations n) :
    Primrec fun q : FinStruct V × List ℕ => relBool I T tagEq V q.1 R q.2 := by
  have hcard : Primrec fun q : FinStruct V × List ℕ => q.1.card :=
    (FinStruct.primrec_card V).comp Primrec.fst
  have hval : Primrec fun q : FinStruct V × List ℕ =>
      List.ofFn fun q' : Fin (n * dim) =>
        digitAt q.1.card (q.2.getD ((finProdFinEquiv.symm q').1 : ℕ) 0 / (T + 1))
          ((finProdFinEquiv.symm q').2 : ℕ) :=
    Primrec.list_ofFn fun q' =>
      (FirstOrder.Language.primrec_digitAt ((finProdFinEquiv.symm q').2 : ℕ)).comp hcard
        (Primrec.nat_div.comp
          ((Primrec.list_getD 0).comp Primrec.snd
            (Primrec.const ((finProdFinEquiv.symm q').1 : ℕ)))
          (Primrec.const (T + 1)))
  have hord : Primrec fun q : FinStruct V × List ℕ => ordStruct V q.1 :=
    (primrec_ordStruct V).comp Primrec.fst
  have htag : Primrec fun q : FinStruct V × List ℕ =>
      tupleIdx (T + 1) (List.ofFn fun i : Fin n => q.2.getD (i : ℕ) 0 % (T + 1)) :=
    FirstOrder.Language.primrec_tupleIdx.comp (Primrec.const (T + 1))
      (Primrec.list_ofFn fun i =>
        Primrec.nat_mod.comp
          ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const (i : ℕ)))
          (Primrec.const (T + 1)))
  exact ((Primrec.list_getD false).comp
    (Primrec.list_ofFn fun m : Fin ((T + 1) ^ n) =>
      (FinStruct.primrec_evalBF (V.sum orderVocab)
        (flatRel I R fun i : Fin n =>
          tagEq ⟨digitAt (T + 1) (m : ℕ) (i : ℕ), digitAt_lt (Nat.succ_pos T) _ _⟩)).comp
        (hord.pair hval))
    htag).of_eq fun _ => rfl

omit [L'.IsRelational] in
theorem primrec_goodList : Primrec fun s : FinStruct V => goodList I T tagEq V s := by
  have hcard : Primrec fun s : FinStruct V => s.card := FinStruct.primrec_card V
  have hrange : Primrec fun s : FinStruct V => List.range ((T + 1) * s.card ^ dim) :=
    Primrec.list_range.comp
      (Primrec.nat_mul.comp (Primrec.const (T + 1))
        ((FirstOrder.Language.primrec_pow_const dim).comp hcard))
  refine (Primrec.list_flatMap hrange
    (Primrec.cond (primrec_domBool I T tagEq V)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (Primrec.const [])).to₂).of_eq fun s => ?_
  exact (filter_eq_flatMap _ _).symm

omit [L'.IsRelational] in
theorem primrec_mapStruct :
    Primrec fun s : FinStruct V => mapStruct I T tagEq V V' s := by
  have hgood : Primrec fun s : FinStruct V => goodList I T tagEq V s :=
    primrec_goodList I T tagEq V
  have hk : Primrec fun s : FinStruct V => (goodList I T tagEq V s).length - 1 :=
    Primrec.nat_sub.comp (Primrec.list_length.comp hgood) (Primrec.const 1)
  refine ((FinStruct.primrec_mk V').comp hk (Primrec.list_ofFn ?_)).of_eq fun _ => rfl
  intro i'
  have hp : Primrec fun q : FinStruct V × ℕ =>
      List.ofFn fun j : Fin (V'.arity i') =>
        (goodList I T tagEq V q.1).getD
          (digitAt ((goodList I T tagEq V q.1).length - 1 + 1) q.2 (j : ℕ)) 0 :=
    Primrec.list_ofFn fun j =>
      (Primrec.list_getD 0).comp (hgood.comp Primrec.fst)
        ((FirstOrder.Language.primrec_digitAt (j : ℕ)).comp
          (Primrec.succ.comp (hk.comp Primrec.fst)) Primrec.snd)
  exact Primrec.list_map
    (Primrec.list_range.comp
      ((FirstOrder.Language.primrec_pow_const (V'.arity i')).comp (Primrec.succ.comp hk)))
    ((primrec_relBool I T tagEq V (V'.sym i')).comp (Primrec.fst.pair hp))

/-! ### The data is the image structure -/

omit [L.IsRelational] [L'.IsRelational] in
theorem getD_ofFn_nat {a : ℕ} (g : Fin a → ℕ) (i : Fin a) : (List.ofFn g).getD (i : ℕ) 0 = g i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **The renumbering is an isomorphism**: the encoded image of an instance is
the relativized interpretation of that instance. -/
noncomputable def mapIso (s : FinStruct V) (hne : 0 < (goodList I T tagEq V s).length) :
    (mapStruct I T tagEq V V' s).Univ ≃[L']
      @RelFOInterpretation.MapRel (L.sum Language.order) L' Tag dim I s.Univ
        (sumOrderStructure L s.Univ) :=
  letI : (L.sum Language.order).Structure s.Univ := sumOrderStructure L s.Univ
  have hcard : (mapStruct I T tagEq V V' s).card = (goodList I T tagEq V s).length := by
    simp only [card_mapStruct]; omega
  have hmem : ∀ j : (mapStruct I T tagEq V V' s).Univ,
      (goodList I T tagEq V s).getD ((j : ℕ)) 0 ∈ goodList I T tagEq V s := fun j =>
    getD_goodList_mem I T tagEq V s (by have := j.isLt; omega)
  have hdom : ∀ j : (mapStruct I T tagEq V V' s).Univ,
      (I.domFormula (ptOfIdx T tagEq dim s ((goodList I T tagEq V s).getD ((j : ℕ)) 0)).1).Realize
        (ptOfIdx T tagEq dim s ((goodList I T tagEq V s).getD ((j : ℕ)) 0)).2 := fun j =>
    (domBool_iff I T tagEq V s _).mp (((mem_goodList I T tagEq V s _).mp (hmem j)).2)
  { toFun := fun j => ⟨ptOfIdx T tagEq dim s ((goodList I T tagEq V s).getD ((j : ℕ)) 0), hdom j⟩
    invFun := fun x =>
      ⟨(goodList I T tagEq V s).idxOf (ptIdx T tagEq s x.1), by
        have hx : ptIdx T tagEq s x.1 ∈ goodList I T tagEq V s := by
          refine (mem_goodList I T tagEq V s _).mpr ⟨ptIdx_lt T tagEq s x.1, ?_⟩
          refine (domBool_iff I T tagEq V s _).mpr ?_
          rw [ptOfIdx_ptIdx T tagEq s x.1]
          exact x.2
        have := List.idxOf_lt_length_iff.mpr hx
        omega⟩
    left_inv := fun j => by
      refine Fin.ext ?_
      have hj : (j : ℕ) < (goodList I T tagEq V s).length := by have := j.isLt; omega
      have hlt : (goodList I T tagEq V s).getD ((j : ℕ)) 0 < (T + 1) * s.card ^ dim :=
        ((mem_goodList I T tagEq V s _).mp (hmem j)).1
      change (goodList I T tagEq V s).idxOf
        (ptIdx T tagEq s (ptOfIdx T tagEq dim s ((goodList I T tagEq V s).getD ((j : ℕ)) 0))) =
        (j : ℕ)
      rw [ptIdx_ptOfIdx T tagEq s hlt, List.getD_eq_getElem _ _ hj]
      exact (nodup_goodList I T tagEq V s).idxOf_getElem (j : ℕ) hj
    right_inv := fun x => by
      refine Subtype.ext ?_
      have hx : ptIdx T tagEq s x.1 ∈ goodList I T tagEq V s := by
        refine (mem_goodList I T tagEq V s _).mpr ⟨ptIdx_lt T tagEq s x.1, ?_⟩
        refine (domBool_iff I T tagEq V s _).mpr ?_
        rw [ptOfIdx_ptIdx T tagEq s x.1]
        exact x.2
      have hg : (goodList I T tagEq V s).getD
          ((goodList I T tagEq V s).idxOf (ptIdx T tagEq s x.1)) 0 = ptIdx T tagEq s x.1 := by
        rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr hx)]
        exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hx)
      change ptOfIdx T tagEq dim s ((goodList I T tagEq V s).getD
        ((goodList I T tagEq V s).idxOf (ptIdx T tagEq s x.1)) 0) = x.1
      rw [hg, ptOfIdx_ptIdx]
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {a} R' x => by
      rw [RelFOInterpretation.relMap_mapRel, FinStruct.relMap_iff, relMapBool_mapStruct,
        relBool_iff]
      have hg : ∀ i : Fin a,
          (List.ofFn fun j : Fin a =>
            (goodList I T tagEq V s).getD ((x j : ℕ)) 0).getD ((i : ℕ)) 0 =
            (goodList I T tagEq V s).getD ((x i : ℕ)) 0 := fun i => getD_ofFn_nat _ i
      exact iff_of_eq (congrArg₂ Formula.Realize
        (congrArg (I.relFormula R')
          (funext fun i => congrArg (fun u => (ptOfIdx T tagEq dim s u).1) (hg i).symm))
        (funext fun q => congrArg (fun u => (ptOfIdx T tagEq dim s u).2 q.2) (hg q.1).symm)) }

end Eval

/-! ### Decidability transfers along reductions -/

section Transfer

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'}

/-- **A relativized ordered reduction is a computable many-one reduction** of
the induced sets of concrete instances: if the target is decidable, so is the
source.

The renumbering forced by the definable domain is the whole content; the
interpretation itself is an evaluation of fixed formulas, primitive recursive
by `FirstOrder.Language.FinStruct.primrec_evalBF`. -/
theorem computablePred_of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q)
    (V : FinVocab L) (V' : FinVocab L') (hQ : ComputablePred (Q.toPred V')) :
    ComputablePred (P.toPred V) := by
  classical
  let := f.tagFinite
  obtain ⟨t0, -, -⟩ := f.dom_nonempty (⟨0, []⟩ : FinStruct V).Univ
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin f.Tag
  obtain ⟨T, rfl⟩ : ∃ T, k = T + 1 := by
    match k, e with
    | 0, e => exact (e t0).elim0
    | T + 1, _ => exact ⟨T, rfl⟩
  have hiff : ∀ s : FinStruct V, Q.toPred V' (mapStruct f.toRelInterpretation T e.symm V V' s) ↔
      P.toPred V s := by
    intro s
    obtain ⟨t, w, hw⟩ := f.dom_nonempty s.Univ
    have hmem : ptIdx T e.symm s (t, w) ∈ goodList f.toRelInterpretation T e.symm V s := by
      refine (mem_goodList _ _ _ _ _ _).mpr ⟨ptIdx_lt T e.symm s (t, w), ?_⟩
      refine (domBool_iff _ _ _ _ _ _).mpr ?_
      rw [ptOfIdx_ptIdx T e.symm s (t, w)]
      exact hw
    have hne : 0 < (goodList f.toRelInterpretation T e.symm V s).length :=
      List.length_pos_of_mem hmem
    exact (Q.iso_invariant (mapIso f.toRelInterpretation T e.symm V V' s hne)).trans
      (f.correct s.Univ).symm
  obtain ⟨D, hD⟩ := hQ
  refine ComputablePred.of_eq (p := fun s : FinStruct V =>
    Q.toPred V' (mapStruct f.toRelInterpretation T e.symm V V' s))
    ⟨fun s => D _, hD.comp (primrec_mapStruct f.toRelInterpretation T e.symm V V').to_comp⟩ hiff

/-- **`¬ComputablePred` transfers backwards along a relativized ordered
reduction.** -/
theorem not_computablePred_of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q)
    (V : FinVocab L) (V' : FinVocab L') (hP : ¬ComputablePred (P.toPred V)) :
    ¬ComputablePred (Q.toPred V') :=
  fun hQ => hP (computablePred_of_relOrderedReduction f V V' hQ)

end Transfer

end DescriptiveComplexity
