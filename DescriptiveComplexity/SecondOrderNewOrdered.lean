/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewPull
import DescriptiveComplexity.SecondOrderOrdered

/-!
# Closure of `∃SO[new]` definability under ordered FO reductions

If `P ≤ᶠᵒ[≤] Q` and `Q` is `∃SO[new]`-definable, then so is `P`
(`DescriptiveComplexity.SigmaSONewDefinable.of_orderedReduction`). With the
pullback of `DescriptiveComplexity.SecondOrderNewPull` this is the second
closure property a complexity class needs, and RE becomes one
(`DescriptiveComplexity.RecursivelyEnumerable`).

The shape is the one of `DescriptiveComplexity.SecondOrderOrdered`: pulling the
definition back through the interpretation yields a sentence over the *ordered*
expansion – correct for every linear order on the instance, by order-invariance
of the reduction – and the order is then re-quantified inside the second-order
block, guarded by a sentence saying that the variable is a linear order.

**What value invention changes.** The order variable now ranges over the
*extended* universe `A ⊕ Fin n`, where it cannot be a linear order at all: the
order symbol of the extended structure relates original elements only (invented
values are related to nothing, by `DescriptiveComplexity.extBase`), so the
guard must be *relativized*: `DescriptiveComplexity.extLinearGuard` states that
the variable relates original elements only, and is reflexive and total on
them. That is exactly enough to recover a `LinearOrder` on the instance
(`DescriptiveComplexity.linearOrderOfGuard`) and to know that the variable *is*
the order of the extended structure (`DescriptiveComplexity.extLeRel`), which
is what the language morphism `DescriptiveComplexity.extOrderElim` needs to be
an expansion.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The order of the instance, seen in the extended universe -/

section ExtLe

variable (A : Type) [LE A] (n : ℕ)

/-- The order of the instance, as a relation on the extended universe: it
relates two original elements when their values are ordered, and relates
nothing else. -/
def extLeRel : (Fin 2 → A ⊕ Fin n) → Prop :=
  fun w => ∃ y : Fin 2 → A, (∀ i, w i = Sum.inl (y i)) ∧ y 0 ≤ y 1

variable {A n}

theorem extLeRel_isOld {w : Fin 2 → A ⊕ Fin n} (h : extLeRel A n w) :
    IsOld (w 0) ∧ IsOld (w 1) := by
  obtain ⟨y, hy, -⟩ := h
  exact ⟨(hy 0).symm ▸ isOld_inl (y 0), (hy 1).symm ▸ isOld_inl (y 1)⟩

@[simp]
theorem extLeRel_inl (a b : A) : extLeRel A n ![Sum.inl a, Sum.inl b] ↔ a ≤ b := by
  refine ⟨fun ⟨y, hy, hle⟩ => ?_, fun h => ⟨![a, b], fun i => by fin_cases i <;> rfl, h⟩⟩
  have h0 : a = y 0 := Sum.inl_injective (hy 0)
  have h1 : b = y 1 := Sum.inl_injective (hy 1)
  rw [h0, h1]
  exact hle

end ExtLe

/-! ### Eliminating the order symbol -/

section Elim

variable (L : Language.{0, 0}) (C : SOBlock)

/-- The marker `old`, as a symbol of the vocabulary the eliminated sentence
lives in. -/
abbrev extOldSym : ((newLang L).sum C.withOrder.lang).Relations 1 :=
  Sum.inl (Sum.inr Language.oldSym)

/-- The language morphism eliminating the order symbol of the extended ordered
vocabulary in favour of the order variable of the extended block. -/
def extOrderElim :
    (newLang (L.sum Language.order)).sum C.lang →ᴸ (newLang L).sum C.withOrder.lang where
  onFunction {_n} f :=
    match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => Sum.inl (Sum.inl g)
    | Sum.inl (Sum.inl (Sum.inr g)) => nomatch g
    | Sum.inl (Sum.inr g) => nomatch g
    | Sum.inr g => nomatch g
  onRelation {n} r :=
    match n, r with
    | _, Sum.inl (Sum.inl (Sum.inl s)) => Sum.inl (Sum.inl s)
    | _, Sum.inl (Sum.inl (Sum.inr .le)) => ordVarSym (newLang L) C
    | _, Sum.inl (Sum.inr s) => Sum.inl (Sum.inr s)
    | _, Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

variable {L C} [L.IsRelational] {A : Type} [L.Structure A] {n : ℕ}

/-- When the order variable is assigned the order of the instance, read in the
extended universe, the extended structure over the bare vocabulary is an
expansion along `DescriptiveComplexity.extOrderElim` of the extended structure
over the ordered one. -/
theorem extOrderElim_isExpansionOn [lo : LinearOrder A]
    (ρ : C.withOrder.Assignment (A ⊕ Fin n)) (ρ' : C.Assignment (A ⊕ Fin n))
    (hrest : C.restPart ρ = ρ')
    (hord : ∀ w : Fin 2 → A ⊕ Fin n, ρ (Sum.inl ()) w ↔ extLeRel A n w) :
    letI := C.structure ρ'
    letI := C.withOrder.structure ρ
    @LHom.IsExpansionOn _ _ (extOrderElim L C) (A ⊕ Fin n) _ _ := by
  subst hrest
  letI := C.structure (C.restPart ρ)
  letI := C.withOrder.structure ρ
  exact
    { map_onFunction := fun {n} f x => by
        match f with
        | Sum.inl (Sum.inl (Sum.inl g)) => rfl
        | Sum.inl (Sum.inl (Sum.inr g)) => exact nomatch g
        | Sum.inl (Sum.inr g) => exact nomatch g
        | Sum.inr g => exact nomatch g
      map_onRelation := fun {n} r x => by
        match n, r with
        | _, Sum.inl (Sum.inl (Sum.inl s)) => rfl
        | _, Sum.inl (Sum.inl (Sum.inr .le)) => exact propext (hord x)
        | _, Sum.inl (Sum.inr s) => rfl
        | _, Sum.inr s => rfl }

end Elim

/-! ### The relativized linear-order guard -/

section Guard

variable (L : Language.{0, 0}) (C : SOBlock)

/-- `x ≤ y` for the order variable. -/
private def leEF {α : Type} (x y : α) : ((newLang L).sum C.withOrder.lang).Formula α :=
  Relations.formula₂ (ordVarSym (newLang L) C) (Term.var x) (Term.var y)

/-- `old x`. -/
private def oldEF {α : Type} (x : α) : ((newLang L).sum C.withOrder.lang).Formula α :=
  Relations.formula₁ (extOldSym L C) (Term.var x)

/-- The order variable relates original elements only. -/
private noncomputable def oldOnlyS : ((newLang L).sum C.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 2)
    (leEF L C (Sum.inr 0) (Sum.inr 1) ⟹ (oldEF L C (Sum.inr 0) ⊓ oldEF L C (Sum.inr 1)))

/-- The order variable is reflexive on the original elements. -/
private noncomputable def reflES : ((newLang L).sum C.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 1) (oldEF L C (Sum.inr 0) ⟹ leEF L C (Sum.inr 0) (Sum.inr 0))

/-- The order variable is transitive. -/
private noncomputable def transES : ((newLang L).sum C.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 3)
    (leEF L C (Sum.inr 0) (Sum.inr 1) ⊓ leEF L C (Sum.inr 1) (Sum.inr 2) ⟹
      leEF L C (Sum.inr 0) (Sum.inr 2))

/-- The order variable is antisymmetric. -/
private noncomputable def antisymmES : ((newLang L).sum C.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 2)
    (leEF L C (Sum.inr 0) (Sum.inr 1) ⊓ leEF L C (Sum.inr 1) (Sum.inr 0) ⟹
      Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

/-- The order variable is total on the original elements. -/
private noncomputable def totalES : ((newLang L).sum C.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 2)
    (oldEF L C (Sum.inr 0) ⊓ oldEF L C (Sum.inr 1) ⟹
      (leEF L C (Sum.inr 0) (Sum.inr 1) ⊔ leEF L C (Sum.inr 1) (Sum.inr 0)))

/-- **The relativized guard**: the order variable relates original elements
only, and is a linear order on them. Relativization is forced by value
invention: the order symbol of an extended structure relates original elements
only, so an unrelativized guard would be unsatisfiable as soon as something is
invented. -/
noncomputable def extLinearGuard : ((newLang L).sum C.withOrder.lang).Sentence :=
  oldOnlyS L C ⊓ (reflES L C ⊓ (transES L C ⊓ (antisymmES L C ⊓ totalES L C)))

variable {L C} [L.IsRelational] (A : Type) [L.Structure A] (n : ℕ)

theorem realize_extLinearGuard (ρ : C.withOrder.Assignment (A ⊕ Fin n)) :
    letI := C.withOrder.structure ρ
    ((A ⊕ Fin n) ⊨ extLinearGuard L C) ↔
      ((∀ x y : A ⊕ Fin n, ρ (Sum.inl ()) ![x, y] → IsOld x ∧ IsOld y) ∧
        ((∀ x : A ⊕ Fin n, IsOld x → ρ (Sum.inl ()) ![x, x]) ∧
          ((∀ x y z : A ⊕ Fin n, ρ (Sum.inl ()) ![x, y] → ρ (Sum.inl ()) ![y, z] →
              ρ (Sum.inl ()) ![x, z]) ∧
            ((∀ x y : A ⊕ Fin n, ρ (Sum.inl ()) ![x, y] → ρ (Sum.inl ()) ![y, x] → x = y) ∧
              (∀ x y : A ⊕ Fin n, IsOld x → IsOld y →
                ρ (Sum.inl ()) ![x, y] ∨ ρ (Sum.inl ()) ![y, x]))))) := by
  letI := C.withOrder.structure ρ
  have hle : ∀ w : Fin 2 → A ⊕ Fin n,
      RelMap (L := (newLang L).sum C.withOrder.lang) (ordVarSym (newLang L) C) w ↔
        ρ (Sum.inl ()) w := fun _ => Iff.rfl
  have hold : ∀ w : Fin 1 → A ⊕ Fin n,
      RelMap (L := (newLang L).sum C.withOrder.lang) (extOldSym L C) w ↔ IsOld (w 0) :=
    fun _ => Iff.rfl
  simp only [extLinearGuard, oldOnlyS, reflES, transES, antisymmES, totalES, leEF, oldEF,
    Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_rel₂, Formula.realize_rel₁, Formula.realize_equal,
    Term.realize_var, Sum.elim_inr, hle, hold, Matrix.cons_val_zero]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · exact ⟨fun h x y hxy => h ![x, y] hxy, fun h i hi => h (i 0) (i 1) hi⟩
  · exact ⟨fun h x hx => h ![x] hx, fun h i hi => h (i 0) hi⟩
  · exact ⟨fun h x y z hxy hyz => h ![x, y, z] ⟨hxy, hyz⟩,
      fun h i hp => h (i 0) (i 1) (i 2) hp.1 hp.2⟩
  · exact ⟨fun h x y hxy hyx => h ![x, y] ⟨hxy, hyx⟩,
      fun h i hp => h (i 0) (i 1) hp.1 hp.2⟩
  · exact ⟨fun h x y hx hy => h ![x, y] ⟨hx, hy⟩, fun h i hp => h (i 0) (i 1) hp.1 hp.2⟩

end Guard

/-! ### Order elimination for `∃SO[new]` -/

section OrderPull

variable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}

private theorem vec_eta₂' {M : Type} (w : Fin 2 → M) : ![w 0, w 1] = w := by
  funext j
  fin_cases j <;> simp

/-- **Order elimination for `∃SO[new]`**: a problem defined by an `∃SO[new]`
sentence over the ordered expansion – correct for *some* linear order on each
instance – is `∃SO[new]`-definable. The order becomes one more relation
variable of the block, guarded by
`DescriptiveComplexity.extLinearGuard`. -/
theorem sigmaSONewDefinable_of_orderPull (C : SOBlock)
    (ψ : (soLang (newLang (L.sum Language.order)) [C]).Sentence)
    (h : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ lo : LinearOrder A,
        letI := lo
        ∃ n : ℕ, SORealize (newLang (L.sum Language.order)) (A ⊕ Fin n) [C] ψ true) :
    SigmaSONewDefinable P := by
  refine ⟨C.withOrder, extLinearGuard L C ⊓ (extOrderElim L C).onSentence ψ, ?_⟩
  intro A _ _ _
  rw [h A]
  constructor
  · rintro ⟨lo, n, ρ', hρ'⟩
    letI := lo
    letI := C.structure ρ'
    refine ⟨n, C.joinOrder (extLeRel A n) ρ', ?_⟩
    letI := C.withOrder.structure (C.joinOrder (extLeRel A n) ρ')
    have hord : ∀ w : Fin 2 → A ⊕ Fin n,
        C.joinOrder (extLeRel A n) ρ' (Sum.inl ()) w ↔ extLeRel A n w := fun _ => Iff.rfl
    refine (Sentence.realize_inf (M := A ⊕ Fin n)).mpr ⟨?_, ?_⟩
    · refine (realize_extLinearGuard A n (C.joinOrder (extLeRel A n) ρ')).mpr
        ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y z hxy hyz => ?_, fun x y hxy hyx => ?_,
          fun x y hx hy => ?_⟩
      · have h2 := extLeRel_isOld ((hord _).mp hxy)
        simpa using h2
      · obtain ⟨a, ha⟩ := isOld_iff.mp hx
        refine (hord _).mpr ⟨![a, a], fun i => ?_, le_refl a⟩
        fin_cases i <;> simpa using ha
      · obtain ⟨y₁, hy₁, hle₁⟩ := (hord _).mp hxy
        obtain ⟨y₂, hy₂, hle₂⟩ := (hord _).mp hyz
        have hmid : y₁ 1 = y₂ 0 := by
          have e1 := hy₁ 1
          have e2 := hy₂ 0
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2
          exact Sum.inl_injective (e1.symm.trans e2)
        refine (hord _).mpr ⟨![y₁ 0, y₂ 1], fun i => ?_, ?_⟩
        · fin_cases i
          · simpa using hy₁ 0
          · simpa using hy₂ 1
        · simpa using le_trans hle₁ (hmid ▸ hle₂)
      · obtain ⟨y₁, hy₁, hle₁⟩ := (hord _).mp hxy
        obtain ⟨y₂, hy₂, hle₂⟩ := (hord _).mp hyx
        have e1 := hy₁ 0
        have e2 := hy₁ 1
        have e3 := hy₂ 0
        have e4 := hy₂ 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2 e3 e4
        have h01 : y₁ 0 = y₂ 1 := Sum.inl_injective (e1.symm.trans e4)
        have h10 : y₁ 1 = y₂ 0 := Sum.inl_injective (e2.symm.trans e3)
        rw [e1, e2, le_antisymm hle₁ (h01 ▸ h10 ▸ hle₂)]
      · obtain ⟨a, ha⟩ := isOld_iff.mp hx
        obtain ⟨b, hb⟩ := isOld_iff.mp hy
        rcases le_total a b with hab | hba
        · refine Or.inl ((hord _).mpr ⟨![a, b], fun i => ?_, by simpa using hab⟩)
          fin_cases i
          · simpa using ha
          · simpa using hb
        · refine Or.inr ((hord _).mpr ⟨![b, a], fun i => ?_, by simpa using hba⟩)
          fin_cases i
          · simpa using hb
          · simpa using ha
    · haveI := extOrderElim_isExpansionOn (L := L) (C := C)
        (C.joinOrder (extLeRel A n) ρ') ρ' rfl hord
      exact (LHom.realize_onSentence (A ⊕ Fin n) (extOrderElim L C) ψ).mpr hρ'
  · rintro ⟨n, ρ, hρ⟩
    letI := C.withOrder.structure ρ
    obtain ⟨hguard, hsent⟩ := (Sentence.realize_inf (M := A ⊕ Fin n)).mp hρ
    obtain ⟨honly, hrefl, htrans, hanti, htotal⟩ := (realize_extLinearGuard A n ρ).mp hguard
    letI lo : LinearOrder A := linearOrderOfGuard
      (fun v => ρ (Sum.inl ()) ![Sum.inl (v 0), Sum.inl (v 1)])
      (fun a => hrefl (Sum.inl a) (isOld_inl a))
      (fun a b c hab hbc => htrans _ _ _ hab hbc)
      (fun a b hab hba => Sum.inl_injective (hanti _ _ hab hba))
      (fun a b => htotal _ _ (isOld_inl a) (isOld_inl b))
    have hord : ∀ w : Fin 2 → A ⊕ Fin n, ρ (Sum.inl ()) w ↔ extLeRel A n w := by
      intro w
      constructor
      · intro hw
        obtain ⟨h0, h1⟩ := honly (w 0) (w 1) (by rwa [vec_eta₂' w])
        obtain ⟨a, ha⟩ := isOld_iff.mp h0
        obtain ⟨b, hb⟩ := isOld_iff.mp h1
        refine ⟨![a, b], fun i => ?_, ?_⟩
        · fin_cases i
          · simpa using ha
          · simpa using hb
        · change ρ (Sum.inl ()) ![Sum.inl (![a, b] 0), Sum.inl (![a, b] 1)]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [← ha, ← hb, vec_eta₂' w]
          exact hw
      · rintro ⟨y, hy, hle⟩
        have hle' : ρ (Sum.inl ()) ![Sum.inl (y 0), Sum.inl (y 1)] := hle
        rw [← hy 0, ← hy 1, vec_eta₂' w] at hle'
        exact hle'
    refine ⟨lo, n, C.restPart ρ, ?_⟩
    letI := C.structure (C.restPart ρ)
    haveI := extOrderElim_isExpansionOn (L := L) (C := C) ρ (C.restPart ρ) rfl hord
    exact (LHom.realize_onSentence (A ⊕ Fin n) (extOrderElim L C) ψ).mp hsent

end OrderPull

/-! ### Closure under ordered FO reductions -/

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] {P : DecisionProblem L₁}
variable {Q : DecisionProblem L₂}

/-- **`∃SO[new]`-definability is closed under ordered FO reductions**: pull the
definition back through the interpretation over the ordered expansion, then
re-quantify the order inside the block, guarded by the relativized linear-order
guard. -/
theorem SigmaSONewDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q)
    (h : SigmaSONewDefinable Q) : SigmaSONewDefinable P := by
  obtain ⟨B, φ, hφ⟩ := h
  letI := f.tagFinite
  letI := f.tagNonempty
  refine sigmaSONewDefinable_of_orderPull (newBlock f.Tag f.dim B)
    (canonGuard (L₁.sum Language.order) f.Tag f.dim B ⊓
      (newInterp (L₁.sum Language.order) f.Tag f.dim B f.toInterpretation).pullRelSentence φ) ?_
  intro A _ _ _
  have key : ∀ lo : LinearOrder A,
      letI := lo
      (P A ↔ ∃ n : ℕ, SORealize (newLang (L₁.sum Language.order)) (A ⊕ Fin n)
        [newBlock f.Tag f.dim B]
        (canonGuard (L₁.sum Language.order) f.Tag f.dim B ⊓
          (newInterp (L₁.sum Language.order) f.Tag f.dim B
            f.toInterpretation).pullRelSentence φ) true) := by
    intro lo
    letI := lo
    haveI := f.toInterpretation.map_finite A
    haveI := f.toInterpretation.map_nonempty A
    rw [f.correct A, hφ (f.toInterpretation.Map A)]
    exact exists_congr fun n => sorealize_newPull f.toInterpretation B φ A n
  exact ⟨fun hP => ⟨finiteLinearOrder A, (key _).mp hP⟩,
    fun hex => (key hex.choose).mpr hex.choose_spec⟩

end Closure

end DescriptiveComplexity
