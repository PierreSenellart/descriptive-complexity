/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.OrderDef
import DescriptiveComplexity.Invariant.Simulation

/-!
# Pulling an ordered induction on the invariant structure back to the base

The backward simulation of the Abiteboul–Vianu argument
(`DescriptiveComplexity.AbiteboulVianu`): an induction over the *ordered
invariant vocabulary* – as
produced by the PTIME capture applied on the invariant structure – runs on
the base structure `A`, once the canonical order on `k`-tuples is available
as a converged relation variable. The **class compiler**
(`DescriptiveComplexity.backCompile`) translates a formula over
`((invLang L k).sum Language.order).sum B'.lang` into a formula over the base
vocabulary expanded by the order block and by a `k`-fold copy of `B'`
(`DescriptiveComplexity.backBlock`):

* every class variable becomes `k` element variables – a representative
  tuple; equality of classes becomes incomparability in the order variable
  (`≡ᵏ`);
* the invariant vocabulary's relations become their defining formulas – bits
  as atomic formulas, substitution and rearrangement as incomparability at
  manipulated tuples, the order symbol as «strictly below or equivalent»;
* a relation variable on classes becomes its `k`-fold pullback, one flat
  `arity · k`-tuple read through `DescriptiveComplexity.backFlatten`;
* a quantifier over classes becomes `k` quantifiers over elements.

The compiler is exact (`DescriptiveComplexity.realize_backCompile`), the
compiled induction `DescriptiveComplexity.StepDef.backStepDef` tracks the
original stage by stage over the pulled-back assignments
(`DescriptiveComplexity.backAssign`), and the values agree
(`DescriptiveComplexity.StepDef.ifpHolds_backStepDef`). Stratified over the
definable refinement (`DescriptiveComplexity.Invariant.OrderDef`,
`DescriptiveComplexity.FixedPointStratify`), this is what turns an ordered
induction on `Iᵏ A` into an order-free induction on `A`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}} {k : ℕ}

/-! ### The pulled-back block -/

/-- The `k`-fold pullback of a block: each relation variable on classes
becomes one on representative tuples, its arity multiplied by `k`. -/
@[reducible]
def backBlock (B' : SOBlock) (k : ℕ) : SOBlock where
  ι := B'.ι
  arity := fun i => B'.arity i * k

/-- Reading a tuple of `k`-tuples as one flat tuple. -/
def backFlatten {A : Type} {m : ℕ} (t : Fin m → Fin k → A) : Fin (m * k) → A :=
  fun p => t (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

theorem backFlatten_apply {A : Type} {m : ℕ} (t : Fin m → Fin k → A)
    (a : Fin m) (q : Fin k) :
    backFlatten t (finProdFinEquiv (a, q)) = t a q := by
  rw [backFlatten, Equiv.symm_apply_apply]

theorem backFlatten_eta {A : Type} {m : ℕ} (flat : Fin (m * k) → A) :
    backFlatten (fun a q => flat (finProdFinEquiv (a, q))) = flat := by
  funext p
  rw [backFlatten, Equiv.apply_symm_apply]

/-- The pullback along the quotient map of an assignment on classes. -/
def backAssign {S : Set (Σ n, L.Relations n)} {A : Type} [L.Structure A]
    {B' : SOBlock} (X' : B'.Assignment (InvMap S k A)) :
    (backBlock B' k).Assignment A :=
  fun i flat => X' i fun a => InvMap.mk S fun q => flat (finProdFinEquiv (a, q))

theorem backAssign_backFlatten {S : Set (Σ n, L.Relations n)} {A : Type}
    [L.Structure A] {B' : SOBlock} (X' : B'.Assignment (InvMap S k A))
    (i : B'.ι) (t : Fin (B'.arity i) → Fin k → A) :
    backAssign X' i (backFlatten t) ↔ X' i fun a => InvMap.mk S (t a) := by
  rw [backAssign]
  refine iff_of_eq (congrArg (X' i) (funext fun a => congrArg _ (funext fun q => ?_)))
  rw [backFlatten_apply]

/-! ### Symbols and atoms over the doubly expanded vocabulary -/

section Atoms

variable (L k)

variable {B' : SOBlock}

/-- The order variable, inside the second expansion. -/
abbrev backPrecSym (B' : SOBlock) :
    (((L.sum (ordBlock k).lang)).sum (backBlock B' k).lang).Relations (k + k) :=
  Sum.inl (ordVSym L k)

/-- A base relation symbol, inside the second expansion. -/
abbrev backBaseSym (B' : SOBlock) {l : ℕ} (R : L.Relations l) :
    (((L.sum (ordBlock k).lang)).sum (backBlock B' k).lang).Relations l :=
  Sum.inl (ordBaseSym L k R)

/-- The `≺`-atom between two `k`-tuples of variables, inside the second
expansion. -/
noncomputable def bPrecF {γ : Type} (f g : Fin k → γ) :
    (((L.sum (ordBlock k).lang)).sum (backBlock B' k).lang).Formula γ :=
  Relations.formula (backPrecSym L k B') fun p => Term.var (Fin.addCases f g p)

/-- The `≡ᵏ`-atom: incomparability. -/
noncomputable def bEquivF {γ : Type} (f g : Fin k → γ) :
    (((L.sum (ordBlock k).lang)).sum (backBlock B' k).lang).Formula γ :=
  ∼(bPrecF L k f g) ⊓ ∼(bPrecF L k g f)

/-- The `≤`-atom on classes: strictly below or equivalent. -/
noncomputable def bLeF {γ : Type} (f g : Fin k → γ) :
    (((L.sum (ordBlock k).lang)).sum (backBlock B' k).lang).Formula γ :=
  bPrecF L k f g ⊔ bEquivF L k f g

end Atoms

/-! ### The class compiler -/

section Compiler

variable (L k) {B' : SOBlock} {S : Set (Σ n, L.Relations n)}

open Classical in
/-- **The class compiler**: a formula over the ordered invariant vocabulary
expanded by a block, read on representative `k`-tuples over the base
vocabulary expanded by the order block and the pulled-back block. Each free
or bound class variable is a selection of `k` context variables. -/
noncomputable def backCompile (S : Set (Σ n, L.Relations n)) :
    ∀ {γ : Type} {α : Type} {n : ℕ},
      (((invLang L k).sum Language.order).sum B'.lang).BoundedFormula α n →
      (α → Fin k → γ) → (Fin n → Fin k → γ) →
      (((L.sum (ordBlock k).lang)).sum (backBlock B' k).lang).Formula γ
  | _, _, _, .falsum, _, _ => ⊥
  | _, _, _, .equal t₁ t₂, E, H =>
      bEquivF L k (Sum.elim E H t₁.varOf) (Sum.elim E H t₂.varOf)
  | _, _, _, .rel R ts, E, H =>
      match R with
      | Sum.inl (Sum.inl r) =>
          match r with
          | .eqBit i j =>
              Term.equal (Term.var (Sum.elim E H (ts 0).varOf i))
                (Term.var (Sum.elim E H (ts 0).varOf j))
          | .relBit R' g =>
              if _ : R' ∈ S then
                Relations.formula (backBaseSym L k B' R'.2)
                  fun p => Term.var (Sum.elim E H (ts 0).varOf (g p))
              else ⊥
          | .sub j =>
              Formula.iExs (Fin 1)
                (bEquivF L k
                  (fun p => if p = j then Sum.inr 0
                    else Sum.inl (Sum.elim E H (ts 0).varOf p))
                  fun p => Sum.inl (Sum.elim E H (ts 1).varOf p))
          | .rearr σ =>
              bEquivF L k (fun p => Sum.elim E H (ts 0).varOf (σ p))
                (Sum.elim E H (ts 1).varOf)
      | Sum.inl (Sum.inr r) =>
          match r with
          | .le => bLeF L k (Sum.elim E H (ts 0).varOf) (Sum.elim E H (ts 1).varOf)
      | Sum.inr rv =>
          Relations.formula (varInSym (L.sum (ordBlock k).lang)
              (backBlock B' k) rv.1)
            fun p => Term.var
              (Sum.elim E H
                (ts (Fin.cast rv.2 (finProdFinEquiv.symm p).1)).varOf
                (finProdFinEquiv.symm p).2)
  | _, _, _, .imp f₁ f₂, E, H =>
      backCompile S f₁ E H ⟹ backCompile S f₂ E H
  | _, _, _, .all ψ, E, H =>
      Formula.iAlls (Fin k)
        (backCompile S ψ (fun a q => Sum.inl (E a q))
          (Fin.snoc (fun j q => Sum.inl (H j q)) fun q => Sum.inr q))

end Compiler

/-! ### Exactness of the class compiler -/

section Realize

variable {B' : SOBlock} {S : Set (Σ n, L.Relations n)} {A : Type}
variable [L.Structure A] [Finite A]
variable {σ : (ordBlock k).Assignment A}
variable {Y : (backBlock B' k).Assignment A}

omit [Finite A] in
private theorem realize_bPrecF {γ : Type} (f g : Fin k → γ) (W : γ → A) :
    (@Formula.Realize _ A (@SOBlock.structure₁ (L.sum (ordBlock k).lang)
      (backBlock B' k) A ((ordBlock k).structure₁ (L := L) σ) Y) _
      (bPrecF L k f g) W) ↔
      toPebble σ (fun i => W (f i)) fun i => W (g i) := by
  letI := (ordBlock k).structure₁ (L := L) σ
  letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang) (backBlock B' k) A _ Y
  rw [bPrecF, Formula.realize_rel]
  rw [toPebble, addCases_comp]
  exact Iff.rfl

omit [Finite A] in
private theorem realize_bEquivF {γ : Type} (f g : Fin k → γ) (W : γ → A) :
    (@Formula.Realize _ A (@SOBlock.structure₁ (L.sum (ordBlock k).lang)
      (backBlock B' k) A ((ordBlock k).structure₁ (L := L) σ) Y) _
      (bEquivF L k f g) W) ↔
      IncompRel (toPebble σ) (fun i => W (f i)) fun i => W (g i) := by
  letI := (ordBlock k).structure₁ (L := L) σ
  letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang) (backBlock B' k) A _ Y
  rw [bEquivF, Formula.realize_inf, Formula.realize_not, Formula.realize_not,
    realize_bPrecF, realize_bPrecF]
  exact Iff.rfl

omit [Finite A] in
private theorem realize_bLeF {γ : Type} (f g : Fin k → γ) (W : γ → A) :
    (@Formula.Realize _ A (@SOBlock.structure₁ (L.sum (ordBlock k).lang)
      (backBlock B' k) A ((ordBlock k).structure₁ (L := L) σ) Y) _
      (bLeF L k f g) W) ↔
      (toPebble σ (fun i => W (f i)) (fun i => W (g i)) ∨
        IncompRel (toPebble σ) (fun i => W (f i)) fun i => W (g i)) := by
  letI := (ordBlock k).structure₁ (L := L) σ
  letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang) (backBlock B' k) A _ Y
  rw [bLeF, Formula.realize_sup, realize_bPrecF, realize_bEquivF]

/-- **Exactness of the class compiler**: over an order variable whose
incomparability is `≡ᵏ` and an assignment corresponding to one on classes,
the compiled formula holds at representative tuples exactly when the
original formula holds at their classes on the ordered invariant
structure. -/
theorem realize_backCompile (lo : LinearOrder (InvMap S k A))
    {X' : B'.Assignment (InvMap S k A)}
    (h1 : IncompRel (toPebble σ) = EquivK (atomicAgreeOn S A k))
    (h2 : ∀ u v : Fin k → A,
      (toPebble σ u v ∨ EquivK (atomicAgreeOn S A k) u v) ↔
        (letI := lo; InvMap.mk S u ≤ InvMap.mk S v))
    (hY : ∀ (i : B'.ι) (t : Fin (B'.arity i) → Fin k → A),
      Y i (backFlatten t) ↔ X' i fun a => InvMap.mk S (t a)) :
    ∀ {α : Type} {n : ℕ}
      (φ : (((invLang L k).sum Language.order).sum B'.lang).BoundedFormula α n)
      {γ : Type} (E : α → Fin k → γ) (H : Fin n → Fin k → γ) (W : γ → A),
      ((@Formula.Realize _ A (@SOBlock.structure₁ (L.sum (ordBlock k).lang)
          (backBlock B' k) A ((ordBlock k).structure₁ (L := L) σ) Y) _
          (backCompile L k S φ E H) W) ↔
        @BoundedFormula.Realize _ (InvMap S k A)
          (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
            (InvMap S k A)
            (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
          φ (fun a => InvMap.mk S fun q => W (E a q))
          fun j => InvMap.mk S fun q => W (H j q)) := by
  intro α n φ
  induction φ with
  | @falsum n =>
    intro γ E H W
    have he : backCompile L k S (B' := B')
        (.falsum : (((invLang L k).sum Language.order).sum
          B'.lang).BoundedFormula α n) E H = ⊥ := by
      simp only [backCompile]
    rw [he]
    exact iff_of_false (fun hf => hf) fun hf => hf
  | @equal n t₁ t₂ =>
    intro γ E H W
    obtain ⟨x₁, rfl⟩ := exists_eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := exists_eq_var_of_isRelational t₂
    have key : ∀ x : α ⊕ Fin n,
        Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
          (fun j => InvMap.mk S fun q => W (H j q)) x =
          InvMap.mk S fun q => W (Sum.elim E H x q) := by
      rintro (a | j) <;> rfl
    have he : backCompile L k S (B' := B')
        (BoundedFormula.equal (Term.var x₁) (Term.var x₂)) E H =
        bEquivF L k (Sum.elim E H x₁) (Sum.elim E H x₂) := by
      simp only [backCompile, Language.Term.varOf]
    rw [he]
    have hL := realize_bEquivF (L := L) (σ := σ) (Y := Y) (Sum.elim E H x₁)
      (Sum.elim E H x₂) W
    rw [h1] at hL
    refine hL.trans ?_
    rw [← InvMap.mk_eq_mk (S := S)]
    exact iff_of_eq (congrArg₂ Eq (key x₁).symm (key x₂).symm)
  | @rel n l R ts =>
    intro γ E H W
    have hts : ∀ p, ∃ x, ts p = Term.var x :=
      fun p => exists_eq_var_of_isRelational (ts p)
    choose x hx using hts
    have hsub : ts = fun p => Term.var (x p) := funext hx
    subst hsub
    have key : ∀ y : α ⊕ Fin n,
        Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
          (fun j => InvMap.mk S fun q => W (H j q)) y =
          InvMap.mk S fun q => W (Sum.elim E H y q) := by
      rintro (a | j) <;> rfl
    rcases R with (r | r) | rv
    · -- an invariant-vocabulary relation
      cases r with
      | eqBit i j =>
        have hR : (@BoundedFormula.Realize _ (InvMap S k A)
            (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
              (InvMap S k A)
              (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
            (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.eqBit i j)))
              fun p => Term.var (x p))
            (fun a => InvMap.mk S fun q => W (E a q))
            fun j' => InvMap.mk S fun q => W (H j' q)) ↔
            W (Sum.elim E H (x 0) i) = W (Sum.elim E H (x 0) j) :=
          InvMap.relMap_eqBit i j
            (fun p => Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
              (fun j' => InvMap.mk S fun q => W (H j' q)) (x p))
            (fun q => W (Sum.elim E H (x 0) q)) (key (x 0))
        have he : backCompile L k S (B' := B')
            (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.eqBit i j)))
              fun p => Term.var (x p)) E H =
            Term.equal (Term.var (Sum.elim E H (x 0) i))
              (Term.var (Sum.elim E H (x 0) j)) := by
          simp only [backCompile, Language.Term.varOf]
        rw [he]
        refine Iff.trans ?_ hR.symm
        letI := (ordBlock k).structure₁ (L := L) σ
        letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang)
          (backBlock B' k) A _ Y
        exact Formula.realize_equal (M := A)
      | relBit R' g =>
        classical
        have hR : (@BoundedFormula.Realize _ (InvMap S k A)
            (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
              (InvMap S k A)
              (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
            (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.relBit R' g)))
              fun p => Term.var (x p))
            (fun a => InvMap.mk S fun q => W (E a q))
            fun j' => InvMap.mk S fun q => W (H j' q)) ↔
            (R' ∈ S ∧ RelMap R'.2 fun p => W (Sum.elim E H (x 0) (g p))) :=
          InvMap.relMap_relBit R' g
            (fun p => Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
              (fun j' => InvMap.mk S fun q => W (H j' q)) (x p))
            (fun q => W (Sum.elim E H (x 0) q)) (key (x 0))
        refine Iff.trans ?_ hR.symm
        by_cases hmem : R' ∈ S
        · have he : backCompile L k S (B' := B')
              (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.relBit R' g)))
                fun p => Term.var (x p)) E H =
              Relations.formula (backBaseSym L k B' R'.2)
                fun p => Term.var (Sum.elim E H (x 0) (g p)) := by
            simp only [backCompile, Language.Term.varOf, dif_pos hmem]
          rw [he]
          letI := (ordBlock k).structure₁ (L := L) σ
          letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang)
            (backBlock B' k) A _ Y
          rw [Formula.realize_rel]
          exact (and_iff_right hmem).symm
        · have he : backCompile L k S (B' := B')
              (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.relBit R' g)))
                fun p => Term.var (x p)) E H = ⊥ := by
            simp only [backCompile, Language.Term.varOf, dif_neg hmem]
          rw [he]
          exact iff_of_false (fun hf => hf) fun hf => hmem hf.1
      | sub j =>
        have hR : (@BoundedFormula.Realize _ (InvMap S k A)
            (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
              (InvMap S k A)
              (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
            (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.sub j)))
              fun p => Term.var (x p))
            (fun a => InvMap.mk S fun q => W (E a q))
            fun j' => InvMap.mk S fun q => W (H j' q)) ↔
            ∃ a, EquivK (atomicAgreeOn S A k)
              (Function.update (fun q => W (Sum.elim E H (x 0) q)) j a)
              fun q => W (Sum.elim E H (x 1) q) :=
          InvMap.relMap_sub j
            (fun p => Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
              (fun j' => InvMap.mk S fun q => W (H j' q)) (x p))
            (fun q => W (Sum.elim E H (x 0) q))
            (fun q => W (Sum.elim E H (x 1) q)) (key (x 0)) (key (x 1))
        have he : backCompile L k S (B' := B')
            (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.sub j)))
              fun p => Term.var (x p)) E H =
            Formula.iExs (Fin 1)
              (bEquivF L k
                (fun p => if p = j then Sum.inr 0
                  else Sum.inl (Sum.elim E H (x 0) p))
                fun p => Sum.inl (Sum.elim E H (x 1) p)) := by
          simp only [backCompile, Language.Term.varOf]
        rw [he]
        refine Iff.trans ?_ hR.symm
        letI := (ordBlock k).structure₁ (L := L) σ
        letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang)
          (backBlock B' k) A _ Y
        rw [Formula.realize_iExs]
        have hupd : ∀ c : Fin 1 → A, (fun i => Sum.elim W c
            ((fun p => if p = j then Sum.inr 0
              else Sum.inl (Sum.elim E H (x 0) p)) i)) =
            Function.update (fun q => W (Sum.elim E H (x 0) q)) j (c 0) := by
          intro c
          funext p
          by_cases hp : p = j
          · subst hp
            simp
          · simp [hp]
        constructor
        · rintro ⟨c, hc⟩
          have hb := realize_bEquivF (L := L) (σ := σ) (Y := Y)
            (fun p => if p = j then Sum.inr 0
              else Sum.inl (Sum.elim E H (x 0) p))
            (fun p => Sum.inl (Sum.elim E H (x 1) p)) (Sum.elim W c)
          rw [h1] at hb
          have hc' := hb.mp hc
          rw [hupd c] at hc'
          exact ⟨c 0, hc'⟩
        · rintro ⟨a, ha⟩
          refine ⟨fun _ => a, ?_⟩
          have hb := realize_bEquivF (L := L) (σ := σ) (Y := Y)
            (fun p => if p = j then Sum.inr 0
              else Sum.inl (Sum.elim E H (x 0) p))
            (fun p => Sum.inl (Sum.elim E H (x 1) p))
            (Sum.elim W fun _ : Fin 1 => a)
          rw [h1] at hb
          refine hb.mpr ?_
          rw [hupd fun _ : Fin 1 => a]
          exact ha
      | rearr σ' =>
        have hR : (@BoundedFormula.Realize _ (InvMap S k A)
            (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
              (InvMap S k A)
              (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
            (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.rearr σ')))
              fun p => Term.var (x p))
            (fun a => InvMap.mk S fun q => W (E a q))
            fun j' => InvMap.mk S fun q => W (H j' q)) ↔
            EquivK (atomicAgreeOn S A k)
              (fun p => W (Sum.elim E H (x 0) (σ' p)))
              fun q => W (Sum.elim E H (x 1) q) :=
          InvMap.relMap_rearr σ'
            (fun p => Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
              (fun j' => InvMap.mk S fun q => W (H j' q)) (x p))
            (fun q => W (Sum.elim E H (x 0) q))
            (fun q => W (Sum.elim E H (x 1) q)) (key (x 0)) (key (x 1))
        have he : backCompile L k S (B' := B')
            (BoundedFormula.rel (Sum.inl (Sum.inl (InvRel.rearr σ')))
              fun p => Term.var (x p)) E H =
            bEquivF L k (fun p => Sum.elim E H (x 0) (σ' p))
              (Sum.elim E H (x 1)) := by
          simp only [backCompile, Language.Term.varOf]
        rw [he]
        refine Iff.trans ?_ hR.symm
        have hb := realize_bEquivF (L := L) (σ := σ) (Y := Y)
          (fun p => Sum.elim E H (x 0) (σ' p)) (Sum.elim E H (x 1)) W
        rw [h1] at hb
        exact hb
    · -- the order symbol
      cases r with
      | le =>
        have he : backCompile L k S (B' := B')
            (BoundedFormula.rel
              (Sum.inl (Sum.inr orderRel.le) :
                (((invLang L k).sum Language.order).sum B'.lang).Relations 2)
              fun p => Term.var (x p)) E H =
            bLeF L k (Sum.elim E H (x 0)) (Sum.elim E H (x 1)) := by
          simp only [backCompile, Language.Term.varOf]
        rw [he]
        have hb := realize_bLeF (L := L) (σ := σ) (Y := Y) (Sum.elim E H (x 0))
          (Sum.elim E H (x 1)) W
        rw [h1] at hb
        refine hb.trans ((h2 _ _).trans ?_)
        letI := lo
        constructor
        · intro h
          have h' : (Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
              (fun j' => InvMap.mk S fun q => W (H j' q)) (x 0)) ≤
              Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
                (fun j' => InvMap.mk S fun q => W (H j' q)) (x 1) := by
            rw [key (x 0), key (x 1)]
            exact h
          exact h'
        · intro h
          have h' : (Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
              (fun j' => InvMap.mk S fun q => W (H j' q)) (x 0)) ≤
              Sum.elim (fun a => InvMap.mk S fun q => W (E a q))
                (fun j' => InvMap.mk S fun q => W (H j' q)) (x 1) := h
          rwa [key (x 0), key (x 1)] at h'
    · -- a relation variable on classes
      have he : backCompile L k S (B' := B')
          (BoundedFormula.rel (Sum.inr rv) fun p => Term.var (x p)) E H =
          (Relations.formula (varInSym (L.sum (ordBlock k).lang)
              (backBlock B' k) rv.1)
            fun p => Term.var
              (Sum.elim E H
                (x (Fin.cast rv.2 (finProdFinEquiv.symm p).1))
                (finProdFinEquiv.symm p).2)) := by
        simp only [backCompile, Language.Term.varOf]
      rw [he]
      have hY' := hY rv.1 fun a q =>
        W (Sum.elim E H (x (Fin.cast rv.2 a)) q)
      have hL : (@Formula.Realize _ A (@SOBlock.structure₁
          (L.sum (ordBlock k).lang) (backBlock B' k) A
          ((ordBlock k).structure₁ (L := L) σ) Y) _
          (Relations.formula (varInSym (L.sum (ordBlock k).lang)
              (backBlock B' k) rv.1)
            fun p => Term.var
              (Sum.elim E H
                (x (Fin.cast rv.2 (finProdFinEquiv.symm p).1))
                (finProdFinEquiv.symm p).2)) W) ↔
          Y rv.1 (backFlatten fun a q =>
            W (Sum.elim E H (x (Fin.cast rv.2 a)) q)) := by
        letI := (ordBlock k).structure₁ (L := L) σ
        letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang)
          (backBlock B' k) A _ Y
        rw [Formula.realize_rel]
        exact Iff.rfl
      refine (hL.trans (hY'.trans ?_))
      have hR : (@BoundedFormula.Realize _ (InvMap S k A)
          (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
            (InvMap S k A)
            (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
          (BoundedFormula.rel (Sum.inr rv) fun p => Term.var (x p))
          (fun a => InvMap.mk S fun q => W (E a q))
          fun j' => InvMap.mk S fun q => W (H j' q)) ↔
          X' rv.1 fun a =>
            Sum.elim (fun a' => InvMap.mk S fun q => W (E a' q))
              (fun j' => InvMap.mk S fun q => W (H j' q))
              (x (Fin.cast rv.2 a)) := Iff.rfl
      refine Iff.trans ?_ hR.symm
      refine iff_of_eq (congrArg (X' rv.1) (funext fun a => ?_))
      exact (key (x (Fin.cast rv.2 a))).symm
  | @imp n f₁ f₂ ih₁ ih₂ =>
    intro γ E H W
    have he : backCompile L k S (B' := B') (f₁ ⟹ f₂) E H =
        (backCompile L k S f₁ E H ⟹ backCompile L k S f₂ E H) := by
      simp only [backCompile]
    rw [he]
    have hL : (@Formula.Realize _ A (@SOBlock.structure₁
        (L.sum (ordBlock k).lang) (backBlock B' k) A
        ((ordBlock k).structure₁ (L := L) σ) Y) _
        (backCompile L k S f₁ E H ⟹ backCompile L k S f₂ E H) W) ↔
        ((@Formula.Realize _ A (@SOBlock.structure₁ (L.sum (ordBlock k).lang)
          (backBlock B' k) A ((ordBlock k).structure₁ (L := L) σ) Y) _
          (backCompile L k S f₁ E H) W) →
        (@Formula.Realize _ A (@SOBlock.structure₁ (L.sum (ordBlock k).lang)
          (backBlock B' k) A ((ordBlock k).structure₁ (L := L) σ) Y) _
          (backCompile L k S f₂ E H) W)) := by
      letI := (ordBlock k).structure₁ (L := L) σ
      letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang)
        (backBlock B' k) A _ Y
      exact Formula.realize_imp
    have hR : (@BoundedFormula.Realize _ (InvMap S k A)
        (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
          (InvMap S k A)
          (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
        (f₁.imp f₂) (fun a => InvMap.mk S fun q => W (E a q))
        fun j => InvMap.mk S fun q => W (H j q)) ↔
        ((@BoundedFormula.Realize _ (InvMap S k A)
          (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
            (InvMap S k A)
            (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
          f₁ (fun a => InvMap.mk S fun q => W (E a q))
          fun j => InvMap.mk S fun q => W (H j q)) →
        (@BoundedFormula.Realize _ (InvMap S k A)
          (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
            (InvMap S k A)
            (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
          f₂ (fun a => InvMap.mk S fun q => W (E a q))
          fun j => InvMap.mk S fun q => W (H j q))) := by
      letI := lo
      letI : ((invLang L k).sum Language.order).Structure (InvMap S k A) :=
        sumOrderStructure (invLang L k) (InvMap S k A)
      letI := @SOBlock.structure₁ ((invLang L k).sum Language.order) B'
        (InvMap S k A) _ X'
      exact BoundedFormula.realize_imp
    rw [hR]
    exact hL.trans (imp_congr (ih₁ E H W) (ih₂ E H W))
  | @all n ψ ih =>
    intro γ E H W
    have he : backCompile L k S (B' := B') ψ.all E H =
        Formula.iAlls (Fin k)
          (backCompile L k S ψ (fun a q => Sum.inl (E a q))
            (Fin.snoc (fun j q => Sum.inl (H j q)) fun q => Sum.inr q)) := by
      simp only [backCompile]
    rw [he]
    have hL : (@Formula.Realize _ A (@SOBlock.structure₁
        (L.sum (ordBlock k).lang) (backBlock B' k) A
        ((ordBlock k).structure₁ (L := L) σ) Y) _
        (Formula.iAlls (Fin k)
          (backCompile L k S ψ (fun a q => Sum.inl (E a q))
            (Fin.snoc (fun j q => Sum.inl (H j q)) fun q => Sum.inr q))) W) ↔
        ∀ c : Fin k → A,
          (@Formula.Realize _ A (@SOBlock.structure₁ (L.sum (ordBlock k).lang)
            (backBlock B' k) A ((ordBlock k).structure₁ (L := L) σ) Y) _
            (backCompile L k S ψ (fun a q => Sum.inl (E a q))
              (Fin.snoc (fun j q => Sum.inl (H j q)) fun q => Sum.inr q))
            (Sum.elim W c)) := by
      letI := (ordBlock k).structure₁ (L := L) σ
      letI := @SOBlock.structure₁ (L.sum (ordBlock k).lang)
        (backBlock B' k) A _ Y
      exact Formula.realize_iAlls
    have hR : (@BoundedFormula.Realize _ (InvMap S k A)
        (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
          (InvMap S k A)
          (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
        ψ.all (fun a => InvMap.mk S fun q => W (E a q))
        fun j => InvMap.mk S fun q => W (H j q)) ↔
        ∀ cl : InvMap S k A,
          (@BoundedFormula.Realize _ (InvMap S k A)
            (@SOBlock.structure₁ ((invLang L k).sum Language.order) B'
              (InvMap S k A)
              (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) X') _ _
            ψ (fun a => InvMap.mk S fun q => W (E a q))
            (Fin.snoc (fun j => InvMap.mk S fun q => W (H j q)) cl)) := by
      letI := lo
      letI : ((invLang L k).sum Language.order).Structure (InvMap S k A) :=
        sumOrderStructure (invLang L k) (InvMap S k A)
      letI := @SOBlock.structure₁ ((invLang L k).sum Language.order) B'
        (InvMap S k A) _ X'
      exact BoundedFormula.realize_all
    rw [hL, hR]
    have hval : ∀ c : Fin k → A,
        ((fun a => InvMap.mk S fun q =>
          Sum.elim W c ((fun a' q' => Sum.inl (E a' q')) a q)) =
          fun a => InvMap.mk S fun q => W (E a q)) ∧
        ((fun j => InvMap.mk S fun q => Sum.elim W c
            ((Fin.snoc (fun j' q' => Sum.inl (H j' q'))
              (fun q' => Sum.inr q') : Fin (n + 1) → Fin k → γ ⊕ Fin k) j q)) =
          Fin.snoc (fun j => InvMap.mk S fun q => W (H j q)) (InvMap.mk S c)) := by
      intro c
      refine ⟨rfl, funext fun j => ?_⟩
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last, Fin.snoc_last]
        rfl
      | cast j' =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        rfl
    constructor
    · intro hall cl
      obtain ⟨c, hc⟩ := InvMap.exists_rep cl
      have h := (ih (fun a q => Sum.inl (E a q))
        (Fin.snoc (fun j q => Sum.inl (H j q)) fun q => Sum.inr q)
        (Sum.elim W c)).mp (hall c)
      rw [(hval c).1, (hval c).2] at h
      rwa [hc] at h
    · intro hall c
      have h := hall (InvMap.mk S c)
      refine (ih (fun a q => Sum.inl (E a q))
        (Fin.snoc (fun j q => Sum.inl (H j q)) fun q => Sum.inr q)
        (Sum.elim W c)).mpr ?_
      rw [(hval c).1, (hval c).2]
      exact h

end Realize

/-! ### The pulled-back induction -/

namespace StepDef

variable (e : StepDef ((invLang L k).sum Language.order))

/-- **The pulled-back induction**: the induction over the ordered invariant
vocabulary, compiled onto representative tuples over the base vocabulary
expanded by the (frozen) order block. -/
noncomputable def backStepDef (S : Set (Σ n, L.Relations n)) :
    StepDef (L.sum (ordBlock k).lang) where
  B := backBlock e.B k
  step := fun i => backCompile L k S (e.step i)
    (fun a q => finProdFinEquiv (a, q)) Fin.elim0
  out := backCompile L k S e.out (fun em _ => Empty.elim em) Fin.elim0

variable {S : Set (Σ n, L.Relations n)} {A : Type} [L.Structure A] [Finite A]
variable {σ : (ordBlock k).Assignment A}

/-- The stages of the pulled-back induction are the pullbacks of the
original stages. -/
theorem inflStage_backStepDef (lo : LinearOrder (InvMap S k A))
    (h1 : IncompRel (toPebble σ) = EquivK (atomicAgreeOn S A k))
    (h2 : ∀ u v : Fin k → A,
      (toPebble σ u v ∨ EquivK (atomicAgreeOn S A k) u v) ↔
        (letI := lo; InvMap.mk S u ≤ InvMap.mk S v)) (n : ℕ) :
    (@StepDef.inflStage (L.sum (ordBlock k).lang) (e.backStepDef S) A
        ((ordBlock k).structure₁ (L := L) σ) n :
      (backBlock e.B k).Assignment A) =
      backAssign (@StepDef.inflStage ((invLang L k).sum Language.order) e
        (InvMap S k A)
        (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i flat
    have hLs : (@StepDef.inflStage (L.sum (ordBlock k).lang) (e.backStepDef S) A
        ((ordBlock k).structure₁ (L := L) σ) (n + 1)) i flat ↔
        ((@StepDef.inflStage (L.sum (ordBlock k).lang) (e.backStepDef S) A
          ((ordBlock k).structure₁ (L := L) σ) n) i flat ∨
        (@StepDef.next (L.sum (ordBlock k).lang) (e.backStepDef S) A
          ((ordBlock k).structure₁ (L := L) σ)
          (@StepDef.inflStage (L.sum (ordBlock k).lang) (e.backStepDef S) A
            ((ordBlock k).structure₁ (L := L) σ) n)) i flat) :=
      iff_of_eq (congrFun (congrFun
        (@StepDef.inflStage_succ (L.sum (ordBlock k).lang) (e.backStepDef S) A
          ((ordBlock k).structure₁ (L := L) σ) n) i) flat)
    have hRs : backAssign (@StepDef.inflStage ((invLang L k).sum Language.order)
        e (InvMap S k A)
        (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) (n + 1))
        i flat ↔
        ((@StepDef.inflStage ((invLang L k).sum Language.order) e (InvMap S k A)
          (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) n) i
            (fun a => InvMap.mk S fun q => flat (finProdFinEquiv (a, q))) ∨
        (@StepDef.next ((invLang L k).sum Language.order) e (InvMap S k A)
          (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A))
          (@StepDef.inflStage ((invLang L k).sum Language.order) e (InvMap S k A)
            (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) n)) i
              fun a => InvMap.mk S fun q => flat (finProdFinEquiv (a, q))) :=
      iff_of_eq (congrArg
        (fun (ρ : e.B.Assignment (InvMap S k A)) =>
          ρ i fun a => InvMap.mk S fun q => flat (finProdFinEquiv (a, q)))
        (@StepDef.inflStage_succ ((invLang L k).sum Language.order) e
          (InvMap S k A)
          (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) n))
    refine propext (hLs.trans (Iff.trans ?_ hRs.symm))
    refine or_congr (iff_of_eq (congrFun (congrFun ih i) flat)) ?_
    rw [ih]
    -- one compiled step, evaluated by the exactness of the class compiler
    have hcomp := realize_backCompile (σ := σ)
      (Y := backAssign (@StepDef.inflStage ((invLang L k).sum Language.order)
        e (InvMap S k A)
        (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) n))
      lo h1 h2
      (backAssign_backFlatten _) (e.step i)
      (fun a q => finProdFinEquiv (a, q)) Fin.elim0 flat
    refine hcomp.trans ?_
    have hxs : (fun (j : Fin 0) => InvMap.mk (A := A) S fun q =>
        flat ((Fin.elim0 : Fin 0 → Fin k → Fin (e.B.arity i * k)) j q)) =
        default := Subsingleton.elim _ _
    rw [hxs]
    exact Iff.rfl

/-- **The value of the pulled-back induction is the original value**: an
ordered induction over the invariant structure runs on the base structure,
over the frozen canonical order. -/
theorem ifpHolds_backStepDef (lo : LinearOrder (InvMap S k A))
    (h1 : IncompRel (toPebble σ) = EquivK (atomicAgreeOn S A k))
    (h2 : ∀ u v : Fin k → A,
      (toPebble σ u v ∨ EquivK (atomicAgreeOn S A k) u v) ↔
        (letI := lo; InvMap.mk S u ≤ InvMap.mk S v)) :
    (@StepDef.IFPHolds (L.sum (ordBlock k).lang) (e.backStepDef S) A
        ((ordBlock k).structure₁ (L := L) σ)) ↔
      @StepDef.IFPHolds ((invLang L k).sum Language.order) e (InvMap S k A)
        (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A)) := by
  have hlim : (@StepDef.inflLimit (L.sum (ordBlock k).lang) (e.backStepDef S) A
      ((ordBlock k).structure₁ (L := L) σ) :
        (backBlock e.B k).Assignment A) =
      backAssign (@StepDef.inflLimit ((invLang L k).sum Language.order) e
        (InvMap S k A)
        (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A))) := by
    funext i flat
    refine propext (exists_congr fun n => ?_)
    exact iff_of_eq (congrFun (congrFun
      (e.inflStage_backStepDef lo h1 h2 n) i) flat)
  have hout := realize_backCompile (σ := σ)
    (Y := backAssign (@StepDef.inflLimit ((invLang L k).sum Language.order) e
      (InvMap S k A)
      (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A))))
    lo h1 h2 (backAssign_backFlatten _) e.out
    (fun em _ => Empty.elim em) Fin.elim0 (default : Empty → A)
  have hL : (@StepDef.IFPHolds (L.sum (ordBlock k).lang) (e.backStepDef S) A
      ((ordBlock k).structure₁ (L := L) σ)) ↔
      (@Formula.Realize _ A (@SOBlock.structure₁ (L.sum (ordBlock k).lang)
        (backBlock e.B k) A ((ordBlock k).structure₁ (L := L) σ)
        (backAssign (@StepDef.inflLimit ((invLang L k).sum Language.order) e
          (InvMap S k A)
          (letI := lo; sumOrderStructure (invLang L k) (InvMap S k A))))) _
        (backCompile L k S e.out (fun em _ => Empty.elim em) Fin.elim0)
        (default : Empty → A)) := by
    rw [StepDef.IFPHolds, hlim]
    exact Iff.rfl
  refine hL.trans (hout.trans ?_)
  have hE : (fun (a : Empty) => InvMap.mk (A := A) S fun q =>
      (default : Empty → A) ((fun (em : Empty) (_ : Fin k) =>
        Empty.elim em) a q)) = (default : Empty → InvMap S k A) :=
    Subsingleton.elim _ _
  have hH : (fun (j : Fin 0) => InvMap.mk (A := A) S fun q =>
      (default : Empty → A) ((Fin.elim0 : Fin 0 → Fin k → Empty) j q)) =
      (default : Fin 0 → InvMap S k A) :=
    Subsingleton.elim _ _
  rw [hE, hH]
  exact Iff.rfl

end StepDef

end DescriptiveComplexity
