/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureReductionClosure

/-!
# Transitivity of FO(TC) and FO(DTC) reductions

`P ≤ᵗᶜ Q` and `Q ≤ᵗᶜ R` give `P ≤ᵗᶜ R` (`DescriptiveComplexity.TCReduction.trans`),
and likewise for `≤ᵈᵗᶜ` (`DescriptiveComplexity.DTCReduction.trans`): the
reductions with a logic inside are reduction *orders*.

## The composite

The outer reduction's interpretation reads the reachability relations of its
own walks, which run on the structure the inner reduction produces. Pulled
back through the inner interpretation
(`DescriptiveComplexity.ParamTCSpec.comapRel`) they are walks over the base
structure *expanded* by the inner walks' relations; flattened
(`DescriptiveComplexity.ParamTCSpec.flat`) they are walks over the base
structure alone, and they join the inner family
(`DescriptiveComplexity.TCInterpretation.flatFamily`). The inner interpretation
is then **extended** to the outer family's vocabulary
(`DescriptiveComplexity.TCInterpretation.CompositeBlock.extendOuter`): a
reachability atom of
an outer walk is interpreted by “the two endpoints have encodings between
which the flat walk reaches”, with the encodings pinned by
`DescriptiveComplexity.ParamTCSpec.encF`. Composing the outer interpretation
with the extended inner one (`DescriptiveComplexity.RelFOInterpretation.compRel`)
is then the composite reduction, and no formula is ever rewritten: the guarded
pullback substitutes the extended formulas for the atoms.

The extended interpretation produces exactly the outer reduction's input –
the inner structure, ordered lexicographically, expanded by the outer walks'
relations
(`DescriptiveComplexity.TCInterpretation.CompositeBlock.extendOuterLEquiv`) – which
is where the two halves of the normal form meet: the pullback's
correspondence between in-domain nodes and the flat walk's at the encodings.

## The deterministic case

The same construction with the searching flat walk, which is functional; the
composite's family is read through its determinization, and the flat walks
lose nothing by it. The pullback of a determinized walk is functional
(`DescriptiveComplexity.ParamTCSpec.comapRel_functional`), which is what the
searching simulation needs.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The pullback of a functional walk is functional -/

section ComapFunctional

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dim : ℕ}
  {s : ParamTCSpec L₂} {I : RelFOInterpretation L₁ L₂ Tag dim} {A : Type} [L₁.Structure A]
  {τp : Fin s.par → Tag}

/-- Encoding after decoding is the identity. -/
theorem ParamTCSpec.encode_decode (a : (s.comapRel I τp).Node A) (ha : ParamTCSpec.InDom a) :
    ParamTCSpec.encode τp (ParamTCSpec.decode a ha) = a := by
  refine Prod.ext (Prod.ext rfl rfl) (funext fun m => ?_)
  change a.2 (ParamTCSpec.coordIx dim (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) =
    a.2 m
  refine congrArg a.2 ?_
  simp only [ParamTCSpec.coordIx, Prod.mk.eta]
  exact Equiv.apply_symm_apply _ _

/-- **The pullback of a functional walk is functional.** -/
theorem ParamTCSpec.comapRel_functional
    (h : ∀ (z : Fin s.par → I.MapRel A) (a b c : s.Node (I.MapRel A)),
      s.StepAt z a b → s.StepAt z a c → b = c)
    (z : Fin (s.par * dim) → A) (a b c : (s.comapRel I τp).Node A)
    (hb : (s.comapRel I τp).StepAt z a b) (hc : (s.comapRel I τp).StepAt z a c) : b = c := by
  obtain ⟨ha, hb', hz, hsb⟩ := (ParamTCSpec.stepAt_comapRel_iff a b).mp hb
  obtain ⟨ha₂, hc', hz₂, hsc⟩ := (ParamTCSpec.stepAt_comapRel_iff a c).mp hc
  have := h _ _ _ _ hsb hsc
  rw [← ParamTCSpec.encode_decode b hb', ← ParamTCSpec.encode_decode c hc', this]

end ComapFunctional

/-! ### The outer walks, pulled back and flattened -/

section Flat

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {Tag₁ : Type} [Finite Tag₁] [LinearOrder Tag₁] {d₁ : ℕ}
variable (I : TCInterpretation (L₁.sum Language.order) L₂ Tag₁ d₁)
variable (Dq : ∀ q : I.fam.block.ι, Decider L₁ (Fin (I.fam.block.arity q)))
variable (hD : ∀ (A : Type) [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
  (q : I.fam.block.ι) (w : Fin (I.fam.block.arity q) → A),
  (Dq q).Decides w (I.fam.reachAssign A q w))
variable (s : ParamTCSpec (L₂.sum Language.order)) (τp : Fin s.par → Tag₁)

attribute [local instance] TCInterpretation.expStructure

/-- An outer walk, pulled back through the inner interpretation: a walk over
the base structure expanded by the inner walks' relations. -/
noncomputable abbrev TCInterpretation.pulled :
    ParamTCSpec ((L₁.sum Language.order).sum I.fam.block.lang) :=
  s.comapRel I.ordInterp τp

include hD in
theorem TCInterpretation.exists_pulledStepDecider (m n : (I.pulled s τp).Mode) :
    ∃ D : Decider L₁ ((Fin (I.pulled s τp).k ⊕ Fin (I.pulled s τp).k) ⊕ Fin (I.pulled s τp).par),
      (∀ (A : Type) [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
        (v : (Fin (I.pulled s τp).k ⊕ Fin (I.pulled s τp).k) ⊕ Fin (I.pulled s τp).par → A),
        D.Decides v (@Formula.Realize _ A (I.expStructure A) _ ((I.pulled s τp).step m n) v)) ∧
      (∀ (A : Type) [L₁.Structure A] [LinearOrder A],
        (∀ q, (Dq q).Functional A) → D.Functional A) :=
  Decider.exists_of_formula₀ (fun A _ _ => I.fam.reachAssign A) Dq hD ((I.pulled s τp).step m n)

/-- The deciders of the pulled walk's steps. -/
noncomputable def TCInterpretation.pulledStepDecider (m n : (I.pulled s τp).Mode) :
    Decider L₁ ((Fin (I.pulled s τp).k ⊕ Fin (I.pulled s τp).k) ⊕ Fin (I.pulled s τp).par) :=
  Classical.choose (I.exists_pulledStepDecider Dq hD s τp m n)

theorem TCInterpretation.pulledStepDecider_decides (A : Type) [L₁.Structure A] [LinearOrder A]
    [Finite A] [Nonempty A] (m n : (I.pulled s τp).Mode)
    (v : (Fin (I.pulled s τp).k ⊕ Fin (I.pulled s τp).k) ⊕ Fin (I.pulled s τp).par → A) :
    (I.pulledStepDecider Dq hD s τp m n).Decides v
      (@Formula.Realize _ A (I.expStructure A) _ ((I.pulled s τp).step m n) v) :=
  (Classical.choose_spec (I.exists_pulledStepDecider Dq hD s τp m n)).1 A v

theorem TCInterpretation.pulledStepDecider_functional (A : Type) [L₁.Structure A]
    [LinearOrder A] (h : ∀ q, (Dq q).Functional A) (m n : (I.pulled s τp).Mode) :
    (I.pulledStepDecider Dq hD s τp m n).Functional A :=
  (Classical.choose_spec (I.exists_pulledStepDecider Dq hD s τp m n)).2 A h

variable (det : Bool)

/-- **An outer walk, pulled back and flattened**: a walk over the base
structure alone. -/
noncomputable abbrev TCInterpretation.flatWalk : ParamTCSpec (L₁.sum Language.order) :=
  ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).toParam

variable {A : Type} [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

theorem TCInterpretation.pulledStepDecider_decidesSteps (z : Fin (I.pulled s τp).par → A) :
    (I.pulled s τp).DecidesSteps (I.pulledStepDecider Dq hD s τp) z :=
  fun p _ _ => I.pulledStepDecider_decides Dq hD s τp A p.1 p.2 _

/-- The coordinates of a node's tuple, as a tuple of the flat walk, at a
bottom element `a₀`. -/
noncomputable def TCInterpretation.flatCoords (a₀ : A) (a : (I.pulled s τp).Node A) :
    Fin (I.flatWalk Dq hD s τp det).k → A :=
  ((I.pulled s τp).flatEnc (I.pulledStepDecider Dq hD s τp) det a₀ a).2 ∘
    ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).coordEquiv.symm

/-- **Reachability in the flat walk is reachability in the outer walk**, at
the encodings of in-domain nodes – for the guessing flat walk, or for the
searching one when the outer walk is functional. -/
theorem TCInterpretation.flatWalk_reachAt_iff {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a)
    (hdet : det = true → ∀ (z : Fin s.par → I.ordInterp.MapRel A)
      (a b c : s.Node (I.ordInterp.MapRel A)), s.StepAt z a b → s.StepAt z a c → b = c)
    (z : Fin (I.pulled s τp).par → A) (hz : ParamTCSpec.ParInDom I.ordInterp τp z)
    (a b : (I.pulled s τp).Node A) (ha : ParamTCSpec.InDom a) (hb : ParamTCSpec.InDom b)
    (w₁ w₂ : Fin (I.flatWalk Dq hD s τp det).k → A)
    (hw₁ : w₁ = I.flatCoords Dq hD s τp det a₀ a)
    (hw₂ : w₂ = I.flatCoords Dq hD s τp det a₀ b) :
    (I.flatWalk Dq hD s τp det).ReachAt z (Sum.inl a.1, w₁) (Sum.inl b.1, w₂) ↔
      s.ReachAt (ParamTCSpec.decodePar hz) (ParamTCSpec.decode a ha)
        (ParamTCSpec.decode b hb) := by
  subst hw₁ hw₂
  rw [CoordWalk.reachAt_toParam]
  have hcomp : ∀ f : ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).Coord → A,
      (f ∘ ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).coordEquiv.symm) ∘
        ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).coordEquiv = f := by
    intro f
    funext c
    simp
  change ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).ReachAt z
    (Sum.inl a.1, ((I.pulled s τp).flatEnc (I.pulledStepDecider Dq hD s τp) det a₀ a).2 ∘
      ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).coordEquiv.symm ∘
      ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).coordEquiv)
    (Sum.inl b.1, ((I.pulled s τp).flatEnc (I.pulledStepDecider Dq hD s τp) det a₀ b).2 ∘
      ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).coordEquiv.symm ∘
      ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).coordEquiv) ↔ _
  rw [← Function.comp_assoc, hcomp, ← Function.comp_assoc, hcomp]
  change ((I.pulled s τp).flat (I.pulledStepDecider Dq hD s τp) det).ReachAt z
    ((I.pulled s τp).flatEnc (I.pulledStepDecider Dq hD s τp) det a₀ a)
    ((I.pulled s τp).flatEnc (I.pulledStepDecider Dq hD s τp) det a₀ b) ↔ _
  rw [← ParamTCSpec.reachAt_comapRel_iff ha hb hz]
  cases det
  · exact (I.pulled s τp).reachAt_flat_iff _ (I.pulledStepDecider_decidesSteps Dq hD s τp z)
      hbot a b
  · exact (I.pulled s τp).reachAt_flat_iff_of_functional _
      (I.pulledStepDecider_decidesSteps Dq hD s τp z) hbot
      (ParamTCSpec.comapRel_functional (hdet rfl) z) a b

omit [Finite A] in
/-- **The searching flat walk is functional** when the inner deciders are. -/
theorem TCInterpretation.flatWalk_functional (h : ∀ q, (Dq q).Functional A) :
    (I.flatWalk Dq hD s τp true).Functional A :=
  CoordWalk.functional_toParam _
    ((I.pulled s τp).functional_flat _ fun p =>
      I.pulledStepDecider_functional Dq hD s τp A h p.1 p.2)

end Flat

/-! ### The flat family -/

section FlatFamily

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {Tag₁ : Type} [Finite Tag₁] [LinearOrder Tag₁] {d₁ : ℕ}
variable (I : TCInterpretation (L₁.sum Language.order) L₂ Tag₁ d₁)
variable (Dq : ∀ q : I.fam.block.ι, Decider L₁ (Fin (I.fam.block.arity q)))
variable (hD : ∀ (A : Type) [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
  (q : I.fam.block.ι) (w : Fin (I.fam.block.arity q) → A),
  (Dq q).Decides w (I.fam.reachAssign A q w))
variable (F : TCFamily (L₂.sum Language.order)) (det : Bool)

/-- **The outer family, pulled back and flattened**: one walk per outer walk
and tag assignment of its parameters. -/
noncomputable def TCInterpretation.flatFamily : TCFamily (L₁.sum Language.order) where
  Ix := Σ i : F.Ix, (Fin (F.spec i).par → Tag₁)
  spec p := I.flatWalk Dq hD (F.spec p.1) p.2 det

end FlatFamily

/-! ### Extending the inner interpretation to the outer family's vocabulary -/

section Extend

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {Tag₁ : Type} [Finite Tag₁] [LinearOrder Tag₁] {d₁ : ℕ}
variable (I : TCInterpretation (L₁.sum Language.order) L₂ Tag₁ d₁)
variable (Dq : ∀ q : I.fam.block.ι, Decider L₁ (Fin (I.fam.block.arity q)))
variable (hD : ∀ (A : Type) [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
  (q : I.fam.block.ι) (w : Fin (I.fam.block.arity q) → A),
  (Dq q).Decides w (I.fam.reachAssign A q w))
variable (F : TCFamily (L₂.sum Language.order)) (det : Bool)

/-- The composite family, abstractly: a block with an assignment, into which
the inner family's relation variables and the flat walks' embed, with their
assignments. Abstract so that the composite family may be read as it is
(`≤ᵗᶜ`) or through its determinization (`≤ᵈᵗᶜ`). -/
structure TCInterpretation.CompositeBlock where
  /-- The block. -/
  B : SOBlock
  /-- Its assignment on each structure. -/
  ρ : (A : Type) → [L₁.Structure A] → [LinearOrder A] → B.Assignment A
  /-- The inner family's relation variables. -/
  ι₁ : I.fam.block.ι → B.ι
  /-- Their arities. -/
  arity₁ : ∀ q, B.arity (ι₁ q) = I.fam.block.arity q
  /-- Their assignments. -/
  ρ₁ : ∀ (A : Type) [L₁.Structure A] [LinearOrder A] (q : I.fam.block.ι)
    (w : Fin (I.fam.block.arity q) → A),
    ρ A (ι₁ q) (w ∘ Fin.cast (arity₁ q)) ↔ I.fam.reachAssign A q w
  /-- The flat walks' relation variables, per pair of modes. -/
  ι₂ : ∀ p : (I.flatFamily Dq hD F det).Ix,
    ((I.flatFamily Dq hD F det).spec p).Mode → ((I.flatFamily Dq hD F det).spec p).Mode → B.ι
  /-- Their arities. -/
  arity₂ : ∀ p m n, B.arity (ι₂ p m n) = (I.flatFamily Dq hD F det).block.arity ⟨p, (m, n)⟩
  /-- Their assignments: the flat walks' reachability relations. -/
  ρ₂ : ∀ (A : Type) [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A] p m n
    (w : Fin ((I.flatFamily Dq hD F det).block.arity ⟨p, (m, n)⟩) → A),
    ρ A (ι₂ p m n) (w ∘ Fin.cast (arity₂ p m n)) ↔
      ((I.flatFamily Dq hD F det).spec p).ReachAt (w ∘ ((I.flatFamily Dq hD F det).spec p).parIx)
        (m, w ∘ ((I.flatFamily Dq hD F det).spec p).leftIx)
        (n, w ∘ ((I.flatFamily Dq hD F det).spec p).rightIx)

variable {I Dq hD F det} (C : I.CompositeBlock Dq hD F det)

/-- The vocabulary map from the inner family's expansion to the composite's. -/
noncomputable def TCInterpretation.CompositeBlock.lhom :
    (L₁.sum Language.order).sum I.fam.block.lang →ᴸ (L₁.sum Language.order).sum C.B.lang :=
  LHom.sumMap (LHom.id _) ⟨fun {_} f => f.elim, fun {_} q => ⟨C.ι₁ q.1, (C.arity₁ q.1).trans q.2⟩⟩

attribute [local instance] TCInterpretation.expStructure

/-- The composite structure: the base expanded by the composite block. -/
@[instance_reducible]
noncomputable def TCInterpretation.CompositeBlock.structure (A : Type) [L₁.Structure A]
    [LinearOrder A] : ((L₁.sum Language.order).sum C.B.lang).Structure A :=
  C.B.structure₁ (L := L₁.sum Language.order) (C.ρ A)

variable {A : Type} [L₁.Structure A] [LinearOrder A]

/-- The vocabulary map is an expansion. -/
theorem TCInterpretation.CompositeBlock.isExpansionOn :
    @LHom.IsExpansionOn _ _ C.lhom A (I.expStructure A) (C.structure A) := by
  let := C.structure A
  constructor
  · intro n f x
    rcases f with f | f
    · rfl
    · exact f.elim
  · intro n R x
    rcases R with r | ⟨q, hq⟩
    · rfl
    · change C.ρ A (C.ι₁ q) (fun j => x (Fin.cast ((C.arity₁ q).trans hq) j)) =
        I.fam.reachAssign A q (fun j => x (Fin.cast hq j))
      exact propext (C.ρ₁ A q fun j => x (Fin.cast hq j))

theorem TCInterpretation.CompositeBlock.realize_lhom {α : Type} (φ : ((L₁.sum Language.order).sum
    I.fam.block.lang).Formula α) (v : α → A) :
    (@Formula.Realize _ A (C.structure A) _ (C.lhom.onFormula φ) v) ↔ φ.Realize v :=
  letI := C.structure A
  letI := C.isExpansionOn (A := A)
  LHom.realize_onFormula _ _

/-! #### The outer atoms -/

section OuterAtom

variable {n : ℕ} (q : F.block.lang.Relations n) (τ : Fin n → Tag₁)

/-- The tags of an outer symbol's arguments, in its walk's packing. -/
def outerTags : Fin ((F.spec q.1.1).k + (F.spec q.1.1).k + (F.spec q.1.1).par) → Tag₁ :=
  fun p => τ (Fin.cast q.2 p)

/-- The tags of the walk's parameters. -/
def outerTp : Fin (F.spec q.1.1).par → Tag₁ := fun j => outerTags q τ ((F.spec q.1.1).parIx j)

/-- The coordinates of the first endpoint, among the symbol's variables. -/
def outerXsel : Fin ((F.spec q.1.1).k * d₁) → Fin n × Fin d₁ :=
  fun c => (Fin.cast q.2 ((F.spec q.1.1).leftIx (finProdFinEquiv.symm c).1),
    (finProdFinEquiv.symm c).2)

/-- The coordinates of the second endpoint. -/
def outerYsel : Fin ((F.spec q.1.1).k * d₁) → Fin n × Fin d₁ :=
  fun c => (Fin.cast q.2 ((F.spec q.1.1).rightIx (finProdFinEquiv.symm c).1),
    (finProdFinEquiv.symm c).2)

/-- The coordinates of the parameters. -/
def outerZsel : Fin ((F.spec q.1.1).par * d₁) → Fin n × Fin d₁ :=
  fun c => (Fin.cast q.2 ((F.spec q.1.1).parIx (finProdFinEquiv.symm c).1),
    (finProdFinEquiv.symm c).2)

/-- The index of the flat walk interpreting the symbol. -/
abbrev outerIx : (I.flatFamily Dq hD F det).Ix := ⟨q.1.1, outerTp q τ⟩

/-- The two modes of the flat walk between which reachability is asked. -/
abbrev outerMode₁ : ((I.flatFamily Dq hD F det).spec (outerIx q τ)).Mode :=
  Sum.inl (q.1.2.1, fun j => outerTags q τ ((F.spec q.1.1).leftIx j))

@[inherit_doc outerMode₁]
abbrev outerMode₂ : ((I.flatFamily Dq hD F det).spec (outerIx q τ)).Mode :=
  Sum.inl (q.1.2.2, fun j => outerTags q τ ((F.spec q.1.1).rightIx j))

/-- The number of coordinates of the flat walk interpreting the symbol. -/
noncomputable abbrev outerK : ℕ :=
  Nat.card ((I.pulled (F.spec q.1.1) (outerTp q τ)).flat
    (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) det).Coord

/-- **The interpretation of an outer reachability atom**: the two endpoints
have encodings between which the flat walk reaches. -/
noncomputable def TCInterpretation.CompositeBlock.outerAtomF :
    ((L₁.sum Language.order).sum C.B.lang).Formula (Fin n × Fin d₁) :=
  Formula.iExs (Fin (outerK q τ (I := I) (Dq := Dq) (hD := hD) (det := det)) ⊕
      Fin (outerK q τ (I := I) (Dq := Dq) (hD := hD) (det := det)))
    (LHom.sumInl.onFormula ((I.pulled (F.spec q.1.1) (outerTp q τ)).encF
        (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) (det := det)
        (Sum.inl ∘ outerXsel q) (Sum.inr ∘ Sum.inl)) ⊓
      LHom.sumInl.onFormula ((I.pulled (F.spec q.1.1) (outerTp q τ)).encF
        (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) (det := det)
        (Sum.inl ∘ outerYsel q) (Sum.inr ∘ Sum.inr)) ⊓
      Relations.formula (varInSym (L₁.sum Language.order) C.B (C.ι₂ (outerIx q τ)
          (outerMode₁ q τ) (outerMode₂ q τ)))
        fun j => Term.var (ParamTCSpec.pack
          (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
          (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q)
          (Fin.cast (C.arity₂ (outerIx q τ) (outerMode₁ q τ)
            (outerMode₂ q τ)) j)))

variable [Finite A] [Nonempty A] (v : Fin n × Fin d₁ → A)
  (hv : ∀ i, (I.toRel.domFormula (τ i)).Realize fun j => v (i, j))

/-- The point of the inner structure held at a position of the symbol. -/
def outerPt (p : Fin ((F.spec q.1.1).k + (F.spec q.1.1).k + (F.spec q.1.1).par)) :
    I.ordInterp.MapRel A :=
  ⟨(outerTags q τ p, fun c => v (Fin.cast q.2 p, c)), hv _⟩

omit [L₁.IsRelational] [Finite A] [Nonempty A] in
include hv in
theorem outer_inDom_left :
    ParamTCSpec.InDom (I := I.ordInterp) (τp := outerTp q τ) (s := F.spec q.1.1)
      ((q.1.2.1, fun j => outerTags q τ ((F.spec q.1.1).leftIx j)), v ∘ outerXsel q) := by
  intro i
  change (I.toRel.domFormula _).Realize fun j =>
    v (outerXsel q (ParamTCSpec.coordIx d₁ i j))
  simp only [outerXsel, ParamTCSpec.coordIx, Equiv.symm_apply_apply]
  exact hv _

omit [L₁.IsRelational] [Finite A] [Nonempty A] in
include hv in
theorem outer_inDom_right :
    ParamTCSpec.InDom (I := I.ordInterp) (τp := outerTp q τ) (s := F.spec q.1.1)
      ((q.1.2.2, fun j => outerTags q τ ((F.spec q.1.1).rightIx j)), v ∘ outerYsel q) := by
  intro i
  change (I.toRel.domFormula _).Realize fun j =>
    v (outerYsel q (ParamTCSpec.coordIx d₁ i j))
  simp only [outerYsel, ParamTCSpec.coordIx, Equiv.symm_apply_apply]
  exact hv _

omit [L₁.IsRelational] [L₂.IsRelational] [Finite Tag₁] [Finite A] [Nonempty A] in
include hv in
theorem outer_parInDom :
    ParamTCSpec.ParInDom I.ordInterp (s := F.spec q.1.1) (outerTp q τ) (v ∘ outerZsel q) := by
  intro i
  change (I.toRel.domFormula _).Realize fun j =>
    v (outerZsel q (ParamTCSpec.coordIx d₁ i j))
  simp only [outerZsel, ParamTCSpec.coordIx, Equiv.symm_apply_apply]
  exact hv _

omit [L₁.IsRelational] [Finite A] [Nonempty A] in
theorem outer_decode_left :
    ParamTCSpec.decode _ (outer_inDom_left q τ v hv) =
      (q.1.2.1, fun j => outerPt q τ v hv ((F.spec q.1.1).leftIx j)) := by
  refine Prod.ext rfl (funext fun j => Subtype.ext (Prod.ext rfl (funext fun c => ?_)))
  change v (outerXsel q (ParamTCSpec.coordIx d₁ j c)) = _
  simp only [outerXsel, ParamTCSpec.coordIx, Equiv.symm_apply_apply]
  rfl

omit [L₁.IsRelational] [Finite A] [Nonempty A] in
theorem outer_decode_right :
    ParamTCSpec.decode _ (outer_inDom_right q τ v hv) =
      (q.1.2.2, fun j => outerPt q τ v hv ((F.spec q.1.1).rightIx j)) := by
  refine Prod.ext rfl (funext fun j => Subtype.ext (Prod.ext rfl (funext fun c => ?_)))
  change v (outerYsel q (ParamTCSpec.coordIx d₁ j c)) = _
  simp only [outerYsel, ParamTCSpec.coordIx, Equiv.symm_apply_apply]
  rfl

omit [L₁.IsRelational] [L₂.IsRelational] [Finite Tag₁] [Finite A] [Nonempty A] in
theorem outer_decodePar :
    ParamTCSpec.decodePar (outer_parInDom q τ v hv) =
      fun j => outerPt q τ v hv ((F.spec q.1.1).parIx j) := by
  refine funext fun j => Subtype.ext (Prod.ext rfl (funext fun c => ?_))
  change v (outerZsel q (ParamTCSpec.coordIx d₁ j c)) = _
  simp only [outerZsel, ParamTCSpec.coordIx, Equiv.symm_apply_apply]
  rfl

/-- **The outer atom's interpretation says reachability in the outer walk**,
between the points the symbol's arguments encode. -/
theorem TCInterpretation.CompositeBlock.realize_outerAtomF {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a)
    (hdet : det = true → ∀ (z : Fin (F.spec q.1.1).par → I.ordInterp.MapRel A)
      (a b c : (F.spec q.1.1).Node (I.ordInterp.MapRel A)),
      (F.spec q.1.1).StepAt z a b → (F.spec q.1.1).StepAt z a c → b = c) :
    (@Formula.Realize _ A (C.structure A) _ (C.outerAtomF q τ) v) ↔
      (F.spec q.1.1).ReachAt (fun j => outerPt q τ v hv ((F.spec q.1.1).parIx j))
        (q.1.2.1, fun j => outerPt q τ v hv ((F.spec q.1.1).leftIx j))
        (q.1.2.2, fun j => outerPt q τ v hv ((F.spec q.1.1).rightIx j)) := by
  let := C.structure A
  have hsel : ∀ w : Fin (outerK q τ (I := I) (Dq := Dq) (hD := hD) (det := det)) ⊕
      Fin (outerK q τ (I := I) (Dq := Dq) (hD := hD) (det := det)) → A,
      ((I.flatFamily Dq hD F det).spec (outerIx q τ)).ReachAt
        ((Sum.elim v w ∘ ParamTCSpec.pack
          (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
          (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q)) ∘
          ((I.flatFamily Dq hD F det).spec (outerIx q τ)).parIx)
        (outerMode₁ q τ, (Sum.elim v w ∘ ParamTCSpec.pack
          (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
          (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q)) ∘
          ((I.flatFamily Dq hD F det).spec (outerIx q τ)).leftIx)
        (outerMode₂ q τ, (Sum.elim v w ∘ ParamTCSpec.pack
          (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
          (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q)) ∘
          ((I.flatFamily Dq hD F det).spec (outerIx q τ)).rightIx) ↔
      ((I.flatFamily Dq hD F det).spec (outerIx q τ)).ReachAt (v ∘ outerZsel q)
        (outerMode₁ q τ, w ∘ Sum.inl) (outerMode₂ q τ, w ∘ Sum.inr) := by
    intro w
    have e₁ : (Sum.elim v w ∘ ParamTCSpec.pack
          (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
          (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q)) ∘
          ((I.flatFamily Dq hD F det).spec (outerIx q τ)).parIx = v ∘ outerZsel q :=
      funext fun j => congrArg (Sum.elim v w) (ParamTCSpec.pack_par _ _ _ j)
    have e₂ : (Sum.elim v w ∘ ParamTCSpec.pack
          (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
          (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q)) ∘
          ((I.flatFamily Dq hD F det).spec (outerIx q τ)).leftIx = w ∘ Sum.inl :=
      funext fun j => congrArg (Sum.elim v w) (ParamTCSpec.pack_left _ _ _ j)
    have e₃ : (Sum.elim v w ∘ ParamTCSpec.pack
          (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
          (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q)) ∘
          ((I.flatFamily Dq hD F det).spec (outerIx q τ)).rightIx = w ∘ Sum.inr :=
      funext fun j => congrArg (Sum.elim v w) (ParamTCSpec.pack_right _ _ _ j)
    rw [e₁, e₂, e₃]
    exact Iff.rfl
  rw [← outer_decode_left q τ v hv, ← outer_decode_right q τ v hv,
    ← outer_decodePar q τ v hv, TCInterpretation.CompositeBlock.outerAtomF,
    Formula.realize_iExs]
  constructor
  · rintro ⟨w, hw⟩
    rw [Formula.realize_inf, Formula.realize_inf, LHom.realize_onFormula,
      LHom.realize_onFormula, ParamTCSpec.realize_encF _ _ det hbot,
      ParamTCSpec.realize_encF _ _ det hbot, Formula.realize_rel] at hw
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hw
    have h₃' := (C.ρ₂ A (outerIx q τ) (outerMode₁ q τ) (outerMode₂ q τ)
      (Sum.elim v w ∘ ParamTCSpec.pack (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
        (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q))).mp h₃
    have h₃'' := (hsel w).mp h₃'
    refine (I.flatWalk_reachAt_iff Dq hD (F.spec q.1.1) (outerTp q τ) det hbot hdet
      (v ∘ outerZsel q) (outer_parInDom q τ v hv) _ _ (outer_inDom_left q τ v hv)
      (outer_inDom_right q τ v hv) (w ∘ Sum.inl) (w ∘ Sum.inr) ?_ ?_).mp h₃''
    · have h₁' : (w ∘ Sum.inl) ∘ ((I.pulled (F.spec q.1.1) (outerTp q τ)).flat
          (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) det).coordEquiv =
          ((I.pulled (F.spec q.1.1) (outerTp q τ)).flatEnc
            (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) det a₀
            ((q.1.2.1, fun j => outerTags q τ ((F.spec q.1.1).leftIx j)), v ∘ outerXsel q)).2 := h₁
      rw [TCInterpretation.flatCoords, ← h₁']
      funext c
      simp
    · have h₂' : (w ∘ Sum.inr) ∘ ((I.pulled (F.spec q.1.1) (outerTp q τ)).flat
          (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) det).coordEquiv =
          ((I.pulled (F.spec q.1.1) (outerTp q τ)).flatEnc
            (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) det a₀
            ((q.1.2.2, fun j => outerTags q τ ((F.spec q.1.1).rightIx j)), v ∘ outerYsel q)).2 := h₂
      rw [TCInterpretation.flatCoords, ← h₂']
      funext c
      simp
  · intro h
    set w₁ := I.flatCoords Dq hD (F.spec q.1.1) (outerTp q τ) det a₀
      ((q.1.2.1, fun j => outerTags q τ ((F.spec q.1.1).leftIx j)), v ∘ outerXsel q) with hw₁
    set w₂ := I.flatCoords Dq hD (F.spec q.1.1) (outerTp q τ) det a₀
      ((q.1.2.2, fun j => outerTags q τ ((F.spec q.1.1).rightIx j)), v ∘ outerYsel q) with hw₂
    refine ⟨Sum.elim w₁ w₂, ?_⟩
    rw [Formula.realize_inf, Formula.realize_inf, LHom.realize_onFormula,
      LHom.realize_onFormula, ParamTCSpec.realize_encF _ _ det hbot,
      ParamTCSpec.realize_encF _ _ det hbot, Formula.realize_rel]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (w₁ ∘ _) = ((I.pulled (F.spec q.1.1) (outerTp q τ)).flatEnc
          (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) det a₀
          ((q.1.2.1, fun j => outerTags q τ ((F.spec q.1.1).leftIx j)), v ∘ outerXsel q)).2
      rw [hw₁, TCInterpretation.flatCoords]
      funext c
      simp
    · change (w₂ ∘ _) = ((I.pulled (F.spec q.1.1) (outerTp q τ)).flatEnc
          (I.pulledStepDecider Dq hD (F.spec q.1.1) (outerTp q τ)) det a₀
          ((q.1.2.2, fun j => outerTags q τ ((F.spec q.1.1).rightIx j)), v ∘ outerYsel q)).2
      rw [hw₂, TCInterpretation.flatCoords]
      funext c
      simp
    · refine (C.ρ₂ A (outerIx q τ) (outerMode₁ q τ) (outerMode₂ q τ)
        (Sum.elim v (Sum.elim w₁ w₂) ∘ ParamTCSpec.pack
          (s := (I.flatFamily Dq hD F det).spec (outerIx q τ))
          (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) (Sum.inl ∘ outerZsel q))).mpr ?_
      refine (hsel (Sum.elim w₁ w₂)).mpr ?_
      exact (I.flatWalk_reachAt_iff Dq hD (F.spec q.1.1) (outerTp q τ) det hbot hdet
        (v ∘ outerZsel q) (outer_parInDom q τ v hv) _ _ (outer_inDom_left q τ v hv)
        (outer_inDom_right q τ v hv) _ _ rfl rfl).mpr h

end OuterAtom

/-! #### The extended interpretation -/

variable (F) in
/-- **The inner interpretation, extended to the outer family's vocabulary**:
the base symbols and the order as before, an outer reachability atom by
`DescriptiveComplexity.TCInterpretation.CompositeBlock.outerAtomF`. -/
noncomputable def TCInterpretation.CompositeBlock.extendOuter :
    RelFOInterpretation ((L₁.sum Language.order).sum C.B.lang)
      ((L₂.sum Language.order).sum F.block.lang) Tag₁ d₁ where
  relFormula {_} R τ :=
    match R with
    | Sum.inl r => C.lhom.onFormula (I.ordInterp.relFormula r τ)
    | Sum.inr q => C.outerAtomF q τ
  domFormula t := C.lhom.onFormula (I.toRel.domFormula t)

variable [Finite A] [Nonempty A]

/-- **The extended interpretation produces the outer reduction's input**: the
inner structure, ordered lexicographically, expanded by the outer walks'
reachability relations. -/
noncomputable def TCInterpretation.CompositeBlock.extendOuterLEquiv {a₀ : A}
    (hbot : ∀ a : A, a₀ ≤ a)
    (hdet : det = true → ∀ (i : F.Ix) (z : Fin (F.spec i).par → I.ordInterp.MapRel A)
      (a b c : (F.spec i).Node (I.ordInterp.MapRel A)),
      (F.spec i).StepAt z a b → (F.spec i).StepAt z a c → b = c) :
    @Language.Equiv ((L₂.sum Language.order).sum F.block.lang)
      (@RelFOInterpretation.MapRel _ _ _ _ (C.extendOuter F) A (C.structure A)) (I.Map A)
      (@RelFOInterpretation.mapRelStructure _ _ _ _ (C.extendOuter F) A (C.structure A) _)
      (letI := I.mapLinearOrder A
       F.block.structure₁ (L := L₂.sum Language.order) (F.reachAssign (I.Map A))) :=
  letI := C.structure A
  letI := I.mapLinearOrder A
  letI : LinearOrder (I.toRel.MapRel A) := I.mapLinearOrder A
  letI : ((L₂.sum Language.order).sum F.block.lang).Structure (I.Map A) :=
    F.block.structure₁ (L := L₂.sum Language.order) (F.reachAssign (I.Map A))
  let e₀ := I.toRel.ordExtendSrcLEquiv LHom.sumInl (I.expStructure A)
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  { toEquiv := Equiv.subtypeEquivRight fun x => C.realize_lhom (I.toRel.domFormula x.1) x.2
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {_} R xs => by
      have hv : ∀ i, (I.toRel.domFormula ((xs i).1.1)).Realize fun j => (xs i).1.2 j :=
        fun i => (C.realize_lhom (I.toRel.domFormula (xs i).1.1) (xs i).1.2).mp (xs i).2
      cases R with
      | inl r =>
        refine Iff.trans ?_ (C.realize_lhom (I.ordInterp.relFormula r fun i => (xs i).1.1)
          fun p => (xs p.1).1.2 p.2).symm
        exact e₀.map_rel' r fun i => (⟨(xs i).1, hv i⟩ : I.ordInterp.MapRel A)
      | inr q =>
        change F.reachAssign (I.Map A) q.1
            (fun j => (⟨(xs (Fin.cast q.2 j)).1, hv _⟩ : I.Map A)) ↔
          (C.outerAtomF q fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2
        rw [C.realize_outerAtomF q _ _ hv hbot (fun h => hdet h q.1.1)]
        exact (TCFamily.reachAssign_iff _ _).trans
          (ParamTCSpec.reachAt_of_equiv e₀ (F.spec q.1.1)
            (fun j => outerPt q (fun i => (xs i).1.1) (fun p => (xs p.1).1.2 p.2) hv
              ((F.spec q.1.1).parIx j))
            (q.1.2.1, fun j => outerPt q (fun i => (xs i).1.1) (fun p => (xs p.1).1.2 p.2) hv
              ((F.spec q.1.1).leftIx j))
            (q.1.2.2, fun j => outerPt q (fun i => (xs i).1.1) (fun p => (xs p.1).1.2 p.2) hv
              ((F.spec q.1.1).rightIx j))) }

end Extend

/-! ### The composite interpretation -/

/-- The sum of two families. -/
def TCFamily.sum {L : Language.{0, 0}} (G H : TCFamily L) : TCFamily L where
  Ix := G.Ix ⊕ H.Ix
  spec := Sum.elim G.spec H.spec

section Composite

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {Tag₁ Tag₂ : Type} [Finite Tag₁] [LinearOrder Tag₁] {d₁ d₂ : ℕ}
variable {I : TCInterpretation (L₁.sum Language.order) L₂ Tag₁ d₁}
variable {Dq : ∀ q : I.fam.block.ι, Decider L₁ (Fin (I.fam.block.arity q))}
variable {hD : ∀ (A : Type) [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
  (q : I.fam.block.ι) (w : Fin (I.fam.block.arity q) → A),
  (Dq q).Decides w (I.fam.reachAssign A q w)}
variable {det : Bool} (If : TCInterpretation (L₂.sum Language.order) L₃ Tag₂ d₂)
variable (C : I.CompositeBlock Dq hD If.fam det)

attribute [local instance] TCInterpretation.expStructure

/-- **The composite interpretation**: the outer interpretation composed with
the extended inner one. -/
noncomputable def TCInterpretation.CompositeBlock.compInterp :
    RelFOInterpretation ((L₁.sum Language.order).sum C.B.lang) L₃ (Tag₂ × (Fin d₂ → Tag₁))
      (d₂ * d₁) :=
  If.toRel.compRel (C.extendOuter If.fam)

variable {A : Type} [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The composite produces the twice-interpreted structure.** -/
noncomputable def TCInterpretation.CompositeBlock.compLEquiv {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a)
    (hdet : det = true → ∀ (i : If.fam.Ix) (z : Fin (If.fam.spec i).par → I.ordInterp.MapRel A)
      (a b c : (If.fam.spec i).Node (I.ordInterp.MapRel A)),
      (If.fam.spec i).StepAt z a b → (If.fam.spec i).StepAt z a c → b = c) :
    @Language.Equiv L₃ (@RelFOInterpretation.MapRel _ _ _ _ (C.compInterp If) A (C.structure A))
      (letI := I.mapLinearOrder A; If.Map (I.Map A))
      (@RelFOInterpretation.mapRelStructure _ _ _ _ (C.compInterp If) A (C.structure A) _)
      (letI := I.mapLinearOrder A; TCInterpretation.mapStructure If (I.Map A)) := by
  letI := C.structure A
  letI := I.mapLinearOrder A
  letI := If.expStructure (I.Map A)
  exact (If.toRel.mapRelLEquiv (C.extendOuterLEquiv hbot hdet)).comp
    (If.toRel.compLEquivRel (C.extendOuter If.fam))

end Composite

/-! ### Transitivity -/

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂} {R : DecisionProblem L₃}

/-- **Transitivity of FO(TC) reductions.** The composite's family is the inner
family together with the outer family's walks pulled back and flattened;
its interpretation is the outer one composed with the inner one extended to
the outer walks' vocabulary. -/
noncomputable def TCReduction.trans (g : P ≤ᵗᶜ Q) (f : Q ≤ᵗᶜ R) : P ≤ᵗᶜ R :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  let I := g.toInterpretation
  let If := f.toInterpretation
  let H := I.flatFamily I.fam.reachDeciders I.fam.decides_reachDeciders If.fam false
  let C : I.CompositeBlock I.fam.reachDeciders I.fam.decides_reachDeciders If.fam false :=
    { B := (I.fam.sum H).block
      ρ := fun A _ _ => (I.fam.sum H).reachAssign A
      ι₁ := fun q => ⟨Sum.inl q.1, q.2⟩
      arity₁ := fun _ => rfl
      ρ₁ := fun _ _ _ _ _ => Iff.rfl
      ι₂ := fun p m n => ⟨Sum.inr p, (m, n)⟩
      arity₂ := fun _ _ _ => rfl
      ρ₂ := fun _ _ _ _ _ _ _ _ _ => Iff.rfl }
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toInterpretation := ⟨I.fam.sum H, C.compInterp If⟩
    map_nonempty := fun A _ _ _ _ => by
      let := I.mapLinearOrder A
      have : Finite (I.Map A) := I.map_finite A
      have : Nonempty (I.Map A) := g.map_nonempty A
      obtain ⟨a₀, hbot⟩ := exists_bot A
      exact (f.map_nonempty (I.Map A)).map
        (C.compLEquiv If hbot fun h => Bool.noConfusion h).symm
    correct := fun A _ _ _ _ => by
      let := I.mapLinearOrder A
      have : Finite (I.Map A) := I.map_finite A
      have : Nonempty (I.Map A) := g.map_nonempty A
      obtain ⟨a₀, hbot⟩ := exists_bot A
      refine (g.correct A).trans ((f.correct (I.Map A)).trans ?_)
      exact (@DecisionProblem.iso_invariant _ _ R _ _ _ _
        (C.compLEquiv If hbot fun h => Bool.noConfusion h)).symm }

/-- **Transitivity of FO(DTC) reductions.** The same composite with the
searching flat walks, read through its determinization: the inner walks are
read deterministically as before, and the flat walks, being functional, are
unchanged by it. -/
noncomputable def DTCReduction.trans (g : P ≤ᵈᵗᶜ Q) (f : Q ≤ᵈᵗᶜ R) : P ≤ᵈᵗᶜ R :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  let I : TCInterpretation (L₁.sum Language.order) L₂ g.Tag g.dim := ⟨g.fam.det, g.toRel⟩
  let If : TCInterpretation (L₂.sum Language.order) L₃ f.Tag f.dim := ⟨f.fam.det, f.toRel⟩
  let H := I.flatFamily g.fam.detReachDeciders g.fam.decides_detReachDeciders If.fam true
  let C : I.CompositeBlock g.fam.detReachDeciders g.fam.decides_detReachDeciders If.fam true :=
    { B := (g.fam.sum H).block
      ρ := fun A _ _ => (g.fam.sum H).det.reachAssign A
      ι₁ := fun q => ⟨Sum.inl q.1, q.2⟩
      arity₁ := fun _ => rfl
      ρ₁ := fun _ _ _ _ _ => Iff.rfl
      ι₂ := fun p m n => ⟨Sum.inr p, (m, n)⟩
      arity₂ := fun _ _ _ => rfl
      ρ₂ := fun A _ _ _ _ p m n w =>
        ParamTCSpec.reachAt_det_of_functional
          (I.flatWalk_functional _ _ (If.fam.spec p.1) p.2 (g.fam.functional_detReachDeciders A))
          _ _ _ }
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    fam := g.fam.sum H
    toRel := C.compInterp If
    map_nonempty := fun A _ _ _ _ => by
      let := I.mapLinearOrder A
      have : Finite (I.Map A) := I.map_finite A
      have : Nonempty (I.Map A) := g.map_nonempty A
      obtain ⟨a₀, hbot⟩ := exists_bot A
      exact (f.map_nonempty (I.Map A)).map
        (C.compLEquiv If hbot fun _ i z a b c => ParamTCSpec.det_functional z a b c).symm
    correct := fun A _ _ _ _ => by
      let := I.mapLinearOrder A
      have : Finite (I.Map A) := I.map_finite A
      have : Nonempty (I.Map A) := g.map_nonempty A
      obtain ⟨a₀, hbot⟩ := exists_bot A
      refine (g.correct A).trans ((f.correct (I.Map A)).trans ?_)
      exact (@DecisionProblem.iso_invariant _ _ R _ _ _ _
        (C.compLEquiv If hbot fun _ i z a b c => ParamTCSpec.det_functional z a b c)).symm }

/-- `Trans` instance: FO(TC) reductions compose. -/
noncomputable instance :
    Trans (α := DecisionProblem L₁) (β := DecisionProblem L₂) (γ := DecisionProblem L₃)
      TCReduction TCReduction TCReduction where
  trans g f := g.trans f

/-- `Trans` instance: FO(DTC) reductions compose. -/
noncomputable instance :
    Trans (α := DecisionProblem L₁) (β := DecisionProblem L₂) (γ := DecisionProblem L₃)
      DTCReduction DTCReduction DTCReduction where
  trans g f := g.trans f

end Trans

end DescriptiveComplexity
