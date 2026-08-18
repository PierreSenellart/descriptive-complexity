/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureDet
import DescriptiveComplexity.SecondOrderPull
import DescriptiveComplexity.OrderedComposition

/-!
# Pulling FO(TC) and FO(DTC) definability back through an interpretation

FO(TC) and FO(DTC) definability are closed under (ordered) first-order
reductions (`DescriptiveComplexity.TCDefinable.of_orderedReduction`,
`DescriptiveComplexity.DTCDefinable.of_orderedReduction`). This is what makes
`DescriptiveComplexity.LOGSPACE` a `DescriptiveComplexity.ComplexityClass` rather than a
mere definability predicate, and it upgrades FO(TC) from the definability
notion of `DescriptiveComplexity.TransitiveClosure` to one closed the same way.

## The walk on the interpreted structure, read on the base structure

A `DescriptiveComplexity.TCSpec` walks on *nodes*: a mode together with a `k`-tuple.
Pulling it back through a `d`-dimensional interpretation with tag type `Tag`
means walking on the nodes of the interpreted structure while writing
everything in terms of the base one, and the arithmetic of that is entirely in
the node type:

* a `k`-tuple of interpreted elements is `k` tags together with `k · d`
  coordinates, so the pulled specification has modes
  `spec.Mode × (Fin spec.k → Tag)` – the tags of the current tuple ride along
  in the mode, exactly as they ride along in the clause instances of
  `DescriptiveComplexity.SecondOrderPull` – and arity `spec.k * d`;
* the three formulas are the ordinary formula pullback
  `DescriptiveComplexity.FOInterpretation.pullF` at those tags, re-indexed from
  argument-then-coordinate to a flat tuple by `finProdFinEquiv`;
* `DescriptiveComplexity.comapNodeEquiv` is the resulting bijection between the nodes
  of the pullback over `A` and the nodes of the original over the interpreted
  structure, and it carries steps to steps
  (`DescriptiveComplexity.TCSpec.comap_step_iff`) and endpoints to endpoints.

The order enters as it does for the clausal fragments: the specification's
formulas live over the *ordered* expansion of the target vocabulary, so the
pullback goes through `DescriptiveComplexity.FOInterpretation.ordExtend`, which
interprets the target's order as the lexicographic order on tagged tuples, and
the interpreted structure is equipped with that same order
(`DescriptiveComplexity.FOInterpretation.mapLinearOrder`). Since FO(TC) definability
is required *for every* linear order, the lexicographic one is available.

## Determinism travels for free

Everything about determinism reduces to one observation: the node
correspondence is a *bijection*, and “this step has no competitor” is preserved
by a bijection of node sets (`DescriptiveComplexity.TCSpec.det_step_congr`). So the
pullback of the determinization and the determinization of the pullback have
the same walk, and `DescriptiveComplexity.DTCDefinable` is closed under reductions by
the same argument as `DescriptiveComplexity.TCDefinable`, with no side condition to
re-establish – which is the point of taking determinization to be a formula
(see `DescriptiveComplexity.TransitiveClosureDet`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Pulling back a formula at an arbitrary variable type

`DescriptiveComplexity.guardPull` pulls back a formula whose variables are `Fin k`; the
transition formula of a `DescriptiveComplexity.TCSpec` has two tuples of variables,
so the same pullback is needed at an arbitrary variable type. -/

section PullF

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}
  {β : Type}

/-- The pullback of a formula at an arbitrary variable type: an `L₁`-formula on
the coordinates of the original variables, which realizes in `A` exactly as the
formula realizes in the interpreted structure. -/
noncomputable def FOInterpretation.pullF (I : FOInterpretation L₁ L₂ Tag d)
    (φ : L₂.Formula β) (τ : β → Tag) : L₁.Formula (β × Fin d) :=
  (I.pull (φ : L₂.BoundedFormula β 0) (Sum.elim τ finZeroElim)).relabel
    fun p => (Sum.elim id finZeroElim p.1, p.2)

theorem realize_pullF {A : Type} [L₁.Structure A] (I : FOInterpretation L₁ L₂ Tag d)
    (φ : L₂.Formula β) (τ : β → Tag) (v : β × Fin d → A) :
    (I.pullF φ τ).Realize v ↔
      φ.Realize (M := I.Map A) fun b => (τ b, fun j => v (b, j)) := by
  rw [FOInterpretation.pullF, Formula.realize_relabel, I.realize_pull]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.Map A) (φ : L₂.BoundedFormula β 0) a b)
    (funext fun _ => rfl) (Subsingleton.elim _ _))

end PullF

/-! ### Transfer along a bijection of nodes

Acceptance only depends on the walk up to a bijection of its nodes. Stated for
two specifications over two vocabularies, since the pullback relates a
specification over the base structure to one over the interpreted structure. -/

section Transfer

variable {L L' : Language.{0, 0}} {spec₁ : TCSpec L} {spec₂ : TCSpec L'}
  {A B : Type} [L.Structure A] [LinearOrder A] [L'.Structure B] [LinearOrder B]

namespace TCSpec

theorem reach_map (e : spec₁.Node A ≃ spec₂.Node B)
    (hstep : ∀ a b, spec₁.Step a b ↔ spec₂.Step (e a) (e b)) {a b : spec₁.Node A}
    (h : spec₁.Reach a b) : spec₂.Reach (e a) (e b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail ((hstep c d).mp hcd)

/-- **Acceptance transfers along a bijection of nodes** carrying steps to
steps and endpoints to endpoints. -/
theorem accepts_congr (e : spec₁.Node A ≃ spec₂.Node B)
    (hstep : ∀ a b, spec₁.Step a b ↔ spec₂.Step (e a) (e b))
    (hsrc : ∀ a, spec₁.IsSrc a ↔ spec₂.IsSrc (e a))
    (htgt : ∀ a, spec₁.IsTgt a ↔ spec₂.IsTgt (e a)) :
    spec₁.Accepts A ↔ spec₂.Accepts B := by
  have hstep' : ∀ a b, spec₂.Step a b ↔ spec₁.Step (e.symm a) (e.symm b) := by
    intro a b
    rw [hstep (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply]
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨e u, e v, (hsrc u).mp hu, (htgt v).mp hv, reach_map e hstep huv⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    refine ⟨e.symm u, e.symm v, ?_, ?_, reach_map e.symm hstep' huv⟩
    · rw [hsrc, e.apply_symm_apply]
      exact hu
    · rw [htgt, e.apply_symm_apply]
      exact hv

/-- **Determinization transfers along a bijection of nodes**: having no
competing successor is a property of the walk, not of its presentation. -/
theorem det_step_congr (e : spec₁.Node A ≃ spec₂.Node B)
    (hstep : ∀ a b, spec₁.Step a b ↔ spec₂.Step (e a) (e b)) (a b : spec₁.Node A) :
    spec₁.det.Step a b ↔ spec₂.det.Step (e a) (e b) := by
  rw [spec₁.det_step_iff, spec₂.det_step_iff]
  refine and_congr (hstep a b) ⟨fun h c hc => ?_, fun h c hc => ?_⟩
  · have hc' : spec₁.Step a (e.symm c) := by
      rw [hstep, e.apply_symm_apply]
      exact hc
    rw [← h (e.symm c) hc', e.apply_symm_apply]
  · exact e.injective (h (e c) ((hstep a c).mp hc))

/-- On a functional specification the deterministic reading changes nothing,
acceptance included. -/
theorem det_accepts_iff (spec : TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]
    (h : spec.Functional A) : spec.det.Accepts A ↔ spec.Accepts A :=
  accepts_congr (Equiv.refl (spec.Node A)) (fun a b => det_step_of_functional h a b)
    (fun _ => Iff.rfl) fun _ => Iff.rfl

end TCSpec

end Transfer

/-! ### The pullback of a specification -/

section Comap

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}

/-- The renaming of the pulled transition formula's variables: a coordinate of
an argument becomes a coordinate of the corresponding flat tuple, the two
tuples staying apart. -/
def comapStepIx (k d : ℕ) : (Fin k ⊕ Fin k) × Fin d → Fin (k * d) ⊕ Fin (k * d) :=
  fun p =>
    Sum.elim (fun i => Sum.inl (finProdFinEquiv (i, p.2)))
      (fun i => Sum.inr (finProdFinEquiv (i, p.2))) p.1

/-- The renaming of a pulled endpoint formula's variables: argument and
coordinate become a position of the flat tuple. -/
def comapEndIx (k d : ℕ) : Fin k × Fin d → Fin (k * d) :=
  fun p => finProdFinEquiv p

/-- **The pullback of a specification through an interpretation**: the walk of
`spec` on the interpreted structure, written on the base structure. The tags of
the current tuple ride along in the mode; its coordinates become the flat tuple
of length `k · d`; the three formulas are pulled back at those tags, through
the order-extended interpretation, the specification's formulas being allowed
to mention the target's order. -/
noncomputable def TCSpec.comap (spec : TCSpec L')
    (I : FOInterpretation (L.sum Language.order) L' Tag d) : TCSpec L where
  Mode := spec.Mode × (Fin spec.k → Tag)
  k := spec.k * d
  step p q :=
    (I.ordExtend.pullF (spec.step p.1 q.1) (Sum.elim p.2 q.2)).relabel
      (comapStepIx spec.k d)
  src p := (I.ordExtend.pullF (spec.src p.1) p.2).relabel (comapEndIx spec.k d)
  tgt p := (I.ordExtend.pullF (spec.tgt p.1) p.2).relabel (comapEndIx spec.k d)

variable (spec : TCSpec L') (I : FOInterpretation (L.sum Language.order) L' Tag d)
variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The bijection between the nodes of the pullback over the base structure and
the nodes of the specification over the interpreted structure: a mode is a mode
with a tuple of tags, and a flat tuple of coordinates is a tuple of tagged
tuples. -/
def comapNodeEquiv :
    letI := I.mapLinearOrder A
    (spec.comap I).Node A ≃ spec.Node (I.Map A) where
  toFun a := (a.1.1, tagVal I a.1.2 a.2)
  invFun b :=
    ((b.1, fun p => (b.2 p).1),
      fun m => (b.2 (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2)
  left_inv a := by
    refine Prod.ext_iff.mpr ⟨rfl, funext fun m => ?_⟩
    exact congrArg a.2 ((congrArg finProdFinEquiv Prod.mk.eta).trans
      (finProdFinEquiv.apply_symm_apply m))
  right_inv b := Prod.ext_iff.mpr ⟨rfl, tagVal_split I b.2⟩

/-! ### Correctness of the pullback

Realizing a pulled formula on the base structure is realizing the original on
the interpreted structure – once the latter is read with the lexicographic
order, which is what the order-extended interpretation produces. The two
structures live on the same type and differ only in how the order symbol is
read, so the transport below is spelled with explicit instances. -/

omit [Finite Tag] in
/-- Reading a formula of the ordered expansion of the target on the structure
produced by the order-extended interpretation is reading it on the interpreted
structure equipped with the lexicographic order. -/
theorem realize_ordExtend_iff {β : Type} (φ : (L'.sum Language.order).Formula β)
    (v : β → I.Map A) :
    @Formula.Realize (L'.sum Language.order) (I.ordExtend.Map A)
        (FOInterpretation.mapStructure I.ordExtend A) β φ v ↔
      @Formula.Realize (L'.sum Language.order) (I.Map A)
        (letI := I.mapLinearOrder A; sumOrderStructure L' (I.Map A)) β φ v := by
  letI := I.mapLinearOrder A
  exact (StrongHomClass.realize_formula (M := I.ordExtend.Map A)
    (I.ordExtendLEquiv A) (φ := φ) (v := v)).symm

/-- **Steps correspond**: a step of the pullback on the base structure is a step
of the specification on the interpreted structure. -/
theorem TCSpec.comap_step_iff (a b : (spec.comap I).Node A) :
    letI := I.mapLinearOrder A
    (spec.comap I).Step a b ↔
      spec.Step (comapNodeEquiv spec I a) (comapNodeEquiv spec I b) := by
  letI := I.mapLinearOrder A
  have h1 := (Formula.realize_relabel
      (φ := I.ordExtend.pullF (spec.step a.1.1 b.1.1) (Sum.elim a.1.2 b.1.2))
      (g := comapStepIx spec.k d) (v := Sum.elim a.2 b.2)).trans
    (realize_pullF I.ordExtend (spec.step a.1.1 b.1.1) (Sum.elim a.1.2 b.1.2)
      (Sum.elim a.2 b.2 ∘ comapStepIx spec.k d))
  have henv : (fun s => ((Sum.elim a.1.2 b.1.2 s : Tag),
        fun j => (Sum.elim a.2 b.2 ∘ comapStepIx spec.k d) (s, j)))
      = Sum.elim (tagVal I a.1.2 a.2) (tagVal I b.1.2 b.2) := by
    funext s
    rcases s with i | i <;> rfl
  refine (h1.trans (iff_of_eq (congrArg
    (fun w => @Formula.Realize (L'.sum Language.order) (I.ordExtend.Map A)
      (FOInterpretation.mapStructure I.ordExtend A) _ (spec.step a.1.1 b.1.1) w)
    henv))).trans ?_
  exact realize_ordExtend_iff I (spec.step a.1.1 b.1.1) _

/-- **Starting nodes correspond.** -/
theorem TCSpec.comap_isSrc_iff (a : (spec.comap I).Node A) :
    letI := I.mapLinearOrder A
    (spec.comap I).IsSrc a ↔ spec.IsSrc (comapNodeEquiv spec I a) := by
  letI := I.mapLinearOrder A
  have h1 := (Formula.realize_relabel
      (φ := I.ordExtend.pullF (spec.src a.1.1) a.1.2)
      (g := comapEndIx spec.k d) (v := a.2)).trans
    (realize_pullF I.ordExtend (spec.src a.1.1) a.1.2 (a.2 ∘ comapEndIx spec.k d))
  exact h1.trans (realize_ordExtend_iff I (spec.src a.1.1) _)

/-- **Accepting nodes correspond.** -/
theorem TCSpec.comap_isTgt_iff (a : (spec.comap I).Node A) :
    letI := I.mapLinearOrder A
    (spec.comap I).IsTgt a ↔ spec.IsTgt (comapNodeEquiv spec I a) := by
  letI := I.mapLinearOrder A
  have h1 := (Formula.realize_relabel
      (φ := I.ordExtend.pullF (spec.tgt a.1.1) a.1.2)
      (g := comapEndIx spec.k d) (v := a.2)).trans
    (realize_pullF I.ordExtend (spec.tgt a.1.1) a.1.2 (a.2 ∘ comapEndIx spec.k d))
  exact h1.trans (realize_ordExtend_iff I (spec.tgt a.1.1) _)

/-- **The pullback is correct**: it accepts the base structure exactly when the
specification accepts the interpreted one. -/
theorem TCSpec.comap_accepts_iff :
    letI := I.mapLinearOrder A
    (spec.comap I).Accepts A ↔ spec.Accepts (I.Map A) := by
  letI := I.mapLinearOrder A
  exact TCSpec.accepts_congr (comapNodeEquiv spec I) (spec.comap_step_iff I)
    (spec.comap_isSrc_iff I) (spec.comap_isTgt_iff I)

/-- **The pullback is correct for the deterministic reading too**, by the same
node bijection: determinism is a property of the walk. -/
theorem TCSpec.comap_det_accepts_iff :
    letI := I.mapLinearOrder A
    (spec.comap I).det.Accepts A ↔ spec.det.Accepts (I.Map A) := by
  letI := I.mapLinearOrder A
  exact TCSpec.accepts_congr (comapNodeEquiv spec I)
    (TCSpec.det_step_congr (comapNodeEquiv spec I) (spec.comap_step_iff I))
    (spec.comap_isSrc_iff I) (spec.comap_isTgt_iff I)

end Comap

/-! ### Closure under reductions -/

section Closure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L}
  {Q : DecisionProblem L'}

/-- **FO(TC) definability is closed under ordered first-order reductions.** The
walk of the specification on the interpreted structure is a walk on the base
structure, its tags carried in the mode and its coordinates flattened. -/
theorem TCDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : TCDefinable Q) :
    TCDefinable P := by
  obtain ⟨spec, hspec⟩ := h
  letI := f.tagFinite
  letI := f.tagNonempty
  letI : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨spec.comap f.toInterpretation, ?_⟩
  intro A _ _ _ _
  letI := f.toInterpretation.mapLinearOrder A
  haveI := f.toInterpretation.map_finite A
  haveI := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans ((hspec (f.toInterpretation.Map A)).trans
    (spec.comap_accepts_iff f.toInterpretation).symm)

/-- FO(TC) definability is closed under first-order reductions. -/
theorem TCDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : TCDefinable Q) : TCDefinable P :=
  h.of_orderedReduction f.toOrdered

/-- **FO(DTC) definability is closed under ordered first-order reductions**, by
the same pullback: the node bijection carries the determinized walk to the
determinized walk. -/
theorem DTCDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : DTCDefinable Q) :
    DTCDefinable P := by
  obtain ⟨spec, hspec⟩ := h
  letI := f.tagFinite
  letI := f.tagNonempty
  letI : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨spec.comap f.toInterpretation, ?_⟩
  intro A _ _ _ _
  letI := f.toInterpretation.mapLinearOrder A
  haveI := f.toInterpretation.map_finite A
  haveI := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans ((hspec (f.toInterpretation.Map A)).trans
    (spec.comap_det_accepts_iff f.toInterpretation).symm)

/-- FO(DTC) definability is closed under first-order reductions. -/
theorem DTCDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : DTCDefinable Q) : DTCDefinable P :=
  h.of_orderedReduction f.toOrdered

end Closure

end DescriptiveComplexity
