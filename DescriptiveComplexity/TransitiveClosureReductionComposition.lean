/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureReductionDet
import DescriptiveComplexity.FixedPointReductionComposition

/-!
# Composing an FO(TC) reduction with a first-order one

An FO(TC) reduction followed by a first-order reduction is an FO(TC) reduction
(`DescriptiveComplexity.TCReduction.trans_rel` and its variants). This is the
half of transitivity that needs no normal form: the outer reduction contributes
no walks, so the composite consults exactly the walks the inner one did.

## Why this half is free and the other is not

Composing `P ≤ᵗᶜ Q` with `Q ≤ʳᶠᵒ[≤] R` pulls the *outer* interpretation's
formulas back through the inner one. Those formulas are first-order over `Q`'s
vocabulary; what the pullback substitutes for their atoms are the inner
interpretation's formulas, which read the inner walks. So the composite's
formulas read the same walks, at the same nesting depth, and the family is
carried over unchanged – the composition is
`DescriptiveComplexity.RelFOInterpretation.compRel` under the walks, with the
lexicographic order supplied to the outer reduction by
`DescriptiveComplexity.RelFOInterpretation.ordExtendSrc`.

The other half – `P ≤ᵗᶜ Q` followed by `Q ≤ᵗᶜ R` – is where the nesting
appears: the outer *walks* run on the interpreted structure, and pulling them
back gives walks whose step formulas read the inner walks' reachability atoms.
Those flatten (`DescriptiveComplexity.ParamTCSpec.flat`), and the inner
interpretation extended to their vocabulary substitutes the flattened atoms
for the outer ones: that is `DescriptiveComplexity.TCReduction.trans`, in
`DescriptiveComplexity.TransitiveClosureReductionTrans`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The composite interpretation -/

section Comp

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₂.IsRelational] [L₃.IsRelational]
variable {Tag₁ Tag₂ : Type} [Finite Tag₁] [LinearOrder Tag₁] {d₁ d₂ : ℕ}

/-- **An FO(TC) interpretation followed by a relativized first-order one.**
The walks are those of the inner interpretation, unchanged; the interpretations
compose with the guarded pullback, the intermediate structure carrying the
lexicographic order. -/
noncomputable def RelFOInterpretation.compTC
    (J : RelFOInterpretation (L₂.sum Language.order) L₃ Tag₂ d₂)
    (I : TCInterpretation (L₁.sum Language.order) L₂ Tag₁ d₁) :
    TCInterpretation (L₁.sum Language.order) L₃ (Tag₂ × (Fin d₂ → Tag₁)) (d₂ * d₁) where
  fam := I.fam
  toRel := J.compRel (I.toRel.ordExtendSrc LHom.sumInl)

variable (I : TCInterpretation (L₁.sum Language.order) L₂ Tag₁ d₁)
variable (A : Type) [L₁.Structure A] [LinearOrder A]

/-- The lexicographic order on the structure an FO(TC) interpretation
produces. -/
@[instance_reducible]
noncomputable def TCInterpretation.mapLinearOrder : LinearOrder (I.Map A) :=
  I.toRel.mapRelLinearOrderSrc (I.expStructure A)

variable (J : RelFOInterpretation (L₂.sum Language.order) L₃ Tag₂ d₂)

/-- **The composite interprets the twice-interpreted structure**: the outer
interpretation read on the inner one's output, ordered lexicographically. -/
noncomputable def RelFOInterpretation.compTCLEquiv :
    @Language.Equiv L₃ ((J.compTC I).Map A)
      (@RelFOInterpretation.MapRel (L₂.sum Language.order) L₃ Tag₂ d₂ J (I.Map A)
        (letI := I.mapLinearOrder A; sumOrderStructure L₂ (I.Map A)))
      (TCInterpretation.mapStructure (J.compTC I) A)
      (@RelFOInterpretation.mapRelStructure (L₂.sum Language.order) L₃ Tag₂ d₂ J (I.Map A)
        (letI := I.mapLinearOrder A; sumOrderStructure L₂ (I.Map A)) _) := by
  letI := I.expStructure A
  letI := I.mapLinearOrder A
  letI : LinearOrder (@RelFOInterpretation.MapRel ((L₁.sum Language.order).sum I.fam.block.lang)
      L₂ Tag₁ d₁ I.toRel A (I.expStructure A)) := I.mapLinearOrder A
  exact (J.mapRelLEquiv (I.toRel.ordExtendSrcLEquiv LHom.sumInl (I.expStructure A)
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩)).comp
    (J.compLEquivRel (I.toRel.ordExtendSrc LHom.sumInl))

end Comp

/-! ### Composition of reductions -/

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂} {R : DecisionProblem L₃}

/-- **An FO(TC) reduction followed by a relativized first-order reduction.**
The composite consults exactly the walks the inner reduction did. -/
noncomputable def TCReduction.trans_rel (g : P ≤ᵗᶜ Q) (f : Q ≤ʳᶠᵒ[≤] R) : P ≤ᵗᶜ R :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toInterpretation := f.toRelInterpretation.compTC g.toInterpretation
    map_nonempty := fun A _ _ _ _ => by
      let := g.toInterpretation.mapLinearOrder A
      have : Finite (g.toInterpretation.Map A) := g.toInterpretation.map_finite A
      have : Nonempty (g.toInterpretation.Map A) := g.map_nonempty A
      exact (f.mapRel_nonempty (g.toInterpretation.Map A)).map
        (f.toRelInterpretation.compTCLEquiv g.toInterpretation A).symm
    correct := fun A _ _ _ _ => by
      let := g.toInterpretation.mapLinearOrder A
      have : Finite (g.toInterpretation.Map A) := g.toInterpretation.map_finite A
      have : Nonempty (g.toInterpretation.Map A) := g.map_nonempty A
      refine (g.correct A).trans ((f.correct (g.toInterpretation.Map A)).trans ?_)
      exact (R.iso_invariant
        (f.toRelInterpretation.compTCLEquiv g.toInterpretation A)).symm }

/-- An FO(TC) reduction followed by an ordered first-order reduction. -/
noncomputable def TCReduction.trans_fo (g : P ≤ᵗᶜ Q) (f : Q ≤ᶠᵒ[≤] R) : P ≤ᵗᶜ R :=
  g.trans_rel f.toRel

/-- An FO(DTC) reduction followed by a relativized first-order reduction. -/
noncomputable def DTCReduction.trans_rel (g : P ≤ᵈᵗᶜ Q) (f : Q ≤ʳᶠᵒ[≤] R) : P ≤ᵗᶜ R :=
  g.toTC.trans_rel f

/-- `Trans` instance: an FO(TC) reduction composes with an ordered first-order
one. -/
noncomputable instance :
    Trans (α := DecisionProblem L₁) (β := DecisionProblem L₂) (γ := DecisionProblem L₃)
      TCReduction OrderedFOReduction TCReduction where
  trans g f := g.trans_fo f

end Trans

end DescriptiveComplexity
