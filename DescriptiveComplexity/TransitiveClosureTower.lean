/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureParam
import DescriptiveComplexity.SecondOrderLift
import DescriptiveComplexity.FixedPointStratify

/-!
# Towers of walks: reachability relations that may read earlier ones

A `DescriptiveComplexity.TCFamily` is a finite family of walks over one
vocabulary. What composition of reductions produces is not that: pulling the
walks of an outer reduction back through an inner one gives walks whose step
formulas read the *inner* walks' reachability relations. A
`DescriptiveComplexity.TCTower` is the closure of the notion under that – a
list of families, each over the vocabulary expanded by the blocks of the ones
before it – which is FO(TC) with nesting, the operator applied to formulas that
may themselves contain it.

## The point of the construction

`DescriptiveComplexity.TCTower.inflLimit_toStepDef`: a tower's reachability
relations are the value of a *single* inflationary induction, namely the
stratification (`DescriptiveComplexity.StepDef.stratify`) of the inductions of
its families. Each family is an induction already
(`DescriptiveComplexity.TCFamily.inflLimit_toStepDef`); a stratum reads the
strata below it through the gate the library's stratification already provides,
and the recursion is one line per constructor.

So a tower costs nothing beyond a family: it is still an FO(LFP) interpretation
(`DescriptiveComplexity.TransitiveClosureReduction`), with the same closure
properties. Composition of `≤ᵗᶜ` with itself does not go through towers in
the end (`DescriptiveComplexity.TransitiveClosureReductionTrans` flattens the
outer walks instead); a tower remains the natural reading of nested walks.

## What is *not* claimed

That a tower can be flattened into a single family. Classically it can, and the
notion this file defines is therefore the classical one; here the flattening
is proved one level at a time and at the encodings of nodes
(`DescriptiveComplexity.ParamTCSpec.flat`,
`DescriptiveComplexity.TransitiveClosureFlatten`), which is what the closure of
`DescriptiveComplexity.NL` under `≤ᵗᶜ` uses, and not as an equality of
families; a tower is not flattened as such.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Towers -/

/-- A **tower of walk families**: each family's walks may read the reachability
relations of the families below, its vocabulary being the base expanded by
their blocks. -/
inductive TCTower : Language.{0, 0} → Type 1 where
  /-- The empty tower. -/
  | nil {L : Language.{0, 0}} : TCTower L
  /-- A family, and above it a tower over the vocabulary its block expands. -/
  | cons {L : Language.{0, 0}} (F : TCFamily L) (rest : TCTower (L.sum F.block.lang)) :
      TCTower L

namespace TCTower

/-- The induction with no relation variables: the empty tower's. -/
noncomputable def emptyStepDef (L : Language.{0, 0}) : StepDef L where
  B := SOBlock.trivial
  step := fun i => Empty.elim i
  out := ⊤

/-- The induction that computes a tower's reachability relations: the
stratification of the families' own inductions. -/
noncomputable def toStepDef : ∀ {L : Language.{0, 0}}, TCTower L → StepDef L
  | L, .nil => emptyStepDef L
  | _, .cons F rest => F.toStepDef.stratify (toStepDef rest)

/-- The block of relation variables a tower's formulas may read. -/
noncomputable def block {L : Language.{0, 0}} (T : TCTower L) : SOBlock := T.toStepDef.B

@[simp]
theorem block_nil {L : Language.{0, 0}} : (TCTower.nil (L := L)).block = SOBlock.trivial := rfl

@[simp]
theorem block_cons {L : Language.{0, 0}} (F : TCFamily L)
    (rest : TCTower (L.sum F.block.lang)) :
    (TCTower.cons F rest).block = stratBlock F.block rest.block := rfl

/-! ### The relations a tower holds -/

section Assign

variable {L : Language.{0, 0}} {A : Type}

/-- An assignment of a stratified block, from its three parts. -/
def stratAssign {B₁ B₂ : SOBlock} (ρ₁ : B₁.Assignment A) (g : Prop)
    (ρ₂ : B₂.Assignment A) : (stratBlock B₁ B₂).Assignment A
  | .inl (.inl i) => ρ₁ i
  | .inl (.inr _) => fun _ => g
  | .inr i => ρ₂ i

@[simp]
theorem strat1Assign_stratAssign {B₁ B₂ : SOBlock} (ρ₁ : B₁.Assignment A) (g : Prop)
    (ρ₂ : B₂.Assignment A) : strat1Assign (stratAssign ρ₁ g ρ₂) = ρ₁ := rfl

@[simp]
theorem strat2Assign_stratAssign {B₁ B₂ : SOBlock} (ρ₁ : B₁.Assignment A) (g : Prop)
    (ρ₂ : B₂.Assignment A) : strat2Assign (stratAssign ρ₁ g ρ₂) = ρ₂ := rfl

theorem stratGate_stratAssign {B₁ B₂ : SOBlock} (ρ₁ : B₁.Assignment A) (g : Prop)
    (ρ₂ : B₂.Assignment A) : StratGate (stratAssign ρ₁ g ρ₂) ↔ g := Iff.rfl

/-- **The relations a tower holds**: each family's reachability relations, read
over the structure the families below it have already expanded. The gate of
each stratum is set, as it is at the value of the stratified induction. -/
noncomputable def reachAssign : ∀ {L : Language.{0, 0}} (T : TCTower L) (A : Type)
    (_instA : L.Structure A), T.block.Assignment A
  | _, .nil, _, _ => fun i => Empty.elim i
  | _, .cons F rest, A, instA =>
      stratAssign (@TCFamily.reachAssign _ F A instA) True
        (reachAssign rest A
          (@SOBlock.structure₁ _ F.block A instA (@TCFamily.reachAssign _ F A instA)))

@[simp]
theorem reachAssign_cons {L : Language.{0, 0}} (F : TCFamily L)
    (rest : TCTower (L.sum F.block.lang)) (A : Type) (instA : L.Structure A) :
    (TCTower.cons F rest).reachAssign A instA =
      stratAssign (@TCFamily.reachAssign _ F A instA) True
        (rest.reachAssign A
          (@SOBlock.structure₁ _ F.block A instA (@TCFamily.reachAssign _ F A instA))) :=
  rfl

end Assign

/-! ### A tower is an induction -/

section Limit

variable {L : Language.{0, 0}} {A : Type} [L.Structure A]

/-- An assignment of a stratified block is its three parts. -/
private theorem stratBlock_ext' {B₁ B₂ : SOBlock} {σ τ : (stratBlock B₁ B₂).Assignment A}
    (h1 : strat1Assign σ = strat1Assign τ) (hg : StratGate σ ↔ StratGate τ)
    (h2 : strat2Assign σ = strat2Assign τ) : σ = τ := by
  funext i x
  match i with
  | .inl (.inl i) => exact congrFun (congrFun h1 i) x
  | .inl (.inr _) =>
    have hx : x = Fin.elim0 := funext fun j => j.elim0
    rw [hx]
    exact propext hg
  | .inr j => exact congrFun (congrFun h2 j) x

/-- The gate of a stratified induction is set at its value. -/
private theorem stratGate_inflLimit [Finite A] (d₁ : StepDef L) (d₂ : StepDef (L.sum d₁.B.lang)) :
    StratGate ((d₁.stratify d₂).inflLimit A) := by
  refine ⟨Nat.card (BAtom d₁.B A) + 1, ?_⟩
  exact (d₁.stratGate_inflStage_succ d₂ _).mpr (Or.inr (d₁.isFixedPt_inflStep_card A))

/-- **A tower's relations are the value of one inflationary induction.** -/
theorem inflLimit_toStepDef : ∀ {L : Language.{0, 0}} (T : TCTower L) (A : Type)
    [instA : L.Structure A] [Finite A],
    @StepDef.inflLimit L T.toStepDef A instA = @reachAssign L T A instA := by
  intro L T
  induction T with
  | nil =>
    intro A instA hfin
    funext i
    exact nomatch i
  | @cons L F rest ih =>
    intro A instA hfin
    rw [reachAssign_cons]
    refine stratBlock_ext' ?_ ?_ ?_
    · exact (F.toStepDef.strat1Assign_inflLimit rest.toStepDef).trans
        TCFamily.inflLimit_toStepDef
    · exact iff_of_true (stratGate_inflLimit F.toStepDef rest.toStepDef) trivial
    · refine Eq.trans (F.toStepDef.strat2Assign_inflLimit rest.toStepDef (A := A)) ?_
      have hlim : @StepDef.inflLimit L F.toStepDef A instA = F.reachAssign A :=
        TCFamily.inflLimit_toStepDef
      rw [hlim]
      exact @ih A (@SOBlock.structure₁ L F.block A instA (F.reachAssign A)) hfin

end Limit

end TCTower

end DescriptiveComplexity
