/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureParam
import DescriptiveComplexity.FixedPointReductionClosure

/-!
# FO(TC) reductions: the logarithmic-space reductions

The reduction notion of `DescriptiveComplexity.NL`: an interpretation whose
defining formulas may consult, besides the input structure, the **reachability
relations of first-order walks** (`DescriptiveComplexity.TCFamily`). It sits
between the two notions already built,

`≤ᶠᵒ[≤]` ⊆ `≤ᵗᶜ` ⊆ `≤ˡᶠᵖ`,

the first inclusion strict (`DescriptiveComplexity.TransitiveClosureReductionStrict`),
and it is what “logarithmic-space reduction” means in a machine-free
development, exactly as `≤ˡᶠᵖ` is what “polynomial-time reduction” means.

## What comes for free, and what does not

A walk is an inflationary induction of a very restricted shape
(`DescriptiveComplexity.TCFamily.inflLimit_toStepDef`), so an FO(TC)
interpretation *is* an FO(LFP) interpretation
(`DescriptiveComplexity.TCInterpretation.toLFP`) and an FO(TC) reduction is an
FO(LFP) reduction (`DescriptiveComplexity.TCReduction.toLFP`). Every closure
theorem of `DescriptiveComplexity.FixedPointReductionClosure` therefore
transfers: PTIME, NP and coNP are closed under `≤ᵗᶜ`, and hardness under
first-order reductions implies hardness under these.

Two things are **not** proved here, and neither is bookkeeping.

* **Transitivity of `≤ᵗᶜ`.** Composing two FO(TC) interpretations pulls the
  outer walks back through the inner interpretation, whose formulas already
  consult walks – so the composite's step formulas contain reachability atoms,
  and flattening them is Immerman's normal form (a `TC` of a formula containing
  a `TC` is a single `TC`). Positively occurring atoms are cheap – suspend the
  outer walk, run the inner one, resume – but a negative occurrence needs
  non-reachability, i.e., inductive counting
  (`DescriptiveComplexity.InductiveCounting`) as a subroutine rather than at
  the top level.
* **Closure of NL itself under `≤ᵗᶜ`**, for the same reason: the membership
  walk pulled back through the reduction is a walk whose steps consult walks.
  The route the other classes took is unavailable here – there the induction
  was absorbed by a *smaller* class already known to sit inside (PTIME inside
  NP), and NL has no smaller class to lean on: the absorption it needs is its
  own normal form. `ROADMAP.md` prices both.

So the honest reading of this file: `≤ᵗᶜ` is a reduction *notion*, with the
closure properties of the classes above NL, and it is not yet a reduction
*order*.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Interpretations that read walks -/

/-- An **FO(TC) interpretation**: a relativized first-order interpretation
whose formulas may read the reachability relations of a finite family of
first-order walks over the base structure.

Over an ordered base (`L := L₀.sum Language.order`) this is Immerman's FO(TC)
reduction, the logical form of a logarithmic-space reduction. -/
structure TCInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) : Type 1 where
  /-- The walks whose reachability relations the formulas may read. -/
  fam : TCFamily L
  /-- The interpretation, over the base vocabulary expanded by the walks'
  relation variables. -/
  toRel : RelFOInterpretation (L.sum fam.block.lang) L' Tag dim

namespace TCInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}
variable (I : TCInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The base structure expanded by the reachability relations of the walks –
the structure the interpretation is read over. -/
@[instance_reducible]
def expStructure : (L.sum I.fam.block.lang).Structure A :=
  I.fam.block.structure₁ (L := L) (I.fam.reachAssign A)

/-- The universe of the interpreted structure. -/
protected def Map : Type :=
  letI := I.expStructure A
  I.toRel.MapRel A

/-- The `L'`-structure interpreted in `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) :=
  letI := I.expStructure A
  RelFOInterpretation.mapRelStructure I.toRel A

theorem map_finite [Finite Tag] [Finite A] : Finite (I.Map A) :=
  letI := I.expStructure A
  I.toRel.mapRel_finite A

/-! ### A walk is an induction, so an FO(TC) interpretation is an FO(LFP) one -/

/-- **An FO(TC) interpretation, read as an FO(LFP) interpretation**: the
family's walks become the one induction that computes their reachability
relations (`DescriptiveComplexity.TCFamily.toStepDef`), and the interpretation
is unchanged. -/
noncomputable def toLFP : LFPInterpretation L L' Tag dim where
  ind := I.fam.toStepDef
  toRel := I.toRel

variable {I A}

/-- The two readings expand the base structure by the same relations: the
value of the induction is the reachability relations. -/
theorem expStructure_toLFP [Finite A] :
    (I.toLFP.expStructure A : (L.sum I.fam.block.lang).Structure A) = I.expStructure A :=
  congrArg (I.fam.block.structure₁ (L := L)) TCFamily.inflLimit_toStepDef

/-- Equal expansions give the same interpreted structure. -/
def mapEquivOfEq [L'.IsRelational] {inst₁ inst₂ : (L.sum I.fam.block.lang).Structure A}
    (h : inst₁ = inst₂) :
    @Language.Equiv L'
      (@RelFOInterpretation.MapRel _ _ _ _ I.toRel A inst₁)
      (@RelFOInterpretation.MapRel _ _ _ _ I.toRel A inst₂)
      (@RelFOInterpretation.mapRelStructure _ _ _ _ I.toRel A inst₁ _)
      (@RelFOInterpretation.mapRelStructure _ _ _ _ I.toRel A inst₂ _) := by
  subst h
  exact { toEquiv := Equiv.refl _
          map_fun' := fun f => isEmptyElim f
          map_rel' := fun R x => Iff.rfl }

/-- **The FO(LFP) reading interprets the same structure**: the identity map on
tagged tuples is an isomorphism. -/
noncomputable def toLFPLEquiv [L'.IsRelational] [Finite A] :
    (I.toLFP).Map A ≃[L'] I.Map A :=
  mapEquivOfEq (I := I) (A := A) expStructure_toLFP

end TCInterpretation

/-! ### FO(TC) reductions -/

variable {L L' : Language.{0, 0}}

/-- An **FO(TC) reduction** from `P` to `Q` – a logarithmic-space reduction, in
the logical form of [Immerman 1999][immerman1999descriptive]: an FO(TC)
interpretation over the ordered expansion of the source vocabulary, mapping
yes-instances exactly to yes-instances, for every finite linear order on the
input. -/
structure TCReduction [L.IsRelational] [L'.IsRelational] (P : DecisionProblem L)
    (Q : DecisionProblem L') : Type 1 where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying FO(TC) interpretation, over the ordered expansion. -/
  toInterpretation : TCInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpreted structure is nonempty on nonempty finite ordered
  inputs. -/
  map_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    Nonempty (toInterpretation.Map A)
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 P:51 " ≤ᵗᶜ " Q:51 => TCReduction P Q

/-! ### Every FO(TC) reduction is an FO(LFP) reduction -/

section ToLFP

variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}

/-- **An FO(TC) reduction is an FO(LFP) reduction**: reachability is an
inflationary induction. Every closure property of `≤ˡᶠᵖ` transfers along
this. -/
noncomputable def TCReduction.toLFP (f : P ≤ᵗᶜ Q) : P ≤ˡᶠᵖ Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation.toLFP
    map_nonempty := fun A _ _ _ _ =>
      (f.map_nonempty A).map (TCInterpretation.toLFPLEquiv (I := f.toInterpretation)).symm
    correct := fun A _ _ _ _ =>
      (f.correct A).trans
        (Q.iso_invariant (TCInterpretation.toLFPLEquiv (I := f.toInterpretation))).symm }

end ToLFP

/-! ### Every first-order reduction is an FO(TC) reduction -/

section OfFO

variable {Tag : Type} {dim : ℕ} [L'.IsRelational]

/-- The empty family of walks: no relation variables, so the expansion is the
structure itself. -/
def TCFamily.empty (L : Language.{0, 0}) : TCFamily L where
  Ix := Empty
  spec := fun i => i.elim

/-- A relativized interpretation, read as an FO(TC) interpretation whose
formulas ignore the walks it is given. -/
def RelFOInterpretation.toTCFam (J : RelFOInterpretation L L' Tag dim) (F : TCFamily L) :
    TCInterpretation L L' Tag dim :=
  ⟨F, J.liftSource LHom.sumInl⟩

/-- An interpretation that ignores its walks produces exactly the structure of
the relativized interpretation it lifts, whatever the walks are: the expansion
interprets the base symbols as the base structure does. -/
def RelFOInterpretation.toTCFamLEquiv (J : RelFOInterpretation L L' Tag dim) (F : TCFamily L)
    (A : Type) [instA : L.Structure A] : (J.toTCFam F).Map A ≃[L'] J.MapRel A :=
  letI := (J.toTCFam F).expStructure A
  J.liftSourceLEquiv LHom.sumInl (inst₀ := instA)
    (inst₁ := (J.toTCFam F).expStructure A) ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- A relativized interpretation, read as an FO(TC) interpretation that
consults no walk. -/
def RelFOInterpretation.toTC (J : RelFOInterpretation L L' Tag dim) :
    TCInterpretation L L' Tag dim :=
  J.toTCFam (TCFamily.empty L)

/-- The FO(TC) interpretation with no walks produces exactly the structure of
the relativized interpretation it lifts. -/
def RelFOInterpretation.toTCLEquiv (J : RelFOInterpretation L L' Tag dim) (A : Type)
    [L.Structure A] : J.toTC.Map A ≃[L'] J.MapRel A :=
  J.toTCFamLEquiv (TCFamily.empty L) A

end OfFO

section Embed

variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}

/-- **A relativized ordered FO reduction is an FO(TC) reduction**, consulting
no walk. -/
def RelOrderedFOReduction.toTC (f : P ≤ʳᶠᵒ[≤] Q) : P ≤ᵗᶜ Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toRelInterpretation.toTC
    map_nonempty := fun A _ _ _ _ =>
      (f.mapRel_nonempty A).map (f.toRelInterpretation.toTCLEquiv A).symm
    correct := fun A _ _ _ _ =>
      (f.correct A).trans (Q.iso_invariant (f.toRelInterpretation.toTCLEquiv A)).symm }

/-- **An ordered FO reduction is an FO(TC) reduction.** -/
def OrderedFOReduction.toTC (f : P ≤ᶠᵒ[≤] Q) : P ≤ᵗᶜ Q :=
  f.toRel.toTC

/-- **An FO reduction is an FO(TC) reduction.** -/
noncomputable def FOReduction.toTC (f : P ≤ᶠᵒ Q) : P ≤ᵗᶜ Q :=
  f.toOrdered.toRel.toTC

end Embed

/-! ### The classes above NL are closed under FO(TC) reductions -/

section Closure

variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}

/-- **PTIME is closed under FO(TC) reductions.** -/
theorem mem_PTIME_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ PTIME) : P ∈ PTIME :=
  mem_PTIME_of_lfpReduction f.toLFP h

/-- **NP is closed under FO(TC) reductions.** -/
theorem mem_NP_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ NP) : P ∈ NP :=
  mem_NP_of_lfpReduction f.toLFP h

/-- **coNP is closed under FO(TC) reductions.** -/
theorem mem_coNP_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ coNP) : P ∈ coNP :=
  mem_coNP_of_lfpReduction f.toLFP h

end Closure

end DescriptiveComplexity
