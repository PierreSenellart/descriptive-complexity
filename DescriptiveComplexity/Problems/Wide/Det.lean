/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Wide.WellFormed
import DescriptiveComplexity.Problems.Machine.Space

/-!
# Determinism is a promise a reduction can enforce: `DWideAcceptSpace ≤ᶠᵒ WideAcceptSpace`

The transfer step of the EXPSPACE machine bridge, and the exact analogue of
`DescriptiveComplexity.Problems.Machine.SpaceDet` one exponent up. Hardness
travels *forward* along reductions, so the deterministic problem – the one a
program is naturally proved hard for, its run being unique – hands the
nondeterministic one its hardness as soon as
`DescriptiveComplexity.DWideAcceptSpace` reduces to
`DescriptiveComplexity.WideAcceptSpace`.

The two problems differ only in that the deterministic one folds
`DescriptiveComplexity.WideDet` into its yes-instances, and that condition is
first-order – `DescriptiveComplexity.SpaceTM.detF` is stated at an arbitrary
vocabulary and arbitrary symbols, so the sentence is the same one the
polynomial-level bridge uses, read at
`FirstOrder.Language.wide`'s symbols. The reduction is therefore the *identity*
interpretation – one dimension, one tag – with a single change: the accepting
states of the image are the accepting states of the source **guarded by the
determinism sentence**. A source whose table is deterministic is copied
verbatim, so the two are isomorphic; a source whose table is not has no
accepting state at all in the image, hence no accepting run, and both sides are
no-instances.

Nothing here needs an order, so this is a plain `≤ᶠᵒ` reduction; the ordered
and relativized readings follow.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace WideDetToNondet

/-! ### The interpretation -/

/-- The determinism of the instance, as a first-order formula whose free
variables are unused: the guard the image puts on its accepting states. -/
noncomputable def detG (γ : Type) : Language.wide.Formula γ :=
  SpaceTM.detF wmTr wmStart wmSrc wmRead wmDst wmWrite

/-- **The identity interpretation with a guarded accepting predicate.** Every
symbol is copied; `wmAcc` is copied only when the transition table is
deterministic. -/
noncomputable def detInterp :
    FOInterpretation Language.wide Language.wide Unit 1 where
  relFormula {n} R _ :=
    match n, R with
    | _, .wle => fo%⟨u, v⟩ wmLe(u, v)
    | _, .tr => fo%⟨u⟩ wmTr(u)
    | _, .start => fo%⟨u⟩ wmStart(u)
    | _, .acc => fo%⟨u⟩ !(detG _) ∧ wmAcc(u)
    | _, .blank => fo%⟨u⟩ wmBlank(u)
    | _, .right => fo%⟨u⟩ wmRight(u)
    | _, .src => fo%⟨u, v⟩ wmSrc(u, v)
    | _, .read => fo%⟨u, v⟩ wmRead(u, v)
    | _, .dst => fo%⟨u, v⟩ wmDst(u, v)
    | _, .write => fo%⟨u, v⟩ wmWrite(u, v)
    | _, .inp => fo%⟨u, v⟩ wmInp(u, v)

section Reading

variable {A : Type} [Language.wide.Structure A]

/-- The universe of the image is the universe of the source. -/
noncomputable abbrev toBase (x : detInterp.Map A) : A := detInterp.mapEquivSelf A x

@[simp]
theorem detG_realize {γ : Type} (v : γ → A) :
    (detG γ).Realize v ↔ WideDet A := by
  rw [detG]
  simp only [SpaceTM.realize_detF]
  exact Iff.rfl

/-- The unary symbols other than `wmAcc` are copied, so their reading is the
reading of the source. -/
private theorem rel₁_map (R : Language.wide.Relations 1)
    (h : ∀ t, detInterp.relFormula R t = Relations.formula₁ R (Term.var (0, 0)))
    (x : detInterp.Map A) : (RelMap R ![x] : Prop) ↔ RelMap R ![toBase x] := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A R ![x]) ?_
  rw [h]
  simp only [Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- The binary symbols are copied, so their reading is the reading of the
source. -/
private theorem rel₂_map (R : Language.wide.Relations 2)
    (h : ∀ t, detInterp.relFormula R t =
      Relations.formula₂ R (Term.var (0, 0)) (Term.var (1, 0)))
    (x y : detInterp.Map A) :
    (RelMap R ![x, y] : Prop) ↔ RelMap R ![toBase x, toBase y] := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A R ![x, y]) ?_
  rw [h]
  simp only [Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem tr_map (x : detInterp.Map A) : WMTr x ↔ WMTr (toBase x) :=
  rel₁_map wmTr (fun _ => rfl) x
@[simp] theorem start_map (x : detInterp.Map A) : WMStart x ↔ WMStart (toBase x) :=
  rel₁_map wmStart (fun _ => rfl) x
@[simp] theorem blank_map (x : detInterp.Map A) : WMBlank x ↔ WMBlank (toBase x) :=
  rel₁_map wmBlank (fun _ => rfl) x
@[simp] theorem right_map (x : detInterp.Map A) : WMRight x ↔ WMRight (toBase x) :=
  rel₁_map wmRight (fun _ => rfl) x

@[simp] theorem le_map (x y : detInterp.Map A) :
    WMLe x y ↔ WMLe (toBase x) (toBase y) :=
  rel₂_map wmLe (fun _ => rfl) x y
@[simp] theorem src_map (x y : detInterp.Map A) :
    WMSrc x y ↔ WMSrc (toBase x) (toBase y) :=
  rel₂_map wmSrc (fun _ => rfl) x y
@[simp] theorem read_map (x y : detInterp.Map A) :
    WMRead x y ↔ WMRead (toBase x) (toBase y) :=
  rel₂_map wmRead (fun _ => rfl) x y
@[simp] theorem dst_map (x y : detInterp.Map A) :
    WMDst x y ↔ WMDst (toBase x) (toBase y) :=
  rel₂_map wmDst (fun _ => rfl) x y
@[simp] theorem write_map (x y : detInterp.Map A) :
    WMWrite x y ↔ WMWrite (toBase x) (toBase y) :=
  rel₂_map wmWrite (fun _ => rfl) x y
@[simp] theorem inp_map (x y : detInterp.Map A) :
    WMInp x y ↔ WMInp (toBase x) (toBase y) :=
  rel₂_map wmInp (fun _ => rfl) x y

/-- **The accepting states of the image are guarded**: an element is accepting
there exactly when the source table is deterministic and it is accepting in the
source. -/
@[simp]
theorem acc_map (x : detInterp.Map A) :
    WMAcc x ↔ (WideDet A ∧ WMAcc (toBase x)) := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A wmAcc ![x]) ?_
  simp only [detInterp, Formula.realize_inf, detG_realize, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

/-- **A deterministic instance is copied verbatim**, so the image *is* the
source up to the identification of the two universes. -/
noncomputable def detEquiv (hdet : WideDet A) :
    A ≃[Language.wide] detInterp.Map A where
  toEquiv := (detInterp.mapEquivSelf A).symm
  map_fun' f := isEmptyElim f
  map_rel' {n} R x := by
    have h₁ : ∀ v : Fin 1 → A, (![v 0] : Fin 1 → A) = v :=
      fun v => funext fun i => by fin_cases i; rfl
    have h₂ : ∀ v : Fin 2 → A, (![v 0, v 1] : Fin 2 → A) = v :=
      fun v => funext fun i => by fin_cases i <;> rfl
    rw [FOInterpretation.relMap_map detInterp A R]
    match n, R with
    | _, .wle =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap wmLe v : Prop)) (h₂ x))
    | _, .tr =>
      simp only [detInterp, Formula.realize_rel₁, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap wmTr v : Prop)) (h₁ x))
    | _, .start =>
      simp only [detInterp, Formula.realize_rel₁, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap wmStart v : Prop)) (h₁ x))
    | _, .acc =>
      simp only [detInterp, Formula.realize_inf, detG_realize, Formula.realize_rel₁,
        Term.realize_var]
      exact (and_iff_right hdet).trans
        (iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap wmAcc v : Prop)) (h₁ x)))
    | _, .blank =>
      simp only [detInterp, Formula.realize_rel₁, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap wmBlank v : Prop)) (h₁ x))
    | _, .right =>
      simp only [detInterp, Formula.realize_rel₁, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap wmRight v : Prop)) (h₁ x))
    | _, .src =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap wmSrc v : Prop)) (h₂ x))
    | _, .read =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap wmRead v : Prop)) (h₂ x))
    | _, .dst =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap wmDst v : Prop)) (h₂ x))
    | _, .write =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap wmWrite v : Prop)) (h₂ x))
    | _, .inp =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap wmInp v : Prop)) (h₂ x))

/-- **A nondeterministic instance has no accepting state in the image**, so its
image cannot accept. -/
theorem not_acceptsSpace_of_not_det (hdet : ¬WideDet A) :
    ¬(wideData (detInterp.Map A)).AcceptsSpace := by
  rintro ⟨-, c, -, -, hacc⟩
  match hs : c.state with
  | Sum.inl _ => rw [hs] at hacc; exact hacc.elim
  | Sum.inr x =>
    rw [hs] at hacc
    exact hdet ((acc_map x).mp hacc).1

end Reading

/-- **The reduction is correct**: the image accepts in bounded space exactly
when the source is a well-formed *deterministic* machine accepting in bounded
space. -/
theorem correct (A : Type) [Language.wide.Structure A] [Finite A] [Nonempty A] :
    DWideAcceptSpace A ↔ WideAcceptSpace (detInterp.Map A) := by
  by_cases hdet : WideDet A
  · refine Iff.trans ?_ (WideAcceptSpace.iso_invariant (detEquiv hdet))
    exact ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, wideData_deterministic_iff.mpr hdet, h.2⟩⟩
  · refine ⟨fun h => absurd (wideData_deterministic_iff.mp h.2.1) hdet, fun h => ?_⟩
    exact absurd h.2 (not_acceptsSpace_of_not_det hdet)

end WideDetToNondet

/-- **Deterministic wide acceptance in bounded space reduces to the
nondeterministic problem.** The interpretation is the identity, save that the
image only keeps its accepting states when the source table is deterministic –
a first-order condition, so the promise folded into the yes-instances of
`DescriptiveComplexity.DWideAcceptSpace` is enforced by the reduction itself.
This is what lets the EXPSPACE-hardness of the deterministic problem be proved
once and inherited by `DescriptiveComplexity.WideAcceptSpace`. -/
noncomputable def dwideAcceptSpace_fo_reduction_wideAcceptSpace :
    DWideAcceptSpace ≤ᶠᵒ WideAcceptSpace where
  Tag := Unit
  dim := 1
  toInterpretation := WideDetToNondet.detInterp
  correct := WideDetToNondet.correct

end DescriptiveComplexity
