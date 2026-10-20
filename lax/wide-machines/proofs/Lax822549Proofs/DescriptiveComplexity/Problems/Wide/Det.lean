/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.WellFormed
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Space
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace FirstOrder.Language
export Lax822549.WideMachines (wide wmAcc wmBlank wmDst wmInp wmLe wmRead wmRight wmSrc wmStart wmTr wmWrite)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMDst WMInp WMLe WMRead WMRight WMSrc WMStart WMTr WMWrite wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

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

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace WideDetToNondet

/-! ### The interpretation -/

/-- The determinism of the instance, as a first-order formula whose free
variables are unused: the guard the image puts on its accepting states. -/
noncomputable def detG (γ : Type) : Lax822549.WideMachines.wide.Formula γ :=
  SpaceTM.detF Lax822549.WideMachines.wmTr Lax822549.WideMachines.wmStart Lax822549.WideMachines.wmSrc Lax822549.WideMachines.wmRead Lax822549.WideMachines.wmDst Lax822549.WideMachines.wmWrite

/-- **The identity interpretation with a guarded accepting predicate.** Every
symbol is copied; `wmAcc` is copied only when the transition table is
deterministic. -/
noncomputable def detInterp :
    Lax904597.Interpretations.FOInterpretation Lax822549.WideMachines.wide Lax822549.WideMachines.wide Unit 1 where
  relFormula {n} R _ :=
    match n, R with
    | _, .wle => FirstOrder.Language.Relations.formula₂ Lax822549.WideMachines.wmLe (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .tr => FirstOrder.Language.Relations.formula₁ Lax822549.WideMachines.wmTr (FirstOrder.Language.Term.var (0, 0))
    | _, .start => FirstOrder.Language.Relations.formula₁ Lax822549.WideMachines.wmStart (FirstOrder.Language.Term.var (0, 0))
    | _, .acc => (detG _) ⊓ FirstOrder.Language.Relations.formula₁ Lax822549.WideMachines.wmAcc (FirstOrder.Language.Term.var (0, 0))
    | _, .blank => FirstOrder.Language.Relations.formula₁ Lax822549.WideMachines.wmBlank (FirstOrder.Language.Term.var (0, 0))
    | _, .right => FirstOrder.Language.Relations.formula₁ Lax822549.WideMachines.wmRight (FirstOrder.Language.Term.var (0, 0))
    | _, .src => FirstOrder.Language.Relations.formula₂ Lax822549.WideMachines.wmSrc (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .read => FirstOrder.Language.Relations.formula₂ Lax822549.WideMachines.wmRead (FirstOrder.Language.Term.var (0, 0))
                      (FirstOrder.Language.Term.var (1, 0))
    | _, .dst => FirstOrder.Language.Relations.formula₂ Lax822549.WideMachines.wmDst (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .write => FirstOrder.Language.Relations.formula₂ Lax822549.WideMachines.wmWrite (FirstOrder.Language.Term.var (0, 0))
                       (FirstOrder.Language.Term.var (1, 0))
    | _, .inp => FirstOrder.Language.Relations.formula₂ Lax822549.WideMachines.wmInp (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))

section Reading

variable {A : Type} [Lax822549.WideMachines.wide.Structure A]

/-- The universe of the image is the universe of the source. -/
noncomputable abbrev toBase (x : detInterp.Map A) : A := detInterp.mapEquivSelf A x

@[simp]
theorem detG_realize {γ : Type} (v : γ → A) :
    (detG γ).Realize v ↔ WideDet A := by
  rw [detG]
  simp only [SpaceTM.realize_detF]
  exact Iff.rfl

/-- **The accepting states of the image are guarded**: an element is accepting
there exactly when the source table is deterministic and it is accepting in the
source. -/
@[simp]
theorem acc_map (x : detInterp.Map A) :
    Lax822549.WideMachines.WMAcc x ↔ (WideDet A ∧ Lax822549.WideMachines.WMAcc (toBase x)) := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A Lax822549.WideMachines.wmAcc ![x]) ?_
  simp only [detInterp, Formula.realize_inf, detG_realize, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

/-- **A deterministic instance is copied verbatim**, so the image *is* the
source up to the identification of the two universes. -/
noncomputable def detEquiv (hdet : WideDet A) :
    A ≃[Lax822549.WideMachines.wide] detInterp.Map A where
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
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap Lax822549.WideMachines.wmLe v : Prop)) (h₂ x))
    | _, .tr =>
      simp only [detInterp, Formula.realize_rel₁, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap Lax822549.WideMachines.wmTr v : Prop)) (h₁ x))
    | _, .start =>
      simp only [detInterp, Formula.realize_rel₁, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap Lax822549.WideMachines.wmStart v : Prop)) (h₁ x))
    | _, .acc =>
      simp only [detInterp, Formula.realize_inf, detG_realize, Formula.realize_rel₁,
        Term.realize_var]
      exact (and_iff_right hdet).trans
        (iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap Lax822549.WideMachines.wmAcc v : Prop)) (h₁ x)))
    | _, .blank =>
      simp only [detInterp, Formula.realize_rel₁, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap Lax822549.WideMachines.wmBlank v : Prop)) (h₁ x))
    | _, .right =>
      simp only [detInterp, Formula.realize_rel₁, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 1 → A => (RelMap Lax822549.WideMachines.wmRight v : Prop)) (h₁ x))
    | _, .src =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap Lax822549.WideMachines.wmSrc v : Prop)) (h₂ x))
    | _, .read =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap Lax822549.WideMachines.wmRead v : Prop)) (h₂ x))
    | _, .dst =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap Lax822549.WideMachines.wmDst v : Prop)) (h₂ x))
    | _, .write =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap Lax822549.WideMachines.wmWrite v : Prop)) (h₂ x))
    | _, .inp =>
      simp only [detInterp, Formula.realize_rel₂, Term.realize_var]
      exact iff_of_eq (congrArg (fun v : Fin 2 → A => (RelMap Lax822549.WideMachines.wmInp v : Prop)) (h₂ x))

/-- **A nondeterministic instance has no accepting state in the image**, so its
image cannot accept. -/
theorem not_acceptsSpace_of_not_det (hdet : ¬WideDet A) :
    ¬(Lax822549.WideMachines.wideData (detInterp.Map A)).AcceptsSpace := by
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
theorem correct (A : Type) [Lax822549.WideMachines.wide.Structure A] [Finite A] [Nonempty A] :
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

end Lax822549Proofs.DescriptiveComplexity


