/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax134656Proofs.DescriptiveComplexity.Problems.Machine.Space
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Machines (TMAcc TMBlank TMDst TMInp TMLe TMPosn TMRead TMRight TMSrc TMStart TMTr TMWrite tmData)
end Lax134656Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing)
end FirstOrder.Language

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

/-!
# Determinism is a promise a reduction can enforce: `DTMAcceptSpace ≤ᶠᵒ NTMAcceptSpace`

The transfer step of the PSPACE machine bridge. Hardness travels *forward*
along reductions, so a single hardness proof – for the deterministic problem,
which is the harder one to establish – gives the nondeterministic one as soon
as `DescriptiveComplexity.DTMAcceptSpace` reduces to
`DescriptiveComplexity.NTMAcceptSpace`.

The two problems differ only in that the deterministic one folds
`DescriptiveComplexity.TMData.Deterministic` into its yes-instances. That
condition is first-order (`DescriptiveComplexity.SpaceTM.detF`), so the
reduction is the *identity* interpretation – one dimension, one tag – with a
single change: the accepting states of the image are the accepting states of
the source **guarded by the determinism sentence**. A source whose table is
deterministic is copied verbatim; a source whose table is not has no accepting
state at all in the image, hence no accepting run, and both sides are
no-instances.

Nothing here needs an order, so this is a plain `≤ᶠᵒ` reduction; the ordered
and relativized readings follow.
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace DetToNondet

/-! ### The interpretation -/

/-- The determinism of the instance, as a first-order formula whose free
variables are unused: the guard the image puts on its accepting states. -/
noncomputable def detG (γ : Type) : Lax904597.Machines.turing.Formula γ :=
  SpaceTM.detF Lax904597.Machines.tmTr Lax904597.Machines.tmStart Lax904597.Machines.tmSrc Lax904597.Machines.tmRead Lax904597.Machines.tmDst Lax904597.Machines.tmWrite

/-- **The identity interpretation with a guarded accepting predicate.** Every
symbol is copied; `acc` is copied only when the transition table is
deterministic. -/
noncomputable def detInterp : Lax904597.Interpretations.FOInterpretation Lax904597.Machines.turing Lax904597.Machines.turing Unit 1 where
  relFormula {n} R _ :=
    match n, R with
    | _, .posn => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmPosn (FirstOrder.Language.Term.var (0, 0))
    | _, .tr => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmTr (FirstOrder.Language.Term.var (0, 0))
    | _, .start => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmStart (FirstOrder.Language.Term.var (0, 0))
    | _, .acc => (detG _) ⊓ FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmAcc (FirstOrder.Language.Term.var (0, 0))
    | _, .blank => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmBlank (FirstOrder.Language.Term.var (0, 0))
    | _, .right => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmRight (FirstOrder.Language.Term.var (0, 0))
    | _, .le => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmLe (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .tsrc => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmSrc (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .tread => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmRead (FirstOrder.Language.Term.var (0, 0))
                       (FirstOrder.Language.Term.var (1, 0))
    | _, .tdst => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmDst (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .twrite => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmWrite (FirstOrder.Language.Term.var (0, 0))
                        (FirstOrder.Language.Term.var (1, 0))
    | _, .inp => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmInp (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))

section Reading

variable {A : Type} [Lax904597.Machines.turing.Structure A]

/-- The universe of the image is the universe of the source. -/
noncomputable abbrev toBase (x : detInterp.Map A) : A := detInterp.mapEquivSelf A x

@[simp]
theorem detG_realize {γ : Type} (v : γ → A) :
    (detG γ).Realize v ↔ (Lax904597.Machines.tmData A).Deterministic := by
  rw [detG]
  simp only [SpaceTM.realize_detF]
  exact Iff.rfl

/-- The unary symbols other than `acc` are copied, so their reading is the
reading of the source. -/
private theorem rel₁_map (R : Lax904597.Machines.turing.Relations 1)
    (h : ∀ t, detInterp.relFormula R t = Relations.formula₁ R (Term.var (0, 0)))
    (x : detInterp.Map A) : (RelMap R ![x] : Prop) ↔ RelMap R ![toBase x] := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A R ![x]) ?_
  rw [h]
  simp only [Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- The binary symbols are copied, so their reading is the reading of the
source. -/
private theorem rel₂_map (R : Lax904597.Machines.turing.Relations 2)
    (h : ∀ t, detInterp.relFormula R t =
      Relations.formula₂ R (Term.var (0, 0)) (Term.var (1, 0)))
    (x y : detInterp.Map A) :
    (RelMap R ![x, y] : Prop) ↔ RelMap R ![toBase x, toBase y] := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A R ![x, y]) ?_
  rw [h]
  simp only [Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem posn_map (x : detInterp.Map A) : Lax904597.Machines.TMPosn x ↔ Lax904597.Machines.TMPosn (toBase x) :=
  rel₁_map Lax904597.Machines.tmPosn (fun _ => rfl) x

@[simp] theorem tr_map (x : detInterp.Map A) : Lax904597.Machines.TMTr x ↔ Lax904597.Machines.TMTr (toBase x) :=
  rel₁_map Lax904597.Machines.tmTr (fun _ => rfl) x

@[simp] theorem start_map (x : detInterp.Map A) : Lax904597.Machines.TMStart x ↔ Lax904597.Machines.TMStart (toBase x) :=
  rel₁_map Lax904597.Machines.tmStart (fun _ => rfl) x

@[simp] theorem blank_map (x : detInterp.Map A) : Lax904597.Machines.TMBlank x ↔ Lax904597.Machines.TMBlank (toBase x) :=
  rel₁_map Lax904597.Machines.tmBlank (fun _ => rfl) x

@[simp] theorem right_map (x : detInterp.Map A) : Lax904597.Machines.TMRight x ↔ Lax904597.Machines.TMRight (toBase x) :=
  rel₁_map Lax904597.Machines.tmRight (fun _ => rfl) x

@[simp] theorem le_map (x y : detInterp.Map A) : Lax904597.Machines.TMLe x y ↔ Lax904597.Machines.TMLe (toBase x) (toBase y) :=
  rel₂_map Lax904597.Machines.tmLe (fun _ => rfl) x y

@[simp] theorem src_map (x y : detInterp.Map A) : Lax904597.Machines.TMSrc x y ↔ Lax904597.Machines.TMSrc (toBase x) (toBase y) :=
  rel₂_map Lax904597.Machines.tmSrc (fun _ => rfl) x y

@[simp] theorem read_map (x y : detInterp.Map A) :
    Lax904597.Machines.TMRead x y ↔ Lax904597.Machines.TMRead (toBase x) (toBase y) :=
  rel₂_map Lax904597.Machines.tmRead (fun _ => rfl) x y

@[simp] theorem dst_map (x y : detInterp.Map A) : Lax904597.Machines.TMDst x y ↔ Lax904597.Machines.TMDst (toBase x) (toBase y) :=
  rel₂_map Lax904597.Machines.tmDst (fun _ => rfl) x y

@[simp] theorem write_map (x y : detInterp.Map A) :
    Lax904597.Machines.TMWrite x y ↔ Lax904597.Machines.TMWrite (toBase x) (toBase y) :=
  rel₂_map Lax904597.Machines.tmWrite (fun _ => rfl) x y

@[simp] theorem inp_map (x y : detInterp.Map A) : Lax904597.Machines.TMInp x y ↔ Lax904597.Machines.TMInp (toBase x) (toBase y) :=
  rel₂_map Lax904597.Machines.tmInp (fun _ => rfl) x y

/-- **The accepting states of the image are guarded**: an element is accepting
there exactly when the source table is deterministic and it is accepting in the
source. -/
@[simp]
theorem acc_map (x : detInterp.Map A) :
    Lax904597.Machines.TMAcc x ↔ ((Lax904597.Machines.tmData A).Deterministic ∧ Lax904597.Machines.TMAcc (toBase x)) := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A Lax904597.Machines.tmAcc ![x]) ?_
  simp only [detInterp, Formula.realize_inf, detG_realize, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

/-- **A deterministic instance is copied verbatim.** -/
theorem agree_of_det (hdet : (Lax904597.Machines.tmData A).Deterministic) :
    (Lax904597.Machines.tmData (detInterp.Map A)).Agree (detInterp.mapEquivSelf A) (Lax904597.Machines.tmData A) where
  posn := posn_map
  le := le_map
  tr := tr_map
  start := start_map
  acc x := (acc_map x).trans (and_iff_right hdet)
  blank := blank_map
  right := right_map
  src := src_map
  read := read_map
  dst := dst_map
  write := write_map
  inp := inp_map

/-- **A nondeterministic instance has no accepting state in the image**, so its
image cannot accept. -/
theorem not_acceptsSpace_of_not_det (hdet : ¬(Lax904597.Machines.tmData A).Deterministic) :
    ¬(Lax904597.Machines.tmData (detInterp.Map A)).AcceptsSpace := by
  rintro ⟨-, c, -, -, hacc⟩
  exact hdet ((acc_map c.state).mp hacc).1

end Reading

/-- **The reduction is correct**: the image accepts in bounded space exactly
when the source is a well-formed *deterministic* machine accepting in bounded
space. -/
theorem correct (A : Type) [Lax904597.Machines.turing.Structure A] [Finite A] [Nonempty A] :
    DTMAcceptSpace A ↔ NTMAcceptSpace (detInterp.Map A) := by
  by_cases hdet : (Lax904597.Machines.tmData A).Deterministic
  · have h := agree_of_det hdet
    exact ⟨fun ⟨hwf, _, hacc⟩ => ⟨h.wellFormed.mpr hwf, h.acceptsSpace.mpr hacc⟩,
      fun ⟨hwf, hacc⟩ => ⟨h.wellFormed.mp hwf, hdet, h.acceptsSpace.mp hacc⟩⟩
  · exact ⟨fun h => absurd h.2.1 hdet, fun h => absurd h.2 (not_acceptsSpace_of_not_det hdet)⟩

end DetToNondet

/-- **Deterministic space-bounded acceptance reduces to the nondeterministic
problem.** The interpretation is the identity, save that the image only keeps
its accepting states when the source table is deterministic – a first-order
condition, so the promise folded into the yes-instances of
`DescriptiveComplexity.DTMAcceptSpace` is enforced by the reduction itself. -/
noncomputable def dtmAcceptSpace_fo_reduction_ntmAcceptSpace :
    DTMAcceptSpace ≤ᶠᵒ NTMAcceptSpace where
  Tag := Unit
  dim := 1
  toInterpretation := DetToNondet.detInterp
  correct := DetToNondet.correct

end Lax134656Proofs.DescriptiveComplexity


