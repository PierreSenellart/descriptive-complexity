/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Reduce
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannelAccept
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannelNo
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannelExpansion
import Lax822549Proofs.DescriptiveComplexity.Exponential.KernelArity
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# The reduction into the register channel

`DescriptiveComplexity.Problems.Wide.Reduce` assembles the reduction into
`DescriptiveComplexity.WideAccept`: the record, the interpretation, the
transport and the hardness statement. This file does the same at the **register
channel** – the same record, the same doubling, the same transport, and one
change: the interpretation writes down the *handed* program
(`nexInterpHandedPad`), whose channel writes for the argument elements and the one
below them, and the problem it lands in is
`DescriptiveComplexity.WideRegAccept`.

The transport is unchanged because it never reads which problem is being asked
about (`wideRegProblem_wideRegInterp_iff` is `wideProblem_wideInterp_iff` at the
other interpretation), so this half of the reduction is free. What is not free
is the machine's correctness, which is the run of
`DescriptiveComplexity.Draw.Data.wideRegAccept_regLaid_of_rules` on the
yes-side and `DescriptiveComplexity.Problems.Wide.DrawNo` on the no-side.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The interpretation the reduction emits -/

section Interp

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

/-- **The handed machine of a source, written down over the doubled universe**:
`DescriptiveComplexity.Draw.dblWideInterp` with the clocked program that is
handed its file, and the channel that writes for the argument elements and the
element below them. The program carries `n` junk rule names, which is what buys
its clock the room the count asks for (`PadRules.lean`); at `n = 0` it is the
plain program with its sites relabeled. -/
noncomputable def dblWideRegInterp (n : ℕ) :
    Lax904597.Interpretations.FOInterpretation ((newLang L).sum Language.order) Lax822549.WideMachines.wide
      ((srcDt X d).NexITagPad ((srcDt X d).d.B.ι → Bool) n) (srcDt X d).dd :=
  letI : LinearOrder ((srcDt X d).NexRIxPad
      (G := (srcDt X d).d.B.ι → Bool) n) := finiteLinearOrder _
  letI : LinearOrder (srcDt X d).NexPF := finiteLinearOrder _
  (srcDt X d).nexInterpHandedPad (srcData_payload_le (relExp X) d)
    (fun v => Data.uVarArgsDef_varArgsOf (dt := srcDt X d)
      (boolEnv (newLang L)) v) none n

/-- **The handed machine of a source, written down in the instance**: the
machine over the doubled universe, composed with the doubling. -/
noncomputable def wideRegInterp (n : ℕ) :
    Lax904597.Interpretations.FOInterpretation (L.sum Language.order) Lax822549.WideMachines.wide
      (((srcDt X d).NexITagPad ((srcDt X d).d.B.ι → Bool) n) ×
        (Fin (srcDt X d).dd → Bool)) ((srcDt X d).dd * 1) :=
  (dblWideRegInterp X d n).comp (dblInterp L).ordExtend

end Interp

/-! ### The composite's universe is the machine's -/

section Transport

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- **The composite interpretation's universe is the machine's over the doubled
universe**, at the handed machine: the composition equivalence followed by the
order extension's, exactly as at the laid one. -/
noncomputable def wideRegInterpEquiv (n : ℕ) :
    (wideRegInterp X d n).Map A ≃[Lax822549.WideMachines.wide]
      (dblWideRegInterp X d n).Map ((dblInterp L).Map A) :=
  Language.Equiv.comp
    ((dblWideRegInterp X d n).mapLEquiv ((dblInterp L).ordExtendLEquiv A))
    ((dblWideRegInterp X d n).compLEquiv (dblInterp L).ordExtend A)

end Transport

/-! ### The interpreted structure reads the handed program's table -/

section RegReads

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

variable (e : Env (newLang L))

/-- The two orders the run layer wants on the handed program's rule names and
phases: an arbitrary one on each, the *same* one the interpretation compares
tags with. -/
noncomputable abbrev srcNexRTagOrder (n : ℕ) :
    LinearOrder ((srcDt X d).NexRIxPad (G := (srcDt X d).d.B.ι → Bool) n) :=
  finiteLinearOrder _

noncomputable abbrev srcNexPFOrder : LinearOrder (srcDt X d).NexPF :=
  finiteLinearOrder _

/-- **The interpreted structure reads the handed program's table** – `srcReads`
at the program a reduction into `DescriptiveComplexity.WideRegAccept`
emits. -/
theorem srcRegReads (n : ℕ) :
    letI := srcNexRTagOrder X d n
    letI := srcNexPFOrder X d
    letI : Lax822549.WideMachines.wide.Structure
        (Univ e.α ((srcDt X d).NexRIxPad (G := (srcDt X d).d.B.ι → Bool) n)
          (srcDt X d).NexPF (srcDt X d).KIx (srcDt X d).dd) :=
      (dblWideRegInterp X d n).mapStructure e.α
    ((srcDt X d).nexProgHandedPad e.zero e.one e.hzo
      (srcData_payload_le (relExp X) d)
      ((srcDt X d).regionSpec e.zero e.one)
      ((fun v => (srcDt X d).varArgsOf e.zero e.one v)) none n).table.Reads :=
  letI := srcNexRTagOrder X d n
  letI := srcNexPFOrder X d
  letI : Lax822549.WideMachines.wide.Structure
      (Univ e.α ((srcDt X d).NexRIxPad (G := (srcDt X d).d.B.ι → Bool) n)
        (srcDt X d).NexPF (srcDt X d).KIx (srcDt X d).dd) :=
    (dblWideRegInterp X d n).mapStructure e.α
  (srcDt X d).reads_nexProgHandedPad (srcData_payload_le (relExp X) d)
    (fun v => Data.uVarArgsDef_varArgsOf (dt := srcDt X d)
      (boolEnv (newLang L)) v) none n e rfl

end RegReads

/-! ### The machine decides the fixed point -/

section Correct

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The emitted machine accepts exactly when some stage satisfies the
kernel**, read over the doubled universe and at the order the encoding pulls
back. This is `dwideAcceptSpace_srcEnv_iff` at the *handed* machine: the record's
own facts – its table is read (`srcRegReads`), its payload fits, its dimension
has slack, its channel marks the argument elements – plus the two the source side
owes, that every guessed variable has an argument and that the padded rule names
outnumber the constant the clock is measured against. -/
theorem wideRegAccept_srcEnv_iff (n : ℕ) :
    letI := srcNexRTagOrder X d n
    letI := srcNexPFOrder X d
    letI : Lax822549.WideMachines.wide.Structure
        (Univ (srcEnv L A).α
          ((srcDt X d).NexRIxPad (G := (srcDt X d).d.B.ι → Bool) n)
          (srcDt X d).NexPF (srcDt X d).KIx (srcDt X d).dd) :=
      (dblWideRegInterp X d n).mapStructure (srcEnv L A).α
    letI : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
      encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
    ∀ (_harity : ∀ iv : (srcDt X d).d.B.ι, 0 < (srcDt X d).d.B.arity iv)
      (_htags : 52 * (4 + (srcDt X d).eDim) * Nat.card (srcDt X d).KIx +
          52 * (4 + (srcDt X d).eDim) + 52 * (15 + (srcDt X d).dimC) + 2 ≤
        Nat.card ((srcDt X d).NexRIxPad (G := (srcDt X d).d.B.ι → Bool) n)),
      (WideRegAccept ((dblWideRegInterp X d n).Map (srcEnv L A).α) ↔
        ∃ σ : (srcDt X d).d.B.Assignment ((srcDt X d).X.Map (srcEnv L A).α),
          @Sentence.Realize _ ((srcDt X d).X.Map (srcEnv L A).α)
            ((srcDt X d).d.B.structure₁ σ) (srcDt X d).d.out) := by
  let := srcNexRTagOrder X d n
  let := srcNexPFOrder X d
  let : Lax822549.WideMachines.wide.Structure
      (Univ (srcEnv L A).α
        ((srcDt X d).NexRIxPad (G := (srcDt X d).d.B.ι → Bool) n)
        (srcDt X d).NexPF (srcDt X d).KIx (srcDt X d).dd) :=
    (dblWideRegInterp X d n).mapStructure (srcEnv L A).α
  let : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
    encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
  have : Nonempty (srcDt X d).KIx := ⟨srcKIx (relExp X) d⟩
  intro harity htags
  -- the encoding's own dimension is at least one: a point's code names a tag
  obtain ⟨t, -, -⟩ := (relExp X).dom_nonempty (srcEnv L A).α
  have : Nonempty (PtCode (relExp X)) := ⟨Sum.inl t⟩
  have hdd0 : 1 ≤ (srcDt X d).dd0 := by
    have h1 : 0 < Nat.card (PtCode (relExp X)) := Nat.card_pos
    have h2 : (srcDt X d).dd0 = encDim (relExp X) := srcData_dd0 (relExp X) d
    rw [h2, encDim]
    omega
  let : LinearOrder ((srcDt X d).NexRIx (G := (srcDt X d).d.B.ι → Bool)) :=
    finiteLinearOrder _
  have hR := srcRegReads X d (srcEnv L A) n
  have hE := Data.nexEmitted_nexProgHandedPad (dt := srcDt X d) (n := n)
    (srcEnv L A).hzo (srcData_payload_le (relExp X) d) none
  obtain ⟨harg, -, -, -⟩ :=
    Data.regFacts_of_marked (zero := (srcEnv L A).zero) hR hE.marked
  exact (srcDt X d).wideRegAccept_iff_exists_out_of_tags
    (srcData_payload_le (relExp X) d) hE hR
    (srcData_dd0_lt (relExp X) d) hdd0 harity (fun _ _ => Iff.rfl) harg
    (fun x => (Table.wmHasInp_iff_marked hR x).trans (hE.marked x)) htags

/-- **The handed machine decides the kernel**, at the doubled universe: the
record's correctness (`wideRegAccept_srcEnv_iff`) read through
`NexKernel.holds_iff_structure₁`, which is the same proposition spelled the
kernel's way. This is `hmach`'s content, with the two obligations the source
side owes still in front of it. -/
theorem wideRegAccept_kernel_iff (K : NexKernel L) (n : ℕ) :
    letI := srcNexRTagOrder K.X K.toStepDef n
    letI := srcNexPFOrder K.X K.toStepDef
    letI : Lax822549.WideMachines.wide.Structure
        (Univ (srcEnv L A).α
          ((srcDt K.X K.toStepDef).NexRIxPad
            (G := (srcDt K.X K.toStepDef).d.B.ι → Bool) n)
          (srcDt K.X K.toStepDef).NexPF (srcDt K.X K.toStepDef).KIx
          (srcDt K.X K.toStepDef).dd) :=
      (dblWideRegInterp K.X K.toStepDef n).mapStructure (srcEnv L A).α
    haveI : Finite ((dblInterp L).Map A) := (dblInterp L).map_finite A
    haveI : Nonempty ((dblInterp L).Map A) := (dblInterp L).map_nonempty A
    letI : LinearOrder ((relExp K.X).Map ((dblInterp L).Map A)) :=
      encOrder (srcDt K.X K.toStepDef).ly (srcEnv L A).zero (srcEnv L A).one
        (srcEnv L A).hzo
    letI : K.X.E.Structure ((relExp K.X).Map ((dblInterp L).Map A)) :=
      Lax480241.Expansions.ExpExpansion.mapStructure (relExp K.X) ((dblInterp L).Map A)
    ∀ (_harity : ∀ iv : (srcDt K.X K.toStepDef).d.B.ι,
        0 < (srcDt K.X K.toStepDef).d.B.arity iv)
      (_htags : 52 * (4 + (srcDt K.X K.toStepDef).eDim) *
            Nat.card (srcDt K.X K.toStepDef).KIx +
          52 * (4 + (srcDt K.X K.toStepDef).eDim) +
          52 * (15 + (srcDt K.X K.toStepDef).dimC) + 2 ≤
        Nat.card ((srcDt K.X K.toStepDef).NexRIxPad
          (G := (srcDt K.X K.toStepDef).d.B.ι → Bool) n)),
      (WideRegAccept ((dblWideRegInterp K.X K.toStepDef n).Map (srcEnv L A).α) ↔
        K.Holds ((relExp K.X).Map ((dblInterp L).Map A))) := by
  intro harity htags
  exact wideRegAccept_srcEnv_iff K.X K.toStepDef A n harity htags

/-- **The emitted instance is a yes-instance exactly when the source is**, for
*any* problem about wide machines: the composite's universe is the machine's
over the doubled universe (`wideRegInterpEquiv`), the caller says what the
machine decides there, and the relativized expansion's points are the
original's. Which problem `PW` is, the transport never asks – which is why the
register channel costs nothing here. -/
theorem wideRegProblem_wideRegInterp_iff (PW : Lax904597.Problems.DecisionProblem Lax822549.WideMachines.wide)
    (n : ℕ) {Q₀ : Lax904597.Problems.DecisionProblem X.E}
    (hmach :
      letI : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
        encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
      letI : X.E.Structure ((relExp X).Map ((dblInterp L).Map A)) :=
        Lax480241.Expansions.ExpExpansion.mapStructure (relExp X) ((dblInterp L).Map A)
      haveI : Finite ((dblInterp L).Map A) := (dblInterp L).map_finite A
      haveI : Nonempty ((dblInterp L).Map A) := (dblInterp L).map_nonempty A
      PW ((dblWideRegInterp X d n).Map (srcEnv L A).α) ↔
        Q₀ ((relExp X).Map ((dblInterp L).Map A))) :
    PW ((wideRegInterp X d n).Map A) ↔ Q₀ (X.Map A) := by
  let : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
    encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
  have : Finite ((dblInterp L).Map A) := (dblInterp L).map_finite A
  have : Nonempty ((dblInterp L).Map A) := (dblInterp L).map_nonempty A
  let : LinearOrder ((relExp X).Map ((dblInterp L).Map A)) :=
    encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
  let : X.E.Structure ((relExp X).Map ((dblInterp L).Map A)) :=
    Lax480241.Expansions.ExpExpansion.mapStructure (relExp X) ((dblInterp L).Map A)
  refine (PW.iso_invariant (wideRegInterpEquiv X d A n)).trans ?_
  exact hmach.trans (Q₀.iso_invariant (relExpMapEquiv (X := X) (A := A))).symm

/-- **The emitted instance is a yes-instance of acceptance on a clock at the
register channel exactly when the source is**, given the handed machine's own
correctness at the doubled universe. -/
theorem wideRegAccept_wideRegInterp_iff (n : ℕ) {Q₀ : Lax904597.Problems.DecisionProblem X.E}
    (hmach :
      letI : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
        encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
      letI : X.E.Structure ((relExp X).Map ((dblInterp L).Map A)) :=
        Lax480241.Expansions.ExpExpansion.mapStructure (relExp X) ((dblInterp L).Map A)
      haveI : Finite ((dblInterp L).Map A) := (dblInterp L).map_finite A
      haveI : Nonempty ((dblInterp L).Map A) := (dblInterp L).map_nonempty A
      WideRegAccept ((dblWideRegInterp X d n).Map (srcEnv L A).α) ↔
        Q₀ ((relExp X).Map ((dblInterp L).Map A))) :
    WideRegAccept ((wideRegInterp X d n).Map A) ↔ Q₀ (X.Map A) :=
  wideRegProblem_wideRegInterp_iff X d A WideRegAccept n hmach

end Correct

end Draw

open FirstOrder

open Language

/-! ### The reduction, and NEXPTIME-hardness -/

section Umbrella

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Every NEXPTIME source problem reduces to acceptance on a clock at the
register channel.** The drawing is the EXPSPACE reduction's at the kernel's own
step definition; only the program written down and the channel it is handed
change. Two paddings make it unconditional: the kernel's variables gain an
argument (`NexKernel.withArg`), which the machine needs to address a stage on its
tape, and the program gains as many junk rule names as the clock's count asks for
(`PadRules.lean`), which costs the drawing nothing and buys its budget outright.
-/
theorem ExpDefinable.ordered_fo_reduction_wideRegAccept {Q : Lax904597.Problems.DecisionProblem L}
    (h : ExpDefinable NP Q) :
    Nonempty (Q ≤ᶠᵒ[≤] WideRegAccept) := by
  obtain ⟨X, Q₀, hQ, hspec⟩ := h
  obtain ⟨B, φ, hker⟩ := exists_orderedKernel (P := Q₀) hQ
  classical
  set K : NexKernel L := (⟨X, B, φ⟩ : NexKernel L).withArg with hK
  set dt := Draw.srcDt K.X K.toStepDef with hdt
  set n : ℕ := 52 * (4 + dt.eDim) * Nat.card dt.KIx + 52 * (4 + dt.eDim) +
    52 * (15 + dt.dimC) + 2 with hn
  refine ⟨{ Tag := (dt.NexITagPad (dt.d.B.ι → Bool) n) × (Fin dt.dd → Bool)
            tagNonempty := ⟨(Draw.Tag.sym, fun _ => false)⟩
            dim := dt.dd * 1
            toInterpretation := Draw.wideRegInterp K.X K.toStepDef n
            correct := fun A _ _ _ _ => ?_ }⟩
  have : Finite ((Draw.dblInterp L).Map A) := (Draw.dblInterp L).map_finite A
  have : Nonempty ((Draw.dblInterp L).Map A) := (Draw.dblInterp L).map_nonempty A
  let : LinearOrder ((Draw.relExp K.X).Map ((Draw.dblInterp L).Map A)) :=
    Draw.encOrder dt.ly (Draw.srcEnv L A).zero (Draw.srcEnv L A).one
      (Draw.srcEnv L A).hzo
  let : LinearOrder ((Draw.relExp X).Map ((Draw.dblInterp L).Map A)) :=
    Draw.encOrder dt.ly (Draw.srcEnv L A).zero (Draw.srcEnv L A).one
      (Draw.srcEnv L A).hzo
  let : X.E.Structure ((Draw.relExp X).Map ((Draw.dblInterp L).Map A)) :=
    Lax480241.Expansions.ExpExpansion.mapStructure (Draw.relExp X) ((Draw.dblInterp L).Map A)
  let : X.E.Structure ((Draw.relExp K.X).Map ((Draw.dblInterp L).Map A)) :=
    Lax480241.Expansions.ExpExpansion.mapStructure (Draw.relExp X) ((Draw.dblInterp L).Map A)
  refine (hspec A).trans (Draw.wideRegAccept_wideRegInterp_iff K.X _ A n ?_).symm
  -- the machine's correctness at this kernel: every variable has an argument,
  -- and the padded rule names outnumber what the clock is measured against
  refine (Draw.wideRegAccept_kernel_iff A K n
    (fun iv => (⟨X, B, φ⟩ : NexKernel L).withArg_arity_pos iv) ?_).trans ?_
  · rw [hn, Draw.Data.card_nexRIxPad]
    exact Nat.le_add_left _ _
  · exact (NexKernel.withArg_holds (⟨X, B, φ⟩ : NexKernel L)).trans
      (hker ((Draw.relExp X).Map ((Draw.dblInterp L).Map A))).symm

/-- **Acceptance on a clock at the register channel is NEXPTIME-hard.** -/
theorem wideRegAccept_NEXPTIME_hard : NEXPTIME.Hard WideRegAccept := by
  refine NEXPTIME_hard_of_expDefinable _ fun {_} _ Q hQ => ?_
  exact (ExpDefinable.ordered_fo_reduction_wideRegAccept hQ).map
    OrderedFOReduction.toRel

/-- **Acceptance on a clock at the register channel is NEXPTIME-complete.** The
membership half is `DescriptiveComplexity.wideRegAccept_mem_NEXPTIME`. -/
theorem wideRegAccept_NEXPTIME_complete : NEXPTIME.Complete WideRegAccept :=
  ⟨wideRegAccept_mem_NEXPTIME, wideRegAccept_NEXPTIME_hard⟩

end Umbrella

end Lax822549Proofs.DescriptiveComplexity


