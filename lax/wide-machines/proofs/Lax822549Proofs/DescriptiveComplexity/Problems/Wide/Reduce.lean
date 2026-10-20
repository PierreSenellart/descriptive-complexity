/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RelExpMap
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.ShFinite
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawNo
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexPack
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawPack
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Membership
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Det
import Lax822549Proofs.DescriptiveComplexity.Relativized
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

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.SecondOrderFixedPoints
end Lax480241.SecondOrderFixedPoints

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549Proofs.DescriptiveComplexity.SOPFPDefinable
end Lax822549Proofs.DescriptiveComplexity.SOPFPDefinable

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

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.SecondOrderFixedPoints (SOPFPDefinable)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (PFPHolds)
end Lax535992.InflationaryFixedPoint.StepDef

/-!
# The EXPSPACE reduction, assembled

Everything the reduction stands on is built elsewhere; this file chooses the
constants and puts them together.

* the **base** is the doubled universe, never a singleton, whose bottom and top
  are the marked copy of the instance's minimum and the junk copy of its maximum
  (`DescriptiveComplexity.Draw.isBot_dblPt`, `isTop_dblPt`);
* the **data** is the relativized expansion packed by
  `DescriptiveComplexity.Draw.Data.ofSource`, at a dimension wide enough for
  both the encoding and the payload (`DescriptiveComplexity.Draw.srcDim`) – the
  knot being that the slot inventory depends on the encoding budget, so the
  budget is chosen first and the record built twice at the same budget.

The payload bound `Fintype.card (CtlIx ⊕ SlotIx) ≤ dd` is *not* here, and the
reason is worth recording. It is true because no budget of the record reads the
dimension, but it is not `rfl`: `DescriptiveComplexity.Draw.Data.nOf` and every
budget above it is defined by a match on `dt.VarIx`, so the matcher takes the
whole record as a parameter and two records differing in *any* field are opaque
to each other. What closes it is `Finset.sup_congr` down the chain, each step
instantiated at a *constructor* of the index so that the matcher reduces.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The extremes of the doubled universe -/

section Extremes

variable {L : Language.{0, 0}} [L.IsRelational]

variable {A : Type} [L.Structure A] [LinearOrder A]

omit [L.IsRelational] [L.Structure A] in
theorem isBot_dblPt {a : A} (ha : IsBot a) : IsBot (dblPt (L := L) false a) := by
  intro p
  refine (tagTupleLe_iff_le (dblPt (L := L) false a) p).mp ?_
  rcases hp : p.1 with _ | _
  · exact Or.inr ⟨hp.symm, (tupLeLex_one _ _).mpr (ha (p.2 0))⟩
  · refine Or.inl ?_
    change (false : Bool) < p.1
    rw [hp]
    decide

omit [L.IsRelational] [L.Structure A] in
theorem isTop_dblPt {a : A} (ha : IsTop a) : IsTop (dblPt (L := L) true a) := by
  intro p
  refine (tagTupleLe_iff_le p (dblPt (L := L) true a)).mp ?_
  rcases hp : p.1 with _ | _
  · refine Or.inl ?_
    change p.1 < (true : Bool)
    rw [hp]
    decide
  · exact Or.inr ⟨hp, (tupLeLex_one _ _).mpr (ha (p.2 0))⟩

end Extremes

/-! ### The budgets do not read the dimension

Every budget of a `DescriptiveComplexity.Draw.Data` is a function of the
expansion, the step definition and the packs; none reads the dimension. That is
*not* `rfl`, though: `DescriptiveComplexity.Draw.Data.nOf` and its relatives
are defined by a match, so their compiled matchers take the whole record as a
parameter and two records differing in the dimension are opaque to each other.
What closes it is a congruence at every level, each instantiated at a
**constructor** of the scrutinee, where the matcher reduces. -/

section Budgets

variable {L : Language.{0, 0}} [L.IsRelational]

variable {X : Lax480241.Expansions.ExpExpansion L} {d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order)}

variable {dd dd' : ℕ} (h : encDim X ≤ dd) (h' : encDim X ≤ dd')

omit [L.IsRelational] in
theorem ofSource_nOf (v : (Data.ofSource X d h).VarIx) :
    (Data.ofSource X d h).nOf v = (Data.ofSource X d h').nOf v := by
  match v with
  | none => rfl
  | some i => rfl

omit [L.IsRelational] in
theorem ofSource_natOf (v : (Data.ofSource X d h).VarIx) :
    (Data.ofSource X d h).natOf v = (Data.ofSource X d h').natOf v := by
  match v with
  | none => rfl
  | some i => rfl

omit [L.IsRelational] in
theorem ofSource_kindDepth {n : ℕ} (κ : MatAtom X d.B n) :
    (Data.ofSource X d h).kindDepth κ = (Data.ofSource X d h').kindDepth κ := by
  match κ with
  | .stage _ _ => rfl
  | .exp _ _ => rfl
  | .eq _ _ => rfl
  | .ord _ _ => rfl

omit [L.IsRelational] in
theorem ofSource_kindReads {n : ℕ} (κ : MatAtom X d.B n) :
    (Data.ofSource X d h).kindReads κ = (Data.ofSource X d h').kindReads κ := by
  match κ with
  | .stage _ _ => rfl
  | .exp _ _ => rfl
  | .eq _ _ => rfl
  | .ord _ _ => rfl

omit [L.IsRelational] in
theorem ofSource_kindArgs {n : ℕ} (κ : MatAtom X d.B n) :
    (Data.ofSource X d h).kindArgs κ = (Data.ofSource X d h').kindArgs κ := by
  match κ with
  | .stage _ _ => rfl
  | .exp _ _ => rfl
  | .eq _ _ => rfl
  | .ord _ _ => rfl

omit [L.IsRelational] in
theorem ofSource_ki : (Data.ofSource X d h).ki = (Data.ofSource X d h').ki := by
  unfold Data.ki
  exact Finset.sup_congr rfl fun v _ => ofSource_nOf h h' v

omit [L.IsRelational] in
theorem ofSource_naDim :
    (Data.ofSource X d h).naDim = (Data.ofSource X d h').naDim := by
  unfold Data.naDim
  rw [ofSource_ki h h']

omit [L.IsRelational] in
theorem ofSource_natMax :
    (Data.ofSource X d h).natMax = (Data.ofSource X d h').natMax := by
  unfold Data.natMax
  exact Finset.sup_congr rfl fun v _ => ofSource_natOf h h' v

omit [L.IsRelational] in
theorem ofSource_eDim : (Data.ofSource X d h).eDim = (Data.ofSource X d h').eDim := by
  unfold Data.eDim
  refine congrArg₂ max rfl (Finset.sup_congr rfl fun v _ => ?_)
  match v with
  | none => exact Finset.sup_congr rfl fun a _ => ofSource_kindDepth h h' _
  | some i => exact Finset.sup_congr rfl fun a _ => ofSource_kindDepth h h' _

omit [L.IsRelational] in
theorem ofSource_nfDim :
    (Data.ofSource X d h).nfDim = (Data.ofSource X d h').nfDim := by
  unfold Data.nfDim
  refine congrArg₂ max rfl (Finset.sup_congr rfl fun v _ => ?_)
  match v with
  | none => exact Finset.sup_congr rfl fun a _ => ofSource_kindReads h h' _
  | some i => exact Finset.sup_congr rfl fun a _ => ofSource_kindReads h h' _

omit [L.IsRelational] in
theorem ofSource_ntgDim :
    (Data.ofSource X d h).ntgDim = (Data.ofSource X d h').ntgDim := by
  unfold Data.ntgDim
  refine congrArg₂ (· * ·) (congrArg₂ (· + ·) (Finset.sup_congr rfl fun v _ => ?_) rfl) rfl
  match v with
  | none => exact Finset.sup_congr rfl fun a _ => ofSource_kindArgs h h' _
  | some i => exact Finset.sup_congr rfl fun a _ => ofSource_kindArgs h h' _

omit [L.IsRelational] in
/-- **The control inventory does not read the dimension.** -/
theorem ofSource_ctlIx :
    (Data.ofSource X d h).CtlIx = (Data.ofSource X d h').CtlIx := by
  unfold Data.CtlIx
  rw [ofSource_eDim h h', ofSource_naDim h h', ofSource_natMax h h',
    ofSource_nfDim h h', ofSource_ntgDim h h']

omit [L.IsRelational] in
/-- **Nor does the track inventory.** -/
theorem ofSource_slotIx :
    (Data.ofSource X d h).SlotIx = (Data.ofSource X d h').SlotIx := by
  unfold Data.SlotIx
  rw [ofSource_ki h h']
  rfl

end Budgets

/-! ### The record a source is packed into, at a dimension that fits -/

section Dim

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

/-- The record at the bare encoding budget: only its slot and control
inventories are read, and neither depends on the dimension. -/
noncomputable def srcData0 : Data L := Data.ofSource X d (le_refl (encDim X))

/-- **The dimension the reduction works at**: one coordinate of slack beyond the
encoding budget, and wide enough for a rule's payload. -/
noncomputable def srcDim : ℕ :=
  max (encDim X + 1) (Nat.card ((srcData0 X d).CtlIx ⊕ (srcData0 X d).SlotIx))

omit [L.IsRelational] in
theorem encDim_lt_srcDim : encDim X < srcDim X d :=
  lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

/-- **The record the reduction works at.** -/
noncomputable def srcData : Data L :=
  Data.ofSource X d (le_of_lt (encDim_lt_srcDim X d))

omit [L.IsRelational] in
theorem srcData_dd0 : (srcData X d).dd0 = encDim X := rfl

omit [L.IsRelational] in
theorem srcData_dd : (srcData X d).dd = srcDim X d := rfl

omit [L.IsRelational] in
theorem srcData_dd0_lt : (srcData X d).dd0 < (srcData X d).dd :=
  encDim_lt_srcDim X d

omit [L.IsRelational] in
/-- **A rule's payload fits the dimension**: the inventories do not read it, so
the count taken at the bare encoding budget is the count at the real one. -/
theorem srcData_payload_le :
    Fintype.card ((srcData X d).CtlIx ⊕ (srcData X d).SlotIx) ≤ (srcData X d).dd := by
  have hT : ((srcData X d).CtlIx ⊕ (srcData X d).SlotIx) =
      ((srcData0 X d).CtlIx ⊕ (srcData0 X d).SlotIx) := by
    rw [show (srcData X d).CtlIx = (srcData0 X d).CtlIx from ofSource_ctlIx _ _,
      show (srcData X d).SlotIx = (srcData0 X d).SlotIx from ofSource_slotIx _ _]
  rw [srcData_dd, srcDim, ← Nat.card_eq_fintype_card]
  exact le_trans (le_of_eq (Nat.card_congr (Equiv.cast hT))) (le_max_right _ _)

/-- The block index of the packed record is nonempty: the output pack was
padded. -/
noncomputable def srcKIx : (srcData X d).KIx :=
  Sum.inrₗ ⟨0, Data.ki_pos X d (le_of_lt (encDim_lt_srcDim X d))⟩

end Dim

/-! ### The interpretation the reduction emits -/

section Interp

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

/-- **The record the reduction runs at**: the relativized expansion, packed. -/
noncomputable abbrev srcDt : Data (newLang L) := srcData (relExp X) d

/-- The accepting predicate of the emitted program: the output machinery's exit
phase, with its verdict read from the control. -/
noncomputable def srcAccept (e : Env (newLang L)) :
    (srcDt X d).PF → ((srcDt X d).CtlIx → e.α) → Prop :=
  fun p f => p = OuterPh.acceptP ∧ ((srcDt X d).varArgsOf e.zero e.one none).accBit f

theorem uGDefinable_srcAccept (p : (srcDt X d).PF) :
    UGDefinable fun (e : Env (newLang L)) f (_ : (srcDt X d).SlotIx → e.α) =>
      srcAccept X d e p f :=
  (uGDefinable_const (p = OuterPh.acceptP)).and
    (Data.uVarArgsDef_varArgsOf (dt := srcDt X d) (boolEnv (newLang L)) none).accBit

/-- **The machine of a source, written down over the doubled universe.** -/
noncomputable def dblWideInterp :
    Lax904597.Interpretations.FOInterpretation ((newLang L).sum Language.order) Lax822549.WideMachines.wide
      (srcDt X d).ITag (srcDt X d).dd :=
  letI : LinearOrder (srcDt X d).RTag := finiteLinearOrder _
  letI : LinearOrder (srcDt X d).PF := finiteLinearOrder _
  (srcDt X d).drawInterp (srcData_payload_le (relExp X) d)
    (Data.uRulesDefinable_progOf (dt := srcDt X d) (boolEnv (newLang L)))
    (uGDefinable_srcAccept X d) OuterPh.start
    (Data.regFileMark (srcData_payload_le (relExp X) d))

/-- **The machine of a source, written down in the instance**: the machine over
the doubled universe, composed with the doubling. The dimension is unchanged –
the doubling is one-dimensional – and the tags only gain a Boolean per
coordinate. -/
noncomputable def wideInterp :
    Lax904597.Interpretations.FOInterpretation (L.sum Language.order) Lax822549.WideMachines.wide
      ((srcDt X d).ITag × (Fin (srcDt X d).dd → Bool)) ((srcDt X d).dd * 1) :=
  (dblWideInterp X d).comp (dblInterp L).ordExtend

end Interp

/-! ### The composite's universe is the machine's -/

section Transport

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- **The composite interpretation's universe is the machine's over the doubled
universe**: the composition equivalence, followed by the order extension's. -/
noncomputable def wideInterpEquiv :
    (wideInterp X d).Map A ≃[Lax822549.WideMachines.wide] (dblWideInterp X d).Map ((dblInterp L).Map A) :=
  Language.Equiv.comp ((dblWideInterp X d).mapLEquiv ((dblInterp L).ordExtendLEquiv A))
    ((dblWideInterp X d).compLEquiv (dblInterp L).ordExtend A)

end Transport

/-! ### The interpreted structure reads the program's table -/

section Reads

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

variable (e : Env (newLang L))

/-- The two orders the run layer wants on the rule names and the phases: an
arbitrary one on each, the *same* one the interpretation compares tags with. -/
noncomputable abbrev srcRTagOrder : LinearOrder (srcDt X d).RTag := finiteLinearOrder _

noncomputable abbrev srcPFOrder : LinearOrder (srcDt X d).PF := finiteLinearOrder _

/-- **The interpreted structure reads the emitted program's table.** -/
theorem srcReads :
    letI := srcRTagOrder X d
    letI := srcPFOrder X d
    letI : LinearOrder ((srcDt X d).RIx e.zero e.one e.hzo
      fun w => (srcDt X d).varArgsOf e.zero e.one w) := srcRTagOrder X d
    letI : Lax822549.WideMachines.wide.Structure
        (Univ e.α ((srcDt X d).RIx e.zero e.one e.hzo
          fun w => (srcDt X d).varArgsOf e.zero e.one w)
          (srcDt X d).PF (srcDt X d).KIx (srcDt X d).dd) :=
      (dblWideInterp X d).mapStructure e.α
    ((srcDt X d).progOf e.zero e.one e.hzo
      (srcData_payload_le (relExp X) d)).table.Reads :=
  letI := srcRTagOrder X d
  letI := srcPFOrder X d
  letI : Lax822549.WideMachines.wide.Structure
      (Univ e.α (srcDt X d).RTag (srcDt X d).PF (srcDt X d).KIx (srcDt X d).dd) :=
    (dblWideInterp X d).mapStructure e.α
  (srcDt X d).reads_progFrom (srcData_payload_le (relExp X) d)
    (Data.uRulesDefinable_progOf (dt := srcDt X d) (boolEnv (newLang L)))
    (uGDefinable_srcAccept X d) OuterPh.start
    (Data.regFileMark (srcData_payload_le (relExp X) d)) e rfl

end Reads

/-! ### The machine decides the fixed point -/

section Correct

variable {L : Language.{0, 0}} [L.IsRelational]

variable (X : Lax480241.Expansions.ExpExpansion L) (d : Lax535992.InflationaryFixedPoint.StepDef (X.E.sum Language.order))

variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The environment the reduction runs at**: the doubled universe, with the
marked copy of the instance's minimum and the junk copy of its maximum as the
two designated elements. -/
noncomputable def srcEnv (L : Language.{0, 0}) [L.IsRelational] (A : Type)
    [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] : Env (newLang L) where
  α := (dblInterp L).Map A
  fin := (dblInterp L).map_finite A
  ne := (dblInterp L).map_nonempty A
  zero := dblPt false (Finite.exists_min (id : A → A)).choose
  one := dblPt true (Finite.exists_max (id : A → A)).choose
  hbot := isBot_dblPt (Finite.exists_min (id : A → A)).choose_spec
  htop := isTop_dblPt (Finite.exists_max (id : A → A)).choose_spec
  hzo := fun h => Bool.false_ne_true (congrArg Prod.fst h)

/-- **The emitted machine accepts exactly when the partial fixed point holds**,
read over the doubled universe and at the order the encoding pulls back. -/
theorem dwideAcceptSpace_srcEnv_iff :
    letI : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
      encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
    (DWideAcceptSpace ((dblWideInterp X d).Map (srcEnv L A).α) ↔
      (srcDt X d).d.PFPHolds ((srcDt X d).X.Map (srcEnv L A).α)) := by
  let : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
    encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
  let := srcRTagOrder X d
  let := srcPFOrder X d
  let : LinearOrder ((srcDt X d).RIx (srcEnv L A).zero (srcEnv L A).one
      (srcEnv L A).hzo fun w => (srcDt X d).varArgsOf (srcEnv L A).zero
        (srcEnv L A).one w) := srcRTagOrder X d
  let : Lax822549.WideMachines.wide.Structure
      (Univ (srcEnv L A).α ((srcDt X d).RIx (srcEnv L A).zero (srcEnv L A).one
        (srcEnv L A).hzo fun w => (srcDt X d).varArgsOf (srcEnv L A).zero
          (srcEnv L A).one w) (srcDt X d).PF (srcDt X d).KIx (srcDt X d).dd) :=
    (dblWideInterp X d).mapStructure (srcEnv L A).α
  exact (srcDt X d).dwideAcceptSpace_iff_pfpHolds (srcReads X d (srcEnv L A))
    (srcData_dd0_lt (relExp X) d) (srcKIx (relExp X) d) fun _ _ => Iff.rfl

/-- **The transport from the doubled universe to the instance**, for *any*
question asked of the emitted machine. Three isomorphisms and nothing else: the
composite's universe is the machine's (`wideInterpEquiv`), the caller says what
the machine decides over the doubled universe, and the relativized expansion's
points are the original's (`relExpMapEquiv`). Which problem `PW` is – acceptance
in bounded space, acceptance on a clock, deterministic or not – the transport
never asks. -/
theorem wideProblem_wideInterp_iff (PW : Lax904597.Problems.DecisionProblem Lax822549.WideMachines.wide)
    {Q₀ : Lax904597.Problems.DecisionProblem X.E}
    (hmach :
      letI : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
        encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
      letI : X.E.Structure ((relExp X).Map ((dblInterp L).Map A)) :=
        Lax480241.Expansions.ExpExpansion.mapStructure (relExp X) ((dblInterp L).Map A)
      haveI : Finite ((dblInterp L).Map A) := (dblInterp L).map_finite A
      haveI : Nonempty ((dblInterp L).Map A) := (dblInterp L).map_nonempty A
      PW ((dblWideInterp X d).Map (srcEnv L A).α) ↔
        Q₀ ((relExp X).Map ((dblInterp L).Map A))) :
    PW ((wideInterp X d).Map A) ↔ Q₀ (X.Map A) := by
  let : LinearOrder ((srcDt X d).X.Map (srcEnv L A).α) :=
    encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
  have : Finite ((dblInterp L).Map A) := (dblInterp L).map_finite A
  have : Nonempty ((dblInterp L).Map A) := (dblInterp L).map_nonempty A
  let : LinearOrder ((relExp X).Map ((dblInterp L).Map A)) :=
    encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
  let : X.E.Structure ((relExp X).Map ((dblInterp L).Map A)) :=
    Lax480241.Expansions.ExpExpansion.mapStructure (relExp X) ((dblInterp L).Map A)
  refine (PW.iso_invariant (wideInterpEquiv X d A)).trans ?_
  exact hmach.trans (Q₀.iso_invariant (relExpMapEquiv (X := X) (A := A))).symm

/-- **The emitted instance is a yes-instance exactly when the source is**: the
composite's universe is the machine's over the doubled universe, the machine
decides the fixed point there, the fixed point is the problem of the relativized
expansion, and that expansion's points are the original's. -/
theorem dwideAcceptSpace_wideInterp_iff {Q₀ : Lax904597.Problems.DecisionProblem X.E}
    (hd : ∀ (M : Type) [X.E.Structure M] [LinearOrder M] [Finite M] [Nonempty M],
      Q₀ M ↔ d.PFPHolds M) :
    DWideAcceptSpace ((wideInterp X d).Map A) ↔ Q₀ (X.Map A) := by
  have : Finite ((dblInterp L).Map A) := (dblInterp L).map_finite A
  have : Nonempty ((dblInterp L).Map A) := (dblInterp L).map_nonempty A
  let : LinearOrder ((relExp X).Map ((dblInterp L).Map A)) :=
    encOrder (srcDt X d).ly (srcEnv L A).zero (srcEnv L A).one (srcEnv L A).hzo
  let : X.E.Structure ((relExp X).Map ((dblInterp L).Map A)) :=
    Lax480241.Expansions.ExpExpansion.mapStructure (relExp X) ((dblInterp L).Map A)
  refine wideProblem_wideInterp_iff X d A DWideAcceptSpace ?_
  exact (dwideAcceptSpace_srcEnv_iff X d A).trans
    (hd ((relExp X).Map ((dblInterp L).Map A))).symm

end Correct

end Draw

open FirstOrder

open Language

/-! ### The reduction, and EXPSPACE-hardness -/

section Umbrella

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Every SO(≤, PFP) definable problem reduces to deterministic acceptance in
bounded space on a wide machine.** -/
theorem SOPFPDefinable.ordered_fo_reduction_dwideAcceptSpace {Q : Lax904597.Problems.DecisionProblem L}
    (h : Lax480241.SecondOrderFixedPoints.SOPFPDefinable Q) : Nonempty (Q ≤ᶠᵒ[≤] DWideAcceptSpace) := by
  obtain ⟨X, Q₀, hpfp, hspec⟩ := h
  obtain ⟨d, hd⟩ := hpfp
  exact ⟨{ Tag := (Draw.srcDt X d).ITag × (Fin (Draw.srcDt X d).dd → Bool)
           tagNonempty := ⟨(Draw.Tag.sym, fun _ => false)⟩
           dim := (Draw.srcDt X d).dd * 1
           toInterpretation := Draw.wideInterp X d
           correct := fun A _ _ _ _ =>
             (hspec A).trans (Draw.dwideAcceptSpace_wideInterp_iff X d A hd).symm }⟩

end Umbrella

end Lax822549Proofs.DescriptiveComplexity

namespace Lax480241.SecondOrderFixedPoints.SOPFPDefinable

export Lax822549Proofs.DescriptiveComplexity.SOPFPDefinable (ordered_fo_reduction_dwideAcceptSpace)

end Lax480241.SecondOrderFixedPoints.SOPFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language

section Umbrella

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Deterministic acceptance in bounded space on a wide machine is
EXPSPACE-hard.** -/
theorem dwideAcceptSpace_EXPSPACE_hard : EXPSPACE.Hard DWideAcceptSpace := by
  refine EXPSPACE_hard_of_sopfpDefinable _ fun {_} _ Q hQ => ?_
  exact (SOPFPDefinable.ordered_fo_reduction_dwideAcceptSpace hQ).map
    OrderedFOReduction.toRel

/-- **Deterministic acceptance in bounded space on a wide machine is
EXPSPACE-complete.** The membership half is
`DescriptiveComplexity.dwideAcceptSpace_mem_EXPSPACE`; the hardness half is the
reduction above, run at the doubled universe so that the machine always has two
elements to write bits with. -/
theorem dwideAcceptSpace_EXPSPACE_complete : EXPSPACE.Complete DWideAcceptSpace :=
  ⟨dwideAcceptSpace_mem_EXPSPACE, dwideAcceptSpace_EXPSPACE_hard⟩

/-- **Acceptance in bounded space on a wide machine is EXPSPACE-hard**: hardness
travels forward along the reduction that adds the determinism promise. -/
theorem wideAcceptSpace_EXPSPACE_hard : EXPSPACE.Hard WideAcceptSpace :=
  EXPSPACE.hard_of_foReduction dwideAcceptSpace_fo_reduction_wideAcceptSpace
    dwideAcceptSpace_EXPSPACE_hard

/-- **Acceptance in bounded space on a wide machine is EXPSPACE-complete.** -/
theorem wideAcceptSpace_EXPSPACE_complete : EXPSPACE.Complete WideAcceptSpace :=
  ⟨wideAcceptSpace_mem_EXPSPACE, wideAcceptSpace_EXPSPACE_hard⟩

end Umbrella

end Lax822549Proofs.DescriptiveComplexity


