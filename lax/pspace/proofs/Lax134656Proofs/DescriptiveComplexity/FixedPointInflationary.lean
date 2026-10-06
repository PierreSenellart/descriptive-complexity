/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.FixedPointStep
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

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656Proofs.DescriptiveComplexity.IFPDefinable
end Lax134656Proofs.DescriptiveComplexity.IFPDefinable

namespace Lax134656Proofs.DescriptiveComplexity.IFPDefinableFree
end Lax134656Proofs.DescriptiveComplexity.IFPDefinableFree

namespace Lax134656Proofs.DescriptiveComplexity.LFPDef
end Lax134656Proofs.DescriptiveComplexity.LFPDef

namespace Lax134656Proofs.DescriptiveComplexity.LFPDefinable
end Lax134656Proofs.DescriptiveComplexity.LFPDefinable

namespace Lax134656Proofs.DescriptiveComplexity.StepDef
end Lax134656Proofs.DescriptiveComplexity.StepDef

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax134656Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (IFPDefinableFree)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives LFPDef LFPDefinable lfpAssign)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable StepDef)
end Lax134656Proofs.DescriptiveComplexity

/-!
# FO(IFP): first-order logic with an inflationary fixed point

The inflationary fixed-point logic ([Gurevich–Shelah
1986][gurevich1986fixed]; [Abiteboul–Vianu 1989][abiteboul1989fixpoint];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 7): iterate the step
formulas of a `DescriptiveComplexity.StepDef` *inflationarily* – each stage
accumulates what the step formulas derive on top of the previous stage – and
read the output sentence at the limit. No positivity is required of the step
formulas: inflation makes the iteration monotone whatever they are, which is
the whole point of the logic.

Two definability notions result, and keeping them distinct is the entire
subject of the Abiteboul–Vianu theorem:

* `DescriptiveComplexity.IFPDefinableFree` – over the bare vocabulary, on
  unordered structures;
* `DescriptiveComplexity.IFPDefinable` – over the vocabulary expanded by an
  order, required for every linear order on the universe, the problem itself
  never seeing it. This is the setting of the capture theorem
  FO(≤, IFP) = PTIME (`DescriptiveComplexity.FixedPointInflationaryLFP`).

For SO(TC) the corresponding two notions coincide
(`DescriptiveComplexity.sotcDefinable_iff_free`): a walk can guess an order
into its state. Here they must *not* be conflated – an inflationary induction
cannot manufacture an order (its stages are isomorphism-invariant, so on a
bare set of `n` elements nothing asymmetric is ever derived), and the gap
between the two notions is precisely what makes the unordered
Abiteboul–Vianu theorem (`DescriptiveComplexity.AbiteboulVianu`) a theorem
about `P = PSPACE` rather than a triviality.

## Relation to FO(LFP), and why Gurevich–Shelah is not needed

`DescriptiveComplexity.LFPDefinable.ifpDefinable` embeds FO(LFP) into ordered
FO(IFP): the rules of a Horn program, read as one simultaneous step
(`DescriptiveComplexity.hornStepF`), form a `StepDef` whose inflationary
stages are exactly the derivation stages `DescriptiveComplexity.derivesIn`
(`DescriptiveComplexity.inflStage_toStepDef`). The converse translation –
FO(≤, IFP) back into FO(LFP), hence the capture of PTIME – is
`DescriptiveComplexity.FixedPointInflationaryLFP`.

This library states the Abiteboul–Vianu theorem for IFP versus PFP, as in
Abiteboul and Vianu's original form. The classical statement for *least*
fixed points on unordered structures needs Gurevich–Shelah (order-free
LFP = IFP, by stage comparison) on top; phrasing the theorem with IFP makes
that machinery unnecessary, a design decision, not an omission.

## Closure properties

FO(IFP) definability is closed under complement by construction
(`DescriptiveComplexity.IFPDefinable.compl` – negate the output), and under
(ordered) first-order reductions
(`DescriptiveComplexity.IFPDefinableFree.of_foReduction`,
`DescriptiveComplexity.IFPDefinable.of_orderedReduction`): the stages commute
with the pullback of the block (`DescriptiveComplexity.StepDef.inflStage_pull`)
and the output sentence pulls back through the extended interpretation,
exactly as for FO(LFP). The notion is class-worthy in the sense of
`DescriptiveComplexity.ComplexityClass`.
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

/-! ### The value of an inflationary definition -/

/-- The value of an inflationary definition is isomorphism-invariant. -/
theorem ifpHolds_equiv (d : Lax535992.InflationaryFixedPoint.StepDef L) {M N : Type} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) : d.IFPHolds M ↔ d.IFPHolds N := by
  rw [Lax535992.InflationaryFixedPoint.StepDef.IFPHolds, Lax535992.InflationaryFixedPoint.StepDef.IFPHolds, d.inflLimit_map e]
  exact realize_sentence_of_equiv (d.B.extendEquiv' (L' := L) e (d.inflLimit M)) d.out

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (ifpHolds_equiv)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

end StepDef

/-! ### Definability, ordered and order-free -/

/-! ### Closure under reductions -/

section Closure

end Closure

/-! ### Horn rules as one simultaneous inflationary step

The rules of an FO(LFP) definition, read as a single simultaneous step: the
step formula of the variable `i` says that some rule with head `i` fires –
its guard holds and its body atoms are in the current stage – with the head's
arguments instantiated at the free variables. Iterated inflationarily, the
stages are exactly the derivation stages `DescriptiveComplexity.derivesIn`,
so the limit is the least fixed point and FO(LFP) embeds into FO(≤, IFP)
(`DescriptiveComplexity.LFPDefinable.ifpDefinable`). The step formulas
produced here are *positive* in the block – inflation just does not care. -/

section Horn

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-- The relation symbol of a block variable, in the expanded vocabulary
`L.sum B.lang` (the generic-`L` sibling of
`DescriptiveComplexity.varOutSym`). -/
abbrev varInSym (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) (i : B.ι) :
    (L.sum B.lang).Relations (B.arity i) :=
  Sum.inr (varSym B i)

/-- A second-order body atom, as a formula over the expanded vocabulary; its
arguments are read from the rule-variable component. -/
noncomputable def bodyAtomF (b : Lax485149.SecondOrderAtoms.SOAtom B k) {n : ℕ} :
    (L.sum B.lang).Formula (Fin n ⊕ Fin k) :=
  Relations.formula (varInSym L B b.idx) fun j => Term.var (Sum.inr (b.args j))

/-- A guard, transported to the expanded vocabulary, over head-argument and
rule variables. -/
noncomputable def guardStepF (φ : L.Formula (Fin k)) {n : ℕ} :
    (L.sum B.lang).Formula (Fin n ⊕ Fin k) :=
  (LHom.sumInl.onFormula φ).relabel Sum.inr

open Classical in
/-- The contribution of one rule to the step formula of the variable `i`:
the rule's head is about `i`, its arguments are the free variables, its guard
holds, and its body atoms are in the current stage. -/
noncomputable def ruleStepF (c : Lax535992.HornFragment.HornClause L B k) (i : B.ι) :
    (L.sum B.lang).Formula (Fin (B.arity i) ⊕ Fin k) :=
  c.head.elim ⊥ fun a =>
    if h : a.idx = i then
      (Formula.iInf fun j : Fin (B.arity i) =>
        Term.equal (Term.var (Sum.inl j))
          (Term.var (Sum.inr (a.args (Fin.cast (congrArg B.arity h.symm) j))))) ⊓
        guardStepF c.guard ⊓ listInf (c.body.map (bodyAtomF (n := B.arity i)))
    else ⊥

/-- The step formula of the variable `i` induced by a list of rules: some
rule with head `i` fires, for some values of the rule variables. -/
noncomputable def hornStepF (rules : List (Lax535992.HornFragment.HornClause L B k)) (i : B.ι) :
    (L.sum B.lang).Formula (Fin (B.arity i)) :=
  Formula.iExs (Fin k) (listSup (rules.map fun c => ruleStepF c i))

section Realize

variable {A : Type} [L.Structure A] (ρ : B.Assignment A)

theorem realize_bodyAtomF (b : Lax485149.SecondOrderAtoms.SOAtom B k) {n : ℕ} (w : Fin n ⊕ Fin k → A) :
    (@Formula.Realize _ A (B.structure₁ (L := L) ρ) _ (bodyAtomF b) w) ↔
      b.Holds ρ fun q => w (Sum.inr q) := by
  let := B.structure₁ (L := L) ρ
  rw [bodyAtomF, Formula.realize_rel]
  exact Iff.rfl

theorem realize_guardStepF (φ : L.Formula (Fin k)) {n : ℕ} (w : Fin n ⊕ Fin k → A) :
    (@Formula.Realize _ A (B.structure₁ (L := L) ρ) _ (guardStepF (B := B) φ) w) ↔
      φ.Realize fun q => w (Sum.inr q) := by
  let := B.structure₁ (L := L) ρ
  rw [guardStepF, Formula.realize_relabel, LHom.realize_onFormula]
  rfl

/-- **The step formula induced by a list of rules realizes as one round of
rule application** (`DescriptiveComplexity.stepDerives`). -/
theorem realize_hornStepF (rules : List (Lax535992.HornFragment.HornClause L B k)) (i : B.ι)
    (x : Fin (B.arity i) → A) :
    (@Formula.Realize _ A (B.structure₁ (L := L) ρ) _ (hornStepF rules i) x) ↔
      stepDerives rules (fun q => ρ q.1 q.2) (⟨i, x⟩ : BAtom B A) := by
  classical
  let := B.structure₁ (L := L) ρ
  rw [hornStepF, Formula.realize_iExs]
  constructor
  · rintro ⟨v, hv⟩
    rw [realize_listSup] at hv
    obtain ⟨ψ, hψmem, hψ⟩ := hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hψmem
    cases hh : c.head with
    | none =>
      rw [ruleStepF, hh, Option.elim_none, Formula.realize_bot] at hψ
      exact hψ.elim
    | some a =>
      rw [ruleStepF, hh, Option.elim_some] at hψ
      by_cases hidx : a.idx = i
      · rw [dif_pos hidx] at hψ
        rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_iInf] at hψ
        obtain ⟨⟨heqs, hguard⟩, hbody⟩ := hψ
        subst hidx
        refine ⟨c, hc, a, hh, v, ?_, ?_, ?_⟩
        · refine congrArg (Sigma.mk a.idx) (funext fun j => ?_)
          have hj := heqs j
          rw [Formula.realize_equal] at hj
          simpa using hj
        · exact (realize_guardStepF ρ c.guard _).mp hguard
        · intro b hb
          rw [realize_listInf] at hbody
          exact (realize_bodyAtomF ρ b _).mp
            (hbody _ (List.mem_map_of_mem hb))
      · rw [dif_neg hidx, Formula.realize_bot] at hψ
        exact hψ.elim
  · rintro ⟨c, hc, a, hh, v, heq, hguard, hbody⟩
    refine ⟨v, ?_⟩
    rw [realize_listSup]
    refine ⟨ruleStepF c i, List.mem_map_of_mem hc, ?_⟩
    have hidx : i = a.idx := congrArg Sigma.fst heq
    subst hidx
    injection heq with _ hargs
    rw [ruleStepF, hh, Option.elim_some, dif_pos rfl]
    rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_iInf]
    refine ⟨⟨fun j => ?_, ?_⟩, ?_⟩
    · rw [Formula.realize_equal]
      simpa using congrFun hargs j
    · exact (realize_guardStepF ρ c.guard _).mpr hguard
    · rw [realize_listInf]
      rintro ψ hψ
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hψ
      exact (realize_bodyAtomF ρ b _).mpr (hbody b hb)

end Realize

end Horn

/-! ### FO(LFP) embeds into FO(≤, IFP) -/

section OfLFP

variable {L : Language.{0, 0}}

/-- The simultaneous induction induced by an FO(LFP) definition: same block,
the rules read as one simultaneous step, same output. -/
noncomputable def LFPDef.toStepDef (d : Lax535992.LeastFixedPoint.LFPDef L) : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order) where
  B := d.B
  step := fun i => hornStepF d.rules i
  out := d.out

end OfLFP

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.LeastFixedPoint.LFPDef

export Lax134656Proofs.DescriptiveComplexity.LFPDef (toStepDef)

end Lax535992.LeastFixedPoint.LFPDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section OfLFP

variable {L : Language.{0, 0}}

/-- The inflationary stages of the induced induction are the derivation
stages of the rules. -/
theorem inflStage_toStepDef (d : Lax535992.LeastFixedPoint.LFPDef L) (A : Type) [L.Structure A] [LinearOrder A]
    (n : ℕ) :
    d.toStepDef.inflStage A n =
      fun i x => derivesIn d.rules n (⟨i, x⟩ : BAtom d.B A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i x
    rw [d.toStepDef.inflStage_succ]
    refine propext (or_congr (iff_of_eq (congrFun (congrFun ih i) x)) ?_)
    rw [ih]
    exact realize_hornStepF (fun i x => derivesIn d.rules n ⟨i, x⟩) d.rules i x

/-- The value of the induced inflationary iteration is the least fixed point
of the rules. -/
theorem inflLimit_toStepDef (d : Lax535992.LeastFixedPoint.LFPDef L) (A : Type) [L.Structure A] [LinearOrder A] :
    d.toStepDef.inflLimit A = Lax535992.LeastFixedPoint.lfpAssign d.rules := by
  funext i x
  refine propext ?_
  change (∃ n, d.toStepDef.inflStage A n i x) ↔ Lax535992.LeastFixedPoint.Derives d.rules ⟨i, x⟩
  rw [derives_iff_derivesIn]
  exact exists_congr fun n => iff_of_eq (congrFun (congrFun (inflStage_toStepDef d A n) i) x)

/-- **Every FO(LFP) definition is an FO(≤, IFP) definition**: read the rules
as one simultaneous step; inflation iterates them to their least fixed point,
and the output survives unchanged. (The converse, closing the circle back
into FO(LFP), is `DescriptiveComplexity.FixedPointInflationaryLFP`.) -/
theorem LFPDefinable.ifpDefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax535992.LeastFixedPoint.LFPDefinable P) :
    Lax535992.InflationaryFixedPoint.IFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.toStepDef, ?_⟩
  intro A _ _ _ _
  refine (hd A).trans ?_
  rw [Lax535992.LeastFixedPoint.LFPDef.Holds, Lax535992.InflationaryFixedPoint.StepDef.IFPHolds, inflLimit_toStepDef]
  exact Iff.rfl

end OfLFP

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.LeastFixedPoint.LFPDefinable

export Lax134656Proofs.DescriptiveComplexity.LFPDefinable (ifpDefinable)

end Lax535992.LeastFixedPoint.LFPDefinable

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section OfLFP

variable {L : Language.{0, 0}}

end OfLFP

end Lax134656Proofs.DescriptiveComplexity


