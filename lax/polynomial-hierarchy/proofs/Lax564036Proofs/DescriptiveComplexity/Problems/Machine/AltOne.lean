/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.AltDefs
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine
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

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMAcc ATMBlk atmData)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Machines (TMAcc tmData)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax564036.AlternatingMachines (atmAcc atmBlank atmBlk atmDst atmInp atmLe atmPosn atmRead atmRight atmSrc atmStart atmTr atmWrite turingAlt)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing)
end FirstOrder.Language

/-!
# The alternating bridge at one block: `ATMAccept 1 true` is NP-complete

The base case of the machine bridge for the polynomial hierarchy, and the
sanity check on the alternating model: at `k = 1` the only block is `0`, its
polarity is the starting one, so for `start = true` no state is universal and
`DescriptiveComplexity.ATMData.AltAccepts` is
`DescriptiveComplexity.TMData.Accepts`
(`DescriptiveComplexity.ATMData.altAccepts_true_iff_accepts`). The alternating
problem is therefore the same problem as `DescriptiveComplexity.NTMAccept`, up
to the mark – and *up to the mark* is exactly what a reduction is for.

Both directions are identity interpretations – one dimension, one tag – in the
style of `DescriptiveComplexity.DetToNondet.detInterp`:

* `DescriptiveComplexity.MarkOne.markInterp` copies a machine and marks *every*
  element as a state of block `0`, so the promise
  `DescriptiveComplexity.ATMData.BlocksWellFormed` holds in the image by
  construction;
* `DescriptiveComplexity.ForgetOne.forgetInterp` copies an alternating machine
  and forgets the mark, keeping the accepting states only when the promise
  holds in the source – the guard trick again, so that an instance failing the
  promise becomes a no-instance rather than a machine that might accept.

Together they make `ATMAccept 1 true` NP-complete: membership travels backwards
along `forgetInterp`, hardness forwards along `markInterp`. Nothing here is
specific to one block except the two `k = 1` facts of
`DescriptiveComplexity.Problems.Machine.AltDefs`; the general bridge replaces
them by the collapse lemmas of `DescriptiveComplexity.MachinesAltPlay`.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Marking a machine: `NTMAccept ≤ᶠᵒ ATMAccept 1 true` -/

namespace MarkOne

/-- **The identity interpretation that marks every element.** Every symbol of
the machine vocabulary is copied, and the single block mark holds of
everything, so the interpreted instance carries a well-formed block
structure. -/
noncomputable def markInterp : Lax904597.Interpretations.FOInterpretation Lax904597.Machines.turing (Lax564036.AlternatingMachines.turingAlt 1) Unit 1 where
  relFormula {n} R _ :=
    match n, R with
    | _, .base .posn => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmPosn (FirstOrder.Language.Term.var (0, 0))
    | _, .base .tr => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmTr (FirstOrder.Language.Term.var (0, 0))
    | _, .base .start => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmStart (FirstOrder.Language.Term.var (0, 0))
    | _, .base .acc => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmAcc (FirstOrder.Language.Term.var (0, 0))
    | _, .base .blank => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmBlank (FirstOrder.Language.Term.var (0, 0))
    | _, .base .right => FirstOrder.Language.Relations.formula₁ Lax904597.Machines.tmRight (FirstOrder.Language.Term.var (0, 0))
    | _, .base .le => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmLe (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .base .tsrc => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmSrc (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .base .tread => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmRead (FirstOrder.Language.Term.var (0, 0))
                             (FirstOrder.Language.Term.var (1, 0))
    | _, .base .tdst => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmDst (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .base .twrite => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmWrite (FirstOrder.Language.Term.var (0, 0))
                              (FirstOrder.Language.Term.var (1, 0))
    | _, .base .inp => FirstOrder.Language.Relations.formula₂ Lax904597.Machines.tmInp (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .blk _ => ⊤

section Reading

variable {A : Type} [Lax904597.Machines.turing.Structure A]

/-- The universe of the image is the universe of the source. -/
noncomputable abbrev toBase (x : markInterp.Map A) : A := markInterp.mapEquivSelf A x

/-- A copied unary symbol is read as its source. -/
private theorem rel₁_map (R : (Lax564036.AlternatingMachines.turingAlt 1).Relations 1)
    (R₀ : Lax904597.Machines.turing.Relations 1)
    (h : ∀ t, markInterp.relFormula R t = Relations.formula₁ R₀ (Term.var (0, 0)))
    (x : markInterp.Map A) : (RelMap R ![x] : Prop) ↔ RelMap R₀ ![toBase x] := by
  refine Iff.trans (FOInterpretation.relMap_map markInterp A R ![x]) ?_
  rw [h]
  simp only [Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- A copied binary symbol is read as its source. -/
private theorem rel₂_map (R : (Lax564036.AlternatingMachines.turingAlt 1).Relations 2)
    (R₀ : Lax904597.Machines.turing.Relations 2)
    (h : ∀ t, markInterp.relFormula R t =
      Relations.formula₂ R₀ (Term.var (0, 0)) (Term.var (1, 0)))
    (x y : markInterp.Map A) :
    (RelMap R ![x, y] : Prop) ↔ RelMap R₀ ![toBase x, toBase y] := by
  refine Iff.trans (FOInterpretation.relMap_map markInterp A R ![x, y]) ?_
  rw [h]
  simp only [Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

/-- **Every element of the image is a state of block `0`.** -/
theorem blk_map (x : markInterp.Map A) : Lax564036.AlternatingMachines.ATMBlk (k := 1) 0 x := by
  refine ⟨by omega, ?_⟩
  refine (FOInterpretation.relMap_map markInterp A (Lax564036.AlternatingMachines.atmBlk (0 : Fin 1)) ![x]).mpr ?_
  simp [markInterp]

/-- **A marked machine is the machine it was built from.** -/
theorem agree (A : Type) [Lax904597.Machines.turing.Structure A] :
    (Lax564036.AlternatingMachines.atmData 1 (markInterp.Map A)).toTMData.Agree (markInterp.mapEquivSelf A) (Lax904597.Machines.tmData A) where
  posn := rel₁_map Lax564036.AlternatingMachines.atmPosn Lax904597.Machines.tmPosn (fun _ => rfl)
  le := rel₂_map Lax564036.AlternatingMachines.atmLe Lax904597.Machines.tmLe (fun _ => rfl)
  tr := rel₁_map Lax564036.AlternatingMachines.atmTr Lax904597.Machines.tmTr (fun _ => rfl)
  start := rel₁_map Lax564036.AlternatingMachines.atmStart Lax904597.Machines.tmStart (fun _ => rfl)
  acc := rel₁_map Lax564036.AlternatingMachines.atmAcc Lax904597.Machines.tmAcc (fun _ => rfl)
  blank := rel₁_map Lax564036.AlternatingMachines.atmBlank Lax904597.Machines.tmBlank (fun _ => rfl)
  right := rel₁_map Lax564036.AlternatingMachines.atmRight Lax904597.Machines.tmRight (fun _ => rfl)
  src := rel₂_map Lax564036.AlternatingMachines.atmSrc Lax904597.Machines.tmSrc (fun _ => rfl)
  read := rel₂_map Lax564036.AlternatingMachines.atmRead Lax904597.Machines.tmRead (fun _ => rfl)
  dst := rel₂_map Lax564036.AlternatingMachines.atmDst Lax904597.Machines.tmDst (fun _ => rfl)
  write := rel₂_map Lax564036.AlternatingMachines.atmWrite Lax904597.Machines.tmWrite (fun _ => rfl)
  inp := rel₂_map Lax564036.AlternatingMachines.atmInp Lax904597.Machines.tmInp (fun _ => rfl)

end Reading

/-- **The reduction is correct**: marking every element changes nothing, since
at one existential block the alternating semantics is the nondeterministic
one. -/
theorem correct (A : Type) [Lax904597.Machines.turing.Structure A] [Finite A] [Nonempty A] :
    NTMAccept A ↔ ATMAccept 1 true (markInterp.Map A) := by
  have : Finite (markInterp.Map A) := markInterp.map_finite A
  have h := agree A
  have hbwf : (Lax564036.AlternatingMachines.atmData 1 (markInterp.Map A)).BlocksWellFormed 1 :=
    blocksWellFormed_one_iff.mpr blk_map
  constructor
  · rintro ⟨hwf, hacc⟩
    have hwf' := h.wellFormed.mpr hwf
    exact ⟨hwf', hbwf,
      (ATMData.altAccepts_true_iff_accepts not_isUniv_one hwf'.2.1).mpr (h.accepts.mpr hacc)⟩
  · rintro ⟨hwf', -, halt⟩
    exact ⟨h.wellFormed.mp hwf',
      h.accepts.mp ((ATMData.altAccepts_true_iff_accepts not_isUniv_one hwf'.2.1).mp halt)⟩

end MarkOne

/-- **Machine acceptance reduces to alternating acceptance at one block**: mark
every element as a state of the single block. -/
noncomputable def ntmAccept_fo_reduction_atmAccept_one :
    NTMAccept ≤ᶠᵒ ATMAccept 1 true where
  Tag := Unit
  dim := 1
  toInterpretation := MarkOne.markInterp
  correct := MarkOne.correct

/-! ### Forgetting the mark: `ATMAccept 1 true ≤ᶠᵒ NTMAccept` -/

namespace ForgetOne

/-- The promise of `DescriptiveComplexity.ATMAccept` at one block – every
element is marked – as a first-order formula whose free variables are unused:
the guard the image puts on its accepting states. -/
noncomputable def markedG (γ : Type) : (Lax564036.AlternatingMachines.turingAlt 1).Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.Relations.formula₁ (Lax564036.AlternatingMachines.atmBlk (0 : Fin 1)) (FirstOrder.Language.Term.var (Sum.inr 0)))

/-- **The identity interpretation that forgets the mark, with a guarded
accepting predicate.** -/
noncomputable def forgetInterp :
    Lax904597.Interpretations.FOInterpretation (Lax564036.AlternatingMachines.turingAlt 1) Lax904597.Machines.turing Unit 1 where
  relFormula {n} R _ :=
    match n, R with
    | _, .posn => FirstOrder.Language.Relations.formula₁ Lax564036.AlternatingMachines.atmPosn (FirstOrder.Language.Term.var (0, 0))
    | _, .tr => FirstOrder.Language.Relations.formula₁ Lax564036.AlternatingMachines.atmTr (FirstOrder.Language.Term.var (0, 0))
    | _, .start => FirstOrder.Language.Relations.formula₁ Lax564036.AlternatingMachines.atmStart (FirstOrder.Language.Term.var (0, 0))
    | _, .acc => (markedG _) ⊓ FirstOrder.Language.Relations.formula₁ Lax564036.AlternatingMachines.atmAcc (FirstOrder.Language.Term.var (0, 0))
    | _, .blank => FirstOrder.Language.Relations.formula₁ Lax564036.AlternatingMachines.atmBlank (FirstOrder.Language.Term.var (0, 0))
    | _, .right => FirstOrder.Language.Relations.formula₁ Lax564036.AlternatingMachines.atmRight (FirstOrder.Language.Term.var (0, 0))
    | _, .le => FirstOrder.Language.Relations.formula₂ Lax564036.AlternatingMachines.atmLe (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .tsrc => FirstOrder.Language.Relations.formula₂ Lax564036.AlternatingMachines.atmSrc (FirstOrder.Language.Term.var (0, 0))
                      (FirstOrder.Language.Term.var (1, 0))
    | _, .tread => FirstOrder.Language.Relations.formula₂ Lax564036.AlternatingMachines.atmRead (FirstOrder.Language.Term.var (0, 0))
                       (FirstOrder.Language.Term.var (1, 0))
    | _, .tdst => FirstOrder.Language.Relations.formula₂ Lax564036.AlternatingMachines.atmDst (FirstOrder.Language.Term.var (0, 0))
                      (FirstOrder.Language.Term.var (1, 0))
    | _, .twrite => FirstOrder.Language.Relations.formula₂ Lax564036.AlternatingMachines.atmWrite (FirstOrder.Language.Term.var (0, 0))
                        (FirstOrder.Language.Term.var (1, 0))
    | _, .inp => FirstOrder.Language.Relations.formula₂ Lax564036.AlternatingMachines.atmInp (FirstOrder.Language.Term.var (0, 0))
                     (FirstOrder.Language.Term.var (1, 0))

section Reading

variable {A : Type} [(Lax564036.AlternatingMachines.turingAlt 1).Structure A] {γ : Type}

@[simp]
theorem markedG_realize (v : γ → A) :
    (markedG γ).Realize v ↔ ∀ q : A, Lax564036.AlternatingMachines.ATMBlk (k := 1) 0 q := by
  rw [markedG]
  simp only [Formula.realize_iAlls, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  constructor
  · intro h q
    exact ⟨by omega, h fun _ => q⟩
  · intro h i
    exact (h (i 0)).2

/-- The universe of the image is the universe of the source. -/
noncomputable abbrev toBase (x : forgetInterp.Map A) : A := forgetInterp.mapEquivSelf A x

/-- A copied unary symbol is read as its source. -/
private theorem rel₁_map (R : Lax904597.Machines.turing.Relations 1)
    (R₀ : (Lax564036.AlternatingMachines.turingAlt 1).Relations 1)
    (h : ∀ t, forgetInterp.relFormula R t = Relations.formula₁ R₀ (Term.var (0, 0)))
    (x : forgetInterp.Map A) : (RelMap R ![x] : Prop) ↔ RelMap R₀ ![toBase x] := by
  refine Iff.trans (FOInterpretation.relMap_map forgetInterp A R ![x]) ?_
  rw [h]
  simp only [Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- A copied binary symbol is read as its source. -/
private theorem rel₂_map (R : Lax904597.Machines.turing.Relations 2)
    (R₀ : (Lax564036.AlternatingMachines.turingAlt 1).Relations 2)
    (h : ∀ t, forgetInterp.relFormula R t =
      Relations.formula₂ R₀ (Term.var (0, 0)) (Term.var (1, 0)))
    (x y : forgetInterp.Map A) :
    (RelMap R ![x, y] : Prop) ↔ RelMap R₀ ![toBase x, toBase y] := by
  refine Iff.trans (FOInterpretation.relMap_map forgetInterp A R ![x, y]) ?_
  rw [h]
  simp only [Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

/-- **The accepting states of the image are guarded**: an element is accepting
there exactly when the source carries its promise and it is accepting in the
source. -/
@[simp]
theorem acc_map (x : forgetInterp.Map A) :
    Lax904597.Machines.TMAcc x ↔ ((∀ q : A, Lax564036.AlternatingMachines.ATMBlk (k := 1) 0 q) ∧ Lax564036.AlternatingMachines.ATMAcc (k := 1) (toBase x)) := by
  refine Iff.trans (FOInterpretation.relMap_map forgetInterp A Lax904597.Machines.tmAcc ![x]) ?_
  simp only [forgetInterp, Formula.realize_inf, markedG_realize, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

/-- **An instance carrying its promise is copied verbatim.** -/
theorem agree_of_marked (hm : ∀ q : A, Lax564036.AlternatingMachines.ATMBlk (k := 1) 0 q) :
    (Lax904597.Machines.tmData (forgetInterp.Map A)).Agree (forgetInterp.mapEquivSelf A)
      (Lax564036.AlternatingMachines.atmData 1 A).toTMData where
  posn := rel₁_map Lax904597.Machines.tmPosn Lax564036.AlternatingMachines.atmPosn (fun _ => rfl)
  le := rel₂_map Lax904597.Machines.tmLe Lax564036.AlternatingMachines.atmLe (fun _ => rfl)
  tr := rel₁_map Lax904597.Machines.tmTr Lax564036.AlternatingMachines.atmTr (fun _ => rfl)
  start := rel₁_map Lax904597.Machines.tmStart Lax564036.AlternatingMachines.atmStart (fun _ => rfl)
  acc x := (acc_map x).trans (and_iff_right hm)
  blank := rel₁_map Lax904597.Machines.tmBlank Lax564036.AlternatingMachines.atmBlank (fun _ => rfl)
  right := rel₁_map Lax904597.Machines.tmRight Lax564036.AlternatingMachines.atmRight (fun _ => rfl)
  src := rel₂_map Lax904597.Machines.tmSrc Lax564036.AlternatingMachines.atmSrc (fun _ => rfl)
  read := rel₂_map Lax904597.Machines.tmRead Lax564036.AlternatingMachines.atmRead (fun _ => rfl)
  dst := rel₂_map Lax904597.Machines.tmDst Lax564036.AlternatingMachines.atmDst (fun _ => rfl)
  write := rel₂_map Lax904597.Machines.tmWrite Lax564036.AlternatingMachines.atmWrite (fun _ => rfl)
  inp := rel₂_map Lax904597.Machines.tmInp Lax564036.AlternatingMachines.atmInp (fun _ => rfl)

/-- **An instance failing its promise has no accepting state in the image.** -/
theorem not_accepts_of_not_marked (hm : ¬∀ q : A, Lax564036.AlternatingMachines.ATMBlk (k := 1) 0 q) :
    ¬(Lax904597.Machines.tmData (forgetInterp.Map A)).Accepts := by
  rintro ⟨-, c, -, -, -, -, hacc⟩
  exact hm ((acc_map c.state).mp hacc).1

end Reading

/-- **The reduction is correct**: forgetting the mark is harmless on instances
that carry the promise, and the guard turns the others into no-instances. -/
theorem correct (A : Type) [(Lax564036.AlternatingMachines.turingAlt 1).Structure A] [Finite A] [Nonempty A] :
    ATMAccept 1 true A ↔ NTMAccept (forgetInterp.Map A) := by
  have : Finite (forgetInterp.Map A) := forgetInterp.map_finite A
  by_cases hm : ∀ q : A, Lax564036.AlternatingMachines.ATMBlk (k := 1) 0 q
  · have h := agree_of_marked hm
    have hbwf : (Lax564036.AlternatingMachines.atmData 1 A).BlocksWellFormed 1 := blocksWellFormed_one_iff.mpr hm
    constructor
    · rintro ⟨hwf, -, halt⟩
      exact ⟨h.wellFormed.mpr hwf,
        h.accepts.mpr ((ATMData.altAccepts_true_iff_accepts not_isUniv_one hwf.2.1).mp halt)⟩
    · rintro ⟨hwf, hacc⟩
      have hwf' := h.wellFormed.mp hwf
      exact ⟨hwf', hbwf,
        (ATMData.altAccepts_true_iff_accepts not_isUniv_one hwf'.2.1).mpr (h.accepts.mp hacc)⟩
  · constructor
    · rintro ⟨-, hbwf, -⟩
      exact absurd (blocksWellFormed_one_iff.mp hbwf) hm
    · rintro ⟨-, hacc⟩
      exact absurd hacc (not_accepts_of_not_marked hm)

end ForgetOne

/-- **Alternating acceptance at one block reduces to machine acceptance**:
forget the mark, keeping the accepting states only when the promise holds. -/
noncomputable def atmAccept_one_fo_reduction_ntmAccept :
    ATMAccept 1 true ≤ᶠᵒ NTMAccept where
  Tag := Unit
  dim := 1
  toInterpretation := ForgetOne.forgetInterp
  correct := ForgetOne.correct

/-! ### The bridge at one block -/

/-- **Alternating acceptance at one existential block is in NP.** -/
theorem atmAccept_one_mem_NP : ATMAccept 1 true ∈ NP :=
  NP.mem_of_foReduction atmAccept_one_fo_reduction_ntmAccept ntmAccept_mem_NP

/-- **Alternating acceptance at one existential block is NP-hard.** -/
theorem atmAccept_one_NP_hard : NP.Hard (ATMAccept 1 true) :=
  NP.hard_of_foReduction ntmAccept_fo_reduction_atmAccept_one ntmAccept_NP_hard

/-- **The bridge at one block**: `ATMAccept 1 true` is NP-complete, the level-1
case of the machine bridge for the polynomial hierarchy. -/
theorem atmAccept_one_NP_complete : NP.Complete (ATMAccept 1 true) :=
  ⟨atmAccept_one_mem_NP, atmAccept_one_NP_hard⟩

end Lax564036Proofs.DescriptiveComplexity


