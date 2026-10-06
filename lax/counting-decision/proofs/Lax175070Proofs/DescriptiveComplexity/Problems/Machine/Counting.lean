/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Problems.Machine.Membership
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.CountingHardness
import Lax175070.CountDefinability
import Lax175070.SelectedSat
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity.Config
end Lax175070Proofs.DescriptiveComplexity.Config

namespace Lax175070Proofs.DescriptiveComplexity.TMData
end Lax175070Proofs.DescriptiveComplexity.TMData

namespace Lax175070Proofs.DescriptiveComplexity.TMData.Agree
end Lax175070Proofs.DescriptiveComplexity.TMData.Agree

namespace Lax175070Proofs.DescriptiveComplexity.TMData.IsHaltWalk
end Lax175070Proofs.DescriptiveComplexity.TMData.IsHaltWalk

namespace Lax175070Proofs.DescriptiveComplexity.TMData.RelHaltWalk
end Lax175070Proofs.DescriptiveComplexity.TMData.RelHaltWalk

namespace Lax175070Proofs.DescriptiveComplexity.TMData.RelWalk
end Lax175070Proofs.DescriptiveComplexity.TMData.RelWalk

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingRuns.TMData
end Lax366625.CountingRuns.TMData

namespace Lax366625.MachineNumbers
end Lax366625.MachineNumbers

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Machines (Config MinPos SuccPos TMAcc TMData TMLe TMPosn tmData)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.MachineNumbers (MaxPos)
end Lax175070Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Machines (turing)
end FirstOrder.Language

namespace Lax904597.Machines.TMData
export Lax366625.CountingRuns.TMData (IsHaltWalk IsWalk)
end Lax904597.Machines.TMData

/-!
# Counting the accepting runs of a machine

The counting version of `DescriptiveComplexity.NTMAccept`, on the same vocabulary: the
number of accepting runs of the machine an instance describes – the quantity
`#P` was introduced to measure ([Valiant 1979][valiant1979complexity]).

A run is counted through its layout along the positions, as in
`DescriptiveComplexity.TMData.IsWalk`, with two more requirements that make the layout
of a run unique (`DescriptiveComplexity.TMData.IsHaltWalk`):

* an accepting configuration is *repeated*, never left: a run is counted up to
  the first accepting configuration it reaches, as for a machine whose
  accepting states are halting;
* times that are not positions carry the initial configuration: the clock of a
  run is the positions, and a walk says something only there.

`DescriptiveComplexity.SharpNTMAccept` is the bundled counting problem; its support is
machine acceptance (`DescriptiveComplexity.sharpNtmAccept_support_iff`), and it
belongs to `#P` (`DescriptiveComplexity.sharpNtmAccept_mem_sharpP`): the tableau of
Fagin's argument is functionally determined by the run, so its guesses are the
runs, bijectively (`DescriptiveComplexity.haltWalkEquiv`). With the counting
Cook–Levin theorem this gives its textbook form,
`DescriptiveComplexity.sharpNtmAccept_reduces_to_sharpSat`: counting the accepting runs
of a machine reduces parsimoniously to counting the models of a CNF formula.

The converse reduction is in
`DescriptiveComplexity.Problems.Machine.CountingHardness`, which makes this problem
parsimoniously `#P`-complete and `#P` the class of the problems reducing to
it.
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

/-- **A run to an accepting configuration is a halting walk**, for a machine
whose accepting configurations have no successor: the run lays out along the
positions and ends on the configuration it reached. -/
theorem exists_haltWalk_of_stepsIn [Finite A] (hwf : M.WellFormed) {c₀ c : Lax904597.Machines.Config A} {n : ℕ}
    (hinit : M.IsInit c₀) (hlt : n < Nat.card {p : A // M.Posn p}) (hrun : M.StepsIn n c₀ c)
    (hacc : M.Acc c.state) (hhalt : ∀ d e : Lax904597.Machines.Config A, M.Acc d.state → ¬ M.Step d e) :
    ∃ conf : A → Lax904597.Machines.Config A, M.IsHaltWalk conf ∧ ∀ p, Lax366625.MachineNumbers.MaxPos M.Le M.Posn p → conf p = c := by
  obtain ⟨hlin, -, -⟩ := hwf
  classical
  obtain ⟨f, hf0, hfn, hfs⟩ := exists_run n c₀ c hrun
  have hposn : ∀ {p}, M.Posn p →
      (if M.Posn p then f (min (bitRank M.Le M.Posn p) n) else f 0) =
        f (min (bitRank M.Le M.Posn p) n) := fun hp => if_pos hp
  refine ⟨fun t => if M.Posn t then f (min (bitRank M.Le M.Posn t) n) else f 0,
    ⟨⟨fun p hp => ?_, fun p q hpq => ?_, fun p hp => ?_⟩, fun p q hpq hpa => ?_,
      fun t p₀ ht hp₀ => ?_⟩, fun p hp => ?_⟩
  · dsimp only
    rw [hposn hp.1, bitRank_eq_zero_of_minPos hlin hp, Nat.zero_min, hf0]
    exact hinit
  · have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    dsimp only
    rw [hposn hpq.1, hposn hpq.2.1]
    rcases lt_or_ge (bitRank M.Le M.Posn p) n with hcase | hcase
    · refine Or.inl ?_
      rw [hrq, min_eq_left (by omega), min_eq_left (by omega)]
      exact hfs _ hcase
    · refine Or.inr ⟨?_, ?_⟩
      · rw [min_eq_right hcase, hfn]
        exact hacc
      · rw [hrq, min_eq_right (by omega), min_eq_right hcase]
  · have hmax : bitRank M.Le M.Posn p + 1 = Nat.card {x : A // M.Posn x} :=
      bitRank_maxPos hp
    dsimp only
    rw [hposn hp.1, min_eq_right (by omega), hfn]
    exact hacc
  · have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    dsimp only at hpa ⊢
    rw [hposn hpq.1] at hpa
    rw [hposn hpq.1, hposn hpq.2.1]
    rcases lt_or_ge (bitRank M.Le M.Posn p) n with hcase | hcase
    · rw [min_eq_left (by omega)] at hpa
      exact absurd (hfs _ hcase) (hhalt _ _ hpa)
    · rw [hrq, min_eq_right (by omega), min_eq_right hcase]
  · dsimp only
    rw [if_neg ht, hposn hp₀.1, bitRank_eq_zero_of_minPos hlin hp₀, Nat.zero_min]
  · have hmax : bitRank M.Le M.Posn p + 1 = Nat.card {x : A // M.Posn x} :=
      bitRank_maxPos hp
    dsimp only
    rw [hposn hp.1, min_eq_right (by omega), hfn]

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax175070Proofs.DescriptiveComplexity.TMData (exists_haltWalk_of_stepsIn)

end Lax904597.Machines.TMData

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

/-! ### Halting walks of agreeing machines -/

section Agree

variable {B : Type} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Agreement of machines is symmetric. -/
theorem Agree.symm (h : Agree u N M) : Agree u.symm M N where
  posn a := by rw [h.posn, Equiv.apply_symm_apply]
  le a a' := by rw [h.le, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  tr a := by rw [h.tr, Equiv.apply_symm_apply]
  start a := by rw [h.start, Equiv.apply_symm_apply]
  acc a := by rw [h.acc, Equiv.apply_symm_apply]
  blank a := by rw [h.blank, Equiv.apply_symm_apply]
  right a := by rw [h.right, Equiv.apply_symm_apply]
  src a a' := by rw [h.src, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  read a a' := by rw [h.read, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  dst a a' := by rw [h.dst, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  write a a' := by rw [h.write, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  inp a a' := by rw [h.inp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Agree

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax175070Proofs.DescriptiveComplexity.TMData.Agree (symm)

end Lax904597.Machines.TMData.Agree

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Agree

variable {B : Type} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

omit M in
theorem _root_.Lax175070Proofs.DescriptiveComplexity.Config.map_symm_map (u : B ≃ A) (c : Lax904597.Machines.Config B) :
    (c.map u).map u.symm = c := by
  refine Lax904597.Machines.Config.ext ?_ ?_ (funext fun p => ?_) <;> simp [Config.map]

end Agree

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.Config

export Lax175070Proofs.DescriptiveComplexity.Config (map_symm_map)

end Lax904597.Machines.Config

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Agree

variable {B : Type} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- **Halting walks transport along an agreement.** -/
theorem Agree.isHaltWalk_map (h : Agree u N M) {conf : B → Lax904597.Machines.Config B}
    (hw : N.IsHaltWalk conf) : M.IsHaltWalk fun a => (conf (u.symm a)).map u := by
  have hmin : ∀ {a}, Lax904597.Machines.MinPos M.Le M.Posn a → Lax904597.Machines.MinPos N.Le N.Posn (u.symm a) := fun ha =>
    h.minPos.mpr (by rwa [Equiv.apply_symm_apply])
  have hsucc : ∀ {a a'}, Lax904597.Machines.SuccPos M.Le M.Posn a a' →
      Lax904597.Machines.SuccPos N.Le N.Posn (u.symm a) (u.symm a') := fun ha =>
    h.succPos.mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  obtain ⟨⟨hinit, hstep, hacc⟩, hhalt, hoff⟩ := hw
  refine ⟨⟨fun a ha => h.isInit.mp (hinit _ (hmin ha)), fun a a' hs => ?_, fun a ha => ?_⟩,
    fun a a' hs ha => ?_, fun a a₀ ha ha₀ => ?_⟩
  · rcases hstep _ _ (hsucc hs) with hst | ⟨hac, heq⟩
    · exact Or.inl (h.step.mp hst)
    · refine Or.inr ⟨(h.acc _).mp hac, ?_⟩
      dsimp only
      rw [heq]
  · refine (h.acc _).mp (hacc (u.symm a) ⟨(h.posn _).mpr ?_, fun q hq => (h.le _ _).mpr ?_⟩)
    · rw [Equiv.apply_symm_apply]
      exact ha.1
    · rw [Equiv.apply_symm_apply]
      exact ha.2 (u q) ((h.posn q).mp hq)
  · dsimp only
    rw [hhalt _ _ (hsucc hs) ((h.acc _).mpr ha)]
  · dsimp only
    rw [hoff (u.symm a) (u.symm a₀) (fun hp => ha ?_) (hmin ha₀)]
    have := (h.posn _).mp hp
    rwa [Equiv.apply_symm_apply] at this

end Agree

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax175070Proofs.DescriptiveComplexity.TMData.Agree (isHaltWalk_map)

end Lax904597.Machines.TMData.Agree

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Agree

variable {B : Type} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- **Agreeing machines have as many halting walks.** -/
theorem Agree.card_haltWalk (h : Agree u N M) :
    Nat.card {conf : B → Lax904597.Machines.Config B // N.IsHaltWalk conf} =
      Nat.card {conf : A → Lax904597.Machines.Config A // M.IsHaltWalk conf} :=
  Nat.card_congr
    { toFun := fun c => ⟨fun a => (c.1 (u.symm a)).map u, h.isHaltWalk_map c.2⟩
      invFun := fun c => ⟨fun b => (c.1 (u b)).map u.symm, h.symm.isHaltWalk_map c.2⟩
      left_inv := fun c => Subtype.ext (funext fun b => by
        change ((c.1 (u.symm (u b))).map u).map u.symm = c.1 b
        rw [Equiv.symm_apply_apply, Config.map_symm_map])
      right_inv := fun c => Subtype.ext (funext fun a => by
        change ((c.1 (u (u.symm a))).map u.symm).map u = c.1 a
        rw [Equiv.apply_symm_apply]
        exact Config.map_symm_map u.symm _) }

end Agree

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax175070Proofs.DescriptiveComplexity.TMData.Agree (card_haltWalk)

end Lax904597.Machines.TMData.Agree

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Agree

variable {B : Type} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

end Agree

/-! ### The relational form of a halting walk -/

section Relational

variable (M) (Q H : A → A → Prop) (T : A → A → A → Prop)

/-- The three relations describe the same configuration at `t'` as at `t`. -/
def RelSame (t t' : A) : Prop :=
  (∀ q, Q t' q ↔ Q t q) ∧ (∀ p, H t' p ↔ H t p) ∧ ∀ p a, T t' p a ↔ T t p a

end Relational

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax175070Proofs.DescriptiveComplexity.TMData (RelSame)

end Lax904597.Machines.TMData

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Relational

variable (M) (Q H : A → A → Prop) (T : A → A → A → Prop)

/-- **A halting walk, guessed as three relations.** -/
structure RelHaltWalk : Prop where
  /-- The relations are a walk. -/
  walk : M.RelWalk Q H T
  /-- An accepting configuration is repeated. -/
  halt : ∀ t t', Lax904597.Machines.SuccPos M.Le M.Posn t t' → (∀ q, Q t q → M.Acc q) → RelSame Q H T t t'
  /-- Times that are not positions carry the initial configuration. -/
  off : ∀ t t₀, ¬ M.Posn t → Lax904597.Machines.MinPos M.Le M.Posn t₀ → RelSame Q H T t₀ t

end Relational

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax175070Proofs.DescriptiveComplexity.TMData (RelHaltWalk)

end Lax904597.Machines.TMData

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Relational

variable (M) (Q H : A → A → Prop) (T : A → A → A → Prop)

end Relational

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.RelHaltWalk

export Lax175070Proofs.DescriptiveComplexity.TMData.RelHaltWalk (halt off walk)

end Lax904597.Machines.TMData.RelHaltWalk

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Relational

variable (M) (Q H : A → A → Prop) (T : A → A → A → Prop)

variable {M Q H T}

/-- Times at which the relations agree carry the same configuration. -/
theorem RelWalk.conf_eq_of_relSame (h : M.RelWalk Q H T) {t t' : A}
    (hs : RelSame Q H T t t') : h.conf t' = h.conf t := by
  obtain ⟨hq, hh, ht⟩ := hs
  refine Lax904597.Machines.Config.ext (h.quniq t _ _ ((hq _).mp (h.qex t').choose_spec) (h.qex t).choose_spec)
    (h.huniq t _ _ ((hh _).mp (h.hex t').choose_spec) (h.hex t).choose_spec)
    (funext fun p => ?_)
  exact h.tuniq t p _ _ ((ht p _).mp (h.tex t' p).choose_spec) (h.tex t p).choose_spec

end Relational

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.RelWalk

export Lax175070Proofs.DescriptiveComplexity.TMData.RelWalk (conf_eq_of_relSame)

end Lax904597.Machines.TMData.RelWalk

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Relational

variable (M) (Q H : A → A → Prop) (T : A → A → A → Prop)

variable {M Q H T}

/-- A relational halting walk is a halting walk, through the configurations it
describes. -/
theorem RelHaltWalk.isHaltWalk (h : M.RelHaltWalk Q H T) : M.IsHaltWalk h.walk.conf := by
  refine ⟨h.walk.isWalk, fun p q hpq hacc => ?_, fun t p₀ ht hp₀ => ?_⟩
  · refine h.walk.conf_eq_of_relSame (h.halt p q hpq fun q' hq' => ?_)
    rw [h.walk.quniq p q' _ hq' (h.walk.qex p).choose_spec]
    exact hacc
  · exact h.walk.conf_eq_of_relSame (h.off t p₀ ht hp₀)

end Relational

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.RelHaltWalk

export Lax175070Proofs.DescriptiveComplexity.TMData.RelHaltWalk (isHaltWalk)

end Lax904597.Machines.TMData.RelHaltWalk

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Relational

variable (M) (Q H : A → A → Prop) (T : A → A → A → Prop)

variable {M Q H T}

/-- A halting walk is a relational halting walk, through the graphs of its
configurations. -/
theorem IsHaltWalk.relHaltWalk {conf : A → Lax904597.Machines.Config A} (h : M.IsHaltWalk conf) :
    M.RelHaltWalk (fun t q => q = (conf t).state) (fun t p => p = (conf t).head)
      (fun t p a => a = (conf t).tape p) := by
  obtain ⟨hw, hhalt, hoff⟩ := h
  refine ⟨hw.relWalk, fun t t' htt' hacc => ?_, fun t t₀ ht ht₀ => ?_⟩
  · have heq := hhalt t t' htt' (hacc _ rfl)
    refine ⟨fun q => ?_, fun p => ?_, fun p a => ?_⟩ <;> dsimp only <;> rw [heq]
  · have heq := hoff t t₀ ht ht₀
    refine ⟨fun q => ?_, fun p => ?_, fun p a => ?_⟩ <;> dsimp only <;> rw [heq]

end Relational

end TMData

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.CountingRuns.TMData.IsHaltWalk

export Lax175070Proofs.DescriptiveComplexity.TMData.IsHaltWalk (relHaltWalk)

end Lax366625.CountingRuns.TMData.IsHaltWalk

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

section Relational

variable (M) (Q H : A → A → Prop) (T : A → A → A → Prop)

variable {M Q H T}

end Relational

end TMData

/-! ### The kernel -/

section Builders

variable {α : Type}

/-- The state at `t` is accepting, as a formula. -/
noncomputable def tqAccAtF (t : α) : tqSOLang.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1) ((tqStateF (Sum.inl t) (Sum.inr 0)).imp (tqAccF (Sum.inr 0)))

/-- The configuration at `t'` is the one at `t`, as a formula. -/
noncomputable def tqSameF (t t' : α) : tqSOLang.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1) ((tqStateF (Sum.inl t') (Sum.inr 0)).iff (tqStateF (Sum.inl t) (Sum.inr 0))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 1)
          ((tqHeadF (Sum.inl t') (Sum.inr 0)).iff (tqHeadF (Sum.inl t) (Sum.inr 0))) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 2)
          ((tqTapeF (Sum.inl t') (Sum.inr 0) (Sum.inr 1)).iff (tqTapeF (Sum.inl t) (Sum.inr 0) (Sum.inr 1))))

/-- An accepting configuration is repeated. -/
noncomputable def tqHaltClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((tqSuccPosF (Sum.inr 0) (Sum.inr 1) ⊓ tqAccAtF (Sum.inr 0)).imp (tqSameF (Sum.inr 0) (Sum.inr 1)))

/-- Times that are not positions carry the initial configuration. -/
noncomputable def tqOffClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.BoundedFormula.not (tqPosnF (Sum.inr 0)) ⊓ tqMinPosF (Sum.inr 1)).imp
        (tqSameF (Sum.inr 1) (Sum.inr 0)))

/-- **The kernel of the counting problem**: the kernel of machine acceptance,
and the two clauses that make the tableau of a run unique. -/
noncomputable def sharpTqKernel : tqSOLang.Sentence :=
  tqKernel ⊓ (tqHaltClause ⊓ tqOffClause)

end Builders

section RealizeKernel

variable {A : Type} [Lax904597.Machines.turing.Structure A] (ρ : tmGuessBlock.Assignment A)

local notation "SOStruc" => @sumStructure Lax904597.Machines.turing tmGuessBlock.lang A _
  (tmGuessBlock.structure ρ)

variable {α : Type} (v : α → A)

theorem realize_tqAccAtF (t : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqAccAtF t) v) ↔
      ∀ q, ρ .state ![v t, q] → Lax904597.Machines.TMAcc q := by
  simp only [tqAccAtF, Formula.realize_imp, Formula.realize_iAlls, realize_tqStateF,
    realize_tqAccF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h q hq => h (fun _ => q) hq, fun h i hi => h (i 0) hi⟩

theorem realize_tqSameF (t t' : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqSameF t t') v) ↔
      TMData.RelSame (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
        (fun t p a => ρ .tape ![t, p, a]) (v t) (v t') := by
  simp only [tqSameF, Formula.realize_inf, Formula.realize_iff, Formula.realize_iAlls,
    realize_tqStateF, realize_tqHeadF, realize_tqTapeF, Sum.elim_inl, Sum.elim_inr,
    TMData.RelSame]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact ⟨fun h q => h fun _ => q, fun h i => h (i 0)⟩
  · exact ⟨fun h p => h fun _ => p, fun h i => h (i 0)⟩
  · exact ⟨fun h p a => h ![p, a], fun h i => h (i 0) (i 1)⟩

theorem realize_tqHaltClause :
    (@Sentence.Realize tqSOLang A SOStruc tqHaltClause) ↔
      ∀ t t', Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn t t' → (∀ q, ρ .state ![t, q] → Lax904597.Machines.TMAcc q) →
        TMData.RelSame (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
          (fun t p a => ρ .tape ![t, p, a]) t t' := by
  simp only [tqHaltClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqSuccPosF, realize_tqAccAtF, realize_tqSameF, Sum.elim_inr]
  exact ⟨fun h t t' h₁ h₂ => h ![t, t'] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

theorem realize_tqOffClause :
    (@Sentence.Realize tqSOLang A SOStruc tqOffClause) ↔
      ∀ t t₀, ¬ Lax904597.Machines.TMPosn t → Lax904597.Machines.MinPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn t₀ →
        TMData.RelSame (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
          (fun t p a => ρ .tape ![t, p, a]) t₀ t := by
  simp only [tqOffClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, realize_tqPosnF, realize_tqMinPosF,
    realize_tqSameF, Sum.elim_inr]
  exact ⟨fun h t t₀ h₁ h₂ => h ![t, t₀] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

/-- **The kernel says exactly what it should**: the instance is well formed and
the guessed relations are a halting walk. -/
theorem realize_sharpTqKernel :
    (@Sentence.Realize tqSOLang A SOStruc sharpTqKernel) ↔
      (Lax904597.Machines.tmData A).WellFormed ∧
        (Lax904597.Machines.tmData A).RelHaltWalk (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
          (fun t p a => ρ .tape ![t, p, a]) := by
  have hinf : ∀ φ ψ : tqSOLang.Sentence, (@Sentence.Realize tqSOLang A SOStruc (φ ⊓ ψ)) ↔
      (@Sentence.Realize tqSOLang A SOStruc φ) ∧ (@Sentence.Realize tqSOLang A SOStruc ψ) := by
    intro φ ψ
    let := tmGuessBlock.structure ρ
    exact Formula.realize_inf
  rw [sharpTqKernel, hinf, hinf, realize_tqKernel, realize_tqHaltClause, realize_tqOffClause]
  exact ⟨fun ⟨⟨hwf, hw⟩, hh, ho⟩ => ⟨hwf, hw, hh, ho⟩,
    fun ⟨hwf, hw, hh, ho⟩ => ⟨⟨hwf, hw⟩, hh, ho⟩⟩

end RealizeKernel

/-! ### Runs are the witnesses of the kernel -/

section Count

variable (A : Type) [Lax904597.Machines.turing.Structure A]

/-- The guess of the block describing a family of configurations: the graphs of
its state, head and tape. -/
def confAssign {A : Type} (conf : A → Lax904597.Machines.Config A) : tmGuessBlock.Assignment A :=
  fun i => match i with
    | .state => fun w : Fin 2 → A => w 1 = (conf (w 0)).state
    | .head => fun w : Fin 2 → A => w 1 = (conf (w 0)).head
    | .tape => fun w : Fin 3 → A => w 2 = (conf (w 0)).tape (w 1)

/-- **The halting walks of a machine are the witnesses of the kernel**,
bijectively: the three guessed relations are functional, so they are the graphs
of the configurations they describe. -/
noncomputable def haltWalkEquiv :
    {ρ : tmGuessBlock.Assignment A //
        @Sentence.Realize tqSOLang A
          (@sumStructure Lax904597.Machines.turing tmGuessBlock.lang A _ (tmGuessBlock.structure ρ))
          sharpTqKernel} ≃
      {conf : A → Lax904597.Machines.Config A // (Lax904597.Machines.tmData A).WellFormed ∧ (Lax904597.Machines.tmData A).IsHaltWalk conf} where
  toFun ρ :=
    ⟨((realize_sharpTqKernel ρ.1).mp ρ.2).2.walk.conf,
      ((realize_sharpTqKernel ρ.1).mp ρ.2).1, ((realize_sharpTqKernel ρ.1).mp ρ.2).2.isHaltWalk⟩
  invFun c :=
    ⟨confAssign c.1, (realize_sharpTqKernel _).mpr ⟨c.2.1, c.2.2.relHaltWalk⟩⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    refine Subtype.ext (funext fun i => ?_)
    have hw := ((realize_sharpTqKernel ρ).mp hρ).2.walk
    cases i with
    | state =>
      refine funext fun (w : Fin 2 → A) => propext ?_
      have hw' : ρ .state ![w 0, w 1] ↔ ρ .state w :=
        iff_of_eq (congrArg (ρ .state) (funext fun k => by fin_cases k <;> rfl))
      refine Iff.trans ?_ hw'
      exact ⟨fun h => h ▸ (hw.qex (w 0)).choose_spec,
        fun h => hw.quniq (w 0) _ _ h (hw.qex (w 0)).choose_spec⟩
    | head =>
      refine funext fun (w : Fin 2 → A) => propext ?_
      have hw' : ρ .head ![w 0, w 1] ↔ ρ .head w :=
        iff_of_eq (congrArg (ρ .head) (funext fun k => by fin_cases k <;> rfl))
      refine Iff.trans ?_ hw'
      exact ⟨fun h => h ▸ (hw.hex (w 0)).choose_spec,
        fun h => hw.huniq (w 0) _ _ h (hw.hex (w 0)).choose_spec⟩
    | tape =>
      refine funext fun (w : Fin 3 → A) => propext ?_
      have hw' : ρ .tape ![w 0, w 1, w 2] ↔ ρ .tape w :=
        iff_of_eq (congrArg (ρ .tape) (funext fun k => by fin_cases k <;> rfl))
      refine Iff.trans ?_ hw'
      exact ⟨fun h => h ▸ (hw.tex (w 0) (w 1)).choose_spec,
        fun h => hw.tuniq (w 0) (w 1) _ _ h (hw.tex (w 0) (w 1)).choose_spec⟩
  right_inv := by
    rintro ⟨conf, hconf⟩
    refine Subtype.ext (funext fun t => ?_)
    have hw := ((realize_sharpTqKernel (confAssign conf)).mp
      ((realize_sharpTqKernel _).mpr ⟨hconf.1, hconf.2.relHaltWalk⟩)).2.walk
    exact Lax904597.Machines.Config.ext (hw.qex t).choose_spec (hw.hex t).choose_spec
      (funext fun p => (hw.tex t p).choose_spec)

/-- The number of halting walks is the number of witnesses of the kernel. -/
theorem card_haltWalk_eq_witnessCount :
    Nat.card {conf : A → Lax904597.Machines.Config A // (Lax904597.Machines.tmData A).WellFormed ∧ (Lax904597.Machines.tmData A).IsHaltWalk conf} =
      Lax366625.WitnessCounting.witnessCount tmGuessBlock sharpTqKernel A :=
  (Nat.card_congr (haltWalkEquiv A)).symm

end Count

/-! ### The counting problem -/

/-- **Counting accepting runs**: the number of runs of the machine described by
the instance that reach an accepting state within as many steps as there are
positions, each counted up to the first accepting configuration it reaches,
through its layout along the positions (`DescriptiveComplexity.TMData.IsHaltWalk`). As
for `DescriptiveComplexity.NTMAccept`, the well-formedness promises are folded in: an
ill-formed instance has no run. -/
noncomputable def SharpNTMAccept : Lax366625.CountingProblems.CountingProblem Lax904597.Machines.turing where
  Count := fun A inst =>
    Nat.card {conf : A → Lax904597.Machines.Config A //
      @Lax904597.Machines.TMData.WellFormed A (@Lax904597.Machines.tmData A inst) ∧ @Lax366625.CountingRuns.TMData.IsHaltWalk A (@Lax904597.Machines.tmData A inst) conf}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_haltWalk_eq_witnessCount A, card_haltWalk_eq_witnessCount B]
    exact witnessCount_iso tmGuessBlock sharpTqKernel e

theorem sharpNtmAccept_apply (A : Type) [Lax904597.Machines.turing.Structure A] :
    SharpNTMAccept A =
      Nat.card {conf : A → Lax904597.Machines.Config A //
        (Lax904597.Machines.tmData A).WellFormed ∧ (Lax904597.Machines.tmData A).IsHaltWalk conf} :=
  rfl

/-- **Counting accepting runs is in `#P`**: the runs are the witnesses of an
existential second-order sentence, the tableau of a run being determined by
it. -/
theorem sharpNtmAccept_mem_sharpP : SharpNTMAccept ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_haltWalk_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel tmGuessBlock sharpTqKernel)

end Lax175070Proofs.DescriptiveComplexity


