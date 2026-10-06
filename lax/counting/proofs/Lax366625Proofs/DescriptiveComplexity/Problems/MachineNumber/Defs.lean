/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax366625Proofs.DescriptiveComplexity.Problems.Machine.DetRun
import Lax366625Proofs.DescriptiveComplexity.FixedPointOrderTransfer
import Lax366625Proofs.DescriptiveComplexity.Counting
import Lax366625Proofs.DescriptiveComplexity.Vocabulary
import Mathlib.Algebra.BigOperators.Finprod
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.MachineNumbers
end Lax366625.MachineNumbers

namespace Lax366625.MachineNumbers.TMData
end Lax366625.MachineNumbers.TMData

namespace Lax366625Proofs.DescriptiveComplexity.TMData
end Lax366625Proofs.DescriptiveComplexity.TMData

namespace Lax366625Proofs.DescriptiveComplexity.TMData.Agree
end Lax366625Proofs.DescriptiveComplexity.TMData.Agree

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.MachineNumbers (LowerCell OutDigit cellRank machineNumber mnLe mnOne mnOut turingOutStructure)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Machines (Config SuccPos TMData tmData)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax366625.MachineNumbers (tapeOut tpOne tpOut turingOut)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Machines (tmLe turing)
end FirstOrder.Language

namespace Lax904597.Machines.TMData
export Lax366625.MachineNumbers.TMData (Halts)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

/-!
# The number written by a machine: definition

The function counterpart of deterministic machine acceptance
(`DescriptiveComplexity.DTMAccept`): the machine is data in the instance, and
the problem is to compute the number it leaves on its tape.

* The vocabulary is the one of machine instances
  (`FirstOrder.Language.turing`) with two more symbols
  (`FirstOrder.Language.tapeOut`): `out` marks the **output cells** and `one`
  marks the symbols read as the digit `1`.
* The machine **halts** (`DescriptiveComplexity.TMData.Halts`) in a
  configuration reached from the initial one within the clock – fewer steps
  than there are positions, as for acceptance – from which no step is
  possible. A deterministic machine halts in at most one configuration
  (`DescriptiveComplexity.TMData.halts_unique`).
* `DescriptiveComplexity.machineNumber`: an output cell holding, when the
  machine halts in an accepting state, a symbol marked `one` contributes
  `2 ^ r`, where `r` is the number of output cells strictly before it on the
  tape: the digits are read **in tape order**, the lowest cell holding the
  least significant one. A machine that does not halt within its clock, or
  halts without accepting, writes `0`, and so does an instance that is not a
  well-formed deterministic machine.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Halting -/

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

/-- **A deterministic machine halts in at most one configuration.** -/
theorem halts_unique [Finite A] (hwf : M.WellFormed) (hdet : M.Deterministic) {c d : Lax904597.Machines.Config A}
    (hc : M.Halts c) (hd : M.Halts d) : c = d := by
  obtain ⟨c₀, n, hi, -, hrun, hstuck⟩ := hc
  obtain ⟨d₀, m, hi', -, hrun', hstuck'⟩ := hd
  obtain rfl := isInit_unique hwf hdet.1 hi hi'
  rcases reach_total hwf.1 hdet (reflTransGen_of_stepsIn hrun) (reflTransGen_of_stepsIn hrun')
    with h | h
  · exact eq_of_reach_stuck hstuck h
  · exact (eq_of_reach_stuck hstuck' h).symm

end TMData

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax366625Proofs.DescriptiveComplexity.TMData (halts_unique)

end Lax904597.Machines.TMData

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

open Classical in
/-- **A step is possible** exactly when some transition applies in the
current state to the symbol under the head, and can fire: it has a
destination, a written symbol, and a neighbor in its direction. -/
theorem exists_step_iff (c : Lax904597.Machines.Config A) :
    (∃ e, M.Step c e) ↔ ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
      (∃ q, M.Dst τ q) ∧ (∃ a, M.Write τ a) ∧
        ((M.Right τ ∧ ∃ p, Lax904597.Machines.SuccPos M.Le M.Posn c.head p) ∨
          (¬M.Right τ ∧ ∃ p, Lax904597.Machines.SuccPos M.Le M.Posn p c.head)) := by
  constructor
  · rintro ⟨e, τ, hτ, hsrc, hread, hdst, hwrite, -, hmove⟩
    exact ⟨τ, hτ, hsrc, hread, ⟨_, hdst⟩, ⟨_, hwrite⟩,
      hmove.imp (fun h => ⟨h.1, _, h.2⟩) fun h => ⟨h.1, _, h.2⟩⟩
  · rintro ⟨τ, hτ, hsrc, hread, ⟨q, hq⟩, ⟨a, ha⟩, hmove⟩
    have key : ∀ p : A, ((M.Right τ ∧ Lax904597.Machines.SuccPos M.Le M.Posn c.head p) ∨
        (¬M.Right τ ∧ Lax904597.Machines.SuccPos M.Le M.Posn p c.head)) →
        M.Step c ⟨q, p, Function.update c.tape c.head a⟩ := fun p hp =>
      ⟨τ, hτ, hsrc, hread, hq,
        (show M.Write τ (Function.update c.tape c.head a c.head) by
          rw [Function.update_self]; exact ha),
        fun p' hp' => Function.update_of_ne hp' _ _, hp⟩
    rcases hmove with ⟨hr, p, hp⟩ | ⟨hr, p, hp⟩
    · exact ⟨_, key p (Or.inl ⟨hr, hp⟩)⟩
    · exact ⟨_, key p (Or.inr ⟨hr, hp⟩)⟩

end TMData

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax366625Proofs.DescriptiveComplexity.TMData (exists_step_iff)

end Lax904597.Machines.TMData

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

/-- Halting transports along an equivalence. -/
theorem Agree.halts {B : Type} {u : B ≃ A} {N : Lax904597.Machines.TMData B} (h : Agree u N M) (c : Lax904597.Machines.Config B) :
    N.Halts c ↔ M.Halts (c.map u) := by
  have hcard : Nat.card {b : B // N.Posn b} = Nat.card {a : A // M.Posn a} :=
    Nat.card_congr (u.subtypeEquiv fun b => h.posn b)
  constructor
  · rintro ⟨c₀, n, hi, hn, hrun, hstuck⟩
    refine ⟨c₀.map u, n, h.isInit.mp hi, hcard ▸ hn, (h.stepsIn n c₀ c).mp hrun, fun e he => ?_⟩
    obtain ⟨e₀, rfl⟩ := Config.map_surjective u e
    exact hstuck e₀ (h.step.mpr he)
  · rintro ⟨c₀, n, hi, hn, hrun, hstuck⟩
    obtain ⟨d₀, rfl⟩ := Config.map_surjective u c₀
    exact ⟨d₀, n, h.isInit.mpr hi, hcard ▸ hn, (h.stepsIn n d₀ c).mpr hrun,
      fun e he => hstuck (e.map u) (h.step.mp he)⟩

end TMData

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax366625Proofs.DescriptiveComplexity.TMData.Agree (halts)

end Lax904597.Machines.TMData.Agree

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

/-- Agreements compose. -/
theorem Agree.trans {B C : Type} {u : B ≃ A} {v : C ≃ B} {N : Lax904597.Machines.TMData B} {K : Lax904597.Machines.TMData C}
    (h₁ : Agree v K N) (h₂ : Agree u N M) : Agree (v.trans u) K M where
  posn b := (h₁.posn b).trans (h₂.posn _)
  le b b' := (h₁.le b b').trans (h₂.le _ _)
  tr b := (h₁.tr b).trans (h₂.tr _)
  start b := (h₁.start b).trans (h₂.start _)
  acc b := (h₁.acc b).trans (h₂.acc _)
  blank b := (h₁.blank b).trans (h₂.blank _)
  right b := (h₁.right b).trans (h₂.right _)
  src b b' := (h₁.src b b').trans (h₂.src _ _)
  read b b' := (h₁.read b b').trans (h₂.read _ _)
  dst b b' := (h₁.dst b b').trans (h₂.dst _ _)
  write b b' := (h₁.write b b').trans (h₂.write _ _)
  inp b b' := (h₁.inp b b').trans (h₂.inp _ _)

end TMData

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax366625Proofs.DescriptiveComplexity.TMData.Agree (trans)

end Lax904597.Machines.TMData.Agree

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

variable {M}

end TMData

/-! ### The number -/

section Semantics

variable {A : Type} [Lax366625.MachineNumbers.turingOut.Structure A]

end Semantics

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

variable {A B : Type} [Lax366625.MachineNumbers.turingOut.Structure A] [Lax366625.MachineNumbers.turingOut.Structure B]

theorem outDigit_equiv (e : A ≃[Lax366625.MachineNumbers.turingOut] B) (p : A) : Lax366625.MachineNumbers.OutDigit (e p) ↔ Lax366625.MachineNumbers.OutDigit p := by
  have hag := agree_of_equiv (reductSumInlEquiv e)
  have hone : ∀ (c : Lax904597.Machines.Config B), (RelMap Lax366625.MachineNumbers.mnOne ![c.tape (e p)] : Prop) ↔
      RelMap Lax366625.MachineNumbers.mnOne ![(c.map (reductSumInlEquiv e).symm.toEquiv).tape p] := by
    intro c
    have h := relMap_equiv₁ e Lax366625.MachineNumbers.mnOne (e.symm (c.tape (e p)))
    rw [show (e (e.symm (c.tape (e p))) : B) = c.tape (e p) from
      e.toEquiv.apply_symm_apply _] at h
    exact h.symm
  refine and_congr (relMap_equiv₁ e Lax366625.MachineNumbers.mnOut p).symm ⟨?_, ?_⟩
  · rintro ⟨c, hc, ha, h1⟩
    exact ⟨_, (hag.halts c).mp hc, (hag.acc _).mp ha, (hone c).mp h1⟩
  · rintro ⟨c, hc, ha, h1⟩
    obtain ⟨d, rfl⟩ := Config.map_surjective (reductSumInlEquiv e).symm.toEquiv c
    exact ⟨d, (hag.halts d).mpr hc, (hag.acc _).mpr ha, (hone d).mpr h1⟩

theorem lowerCell_equiv (e : A ≃[Lax366625.MachineNumbers.turingOut] B) (p q : A) :
    Lax366625.MachineNumbers.LowerCell (e p) (e q) ↔ Lax366625.MachineNumbers.LowerCell p q :=
  and_congr (relMap_equiv₁ e Lax366625.MachineNumbers.mnOut q).symm
    (and_congr e.toEquiv.injective.ne_iff (relMap_equiv₂ e Lax366625.MachineNumbers.mnLe q p).symm)

theorem cellRank_equiv (e : A ≃[Lax366625.MachineNumbers.turingOut] B) (p : A) :
    Lax366625.MachineNumbers.cellRank (e p) = Lax366625.MachineNumbers.cellRank p :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv fun q => (lowerCell_equiv e p q).symm)).symm

/-- The number written is isomorphism-invariant. -/
theorem machineNumber_iso (e : A ≃[Lax366625.MachineNumbers.turingOut] B) :
    Lax366625.MachineNumbers.machineNumber A = Lax366625.MachineNumbers.machineNumber B := by
  classical
  have hag := agree_of_equiv (reductSumInlEquiv e)
  have hsum : (∑ᶠ p : A, if Lax366625.MachineNumbers.OutDigit p then 2 ^ Lax366625.MachineNumbers.cellRank p else 0) =
      ∑ᶠ p : B, if Lax366625.MachineNumbers.OutDigit p then 2 ^ Lax366625.MachineNumbers.cellRank p else 0 := by
    rw [← finsum_comp_equiv e.toEquiv]
    refine finsum_congr fun p => ?_
    change _ = if Lax366625.MachineNumbers.OutDigit (e p) then 2 ^ Lax366625.MachineNumbers.cellRank (e p) else 0
    rw [cellRank_equiv e p, if_congr (outDigit_equiv e p) rfl rfl]
  rw [Lax366625.MachineNumbers.machineNumber, Lax366625.MachineNumbers.machineNumber, hsum]
  exact if_congr (and_congr hag.wellFormed hag.deterministic).symm rfl rfl

end Iso

/-- **The number written by a deterministic machine**, as a counting problem
on `Language.turingOut`-structures: the function counterpart of
`DescriptiveComplexity.DTMAccept`. -/
noncomputable def DTMNumber : Lax366625.CountingProblems.CountingProblem Lax366625.MachineNumbers.turingOut where
  Count := fun A inst => @Lax366625.MachineNumbers.machineNumber A inst
  iso_invariant := fun e => machineNumber_iso e

end Lax366625Proofs.DescriptiveComplexity


