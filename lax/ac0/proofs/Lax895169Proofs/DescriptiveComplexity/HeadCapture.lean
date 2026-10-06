/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.HeadEval
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

namespace Lax485149.HeadAutomata
end Lax485149.HeadAutomata

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCDefinable TCSpec)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.HeadAutomata (HeadAutomaton HeadMove)
end Lax895169Proofs.DescriptiveComplexity

/-!
# The capture theorem for NL: FO(TC) is what a multi-head automaton recognizes

`DescriptiveComplexity.HeadAutomaton` compiles a machine into a
`DescriptiveComplexity.TCSpec`, which is the easy half. This file is the other half:
**every FO(TC) definable problem is recognized by a two-way multi-head
automaton**, so that the two notions coincide and
`DescriptiveComplexity.NL` is captured by the machine model as well as by the logic.

## The machine

Given a specification with arity `k`, the machine has `2 * k + D + 1` heads:

* the first `k` hold the **current tuple** of the walk;
* the next `k` hold a **candidate** for the next tuple;
* the remaining `D` are the workspace of
  `DescriptiveComplexity.HeadProgram.evalP`, which evaluates the specification's
  formulas – `D` being the largest quantifier budget among them – plus one spare
  head so that the head type is never empty.

The *mode* of the walk is not on a head – it cannot be, a one-element universe
having only one tuple – but in the control, which is what a finite control is
for.

## The loop

Written as a control graph over fragments
(`DescriptiveComplexity.HeadProgram.wireP`), the machine is:

* **pick a source mode**: a chain of free choices
  (`DescriptiveComplexity.HeadProgram.chooseP`) walking the list of modes, so that any
  mode may be selected;
* **try it**: guess the current tuple (`DescriptiveComplexity.HeadProgram.guessP`,
  a head walked up the order by a nondeterministic number of steps) and evaluate
  the source formula; a failure leads nowhere;
* **at a node**: evaluate the target formula – if it holds, accept;
* otherwise **pick a candidate mode**, guess the candidate tuple, evaluate the
  transition formula, and, if it holds, **commit**: copy the candidate onto the
  current tuple and go back to evaluating the target formula.

Guessing is where the nondeterminism lives, and it is the only place: the
evaluator itself is deterministic.

## The proof

`DescriptiveComplexity.HeadProgram.runs_wireP` turns the machine's runs into a walk in
the control graph, and the correctness is then an argument about that walk, in
two directions:

* **soundness** – an invariant carried along the walk: at a node of the control
  graph, the tuple on the first `k` heads is a node of the specification
  reachable from a source. It is preserved by every arc, and at the accepting
  arc it says exactly that the specification accepts;
* **completeness** – by induction along `DescriptiveComplexity.TCSpec.Reach`: every
  step of the specification's walk is imitated by the loop above, unless the
  target formula holds on the way, in which case the machine has already
  accepted.

The result is `DescriptiveComplexity.tcDefinable_iff_automaton`, and with it
`DescriptiveComplexity.mem_NL_iff_automaton`.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {K : ℕ}

namespace HeadProgram

/-! ### Free choices and guesses -/

section Choice

end Choice

/-! ### Guessing one head -/

section Guess

end Guess

/-! ### Guessing a block of heads -/

theorem runs_exitP_local {A : Type} [L.Structure A] [LinearOrder A] (b : Bool) (m : ℕ) :
    (exitP (L := L) (K := K) b).Runs A m fun x b' y => b' = b ∧ HeadAgree m x y :=
  (runs_exitP b).mono (fun x b' y hxy => ⟨hxy.1, fun j _ => by rw [hxy.2]⟩)
    fun x b' y hxy => ⟨x, hxy.2.symm, hxy.1, rfl⟩

theorem headLocal2_exitP {A : Type} (b : Bool) (m : ℕ) :
    HeadLocal2 m fun (x : Fin K → A) b' y => b' = b ∧ HeadAgree m x y := by
  intro x x' y y' hx hy b'
  exact and_congr Iff.rfl ⟨fun h => hx.symm.trans (h.trans hy), fun h => hx.trans (h.trans hy.symm)⟩

section GuessMany

end GuessMany

/-! ### The control graph of the machine -/

end HeadProgram

/-! ### The machine of a specification -/

open HeadProgram

section Capture

variable (spec : Lax485149.TransitiveClosure.TCSpec L)

open Classical in
/-- **The quantifier budget of a specification**: the largest number of extra
heads the evaluation of one of its formulas needs. -/
noncomputable def specDepth : ℕ :=
  letI := Fintype.ofFinite spec.Mode
  max (Finset.univ.sup fun p : spec.Mode × spec.Mode => qdepth (spec.step p.1 p.2))
    (max (Finset.univ.sup fun m => qdepth (spec.src m))
      (Finset.univ.sup fun m => qdepth (spec.tgt m)))

end Capture

/-! ### The fragments -/

section Fragments

variable (spec : Lax485149.TransitiveClosure.TCSpec L)

open Classical in
theorem qdepth_src_le (m : spec.Mode) : qdepth (spec.src m) ≤ specDepth spec := by
  let := Fintype.ofFinite spec.Mode
  exact le_trans (Finset.le_sup (f := fun m => qdepth (spec.src m)) (Finset.mem_univ m))
    (le_trans (le_max_left _ _) (le_max_right _ _))

open Classical in
theorem qdepth_tgt_le (m : spec.Mode) : qdepth (spec.tgt m) ≤ specDepth spec := by
  let := Fintype.ofFinite spec.Mode
  exact le_trans (Finset.le_sup (f := fun m => qdepth (spec.tgt m)) (Finset.mem_univ m))
    (le_trans (le_max_right _ _) (le_max_right _ _))

open Classical in
theorem qdepth_step_le (m m' : spec.Mode) : qdepth (spec.step m m') ≤ specDepth spec := by
  let := Fintype.ofFinite spec.Mode
  exact le_trans (Finset.le_sup (f := fun p : spec.Mode × spec.Mode => qdepth (spec.step p.1 p.2))
    (Finset.mem_univ (m, m'))) (le_max_left _ _)

section Eval

end Eval

end Fragments

/-! ### The machine -/

section Machine

variable (spec : Lax485149.TransitiveClosure.TCSpec L)

/-- The number of modes. -/
noncomputable def modeCard : ℕ := Nat.card spec.Mode

/-- An enumeration of the modes. -/
noncomputable def modeEquiv : spec.Mode ≃ Fin (modeCard spec) := Finite.equivFin spec.Mode

/-- The mode at an index of the enumeration, if any. -/
noncomputable def modeAt (i : Fin (modeCard spec + 1)) : Option spec.Mode :=
  if h : (i : ℕ) < modeCard spec then some ((modeEquiv spec).symm ⟨i, h⟩) else none

/-- The next index of the enumeration; it stops at the last one. -/
noncomputable def nextIx (i : Fin (modeCard spec + 1)) : Fin (modeCard spec + 1) :=
  if h : (i : ℕ) < modeCard spec then ⟨i + 1, by omega⟩ else i

/-- The index the enumeration starts at. -/
noncomputable def ix0 : Fin (modeCard spec + 1) := ⟨0, Nat.succ_pos _⟩

/-- The index of a mode in the enumeration. -/
noncomputable def ixOf (m : spec.Mode) : Fin (modeCard spec + 1) :=
  ⟨modeEquiv spec m, by have := (modeEquiv spec m).isLt; omega⟩

theorem modeAt_ixOf (m : spec.Mode) : modeAt spec (ixOf spec m) = some m := by
  have h : ((ixOf spec m : Fin (modeCard spec + 1)) : ℕ) < modeCard spec := (modeEquiv spec m).isLt
  rw [modeAt, dif_pos h]
  refine congrArg some ?_
  rw [show (⟨((ixOf spec m : Fin (modeCard spec + 1)) : ℕ), h⟩ : Fin (modeCard spec)) =
    modeEquiv spec m from Fin.ext rfl, Equiv.symm_apply_apply]

section Runs

/-! ### Soundness: what the machine knows -/

/-! The wiring, arc by arc. -/

section Arcs

end Arcs

/-! ### Completeness: the machine imitates the walk -/

/-! ### The capture theorem -/

end Runs

end Machine

/-! ### The capture theorem -/

end Lax895169Proofs.DescriptiveComplexity


