/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.DetLogSpace
import Lax895169Proofs.DescriptiveComplexity.OrderWalk
import Lax895169Proofs.DescriptiveComplexity.Padding
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

namespace Lax485149.DeterministicTransitiveClosure
end Lax485149.DeterministicTransitiveClosure

namespace Lax485149.HeadAutomata
end Lax485149.HeadAutomata

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax895169Proofs.DescriptiveComplexity.HeadAutomaton
end Lax895169Proofs.DescriptiveComplexity.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity.HeadMove
end Lax895169Proofs.DescriptiveComplexity.HeadMove

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCDefinable TCSpec)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.DeterministicTransitiveClosure (DTCDefinable)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.HeadAutomata (HeadAutomaton HeadMove)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Two-way multi-head automata over a structure

The machine model of the logarithmic-space level: a **fixed finite control with
`k` two-way heads**, each head holding an *element of the universe*, with no
work tape at all. This is the machine side of `DescriptiveComplexity.LOGSPACE` and
`DescriptiveComplexity.NL`, and it is deliberately *not* the automaton of formal
language theory.

## Which automaton this is, and which it is not

Mathlib's `FirstOrder`-free `DFA`/`NFA` consume a *word* by a one-way left fold
over an alphabet. Neither half of that fits here:

* the input is a finite **structure**, not a string, so using them would require
  serializing the instance – fixing an order and an encoding – and the theorem
  would be about the encoding rather than about the structure;
* they are **one-way and single-head**. A one-way single-head automaton over any
  such encoding recognizes only regular languages. Two-wayness and the `k` heads
  are not decoration: they *are* the logarithmic-space resource bound, `k` head
  positions being `k · log |A|` bits of storage.

So the model here is its own structure, in the style of
`DescriptiveComplexity.TMData` (which likewise presents a machine as relations on a
universe rather than as strings):

* a finite set of control states, one of them initial, some of them accepting;
* `k` heads, each holding an element of the universe; a **configuration** is a
  state together with a `k`-tuple of elements;
* what a step **reads**: the truth values of a fixed finite list of
  *quantifier-free* formulas of the head variables
  (`DescriptiveComplexity.HeadAutomaton.test`, with `test_qf` recording the
  restriction). Quantifier-freeness is what keeps this a machine: the control
  may compare its heads and look at the relations holding between them, and
  nothing else. Without that field the model would be first-order logic in
  disguise;
* what a step **does**: per head, `stay`, jump to the minimum or the maximum,
  copy another head, or step to the immediate successor or predecessor of
  another head (`DescriptiveComplexity.HeadMove`). A head at the last element moving
  right has no successor and the transition is simply disabled, the same
  convention as `DescriptiveComplexity.TMData`.

Nondeterminism is a *list* of transitions per state and reading;
`DescriptiveComplexity.HeadAutomaton.IsDeterministic` restricts it to at most one, which
is the machine-level counterpart of the determinization of
`DescriptiveComplexity.TCSpec.det`.

## What is proved here, and what is not

A configuration – a control state with a `k`-tuple – *is* a
`DescriptiveComplexity.TCSpec.Node`: the control is the mode and the heads are the
tuple. So an automaton compiles into a specification
(`DescriptiveComplexity.HeadAutomaton.toSpec`) by writing each transition as a
first-order formula, and its acceptance is the acceptance of that specification
(`DescriptiveComplexity.HeadAutomaton.accepts_toSpec`). Hence

* `DescriptiveComplexity.tcDefinable_of_automaton`: a problem recognized by such an
  automaton is FO(TC) definable, so in `DescriptiveComplexity.NL`;
* `DescriptiveComplexity.dtcDefinable_of_automaton`: recognized by a *deterministic*
  one, it is FO(DTC) definable, so in `DescriptiveComplexity.LOGSPACE`.

This direction is the cheap one, and it is also a practical membership tool:
exhibiting an automaton is often much easier than writing a
`DescriptiveComplexity.TCSpec` by hand.

The converse – every FO(TC) definable problem is *recognized* by such an
automaton – is proved in `DescriptiveComplexity.HeadCapture`, on top of the
guarded-transition presentation of `DescriptiveComplexity.HeadProgram` and the
formula evaluator of `DescriptiveComplexity.HeadEval`; together with the above it
gives the capture theorem `DescriptiveComplexity.tcDefinable_iff_automaton`, and
`DescriptiveComplexity.mem_NL_iff_automaton`. The deterministic level is
`DescriptiveComplexity.HeadCaptureDet`, where a machine for an arbitrary FO(DTC)
definition needs more than the evaluator – it has to search where the
nondeterministic one guesses, and to bound its own walk with a step budget –
giving `DescriptiveComplexity.dtcDefinable_iff_automaton` and
`DescriptiveComplexity.mem_LOGSPACE_iff_automaton`.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Moves -/

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

/-- A move determines the new position of its head. -/
theorem holds_unique {mv : Lax485149.HeadAutomata.HeadMove k} {x : Fin k → A} {j : Fin k} {y y' : A}
    (h : mv.Holds x j y) (h' : mv.Holds x j y') : y = y' := by
  cases mv with
  | stay => exact h.trans h'.symm
  | toMin => exact le_antisymm (h y') (h' y)
  | toMax => exact le_antisymm (h' y) (h y')
  | copy i => exact h.trans h'.symm
  | succ i =>
    rcases lt_trichotomy y y' with hlt | heq | hgt
    · exact absurd ⟨h.1, hlt⟩ (h'.2 y)
    · exact heq
    · exact absurd ⟨h'.1, hgt⟩ (h.2 y')
  | pred i =>
    rcases lt_trichotomy y y' with hlt | heq | hgt
    · exact absurd ⟨hlt, h'.1⟩ (h.2 y')
    · exact heq
    · exact absurd ⟨hgt, h.1⟩ (h'.2 y)

end HeadMove

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadMove

export Lax895169Proofs.DescriptiveComplexity.HeadMove (holds_unique)

end Lax485149.HeadAutomata.HeadMove

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

variable (L)

/-- Equality of two variables, as a formula. -/
def eqVarF {γ : Type} (u v : γ) : (L.sum Language.order).Formula γ :=
  Term.equal (Term.var u) (Term.var v)

end HeadMove

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadMove

export Lax895169Proofs.DescriptiveComplexity.HeadMove (eqVarF)

end Lax485149.HeadAutomata.HeadMove

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

variable (L)

/-- A move, as a formula relating the current heads (left) to the new position
of head `j` (right). -/
noncomputable def toFormula (j : Fin k) :
    Lax485149.HeadAutomata.HeadMove k → (L.sum Language.order).Formula (Fin k ⊕ Fin k)
  | .stay => eqVarF L (Sum.inr j) (Sum.inl j)
  | .toMin => minF (Sum.inr j)
  | .toMax => maxF (Sum.inr j)
  | .copy i => eqVarF L (Sum.inr j) (Sum.inl i)
  | .succ i => succF (Sum.inl i) (Sum.inr j)
  | .pred i => succF (Sum.inr j) (Sum.inl i)

end HeadMove

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadMove

export Lax895169Proofs.DescriptiveComplexity.HeadMove (toFormula)

end Lax485149.HeadAutomata.HeadMove

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

variable (L)

variable {L}

@[simp]
theorem realize_eqVarF {γ A : Type} [L.Structure A] [LinearOrder A] {v : γ → A} (u w : γ) :
    (eqVarF L u w).Realize v ↔ v u = v w := by
  rw [eqVarF, Formula.realize_equal, Term.realize_var, Term.realize_var]

end HeadMove

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadMove

export Lax895169Proofs.DescriptiveComplexity.HeadMove (realize_eqVarF)

end Lax485149.HeadAutomata.HeadMove

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

variable (L)

variable {L}

@[simp]
theorem realize_toFormula [L.Structure A] (j : Fin k) (mv : Lax485149.HeadAutomata.HeadMove k)
    (x y : Fin k → A) :
    (mv.toFormula L j).Realize (Sum.elim x y) ↔ mv.Holds x j (y j) := by
  cases mv <;>
    simp only [toFormula, Lax485149.HeadAutomata.HeadMove.Holds, realize_eqVarF, realize_minF, realize_maxF, realize_succF,
      Sum.elim_inl, Sum.elim_inr]

end HeadMove

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadMove

export Lax895169Proofs.DescriptiveComplexity.HeadMove (realize_toFormula)

end Lax485149.HeadAutomata.HeadMove

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

variable (L)

variable {L}

end HeadMove

/-! ### The automaton -/

attribute [instance] Lax485149.HeadAutomata.HeadAutomaton.stateFinite Lax485149.HeadAutomata.HeadAutomaton.testFinite

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

theorem reading_iff (x : Fin k → A) (i : M.TestIx) :
    M.reading x i = true ↔ (M.test i).Realize x := by
  classical
  rw [Lax485149.HeadAutomata.HeadAutomaton.reading, decide_eq_true_iff]

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (reading_iff)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

/-! ### Compiling an automaton into a specification -/

open Classical in
/-- All outcomes the tests may have, as a list: the transition formula is a
disjunction over them. -/
noncomputable def allReadings (T : Type) [Finite T] : List (T → Bool) :=
  letI := Fintype.ofFinite T
  (Finset.univ : Finset (T → Bool)).toList

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (allReadings)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

theorem mem_allReadings {T : Type} [Finite T] (r : T → Bool) : r ∈ allReadings T := by
  classical
  let := Fintype.ofFinite T
  exact Finset.mem_toList.mpr (Finset.mem_univ r)

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (mem_allReadings)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

open Classical in
/-- The test indices, as a list. -/
noncomputable def allTests : List M.TestIx :=
  letI := Fintype.ofFinite M.TestIx
  (Finset.univ : Finset M.TestIx).toList

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (allTests)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

theorem mem_allTests (i : M.TestIx) : i ∈ M.allTests := by
  classical
  let := Fintype.ofFinite M.TestIx
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (mem_allTests)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

/-- The formula saying that the tests come out as `r` does. -/
noncomputable def readingF (r : M.TestIx → Bool) :
    (L.sum Language.order).Formula (Fin k ⊕ Fin k) :=
  listInf (M.allTests.map fun i =>
    if r i then (M.test i).relabel Sum.inl else ∼((M.test i).relabel Sum.inl))

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (readingF)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_readingF (r : M.TestIx → Bool) (x y : Fin k → A) :
    (M.readingF r).Realize (Sum.elim x y) ↔ M.reading x = r := by
  classical
  have hrel : ∀ i, ((M.test i).relabel Sum.inl).Realize (Sum.elim x y) ↔
      (M.test i).Realize x := by
    intro i
    rw [Formula.realize_relabel]
    exact Iff.rfl
  have key : ∀ i, ((if r i then (M.test i).relabel Sum.inl
      else ∼((M.test i).relabel Sum.inl)).Realize (Sum.elim x y)) ↔ M.reading x i = r i := by
    intro i
    rw [Lax485149.HeadAutomata.HeadAutomaton.reading]
    cases hri : r i with
    | true => simp [hrel i]
    | false => simp [hrel i]
  rw [readingF, realize_listInf]
  constructor
  · intro h
    funext i
    exact (key i).mp (h _ (List.mem_map.mpr ⟨i, M.mem_allTests i, rfl⟩))
  · rintro rfl ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (key i).mpr rfl

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (realize_readingF)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

/-- The formula prescribing the moves of every head. -/
noncomputable def movesF (mvs : Fin k → Lax485149.HeadAutomata.HeadMove k) :
    (L.sum Language.order).Formula (Fin k ⊕ Fin k) :=
  listInf ((List.finRange k).map fun j => (mvs j).toFormula L j)

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (movesF)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_movesF (mvs : Fin k → Lax485149.HeadAutomata.HeadMove k) (x y : Fin k → A) :
    (movesF (L := L) mvs).Realize (Sum.elim x y) ↔ ∀ j, (mvs j).Holds x j (y j) := by
  rw [movesF, realize_listInf]
  constructor
  · intro h j
    exact (HeadMove.realize_toFormula j (mvs j) x y).mp
      (h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    exact (HeadMove.realize_toFormula j (mvs j) x y).mpr (h j)

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (realize_movesF)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

open Classical in
/-- The transition formula of the specification, at a pair of control states:
a disjunction over the possible readings and over the transitions they enable
that land in the second state. -/
noncomputable def stepF (s s' : M.State) :
    (L.sum Language.order).Formula (Fin k ⊕ Fin k) :=
  listSup ((allReadings M.TestIx).map fun r =>
    M.readingF r ⊓
      listSup (((M.trans s r).filter fun p => p.1 = s').map fun p => movesF p.2))

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (stepF)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_stepF (s s' : M.State) (x y : Fin k → A) :
    (M.stepF s s').Realize (Sum.elim x y) ↔
      ∃ p ∈ M.trans s (M.reading x), p.1 = s' ∧ ∀ j, (p.2 j).Holds x j (y j) := by
  classical
  rw [stepF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_inf, M.realize_readingF] at hr
    obtain ⟨hrx, hmv⟩ := hr
    rw [realize_listSup] at hmv
    obtain ⟨χ, hχ, hmv'⟩ := hmv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hχ
    obtain ⟨hpm, hps⟩ := List.mem_filter.mp hp
    refine ⟨p, hrx ▸ hpm, by simpa using hps, ?_⟩
    exact (realize_movesF p.2 x y).mp hmv'
  · rintro ⟨p, hp, hps, hmv⟩
    refine ⟨_, List.mem_map.mpr ⟨M.reading x, mem_allReadings _, rfl⟩, ?_⟩
    rw [Formula.realize_inf, M.realize_readingF, realize_listSup]
    refine ⟨rfl, movesF p.2, List.mem_map.mpr ⟨p, ?_, rfl⟩, (realize_movesF p.2 x y).mpr hmv⟩
    exact List.mem_filter.mpr ⟨hp, by simpa using hps⟩

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (realize_stepF)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

open Classical in
/-- **The specification of the automaton's walk**: the control states are the
modes, the heads are the tuple, and the transitions are the step formulas. -/
noncomputable def toSpec : Lax485149.TransitiveClosure.TCSpec L where
  Mode := M.State
  k := k
  step := M.stepF
  src s := if s = M.start then listInf ((List.finRange k).map fun j => minF j) else ⊥
  tgt s := if M.accept s then ⊤ else ⊥

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (toSpec)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

@[simp]
theorem step_toSpec (a b : M.Config A) : M.toSpec.Step a b ↔ M.Step a b :=
  M.realize_stepF a.1 b.1 a.2 b.2

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (step_toSpec)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

theorem isSrc_toSpec (a : M.Config A) :
    M.toSpec.IsSrc a ↔ a.1 = M.start ∧ ∀ j, ∀ b : A, a.2 j ≤ b := by
  classical
  change ((if a.1 = M.start then listInf ((List.finRange k).map fun j => minF j)
    else ⊥ : (L.sum Language.order).Formula (Fin k))).Realize a.2 ↔ _
  by_cases hs : a.1 = M.start
  · rw [if_pos hs, realize_listInf]
    refine ⟨fun h => ⟨hs, fun j => ?_⟩, fun h ψ hψ => ?_⟩
    · exact (realize_minF j).mp (h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
      exact (realize_minF j).mpr (h.2 j)
  · rw [if_neg hs, Formula.realize_bot]
    exact iff_of_false id fun h => hs h.1

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (isSrc_toSpec)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

theorem isTgt_toSpec (a : M.Config A) : M.toSpec.IsTgt a ↔ M.accept a.1 = true := by
  classical
  change ((if M.accept a.1 then ⊤ else ⊥ : (L.sum Language.order).Formula (Fin k))).Realize
    a.2 ↔ _
  by_cases hs : M.accept a.1 = true
  · rw [if_pos hs]
    exact iff_of_true (Formula.realize_top.mpr trivial) hs
  · rw [if_neg hs, Formula.realize_bot]
    exact iff_of_false id hs

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (isTgt_toSpec)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

/-- The walk of the specification is the run of the automaton. -/
theorem reach_toSpec (a b : M.Config A) :
    M.toSpec.Reach a b ↔ Relation.ReflTransGen M.Step a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail d e _ hde ih => exact ih.tail ((M.step_toSpec d e).mp hde)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail d e _ hde ih => exact ih.tail ((M.step_toSpec d e).mpr hde)

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (reach_toSpec)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

/-- **The compilation is correct**: the specification accepts exactly the
structures the automaton does. -/
theorem accepts_toSpec : M.toSpec.Accepts A ↔ M.Accepts A := by
  constructor
  · rintro ⟨c₀, c, hsrc, htgt, hreach⟩
    exact ⟨c₀, c, (M.isSrc_toSpec c₀).mp hsrc, (M.reach_toSpec c₀ c).mp hreach,
      (M.isTgt_toSpec c).mp htgt⟩
  · rintro ⟨c₀, c, hsrc, hreach, hacc⟩
    exact ⟨c₀, c, (M.isSrc_toSpec c₀).mpr hsrc, (M.isTgt_toSpec c).mpr hacc,
      (M.reach_toSpec c₀ c).mpr hreach⟩

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (accepts_toSpec)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

/-- A deterministic automaton has a functional walk: its transition list holds
at most one transition, and each move determines where its head lands. -/
theorem functional_toSpec (hdet : M.IsDeterministic) : M.toSpec.Functional A := by
  intro a b c hb hc
  obtain ⟨p, hp, hps, hpm⟩ := (M.step_toSpec a b).mp hb
  obtain ⟨q, hq, hqs, hqm⟩ := (M.step_toSpec a c).mp hc
  have hpq : p = q := by
    rcases hl : M.trans a.1 (M.reading a.2) with _ | ⟨u, us⟩
    · rw [hl] at hp
      simp at hp
    · have hus : us = [] := by
        have hlen := hdet a.1 (M.reading a.2)
        rw [hl] at hlen
        simpa using hlen
      rw [hl, hus, List.mem_singleton] at hp hq
      rw [hp, hq]
  refine Prod.ext_iff.mpr ⟨hps.symm.trans (hpq ▸ hqs), funext fun j => ?_⟩
  exact HeadMove.holds_unique (hpm j) (hpq ▸ hqm j)

end HeadAutomaton

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.HeadAutomata.HeadAutomaton

export Lax895169Proofs.DescriptiveComplexity.HeadAutomaton (functional_toSpec)

end Lax485149.HeadAutomata.HeadAutomaton

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace HeadAutomaton

variable {k : ℕ} (M : Lax485149.HeadAutomata.HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

end HeadAutomaton

/-! ### Membership through an automaton -/

/-- **A problem recognized by a *deterministic* two-way multi-head automaton is
FO(DTC) definable** – hence in `DescriptiveComplexity.LOGSPACE`. Determinism of the
control is exactly what makes the walk functional, so its determinization
changes nothing. -/
theorem dtcDefinable_of_automaton {k : ℕ} [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (M : Lax485149.HeadAutomata.HeadAutomaton L k)
    (hdet : M.IsDeterministic)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ M.Accepts A) : Lax485149.DeterministicTransitiveClosure.DTCDefinable P := by
  refine ⟨M.toSpec, ?_⟩
  intro A _ _ _ _
  rw [TCSpec.det_accepts_iff _ (M.functional_toSpec hdet)]
  exact (h A).trans (M.accepts_toSpec).symm

end Lax895169Proofs.DescriptiveComplexity


