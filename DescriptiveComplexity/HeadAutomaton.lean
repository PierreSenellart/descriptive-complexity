/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.DetLogSpace
import DescriptiveComplexity.OrderWalk
import DescriptiveComplexity.Padding

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Moves -/

/-- What a head may do in one step: stay where it is, jump to an end of the
order, copy another head, or step to the immediate successor or predecessor of
another head. All of it is definable from the order, which is what lets a
transition become a first-order formula. -/
inductive HeadMove (k : ℕ) where
  /-- Stay on the current element. -/
  | stay : HeadMove k
  /-- Jump to the least element. -/
  | toMin : HeadMove k
  /-- Jump to the greatest element. -/
  | toMax : HeadMove k
  /-- Copy the position of head `i`. -/
  | copy (i : Fin k) : HeadMove k
  /-- Move to the immediate successor of head `i` (disabled at the greatest
  element, which is how a head runs off the end). -/
  | succ (i : Fin k) : HeadMove k
  /-- Move to the immediate predecessor of head `i` (disabled at the least
  element). -/
  | pred (i : Fin k) : HeadMove k
  deriving DecidableEq

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

/-- The semantics of a move: where head `j` may be after it, the current heads
being `x`. -/
def Holds (mv : HeadMove k) (x : Fin k → A) (j : Fin k) (y : A) : Prop :=
  match mv with
  | .stay => y = x j
  | .toMin => ∀ b : A, y ≤ b
  | .toMax => ∀ b : A, b ≤ y
  | .copy i => y = x i
  | .succ i => x i < y ∧ ∀ a : A, ¬(x i < a ∧ a < y)
  | .pred i => y < x i ∧ ∀ a : A, ¬(y < a ∧ a < x i)

/-- A move determines the new position of its head. -/
theorem holds_unique {mv : HeadMove k} {x : Fin k → A} {j : Fin k} {y y' : A}
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

variable (L)

/-- Equality of two variables, as a formula. -/
def eqVarF {γ : Type} (u v : γ) : (L.sum Language.order).Formula γ :=
  Term.equal (Term.var u) (Term.var v)

/-- A move, as a formula relating the current heads (left) to the new position
of head `j` (right). -/
noncomputable def toFormula (j : Fin k) :
    HeadMove k → (L.sum Language.order).Formula (Fin k ⊕ Fin k)
  | .stay => eqVarF L (Sum.inr j) (Sum.inl j)
  | .toMin => minF (Sum.inr j)
  | .toMax => maxF (Sum.inr j)
  | .copy i => eqVarF L (Sum.inr j) (Sum.inl i)
  | .succ i => succF (Sum.inl i) (Sum.inr j)
  | .pred i => succF (Sum.inr j) (Sum.inl i)

variable {L}

@[simp]
theorem realize_eqVarF {γ A : Type} [L.Structure A] [LinearOrder A] {v : γ → A} (u w : γ) :
    (eqVarF L u w).Realize v ↔ v u = v w := by
  rw [eqVarF, Formula.realize_equal, Term.realize_var, Term.realize_var]

@[simp]
theorem realize_toFormula [L.Structure A] (j : Fin k) (mv : HeadMove k)
    (x y : Fin k → A) :
    (mv.toFormula L j).Realize (Sum.elim x y) ↔ mv.Holds x j (y j) := by
  cases mv <;>
    simp only [toFormula, Holds, realize_eqVarF, realize_minF, realize_maxF, realize_succF,
      Sum.elim_inl, Sum.elim_inr]

end HeadMove

/-! ### The automaton -/

/-- **A two-way `k`-head automaton over `L`-structures**: a finite control, a
finite list of quantifier-free tests of the head positions, and, per state and
per outcome of those tests, a list of possible transitions – a new state and one
move per head. No work tape: all the storage is in the `k` heads. -/
structure HeadAutomaton (L : Language.{0, 0}) (k : ℕ) where
  /-- The control states. -/
  State : Type
  /-- The control is finite: that is what makes this a machine. -/
  [stateFinite : Finite State]
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  accept : State → Bool
  /-- What the control reads at each step, indexed by a finite type. -/
  TestIx : Type
  /-- Finitely many tests: a control that could read unboundedly many facts
  would not be a finite control. -/
  [testFinite : Finite TestIx]
  /-- The tests: what the control sees of the current head positions. -/
  test : TestIx → (L.sum Language.order).Formula (Fin k)
  /-- **The tests are quantifier-free.** The control may compare its heads and
  look at the relations holding between them, and nothing else; a quantified
  test would make the model first-order logic in disguise. -/
  test_qf : ∀ i, (test i).IsQF
  /-- The transitions available in a state, at a given outcome of the tests:
  a new state and a move for each head. Nondeterminism is the length of this
  list. -/
  trans : State → (TestIx → Bool) → List (State × (Fin k → HeadMove k))

attribute [instance] HeadAutomaton.stateFinite HeadAutomaton.testFinite

namespace HeadAutomaton

variable {k : ℕ} (M : HeadAutomaton L k) {A : Type} [L.Structure A] [LinearOrder A]

/-- A configuration: a control state together with the positions of the heads.
It is exactly a node of a `DescriptiveComplexity.TCSpec`. -/
abbrev Config (A : Type) : Type := M.State × (Fin k → A)

open Classical in
/-- What the control reads at a configuration: the truth values of its tests. -/
noncomputable def reading (x : Fin k → A) : M.TestIx → Bool :=
  fun i => decide ((M.test i).Realize x)

theorem reading_iff (x : Fin k → A) (i : M.TestIx) :
    M.reading x i = true ↔ (M.test i).Realize x := by
  classical
  rw [reading, decide_eq_true_iff]

/-- One step of the automaton: some transition available at the current state
and reading leads to the new state, each head moving as it prescribes. -/
def Step (a b : M.Config A) : Prop :=
  ∃ p ∈ M.trans a.1 (M.reading a.2), p.1 = b.1 ∧ ∀ j, (p.2 j).Holds a.2 j (b.2 j)

/-- The automaton accepts the structure when an accepting state is reachable
from an initial configuration – the initial state with every head on the least
element. -/
def Accepts (A : Type) [L.Structure A] [LinearOrder A] : Prop :=
  ∃ c₀ c : M.Config A, (c₀.1 = M.start ∧ ∀ j, ∀ b : A, c₀.2 j ≤ b) ∧
    Relation.ReflTransGen M.Step c₀ c ∧ M.accept c.1 = true

/-- **The automaton is deterministic**: at most one transition per state and
reading. -/
def IsDeterministic : Prop :=
  ∀ (s : M.State) (r : M.TestIx → Bool), (M.trans s r).length ≤ 1

/-! ### Compiling an automaton into a specification -/

open Classical in
/-- All outcomes the tests may have, as a list: the transition formula is a
disjunction over them. -/
noncomputable def allReadings (T : Type) [Finite T] : List (T → Bool) :=
  letI := Fintype.ofFinite T
  (Finset.univ : Finset (T → Bool)).toList

theorem mem_allReadings {T : Type} [Finite T] (r : T → Bool) : r ∈ allReadings T := by
  classical
  letI := Fintype.ofFinite T
  exact Finset.mem_toList.mpr (Finset.mem_univ r)

open Classical in
/-- The test indices, as a list. -/
noncomputable def allTests : List M.TestIx :=
  letI := Fintype.ofFinite M.TestIx
  (Finset.univ : Finset M.TestIx).toList

theorem mem_allTests (i : M.TestIx) : i ∈ M.allTests := by
  classical
  letI := Fintype.ofFinite M.TestIx
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

/-- The formula saying that the tests come out as `r` does. -/
noncomputable def readingF (r : M.TestIx → Bool) :
    (L.sum Language.order).Formula (Fin k ⊕ Fin k) :=
  listInf (M.allTests.map fun i =>
    if r i then (M.test i).relabel Sum.inl else ∼((M.test i).relabel Sum.inl))

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
    rw [reading]
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

/-- The formula prescribing the moves of every head. -/
noncomputable def movesF (mvs : Fin k → HeadMove k) :
    (L.sum Language.order).Formula (Fin k ⊕ Fin k) :=
  listInf ((List.finRange k).map fun j => (mvs j).toFormula L j)

theorem realize_movesF (mvs : Fin k → HeadMove k) (x y : Fin k → A) :
    (movesF (L := L) mvs).Realize (Sum.elim x y) ↔ ∀ j, (mvs j).Holds x j (y j) := by
  rw [movesF, realize_listInf]
  constructor
  · intro h j
    exact (HeadMove.realize_toFormula j (mvs j) x y).mp
      (h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    exact (HeadMove.realize_toFormula j (mvs j) x y).mpr (h j)

open Classical in
/-- The transition formula of the specification, at a pair of control states:
a disjunction over the possible readings and over the transitions they enable
that land in the second state. -/
noncomputable def stepF (s s' : M.State) :
    (L.sum Language.order).Formula (Fin k ⊕ Fin k) :=
  listSup ((allReadings M.TestIx).map fun r =>
    M.readingF r ⊓
      listSup (((M.trans s r).filter fun p => p.1 = s').map fun p => movesF p.2))

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

open Classical in
/-- **The specification of the automaton's walk**: the control states are the
modes, the heads are the tuple, and the transitions are the step formulas. -/
noncomputable def toSpec : TCSpec L where
  Mode := M.State
  k := k
  step := M.stepF
  src s := if s = M.start then listInf ((List.finRange k).map fun j => minF j) else ⊥
  tgt s := if M.accept s then ⊤ else ⊥

@[simp]
theorem step_toSpec (a b : M.Config A) : M.toSpec.Step a b ↔ M.Step a b :=
  M.realize_stepF a.1 b.1 a.2 b.2

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

theorem isTgt_toSpec (a : M.Config A) : M.toSpec.IsTgt a ↔ M.accept a.1 = true := by
  classical
  change ((if M.accept a.1 then ⊤ else ⊥ : (L.sum Language.order).Formula (Fin k))).Realize
    a.2 ↔ _
  by_cases hs : M.accept a.1 = true
  · rw [if_pos hs]
    exact iff_of_true (Formula.realize_top.mpr trivial) hs
  · rw [if_neg hs, Formula.realize_bot]
    exact iff_of_false id hs

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

/-! ### Membership through an automaton -/

/-- **A problem recognized by a two-way multi-head automaton is FO(TC)
definable** – hence in `DescriptiveComplexity.NL`. The configurations of the automaton
*are* the nodes of the specification: the control is the mode, the heads are the
tuple. -/
theorem tcDefinable_of_automaton {k : ℕ} [L.IsRelational] {P : DecisionProblem L}
    (M : HeadAutomaton L k)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ M.Accepts A) : TCDefinable P := by
  refine ⟨M.toSpec, ?_⟩
  intro A _ _ _ _
  exact (h A).trans (M.accepts_toSpec).symm

/-- **A problem recognized by a *deterministic* two-way multi-head automaton is
FO(DTC) definable** – hence in `DescriptiveComplexity.LOGSPACE`. Determinism of the
control is exactly what makes the walk functional, so its determinization
changes nothing. -/
theorem dtcDefinable_of_automaton {k : ℕ} [L.IsRelational] {P : DecisionProblem L}
    (M : HeadAutomaton L k)
    (hdet : M.IsDeterministic)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ M.Accepts A) : DTCDefinable P := by
  refine ⟨M.toSpec, ?_⟩
  intro A _ _ _ _
  rw [TCSpec.det_accepts_iff _ (M.functional_toSpec hdet)]
  exact (h A).trans (M.accepts_toSpec).symm

/-- **A problem recognized by a two-way multi-head automaton is in NL**, the
membership tool the compilation provides: exhibiting a machine is usually
easier than writing a specification by hand. -/
theorem mem_NL_of_automaton {k : ℕ} [L.IsRelational] {P : DecisionProblem L} (M : HeadAutomaton L k)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ M.Accepts A) : P ∈ NL :=
  (tcDefinable_iff_mem_NL P).mp (tcDefinable_of_automaton M h)

/-- **A problem recognized by a deterministic two-way multi-head automaton is in
LOGSPACE.** -/
theorem mem_LOGSPACE_of_automaton {k : ℕ} [L.IsRelational] {P : DecisionProblem L}
    (M : HeadAutomaton L k)
    (hdet : M.IsDeterministic)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ M.Accepts A) : P ∈ LOGSPACE :=
  dtcDefinable_of_automaton M hdet h

end DescriptiveComplexity
