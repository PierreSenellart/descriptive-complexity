/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadLex
import DescriptiveComplexity.WalkBudget

/-!
# The capture theorem for L: the deterministic machine of a specification

`DescriptiveComplexity.HeadCapture` builds a machine for an FO(TC) definition by
*guessing*. A deterministic machine may not guess, and this file builds the one
that does not: it **searches** where the other one guesses, and it **counts** so
that a search leading nowhere is abandoned. With it, **FO(DTC) definability is
recognizability by a deterministic two-way multi-head automaton**
(`DescriptiveComplexity.dtcDefinable_iff_automaton`,
`DescriptiveComplexity.mem_LOGSPACE_iff_automaton`), the deterministic counterpart of
`DescriptiveComplexity.tcDefinable_iff_automaton`.

## Where the deterministic machine differs

Both machines simulate the walk of a specification, holding the current tuple on
one block of heads and a candidate on another, with the mode in the control.
Three things change.

* **The candidate is scanned, not guessed.** The walk being deterministic
  (`DescriptiveComplexity.TCSpec.det_functional`), a node has at most one successor, so
  the machine may look for it: `DescriptiveComplexity.HeadProgram.lexNextP` walks the
  candidate block through every tuple in turn, and the transition formula is
  evaluated at each. The tuple that passes *is* the successor.
* **The source is scanned too**, on a third block, and the machine keeps it
  there: when a walk leads nowhere it comes back and takes the next source.
* **The walk is given a budget.** A deterministic walk that does not reach an
  accepting node cycles, and a machine following it would never come back. So
  the machine counts its steps on a fourth block – with a mode in the control,
  giving exactly as many counter values as the specification has nodes – and
  abandons the source when the counter overflows. That this is enough is
  `DescriptiveComplexity.exists_iterate_lt_card`: a node reachable along a functional
  relation is reachable in fewer steps than the type has elements.

Every block needs to know when a head is at the greatest element, which is not a
quantifier-free fact of one head; so one further head is parked there once and
for all (`DescriptiveComplexity.HeadProgram.dmk`), shared by the three odometers as
their marker.

## The machine, and the half that says it never lies

`DescriptiveComplexity.HeadProgram.DetNode` (the control graph),
`DescriptiveComplexity.HeadProgram.dFam` and `DescriptiveComplexity.HeadProgram.dWire` (its
fragments and its arcs), `DescriptiveComplexity.HeadProgram.dP` (the machine), the
layout of the heads with the fact that the protected heads are exactly the four
blocks and the marker (`DescriptiveComplexity.HeadProgram.dHeadAgree_iff`), the
relations its fragments run (`DescriptiveComplexity.HeadProgram.dRel`) with all of them
proved (`DescriptiveComplexity.HeadProgram.runs_dFam`) and local
(`DescriptiveComplexity.HeadProgram.headLocal2_dRel`), and **soundness**:
`DescriptiveComplexity.HeadProgram.dInv` – at any node of the walk phase the tuple on
the first block is a node of the specification reachable from a source, and at
`commit` the candidate is one deterministic step away – is carried along every
arc (`DescriptiveComplexity.HeadProgram.dInv_of_walk`), and at the accepting arc it
says that the specification accepts
(`DescriptiveComplexity.HeadProgram.accepts_of_dExit`).

## The search for the successor

It is proved in full, and both ways. Over
the tuples of one mode – `DescriptiveComplexity.HeadProgram.scanFound` (if the current
node's successor, unique by `DescriptiveComplexity.TCSpec.det_step_iff`, is in the mode
being tried with a tuple at or above the block's, the scan walks the block up to
it and reaches `commit` holding it) and
`DescriptiveComplexity.HeadProgram.scanNone` (if there is no successor in that mode,
the scan runs the block to its greatest tuple and moves on) – both inductions
downwards along the lexicographic order, in the style of
`DescriptiveComplexity.HeadProgram.decides_scanP`. And over the chain of modes –
`DescriptiveComplexity.HeadProgram.modeFound` and
`DescriptiveComplexity.HeadProgram.modeNone`, inductions on the number of mode indices
left. So from `candMode` the machine provably reaches `commit` holding the
successor when there is one, and `srcNext` when there is none, in both cases
leaving the current tuple, the source and the counter as they were.

One **step of the simulated walk** follows (`DescriptiveComplexity.HeadProgram.walkStep`)
– at a node that is not accepting but has a successor, with a counter block that
can still be stepped, the machine tests the target formula, searches out the
successor, commits it onto the current block and ticks, arriving at `tgtTest`
one node along with the counter's tuple advanced by one in the lexicographic
order.

## The counter, and the two ways a walk ends

The counter is read as a value of one finite linear order
(`DescriptiveComplexity.HeadProgram.dcount`): the index of its mode, lexicographically
above the tuple on its block. This is the whole of the budget argument, because
a **tick is a cover** in that order – `dcount_covBy_tup` where the tuple can be
stepped, `dcount_covBy_mode` where it cannot and the machine resets it and moves
to the next counter mode – and because the order has **exactly as many elements
as the specification has nodes** (`DescriptiveComplexity.HeadProgram.card_dcount`),
which is the number `DescriptiveComplexity.exists_iterate_lt_card` bounds a walk by.
`DescriptiveComplexity.HeadProgram.dTick` packages one tick: at a node that is neither
accepting nor stuck, with a cover above the counter, the machine moves to the
successor and its counter to that cover.

A walk then ends in one of two ways, and both are proved:

* `DescriptiveComplexity.HeadProgram.walkAcc` – **if the walk reaches an accepting node
  within the budget, the machine accepts**: an induction on the number of steps
  left, `Ticks` supplying the cover `dTick` needs at each of them;
* `DescriptiveComplexity.HeadProgram.walkOut` – **whatever the specification does, the
  machine comes back**: it accepts, or it reaches `srcNext` with its source
  block untouched. This is an induction *downwards along the counter's order*
  (`DescriptiveComplexity.order_induction_down`), the measure being the counter itself;
  at the top of the order the tuple is greatest and the mode last, so the tick
  fails and `tickReset` falls through to the next source
  (`DescriptiveComplexity.HeadProgram.dcount_of_isTop`), and where the walk is stuck
  `DescriptiveComplexity.HeadProgram.walkStuck` reaches `srcNext` through the exhausted
  chain of candidate modes.

## The source enumeration, and the theorem

`DescriptiveComplexity.HeadProgram.srcEnum` walks the sources in the same order –
mode index above source tuple – downwards from any position at or below the
source the specification accepts from: at each position the machine either
accepts (`walkAcc`, when the position *is* that source) or comes back to
`srcNext` (`DescriptiveComplexity.HeadProgram.srcTried`, which is `walkOut` with the
`start` arc in front of it), and the odometer of `DescriptiveComplexity.HeadLex` then
advances the position by exactly one cover – stepping the tuple, or resetting it
and taking the next source mode.

`DescriptiveComplexity.HeadProgram.accepts_dP` conjoins the two halves: the machine
accepts exactly what the determinized specification does. Its fragments are
evaluators, odometers and moves, all deterministic, so the program is
(`DescriptiveComplexity.HeadProgram.deterministic_dP`) and
`DescriptiveComplexity.HeadProgram.compile true` – at most one enabled transition per
reading whatever the guards, and agreeing with the program where they are
exclusive – gives a machine that `DescriptiveComplexity.HeadAutomaton.IsDeterministic`
holds of on the nose. `DescriptiveComplexity.dtcDefinable_of_automaton` closes the
loop.

-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace HeadProgram

variable {L : Language.{0, 0}}

/-! ### The control graph -/

/-- The control nodes of the deterministic machine. Besides what it is doing,
a node carries the source mode `ms` it is walking from, the current mode `m`,
and the mode component `cm` of the step counter. -/
inductive DetNode (M : Type) (r : ℕ)
  /-- Park the marker at the greatest element and start the source scan. -/
  | init : DetNode M r
  /-- Dispatch on the source mode of index `i`. -/
  | srcMode (i : Fin (r + 1)) : DetNode M r
  /-- Test the source formula of `ms` on the source block. -/
  | srcTest (ms : M) : DetNode M r
  /-- Step the source block to the next tuple. -/
  | srcNext (ms : M) : DetNode M r
  /-- Reset the source block and move on to the next source mode. -/
  | srcReset (ms : M) : DetNode M r
  /-- Copy the source onto the current block and reset the counter. -/
  | start (ms : M) : DetNode M r
  /-- Test the target formula of `m` on the current block. -/
  | tgtTest (ms m cm : M) : DetNode M r
  /-- Reset the candidate block and dispatch on the candidate mode of index `i`. -/
  | candMode (ms m cm : M) (i : Fin (r + 1)) : DetNode M r
  /-- Test the transition formula from `m` to `m'`. -/
  | candTest (ms m cm m' : M) : DetNode M r
  /-- Step the candidate block to the next tuple. -/
  | candNext (ms m cm m' : M) : DetNode M r
  /-- Copy the candidate onto the current block. -/
  | commit (ms m cm m' : M) : DetNode M r
  /-- Step the counter. -/
  | tick (ms m cm : M) : DetNode M r
  /-- Reset the counter block and step its mode component. -/
  | tickReset (ms m cm : M) : DetNode M r
  /-- Nothing more to do. -/
  | dead : DetNode M r

instance {M : Type} [Finite M] {r : ℕ} : Finite (DetNode M r) := by
  classical
  refine Finite.of_injective (fun c : DetNode M r => match c with
      | .init => Sum.inl (Sum.inl ())
      | .srcMode i => Sum.inl (Sum.inr (Sum.inl i))
      | .srcTest ms => Sum.inl (Sum.inr (Sum.inr (Sum.inl ms)))
      | .srcNext ms => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl ms))))
      | .srcReset ms => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ms)))))
      | .start ms => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ms)))))
      | .tgtTest ms m cm => Sum.inr (Sum.inl (ms, m, cm))
      | .candMode ms m cm i => Sum.inr (Sum.inr (Sum.inl (ms, m, cm, i)))
      | .candTest ms m cm m' => Sum.inr (Sum.inr (Sum.inr (Sum.inl (ms, m, cm, m'))))
      | .candNext ms m cm m' => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (ms, m, cm, m')))))
      | .commit ms m cm m' =>
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (ms, m, cm, m'))))))
      | .tick ms m cm =>
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (ms, m, cm)))))))
      | .tickReset ms m cm =>
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (ms, m, cm))))))))
      | .dead =>
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))))) :
    DetNode M r → (Unit ⊕ Fin (r + 1) ⊕ M ⊕ M ⊕ M ⊕ M) ⊕
      (M × M × M) ⊕ (M × M × M × Fin (r + 1)) ⊕ (M × M × M × M) ⊕ (M × M × M × M) ⊕
      (M × M × M × M) ⊕ (M × M × M) ⊕ (M × M × M) ⊕ Unit) ?_
  rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _)
    (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) h <;> simp_all

/-! ### Evaluating a formula on any block -/

section Eval

variable {K : ℕ} {α A : Type} [L.Structure A] [LinearOrder A] [Finite A]

/-- The evaluator, with the formula's variables read off any heads below the
protected level. -/
theorem decides_evalFormula (sh : ℕ → Fin K) (hsh : ∀ i : ℕ, i < K → ((sh i : Fin K) : ℕ) = i)
    (prot : ℕ) (φ : (L.sum Language.order).Formula α) (hv : α → Fin K)
    (hlow : ∀ a, ((hv a : Fin K) : ℕ) < prot) (hK : prot + qdepth φ ≤ K) :
    (evalP sh prot (Sum.elim hv Fin.elim0) φ).Decides A prot
      fun x => φ.Realize fun a => x (hv a) := by
  refine (decides_evalP sh hsh φ prot (Sum.elim hv Fin.elim0) ?_ hK).congr fun x => ?_
  · rintro (a | i)
    · exact hlow a
    · exact i.elim0
  · exact iff_of_eq (congrArg (BoundedFormula.Realize φ fun a => x (hv a))
      (funext fun i => i.elim0))

end Eval

/-! ### The layout of the heads -/

section Layout

variable (spec : TCSpec L)

/-- **How many heads the deterministic machine has**: four blocks – current
tuple, candidate, source, counter – a marker parked at the greatest element, the
evaluator's workspace, and a spare. -/
noncomputable def dHeads : ℕ := 4 * spec.k + specDepth spec.det + 2

/-- The heads the machine's fragments must give back untouched. -/
noncomputable def dprot : ℕ := 4 * spec.k + 1

theorem dprot_lt_dHeads : dprot spec < dHeads spec := by
  rw [dprot, dHeads]
  omega

/-- Block `t` of the machine's heads: `0` the current tuple, `1` the candidate,
`2` the source, `3` the counter. -/
noncomputable def dblk (t : Fin 4) (i : Fin spec.k) : Fin (dHeads spec) :=
  ⟨(t : ℕ) * spec.k + i, by
    have h1 := t.isLt
    have h2 := i.isLt
    rw [dHeads]
    have : (t : ℕ) * spec.k + (i : ℕ) < 4 * spec.k := by
      calc (t : ℕ) * spec.k + (i : ℕ) < (t : ℕ) * spec.k + spec.k := by omega
        _ = ((t : ℕ) + 1) * spec.k := by ring
        _ ≤ 4 * spec.k := Nat.mul_le_mul_right _ (by omega)
    omega⟩

/-- The marker head, parked at the greatest element. -/
noncomputable def dmk : Fin (dHeads spec) := ⟨4 * spec.k, by rw [dHeads]; omega⟩

/-- The head at a given index. -/
noncomputable def dshd (i : ℕ) : Fin (dHeads spec) :=
  if h : i < dHeads spec then ⟨i, h⟩ else ⟨0, by rw [dHeads]; omega⟩

@[simp]
theorem dblk_val (t : Fin 4) (i : Fin spec.k) :
    ((dblk spec t i : Fin (dHeads spec)) : ℕ) = (t : ℕ) * spec.k + (i : ℕ) := rfl

@[simp]
theorem dmk_val : ((dmk spec : Fin (dHeads spec)) : ℕ) = 4 * spec.k := rfl

theorem dshd_val {i : ℕ} (h : i < dHeads spec) : ((dshd spec i : Fin (dHeads spec)) : ℕ) = i := by
  rw [dshd, dif_pos h]

theorem dshd_val' : ∀ i : ℕ, i < dHeads spec → ((dshd spec i : Fin (dHeads spec)) : ℕ) = i :=
  fun _ h => dshd_val spec h

theorem dblk_lt (t : Fin 4) (i : Fin spec.k) :
    ((dblk spec t i : Fin (dHeads spec)) : ℕ) < 4 * spec.k := by
  have h1 := t.isLt
  have h2 := i.isLt
  rw [dblk_val]
  calc (t : ℕ) * spec.k + (i : ℕ) < (t : ℕ) * spec.k + spec.k := by omega
    _ = ((t : ℕ) + 1) * spec.k := by ring
    _ ≤ 4 * spec.k := Nat.mul_le_mul_right _ (by omega)

theorem dblk_lt_prot (t : Fin 4) (i : Fin spec.k) :
    ((dblk spec t i : Fin (dHeads spec)) : ℕ) < dprot spec :=
  lt_trans (dblk_lt spec t i) (by rw [dprot]; omega)

theorem dmk_lt_prot : ((dmk spec : Fin (dHeads spec)) : ℕ) < dprot spec := by
  rw [dmk_val, dprot]
  omega

theorem dblk_inj (t : Fin 4) : Function.Injective (dblk spec t) := by
  intro i j h
  have := congrArg (fun z : Fin (dHeads spec) => (z : ℕ)) h
  rw [dblk_val, dblk_val] at this
  exact Fin.ext (by omega)

theorem dblk_ne_dmk (t : Fin 4) (i : Fin spec.k) : dblk spec t i ≠ dmk spec := by
  intro h
  have := congrArg (fun z : Fin (dHeads spec) => (z : ℕ)) h
  rw [dblk_val, dmk_val] at this
  have := dblk_lt spec t i
  rw [dblk_val] at this
  omega

/-- The tuple block `t` holds. -/
noncomputable def dTup {A : Type} (t : Fin 4) (x : Fin (dHeads spec) → A) : Fin spec.k → A :=
  fun i => x (dblk spec t i)

variable {A : Type}

/-- **The protected heads are exactly the four blocks and the marker**: there is
nothing else below the protected level. -/
theorem dHeadAgree_iff {x y : Fin (dHeads spec) → A} :
    HeadAgree (dprot spec) x y ↔
      (∀ (t : Fin 4) (i : Fin spec.k), x (dblk spec t i) = y (dblk spec t i)) ∧
        x (dmk spec) = y (dmk spec) := by
  constructor
  · intro h
    exact ⟨fun t i => h _ (dblk_lt_prot spec t i), h _ (dmk_lt_prot spec)⟩
  · rintro ⟨hb, hm⟩ j hj
    rw [dprot] at hj
    by_cases hjm : (j : ℕ) = 4 * spec.k
    · have : j = dmk spec := Fin.ext (by rw [dmk_val, hjm])
      rw [this]
      exact hm
    · have hjlt : (j : ℕ) < 4 * spec.k := by omega
      have hk : 0 < spec.k := by
        by_contra hcon
        have : spec.k = 0 := by omega
        rw [this] at hjlt
        omega
      have ht : (j : ℕ) / spec.k < 4 := by
        by_contra hcon
        have : 4 * spec.k ≤ (j : ℕ) := by
          calc 4 * spec.k ≤ ((j : ℕ) / spec.k) * spec.k := Nat.mul_le_mul_right _ (by omega)
            _ ≤ (j : ℕ) := Nat.div_mul_le_self _ _
        omega
      have hi : (j : ℕ) % spec.k < spec.k := Nat.mod_lt _ hk
      have hje : j = dblk spec ⟨(j : ℕ) / spec.k, ht⟩ ⟨(j : ℕ) % spec.k, hi⟩ := by
        refine Fin.ext ?_
        rw [dblk_val]
        change (j : ℕ) = (j : ℕ) / spec.k * spec.k + (j : ℕ) % spec.k
        have := Nat.div_add_mod (j : ℕ) spec.k
        rw [Nat.mul_comm] at this
        omega
      rw [hje]
      exact hb _ _

/-- Everything but block `t` is where it was. -/
def dKeepBut (t : Fin 4) (x y : Fin (dHeads spec) → A) : Prop :=
  (∀ (t' : Fin 4) (i : Fin spec.k), t' ≠ t → y (dblk spec t' i) = x (dblk spec t' i)) ∧
    y (dmk spec) = x (dmk spec)

end Layout

/-! ### The moves -/

section Moves

variable (spec : TCSpec L)

theorem dblk_range (t : Fin 4) (i : Fin spec.k) :
    (t : ℕ) * spec.k ≤ ((dblk spec t i : Fin (dHeads spec)) : ℕ) ∧
      ((dblk spec t i : Fin (dHeads spec)) : ℕ) < (t : ℕ) * spec.k + spec.k := by
  rw [dblk_val]
  have := i.isLt
  omega

theorem dblk_notMem_range {t t' : Fin 4} (i : Fin spec.k) (h : t' ≠ t) :
    ¬((t : ℕ) * spec.k ≤ ((dblk spec t' i : Fin (dHeads spec)) : ℕ) ∧
      ((dblk spec t' i : Fin (dHeads spec)) : ℕ) < (t : ℕ) * spec.k + spec.k) := by
  rw [dblk_val]
  have hi := i.isLt
  have hne : (t' : ℕ) ≠ (t : ℕ) := fun he => h (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (t' : ℕ) * spec.k + spec.k ≤ (t : ℕ) * spec.k := by
      calc (t' : ℕ) * spec.k + spec.k = ((t' : ℕ) + 1) * spec.k := by ring
        _ ≤ (t : ℕ) * spec.k := Nat.mul_le_mul_right _ (by omega)
    omega
  · have : (t : ℕ) * spec.k + spec.k ≤ (t' : ℕ) * spec.k := by
      calc (t : ℕ) * spec.k + spec.k = ((t : ℕ) + 1) * spec.k := by ring
        _ ≤ (t' : ℕ) * spec.k := Nat.mul_le_mul_right _ (by omega)
    omega

theorem dmk_notMem_range (t : Fin 4) :
    ¬((t : ℕ) * spec.k ≤ ((dmk spec : Fin (dHeads spec)) : ℕ) ∧
      ((dmk spec : Fin (dHeads spec)) : ℕ) < (t : ℕ) * spec.k + spec.k) := by
  rw [dmk_val]
  have ht := t.isLt
  have : (t : ℕ) * spec.k + spec.k ≤ 4 * spec.k := by
    calc (t : ℕ) * spec.k + spec.k = ((t : ℕ) + 1) * spec.k := by ring
      _ ≤ 4 * spec.k := Nat.mul_le_mul_right _ (by omega)
  omega

theorem high_notMem_range (t : Fin 4) {h : Fin (dHeads spec)} (hh : dprot spec ≤ (h : ℕ)) :
    ¬((t : ℕ) * spec.k ≤ (h : ℕ) ∧ (h : ℕ) < (t : ℕ) * spec.k + spec.k) := by
  have ht := t.isLt
  have hle : (t : ℕ) * spec.k + spec.k ≤ 4 * spec.k := by
    calc (t : ℕ) * spec.k + spec.k = ((t : ℕ) + 1) * spec.k := by ring
      _ ≤ 4 * spec.k := Nat.mul_le_mul_right _ (by omega)
  rw [dprot] at hh
  omega

/-- The moves that park the marker at the greatest element. -/
noncomputable def dParkMoves : Fin (dHeads spec) → HeadMove (dHeads spec) :=
  fun h => if (h : ℕ) = 4 * spec.k then .toMax else .stay

/-- The moves that send block `t` to the least element. -/
noncomputable def dResetMoves (t : Fin 4) : Fin (dHeads spec) → HeadMove (dHeads spec) :=
  fun h => if (t : ℕ) * spec.k ≤ (h : ℕ) ∧ (h : ℕ) < (t : ℕ) * spec.k + spec.k then .toMin
    else .stay

/-- The moves that copy block `t` onto block `0`. -/
noncomputable def dCopyMoves (t : Fin 4) : Fin (dHeads spec) → HeadMove (dHeads spec) :=
  fun h => if (h : ℕ) < spec.k then .copy (dshd spec ((t : ℕ) * spec.k + (h : ℕ))) else .stay

/-- The moves that start a walk: the source onto the current block, and the
counter back to the least tuple. -/
noncomputable def dStartMoves : Fin (dHeads spec) → HeadMove (dHeads spec) :=
  fun h => if (h : ℕ) < spec.k then .copy (dshd spec (2 * spec.k + (h : ℕ)))
    else if 3 * spec.k ≤ (h : ℕ) ∧ (h : ℕ) < 4 * spec.k then .toMin else .stay

theorem dshd_dblk (t : Fin 4) (i : Fin spec.k) :
    dshd spec ((t : ℕ) * spec.k + (i : ℕ)) = dblk spec t i := by
  have hlt : (t : ℕ) * spec.k + (i : ℕ) < dHeads spec := by
    have := dblk_lt spec t i
    rw [dblk_val] at this
    rw [dHeads]
    omega
  exact Fin.ext (by rw [dshd_val spec hlt, dblk_val])

end Moves

/-! ### The machine -/

section Machine

variable (spec : TCSpec L)

/-- The fragments of the deterministic machine. -/
noncomputable def dFam : DetNode spec.Mode (modeCard spec) → HeadProgram L (dHeads spec)
  | .init => moveP (dParkMoves spec)
  | .srcMode _ => exitP true
  | .srcTest ms =>
      evalP (dshd spec) (dprot spec) (Sum.elim (dblk spec 2) Fin.elim0) (spec.src ms)
  | .srcNext _ => lexNextP (dblk spec 2) (dmk spec)
  | .srcReset _ => moveP (dResetMoves spec 2)
  | .start _ => moveP (dStartMoves spec)
  | .tgtTest _ m _ =>
      evalP (dshd spec) (dprot spec) (Sum.elim (dblk spec 0) Fin.elim0) (spec.tgt m)
  | .candMode _ _ _ _ => moveP (dResetMoves spec 1)
  | .candTest _ m _ m' => evalP (dshd spec) (dprot spec)
      (Sum.elim (Sum.elim (dblk spec 0) (dblk spec 1)) Fin.elim0) (spec.detStep m m')
  | .candNext _ _ _ _ => lexNextP (dblk spec 1) (dmk spec)
  | .commit _ _ _ _ => moveP (dCopyMoves spec 1)
  | .tick _ _ _ => lexNextP (dblk spec 3) (dmk spec)
  | .tickReset _ _ _ => moveP (dResetMoves spec 3)
  | .dead => exitP false

/-- Where the deterministic machine goes when a fragment exits. -/
noncomputable def dWire : DetNode spec.Mode (modeCard spec) → Bool →
    DetNode spec.Mode (modeCard spec) ⊕ Bool
  | .init, _ => Sum.inl (.srcMode (ix0 spec))
  | .srcMode i, _ => Sum.inl ((modeAt spec i).elim .dead .srcTest)
  | .srcTest ms, true => Sum.inl (.start ms)
  | .srcTest ms, false => Sum.inl (.srcNext ms)
  | .srcNext ms, true => Sum.inl (.srcTest ms)
  | .srcNext ms, false => Sum.inl (.srcReset ms)
  | .srcReset ms, _ => Sum.inl (.srcMode (nextIx spec (ixOf spec ms)))
  | .start ms, _ =>
      Sum.inl ((modeAt spec (ix0 spec)).elim .dead fun cm => .tgtTest ms ms cm)
  | .tgtTest _ _ _, true => Sum.inr true
  | .tgtTest ms m cm, false => Sum.inl (.candMode ms m cm (ix0 spec))
  | .candMode ms m cm i, _ =>
      Sum.inl ((modeAt spec i).elim (.srcNext ms) fun m' => .candTest ms m cm m')
  | .candTest ms m cm m', true => Sum.inl (.commit ms m cm m')
  | .candTest ms m cm m', false => Sum.inl (.candNext ms m cm m')
  | .candNext ms m cm m', true => Sum.inl (.candTest ms m cm m')
  | .candNext ms m cm m', false => Sum.inl (.candMode ms m cm (nextIx spec (ixOf spec m')))
  | .commit ms _ cm m', _ => Sum.inl (.tick ms m' cm)
  | .tick ms m cm, true => Sum.inl (.tgtTest ms m cm)
  | .tick ms m cm, false => Sum.inl (.tickReset ms m cm)
  | .tickReset ms m cm, _ =>
      Sum.inl ((modeAt spec (nextIx spec (ixOf spec cm))).elim (.srcNext ms)
        fun cm' => .tgtTest ms m cm')
  | .dead, _ => Sum.inr false

/-- **The deterministic machine of a specification.** -/
noncomputable def dP : HeadProgram L (dHeads spec) := wireP (dFam spec) (dWire spec) .init

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]

/-- What the fragments of the deterministic machine run. -/
noncomputable def dRel : DetNode spec.Mode (modeCard spec) → (Fin (dHeads spec) → A) → Bool →
    (Fin (dHeads spec) → A) → Prop
  | .init => fun x b y => b = true ∧ (∀ a : A, a ≤ y (dmk spec)) ∧
      ∀ (t : Fin 4) (i : Fin spec.k), y (dblk spec t i) = x (dblk spec t i)
  | .srcMode _ => fun x b y => b = true ∧ HeadAgree (dprot spec) x y
  | .srcTest ms => fun x b y => (b = true ↔ spec.IsSrc (ms, dTup spec 2 x)) ∧
      HeadAgree (dprot spec) x y
  | .srcNext _ => lexRel (dblk spec 2) (dmk spec) (dprot spec)
  | .srcReset _ => fun x b y => b = true ∧ (∀ (i : Fin spec.k) (a : A), y (dblk spec 2 i) ≤ a) ∧
      dKeepBut spec 2 x y
  | .start _ => fun x b y => b = true ∧ (∀ i, y (dblk spec 0 i) = x (dblk spec 2 i)) ∧
      (∀ (i : Fin spec.k) (a : A), y (dblk spec 3 i) ≤ a) ∧
      (∀ (t : Fin 4) (i : Fin spec.k), t ≠ 0 → t ≠ 3 → y (dblk spec t i) = x (dblk spec t i)) ∧
      y (dmk spec) = x (dmk spec)
  | .tgtTest _ m _ => fun x b y => (b = true ↔ spec.IsTgt (m, dTup spec 0 x)) ∧
      HeadAgree (dprot spec) x y
  | .candMode _ _ _ _ => fun x b y => b = true ∧
      (∀ (i : Fin spec.k) (a : A), y (dblk spec 1 i) ≤ a) ∧ dKeepBut spec 1 x y
  | .candTest _ m _ m' => fun x b y =>
      (b = true ↔ spec.det.Step (m, dTup spec 0 x) (m', dTup spec 1 x)) ∧
        HeadAgree (dprot spec) x y
  | .candNext _ _ _ _ => lexRel (dblk spec 1) (dmk spec) (dprot spec)
  | .commit _ _ _ _ => fun x b y => b = true ∧ (∀ i, y (dblk spec 0 i) = x (dblk spec 1 i)) ∧
      dKeepBut spec 0 x y
  | .tick _ _ _ => lexRel (dblk spec 3) (dmk spec) (dprot spec)
  | .tickReset _ _ _ => fun x b y => b = true ∧
      (∀ (i : Fin spec.k) (a : A), y (dblk spec 3 i) ≤ a) ∧ dKeepBut spec 3 x y
  | .dead => fun x b y => b = false ∧ HeadAgree (dprot spec) x y

/-! ### What the fragments run -/

omit [Finite A] in
theorem runs_resetP (t : Fin 4) :
    (moveP (L := L) (dResetMoves spec t)).Runs A (dprot spec) fun x b y => b = true ∧
      (∀ (i : Fin spec.k) (a : A), y (dblk spec t i) ≤ a) ∧ dKeepBut spec t x y := by
  refine (runs_moveP_local (dResetMoves spec t) (dprot spec) fun h hh => ?_).mono ?_ ?_
  · rw [dResetMoves, if_neg (high_notMem_range spec t hh)]
  · rintro x b y ⟨rfl, hmv⟩
    refine ⟨rfl, fun i a => ?_, fun t' i ht' => ?_, ?_⟩
    · have hx := hmv (dblk spec t i) (dblk_lt_prot spec t i)
      rw [dResetMoves, if_pos (dblk_range spec t i)] at hx
      exact hx a
    · have hx := hmv (dblk spec t' i) (dblk_lt_prot spec t' i)
      rw [dResetMoves, if_neg (dblk_notMem_range spec i ht')] at hx
      exact hx
    · have hx := hmv (dmk spec) (dmk_lt_prot spec)
      rw [dResetMoves, if_neg (dmk_notMem_range spec t)] at hx
      exact hx
  · rintro x b y ⟨rfl, hmin, hkeep, hkmk⟩
    classical
    refine ⟨fun h => if (t : ℕ) * spec.k ≤ (h : ℕ) ∧ (h : ℕ) < (t : ℕ) * spec.k + spec.k
      then y h else x h, ?_, rfl, fun j hj => ?_⟩
    · refine dHeadAgree_iff spec |>.mpr ⟨fun t' i => ?_, ?_⟩
      · by_cases ht' : t' = t
        · rw [ht', if_pos (dblk_range spec t i)]
        · rw [if_neg (dblk_notMem_range spec i ht')]
          exact hkeep t' i ht'
      · rw [if_neg (dmk_notMem_range spec t)]
        exact hkmk
    · change (dResetMoves spec t j).Holds x j
        (if (t : ℕ) * spec.k ≤ (j : ℕ) ∧ (j : ℕ) < (t : ℕ) * spec.k + spec.k then y j else x j)
      rw [dResetMoves]
      by_cases hin : (t : ℕ) * spec.k ≤ (j : ℕ) ∧ (j : ℕ) < (t : ℕ) * spec.k + spec.k
      · rw [if_pos hin, if_pos hin]
        intro a
        have hk : 0 < spec.k := by omega
        have hi : (j : ℕ) - (t : ℕ) * spec.k < spec.k := by omega
        have hje : j = dblk spec t ⟨(j : ℕ) - (t : ℕ) * spec.k, hi⟩ := by
          refine Fin.ext ?_
          rw [dblk_val]
          change (j : ℕ) = (t : ℕ) * spec.k + ((j : ℕ) - (t : ℕ) * spec.k)
          omega
        rw [hje]
        exact hmin _ a
      · rw [if_neg hin, if_neg hin]
        rfl

omit [Finite A] in
theorem runs_copyP :
    (moveP (L := L) (dCopyMoves spec 1)).Runs A (dprot spec) fun x b y => b = true ∧
      (∀ i, y (dblk spec 0 i) = x (dblk spec 1 i)) ∧ dKeepBut spec 0 x y := by
  refine (runs_moveP_local (dCopyMoves spec 1) (dprot spec) fun h hh => ?_).mono ?_ ?_
  · rw [dCopyMoves, if_neg (by
      have := high_notMem_range spec 0 hh
      simp only [Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.zero_le, true_and] at this
      omega)]
  · rintro x b y ⟨rfl, hmv⟩
    refine ⟨rfl, fun i => ?_, fun t' i ht' => ?_, ?_⟩
    · have hx := hmv (dblk spec 0 i) (dblk_lt_prot spec 0 i)
      rw [dCopyMoves, if_pos (by simp)] at hx
      rw [hx]
      exact congrArg x (by rw [← dshd_dblk spec 1 i]; simp)
    · have hx := hmv (dblk spec t' i) (dblk_lt_prot spec t' i)
      rw [dCopyMoves, if_neg (by
        have := dblk_notMem_range spec (t := 0) i ht'
        simp only [Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.zero_le, true_and] at this
        omega)] at hx
      exact hx
    · have hx := hmv (dmk spec) (dmk_lt_prot spec)
      rw [dCopyMoves, if_neg (by
        have := dmk_notMem_range spec 0
        simp only [Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.zero_le, true_and] at this
        omega)] at hx
      exact hx
  · rintro x b y ⟨rfl, hcopy, hkeep, hkmk⟩
    classical
    refine ⟨fun h => if (h : ℕ) < spec.k then y h else x h, ?_, rfl, fun j hj => ?_⟩
    · refine dHeadAgree_iff spec |>.mpr ⟨fun t' i => ?_, ?_⟩
      · by_cases ht' : t' = 0
        · rw [ht', if_pos (by simp)]
        · rw [if_neg (by
            have := dblk_notMem_range spec (t := 0) i ht'
            simp only [Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.zero_le, true_and] at this
            omega)]
          exact hkeep t' i ht'
      · rw [if_neg (by
          have := dmk_notMem_range spec 0
          simp only [Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.zero_le, true_and] at this
          omega)]
        exact hkmk
    · change (dCopyMoves spec 1 j).Holds x j (if (j : ℕ) < spec.k then y j else x j)
      rw [dCopyMoves]
      by_cases hin : (j : ℕ) < spec.k
      · rw [if_pos hin, if_pos hin]
        have hje : j = dblk spec 0 ⟨(j : ℕ), hin⟩ := Fin.ext (by rw [dblk_val]; simp)
        rw [hje, hcopy ⟨(j : ℕ), hin⟩]
        exact congrArg x (by rw [← dshd_dblk spec 1 ⟨(j : ℕ), hin⟩]; simp)
      · rw [if_neg hin, if_neg hin]
        rfl

omit [Finite A] in
theorem dblk_of_range {t : Fin 4} {j : Fin (dHeads spec)} (h1 : (t : ℕ) * spec.k ≤ (j : ℕ))
    (h2 : (j : ℕ) < (t : ℕ) * spec.k + spec.k) : ∃ i : Fin spec.k, j = dblk spec t i := by
  have hi : (j : ℕ) - (t : ℕ) * spec.k < spec.k := by omega
  refine ⟨⟨_, hi⟩, Fin.ext ?_⟩
  rw [dblk_val]
  change (j : ℕ) = (t : ℕ) * spec.k + ((j : ℕ) - (t : ℕ) * spec.k)
  omega

omit [Finite A] in
theorem runs_parkP : (moveP (L := L) (dParkMoves spec)).Runs A (dprot spec) (dRel spec .init) := by
  refine (runs_moveP_local (dParkMoves spec) (dprot spec) fun h hh => ?_).mono ?_ ?_
  · rw [dprot] at hh
    rw [dParkMoves, if_neg (by omega)]
  · rintro x b y ⟨rfl, hmv⟩
    refine ⟨rfl, ?_, fun t i => ?_⟩
    · have hx := hmv (dmk spec) (dmk_lt_prot spec)
      rw [dParkMoves, if_pos (dmk_val spec)] at hx
      exact hx
    · have hx := hmv (dblk spec t i) (dblk_lt_prot spec t i)
      have hne : ((dblk spec t i : Fin (dHeads spec)) : ℕ) ≠ 4 * spec.k := by
        have := dblk_lt spec t i
        omega
      rw [dParkMoves, if_neg hne] at hx
      exact hx
  · rintro x b y ⟨rfl, hmax, hkeep⟩
    classical
    refine ⟨fun h => if (h : ℕ) = 4 * spec.k then y (dmk spec) else x h, ?_, rfl, fun j hj => ?_⟩
    · refine (dHeadAgree_iff spec).mpr ⟨fun t i => ?_, ?_⟩
      · rw [if_neg (by have := dblk_lt spec t i; omega)]
        exact hkeep t i
      · rw [if_pos (dmk_val spec)]
    · change (dParkMoves spec j).Holds x j (if (j : ℕ) = 4 * spec.k then y (dmk spec) else x j)
      rw [dParkMoves]
      by_cases hjm : (j : ℕ) = 4 * spec.k
      · rw [if_pos hjm, if_pos hjm]
        exact hmax
      · rw [if_neg hjm, if_neg hjm]
        rfl

omit [Finite A] in
theorem runs_startP (ms : spec.Mode) :
    (moveP (L := L) (dStartMoves spec)).Runs A (dprot spec) (dRel spec (.start ms)) := by
  have hk3 : ∀ (t : Fin 4) (i : Fin spec.k), t ≠ 0 → t ≠ 3 →
      ¬((dblk spec t i : Fin (dHeads spec)) : ℕ) < spec.k ∧
        ¬(3 * spec.k ≤ ((dblk spec t i : Fin (dHeads spec)) : ℕ) ∧
          ((dblk spec t i : Fin (dHeads spec)) : ℕ) < 4 * spec.k) := by
    intro t i h0 h3
    have h1 := dblk_notMem_range spec (t := 0) i h0
    have h2 := dblk_notMem_range spec (t := 3) i h3
    simp only [Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.zero_le, true_and,
      Nat.zero_add] at h1
    refine ⟨h1, ?_⟩
    have : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [this] at h2
    omega
  refine (runs_moveP_local (dStartMoves spec) (dprot spec) fun h hh => ?_).mono ?_ ?_
  · rw [dprot] at hh
    rw [dStartMoves, if_neg (by omega), if_neg (by omega)]
  · rintro x b y ⟨rfl, hmv⟩
    refine ⟨rfl, fun i => ?_, fun i a => ?_, fun t i h0 h3 => ?_, ?_⟩
    · have hx := hmv (dblk spec 0 i) (dblk_lt_prot spec 0 i)
      rw [dStartMoves, if_pos (by simp)] at hx
      rw [hx]
      refine congrArg x ?_
      rw [← dshd_dblk spec 2 i]
      simp
    · have hx := hmv (dblk spec 3 i) (dblk_lt_prot spec 3 i)
      have h1 : ¬((dblk spec 3 i : Fin (dHeads spec)) : ℕ) < spec.k := by
        have := dblk_range spec 3 i
        have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
        rw [h3] at this
        omega
      have h2 : 3 * spec.k ≤ ((dblk spec 3 i : Fin (dHeads spec)) : ℕ) ∧
          ((dblk spec 3 i : Fin (dHeads spec)) : ℕ) < 4 * spec.k := by
        have := dblk_range spec 3 i
        have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
        rw [h3] at this
        omega
      rw [dStartMoves, if_neg h1, if_pos h2] at hx
      exact hx a
    · obtain ⟨h1, h2⟩ := hk3 t i h0 h3
      have hx := hmv (dblk spec t i) (dblk_lt_prot spec t i)
      rw [dStartMoves, if_neg h1, if_neg h2] at hx
      exact hx
    · have hx := hmv (dmk spec) (dmk_lt_prot spec)
      rw [dStartMoves, if_neg (by rw [dmk_val]; omega), if_neg (by rw [dmk_val]; omega)] at hx
      exact hx
  · rintro x b y ⟨rfl, hcopy, hmin, hkeep, hkmk⟩
    classical
    refine ⟨fun h => if (h : ℕ) < spec.k ∨ (3 * spec.k ≤ (h : ℕ) ∧ (h : ℕ) < 4 * spec.k)
      then y h else x h, ?_, rfl, fun j hj => ?_⟩
    · refine (dHeadAgree_iff spec).mpr ⟨fun t i => ?_, ?_⟩
      · by_cases h0 : t = 0
        · rw [h0, if_pos (Or.inl (by simp))]
        · by_cases h3 : t = 3
          · refine (if_pos (Or.inr ?_)).symm ▸ rfl
            have := dblk_range spec t i
            rw [h3] at this ⊢
            have h3' : ((3 : Fin 4) : ℕ) = 3 := rfl
            rw [h3'] at this
            omega
          · obtain ⟨h1, h2⟩ := hk3 t i h0 h3
            rw [if_neg (by tauto)]
            exact hkeep t i h0 h3
      · rw [if_neg (by rw [dmk_val]; omega)]
        exact hkmk
    · change (dStartMoves spec j).Holds x j
        (if (j : ℕ) < spec.k ∨ (3 * spec.k ≤ (j : ℕ) ∧ (j : ℕ) < 4 * spec.k) then y j else x j)
      rw [dStartMoves]
      by_cases h1 : (j : ℕ) < spec.k
      · rw [if_pos h1, if_pos (Or.inl h1)]
        obtain ⟨i, rfl⟩ := dblk_of_range spec (t := 0) (by simp) (by simpa using h1)
        rw [hcopy i]
        refine congrArg x ?_
        rw [← dshd_dblk spec 2 i]
        simp
      · rw [if_neg h1]
        by_cases h2 : 3 * spec.k ≤ (j : ℕ) ∧ (j : ℕ) < 4 * spec.k
        · rw [if_pos h2, if_pos (Or.inr h2)]
          obtain ⟨i, rfl⟩ := dblk_of_range spec (t := 3) (by
            have h3' : ((3 : Fin 4) : ℕ) = 3 := rfl
            rw [h3']
            exact h2.1) (by
            have h3' : ((3 : Fin 4) : ℕ) = 3 := rfl
            rw [h3']
            have := h2.2
            omega)
          exact hmin i
        · rw [if_neg h2, if_neg (by tauto)]
          rfl

/-- **The fragments of the deterministic machine run what they are meant to.** -/
theorem runs_dFam (c : DetNode spec.Mode (modeCard spec)) :
    (dFam spec c).Runs A (dprot spec) (dRel spec c) := by
  have hlow01 : ∀ a : Fin spec.k ⊕ Fin spec.k,
      ((Sum.elim (dblk spec 0) (dblk spec 1) a : Fin (dHeads spec)) : ℕ) < dprot spec := by
    rintro (i | i)
    exacts [dblk_lt_prot spec 0 i, dblk_lt_prot spec 1 i]
  have hKsrc : ∀ m, dprot spec + qdepth (spec.src m) ≤ dHeads spec := by
    intro m
    have hq : qdepth (spec.src m) ≤ specDepth spec.det := qdepth_src_le spec.det m
    rw [dprot, dHeads]
    omega
  have hKtgt : ∀ m, dprot spec + qdepth (spec.tgt m) ≤ dHeads spec := by
    intro m
    have hq : qdepth (spec.tgt m) ≤ specDepth spec.det := qdepth_tgt_le spec.det m
    rw [dprot, dHeads]
    omega
  have hKstep : ∀ m m', dprot spec + qdepth (spec.detStep m m') ≤ dHeads spec := by
    intro m m'
    have hq : qdepth (spec.detStep m m') ≤ specDepth spec.det := qdepth_step_le spec.det m m'
    rw [dprot, dHeads]
    omega
  cases c with
  | init => exact runs_parkP spec
  | srcMode i => exact runs_exitP_local true (dprot spec)
  | srcTest ms =>
    exact decides_evalFormula (dshd spec) (dshd_val' spec) (dprot spec) (spec.src ms)
      (dblk spec 2) (dblk_lt_prot spec 2) (hKsrc ms)
  | srcNext ms => exact runs_lexNextP (dblk_inj spec 2) (dblk_lt_prot spec 2) (dmk_lt_prot spec)
  | srcReset ms => exact runs_resetP spec 2
  | start ms => exact runs_startP spec ms
  | tgtTest ms m cm =>
    exact decides_evalFormula (dshd spec) (dshd_val' spec) (dprot spec) (spec.tgt m)
      (dblk spec 0) (dblk_lt_prot spec 0) (hKtgt m)
  | candMode ms m cm i => exact runs_resetP spec 1
  | candTest ms m cm m' =>
    refine (decides_evalFormula (dshd spec) (dshd_val' spec) (dprot spec) (spec.detStep m m')
      (Sum.elim (dblk spec 0) (dblk spec 1)) hlow01 (hKstep m m')).congr fun x => ?_
    change ((spec.detStep m m').Realize fun a => x (Sum.elim (dblk spec 0) (dblk spec 1) a)) ↔
      (spec.detStep m m').Realize (Sum.elim (dTup spec 0 x) (dTup spec 1 x))
    refine iff_of_eq (congrArg
      (fun v : (Fin spec.k ⊕ Fin spec.k) → A => (spec.detStep m m').Realize v) ?_)
    funext a
    rcases a with i | i <;> rfl
  | candNext ms m cm m' =>
    exact runs_lexNextP (dblk_inj spec 1) (dblk_lt_prot spec 1) (dmk_lt_prot spec)
  | commit ms m cm m' => exact runs_copyP spec
  | tick ms m cm => exact runs_lexNextP (dblk_inj spec 3) (dblk_lt_prot spec 3) (dmk_lt_prot spec)
  | tickReset ms m cm => exact runs_resetP spec 3
  | dead => exact runs_exitP_local false (dprot spec)

omit [Finite A] in
/-- The relations the fragments run see only the four blocks and the marker. -/
theorem headLocal2_dRel (c : DetNode spec.Mode (modeCard spec)) :
    HeadLocal2 (dprot spec) (dRel (A := A) spec c) := by
  have hkeep : ∀ (t : Fin 4) (x x' y y' : Fin (dHeads spec) → A), HeadAgree (dprot spec) x x' →
      HeadAgree (dprot spec) y y' → (dKeepBut spec t x y ↔ dKeepBut spec t x' y') := by
    intro t x x' y y' hx hy
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun t' i ht' => by
          rw [← hy _ (dblk_lt_prot spec t' i), ← hx _ (dblk_lt_prot spec t' i)]
          exact h1 t' i ht',
        by rw [← hy _ (dmk_lt_prot spec), ← hx _ (dmk_lt_prot spec)]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun t' i ht' => by
          rw [hy _ (dblk_lt_prot spec t' i), hx _ (dblk_lt_prot spec t' i)]
          exact h1 t' i ht',
        by rw [hy _ (dmk_lt_prot spec), hx _ (dmk_lt_prot spec)]; exact h2⟩
  have hres : ∀ (t : Fin 4), HeadLocal2 (dprot spec) (A := A) fun x b y => b = true ∧
      (∀ (i : Fin spec.k) (a : A), y (dblk spec t i) ≤ a) ∧ dKeepBut spec t x y := by
    intro t x x' y y' hx hy b
    refine and_congr Iff.rfl (and_congr ?_ (hkeep t x x' y y' hx hy))
    exact forall_congr' fun i => forall_congr' fun a => by rw [hy _ (dblk_lt_prot spec t i)]
  have hag : ∀ x x' y y' : Fin (dHeads spec) → A, HeadAgree (dprot spec) x x' →
      HeadAgree (dprot spec) y y' →
      (HeadAgree (dprot spec) x y ↔ HeadAgree (dprot spec) x' y') :=
    fun x x' y y' hx hy =>
      ⟨fun h => hx.symm.trans (h.trans hy), fun h => hx.trans (h.trans hy.symm)⟩
  have htup : ∀ (t : Fin 4) (x x' : Fin (dHeads spec) → A), HeadAgree (dprot spec) x x' →
      dTup spec t x = dTup spec t x' :=
    fun t x x' hx => funext fun i => hx _ (dblk_lt_prot spec t i)
  cases c with
  | init =>
    intro x x' y y' hx hy b
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · exact forall_congr' fun a => by rw [hy _ (dmk_lt_prot spec)]
    · exact forall_congr' fun t => forall_congr' fun i => by
        rw [hy _ (dblk_lt_prot spec t i), hx _ (dblk_lt_prot spec t i)]
  | srcMode i => exact fun x x' y y' hx hy b => and_congr Iff.rfl (hag x x' y y' hx hy)
  | srcTest ms =>
    intro x x' y y' hx hy b
    simp only [dRel]
    rw [htup 2 x x' hx]
    exact and_congr Iff.rfl (hag x x' y y' hx hy)
  | srcNext ms => exact lexRel_local _ _ _ (dblk_lt_prot spec 2) (dmk_lt_prot spec)
  | srcReset ms => exact hres 2
  | start ms =>
    intro x x' y y' hx hy b
    refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
    · exact forall_congr' fun i => by
        rw [hy _ (dblk_lt_prot spec 0 i), hx _ (dblk_lt_prot spec 2 i)]
    · exact forall_congr' fun i => forall_congr' fun a => by rw [hy _ (dblk_lt_prot spec 3 i)]
    · exact forall_congr' fun t => forall_congr' fun i => imp_congr_right fun _ =>
        imp_congr_right fun _ => by
          rw [hy _ (dblk_lt_prot spec t i), hx _ (dblk_lt_prot spec t i)]
    · rw [hy _ (dmk_lt_prot spec), hx _ (dmk_lt_prot spec)]
  | tgtTest ms m cm =>
    intro x x' y y' hx hy b
    simp only [dRel]
    rw [htup 0 x x' hx]
    exact and_congr Iff.rfl (hag x x' y y' hx hy)
  | candMode ms m cm i => exact hres 1
  | candTest ms m cm m' =>
    intro x x' y y' hx hy b
    simp only [dRel]
    rw [htup 0 x x' hx, htup 1 x x' hx]
    exact and_congr Iff.rfl (hag x x' y y' hx hy)
  | candNext ms m cm m' => exact lexRel_local _ _ _ (dblk_lt_prot spec 1) (dmk_lt_prot spec)
  | commit ms m cm m' =>
    intro x x' y y' hx hy b
    refine and_congr Iff.rfl (and_congr ?_ (hkeep 0 x x' y y' hx hy))
    exact forall_congr' fun i => by
      rw [hy _ (dblk_lt_prot spec 0 i), hx _ (dblk_lt_prot spec 1 i)]
  | tick ms m cm => exact lexRel_local _ _ _ (dblk_lt_prot spec 3) (dmk_lt_prot spec)
  | tickReset ms m cm => exact hres 3
  | dead => exact fun x x' y y' hx hy b => and_congr Iff.rfl (hag x x' y y' hx hy)

/-! ### Soundness -/

omit [Finite A] in
theorem dblk_ne_dblk {t t' : Fin 4} (ht : t ≠ t') (i i' : Fin spec.k) :
    dblk spec t i ≠ dblk spec t' i' := by
  intro he
  have := dblk_notMem_range spec (t := t') i ht
  rw [he] at this
  exact this (dblk_range spec t' i')

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem dTup_of_keepBut {t t' : Fin 4} (ht : t' ≠ t) {x y : Fin (dHeads spec) → A}
    (h : dKeepBut spec t x y) : dTup spec t' y = dTup spec t' x :=
  funext fun i => h.1 t' i ht

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem dTup_of_agree {t : Fin 4} {x y : Fin (dHeads spec) → A}
    (h : HeadAgree (dprot spec) x y) : dTup spec t y = dTup spec t x :=
  funext fun i => (h _ (dblk_lt_prot spec t i)).symm

omit [L.Structure A] [Finite A] in
theorem dTup_of_lexRel {t t' : Fin 4} (ht : t' ≠ t) {x y : Fin (dHeads spec) → A} {b : Bool}
    (h : lexRel (dblk spec t) (dmk spec) (dprot spec) x b y) : dTup spec t' y = dTup spec t' x := by
  rcases h with ⟨-, p, -, -, -, -, -, hother⟩ | ⟨-, -, hag⟩
  · exact funext fun i => hother _ (dblk_lt_prot spec t' i) fun i' => dblk_ne_dblk spec ht i i'
  · exact dTup_of_agree spec hag

/-- The invariant the deterministic machine carries: the tuple on the first
block is a node reachable from a source, and at `commit` the candidate is one
deterministic step away. -/
def dInv (u : DetNode spec.Mode (modeCard spec) × (Fin (dHeads spec) → A)) : Prop :=
  match u.1 with
  | .start ms => spec.IsSrc (ms, dTup spec 2 u.2)
  | .tgtTest _ m _ => ∃ u₀, spec.IsSrc u₀ ∧ spec.det.Reach u₀ (m, dTup spec 0 u.2)
  | .candMode _ m _ _ => ∃ u₀, spec.IsSrc u₀ ∧ spec.det.Reach u₀ (m, dTup spec 0 u.2)
  | .candTest _ m _ _ => ∃ u₀, spec.IsSrc u₀ ∧ spec.det.Reach u₀ (m, dTup spec 0 u.2)
  | .candNext _ m _ _ => ∃ u₀, spec.IsSrc u₀ ∧ spec.det.Reach u₀ (m, dTup spec 0 u.2)
  | .commit _ m _ m' => ∃ u₀, spec.IsSrc u₀ ∧ spec.det.Reach u₀ (m, dTup spec 0 u.2) ∧
      spec.det.Step (m, dTup spec 0 u.2) (m', dTup spec 1 u.2)
  | .tick _ m _ => ∃ u₀, spec.IsSrc u₀ ∧ spec.det.Reach u₀ (m, dTup spec 0 u.2)
  | .tickReset _ m _ => ∃ u₀, spec.IsSrc u₀ ∧ spec.det.Reach u₀ (m, dTup spec 0 u.2)
  | _ => True

omit [Finite A] in
/-- **The invariant is carried along the machine's walk.** -/
theorem dInv_of_walk (x₀ : Fin (dHeads spec) → A)
    {u : DetNode spec.Mode (modeCard spec) × (Fin (dHeads spec) → A)}
    (h : Relation.ReflTransGen (wireStep (dRel spec) (dWire spec))
      ((.init : DetNode spec.Mode (modeCard spec)), x₀) u) : dInv spec u := by
  induction h with
  | refl => trivial
  | @tail p q hp hpq ih =>
    obtain ⟨b, hR, hw⟩ := hpq
    cases hp1 : p.1 with
    | init =>
      rw [hp1] at hw
      have : q.1 = DetNode.srcMode (ix0 spec) := (Sum.inl.inj hw).symm
      simp only [dInv, this]
    | srcMode i =>
      rw [hp1] at hw
      have hq : q.1 = (modeAt spec i).elim .dead .srcTest := (Sum.inl.inj hw).symm
      rcases hmi : modeAt spec i with _ | ms
      · rw [hmi] at hq
        simp only [Option.elim] at hq
        simp only [dInv, hq]
      · rw [hmi] at hq
        simp only [Option.elim] at hq
        simp only [dInv, hq]
    | srcTest ms =>
      rw [hp1] at hw hR
      obtain ⟨hiff, hag⟩ : (b = true ↔ spec.IsSrc (ms, dTup spec 2 p.2)) ∧
        HeadAgree (dprot spec) p.2 q.2 := hR
      cases b with
      | true =>
        have hq : q.1 = DetNode.start ms := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
        rw [dTup_of_agree spec hag]
        exact hiff.mp rfl
      | false =>
        have hq : q.1 = DetNode.srcNext ms := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
    | srcNext ms =>
      rw [hp1] at hw
      cases b with
      | true =>
        have hq : q.1 = DetNode.srcTest ms := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
      | false =>
        have hq : q.1 = DetNode.srcReset ms := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
    | srcReset ms =>
      rw [hp1] at hw
      have hq : q.1 = DetNode.srcMode (nextIx spec (ixOf spec ms)) := (Sum.inl.inj hw).symm
      simp only [dInv, hq]
    | start ms =>
      rw [hp1] at hw hR
      simp only [dInv, hp1] at ih
      obtain ⟨-, hcopy, -, -, -⟩ : b = true ∧ (∀ i, q.2 (dblk spec 0 i) = p.2 (dblk spec 2 i)) ∧
        (∀ (i : Fin spec.k) (a : A), q.2 (dblk spec 3 i) ≤ a) ∧
        (∀ (t : Fin 4) (i : Fin spec.k), t ≠ 0 → t ≠ 3 →
          q.2 (dblk spec t i) = p.2 (dblk spec t i)) ∧
        q.2 (dmk spec) = p.2 (dmk spec) := hR
      have hq : q.1 = (modeAt spec (ix0 spec)).elim .dead fun cm => .tgtTest ms ms cm :=
        (Sum.inl.inj hw).symm
      have htup : dTup spec 0 q.2 = dTup spec 2 p.2 := funext hcopy
      rcases hmi : modeAt spec (ix0 spec) with _ | cm
      · rw [hmi] at hq
        simp only [Option.elim] at hq
        simp only [dInv, hq]
      · rw [hmi] at hq
        simp only [Option.elim] at hq
        simp only [dInv, hq]
        rw [htup]
        exact ⟨(ms, dTup spec 2 p.2), ih, Relation.ReflTransGen.refl⟩
    | tgtTest ms m cm =>
      rw [hp1] at hw hR
      simp only [dInv, hp1] at ih
      obtain ⟨-, hag⟩ : (b = true ↔ spec.IsTgt (m, dTup spec 0 p.2)) ∧
        HeadAgree (dprot spec) p.2 q.2 := hR
      cases b with
      | true => exact absurd hw (by simp [dWire])
      | false =>
        have hq : q.1 = DetNode.candMode ms m cm (ix0 spec) := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
        rw [dTup_of_agree spec hag]
        exact ih
    | candMode ms m cm i =>
      rw [hp1] at hw hR
      simp only [dInv, hp1] at ih
      obtain ⟨-, -, hkeep⟩ : b = true ∧
        (∀ (i : Fin spec.k) (a : A), q.2 (dblk spec 1 i) ≤ a) ∧ dKeepBut spec 1 p.2 q.2 := hR
      have hq : q.1 = (modeAt spec i).elim (.srcNext ms) fun m' => .candTest ms m cm m' :=
        (Sum.inl.inj hw).symm
      rcases hmi : modeAt spec i with _ | m'
      · rw [hmi] at hq
        simp only [Option.elim] at hq
        simp only [dInv, hq]
      · rw [hmi] at hq
        simp only [Option.elim] at hq
        simp only [dInv, hq]
        rw [dTup_of_keepBut spec (by decide) hkeep]
        exact ih
    | candTest ms m cm m' =>
      rw [hp1] at hw hR
      simp only [dInv, hp1] at ih
      obtain ⟨hiff, hag⟩ : (b = true ↔
          spec.det.Step (m, dTup spec 0 p.2) (m', dTup spec 1 p.2)) ∧
        HeadAgree (dprot spec) p.2 q.2 := hR
      cases b with
      | true =>
        have hq : q.1 = DetNode.commit ms m cm m' := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
        rw [dTup_of_agree spec hag, dTup_of_agree spec hag]
        obtain ⟨u₀, hu₀, hreach⟩ := ih
        exact ⟨u₀, hu₀, hreach, hiff.mp rfl⟩
      | false =>
        have hq : q.1 = DetNode.candNext ms m cm m' := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
        rw [dTup_of_agree spec hag]
        exact ih
    | candNext ms m cm m' =>
      rw [hp1] at hw hR
      simp only [dInv, hp1] at ih
      have htup : dTup spec 0 q.2 = dTup spec 0 p.2 :=
        dTup_of_lexRel spec (by decide) hR
      cases b with
      | true =>
        have hq : q.1 = DetNode.candTest ms m cm m' := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
        rw [htup]
        exact ih
      | false =>
        have hq : q.1 = DetNode.candMode ms m cm (nextIx spec (ixOf spec m')) :=
          (Sum.inl.inj hw).symm
        simp only [dInv, hq]
        rw [htup]
        exact ih
    | commit ms m cm m' =>
      rw [hp1] at hw hR
      simp only [dInv, hp1] at ih
      obtain ⟨-, hcopy, hkeep⟩ : b = true ∧ (∀ i, q.2 (dblk spec 0 i) = p.2 (dblk spec 1 i)) ∧
        dKeepBut spec 0 p.2 q.2 := hR
      have hq : q.1 = DetNode.tick ms m' cm := (Sum.inl.inj hw).symm
      simp only [dInv, hq]
      obtain ⟨u₀, hu₀, hreach, hstep⟩ := ih
      refine ⟨u₀, hu₀, ?_⟩
      have htup : dTup spec 0 q.2 = dTup spec 1 p.2 := funext hcopy
      rw [htup]
      exact hreach.tail hstep
    | tick ms m cm =>
      rw [hp1] at hw hR
      simp only [dInv, hp1] at ih
      have htup : dTup spec 0 q.2 = dTup spec 0 p.2 := dTup_of_lexRel spec (by decide) hR
      cases b with
      | true =>
        have hq : q.1 = DetNode.tgtTest ms m cm := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
        rw [htup]
        exact ih
      | false =>
        have hq : q.1 = DetNode.tickReset ms m cm := (Sum.inl.inj hw).symm
        simp only [dInv, hq]
        rw [htup]
        exact ih
    | tickReset ms m cm =>
      rw [hp1] at hw hR
      simp only [dInv, hp1] at ih
      obtain ⟨-, -, hkeep⟩ : b = true ∧
        (∀ (i : Fin spec.k) (a : A), q.2 (dblk spec 3 i) ≤ a) ∧ dKeepBut spec 3 p.2 q.2 := hR
      have hq : q.1 = (modeAt spec (nextIx spec (ixOf spec cm))).elim (.srcNext ms)
          fun cm' => .tgtTest ms m cm' := (Sum.inl.inj hw).symm
      rcases hmi : modeAt spec (nextIx spec (ixOf spec cm)) with _ | cm'
      · rw [hmi] at hq
        simp only [Option.elim] at hq
        simp only [dInv, hq]
      · rw [hmi] at hq
        simp only [Option.elim] at hq
        simp only [dInv, hq]
        rw [dTup_of_keepBut spec (by decide) hkeep]
        exact ih
    | dead =>
      rw [hp1] at hw
      exact absurd hw (by cases b <;> simp [dWire])

omit [Finite A] in
/-- **Soundness**: if the deterministic machine accepts, the specification
does. -/
theorem accepts_of_dExit (x₀ : Fin (dHeads spec) → A)
    {u : DetNode spec.Mode (modeCard spec) × (Fin (dHeads spec) → A)}
    {z : Fin (dHeads spec) → A}
    (hwalk : Relation.ReflTransGen (wireStep (dRel spec) (dWire spec))
      ((.init : DetNode spec.Mode (modeCard spec)), x₀) u)
    (hexit : wireExit (dRel spec) (dWire spec) u true z) : spec.det.Accepts A := by
  obtain ⟨b, hR, hw⟩ := hexit
  have hinv := dInv_of_walk spec x₀ hwalk
  cases hu1 : u.1 with
  | tgtTest ms m cm =>
    rw [hu1] at hw hR
    simp only [dInv, hu1] at hinv
    obtain ⟨u₀, hu₀, hreach⟩ := hinv
    cases b with
    | false => exact absurd hw (by simp [dWire])
    | true =>
      obtain ⟨hiff, -⟩ : (true = true ↔ spec.IsTgt (m, dTup spec 0 u.2)) ∧
        HeadAgree (dprot spec) u.2 z := hR
      exact ⟨u₀, (m, dTup spec 0 u.2), hu₀, hiff.mp rfl, hreach⟩
  | init => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | srcMode i => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | srcTest ms => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | srcNext ms => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | srcReset ms => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | start ms =>
    rw [hu1] at hw
    exact absurd hw (by
      cases b <;> rcases hmi : modeAt spec (ix0 spec) with _ | cm <;> simp [dWire, hmi])
  | candMode ms m cm i =>
    rw [hu1] at hw
    exact absurd hw (by cases b <;> rcases hmi : modeAt spec i with _ | m' <;> simp [dWire, hmi])
  | candTest ms m cm m' => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | candNext ms m cm m' => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | commit ms m cm m' => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | tick ms m cm => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])
  | tickReset ms m cm =>
    rw [hu1] at hw
    exact absurd hw (by
      cases b <;>
        rcases hmi : modeAt spec (nextIx spec (ixOf spec cm)) with _ | cm' <;> simp [dWire, hmi])
  | dead => rw [hu1] at hw; exact absurd hw (by cases b <;> simp [dWire])

/-! ### Completeness: the candidate scan -/

/-- Reachability in the machine's control graph. -/
abbrev DReach : DetNode spec.Mode (modeCard spec) × (Fin (dHeads spec) → A) →
    DetNode spec.Mode (modeCard spec) × (Fin (dHeads spec) → A) → Prop :=
  Relation.ReflTransGen (wireStep (dRel spec) (dWire spec))

variable {spec}

omit [Finite A] in
theorem dstep_candTest_true {ms m cm m' : spec.Mode} {x : Fin (dHeads spec) → A}
    (h : spec.det.Step (m, dTup spec 0 x) (m', dTup spec 1 x)) :
    wireStep (dRel spec) (dWire spec) ((.candTest ms m cm m' : DetNode spec.Mode _), x)
      ((.commit ms m cm m' : DetNode spec.Mode _), x) :=
  ⟨true, ⟨⟨fun _ => h, fun _ => rfl⟩, HeadAgree.refl x⟩, rfl⟩

omit [Finite A] in
theorem dstep_candTest_false {ms m cm m' : spec.Mode} {x : Fin (dHeads spec) → A}
    (h : ¬spec.det.Step (m, dTup spec 0 x) (m', dTup spec 1 x)) :
    wireStep (dRel spec) (dWire spec) ((.candTest ms m cm m' : DetNode spec.Mode _), x)
      ((.candNext ms m cm m' : DetNode spec.Mode _), x) :=
  ⟨false, ⟨⟨fun hc => absurd hc (by simp), fun hc => absurd hc h⟩, HeadAgree.refl x⟩, rfl⟩

omit [Finite A] in
theorem dstep_candNext_true {ms m cm m' : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h : lexRel (dblk spec 1) (dmk spec) (dprot spec) x true y) :
    wireStep (dRel spec) (dWire spec) ((.candNext ms m cm m' : DetNode spec.Mode _), x)
      ((.candTest ms m cm m' : DetNode spec.Mode _), y) :=
  ⟨true, h, rfl⟩

omit [Finite A] in
theorem dstep_candNext_false {ms m cm m' : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h : lexRel (dblk spec 1) (dmk spec) (dprot spec) x false y) :
    wireStep (dRel spec) (dWire spec) ((.candNext ms m cm m' : DetNode spec.Mode _), x)
      ((.candMode ms m cm (nextIx spec (ixOf spec m')) : DetNode spec.Mode _), y) :=
  ⟨false, h, rfl⟩

omit [Finite A] in
theorem dmk_ne_blk1 (i : Fin spec.k) : dmk spec ≠ dblk spec 1 i :=
  fun he => dblk_ne_dmk spec 1 i he.symm

/-- Covers are unique in a linear order. -/
theorem covBy_unique {C : Type} [LinearOrder C] {a b b' : C} (h : a ⋖ b) (h' : a ⋖ b') :
    b = b' := by
  rcases lt_trichotomy b b' with hlt | he | hgt
  · exact absurd hlt (h'.2 h.1)
  · exact he
  · exact absurd hgt (h.2 h'.1)

/-- **The tuple scan finds the successor**: from the candidate block at `c`, if
the (unique) successor of the current node is in mode `m'` with a tuple at or
above `c`, the scan reaches `commit` holding it. -/
theorem scanFound (ms m cm m' : spec.Mode) (w' : spec.Node A) (hw1 : w'.1 = m') :
    ∀ (c : Lex (Fin spec.k → A)) (x : Fin (dHeads spec) → A), (∀ a : A, a ≤ x (dmk spec)) →
      dTup spec 1 x = ofLex c → spec.det.Step (m, dTup spec 0 x) w' → c ≤ toLex w'.2 →
      ∃ x' : Fin (dHeads spec) → A,
        DReach spec ((.candTest ms m cm m' : DetNode spec.Mode _), x)
          ((.commit ms m cm m' : DetNode spec.Mode _), x') ∧
        (∀ a : A, a ≤ x' (dmk spec)) ∧ dTup spec 0 x' = dTup spec 0 x ∧
        dTup spec 1 x' = w'.2 ∧ dTup spec 2 x' = dTup spec 2 x ∧
        dTup spec 3 x' = dTup spec 3 x := by
  intro c
  induction c using order_induction_down with
  | hmax c hctop =>
    intro x hmk htup hstep hle
    have hc : c = toLex w'.2 := le_antisymm hle (hctop _)
    have h1 : dTup spec 1 x = w'.2 := by rw [htup, hc]; rfl
    refine ⟨x, Relation.ReflTransGen.single (dstep_candTest_true ?_), hmk, rfl, h1, rfl, rfl⟩
    rw [h1, ← hw1]
    exact hstep
  | hstep c c' hlt hnb ih =>
    intro x hmk htup hstep hle
    by_cases heq : dTup spec 1 x = w'.2
    · refine ⟨x, Relation.ReflTransGen.single (dstep_candTest_true ?_), hmk, rfl, heq, rfl, rfl⟩
      rw [heq, ← hw1]
      exact hstep
    · have hfail : ¬spec.det.Step (m, dTup spec 0 x) (m', dTup spec 1 x) := by
        intro hcon
        have h1 := ((spec.det_step_iff (m, dTup spec 0 x) w').mp hstep).2 (m', dTup spec 1 x)
          ((spec.det_step_iff _ _).mp hcon).1
        exact heq (congrArg Prod.snd h1)
      have hnotTop : ¬∀ (i : Fin spec.k) (a : A), a ≤ x (dblk spec 1 i) := by
        intro hcon
        have h1 : toLex w'.2 ≤ toLex (dTup spec 1 x) := tup_isTop_iff.mpr hcon _
        rw [htup] at h1
        simp only [toLex_ofLex] at h1
        exact heq (by rw [htup]; exact congrArg ofLex (le_antisymm hle h1))
      have hccov : c ⋖ c' := ⟨hlt, fun a h1 h2 => hnb a ⟨h1, h2⟩⟩
      obtain ⟨y, hlex, hsucc, hother⟩ := exists_lexRel_succ (dblk_inj spec 1) hmk hnotTop
      have hmky : y (dmk spec) = x (dmk spec) :=
        hother (dmk spec) (dmk_lt_prot spec) fun i => dmk_ne_blk1 i
      have hcov1 : c ⋖ toLex (dTup spec 1 y) := by
        have hc : toLex (dTup spec 1 x) ⋖ toLex (dTup spec 1 y) := tupSucc_iff_covBy.mp hsucc
        rw [htup] at hc
        simpa only [toLex_ofLex] using hc
      have hcc : dTup spec 1 y = ofLex c' := congrArg ofLex (covBy_unique hcov1 hccov)
      have hlt2 : c < toLex w'.2 :=
        lt_of_le_of_ne hle fun hcon => heq (by rw [htup]; exact congrArg ofLex hcon)
      have hle2 : c' ≤ toLex w'.2 := by
        by_contra hcon
        exact hnb (toLex w'.2) ⟨hlt2, not_le.mp hcon⟩
      have h0y : dTup spec 0 y = dTup spec 0 x := dTup_of_lexRel spec (by decide) hlex
      obtain ⟨x', hreach, hmk', h0, h1, h2, h3⟩ := ih y (by rw [hmky]; exact hmk) hcc
        (by rw [h0y]; exact hstep) hle2
      refine ⟨x', Relation.ReflTransGen.head (dstep_candTest_false hfail)
        (Relation.ReflTransGen.head (dstep_candNext_true hlex) hreach), hmk', ?_, h1, ?_, ?_⟩
      · rw [h0, h0y]
      · rw [h2, dTup_of_lexRel spec (show (2 : Fin 4) ≠ 1 by decide) hlex]
      · rw [h3, dTup_of_lexRel spec (show (3 : Fin 4) ≠ 1 by decide) hlex]

/-- **The tuple scan exhausts**: if the current node has no successor in mode
`m'`, the scan walks the candidate block to its greatest tuple and moves on to
the next candidate mode. -/
theorem scanNone (ms m cm m' : spec.Mode) :
    ∀ (c : Lex (Fin spec.k → A)) (x : Fin (dHeads spec) → A), (∀ a : A, a ≤ x (dmk spec)) →
      dTup spec 1 x = ofLex c →
      (∀ t : Fin spec.k → A, ¬spec.det.Step (m, dTup spec 0 x) (m', t)) →
      ∃ x' : Fin (dHeads spec) → A,
        DReach spec ((.candTest ms m cm m' : DetNode spec.Mode _), x)
          ((.candMode ms m cm (nextIx spec (ixOf spec m')) : DetNode spec.Mode _), x') ∧
        (∀ a : A, a ≤ x' (dmk spec)) ∧ dTup spec 0 x' = dTup spec 0 x ∧
        dTup spec 2 x' = dTup spec 2 x ∧ dTup spec 3 x' = dTup spec 3 x := by
  intro c
  induction c using order_induction_down with
  | hmax c hctop =>
    intro x hmk htup hnone
    have htop : ∀ (i : Fin spec.k) (a : A), a ≤ x (dblk spec 1 i) := by
      refine tup_isTop_iff.mp ?_
      intro u
      rw [show (fun i => x (dblk spec 1 i)) = dTup spec 1 x from rfl, htup]
      simpa only [toLex_ofLex] using hctop u
    exact ⟨x, Relation.ReflTransGen.head (dstep_candTest_false (hnone _))
      (Relation.ReflTransGen.single (dstep_candNext_false (lexRel_top hmk htop))), hmk, rfl,
      rfl, rfl⟩
  | hstep c c' hlt hnb ih =>
    intro x hmk htup hnone
    have hnotTop : ¬∀ (i : Fin spec.k) (a : A), a ≤ x (dblk spec 1 i) := by
      intro hcon
      have h1 : toLex (ofLex c') ≤ toLex (dTup spec 1 x) := tup_isTop_iff.mpr hcon _
      rw [htup] at h1
      simp only [toLex_ofLex] at h1
      exact absurd hlt (not_lt.mpr h1)
    have hccov : c ⋖ c' := ⟨hlt, fun a h1 h2 => hnb a ⟨h1, h2⟩⟩
    obtain ⟨y, hlex, hsucc, hother⟩ := exists_lexRel_succ (dblk_inj spec 1) hmk hnotTop
    have hmky : y (dmk spec) = x (dmk spec) :=
      hother (dmk spec) (dmk_lt_prot spec) fun i => dmk_ne_blk1 i
    have hcov1 : c ⋖ toLex (dTup spec 1 y) := by
      have hc : toLex (dTup spec 1 x) ⋖ toLex (dTup spec 1 y) := tupSucc_iff_covBy.mp hsucc
      rw [htup] at hc
      simpa only [toLex_ofLex] using hc
    have hcc : dTup spec 1 y = ofLex c' := congrArg ofLex (covBy_unique hcov1 hccov)
    have h0y : dTup spec 0 y = dTup spec 0 x := dTup_of_lexRel spec (by decide) hlex
    obtain ⟨x', hreach, hmk', h0, h2, h3⟩ := ih y (by rw [hmky]; exact hmk) hcc
      (by rw [h0y]; exact hnone)
    refine ⟨x', Relation.ReflTransGen.head (dstep_candTest_false (hnone _))
      (Relation.ReflTransGen.head (dstep_candNext_true hlex) hreach), hmk', ?_, ?_, ?_⟩
    · rw [h0, h0y]
    · rw [h2, dTup_of_lexRel spec (show (2 : Fin 4) ≠ 1 by decide) hlex]
    · rw [h3, dTup_of_lexRel spec (show (3 : Fin 4) ≠ 1 by decide) hlex]

/-! ### Completeness: the chain of candidate modes -/

omit [L.Structure A] in
theorem exists_dReset (t : Fin 4) (x : Fin (dHeads spec) → A) :
    ∃ y : Fin (dHeads spec) → A, (∀ (i : Fin spec.k) (a : A), y (dblk spec t i) ≤ a) ∧
      dKeepBut spec t x y := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ : Finset A).Nonempty := ⟨x (dmk spec), Finset.mem_univ _⟩
  obtain ⟨mn, hmn⟩ : ∃ mn : A, ∀ a : A, mn ≤ a :=
    ⟨Finset.univ.min' hne, fun a => Finset.min'_le _ a (Finset.mem_univ a)⟩
  refine ⟨fun h => if (t : ℕ) * spec.k ≤ (h : ℕ) ∧ (h : ℕ) < (t : ℕ) * spec.k + spec.k then mn
    else x h, fun i a => ?_, fun t' i ht' => ?_, ?_⟩
  · change (if (t : ℕ) * spec.k ≤ ((dblk spec t i : Fin (dHeads spec)) : ℕ) ∧
      ((dblk spec t i : Fin (dHeads spec)) : ℕ) < (t : ℕ) * spec.k + spec.k then mn
      else x (dblk spec t i)) ≤ a
    rw [if_pos (dblk_range spec t i)]
    exact hmn a
  · change (if (t : ℕ) * spec.k ≤ ((dblk spec t' i : Fin (dHeads spec)) : ℕ) ∧
      ((dblk spec t' i : Fin (dHeads spec)) : ℕ) < (t : ℕ) * spec.k + spec.k then mn
      else x (dblk spec t' i)) = x (dblk spec t' i)
    rw [if_neg (dblk_notMem_range spec i ht')]
  · change (if (t : ℕ) * spec.k ≤ ((dmk spec : Fin (dHeads spec)) : ℕ) ∧
      ((dmk spec : Fin (dHeads spec)) : ℕ) < (t : ℕ) * spec.k + spec.k then mn
      else x (dmk spec)) = x (dmk spec)
    rw [if_neg (dmk_notMem_range spec t)]

omit [Finite A] in
theorem dstep_candMode {ms m cm : spec.Mode} {i : Fin (modeCard spec + 1)}
    {x y : Fin (dHeads spec) → A} (h1 : ∀ (i' : Fin spec.k) (a : A), y (dblk spec 1 i') ≤ a)
    (h2 : dKeepBut spec 1 x y) :
    wireStep (dRel spec) (dWire spec) ((.candMode ms m cm i : DetNode spec.Mode _), x)
      (((modeAt spec i).elim (.srcNext ms) fun m' => .candTest ms m cm m' :
        DetNode spec.Mode _), y) :=
  ⟨true, ⟨rfl, h1, h2⟩, rfl⟩

theorem ixOf_of_modeAt {i : Fin (modeCard spec + 1)} {m : spec.Mode}
    (h : modeAt spec i = some m) : ixOf spec m = i := by
  rw [modeAt] at h
  by_cases hi : (i : ℕ) < modeCard spec
  · rw [dif_pos hi] at h
    have hm : m = (modeEquiv spec).symm ⟨(i : ℕ), hi⟩ := (Option.some.inj h).symm
    refine Fin.ext ?_
    change ((modeEquiv spec m : Fin (modeCard spec)) : ℕ) = (i : ℕ)
    rw [hm, Equiv.apply_symm_apply]
  · rw [dif_neg hi] at h
    exact absurd h (by simp)

theorem nextIx_val {i : Fin (modeCard spec + 1)} (hi : (i : ℕ) < modeCard spec) :
    ((nextIx spec i : Fin (modeCard spec + 1)) : ℕ) = (i : ℕ) + 1 := by
  rw [nextIx, dif_pos hi]

/-- **The chain of candidate modes finds the successor.** -/
theorem modeFound (ms m cm : spec.Mode) (w' : spec.Node A) :
    ∀ (d : ℕ) (i : Fin (modeCard spec + 1)) (x : Fin (dHeads spec) → A),
      (i : ℕ) + d = ((ixOf spec w'.1 : Fin (modeCard spec + 1)) : ℕ) →
      (∀ a : A, a ≤ x (dmk spec)) → spec.det.Step (m, dTup spec 0 x) w' →
      ∃ x' : Fin (dHeads spec) → A,
        DReach spec ((.candMode ms m cm i : DetNode spec.Mode _), x)
          ((.commit ms m cm w'.1 : DetNode spec.Mode _), x') ∧
        (∀ a : A, a ≤ x' (dmk spec)) ∧ dTup spec 0 x' = dTup spec 0 x ∧ dTup spec 1 x' = w'.2 ∧
        dTup spec 2 x' = dTup spec 2 x ∧ dTup spec 3 x' = dTup spec 3 x := by
  intro d
  induction d with
  | zero =>
    intro i x hix hmk hstep
    have hi : i = ixOf spec w'.1 := Fin.ext (by omega)
    obtain ⟨y, hmin, hkeep⟩ := exists_dReset 1 x
    have hmky : y (dmk spec) = x (dmk spec) := hkeep.2
    have h0y : dTup spec 0 y = dTup spec 0 x := dTup_of_keepBut spec (by decide) hkeep
    obtain ⟨x', hreach, hmk', h0, h1, h2, h3⟩ :=
      scanFound ms m cm w'.1 w' rfl (toLex (dTup spec 1 y)) y (by rw [hmky]; exact hmk) rfl
        (by rw [h0y]; exact hstep) ((tup_isBot_iff.mpr fun p a => hmin p a) _)
    refine ⟨x', ?_, hmk', ?_, h1, ?_, ?_⟩
    · refine Relation.ReflTransGen.head ?_ hreach
      subst hi
      have := dstep_candMode (ms := ms) (m := m) (cm := cm) (i := ixOf spec w'.1) hmin hkeep
      rwa [modeAt_ixOf] at this
    · rw [h0, h0y]
    · rw [h2, dTup_of_keepBut spec (show (2 : Fin 4) ≠ 1 by decide) hkeep]
    · rw [h3, dTup_of_keepBut spec (show (3 : Fin 4) ≠ 1 by decide) hkeep]
  | succ d ih =>
    intro i x hix hmk hstep
    have hilt : (i : ℕ) < modeCard spec := by
      have := (ixOf spec w'.1).isLt
      have h2 : ((ixOf spec w'.1 : Fin (modeCard spec + 1)) : ℕ) < modeCard spec + 1 := this
      omega
    obtain ⟨m₂, hm₂⟩ : ∃ m₂, modeAt spec i = some m₂ := by
      rw [modeAt, dif_pos hilt]
      exact ⟨_, rfl⟩
    have hne : m₂ ≠ w'.1 := by
      intro he
      rw [← he, ixOf_of_modeAt hm₂] at hix
      omega
    obtain ⟨y, hmin, hkeep⟩ := exists_dReset 1 x
    have hmky : y (dmk spec) = x (dmk spec) := hkeep.2
    have h0y : dTup spec 0 y = dTup spec 0 x := dTup_of_keepBut spec (by decide) hkeep
    obtain ⟨x₁, hreach₁, hmk₁, h0₁, h2₁, h3₁⟩ :=
      scanNone ms m cm m₂ (toLex (dTup spec 1 y)) y (by rw [hmky]; exact hmk) rfl
        (by
          intro t hcon
          rw [h0y] at hcon
          exact hne (congrArg Prod.fst
            (((spec.det_step_iff (m, dTup spec 0 x) w').mp hstep).2 (m₂, t)
              ((spec.det_step_iff _ _).mp hcon).1)))
    obtain ⟨x', hreach', hmk', h0', h1', h2', h3'⟩ := ih (nextIx spec (ixOf spec m₂)) x₁
      (by rw [ixOf_of_modeAt hm₂, nextIx_val hilt]; omega) hmk₁
      (by rw [h0₁, h0y]; exact hstep)
    refine ⟨x', ?_, hmk', ?_, h1', ?_, ?_⟩
    · refine Relation.ReflTransGen.head ?_ (hreach₁.trans hreach')
      have := dstep_candMode (ms := ms) (m := m) (cm := cm) (i := i) hmin hkeep
      rwa [hm₂] at this
    · rw [h0', h0₁, h0y]
    · rw [h2', h2₁, dTup_of_keepBut spec (show (2 : Fin 4) ≠ 1 by decide) hkeep]
    · rw [h3', h3₁, dTup_of_keepBut spec (show (3 : Fin 4) ≠ 1 by decide) hkeep]

/-- **The chain of candidate modes exhausts**: with no successor to find, the
machine tries every mode and moves on to the next source. -/
theorem modeNone (ms m cm : spec.Mode) :
    ∀ (d : ℕ) (i : Fin (modeCard spec + 1)) (x : Fin (dHeads spec) → A),
      modeCard spec ≤ (i : ℕ) + d → (∀ a : A, a ≤ x (dmk spec)) →
      (∀ w : spec.Node A, ¬spec.det.Step (m, dTup spec 0 x) w) →
      ∃ x' : Fin (dHeads spec) → A,
        DReach spec ((.candMode ms m cm i : DetNode spec.Mode _), x)
          ((.srcNext ms : DetNode spec.Mode _), x') ∧
        (∀ a : A, a ≤ x' (dmk spec)) ∧ dTup spec 0 x' = dTup spec 0 x ∧
        dTup spec 2 x' = dTup spec 2 x ∧ dTup spec 3 x' = dTup spec 3 x := by
  have hnone : ∀ (i : Fin (modeCard spec + 1)) (x : Fin (dHeads spec) → A),
      modeAt spec i = none → (∀ a : A, a ≤ x (dmk spec)) →
      ∃ x' : Fin (dHeads spec) → A,
        DReach spec ((.candMode ms m cm i : DetNode spec.Mode _), x)
          ((.srcNext ms : DetNode spec.Mode _), x') ∧
        (∀ a : A, a ≤ x' (dmk spec)) ∧ dTup spec 0 x' = dTup spec 0 x ∧
        dTup spec 2 x' = dTup spec 2 x ∧ dTup spec 3 x' = dTup spec 3 x := by
    intro i x hmi hmk
    obtain ⟨y, hmin, hkeep⟩ := exists_dReset 1 x
    refine ⟨y, Relation.ReflTransGen.single ?_, by rw [hkeep.2]; exact hmk,
      dTup_of_keepBut spec (by decide) hkeep,
      dTup_of_keepBut spec (show (2 : Fin 4) ≠ 1 by decide) hkeep,
      dTup_of_keepBut spec (show (3 : Fin 4) ≠ 1 by decide) hkeep⟩
    have := dstep_candMode (ms := ms) (m := m) (cm := cm) (i := i) hmin hkeep
    rwa [hmi] at this
  intro d
  induction d with
  | zero =>
    intro i x hi hmk _
    have := i.isLt
    exact hnone i x (by rw [modeAt, dif_neg (by omega)]) hmk
  | succ d ih =>
    intro i x hi hmk hns
    rcases hmi : modeAt spec i with _ | m₂
    · exact hnone i x hmi hmk
    · have hilt : (i : ℕ) < modeCard spec := by
        by_contra hcon
        rw [modeAt, dif_neg hcon] at hmi
        exact absurd hmi (by simp)
      obtain ⟨y, hmin, hkeep⟩ := exists_dReset 1 x
      have hmky : y (dmk spec) = x (dmk spec) := hkeep.2
      have h0y : dTup spec 0 y = dTup spec 0 x := dTup_of_keepBut spec (by decide) hkeep
      obtain ⟨x₁, hreach₁, hmk₁, h0₁, h2₁, h3₁⟩ :=
        scanNone ms m cm m₂ (toLex (dTup spec 1 y)) y (by rw [hmky]; exact hmk) rfl
          (by
            intro t hcon
            rw [h0y] at hcon
            exact hns (m₂, t) hcon)
      obtain ⟨x', hreach', hmk', h0', h2', h3'⟩ := ih (nextIx spec (ixOf spec m₂)) x₁
        (by rw [ixOf_of_modeAt hmi, nextIx_val hilt]; omega) hmk₁
        (by rw [h0₁, h0y]; exact hns)
      refine ⟨x', ?_, hmk', ?_, ?_, ?_⟩
      · refine Relation.ReflTransGen.head ?_ (hreach₁.trans hreach')
        have := dstep_candMode (ms := ms) (m := m) (cm := cm) (i := i) hmin hkeep
        rwa [hmi] at this
      · rw [h0', h0₁, h0y]
      · rw [h2', h2₁, dTup_of_keepBut spec (show (2 : Fin 4) ≠ 1 by decide) hkeep]
      · rw [h3', h3₁, dTup_of_keepBut spec (show (3 : Fin 4) ≠ 1 by decide) hkeep]

/-! ### Completeness: one step of the simulated walk -/

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem exists_dCopy (t : Fin 4) (x : Fin (dHeads spec) → A) :
    ∃ y : Fin (dHeads spec) → A, (∀ i, y (dblk spec 0 i) = x (dblk spec t i)) ∧
      dKeepBut spec 0 x y := by
  classical
  refine ⟨fun h => if hh : (h : ℕ) < spec.k then x (dblk spec t ⟨(h : ℕ), hh⟩) else x h,
    fun i => ?_, fun t' i ht' => ?_, ?_⟩
  · change (if hh : ((dblk spec 0 i : Fin (dHeads spec)) : ℕ) < spec.k then
      x (dblk spec t ⟨_, hh⟩) else x (dblk spec 0 i)) = x (dblk spec t i)
    rw [dif_pos (show ((dblk spec 0 i : Fin (dHeads spec)) : ℕ) < spec.k by simp)]
    exact congrArg (fun j => x (dblk spec t j)) (Fin.ext (by simp))
  · change (if hh : ((dblk spec t' i : Fin (dHeads spec)) : ℕ) < spec.k then
      x (dblk spec t ⟨_, hh⟩) else x (dblk spec t' i)) = x (dblk spec t' i)
    refine dif_neg ?_
    have := dblk_notMem_range spec (t := 0) i ht'
    simp only [Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.zero_le, true_and, Nat.zero_add] at this
    exact this
  · change (if hh : ((dmk spec : Fin (dHeads spec)) : ℕ) < spec.k then
      x (dblk spec t ⟨_, hh⟩) else x (dmk spec)) = x (dmk spec)
    refine dif_neg ?_
    have := dmk_notMem_range spec 0
    simp only [Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.zero_le, true_and, Nat.zero_add] at this
    exact this

omit [Finite A] in
theorem dstep_tgtTest_false {ms m cm : spec.Mode} {x : Fin (dHeads spec) → A}
    (h : ¬spec.IsTgt (m, dTup spec 0 x)) :
    wireStep (dRel spec) (dWire spec) ((.tgtTest ms m cm : DetNode spec.Mode _), x)
      ((.candMode ms m cm (ix0 spec) : DetNode spec.Mode _), x) :=
  ⟨false, ⟨⟨fun hc => absurd hc (by simp), fun hc => absurd hc h⟩, HeadAgree.refl x⟩, rfl⟩

omit [Finite A] in
theorem dstep_commit {ms m cm m' : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h1 : ∀ i, y (dblk spec 0 i) = x (dblk spec 1 i)) (h2 : dKeepBut spec 0 x y) :
    wireStep (dRel spec) (dWire spec) ((.commit ms m cm m' : DetNode spec.Mode _), x)
      ((.tick ms m' cm : DetNode spec.Mode _), y) :=
  ⟨true, ⟨rfl, h1, h2⟩, rfl⟩

omit [Finite A] in
theorem dstep_tick_true {ms m cm : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h : lexRel (dblk spec 3) (dmk spec) (dprot spec) x true y) :
    wireStep (dRel spec) (dWire spec) ((.tick ms m cm : DetNode spec.Mode _), x)
      ((.tgtTest ms m cm : DetNode spec.Mode _), y) :=
  ⟨true, h, rfl⟩

omit [Finite A] in
theorem dmk_ne_blk3 (i : Fin spec.k) : dmk spec ≠ dblk spec 3 i :=
  fun he => dblk_ne_dmk spec 3 i he.symm

/-- **One step of the simulated walk**: at a node that is not accepting but has
a successor, with a counter that can still be stepped, the machine moves to the
successor and ticks. -/
theorem walkStep (ms m cm : spec.Mode) (x : Fin (dHeads spec) → A)
    (hmk : ∀ a : A, a ≤ x (dmk spec)) (hntgt : ¬spec.IsTgt (m, dTup spec 0 x))
    {w' : spec.Node A} (hstep : spec.det.Step (m, dTup spec 0 x) w')
    (hnotTop : ¬∀ (i : Fin spec.k) (a : A), a ≤ x (dblk spec 3 i)) :
    ∃ x' : Fin (dHeads spec) → A,
      DReach spec ((.tgtTest ms m cm : DetNode spec.Mode _), x)
        ((.tgtTest ms w'.1 cm : DetNode spec.Mode _), x') ∧
      (∀ a : A, a ≤ x' (dmk spec)) ∧ dTup spec 0 x' = w'.2 ∧
      dTup spec 2 x' = dTup spec 2 x ∧ TupSucc (dTup spec 3 x) (dTup spec 3 x') := by
  -- find the successor
  obtain ⟨x₁, hreach₁, hmk₁, h0₁, h1₁, h2₁, h3₁⟩ :=
    modeFound ms m cm w' ((ixOf spec w'.1 : Fin (modeCard spec + 1)) : ℕ) (ix0 spec) x
      (Nat.zero_add _) hmk hstep
  -- commit
  obtain ⟨x₂, hcopy, hkeep₂⟩ := exists_dCopy 1 x₁
  have h0₂ : dTup spec 0 x₂ = w'.2 := by rw [← h1₁]; exact funext hcopy
  have h2₂ : dTup spec 2 x₂ = dTup spec 2 x₁ :=
    dTup_of_keepBut spec (show (2 : Fin 4) ≠ 0 by decide) hkeep₂
  have h3₂ : dTup spec 3 x₂ = dTup spec 3 x₁ :=
    dTup_of_keepBut spec (show (3 : Fin 4) ≠ 0 by decide) hkeep₂
  have hmk₂ : ∀ a : A, a ≤ x₂ (dmk spec) := by rw [hkeep₂.2]; exact hmk₁
  -- tick
  have hnotTop₂ : ¬∀ (i : Fin spec.k) (a : A), a ≤ x₂ (dblk spec 3 i) := by
    intro hcon
    refine hnotTop fun i a => ?_
    have hxx : x (dblk spec 3 i) = x₂ (dblk spec 3 i) := by
      have h : dTup spec 3 x₂ = dTup spec 3 x := by rw [h3₂, h3₁]
      exact (congrFun h i).symm
    rw [hxx]
    exact hcon i a
  obtain ⟨x₃, hlex, hsucc, hother⟩ := exists_lexRel_succ (dblk_inj spec 3) hmk₂ hnotTop₂
  refine ⟨x₃, ?_, ?_, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.head (dstep_tgtTest_false hntgt)
      (hreach₁.trans (Relation.ReflTransGen.head (dstep_commit hcopy hkeep₂)
        (Relation.ReflTransGen.single (dstep_tick_true hlex))))
  · rw [hother (dmk spec) (dmk_lt_prot spec) fun i => dmk_ne_blk3 i]
    exact hmk₂
  · rw [dTup_of_lexRel spec (show (0 : Fin 4) ≠ 3 by decide) hlex, h0₂]
  · rw [dTup_of_lexRel spec (show (2 : Fin 4) ≠ 3 by decide) hlex, h2₂, h2₁]
  · have h3 : dTup spec 3 x₂ = dTup spec 3 x := by rw [h3₂, h3₁]
    have : TupSucc (dTup spec 3 x₂) (dTup spec 3 x₃) := hsucc
    rwa [h3] at this

/-! ### Completeness: the counter as a linear order -/

section Counter

/-- **The value of the counter**: the mode it carries in the control together
with the tuple on its block, ordered lexicographically with the mode most
significant. A tick of the machine is a cover in this order
(`DescriptiveComplexity.HeadProgram.dcount_covBy_tup` within a mode,
`DescriptiveComplexity.HeadProgram.dcount_covBy_mode` across one), and the order has
exactly as many elements as the specification has nodes
(`DescriptiveComplexity.HeadProgram.card_dcount`) – which is what makes the budget long
enough. -/
abbrev DCount (spec : TCSpec L) (B : Type) [LinearOrder B] : Type :=
  Fin (modeCard spec) ×ₗ Lex (Fin spec.k → B)

/-- The counter's value, read off the mode in the control and the tuple on the
block. -/
noncomputable def dcount (spec : TCSpec L) {B : Type} [LinearOrder B] (cm : spec.Mode)
    (t : Fin spec.k → B) : DCount spec B := toLex (modeEquiv spec cm, toLex t)

omit [L.Structure A] [Finite A] in
/-- The counter's value determines the mode and the tuple. -/
theorem dcount_inj {cm cm' : spec.Mode} {t t' : Fin spec.k → A}
    (h : dcount spec cm t = dcount spec cm' t') : cm = cm' ∧ t = t' := by
  have h1 : (modeEquiv spec cm, toLex t) = (modeEquiv spec cm', toLex t') := toLex_inj.mp h
  exact ⟨(modeEquiv spec).injective (congrArg Prod.fst h1),
    toLex_inj.mp (congrArg Prod.snd h1)⟩

omit [L.Structure A] [Finite A] in
/-- Stepping the tuple is a cover of the counter. -/
theorem dcount_covBy_tup [Nonempty A] (cm : spec.Mode) {t t' : Fin spec.k → A}
    (h : TupSucc t t') : dcount spec cm t ⋖ dcount spec cm t' :=
  prodLex_covBy_iff.mpr (Or.inl ⟨rfl, tupSucc_iff_covBy.mp h⟩)

/-- The index of a mode the enumeration produces. -/
theorem modeEquiv_of_modeAt {i : Fin (modeCard spec + 1)} {m : spec.Mode}
    (h : modeAt spec i = some m) : ((modeEquiv spec m : Fin (modeCard spec)) : ℕ) = (i : ℕ) :=
  congrArg (fun j : Fin (modeCard spec + 1) => (j : ℕ)) (ixOf_of_modeAt h)

omit [L.Structure A] [Finite A] in
/-- Running the tuple out and moving to the next mode is a cover of the
counter. -/
theorem dcount_covBy_mode [Nonempty A] {cm cm' : spec.Mode} {t t' : Fin spec.k → A}
    (hnext : modeAt spec (nextIx spec (ixOf spec cm)) = some cm')
    (htop : ∀ (i : Fin spec.k) (a : A), a ≤ t i)
    (hbot : ∀ (i : Fin spec.k) (a : A), t' i ≤ a) :
    dcount spec cm t ⋖ dcount spec cm' t' := by
  refine prodLex_covBy_iff.mpr (Or.inr ⟨finCovBy_iff.mpr ?_, tup_isTop_iff.mpr htop,
    tup_isBot_iff.mpr hbot⟩)
  have hlt : ((ixOf spec cm : Fin (modeCard spec + 1)) : ℕ) < modeCard spec :=
    (modeEquiv spec cm).isLt
  rw [modeEquiv_of_modeAt hnext, nextIx_val hlt]
  rfl

omit [L.Structure A] [Finite A] in
/-- The counter starts at the bottom of its order. -/
theorem dcount_isBot {cm : spec.Mode} {t : Fin spec.k → A}
    (h0 : modeAt spec (ix0 spec) = some cm) (hbot : ∀ (i : Fin spec.k) (a : A), t i ≤ a) :
    ∀ u : DCount spec A, dcount spec cm t ≤ u := by
  refine prodLex_isBot_iff.mpr ⟨fun j => ?_, tup_isBot_iff.mpr hbot⟩
  rw [Fin.le_def, modeEquiv_of_modeAt h0]
  exact Nat.zero_le _

omit [L.Structure A] [Finite A] in
/-- **The counter is exhausted** when its tuple is the greatest one and its
mode is the last of the enumeration. -/
theorem dcount_isTop {cm : spec.Mode} {t : Fin spec.k → A}
    (htop : ∀ (i : Fin spec.k) (a : A), a ≤ t i)
    (hnone : modeAt spec (nextIx spec (ixOf spec cm)) = none) :
    ∀ u : DCount spec A, u ≤ dcount spec cm t := by
  refine prodLex_isTop_iff.mpr ⟨fun j => ?_, tup_isTop_iff.mpr htop⟩
  have hix : ((ixOf spec cm : Fin (modeCard spec + 1)) : ℕ) < modeCard spec :=
    (modeEquiv spec cm).isLt
  have hlast : ¬((nextIx spec (ixOf spec cm) : Fin (modeCard spec + 1)) : ℕ) < modeCard spec := by
    intro hlt
    rw [modeAt, dif_pos hlt] at hnone
    exact absurd hnone (by simp)
  rw [nextIx_val hix] at hlast
  have hval : ((ixOf spec cm : Fin (modeCard spec + 1)) : ℕ) =
      ((modeEquiv spec cm : Fin (modeCard spec)) : ℕ) := rfl
  rw [Fin.le_def]
  have := j.isLt
  omega

omit [L.Structure A] [Finite A] in
/-- **At the top of the counter there is nothing left**: the tuple is the
greatest one and the mode is the last of the enumeration. -/
theorem dcount_of_isTop {cm : spec.Mode} {t : Fin spec.k → A}
    (h : ∀ u : DCount spec A, u ≤ dcount spec cm t) :
    (∀ (i : Fin spec.k) (a : A), a ≤ t i) ∧
      modeAt spec (nextIx spec (ixOf spec cm)) = none := by
  obtain ⟨hm, ht⟩ := prodLex_isTop_iff.mp h
  refine ⟨tup_isTop_iff.mp ht, ?_⟩
  have hlt : ((modeEquiv spec cm : Fin (modeCard spec)) : ℕ) < modeCard spec :=
    (modeEquiv spec cm).isLt
  have hlast : ((modeEquiv spec cm : Fin (modeCard spec)) : ℕ) + 1 = modeCard spec := by
    have hle := hm ⟨modeCard spec - 1, by omega⟩
    rw [Fin.le_def] at hle
    simp only at hle
    omega
  have hval : ((ixOf spec cm : Fin (modeCard spec + 1)) : ℕ) =
      ((modeEquiv spec cm : Fin (modeCard spec)) : ℕ) := rfl
  have hix : ((ixOf spec cm : Fin (modeCard spec + 1)) : ℕ) < modeCard spec := hlt
  rw [modeAt, dif_neg (by rw [nextIx_val hix, hval]; omega)]

omit [L.Structure A] [Finite A] in
/-- The counter has exactly as many values as the specification has nodes. -/
theorem card_dcount : Nat.card (DCount spec A) = Nat.card (spec.det.Node A) := by
  have h1 : Nat.card (DCount spec A) = Nat.card (Fin (modeCard spec) × Lex (Fin spec.k → A)) :=
    Nat.card_congr (toLex (α := Fin (modeCard spec) × Lex (Fin spec.k → A))).symm
  have h2 : Nat.card (Lex (Fin spec.k → A)) = Nat.card (Fin spec.k → A) :=
    Nat.card_congr (toLex (α := Fin spec.k → A)).symm
  rw [h1, Nat.card_prod, h2, Nat.card_eq_fintype_card, Fintype.card_fin, modeCard]
  exact (Nat.card_prod spec.Mode (Fin spec.k → A)).symm

end Counter

/-! ### Completeness: the remaining arcs -/

omit [L.Structure A] in
/-- The marker can be parked at the greatest element. -/
theorem exists_dPark (x : Fin (dHeads spec) → A) :
    ∃ y : Fin (dHeads spec) → A, (∀ a : A, a ≤ y (dmk spec)) ∧
      ∀ (t : Fin 4) (i : Fin spec.k), y (dblk spec t i) = x (dblk spec t i) := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ : Finset A).Nonempty := ⟨x (dmk spec), Finset.mem_univ _⟩
  obtain ⟨mx, hmx⟩ : ∃ mx : A, ∀ a : A, a ≤ mx :=
    ⟨Finset.univ.max' hne, fun a => Finset.le_max' _ a (Finset.mem_univ a)⟩
  refine ⟨Function.update x (dmk spec) mx, ?_, fun t i => ?_⟩
  · rw [Function.update_self]
    exact hmx
  · rw [Function.update_of_ne (dblk_ne_dmk spec t i)]

omit [L.Structure A] in
/-- A walk can be started: the source is copied onto the current block and the
counter is set to its least tuple. -/
theorem exists_dStart (x : Fin (dHeads spec) → A) :
    ∃ y : Fin (dHeads spec) → A, (∀ i, y (dblk spec 0 i) = x (dblk spec 2 i)) ∧
      (∀ (i : Fin spec.k) (a : A), y (dblk spec 3 i) ≤ a) ∧
      (∀ (t : Fin 4) (i : Fin spec.k), t ≠ 0 → t ≠ 3 →
        y (dblk spec t i) = x (dblk spec t i)) ∧ y (dmk spec) = x (dmk spec) := by
  obtain ⟨y₁, hmin₁, hkeep₁⟩ := exists_dReset (A := A) 3 x
  obtain ⟨y, hcopy, hkeep⟩ := exists_dCopy 2 y₁
  refine ⟨y, fun i => ?_, fun i a => ?_, fun t i ht0 ht3 => ?_, ?_⟩
  · rw [hcopy i, hkeep₁.1 2 i (by decide)]
  · rw [hkeep.1 3 i (by decide)]
    exact hmin₁ i a
  · rw [hkeep.1 t i ht0, hkeep₁.1 t i ht3]
  · rw [hkeep.2, hkeep₁.2]

omit [Finite A] in
theorem dstep_init {x y : Fin (dHeads spec) → A} (hmk : ∀ a : A, a ≤ y (dmk spec))
    (hkeep : ∀ (t : Fin 4) (i : Fin spec.k), y (dblk spec t i) = x (dblk spec t i)) :
    wireStep (dRel spec) (dWire spec) ((.init : DetNode spec.Mode _), x)
      ((.srcMode (ix0 spec) : DetNode spec.Mode _), y) :=
  ⟨true, ⟨rfl, hmk, hkeep⟩, rfl⟩

omit [Finite A] in
theorem dstep_srcMode {i : Fin (modeCard spec + 1)} {ms : spec.Mode}
    (h : modeAt spec i = some ms) (x : Fin (dHeads spec) → A) :
    wireStep (dRel spec) (dWire spec) ((.srcMode i : DetNode spec.Mode _), x)
      ((.srcTest ms : DetNode spec.Mode _), x) := by
  refine ⟨true, ⟨rfl, HeadAgree.refl x⟩, ?_⟩
  change Sum.inl ((modeAt spec i).elim (.dead : DetNode spec.Mode _) .srcTest) = _
  rw [h]
  rfl

omit [Finite A] in
theorem dstep_srcTest_true {ms : spec.Mode} {x : Fin (dHeads spec) → A}
    (h : spec.IsSrc (ms, dTup spec 2 x)) :
    wireStep (dRel spec) (dWire spec) ((.srcTest ms : DetNode spec.Mode _), x)
      ((.start ms : DetNode spec.Mode _), x) :=
  ⟨true, ⟨⟨fun _ => h, fun _ => rfl⟩, HeadAgree.refl x⟩, rfl⟩

omit [Finite A] in
theorem dstep_srcTest_false {ms : spec.Mode} {x : Fin (dHeads spec) → A}
    (h : ¬spec.IsSrc (ms, dTup spec 2 x)) :
    wireStep (dRel spec) (dWire spec) ((.srcTest ms : DetNode spec.Mode _), x)
      ((.srcNext ms : DetNode spec.Mode _), x) :=
  ⟨false, ⟨⟨fun hc => absurd hc (by simp), fun hc => absurd hc h⟩, HeadAgree.refl x⟩, rfl⟩

omit [Finite A] in
theorem dstep_start {ms : spec.Mode} {x y : Fin (dHeads spec) → A}
    (hcopy : ∀ i, y (dblk spec 0 i) = x (dblk spec 2 i))
    (hreset : ∀ (i : Fin spec.k) (a : A), y (dblk spec 3 i) ≤ a)
    (hkeep : ∀ (t : Fin 4) (i : Fin spec.k), t ≠ 0 → t ≠ 3 →
      y (dblk spec t i) = x (dblk spec t i))
    (hmk : y (dmk spec) = x (dmk spec)) :
    wireStep (dRel spec) (dWire spec) ((.start ms : DetNode spec.Mode _), x)
      (((modeAt spec (ix0 spec)).elim .dead fun cm => .tgtTest ms ms cm :
        DetNode spec.Mode _), y) :=
  ⟨true, ⟨rfl, hcopy, hreset, hkeep, hmk⟩, rfl⟩

omit [Finite A] in
theorem dstep_srcNext_true {ms : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h : lexRel (dblk spec 2) (dmk spec) (dprot spec) x true y) :
    wireStep (dRel spec) (dWire spec) ((.srcNext ms : DetNode spec.Mode _), x)
      ((.srcTest ms : DetNode spec.Mode _), y) :=
  ⟨true, h, rfl⟩

omit [Finite A] in
theorem dstep_srcNext_false {ms : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h : lexRel (dblk spec 2) (dmk spec) (dprot spec) x false y) :
    wireStep (dRel spec) (dWire spec) ((.srcNext ms : DetNode spec.Mode _), x)
      ((.srcReset ms : DetNode spec.Mode _), y) :=
  ⟨false, h, rfl⟩

omit [Finite A] in
theorem dstep_srcReset {ms : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h1 : ∀ (i : Fin spec.k) (a : A), y (dblk spec 2 i) ≤ a) (h2 : dKeepBut spec 2 x y) :
    wireStep (dRel spec) (dWire spec) ((.srcReset ms : DetNode spec.Mode _), x)
      ((.srcMode (nextIx spec (ixOf spec ms)) : DetNode spec.Mode _), y) :=
  ⟨true, ⟨rfl, h1, h2⟩, rfl⟩

omit [Finite A] in
theorem dstep_tick_false {ms m cm : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h : lexRel (dblk spec 3) (dmk spec) (dprot spec) x false y) :
    wireStep (dRel spec) (dWire spec) ((.tick ms m cm : DetNode spec.Mode _), x)
      ((.tickReset ms m cm : DetNode spec.Mode _), y) :=
  ⟨false, h, rfl⟩

omit [Finite A] in
theorem dstep_tickReset {ms m cm : spec.Mode} {x y : Fin (dHeads spec) → A}
    (h1 : ∀ (i : Fin spec.k) (a : A), y (dblk spec 3 i) ≤ a) (h2 : dKeepBut spec 3 x y) :
    wireStep (dRel spec) (dWire spec) ((.tickReset ms m cm : DetNode spec.Mode _), x)
      (((modeAt spec (nextIx spec (ixOf spec cm))).elim (.srcNext ms)
        fun cm' => .tgtTest ms m cm' : DetNode spec.Mode _), y) :=
  ⟨true, ⟨rfl, h1, h2⟩, rfl⟩

omit [Finite A] in
theorem dexit_tgtTest {ms m cm : spec.Mode} {x : Fin (dHeads spec) → A}
    (h : spec.IsTgt (m, dTup spec 0 x)) :
    wireExit (dRel spec) (dWire spec) ((.tgtTest ms m cm : DetNode spec.Mode _), x) true x :=
  ⟨true, ⟨⟨fun _ => h, fun _ => rfl⟩, HeadAgree.refl x⟩, rfl⟩

variable (spec) in
/-- **The machine accepts from here**: its control walk reaches the `true`
exit. -/
def DAccepts (u : DetNode spec.Mode (modeCard spec) × (Fin (dHeads spec) → A)) : Prop :=
  ∃ (v : DetNode spec.Mode (modeCard spec) × (Fin (dHeads spec) → A))
    (z : Fin (dHeads spec) → A), DReach spec u v ∧ wireExit (dRel spec) (dWire spec) v true z

omit [Finite A] in
theorem DAccepts.mono {u v : DetNode spec.Mode (modeCard spec) × (Fin (dHeads spec) → A)}
    (h : DReach spec u v) (ha : DAccepts spec v) : DAccepts spec u := by
  obtain ⟨w, z, hw, hz⟩ := ha
  exact ⟨w, z, h.trans hw, hz⟩

/-! ### Completeness: one tick of the counter -/

omit [Finite A] in
theorem dmk_ne_blk2 (i : Fin spec.k) : dmk spec ≠ dblk spec 2 i :=
  fun he => dblk_ne_dmk spec 2 i he.symm

/-- **A step of the walk taken with the counter at its greatest tuple**: the
machine moves to the successor, fails to tick, and lands at `tickReset`. -/
theorem walkToTickReset (ms m cm : spec.Mode) (x : Fin (dHeads spec) → A)
    (hmk : ∀ a : A, a ≤ x (dmk spec)) (hntgt : ¬spec.IsTgt (m, dTup spec 0 x))
    {w' : spec.Node A} (hstep : spec.det.Step (m, dTup spec 0 x) w')
    (htop : ∀ (i : Fin spec.k) (a : A), a ≤ x (dblk spec 3 i)) :
    ∃ x' : Fin (dHeads spec) → A,
      DReach spec ((.tgtTest ms m cm : DetNode spec.Mode _), x)
        ((.tickReset ms w'.1 cm : DetNode spec.Mode _), x') ∧
      (∀ a : A, a ≤ x' (dmk spec)) ∧ dTup spec 0 x' = w'.2 ∧
      dTup spec 2 x' = dTup spec 2 x ∧ dTup spec 3 x' = dTup spec 3 x := by
  obtain ⟨x₁, hreach₁, hmk₁, h0₁, h1₁, h2₁, h3₁⟩ :=
    modeFound ms m cm w' ((ixOf spec w'.1 : Fin (modeCard spec + 1)) : ℕ) (ix0 spec) x
      (Nat.zero_add _) hmk hstep
  obtain ⟨x₂, hcopy, hkeep₂⟩ := exists_dCopy 1 x₁
  have h0₂ : dTup spec 0 x₂ = w'.2 := by rw [← h1₁]; exact funext hcopy
  have h2₂ : dTup spec 2 x₂ = dTup spec 2 x :=
    (dTup_of_keepBut spec (show (2 : Fin 4) ≠ 0 by decide) hkeep₂).trans h2₁
  have h3₂ : dTup spec 3 x₂ = dTup spec 3 x :=
    (dTup_of_keepBut spec (show (3 : Fin 4) ≠ 0 by decide) hkeep₂).trans h3₁
  have hmk₂ : ∀ a : A, a ≤ x₂ (dmk spec) := by rw [hkeep₂.2]; exact hmk₁
  have htop₂ : ∀ (i : Fin spec.k) (a : A), a ≤ x₂ (dblk spec 3 i) := by
    intro i a
    rw [show x₂ (dblk spec 3 i) = dTup spec 3 x₂ i from rfl, h3₂]
    exact htop i a
  exact ⟨x₂, Relation.ReflTransGen.head (dstep_tgtTest_false hntgt)
    (hreach₁.trans (Relation.ReflTransGen.head (dstep_commit hcopy hkeep₂)
      (Relation.ReflTransGen.single (dstep_tick_false (lexRel_top hmk₂ htop₂))))),
    hmk₂, h0₂, h2₂, h3₂⟩

/-- **One tick**: at a node that is not accepting but has a successor, with a
counter that still has a cover above it, the machine moves to the successor and
sets its counter to that cover – stepping the tuple where it can, and crossing
over to the next counter mode where it cannot. -/
theorem dTick (ms m cm : spec.Mode) (x : Fin (dHeads spec) → A)
    (hmk : ∀ a : A, a ≤ x (dmk spec)) (hntgt : ¬spec.IsTgt (m, dTup spec 0 x))
    {w' : spec.Node A} (hstep : spec.det.Step (m, dTup spec 0 x) w')
    {z : DCount spec A} (hcov : dcount spec cm (dTup spec 3 x) ⋖ z) :
    ∃ (cm' : spec.Mode) (x' : Fin (dHeads spec) → A),
      DReach spec ((.tgtTest ms m cm : DetNode spec.Mode _), x)
        ((.tgtTest ms w'.1 cm' : DetNode spec.Mode _), x') ∧
      (∀ a : A, a ≤ x' (dmk spec)) ∧ dTup spec 0 x' = w'.2 ∧
      dTup spec 2 x' = dTup spec 2 x ∧ dcount spec cm' (dTup spec 3 x') = z := by
  haveI : Nonempty A := ⟨x (dmk spec)⟩
  by_cases htop : ∀ (i : Fin spec.k) (a : A), a ≤ x (dblk spec 3 i)
  · obtain ⟨x₁, hreach₁, hmk₁, h0₁, h2₁, h3₁⟩ := walkToTickReset ms m cm x hmk hntgt hstep htop
    have htop₁ : ∀ (i : Fin spec.k) (a : A), a ≤ x₁ (dblk spec 3 i) := by
      intro i a
      rw [show x₁ (dblk spec 3 i) = dTup spec 3 x₁ i from rfl, h3₁]
      exact htop i a
    obtain ⟨cm', hcm'⟩ : ∃ cm', modeAt spec (nextIx spec (ixOf spec cm)) = some cm' := by
      rcases hnext : modeAt spec (nextIx spec (ixOf spec cm)) with _ | cm'
      · exact absurd hcov.1 (not_lt.mpr (dcount_isTop htop hnext z))
      · exact ⟨cm', rfl⟩
    obtain ⟨y, hmin, hkeep⟩ := exists_dReset 3 x₁
    refine ⟨cm', y, ?_, ?_, ?_, ?_, ?_⟩
    · refine hreach₁.tail ?_
      have hstepR := dstep_tickReset (ms := ms) (m := w'.1) (cm := cm) hmin hkeep
      rw [hcm'] at hstepR
      exact hstepR
    · rw [hkeep.2]; exact hmk₁
    · rw [dTup_of_keepBut spec (show (0 : Fin 4) ≠ 3 by decide) hkeep, h0₁]
    · rw [dTup_of_keepBut spec (show (2 : Fin 4) ≠ 3 by decide) hkeep, h2₁]
    · refine covBy_unique ?_ hcov
      have hcov' : dcount spec cm (dTup spec 3 x₁) ⋖ dcount spec cm' (dTup spec 3 y) :=
        dcount_covBy_mode hcm' htop₁ (fun i a => hmin i a)
      rwa [h3₁] at hcov'
  · obtain ⟨x', hreach, hmk', h0', h2', hsucc⟩ := walkStep ms m cm x hmk hntgt hstep htop
    exact ⟨cm, x', hreach, hmk', h0', h2', covBy_unique (dcount_covBy_tup cm hsucc) hcov⟩

/-! ### Completeness: the walk, and its two outcomes -/

/-- **A walk that leads nowhere is abandoned**: with no successor to go to, the
machine tries every candidate mode and comes back for the next source. -/
theorem walkStuck (ms m cm : spec.Mode) (x : Fin (dHeads spec) → A)
    (hmk : ∀ a : A, a ≤ x (dmk spec)) (hntgt : ¬spec.IsTgt (m, dTup spec 0 x))
    (hns : ∀ w : spec.Node A, ¬spec.det.Step (m, dTup spec 0 x) w) :
    ∃ x' : Fin (dHeads spec) → A,
      DReach spec ((.tgtTest ms m cm : DetNode spec.Mode _), x)
        ((.srcNext ms : DetNode spec.Mode _), x') ∧ (∀ a : A, a ≤ x' (dmk spec)) ∧
      dTup spec 2 x' = dTup spec 2 x := by
  obtain ⟨x', hreach, hmk', -, h2', -⟩ := modeNone ms m cm (modeCard spec) (ix0 spec) x
    (by change modeCard spec ≤ 0 + modeCard spec; omega) hmk hns
  exact ⟨x', Relation.ReflTransGen.head (dstep_tgtTest_false hntgt) hreach, hmk', h2'⟩

/-- **The machine follows the walk while its counter lasts**: if the walk
reaches an accepting node within the budget, the machine accepts. -/
theorem walkAcc (ms : spec.Mode) : ∀ (n : ℕ) (m cm : spec.Mode) (x : Fin (dHeads spec) → A),
    (∀ a : A, a ≤ x (dmk spec)) → Ticks n (dcount spec cm (dTup spec 3 x)) →
    spec.det.IsTgt ((stepNext spec.det.Step)^[n] (m, dTup spec 0 x)) →
    DAccepts spec ((.tgtTest ms m cm : DetNode spec.Mode _), x) := by
  intro n
  induction n with
  | zero =>
    intro m cm x _ _ htgt
    rw [Function.iterate_zero_apply] at htgt
    exact ⟨_, x, Relation.ReflTransGen.refl, dexit_tgtTest htgt⟩
  | succ n ih =>
    intro m cm x hmk hticks htgt
    by_cases hcur : spec.IsTgt (m, dTup spec 0 x)
    · exact ⟨_, x, Relation.ReflTransGen.refl, dexit_tgtTest hcur⟩
    · by_cases hs : ∃ w, spec.det.Step (m, dTup spec 0 x) w
      · obtain ⟨w', hstep⟩ := hs
        obtain ⟨z, hcov, hticks'⟩ := hticks
        obtain ⟨cm', x', hreach, hmk', h0', -, hc'⟩ := dTick ms m cm x hmk hcur hstep hcov
        refine DAccepts.mono hreach (ih w'.1 cm' x' hmk' (by rw [hc']; exact hticks') ?_)
        rw [h0']
        rw [Function.iterate_succ_apply, stepNext_eq TCSpec.det_functional hstep] at htgt
        exact htgt
      · refine absurd ?_ hcur
        have hfix : stepNext spec.det.Step (m, dTup spec 0 x) = (m, dTup spec 0 x) :=
          stepNext_eq_self hs
        rw [Function.iterate_fixed hfix] at htgt
        exact htgt

/-- **A walk always comes to an end**: whatever the specification does, the
machine either accepts or comes back for the next source, its source block
untouched. The measure is the counter, which the machine steps once per node
visited. -/
theorem walkOut (ms : spec.Mode) : ∀ (z : DCount spec A) (m cm : spec.Mode)
    (x : Fin (dHeads spec) → A), (∀ a : A, a ≤ x (dmk spec)) →
    dcount spec cm (dTup spec 3 x) = z →
    DAccepts spec ((.tgtTest ms m cm : DetNode spec.Mode _), x) ∨
      ∃ x' : Fin (dHeads spec) → A,
        DReach spec ((.tgtTest ms m cm : DetNode spec.Mode _), x)
          ((.srcNext ms : DetNode spec.Mode _), x') ∧ (∀ a : A, a ≤ x' (dmk spec)) ∧
        dTup spec 2 x' = dTup spec 2 x := by
  intro z
  induction z using order_induction_down with
  | hmax z hztop =>
    intro m cm x hmk hz
    by_cases hcur : spec.IsTgt (m, dTup spec 0 x)
    · exact Or.inl ⟨_, x, Relation.ReflTransGen.refl, dexit_tgtTest hcur⟩
    · by_cases hs : ∃ w, spec.det.Step (m, dTup spec 0 x) w
      · obtain ⟨w', hstep⟩ := hs
        have htopz : ∀ u : DCount spec A, u ≤ dcount spec cm (dTup spec 3 x) := by
          rw [hz]; exact hztop
        obtain ⟨htop, hnone⟩ := dcount_of_isTop htopz
        obtain ⟨x₁, hreach₁, hmk₁, -, h2₁, h3₁⟩ := walkToTickReset ms m cm x hmk hcur hstep htop
        obtain ⟨y, hmin, hkeep⟩ := exists_dReset 3 x₁
        refine Or.inr ⟨y, ?_, by rw [hkeep.2]; exact hmk₁, ?_⟩
        · refine hreach₁.tail ?_
          have hstepR := dstep_tickReset (ms := ms) (m := w'.1) (cm := cm) hmin hkeep
          rw [hnone] at hstepR
          exact hstepR
        · rw [dTup_of_keepBut spec (show (2 : Fin 4) ≠ 3 by decide) hkeep, h2₁]
      · push Not at hs
        exact Or.inr (walkStuck ms m cm x hmk hcur hs)
  | hstep z z' hlt hnb ih =>
    intro m cm x hmk hz
    by_cases hcur : spec.IsTgt (m, dTup spec 0 x)
    · exact Or.inl ⟨_, x, Relation.ReflTransGen.refl, dexit_tgtTest hcur⟩
    · by_cases hs : ∃ w, spec.det.Step (m, dTup spec 0 x) w
      · obtain ⟨w', hstep⟩ := hs
        have hcov : dcount spec cm (dTup spec 3 x) ⋖ z' := by
          rw [hz]
          exact ⟨hlt, fun a h1 h2 => hnb a ⟨h1, h2⟩⟩
        obtain ⟨cm', x', hreach, hmk', -, h2', hc'⟩ := dTick ms m cm x hmk hcur hstep hcov
        rcases ih w'.1 cm' x' hmk' hc' with hacc | ⟨x'', hreach'', hmk'', h2''⟩
        · exact Or.inl (DAccepts.mono hreach hacc)
        · exact Or.inr ⟨x'', hreach.trans hreach'', hmk'', by rw [h2'', h2']⟩
      · push Not at hs
        exact Or.inr (walkStuck ms m cm x hmk hcur hs)

/-! ### Completeness: the source enumeration -/

/-- The counter mode the machine starts a walk with. -/
theorem exists_modeAt_ix0 (m : spec.Mode) : ∃ cm₀, modeAt spec (ix0 spec) = some cm₀ := by
  have hpos : ((ix0 spec : Fin (modeCard spec + 1)) : ℕ) < modeCard spec :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (modeEquiv spec m).isLt
  exact ⟨_, by rw [modeAt, dif_pos hpos]⟩

/-- **A source is tried**: from the test of a source, the machine either
accepts or comes back for the next tuple of the enumeration, its source block
where it was. -/
theorem srcTried (ms : spec.Mode) (x : Fin (dHeads spec) → A)
    (hmk : ∀ a : A, a ≤ x (dmk spec)) :
    DAccepts spec ((.srcTest ms : DetNode spec.Mode _), x) ∨
      ∃ x' : Fin (dHeads spec) → A,
        DReach spec ((.srcTest ms : DetNode spec.Mode _), x)
          ((.srcNext ms : DetNode spec.Mode _), x') ∧ (∀ a : A, a ≤ x' (dmk spec)) ∧
        dTup spec 2 x' = dTup spec 2 x := by
  by_cases hsrc : spec.IsSrc (ms, dTup spec 2 x)
  · obtain ⟨y, hcopy, hreset, hkeep, hmky⟩ := exists_dStart x
    obtain ⟨cm₀, hcm₀⟩ := exists_modeAt_ix0 ms
    have hstart := dstep_start (ms := ms) hcopy hreset hkeep hmky
    rw [hcm₀] at hstart
    have hreach0 : DReach spec ((.srcTest ms : DetNode spec.Mode _), x)
        ((.tgtTest ms ms cm₀ : DetNode spec.Mode _), y) :=
      Relation.ReflTransGen.head (dstep_srcTest_true hsrc)
        (Relation.ReflTransGen.single hstart)
    have h2y : dTup spec 2 y = dTup spec 2 x :=
      funext fun i => hkeep 2 i (by decide) (by decide)
    rcases walkOut ms (dcount spec cm₀ (dTup spec 3 y)) ms cm₀ y
      (by rw [hmky]; exact hmk) rfl with hacc | ⟨x'', hreach'', hmk'', h2''⟩
    · exact Or.inl (DAccepts.mono hreach0 hacc)
    · exact Or.inr ⟨x'', hreach0.trans hreach'', hmk'', by rw [h2'', h2y]⟩
  · exact Or.inr ⟨x, Relation.ReflTransGen.single (dstep_srcTest_false hsrc), hmk, rfl⟩

/-- **The source enumeration reaches the source that works**: from any position
of the enumeration at or below a source from which the walk accepts within the
budget, the machine accepts. -/
theorem srcEnum {u₀ : spec.det.Node A} (hsrc : spec.IsSrc u₀) {n : ℕ}
    (hn : n < Nat.card (spec.det.Node A))
    (htgt : spec.det.IsTgt ((stepNext spec.det.Step)^[n] u₀)) :
    ∀ (z : DCount spec A) (ms : spec.Mode) (x : Fin (dHeads spec) → A),
      (∀ a : A, a ≤ x (dmk spec)) → dcount spec ms (dTup spec 2 x) = z →
      z ≤ dcount spec u₀.1 u₀.2 → DAccepts spec ((.srcTest ms : DetNode spec.Mode _), x) := by
  -- the source of the enumeration that works, once the machine stands on it
  have hhit : ∀ (ms : spec.Mode) (x : Fin (dHeads spec) → A), (∀ a : A, a ≤ x (dmk spec)) →
      ms = u₀.1 → dTup spec 2 x = u₀.2 →
      DAccepts spec ((.srcTest ms : DetNode spec.Mode _), x) := by
    intro ms x hmk hms ht
    have hsrc' : spec.IsSrc (ms, dTup spec 2 x) := by rw [hms, ht]; exact hsrc
    obtain ⟨y, hcopy, hreset, hkeep, hmky⟩ := exists_dStart x
    obtain ⟨cm₀, hcm₀⟩ := exists_modeAt_ix0 ms
    have hstart := dstep_start (ms := ms) hcopy hreset hkeep hmky
    rw [hcm₀] at hstart
    have h0y : dTup spec 0 y = u₀.2 := funext fun i => (hcopy i).trans (congrFun ht i)
    have hticks : Ticks n (dcount spec cm₀ (dTup spec 3 y)) :=
      ticks_bot (dcount_isBot hcm₀ fun i a => hreset i a) (by rw [card_dcount]; exact hn)
    refine DAccepts.mono (Relation.ReflTransGen.head (dstep_srcTest_true hsrc')
      (Relation.ReflTransGen.single hstart))
      (walkAcc ms n ms cm₀ y (by rw [hmky]; exact hmk) hticks ?_)
    rw [h0y, hms]
    exact htgt
  intro z
  induction z using order_induction_down with
  | hmax z hztop =>
    intro ms x hmk hz hle
    obtain ⟨h1, h2⟩ := dcount_inj (hz.trans (le_antisymm hle (hztop _)))
    exact hhit ms x hmk h1 h2
  | hstep z z' hlt hnb ih =>
    intro ms x hmk hz hle
    haveI : Nonempty A := ⟨x (dmk spec)⟩
    by_cases hhitq : dcount spec ms (dTup spec 2 x) = dcount spec u₀.1 u₀.2
    · obtain ⟨h1, h2⟩ := dcount_inj hhitq
      exact hhit ms x hmk h1 h2
    · have hz'le : z' ≤ dcount spec u₀.1 u₀.2 := by
        by_contra hcon
        exact hnb _ ⟨lt_of_le_of_ne hle (by rw [← hz]; exact hhitq), not_le.mp hcon⟩
      rcases srcTried ms x hmk with hacc | ⟨x₁, hreach₁, hmk₁, h2₁⟩
      · exact hacc
      · have hz₁ : dcount spec ms (dTup spec 2 x₁) = z := by rw [h2₁]; exact hz
        by_cases htop2 : ∀ (i : Fin spec.k) (a : A), a ≤ x₁ (dblk spec 2 i)
        · -- the block is at its greatest tuple: reset it and take the next source mode
          obtain ⟨ms', hms'⟩ : ∃ ms', modeAt spec (nextIx spec (ixOf spec ms)) = some ms' := by
            rcases hnx : modeAt spec (nextIx spec (ixOf spec ms)) with _ | ms'
            · refine absurd hlt (not_lt.mpr ?_)
              rw [← hz₁]
              exact dcount_isTop htop2 hnx z'
            · exact ⟨ms', rfl⟩
          obtain ⟨y₂, hmin₂, hkeep₂⟩ := exists_dReset 2 x₁
          have hmk₂ : ∀ a : A, a ≤ y₂ (dmk spec) := by rw [hkeep₂.2]; exact hmk₁
          refine DAccepts.mono ((((hreach₁.tail
            (dstep_srcNext_false (lexRel_top hmk₁ htop2))).tail
              (dstep_srcReset hmin₂ hkeep₂)).tail (dstep_srcMode hms' y₂)))
            (ih ms' y₂ hmk₂ ?_ hz'le)
          refine covBy_unique ?_ ⟨hlt, fun a ha ha' => hnb a ⟨ha, ha'⟩⟩
          rw [← hz₁]
          exact dcount_covBy_mode hms' htop2 fun i a => hmin₂ i a
        · -- the block can be stepped
          obtain ⟨y₂, hlex, hsucc, hother⟩ := exists_lexRel_succ (dblk_inj spec 2) hmk₁ htop2
          have hsucc' : TupSucc (dTup spec 2 x₁) (dTup spec 2 y₂) := hsucc
          have hmk₂ : ∀ a : A, a ≤ y₂ (dmk spec) := by
            rw [hother (dmk spec) (dmk_lt_prot spec) fun i => dmk_ne_blk2 i]
            exact hmk₁
          refine DAccepts.mono (hreach₁.tail (dstep_srcNext_true hlex)) (ih ms y₂ hmk₂ ?_ hz'le)
          refine covBy_unique ?_ ⟨hlt, fun a ha ha' => hnb a ⟨ha, ha'⟩⟩
          rw [← hz₁]
          exact dcount_covBy_tup ms hsucc'

/-! ### The machine of a specification -/

omit [Finite A] in
theorem deterministic_dP : (dP spec).Deterministic A := by
  refine deterministic_wireP (dFam spec) (dWire spec) .init fun c => ?_
  cases c with
  | init => exact deterministic_moveP _
  | srcMode i => exact deterministic_exitP _
  | srcTest ms => exact deterministic_evalP _ _ _ _
  | srcNext ms => exact deterministic_lexNextP
  | srcReset ms => exact deterministic_moveP _
  | start ms => exact deterministic_moveP _
  | tgtTest ms m cm => exact deterministic_evalP _ _ _ _
  | candMode ms m cm i => exact deterministic_moveP _
  | candTest ms m cm m' => exact deterministic_evalP _ _ _ _
  | candNext ms m cm m' => exact deterministic_lexNextP
  | commit ms m cm m' => exact deterministic_moveP _
  | tick ms m cm => exact deterministic_lexNextP
  | tickReset ms m cm => exact deterministic_moveP _
  | dead => exact deterministic_exitP _

variable (spec A) in
/-- **The deterministic machine of a specification accepts exactly what the
determinized specification does.** Soundness is the invariant of
`DescriptiveComplexity.HeadProgram.dInv`; completeness is the source enumeration,
each source walked out to its end – or to the budget, which
`DescriptiveComplexity.exists_iterate_lt_card` says is long enough. -/
theorem accepts_dP [Nonempty A] :
    ((dP spec).compile true).Accepts A ↔ spec.det.Accepts A := by
  have hruns := runs_wireP (C := DetNode spec.Mode (modeCard spec)) (dFam spec)
    (dWire spec) (runs_dFam (A := A) spec) (headLocal2_dRel (A := A) spec) .init
  rw [accepts_compile_true (dP spec) (deterministic_dP (spec := spec) (A := A))]
  constructor
  · rintro ⟨x, y, -, hreach⟩
    obtain ⟨u, hwalk, hexit⟩ := hruns.sound hreach
    exact accepts_of_dExit spec x hwalk hexit
  · rintro ⟨u₀, v, hu₀, hv, hreach⟩
    have hu₀' : spec.IsSrc u₀ := hu₀
    obtain ⟨n, hn, hiter⟩ := exists_iterate_lt_card
      ((reach_iff_iterate TCSpec.det_functional u₀ v).mp hreach)
    have htgt' : spec.det.IsTgt ((stepNext spec.det.Step)^[n] u₀) := by rw [hiter]; exact hv
    obtain ⟨mn, hmn⟩ : ∃ mn : A, ∀ a : A, mn ≤ a := by
      have := Fintype.ofFinite A
      have hune : (Finset.univ : Finset A).Nonempty := ⟨Classical.arbitrary A, Finset.mem_univ _⟩
      exact ⟨Finset.univ.min' hune, fun a => Finset.min'_le _ a (Finset.mem_univ a)⟩
    obtain ⟨x₁, hmk₁, hkeep₁⟩ := exists_dPark (spec := spec) (fun _ => mn)
    obtain ⟨ms₀, hms₀⟩ := exists_modeAt_ix0 (spec := spec) u₀.1
    have hbot : ∀ (i : Fin spec.k) (a : A), dTup spec 2 x₁ i ≤ a := by
      intro i a
      rw [show dTup spec 2 x₁ i = x₁ (dblk spec 2 i) from rfl, hkeep₁ 2 i]
      exact hmn a
    have hacc : DAccepts spec ((.init : DetNode spec.Mode _), fun _ => mn) :=
      DAccepts.mono (Relation.ReflTransGen.head (dstep_init hmk₁ hkeep₁)
        (Relation.ReflTransGen.single (dstep_srcMode hms₀ x₁)))
        (srcEnum (spec := spec) hu₀' hn htgt' (dcount spec ms₀ (dTup spec 2 x₁)) ms₀ x₁ hmk₁ rfl
          (dcount_isBot hms₀ hbot _))
    obtain ⟨u, z, hwalk, hexit⟩ := hacc
    obtain ⟨y', -, hy'⟩ := hruns.complete ⟨u, hwalk, hexit⟩
    exact ⟨fun _ => mn, y', fun _ => hmn, hy'⟩

end Machine

end HeadProgram

/-! ### The capture theorem -/

/-- **The capture theorem for FO(DTC)**: a problem is definable by a single
*deterministic* transitive closure exactly when a **deterministic** two-way
multi-head automaton recognizes it. One direction is
`DescriptiveComplexity.dtcDefinable_of_automaton` – a configuration is a node of a
specification, and determinism of the control is functionality of the walk –
and the other is the machine built here: it scans where the machine of
`DescriptiveComplexity.HeadCapture` guesses, and counts so that a walk leading nowhere
is abandoned. -/
theorem dtcDefinable_iff_automaton {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} :
    DTCDefinable P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k) (_ : M.IsDeterministic),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
        P A ↔ M.Accepts A := by
  constructor
  · rintro ⟨spec, hspec⟩
    refine ⟨HeadProgram.dHeads spec, (HeadProgram.dP spec).compile true,
      HeadProgram.isDeterministic_compile_true _, fun A _ _ _ _ => ?_⟩
    rw [hspec A, ← HeadProgram.accepts_dP spec A]
  · rintro ⟨k, M, hdet, hM⟩
    exact dtcDefinable_of_automaton M hdet hM

/-- **LOGSPACE is the class of the deterministic two-way multi-head
automata**: membership in `DescriptiveComplexity.LOGSPACE` is recognizability by such
a machine, the deterministic counterpart of
`DescriptiveComplexity.mem_NL_iff_automaton`. -/
theorem mem_LOGSPACE_iff_automaton {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} :
    P ∈ LOGSPACE ↔ ∃ (k : ℕ) (M : HeadAutomaton L k) (_ : M.IsDeterministic),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
        P A ↔ M.Accepts A :=
  (mem_LOGSPACE_iff P).trans dtcDefinable_iff_automaton

end DescriptiveComplexity
