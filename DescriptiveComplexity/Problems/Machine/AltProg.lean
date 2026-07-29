/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltTape
import DescriptiveComplexity.Problems.Qbf.Defs
import DescriptiveComplexity.MachinesAlt

/-!
# The machine of a quantified Boolean formula

The program half of `QBF k ≤ᶠᵒ[≤] ATMAccept k`: the states, symbols and
transitions of the alternating machine `M_φ` built inside an ordered QBF
instance, on the tape laid out in
`DescriptiveComplexity.Problems.Machine.AltTape`.

## The program

```
  sweep i:  ⊢ →  at each cell (x, b): if block i marks x and b is false,
                 write true or leave it – the round's choice        → ⊣
            ⊣ ←  back over the cells, unchanged                     → ⊢
            at ⊢: hand over to sweep i + 1, or start the check
  check c:  sweep over the cells accumulating
              flag := flag ∨ (the literal of c at this cell is `good`)
            at the far marker: settle the clause, or die
  accept:   the check has settled every clause
```

Three things differ from the SAT machine of
`DescriptiveComplexity.Problems.Machine.Hardness`.

**The guess is spread over `k` sweeps, and it accumulates.** A cell holds one
truth value, initially `false`, and sweep `i` may turn it to `true` when block
`i` marks the variable – never back. After the `k` sweeps the cell holds
`DescriptiveComplexity.qbfVal`, which is a disjunction over the blocks marking
the variable. So there are two transitions available at a cell block `i` marks
and holds `false`, and one everywhere else: the choice a round makes is exactly
its block's truth assignment.

**Only the guess is nondeterministic**, as in the SAT machine – which is what
makes the check work at either polarity: a universal block whose configuration
has a single available move is an existential one.

**The check serves both matrix shapes.** For a conjunctive matrix the flag
records that some literal of the clause is *satisfied*, and a clause is settled
when the flag is set; for a disjunctive one it records that some literal is
*violated*, and a term is settled – by accepting – when the flag is *clear*.
The two are the same clause with the truth value flipped
(`DescriptiveComplexity.xorB`), which is why one table serves both.

## Semantics first

Everything here is a plain predicate on tagged tuples: the machine is assembled
as a `DescriptiveComplexity.ATMData` and reasoned about directly. Only once its
correctness is proved does the first-order transcription happen.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Machine

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The instance, read -/

variable (k) in
/-- Being a clause – a term, for a disjunctive matrix – of the instance. -/
def QbfCl (c : A) : Prop := RelMap (qbfIsClause (k := k)) ![c]

variable (k) in
/-- The variable `x` occurs positively in the clause `c`. -/
def QbfPos (c x : A) : Prop := RelMap (qbfPosIn (k := k)) ![c, x]

variable (k) in
/-- The variable `x` occurs negatively in the clause `c`. -/
def QbfNeg (c x : A) : Prop := RelMap (qbfNegIn (k := k)) ![c, x]

/-- The variable `x` carries the mark of block `i`. -/
def QbfBlk (i : Fin k) (x : A) : Prop := RelMap (qbfBlock i) ![x]

/-- The variable `x` carries the mark of the block of index `i`, where `i` is
allowed to be the sentinel `k`: at the sentinel, no mark. -/
def QbfBlkAt (i : Fin (k + 1)) (x : A) : Prop := ∃ j : Fin k, (j : ℕ) = (i : ℕ) ∧ QbfBlk j x

variable (k) in
/-- **The literal test**: the cell `x`, holding the truth value `v`, satisfies
the clause `c`. This is the first-order test on the source structure that the
transition relation performs. -/
def QbfLit (c x : A) (v : Bool) : Prop :=
  (QbfPos k c x ∧ v = true) ∨ (QbfNeg k c x ∧ v = false)

/-- The truth value the check phase tests: the value itself for a conjunctive
matrix, its negation for a disjunctive one, so that the flag records a
satisfied literal in the first case and a violated one in the second. -/
def xorB (cnf v : Bool) : Bool := if cnf then v else !v

variable (k) in
/-- `c` is the lowest clause. -/
def QbfMinCl (c : A) : Prop := QbfCl k c ∧ ∀ e, QbfCl k e → c ≤ e

variable (k) in
/-- `c` is the highest clause. -/
def QbfMaxCl (c : A) : Prop := QbfCl k c ∧ ∀ e, QbfCl k e → e ≤ c

variable (k) in
/-- `c'` is the clause immediately above `c`. -/
def QbfNextCl (c c' : A) : Prop :=
  QbfCl k c ∧ QbfCl k c' ∧ c < c' ∧ ∀ e, QbfCl k e → c < e → c' ≤ e

/-! ### The elements of the machine -/

/-- The least element of the instance, to which every constant of the machine
is pinned. -/
def qbotA : A := (Finite.exists_min (id : A → A)).choose

omit [(Language.qbf k).Structure A] in
theorem qbotA_le (a : A) : qbotA (A := A) ≤ a := (Finite.exists_min (id : A → A)).choose_spec a

omit [(Language.qbf k).Structure A] in
theorem isMinTup2_qbot : IsMinTup2 (fun _ => qbotA (A := A)) := ⟨qbotA_le, qbotA_le⟩

variable (k A) in
/-- The universe of the machine: tagged pairs. -/
abbrev AltV : Type := AltTag k × (Fin 2 → A)

/-- A constant of the machine at the sweep index `i`. -/
def acstI (t : AltBase) (i : Fin (k + 1)) : AltV k A := ((t, i), fun _ => qbotA)

/-- A tag carrying one element at the sweep index `i`. -/
def aoneI (t : AltBase) (i : Fin (k + 1)) (a : A) : AltV k A := ((t, i), ![a, qbotA])

/-- A constant of the machine: a tag on the pair of least elements. -/
abbrev acst (t : AltBase) : AltV k A := acstI t 0

/-- A tag carrying one element, pinned in the second coordinate. -/
abbrev aone (t : AltBase) (a : A) : AltV k A := aoneI t 0 a

/-! #### Symbols -/

/-- The left-marker symbol. -/
abbrev symStart : AltV k A := acst .sStart

/-- The right-marker symbol. -/
abbrev symEnd : AltV k A := acst .sEnd

/-- The blank symbol. -/
abbrev symBlank : AltV k A := acst .sBlank

/-- The symbol of the cell of `x`, holding the truth value `v`. -/
abbrev symV (v : Bool) (x : A) : AltV k A := aone (.sVal v) x

/-! #### Positions -/

/-- The left-marker cell. -/
abbrev posStart : AltV k A := acst .pStart

/-- The cell of the element `x`. -/
abbrev posCell (x : A) : AltV k A := aone .pCell x

/-- The right-marker cell. -/
abbrev posEnd : AltV k A := acst .pEnd

/-! #### States -/

/-- Sweeping in direction `d` during the sweep of index `i`. The index runs
over `Fin (k + 1)`, but only the values below `k` are ever reached. -/
abbrev stG (i : Fin (k + 1)) (d : Bool) : AltV k A := acstI (.qG d) i

/-- Checking the clause `c`, flag `f`, sweeping in direction `d`. -/
abbrev stChk (f d : Bool) (c : A) : AltV k A := aone (.qChk f d) c

/-- The accepting state. -/
abbrev stAcc : AltV k A := acst .qAcc

/-! ### The transition table -/

/-- Which tagged tuples are transitions. The payload is pinned exactly as far
as the transition needs it, the sweep index is required to be a real sweep, and
the clause coordinates are required to be clauses, so that no junk element is
ever a transition. -/
def AltTr (cnf : Bool) (τ : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => IsMinTup2 τ.2 ∧ (τ.1.2 : ℕ) = 0 ∧ 0 < k
  | .tGKeep _ => (∀ a : A, τ.2 1 ≤ a) ∧ (τ.1.2 : ℕ) < k
  | .tGSet => (∀ a : A, τ.2 1 ≤ a) ∧ QbfBlkAt τ.1.2 (τ.2 0)
  | .tGTurn => IsMinTup2 τ.2 ∧ (τ.1.2 : ℕ) < k
  | .tGBack _ => (∀ a : A, τ.2 1 ≤ a) ∧ (τ.1.2 : ℕ) < k
  | .tGNext => IsMinTup2 τ.2 ∧ (τ.1.2 : ℕ) + 1 < k
  | .tGEndAcc => IsMinTup2 τ.2 ∧ (τ.1.2 : ℕ) + 1 = k ∧ cnf = true ∧ ∀ e : A, ¬QbfCl k e
  | .tGEndChk => (∀ a : A, τ.2 1 ≤ a) ∧ (τ.1.2 : ℕ) + 1 = k ∧ QbfMinCl k (τ.2 0)
  | .tChk _ _ _ => QbfCl k (τ.2 0) ∧ (τ.1.2 : ℕ) = 0
  | .tTurnNext _ => QbfNextCl k (τ.2 0) (τ.2 1) ∧ (τ.1.2 : ℕ) = 0
  | .tTurnAcc _ =>
      (∀ a : A, τ.2 1 ≤ a) ∧ (τ.1.2 : ℕ) = 0 ∧ QbfCl k (τ.2 0) ∧ (cnf = true → QbfMaxCl k (τ.2 0))
  | _ => False

/-- The state a transition applies in. The accepting turn fires at the flag
`cnf`: set, for a conjunctive matrix, where it means the clause is satisfied;
clear, for a disjunctive one, where it means no literal of the term is
violated. -/
def AltSrc (cnf : Bool) (τ q : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => q = stG τ.1.2 true
  | .tGKeep _ => q = stG τ.1.2 true
  | .tGSet => q = stG τ.1.2 true
  | .tGTurn => q = stG τ.1.2 true
  | .tGBack _ => q = stG τ.1.2 false
  | .tGNext => q = stG τ.1.2 false
  | .tGEndAcc => q = stG τ.1.2 false
  | .tGEndChk => q = stG τ.1.2 false
  | .tChk _ f d => q = stChk f d (τ.2 0)
  | .tTurnNext d => q = stChk true d (τ.2 0)
  | .tTurnAcc d => q = stChk cnf d (τ.2 0)
  | _ => False

/-- The symbol a transition reads. -/
def AltRead (τ a : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => a = symStart
  | .tGKeep b => a = symV b (τ.2 0)
  | .tGSet => a = symV false (τ.2 0)
  | .tGTurn => a = symEnd
  | .tGBack b => a = symV b (τ.2 0)
  | .tGNext => a = symStart
  | .tGEndAcc => a = symStart
  | .tGEndChk => a = symStart
  | .tChk v _ _ => a = symV v (τ.2 1)
  | .tTurnNext d => a = if d then symEnd else symStart
  | .tTurnAcc d => a = if d then symEnd else symStart
  | _ => False

/-- The state a transition moves to. The only place the instance is consulted
is the check clause, where the new flag depends on
`DescriptiveComplexity.QbfLit`. -/
def AltDst (cnf : Bool) (τ q : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => q = stG τ.1.2 true
  | .tGKeep _ => q = stG τ.1.2 true
  | .tGSet => q = stG τ.1.2 true
  | .tGTurn => q = stG τ.1.2 false
  | .tGBack _ => q = stG τ.1.2 false
  | .tGNext => q = stG (τ.1.2 + 1) true
  | .tGEndAcc => q = stAcc
  | .tGEndChk => q = stChk false true (τ.2 0)
  | .tChk v f d =>
      (q = stChk true d (τ.2 0) ∧ (f = true ∨ QbfLit k (τ.2 0) (τ.2 1) (xorB cnf v))) ∨
        (q = stChk false d (τ.2 0) ∧ f = false ∧ ¬QbfLit k (τ.2 0) (τ.2 1) (xorB cnf v))
  | .tTurnNext d => q = stChk false (!d) (τ.2 1)
  | .tTurnAcc _ => q = stAcc
  | _ => False

/-- The symbol a transition writes: only a guessing sweep ever changes the
tape, and only from `false` to `true`. -/
def AltWrite (τ a : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => a = symStart
  | .tGKeep b => a = symV b (τ.2 0)
  | .tGSet => a = symV true (τ.2 0)
  | .tGTurn => a = symEnd
  | .tGBack b => a = symV b (τ.2 0)
  | .tGNext => a = symStart
  | .tGEndAcc => a = symStart
  | .tGEndChk => a = symStart
  | .tChk v _ _ => a = symV v (τ.2 1)
  | .tTurnNext d => a = if d then symEnd else symStart
  | .tTurnAcc d => a = if d then symEnd else symStart
  | _ => False

/-- Which transitions move the head right: a sweep goes in its own direction,
and every transition that fires at a marker moves away from it. -/
def AltRight (τ : AltV k A) : Prop :=
  match τ.1.1 with
  | .tGStart => True
  | .tGKeep _ => True
  | .tGSet => True
  | .tGTurn => False
  | .tGBack _ => False
  | .tGNext => True
  | .tGEndAcc => True
  | .tGEndChk => True
  | .tChk _ _ d => d = true
  | .tTurnNext d => d = false
  | .tTurnAcc d => d = false
  | _ => False

/-- Accepting states: just `DescriptiveComplexity.stAcc`. -/
def AltAccSt (q : AltV k A) : Prop := q.1.1 = AltBase.qAcc

/-- Start states: the rightward sweep of index `0`. -/
def AltStartSt (q : AltV k A) : Prop := q.1 = (AltBase.qG true, 0) ∧ IsMinTup2 q.2

/-- The quantifier block an element belongs to: its sweep index for a sweeping
state, the last block for the check and the accepting state, and block `0` for
everything else – `DescriptiveComplexity.ATMData.BlocksWellFormed` asks *every*
element for a block, junk included. -/
def altBlockOf (q : AltV k A) : ℕ :=
  match q.1.1 with
  | .qG _ => if (q.1.2 : ℕ) < k then (q.1.2 : ℕ) else 0
  | .qChk _ _ => k - 1
  | .qAcc => k - 1
  | _ => 0

/-- The block marks of the machine. -/
def AltBlkOf (j : ℕ) (q : AltV k A) : Prop := j = altBlockOf q

variable (k A) in
/-- **The alternating machine of a quantified Boolean formula.** -/
def altMachine (cnf : Bool) : ATMData (AltV k A) where
  Posn := AltPosn
  Le := tagTupleLe
  Tr := AltTr cnf
  Start := AltStartSt
  Acc := AltAccSt
  Blank := AltBlank
  Right := AltRight
  Src := AltSrc cnf
  Read := AltRead
  Dst := AltDst cnf
  Write := AltWrite
  Inp := AltInp
  Blk := AltBlkOf

/-! ### The instance obligations

Everything `DescriptiveComplexity.TMData.WellFormed` and
`DescriptiveComplexity.ATMData.BlocksWellFormed` ask, discharged before any run
is considered. -/

theorem altMachine_wellFormed (cnf : Bool) :
    (altMachine k A cnf).toTMData.WellFormed :=
  ⟨isLinOrd_altTagTupleLe, exists_altPosn, fun _ _ _ ha hb => altInp_functional ha hb,
    exists_altBlank, fun _ _ ha hb => altBlank_unique ha hb⟩

omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem altBlockOf_lt (hk : 0 < k) (q : AltV k A) : altBlockOf q < k := by
  unfold altBlockOf
  split
  · split
    · assumption
    · exact hk
  · omega
  · omega
  · exact hk

omit [(Language.qbf k).Structure A] in
/-- A sweeping state's block is its sweep index. -/
theorem altBlockOf_stG {i : Fin (k + 1)} (hi : (i : ℕ) < k) (d : Bool) :
    altBlockOf (stG i d : AltV k A) = (i : ℕ) := by
  simp only [altBlockOf, acstI, stG]
  exact if_pos hi

omit [(Language.qbf k).Structure A] in
theorem altBlockOf_stChk (f d : Bool) (c : A) :
    altBlockOf (stChk f d c : AltV k A) = k - 1 := rfl

omit [(Language.qbf k).Structure A] in
theorem altBlockOf_stAcc : altBlockOf (stAcc : AltV k A) = k - 1 := rfl

/-- **The block structure is well formed**: every element has exactly one
block, a transition stays in its block or moves to the next one, and a start
state is in block `0`. -/
theorem altMachine_blocksWellFormed (cnf : Bool) (hk : 0 < k) :
    (altMachine k A cnf).BlocksWellFormed k := by
  refine ⟨fun q => ⟨altBlockOf q, altBlockOf_lt hk q, rfl, fun j' hj' => hj'⟩, ?_, ?_⟩
  · rintro τ q q' j j' hτ hsrc hdst rfl rfl
    revert hτ hsrc hdst
    change AltTr cnf τ → AltSrc cnf τ q → AltDst cnf τ q' →
      altBlockOf q ≤ altBlockOf q' ∧ altBlockOf q' ≤ altBlockOf q + 1
    unfold AltTr AltSrc AltDst
    cases hb : τ.1.1 <;> intro hτ hsrc hdst <;>
      first
        | exact hτ.elim
        | (subst hsrc; subst hdst; exact ⟨le_refl _, Nat.le_succ _⟩)
        | (subst hsrc
           rcases hdst with ⟨rfl, -⟩ | ⟨rfl, -, -⟩ <;> exact ⟨le_refl _, Nat.le_succ _⟩)
        | (subst hsrc; subst hdst
           have hne : τ.1.2 ≠ Fin.last k := by
             intro hcon
             rw [hcon] at hτ
             simp only [Fin.val_last] at hτ
             omega
           have hlt : ((τ.1.2 + 1 : Fin (k + 1)) : ℕ) = (τ.1.2 : ℕ) + 1 :=
             Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr hne)
           rw [altBlockOf_stG (show (τ.1.2 : ℕ) < k by omega) false,
             altBlockOf_stG (show ((τ.1.2 + 1 : Fin (k + 1)) : ℕ) < k by omega) true, hlt]
           omega)
        | (subst hsrc; subst hdst
           rw [altBlockOf_stG (show (τ.1.2 : ℕ) < k by omega) false, altBlockOf_stChk]
           omega)
        | (subst hsrc; subst hdst
           rw [altBlockOf_stG (show (τ.1.2 : ℕ) < k by omega) false, altBlockOf_stAcc]
           omega)
  · rintro q ⟨hq, -⟩
    change (0 : ℕ) = altBlockOf q
    simp only [altBlockOf, hq]
    exact (if_pos hk).symm

end Machine

end AltQbf

end DescriptiveComplexity
