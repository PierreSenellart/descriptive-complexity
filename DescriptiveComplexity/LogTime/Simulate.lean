/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.BitLogic

/-!
# The upper fence: a machine's acceptance is a sentence of the bit-level logic

**Every problem decided by an alternating machine with a logarithmic clock and a
bit-level base is defined by a prenex sentence of `FO(≤, +, BIT)`**
(`DescriptiveComplexity.LTDecidable.bitDefinable`). With
`DescriptiveComplexity.BitDefinable.ltDecidable` this makes the model *exactly*
that logic.

## The four moving parts

* **The guesses are quantifiers.** A register holds an element of the universe,
  and filling it existentially or universally is `∃` or `∀` – the alternation
  structure of the machine is the quantifier prefix of the sentence, on the
  nose.
* **A query is an atom.** Reading the instance at a tuple of registers is an
  atomic formula of the input vocabulary; no encoding of addresses is involved,
  which is the whole reason the model fits a structure-based framework.
* **A read is an atom too.** `DescriptiveComplexity.BaseTest.bit` is the bit
  atom of the logic and nothing more: both name a bit position by an *element*,
  so the translation has nothing to do.
* **A sweep is a guessed trace.** This is the content. A sweep carries `σ` bits
  of state past each of the `posCount A` bit positions, so its entire history is
  `σ` bit *vectors over the positions* – and a bit vector over the positions **is
  an element of the universe**. The formula therefore guesses `σ` elements, says
  with `DescriptiveComplexity.BitIx` that the bit of the `j`-th at each index is
  what the transition of the sweep produces there, and reads acceptance off the
  top. Determinism of the sweep makes the guess unique, so the existential is
  faithful.

## Two places the index naming pays

The trace is pinned by a condition relating the bit at an index to the bit at
the index *below*, and under the index naming that is the cover relation of the
order (`DescriptiveComplexity.stepAt`), where naming positions by their place
value made it a doubling. The end of the tape is likewise *read* rather than
computed: `DescriptiveComplexity.IsTopIx` is “the highest index carrying a bit of
the greatest element”, an order condition on the bit atom
(`DescriptiveComplexity.isTopIx_iff_bits`).

## The one asymmetry: the last position

A bit vector over *all* the positions need not be a rank – the universe need not
have a power of two elements – so the trace elements can only carry the state up
to the index below the top (`DescriptiveComplexity.exists_orank_testBit`). The
state after the top position is therefore carried by `σ` further elements used
as *flags*, one bit each, read as “nonzero rank”. Everything else in the
construction is uniform.

## Two statements, one construction

Landing in `FO(≤, +, BIT)` is what the construction below does; landing in
`FO(≤, +, ×)` is that plus one lemma – `DescriptiveComplexity.powArithDef`, the
definability of `i ↦ 2 ^ i`. Both are unconditional, and the statement of record
here is the first, `DescriptiveComplexity.LTDecidable.bitDefinable`: it is the
classical logic for AC⁰, and it is what the converse direction reads.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Boolean expressions, read as formulas -/

section BitExprDef

variable {L : Language.{0, 0}} {α : Type} {V : Type}

/-- A Boolean expression of definable bits is definable: the translation is a
recursion over the expression, not an enumeration of its truth table. -/
theorem bitDef_bitExpr {val : V → ArithRel L α} (h : ∀ z, BitDef (val z)) :
    ∀ e : BitExpr V,
      BitDef (L := L) (α := α) (fun A _ _ _ _ v => e.Holds fun z => val z A v)
  | .var z => (h z).congr fun _A _ _ _ _ _v => Iff.rfl
  | .tt => BitDef.top.congr fun _A _ _ _ _ _v => Iff.rfl
  | .ff => BitDef.bot.congr fun _A _ _ _ _ _v => Iff.rfl
  | .not e => (bitDef_bitExpr h e).not.congr fun _A _ _ _ _ _v => Iff.rfl
  | .and e f => ((bitDef_bitExpr h e).and (bitDef_bitExpr h f)).congr
      fun _A _ _ _ _ _v => Iff.rfl
  | .or e f => ((bitDef_bitExpr h e).or (bitDef_bitExpr h f)).congr
      fun _A _ _ _ _ _v => Iff.rfl

end BitExprDef

/-! ### The trace of a sweep -/

section SweepTrace

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

/-- **The transition of a sweep at an index**, as a statement about a guessed
trace: the state bits before the position are the initial ones at the lowest
index, and the trace bits at the index *covered* by this one otherwise. Under
the index naming the previous position is the predecessor in the order, so
nothing but `≤` is needed to find it. -/
def stepAt (S : Sweep ρ) (x : Fin ρ → A) (t : Fin S.σ → A) (i : A) (j : Fin S.σ) : Prop :=
  (S.step j).Holds (Sum.elim
    (fun j' => (orank i = 0 ∧ S.init j' = true) ∨
      ∃ i' : A, (i' < i ∧ ∀ k : A, i' < k → i ≤ k) ∧ BitIx i' (t j'))
    fun k => BitIx i (x k))

/-- **What the formula asks of the guessed trace and flags**: the trace records
the state after each index below the top, the flags record the state after the
top position, and the acceptance condition holds of the flags – of the initial
state, if the universe has no bit position at all. -/
def SweepWitness (S : Sweep ρ) (x : Fin ρ → A) (t f : Fin S.σ → A) : Prop :=
  (∀ i : A, IsLowIx i → ∀ j, (BitIx i (t j) ↔ stepAt S x t i j)) ∧
    (∀ i : A, IsTopIx i → ∀ j, (orank (f j) ≠ 0 ↔ stepAt S x t i j)) ∧
      ((∃ i : A, IsTopIx i) → S.acc.Holds fun j => orank (f j) ≠ 0) ∧
        ((¬∃ i : A, IsTopIx i) → S.acc.eval S.init = true)

/-- The state the witnesses record after position `i`: a trace bit below the
top, a flag at the top. -/
def storedAfter (S : Sweep ρ) (t f : Fin S.σ → A) (i : ℕ) (j : Fin S.σ) : Prop :=
  if i + 1 < posCount A then (orank (t j)).testBit i = true else orank (f j) ≠ 0

/-- A top index exists exactly when the universe has more than one element. -/
theorem exists_isTopIx_iff : (∃ i : A, IsTopIx i) ↔ 0 < posCount A := by
  constructor
  · rintro ⟨i, hi⟩
    rw [IsTopIx] at hi
    omega
  · intro h
    obtain ⟨i, hi⟩ := exists_orank_eq (A := A)
      (lt_card_of_lt_posCount (A := A) (Nat.sub_lt h Nat.one_pos))
    exact ⟨i, by rw [IsTopIx, hi]; omega⟩

/-- **The transition read from the trace is the transition of the sweep**: at
the index `i`, the guessed bits say exactly what the automaton computes from the
state before that position. -/
theorem stepAt_iff (S : Sweep ρ) (x : Fin ρ → A) (t : Fin S.σ → A) (i : A) (j : Fin S.σ) :
    stepAt S x t i j ↔ (S.step j).eval (Sum.elim
      (fun j' => if orank i = 0 then S.init j' else (orank (t j')).testBit (orank i - 1))
      fun k => (orank (x k)).testBit (orank i)) = true := by
  rw [stepAt, ← BitExpr.holds_iff_eval]
  refine BitExpr.holds_congr ?_ _
  rintro (j' | k)
  · simp only [Sum.elim_inl]
    rcases Nat.eq_zero_or_pos (orank i) with h0 | hpos
    · rw [if_pos h0]
      constructor
      · rintro (⟨-, h⟩ | ⟨i', ⟨hlt, -⟩, -⟩)
        · exact h
        · exact absurd (orank_lt_orank hlt) (by omega)
      · intro h
        exact Or.inl ⟨h0, h⟩
    · rw [if_neg (by omega)]
      constructor
      · rintro (⟨h0, -⟩ | ⟨i', ⟨hlt, hcov⟩, hbit⟩)
        · exact absurd h0 (by omega)
        · have hsucc : orank i = orank i' + 1 :=
            orank_eq_succ_of_pred hlt fun a ha => absurd (hcov a ha.1) (not_le_of_gt ha.2)
          rw [bitIx_iff] at hbit
          rw [show orank i - 1 = orank i' by omega]
          exact hbit
      · intro h
        obtain ⟨i', hi', hlt, hno⟩ := exists_pred_of_orank_succ (A := A)
          (show orank i = (orank i - 1) + 1 by omega)
        refine Or.inr ⟨i', ⟨hlt, fun k hk => le_of_not_gt fun hcon => hno k ⟨hk, hcon⟩⟩, ?_⟩
        rw [bitIx_iff, hi']
        exact h
  · simp only [Sum.elim_inr]
    exact bitIx_iff

/-- **The guessed trace is the run**: the witnesses of the formula record,
position by position, the states of the sweep. Determinism does the work – the
local conditions pin the trace by induction along the indices. -/
theorem storedAfter_iff_state (S : Sweep ρ) (x : Fin ρ → A) (t f : Fin S.σ → A)
    (hw : SweepWitness S x t f) :
    ∀ i, i < posCount A → ∀ j, (storedAfter S t f i j ↔ S.state x (i + 1) j = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi j
    obtain ⟨e, he⟩ := exists_orank_eq (A := A) (lt_card_of_lt_posCount (A := A) hi)
    have hprev : ∀ j', (if i = 0 then S.init j' else (orank (t j')).testBit (i - 1)) =
        S.state x i j' := by
      intro j'
      cases i with
      | zero => simp
      | succ i' =>
        simp only [Nat.succ_sub_one, if_neg (Nat.succ_ne_zero i')]
        have hi' : i' < posCount A := by omega
        have hstored : storedAfter S t f i' j' ↔ S.state x (i' + 1) j' = true :=
          IH i' (by omega) hi' j'
        have hlow : storedAfter S t f i' j' ↔ (orank (t j')).testBit i' = true := by
          rw [storedAfter, if_pos (by omega)]
        have hiff : ((orank (t j')).testBit i' = true) ↔ (S.state x (i' + 1) j' = true) :=
          hlow.symm.trans hstored
        by_cases hs : S.state x (i' + 1) j' = true
        · rw [hs, hiff.mpr hs]
        · have hb : (orank (t j')).testBit i' ≠ true := fun hc => hs (hiff.mp hc)
          simp only [Bool.not_eq_true] at hb hs
          rw [hb, hs]
    have hstep : stepAt S x t e j ↔ S.state x (i + 1) j = true := by
      rw [stepAt_iff S x t e j, he, S.state_succ x i j, funext hprev]
    rcases Nat.lt_or_ge (i + 1) (posCount A) with hlt | hge
    · have hlow : IsLowIx e := by rw [IsLowIx, he]; omega
      have hbit : ((orank (t j)).testBit i = true) ↔ BitIx e (t j) := by rw [bitIx_iff, he]
      rw [storedAfter, if_pos hlt, hbit, hw.1 e hlow j]
      exact hstep
    · have htop : IsTopIx e := by rw [IsTopIx, he]; omega
      rw [storedAfter, if_neg (by omega), hw.2.1 e htop j]
      exact hstep

/-- **The formula says what the sweep does.** -/
theorem sweepWitness_iff [Nonempty A] (S : Sweep ρ) (x : Fin ρ → A) :
    (∃ t f : Fin S.σ → A, SweepWitness S x t f) ↔ S.Accepts x := by
  constructor
  · rintro ⟨t, f, hw⟩
    rw [Sweep.Accepts, ← BitExpr.holds_iff_eval]
    rcases Nat.eq_zero_or_pos (posCount A) with h0 | hpos
    · have hnone : ¬∃ i : A, IsTopIx i := by
        rw [exists_isTopIx_iff]
        omega
      have := hw.2.2.2 hnone
      rw [h0, Sweep.state_zero, BitExpr.holds_iff_eval]
      exact this
    · have hstate := storedAfter_iff_state S x t f hw (posCount A - 1) (by omega)
      refine (BitExpr.holds_congr (fun j => ?_) _).mpr
        (hw.2.2.1 (exists_isTopIx_iff.mpr hpos))
      have h1 : posCount A - 1 + 1 = posCount A := by omega
      have := hstate j
      rw [storedAfter, if_neg (by omega), h1] at this
      exact this.symm
  · intro hacc
    rcases Nat.eq_zero_or_pos (posCount A) with h0 | hpos
    · obtain ⟨a⟩ := ‹Nonempty A›
      refine ⟨fun _ => a, fun _ => a, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [IsLowIx] at hi
        omega
      · intro i hi
        exact absurd (exists_isTopIx_iff.mp ⟨i, hi⟩) (by omega)
      · intro hex
        exact absurd (exists_isTopIx_iff.mp hex) (by omega)
      · intro _
        rw [Sweep.Accepts, h0, Sweep.state_zero] at hacc
        exact hacc
    · have hcard : 1 < Nat.card A := by
        have := (two_pow_lt_card_iff_lt_posCount (A := A) 0).mpr hpos
        simpa using this
      obtain ⟨zero, hzero⟩ := exists_orank_eq (A := A) (by omega : 0 < Nat.card A)
      obtain ⟨one, hone⟩ := exists_orank_eq (A := A) hcard
      classical
      -- the trace: one element per state bit, its bits the states of the run
      have htrace : ∀ j : Fin S.σ, ∃ t : A, ∀ i, i + 1 < posCount A →
          (orank t).testBit i = S.state x (i + 1) j := fun j =>
        exists_orank_testBit (A := A) fun i => S.state x (i + 1) j
      choose t ht using htrace
      have hprev : ∀ (i : A), orank i + 1 ≤ posCount A →
          (fun j' => if orank i = 0 then S.init j'
            else (orank (t j')).testBit (orank i - 1)) = S.state x (orank i) := by
        intro i hi
        funext j'
        obtain ⟨d, hd⟩ : ∃ d, orank i = d := ⟨_, rfl⟩
        rw [hd]
        cases d with
        | zero => simp
        | succ d' =>
          simp only [Nat.succ_sub_one, if_neg (Nat.succ_ne_zero d')]
          exact ht j' d' (by omega)
      refine ⟨t, fun j => if S.state x (posCount A) j = true then one else zero, ?_, ?_, ?_, ?_⟩
      · intro i hlow j
        rw [IsLowIx] at hlow
        rw [bitIx_iff, stepAt_iff S x t i j, hprev i (by omega), ← S.state_succ x (orank i) j,
          ht j (orank i) (by omega)]
      · intro i htop j
        rw [IsTopIx] at htop
        rw [stepAt_iff S x t i j, hprev i (by omega), ← S.state_succ x (orank i) j, htop]
        by_cases hs : S.state x (posCount A) j = true
        · simp [hs, hone]
        · simp [hs, hzero]
      · intro _
        rw [Sweep.Accepts, ← BitExpr.holds_iff_eval] at hacc
        refine (BitExpr.holds_congr (fun j => ?_) _).mp hacc
        by_cases hs : S.state x (posCount A) j = true
        · simp [hs, hone]
        · simp [hs, hzero]
      · intro hnone
        exact absurd (exists_isTopIx_iff.mpr hpos) hnone

end SweepTrace

/-! ### Definability of the machine -/

section MachineDef

variable {L : Language.{0, 0}} {α : Type} {ρ : ℕ}

/-- The transition condition at an index is definable. -/
theorem bitDef_stepAt (S : Sweep ρ) (reg : Fin ρ → α) (tr : Fin S.σ → α) (p : α)
    (j : Fin S.σ) :
    BitDef (L := L) (α := α) (fun _A _ _ _ _ v =>
      stepAt S (fun k => v (reg k)) (fun j' => v (tr j')) (v p) j) := by
  have hval : ∀ z : Fin S.σ ⊕ Fin ρ, BitDef (L := L) (α := α)
      (Sum.elim
        (fun j' : Fin S.σ => fun A _ _ _ _ (v : α → A) =>
          (orank (v p) = 0 ∧ S.init j' = true) ∨
            ∃ i' : A, (i' < v p ∧ ∀ k : A, i' < k → v p ≤ k) ∧ BitIx i' (v (tr j')))
        (fun k : Fin ρ => fun A _ _ _ _ (v : α → A) => BitIx (v p) (v (reg k))) z) := by
    rintro (j' | k)
    · have hcov : BitDef (L := L) (α := α ⊕ Fin 1) (fun A _ _ _ _ u =>
          ∀ k : A, u (Sum.inr 0) < k → u (Sum.inl p) ≤ k) :=
        ((bitDef_lt (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1)
          (Sum.inl (Sum.inr 0)) (Sum.inr 0)).imp
          (bitDef_le (Sum.inl (Sum.inl p)) (Sum.inr 0))).all
      refine (((bitDef_isZero p).and (BitDef.prop (S.init j' = true))).or
        ((((bitDef_lt (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inl p)).and hcov).and
          (bitDef_bit (Sum.inr 0) (Sum.inl (tr j')))).ex)).congr fun A _ _ _ _ v => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
    · exact (bitDef_bit p (reg k)).congr fun _A _ _ _ _ _v => Iff.rfl
  exact (bitDef_bitExpr hval (S.step j)).congr fun A _ _ _ _ v => by
    rw [stepAt]
    exact BitExpr.holds_congr (by rintro (j' | k) <;> exact Iff.rfl) _

/-- **A sweep is definable**: the formula guesses the trace and the flags, and
asks that they be the run. -/
theorem bitDef_sweep (S : Sweep ρ) (reg : Fin ρ → α) :
    BitDef (L := L) (α := α)
      (fun _A _ _ _ _ v => S.Accepts fun k => v (reg k)) := by
  classical
  -- variables: the ambient ones, then the trace, then the flags
  set γ : Type := (α ⊕ Fin S.σ) ⊕ Fin S.σ with hγ
  let amb : α → γ := fun a => Sum.inl (Sum.inl a)
  let tr : Fin S.σ → γ := fun j => Sum.inl (Sum.inr j)
  let fl : Fin S.σ → γ := fun j => Sum.inr j
  -- the local condition at an index below the top, with the index bound as `Sum.inr 0`
  have hlocal : BitDef (L := L) (α := γ) (fun A _ _ _ _ v =>
      ∀ i : A, IsLowIx i → ∀ j,
        (BitIx i (v (tr j)) ↔ stepAt S (fun k => v (amb (reg k)))
          (fun j' => v (tr j')) i j)) := by
    refine (((bitDef_isLowIx (L := L) (α := γ ⊕ Fin 1) (Sum.inr 0)).imp
      (BitDef.forallFin (R := fun j => fun A _ _ _ _ (v : (γ ⊕ Fin 1) → A) =>
          (BitIx (v (Sum.inr 0)) (v (Sum.inl (tr j))) ↔
            stepAt S (fun k => v (Sum.inl (amb (reg k))))
              (fun j' => v (Sum.inl (tr j'))) (v (Sum.inr 0)) j))
        fun j => (bitDef_bit (Sum.inr 0) (Sum.inl (tr j))).iff
          (bitDef_stepAt S (fun k => Sum.inl (amb (reg k))) (fun j' => Sum.inl (tr j'))
            (Sum.inr 0) j))).all).congr fun A _ _ _ _ v => ?_
    refine forall_congr' fun a => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
  -- the condition at the top index, recorded by the flags
  have htop : BitDef (L := L) (α := γ) (fun A _ _ _ _ v =>
      ∀ i : A, IsTopIx i → ∀ j,
        (orank (v (fl j)) ≠ 0 ↔ stepAt S (fun k => v (amb (reg k)))
          (fun j' => v (tr j')) i j)) := by
    refine (((bitDef_isTopIx (L := L) (α := γ ⊕ Fin 1) (Sum.inr 0)).imp
      (BitDef.forallFin (R := fun j => fun A _ _ _ _ (v : (γ ⊕ Fin 1) → A) =>
          (¬ orank (v (Sum.inl (fl j))) = 0 ↔
            stepAt S (fun k => v (Sum.inl (amb (reg k))))
              (fun j' => v (Sum.inl (tr j'))) (v (Sum.inr 0)) j))
        fun j => ((bitDef_isZero (Sum.inl (fl j))).not).iff
          (bitDef_stepAt S (fun k => Sum.inl (amb (reg k))) (fun j' => Sum.inl (tr j'))
            (Sum.inr 0) j))).all).congr fun A _ _ _ _ v => ?_
    exact forall_congr' fun a => by simp only [Sum.elim_inl, Sum.elim_inr]
  -- acceptance, read from the flags, or from the initial state if there are no positions
  have hex : BitDef (L := L) (α := γ) (fun A _ _ _ _ v => ∃ i : A, IsTopIx i) := by
    refine ((bitDef_isTopIx (L := L) (α := γ ⊕ Fin 1) (Sum.inr 0)).ex).congr
      fun A _ _ _ _ v => ?_
    exact exists_congr fun a => by simp only [Sum.elim_inr]
  have hacc : BitDef (L := L) (α := γ) (fun A _ _ _ _ v =>
      S.acc.Holds fun j => orank (v (fl j)) ≠ 0) :=
    bitDef_bitExpr (fun j => (bitDef_isZero (L := L) (α := γ) (fl j)).not) S.acc
  have hbody : BitDef (L := L) (α := γ) (fun A _ _ _ _ v =>
      SweepWitness S (fun k => v (amb (reg k))) (fun j => v (tr j)) fun j => v (fl j)) :=
    hlocal.and (htop.and ((hex.imp hacc).and
      (hex.not.imp (BitDef.prop (S.acc.eval S.init = true)))))
  refine (hbody.exs.exs).congr fun A _ _ _ _ v => ?_
  rw [← sweepWitness_iff S fun k => v (reg k)]
  constructor
  · rintro ⟨tw, fw, hw⟩
    exact ⟨tw, fw, hw⟩
  · rintro ⟨tw, fw, hw⟩
    exact ⟨tw, fw, hw⟩

/-- **A base test is definable**: sweeps by the construction above, reads and
queries as atoms, and the Boolean structure by the closure lemmas. -/
theorem bitDef_baseTest (t : BaseTest L ρ) (reg : Fin ρ → α) :
    BitDef (L := L) (α := α) (fun _A _ _ _ _ v => t.Holds fun k => v (reg k)) := by
  induction t with
  | sweep S => exact (bitDef_sweep S reg).congr fun A _ _ _ _ v => Iff.rfl
  | bit i y => exact (bitDef_bit (reg i) (reg y)).congr fun A _ _ _ _ v => Iff.rfl
  | query R arg =>
    exact (bitDef_rel R fun i => reg (arg i)).congr fun A _ _ _ _ v => Iff.rfl
  | not t ih => exact ih.not.congr fun A _ _ _ _ v => Iff.rfl
  | and t u iht ihu => exact (iht.and ihu).congr fun A _ _ _ _ v => Iff.rfl
  | or t u iht ihu => exact (iht.or ihu).congr fun A _ _ _ _ v => Iff.rfl

end MachineDef

/-! ### The inclusion -/

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The machine model is inside the bit-level logic**: every problem decided
by an alternating machine with a logarithmic clock and a bit-level base is
defined by a prenex sentence over `≤`, `+` and the bit at an index. The guesses
are the quantifier prefix, the queries and the reads are atoms, and each sweep is
a guessed trace pinned by its transition.

With `DescriptiveComplexity.BitDefinable.ltDecidable` this makes the fence an
**equality**: the machine model is exactly characterized by a logic, and by the
logic that is classically AC⁰. -/
theorem LTDecidable.bitDefinable {P : DecisionProblem L} (h : LTDecidable P) :
    BitDefinable P := by
  obtain ⟨M, hM⟩ := h
  refine BitDef.bitDefinable (R := fun A _ _ _ _ _ =>
    prefixHolds (A := A) M.regs M.pol fun x => M.base.Holds x) ?_ ?_
  · exact ((bitDef_baseTest M.base fun k => Sum.inr k).block M.pol).congr
      fun A _ _ _ _ v => Iff.rfl
  · intro A _ _ _ _
    rw [hM A, LTMachine.Accepts]

/-- **The machine model is inside AC⁰**: a corollary of the statement above and
of the translation of the bit-level logic into `FO(≤, +, ×)`, whose bit atom is
`DescriptiveComplexity.powArithDef` and whose other atoms are numeric predicates
outright. -/
theorem LTDecidable.ac0Definable {P : DecisionProblem L} (h : LTDecidable P) :
    AC0Definable P :=
  h.bitDefinable.ac0Definable

end DescriptiveComplexity
