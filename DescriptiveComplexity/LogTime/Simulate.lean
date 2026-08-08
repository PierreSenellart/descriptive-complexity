/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Machine

/-!
# Sweeping logarithmic time is inside AC⁰

The half of the machine bridge that this file proves: **every problem decided by
an alternating machine with a logarithmic clock and a bit-level base is AC⁰
definable** (`DescriptiveComplexity.LTDecidable.ac0Definable`), hence, through
`DescriptiveComplexity.ac0Definable_mem_LOGSPACE`, inside LOGSPACE.

## The three moving parts

* **The guesses are quantifiers.** A register holds an element of the universe,
  and filling it existentially or universally is `∃` or `∀` – the alternation
  structure of the machine is the quantifier prefix of the sentence, on the
  nose (`DescriptiveComplexity.arithDef_prefix`).
* **A query is an atom.** Reading the instance at a tuple of registers is an
  atomic formula of the input vocabulary; no encoding of addresses is involved,
  which is the whole reason the model fits a structure-based framework.
* **A sweep is a guessed trace.** This is the content. A sweep carries `σ` bits
  of state past each of the `posCount A` bit positions, so its entire history is
  `σ` bit *vectors over the positions* – and a bit vector over the positions **is
  an element of the universe**. The formula therefore guesses `σ` elements, says
  with `DescriptiveComplexity.BitAt` that the bit of the `j`-th at each position
  is what the transition of the sweep produces there, and reads acceptance off
  the top. Determinism of the sweep makes the guess unique, so the existential
  is faithful.

## The one asymmetry: the last position

A bit vector over *all* the positions need not be a rank – the universe need not
have a power of two elements – so the trace elements can only carry the state up
to the position below the top (`DescriptiveComplexity.exists_orank_testBit`).
The state after the top position is therefore carried by `σ` further elements
used as *flags*, one bit each, read as “nonzero rank”. Everything else in the
construction is uniform.

## Why this is the direction that goes through

The converse inclusion – that every AC⁰ definable problem is decided by such a
machine – is *not* proved here, and cannot be with this base: a constant number
of sweeps cannot multiply, since a sweep passes only `σ` bits of state across a
position while the schoolbook product of two `log n`-bit numbers needs a running
count. That is the same wall as the classical statement that `AC⁰ = LH` needs a
log-time machine that *counts* – whose simulation in the logic is exactly the
hard half of [Barrington, Immerman & Straubing 1990][barrington1990uniformity].
What the model does compute is the rest of the arithmetic, bit by bit:
`DescriptiveComplexity.LogTime.Arith`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The quantifier prefix -/

section Prefix

variable {L : Language.{0, 0}}

/-- The variable layout of one quantifier step: the last variable of an
`m + 1`-tuple is the bound one. -/
private def lastSplit (m : ℕ) : Fin (m + 1) → Fin m ⊕ Fin 1 :=
  Fin.lastCases (Sum.inr 0) fun j => Sum.inl j

private theorem elim_lastSplit {A : Type} {m : ℕ} (v : Fin m → A) (a : A) :
    (Sum.elim v fun _ => a) ∘ lastSplit m = Fin.snoc v a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [lastSplit, Fin.snoc_last]
  · simp [lastSplit, Fin.snoc_castSucc]

/-- **A quantifier prefix of a machine is a quantifier prefix of a formula**:
the registers, filled in order by the two players, become nested `∃` and `∀`
over the universe. -/
theorem arithDef_prefix : ∀ (m : ℕ) (pol : Fin m → Bool) {R : ArithRel L (Fin m)},
    ArithDef R →
      ArithDef (L := L) (α := Empty)
        (fun A _ _ _ _ _ => prefixHolds (A := A) m pol fun x => R A x) := by
  intro m
  induction m with
  | zero =>
    intro pol R h
    refine (h.relabel (Fin.elim0 : Fin 0 → Empty)).congr fun A _ _ _ _ v => ?_
    rw [Subsingleton.elim (v ∘ (Fin.elim0 : Fin 0 → Empty)) (Fin.elim0 : Fin 0 → A)]
    exact Iff.rfl
  | succ m ih =>
    intro pol R h
    refine ih (fun j => pol j.castSucc) ?_
    by_cases hp : pol (Fin.last m) = true
    · refine ((h.relabel (lastSplit m)).ex).congr fun A _ _ _ _ v => ?_
      rw [if_pos hp]
      exact exists_congr fun a => by rw [elim_lastSplit]
    · refine ((h.relabel (lastSplit m)).all).congr fun A _ _ _ _ v => ?_
      rw [if_neg hp]
      exact forall_congr' fun a => by rw [elim_lastSplit]

end Prefix

/-! ### Boolean expressions, read as formulas -/

section BitExprDef

variable {L : Language.{0, 0}} {α : Type} {V : Type}

/-- A Boolean expression of definable bits is definable: the translation is a
recursion over the expression, not an enumeration of its truth table. -/
theorem arithDef_bitExpr {val : V → ArithRel L α} (h : ∀ z, ArithDef (val z)) :
    ∀ e : BitExpr V,
      ArithDef (L := L) (α := α) (fun A _ _ _ _ v => e.Holds fun z => val z A v)
  | .var z => (h z).congr fun _A _ _ _ _ _v => Iff.rfl
  | .tt => ArithDef.top.congr fun _A _ _ _ _ _v => Iff.rfl
  | .ff => ArithDef.bot.congr fun _A _ _ _ _ _v => Iff.rfl
  | .not e => (arithDef_bitExpr h e).not.congr fun _A _ _ _ _ _v => Iff.rfl
  | .and e f => ((arithDef_bitExpr h e).and (arithDef_bitExpr h f)).congr
      fun _A _ _ _ _ _v => Iff.rfl
  | .or e f => ((arithDef_bitExpr h e).or (arithDef_bitExpr h f)).congr
      fun _A _ _ _ _ _v => Iff.rfl

end BitExprDef

/-! ### The trace of a sweep -/

section SweepTrace

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

/-- **The transition of a sweep at a position**, as a statement about a guessed
trace: the state bits before the position are the initial ones if the position
is the lowest, and the trace bits at the position below otherwise. -/
def stepAt (S : Sweep ρ) (x : Fin ρ → A) (t : Fin S.σ → A) (p : A) (j : Fin S.σ) : Prop :=
  (S.step j).Holds (Sum.elim
    (fun j' => (orank p = 1 ∧ S.init j' = true) ∨
      ∃ p' : A, orank p' + orank p' = orank p ∧ BitAt p' (t j'))
    fun k => BitAt p (x k))

/-- **What the formula asks of the guessed trace and flags**: the trace records
the state after each position below the top, the flags record the state after
the top position, and the acceptance condition holds of the flags – of the
initial state, if the universe has no bit position at all. -/
def SweepWitness (S : Sweep ρ) (x : Fin ρ → A) (t f : Fin S.σ → A) : Prop :=
  (∀ p : A, IsPos p → ¬IsTopPos p → ∀ j, (BitAt p (t j) ↔ stepAt S x t p j)) ∧
    (∀ p : A, IsTopPos p → ∀ j, (orank (f j) ≠ 0 ↔ stepAt S x t p j)) ∧
      ((∃ p : A, IsPos p) → S.acc.Holds fun j => orank (f j) ≠ 0) ∧
        ((¬∃ p : A, IsPos p) → S.acc.eval S.init = true)

/-- The state the witnesses record after position `i`: a trace bit below the
top, a flag at the top. -/
def storedAfter (S : Sweep ρ) (t f : Fin S.σ → A) (i : ℕ) (j : Fin S.σ) : Prop :=
  if i + 1 < posCount A then (orank (t j)).testBit i = true else orank (f j) ≠ 0

/-- Positions exist exactly when the universe has more than one element. -/
theorem exists_isPos_iff : (∃ p : A, IsPos p) ↔ 0 < posCount A := by
  constructor
  · rintro ⟨p, i, hi⟩
    have h1 : 2 ^ i < Nat.card A := by rw [← hi]; exact orank_lt_card p
    have h2 : i < posCount A := (two_pow_lt_card_iff_lt_posCount i).mp h1
    omega
  · intro h
    obtain ⟨p, hp⟩ := exists_isPos (A := A) h
    exact ⟨p, 0, hp⟩

/-- **The transition read from the trace is the transition of the sweep**: at
the position of place value `2 ^ i`, the guessed bits say exactly what the
automaton computes from the state before that position. -/
theorem stepAt_iff (S : Sweep ρ) (x : Fin ρ → A) (t : Fin S.σ → A) {p : A} {i : ℕ}
    (hp : orank p = 2 ^ i) (j : Fin S.σ) :
    stepAt S x t p j ↔ (S.step j).eval (Sum.elim
      (fun j' => if i = 0 then S.init j' else (orank (t j')).testBit (i - 1))
      fun k => (orank (x k)).testBit i) = true := by
  rw [stepAt, ← BitExpr.holds_iff_eval]
  refine BitExpr.holds_congr ?_ _
  rintro (j' | k)
  · simp only [Sum.elim_inl]
    cases i with
    | zero =>
      simp only [pow_zero] at hp ⊢
      constructor
      · rintro (⟨-, h⟩ | ⟨p', hp', -⟩)
        · exact h
        · rw [hp] at hp'
          omega
      · intro h
        exact Or.inl ⟨hp, h⟩
    | succ i =>
      have hne : orank p ≠ 1 := by
        rw [hp]
        have : 2 ≤ 2 ^ (i + 1) := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      simp only [Nat.succ_sub_one, if_neg (Nat.succ_ne_zero i)]
      constructor
      · rintro (⟨h, -⟩ | ⟨p', hp', hbit⟩)
        · exact absurd h hne
        · have hp'' : orank p' = 2 ^ i := by rw [hp] at hp'; rw [pow_succ] at hp'; omega
          exact (bitAt_iff hp'').mp hbit
      · intro h
        have hlt : 2 ^ i < Nat.card A := by
          have := orank_lt_card p
          rw [hp, pow_succ] at this
          have : (0 : ℕ) < 2 ^ i := Nat.two_pow_pos i
          omega
        obtain ⟨p', hp'⟩ := exists_orank_eq (A := A) hlt
        exact Or.inr ⟨p', by rw [hp', hp, pow_succ]; ring, (bitAt_iff hp').mpr h⟩
  · simp only [Sum.elim_inr]
    exact bitAt_iff hp

/-- **The guessed trace is the run**: the witnesses of the formula record,
position by position, the states of the sweep. Determinism does the work – the
local conditions pin the trace by induction along the positions. -/
theorem storedAfter_iff_state (S : Sweep ρ) (x : Fin ρ → A) (t f : Fin S.σ → A)
    (hw : SweepWitness S x t f) :
    ∀ i, i < posCount A → ∀ j, (storedAfter S t f i j ↔ S.state x (i + 1) j = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi j
    obtain ⟨p, hp⟩ := exists_isPos (A := A) hi
    have hpos : IsPos p := ⟨i, hp⟩
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
    have hstep : stepAt S x t p j ↔ S.state x (i + 1) j = true := by
      rw [stepAt_iff S x t hp j, S.state_succ x i j]
      have : (fun j' => if i = 0 then S.init j' else (orank (t j')).testBit (i - 1)) =
          S.state x i := funext hprev
      rw [this]
    rcases Nat.lt_or_ge (i + 1) (posCount A) with hlt | hge
    · have hntop : ¬IsTopPos p := by
        rw [isTopPos_iff hpos, posExp_eq hp]
        omega
      rw [storedAfter, if_pos hlt, ← bitAt_iff hp, hw.1 p hpos hntop j]
      exact hstep
    · have htop : IsTopPos p := by
        rw [isTopPos_iff hpos, posExp_eq hp]
        omega
      rw [storedAfter, if_neg (by omega), hw.2.1 p htop j]
      exact hstep

/-- **The formula says what the sweep does.** -/
theorem sweepWitness_iff [Nonempty A] (S : Sweep ρ) (x : Fin ρ → A) :
    (∃ t f : Fin S.σ → A, SweepWitness S x t f) ↔ S.Accepts x := by
  constructor
  · rintro ⟨t, f, hw⟩
    rw [Sweep.Accepts, ← BitExpr.holds_iff_eval]
    rcases Nat.eq_zero_or_pos (posCount A) with h0 | hpos
    · have hnone : ¬∃ p : A, IsPos p := by
        rw [exists_isPos_iff]
        omega
      have := hw.2.2.2 hnone
      rw [h0, Sweep.state_zero, BitExpr.holds_iff_eval]
      exact this
    · have hstate := storedAfter_iff_state S x t f hw (posCount A - 1) (by omega)
      refine (BitExpr.holds_congr (fun j => ?_) _).mpr
        (hw.2.2.1 (exists_isPos_iff.mpr hpos))
      have h1 : posCount A - 1 + 1 = posCount A := by omega
      have := hstate j
      rw [storedAfter, if_neg (by omega), h1] at this
      exact this.symm
  · intro hacc
    rcases Nat.eq_zero_or_pos (posCount A) with h0 | hpos
    · obtain ⟨a⟩ := ‹Nonempty A›
      refine ⟨fun _ => a, fun _ => a, ?_, ?_, ?_, ?_⟩
      · intro p hp
        exact absurd (exists_isPos_iff.mp ⟨p, hp⟩) (by omega)
      · intro p hp
        exact absurd (exists_isPos_iff.mp ⟨p, hp.1⟩) (by omega)
      · intro hex
        exact absurd (exists_isPos_iff.mp hex) (by omega)
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
      refine ⟨t, fun j => if S.state x (posCount A) j = true then one else zero, ?_, ?_, ?_, ?_⟩
      · intro p hpos' hntop j
        obtain ⟨i, hi⟩ := hpos'
        have hilt : i < posCount A := by
          rw [← two_pow_lt_card_iff_lt_posCount, ← hi]
          exact orank_lt_card p
        have hne : i + 1 ≠ posCount A := by
          intro hcon
          exact hntop (by rw [isTopPos_iff ⟨i, hi⟩, posExp_eq hi]; exact hcon)
        have hprev : (fun j' => if i = 0 then S.init j' else (orank (t j')).testBit (i - 1)) =
            S.state x i := by
          funext j'
          cases i with
          | zero => simp
          | succ i' =>
            simp only [Nat.succ_sub_one, if_neg (Nat.succ_ne_zero i')]
            exact ht j' i' (by omega)
        rw [bitAt_iff hi, stepAt_iff S x t hi j, hprev, ← S.state_succ x i j,
          ht j i (by omega)]
      · intro p htop j
        obtain ⟨i, hi⟩ := htop.1
        have heq : i + 1 = posCount A := by
          rw [← posExp_eq hi]
          exact (isTopPos_iff htop.1).mp htop
        have hprev : (fun j' => if i = 0 then S.init j' else (orank (t j')).testBit (i - 1)) =
            S.state x i := by
          funext j'
          cases i with
          | zero => simp
          | succ i' =>
            simp only [Nat.succ_sub_one, if_neg (Nat.succ_ne_zero i')]
            exact ht j' i' (by omega)
        rw [stepAt_iff S x t hi j, hprev, ← S.state_succ x i j, heq]
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
        exact absurd (exists_isPos_iff.mpr hpos) hnone

end SweepTrace

/-! ### Definability of the machine -/

section MachineDef

variable {L : Language.{0, 0}} {α : Type} {ρ : ℕ}

/-- The transition condition at a position is definable. -/
theorem arithDef_stepAt (S : Sweep ρ) (reg : Fin ρ → α) (tr : Fin S.σ → α) (p : α)
    (j : Fin S.σ) :
    ArithDef (L := L) (α := α) (fun _A _ _ _ _ v =>
      stepAt S (fun k => v (reg k)) (fun j' => v (tr j')) (v p) j) := by
  have hval : ∀ z : Fin S.σ ⊕ Fin ρ, ArithDef (L := L) (α := α)
      (Sum.elim
        (fun j' : Fin S.σ => fun A _ _ _ _ (v : α → A) =>
          (orank (v p) = 1 ∧ S.init j' = true) ∨
            ∃ p' : A, orank p' + orank p' = orank (v p) ∧ BitAt p' (v (tr j')))
        (fun k : Fin ρ => fun A _ _ _ _ (v : α → A) => BitAt (v p) (v (reg k))) z) := by
    rintro (j' | k)
    · refine (((arithDef_isOne p).and (ArithDef.prop (S.init j' = true))).or
        (((arithDef_plus (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0)
            (Sum.inl p)).and
          (arithDef_bit (L := L) (α := α ⊕ Fin 1) (Sum.inr 0)
            (Sum.inl (tr j')))).ex)).congr fun A _ _ _ _ v => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
    · exact (arithDef_bit p (reg k)).congr fun _A _ _ _ _ _v => Iff.rfl
  exact (arithDef_bitExpr hval (S.step j)).congr fun A _ _ _ _ v => by
    rw [stepAt]
    exact BitExpr.holds_congr (by rintro (j' | k) <;> exact Iff.rfl) _

/-- **A sweep is definable**: the formula guesses the trace and the flags, and
asks that they be the run. -/
theorem arithDef_sweep (S : Sweep ρ) (reg : Fin ρ → α) :
    ArithDef (L := L) (α := α)
      (fun _A _ _ _ _ v => S.Accepts fun k => v (reg k)) := by
  classical
  -- variables: the ambient ones, then the trace, then the flags
  set γ : Type := (α ⊕ Fin S.σ) ⊕ Fin S.σ with hγ
  let amb : α → γ := fun a => Sum.inl (Sum.inl a)
  let tr : Fin S.σ → γ := fun j => Sum.inl (Sum.inr j)
  let fl : Fin S.σ → γ := fun j => Sum.inr j
  -- the local condition at a position, with the position bound as `Sum.inr 0`
  have hlocal : ArithDef (L := L) (α := γ) (fun A _ _ _ _ v =>
      ∀ p : A, IsPos p → ¬IsTopPos p → ∀ j,
        (BitAt p (v (tr j)) ↔ stepAt S (fun k => v (amb (reg k)))
          (fun j' => v (tr j')) p j)) := by
    refine (((arithDef_isPos (L := L) (α := γ ⊕ Fin 1) (Sum.inr 0)).imp
      (((arithDef_isTopPos (L := L) (α := γ ⊕ Fin 1) (Sum.inr 0)).not).imp
        (ArithDef.forallFin (R := fun j => fun A _ _ _ _ (v : (γ ⊕ Fin 1) → A) =>
            (BitAt (v (Sum.inr 0)) (v (Sum.inl (tr j))) ↔
              stepAt S (fun k => v (Sum.inl (amb (reg k))))
                (fun j' => v (Sum.inl (tr j'))) (v (Sum.inr 0)) j))
          fun j => (arithDef_bit (Sum.inr 0) (Sum.inl (tr j))).iff
            (arithDef_stepAt S (fun k => Sum.inl (amb (reg k))) (fun j' => Sum.inl (tr j'))
              (Sum.inr 0) j)))).all).congr fun A _ _ _ _ v => ?_
    exact forall_congr' fun a => by simp only [Sum.elim_inl, Sum.elim_inr]
  -- the condition at the top position, recorded by the flags
  have htop : ArithDef (L := L) (α := γ) (fun A _ _ _ _ v =>
      ∀ p : A, IsTopPos p → ∀ j,
        (orank (v (fl j)) ≠ 0 ↔ stepAt S (fun k => v (amb (reg k)))
          (fun j' => v (tr j')) p j)) := by
    refine (((arithDef_isTopPos (L := L) (α := γ ⊕ Fin 1) (Sum.inr 0)).imp
      (ArithDef.forallFin (R := fun j => fun A _ _ _ _ (v : (γ ⊕ Fin 1) → A) =>
          (¬ orank (v (Sum.inl (fl j))) = 0 ↔
            stepAt S (fun k => v (Sum.inl (amb (reg k))))
              (fun j' => v (Sum.inl (tr j'))) (v (Sum.inr 0)) j))
        fun j => ((arithDef_isZero (Sum.inl (fl j))).not).iff
          (arithDef_stepAt S (fun k => Sum.inl (amb (reg k))) (fun j' => Sum.inl (tr j'))
            (Sum.inr 0) j))).all).congr fun A _ _ _ _ v => ?_
    exact forall_congr' fun a => by simp only [Sum.elim_inl, Sum.elim_inr]
  -- acceptance, read from the flags, or from the initial state if there are no positions
  have hex : ArithDef (L := L) (α := γ) (fun A _ _ _ _ v => ∃ p : A, IsPos p) := by
    refine ((arithDef_isPos (L := L) (α := γ ⊕ Fin 1) (Sum.inr 0)).ex).congr
      fun A _ _ _ _ v => ?_
    exact exists_congr fun a => by simp only [Sum.elim_inr]
  have hacc : ArithDef (L := L) (α := γ) (fun A _ _ _ _ v =>
      S.acc.Holds fun j => orank (v (fl j)) ≠ 0) :=
    arithDef_bitExpr (fun j => (arithDef_isZero (L := L) (α := γ) (fl j)).not) S.acc
  have hbody : ArithDef (L := L) (α := γ) (fun A _ _ _ _ v =>
      SweepWitness S (fun k => v (amb (reg k))) (fun j => v (tr j)) fun j => v (fl j)) :=
    hlocal.and (htop.and ((hex.imp hacc).and
      (hex.not.imp (ArithDef.prop (S.acc.eval S.init = true)))))
  refine (hbody.exs.exs).congr fun A _ _ _ _ v => ?_
  rw [← sweepWitness_iff S fun k => v (reg k)]
  constructor
  · rintro ⟨tw, fw, hw⟩
    exact ⟨tw, fw, hw⟩
  · rintro ⟨tw, fw, hw⟩
    exact ⟨tw, fw, hw⟩

/-- **A base test is definable**: sweeps by the construction above, queries as
atoms, and the Boolean structure by the closure lemmas. -/
theorem arithDef_baseTest (t : BaseTest L ρ) (reg : Fin ρ → α) :
    ArithDef (L := L) (α := α) (fun _A _ _ _ _ v => t.Holds fun k => v (reg k)) := by
  induction t with
  | sweep S => exact (arithDef_sweep S reg).congr fun A _ _ _ _ v => Iff.rfl
  | query R arg =>
    exact (arithDef_rel R fun i => reg (arg i)).congr fun A _ _ _ _ v => Iff.rfl
  | not t ih => exact ih.not.congr fun A _ _ _ _ v => Iff.rfl
  | and t u iht ihu => exact (iht.and ihu).congr fun A _ _ _ _ v => Iff.rfl
  | or t u iht ihu => exact (iht.or ihu).congr fun A _ _ _ _ v => Iff.rfl

end MachineDef

/-! ### The inclusion -/

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Sweeping logarithmic time is inside AC⁰**: every problem decided by an
alternating machine with a logarithmic clock and a bit-level base is defined by
a sentence of `FO(≤, +, ×)`. The guesses are the quantifier prefix, the queries
are atoms, and each sweep is a guessed trace pinned by its transition. -/
theorem LTDecidable.ac0Definable {P : DecisionProblem L} (h : LTDecidable P) :
    AC0Definable P := by
  obtain ⟨M, hM⟩ := h
  refine (arithDef_prefix M.regs M.pol (arithDef_baseTest M.base id)).ac0Definable ?_
  intro A _ _ _ _
  rw [hM A, LTMachine.Accepts]
  exact prefixHolds_congr M.regs M.pol fun v => Iff.rfl

end DescriptiveComplexity
