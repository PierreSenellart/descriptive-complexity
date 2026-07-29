/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltProg

/-!
# The transition table of the QBF machine is a table

Before any run is considered: each transition has exactly one destination and
one symbol written, and the places where two tags could both apply are
identified. A mistake in the table shows up here first, which is why this comes
before the correctness proof.

Unlike the SAT machine there are *three* such places, not two:

* at `⊢` in a leftward sweep, the three ways a sweep can end – hand over to the
  next sweep, start the check, or accept because there is no clause at all –
  are separated by the sweep index (`i + 1 < k` against `i + 1 = k`) and, for
  the last two, by whether the instance has a clause;
* at a marker in the check phase, the turn to the next clause and the
  accepting turn are separated, for a conjunctive matrix, by whether the clause
  just settled was the last one; for a disjunctive matrix they fire at
  different flags and so never compete;
* at a cell holding `false` in a rightward sweep, `tGSet` and `tGKeep false`
  *are* both applicable. That is the guessing choice, and it is the one
  ambiguity `DescriptiveComplexity.altTr_unique` does not resolve: it is the
  round's move.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Table

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The elements of the machine, compared -/

omit [(Language.qbf k).Structure A] in
theorem acstI_eq_iff {t t' : AltBase} {i i' : Fin (k + 1)} :
    (acstI t i : AltV k A) = acstI t' i' ↔ t = t' ∧ i = i' := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

omit [(Language.qbf k).Structure A] in
theorem aoneI_eq_iff {t t' : AltBase} {i i' : Fin (k + 1)} {a a' : A} :
    (aoneI t i a : AltV k A) = aoneI t' i' a' ↔ t = t' ∧ i = i' ∧ a = a' := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrFun (congrArg Prod.snd h) 0
    simp only [aoneI, Matrix.cons_val_zero] at h2
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1, h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- Two elements agree when their tag and both coordinates do. -/
theorem altV_ext {τ τ' : AltV k A} (ht : τ.1 = τ'.1) (h0 : τ.2 0 = τ'.2 0)
    (h1 : τ.2 1 = τ'.2 1) : τ = τ' := by
  refine Prod.ext ht (funext fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1

/-! ### The table is functional -/

omit [(Language.qbf k).Structure A] in
/-- A transition writes exactly one symbol. -/
theorem altWrite_functional {τ a a' : AltV k A} (h : AltWrite τ a) (h' : AltWrite τ a') :
    a = a' := by
  unfold AltWrite at h h'
  cases hτ : τ.1.1 <;> rw [hτ] at h h' <;> simp only at h h' <;> exact h.trans h'.symm

/-- A transition moves to exactly one state. The only case with a choice is the
check clause, whose two branches are separated by the flag and by
`DescriptiveComplexity.QbfLit`. -/
theorem altDst_functional {cnf : Bool} {τ q q' : AltV k A} (h : AltDst cnf τ q)
    (h' : AltDst cnf τ q') : q = q' := by
  unfold AltDst at h h'
  cases hτ : τ.1.1 <;> rw [hτ] at h h' <;> simp only at h h'
  case tChk v f d =>
    rcases h with ⟨hq, hcase⟩ | ⟨hq, hf, hlit⟩ <;> rcases h' with ⟨hq', hcase'⟩ | ⟨hq', hf', hlit'⟩
    · exact hq.trans hq'.symm
    · rcases hcase with hc | hc
      · exact absurd (hc.symm.trans hf') (by decide)
      · exact absurd hc hlit'
    · rcases hcase' with hc | hc
      · exact absurd (hc.symm.trans hf) (by decide)
      · exact absurd hc hlit
    · exact hq.trans hq'.symm
  all_goals exact h.trans h'.symm

/-! ### The three branch points -/

omit [Finite A] [Nonempty A] in
/-- **A sweep hands over, or ends**: the two are separated by the sweep
index. -/
theorem altTr_next_end_excl {cnf : Bool} {τ τ' : AltV k A} (h : AltTr cnf τ)
    (h' : AltTr cnf τ') (hτ : τ.1.1 = AltBase.tGNext)
    (hτ' : τ'.1.1 = AltBase.tGEndAcc ∨ τ'.1.1 = AltBase.tGEndChk)
    (hi : τ.1.2 = τ'.1.2) : False := by
  unfold AltTr at h h'
  rw [hτ] at h
  rcases hτ' with hτ' | hτ' <;> rw [hτ'] at h' <;> rw [hi] at h <;> omega

omit [Finite A] [Nonempty A] in
/-- **The end of the last sweep is not ambiguous**: an instance either has a
clause to check or has none. -/
theorem altTr_end_excl {cnf : Bool} {τ τ' : AltV k A} (h : AltTr cnf τ) (h' : AltTr cnf τ')
    (hτ : τ.1.1 = AltBase.tGEndAcc) (hτ' : τ'.1.1 = AltBase.tGEndChk) : False := by
  unfold AltTr at h h'
  rw [hτ] at h
  rw [hτ'] at h'
  exact h.2.2.2 _ h'.2.2.1

omit [Finite A] [Nonempty A] in
/-- **A turn is not ambiguous**: for a conjunctive matrix the clause just
checked either has a successor or is the last one, and for a disjunctive one
the two turns fire at different flags. -/
theorem altTr_turn_excl {cnf : Bool} {τ τ' : AltV k A} {d d' : Bool} (h : AltTr cnf τ)
    (h' : AltTr cnf τ') (hτ : τ.1.1 = AltBase.tTurnNext d) (hτ' : τ'.1.1 = AltBase.tTurnAcc d')
    (hcnf : cnf = true) (hc : τ.2 0 = τ'.2 0) : False := by
  unfold AltTr at h h'
  rw [hτ] at h
  rw [hτ'] at h'
  exact absurd ((h'.2.2.2 hcnf).2 _ h.1.2.1) (not_le.mpr (hc ▸ h.1.2.2.1))

/-! ### Reading the tag off the state and the symbol -/

/-- Which base tag the state a transition applies in carries. -/
def stateBase (cnf : Bool) : AltBase → AltBase
  | .tGStart => .qG true
  | .tGKeep _ => .qG true
  | .tGSet => .qG true
  | .tGTurn => .qG true
  | .tGBack _ => .qG false
  | .tGNext => .qG false
  | .tGEndAcc => .qG false
  | .tGEndChk => .qG false
  | .tChk _ f d => .qChk f d
  | .tTurnNext d => .qChk true d
  | .tTurnAcc d => .qChk cnf d
  | t => t

/-- Which base tag the symbol a transition reads carries. -/
def readBase : AltBase → AltBase
  | .tGStart => .sStart
  | .tGKeep b => .sVal b
  | .tGSet => .sVal false
  | .tGTurn => .sEnd
  | .tGBack b => .sVal b
  | .tGNext => .sStart
  | .tGEndAcc => .sStart
  | .tGEndChk => .sStart
  | .tChk v _ _ => .sVal v
  | .tTurnNext d => if d then .sEnd else .sStart
  | .tTurnAcc d => if d then .sEnd else .sStart
  | t => t

/-- The base tags that a transition may carry. -/
def isTrBase : AltBase → Bool
  | .tGStart => true
  | .tGKeep _ => true
  | .tGSet => true
  | .tGTurn => true
  | .tGBack _ => true
  | .tGNext => true
  | .tGEndAcc => true
  | .tGEndChk => true
  | .tChk _ _ _ => true
  | .tTurnNext _ => true
  | .tTurnAcc _ => true
  | _ => false

/-- The base tags whose source state is a sweeping state, and so carries the
transition's own sweep index. -/
def isSweepBase : AltBase → Bool
  | .tGStart => true
  | .tGKeep _ => true
  | .tGSet => true
  | .tGTurn => true
  | .tGBack _ => true
  | .tGNext => true
  | .tGEndAcc => true
  | .tGEndChk => true
  | _ => false

omit [Finite A] [Nonempty A] in
/-- Only transitions have transition tags. -/
theorem altTr_isTrBase {cnf : Bool} {τ : AltV k A} (hτ : AltTr cnf τ) : isTrBase τ.1.1 := by
  obtain ⟨⟨t, i⟩, w⟩ := τ
  cases t <;> first | exact False.elim hτ | rfl

/-- The state a transition applies in has the base tag its own tag names, and
its sweep index. -/
theorem altSrc_base {cnf : Bool} {τ q : AltV k A} (hτ : AltTr cnf τ) (hs : AltSrc cnf τ q) :
    q.1.1 = stateBase cnf τ.1.1 ∧ (isSweepBase τ.1.1 → q.1.2 = τ.1.2) := by
  obtain ⟨⟨t, i⟩, w⟩ := τ
  cases t <;> dsimp only [AltTr, AltSrc, stateBase, isSweepBase] at hτ hs ⊢ <;>
    first
      | exact False.elim hτ
      | (subst hs; exact ⟨rfl, fun _ => rfl⟩)
      | (subst hs; exact ⟨rfl, fun h => absurd h (by simp)⟩)

/-- The symbol a transition reads has the base tag its own tag names. -/
theorem altRead_base {cnf : Bool} {τ a : AltV k A} (hτ : AltTr cnf τ) (hr : AltRead τ a) :
    a.1.1 = readBase τ.1.1 := by
  obtain ⟨⟨t, i⟩, w⟩ := τ
  cases t <;> dsimp only [AltTr, AltRead, readBase] at hτ hr ⊢ <;>
    first
      | exact False.elim hτ
      | (subst hr; rfl)
      | (rename_i d; cases d <;> (subst hr; rfl))

/-! ### At most one transition applies, away from the guess -/

/-- The base tags at which a sweep ends. -/
def isEndBase : AltBase → Bool
  | .tGNext => true
  | .tGEndAcc => true
  | .tGEndChk => true
  | _ => false

/-- The base tags of a turn in the check phase. -/
def isTurnBase : AltBase → Bool
  | .tTurnNext _ => true
  | .tTurnAcc _ => true
  | _ => false

/-- **The state and the symbol pin the tag**, up to the three branch points:
the guessing choice, the end of a sweep and the turn. -/
theorem base_cases (cnf : Bool) : ∀ t t' : AltBase, isTrBase t → isTrBase t' →
    stateBase cnf t = stateBase cnf t' → readBase t = readBase t' →
    t = t' ∨ (t = .tGKeep false ∧ t' = .tGSet) ∨ (t = .tGSet ∧ t' = .tGKeep false) ∨
      (t = .tGNext ∧ (t' = .tGEndAcc ∨ t' = .tGEndChk)) ∨
      ((t = .tGEndAcc ∨ t = .tGEndChk) ∧ t' = .tGNext) ∨
      (t = .tGEndAcc ∧ t' = .tGEndChk) ∨ (t = .tGEndChk ∧ t' = .tGEndAcc) ∨
      (∃ d, t = .tTurnNext d ∧ t' = .tTurnAcc d) ∨
      (∃ d, t = .tTurnAcc d ∧ t' = .tTurnNext d) := by
  cases cnf <;> decide

omit [Finite A] [Nonempty A] in
/-- Away from the sweeps, a transition's sweep index is `0`. -/
theorem altTr_index_zero {cnf : Bool} {τ : AltV k A} (hτ : AltTr cnf τ)
    (h : ¬isSweepBase τ.1.1) : (τ.1.2 : ℕ) = 0 := by
  obtain ⟨⟨t, i⟩, w⟩ := τ
  cases t <;> dsimp only [AltTr, isSweepBase] at hτ h ⊢ <;>
    first
      | exact False.elim hτ
      | exact absurd rfl h
      | exact hτ.2
      | exact hτ.1.2
      | exact hτ.2.1

/-- Whether a transition's source is a sweeping state is determined by the base
tag of that state. -/
theorem isSweepBase_congr (cnf : Bool) : ∀ t t' : AltBase, isTrBase t → isTrBase t' →
    stateBase cnf t = stateBase cnf t' → isSweepBase t = isSweepBase t' := by
  cases cnf <;> decide

/-- **Equal base tags force equal transitions**: the state and the symbol pin
one coordinate and the sweep index, and the promises in
`DescriptiveComplexity.AltTr` pin the other. -/
theorem altTr_payload {cnf : Bool} {τ τ' q a : AltV k A} (hτ : AltTr cnf τ) (hτ' : AltTr cnf τ')
    (hs : AltSrc cnf τ q) (hs' : AltSrc cnf τ' q) (hr : AltRead τ a) (hr' : AltRead τ' a)
    (hb : τ.1.1 = τ'.1.1) : τ = τ' := by
  have hmin : ∀ u v : A, (∀ b : A, u ≤ b) → (∀ b : A, v ≤ b) → u = v :=
    fun u v hu hv => le_antisymm (hu v) (hv u)
  -- the sweep index agrees, from the state or from the table
  have hi : τ.1.2 = τ'.1.2 := by
    by_cases hsw : isSweepBase τ.1.1
    · have h1 := (altSrc_base hτ hs).2 hsw
      have h2 := (altSrc_base hτ' hs').2 (hb ▸ hsw)
      exact h1.symm.trans h2
    · exact Fin.ext ((altTr_index_zero hτ hsw).trans (altTr_index_zero hτ' (hb ▸ hsw)).symm)
  have ht : τ.1 = τ'.1 := Prod.ext hb hi
  obtain ⟨⟨t, i⟩, w⟩ := τ
  obtain ⟨⟨t', i'⟩, w'⟩ := τ'
  cases ht
  cases t <;> dsimp only [AltTr, AltSrc, AltRead] at hτ hτ' hs hs' hr hr' <;>
    first
      | exact False.elim hτ
      | exact Prod.ext rfl (isMinTup2_unique hτ hτ')
      | exact Prod.ext rfl (isMinTup2_unique hτ.1 hτ'.1)
      | exact altV_ext rfl (aoneI_eq_iff.mp (hr.symm.trans hr')).2.2 (hmin _ _ hτ.1 hτ'.1)
      | exact altV_ext rfl (aoneI_eq_iff.mp (hs.symm.trans hs')).2.2
          (aoneI_eq_iff.mp (hr.symm.trans hr')).2.2
      | exact altV_ext rfl (aoneI_eq_iff.mp (hs.symm.trans hs')).2.2 (hmin _ _ hτ.1 hτ'.1)
      | exact altV_ext rfl (le_antisymm (hτ.2.2.2 _ hτ'.2.2.1) (hτ'.2.2.2 _ hτ.2.2.1))
          (hmin _ _ hτ.1 hτ'.1)
      | (refine altV_ext rfl (aoneI_eq_iff.mp (hs.symm.trans hs')).2.2 ?_
         have h0 := (aoneI_eq_iff.mp (hs.symm.trans hs')).2.2
         exact le_antisymm (hτ.1.2.2.2 _ hτ'.1.2.1 (h0 ▸ hτ'.1.2.2.1))
           (hτ'.1.2.2.2 _ hτ.1.2.1 (h0 ▸ hτ.1.2.2.1)))

omit [(Language.qbf k).Structure A] in
/-- At a guessing choice, the state and the symbol read are what
`DescriptiveComplexity.altTr_unique`'s hypothesis excludes. -/
theorem altSrc_read_guess {cnf : Bool} {τ q a : AltV k A}
    (hb : τ.1.1 = AltBase.tGKeep false ∨ τ.1.1 = AltBase.tGSet) (hs : AltSrc cnf τ q)
    (hr : AltRead τ a) : q = stG τ.1.2 true ∧ a = symV false (τ.2 0) := by
  obtain ⟨⟨t, i⟩, w⟩ := τ
  rcases hb with hb | hb <;> simp only at hb <;> subst hb <;> exact ⟨hs, hr⟩

/-- **The two turns never compete**: for a conjunctive matrix the clause just
settled is either the last one or has a successor, and for a disjunctive one
they fire at different flags, so their source states differ. -/
theorem altTr_turn_pair {cnf : Bool} {τ τ' q : AltV k A} (hτ : AltTr cnf τ) (hτ' : AltTr cnf τ')
    (hs : AltSrc cnf τ q) (hs' : AltSrc cnf τ' q) {d : Bool}
    (hb : τ.1.1 = AltBase.tTurnNext d) (hb' : τ'.1.1 = AltBase.tTurnAcc d) : False := by
  have hs2 : q = stChk true d (τ.2 0) := by
    obtain ⟨⟨t, i⟩, w⟩ := τ
    simp only at hb
    subst hb
    exact hs
  have hs2' : q = stChk cnf d (τ'.2 0) := by
    obtain ⟨⟨t, i⟩, w⟩ := τ'
    simp only at hb'
    subst hb'
    exact hs'
  have hpair := aoneI_eq_iff.mp (hs2.symm.trans hs2')
  have hcnf : cnf = true := by
    have h := hpair.1
    simp only [AltBase.qChk.injEq] at h
    exact h.1.symm
  exact altTr_turn_excl hτ hτ' hb hb' hcnf hpair.2.2

/-- **At most one transition applies**, away from the one nondeterministic
choice of a guessing sweep: the state and the symbol read pin the base tag
(`DescriptiveComplexity.base_cases`), the base tag pins the rest
(`DescriptiveComplexity.altTr_payload`), and the two remaining ambiguities are
the exclusive branch points. -/
theorem altTr_unique {cnf : Bool} {τ τ' q a : AltV k A} (hτ : AltTr cnf τ) (hτ' : AltTr cnf τ')
    (hs : AltSrc cnf τ q) (hs' : AltSrc cnf τ' q) (hr : AltRead τ a) (hr' : AltRead τ' a)
    (hguess : ¬∃ (i : Fin (k + 1)) (x : A), q = stG i true ∧ a = symV false x) : τ = τ' := by
  have hst : stateBase cnf τ.1.1 = stateBase cnf τ'.1.1 :=
    ((altSrc_base hτ hs).1).symm.trans (altSrc_base hτ' hs').1
  have hrd : readBase τ.1.1 = readBase τ'.1.1 :=
    (altRead_base hτ hr).symm.trans (altRead_base hτ' hr')
  have hi : τ.1.2 = τ'.1.2 := by
    by_cases hsw : isSweepBase τ.1.1
    · have hsw' : isSweepBase τ'.1.1 := by
        rw [← isSweepBase_congr cnf _ _ (altTr_isTrBase hτ) (altTr_isTrBase hτ') hst]
        exact hsw
      have h1 := (altSrc_base hτ hs).2 hsw
      have h2 := (altSrc_base hτ' hs').2 hsw'
      exact h1.symm.trans h2
    · have hsw' : ¬isSweepBase τ'.1.1 := by
        rw [← isSweepBase_congr cnf _ _ (altTr_isTrBase hτ) (altTr_isTrBase hτ') hst]
        exact hsw
      exact Fin.ext ((altTr_index_zero hτ hsw).trans (altTr_index_zero hτ' hsw').symm)
  rcases base_cases cnf τ.1.1 τ'.1.1 (altTr_isTrBase hτ) (altTr_isTrBase hτ') hst hrd with
    heq | ⟨hk1, -⟩ | ⟨hk1, -⟩ | ⟨hb, hb'⟩ | ⟨hb, hb'⟩ | ⟨hb, hb'⟩ | ⟨hb, hb'⟩ |
      ⟨d, hb, hb'⟩ | ⟨d, hb, hb'⟩
  · exact altTr_payload hτ hτ' hs hs' hr hr' heq
  · exact absurd ⟨τ.1.2, τ.2 0, (altSrc_read_guess (Or.inl hk1) hs hr).1,
      (altSrc_read_guess (Or.inl hk1) hs hr).2⟩ hguess
  · exact absurd ⟨τ.1.2, τ.2 0, (altSrc_read_guess (Or.inr hk1) hs hr).1,
      (altSrc_read_guess (Or.inr hk1) hs hr).2⟩ hguess
  · exact (altTr_next_end_excl hτ hτ' hb hb' hi).elim
  · exact (altTr_next_end_excl hτ' hτ hb' hb hi.symm).elim
  · exact (altTr_end_excl hτ hτ' hb hb').elim
  · exact (altTr_end_excl hτ' hτ hb' hb).elim
  · exact (altTr_turn_pair hτ hτ' hs hs' hb hb').elim
  · exact (altTr_turn_pair hτ' hτ hs' hs hb' hb).elim


end Table

end AltQbf

end DescriptiveComplexity
