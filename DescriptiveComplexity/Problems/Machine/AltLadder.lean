/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltRound

/-!
# The round game as an implication ladder

The last semantic step before the `Σₖ` sentence of the membership half. The
game of `DescriptiveComplexity.Problems.Machine.AltGame` quantifies its rounds
with `DescriptiveComplexity.guardQ`, whose universal case carries an existence
clause: a universal player with no legal move loses rather than winning
vacuously. Over configurations that clause is harmless, but over *walks* it is
an existential second-order quantifier sitting inside a universal block, and a
sentence built on it would not be `Σₖ` at all.

The clause is however redundant. A round always has a move available: follow
the previous round's walk as far as it is committed, and from the entry into
the round's own block run *greedily* – step while a step is available, stand
still once stuck – which is `DescriptiveComplexity.ATMData.greedyFrom`. So the
game can be restated with the unguarded
`DescriptiveComplexity.bareQ`, and `DescriptiveComplexity.ATMData.AltLadder` is
that restatement: an alternating chain of conjunctions and implications, which
is exactly the shape a first-order kernel can have.

The one clause that is *not* redundant is at the top: round `0` has no previous
walk to extend, so a legal walk exists only if an initial configuration does.
That is first-order – it is `∃ q, Start q`, the rest being supplied by
`DescriptiveComplexity.TMData.exists_isInit` – and it is carried into the
sentence as a plain conjunct rather than as a quantifier.
-/

namespace DescriptiveComplexity

/-! ### Unguarded alternation -/

/-- **Quantification with a polarity, unguarded**: existentially the guard is
conjoined, universally it is assumed. Unlike `DescriptiveComplexity.guardQ`
nothing here asks the guard to be satisfiable, which is what makes this shape
expressible by a first-order kernel under a second-order prefix. -/
def bareQ (pol : Bool) {α : Type} (C P : α → Prop) : Prop :=
  match pol with
  | true => ∃ a, C a ∧ P a
  | false => ∀ a, C a → P a

theorem bareQ_true {α : Type} (C P : α → Prop) :
    bareQ true C P ↔ ∃ a, C a ∧ P a := Iff.rfl

theorem bareQ_false {α : Type} (C P : α → Prop) :
    bareQ false C P ↔ ∀ a, C a → P a := Iff.rfl

/-- Unguarded quantification only depends on its two predicates up to pointwise
equivalence. -/
theorem bareQ_congr (pol : Bool) {α : Type} {C C' P P' : α → Prop}
    (hC : ∀ a, C a ↔ C' a) (hP : ∀ a, C a → (P a ↔ P' a)) :
    bareQ pol C P ↔ bareQ pol C' P' := by
  cases pol
  · exact ⟨fun h a ha => (hP a ((hC a).mpr ha)).mp (h a ((hC a).mpr ha)),
      fun h a ha => (hP a ha).mpr (h a ((hC a).mp ha))⟩
  · exact exists_congr fun a => ⟨fun ⟨h1, h2⟩ => ⟨(hC a).mp h1, (hP a h1).mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨(hC a).mpr h1, (hP a ((hC a).mpr h1)).mpr h2⟩⟩

/-- **A satisfiable guard makes the two quantifications agree**: the existence
clause of `DescriptiveComplexity.guardQ` is the only difference between them. -/
theorem guardQ_iff_bareQ (pol : Bool) {α : Type} {C P : α → Prop} (hne : ∃ a, C a) :
    guardQ pol C P ↔ bareQ pol C P := by
  cases pol
  · exact ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩
  · exact Iff.rfl

namespace ATMData

variable {A : Type} [Finite A] {M : ATMData A} {k : ℕ}

/-! ### The greedy continuation of a round -/

open Classical in
/-- **The walk following `prev` up to `t` and running greedily after it**: the
move a round can always make. It is
`DescriptiveComplexity.ATMData.splice` of the greedy sequence, with no bound on
its length – a walk never has to stand still, since
`DescriptiveComplexity.ATMData.greedy` already does when it must. -/
noncomputable def greedyFrom (M : ATMData A) (prev : A → Config A) (t : A) : A → Config A :=
  fun x =>
    if M.Posn x ∧ ¬M.Le x t then
      M.greedy (prev t) (bitRank M.Le M.Posn x - bitRank M.Le M.Posn t)
    else prev x

omit [Finite A] in
/-- Below the entry time the continuation is the previous walk. -/
theorem greedyFrom_of_le {prev : A → Config A} {t x : A} (h : ¬(M.Posn x ∧ ¬M.Le x t)) :
    M.greedyFrom prev t x = prev x := by
  classical
  rw [greedyFrom, if_neg h]

omit [Finite A] in
/-- From the entry time on, the continuation is the greedy sequence. -/
theorem greedyFrom_of_lt (hlin : IsLinOrd M.Le) {prev : A → Config A} {t x : A}
    (hx : M.Posn x) (hle : M.Le t x) :
    M.greedyFrom prev t x =
      M.greedy (prev t) (bitRank M.Le M.Posn x - bitRank M.Le M.Posn t) := by
  classical
  rcases eq_or_ne x t with rfl | hne
  · rw [greedyFrom, if_neg fun h => h.2 (hlin.1 x), Nat.sub_self]
    rfl
  · have hnle : ¬M.Le x t := fun hcon => hne (hlin.2.2.1 x t hcon hle)
    rw [greedyFrom, if_pos ⟨hx, hnle⟩]

/-- **The greedy continuation is an admissible move for round `i`**, given the
entry `t` into block `i`: it reproduces everything the earlier rounds committed
– they committed exactly the times strictly below `t` – and it is legal below
block `i + 1` because the greedy sequence is. -/
theorem roundCond_greedyFrom (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le) {i : ℕ}
    {prev : A → Config A} (hprev : M.LegalBelow i prev) {t : A}
    (ht : M.Posn t) (hti : M.Blk i (prev t).state)
    (hpast : ∀ s, M.Posn s → M.Le s t → s ≠ t → M.BlkLt i (prev s).state) :
    M.RoundCond i prev (M.greedyFrom prev t) := by
  classical
  set w := M.greedyFrom prev t with hw
  have hreadlow : ∀ x, M.Posn x → M.Le x t → w x = prev x := fun x _ hle =>
    greedyFrom_of_le fun hcon => hcon.2 hle
  have hread : ∀ x, M.Posn x → M.Le t x →
      w x = M.greedy (prev t) (bitRank M.Le M.Posn x - bitRank M.Le M.Posn t) :=
    fun x hx hle => greedyFrom_of_lt hlin hx hle
  -- the low blocks of `prev` are exactly the times strictly below `t`
  have hlow : ∀ x, M.Posn x → M.BlkLt i (prev x).state → M.Le x t ∧ x ≠ t := by
    intro x hx hbx
    have hne : x ≠ t := by
      rintro rfl
      exact ((blkLt_iff hbwf hti).mp hbx).false
    refine ⟨?_, hne⟩
    by_contra hcon
    have hle : M.Le t x := (hlin.2.2.2 t x).resolve_right hcon
    exact ((blkLt_iff hbwf hti).mp (blkLt_of_le hbwf hlin hprev.2.1 ht hx hle hbx)).false
  -- the step obligation, at a pair of consecutive positions, with no guard
  have hstep : ∀ p q, SuccPos M.Le M.Posn p q →
      (M.Step (w p) (w q) ∧ ¬M.Acc (w p).state) ∨
        (w q = w p ∧ (M.Acc (w p).state ∨ M.Stuck (w p))) := by
    intro p q hpq
    have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    by_cases hpt : p = t
    · -- the entry itself: the greedy sequence starts here
      subst hpt
      rw [hreadlow p hpq.1 (hlin.1 p), hread q hpq.2.1 hpq.2.2.1, hrq, Nat.add_sub_cancel_left]
      exact greedy_step M (prev p) 0
    · by_cases hple : M.Le p t
      · -- strictly below the entry: the previous walk answers
        have hlt : bitRank M.Le M.Posn p < bitRank M.Le M.Posn t := bitRank_lt hlin hpq.1 hple hpt
        have hqle : M.Le q t := le_of_bitRank_le hlin hpq.2.1 ht (by omega)
        rw [hreadlow p hpq.1 hple, hreadlow q hpq.2.1 hqle]
        exact hprev.2.2 p q hpq (hpast p hpq.1 hple hpt)
      · -- above the entry: the greedy sequence answers
        have htp : M.Le t p := (hlin.2.2.2 t p).resolve_right hple
        have hlt : bitRank M.Le M.Posn t < bitRank M.Le M.Posn p :=
          bitRank_lt hlin ht htp fun hcon => hpt hcon.symm
        rw [hread p hpq.1 htp, hread q hpq.2.1 (hlin.2.1 t p q htp hpq.2.2.1), hrq,
          show bitRank M.Le M.Posn p + 1 - bitRank M.Le M.Posn t =
            (bitRank M.Le M.Posn p - bitRank M.Le M.Posn t) + 1 by omega]
        exact greedy_step M (prev t) _
  refine ⟨⟨fun p hp => ?_, fun p q hpq j j' hj hj' => ?_,
      fun p q hpq _ => hstep p q hpq⟩, fun x hx hbx => ?_, fun x y hxy hbx => ?_⟩
  · rw [hreadlow p hp.1 (hp.2 t ht)]
    exact hprev.1 p hp
  · rcases hstep p q hpq with ⟨hs, -⟩ | ⟨heq, -⟩
    · rcases blk_step hbwf hs hj with h | h
      · exact Nat.le_of_eq (blk_unique hbwf hj' h).symm
      · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j)
          (Nat.le_of_eq (blk_unique hbwf h hj')))
    · rw [heq] at hj'
      exact Nat.le_of_eq (blk_unique hbwf hj hj')
  · exact hreadlow x hx (hlow x hx hbx).1
  · obtain ⟨hle, hne⟩ := hlow x hxy.1 hbx
    have hlt : bitRank M.Le M.Posn x < bitRank M.Le M.Posn t := bitRank_lt hlin hxy.1 hle hne
    have hrq : bitRank M.Le M.Posn y = bitRank M.Le M.Posn x + 1 := bitRank_succPos hlin hxy
    exact hreadlow y hxy.2.1 (le_of_bitRank_le hlin hxy.2.1 ht (by omega))

/-! ### Every round has a move -/

/-- **Either the previous walk never reaches block `i`, or it enters it at a
definite time.** The entry is the lowest time whose block is not below `i`, and
it is in block `i` exactly because the step into it is legal. -/
theorem exists_entry (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le) {i : ℕ} (hi : 0 < i)
    {prev : A → Config A} (hprev : M.LegalBelow i prev) :
    (∀ x, M.Posn x → M.BlkLt i (prev x).state) ∨
      ∃ t, M.Posn t ∧ M.Blk i (prev t).state ∧
        ∀ s, M.Posn s → M.Le s t → s ≠ t → M.BlkLt i (prev s).state := by
  classical
  by_cases hall : ∀ x, M.Posn x → M.BlkLt i (prev x).state
  · exact Or.inl hall
  refine Or.inr ?_
  push Not at hall
  obtain ⟨x₀, hx₀, hbx₀⟩ := hall
  obtain ⟨t, ⟨htp, htb⟩, htmin⟩ :=
    exists_minPos (Le := M.Le) (Posn := fun y => M.Posn y ∧ ¬M.BlkLt i (prev y).state)
      hlin ⟨x₀, hx₀, hbx₀⟩
  have hpast : ∀ s, M.Posn s → M.Le s t → s ≠ t → M.BlkLt i (prev s).state := by
    intro s hs hle hne
    by_contra hcon
    exact hne (hlin.2.2.1 s t hle (htmin s ⟨hs, hcon⟩))
  have hnotmin : ¬MinPos M.Le M.Posn t := by
    intro hmin
    exact htb ⟨0, hi, hbwf.2.2 (prev t).state (hprev.1 t hmin).1⟩
  obtain ⟨s₀, hs₀⟩ := exists_predPos hlin htp hnotmin
  exact ⟨t, htp,
    blk_eq_of_entry hbwf hprev hs₀ (hpast s₀ hs₀.1 hs₀.2.2.1 hs₀.2.2.2.1) htb, hpast⟩

/-- **A round always has an admissible move**, which is what makes the
existence clause of `DescriptiveComplexity.guardQ` redundant from round `1` on.
If the previous walk never reaches block `i` it is itself admissible – it has
nothing left to answer for – and otherwise the greedy continuation of its entry
into the block is. -/
theorem exists_roundCond (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le) {i : ℕ}
    (hi : 0 < i) {prev : A → Config A} (hprev : M.LegalBelow i prev) :
    ∃ w, M.RoundCond i prev w := by
  rcases exists_entry hbwf hlin hi hprev with hall | ⟨t, ht, hti, hpast⟩
  · exact ⟨prev, ⟨hprev.1, hprev.2.1, fun p q hpq _ => hprev.2.2 p q hpq (hall p hpq.1)⟩,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · exact ⟨M.greedyFrom prev t, roundCond_greedyFrom hbwf hlin hprev ht hti hpast⟩

/-! ### The ladder -/

variable (M) in
/-- **The game from round `i` on, unguarded**: the shape a first-order kernel
can express, an alternating chain of conjunctions and implications. -/
def gameLadder (start : Bool) (i : ℕ) : ℕ → (A → Config A) → Prop
  | 0, prev => M.AccAt prev
  | m + 1, prev =>
      bareQ (blockPol start i) (M.RoundCond i prev) fun w => gameLadder start (i + 1) m w

variable (M) in
/-- **The whole `k`-round ladder**, with the first round peeled off as in
`DescriptiveComplexity.ATMData.AltGame`. -/
def AltLadder (start : Bool) : ℕ → Prop
  | 0 => False
  | m + 1 =>
      bareQ (blockPol start 0) (fun w => M.LegalBelow 1 w) fun w => M.gameLadder start 1 m w

/-- **The game is the ladder, from round `1` on.** -/
theorem gameFrom_iff_gameLadder (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le)
    (start : Bool) :
    ∀ (m i : ℕ), 0 < i → ∀ prev : A → Config A, M.LegalBelow i prev →
      (M.gameFrom start i m prev ↔ M.gameLadder start i m prev) := by
  intro m
  induction m with
  | zero => intro _ _ _ _; exact Iff.rfl
  | succ m ih =>
    intro i hi prev hprev
    change guardQ _ _ _ ↔ bareQ _ _ _
    refine (guardQ_iff_bareQ _ (exists_roundCond hbwf hlin hi hprev)).trans ?_
    exact bareQ_congr _ (fun _ => Iff.rfl) fun w hw => ih (i + 1) (by omega) w hw.1

/-- **The whole game is the whole ladder.** The hypothesis is the one existence
clause that is not redundant: round `0` extends no previous walk, so it needs an
initial configuration to exist. -/
theorem altGame_iff_altLadder (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le)
    (hinit : ∃ c₀, M.IsInit c₀) (start : Bool) :
    M.AltGame start k ↔ M.AltLadder start k := by
  obtain ⟨c₀, hc₀⟩ := hinit
  cases k with
  | zero => exact Iff.rfl
  | succ m =>
    change guardQ _ _ _ ↔ bareQ _ _ _
    refine (guardQ_iff_bareQ _
      ⟨M.greedyWalk c₀, (legalBelow_greedyWalk hbwf hlin hc₀ 1).1⟩).trans ?_
    exact bareQ_congr _ (fun _ => Iff.rfl)
      fun w hw => gameFrom_iff_gameLadder hbwf hlin start m 1 (by omega) w hw

/-- **Alternating acceptance is the ladder**, the statement the `Σₖ` sentence
of the membership half expresses. -/
theorem altAccepts_iff_altLadder (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le)
    {p₀ p₁ : A} (hmin : MinPos M.Le M.Posn p₀) (hmax : MaxPos M.Le M.Posn p₁) (hk : 0 < k)
    (hinit : ∃ c₀, M.IsInit c₀) (start : Bool) :
    M.AltAccepts start ↔ M.AltLadder start k :=
  (M.altAccepts_iff_altGame hbwf hlin hmax start hmin hk).trans
    (altGame_iff_altLadder hbwf hlin hinit start)

end ATMData

end DescriptiveComplexity
