/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltGuess

/-!
# The check phase decides the matrix

`DescriptiveComplexity.AltQbf.accepts_from_chk_cnf` and its disjunctive twin build an
accepting run when the matrix holds. This is the converse: if the check phase
accepts, the matrix holds. Together they say that the tape the sweeps leave
behind is tested exactly.

The check phase is deterministic, so no read-off is needed: acceptance descends
along its unique run whatever the polarity of the block it sits in
(`DescriptiveComplexity.AltQbf.StepForced`), and each sweep can only end in one of the
two turns. The turn that accepts fires at the flag `cnf` – set for a
conjunctive matrix, where it means the clause is satisfied, clear for a
disjunctive one, where it means no literal of the term is violated – and that
is precisely the semantic conclusion. The turn that moves on fires at the flag
`true`, and hands the argument to the next clause.

The induction is therefore over the clauses, upwards, exactly as in the two
forward lemmas: `DescriptiveComplexity.AltQbf.ChkOk` is what the run from a clause
proves about that clause and every clause above it.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Verdict

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable {νs : Fin k → A → Prop}

/-! ### What a check sweep proves -/

variable (k) in
/-- Some literal of the clause `c` is good: satisfied, for a conjunctive
matrix; violated, for a disjunctive one. -/
def QChkGood (cnf : Bool) (νs : Fin k → A → Prop) (c : A) : Prop :=
  ∃ y : A, QGood k cnf c y (chkVal νs y)

variable (k) in
/-- **What the check phase has left to prove when it reaches the clause `c`**:
that every clause from `c` up is satisfied, or that some term from `c` up has
no violated literal. -/
def ChkOk (cnf : Bool) (νs : Fin k → A → Prop) (c : A) : Prop :=
  match cnf with
  | true => ∀ e : A, QbfCl k e → c ≤ e → QChkGood k cnf νs e
  | false => ∃ e : A, QbfCl k e ∧ c ≤ e ∧ ¬QChkGood k cnf νs e

/-! ### Elementary facts about check configurations -/

/-- A checking state is not accepting. -/
theorem not_acc_stChk {cnf f d : Bool} {c : A} :
    ¬(altMachine k A cnf).Acc (stChk f d c : AltV k A) := fun h =>
  AltBase.noConfusion (show AltBase.qChk f d = AltBase.qAcc from h)

omit [(Language.qbf k).Structure A] in
/-- Checking states are told apart by their flag, their direction and their
clause. -/
theorem stChk_eq_iff {f d f' d' : Bool} {c c' : A} :
    (stChk f d c : AltV k A) = stChk f' d' c' ↔ f = f' ∧ d = d' ∧ c = c' := by
  constructor
  · intro h
    obtain ⟨ht, -, hc⟩ := aoneI_eq_iff.mp h
    exact ⟨(AltBase.qChk.injEq f d f' d' ▸ ht).1, (AltBase.qChk.injEq f d f' d' ▸ ht).2, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem inCheck_confChkR (cnf : Bool) (c : A) (p : AltV k A) :
    InCheck (confChkR cnf νs c p) := Or.inl ⟨_, _, _, rfl⟩

theorem inCheck_confChkL (cnf : Bool) (c : A) (p : AltV k A) :
    InCheck (confChkL cnf νs c p) := Or.inl ⟨_, _, _, rfl⟩

/-- **Every step of the check phase is forced**: it is the only one available,
so acceptance descends along it whatever the polarity of the block. -/
theorem stepForced_of_inCheck {cnf start : Bool} {c c' : Config (AltV k A)} (hP : InCheck c)
    (hnacc : ¬(altMachine k A cnf).Acc c.state)
    (hstep : (altMachine k A cnf).Step c c') :
    StepForced (altMachine k A cnf) start c c' :=
  ⟨hnacc, Or.inr fun c'' h => inCheck_det c c'' c' hP h hstep⟩

omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- A configuration that accepts and is not accepting outright has an accepting
successor, whichever player owns it. -/
theorem exists_step_of_altAcc {M : ATMData (AltV k A)} {start : Bool} {n : ℕ}
    {c : Config (AltV k A)} (hnacc : ¬M.Acc c.state) (hacc : M.AltAcc start n c) :
    ∃ (c' : Config (AltV k A)) (m : ℕ), M.Step c c' ∧ M.AltAcc start m c' := by
  cases n with
  | zero => exact absurd hacc hnacc
  | succ m =>
    rcases hacc with h | ⟨-, ⟨c', hstep⟩, hall⟩ | ⟨-, c', hstep, hacc'⟩
    · exact absurd h hnacc
    · exact ⟨c', m, hstep, hall c' hstep⟩
    · exact ⟨c', m, hstep, hacc'⟩

/-! ### Descending a check sweep -/

/-- **A rightward check sweep reaches the right marker.** -/
theorem altAcc_chkR_posEnd {cnf start : Bool} {c : A} (hc : QbfCl k c) {n : ℕ}
    (hacc : (altMachine k A cnf).AltAcc start n (confChkR cnf νs c (posCell qbotA))) :
    ∃ m, (altMachine k A cnf).AltAcc start m (confChkR cnf νs c posEnd) := by
  have hcell : ∀ p q : AltV k A, SuccPos tagTupleLe AltPosn p q →
      tagTupleLe (posCell qbotA : AltV k A) p → tagTupleLe q (posEnd : AltV k A) →
      p.1.1 = AltBase.pCell := by
    intro p q hsucc hlb hub
    have h1 : altBaseIdx AltBase.pCell ≤ altBaseIdx p.1.1 :=
      altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hlb)
    have h2 : altBaseIdx p.1.1 ≤ altBaseIdx AltBase.pEnd :=
      altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le
        (isLinOrd_altTagTupleLe.2.1 p q posEnd hsucc.2.2.1 hub))
    rcases base_between h1 h2 with h | h
    · exact h
    · exact absurd (isLinOrd_altTagTupleLe.2.2.1 p q hsucc.2.2.1
        ((eq_posEnd_of_posn hsucc.1 h) ▸ hub)) hsucc.2.2.2.1
  obtain ⟨-, hend⟩ := altAcc_along_segment (M := altMachine k A cnf) isLinOrd_altTagTupleLe
    (conf := fun p => confChkR cnf νs c p) (p₀ := posCell qbotA) (p₁ := posEnd)
    (altPosn_posCell _) (fun p q hsucc hlb hub => step_chkR hc hsucc (hcell p q hsucc hlb hub))
    (fun p q hsucc hlb hub => stepForced_of_inCheck (inCheck_confChkR cnf c p) not_acc_stChk
      (step_chkR hc hsucc (hcell p q hsucc hlb hub)))
    n posEnd altPosn_posEnd (posCell_le_posEnd _) (altTagTupleLe_refl _) hacc
  exact ⟨_, hend⟩

/-- **A leftward check sweep reaches the left marker.** -/
theorem altAcc_chkL_posStart {cnf start : Bool} {c : A} (hc : QbfCl k c) {n : ℕ}
    (hacc : (altMachine k A cnf).AltAcc start n (confChkL cnf νs c (posCell qtopA))) :
    ∃ m, (altMachine k A cnf).AltAcc start m (confChkL cnf νs c posStart) := by
  have hcell : ∀ p q : AltV k A, SuccPos tagTupleLe AltPosn p q →
      tagTupleLe (posStart : AltV k A) p → tagTupleLe q (posCell (qtopA (A := A)) : AltV k A) →
      q.1.1 = AltBase.pCell := by
    intro p q hsucc _ hub
    rcases base_le_pCell (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hub)) with h | h
    · refine absurd (isLinOrd_altTagTupleLe.2.2.1 p q hsucc.2.2.1 ?_) hsucc.2.2.2.1
      rw [eq_posStart_of_posn hsucc.2.1 h]
      exact minPos_posStart.2 p hsucc.1
    · exact h
  obtain ⟨-, hend⟩ := altAcc_along_segment_down (M := altMachine k A cnf) isLinOrd_altTagTupleLe
    (conf := fun p => confChkL cnf νs c p) (p₀ := posStart) (p₁ := posCell qtopA)
    (altPosn_posCell _) (fun p q hsucc hlb hub => step_chkL hc hsucc (hcell p q hsucc hlb hub))
    (fun p q hsucc hlb hub => stepForced_of_inCheck (inCheck_confChkL cnf c q) not_acc_stChk
      (step_chkL hc hsucc (hcell p q hsucc hlb hub)))
    n posStart altPosn_posStart (altTagTupleLe_refl _) (posStart_le_posCell _) hacc
  exact ⟨_, hend⟩

/-! ### What the turn says -/

/-- **The turn at the right marker, read backwards.** Either the clause has a
good literal and the run moves on to the next one, or the flag settles the run
and the semantics of the matrix is decided on the spot. -/
theorem turn_of_step_chkR {cnf : Bool} {c : A} {c' : Config (AltV k A)}
    (hstep : (altMachine k A cnf).Step (confChkR cnf νs c posEnd) c') :
    (QChkGood k cnf νs c ∧ ∃ e : A, QbfNextCl k c e ∧ c' = confChkL cnf νs e (posCell qtopA)) ∨
      (chkFlagR cnf νs c posEnd = cnf ∧ (cnf = true → QbfMaxCl k c)) := by
  classical
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  have hTr : AltTr cnf τ := hτ
  have hSrc : AltSrc cnf τ (stChk (chkFlagR cnf νs c posEnd) true c : AltV k A) := hsrc
  have hRead : AltRead τ (tapeAfter νs k (posEnd : AltV k A)) := hread
  have hDst : AltDst cnf τ c'.state := hdst
  have hWrite : AltWrite τ (c'.tape (posEnd : AltV k A)) := hwrite
  have hMove : (AltRight τ ∧ SuccPos tagTupleLe AltPosn (posEnd : AltV k A) c'.head) ∨
      (¬AltRight τ ∧ SuccPos tagTupleLe AltPosn c'.head (posEnd : AltV k A)) := hmove
  have hFrame : ∀ r, r ≠ (posEnd : AltV k A) → c'.tape r = tapeAfter νs k r := hframe
  unfold AltTr at hTr
  unfold AltSrc at hSrc
  unfold AltRead at hRead
  unfold AltDst at hDst
  unfold AltWrite at hWrite
  unfold AltRight at hMove
  cases hb : τ.1.1
  all_goals rw [hb] at hTr hSrc hRead hDst hWrite hMove
  all_goals simp only at hTr hSrc hRead hDst hWrite hMove
  case tChk v f d =>
    -- the machine reads the right marker, not a cell
    exact absurd (congrArg (fun p => p.1.1) (hRead.symm.trans (rfl : _ = symEnd)))
      (by simp [acstI, aoneI])
  case tTurnNext d =>
    obtain ⟨hf, hd, hcl⟩ := stChk_eq_iff.mp hSrc.symm
    subst hd
    have hflag : chkFlagR cnf νs c posEnd = true := hf.symm
    have hnext : QbfNextCl k c (τ.2 1) := by rw [← hcl]; exact hTr.1
    have htape : c'.tape = tapeAfter νs k := by
      funext r
      rcases eq_or_ne r (posEnd : AltV k A) with rfl | hne
      · rw [hWrite]
        rfl
      · exact hFrame r hne
    have hhead : c'.head = posCell (qtopA (A := A)) := by
      rcases hMove with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (by simp)
      · exact succPos_left_unique isLinOrd_altTagTupleLe h succPos_posCell_posEnd
    refine Or.inl ⟨(chkFlagR_posEnd cnf c).mp hflag, τ.2 1, hnext, ?_⟩
    refine Config.ext ?_ hhead htape
    rw [hDst]
    change stChk false false (τ.2 1) = stChk (chkFlagL cnf νs (τ.2 1) (posCell qtopA)) false (τ.2 1)
    rw [chkFlagL_top]
  case tTurnAcc d =>
    obtain ⟨hf, hd, hcl⟩ := stChk_eq_iff.mp hSrc.symm
    subst hd
    exact Or.inr ⟨hf.symm, fun h => by rw [← hcl]; exact hTr.2.2.2 h⟩
  all_goals
    first
      | exact hTr.elim
      | exact absurd hSrc (by simp [acstI, aoneI])

/-- **The turn at the left marker, read backwards.** -/
theorem turn_of_step_chkL {cnf : Bool} {c : A} {c' : Config (AltV k A)}
    (hstep : (altMachine k A cnf).Step (confChkL cnf νs c posStart) c') :
    (QChkGood k cnf νs c ∧ ∃ e : A, QbfNextCl k c e ∧ c' = confChkR cnf νs e (posCell qbotA)) ∨
      (chkFlagL cnf νs c posStart = cnf ∧ (cnf = true → QbfMaxCl k c)) := by
  classical
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  have hTr : AltTr cnf τ := hτ
  have hSrc : AltSrc cnf τ (stChk (chkFlagL cnf νs c posStart) false c : AltV k A) := hsrc
  have hRead : AltRead τ (tapeAfter νs k (posStart : AltV k A)) := hread
  have hDst : AltDst cnf τ c'.state := hdst
  have hWrite : AltWrite τ (c'.tape (posStart : AltV k A)) := hwrite
  have hMove : (AltRight τ ∧ SuccPos tagTupleLe AltPosn (posStart : AltV k A) c'.head) ∨
      (¬AltRight τ ∧ SuccPos tagTupleLe AltPosn c'.head (posStart : AltV k A)) := hmove
  have hFrame : ∀ r, r ≠ (posStart : AltV k A) → c'.tape r = tapeAfter νs k r := hframe
  unfold AltTr at hTr
  unfold AltSrc at hSrc
  unfold AltRead at hRead
  unfold AltDst at hDst
  unfold AltWrite at hWrite
  unfold AltRight at hMove
  cases hb : τ.1.1
  all_goals rw [hb] at hTr hSrc hRead hDst hWrite hMove
  all_goals simp only at hTr hSrc hRead hDst hWrite hMove
  case tChk v f d =>
    exact absurd (congrArg (fun p => p.1.1) (hRead.symm.trans (rfl : _ = symStart)))
      (by simp [acstI, aoneI])
  case tTurnNext d =>
    obtain ⟨hf, hd, hcl⟩ := stChk_eq_iff.mp hSrc.symm
    subst hd
    have hflag : chkFlagL cnf νs c posStart = true := hf.symm
    have hnext : QbfNextCl k c (τ.2 1) := by rw [← hcl]; exact hTr.1
    have htape : c'.tape = tapeAfter νs k := by
      funext r
      rcases eq_or_ne r (posStart : AltV k A) with rfl | hne
      · rw [hWrite]
        rfl
      · exact hFrame r hne
    have hhead : c'.head = posCell (qbotA (A := A)) := by
      rcases hMove with ⟨-, h⟩ | ⟨h, -⟩
      · exact TMData.succPos_right_unique (M := (altMachine k A cnf).toTMData)
          isLinOrd_altTagTupleLe h succPos_posStart_posCell
      · exact absurd rfl h
    refine Or.inl ⟨(chkFlagL_posStart cnf c).mp hflag, τ.2 1, hnext, ?_⟩
    refine Config.ext ?_ hhead htape
    rw [hDst]
    change stChk false true (τ.2 1) = stChk (chkFlagR cnf νs (τ.2 1) (posCell qbotA)) true (τ.2 1)
    rw [chkFlagR_bot]
  case tTurnAcc d =>
    obtain ⟨hf, hd, hcl⟩ := stChk_eq_iff.mp hSrc.symm
    subst hd
    exact Or.inr ⟨hf.symm, fun h => by rw [← hcl]; exact hTr.2.2.2 h⟩
  all_goals
    first
      | exact hTr.elim
      | exact absurd hSrc (by simp [acstI, aoneI])

/-! ### Putting the clauses together -/

omit [Finite A] [Nonempty A] in
/-- **What the accepting turn says**: the clause settles the run, so it is the
last one that matters. -/
theorem chkOk_of_flag {cnf : Bool} {c : A} (hc : QbfCl k c) (hmax : cnf = true → QbfMaxCl k c)
    (hgood : QChkGood k cnf νs c ↔ cnf = true) : ChkOk k cnf νs c := by
  cases cnf with
  | true =>
    intro e he hle
    rw [le_antisymm ((hmax rfl).2 e he) hle]
    exact hgood.mpr rfl
  | false =>
    exact ⟨c, hc, le_refl c, fun h => Bool.noConfusion (hgood.mp h)⟩

omit [Finite A] [Nonempty A] in
/-- **What the turn to the next clause says**: this clause is good, and the run
goes on to settle the ones above it. -/
theorem chkOk_of_next {cnf : Bool} {c e : A} (hnext : QbfNextCl k c e)
    (hgood : QChkGood k cnf νs c) (hok : ChkOk k cnf νs e) : ChkOk k cnf νs c := by
  cases cnf with
  | true =>
    intro f hf hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact hgood
    · exact hok f hf (hnext.2.2.2 f hf hlt)
  | false =>
    obtain ⟨f, hf, hle, hbad⟩ := hok
    exact ⟨f, hf, le_trans (le_of_lt hnext.2.2.1) hle, hbad⟩

/-- **The check phase decides the matrix.** Whichever sweep it is on and
whichever clause it has reached, an accepting run proves that clause and every
clause above it settled. -/
theorem chkOk_of_altAcc {cnf start : Bool} :
    ∀ c : A, QbfCl k c →
      (∀ n : ℕ, (altMachine k A cnf).AltAcc start n (confChkR cnf νs c (posCell qbotA)) →
          ChkOk k cnf νs c) ∧
        ∀ n : ℕ, (altMachine k A cnf).AltAcc start n (confChkL cnf νs c (posCell qtopA)) →
          ChkOk k cnf νs c := by
  intro c
  induction c using WellFoundedGT.induction with
  | ind c IH =>
    intro hc
    constructor
    · intro n hacc
      obtain ⟨m, hend⟩ := altAcc_chkR_posEnd hc hacc
      obtain ⟨c', m', hstep, hacc'⟩ := exists_step_of_altAcc not_acc_stChk hend
      rcases turn_of_step_chkR hstep with ⟨hgood, e, hnext, hceq⟩ | ⟨hflag, hmax⟩
      · subst hceq
        exact chkOk_of_next hnext hgood ((IH e hnext.2.2.1 hnext.2.1).2 _ hacc')
      · refine chkOk_of_flag hc hmax ⟨fun h => ?_, fun h => ?_⟩
        · rw [← hflag]
          exact (chkFlagR_posEnd cnf c).mpr h
        · exact (chkFlagR_posEnd cnf c).mp (hflag.trans h)
    · intro n hacc
      obtain ⟨m, hend⟩ := altAcc_chkL_posStart hc hacc
      obtain ⟨c', m', hstep, hacc'⟩ := exists_step_of_altAcc not_acc_stChk hend
      rcases turn_of_step_chkL hstep with ⟨hgood, e, hnext, hceq⟩ | ⟨hflag, hmax⟩
      · subst hceq
        exact chkOk_of_next hnext hgood ((IH e hnext.2.2.1 hnext.2.1).1 _ hacc')
      · refine chkOk_of_flag hc hmax ⟨fun h => ?_, fun h => ?_⟩
        · rw [← hflag]
          exact (chkFlagL_posStart cnf c).mpr h
        · exact (chkFlagL_posStart cnf c).mp (hflag.trans h)

/-! ### The check's literal test is the matrix's -/

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem xorB_true (v : Bool) : xorB true v = v := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem xorB_false (v : Bool) : xorB false v = !v := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem chkVal_eq_true {x : A} : chkVal νs x = true ↔ qbfVal νs x := valAfter_top

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem chkVal_eq_false {x : A} : chkVal νs x = false ↔ ¬qbfVal νs x := by
  rw [← Bool.not_eq_true, chkVal_eq_true]

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- A conjunctive clause is good exactly when the assignment satisfies one of
its literals. -/
theorem qChkGood_true_iff {c : A} :
    QChkGood k true νs c ↔
      ∃ x : A, (QbfPos k c x ∧ qbfVal νs x) ∨ (QbfNeg k c x ∧ ¬qbfVal νs x) := by
  refine exists_congr fun x => ?_
  simp only [QGood, QbfLit, xorB_true]
  rw [chkVal_eq_true, chkVal_eq_false]

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- A disjunctive term has no violated literal exactly when the assignment
satisfies all of them. -/
theorem not_qChkGood_false_iff {c : A} :
    ¬QChkGood k false νs c ↔
      ∀ x : A, (QbfPos k c x → qbfVal νs x) ∧ (QbfNeg k c x → ¬qbfVal νs x) := by
  simp only [QChkGood, not_exists, QGood, QbfLit, xorB_false, not_or, not_and]
  refine forall_congr' fun x => ?_
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hp => ?_, fun hn hv => ?_⟩
    · by_contra hv
      exact h1 hp (by rw [chkVal_eq_false.mpr hv]; rfl)
    · exact h2 hn (by rw [chkVal_eq_true.mpr hv]; rfl)
  · rintro ⟨h1, h2⟩
    refine ⟨fun hp hbang => ?_, fun hn hbang => ?_⟩
    · exact chkVal_eq_false.mp (by simpa using hbang) (h1 hp)
    · exact h2 hn (chkVal_eq_true.mp (by simpa using hbang))

omit [Finite A] [Nonempty A] in
/-- **What the check phase tests is the matrix.** -/
theorem chkOk_iff_qbfMatrix {cnf : Bool} {c₀ : A} (hmin : QbfMinCl k c₀) :
    ChkOk k cnf νs c₀ ↔ QbfMatrix cnf νs := by
  cases cnf with
  | true =>
    constructor
    · intro h e he
      exact qChkGood_true_iff.mp (h e he (hmin.2 e he))
    · intro h e he _
      exact qChkGood_true_iff.mpr (h e he)
  | false =>
    constructor
    · rintro ⟨e, he, -, hbad⟩
      exact ⟨e, he, not_qChkGood_false_iff.mp hbad⟩
    · rintro ⟨e, he, hall⟩
      exact ⟨e, he, hmin.2 e he, not_qChkGood_false_iff.mpr hall⟩

/-! ### The check phase, both ways

What the last round hands over: from the entry of the check phase the machine
accepts exactly when the matrix holds of the tape the sweeps have written.
-/

variable (k A) in
/-- A generous bound on the length of the check phase: one sweep per clause. -/
noncomputable def chkLen : ℕ :=
  Nat.card A * bitRank tagTupleLe AltPosn (posEnd : AltV k A)

/-- **The check phase proves the matrix.** -/
theorem qbfMatrix_of_altAcc {cnf start : Bool} {c₀ : A} (hmin : QbfMinCl k c₀) {n : ℕ}
    (hacc : (altMachine k A cnf).AltAcc start n (confChkR cnf νs c₀ (posCell qbotA))) :
    QbfMatrix cnf νs :=
  (chkOk_iff_qbfMatrix hmin).mp ((chkOk_of_altAcc c₀ hmin.1).1 n hacc)

/-- **The matrix makes the check phase accept**, at either polarity of the
block it sits in, since the phase is deterministic. -/
theorem altAcc_of_qbfMatrix {cnf start : Bool} {c₀ : A} (hmin : QbfMinCl k c₀)
    (hmat : QbfMatrix cnf νs) {n : ℕ} (hn : chkLen k A ≤ n) :
    (altMachine k A cnf).AltAcc start n (confChkR cnf νs c₀ (posCell qbotA)) := by
  have hbound : {e : A | QbfCl k e ∧ c₀ ≤ e}.ncard *
      bitRank tagTupleLe AltPosn (posEnd : AltV k A) ≤ n := by
    refine le_trans (Nat.mul_le_mul_right _ ?_) hn
    have h := Set.ncard_le_ncard (Set.subset_univ {e : A | QbfCl k e ∧ c₀ ≤ e}) (Set.toFinite _)
    rwa [Set.ncard_univ] at h
  cases cnf with
  | true =>
    obtain ⟨-, m, cfin, hm, hrun, hacc⟩ :=
      accepts_from_chk_cnf rfl (fun e he => qChkGood_true_iff.mpr (hmat e he)) c₀ hmin.1
    exact altAcc_of_check (le_trans hm hbound) (inCheck_confChkR _ _ _) hrun hacc
  | false =>
    obtain ⟨e, he, hall⟩ := hmat
    obtain ⟨-, m, cfin, hm, hrun, hacc⟩ :=
      accepts_from_chk_dnf rfl he (not_exists.mp (not_qChkGood_false_iff.mpr hall)) c₀ hmin.1
        (hmin.2 e he)
    exact altAcc_of_check (le_trans hm hbound) (inCheck_confChkR _ _ _) hrun hacc

end Verdict

end AltQbf

end DescriptiveComplexity
