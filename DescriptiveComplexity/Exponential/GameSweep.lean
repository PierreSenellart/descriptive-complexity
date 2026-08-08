/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameRun

/-!
# The sweep, read back

`DescriptiveComplexity.sweep_run` says what a sweep *may do*; the game needs
the converse as well, because the universal player's move **is** a sweep and
`DescriptiveComplexity.ATMData.AltWin.all` quantifies over every step. So a
sweep has to be read back the way `DescriptiveComplexity.ctrlCfg_cases` reads
back a control step.

## The invariant

`DescriptiveComplexity.SweptCfg` is *the tape is `tapeOfAssign ρ' σ'` for some
pair agreeing with the original outside the swept region*. That is exactly what
a half-finished sweep has: the cells it has passed hold the new assignment,
those ahead the old one, and **a mixture of the two is again an assignment** –
so no notion of “how far it has got” is needed, and the order on cells is never
consulted.

The step that rewrites one cell is
`DescriptiveComplexity.exists_tapeOfAssign_upd`, and the whole content of
`DescriptiveComplexity.sweepCfg_cases` is that every step either keeps the
family and moves the head on, or is the handover to the rewind at the right
sentinel.

## What the game gets

* `DescriptiveComplexity.altWin_sweep_ex` – the existential player sweeps a
  chosen assignment in and the play continues at the rewind's target;
* `DescriptiveComplexity.altWin_sweep_all` – the universal player's sweep, where
  *every* assignment of the region has to be answered. It is the one place a
  walk is run backwards, through `DescriptiveComplexity.altWin_of_walk`.
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### A configuration of a sweep -/

/-- **A tape a sweep may have produced**: the machine is in the given phase at
the constant valuation, its head is a position, and the tape holds a pair of
assignments agreeing with the original outside the region being written. -/
def SweptCfg {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] (a₀ : A)
    (hdim : blockArityBound B ≤ gameDim B V) (vars : GameQuestion → ℕ)
    (ρ σ : B.Assignment A) (tgt : Bool) (p : MachPh V M)
    (c : Config (GamePt B V M A)) : Prop :=
  ∃ ρ' σ' : B.Assignment A, (∀ rr : Bool, rr ≠ tgt → cond rr σ' ρ' = cond rr σ ρ) ∧
    c.state = phasePt p (fun _ => a₀) ∧ machPosn c.head ∧ machDom (ctrlArity vars) c.head ∧
    ∀ q : GamePt B V M A, machPosn q → machDom (ctrlArity vars) q →
      c.tape q = tapeOfAssign a₀ hdim ρ' σ' q

section Sweep

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] [Finite A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {ρ σ : B.Assignment A} {r tgt : Bool} {cont : SweepCont} {par : Bool}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

omit [Finite A] in
/-- **Every step of a sweep either carries it on or hands over to its rewind.**
The three rule families are told apart by the symbol read – the left mark, a
cell's symbol, the right mark – so the head's position decides which fires, and
the family is closed because rewriting one cell of the swept region gives
another assignment of it. -/
theorem sweepCfg_cases (h₀ : IsBot a₀) {c c' : Config (GamePt B V M A)}
    (h : SweptCfg a₀ hdim vars ρ σ tgt (MachPh.sweepPh r tgt cont par) c)
    (hstep : (𝕄).toTMData.Step c c') :
    (SweptCfg a₀ hdim vars ρ σ tgt (MachPh.sweepPh r tgt cont par) c' ∧
      SuccPos (𝕄).Le (𝕄).Posn c.head c'.head) ∨
    (SweptCfg a₀ hdim vars ρ σ tgt (MachPh.rewindPh r tgt cont false) c' ∧
      c'.head ≠ rightPt a₀ ∧ c'.head ≠ leftPt a₀ false) := by
  classical
  obtain ⟨ρ', σ', hkeep, hstate, hpos, hdom, htape⟩ := h
  obtain ⟨t, w, hrule, ⟨hsrc, -, -⟩, hread, ⟨hdst, hcd, -⟩, hwrite, hframe, hmove⟩ :=
    (game_step_iff c c').mp hstep
  have hts : t.src = MachPh.sweepPh r tgt cont par := by
    have := hsrc.symm.trans (congrArg Prod.fst hstate)
    exact Sum.inl.inj (Sum.inr.inj this)
  have hconst : ∀ x : Fin (gameDim B V) → A, Canon 0 x → x = fun _ => a₀ :=
    fun x hx => funext fun j => le_antisymm (hx j (Nat.zero_le _) a₀) (h₀ _)
  have hold : c.tape c.head = tapeOfAssign a₀ hdim ρ' σ' c.head := htape _ hpos hdom
  rcases sweep_cases (by rw [hts]; rfl) hrule with
    ⟨hd, hrd, hwr, hrt⟩ | ⟨hd, hrt, b₁, b', rr, i₁, hrd, hwr, hb⟩ | ⟨hd, hrd, hwr, hrt⟩
  · -- (B) crossing a sentinel: the head is on one, and nothing changes
    have hsymr : c.tape c.head = markPt a₀ false := by rw [hread, hrd]; rfl
    have hhd : ∃ b, c.head = leftPt a₀ b := by
      rcases posn_cases_tape h₀ (blockArityBound_le_gameDim B V) hpos hdom with
        hb | ⟨r₁, i₁, ā, hcell⟩ | hr
      · exact hb
      · exact absurd (hold.symm.trans hsymr) (by
          rw [hcell, tapeOfAssign_cellPt]; exact valPt_ne_markPt a₀)
      · exact absurd (hold.symm.trans hsymr) (by
          rw [hr, tapeOfAssign_rightPt]; exact markPt_ne_markPt a₀ (by simp))
    have hsame : ∀ q : GamePt B V M A, q ≠ c.head → c'.tape q = c.tape q := hframe
    have hhead : c'.tape c.head = c.tape c.head := by rw [hwrite, hwr, gameSymPt_mark, hsymr]
    have hcd0 : Canon 0 c'.state.2 := by rw [hd, hts] at hcd; exact hcd
    obtain ⟨-, hs⟩ : t.right = true ∧ SuccPos (𝕄).Le (𝕄).Posn c.head c'.head := by
      rcases hmove with hl | ⟨hrf, -⟩
      · exact hl
      · exact absurd (hrt.symm.trans hrf) (by simp)
    refine Or.inl ⟨⟨ρ', σ', hkeep, Prod.ext (by rw [hdst, hd, hts]; rfl) (hconst _ hcd0),
      hs.2.1.1, hs.2.1.2, fun q hq hd' => ?_⟩, hs⟩
    by_cases hqe : q = c.head
    · rw [hqe, hhead]; exact htape _ hpos hdom
    · rw [hsame q hqe]; exact htape q hq hd'
  · -- (C) at a cell: the swept region is rewritten, the other copied back
    have hsymr : c.tape c.head = valPt a₀ b₁ rr i₁ (argsOf i₁ (addrOf w)) := by
      rw [hread, hrd]; rfl
    have hwrs : c'.tape c.head = valPt a₀ b' rr i₁ (argsOf i₁ (addrOf w)) := by
      rw [hwrite, hwr]; rfl
    obtain ⟨r₁, i₂, ā, hcell⟩ : ∃ (r₁ : Bool) (i₂ : B.ι) (ā : Fin (B.arity i₂) → A),
        c.head = cellPt a₀ r₁ i₂ ā := by
      rcases posn_cases_tape h₀ (blockArityBound_le_gameDim B V) hpos hdom with
        ⟨b, hb⟩ | hc | hr
      · exact absurd (hsymr.symm.trans hold) (by
          rw [hb, tapeOfAssign_leftPt]; exact valPt_ne_markPt a₀)
      · exact hc
      · exact absurd (hsymr.symm.trans hold) (by
          rw [hr, tapeOfAssign_rightPt]; exact valPt_ne_markPt a₀)
    have hval : valPt (C := GameCtrlTag B V M) (dim := gameDim B V) a₀ b₁ rr i₁
        (argsOf i₁ (addrOf w)) =
        valPt a₀ (decide (cond r₁ σ' ρ' i₂ ā)) r₁ i₂ ā := by
      rw [← hsymr, hold, hcell, tapeOfAssign_cellPt]
    obtain ⟨hb₁, hrr, -⟩ := valPt_inj_tag a₀ hval
    have hcelleq : cellPt (C := GameCtrlTag B V M) (dim := gameDim B V) a₀ rr i₁
        (argsOf i₁ (addrOf w)) = cellPt a₀ r₁ i₂ ā :=
      cellPt_eq_of_valPt_eq a₀ hdim hval
    have hwr' : c'.tape c.head = valPt a₀ b' r₁ i₂ ā := by
      rw [hwrs]; exact valPt_eq_of_valPt_eq a₀ hdim b' hval
    have hcd0 : Canon 0 c'.state.2 := by rw [hd, hts] at hcd; exact hcd
    obtain ⟨-, hs⟩ : t.right = true ∧ SuccPos (𝕄).Le (𝕄).Posn c.head c'.head := by
      rcases hmove with hl | ⟨hrf, -⟩
      · exact hl
      · exact absurd (hrt.symm.trans hrf) (by simp)
    have hstate' : c'.state = phasePt (MachPh.sweepPh r tgt cont par) (fun _ => a₀) :=
      Prod.ext (by rw [hdst, hd, hts]; rfl) (hconst _ hcd0)
    refine Or.inl ⟨?_, hs⟩
    by_cases hbb : b' = decide (cond r₁ σ' ρ' i₂ ā)
    · -- the bit is written back: the tape does not change at all
      refine ⟨ρ', σ', hkeep, hstate', hs.2.1.1, hs.2.1.2, fun q hq hd' => ?_⟩
      by_cases hqe : q = c.head
      · rw [hqe, hwr', hbb, ← tapeOfAssign_cellPt a₀ hdim ρ' σ' r₁ i₂ ā, ← hcell]
      · rw [hframe q hqe]; exact htape q hq hd'
    · -- the bit is guessed: it is the swept region, and the pair is updated
      have hrtgt : r₁ = tgt := by
        rcases hb with hc | hc
        · rw [hts] at hc
          rw [← hrr]
          exact hc
        · exact absurd (hc.trans hb₁) hbb
      obtain ⟨ρ'', σ'', hkeep', hoff, hat⟩ :=
        exists_tapeOfAssign_upd (C := GameCtrlTag B V M) (carity := ctrlArity vars) a₀ h₀ hdim
          ρ' σ' tgt i₂ ā b'
      refine ⟨ρ'', σ'', fun rr' hrr' => (hkeep' rr' hrr').trans (hkeep rr' hrr'), hstate',
        hs.2.1.1, hs.2.1.2, fun q hq hd' => ?_⟩
      by_cases hqe : q = c.head
      · rw [hqe, hwr', hcell, hrtgt] at *
        exact hat.symm
      · rw [hframe q hqe, htape q hq hd', hoff q hq hd' (by rw [← hrtgt, ← hcell]; exact hqe)]
  · -- (D) at the right mark: hand over to the rewind, moving left
    have hsymr : c.tape c.head = markPt a₀ true := by rw [hread, hrd]; rfl
    have hhd : c.head = rightPt a₀ := by
      rcases posn_cases_tape h₀ (blockArityBound_le_gameDim B V) hpos hdom with
        ⟨b, hb⟩ | ⟨r₁, i₁, ā, hcell⟩ | hr
      · exact absurd (hold.symm.trans hsymr) (by
          rw [hb, tapeOfAssign_leftPt]; exact markPt_ne_markPt a₀ (by simp))
      · exact absurd (hold.symm.trans hsymr) (by
          rw [hcell, tapeOfAssign_cellPt]; exact valPt_ne_markPt a₀)
      · exact hr
    have hcd0 : Canon 0 c'.state.2 := by rw [hd, hts] at hcd; exact hcd
    obtain ⟨-, hs⟩ : t.right = false ∧ SuccPos (𝕄).Le (𝕄).Posn c'.head c.head := by
      rcases hmove with ⟨hrf, -⟩ | hl
      · exact absurd (hrt.symm.trans hrf) (by simp)
      · exact hl
    have hhead : c'.tape c.head = c.tape c.head := by rw [hwrite, hwr, gameSymPt_mark, hsymr]
    refine Or.inr ⟨⟨ρ', σ', hkeep, Prod.ext (by rw [hdst, hd, hts]; rfl) (hconst _ hcd0),
      hs.1.1, hs.1.2, fun q hq hd' => ?_⟩, ?_, ?_⟩
    · by_cases hqe : q = c.head
      · rw [hqe, hhead]; exact htape _ hpos hdom
      · rw [hframe q hqe]; exact htape q hq hd'
    · intro hc
      exact hs.2.2.2.1 (hc.trans hhd.symm)
    · have hs' : SuccPos (𝕄).Le (𝕄).Posn c'.head (rightPt a₀) := hhd ▸ hs
      exact succPos_ne_leftPt (carity := ctrlArity vars) h₀ (one_lt_fam_rightPt (a₀ := a₀)) hs'

/-! ### The rewind that follows a sweep -/

/-- **A rewind wins if its continuation does.** It changes nothing and its
phase is existential, so the whole walk back is one guarded chain. -/
theorem altWin_rewind (h₀ : IsBot a₀) {ρ' σ' : B.Assignment A} {d : Config (GamePt B V M A)}
    (hstate : d.state = phasePt (MachPh.rewindPh r tgt cont false) (fun _ => a₀))
    (hpos : (𝕄).Posn d.head) (hne : d.head ≠ rightPt a₀) (hlow : d.head ≠ leftPt a₀ false)
    (htape : ∀ q : GamePt B V M A, machPosn q → machDom (ctrlArity vars) q →
      d.tape q = tapeOfAssign a₀ hdim ρ' σ' q)
    (hcont : ∀ c', CtrlCfg a₀ hdim vars ρ' σ'
        (MachPh.rewindTarget (MachPh.rewindPh r tgt cont false)) (fun _ => a₀) c' →
        (𝕄).AltWin true c') :
    (𝕄).AltWin true d := by
  obtain ⟨e, hchain, hestate, hehead, hetape⟩ :=
    rewind_run (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
      h₀ d hstate hpos hne hlow (fun q hq => htape q hq.1 hq.2)
  refine altWin_of_guardedChain (Guard := fun x => x.state = d.state) (fun x hx => ?_) hchain ?_
  · rw [hx, hstate, gameMachine_isUniv hdim _ _ _, MachPh.isUniv_rewind pol rfl]
    exact Bool.false_ne_true
  · refine hcont e ⟨hestate, fun _ _ => h₀, ?_, fun q hq hd => hetape q ⟨hq, hd⟩⟩
    rw [hehead, MachPh.par_rewindTarget]

/-! ### The two sweeps -/

/-- **An existential sweep writes the assignment its owner chooses**, and the
play continues at the rewind's target. -/
theorem altWin_sweep_ex (h₀ : IsBot a₀) {ρ' σ' : B.Assignment A}
    (hkeep : ∀ rr : Bool, rr ≠ tgt → cond rr σ' ρ' = cond rr σ ρ)
    (hnu : MachPh.IsUniv pol (MachPh.sweepPh r tgt cont par : MachPh V M) = false)
    {c : Config (GamePt B V M A)}
    (hstate : c.state = phasePt (MachPh.sweepPh r tgt cont par) (fun _ => a₀))
    {bhd : Bool} (hhead : c.head = leftPt a₀ bhd)
    (htape : ∀ q : GamePt B V M A, machPosn q → machDom (ctrlArity vars) q →
      c.tape q = tapeOfAssign a₀ hdim ρ σ q)
    (hcont : ∀ c', CtrlCfg a₀ hdim vars ρ' σ'
        (MachPh.rewindTarget (MachPh.rewindPh r tgt cont false)) (fun _ => a₀) c' →
        (𝕄).AltWin true c') :
    (𝕄).AltWin true c := by
  have hlin : IsLinOrd (𝕄).Le := isLinOrd_gameLe
  obtain ⟨d, hchain, hdstate, hdhead, hdtape⟩ :=
    sweep_run (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
      h₀ hkeep c hstate hhead (fun q hq => htape q hq.1 hq.2)
  -- the head is at the right sentinel, which is not the lowest position
  have hnmin : ¬ MinPos (𝕄).Le (𝕄).Posn d.head := by
    intro hm
    rw [hdhead] at hm
    exact leftPt_ne_rightPt a₀ false (hlin.2.2.1 _ _
      ((minPos_leftPt h₀ (carity := ctrlArity vars)).2 _ hm.1) (hm.2 _ (minPos_leftPt h₀).1))
  obtain ⟨h', hsucc⟩ := exists_predPos hlin (hdhead ▸ ⟨trivial, fun _ _ => h₀⟩) hnmin
  have hread : d.tape d.head = markPt a₀ true := by
    rw [hdhead, hdtape (rightPt a₀) ⟨trivial, fun _ _ => h₀⟩, tapeOfAssign_rightPt]
  have hstep := sweep_step_right (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
    (pol := pol) h₀ d (hdstate.trans hstate) hread hsucc
  refine altWin_of_guardedChain (Guard := fun x => x.state = c.state) (fun x hx => ?_) hchain ?_
  · rw [hx, hstate, gameMachine_isUniv hdim _ _ _, hnu]
    exact Bool.false_ne_true
  · refine ATMData.AltWin.ex (fun hcon => ?_) hstep ?_
    · rw [hdstate, hstate, gameMachine_isUniv hdim _ _ _, hnu] at hcon
      exact Bool.false_ne_true hcon
    · refine altWin_rewind (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
        (pol := pol) h₀ rfl hsucc.1 ?_ ?_ (fun q hq hd => hdtape q ⟨hq, hd⟩) hcont
      · intro hc
        exact hsucc.2.2.2.1 (hc.trans hdhead.symm)
      · exact succPos_ne_leftPt (carity := ctrlArity vars) h₀ (one_lt_fam_rightPt (a₀ := a₀))
          (hdhead ▸ hsucc)

/-- **A universal sweep is answered for every assignment of its region.** This
is the one place the simulation runs a walk backwards: `AltWin.all` quantifies
over every step, so the sweep cannot be summarized by its run. -/
theorem altWin_sweep_all (h₀ : IsBot a₀)
    (hu : MachPh.IsUniv pol (MachPh.sweepPh r tgt cont par : MachPh V M) = true)
    {c : Config (GamePt B V M A)}
    (hc : SweptCfg a₀ hdim vars ρ σ tgt (MachPh.sweepPh r tgt cont par) c)
    (hcont : ∀ ρ' σ' : B.Assignment A, (∀ rr : Bool, rr ≠ tgt → cond rr σ' ρ' = cond rr σ ρ) →
      ∀ c', CtrlCfg a₀ hdim vars ρ' σ' (MachPh.rewindTarget (MachPh.rewindPh r tgt cont false))
        (fun _ => a₀) c' → (𝕄).AltWin true c') :
    (𝕄).AltWin true c := by
  classical
  have hlin : IsLinOrd (𝕄).Le := isLinOrd_gameLe
  refine altWin_of_walk hlin (fun d hd => ?_) (fun d hd => ?_)
    (fun d hd => ?_) (fun d d' hd hstep => ?_) c hc
  · obtain ⟨-, -, -, -, hp, hdm, -⟩ := hd
    exact ⟨hp, hdm⟩
  · obtain ⟨-, -, -, hst, -⟩ := hd
    rw [hst, gameMachine_isUniv hdim _ _ _]
    exact hu
  · -- a step is always available
    obtain ⟨ρ', σ', -, hst, hp, hdm, htp⟩ := hd
    have hnmax : ¬ MaxPos (𝕄).Le (𝕄).Posn d.head → True := fun _ => trivial
    rcases posn_cases_tape h₀ (blockArityBound_le_gameDim B V) hp hdm with
      ⟨b, hb⟩ | ⟨r₁, i, ā, hcell⟩ | hr
    · have hnm : ¬ MaxPos (𝕄).Le (𝕄).Posn d.head := by
        intro hm
        rw [hb] at hm
        exact leftPt_ne_rightPt a₀ b (hlin.2.2.1 _ _
          ((maxPos_rightPt h₀ (carity := ctrlArity vars)).2 _ hm.1) (hm.2 _ (maxPos_rightPt h₀).1))
      obtain ⟨h', hsucc⟩ := TMData.exists_succPos' (M := (𝕄).toTMData) hlin ⟨hp, hdm⟩ hnm
      exact ⟨_, sweep_step_left (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
        (pol := pol) h₀ d hst
        (by rw [hb, htp (leftPt a₀ b) (machPosn_leftPt a₀ b) (fun _ _ => h₀),
          tapeOfAssign_leftPt]) hsucc⟩
    · have hnm : ¬ MaxPos (𝕄).Le (𝕄).Posn d.head := by
        intro hm
        rw [hcell] at hm
        exact rightPt_ne_cellPt a₀ r₁ i ā (hlin.2.2.1 _ _
          (hm.2 _ (maxPos_rightPt h₀ (carity := ctrlArity vars)).1)
          ((maxPos_rightPt h₀).2 _ hm.1))
      obtain ⟨h', hsucc⟩ := TMData.exists_succPos' (M := (𝕄).toTMData) hlin ⟨hp, hdm⟩ hnm
      exact ⟨_, sweep_step_cell (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
        (pol := pol) (b := decide (cond r₁ σ' ρ' i ā)) (b' := decide (cond r₁ σ' ρ' i ā))
        h₀ d hst (by rw [hcell, htp _ (machPosn_cellPt a₀ r₁ i ā) (machDom_cellPt a₀ h₀ r₁ i ā),
          tapeOfAssign_cellPt]) (Or.inr rfl) hsucc⟩
    · have hnmin : ¬ MinPos (𝕄).Le (𝕄).Posn d.head := by
        intro hm
        rw [hr] at hm
        exact leftPt_ne_rightPt a₀ false (hlin.2.2.1 _ _
          ((minPos_leftPt h₀ (carity := ctrlArity vars)).2 _ hm.1) (hm.2 _ (minPos_leftPt h₀).1))
      obtain ⟨h', hsucc⟩ := exists_predPos hlin ⟨hp, hdm⟩ hnmin
      exact ⟨_, sweep_step_right (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
        (pol := pol) h₀ d hst
        (by rw [hr, htp (rightPt a₀) (machPosn_rightPt a₀) (fun _ _ => h₀),
          tapeOfAssign_rightPt]) hsucc⟩
  · rcases sweepCfg_cases h₀ hd hstep with ⟨hF, hs⟩ | ⟨hF, hne, hlow⟩
    · exact Or.inl ⟨hF, hs⟩
    · obtain ⟨ρ', σ', hkeep', hst, hp, hdm, htp⟩ := hF
      exact Or.inr (altWin_rewind (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
        (pol := pol) h₀ hst ⟨hp, hdm⟩ hne hlow htp (hcont ρ' σ' hkeep'))

end Sweep

end DescriptiveComplexity
