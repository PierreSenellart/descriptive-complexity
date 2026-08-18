/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameRun

/-!
# Reading a win back: the phases of a question

The backward simulation, for the phases that settle a question. Where the
forward direction *builds* a play, this one *reads one back*, so the two players
change roles: an existential phase now has to be case-analyzed (the play chose
one successor, and we must see what that choice proves) and a universal one may
be instantiated at the successors we care about.

Everything it needs was built as an equivalence for exactly this reason –
`DescriptiveComplexity.ctrlCfg_cases` reads a control step back, and the
`_det`-style rule lemmas read a walk step back.

## The three shapes of a phase

* **existential** (`claim`, `conc`, `seek`, `pre` at an existential variable):
  `DescriptiveComplexity.exists_altWin_succ_of_ex` gives the successor the play
  chose, and the step analysis says what it can be;
* **universal** (`check`, `pre` at a universal variable):
  `DescriptiveComplexity.altWin_succ_of_univ` instantiates the play at any
  successor we can build – which is what the forward direction's step lemmas
  supply;
* **a walk** (`seek`): neither, but an induction on
  `DescriptiveComplexity.ATMData.AltWin` itself, the invariant being the one
  thing the walk is looking for. That the seek's phase does not change along the
  way is what makes it work.

## What a seek proves

`DescriptiveComplexity.SeekArrives` is what a winning seek delivers: a cell
whose symbol answers the test, together with **the transition's tuple** – the
seek's own valuation up to the arity its phase declares, and an address that
`argsOf` reads as the cell's. The tuple is kept because `isTarget` is a
condition on it, and only the program knows that the coordinates outside those
two halves are irrelevant.
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### Reading a win back, one step -/

section Plumbing

variable {U : Type} {N : ATMData U} {start : Bool}

/-- **At a universal configuration every successor wins.** -/
theorem altWin_succ_of_univ {c c' : Config U} (hnacc : ¬ N.Acc c.state)
    (hu : N.IsUniv start c.state) (hc : N.AltWin start c) (hstep : N.toTMData.Step c c') :
    N.AltWin start c' := by
  cases hc with
  | acc h => exact absurd h hnacc
  | ex hnu _ _ => exact absurd hu hnu
  | all _ _ hall => exact hall _ hstep

/-- **At an existential configuration some successor wins**, and it is the one
the play chose. -/
theorem exists_altWin_succ_of_ex {c : Config U} (hnacc : ¬ N.Acc c.state)
    (hnu : ¬ N.IsUniv start c.state) (hc : N.AltWin start c) :
    ∃ c', N.toTMData.Step c c' ∧ N.AltWin start c' := by
  cases hc with
  | acc h => exact absurd h hnacc
  | ex _ hs hw => exact ⟨_, hs, hw⟩
  | all hu _ _ => exact absurd hu hnu

end Plumbing

/-- **The cell a winning seek arrived at**: its symbol answers the test, at a
tuple carrying the phase's valuation and an address `argsOf` reads as the
cell's. -/
def SeekArrives {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] (a₀ : A)
    (isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop)
    (vars : GameQuestion → ℕ) (ph : MachPh V M) (vv : Fin (gameDim B V) → A)
    (tape : GamePt B V M A → GamePt B V M A) (pos : GamePt B V M A) : Prop :=
  ∃ (b rr : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) (w : Fin (gameDim B V) → A),
    pos = cellPt a₀ rr i ā ∧ tape pos = valPt a₀ b rr i ā ∧
      Agree (MachPh.arity vars ph) w vv ∧ argsOf i (addrOf w) = ā ∧
      isTarget ph (SymTag.val b rr i) w

section Back

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] [Finite A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {ρ σ : B.Assignment A}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

omit [Finite A] in
/-- A configuration of the control accepts only in the accepting phase. -/
theorem not_acc_ctrlCfg {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (h : CtrlCfg a₀ hdim vars ρ σ p vv c)
    (hk : p.kind ≠ .acc) : ¬ (𝕄).Acc c.state := by
  rintro ⟨ph, hph, hkind⟩
  rw [h.1] at hph
  exact hk ((Sum.inl.inj (Sum.inr.inj hph)) ▸ hkind)

/-! ### What a winning seek delivers -/

omit [Finite A] in
/-- **What a step of a seek may be**: it stays in the phase with the tape
untouched, or it is the arrival at the cell the seek was looking for. -/
theorem seekCfg_cases (h₀ : IsBot a₀) {ph : MachPh V M} (hk : ph.kind = .seek)
    (hmark : ∀ (b : Bool) (w : Fin (gameDim B V) → A), ¬ isTarget ph (SymTag.mark b) w)
    {vv : Fin (gameDim B V) → A} (hcv : Canon (MachPh.arity vars ph) vv)
    {c c' : Config (GamePt B V M A)} (hstate : c.state = phasePt ph vv)
    (hpos : (𝕄).Posn c.head)
    (htape : ∀ q, (𝕄).Posn q → c.tape q = tapeOfAssign a₀ hdim ρ σ q)
    (hstep : (𝕄).toTMData.Step c c') :
    (c'.state = c.state ∧ (𝕄).Posn c'.head ∧
      ∀ q, (𝕄).Posn q → c'.tape q = tapeOfAssign a₀ hdim ρ σ q) ∨
    (∃ pos, (𝕄).Posn pos ∧
      SeekArrives a₀ isTarget vars ph vv (tapeOfAssign a₀ hdim ρ σ) pos) := by
  classical
  obtain ⟨t, w, hrule, ⟨hsrc, -, hags⟩, hread, ⟨hdst, hcd, had⟩, hwrite, hframe, hmove⟩ :=
    (game_step_iff c c').mp hstep
  have hts : t.src = ph := by
    have := hsrc.symm.trans (congrArg Prod.fst hstate)
    exact Sum.inl.inj (Sum.inr.inj this)
  have hagv : Agree (MachPh.arity vars ph) w vv := by
    rw [hstate] at hags; rw [← hts]; exact hags
  have hold : c.tape c.head = tapeOfAssign a₀ hdim ρ σ c.head := htape _ hpos
  -- every rule of a seek moves right
  have hrt : t.right = true := by
    rcases seek_cases (by rw [hts]; exact hk) hrule with
      ⟨-, -, -, h⟩ | ⟨-, -, h, -, -⟩ | ⟨-, -, h, -⟩ <;> exact h
  have hsucc : SuccPos (𝕄).Le (𝕄).Posn c.head c'.head := by
    rcases hmove with ⟨-, hs⟩ | ⟨hr, -⟩
    · exact hs
    · exact absurd (hrt.symm.trans hr) (by simp)
  -- the same phase and the same tape, whenever the seek carries on
  have hstay : t.dst = ph → t.rd = t.wr →
      (c'.state = c.state ∧ (𝕄).Posn c'.head ∧
        ∀ q, (𝕄).Posn q → c'.tape q = tapeOfAssign a₀ hdim ρ σ q) := by
    intro hd hrw
    refine ⟨?_, hsucc.2.1, fun q hq => ?_⟩
    · have h1 : c'.state.2 = truncTuple a₀ (MachPh.arity vars ph) w :=
        eq_truncTuple h₀ (hd ▸ hcd) (hd ▸ had)
      have h2 : vv = truncTuple a₀ (MachPh.arity vars ph) w := eq_truncTuple h₀ hcv hagv
      rw [hstate]
      exact Prod.ext (by rw [hdst, hd]; rfl) (h1.trans h2.symm)
    · by_cases hqe : q = c.head
      · rw [hqe, hwrite, ← hrw, ← hread, hold]
      · rw [hframe q hqe]; exact htape q hq
  rcases seek_cases (by rw [hts]; exact hk) hrule with
    ⟨hd, hrd, hwr, -⟩ | ⟨hd, hrw, -, -, -⟩ | ⟨-, hrw, -, hhit⟩
  · exact Or.inl (hstay (hd.trans hts) (by rw [hrd, hwr]))
  · exact Or.inl (hstay (hd.trans hts) hrw)
  · -- the arrival: the head must be a cell, and its symbol is the one tested
    refine Or.inr ⟨c.head, hpos, ?_⟩
    rcases posn_cases_tape h₀ (blockArityBound_le_gameDim B V) hpos.1 hpos.2 with
      ⟨b, hb⟩ | ⟨r₁, i, ā, hcell⟩ | hr
    · exfalso
      have : gameSymPt (C := GameCtrlTag B V M) (V := V) a₀ t.rd (addrOf w) = markPt a₀ false := by
        rw [← hread, hold, hb, tapeOfAssign_leftPt]
      cases hrd : t.rd with
      | mark b' => exact hmark b' w (by rw [hts, hrd] at hhit; exact hhit)
      | val b' rr i => exact absurd (by rw [hrd] at this; exact this) (valPt_ne_markPt a₀)
    · have hsym : gameSymPt (C := GameCtrlTag B V M) (V := V) a₀ t.rd (addrOf w) =
          valPt a₀ (decide (cond r₁ σ ρ i ā)) r₁ i ā := by
        rw [← hread, hold, hcell, tapeOfAssign_cellPt]
      cases hrd : t.rd with
      | mark b' =>
        exact absurd (by rw [hrd] at hsym; exact hsym.symm) (valPt_ne_markPt a₀)
      | val b' rr i' =>
        rw [hrd, gameSymPt_val] at hsym
        obtain ⟨rfl, rfl, rfl⟩ := valPt_inj_tag a₀ hsym
        rw [hts, hrd] at hhit
        exact ⟨_, rr, i', ā, w, hcell, by rw [hcell, tapeOfAssign_cellPt], hagv,
          args_eq_of_valPt_eq a₀ hdim hsym, hhit⟩
    · exfalso
      have : gameSymPt (C := GameCtrlTag B V M) (V := V) a₀ t.rd (addrOf w) = markPt a₀ true := by
        rw [← hread, hold, hr, tapeOfAssign_rightPt]
      cases hrd : t.rd with
      | mark b' => exact hmark b' w (by rw [hts, hrd] at hhit; exact hhit)
      | val b' rr i => exact absurd (by rw [hrd] at this; exact this) (valPt_ne_markPt a₀)

omit [Finite A] in
/-- **A winning seek has arrived somewhere.** The phase never changes along the
walk and the tape is never touched, so the induction is on
`DescriptiveComplexity.ATMData.AltWin` itself. -/
theorem seekArrives_of_altWin (h₀ : IsBot a₀) {ph : MachPh V M} (hk : ph.kind = .seek)
    (hmark : ∀ (b : Bool) (w : Fin (gameDim B V) → A), ¬ isTarget ph (SymTag.mark b) w)
    {vv : Fin (gameDim B V) → A} (hcv : Canon (MachPh.arity vars ph) vv) :
    ∀ c : Config (GamePt B V M A), (𝕄).AltWin true c → c.state = phasePt ph vv →
      (𝕄).Posn c.head → (∀ q, (𝕄).Posn q → c.tape q = tapeOfAssign a₀ hdim ρ σ q) →
      ∃ pos, (𝕄).Posn pos ∧
        SeekArrives a₀ isTarget vars ph vv (tapeOfAssign a₀ hdim ρ σ) pos := by
  intro c hw
  induction hw with
  | @acc d hacc =>
    intro hstate _ _
    obtain ⟨p₁, hp₁, hkind⟩ := hacc
    rw [hstate] at hp₁
    rw [← Sum.inl.inj (Sum.inr.inj hp₁), hk] at hkind
    exact absurd hkind (by simp)
  | @ex d d' hnu hstep _ ih =>
    intro hstate hpos htape
    rcases seekCfg_cases h₀ hk hmark hcv hstate hpos htape hstep with
      ⟨hs, hp, ht⟩ | harr
    · exact ih (hs.trans hstate) hp ht
    · exact harr
  | @all d hu hex _ _ =>
    intro hstate _ _
    rw [hstate, gameMachine_isUniv hdim _ _ _, MachPh.isUniv_seek pol hk] at hu
    exact absurd hu (by simp)

/-! ### What a step of a rewind may be -/

omit [Finite A] in
/-- **A rewind either walks on or hands over**, and either way the tape is
untouched – both its rules write back what they read. The handover lands on the
lowest position, which is what the two sentinels being adjacent buys. -/
theorem rewindCfg_cases (h₀ : IsBot a₀) {r tgt : Bool} {cont : SweepCont} {par : Bool}
    {c c' : Config (GamePt B V M A)}
    (hstate : c.state = phasePt (MachPh.rewindPh r tgt cont par) (fun _ => a₀))
    (hpos : (𝕄).Posn c.head)
    (htape : ∀ q, (𝕄).Posn q → c.tape q = tapeOfAssign a₀ hdim ρ σ q)
    (hstep : (𝕄).toTMData.Step c c') :
    ((c'.state = c.state ∨
        (c'.state = phasePt (MachPh.rewindTarget (MachPh.rewindPh r tgt cont par))
          (fun _ => a₀) ∧ c'.head = leftPt a₀ false)) ∧
      (𝕄).Posn c'.head ∧ ∀ q, (𝕄).Posn q → c'.tape q = tapeOfAssign a₀ hdim ρ σ q) := by
  obtain ⟨t, w, hrule, ⟨hsrc, -, -⟩, hread, ⟨hdst, hcd, -⟩, hwrite, hframe, hmove⟩ :=
    (game_step_iff c c').mp hstep
  have hts : t.src = MachPh.rewindPh r tgt cont par := by
    have := hsrc.symm.trans (congrArg Prod.fst hstate)
    exact Sum.inl.inj (Sum.inr.inj this)
  have hconst : ∀ x : Fin (gameDim B V) → A, Canon 0 x → x = fun _ => a₀ :=
    fun x hx => funext fun j => le_antisymm (hx j (Nat.zero_le _) a₀) (h₀ _)
  have hrw : t.rd = t.wr := rewind_writes_back (by rw [hts]; rfl) hrule
  have hrt : t.right = false := by
    rcases rewind_cases (by rw [hts]; rfl) hrule with ⟨-, -, h, -⟩ | ⟨-, -, -, h⟩ <;> exact h
  have hs : SuccPos (𝕄).Le (𝕄).Posn c'.head c.head := by
    rcases hmove with ⟨hr, -⟩ | ⟨-, hs⟩
    · exact absurd (hrt.symm.trans hr) (by simp)
    · exact hs
  -- the tape is written back
  have htape' : ∀ q, (𝕄).Posn q → c'.tape q = tapeOfAssign a₀ hdim ρ σ q := by
    intro q hq
    by_cases hqe : q = c.head
    · rw [hqe, hwrite, ← hrw, ← hread]
      exact htape _ hpos
    · rw [hframe q hqe]; exact htape q hq
  refine ⟨?_, hs.1, htape'⟩
  rcases rewind_cases (by rw [hts]; rfl) hrule with ⟨hd, -, -, -⟩ | ⟨hd, hrd, -, -⟩
  · -- walking on: the same phase, at the same (constant) valuation
    refine Or.inl ?_
    rw [hstate]
    exact Prod.ext (by rw [hdst, hd, hts]; rfl)
      (hconst _ (by rw [hd, hts] at hcd; exact hcd))
  · -- handing over: the head reads the left mark, so it is on the second sentinel
    refine Or.inr ⟨Prod.ext (by rw [hdst, hd, hts]; rfl)
      (hconst _ (by rw [hd, hts, MachPh.arity_rewindTarget] at hcd; exact hcd)), ?_⟩
    have hsym : c.tape c.head = markPt a₀ false := by rw [hread, hrd]; rfl
    rcases posn_cases_tape h₀ (blockArityBound_le_gameDim B V) hpos.1 hpos.2 with
      ⟨b, hb⟩ | ⟨r₁, i, ā, hcell⟩ | hr
    · cases b with
      | false =>
        have hle : (𝕄).Le c.head c'.head := by
          rw [hb]
          exact (minPos_leftPt h₀ (carity := ctrlArity vars)).2 _ hs.1
        exact absurd (isLinOrd_gameLe.2.2.1 _ _ hs.2.2.1 hle) hs.2.2.2.1
      | true =>
        exact succPos_left_unique isLinOrd_gameLe (hb ▸ hs)
          (succPos_leftPt h₀ (carity := ctrlArity vars))
    · exact absurd ((htape _ hpos).symm.trans hsym) (by
        rw [hcell, tapeOfAssign_cellPt]; exact valPt_ne_markPt a₀)
    · exact absurd ((htape _ hpos).symm.trans hsym) (by
        rw [hr, tapeOfAssign_rightPt]; exact markPt_ne_markPt a₀ (by simp))

/-! ### A phase with one successor -/

omit [Finite A] in
/-- **A phase with exactly one successor hands its win on**, whichever player
owns it: the universal one because every successor wins, the existential one
because the successor it chose is that one. The valuation is carried over
because the two phases declare the same coordinates. -/
theorem exists_altWin_succ_uniq (h₀ : IsBot a₀) {p p' : MachPh V M}
    {vv : Fin (gameDim B V) → A} {c : Config (GamePt B V M A)}
    (hsw : p.kind ≠ .sweep) (hrw : p.kind ≠ .rewind) (hsk : p.kind ≠ .seek)
    (hnc : p.kind ≠ .conc) (hna : p.kind ≠ .acc)
    (harity : MachPh.arity vars p' = MachPh.arity vars p)
    (hcs : MachPh.CtrlStep vars natoms p p')
    (hcsu : ∀ p'', MachPh.CtrlStep vars natoms p p'' → p'' = p')
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) (hw : (𝕄).AltWin true c) :
    ∃ c', CtrlCfg a₀ hdim vars ρ σ p' vv c' ∧ (𝕄).AltWin true c' := by
  have hvv : truncTuple a₀ (MachPh.arity vars p') vv = vv := by
    rw [harity]
    exact (eq_truncTuple h₀ h.2.1 (fun _ _ => rfl)).symm
  by_cases hu : MachPh.IsUniv pol p = true
  · obtain ⟨c', hstep, h'⟩ := ctrlCfg_step (natoms := natoms) (concOk := concOk)
      (isTarget := isTarget) (pol := pol) (w := vv) h₀ hcs
      (fun hc => absurd hc hnc) (fun _ _ => rfl) h
    exact ⟨c', hvv ▸ h', altWin_succ_of_univ (not_acc_ctrlCfg h hna)
      ((isUniv_ctrlCfg (pol := pol) h).mpr hu) hw hstep⟩
  · obtain ⟨c', hstep, hw'⟩ := exists_altWin_succ_of_ex (not_acc_ctrlCfg h hna)
      (fun hcon => hu ((isUniv_ctrlCfg (pol := pol) h).mp hcon)) hw
    obtain ⟨p'', w, hcs'', -, hag, h''⟩ :=
      ctrlCfg_cases (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
        h₀ hsw hrw hsk h hstep
    obtain rfl := hcsu p'' hcs''
    refine ⟨c', ?_, hw'⟩
    rwa [harity, ← eq_truncTuple h₀ h.2.1 hag] at h''

/-! ### The concluding phase, the challenge round, the claim -/

omit [Finite A] in
/-- **A winning concluding phase has its guard satisfied** – which is the only
thing it can be doing, since a false guard leaves it with no transition. -/
theorem concOk_of_altWin (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hk : p.kind = .conc)
    (hcong : ∀ w, Agree (MachPh.arity vars p) w vv → concOk p w → concOk p vv)
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) (hw : (𝕄).AltWin true c) : concOk p vv := by
  obtain ⟨c', hstep, -⟩ := exists_altWin_succ_of_ex (not_acc_ctrlCfg h (by simp [hk]))
    (fun hcon => by
      rw [isUniv_ctrlCfg (pol := pol) h, MachPh.isUniv_conc pol hk] at hcon
      exact Bool.false_ne_true hcon) hw
  obtain ⟨p', w, -, hconc, hag, -⟩ :=
    ctrlCfg_cases (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
      h₀ (by simp [hk]) (by simp [hk]) (by simp [hk]) h hstep
  exact hcong w hag (hconc hk)

omit [Finite A] in
/-- **A winning challenge round has correct claims and a satisfied guard.** The
phase is universal, so the play answers *every* challenge and the concluding
branch as well; each is a successor we build. -/
theorem check_of_altWin (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hk : p.kind = .check)
    (hmark : ∀ (k : Fin (M + 1)) (b : Bool) (w : Fin (gameDim B V) → A),
      ¬ isTarget (MachPh.seekPh p.q p.r p.claims k (!p.par)) (SymTag.mark b) w)
    (hcong : ∀ w, Agree (vars p.q) w vv →
      concOk (MachPh.concPh p.q p.r p.claims (!p.par)) w →
        concOk (MachPh.concPh p.q p.r p.claims (!p.par)) vv)
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) (hw : (𝕄).AltWin true c) :
    (∀ k : Fin (M + 1), (k : ℕ) < natoms p.q → ∃ pos, (𝕄).Posn pos ∧
        SeekArrives a₀ isTarget vars (MachPh.seekPh p.q p.r p.claims k (!p.par)) vv
          (tapeOfAssign a₀ hdim ρ σ) pos) ∧
      concOk (MachPh.concPh p.q p.r p.claims (!p.par)) vv := by
  have hac : MachPh.arity vars p = vars p.q := MachPh.arity_of_matrix vars (Or.inr (Or.inl hk))
  have hnacc := not_acc_ctrlCfg (pol := pol) (natoms := natoms) (concOk := concOk)
    (isTarget := isTarget) h (by simp [hk])
  have hu : (𝕄).IsUniv true c.state :=
    (isUniv_ctrlCfg (pol := pol) h).mpr (MachPh.isUniv_check pol hk)
  -- every successor wins, at the same valuation
  have hsucc : ∀ p' : MachPh V M, MachPh.CtrlStep vars natoms p p' →
      MachPh.arity vars p' = vars p.q →
      ∃ c', CtrlCfg a₀ hdim vars ρ σ p' vv c' ∧ (𝕄).AltWin true c' := by
    intro p' hcs harity
    obtain ⟨c', hstep, h'⟩ := ctrlCfg_step (natoms := natoms) (concOk := concOk)
      (isTarget := isTarget) (pol := pol) (w := vv) h₀ hcs
      (fun hc => absurd (hk.symm.trans hc) (by simp)) (fun _ _ => rfl) h
    refine ⟨c', ?_, altWin_succ_of_univ hnacc hu hw hstep⟩
    rwa [harity, ← hac, ← eq_truncTuple h₀ h.2.1 (fun _ _ => rfl)] at h'
  constructor
  · intro k hkk
    obtain ⟨c', h', hw'⟩ := hsucc _ (by
      rw [MachPh.CtrlStep, hk]
      exact Or.inl ⟨k, hkk, rfl⟩) (MachPh.arity_seekPh vars _ _ _ _ _)
    have hcvq : Canon (vars p.q) vv := hac ▸ h.2.1
    exact seekArrives_of_altWin h₀ rfl (hmark k) hcvq c' hw' h'.1
      ⟨by rw [h'.2.2.1]; exact trivial, by rw [h'.2.2.1]; exact fun _ _ => h₀⟩
      (fun qq hq => h'.2.2.2 qq hq.1 hq.2)
  · obtain ⟨c', h', hw'⟩ := hsucc _ (by
      rw [MachPh.CtrlStep, hk]
      exact Or.inr rfl) (MachPh.arity_concPh vars _ _ _ _)
    exact concOk_of_altWin (natoms := natoms) (pol := pol) (isTarget := isTarget) h₀ rfl hcong
      h' hw'

omit [Finite A] in
/-- **A winning claim phase has claimed something that survives the round.** -/
theorem claim_of_altWin (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hk : p.kind = .claim)
    (hmark : ∀ (b' : Fin M → Bool) (k : Fin (M + 1)) (b : Bool) (w : Fin (gameDim B V) → A),
      ¬ isTarget (MachPh.seekPh p.q p.r b' k p.par) (SymTag.mark b) w)
    (hcong : ∀ (b' : Fin M → Bool) w, Agree (vars p.q) w vv →
      concOk (MachPh.concPh p.q p.r b' p.par) w → concOk (MachPh.concPh p.q p.r b' p.par) vv)
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) (hw : (𝕄).AltWin true c) :
    ∃ b : Fin M → Bool,
      (∀ k : Fin (M + 1), (k : ℕ) < natoms p.q → ∃ pos, (𝕄).Posn pos ∧
        SeekArrives a₀ isTarget vars (MachPh.seekPh p.q p.r b k p.par) vv
          (tapeOfAssign a₀ hdim ρ σ) pos) ∧
      concOk (MachPh.concPh p.q p.r b p.par) vv := by
  have hac : MachPh.arity vars p = vars p.q := MachPh.arity_of_matrix vars (Or.inl hk)
  obtain ⟨c', hstep, hw'⟩ := exists_altWin_succ_of_ex (not_acc_ctrlCfg h (by simp [hk]))
    (fun hcon => by
      rw [isUniv_ctrlCfg (pol := pol) h, MachPh.isUniv_claim pol hk] at hcon
      exact Bool.false_ne_true hcon) hw
  obtain ⟨p', w, hcs, -, hag, h'⟩ :=
    ctrlCfg_cases (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
      h₀ (by simp [hk]) (by simp [hk]) (by simp [hk]) h hstep
  rw [MachPh.CtrlStep, hk] at hcs
  obtain ⟨b, rfl⟩ := hcs
  rw [show MachPh.arity vars (MachPh.checkPh p.q p.r b (!p.par)) = MachPh.arity vars p from
    hac ▸ rfl, ← eq_truncTuple h₀ h.2.1 hag] at h'
  refine ⟨b, ?_⟩
  have hres := check_of_altWin (natoms := natoms) (pol := pol) h₀
    (p := MachPh.checkPh p.q p.r b (!p.par)) rfl
    (fun k b'' w => by
      simp only [MachPh.checkPh, Bool.not_not]
      exact hmark b k b'' w)
    (fun w hag hc => by
      simp only [MachPh.checkPh, Bool.not_not] at hag hc ⊢
      exact hcong b w hag hc) h' hw'
  simpa only [MachPh.checkPh, Bool.not_not] using hres

/-! ### The prefix, read back -/

omit [Finite A] in
/-- **A winning prefix phase proves its prefix.** The mirror of
`DescriptiveComplexity.altWin_pre`, with the players' roles exchanged: at an
existential variable the play chose a value and we read it off, at a universal
one we instantiate the play at every value – each being a successor the forward
direction knows how to build. -/
theorem pre_of_altWin (h₀ : IsBot a₀) (hV : ∀ q, vars q ≤ V) {q : GameQuestion}
    {P : (Fin (vars q) → A) → Prop} {r : Bool}
    (hclaim : ∀ (par : Bool) (vv : Fin (gameDim B V) → A) (c : Config (GamePt B V M A)),
      CtrlCfg a₀ hdim vars ρ σ (MachPh.claimPh q r par) vv c → (𝕄).AltWin true c →
        P (qval hV q vv)) :
    ∀ (fuel j : ℕ), vars q - j ≤ fuel → j ≤ vars q → ∀ (par : Bool) (jj : Fin (V + 1)),
      (jj : ℕ) = j → ∀ (vv : Fin (gameDim B V) → A) (c : Config (GamePt B V M A)),
        CtrlCfg a₀ hdim vars ρ σ (MachPh.prePh q r jj par) vv c → (𝕄).AltWin true c →
          altQuantFrom (pol q) P j (qval hV q vv) := by
  have hqD : vars q ≤ gameDim B V := (hV q).trans (le_gameDim B V)
  -- the handover to the claim, at either polarity
  have hlast : ∀ (par : Bool) (jj : Fin (V + 1)), (jj : ℕ) = vars q →
      ∀ (vv : Fin (gameDim B V) → A) (c : Config (GamePt B V M A)),
        CtrlCfg a₀ hdim vars ρ σ (MachPh.prePh q r jj par) vv c → (𝕄).AltWin true c →
          P (qval hV q vv) := by
    intro par jj hjj vv c h hw
    have hcs := MachPh.ctrlStep_prePh_last (M := M) vars natoms q r jj par (by rw [hjj]; omega)
    obtain ⟨c', h', hw'⟩ := exists_altWin_succ_uniq (natoms := natoms) (concOk := concOk)
      (isTarget := isTarget) (pol := pol) h₀ (by simp [MachPh.prePh]) (by simp [MachPh.prePh])
      (by simp [MachPh.prePh]) (by simp [MachPh.prePh]) (by simp [MachPh.prePh])
      (by rw [MachPh.arity_claimPh, MachPh.arity_prePh, hjj, min_self])
      ((hcs _).mpr rfl) (fun p'' hp'' => (hcs p'').mp hp'') h hw
    exact hclaim _ vv c' h' hw'
  intro fuel
  induction fuel with
  | zero =>
    intro j hf hj par jj hjj vv c h hw
    have hje : j = vars q := by omega
    rw [hje, altQuantFrom_last]
    exact hlast par jj (hjj.trans hje) vv c h hw
  | succ fuel ih =>
    intro j hf hj par jj hjj vv c h hw
    by_cases hjlt : j < vars q
    · have hjD : j < gameDim B V := lt_of_lt_of_le hjlt hqD
      have harity : MachPh.arity vars (MachPh.prePh q r jj par : MachPh V M) = j := by
        rw [MachPh.arity_prePh, hjj, min_eq_left hjlt.le]
      have hjV : j + 1 < V + 1 := by have := hV q; omega
      have hcs : ∀ p' : MachPh V M, MachPh.CtrlStep vars natoms (MachPh.prePh q r jj par) p' ↔
          p' = MachPh.prePh q r ⟨j + 1, hjV⟩ (!par) := by
        intro p'
        rw [MachPh.ctrlStep_prePh (M := M) vars natoms q r jj par (by rw [hjj]; exact hjlt)]
        constructor
        · rintro ⟨j'', hj'', rfl⟩
          rw [show j'' = (⟨j + 1, hjV⟩ : Fin (V + 1)) from Fin.ext (by rw [hj'', hjj])]
        · rintro rfl
          exact ⟨⟨j + 1, hjV⟩, by rw [hjj], rfl⟩
      have harity' : MachPh.arity vars
          (MachPh.prePh q r ⟨j + 1, hjV⟩ (!par) : MachPh V M) = j + 1 := by
        rw [MachPh.arity_prePh]
        change min (j + 1) (vars q) = j + 1
        exact min_eq_left (by omega)
      rcases hpol : pol q j with _ | _
      · -- universal: the play answers every value, so instantiate it at each
        rw [altQuantFrom_all hjlt hpol]
        intro a
        have hag : Agree (MachPh.arity vars (MachPh.prePh q r jj par : MachPh V M))
            (Function.update vv ⟨j, hjD⟩ a) vv := by
          intro l hl
          rw [harity] at hl
          exact (Function.update_of_ne
            (fun hc => absurd (congrArg Fin.val hc : (l : ℕ) = j) (by omega)) _ _).symm
        obtain ⟨c', hstep, h'⟩ := ctrlCfg_step (natoms := natoms) (concOk := concOk)
          (isTarget := isTarget) (pol := pol) (w := Function.update vv ⟨j, hjD⟩ a) h₀
          ((hcs _).mpr rfl) (fun hc => absurd hc (by simp [MachPh.prePh])) hag h
        have hw' := altWin_succ_of_univ (not_acc_ctrlCfg h (by simp [MachPh.prePh]))
          ((isUniv_ctrlCfg (pol := pol) h).mpr
            (by rw [MachPh.isUniv_pre pol rfl, MachPh.prePh, hjj, hpol]; rfl)) hw hstep
        rw [harity', truncTuple_succ h₀ hjD (harity ▸ h.2.1) (harity ▸ hag)] at h'
        have hres := ih (j + 1) (by omega) (by omega) (!par) ⟨j + 1, hjV⟩ rfl _ c' h' hw'
        rwa [qval_update hV q hjD hjlt, Function.update_self] at hres
      · -- existential: the play chose a value, and it is the witness
        rw [altQuantFrom_ex hjlt hpol]
        obtain ⟨c', hstep, hw'⟩ := exists_altWin_succ_of_ex
          (not_acc_ctrlCfg h (by simp [MachPh.prePh]))
          (fun hcon => by
            rw [isUniv_ctrlCfg (pol := pol) h, MachPh.isUniv_pre pol rfl, MachPh.prePh, hjj,
              hpol] at hcon
            exact Bool.false_ne_true hcon) hw
        obtain ⟨p'', w, hcs'', -, hag, h'⟩ :=
          ctrlCfg_cases (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
            h₀ (by simp [MachPh.prePh]) (by simp [MachPh.prePh]) (by simp [MachPh.prePh]) h hstep
        obtain rfl := (hcs p'').mp hcs''
        rw [harity', truncTuple_succ h₀ hjD (harity ▸ h.2.1) (harity ▸ hag)] at h'
        refine ⟨w ⟨j, hjD⟩, ?_⟩
        have hres := ih (j + 1) (by omega) (by omega) (!par) ⟨j + 1, hjV⟩ rfl _ c' h' hw'
        rwa [qval_update hV q hjD hjlt] at hres
    · have hje : j = vars q := by omega
      rw [hje, altQuantFrom_last]
      exact hlast par jj (hjj.trans hje) vv c h hw

end Back

end DescriptiveComplexity
