/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltPrefix

/-!
# The rounds, one block at a time

The induction that turns the machine into the quantifier prefix. Round `m`
starts at `DescriptiveComplexity.AltQbf.AtRound`: the head at the first cell, the tape
holding what the blocks below `m` have written, and the state the entry of
sweep `m` – or, when every block has played, the entry of the check phase.

Each round is answered by whichever player owns its block, and the four corners
were built in `AltGuess`: an existential round picks an assignment
(`altAcc_passes_up`) and any accepting run of it hands one over
(`exit_of_altAcc`); a universal round survives all of them
(`altAcc_of_inSweepR`) and is followed along the run of any given one
(`altAcc_passes_down`). The base case is the check phase, decided both ways in
`AltVerdict`.

The read-off returns *some* assignment, not a chosen one, which is what an
existential round wants and a universal one does not. So a universal round does
not follow the read-off at all: it names the configuration it wants to hand
over (`DescriptiveComplexity.AltQbf.exists_atRound`) and appeals to the fact that
every successor of a universal configuration accepts.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Rounds

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### Where the machine stands between rounds -/

variable (cnf : Bool) in
/-- **The entry of round `m`**: the head at the first cell, the tape holding
what the blocks below `m` wrote, and the state the entry of sweep `m` – or,
once every block has played, the entry of the check phase, or acceptance
outright when there is nothing to check. -/
def AtRound (m : ℕ) (νs : Fin k → A → Prop) (c : Config (AltV k A)) : Prop :=
  c.head = posCell qbotA ∧ c.tape = tapeAfter νs m ∧
    ((m < k ∧ ∃ j : Fin (k + 1), (j : ℕ) = m ∧ c.state = stG j true) ∨
      (m = k ∧ ((∃ c₀ : A, QbfMinCl k c₀ ∧ c.state = stChk false true c₀) ∨
        ((∀ e : A, ¬QbfCl k e) ∧ cnf = true ∧ c.state = stAcc))))

/-- **A round hands over to the next one.** -/
theorem atRound_of_afterSweep {cnf : Bool} {i : Fin k} {ρ : Fin k → A → Prop}
    {c : Config (AltV k A)} (h : AfterSweep cnf i ρ c) : AtRound cnf ((i : ℕ) + 1) ρ c := by
  obtain ⟨hhead, htape, hcase⟩ := h
  refine ⟨hhead, htape, ?_⟩
  rcases hcase with ⟨hlt, hst⟩ | ⟨hlast, hrest⟩
  · exact Or.inl ⟨hlt, i.succ, Fin.val_succ i, hst⟩
  · exact Or.inr ⟨hlast, hrest⟩

/-- Before the last block has played, the entry of a round is the entry of its
sweep. -/
theorem eq_confSweep_of_atRound {cnf : Bool} {m : ℕ} {νs : Fin k → A → Prop}
    {c : Config (AltV k A)} (i : Fin k) (hi : (i : ℕ) = m) (h : AtRound cnf m νs c) :
    c = confSweep νs i.castSucc (posCell qbotA) := by
  obtain ⟨hhead, htape, hcase⟩ := h
  rcases hcase with ⟨-, j, hj, hst⟩ | ⟨hlast, -⟩
  · refine Config.ext ?_ hhead ?_
    · rw [hst]
      exact congrArg (fun t => stG t true) (Fin.ext (by rw [hj, ← hi, Fin.val_castSucc]))
    · rw [htape, tape_confSweep_bot νs i.castSucc, Fin.val_castSucc, hi]
  · exact absurd (hlast ▸ hi ▸ i.isLt) (lt_irrefl _)

/-- **The entry of a round exists.** Before the last block has played it is
the entry of the next sweep; after it, the check phase starts at the lowest
clause, or the machine accepts outright when there is nothing to check. -/
theorem exists_atRound {cnf : Bool} {m : ℕ} (hm : m ≤ k) (νs : Fin k → A → Prop)
    (hover : m = k → CanHandOver k A cnf) : ∃ c : Config (AltV k A), AtRound cnf m νs c := by
  rcases Nat.lt_or_ge m k with hlt | hge
  · exact ⟨confSweep νs ⟨m, by omega⟩ (posCell qbotA), rfl,
      tape_confSweep_bot νs ⟨m, by omega⟩, Or.inl ⟨hlt, ⟨m, by omega⟩, rfl, rfl⟩⟩
  · have hmk : m = k := by omega
    rcases hover hmk with ⟨c₀, hmin⟩ | ⟨hcnf, hno⟩
    · exact ⟨⟨stChk false true c₀, posCell qbotA, tapeAfter νs m⟩, rfl, rfl,
        Or.inr ⟨hmk, Or.inl ⟨c₀, hmin, rfl⟩⟩⟩
    · exact ⟨⟨stAcc, posCell qbotA, tapeAfter νs m⟩, rfl, rfl,
        Or.inr ⟨hmk, Or.inr ⟨hno, hcnf, rfl⟩⟩⟩

/-- **The handover step.** Whatever the entry of the next round is, the machine
reaches it from the left marker in one step. -/
theorem step_handover {cnf : Bool} {i : Fin k} {ρ : Fin k → A → Prop} {d : Config (AltV k A)}
    (h : AtRound cnf ((i : ℕ) + 1) ρ d) :
    (altMachine k A cnf).Step (confBack ρ i.castSucc posStart) d := by
  obtain ⟨hhead, htape, hcase⟩ := h
  have hik : ((i.castSucc : Fin (k + 1)) : ℕ) = (i : ℕ) := Fin.val_castSucc i
  rcases hcase with ⟨hlt, j, hj, hst⟩ | ⟨hlast, hrest⟩
  · have hd : d = confSweep ρ (i.castSucc + 1) (posCell qbotA) := by
      have hval : ((i.castSucc + 1 : Fin (k + 1)) : ℕ) = (i : ℕ) + 1 := by
        rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i), hik]
      refine Config.ext ?_ hhead ?_
      · rw [hst]
        exact congrArg (fun t => stG t true) (Fin.ext (by rw [hj, hval]))
      · rw [htape, tape_confSweep_bot ρ (i.castSucc + 1), hval]
    rw [hd]
    exact step_next (by rw [hik]; exact hlt)
  · have hlast' : ((i.castSucc : Fin (k + 1)) : ℕ) + 1 = k := by rw [hik]; exact hlast
    rcases hrest with ⟨c₀, hmin, hst⟩ | ⟨hno, hcnf, hst⟩
    · have hd : d = ⟨stChk false true c₀, posCell qbotA, tapeAfter ρ k⟩ :=
        Config.ext hst hhead (by rw [htape, hlast])
      rw [hd]
      exact step_toChk hlast' hmin
    · have hd : d = ⟨stAcc, posCell qbotA, tapeAfter ρ k⟩ :=
        Config.ext hst hhead (by rw [htape, hlast])
      rw [hd]
      exact step_toAcc hlast' hcnf hno

omit [Nonempty A] in
/-- **A satisfied matrix leaves the last sweep somewhere to go.** -/
theorem canHandOver_of_qbfMatrix {cnf : Bool} {ρ : Fin k → A → Prop} (hmat : QbfMatrix cnf ρ) :
    CanHandOver k A cnf := by
  classical
  by_cases hcl : ∃ e : A, QbfCl k e
  · obtain ⟨c₀, hc₀, hmin⟩ := Set.exists_min_image {e : A | QbfCl k e} id (Set.toFinite _) hcl
    exact Or.inl ⟨c₀, hc₀, fun e he => hmin e he⟩
  · have hno : ∀ e : A, ¬QbfCl k e := not_exists.mp hcl
    refine Or.inr ⟨?_, hno⟩
    cases cnf with
    | true => rfl
    | false =>
      obtain ⟨e, he, -⟩ := hmat
      exact absurd he (hno e)

/-- Replacing a block's assignment does not change the tape its own sweep
starts from. -/
theorem confSweep_update_self {i : Fin k} {ν : A → Prop} (νs : Fin k → A → Prop) :
    confSweep (Function.update νs i ν) i.castSucc (posCell qbotA) =
      confSweep νs i.castSucc (posCell qbotA) := by
  refine Config.ext rfl rfl ?_
  rw [tape_confSweep_bot, tape_confSweep_bot, Fin.val_castSucc]
  exact funext fun p => tapeAfter_congr_at (by rw [valAfter_update_le (le_refl _)])

/-! ### The budget

A round costs a sweep, and a universal round costs a walk up and back down the
tape once for each of the two passes, whatever the play. -/

variable (k A) in
/-- What one round costs: exactly the sweep it plays, whichever player owns
it. -/
noncomputable def roundStep : ℕ := sweepLen k A

variable (k A) in
/-- What the last `r` rounds cost, the check phase included. -/
noncomputable def roundBound : ℕ → ℕ
  | 0 => chkLen k A
  | r + 1 => roundBound r + roundStep k A

/-! ### The induction over rounds -/

/-- **The machine plays the quantifier prefix.** At the entry of round `m`, the
machine accepts exactly when the `r` blocks still to play can settle the
matrix – the round's own block quantified at the polarity its index gives it.

Both directions of both polarities are one line each, on top of the four
corners of `AltGuess`: the existential player picks and climbs, the universal
player is followed down one play at a time and survives all of them. -/
theorem rounds {cnf start : Bool} :
    ∀ (r m : ℕ), m + r = k → ∀ (νs : Fin k → A → Prop) (c : Config (AltV k A)),
      AtRound cnf m νs c →
        (∀ n : ℕ, (altMachine k A cnf).AltAcc start n c →
          AltTail (QbfMatrix cnf) r m νs (blockPol start m)) ∧
        (AltTail (QbfMatrix cnf) r m νs (blockPol start m) →
          ∀ n : ℕ, roundBound k A r ≤ n → (altMachine k A cnf).AltAcc start n c) := by
  intro r
  induction r with
  | zero =>
    -- every block has played: the check phase decides
    intro m hmr νs c hround
    obtain ⟨hhead, htape, hcase⟩ := hround
    rcases hcase with ⟨hlt, -⟩ | ⟨-, hrest⟩
    · exact absurd hlt (by omega)
    rcases hrest with ⟨c₀, hmin, hst⟩ | ⟨hno, hcnf, hst⟩
    · have hc : c = confChkR cnf νs c₀ (posCell qbotA) := by
        refine Config.ext ?_ hhead ?_
        · rw [hst]
          change stChk false true c₀ = stChk (chkFlagR cnf νs c₀ (posCell qbotA)) true c₀
          rw [chkFlagR_bot]
        · rw [htape, show m = k by omega]
          rfl
      refine ⟨fun n hacc => ?_, fun hmat n hn => ?_⟩
      · rw [hc] at hacc
        exact qbfMatrix_of_altAcc hmin hacc
      · rw [hc]
        exact altAcc_of_qbfMatrix hmin hmat hn
    · refine ⟨fun n hacc => ?_, fun _ n _ => ?_⟩
      · subst hcnf
        exact fun e he => absurd he (hno e)
      · exact ATMData.altAcc_of_acc (show (altMachine k A cnf).Acc c.state by rw [hst]; rfl)
  | succ r ih =>
    intro m hmr νs c hround
    have hlt : m < k := by omega
    have hval : ((⟨m, hlt⟩ : Fin k) : ℕ) = m := rfl
    have hci : c = confSweep νs (Fin.castSucc ⟨m, hlt⟩) (posCell qbotA) :=
      eq_confSweep_of_atRound ⟨m, hlt⟩ rfl hround
    have hpolsucc : blockPol start (m + 1) = !blockPol start m := blockPol_succ start m
    rw [altTail_succ (QbfMatrix cnf) hlt νs (blockPol start m)]
    cases hpol : blockPol start m with
    | true =>
      -- an existential round: the machine picks the block's assignment
      refine ⟨fun n hacc => ?_, fun htail n hn => ?_⟩
      · rw [hci] at hacc
        obtain ⟨ν', d, m', -, -, hafter, haccd⟩ :=
          exit_of_altAcc n _ (Or.inl (inSweepR_start ⟨m, hlt⟩ νs)) hacc
        refine ⟨ν', ?_⟩
        have hres := (ih (m + 1) (by omega) (Function.update νs ⟨m, hlt⟩ ν') d
          (atRound_of_afterSweep hafter)).1 m' haccd
        rwa [hpolsucc, hpol] at hres
      · obtain ⟨ν, htail⟩ := htail
        have hmat : m + 1 = k → QbfMatrix cnf (Function.update νs ⟨m, hlt⟩ ν) := by
          intro hmk
          have hr0 : r = 0 := by omega
          subst hr0
          exact htail
        obtain ⟨d, hd⟩ := exists_atRound (by omega) (Function.update νs ⟨m, hlt⟩ ν)
          (fun hmk => canHandOver_of_qbfMatrix (hmat hmk))
        have haccd := (ih (m + 1) (by omega) (Function.update νs ⟨m, hlt⟩ ν) d hd).2
          (by rwa [hpolsucc, hpol]) (n - roundStep k A) (by
            simp only [roundBound] at hn
            omega)
        have hnu : ¬(altMachine k A cnf).IsUniv start
            (confBack (Function.update νs ⟨m, hlt⟩ ν) (Fin.castSucc ⟨m, hlt⟩) posStart).state := by
          intro hu
          exact absurd (isUniv_stG.mp hu) (by rw [hpol]; exact Bool.noConfusion)
        have hup := altAcc_passes_up (i := ⟨m, hlt⟩) (by rw [hpol])
          (altAcc_up_step hnu (step_handover hd) haccd)
        rw [confSweep_update_self] at hup
        rw [hci]
        refine ATMData.altAcc_mono ?_ hup
        have hsl : sweepLen k A = passLen k A + 1 := sweepLen_eq_passLen
        simp only [roundBound, roundStep] at hn ⊢
        omega
    | false =>
      -- a universal round: every assignment of the block must settle the matrix
      refine ⟨fun n hacc => ?_, fun htail n hn => ?_⟩
      · intro ν
        rw [hci, ← confSweep_update_self (i := ⟨m, hlt⟩) (ν := ν) νs] at hacc
        obtain ⟨-, haccBack⟩ := altAcc_passes_down (i := ⟨m, hlt⟩) (by rw [hpol]) hacc
        -- the machine can still move, so the handover is available
        have hinvL : InSweepL ⟨m, hlt⟩ νs
            (confBack (Function.update νs ⟨m, hlt⟩ ν) (Fin.castSucc ⟨m, hlt⟩) posStart) :=
          ⟨fun x => QbfBlk ⟨m, hlt⟩ x ∧ ν x, fun x hx => hx.1, rfl, altPosn_posStart,
            posStart_le_posCell _, funext fun p =>
              tapeAfter_congr_at (Bool.eq_iff_iff.mpr (by
                rw [Fin.val_castSucc, valAfter_update_succ, valAfter_update_succ]
                exact or_congr_right ⟨fun h => ⟨h.1, h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩))⟩
        obtain ⟨d₀, -, hstep₀, -⟩ := exists_step_of_altAcc not_acc_stG haccBack
        have hover : m + 1 = k → CanHandOver k A cnf := by
          intro hmk
          rcases inSweepL_step hinvL hstep₀ with ⟨-, hrank⟩ | ⟨-, -, -, -, hcase⟩
          · refine absurd hrank ?_
            change ¬(bitRank tagTupleLe AltPosn d₀.head <
              bitRank tagTupleLe AltPosn (posStart : AltV k A))
            rw [bitRank_posStart]
            omega
          · rcases hcase with ⟨hbad, -⟩ | ⟨-, hrest⟩
            · exact absurd hbad (by omega)
            · rcases hrest with ⟨c₀, hmin, -⟩ | ⟨hno, hcnf, -⟩
              · exact Or.inl ⟨c₀, hmin⟩
              · exact Or.inr ⟨hcnf, hno⟩
        obtain ⟨d, hd⟩ := exists_atRound (m := m + 1) (by omega)
          (Function.update νs ⟨m, hlt⟩ ν) hover
        obtain ⟨-, haccd⟩ := altAcc_down_step
          (⟨not_acc_stG, Or.inl (isUniv_stG.mpr hpol)⟩ :
            StepForced (altMachine k A cnf) start
              (confBack (Function.update νs ⟨m, hlt⟩ ν) (Fin.castSucc ⟨m, hlt⟩) posStart) d)
          (step_handover hd) haccBack
        have hres := (ih (m + 1) (by omega) (Function.update νs ⟨m, hlt⟩ ν) d hd).1 _ haccd
        rwa [hpolsucc, hpol] at hres
      · refine altAcc_of_inSweepR (i := ⟨m, hlt⟩) (n' := roundBound k A r) (by rw [hpol]) ?_ ?_
          (bitRank tagTupleLe AltPosn (posEnd : AltV k A) - 1) n c
          (hci ▸ inSweepR_start ⟨m, hlt⟩ νs) (by rw [hci]; exact le_of_eq (by
            rw [show (confSweep νs (Fin.castSucc ⟨m, hlt⟩) (posCell qbotA)).head =
              (posCell qbotA : AltV k A) from rfl, bitRank_posCell_qbotA])) ?_
        · intro hmk
          have hr0 : r = 0 := by omega
          subst hr0
          exact canHandOver_of_qbfMatrix (ρ := Function.update νs ⟨m, hlt⟩ fun _ => False)
            (htail _)
        · intro ν' e _ hafter
          exact (ih (m + 1) (by omega) (Function.update νs ⟨m, hlt⟩ ν') e
            (atRound_of_afterSweep hafter)).2 (by
              have := htail ν'
              rwa [hpolsucc, hpol]) _ (le_refl _)
        · have h1 : bitRank tagTupleLe AltPosn (posEnd : AltV k A) =
              bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) + 1 :=
            bitRank_posEnd_eq
          have h2 : sweepLen k A =
              (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
                bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A)) + 1 +
              (bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) -
                bitRank tagTupleLe AltPosn (posStart : AltV k A)) + 1 := rfl
          have h3 : bitRank tagTupleLe AltPosn (posCell (qbotA (A := A)) : AltV k A) = 1 :=
            bitRank_posCell_qbotA
          have h4 : bitRank tagTupleLe AltPosn (posStart : AltV k A) = 0 := bitRank_posStart
          simp only [roundBound, roundStep] at hn ⊢
          omega

/-! ### The whole run

The first sweep starts at the left marker rather than at the first cell, so the
run has one step to take before round `0` begins. It is a forced step – the
machine reads `⊢`, which is not a guess – so it costs one unit of budget and
nothing else. -/

/-- **The machine has one initial configuration.** -/
theorem eq_init_of_isInit {cnf : Bool} (νs : Fin k → A → Prop) {c : Config (AltV k A)}
    (hinit : (altMachine k A cnf).IsInit c) : c = confSweep νs 0 posStart := by
  refine TMData.isInit_unique (altMachine_wellFormed cnf) ?_ hinit (isInit_confSweep νs cnf)
  rintro q q' ⟨hq, hq2⟩ ⟨hq', hq2'⟩
  exact Prod.ext (hq.trans hq'.symm) (isMinTup2_unique hq2 hq2')

/-- **The step over the left marker is forced**: the machine reads `⊢`, and
only one transition applies. -/
theorem step_init_det {cnf : Bool} (hk : 0 < k) (νs : Fin k → A → Prop) :
    ∀ c'', (altMachine k A cnf).Step (confSweep νs 0 posStart) c'' →
      c'' = confSweep νs 0 (posCell qbotA) := by
  refine fun c'' hstep => step_functional_off_guess ?_ hstep
    (step_sweepStart (νs := νs) (cnf := cnf) hk)
  rintro ⟨j, x, -, hread⟩
  have : (confSweep νs 0 posStart).tape (confSweep νs 0 posStart).head = symStart := by
    change sweepTape νs 0 posStart posStart = symStart
    rw [sweepTape_posStart]
    rfl
  exact absurd (this.symm.trans hread) (by simp [acstI, aoneI])

/-- The step over the left marker descends whatever the polarity. -/
theorem stepForced_init {cnf start : Bool} (hk : 0 < k) (νs : Fin k → A → Prop) :
    StepForced (altMachine k A cnf) start (confSweep νs 0 posStart)
      (confSweep νs 0 (posCell qbotA)) :=
  ⟨not_acc_stG, Or.inr (step_init_det hk νs)⟩

/-- **The run before round `0`**: one forced step. -/
theorem altAcc_init_iff {cnf start : Bool} (hk : 0 < k) (νs : Fin k → A → Prop) (n : ℕ) :
    (altMachine k A cnf).AltAcc start (n + 1) (confSweep νs 0 posStart) ↔
      (altMachine k A cnf).AltAcc start n (confSweep νs 0 (posCell qbotA)) := by
  constructor
  · intro hacc
    exact (altAcc_down_step (stepForced_init hk νs) (step_sweepStart hk) hacc).2
  · intro hacc
    by_cases hu : (altMachine k A cnf).IsUniv start (confSweep νs 0 posStart).state
    · exact Or.inr (Or.inl ⟨hu, ⟨_, step_sweepStart hk⟩, fun c' hc' => by
        rw [step_init_det hk νs c' hc']
        exact hacc⟩)
    · exact Or.inr (Or.inr ⟨hu, _, step_sweepStart hk, hacc⟩)

/-- **The machine plays the formula.** Acceptance of the alternating machine is
the alternating quantification of the matrix over the `k` blocks – provided the
tape is long enough to hold the run, which
`DescriptiveComplexity.AltQbf.alt_budget` guarantees. -/
theorem altAccepts_iff_altQuant {cnf start : Bool} (hk : 0 < k)
    (hbudget : roundBound k A k + 1 ≤ Nat.card {p : AltV k A // AltPosn p} - 1) :
    (altMachine k A cnf).AltAccepts start ↔ altQuant A k (QbfMatrix cnf) start := by
  classical
  set νs : Fin k → A → Prop := fun _ _ => False with hνs
  obtain ⟨N', hN'⟩ : ∃ N', Nat.card {p : AltV k A // AltPosn p} - 1 = N' + 1 :=
    ⟨Nat.card {p : AltV k A // AltPosn p} - 2, by omega⟩
  -- acceptance is acceptance of the one initial configuration
  have hinit : (altMachine k A cnf).AltAccepts start ↔
      (altMachine k A cnf).AltAcc start (N' + 1) (confSweep νs 0 posStart) := by
    rw [← hN']
    cases start with
    | true =>
      constructor
      · rintro ⟨c₀, hc₀, hacc⟩
        rwa [eq_init_of_isInit νs hc₀] at hacc
      · exact fun hacc => ⟨_, isInit_confSweep νs cnf, hacc⟩
    | false =>
      constructor
      · rintro ⟨-, hall⟩
        exact hall _ (isInit_confSweep νs cnf)
      · exact fun hacc => ⟨⟨_, isInit_confSweep νs cnf⟩, fun c₀ hc₀ => by
          rwa [eq_init_of_isInit νs hc₀]⟩
  -- the round induction, from the entry of round `0`
  have hround : AtRound cnf 0 νs (confSweep νs 0 (posCell qbotA)) :=
    ⟨rfl, tape_confSweep_bot νs 0, Or.inl ⟨hk, 0, rfl, rfl⟩⟩
  obtain ⟨hfwd, hbwd⟩ := rounds (cnf := cnf) (start := start) k 0 (by omega) νs _ hround
  rw [hinit, altAcc_init_iff hk νs N']
  constructor
  · intro hacc
    exact (altTail_zero_iff_altQuant (QbfMatrix cnf) νs start).mp
      (by simpa only [blockPol_zero] using hfwd N' hacc)
  · intro hq
    refine hbwd ?_ N' (by omega)
    simpa only [blockPol_zero] using
      (altTail_zero_iff_altQuant (QbfMatrix cnf) νs start).mpr hq

/-! ### The tape is long enough

The `k` rounds cost one sweep each and the check one sweep per clause, which is
what `DescriptiveComplexity.AltQbf.alt_budget` was proved for: the filler positions
alone outnumber them. -/

omit [(Language.qbf k).Structure A] in
theorem roundBound_eq (r : ℕ) : roundBound k A r = chkLen k A + r * sweepLen k A := by
  induction r with
  | zero => simp [roundBound]
  | succ r ih =>
    simp only [roundBound, roundStep, ih]
    ring

omit [(Language.qbf k).Structure A] in
/-- **The whole run fits in the budget.** -/
theorem roundBound_lt_card :
    roundBound k A k + 1 ≤ Nat.card {p : AltV k A // AltPosn p} - 1 := by
  have hn : 1 ≤ Nat.card A := Nat.card_pos
  have h1 : bitRank tagTupleLe AltPosn (posEnd : AltV k A) ≤ Nat.card A + 1 :=
    bitRank_posEnd_le
  have h2 : sweepLen k A ≤ 2 * (Nat.card A + 1) := sweepLen_le
  have h3 := alt_budget (k := k) (n := Nat.card A) (m := Nat.card A) hn (le_refl _)
  have h4 : 8 * (k + 1) * Nat.card A * Nat.card A ≤ Nat.card {p : AltV k A // AltPosn p} :=
    alt_card_le_card_posn k A
  have h5 : chkLen k A ≤ Nat.card A * (Nat.card A + 1) := by
    simp only [chkLen]
    exact Nat.mul_le_mul_left _ h1
  have h6 : k * sweepLen k A ≤ k * (2 * (Nat.card A + 1)) := Nat.mul_le_mul_left k h2
  have h7 : Nat.card A * (Nat.card A + 1) + k * (2 * (Nat.card A + 1)) + 2 ≤
      (2 * k + Nat.card A + 1) * (Nat.card A + 2) := by nlinarith
  rw [roundBound_eq]
  omega

/-- **The machine of a quantified Boolean formula accepts exactly when the
formula is true.** The semantic half of `QBF k ≤ᶠᵒ[≤] ATMAccept k`: what is
left is to write the machine down in first-order logic. -/
theorem altAccepts_iff_qbf {cnf start : Bool} (hk : 0 < k) :
    (altMachine k A cnf).AltAccepts start ↔ altQuant A k (QbfMatrix cnf) start :=
  altAccepts_iff_altQuant hk roundBound_lt_card

end Rounds

end AltQbf

end DescriptiveComplexity
