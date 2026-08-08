/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameAsk
import DescriptiveComplexity.Exponential.GameSweep

/-!
# The machine plays the game

The forward simulation: **a winning state of an `SOGameSpec` is a winning
configuration of the machine**. Everything it is made of is already proved – a
question holding wins from the entry of its prefix
(`DescriptiveComplexity.GameProg.altWin_ask`), an existential sweep writes what
its owner chooses and a universal one is answered for every assignment
(`DescriptiveComplexity.altWin_sweep_ex`,
`DescriptiveComplexity.altWin_sweep_all`) – so what is left is the control
graph, one clause of `DescriptiveComplexity.SOGameSpec.Wins` at a time.

## The invariant

`DescriptiveComplexity.PlayCfg` says the tape's region `r` holds the current
position and the machine is at `play` for that region. The candidate region is
junk: nothing reads it before it is swept.

That is where the roles swapping pays. `play` at `!r` re-enters the same
invariant with the regions exchanged, so a move of the game costs one sweep and
**nothing is ever copied**.

## The three clauses

```
Wins.won  ρ  ⟶  ∃ picks `verify won`
Wins.ex   ρ σ ⟶  ∃ picks splitEx: ∀ { verify ¬univ ; sweep σ ; ∀ { verify move ; play σ } }
Wins.all  ρ   ⟶  ∃ picks splitAll: ∀ { verify univ
                                     ; sweep a witness ; verify move
                                     ; ∀-sweep ; ∃ { verify ¬move ; play } }
```

The last line is the one that needed the machinery: the universal sweep hands
an *arbitrary* candidate to `allStep`, where the existential player either
refutes the move – no sentence over the base could have filtered it out earlier
– or plays on, which is the induction hypothesis.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **The machine sits at a position of the game**: the tape's region `r` holds
that position, and the control is at `play` for that region. -/
def PlayCfg {L : Language.{0, 0}} (spec : SOGameSpec L) {V M : ℕ} {A : Type}
    [L.Structure A] [LinearOrder A] (a₀ : A)
    (hdim : blockArityBound spec.B ≤ gameDim spec.B V)
    (prog : GameProg (L.sum Language.order) spec.B V M) (ρ : spec.State A) (r par : Bool)
    (c : Config (GamePt spec.B V M A)) : Prop :=
  ∃ ρ₀ σ₀ : spec.B.Assignment A, cond r σ₀ ρ₀ = ρ ∧
    CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.playPh r par) (fun _ => a₀) c

section Play

variable {L : Language.{0, 0}} {spec : SOGameSpec L} {V M : ℕ}
  {prog : GameProg (L.sum Language.order) spec.B V M}
  {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
  {a₀ : A} {hdim : blockArityBound spec.B ≤ gameDim spec.B V}

local notation "𝕄" => gameMachine prog.vars prog.pol a₀ hdim
  (gameRule prog.vars prog.natoms prog.concOk prog.isTarget)

omit [L.Structure A] [LinearOrder A] [Finite A] in
private theorem not_true_of_eq_false {b : Bool} (h : b = false) : ¬ (b = true) := by
  rw [h]; simp

/-- **A branch that checks a question wins when the question holds.** -/
theorem altWin_question (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    {ρ₀ σ₀ : spec.B.Assignment A} {q : GameQuestion} {r par : Bool}
    {c : Config (GamePt spec.B V M A)}
    (hQ : spec.QuestionHolds q (cond r σ₀ ρ₀) (cond (!r) σ₀ ρ₀))
    (h : CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.prePh q r 0 par) (fun _ => a₀) c) :
    (𝕄).AltWin true c :=
  GameProg.altWin_ask h₀ q (hplays q) (by simp)
    ((spec.realize_question q _ _).mpr hQ) h

omit [L.Structure A] [LinearOrder A] [Finite A] in
/-- The pair of assignments that writes `σ` into the candidate region and
leaves the current one alone. -/
theorem cond_swap (r : Bool) (ρ₀ σ₀ σ : spec.B.Assignment A) :
    cond r (cond r σ₀ σ) (cond r σ ρ₀) = cond r σ₀ ρ₀ ∧
      cond (!r) (cond r σ₀ σ) (cond r σ ρ₀) = σ := by
  cases r <;> exact ⟨rfl, rfl⟩

/-! ### The three clauses of `Wins` -/

/-- **A state that wins outright**: the existential player claims `won`. -/
theorem altWin_play_won (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    {ρ₀ σ₀ : spec.B.Assignment A} {r par : Bool} {c : Config (GamePt spec.B V M A)}
    (hw : spec.IsWon (cond r σ₀ ρ₀))
    (h : CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.playPh r par) (fun _ => a₀) c) :
    (𝕄).AltWin true c := by
  refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
    (isTarget := prog.isTarget) (pol := prog.pol)
    (Good := fun p' _ => p' = MachPh.prePh .won r 0 (!par)) h₀
    (by simp [MachPh.playPh]) (by simp [MachPh.playPh]) (by simp [MachPh.playPh])
    (by simp [MachPh.playPh])
    ⟨_, fun _ => a₀, (MachPh.ctrlStep_playPh _ _ r par _).mpr (Or.inl rfl), fun _ _ => rfl, rfl⟩
    (fun hu => absurd hu (not_true_of_eq_false rfl))
    (fun p' w _ _ hgood c' h' => ?_) h
  subst hgood
  exact altWin_question h₀ hplays (q := .won) hw (ctrlCfg_of_arity_zero (by simp) h')

/-- **An existential state with a winning move**: the existential player claims
the existential clause, proves the state is its own and sweeps the move in;
then the move is checked and the play goes on at the other region. -/
theorem altWin_play_ex (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    {ρ₀ σ₀ : spec.B.Assignment A} {σ : spec.State A} {r par : Bool}
    {c : Config (GamePt spec.B V M A)}
    (hnu : ¬ spec.IsUniv (cond r σ₀ ρ₀)) (hmv : spec.Move (cond r σ₀ ρ₀) σ)
    (ih : ∀ (r' par' : Bool) (c' : Config (GamePt spec.B V M A)),
      PlayCfg spec a₀ hdim prog σ r' par' c' → (𝕄).AltWin true c')
    (h : CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.playPh r par) (fun _ => a₀) c) :
    (𝕄).AltWin true c := by
  obtain ⟨hkeepr, hnewr⟩ := cond_swap (spec := spec) r ρ₀ σ₀ σ
  -- ∃ claims the existential clause
  refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
    (isTarget := prog.isTarget) (pol := prog.pol)
    (Good := fun p' _ => p' = MachPh.splitExPh r (!par)) h₀
    (by simp [MachPh.playPh]) (by simp [MachPh.playPh]) (by simp [MachPh.playPh])
    (by simp [MachPh.playPh])
    ⟨_, fun _ => a₀, (MachPh.ctrlStep_playPh _ _ r par _).mpr (Or.inr (Or.inl rfl)),
      fun _ _ => rfl, rfl⟩
    (fun hu => absurd hu (not_true_of_eq_false rfl))
    (fun p' w _ _ hgood c' h' => ?_) h
  subst hgood
  -- the split: prove the state is existential, and move
  refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
    (isTarget := prog.isTarget) (pol := prog.pol) (Good := fun _ _ => True) h₀
    (by simp [MachPh.splitExPh]) (by simp [MachPh.splitExPh]) (by simp [MachPh.splitExPh])
    (by simp [MachPh.splitExPh])
    ⟨_, fun _ => a₀, (MachPh.ctrlStep_splitExPh _ _ r (!par) _).mpr (Or.inl rfl),
      fun _ _ => rfl, trivial⟩
    (fun _ _ _ _ _ => trivial) (fun p₂ w₂ hcs _ _ c₂ h₂ => ?_)
    (ctrlCfg_of_arity_zero (by simp) h')
  rcases (MachPh.ctrlStep_splitExPh _ _ r (!par) p₂).mp hcs with rfl | rfl
  · exact altWin_question h₀ hplays (q := .notUniv) hnu (ctrlCfg_of_arity_zero (by simp) h₂)
  · -- the sweep writes `σ` into the candidate region
    have h₂' := ctrlCfg_of_arity_zero (by simp) h₂
    refine altWin_sweep_ex (natoms := prog.natoms) (concOk := prog.concOk)
      (isTarget := prog.isTarget) (pol := prog.pol) h₀ (ρ' := cond r σ ρ₀) (σ' := cond r σ₀ σ)
      ?_ rfl h₂'.1 h₂'.2.2.1 h₂'.2.2.2 (fun c₃ h₃ => ?_)
    · intro rr hrr
      cases r <;> cases rr <;> simp_all
    · -- the move is checked, and the play goes on at the other region
      have h₄ : CtrlCfg a₀ hdim prog.vars (cond r σ ρ₀) (cond r σ₀ σ)
          (MachPh.splitMovePh r false) (fun _ => a₀) c₃ := h₃
      refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
        (isTarget := prog.isTarget) (pol := prog.pol) (Good := fun _ _ => True) h₀
        (by simp [MachPh.splitMovePh]) (by simp [MachPh.splitMovePh])
        (by simp [MachPh.splitMovePh]) (by simp [MachPh.splitMovePh])
        ⟨_, fun _ => a₀, (MachPh.ctrlStep_splitMovePh _ _ r false _).mpr (Or.inl rfl),
          fun _ _ => rfl, trivial⟩
        (fun _ _ _ _ _ => trivial) (fun p₅ w₅ hcs₅ _ _ c₅ h₅ => ?_) h₄
      rcases (MachPh.ctrlStep_splitMovePh _ _ r false p₅).mp hcs₅ with rfl | rfl
      · refine altWin_question h₀ hplays (q := .move) ?_ (ctrlCfg_of_arity_zero (by simp) h₅)
        rw [hkeepr, hnewr]
        exact hmv
      · exact ih (!r) true c₅ ⟨_, _, hnewr, ctrlCfg_of_arity_zero (by simp) h₅⟩

/-- **A universal state all of whose moves win**: the existential player claims
the universal clause, proves the state is universal, certifies that a move
exists at all, and then answers every candidate the universal sweep may write –
by refuting the move, or by playing on. -/
theorem altWin_play_all (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    {ρ₀ σ₀ : spec.B.Assignment A} {r par : Bool} {c : Config (GamePt spec.B V M A)}
    (hu : spec.IsUniv (cond r σ₀ ρ₀)) (hex : ∃ σ, spec.Move (cond r σ₀ ρ₀) σ)
    (ih : ∀ σ, spec.Move (cond r σ₀ ρ₀) σ → ∀ (r' par' : Bool)
      (c' : Config (GamePt spec.B V M A)),
      PlayCfg spec a₀ hdim prog σ r' par' c' → (𝕄).AltWin true c')
    (h : CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.playPh r par) (fun _ => a₀) c) :
    (𝕄).AltWin true c := by
  obtain ⟨σw, hσw⟩ := hex
  obtain ⟨hkeepr, hnewr⟩ := cond_swap (spec := spec) r ρ₀ σ₀ σw
  have hrr : r ≠ !r := by cases r <;> simp
  -- ∃ claims the universal clause
  refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
    (isTarget := prog.isTarget) (pol := prog.pol)
    (Good := fun p' _ => p' = MachPh.splitAllPh r (!par)) h₀
    (by simp [MachPh.playPh]) (by simp [MachPh.playPh]) (by simp [MachPh.playPh])
    (by simp [MachPh.playPh])
    ⟨_, fun _ => a₀, (MachPh.ctrlStep_playPh _ _ r par _).mpr (Or.inr (Or.inr rfl)),
      fun _ _ => rfl, rfl⟩
    (fun hu' => absurd hu' (not_true_of_eq_false rfl))
    (fun p' w _ _ hgood c' h' => ?_) h
  subst hgood
  -- the split: three branches
  refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
    (isTarget := prog.isTarget) (pol := prog.pol) (Good := fun _ _ => True) h₀
    (by simp [MachPh.splitAllPh]) (by simp [MachPh.splitAllPh]) (by simp [MachPh.splitAllPh])
    (by simp [MachPh.splitAllPh])
    ⟨_, fun _ => a₀, (MachPh.ctrlStep_splitAllPh _ _ r (!par) _).mpr (Or.inl rfl),
      fun _ _ => rfl, trivial⟩
    (fun _ _ _ _ _ => trivial) (fun p₂ w₂ hcs _ _ c₂ h₂ => ?_)
    (ctrlCfg_of_arity_zero (by simp) h')
  rcases (MachPh.ctrlStep_splitAllPh _ _ r (!par) p₂).mp hcs with rfl | rfl | rfl
  · exact altWin_question h₀ hplays (q := .univ) hu (ctrlCfg_of_arity_zero (by simp) h₂)
  · -- certify that a move exists: sweep the witness in and check it
    have h₂' := ctrlCfg_of_arity_zero (by simp) h₂
    refine altWin_sweep_ex (natoms := prog.natoms) (concOk := prog.concOk)
      (isTarget := prog.isTarget) (pol := prog.pol) h₀ (ρ' := cond r σw ρ₀) (σ' := cond r σ₀ σw)
      ?_ rfl h₂'.1 h₂'.2.2.1 h₂'.2.2.2 (fun c₃ h₃ => ?_)
    · intro rr hrr'
      cases r <;> cases rr <;> simp_all
    · have h₃' : CtrlCfg a₀ hdim prog.vars (cond r σw ρ₀) (cond r σ₀ σw)
          (MachPh.prePh .move r 0 false) (fun _ => a₀) c₃ := h₃
      refine altWin_question h₀ hplays (q := .move) ?_ h₃'
      rw [hkeepr, hnewr]
      exact hσw
  · -- the universal sweep: every candidate is answered
    have h₂' := ctrlCfg_of_arity_zero (by simp) h₂
    refine altWin_sweep_all (natoms := prog.natoms) (concOk := prog.concOk)
      (isTarget := prog.isTarget) (pol := prog.pol) h₀
      rfl
      ⟨ρ₀, σ₀, fun _ _ => rfl, h₂'.1, by rw [h₂'.2.2.1]; exact trivial,
        by rw [h₂'.2.2.1]; exact fun _ _ => h₀, h₂'.2.2.2⟩ (fun ρ' σ' hkeep' c₃ h₃ => ?_)
    have h₄ : CtrlCfg a₀ hdim prog.vars ρ' σ' (MachPh.allStepPh r false) (fun _ => a₀) c₃ := h₃
    have hcur : cond r σ' ρ' = cond r σ₀ ρ₀ := hkeep' r hrr
    by_cases hmv : spec.Move (cond r σ₀ ρ₀) (cond (!r) σ' ρ')
    · -- the move is legal: play on at the other region
      refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
        (isTarget := prog.isTarget) (pol := prog.pol)
        (Good := fun p' _ => p' = MachPh.playPh (!r) true) h₀
        (by simp [MachPh.allStepPh]) (by simp [MachPh.allStepPh]) (by simp [MachPh.allStepPh])
        (by simp [MachPh.allStepPh])
        ⟨_, fun _ => a₀, (MachPh.ctrlStep_allStepPh _ _ r false _).mpr (Or.inr rfl),
          fun _ _ => rfl, rfl⟩
        (fun hu' => absurd hu' (not_true_of_eq_false rfl))
        (fun p₅ w₅ _ _ hgood₅ c₅ h₅ => ?_) h₄
      subst hgood₅
      exact ih _ hmv (!r) true c₅ ⟨ρ', σ', rfl, ctrlCfg_of_arity_zero (by simp) h₅⟩
    · -- the move is illegal: refute it
      refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
        (isTarget := prog.isTarget) (pol := prog.pol)
        (Good := fun p' _ => p' = MachPh.prePh .notMove r 0 true) h₀
        (by simp [MachPh.allStepPh]) (by simp [MachPh.allStepPh]) (by simp [MachPh.allStepPh])
        (by simp [MachPh.allStepPh])
        ⟨_, fun _ => a₀, (MachPh.ctrlStep_allStepPh _ _ r false _).mpr (Or.inl rfl),
          fun _ _ => rfl, rfl⟩
        (fun hu' => absurd hu' (not_true_of_eq_false rfl))
        (fun p₅ w₅ _ _ hgood₅ c₅ h₅ => ?_) h₄
      subst hgood₅
      refine altWin_question h₀ hplays (q := .notMove) ?_ (ctrlCfg_of_arity_zero (by simp) h₅)
      rw [hcur]
      exact hmv

/-! ### The play -/

/-- **A winning state of the game is a winning configuration of the machine.**
By induction on `DescriptiveComplexity.SOGameSpec.Wins`, one clause per lemma
above. -/
theorem altWin_play (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    {ρ : spec.State A} (hw : spec.Wins ρ) :
    ∀ (r par : Bool) (c : Config (GamePt spec.B V M A)),
      PlayCfg spec a₀ hdim prog ρ r par c → (𝕄).AltWin true c := by
  induction hw with
  | won hw =>
    rintro r par c ⟨ρ₀, σ₀, rfl, h⟩
    exact altWin_play_won h₀ hplays hw h
  | ex hnu hmv _ ih =>
    rintro r par c ⟨ρ₀, σ₀, rfl, h⟩
    exact altWin_play_ex h₀ hplays hnu hmv (fun r' par' c' hc' => ih r' par' c' hc') h
  | all hu hex _ ih =>
    rintro r par c ⟨ρ₀, σ₀, rfl, h⟩
    exact altWin_play_all h₀ hplays hu hex (fun σ hσ r' par' c' hc' => ih σ hσ r' par' c' hc') h

/-! ### The entry -/

open Classical in
/-- **The machine accepts when the game does.** The initial tape is empty –
`Inp` is total on the positions, which is what makes it functional – so the
starting position is *guessed*, by the very first sweep; the split that follows
checks it starts the game, and plays it. -/
theorem altAcceptsSpace_of_accepts (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q)) (hacc : spec.Accepts A) :
    (𝕄).AltAcceptsSpace true := by
  obtain ⟨ρ, hstart, hwins⟩ := hacc
  refine ⟨⟨phasePt (startPh V M) (fun _ => a₀), leftPt a₀ false,
    fun p => if machPosn p then gameInitTape a₀ hdim p else markPt a₀ false⟩, ?_, ?_⟩
  · -- an initial configuration: the start state, the lowest position, the empty tape
    refine ⟨rfl, minPos_leftPt h₀ (carity := ctrlArity prog.vars), fun p => ?_⟩
    by_cases hp : machPosn p
    · exact Or.inl ⟨hp, if_pos hp⟩
    · exact Or.inr ⟨fun b hb => hp hb.1, if_neg hp⟩
  · -- the first sweep guesses the starting position
    refine altWin_sweep_ex (natoms := prog.natoms) (concOk := prog.concOk)
      (isTarget := prog.isTarget) (pol := prog.pol) (ρ := emptyAssign spec.B A)
      (σ := emptyAssign spec.B A) h₀ (ρ' := ρ) (σ' := emptyAssign spec.B A) ?_ rfl rfl rfl
      (fun q hq hd => ?_) (fun c₃ h₃ => ?_)
    · intro rr hrr
      cases rr with
      | false => exact absurd rfl hrr
      | true => rfl
    · exact if_pos hq
    · -- check that it starts the game, and play
      have h₄ : CtrlCfg a₀ hdim prog.vars ρ (emptyAssign spec.B A)
          (MachPh.splitStartPh false false) (fun _ => a₀) c₃ := h₃
      refine altWin_of_steps (natoms := prog.natoms) (concOk := prog.concOk)
        (isTarget := prog.isTarget) (pol := prog.pol) (Good := fun _ _ => True) h₀
        (by simp [MachPh.splitStartPh]) (by simp [MachPh.splitStartPh])
        (by simp [MachPh.splitStartPh]) (by simp [MachPh.splitStartPh])
        ⟨_, fun _ => a₀, (MachPh.ctrlStep_splitStartPh _ _ false false _).mpr (Or.inl rfl),
          fun _ _ => rfl, trivial⟩
        (fun _ _ _ _ _ => trivial) (fun p₅ w₅ hcs₅ _ _ c₅ h₅ => ?_) h₄
      rcases (MachPh.ctrlStep_splitStartPh _ _ false false p₅).mp hcs₅ with rfl | rfl
      · refine altWin_question h₀ hplays (q := .start) ?_ (ctrlCfg_of_arity_zero (by simp) h₅)
        exact hstart
      · exact altWin_play h₀ hplays hwins false true c₅
          ⟨ρ, emptyAssign spec.B A, rfl, ctrlCfg_of_arity_zero (by simp) h₅⟩

end Play

end DescriptiveComplexity
