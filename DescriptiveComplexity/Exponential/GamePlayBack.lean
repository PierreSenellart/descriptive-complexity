/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameAskBack
import DescriptiveComplexity.Exponential.GameSweep
import DescriptiveComplexity.Exponential.GamePlay

/-!
# The game, read back

The backward simulation of the game itself: **a winning configuration of the
machine is a winning state of the game**. It is one induction on
`DescriptiveComplexity.ATMData.AltWin`, whose motive is a conjunction with one
clause per phase the game proper can be in.

## What each phase proves

The conclusions at `play`, `splitEx` and `splitAll` are all `spec.Wins ρ`,
because what a split proves is exactly the premises of the matching constructor
of `DescriptiveComplexity.SOGameSpec.Wins`. The others are the
`DescriptiveComplexity.ContGoal` a sweep's continuation names:

```
start   ⟶ IsStart ρ ∧ Wins ρ            certify ⟶ Move ρ σ
exMove  ⟶ Move ρ σ ∧ Wins σ             allMove ⟶ ¬ Move ρ σ ∨ Wins σ
```

In each case of the induction most clauses are one line: at `acc` no phase of
the game is accepting, and at `ex`/`all` the clauses of the *other* polarity are
killed by `IsUniv`.

## The one trap, and the motive that avoids it

A universal sweep cannot be read backwards: its clause is *every candidate is
answered*, and at a half-finished sweep that is false – the cells already
written cannot be changed. So the motive is strengthened to

> `Sound c` : for every `d` reachable from `c` by steps **whose sources are
> universal sweeps**, the clauses hold at `d`.

The clauses at `c` follow by the reflexive chain, and in the `all` case the
chain's first step is a successor, so the induction hypothesis covers the rest
of it. That lets the universal sweep be proved *forward*: its run supplies the
chain, the handover the last step, and the motive delivers the clauses at the
**rewind** configuration – whose clause is the `ContGoal` wanted.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **A configuration in the middle of a walk**: the phase at the constant
valuation, the head anywhere among the positions, and the tape holding the two
assignments. Unlike `DescriptiveComplexity.CtrlCfg` it does not pin the head to
a sentinel, which is exactly what a rewind needs. -/
def WalkCfg {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] (a₀ : A)
    (hdim : blockArityBound B ≤ gameDim B V) (vars : GameQuestion → ℕ)
    (ρ σ : B.Assignment A) (p : MachPh V M) (c : Config (GamePt B V M A)) : Prop :=
  c.state = phasePt p (fun _ => a₀) ∧ machPosn c.head ∧ machDom (ctrlArity vars) c.head ∧
    ∀ q : GamePt B V M A, machPosn q → machDom (ctrlArity vars) q →
      c.tape q = tapeOfAssign a₀ hdim ρ σ q

/-- **What a sweep's continuation has to prove**, one clause per place the
control guesses an assignment. -/
def ContGoal {L : Language.{0, 0}} (spec : SOGameSpec L) {A : Type} [L.Structure A]
    [LinearOrder A] (cont : SweepCont) (r : Bool) (ρ σ : spec.B.Assignment A) : Prop :=
  match cont with
  | .start => spec.IsStart (cond r σ ρ) ∧ spec.Wins (cond r σ ρ)
  | .exMove => spec.Move (cond r σ ρ) (cond (!r) σ ρ) ∧ spec.Wins (cond (!r) σ ρ)
  | .certify => spec.Move (cond r σ ρ) (cond (!r) σ ρ)
  | .allMove => ¬ spec.Move (cond r σ ρ) (cond (!r) σ ρ) ∨ spec.Wins (cond (!r) σ ρ)

section Play

variable {L : Language.{0, 0}} {spec : SOGameSpec L} {V M : ℕ}
  {prog : GameProg (L.sum Language.order) spec.B V M}
  {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
  {a₀ : A} {hdim : blockArityBound spec.B ≤ gameDim spec.B V}

local notation "𝕄" => gameMachine prog.vars prog.pol a₀ hdim
  (gameRule prog.vars prog.natoms prog.concOk prog.isTarget)

variable (spec a₀ hdim prog) in
/-- **What a win proves, phase by phase.** -/
structure GameStmt (d : Config (GamePt spec.B V M A)) : Prop where
  /-- A position of the game is winning. -/
  play : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r par : Bool),
    CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.playPh r par) (fun _ => a₀) d →
      spec.Wins (cond r σ₀ ρ₀)
  /-- So is the existential clause. -/
  splitEx : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r par : Bool),
    CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.splitExPh r par) (fun _ => a₀) d →
      spec.Wins (cond r σ₀ ρ₀)
  /-- And the universal one. -/
  splitAll : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r par : Bool),
    CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.splitAllPh r par) (fun _ => a₀) d →
      spec.Wins (cond r σ₀ ρ₀)
  /-- After an existential move: it is legal, and the play goes on. -/
  splitMove : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r par : Bool),
    CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.splitMovePh r par) (fun _ => a₀) d →
      ContGoal spec .exMove r ρ₀ σ₀
  /-- After a universal move: it is refuted, or the play goes on. -/
  allStep : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r par : Bool),
    CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.allStepPh r par) (fun _ => a₀) d →
      ContGoal spec .allMove r ρ₀ σ₀
  /-- At the start: the position starts the game, and wins it. -/
  splitStart : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r par : Bool),
    CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.splitStartPh r par) (fun _ => a₀) d →
      ContGoal spec .start r ρ₀ σ₀
  /-- A rewind proves what its continuation must. -/
  rewind : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r tgt : Bool) (cont : SweepCont) (par : Bool),
    WalkCfg a₀ hdim prog.vars ρ₀ σ₀ (MachPh.rewindPh r tgt cont par) d →
      ContGoal spec cont r ρ₀ σ₀
  /-- An existential sweep proves it for *some* assignment of its region. -/
  sweepEx : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r tgt : Bool) (cont : SweepCont) (par : Bool),
    cont ≠ .allMove → SweptCfg a₀ hdim prog.vars ρ₀ σ₀ tgt
      (MachPh.sweepPh r tgt cont par) d →
      ∃ ρ' σ' : spec.B.Assignment A,
        (∀ rr : Bool, rr ≠ tgt → cond rr σ' ρ' = cond rr σ₀ ρ₀) ∧ ContGoal spec cont r ρ' σ'
  /-- A universal sweep proves it for *every* assignment of its region – but
  only at its entry, the head on the sentinel its parity names. -/
  sweepAll : ∀ (ρ₀ σ₀ : spec.B.Assignment A) (r tgt par : Bool),
    SweptCfg a₀ hdim prog.vars ρ₀ σ₀ tgt (MachPh.sweepPh r tgt .allMove par) d →
      d.head = leftPt a₀ par →
      ∀ ρ' σ' : spec.B.Assignment A,
        (∀ rr : Bool, rr ≠ tgt → cond rr σ' ρ' = cond rr σ₀ ρ₀) →
          ContGoal spec .allMove r ρ' σ'

variable (a₀) in
/-- The guard of the chain the motive quantifies over: a step taken *from* a
universal sweep. -/
def AtAllSweep (d : Config (GamePt spec.B V M A)) : Prop :=
  ∃ r tgt par : Bool, d.state = phasePt (MachPh.sweepPh r tgt .allMove par) (fun _ => a₀)

variable (spec a₀ hdim prog) in
/-- **The motive**: the clauses hold not only here but everywhere a universal
sweep can carry the play. See the module docstring for why. -/
def Sound (c : Config (GamePt spec.B V M A)) : Prop :=
  ∀ d, Relation.ReflTransGen
    (fun x y => (𝕄).toTMData.Step x y ∧ AtAllSweep a₀ x) c d → GameStmt spec prog a₀ hdim d

/-! ### Small conversions between the three shapes of a configuration -/

omit [L.Structure A] [Finite A] in
theorem WalkCfg.of_ctrlCfg {ρ₀ σ₀ : spec.B.Assignment A} {p : MachPh V M}
    {d : Config (GamePt spec.B V M A)} (h₀ : IsBot a₀)
    (h : CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ p (fun _ => a₀) d) :
    WalkCfg a₀ hdim prog.vars ρ₀ σ₀ p d :=
  ⟨h.1, by rw [h.2.2.1]; exact trivial, by rw [h.2.2.1]; exact fun _ _ => h₀, h.2.2.2⟩

omit [L.Structure A] [Finite A] in
theorem CtrlCfg.of_walkCfg {ρ₀ σ₀ : spec.B.Assignment A} {p : MachPh V M}
    {d : Config (GamePt spec.B V M A)} (h₀ : IsBot a₀)
    (h : WalkCfg a₀ hdim prog.vars ρ₀ σ₀ p d) (hhead : d.head = leftPt a₀ p.par) :
    CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ p (fun _ => a₀) d :=
  ⟨h.1, fun _ _ => h₀, hhead, h.2.2.2⟩

omit [L.Structure A] [Finite A] in
theorem SweptCfg.of_ctrlCfg {ρ₀ σ₀ : spec.B.Assignment A} {tgt : Bool} {p : MachPh V M}
    {d : Config (GamePt spec.B V M A)} (h₀ : IsBot a₀)
    (h : CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ p (fun _ => a₀) d) :
    SweptCfg a₀ hdim prog.vars ρ₀ σ₀ tgt p d :=
  ⟨ρ₀, σ₀, fun _ _ => rfl, (WalkCfg.of_ctrlCfg h₀ h)⟩

omit [Finite A] in
/-- No phase of the game is accepting. -/
theorem not_acc_of_state {d : Config (GamePt spec.B V M A)} {p : MachPh V M}
    {vv : Fin (gameDim spec.B V) → A} (hst : d.state = phasePt p vv) (hk : p.kind ≠ .acc) :
    ¬ (𝕄).Acc d.state := by
  rintro ⟨ph, hph, hkind⟩
  rw [hst] at hph
  exact hk ((Sum.inl.inj (Sum.inr.inj hph)) ▸ hkind)

omit [Finite A] in
/-- A configuration belongs to the universal player exactly when its phase
does. -/
theorem isUniv_state {d : Config (GamePt spec.B V M A)} {p : MachPh V M}
    {vv : Fin (gameDim spec.B V) → A} (hst : d.state = phasePt p vv) :
    (𝕄).IsUniv true d.state ↔ MachPh.IsUniv prog.pol p = true := by
  rw [hst]
  exact gameMachine_isUniv hdim _ p vv

/-! ### The three cases of the induction -/

omit [Finite A] in
/-- **At an accepting configuration the clauses are vacuous**: no phase of the
game is the accepting one. -/
theorem gameStmt_of_acc {d : Config (GamePt spec.B V M A)} (hacc : (𝕄).Acc d.state) :
    GameStmt spec prog a₀ hdim d := by
  constructor
  · intro _ _ _ _ h
    exact absurd hacc (not_acc_of_state h.1 (by simp [MachPh.playPh]))
  · intro _ _ _ _ h
    exact absurd hacc (not_acc_of_state h.1 (by simp [MachPh.splitExPh]))
  · intro _ _ _ _ h
    exact absurd hacc (not_acc_of_state h.1 (by simp [MachPh.splitAllPh]))
  · intro _ _ _ _ h
    exact absurd hacc (not_acc_of_state h.1 (by simp [MachPh.splitMovePh]))
  · intro _ _ _ _ h
    exact absurd hacc (not_acc_of_state h.1 (by simp [MachPh.allStepPh]))
  · intro _ _ _ _ h
    exact absurd hacc (not_acc_of_state h.1 (by simp [MachPh.splitStartPh]))
  · intro _ _ _ _ _ _ h
    exact absurd hacc (not_acc_of_state h.1 (by simp [MachPh.rewindPh]))
  · rintro _ _ _ _ _ _ _ ⟨-, -, -, hst, -⟩
    exact absurd hacc (not_acc_of_state hst (by simp [MachPh.sweepPh]))
  · rintro _ _ _ _ _ ⟨-, -, -, hst, -⟩ _ _ _ _
    exact absurd hacc (not_acc_of_state hst (by simp [MachPh.sweepPh]))

omit [Finite A] in
/-- **At an existential configuration**, the play chose one successor and what
that choice proves is read off the step analysis. -/
theorem gameStmt_of_ex (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    {d d' : Config (GamePt spec.B V M A)} (hnu : ¬ (𝕄).IsUniv true d.state)
    (hstep : (𝕄).toTMData.Step d d') (hw' : (𝕄).AltWin true d')
    (ihd : GameStmt spec prog a₀ hdim d') : GameStmt spec prog a₀ hdim d := by
  -- a universal phase is impossible here
  have huniv : ∀ (p : MachPh V M) (vv : Fin (gameDim spec.B V) → A),
      d.state = phasePt p vv → MachPh.IsUniv prog.pol p = true → False :=
    fun p vv hst hu => hnu ((isUniv_state hst).mpr hu)
  constructor
  · -- play: the existential player claims one clause of `Wins`
    intro ρ₀ σ₀ r par h
    obtain ⟨p', w, hcs, -, -, h'⟩ := ctrlCfg_cases h₀ (by simp [MachPh.playPh])
      (by simp [MachPh.playPh]) (by simp [MachPh.playPh]) h hstep
    rw [MachPh.ctrlStep_playPh] at hcs
    rcases hcs with rfl | rfl | rfl
    · exact .won ((spec.realize_question .won _ _).mp
        (GameProg.ask_of_altWin h₀ .won (hplays .won) (by simp)
          (ctrlCfg_of_arity_zero (by simp) h') hw'))
    · exact ihd.splitEx _ _ _ _ (ctrlCfg_of_arity_zero (by simp) h')
    · exact ihd.splitAll _ _ _ _ (ctrlCfg_of_arity_zero (by simp) h')
  · intro _ _ _ _ h
    exact (huniv _ _ h.1 (MachPh.isUniv_split prog.pol (Or.inr (Or.inl rfl)))).elim
  · intro _ _ _ _ h
    exact (huniv _ _ h.1 (MachPh.isUniv_split prog.pol (Or.inr (Or.inr (Or.inl rfl))))).elim
  · intro _ _ _ _ h
    exact (huniv _ _ h.1 (MachPh.isUniv_split prog.pol (Or.inr (Or.inr (Or.inr rfl))))).elim
  · -- allStep: refute the move, or play on
    intro ρ₀ σ₀ r par h
    obtain ⟨p', w, hcs, -, -, h'⟩ := ctrlCfg_cases h₀ (by simp [MachPh.allStepPh])
      (by simp [MachPh.allStepPh]) (by simp [MachPh.allStepPh]) h hstep
    rw [MachPh.ctrlStep_allStepPh] at hcs
    rcases hcs with rfl | rfl
    · exact Or.inl ((spec.realize_question .notMove _ _).mp
        (GameProg.ask_of_altWin h₀ .notMove (hplays .notMove) (by simp)
          (ctrlCfg_of_arity_zero (by simp) h') hw'))
    · exact Or.inr (ihd.play _ _ _ _ (ctrlCfg_of_arity_zero (by simp) h'))
  · intro _ _ _ _ h
    exact (huniv _ _ h.1 (MachPh.isUniv_split prog.pol (Or.inl rfl))).elim
  · -- rewind: walk on, or hand over to the continuation
    intro ρ₀ σ₀ r tgt cont par h
    obtain ⟨hdst, hpos, htape⟩ := rewindCfg_cases h₀ h.1 ⟨h.2.1, h.2.2.1⟩
      (fun q hq => h.2.2.2 q hq.1 hq.2) hstep
    rcases hdst with hsame | ⟨hst, hhd⟩
    · exact ihd.rewind ρ₀ σ₀ r tgt cont par ⟨hsame.trans h.1, hpos.1, hpos.2,
        fun q hq hd => htape q ⟨hq, hd⟩⟩
    · have hwalk : WalkCfg a₀ hdim prog.vars ρ₀ σ₀
          (MachPh.rewindTarget (MachPh.rewindPh r tgt cont par)) d' :=
        ⟨hst, hpos.1, hpos.2, fun q hq hd => htape q ⟨hq, hd⟩⟩
      have hctrl : CtrlCfg a₀ hdim prog.vars ρ₀ σ₀
          (MachPh.rewindTarget (MachPh.rewindPh r tgt cont par)) (fun _ => a₀) d' :=
        CtrlCfg.of_walkCfg h₀ hwalk (by rw [hhd, MachPh.par_rewindTarget])
      cases cont with
      | start => exact ihd.splitStart ρ₀ σ₀ r false hctrl
      | exMove => exact ihd.splitMove ρ₀ σ₀ r false hctrl
      | certify =>
        exact (spec.realize_question .move _ _).mp
          (GameProg.ask_of_altWin h₀ .move (hplays .move) (by simp) hctrl hw')
      | allMove => exact ihd.allStep ρ₀ σ₀ r false hctrl
  · -- an existential sweep: what it has written so far, or what it hands over
    intro ρ₀ σ₀ r tgt cont par hcont h
    rcases sweepCfg_cases h₀ h hstep with ⟨hsw, -⟩ | ⟨hrw, -, -⟩
    · exact ihd.sweepEx ρ₀ σ₀ r tgt cont par hcont hsw
    · obtain ⟨ρ', σ', hagree, hwalk⟩ := hrw
      exact ⟨ρ', σ', hagree, ihd.rewind ρ' σ' r tgt cont false hwalk⟩
  · -- a universal sweep is not existential
    rintro _ _ r tgt par ⟨-, -, -, hst, -⟩ _ _ _ _
    exact (huniv _ _ hst
      (by rw [MachPh.isUniv_sweep prog.pol (p := MachPh.sweepPh r tgt .allMove par) rfl]; rfl)).elim

omit [Finite A] in
/-- The chain a sweep's run produces is guarded by *at a universal sweep*. -/
theorem chain_atAllSweep {r tgt par : Bool} {d dR : Config (GamePt spec.B V M A)}
    (hst : d.state = phasePt (MachPh.sweepPh r tgt .allMove par) (fun _ => a₀))
    (h : Relation.ReflTransGen
      (fun x y => (𝕄).toTMData.Step x y ∧ x.state = d.state) d dR) :
    Relation.ReflTransGen (fun x y => (𝕄).toTMData.Step x y ∧ AtAllSweep a₀ x) d dR := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hyz ihc => exact ihc.tail ⟨hyz.1, ⟨r, tgt, par, hyz.2.trans hst⟩⟩

/-- **At a universal configuration** every successor wins, so the play may be
instantiated at each of the ones the forward direction knows how to build. The
universal sweep is the exception: it is followed *forward*, through the chain
the motive quantifies over. -/
theorem gameStmt_of_all (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    {d : Config (GamePt spec.B V M A)} (hu : (𝕄).IsUniv true d.state)
    (hall : ∀ c', (𝕄).toTMData.Step d c' → (𝕄).AltWin true c')
    (ih : ∀ c', (𝕄).toTMData.Step d c' → Sound spec prog a₀ hdim c') :
    GameStmt spec prog a₀ hdim d := by
  have hexf : ∀ (p : MachPh V M) (vv : Fin (gameDim spec.B V) → A),
      d.state = phasePt p vv → MachPh.IsUniv prog.pol p = false → False := by
    intro p vv hst hf
    rw [isUniv_state hst, hf] at hu
    exact Bool.false_ne_true hu
  -- one successor of a phase that carries no data, built and won
  have hstep : ∀ (p p' : MachPh V M) (ρ₀ σ₀ : spec.B.Assignment A),
      CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ p (fun _ => a₀) d →
      MachPh.CtrlStep prog.vars prog.natoms p p' → p.kind ≠ .conc →
      MachPh.arity prog.vars p' = 0 →
      ∃ c', CtrlCfg a₀ hdim prog.vars ρ₀ σ₀ p' (fun _ => a₀) c' ∧
        (𝕄).AltWin true c' ∧ Sound spec prog a₀ hdim c' := by
    intro p p' ρ₀ σ₀ h hcs hnc harity
    obtain ⟨c', hst, h'⟩ := ctrlCfg_step (w := fun _ => a₀) h₀ hcs
      (fun hc => absurd hc hnc) (fun _ _ => rfl) h
    exact ⟨c', ctrlCfg_of_arity_zero harity h', hall c' hst, ih c' hst⟩
  constructor
  · intro _ _ r par h
    exact (hexf _ _ h.1 (MachPh.isUniv_play prog.pol rfl)).elim
  · -- splitEx: the state is existential, and the sweep supplies a winning move
    intro ρ₀ σ₀ r par h
    obtain ⟨c₁, h₁, hw₁, -⟩ := hstep _ (MachPh.prePh .notUniv r 0 (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitExPh _ _ r par _).mpr (Or.inl rfl))
      (by simp [MachPh.splitExPh]) (by simp)
    obtain ⟨c₂, h₂, -, hs₂⟩ := hstep _ (MachPh.sweepPh r (!r) .exMove (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitExPh _ _ r par _).mpr (Or.inr rfl))
      (by simp [MachPh.splitExPh]) (by simp)
    obtain ⟨ρ', σ', hagree, hgoal⟩ := (hs₂ c₂ Relation.ReflTransGen.refl).sweepEx ρ₀ σ₀ r
      (!r) .exMove (!par) (by simp) (SweptCfg.of_ctrlCfg h₀ h₂)
    have hkeepr : cond r σ' ρ' = cond r σ₀ ρ₀ := hagree r (by cases r <;> simp)
    exact .ex ((spec.realize_question .notUniv _ _).mp
      (GameProg.ask_of_altWin h₀ .notUniv (hplays .notUniv) (by simp) h₁ hw₁))
      (hkeepr ▸ hgoal.1) hgoal.2
  · -- splitAll: the state is universal, a move exists, and every move wins
    intro ρ₀ σ₀ r par h
    obtain ⟨c₁, h₁, hw₁, -⟩ := hstep _ (MachPh.prePh .univ r 0 (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitAllPh _ _ r par _).mpr (Or.inl rfl))
      (by simp [MachPh.splitAllPh]) (by simp)
    obtain ⟨c₂, h₂, -, hs₂⟩ := hstep _ (MachPh.sweepPh r (!r) .certify (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitAllPh _ _ r par _).mpr (Or.inr (Or.inl rfl)))
      (by simp [MachPh.splitAllPh]) (by simp)
    obtain ⟨c₃, h₃, -, hs₃⟩ := hstep _ (MachPh.sweepPh r (!r) .allMove (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitAllPh _ _ r par _).mpr (Or.inr (Or.inr rfl)))
      (by simp [MachPh.splitAllPh]) (by simp)
    obtain ⟨ρ', σ', hagree, hgoal⟩ := (hs₂ c₂ Relation.ReflTransGen.refl).sweepEx ρ₀ σ₀ r
      (!r) .certify (!par) (by simp) (SweptCfg.of_ctrlCfg h₀ h₂)
    have hkeepr : cond r σ' ρ' = cond r σ₀ ρ₀ := hagree r (by cases r <;> simp)
    have hmv' : spec.Move (cond r σ' ρ') (cond (!r) σ' ρ') := hgoal
    refine .all ((spec.realize_question .univ _ _).mp
      (GameProg.ask_of_altWin h₀ .univ (hplays .univ) (by simp) h₁ hw₁))
      ⟨_, hkeepr ▸ hmv'⟩ (fun τ hmv => ?_)
    obtain ⟨hk, hn⟩ := cond_swap (spec := spec) r ρ₀ σ₀ τ
    have hgoal₃ := (hs₃ c₃ Relation.ReflTransGen.refl).sweepAll ρ₀ σ₀ r (!r) (!par)
      (SweptCfg.of_ctrlCfg h₀ h₃) h₃.2.2.1 (cond r τ ρ₀) (cond r σ₀ τ)
      (fun rr hrr => by
        have : rr = r := by cases r <;> cases rr <;> simp_all
        subst this
        exact hk)
    rcases hgoal₃ with hno | hyes
    · exact absurd (show spec.Move _ _ by rw [hk, hn]; exact hmv) hno
    · rw [← hn]
      exact hyes
  · -- splitMove: the move is legal, and the play goes on
    intro ρ₀ σ₀ r par h
    obtain ⟨c₁, h₁, hw₁, -⟩ := hstep _ (MachPh.prePh .move r 0 (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitMovePh _ _ r par _).mpr (Or.inl rfl))
      (by simp [MachPh.splitMovePh]) (by simp)
    obtain ⟨c₂, h₂, -, hs₂⟩ := hstep _ (MachPh.playPh (!r) (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitMovePh _ _ r par _).mpr (Or.inr rfl))
      (by simp [MachPh.splitMovePh]) (by simp)
    exact ⟨(spec.realize_question .move _ _).mp
      (GameProg.ask_of_altWin h₀ .move (hplays .move) (by simp) h₁ hw₁),
      (hs₂ c₂ Relation.ReflTransGen.refl).play _ _ _ _ h₂⟩
  · intro _ _ r par h
    exact (hexf _ _ h.1 (MachPh.isUniv_allStep prog.pol rfl)).elim
  · -- splitStart: the position starts the game, and wins it
    intro ρ₀ σ₀ r par h
    obtain ⟨c₁, h₁, hw₁, -⟩ := hstep _ (MachPh.prePh .start r 0 (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitStartPh _ _ r par _).mpr (Or.inl rfl))
      (by simp [MachPh.splitStartPh]) (by simp)
    obtain ⟨c₂, h₂, -, hs₂⟩ := hstep _ (MachPh.playPh r (!par)) ρ₀ σ₀ h
      ((MachPh.ctrlStep_splitStartPh _ _ r par _).mpr (Or.inr rfl))
      (by simp [MachPh.splitStartPh]) (by simp)
    exact ⟨(spec.realize_question .start _ _).mp
      (GameProg.ask_of_altWin h₀ .start (hplays .start) (by simp) h₁ hw₁),
      (hs₂ c₂ Relation.ReflTransGen.refl).play _ _ _ _ h₂⟩
  · intro _ _ r tgt cont par h
    exact (hexf _ _ h.1 (MachPh.isUniv_rewind prog.pol rfl)).elim
  · rintro _ _ r tgt cont par hcont ⟨-, -, -, hst, -⟩
    refine (hexf _ _ hst ?_).elim
    rw [MachPh.isUniv_sweep prog.pol (p := MachPh.sweepPh r tgt cont par) rfl]
    simpa [MachPh.sweepPh] using hcont
  · -- the universal sweep, followed forward to the rewind it hands over to
    intro ρ₀ σ₀ r tgt par h hhead ρ' σ' hagree
    obtain ⟨ρt, σt, hagt, hwalk⟩ := h
    have hlin : IsLinOrd (𝕄).Le := isLinOrd_gameLe
    obtain ⟨dR, hchain, hstR, hheadR, htapeR⟩ :=
      sweep_run h₀ (fun rr hrr => (hagree rr hrr).trans (hagt rr hrr).symm) d hwalk.1 hhead
        (fun q hq => hwalk.2.2.2 q hq.1 hq.2)
    have hnmin : ¬ MinPos (𝕄).Le (𝕄).Posn dR.head := by
      intro hm
      rw [hheadR] at hm
      exact leftPt_ne_rightPt a₀ false (hlin.2.2.1 _ _
        ((minPos_leftPt h₀ (carity := ctrlArity prog.vars)).2 _ hm.1)
        (hm.2 _ (minPos_leftPt h₀).1))
    obtain ⟨h', hsu⟩ := exists_predPos hlin (hheadR ▸ ⟨trivial, fun _ _ => h₀⟩) hnmin
    have hread : dR.tape dR.head = markPt a₀ true := by
      rw [hheadR, htapeR (rightPt a₀) ⟨trivial, fun _ _ => h₀⟩, tapeOfAssign_rightPt]
    have hlast := sweep_step_right h₀ dR (hstR.trans hwalk.1) hread hsu
    have hguard : ∀ x : Config (GamePt spec.B V M A), x.state = d.state → AtAllSweep a₀ x :=
      fun x hx => ⟨r, tgt, par, hx.trans hwalk.1⟩
    have hfull := (chain_atAllSweep hwalk.1 hchain).tail ⟨hlast, hguard dR hstR⟩
    rcases Relation.ReflTransGen.cases_head hfull with hrefl | ⟨e₁, hst₁, hrest⟩
    · exfalso
      have hq := congrArg Prod.fst (hwalk.1.symm.trans (congrArg Config.state hrefl))
      simp [phasePt, MachPh.sweepPh, MachPh.rewindPh] at hq
    · exact ((ih e₁ hst₁.1) _ hrest).rewind ρ' σ' r tgt .allMove false
        ⟨rfl, hsu.1.1, hsu.1.2, fun q hq hd => htapeR q ⟨hq, hd⟩⟩

/-! ### The induction, and the entry -/

/-- **A winning configuration of the machine proves what its phase says.** One
induction on `DescriptiveComplexity.ATMData.AltWin`, the three cases being the
three lemmas above; the chain in the motive is what carries a universal sweep. -/
theorem sound_of_altWin (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q)) :
    ∀ c : Config (GamePt spec.B V M A), (𝕄).AltWin true c → Sound spec prog a₀ hdim c := by
  intro c hw
  induction hw with
  | @acc d hacc =>
    intro e hchain
    rcases Relation.ReflTransGen.cases_head hchain with rfl | ⟨e₁, hst₁, -⟩
    · exact gameStmt_of_acc hacc
    · obtain ⟨r, tgt, par, hst⟩ := hst₁.2
      exact absurd hacc (not_acc_of_state hst (by simp [MachPh.sweepPh]))
  | @ex d d' hnu hstep hw' ih =>
    intro e hchain
    rcases Relation.ReflTransGen.cases_head hchain with rfl | ⟨e₁, hst₁, -⟩
    · exact gameStmt_of_ex h₀ hplays hnu hstep hw' (ih d' Relation.ReflTransGen.refl)
    · obtain ⟨r, tgt, par, hst⟩ := hst₁.2
      exact absurd ((isUniv_state hst).mpr
        (by rw [MachPh.isUniv_sweep prog.pol (p := MachPh.sweepPh r tgt .allMove par) rfl];
            rfl)) hnu
  | @all d hu hexs hall ih =>
    intro e hchain
    rcases Relation.ReflTransGen.cases_head hchain with rfl | ⟨e₁, hst₁, hrest⟩
    · exact gameStmt_of_all h₀ hplays hu hall ih
    · exact ih e₁ hst₁.1 e hrest

/-- **The game accepts when the machine does.** The very first sweep is the
one that guessed the starting position, so what it proves – by
`DescriptiveComplexity.ContGoal` at `start` – is that *some* assignment starts
the game and wins it. -/
theorem accepts_of_altAcceptsSpace (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    (hacc : (𝕄).AltAcceptsSpace true) : spec.Accepts A := by
  obtain ⟨c₀, hinit, hw⟩ := hacc
  have hst : c₀.state = phasePt (MachPh.sweepPh false false .start false) (fun _ => a₀) :=
    hinit.1
  have hhd : c₀.head = leftPt a₀ false :=
    isLinOrd_gameLe.2.2.1 _ _
      (hinit.2.1.2 _ (minPos_leftPt h₀ (carity := ctrlArity prog.vars)).1)
      ((minPos_leftPt h₀ (carity := ctrlArity prog.vars)).2 _ hinit.2.1.1)
  have htape : ∀ q : GamePt spec.B V M A, machPosn q → machDom (ctrlArity prog.vars) q →
      c₀.tape q = tapeOfAssign a₀ hdim (emptyAssign spec.B A) (emptyAssign spec.B A) q := by
    intro q hq _
    rcases hinit.2.2 q with hin | ⟨hno, -⟩
    · exact hin.2
    · exact absurd ⟨hq, rfl⟩ (hno _)
  have hsw : SweptCfg a₀ hdim prog.vars (emptyAssign spec.B A) (emptyAssign spec.B A) false
      (MachPh.sweepPh false false .start false) c₀ :=
    ⟨_, _, fun _ _ => rfl, hst, by rw [hhd]; exact trivial,
      by rw [hhd]; exact fun _ _ => h₀, htape⟩
  obtain ⟨ρ', σ', -, hgoal⟩ :=
    (sound_of_altWin h₀ hplays c₀ hw c₀ Relation.ReflTransGen.refl).sweepEx
      _ _ false false .start false (by simp) hsw
  exact ⟨cond false σ' ρ', hgoal.1, hgoal.2⟩

/-- **The machine accepts exactly when the game does.** Both halves of the
simulation, in one statement – and the whole of what `SO-GAME ≤ʳᶠᵒ[≤]
ATMAcceptSpace` needs of the machine. -/
theorem altAcceptsSpace_iff_accepts (h₀ : IsBot a₀)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q)) :
    (𝕄).AltAcceptsSpace true ↔ spec.Accepts A :=
  ⟨accepts_of_altAcceptsSpace h₀ hplays, altAcceptsSpace_of_accepts h₀ hplays⟩

end Play

end DescriptiveComplexity
