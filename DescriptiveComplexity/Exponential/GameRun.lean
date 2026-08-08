/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameMachine

/-!
# A configuration of the control, and the steps out of it

The bridge between the machine of `DescriptiveComplexity.Exponential.GameMachine`
and the two simulations: what it means for the machine to *sit at a phase of the
control*, that a step of the control graph is a step of the machine, and that
nothing else is.

## The configuration

`DescriptiveComplexity.CtrlCfg` bundles the four facts every phase of the
control keeps:

* the state is that phase, at a valuation it declares;
* the valuation is canonical – everything the phase does not declare is pinned,
  which is what makes it *unique* (`DescriptiveComplexity.eq_truncTuple`), and
  so what lets the backward reading name it;
* the head is on the sentinel `DescriptiveComplexity.MachPh.par` names, which is
  the invariant that replaces knowing where the head is;
* the tape holds the two assignments – at the positions, the only place it is
  ever read.

Being a conjunction of equations rather than a structure keeps it usable with
`rw` at the transparency the tagged-tuple types force.

## The two readings

`DescriptiveComplexity.ctrlCfg_step` builds a step from an edge of
`DescriptiveComplexity.MachPh.CtrlStep`, and
`DescriptiveComplexity.ctrlCfg_cases` reads every step back as such an edge –
the `_det`-style lemma the universal phases need, since a universal
configuration wins only when *every* successor does. Both are stated at an
arbitrary phase that is not a walk; the walks have their own runs.

## Winning along a walk

`DescriptiveComplexity.altWin_of_guardedChain` is what turns a run into a win:
a chain of steps all of whose sources are existential is won as soon as its last
configuration is. The runs of `GameMachine` produce exactly such a chain – the
guard being *the state has not changed* – which is why they carry it. Its
universal counterpart is `DescriptiveComplexity.altWin_of_walk`, which runs a
walk *backwards*: a family of configurations closed under the steps that carry
the walk on, every exit of which wins.

## One move, and then the prefix

`DescriptiveComplexity.altWin_of_steps` is the shape every phase of the control
has, whichever player owns it: a witness among the successors, always, and
*goodness of every successor*, only when the phase is universal – both read off
one `Good` predicate, into which the phase's own content goes.

Its first customers are here: the alternating prefix of a question, played one
variable at a time (`DescriptiveComplexity.altWin_pre`, with
`DescriptiveComplexity.qval` naming the restriction of the machine's tuple to
the question's variables), and the challenge round that settles the matrix –
`altWin_claim` into `altWin_check` into `altWin_seek` and `altWin_conc`. All of
it is parametric in `concOk` and `isTarget`; the program that supplies them is
`DescriptiveComplexity.Exponential.GameAsk`.
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### Winning along a chain of existential steps -/

section Chain

variable {U : Type} {N : ATMData U} {start : Bool}

/-- **A chain of existential steps wins if its last configuration does.** The
guard is what the walks of `DescriptiveComplexity.Exponential.GameMachine`
carry: a predicate true of every configuration a step is taken *from*. -/
theorem altWin_of_guardedChain {Guard : Config U → Prop}
    (hnu : ∀ e, Guard e → ¬ N.IsUniv start e.state) {c d : Config U}
    (h : Relation.ReflTransGen (fun x y => N.toTMData.Step x y ∧ Guard x) c d)
    (hd : N.AltWin start d) : N.AltWin start c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hd
  | head hstep _ ih => exact ATMData.AltWin.ex (hnu _ hstep.2) hstep.1 ih

/-- **A universal walk wins if every way out of it wins.** The family `F` is
closed under the steps that carry the walk on – each moving the head one
position – and a step that leaves it already wins; so the walk is won, by
induction on how far the head still has to go.

This is what a *universal* sweep needs, and it is the one place the simulation
runs a walk backwards: `AltWin.all` quantifies over every step, so the walk
cannot be summarized by its run. -/
theorem altWin_of_walk [Finite U] (hlin : IsLinOrd N.Le) {F : Config U → Prop}
    (hpos : ∀ c, F c → N.Posn c.head) (huniv : ∀ c, F c → N.IsUniv start c.state)
    (hex : ∀ c, F c → ∃ c', N.toTMData.Step c c')
    (hstep : ∀ c c', F c → N.toTMData.Step c c' →
      (F c' ∧ SuccPos N.Le N.Posn c.head c'.head) ∨ N.AltWin start c') :
    ∀ c, F c → N.AltWin start c := by
  have key : ∀ n c, Nat.card {x : U // N.Posn x} - bitRank N.Le N.Posn c.head ≤ n → F c →
      N.AltWin start c := by
    intro n
    induction n with
    | zero =>
      intro c hle hF
      have := bitRank_lt_card (Le := N.Le) (Posn := N.Posn) (hpos c hF)
      omega
    | succ n ih =>
      intro c hle hF
      refine ATMData.AltWin.all (huniv c hF) (hex c hF) (fun c' hst => ?_)
      rcases hstep c c' hF hst with ⟨hF', hsucc⟩ | hw
      · exact ih c' (by have := bitRank_succPos hlin hsucc; omega) hF'
      · exact hw
  exact fun c => key _ c le_rfl

end Chain

/-! ### A configuration of the control -/

/-- **The machine sits at a phase of the control**: the phase at a canonical
valuation, the head on the sentinel its parity names, and the tape holding the
two assignments – at the positions, the only place it is ever read. -/
def CtrlCfg {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] (a₀ : A)
    (hdim : blockArityBound B ≤ gameDim B V) (vars : GameQuestion → ℕ)
    (ρ σ : B.Assignment A) (p : MachPh V M) (vv : Fin (gameDim B V) → A)
    (c : Config (GamePt B V M A)) : Prop :=
  c.state = phasePt p vv ∧ Canon (MachPh.arity vars p) vv ∧ c.head = leftPt a₀ p.par ∧
    ∀ q : GamePt B V M A, machPosn q → machDom (ctrlArity vars) q →
      c.tape q = tapeOfAssign a₀ hdim ρ σ q

section Ctrl

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {ρ σ : B.Assignment A}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

/-- The head of a control configuration is a position, and it reads the left
mark. -/
theorem CtrlCfg.read (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (h : CtrlCfg a₀ hdim vars ρ σ p vv c) :
    c.tape c.head = markPt a₀ false := by
  rw [h.2.2.1, h.2.2.2 (leftPt a₀ p.par) (machPosn_leftPt a₀ p.par) (fun _ _ => h₀),
    tapeOfAssign_leftPt]

theorem CtrlCfg.posn {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (h₀ : IsBot a₀) (h : CtrlCfg a₀ hdim vars ρ σ p vv c) :
    (𝕄).Posn c.head := by
  rw [h.2.2.1]; exact ⟨trivial, fun _ _ => h₀⟩

/-- **A phase that declares no coordinate is entered at the constant
valuation** – which is every phase of the game proper, and the entry of every
question's prefix. -/
theorem ctrlCfg_of_arity_zero {p : MachPh V M} (harity : MachPh.arity vars p = 0)
    {w : Fin (gameDim B V) → A} {c : Config (GamePt B V M A)}
    (h : CtrlCfg a₀ hdim vars ρ σ p (truncTuple a₀ (MachPh.arity vars p) w) c) :
    CtrlCfg a₀ hdim vars ρ σ p (fun _ => a₀) c := by
  rwa [harity, truncTuple_zero] at h

/-- **An edge of the control graph is a step of the machine.** The tape is
untouched, the head bounces to the other sentinel, and the destination keeps
the transition's tuple up to the arity it declares – so the choice of the
transition *is* the choice of the coordinate a prefix phase writes. -/
theorem ctrlCfg_step (h₀ : IsBot a₀) {p p' : MachPh V M} {w vv : Fin (gameDim B V) → A}
    (hcs : MachPh.CtrlStep vars natoms p p') (hconc : p.kind = .conc → concOk p w)
    (hag : Agree (MachPh.arity vars p) w vv) {c : Config (GamePt B V M A)}
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) :
    ∃ c', (𝕄).toTMData.Step c c' ∧
      CtrlCfg a₀ hdim vars ρ σ p' (truncTuple a₀ (MachPh.arity vars p') w) c' := by
  refine ⟨_, ctrl_step h₀ hcs hconc c h.1 h.2.1 hag h.2.2.1 (h.read h₀), rfl,
    canon_truncTuple h₀ _ w, ?_, h.2.2.2⟩
  rw [MachPh.par_of_ctrlStep vars natoms hcs]

/-- **And nothing else is**: every step out of a control configuration is such
an edge. This is what a universal phase needs, since it wins only when all its
successors do; the destination's valuation is forced because the domain pins
whatever the phase does not declare. -/
theorem ctrlCfg_cases (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c c' : Config (GamePt B V M A)} (hsw : p.kind ≠ .sweep) (hrw : p.kind ≠ .rewind)
    (hsk : p.kind ≠ .seek) (h : CtrlCfg a₀ hdim vars ρ σ p vv c)
    (hstep : (𝕄).toTMData.Step c c') :
    ∃ (p' : MachPh V M) (w : Fin (gameDim B V) → A),
      MachPh.CtrlStep vars natoms p p' ∧ (p.kind = .conc → concOk p w) ∧
        Agree (MachPh.arity vars p) w vv ∧
        CtrlCfg a₀ hdim vars ρ σ p' (truncTuple a₀ (MachPh.arity vars p') w) c' := by
  obtain ⟨t, w, hrule, ⟨hsrc, -, hags⟩, -, ⟨hdst, hcd, had⟩, hwrite, hframe, hmove⟩ :=
    (game_step_iff c c').mp hstep
  -- the transition applies in the phase the configuration is in
  have hts : t.src = p := by
    have := hsrc.symm.trans (congrArg Prod.fst h.1)
    exact (Sum.inl.inj (Sum.inr.inj this))
  subst hts
  obtain ⟨hrd, hwr, hright, hcs, hcc⟩ := ctrl_cases hsw hrw hsk hrule
  -- the head bounces to the other sentinel
  have hsucc : SuccPos (𝕄).Le (𝕄).Posn (leftPt a₀ false) (leftPt a₀ true) :=
    succPos_leftPt h₀ (carity := ctrlArity vars)
  have hlin : IsLinOrd (𝕄).Le := isLinOrd_gameLe
  have hhead : c'.head = leftPt a₀ (!t.src.par) := by
    rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · have hpar : t.src.par = false := by
        rw [hright] at hr; simpa using hr
      rw [h.2.2.1, hpar] at hs
      rw [hpar]
      exact succPos_right_unique hlin hs hsucc
    · have hpar : t.src.par = true := by
        rw [hright] at hr; simpa using hr
      rw [h.2.2.1, hpar] at hs
      rw [hpar]
      exact succPos_left_unique hlin hs hsucc
  -- the tape is written back
  have htape : ∀ q : GamePt B V M A, machPosn q → machDom (ctrlArity vars) q →
      c'.tape q = tapeOfAssign a₀ hdim ρ σ q := by
    intro q hq hd
    by_cases hqe : q = c.head
    · rw [hqe, hwrite, hwr, gameSymPt_mark, h.2.2.1, tapeOfAssign_leftPt]
    · rw [hframe q hqe]
      exact h.2.2.2 q hq hd
  have hagv : Agree (MachPh.arity vars t.src) w vv := by rw [h.1] at hags; exact hags
  refine ⟨t.dst, w, hcs, hcc, hagv, ?_, canon_truncTuple h₀ _ w, ?_, htape⟩
  · rw [← eq_truncTuple h₀ hcd had]
    exact Prod.ext hdst rfl
  · rw [hhead, MachPh.par_of_ctrlStep vars natoms hcs]

/-! ### The two ends of a branch -/

/-- **A state of the control belongs to the universal player exactly when its
phase does** – read at a configuration rather than at a point. -/
theorem isUniv_ctrlCfg {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (h : CtrlCfg a₀ hdim vars ρ σ p vv c) :
    (𝕄).IsUniv true c.state ↔ MachPh.IsUniv pol p = true := by
  rw [h.1]
  exact gameMachine_isUniv hdim _ p vv

/-- **The accepting phase accepts.** -/
theorem acc_ctrlCfg {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hk : p.kind = .acc)
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) : (𝕄).Acc c.state :=
  ⟨p, by rw [h.1]; rfl, hk⟩

/-- **A concluding phase whose residual formula holds wins.** This is the one
place a question is settled by the *source structure* rather than by the tape:
`concOk` is a guard the interpretation writes, and a branch that fails it has
no transition at all – so it loses, the phase being existential. -/
theorem altWin_conc (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hk : p.kind = .conc) (hok : concOk p vv)
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) : (𝕄).AltWin true c := by
  obtain ⟨c', hstep, h'⟩ := ctrlCfg_step (natoms := natoms) (concOk := concOk)
    (isTarget := isTarget) (pol := pol) h₀ (p' := MachPh.accPh (!p.par))
    (by simp [MachPh.CtrlStep, hk]) (fun _ => hok) (fun _ _ => rfl) h
  refine ATMData.AltWin.ex ?_ hstep (ATMData.AltWin.acc (acc_ctrlCfg rfl h'))
  rw [isUniv_ctrlCfg (pol := pol) h, MachPh.isUniv_conc pol hk]
  exact Bool.false_ne_true

/-! ### One move of the control, whichever player owns it -/

/-- **A phase wins when the moves its owner may make win.** The existential
player needs one good successor, the universal player needs every successor to
be good – so the two halves of the hypothesis are a witness, always, and
*goodness of all successors*, only when the phase is universal. Both are read
off the same `Good` predicate, which is where the phase's own content goes.

This is the shape every phase of the control has, the prefix included: a
transition is a pair (destination phase, tuple), the tuple being the value a
prefix move writes. -/
theorem altWin_of_steps (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hsw : p.kind ≠ .sweep) (hrw : p.kind ≠ .rewind)
    (hsk : p.kind ≠ .seek) (hnc : p.kind ≠ .conc)
    {Good : MachPh V M → (Fin (gameDim B V) → A) → Prop}
    (hwit : ∃ p' w, MachPh.CtrlStep vars natoms p p' ∧
      Agree (MachPh.arity vars p) w vv ∧ Good p' w)
    (hall : MachPh.IsUniv pol p = true → ∀ p' w, MachPh.CtrlStep vars natoms p p' →
      Agree (MachPh.arity vars p) w vv → Good p' w)
    (hwin : ∀ p' w, MachPh.CtrlStep vars natoms p p' → Agree (MachPh.arity vars p) w vv →
      Good p' w → ∀ c', CtrlCfg a₀ hdim vars ρ σ p' (truncTuple a₀ (MachPh.arity vars p') w) c' →
        (𝕄).AltWin true c')
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) : (𝕄).AltWin true c := by
  by_cases hu : MachPh.IsUniv pol p = true
  · refine ATMData.AltWin.all ((isUniv_ctrlCfg (pol := pol) h).mpr hu) ?_ ?_
    · obtain ⟨p', w, hcs, hag, -⟩ := hwit
      obtain ⟨c', hstep, -⟩ := ctrlCfg_step (natoms := natoms) (concOk := concOk)
        (isTarget := isTarget) (pol := pol) h₀ hcs (fun hc => absurd hc hnc) hag h
      exact ⟨c', hstep⟩
    · intro c' hstep
      obtain ⟨p', w, hcs, -, hag, h'⟩ :=
        ctrlCfg_cases (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
          h₀ hsw hrw hsk h hstep
      exact hwin p' w hcs hag (hall hu p' w hcs hag) _ h'
  · obtain ⟨p', w, hcs, hag, hgood⟩ := hwit
    obtain ⟨c', hstep, h'⟩ := ctrlCfg_step (natoms := natoms) (concOk := concOk)
      (isTarget := isTarget) (pol := pol) h₀ hcs (fun hc => absurd hc hnc) hag h
    exact ATMData.AltWin.ex (fun hcon => hu ((isUniv_ctrlCfg (pol := pol) h).mp hcon)) hstep
      (hwin p' w hcs hag hgood _ h')

/-! ### The prefix, played one variable at a time -/

/-- **The question's own valuation**, read off the machine's tuple: the prefix
of `DescriptiveComplexity.QuestionData` quantifies over `Fin (vars q) → A`,
while the machine carries the whole tuple with junk above – which
`DescriptiveComplexity.altQuantFrom_congr_val` licenses. -/
noncomputable def qval (hV : ∀ q, vars q ≤ V) (q : GameQuestion)
    (vv : Fin (gameDim B V) → A) : Fin (vars q) → A :=
  pref ((hV q).trans (le_gameDim B V)) vv

omit [LinearOrder A] in
theorem qval_update (hV : ∀ q, vars q ≤ V) (q : GameQuestion) {j : ℕ}
    (hjD : j < gameDim B V) (hjm : j < vars q) (vv : Fin (gameDim B V) → A) (a : A) :
    qval hV q (Function.update vv ⟨j, hjD⟩ a) = Function.update (qval hV q vv) ⟨j, hjm⟩ a :=
  pref_update _ hjD hjm a

/-- **The prefix hands over to the claim** once every variable has been
written. The phase still has an owner, but only one successor, so the two
readings of `DescriptiveComplexity.altWin_of_steps` coincide. -/
theorem altWin_pre_last (h₀ : IsBot a₀) (hV : ∀ q, vars q ≤ V) {q : GameQuestion}
    {P : (Fin (vars q) → A) → Prop} {r par : Bool} {jj : Fin (V + 1)}
    (hjj : (jj : ℕ) = vars q)
    (hclaim : ∀ (par' : Bool) (vv' : Fin (gameDim B V) → A) (c' : Config (GamePt B V M A)),
      P (qval hV q vv') → CtrlCfg a₀ hdim vars ρ σ (MachPh.claimPh q r par') vv' c' →
        (𝕄).AltWin true c')
    {vv : Fin (gameDim B V) → A} {c : Config (GamePt B V M A)}
    (hpre : altQuantFrom (pol q) P (vars q) (qval hV q vv))
    (h : CtrlCfg a₀ hdim vars ρ σ (MachPh.prePh q r jj par) vv c) : (𝕄).AltWin true c := by
  have harity : MachPh.arity vars (MachPh.prePh q r jj par : MachPh V M) = vars q := by
    rw [MachPh.arity_prePh, hjj, min_self]
  have hcs : ∀ p' : MachPh V M, MachPh.CtrlStep vars natoms (MachPh.prePh q r jj par) p' ↔
      p' = MachPh.claimPh q r (!par) :=
    MachPh.ctrlStep_prePh_last vars natoms q r jj par (by rw [hjj]; omega)
  refine altWin_of_steps (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
    (pol := pol) (Good := fun p' _ => p' = MachPh.claimPh q r (!par)) h₀
    (by simp [MachPh.prePh]) (by simp [MachPh.prePh]) (by simp [MachPh.prePh])
    (by simp [MachPh.prePh]) ⟨_, vv, (hcs _).mpr rfl, fun _ _ => rfl, rfl⟩
    (fun _ p' w hstep _ => (hcs p').mp hstep) (fun p' w _ hag hgood c' h' => ?_) h
  subst hgood
  have hvv : truncTuple a₀
      (MachPh.arity vars (MachPh.claimPh q r (!par) : MachPh V M)) w = vv := by
    rw [MachPh.arity_claimPh]
    exact (eq_truncTuple h₀ (harity ▸ h.2.1) (harity ▸ hag)).symm
  rw [hvv] at h'
  have hP : P (qval hV q vv) := by
    rw [← altQuantFrom_last (pol := pol q) (P := P)]
    exact hpre
  exact hclaim _ vv c' hP h'

/-- **The alternating prefix of a question is played as moves.** The phase index
is the number of variables already written, the player its polarity names
chooses the next one – which is the choice of the transition, since the
transition's tuple *is* the value written – and the phase declares one more
coordinate than the one before, so `DescriptiveComplexity.truncTuple_succ`
turns the step into a single `Function.update` on either side of `qval`. -/
theorem altWin_pre (h₀ : IsBot a₀) (hV : ∀ q, vars q ≤ V) {q : GameQuestion}
    {P : (Fin (vars q) → A) → Prop} {r : Bool}
    (hclaim : ∀ (par' : Bool) (vv' : Fin (gameDim B V) → A) (c' : Config (GamePt B V M A)),
      P (qval hV q vv') → CtrlCfg a₀ hdim vars ρ σ (MachPh.claimPh q r par') vv' c' →
        (𝕄).AltWin true c') :
    ∀ (fuel j : ℕ), vars q - j ≤ fuel → j ≤ vars q → ∀ (par : Bool) (jj : Fin (V + 1)),
      (jj : ℕ) = j → ∀ (vv : Fin (gameDim B V) → A) (c : Config (GamePt B V M A)),
        altQuantFrom (pol q) P j (qval hV q vv) →
        CtrlCfg a₀ hdim vars ρ σ (MachPh.prePh q r jj par) vv c → (𝕄).AltWin true c := by
  have hqD : vars q ≤ gameDim B V := (hV q).trans (le_gameDim B V)
  intro fuel
  induction fuel with
  | zero =>
    intro j hf hj par jj hjj vv c hpre h
    have hje : j = vars q := by omega
    exact altWin_pre_last (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
      h₀ hV (hjj.trans hje) hclaim (hje ▸ hpre) h
  | succ fuel ih =>
    intro j hf hj par jj hjj vv c hpre h
    by_cases hjlt : j < vars q
    · have hjD : j < gameDim B V := lt_of_lt_of_le hjlt hqD
      have harity : MachPh.arity vars (MachPh.prePh q r jj par : MachPh V M) = j := by
        rw [MachPh.arity_prePh, hjj, min_eq_left hjlt.le]
      have hjV : j + 1 < V + 1 := by have := hV q; omega
      have hcs : ∀ p' : MachPh V M, MachPh.CtrlStep vars natoms (MachPh.prePh q r jj par) p' ↔
          p' = MachPh.prePh q r ⟨j + 1, hjV⟩ (!par) := by
        intro p'
        rw [MachPh.ctrlStep_prePh vars natoms q r jj par (by rw [hjj]; exact hjlt)]
        constructor
        · rintro ⟨j'', hj'', rfl⟩
          rw [show j'' = (⟨j + 1, hjV⟩ : Fin (V + 1)) from Fin.ext (by rw [hj'', hjj])]
        · rintro rfl
          exact ⟨⟨j + 1, hjV⟩, by rw [hjj], rfl⟩
      -- the value the next phase is given
      have hnext : ∃ a : A,
          altQuantFrom (pol q) P (j + 1) (Function.update (qval hV q vv) ⟨j, hjlt⟩ a) := by
        rcases hpol : pol q j with _ | _
        · exact ⟨a₀, (altQuantFrom_all hjlt hpol _).mp hpre a₀⟩
        · exact (altQuantFrom_ex hjlt hpol _).mp hpre
      obtain ⟨a, ha⟩ := hnext
      refine altWin_of_steps (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
        (pol := pol)
        (Good := fun p' w => p' = MachPh.prePh q r ⟨j + 1, hjV⟩ (!par) ∧
          altQuantFrom (pol q) P (j + 1)
            (Function.update (qval hV q vv) ⟨j, hjlt⟩ (w ⟨j, hjD⟩)))
        h₀ (by simp [MachPh.prePh]) (by simp [MachPh.prePh]) (by simp [MachPh.prePh])
        (by simp [MachPh.prePh])
        ⟨_, Function.update vv ⟨j, hjD⟩ a, (hcs _).mpr rfl, ?_, rfl, ?_⟩ ?_
        (fun p' w hstep hag hgood c' h' => ?_) h
      · intro l hl
        rw [harity] at hl
        exact (Function.update_of_ne
          (fun hc => absurd (congrArg Fin.val hc : (l : ℕ) = j) (by omega)) _ _).symm
      · rwa [Function.update_self]
      · -- the universal case: every value the transition may carry is answered
        intro hu p' w hstep hag
        refine ⟨(hcs p').mp hstep, ?_⟩
        have hpol : pol q j = false := by
          rw [MachPh.isUniv_pre pol rfl, MachPh.prePh, hjj] at hu
          simpa using hu
        exact (altQuantFrom_all hjlt hpol _).mp hpre _
      · -- one step: the tuple the next phase keeps is this one, updated at `j`
        obtain ⟨rfl, hgq⟩ := hgood
        have harity' : MachPh.arity vars (MachPh.prePh q r ⟨j + 1, hjV⟩ (!par) : MachPh V M) =
            j + 1 := by
          rw [MachPh.arity_prePh]
          change min (j + 1) (vars q) = j + 1
          exact min_eq_left (by omega)
        rw [harity', truncTuple_succ h₀ hjD (harity ▸ h.2.1) (harity ▸ hag)] at h'
        refine ih (j + 1) (by omega) (by omega) (!par) ⟨j + 1, hjV⟩ rfl _ c' ?_ h'
        rwa [qval_update hV q hjD hjlt]
    · have hje : j = vars q := by omega
      exact altWin_pre_last (natoms := natoms) (concOk := concOk) (isTarget := isTarget)
        h₀ hV (hjj.trans hje) hclaim (hje ▸ hpre) h

/-! ### Settling a question: the challenge round -/

variable [Finite A]

/-- **A seek whose cell exists wins.** The run either meets it – and the next
state accepts – or reaches the right sentinel having found none, which the
hypothesis forbids. Every configuration of the run is the same existential
phase, which is what the run's guarded chain carries. -/
theorem altWin_seek (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hk : p.kind = .seek) (harity : MachPh.arity vars p ≤ V)
    (hhit : ∃ q : GamePt B V M A, machPosn q ∧ machDom (ctrlArity vars) q ∧
      SeekHit a₀ isTarget p vv (tapeOfAssign a₀ hdim ρ σ) q)
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) : (𝕄).AltWin true c := by
  obtain ⟨c', hchain, -, hend⟩ :=
    seek_run (natoms := natoms) (concOk := concOk) (pol := pol) h₀ hk harity h.2.1 (ρ := ρ)
      (σ := σ) c h.1 h.2.2.1 (fun q hq => h.2.2.2 q hq.1 hq.2)
  refine altWin_of_guardedChain (Guard := fun x => x.state = c.state) (fun e he => ?_) hchain ?_
  · rw [he, isUniv_ctrlCfg (pol := pol) h, MachPh.isUniv_seek pol hk]
    exact Bool.false_ne_true
  · rcases hend with hacc | ⟨-, -, hnone⟩
    · exact ATMData.AltWin.acc ⟨MachPh.accPh false, by rw [hacc]; rfl, rfl⟩
    · obtain ⟨q, hq, hd, hhq⟩ := hhit
      exact absurd hhq (hnone q ⟨hq, hd⟩)

/-- **The challenge round wins.** `check` is universal: the existential player
has already claimed the whole vector of truth values, and every successor is
either a challenge – settled by a seek, which finds its cell exactly when the
claim was right – or the concluding transition, guarded by the residual
formula. So the round is won precisely when the claims are correct *and* the
residue holds, which is `DescriptiveComplexity.QuestionData.MatrixHolds`. -/
theorem altWin_check (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hk : p.kind = .check) (hV : ∀ q, vars q ≤ V)
    (hseek : ∀ k : Fin (M + 1), (k : ℕ) < natoms p.q →
      ∃ q : GamePt B V M A, machPosn q ∧ machDom (ctrlArity vars) q ∧
        SeekHit a₀ isTarget (MachPh.seekPh p.q p.r p.claims k (!p.par)) vv
          (tapeOfAssign a₀ hdim ρ σ) q)
    (hconc : concOk (MachPh.concPh p.q p.r p.claims (!p.par)) vv)
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) : (𝕄).AltWin true c := by
  have hac : MachPh.arity vars p = vars p.q := MachPh.arity_of_matrix vars (Or.inr (Or.inl hk))
  have hconcStep : MachPh.CtrlStep vars natoms p (MachPh.concPh p.q p.r p.claims (!p.par)) := by
    simp [MachPh.CtrlStep, hk]
  refine ATMData.AltWin.all ?_ ?_ ?_
  · rw [isUniv_ctrlCfg (pol := pol) h, MachPh.isUniv_check pol hk]
  · obtain ⟨c', hstep, -⟩ := ctrlCfg_step (natoms := natoms) (concOk := concOk)
      (isTarget := isTarget) (pol := pol) h₀ hconcStep
      (fun hc => absurd (hk.symm.trans hc) (by simp)) (fun _ _ => rfl) h
    exact ⟨c', hstep⟩
  · intro c' hstep
    obtain ⟨p', w, hcs, -, hag, h'⟩ :=
      ctrlCfg_cases (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
        h₀ (by simp [hk]) (by simp [hk]) (by simp [hk]) h hstep
    -- the successor keeps the valuation: both phases declare the same coordinates
    have hval : ∀ p'' : MachPh V M, MachPh.arity vars p'' = vars p.q →
        truncTuple a₀ (MachPh.arity vars p'') w = vv := by
      intro p'' hp''
      rw [hp'', ← hac]
      exact (eq_truncTuple h₀ h.2.1 hag).symm
    rw [MachPh.CtrlStep, hk] at hcs
    rcases hcs with ⟨k, hkk, rfl⟩ | rfl
    · rw [hval _ (MachPh.arity_seekPh vars _ _ _ _ _)] at h'
      exact altWin_seek (natoms := natoms) (concOk := concOk) (pol := pol) h₀ rfl
        (by rw [MachPh.arity_seekPh]; exact hV _) (hseek k hkk) h'
    · rw [hval _ (MachPh.arity_concPh vars _ _ _ _)] at h'
      exact altWin_conc (natoms := natoms) (isTarget := isTarget) (pol := pol) h₀ rfl hconc h'

/-- **Claiming the truth values wins, when a correct vector concludes.** The
claim is one existential move – finitely many vectors, so finitely many
transitions – and it is the whole of the matrix the machine ever computes: what
follows is a challenge round, `DescriptiveComplexity.altWin_check`. -/
theorem altWin_claim (h₀ : IsBot a₀) {p : MachPh V M} {vv : Fin (gameDim B V) → A}
    {c : Config (GamePt B V M A)} (hk : p.kind = .claim) (hV : ∀ q, vars q ≤ V)
    (b : Fin M → Bool)
    (hseek : ∀ k : Fin (M + 1), (k : ℕ) < natoms p.q →
      ∃ q : GamePt B V M A, machPosn q ∧ machDom (ctrlArity vars) q ∧
        SeekHit a₀ isTarget (MachPh.seekPh p.q p.r b k p.par) vv
          (tapeOfAssign a₀ hdim ρ σ) q)
    (hconc : concOk (MachPh.concPh p.q p.r b p.par) vv)
    (h : CtrlCfg a₀ hdim vars ρ σ p vv c) : (𝕄).AltWin true c := by
  have hac : MachPh.arity vars p = vars p.q := MachPh.arity_of_matrix vars (Or.inl hk)
  obtain ⟨c', hstep, h'⟩ := ctrlCfg_step (natoms := natoms) (concOk := concOk)
    (isTarget := isTarget) (pol := pol) (w := vv) h₀
    (p' := MachPh.checkPh p.q p.r b (!p.par))
    (by simp only [MachPh.CtrlStep, hk]; exact ⟨b, rfl⟩)
    (fun hc => absurd (hk.symm.trans hc) (by simp)) (fun _ _ => rfl) h
  rw [show MachPh.arity vars (MachPh.checkPh p.q p.r b (!p.par)) = MachPh.arity vars p from
    hac ▸ rfl, ← eq_truncTuple h₀ h.2.1 (fun _ _ => rfl)] at h'
  refine ATMData.AltWin.ex ?_ hstep
    (altWin_check (natoms := natoms) (concOk := concOk) (isTarget := isTarget) (pol := pol)
      h₀ rfl hV ?_ ?_ h')
  · rw [isUniv_ctrlCfg (pol := pol) h, MachPh.isUniv_claim pol hk]
    exact Bool.false_ne_true
  · simp only [MachPh.checkPh, Bool.not_not]
    exact hseek
  · simp only [MachPh.checkPh, Bool.not_not]
    exact hconc

end Ctrl

end DescriptiveComplexity
