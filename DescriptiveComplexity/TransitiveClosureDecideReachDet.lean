/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureDecideReach
import DescriptiveComplexity.TransitiveClosureReductionDet
import DescriptiveComplexity.WalkBudget

/-!
# Deciding reachability in a deterministic walk: a step budget

The atom case of the normal form for FO(DTC): the reachability relation of a
walk read through its determinization
(`DescriptiveComplexity.ParamTCSpec.det`) has a *functional*
`DescriptiveComplexity.Decider`
(`DescriptiveComplexity.ParamTCSpec.detReachDecider`). No inductive counting is
involved: the decider follows the one run of the walk from the first endpoint,
exits `yes` on standing at the second, and exits `no` when the run is stuck –
either because the walk has no step to take, or because a **step budget** is
exhausted.

The budget is the walk's own set of nodes: a second node, carried beside the
current one and advanced by one at every step in the mode-major lexicographic
order of nodes (`DescriptiveComplexity.ParamTCSpec.cntSuccF`), so that the run
may take exactly as many steps as there are nodes. A node reachable along a
functional relation is reached in fewer steps than that
(`DescriptiveComplexity.exists_iterate_lt_card`), so a run that has not
arrived when the budget runs out never will. This is the argument of
`DescriptiveComplexity.LOGSPACE_eq_coLOGSPACE`, with parameters.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- In a linear order, an element covers at most one element. -/
theorem covBy_right_unique {α : Type} [LinearOrder α] {a b c : α} (hb : a ⋖ b) (hc : a ⋖ c) :
    b = c := by
  rcases lt_trichotomy b c with h | h | h
  · exact absurd h (hc.2 hb.1)
  · exact h
  · exact absurd h (hb.2 hc.1)

namespace ParamTCSpec

variable {L : Language.{0, 0}} (W : ParamTCSpec (L.sum Language.order))

/-! ### The counter -/

/-- An arbitrary linear order on the modes, for the counter. -/
@[instance_reducible]
noncomputable def modeOrder : LinearOrder W.Mode := finiteLinearOrder W.Mode

variable (A : Type) [LinearOrder A] in
/-- The counter's values: the nodes of the walk, mode-major then
lexicographically on tuples. -/
abbrev Counter : Type := Lex (W.Mode × Lex (Fin W.k → A))

/-- The counter holding a mode and a tuple. -/
abbrev cntOf {A : Type} [LinearOrder A] (c : W.Mode) (r : Fin W.k → A) : W.Counter A :=
  toLex (c, toLex r)

/-- The coordinates of the decider: the current tuple, then the counter's. -/
abbrev DCoord : Type := Fin W.k ⊕ Fin W.k

/-! ### The formulas -/

/-- The variables of the determinized step, in the decider's step. -/
def runVar : (Fin W.k ⊕ Fin W.k) ⊕ Fin W.par → ((W.DCoord ⊕ W.DCoord) ⊕ W.AtomPar)
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (Sum.inl i))
  | Sum.inl (Sum.inr i) => Sum.inl (Sum.inr (Sum.inl i))
  | Sum.inr j => Sum.inr (W.parIx j)

open Classical in
/-- “The current tuple is the second endpoint, and the mode is its mode.” -/
noncomputable def atTgtF (mb m : W.Mode) :
    (L.sum Language.order).Formula (W.DCoord ⊕ W.AtomPar) :=
  if m = mb then
    Formula.iInf fun i =>
      Term.equal (Term.var (Sum.inl (Sum.inl i))) (Term.var (Sum.inr (W.rightIx i)))
  else ⊥

open Classical in
/-- **The counter advances by one**: same mode and the successor tuple, or the
next mode with the tuple going from the maximum to the minimum. -/
noncomputable def cntSuccF (c c' : W.Mode) :
    (L.sum Language.order).Formula ((W.DCoord ⊕ W.DCoord) ⊕ W.AtomPar) :=
  letI := W.modeOrder
  if c' = c then
    succTupF (fun i => Decider.curVar (Sum.inr i)) fun i => Decider.nextVar (Sum.inr i)
  else if c ⋖ c' then
    maxTupF (fun i => Decider.curVar (Sum.inr i)) ⊓ minTupF fun i => Decider.nextVar (Sum.inr i)
  else ⊥

/-- **The run step**: the determinized step of the walk, off the target, the
counter advancing. -/
noncomputable def runStepF (mb m c m' c' : W.Mode) :
    (L.sum Language.order).Formula ((W.DCoord ⊕ W.DCoord) ⊕ W.AtomPar) :=
  (W.detStep m m').relabel W.runVar ⊓ ∼((W.atTgtF mb m).relabel (Sum.map Sum.inl id)) ⊓
    W.cntSuccF c c'

/-- The variables of a step, with the next tuple quantified. -/
def exVar : (W.DCoord ⊕ W.DCoord) ⊕ W.AtomPar → (W.DCoord ⊕ W.AtomPar) ⊕ W.DCoord
  | Sum.inl (Sum.inl c) => Sum.inl (Sum.inl c)
  | Sum.inl (Sum.inr c) => Sum.inr c
  | Sum.inr g => Sum.inl (Sum.inr g)

/-- “Some run step is available.” -/
noncomputable def hasStepF (mb m c : W.Mode) :
    (L.sum Language.order).Formula (W.DCoord ⊕ W.AtomPar) :=
  Formula.iSup fun p : W.Mode × W.Mode =>
    Formula.iExs W.DCoord ((W.runStepF mb m c p.1 p.2).relabel W.exVar)

open Classical in
/-- **The decider of reachability in the deterministic reading** between two
modes, at the two endpoints and the parameters: it enters the walk at the
first endpoint with the counter at its least value, follows the one run,
exits `yes` on standing at the second endpoint and `no` when no run step is
available. -/
@[reducible]
noncomputable def detReachDecider (ma mb : W.Mode) : Decider L W.AtomPar where
  Mode := Option (W.Mode × W.Mode)
  Coord := W.DCoord
  start := none
  step m n :=
    match m, n with
    | none, some (m, c) =>
        letI := W.modeOrder
        if m = ma ∧ ∀ c' : W.Mode, c ≤ c' then
          (Formula.iInf fun i : Fin W.k =>
            Term.equal (Term.var (Decider.nextVar (Sum.inl i))) (Term.var (Sum.inr (W.leftIx i)))) ⊓
            minTupF fun i => Decider.nextVar (Sum.inr i)
        else ⊥
    | some (m, c), some (m', c') => W.runStepF mb m c m' c'
    | _, none => ⊥
  exit m o :=
    match m, o with
    | some (m, _), true => W.atTgtF mb m
    | some (m, c), false => ∼(W.atTgtF mb m) ⊓ ∼(W.hasStepF mb m c)
    | none, _ => ⊥

/-! ### Semantics of the formulas -/

section Semantics

variable {A : Type} [L.Structure A] [LinearOrder A] (ma mb : W.Mode) (w : W.AtomPar → A)

theorem realize_atTgtF (m : W.Mode) (t : W.DCoord → A) :
    (W.atTgtF mb m).Realize (Sum.elim t w) ↔ m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx := by
  classical
  rw [atTgtF]
  split_ifs with h
  · rw [Formula.realize_iInf, and_iff_right h]
    simp only [Formula.realize_equal, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

variable [Nonempty A]

theorem realize_cntSuccF (c c' : W.Mode) (t t' : W.DCoord → A) :
    (W.cntSuccF c c').Realize (Sum.elim (Sum.elim t t') w) ↔
      (letI := W.modeOrder; W.cntOf c (t ∘ Sum.inr) ⋖ W.cntOf c' (t' ∘ Sum.inr)) := by
  classical
  let := W.modeOrder
  rw [cntSuccF, cntOf, cntOf, prodLex_covBy_iff]
  split_ifs with h1 h2
  · subst h1
    rw [realize_succTupF, tupSucc_iff_covBy]
    constructor
    · intro h
      exact Or.inl ⟨rfl, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd rfl h.ne
  · rw [Formula.realize_inf, realize_maxTupF, realize_minTupF]
    constructor
    · rintro ⟨hmax, hmin⟩
      exact Or.inr ⟨h2, tup_isTop_iff.mpr hmax, tup_isBot_iff.mpr hmin⟩
    · rintro (⟨h, -⟩ | ⟨-, hmax, hmin⟩)
      · exact absurd h.symm h1
      · exact ⟨tup_isTop_iff.mp hmax, tup_isBot_iff.mp hmin⟩
  · simp only [Formula.realize_bot, false_iff, not_or, not_and]
    exact ⟨fun h => absurd h.symm h1, fun h => absurd h h2⟩

theorem realize_runStepF (m c m' c' : W.Mode) (t t' : W.DCoord → A) :
    (W.runStepF mb m c m' c').Realize (Sum.elim (Sum.elim t t') w) ↔
      W.det.StepAt (w ∘ W.parIx) (m, t ∘ Sum.inl) (m', t' ∘ Sum.inl) ∧
        ¬(m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx) ∧
        (letI := W.modeOrder; W.cntOf c (t ∘ Sum.inr) ⋖ W.cntOf c' (t' ∘ Sum.inr)) := by
  rw [runStepF, Formula.realize_inf, Formula.realize_inf, Formula.realize_relabel,
    Formula.realize_not, Formula.realize_relabel, and_assoc, W.realize_cntSuccF w]
  refine and_congr (iff_of_eq (congrArg (Formula.Realize (M := A) (W.detStep m m'))
    (funext fun i => ?_))) (and_congr (not_congr ?_) Iff.rfl)
  · rcases i with (i | i) | i <;> rfl
  · refine Iff.trans (iff_of_eq (congrArg (Formula.Realize (M := A) (W.atTgtF mb m))
      (funext fun i => ?_))) (W.realize_atTgtF mb w m t)
    rcases i with i | i <;> rfl

/-! ### Steps and exits of the decider -/

omit [Nonempty A] in
theorem detReachDecider_stepAt_none_some (m c : W.Mode) (t t' : W.DCoord → A) :
    (W.detReachDecider ma mb).StepAt w (none, t) (some (m, c), t') ↔
      m = ma ∧ (letI := W.modeOrder; ∀ c' : W.Mode, c ≤ c') ∧ t' ∘ Sum.inl = w ∘ W.leftIx ∧
        ∀ (i : Fin W.k) (a : A), t' (Sum.inr i) ≤ a := by
  classical
  let := W.modeOrder
  have hstep : (W.detReachDecider ma mb).step none (some (m, c)) =
      if m = ma ∧ ∀ c' : W.Mode, c ≤ c' then
        (Formula.iInf fun i : Fin W.k =>
          Term.equal (Term.var (Decider.nextVar (Sum.inl i))) (Term.var (Sum.inr (W.leftIx i)))) ⊓
          minTupF fun i => Decider.nextVar (Sum.inr i)
      else ⊥ := rfl
  unfold Decider.StepAt
  rw [hstep]
  split_ifs with h
  · rw [Formula.realize_inf, Formula.realize_iInf, realize_minTupF, and_iff_right h.1,
      and_iff_right h.2]
    simp only [Formula.realize_equal, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    exact and_congr ⟨fun h => funext h, fun h i => congrFun h i⟩ Iff.rfl
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h1 h2 => absurd ⟨h1, h2⟩ h

theorem detReachDecider_stepAt_some_some (m c m' c' : W.Mode) (t t' : W.DCoord → A) :
    (W.detReachDecider ma mb).StepAt w (some (m, c), t) (some (m', c'), t') ↔
      W.det.StepAt (w ∘ W.parIx) (m, t ∘ Sum.inl) (m', t' ∘ Sum.inl) ∧
        ¬(m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx) ∧
        (letI := W.modeOrder; W.cntOf c (t ∘ Sum.inr) ⋖ W.cntOf c' (t' ∘ Sum.inr)) :=
  W.realize_runStepF mb w m c m' c' t t'

omit [Nonempty A] in
theorem detReachDecider_not_stepAt_none (a : (W.detReachDecider ma mb).Node A)
    (t' : W.DCoord → A) : ¬(W.detReachDecider ma mb).StepAt w a (none, t') := by
  obtain ⟨m, t⟩ := a
  rcases m with _ | ⟨m, c⟩ <;> exact fun h => h

omit [Nonempty A] in
theorem detReachDecider_exitAt_some_true (m c : W.Mode) (t : W.DCoord → A) :
    (W.detReachDecider ma mb).ExitAt w (some (m, c), t) true ↔
      m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx :=
  W.realize_atTgtF mb w m t

omit [Nonempty A] in
theorem detReachDecider_exitAt_some_false (m c : W.Mode) (t : W.DCoord → A) :
    (W.detReachDecider ma mb).ExitAt w (some (m, c), t) false ↔
      ¬(m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx) ∧
        ¬∃ b, (W.detReachDecider ma mb).StepAt w (some (m, c), t) b := by
  have hexit : (W.detReachDecider ma mb).exit (some (m, c)) false =
      ∼(W.atTgtF mb m) ⊓ ∼(W.hasStepF mb m c) := rfl
  unfold Decider.ExitAt
  rw [hexit, Formula.realize_inf, Formula.realize_not, Formula.realize_not, W.realize_atTgtF mb w]
  refine and_congr Iff.rfl (not_congr ?_)
  rw [hasStepF, Formula.realize_iSup]
  constructor
  · rintro ⟨p, hp⟩
    rw [Formula.realize_iExs] at hp
    obtain ⟨u, hu⟩ := hp
    refine ⟨(some p, u), ?_⟩
    rw [Formula.realize_relabel] at hu
    change (W.runStepF mb m c p.1 p.2).Realize (Sum.elim (Sum.elim t u) w)
    refine (iff_of_eq (congrArg (Formula.Realize (M := A) _) (funext fun i => ?_))).mp hu
    rcases i with (i | i) | i <;> rfl
  · rintro ⟨⟨mb', u⟩, hb⟩
    rcases mb' with _ | p
    · exact absurd hb (W.detReachDecider_not_stepAt_none ma mb w _ u)
    · refine ⟨p, ?_⟩
      rw [Formula.realize_iExs]
      refine ⟨u, ?_⟩
      rw [Formula.realize_relabel]
      change (W.runStepF mb m c p.1 p.2).Realize (Sum.elim (Sum.elim t u) w) at hb
      refine (iff_of_eq (congrArg (Formula.Realize (M := A) _) (funext fun i => ?_))).mp hb
      rcases i with (i | i) | i <;> rfl

omit [Nonempty A] in
theorem detReachDecider_not_exitAt_none (t : W.DCoord → A) (o : Bool) :
    ¬(W.detReachDecider ma mb).ExitAt w (none, t) o := by
  cases o <;> exact fun h => h

/-! ### The run -/

variable [Finite A]

/-- The one step of the determinized walk, as a function. -/
noncomputable abbrev detNext : W.Node A → W.Node A := stepNext (W.det.StepAt (w ∘ W.parIx))

omit [Nonempty A] [Finite A] in
theorem detNext_functional (u v v' : W.Node A) (hv : W.det.StepAt (w ∘ W.parIx) u v)
    (hv' : W.det.StepAt (w ∘ W.parIx) u v') : v = v' :=
  det_functional (s := W) _ u v v' hv hv'

/-- What a node of the decider records: the current node is the `i`-th of the
run from the first endpoint, the counter has rank `i`, and no earlier node of
the run was the second endpoint. -/
def DetInv (i : ℕ) (m c : W.Mode) (t : W.DCoord → A) : Prop :=
  (m, t ∘ Sum.inl) = (W.detNext w)^[i] (ma, w ∘ W.leftIx) ∧
    (letI := W.modeOrder; orank (W.cntOf c (t ∘ Sum.inr)) = i) ∧
    ∀ j < i, (W.detNext w)^[j] (ma, w ∘ W.leftIx) ≠ (mb, w ∘ W.rightIx)

omit [Nonempty A] [Finite A] in
/-- Reachability in the determinized walk is iteration of its step. -/
theorem det_reachAt_iff :
    W.det.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx) ↔
      ∃ n, (W.detNext w)^[n] (ma, w ∘ W.leftIx) = (mb, w ∘ W.rightIx) :=
  reach_iff_iterate (W.detNext_functional w) _ _

omit [L.Structure A] [LinearOrder A] [Nonempty A] [Finite A] in
theorem card_counter : Nat.card (W.Counter A) = Nat.card (W.Node A) :=
  Nat.card_congr (toLex.symm.trans (Equiv.prodCongr (Equiv.refl _) toLex.symm))

/-- **A stuck run does not reach the target.** -/
theorem not_reach_of_stuck {i : ℕ} {m c : W.Mode} {t : W.DCoord → A}
    (hinv : W.DetInv ma mb w i m c t) (htgt : ¬(m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx))
    (hstuck : ¬∃ b, (W.detReachDecider ma mb).StepAt w (some (m, c), t) b) :
    ¬W.det.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx) := by
  let := W.modeOrder
  have : Nonempty W.Mode := ⟨ma⟩
  obtain ⟨hi, hr, hne⟩ := hinv
  have hcur : (m, t ∘ Sum.inl) ≠ (mb, w ∘ W.rightIx) := fun h =>
    htgt ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  intro hreach
  obtain ⟨n, hn⟩ := (W.det_reachAt_iff ma mb w).mp hreach
  obtain ⟨n, hncard, hn⟩ := exists_iterate_lt_card ⟨n, hn⟩
  by_cases hsucc : ∃ b, W.det.StepAt (w ∘ W.parIx) (m, t ∘ Sum.inl) b
  · by_cases htop : ∀ u : W.Counter A, u ≤ W.cntOf c (t ∘ Sum.inr)
    · have hrank := orank_isTop htop
      rw [hr, W.card_counter] at hrank
      rcases lt_trichotomy n i with h | rfl | h
      · exact hne n h hn
      · exact hcur (hi.trans hn)
      · omega
    · obtain ⟨κ', hlt, hnb⟩ := exists_gt_of_not_max htop
      obtain ⟨⟨m', u'⟩, hb⟩ := hsucc
      refine hstuck ⟨(some (m', (ofLex κ').1), Sum.elim u' (ofLex (ofLex κ').2)), ?_⟩
      refine (W.detReachDecider_stepAt_some_some ma mb w m c m' _ t _).mpr
        ⟨by simpa using hb, htgt, ?_⟩
      exact ⟨hlt, fun a h1 h2 => hnb a ⟨h1, h2⟩⟩
  · have hself : W.detNext w (m, t ∘ Sum.inl) = (m, t ∘ Sum.inl) := stepNext_eq_self hsucc
    have hconst : ∀ j, (W.detNext w)^[i + j] (ma, w ∘ W.leftIx) = (m, t ∘ Sum.inl) := by
      intro j
      induction j with
      | zero => exact hi.symm
      | succ j ih => rw [← Nat.add_assoc, Function.iterate_succ_apply', ih, hself]
    rcases lt_or_ge n i with h | h
    · exact hne n h hn
    · have := hconst (n - i)
      rw [Nat.add_sub_cancel' h, hn] at this
      exact hcur this.symm

/-- **The run decides**, from any node the invariant admits: it exits `yes` if
the target is reachable, `no` if not. Proved downwards along the counter. -/
theorem detReachDecider_run (κ : W.Counter A) :
    ∀ (m c : W.Mode) (t : W.DCoord → A) (i : ℕ),
      (letI := W.modeOrder; W.cntOf c (t ∘ Sum.inr) = κ) → W.DetInv ma mb w i m c t →
        (W.det.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx) →
          ∃ b, (W.detReachDecider ma mb).ReachAt w (some (m, c), t) b ∧
            (W.detReachDecider ma mb).ExitAt w b true) ∧
        (¬W.det.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx) →
          ∃ b, (W.detReachDecider ma mb).ReachAt w (some (m, c), t) b ∧
            (W.detReachDecider ma mb).ExitAt w b false) := by
  let := W.modeOrder
  have : Nonempty W.Mode := ⟨ma⟩
  induction κ using order_induction_down with
  | hmax κ hκ =>
    intro m c t i hκt hinv
    by_cases htgt : m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx
    · have hreach : W.det.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx) := by
        rw [W.det_reachAt_iff ma mb w]
        exact ⟨i, hinv.1.symm.trans (by rw [htgt.1, htgt.2])⟩
      exact ⟨fun _ => ⟨_, Relation.ReflTransGen.refl,
        (W.detReachDecider_exitAt_some_true ma mb w m c t).mpr htgt⟩, fun h => absurd hreach h⟩
    · have hstuck : ¬∃ b, (W.detReachDecider ma mb).StepAt w (some (m, c), t) b := by
        rintro ⟨⟨mb', u⟩, hb⟩
        rcases mb' with _ | ⟨m', c'⟩
        · exact W.detReachDecider_not_stepAt_none ma mb w _ u hb
        · obtain ⟨-, -, hcov⟩ := (W.detReachDecider_stepAt_some_some ma mb w m c m' c' t u).mp hb
          rw [hκt] at hcov
          exact absurd (hκ _) (not_le.mpr hcov.1)
      exact ⟨fun h => absurd h (W.not_reach_of_stuck ma mb w hinv htgt hstuck),
        fun _ => ⟨_, Relation.ReflTransGen.refl,
          (W.detReachDecider_exitAt_some_false ma mb w m c t).mpr ⟨htgt, hstuck⟩⟩⟩
  | hstep κ κ' hlt hnb ih =>
    intro m c t i hκt hinv
    by_cases htgt : m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx
    · have hreach : W.det.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx) := by
        rw [W.det_reachAt_iff ma mb w]
        exact ⟨i, hinv.1.symm.trans (by rw [htgt.1, htgt.2])⟩
      exact ⟨fun _ => ⟨_, Relation.ReflTransGen.refl,
        (W.detReachDecider_exitAt_some_true ma mb w m c t).mpr htgt⟩, fun h => absurd hreach h⟩
    · by_cases hsucc : ∃ b, W.det.StepAt (w ∘ W.parIx) (m, t ∘ Sum.inl) b
      · obtain ⟨⟨m', u'⟩, hb⟩ := hsucc
        have hcov : W.cntOf c (t ∘ Sum.inr) ⋖ κ' := hκt ▸ ⟨hlt, fun a h1 h2 => hnb a ⟨h1, h2⟩⟩
        set c' := (ofLex κ').1
        set r' : Fin W.k → A := ofLex (ofLex κ').2
        have hκ' : W.cntOf c' r' = κ' := rfl
        have hstep : (W.detReachDecider ma mb).StepAt w (some (m, c), t)
            (some (m', c'), Sum.elim u' r') :=
          (W.detReachDecider_stepAt_some_some ma mb w m c m' c' t _).mpr
            ⟨by simpa using hb, htgt, by simpa [hκ'] using hcov⟩
        have hinv' : W.DetInv ma mb w (i + 1) m' c' (Sum.elim u' r') := by
          obtain ⟨hi, hr, hne⟩ := hinv
          refine ⟨?_, ?_, fun j hj => ?_⟩
          · rw [Function.iterate_succ_apply', ← hi]
            exact (stepNext_eq (W.detNext_functional w) hb).symm
          · change orank (W.cntOf c' r') = i + 1
            rw [hκ', orank_covBy hcov, hr]
          · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | rfl
            · exact hne j h
            · rw [← hi]
              exact fun h => htgt ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
        obtain ⟨h1, h2⟩ := ih m' c' (Sum.elim u' r') (i + 1) hκ' hinv'
        exact ⟨fun h => (h1 h).imp fun b hb => ⟨Relation.ReflTransGen.head hstep hb.1, hb.2⟩,
          fun h => (h2 h).imp fun b hb => ⟨Relation.ReflTransGen.head hstep hb.1, hb.2⟩⟩
      · have hstuck : ¬∃ b, (W.detReachDecider ma mb).StepAt w (some (m, c), t) b := by
          rintro ⟨⟨mb', u⟩, hb⟩
          rcases mb' with _ | ⟨m', c'⟩
          · exact W.detReachDecider_not_stepAt_none ma mb w _ u hb
          · obtain ⟨hs, -, -⟩ :=
              (W.detReachDecider_stepAt_some_some ma mb w m c m' c' t u).mp hb
            exact hsucc ⟨_, hs⟩
        exact ⟨fun h => absurd h (W.not_reach_of_stuck ma mb w hinv htgt hstuck),
          fun _ => ⟨_, Relation.ReflTransGen.refl,
            (W.detReachDecider_exitAt_some_false ma mb w m c t).mpr ⟨htgt, hstuck⟩⟩⟩

/-- What the decider may have reached from its start: its start, or a node
the invariant admits. -/
theorem detReachDecider_inv (t : W.DCoord → A) {b : (W.detReachDecider ma mb).Node A}
    (h : (W.detReachDecider ma mb).ReachAt w (none, t) b) :
    b = (none, t) ∨ ∃ (m c : W.Mode) (t' : W.DCoord → A) (i : ℕ),
      b = (some (m, c), t') ∧ W.DetInv ma mb w i m c t' := by
  let := W.modeOrder
  have : Nonempty W.Mode := ⟨ma⟩
  refine reach_invariant (P := fun b => b = (none, t) ∨ ∃ (m c : W.Mode) (t' : W.DCoord → A)
    (i : ℕ), b = (some (m, c), t') ∧ W.DetInv ma mb w i m c t') (fun a b ha hab => ?_) h
    (Or.inl rfl)
  obtain ⟨mb', tb⟩ := b
  rcases mb' with _ | ⟨m', c'⟩
  · exact absurd hab (W.detReachDecider_not_stepAt_none ma mb w a tb)
  rcases ha with rfl | ⟨m, c, t', i, rfl, hi, hr, hne⟩
  · obtain ⟨rfl, hc, hl, hmin⟩ := (W.detReachDecider_stepAt_none_some ma mb w m' c' t tb).mp hab
    refine Or.inr ⟨m', c', tb, 0, rfl, by rw [hl]; rfl, ?_,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    exact orank_eq_zero (prodLex_isBot_iff.mpr ⟨hc, tup_isBot_iff.mpr hmin⟩)
  · obtain ⟨hs, htgt, hcov⟩ :=
      (W.detReachDecider_stepAt_some_some ma mb w m c m' c' t' tb).mp hab
    refine Or.inr ⟨m', c', tb, i + 1, rfl, ?_, ?_, fun j hj => ?_⟩
    · rw [Function.iterate_succ_apply', ← hi]
      exact (stepNext_eq (W.detNext_functional w) hs).symm
    · rw [orank_covBy hcov, hr]
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | rfl
      · exact hne j h
      · rw [← hi]
        exact fun h => htgt ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- **The decider decides reachability in the deterministic reading** between
its two modes, at the two endpoints and the parameters. -/
theorem decides_detReachDecider :
    (W.detReachDecider ma mb).Decides w
      (W.det.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx)) := by
  let := W.modeOrder
  have : Nonempty W.Mode := ⟨ma⟩
  intro t
  obtain ⟨cmin, -, hcmin⟩ := (Finite.to_wellFoundedLT (α := W.Mode)).wf.has_min Set.univ
    ⟨ma, Set.mem_univ _⟩
  have hcmin' : ∀ c' : W.Mode, cmin ≤ c' := fun c' => not_lt.mp (hcmin c' (Set.mem_univ c'))
  obtain ⟨amin, -, hamin⟩ := (Finite.to_wellFoundedLT (α := A)).wf.has_min Set.univ
    ⟨Classical.arbitrary A, Set.mem_univ _⟩
  have hamin' : ∀ a : A, amin ≤ a := fun a => not_lt.mp (hamin a (Set.mem_univ a))
  have hinit : (W.detReachDecider ma mb).StepAt w (none, t)
      (some (ma, cmin), Sum.elim (w ∘ W.leftIx) fun _ => amin) :=
    (W.detReachDecider_stepAt_none_some ma mb w ma cmin t _).mpr
      ⟨rfl, hcmin', by simp, fun _ a => hamin' a⟩
  have hinv : W.DetInv ma mb w 0 ma cmin (Sum.elim (w ∘ W.leftIx) fun _ => amin) :=
    ⟨by simp, orank_eq_zero (prodLex_isBot_iff.mpr ⟨hcmin', tup_isBot_iff.mpr
      fun _ a => hamin' a⟩), fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  obtain ⟨hyes, hno⟩ := W.detReachDecider_run ma mb w _ ma cmin _ 0 rfl hinv
  have hout : ∀ o, (W.detReachDecider ma mb).Out w t o →
      ∃ (m c : W.Mode) (t' : W.DCoord → A) (i : ℕ), W.DetInv ma mb w i m c t' ∧
        (W.detReachDecider ma mb).ExitAt w (some (m, c), t') o := by
    rintro o ⟨b, hb, he⟩
    rcases W.detReachDecider_inv ma mb w t hb with rfl | ⟨m, c, t', i, rfl, hinv⟩
    · exact absurd he (W.detReachDecider_not_exitAt_none ma mb w t o)
    · exact ⟨m, c, t', i, hinv, he⟩
  constructor
  · constructor
    · intro h
      obtain ⟨m, c, t', i, hinv, he⟩ := hout true h
      obtain ⟨hm, ht⟩ := (W.detReachDecider_exitAt_some_true ma mb w m c t').mp he
      rw [W.det_reachAt_iff ma mb w]
      exact ⟨i, hinv.1.symm.trans (by rw [ht, hm])⟩
    · intro h
      obtain ⟨b, hb, he⟩ := hyes h
      exact ⟨b, Relation.ReflTransGen.head hinit hb, he⟩
  · constructor
    · intro h
      obtain ⟨m, c, t', i, hinv, he⟩ := hout false h
      obtain ⟨htgt, hstuck⟩ := (W.detReachDecider_exitAt_some_false ma mb w m c t').mp he
      exact W.not_reach_of_stuck ma mb w hinv htgt hstuck
    · intro h
      obtain ⟨b, hb, he⟩ := hno h
      exact ⟨b, Relation.ReflTransGen.head hinit hb, he⟩

omit [Finite A] in
/-- **The decider is functional.** -/
theorem functional_detReachDecider : (W.detReachDecider ma mb).Functional A := by
  let := W.modeOrder
  refine Decider.functional_of ?_ ?_ ?_
  · rintro w ⟨m, t⟩ ⟨mb₁, t₁⟩ ⟨mb₂, t₂⟩ h₁ h₂
    rcases mb₁ with _ | ⟨m₁, c₁⟩
    · exact absurd h₁ (W.detReachDecider_not_stepAt_none ma mb w _ t₁)
    rcases mb₂ with _ | ⟨m₂, c₂⟩
    · exact absurd h₂ (W.detReachDecider_not_stepAt_none ma mb w _ t₂)
    rcases m with _ | ⟨m, c⟩
    · obtain ⟨hm₁', hc₁, hl₁, hm₁⟩ :=
        (W.detReachDecider_stepAt_none_some ma mb w m₁ c₁ t t₁).mp h₁
      obtain ⟨hm₂', hc₂, hl₂, hm₂⟩ :=
        (W.detReachDecider_stepAt_none_some ma mb w m₂ c₂ t t₂).mp h₂
      refine Prod.ext (congrArg some (Prod.ext (hm₁'.trans hm₂'.symm)
        (le_antisymm (hc₁ c₂) (hc₂ c₁)))) (funext fun i => ?_)
      rcases i with i | i
      · exact (congrFun hl₁ i).trans (congrFun hl₂ i).symm
      · exact le_antisymm (hm₁ i _) (hm₂ i _)
    · obtain ⟨hs₁, -, hc₁⟩ := (W.detReachDecider_stepAt_some_some ma mb w m c m₁ c₁ t t₁).mp h₁
      obtain ⟨hs₂, -, hc₂⟩ := (W.detReachDecider_stepAt_some_some ma mb w m c m₂ c₂ t t₂).mp h₂
      have hn := W.detNext_functional w _ _ _ hs₁ hs₂
      have hκ := covBy_right_unique hc₁ hc₂
      have hκ1 : c₁ = c₂ := congrArg (fun κ : W.Counter A => (ofLex κ).1) hκ
      have hκ2 : t₁ ∘ Sum.inr = t₂ ∘ Sum.inr :=
        congrArg (fun κ : W.Counter A => (ofLex (ofLex κ).2 : Fin W.k → A)) hκ
      refine Prod.ext (congrArg some (Prod.ext (congrArg Prod.fst hn : m₁ = m₂) hκ1))
        (funext fun i => ?_)
      rcases i with i | i
      · exact congrFun (congrArg Prod.snd hn) i
      · exact congrFun hκ2 i
  · rintro w ⟨m, t⟩ ⟨mb', tb⟩ o hb he
    rcases m with _ | ⟨m, c⟩
    · exact W.detReachDecider_not_exitAt_none ma mb w t o he
    rcases mb' with _ | ⟨m', c'⟩
    · exact W.detReachDecider_not_stepAt_none ma mb w _ tb hb
    obtain ⟨-, htgt, -⟩ := (W.detReachDecider_stepAt_some_some ma mb w m c m' c' t tb).mp hb
    cases o
    · exact ((W.detReachDecider_exitAt_some_false ma mb w m c t).mp he).2 ⟨_, hb⟩
    · exact htgt ((W.detReachDecider_exitAt_some_true ma mb w m c t).mp he)
  · rintro w ⟨m, t⟩ h₁ h₂
    rcases m with _ | ⟨m, c⟩
    · exact W.detReachDecider_not_exitAt_none ma mb w t true h₁
    · exact ((W.detReachDecider_exitAt_some_false ma mb w m c t).mp h₂).1
        ((W.detReachDecider_exitAt_some_true ma mb w m c t).mp h₁)

end Semantics

end ParamTCSpec

/-! ### The deciders of a family, read deterministically -/

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily (L.sum Language.order))

/-- **The deterministic reachability deciders of a family**: one per relation
variable of its block, deciding the reachability relations of the family's
deterministic reading. -/
noncomputable def detReachDeciders (q : F.block.ι) : Decider L (Fin (F.block.arity q)) :=
  (F.spec q.1).detReachDecider q.2.1 q.2.2

/-- **The deciders decide the deterministic reading's reachability
relations.** -/
theorem decides_detReachDeciders (A : Type) [L.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] (q : F.block.ι) (w : Fin (F.block.arity q) → A) :
    (F.detReachDeciders q).Decides w (F.det.reachAssign A q w) :=
  (F.spec q.1).decides_detReachDecider q.2.1 q.2.2 w

/-- **The deciders are functional.** -/
theorem functional_detReachDeciders (A : Type) [L.Structure A] [LinearOrder A] [Nonempty A]
    (q : F.block.ι) : (F.detReachDeciders q).Functional A :=
  (F.spec q.1).functional_detReachDecider q.2.1 q.2.2

end TCFamily

end DescriptiveComplexity
