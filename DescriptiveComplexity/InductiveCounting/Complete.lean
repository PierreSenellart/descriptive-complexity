/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.InductiveCounting.Sound

/-!
# Completeness of the inductive-counting machine

If no target is reachable from a source, the machine has an accepting run: the
honest one, which certifies every node of every layer. The proof builds that
run, four nested loops at a time – the certifying walk, the inner scan, the
outer scan, and the sequence of stages – each by an induction along the finite
linear order of nodes or, for the stages, on how much room the layer still has
to grow.
-/

namespace DescriptiveComplexity

namespace InductiveCounting

section Complete

variable {V : Type} [LinearOrder V] [Finite V] {E : V → V → Prop} {S T : V → Prop}

/-! ### Walking a finite linear order downwards -/

/-- Induction from the greatest element downwards, one cover at a time. -/
theorem order_induction_down {A : Type} [LinearOrder A] [Finite A] {P : A → Prop}
    (hmax : ∀ z : A, (∀ a : A, a ≤ z) → P z)
    (hstep : ∀ w z : A, w ⋖ z → P z → P w) (z : A) : P z := by
  induction z using (Finite.to_wellFoundedGT (α := A)).wf.induction with
  | _ z ih =>
    by_cases hz : ∀ a : A, a ≤ z
    · exact hmax z hz
    · obtain ⟨w, hw⟩ := exists_covBy_of_not_max hz
      exact hstep z w hw (ih w hw.lt)

/-- A nonzero counter has a predecessor. -/
theorem exists_covBy_of_orank_pos {r : WithBot V} (h : 0 < orank r) :
    ∃ r' : WithBot V, r' ⋖ r := by
  have hne : ¬∀ a : WithBot V, r ≤ a := by
    intro hmin
    rw [orank_eq_zero hmin] at h
    exact absurd h (lt_irrefl _)
  obtain ⟨w, hlt, hnb⟩ := exists_succ_of_not_min hne
  exact ⟨w, hlt, fun c hwc hcr => hnb c ⟨hwc, hcr⟩⟩

variable (V) in
/-- A finite nonempty linear order has a least element. -/
theorem exists_isMin [Nonempty V] : ∃ x : V, ∀ z : V, x ≤ z := by
  classical
  have := Fintype.ofFinite V
  exact ⟨Finset.univ.min' Finset.univ_nonempty,
    fun z => Finset.min'_le _ z (Finset.mem_univ z)⟩

end Complete

/-! ### Configurations, explicitly -/

/-- A configuration with its eight registers given one by one. -/
def mkCfg {V : Type} (ph : Phase) (fl : Bool) (rd rc rc2 rv rcnt ru rw rj : WithBot V) :
    Cfg V :=
  ⟨ph, fl, ![rd, rc, rc2, rv, rcnt, ru, rw, rj]⟩

section Build

variable {V : Type} {ph : Phase} {fl : Bool} {rd rc rc2 rv rcnt ru rw rj : WithBot V}

@[simp] theorem mkCfg_phase : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).phase = ph := rfl

@[simp] theorem mkCfg_flag : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).flag = fl := rfl

@[simp] theorem mkCfg_d : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).regs Reg.d = rd := rfl

@[simp] theorem mkCfg_c : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).regs Reg.c = rc := rfl

@[simp] theorem mkCfg_c2 : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).regs Reg.c2 = rc2 := rfl

@[simp] theorem mkCfg_v : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).regs Reg.v = rv := rfl

@[simp] theorem mkCfg_cnt : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).regs Reg.cnt = rcnt := rfl

@[simp] theorem mkCfg_u : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).regs Reg.u = ru := rfl

@[simp] theorem mkCfg_w : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).regs Reg.w = rw := rfl

@[simp] theorem mkCfg_j : (mkCfg ph fl rd rc rc2 rv rcnt ru rw rj).regs Reg.j = rj := rfl

end Build

/-! ### The transitions, one lemma each -/

section Steps

variable {V : Type} [LinearOrder V] {E : V → V → Prop} {S T : V → Prop}
variable {fl fl' : Bool} {rd rd' rc rc' rc2 rc2' rv rv' rcnt rcnt' ru ru' rw rw' rj rj' : WithBot V}

open VAtom

/-- Counting a source and moving on. -/
theorem step_init_src (hsrc : PW S rv) (hc : rc ⋖ rc') (hv : rv ⋖ rv') :
    CfgStep E S T (mkCfg Phase.initCount fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.initCount fl rd rc' rc2 rv' rcnt ru rw rj) := by
  refine ⟨[srcR (old Reg.v), succR (old Reg.c) (nxt Reg.c), succR (old Reg.v) (nxt Reg.v)],
    by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hsrc, hc, hv]

/-- Skipping a non-source and moving on. -/
theorem step_init_nsrc (hsrc : ¬PW S rv) (hv : rv ⋖ rv') :
    CfgStep E S T (mkCfg Phase.initCount fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.initCount fl rd rc rc2 rv' rcnt ru rw rj) := by
  refine ⟨[nsrcR (old Reg.v), eqR (old Reg.c) (nxt Reg.c), succR (old Reg.v) (nxt Reg.v)],
    by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hsrc, hv]

/-- The last node of the source scan is a source: the first stage begins. -/
theorem step_init_last_src (hsrc : PW S rv) (hc : rc ⋖ rc')
    (htop : PW (fun p : V => ∀ z : V, z ≤ p) rv)
    (hv' : PW (fun p : V => ∀ z : V, p ≤ z) rv')
    (hu' : PW (fun p : V => ∀ z : V, p ≤ z) ru') :
    CfgStep E S T (mkCfg Phase.initCount fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner false ⊥ rc' ⊥ rv' ⊥ ru' rw' rj') := by
  refine ⟨[srcR (old Reg.v), succR (old Reg.c) (nxt Reg.c), topNode (old Reg.v),
    isZero (nxt Reg.d), isZero (nxt Reg.c2), isZero (nxt Reg.cnt), botNode (nxt Reg.v),
    botNode (nxt Reg.u)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hsrc, hc, htop, hv', hu']

/-- The last node of the source scan is not a source: the first stage begins. -/
theorem step_init_last_nsrc (hsrc : ¬PW S rv)
    (htop : PW (fun p : V => ∀ z : V, z ≤ p) rv)
    (hv' : PW (fun p : V => ∀ z : V, p ≤ z) rv')
    (hu' : PW (fun p : V => ∀ z : V, p ≤ z) ru') :
    CfgStep E S T (mkCfg Phase.initCount fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner false ⊥ rc ⊥ rv' ⊥ ru' rw' rj') := by
  refine ⟨[nsrcR (old Reg.v), eqR (old Reg.c) (nxt Reg.c), topNode (old Reg.v),
    isZero (nxt Reg.d), isZero (nxt Reg.c2), isZero (nxt Reg.cnt), botNode (nxt Reg.v),
    botNode (nxt Reg.u)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hsrc, htop, hv', hu']

/-- Skipping a node of the inner scan. -/
theorem step_skip (hu : ru ⋖ ru') :
    CfgStep E S T (mkCfg Phase.inner fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner fl rd rc rc2 rv rcnt ru' rw' rj') := by
  refine ⟨[succR (old Reg.u) (nxt Reg.u), eqR (old Reg.d) (nxt Reg.d),
    eqR (old Reg.c) (nxt Reg.c), eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v),
    eqR (old Reg.cnt) (nxt Reg.cnt)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hu]

/-- Skipping the last node of the inner scan. -/
theorem step_skip_last (hu : PW (fun p : V => ∀ z : V, z ≤ p) ru) :
    CfgStep E S T (mkCfg Phase.inner fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.check fl rd rc rc2 rv rcnt ru' rw' rj') := by
  refine ⟨[topNode (old Reg.u), eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c),
    eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v),
    eqR (old Reg.cnt) (nxt Reg.cnt)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hu]

/-- Starting to certify the current node of the inner scan. -/
theorem step_certify (hu : ¬PW T ru) :
    CfgStep E S T (mkCfg Phase.inner fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.walk fl rd rc rc2 rv rcnt ru ru rd) := by
  refine ⟨[ntgtR (old Reg.u), eqR (old Reg.u) (nxt Reg.w), eqR (old Reg.d) (nxt Reg.j),
    eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c), eqR (old Reg.c2) (nxt Reg.c2),
    eqR (old Reg.v) (nxt Reg.v), eqR (old Reg.cnt) (nxt Reg.cnt),
    eqR (old Reg.u) (nxt Reg.u)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hu]

/-- One edge backwards along the certifying path. -/
theorem step_walk (hj : rj' ⋖ rj) (hw : EW E rw' rw) :
    CfgStep E S T (mkCfg Phase.walk fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.walk fl rd rc rc2 rv rcnt ru rw' rj') := by
  refine ⟨[succR (nxt Reg.j) (old Reg.j), edge (nxt Reg.w) (old Reg.w),
    eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c), eqR (old Reg.c2) (nxt Reg.c2),
    eqR (old Reg.v) (nxt Reg.v), eqR (old Reg.cnt) (nxt Reg.cnt),
    eqR (old Reg.u) (nxt Reg.u)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hj, hw]

/-- The certifying path has reached a source. -/
theorem step_walk_done (hw : PW S rw) :
    CfgStep E S T (mkCfg Phase.walk fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.certDone fl rd rc rc2 rv rcnt ru rw rj) := by
  refine ⟨[srcR (old Reg.w), eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c),
    eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v),
    eqR (old Reg.cnt) (nxt Reg.cnt), eqR (old Reg.u) (nxt Reg.u)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hw]

/-- Counting in a certified node equal to the outer one. -/
theorem step_count_eq (heq : ru = rv) (hcnt : rcnt ⋖ rcnt') (hu : ru ⋖ ru') :
    CfgStep E S T (mkCfg Phase.certDone fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner true rd rc rc2 rv rcnt' ru' rw rj) := by
  subst heq
  refine ⟨eqR (old Reg.u) (old Reg.v) :: [succR (old Reg.cnt) (nxt Reg.cnt),
    succR (old Reg.u) (nxt Reg.u), eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c),
    eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hcnt, hu]

/-- Counting in a certified node with an edge to the outer one. -/
theorem step_count_edge (hedge : EW E ru rv) (hcnt : rcnt ⋖ rcnt') (hu : ru ⋖ ru') :
    CfgStep E S T (mkCfg Phase.certDone fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner true rd rc rc2 rv rcnt' ru' rw rj) := by
  refine ⟨edge (old Reg.u) (old Reg.v) :: [succR (old Reg.cnt) (nxt Reg.cnt),
    succR (old Reg.u) (nxt Reg.u), eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c),
    eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hedge, hcnt, hu]

/-- Counting in a certified node unrelated to the outer one. -/
theorem step_count_none (hne : ru ≠ rv) (hnedge : ¬EW E ru rv) (hcnt : rcnt ⋖ rcnt')
    (hu : ru ⋖ ru') :
    CfgStep E S T (mkCfg Phase.certDone fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner fl rd rc rc2 rv rcnt' ru' rw rj) := by
  refine ⟨neqR (old Reg.u) (old Reg.v) :: nedge (old Reg.u) (old Reg.v) ::
    [succR (old Reg.cnt) (nxt Reg.cnt), succR (old Reg.u) (nxt Reg.u),
      eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c),
      eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hne, hnedge, hcnt, hu]

/-- Counting in the last certified node, equal to the outer one. -/
theorem step_count_last_eq (heq : ru = rv) (hcnt : rcnt ⋖ rcnt')
    (hu : PW (fun p : V => ∀ z : V, z ≤ p) ru) :
    CfgStep E S T (mkCfg Phase.certDone fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.check true rd rc rc2 rv rcnt' ru' rw rj) := by
  subst heq
  refine ⟨eqR (old Reg.u) (old Reg.v) :: [succR (old Reg.cnt) (nxt Reg.cnt),
    topNode (old Reg.u), eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c),
    eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hcnt, hu]

/-- Counting in the last certified node, with an edge to the outer one. -/
theorem step_count_last_edge (hedge : EW E ru rv) (hcnt : rcnt ⋖ rcnt')
    (hu : PW (fun p : V => ∀ z : V, z ≤ p) ru) :
    CfgStep E S T (mkCfg Phase.certDone fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.check true rd rc rc2 rv rcnt' ru' rw rj) := by
  refine ⟨edge (old Reg.u) (old Reg.v) :: [succR (old Reg.cnt) (nxt Reg.cnt),
    topNode (old Reg.u), eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c),
    eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hedge, hcnt, hu]

/-- Counting in the last certified node, unrelated to the outer one. -/
theorem step_count_last_none (hne : ru ≠ rv) (hnedge : ¬EW E ru rv) (hcnt : rcnt ⋖ rcnt')
    (hu : PW (fun p : V => ∀ z : V, z ≤ p) ru) :
    CfgStep E S T (mkCfg Phase.certDone fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.check fl rd rc rc2 rv rcnt' ru' rw rj) := by
  refine ⟨neqR (old Reg.u) (old Reg.v) :: nedge (old Reg.u) (old Reg.v) ::
    [succR (old Reg.cnt) (nxt Reg.cnt), topNode (old Reg.u),
      eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c),
      eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.v) (nxt Reg.v)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hne, hnedge, hcnt, hu]

/-- The count checks out and the outer node was in the next layer. -/
theorem step_check_true (hc2 : rc2 ⋖ rc2') (hcnt : rcnt = rc) (hv : rv ⋖ rv')
    (hu' : PW (fun p : V => ∀ z : V, p ≤ z) ru') :
    CfgStep E S T (mkCfg Phase.check true rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner false rd rc rc2' rv' ⊥ ru' rw' rj') := by
  refine ⟨[succR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.cnt) (old Reg.c),
    succR (old Reg.v) (nxt Reg.v), isZero (nxt Reg.cnt), botNode (nxt Reg.u),
    eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hc2, hcnt, hv, hu']

/-- The count checks out and the outer node was not in the next layer. -/
theorem step_check_false (hcnt : rcnt = rc) (hv : rv ⋖ rv')
    (hu' : PW (fun p : V => ∀ z : V, p ≤ z) ru') :
    CfgStep E S T (mkCfg Phase.check false rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner false rd rc rc2 rv' ⊥ ru' rw' rj') := by
  refine ⟨[eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.cnt) (old Reg.c),
    succR (old Reg.v) (nxt Reg.v), isZero (nxt Reg.cnt), botNode (nxt Reg.u),
    eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hcnt, hv, hu']

/-- The last outer node was in the next layer: the stage ends. -/
theorem step_check_last_true (hc2 : rc2 ⋖ rc2') (hcnt : rcnt = rc)
    (hv : PW (fun p : V => ∀ z : V, z ≤ p) rv) :
    CfgStep E S T (mkCfg Phase.check true rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.stageEnd false rd rc rc2' rv' rcnt' ru' rw' rj') := by
  refine ⟨[succR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.cnt) (old Reg.c),
    topNode (old Reg.v), eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c)],
    by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hc2, hcnt, hv]

/-- The last outer node was not in the next layer: the stage ends. -/
theorem step_check_last_false (hcnt : rcnt = rc)
    (hv : PW (fun p : V => ∀ z : V, z ≤ p) rv) :
    CfgStep E S T (mkCfg Phase.check false rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.stageEnd false rd rc rc2 rv' rcnt' ru' rw' rj') := by
  refine ⟨[eqR (old Reg.c2) (nxt Reg.c2), eqR (old Reg.cnt) (old Reg.c),
    topNode (old Reg.v), eqR (old Reg.d) (nxt Reg.d), eqR (old Reg.c) (nxt Reg.c)],
    by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hcnt, hv]

/-- The two counts agree: the machine accepts. -/
theorem step_accept (hc2 : rc2 = rc) :
    CfgStep E S T (mkCfg Phase.stageEnd fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.accept fl' rd' rc' rc2' rv' rcnt' ru' rw' rj') := by
  refine ⟨[eqR (old Reg.c2) (old Reg.c)], by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hc2]

/-- On to the next stage. -/
theorem step_nextStage (hd : rd ⋖ rd')
    (hv' : PW (fun p : V => ∀ z : V, p ≤ z) rv')
    (hu' : PW (fun p : V => ∀ z : V, p ≤ z) ru') :
    CfgStep E S T (mkCfg Phase.stageEnd fl rd rc rc2 rv rcnt ru rw rj)
      (mkCfg Phase.inner false rd' rc2 ⊥ rv' ⊥ ru' rw' rj') := by
  refine ⟨[succR (old Reg.d) (nxt Reg.d), eqR (old Reg.c2) (nxt Reg.c),
    isZero (nxt Reg.c2), isZero (nxt Reg.cnt), botNode (nxt Reg.v), botNode (nxt Reg.u)],
    by simp [table], ?_⟩
  simp [VAtom.Holds, slotVal, hd, hv', hu']

end Steps

/-! ### The certifying walk -/

section Runs

variable {V : Type} [LinearOrder V] [Finite V] {E : V → V → Prop} {S T : V → Prop}

/-- A node of the current layer can be certified: the machine walks backwards
along a witnessing path until it meets a source. -/
theorem reach_certDone {fl : Bool} {rd rc rc2 rv rcnt : WithBot V} {uu : V} :
    ∀ (n : ℕ) (ww : V) (rj : WithBot V), n ≤ orank rj → (∃ s0 : V, S s0 ∧ RInLe E n s0 ww) →
      ∃ rw' rj', CfgReach E S T
        (mkCfg Phase.walk fl rd rc rc2 rv rcnt ↑uu ↑ww rj)
        (mkCfg Phase.certDone fl rd rc rc2 rv rcnt ↑uu rw' rj') := by
  intro n
  induction n with
  | zero =>
    rintro ww rj - ⟨s0, hs0, heq⟩
    exact ⟨↑ww, rj, Relation.ReflTransGen.single
      (step_walk_done (pW_coe.mpr ((rInLe_zero.mp heq) ▸ hs0)))⟩
  | succ n ih =>
    rintro ww rj hn ⟨s0, hs0, hr⟩
    rcases rInLe_succ.mp hr with hr' | ⟨c, hc, hcw⟩
    · exact ih ww rj (le_trans (Nat.le_succ n) hn) ⟨s0, hs0, hr'⟩
    · obtain ⟨rj', hcov⟩ := exists_covBy_of_orank_pos (r := rj) (by omega)
      have hn' : n ≤ orank rj' := by
        have := orank_covBy hcov
        omega
      obtain ⟨rw2, rj2, hrest⟩ := ih c rj' hn' ⟨s0, hs0, hc⟩
      exact ⟨rw2, rj2, Relation.ReflTransGen.head (step_walk hcov (eW_coe_coe.mpr hcw)) hrest⟩

/-! ### The inner scan -/

omit [LinearOrder V] [Finite V] in
/-- Rewriting the witnesses of the outer node when the scan passes a node that
is not one. -/
theorem exists_wit_insert {D : ℕ} {rv : WithBot V} {x : V} {P : Set V}
    (hnw : ¬Wit E rv x ∨ x ∉ Rset E S D) :
    (∃ y ∈ Rset E S D ∩ insert x P, Wit E rv y) ↔ ∃ y ∈ Rset E S D ∩ P, Wit E rv y := by
  constructor
  · rintro ⟨y, ⟨hyR, hyP⟩, hwit⟩
    rcases Set.mem_insert_iff.mp hyP with heq | hyP'
    · subst heq
      rcases hnw with h | h
      · exact absurd hwit h
      · exact absurd hyR h
    · exact ⟨y, ⟨hyR, hyP'⟩, hwit⟩
  · rintro ⟨y, ⟨hyR, hyP⟩, hwit⟩
    exact ⟨y, ⟨hyR, Set.mem_insert_of_mem _ hyP⟩, hwit⟩

/-- **The inner scan**: from any node on, with an honest count and an honest
flag, the machine reaches the count check with the exact count of the current
layer and with the flag telling whether the outer node has entered the next
layer. -/
theorem reach_check {rd rc rc2 : WithBot V} {vv : V}
    (hnoT : ∀ y ∈ Rset E S (orank rd), ¬T y) (x : V) :
    ∀ (rcnt rw rj : WithBot V) (fl : Bool),
      orank rcnt = (Rset E S (orank rd) ∩ predSet (↑x : WithBot V)).ncard →
      ((fl = true) ↔ ∃ y ∈ Rset E S (orank rd) ∩ predSet (↑x : WithBot V),
        Wit E (↑vv : WithBot V) y) →
      ∃ (rcnt' rw' rj' ru' : WithBot V) (fl' : Bool),
        CfgReach E S T (mkCfg Phase.inner fl rd rc rc2 ↑vv rcnt ↑x rw rj)
          (mkCfg Phase.check fl' rd rc rc2 ↑vv rcnt' ru' rw' rj') ∧
        orank rcnt' = (Rset E S (orank rd)).ncard ∧
        ((fl' = true) ↔ vv ∈ Rset E S (orank rd + 1)) := by
  induction x using order_induction_down with
  | hmax x hx =>
    intro rcnt rw rj fl hcnt hfl
    have key : ∀ hnw : ¬Wit E (↑vv : WithBot V) x ∨ x ∉ Rset E S (orank rd),
        (∃ z ∈ Rset E S (orank rd) ∩ predSet (↑x : WithBot V), Wit E (↑vv : WithBot V) z)
          ↔ vv ∈ Rset E S (orank rd + 1) := by
      intro hnw
      rw [mem_rset_succ_iff_wit, ← exists_wit_insert (P := predSet (↑x : WithBot V)) hnw,
        insert_predSet_of_isMax hx, Set.inter_univ]
    by_cases hxR : x ∈ Rset E S (orank rd)
    · obtain ⟨s0, hs0, hpath⟩ := exists_rInLe_of_mem_rset hxR
      have hone : (Rset E S (orank rd) ∩ predSet (↑x : WithBot V)).ncard + 1
          = (Rset E S (orank rd)).ncard := ncard_inter_predSet_isMax_of_mem hx hxR
      have hlt : orank rcnt < Nat.card V := by
        have := ncard_le_card (Rset E S (orank rd)); omega
      obtain ⟨rcnt', hcov⟩ := exists_covBy_of_orank_lt hlt
      obtain ⟨rw2, rj2, hwalk⟩ := reach_certDone (E := E) (S := S) (T := T) (fl := fl)
        (rd := rd) (rc := rc) (rc2 := rc2) (rv := ↑vv) (rcnt := rcnt) (uu := x)
        (orank rd) x rd (le_refl _) ⟨s0, hs0, hpath⟩
      have hcnt' : orank rcnt' = (Rset E S (orank rd)).ncard := by
        rw [orank_covBy hcov, hcnt, hone]
      have hstart : CfgReach E S T (mkCfg Phase.inner fl rd rc rc2 ↑vv rcnt ↑x rw rj)
          (mkCfg Phase.certDone fl rd rc rc2 ↑vv rcnt ↑x rw2 rj2) :=
        Relation.ReflTransGen.head (step_certify (fun h => hnoT x hxR (pW_coe.mp h))) hwalk
      by_cases hwit : Wit E (↑vv : WithBot V) x
      · rcases hwit with heq | hedge
        · exact ⟨rcnt', rw2, rj2, ↑x, true, hstart.tail
            (step_count_last_eq heq hcov (pW_coe.mpr hx)), hcnt',
            ⟨fun _ => mem_rset_succ_iff_wit.mpr ⟨x, hxR, Or.inl heq⟩, fun _ => rfl⟩⟩
        · exact ⟨rcnt', rw2, rj2, ↑x, true, hstart.tail
            (step_count_last_edge hedge hcov (pW_coe.mpr hx)), hcnt',
            ⟨fun _ => mem_rset_succ_iff_wit.mpr ⟨x, hxR, Or.inr hedge⟩, fun _ => rfl⟩⟩
      · have hnot := hwit
        rw [Wit, not_or] at hwit
        exact ⟨rcnt', rw2, rj2, ↑x, fl, hstart.tail
          (step_count_last_none hwit.1 hwit.2 hcov (pW_coe.mpr hx)), hcnt',
          hfl.trans (key (Or.inl hnot))⟩
    · have hsame : (Rset E S (orank rd) ∩ predSet (↑x : WithBot V)).ncard
          = (Rset E S (orank rd)).ncard := ncard_inter_predSet_isMax_of_notMem hx hxR
      exact ⟨rcnt, rw, rj, ↑x, fl, Relation.ReflTransGen.single
        (step_skip_last (pW_coe.mpr hx)), by rw [hcnt, hsame],
        hfl.trans (key (Or.inr hxR))⟩
  | hstep x x' hcov ih =>
    intro rcnt rw rj fl hcnt hfl
    have hcovW : (↑x : WithBot V) ⋖ ↑x' := WithBot.coe_covBy_coe.mpr hcov
    have hins : predSet (↑x' : WithBot V) = insert x (predSet (↑x : WithBot V)) :=
      predSet_of_covBy hcovW
    by_cases hxR : x ∈ Rset E S (orank rd)
    · obtain ⟨s0, hs0, hpath⟩ := exists_rInLe_of_mem_rset hxR
      have hone : (Rset E S (orank rd) ∩ predSet (↑x' : WithBot V)).ncard
          = (Rset E S (orank rd) ∩ predSet (↑x : WithBot V)).ncard + 1 :=
        ncard_inter_predSet_covBy_of_mem hcovW hxR
      have hlt : orank rcnt < Nat.card V := by
        have h1 := ncard_le_card (Rset E S (orank rd) ∩ predSet (↑x' : WithBot V))
        omega
      obtain ⟨rcnt', hcovc⟩ := exists_covBy_of_orank_lt hlt
      obtain ⟨rw2, rj2, hwalk⟩ := reach_certDone (E := E) (S := S) (T := T) (fl := fl)
        (rd := rd) (rc := rc) (rc2 := rc2) (rv := ↑vv) (rcnt := rcnt) (uu := x)
        (orank rd) x rd (le_refl _) ⟨s0, hs0, hpath⟩
      have hstart : CfgReach E S T (mkCfg Phase.inner fl rd rc rc2 ↑vv rcnt ↑x rw rj)
          (mkCfg Phase.certDone fl rd rc rc2 ↑vv rcnt ↑x rw2 rj2) :=
        Relation.ReflTransGen.head (step_certify (fun h => hnoT x hxR (pW_coe.mp h))) hwalk
      have hcnt' : orank rcnt' =
          (Rset E S (orank rd) ∩ predSet (↑x' : WithBot V)).ncard := by
        rw [orank_covBy hcovc, hcnt, hone]
      have hxmem : x ∈ Rset E S (orank rd) ∩ predSet (↑x' : WithBot V) :=
        ⟨hxR, mem_predSet_coe.mpr hcov.lt⟩
      by_cases hwit : Wit E (↑vv : WithBot V) x
      · obtain ⟨rcnt2, rw3, rj3, ru3, fl3, hrun, hres1, hres2⟩ :=
          ih rcnt' rw2 rj2 true hcnt' ⟨fun _ => ⟨x, hxmem, hwit⟩, fun _ => rfl⟩
        rcases hwit with heq | hedge
        · exact ⟨rcnt2, rw3, rj3, ru3, fl3,
            (hstart.tail (step_count_eq heq hcovc hcovW)).trans hrun, hres1, hres2⟩
        · exact ⟨rcnt2, rw3, rj3, ru3, fl3,
            (hstart.tail (step_count_edge hedge hcovc hcovW)).trans hrun, hres1, hres2⟩
      · have hfl' : (fl = true) ↔ ∃ y ∈ Rset E S (orank rd) ∩ predSet (↑x' : WithBot V),
            Wit E (↑vv : WithBot V) y := by
          rw [hins, exists_wit_insert (Or.inl hwit)]
          exact hfl
        obtain ⟨rcnt2, rw3, rj3, ru3, fl3, hrun, hres1, hres2⟩ :=
          ih rcnt' rw2 rj2 fl hcnt' hfl'
        rw [Wit, not_or] at hwit
        exact ⟨rcnt2, rw3, rj3, ru3, fl3,
          (hstart.tail (step_count_none hwit.1 hwit.2 hcovc hcovW)).trans hrun, hres1, hres2⟩
    · have hcnt' : orank rcnt = (Rset E S (orank rd) ∩ predSet (↑x' : WithBot V)).ncard := by
        rw [ncard_inter_predSet_covBy_of_notMem hcovW hxR, hcnt]
      have hfl' : (fl = true) ↔ ∃ y ∈ Rset E S (orank rd) ∩ predSet (↑x' : WithBot V),
          Wit E (↑vv : WithBot V) y := by
        rw [hins, exists_wit_insert (Or.inr hxR)]
        exact hfl
      obtain ⟨rcnt2, rw3, rj3, ru3, fl3, hrun, hres1, hres2⟩ := ih rcnt rw rj fl hcnt' hfl'
      exact ⟨rcnt2, rw3, rj3, ru3, fl3,
        Relation.ReflTransGen.head (step_skip hcovW) hrun, hres1, hres2⟩

/-! ### The outer scan, the source count, and the stages -/

/-- **The outer scan**: with the layer count in hand, the machine runs over
every node and reaches the end of the stage with the exact count of the next
layer. -/
theorem reach_stageEnd [Nonempty V] {rd rc : WithBot V}
    (hnoT : ∀ y ∈ Rset E S (orank rd), ¬T y)
    (hc : orank rc = (Rset E S (orank rd)).ncard) (x : V) :
    ∀ (rc2 rw rj : WithBot V) (u0 : V), (∀ z : V, u0 ≤ z) →
      orank rc2 = (Rset E S (orank rd + 1) ∩ predSet (↑x : WithBot V)).ncard →
      ∃ (rc2' rv' rcnt' ru' rw' rj' : WithBot V),
        CfgReach E S T (mkCfg Phase.inner false rd rc rc2 ↑x ⊥ ↑u0 rw rj)
          (mkCfg Phase.stageEnd false rd rc rc2' rv' rcnt' ru' rw' rj') ∧
        orank rc2' = (Rset E S (orank rd + 1)).ncard := by
  induction x using order_induction_down with
  | hmax x hx =>
    intro rc2 rw rj u0 hu0 hc2
    obtain ⟨rcnt', rw2, rj2, ru2, fl2, hrun, hcnt2, hfl2⟩ :=
      reach_check (rc2 := rc2) hnoT u0 ⊥ rw rj false
        (by rw [orank_bot, predSet_of_isMin hu0, Set.inter_empty, Set.ncard_empty])
        (by
          rw [predSet_of_isMin hu0, Set.inter_empty]
          exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩)
    have hcnteq : rcnt' = rc := orank_inj (by rw [hcnt2, hc])
    subst hcnteq
    cases hfl : fl2 with
    | true =>
      have hxmem : x ∈ Rset E S (orank rd + 1) := hfl2.mp hfl
      have hone : (Rset E S (orank rd + 1) ∩ predSet (↑x : WithBot V)).ncard + 1
          = (Rset E S (orank rd + 1)).ncard := ncard_inter_predSet_isMax_of_mem hx hxmem
      have hlt : orank rc2 < Nat.card V := by
        have := ncard_le_card (Rset E S (orank rd + 1)); omega
      obtain ⟨rc2', hcov⟩ := exists_covBy_of_orank_lt hlt
      exact ⟨rc2', ↑x, rcnt', ru2, rw2, rj2,
        (hfl ▸ hrun).tail (step_check_last_true hcov rfl (pW_coe.mpr hx)),
        by rw [orank_covBy hcov, hc2, hone]⟩
    | false =>
      have hxmem : x ∉ Rset E S (orank rd + 1) := fun h =>
        absurd (hfl2.mpr h) (by rw [hfl]; simp)
      exact ⟨rc2, ↑x, rcnt', ru2, rw2, rj2,
        (hfl ▸ hrun).tail (step_check_last_false rfl (pW_coe.mpr hx)),
        by rw [hc2, ncard_inter_predSet_isMax_of_notMem hx hxmem]⟩
  | hstep x x' hcov ih =>
    intro rc2 rw rj u0 hu0 hc2
    have hcovW : (↑x : WithBot V) ⋖ ↑x' := WithBot.coe_covBy_coe.mpr hcov
    obtain ⟨rcnt', rw2, rj2, ru2, fl2, hrun, hcnt2, hfl2⟩ :=
      reach_check (rc2 := rc2) hnoT u0 ⊥ rw rj false
        (by rw [orank_bot, predSet_of_isMin hu0, Set.inter_empty, Set.ncard_empty])
        (by
          rw [predSet_of_isMin hu0, Set.inter_empty]
          exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩)
    have hcnteq : rcnt' = rc := orank_inj (by rw [hcnt2, hc])
    subst hcnteq
    obtain ⟨m0, hm0⟩ := exists_isMin V
    cases hfl : fl2 with
    | true =>
      have hxmem : x ∈ Rset E S (orank rd + 1) := hfl2.mp hfl
      have hone : (Rset E S (orank rd + 1) ∩ predSet (↑x' : WithBot V)).ncard
          = (Rset E S (orank rd + 1) ∩ predSet (↑x : WithBot V)).ncard + 1 :=
        ncard_inter_predSet_covBy_of_mem hcovW hxmem
      have hlt : orank rc2 < Nat.card V := by
        have := ncard_le_card (Rset E S (orank rd + 1) ∩ predSet (↑x' : WithBot V)); omega
      obtain ⟨rc2', hcovc⟩ := exists_covBy_of_orank_lt hlt
      obtain ⟨rc2'', rv3, rcnt3, ru3, rw3, rj3, hrest, hres⟩ :=
        ih rc2' rw2 rj2 m0 hm0 (by rw [orank_covBy hcovc, hc2, hone])
      exact ⟨rc2'', rv3, rcnt3, ru3, rw3, rj3,
        ((hfl ▸ hrun).tail (step_check_true hcovc rfl hcovW (pW_coe.mpr hm0))).trans hrest, hres⟩
    | false =>
      have hxmem : x ∉ Rset E S (orank rd + 1) := fun h =>
        absurd (hfl2.mpr h) (by rw [hfl]; simp)
      obtain ⟨rc2'', rv3, rcnt3, ru3, rw3, rj3, hrest, hres⟩ :=
        ih rc2 rw2 rj2 m0 hm0
          (by rw [hc2, ncard_inter_predSet_covBy_of_notMem hcovW hxmem])
      exact ⟨rc2'', rv3, rcnt3, ru3, rw3, rj3,
        ((hfl ▸ hrun).tail (step_check_false rfl hcovW (pW_coe.mpr hm0))).trans hrest, hres⟩

/-- **The source scan**: the machine counts the sources and enters the first
stage. -/
theorem reach_firstStage [Nonempty V] (x : V) :
    ∀ (fl : Bool) (rd rc rc2 rcnt ru rw rj : WithBot V),
      orank rc = ({y : V | S y} ∩ predSet (↑x : WithBot V)).ncard →
      ∃ (rc' rw' rj' : WithBot V) (v0 u0 : V), (∀ z : V, v0 ≤ z) ∧ (∀ z : V, u0 ≤ z) ∧
        CfgReach E S T (mkCfg Phase.initCount fl rd rc rc2 ↑x rcnt ru rw rj)
          (mkCfg Phase.inner false ⊥ rc' ⊥ ↑v0 ⊥ ↑u0 rw' rj') ∧
        orank rc' = (Rset E S 0).ncard := by
  induction x using order_induction_down with
  | hmax x hx =>
    intro fl rd rc rc2 rcnt ru rw rj hcrank
    obtain ⟨m0, hm0⟩ := exists_isMin V
    by_cases hSx : S x
    · have hone : ({y : V | S y} ∩ predSet (↑x : WithBot V)).ncard + 1
          = ({y : V | S y}).ncard := ncard_inter_predSet_isMax_of_mem (P := {y : V | S y}) hx hSx
      have hlt : orank rc < Nat.card V := by
        have := ncard_le_card {y : V | S y}; omega
      obtain ⟨rc', hcov⟩ := exists_covBy_of_orank_lt hlt
      exact ⟨rc', rw, rj, m0, m0, hm0, hm0, Relation.ReflTransGen.single
        (step_init_last_src (pW_coe.mpr hSx) hcov (pW_coe.mpr hx) (pW_coe.mpr hm0)
          (pW_coe.mpr hm0)), by rw [rset_zero, orank_covBy hcov, hcrank, hone]⟩
    · exact ⟨rc, rw, rj, m0, m0, hm0, hm0, Relation.ReflTransGen.single
        (step_init_last_nsrc (fun h => hSx (pW_coe.mp h)) (pW_coe.mpr hx) (pW_coe.mpr hm0)
          (pW_coe.mpr hm0)),
        by rw [rset_zero, hcrank, ncard_inter_predSet_isMax_of_notMem (P := {y : V | S y}) hx hSx]⟩
  | hstep x x' hcov ih =>
    intro fl rd rc rc2 rcnt ru rw rj hcrank
    have hcovW : (↑x : WithBot V) ⋖ ↑x' := WithBot.coe_covBy_coe.mpr hcov
    by_cases hSx : S x
    · have hone : ({y : V | S y} ∩ predSet (↑x' : WithBot V)).ncard
          = ({y : V | S y} ∩ predSet (↑x : WithBot V)).ncard + 1 :=
        ncard_inter_predSet_covBy_of_mem (P := {y : V | S y}) hcovW hSx
      have hlt : orank rc < Nat.card V := by
        have := ncard_le_card ({y : V | S y} ∩ predSet (↑x' : WithBot V)); omega
      obtain ⟨rc', hcovc⟩ := exists_covBy_of_orank_lt hlt
      obtain ⟨rc'', rw2, rj2, v0, u0, hv0, hu0, hrest, hres⟩ :=
        ih fl rd rc' rc2 rcnt ru rw rj (by rw [orank_covBy hcovc, hcrank, hone])
      exact ⟨rc'', rw2, rj2, v0, u0, hv0, hu0,
        Relation.ReflTransGen.head (step_init_src (pW_coe.mpr hSx) hcovc hcovW) hrest, hres⟩
    · obtain ⟨rc'', rw2, rj2, v0, u0, hv0, hu0, hrest, hres⟩ :=
        ih fl rd rc rc2 rcnt ru rw rj
          (by rw [hcrank, ncard_inter_predSet_covBy_of_notMem (P := {y : V | S y}) hcovW hSx])
      exact ⟨rc'', rw2, rj2, v0, u0, hv0, hu0,
        Relation.ReflTransGen.head
          (step_init_nsrc (fun h => hSx (pW_coe.mp h)) hcovW) hrest, hres⟩

/-- **The stages**: as long as the layer keeps growing the machine starts a new
stage; when it stops growing the two counts agree and the machine accepts. -/
theorem reach_accept [Nonempty V]
    (hno : ¬∃ a b : V, S a ∧ T b ∧ Relation.ReflTransGen E a b) :
    ∀ (m : ℕ) (rd rc : WithBot V) (v0 u0 : V) (rw rj : WithBot V),
      (∀ z : V, v0 ≤ z) → (∀ z : V, u0 ≤ z) →
      orank rc = (Rset E S (orank rd)).ncard →
      orank rd + (Rset E S 0).ncard ≤ (Rset E S (orank rd)).ncard →
      Nat.card V - (Rset E S (orank rd)).ncard ≤ m →
      ∃ s' : Cfg V, s'.phase = Phase.accept ∧
        CfgReach E S T (mkCfg Phase.inner false rd rc ⊥ ↑v0 ⊥ ↑u0 rw rj) s' := by
  have hnoT : ∀ d : ℕ, ∀ y ∈ Rset E S d, ¬T y := by
    intro d y hy hTy
    obtain ⟨s0, hs0, hreach⟩ := reflTransGen_of_mem_rset hy
    exact hno ⟨s0, y, hs0, hTy, hreach⟩
  intro m
  induction m with
  | zero =>
    intro rd rc v0 u0 rw rj hv0 hu0 hc hD hm
    obtain ⟨rc2', rv3, rcnt3, ru3, rw3, rj3, hrun, hres⟩ :=
      reach_stageEnd (rc := rc) (hnoT _) hc v0 ⊥ rw rj u0 hu0
        (by rw [orank_bot, predSet_of_isMin hv0, Set.inter_empty, Set.ncard_empty])
    have hsub : (Rset E S (orank rd)).ncard ≤ (Rset E S (orank rd + 1)).ncard :=
      Set.ncard_le_ncard Rset.subset_succ (Set.toFinite _)
    have hle : (Rset E S (orank rd + 1)).ncard ≤ Nat.card V :=
      ncard_le_card (Rset E S (orank rd + 1))
    have heq : rc2' = rc := orank_inj (by rw [hres, hc]; omega)
    subst heq
    exact ⟨_, rfl, hrun.tail (step_accept (fl' := false) (rd' := rc2') (rc' := rc2')
      (rc2' := rc2') (rv' := rc2') (rcnt' := rc2') (ru' := rc2') (rw' := rc2')
      (rj' := rc2') rfl)⟩
  | succ m ih =>
    intro rd rc v0 u0 rw rj hv0 hu0 hc hD hm
    obtain ⟨rc2', rv3, rcnt3, ru3, rw3, rj3, hrun, hres⟩ :=
      reach_stageEnd (rc := rc) (hnoT _) hc v0 ⊥ rw rj u0 hu0
        (by rw [orank_bot, predSet_of_isMin hv0, Set.inter_empty, Set.ncard_empty])
    have hsub : (Rset E S (orank rd)).ncard ≤ (Rset E S (orank rd + 1)).ncard :=
      Set.ncard_le_ncard Rset.subset_succ (Set.toFinite _)
    have hle : (Rset E S (orank rd + 1)).ncard ≤ Nat.card V :=
      ncard_le_card (Rset E S (orank rd + 1))
    by_cases heq : (Rset E S (orank rd + 1)).ncard = (Rset E S (orank rd)).ncard
    · have hrceq : rc2' = rc := orank_inj (by rw [hres, hc, heq])
      subst hrceq
      exact ⟨_, rfl, hrun.tail (step_accept (fl' := false) (rd' := rc2') (rc' := rc2')
        (rc2' := rc2') (rv' := rc2') (rcnt' := rc2') (ru' := rc2') (rw' := rc2')
        (rj' := rc2') rfl)⟩
    · have hgrow : (Rset E S (orank rd)).ncard < (Rset E S (orank rd + 1)).ncard := by
        omega
      have hdlt : orank rd < Nat.card V := by omega
      obtain ⟨rd', hcovd⟩ := exists_covBy_of_orank_lt hdlt
      have hrank : orank rd' = orank rd + 1 := orank_covBy hcovd
      obtain ⟨m1, hm1⟩ := exists_isMin V
      obtain ⟨s', hph, hrest⟩ := ih rd' rc2' m1 m1 rw3 rj3 hm1 hm1
        (by rw [hrank]; exact hres) (by rw [hrank]; omega) (by rw [hrank]; omega)
      exact ⟨s', hph, (hrun.tail (step_nextStage hcovd (pW_coe.mpr hm1)
        (pW_coe.mpr hm1))).trans hrest⟩

/-! ### Completeness -/

/-- **Completeness**: if no target is reachable from a source, the machine has
an accepting run. -/
theorem machineAccepts_of_not_reach [Nonempty V]
    (hno : ¬∃ a b : V, S a ∧ T b ∧ Relation.ReflTransGen E a b) : MachineAccepts E S T := by
  obtain ⟨m0, hm0⟩ := exists_isMin V
  obtain ⟨rc', rw', rj', v0, u0, hv0, hu0, hinit, hcrank⟩ :=
    reach_firstStage (E := E) (S := S) (T := T) m0 false ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥
      (by rw [orank_bot, predSet_of_isMin hm0, Set.inter_empty, Set.ncard_empty])
  obtain ⟨s', hph, hrest⟩ :=
    reach_accept hno (Nat.card V) ⊥ rc' v0 u0 rw' rj' hv0 hu0 (by rw [orank_bot]; exact hcrank)
      (by rw [orank_bot]; omega) (by rw [orank_bot]; omega)
  exact ⟨mkCfg Phase.initCount false ⊥ ⊥ ⊥ ↑m0 ⊥ ⊥ ⊥ ⊥, s',
    ⟨rfl, rfl, rfl, pW_coe.mpr hm0⟩, hph, hinit.trans hrest⟩

/-- **The machine is correct**: it accepts exactly when no target is reachable
from a source. -/
theorem machineAccepts_iff [Nonempty V] :
    MachineAccepts E S T ↔ ¬∃ a b : V, S a ∧ T b ∧ Relation.ReflTransGen E a b :=
  ⟨not_reach_of_machineAccepts, machineAccepts_of_not_reach⟩

end Runs

end InductiveCounting

end DescriptiveComplexity
