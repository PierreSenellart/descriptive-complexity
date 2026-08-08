/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GamePrefix

/-!
# The node phases play the AND/OR graph

The second correctness half: from `main tx`, the graph game wins exactly when
the existential player wins the interpreted AND/OR graph at the node the state
carries (`DescriptiveComplexity.ExpExpansion.wins_main_iff`). Both directions are
inductions — on `DescriptiveComplexity.SOGameSpec.Wins` one way, on
`DescriptiveComplexity.WinsOn` the other — and the first goes through
`DescriptiveComplexity.ExpExpansion.Target`, which says what each of the five
node phases is *for*.

The two places the simulation could have gone wrong, and how it does not:

* a **universal node with no successor loses** (`WinsOn.all` demands a move), so
  the existential player must certify a successor before the universal player
  chooses one — that is what `allCert` does, and its witness lives in the same
  rounds the chosen successor will;
* an **illegal proposal must not count**, so `allStep` is existential and lets
  the player refute `AGMove` instead of the move being filtered out — which no
  sentence over the base could do.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : ExpExpansion L} {T : Type} [Finite T] {d n Dm : ℕ}
variable {A : Type} [instL : L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### States whose rounds are all points -/

/-- The state at a phase whose rounds carry the given points. -/
def nodeState (p : Ph T Dm) (pts : Fin n → X.Map A) : (gameBlock X n T Dm).Assignment A :=
  stateAssign p fun i => pointAssign (pts i)

omit [Finite T] [Finite A] [Nonempty A] in
theorem pointAssign_injective (p q : X.Map A) (h : pointAssign p = pointAssign q) : p = q := by
  have ht : p.1.1 = q.1.1 := by
    have hbit := congrFun (congrFun h (Sum.inl p.1.1)) fun i => isEmptyElim i
    exact Eq.mp hbit rfl
  exact map_ext ht (congrArg SOBlock.dropTag h)

omit [Finite A] [Nonempty A] in
/-- **A state all of whose rounds are points carries points**, and they are
determined. -/
theorem exists_nodeState {p : Ph T Dm} {σs : Fin n → X.pointBlock.Assignment A}
    (h : ∀ i, IsPointAssign (X := X) (σs i)) :
    ∃ pts : Fin n → X.Map A, stateAssign p σs = nodeState p pts ∧
      σs = fun i => pointAssign (pts i) := by
  obtain ⟨pts, hpts⟩ := exists_points_of_allRoundsPoint h
  exact ⟨pts, by rw [nodeState, hpts], hpts⟩

/-! ### The nodes a state carries -/

variable (I : FOInterpretation (X.E.sum Language.order) Language.andOrGraph T d)
variable (hdn : 2 * d ≤ n)

omit [Finite T] [Finite A] [Nonempty A] in
theorem nodeAt_congr (t : T) (a : Fin 2) (pts pts' : Fin n → X.Map A)
    (hag : ∀ b : Fin d, pts (paramIx d n hdn a b) = pts' (paramIx d n hdn a b)) :
    nodeAt I hdn t a pts = nodeAt I hdn t a pts' :=
  congrArg (fun f => ((t, f) : I.Map (X.Map A))) (funext hag)

omit [Finite T] [Finite A] [Nonempty A] in
/-- The first node only reads the rounds below `d`. -/
theorem nodeAt_zero_congr (t : T) (pts pts' : Fin n → X.Map A)
    (hag : ∀ i : Fin n, (i : ℕ) < d → pts i = pts' i) :
    nodeAt I hdn t 0 pts = nodeAt I hdn t 0 pts' :=
  nodeAt_congr I hdn t 0 pts pts' fun b => hag _ (by simp)

omit [Finite T] [Finite A] [Nonempty A] in
/-- **Shifting the second node's rounds onto the first's reads the same
node.** -/
theorem nodeAt_shift (t : T) (pts : Fin n → X.Map A) :
    nodeAt I hdn t 0 (fun i => pts (shiftIx d n hdn i)) = nodeAt I hdn t 1 pts := by
  refine congrArg (fun f => ((t, f) : I.Map (X.Map A))) (funext fun b => congrArg pts ?_)
  rw [shiftIx, dif_pos (show ((paramIx d n hdn 0 b : Fin n) : ℕ) < d by simp)]
  exact Fin.ext (by simp; omega)

omit [Finite T] [Finite A] [Nonempty A] in
/-- **Every node of the graph sits in the second node's rounds** of some tuple
agreeing with a given one outside them. -/
theorem exists_pts_of_node (z : I.Map (X.Map A)) (pts : Fin n → X.Map A) :
    ∃ pts' : Fin n → X.Map A,
      (∀ i : Fin n, ¬(d ≤ (i : ℕ) ∧ (i : ℕ) < 2 * d) → pts' i = pts i) ∧
      nodeAt I hdn z.1 1 pts' = z := by
  classical
  set pts' : Fin n → X.Map A :=
    fun i => if _ : d ≤ (i : ℕ) ∧ (i : ℕ) < 2 * d then z.2 ⟨(i : ℕ) - d, by omega⟩ else pts i
    with hdef
  have hmid : ∀ b : Fin d, pts' (paramIx d n hdn 1 b) = z.2 b := by
    intro b
    have hin : d ≤ ((paramIx d n hdn 1 b : Fin n) : ℕ) ∧
        ((paramIx d n hdn 1 b : Fin n) : ℕ) < 2 * d := by
      have := b.isLt
      simp only [paramIx_val, Fin.val_one, one_mul]
      omega
    rw [hdef]
    simp only [dif_pos hin]
    refine congrArg z.2 (Fin.ext ?_)
    simp only [paramIx_val, Fin.val_one, one_mul]
    omega
  refine ⟨pts', fun i hi => by rw [hdef]; exact dif_neg hi, ?_⟩
  change ((z.1, fun b => pts' (paramIx d n hdn 1 b)) : I.Map (X.Map A)) = z
  rw [funext hmid]
  rfl

/-! ### What each node phase is for -/

/-- **What a node phase promises.** The prefix phases promise nothing: they are
`DescriptiveComplexity.ExpExpansion.wins_pre`'s business. -/
def Target : Ph T Dm → (Fin n → X.Map A) → Prop
  | .startPick tx, pts =>
      letI := X.mapLinearOrder A
      letI := I.mapStructure (X.Map A)
      AGStart (nodeAt I hdn tx 0 pts) ∧ WinsOn (I.Map (X.Map A)) (nodeAt I hdn tx 0 pts)
  | .main tx, pts =>
      letI := X.mapLinearOrder A
      letI := I.mapStructure (X.Map A)
      WinsOn (I.Map (X.Map A)) (nodeAt I hdn tx 0 pts)
  | .exStep tx ty, pts =>
      letI := X.mapLinearOrder A
      letI := I.mapStructure (X.Map A)
      ¬AGUniv (nodeAt I hdn tx 0 pts) ∧
        AGMove (nodeAt I hdn tx 0 pts) (nodeAt I hdn ty 1 pts) ∧
        WinsOn (I.Map (X.Map A)) (nodeAt I hdn ty 1 pts)
  | .allCert tx ty, pts =>
      letI := X.mapLinearOrder A
      letI := I.mapStructure (X.Map A)
      AGUniv (nodeAt I hdn tx 0 pts) ∧
        AGMove (nodeAt I hdn tx 0 pts) (nodeAt I hdn ty 1 pts) ∧
        ∀ z, AGMove (nodeAt I hdn tx 0 pts) z → WinsOn (I.Map (X.Map A)) z
  | .allStep tx ty, pts =>
      letI := X.mapLinearOrder A
      letI := I.mapStructure (X.Map A)
      ¬AGMove (nodeAt I hdn tx 0 pts) (nodeAt I hdn ty 1 pts) ∨
        WinsOn (I.Map (X.Map A)) (nodeAt I hdn ty 1 pts)
  | .pre _ _ _ _ _, _ => True

/-! ### The moves out of the node phases -/

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}
variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

theorem movesFrom_startPick (tx : T) :
    movesFrom hn D hD (.startPick tx) =
      [preEntry D hD .st tx tx, ⟨.main tx, keepAll n, []⟩] := rfl

theorem movesFrom_main (tx : T) :
    movesFrom hn D hD (.main tx) = preEntry D hD .won tx tx ::
      (finEnum T).flatMap fun ty =>
        [⟨.exStep tx ty, keepOff n (isMid d n), midRounds d n⟩,
          ⟨.allCert tx ty, keepOff n (isMid d n), midRounds d n⟩] := rfl

theorem movesFrom_exStep (tx ty : T) :
    movesFrom hn D hD (.exStep tx ty) =
      [preEntry D hD .notuniv tx tx, preEntry D hD .mv tx ty,
        ⟨.main ty, keepShift d n hdn, []⟩] := rfl

theorem movesFrom_allCert (tx ty : T) :
    movesFrom hn D hD (.allCert tx ty) =
      preEntry D hD .univ tx tx :: preEntry D hD .mv tx ty ::
        (finEnum T).map fun ty' =>
          ⟨.allStep tx ty', keepOff n (isMid d n), midRounds d n⟩ := rfl

theorem movesFrom_allStep (tx ty : T) :
    movesFrom hn D hD (.allStep tx ty) =
      [preEntry D hD .notmv tx ty, ⟨.main ty, keepShift d n hdn, []⟩] := rfl

omit [Finite A] [Nonempty A] in
/-- A move that keeps every round lands on the same points. -/
theorem moveTo_keepAll {q : Ph T Dm} {pts : Fin n → X.Map A}
    {σs : Fin n → X.pointBlock.Assignment A}
    (hkeep : ∀ e ∈ keepAll n, pointAssign (pts e.1) = σs e.2) :
    stateAssign q σs = nodeState q pts :=
  congrArg (stateAssign q) ((forall_keepAll (fun j => pointAssign (pts j)) σs).mp hkeep).symm

omit [Finite A] [Nonempty A] in
/-- A shifting move carries the second node's points onto the first node's
rounds. -/
theorem moveTo_keepShift {q : Ph T Dm} {pts : Fin n → X.Map A}
    {σs : Fin n → X.pointBlock.Assignment A}
    (hkeep : ∀ e ∈ keepShift d n hdn, pointAssign (pts e.1) = σs e.2) :
    stateAssign q σs = nodeState q fun i => pts (shiftIx d n hdn i) :=
  congrArg (stateAssign q)
    (funext fun i =>
      ((forall_keepShift hdn (fun j => pointAssign (pts j)) σs).mp hkeep i).symm)

omit [Finite A] [Nonempty A] in
/-- A move that guesses the second node's rounds lands on points agreeing
outside them. -/
theorem moveTo_keepMid {q : Ph T Dm} {pts : Fin n → X.Map A}
    {σs : Fin n → X.pointBlock.Assignment A}
    (hkeep : ∀ e ∈ keepOff n (isMid d n), pointAssign (pts e.1) = σs e.2)
    (hguard : ∀ i ∈ midRounds d n, IsPointAssign (X := X) (σs i)) :
    ∃ pts' : Fin n → X.Map A, stateAssign q σs = nodeState q pts' ∧
      ∀ i : Fin n, ¬(d ≤ (i : ℕ) ∧ (i : ℕ) < 2 * d) → pts' i = pts i := by
  classical
  have hall : ∀ i, IsPointAssign (X := X) (σs i) := by
    intro i
    by_cases hmid : d ≤ (i : ℕ) ∧ (i : ℕ) < 2 * d
    · exact hguard i ((mem_midRounds i).mpr hmid)
    · rw [← (forall_keepOff (isMid d n) (fun j => pointAssign (pts j)) σs).mp hkeep i
        ((isMid_eq_false i).mpr hmid)]
      exact isPointAssign_pointAssign _
  obtain ⟨pts', hst, hσ⟩ := exists_nodeState (p := q) hall
  refine ⟨pts', hst, fun i hi => ?_⟩
  exact (pointAssign_injective _ _
    (((forall_keepOff (isMid d n) (fun j => pointAssign (pts j)) σs).mp hkeep i
      ((isMid_eq_false i).mpr hi)).trans (congrFun hσ i))).symm

omit [Finite A] [Nonempty A] in
/-- Making a move that keeps every round. -/
theorem move_keepAll (p : Ph T Dm) (m : MoveTo T Dm n) (hm : m ∈ movesFrom hn D hD p)
    (hk : m.keep = keepAll n) (hg : m.guard = []) (pts : Fin n → X.Map A) :
    (graphGame X hn D hD K).Move (nodeState p pts) (nodeState m.tgt pts) :=
  (graphGame_move _ _ _ _).mpr ⟨m, hm, rfl,
    by rw [hk]
       exact (forall_keepAll (fun j => pointAssign (pts j)) (fun j => pointAssign (pts j))).mpr rfl,
    by rw [hg]; simp⟩

omit [Finite A] [Nonempty A] in
/-- Making a shifting move. -/
theorem move_keepShift (p : Ph T Dm) (m : MoveTo T Dm n) (hm : m ∈ movesFrom hn D hD p)
    (hk : m.keep = keepShift d n hdn) (hg : m.guard = []) (pts : Fin n → X.Map A) :
    (graphGame X hn D hD K).Move (nodeState p pts)
      (nodeState m.tgt fun i => pts (shiftIx d n hdn i)) :=
  (graphGame_move _ _ _ _).mpr ⟨m, hm, rfl,
    by rw [hk]
       exact (forall_keepShift hdn (fun j => pointAssign (pts j))
         (fun i => pointAssign (pts (shiftIx d n hdn i)))).mpr fun _ => rfl,
    by rw [hg]; simp⟩

omit [Finite A] [Nonempty A] in
/-- Making a move that guesses the second node's rounds. -/
theorem move_keepMid (p : Ph T Dm) (m : MoveTo T Dm n) (hm : m ∈ movesFrom hn D hD p)
    (hk : m.keep = keepOff n (isMid d n)) (hg : m.guard = midRounds d n)
    (pts pts' : Fin n → X.Map A)
    (hag : ∀ i : Fin n, ¬(d ≤ (i : ℕ) ∧ (i : ℕ) < 2 * d) → pts' i = pts i) :
    (graphGame X hn D hD K).Move (nodeState p pts) (nodeState m.tgt pts') := by
  refine (graphGame_move _ _ _ _).mpr ⟨m, hm, rfl, ?_, ?_⟩
  · rw [hk]
    exact (forall_keepOff (isMid d n) (fun j => pointAssign (pts j))
      (fun j => pointAssign (pts' j))).mpr fun i hi =>
        congrArg pointAssign (hag i ((isMid_eq_false i).mp hi)).symm
  · rw [hg]
    exact fun i _ => isPointAssign_pointAssign _

/-! ### Entering a prefix decides its question -/

variable (hK : ∀ s tx ty, KernelSpec I hdn (n - D s tx ty) (D s tx ty) s tx ty (K s tx ty))

include hK in
/-- **Entering a prefix wins exactly when its question holds.** -/
theorem wins_preEntry (s : Sub) (tx ty : T) (pts : Fin n → X.Map A) :
    ((graphGame X hn D hD K).Wins (nodeState (preEntry (n := n) D hD s tx ty).tgt pts) ↔
      SubHolds I hdn s tx ty pts) := by
  have hle : D s tx ty ≤ Dm := hD s tx ty
  refine (wins_pre (D s tx ty) (by omega) true s tx ty _).trans ?_
  refine hK s tx ty A pts (fun τs => fillRounds (X := X) (n := n) (by omega)
    (fun i => pointAssign (pts i)) τs) ?_ ?_
  · intro τs kk hkk
    simp only [fillRounds]
    rw [dif_neg (by omega)]
  · intro τs i kk hkk
    simp only [fillRounds]
    rw [dif_pos (by omega)]
    exact congrArg τs (Fin.ext (show (kk : ℕ) - (n - D s tx ty) = (i : ℕ) by omega))

/-! ### The node phases play the graph -/

include hK in
/-- **Every node phase keeps its promise.** -/
theorem target_of_wins :
    ∀ τ, (graphGame X hn D hD K).Wins τ →
      ∀ (p : Ph T Dm) (pts : Fin n → X.Map A), τ = nodeState p pts → Target I hdn p pts := by
  letI := X.mapLinearOrder A
  letI := I.mapStructure (X.Map A)
  intro τ h
  induction h with
  | @won a hw =>
    intro p pts hτ
    subst hτ
    obtain ⟨s, tx, ty, pol, hp, -⟩ := (graphGame_isWon _ _).mp hw
    subst hp
    trivial
  | @ex a b hnu hm hwin ih =>
    intro p pts hτ
    subst hτ
    cases p with
    | pre s tx ty j pol => trivial
    | startPick tx => exact (hnu ((graphGame_isUniv (Ph.startPick tx) _).mpr trivial)).elim
    | exStep tx ty => exact (hnu ((graphGame_isUniv (Ph.exStep tx ty) _).mpr trivial)).elim
    | allCert tx ty => exact (hnu ((graphGame_isUniv (Ph.allCert tx ty) _).mpr trivial)).elim
    | main tx =>
      obtain ⟨q, σs, rfl⟩ := graphGame_move_shape hm
      obtain ⟨m, hmem, htgt, hkeep, hguard⟩ := (graphGame_move _ _ _ _).mp hm
      rw [movesFrom_main] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem2
      · have htgt' : (preEntry (n := n) D hD .won tx tx).tgt = q := htgt
        subst htgt'
        rw [moveTo_keepAll hkeep] at hwin
        exact .won ((wins_preEntry I hdn hK .won tx tx pts).mp hwin)
      · obtain ⟨ty, -, hmem3⟩ := List.mem_flatMap.mp hmem2
        rcases List.mem_cons.mp hmem3 with rfl | hmem4
        · have htgt' : Ph.exStep tx ty = q := htgt
          subst htgt'
          obtain ⟨pts', hst, hag⟩ := moveTo_keepMid (q := Ph.exStep tx ty) hkeep hguard
          obtain ⟨h1, h2, h3⟩ := ih _ pts' hst
          have hx : nodeAt I hdn tx 0 pts' = nodeAt I hdn tx 0 pts :=
            nodeAt_zero_congr I hdn tx pts' pts fun i hi => hag i (by omega)
          rw [hx] at h1 h2
          exact .ex h1 h2 h3
        · rw [List.mem_singleton] at hmem4
          subst hmem4
          have htgt' : Ph.allCert tx ty = q := htgt
          subst htgt'
          obtain ⟨pts', hst, hag⟩ := moveTo_keepMid (q := Ph.allCert tx ty) hkeep hguard
          obtain ⟨h1, h2, h3⟩ := ih _ pts' hst
          have hx : nodeAt I hdn tx 0 pts' = nodeAt I hdn tx 0 pts :=
            nodeAt_zero_congr I hdn tx pts' pts fun i hi => hag i (by omega)
          rw [hx] at h1 h2 h3
          exact .all h1 ⟨_, h2⟩ h3
    | allStep tx ty =>
      obtain ⟨q, σs, rfl⟩ := graphGame_move_shape hm
      obtain ⟨m, hmem, htgt, hkeep, hguard⟩ := (graphGame_move _ _ _ _).mp hm
      rw [movesFrom_allStep hdn] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem2
      · have htgt' : (preEntry (n := n) D hD .notmv tx ty).tgt = q := htgt
        subst htgt'
        rw [moveTo_keepAll hkeep] at hwin
        exact Or.inl ((wins_preEntry I hdn hK .notmv tx ty pts).mp hwin)
      · rw [List.mem_singleton] at hmem2
        subst hmem2
        have htgt' : Ph.main ty = q := htgt
        subst htgt'
        refine Or.inr ?_
        rw [← nodeAt_shift I hdn ty pts]
        exact ih _ _ (moveTo_keepShift hdn hkeep)
  | @all a hu hex hall ih =>
    intro p pts hτ
    subst hτ
    cases p with
    | pre s tx ty j pol => trivial
    | main tx => exact ((graphGame_isUniv _ _).mp hu).elim
    | allStep tx ty => exact ((graphGame_isUniv _ _).mp hu).elim
    | startPick tx =>
      refine ⟨(wins_preEntry I hdn hK .st tx tx pts).mp (hall _ (move_keepAll (Ph.startPick tx)
        (preEntry D hD .st tx tx) (by rw [movesFrom_startPick]; simp) rfl rfl pts)), ?_⟩
      exact ih _ (move_keepAll (Ph.startPick tx) (⟨.main tx, keepAll n, []⟩ : MoveTo T Dm n)
        (by rw [movesFrom_startPick]; simp) rfl rfl pts) _ _ rfl
    | exStep tx ty =>
      refine ⟨(wins_preEntry I hdn hK .notuniv tx tx pts).mp
          (hall _ (move_keepAll (Ph.exStep tx ty)
          (preEntry D hD .notuniv tx tx) (by rw [movesFrom_exStep hdn]; simp) rfl rfl pts)),
        (wins_preEntry I hdn hK .mv tx ty pts).mp (hall _ (move_keepAll (Ph.exStep tx ty)
          (preEntry D hD .mv tx ty) (by rw [movesFrom_exStep hdn]; simp) rfl rfl pts)), ?_⟩
      rw [← nodeAt_shift I hdn ty pts]
      exact ih _ (move_keepShift hdn (Ph.exStep tx ty)
        (⟨.main ty, keepShift d n hdn, []⟩ : MoveTo T Dm n)
        (by rw [movesFrom_exStep hdn]; simp) rfl rfl pts) _ _ rfl
    | allCert tx ty =>
      refine ⟨(wins_preEntry I hdn hK .univ tx tx pts).mp
          (hall _ (move_keepAll (Ph.allCert tx ty)
          (preEntry D hD .univ tx tx) (by rw [movesFrom_allCert]; simp) rfl rfl pts)),
        (wins_preEntry I hdn hK .mv tx ty pts).mp (hall _ (move_keepAll (Ph.allCert tx ty)
          (preEntry D hD .mv tx ty) (by rw [movesFrom_allCert]; simp) rfl rfl pts)), ?_⟩
      intro z hz
      obtain ⟨pts', hag, hz'⟩ := exists_pts_of_node I hdn z pts
      have hmove : (graphGame X hn D hD K).Move (nodeState (Ph.allCert tx ty) pts)
          (nodeState (Ph.allStep tx z.1) pts') :=
        move_keepMid (Ph.allCert tx ty)
          (⟨.allStep tx z.1, keepOff n (isMid d n), midRounds d n⟩ : MoveTo T Dm n)
          (by rw [movesFrom_allCert]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_map.mpr ⟨z.1, mem_finEnum _, rfl⟩))) rfl rfl pts pts' hag
      have hx : nodeAt I hdn tx 0 pts' = nodeAt I hdn tx 0 pts :=
        nodeAt_zero_congr I hdn tx pts' pts fun i hi => hag i (by omega)
      rcases ih _ hmove _ pts' rfl with hno | hyes
      · rw [hx, hz'] at hno
        exact absurd hz hno
      · rw [hz'] at hyes
        exact hyes

include hK in
/-- **Every win of the interpreted graph is a win of the game.** -/
theorem wins_of_winsOn :
    letI := X.mapLinearOrder A
    letI := I.mapStructure (X.Map A)
    ∀ x : I.Map (X.Map A), WinsOn (I.Map (X.Map A)) x →
      ∀ (tx : T) (pts : Fin n → X.Map A), x = nodeAt I hdn tx 0 pts →
        (graphGame X hn D hD K).Wins (nodeState (.main tx) pts) := by
  letI := X.mapLinearOrder A
  letI := I.mapStructure (X.Map A)
  intro x h
  induction h with
  | @won a hw =>
    intro tx pts hx
    subst hx
    refine .ex (fun hu' => ((graphGame_isUniv _ _).mp hu').elim) (move_keepAll (Ph.main tx)
      (preEntry D hD .won tx tx) (by rw [movesFrom_main]; simp) rfl rfl pts) ?_
    exact (wins_preEntry I hdn hK .won tx tx pts).mpr hw
  | @ex a b hnu hm hwin ih =>
    intro tx pts hx
    subst hx
    obtain ⟨pts', hag, hb⟩ := exists_pts_of_node I hdn b pts
    have hx' : nodeAt I hdn tx 0 pts' = nodeAt I hdn tx 0 pts :=
      nodeAt_zero_congr I hdn tx pts' pts fun i hi => hag i (by omega)
    refine .ex (fun hu' => ((graphGame_isUniv _ _).mp hu').elim) (move_keepMid (Ph.main tx)
      (⟨.exStep tx b.1, keepOff n (isMid d n), midRounds d n⟩ : MoveTo T Dm n)
      (by rw [movesFrom_main]
          exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
            ⟨b.1, mem_finEnum _, List.mem_cons_self⟩)) rfl rfl pts pts' hag) ?_
    refine .all ((graphGame_isUniv (Ph.exStep tx b.1) _).mpr trivial)
      ⟨_, move_keepAll (Ph.exStep tx b.1)
      (preEntry D hD .notuniv tx tx) (by rw [movesFrom_exStep hdn]; simp) rfl rfl pts'⟩ ?_
    intro τ hmv
    obtain ⟨q, σs, rfl⟩ := graphGame_move_shape hmv
    obtain ⟨m, hmem, htgt, hkeep, hguard⟩ := (graphGame_move _ _ _ _).mp hmv
    rw [movesFrom_exStep hdn] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem2
    · have htgt' : (preEntry (n := n) D hD .notuniv tx tx).tgt = q := htgt
      subst htgt'
      rw [moveTo_keepAll hkeep]
      exact (wins_preEntry I hdn hK .notuniv tx tx pts').mpr
        (show ¬AGUniv (nodeAt I hdn tx 0 pts') by rw [hx']; exact hnu)
    · rcases List.mem_cons.mp hmem2 with rfl | hmem3
      · have htgt' : (preEntry (n := n) D hD .mv tx b.1).tgt = q := htgt
        subst htgt'
        rw [moveTo_keepAll hkeep]
        exact (wins_preEntry I hdn hK .mv tx b.1 pts').mpr
          (show AGMove (nodeAt I hdn tx 0 pts') (nodeAt I hdn b.1 1 pts') by
            rw [hx', hb]; exact hm)
      · rw [List.mem_singleton] at hmem3
        subst hmem3
        have htgt' : Ph.main b.1 = q := htgt
        subst htgt'
        rw [moveTo_keepShift hdn hkeep]
        exact ih b.1 _ (by rw [nodeAt_shift]; exact hb.symm)
  | @all a hu hex hall ih =>
    intro tx pts hx
    subst hx
    obtain ⟨y0, hy0⟩ := hex
    obtain ⟨pts', hag, hb⟩ := exists_pts_of_node I hdn y0 pts
    have hx' : nodeAt I hdn tx 0 pts' = nodeAt I hdn tx 0 pts :=
      nodeAt_zero_congr I hdn tx pts' pts fun i hi => hag i (by omega)
    refine .ex (fun hu' => ((graphGame_isUniv _ _).mp hu').elim) (move_keepMid (Ph.main tx)
      (⟨.allCert tx y0.1, keepOff n (isMid d n), midRounds d n⟩ : MoveTo T Dm n)
      (by rw [movesFrom_main]
          exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
            ⟨y0.1, mem_finEnum _, List.mem_cons_of_mem _ List.mem_cons_self⟩))
      rfl rfl pts pts' hag) ?_
    refine .all ((graphGame_isUniv (Ph.allCert tx y0.1) _).mpr trivial)
      ⟨_, move_keepAll (Ph.allCert tx y0.1)
      (preEntry D hD .univ tx tx) (by rw [movesFrom_allCert]; simp) rfl rfl pts'⟩ ?_
    intro τ hmv
    obtain ⟨q, σs, rfl⟩ := graphGame_move_shape hmv
    obtain ⟨m, hmem, htgt, hkeep, hguard⟩ := (graphGame_move _ _ _ _).mp hmv
    rw [movesFrom_allCert] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem2
    · have htgt' : (preEntry (n := n) D hD .univ tx tx).tgt = q := htgt
      subst htgt'
      rw [moveTo_keepAll hkeep]
      exact (wins_preEntry I hdn hK .univ tx tx pts').mpr
        (show AGUniv (nodeAt I hdn tx 0 pts') by rw [hx']; exact hu)
    · rcases List.mem_cons.mp hmem2 with rfl | hmem3
      · have htgt' : (preEntry (n := n) D hD .mv tx y0.1).tgt = q := htgt
        subst htgt'
        rw [moveTo_keepAll hkeep]
        exact (wins_preEntry I hdn hK .mv tx y0.1 pts').mpr
          (show AGMove (nodeAt I hdn tx 0 pts') (nodeAt I hdn y0.1 1 pts') by
            rw [hx', hb]; exact hy0)
      · obtain ⟨tz, -, hmz⟩ := List.mem_map.mp hmem3
        subst hmz
        have htgt' : Ph.allStep tx tz = q := htgt
        subst htgt'
        obtain ⟨pts'', hst, hag2⟩ := moveTo_keepMid (q := Ph.allStep tx tz) hkeep hguard
        rw [hst]
        have hx'' : nodeAt I hdn tx 0 pts'' = nodeAt I hdn tx 0 pts :=
          (nodeAt_zero_congr I hdn tx pts'' pts' fun i hi => hag2 i (by omega)).trans hx'
        by_cases hmv2 : AGMove (nodeAt I hdn tx 0 pts'') (nodeAt I hdn tz 1 pts'')
        · rw [hx''] at hmv2
          refine .ex (fun hu' => ((graphGame_isUniv _ _).mp hu').elim)
            (move_keepShift hdn (Ph.allStep tx tz)
            (⟨.main tz, keepShift d n hdn, []⟩ : MoveTo T Dm n)
            (by rw [movesFrom_allStep hdn]; simp) rfl rfl pts'') ?_
          exact ih _ hmv2 tz _ (by rw [nodeAt_shift])
        · refine .ex (fun hu' => ((graphGame_isUniv _ _).mp hu').elim)
            (move_keepAll (Ph.allStep tx tz)
            (preEntry D hD .notmv tx tz) (by rw [movesFrom_allStep hdn]; simp) rfl rfl pts'') ?_
          exact (wins_preEntry I hdn hK .notmv tx tz pts'').mpr hmv2

end ExpExpansion

end DescriptiveComplexity
