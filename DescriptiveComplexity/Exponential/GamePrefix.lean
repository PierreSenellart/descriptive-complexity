/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameSpec

/-!
# The prefix phases play the alternating prefix

The first of the two correctness halves of the graph game: from a phase
`pre s tx ty j pol`, the game plays exactly `j` more rounds, alternating from
`pol`, and is then decided by the kernel of the question `s`
(`DescriptiveComplexity.ExpExpansion.wins_pre`). The proof is a plain induction
on `j` against `DescriptiveComplexity.altBlockQuant`'s own recursion — which is
what carrying the polarity in the phase buys.

Two things make the base and the step line up.

* **A leaf is existential and moveless.** `movesFrom` returns `[]` at `j = 0`
  and `Ph.IsUniv` is false there, so the position wins exactly when it wins
  outright, i.e. exactly when the kernel holds. A question the player cannot
  prove therefore *loses*, which is the whole point of asking it as a move.
* **Filling a round is changing one round.** The move out of `pre … (j+1) …`
  freezes every round but `n - (j + 1)`, and
  `DescriptiveComplexity.ExpExpansion.fillRounds_succ` is the identity between
  filling `j + 1` rounds of the state left and filling `j` rounds of the state
  entered.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### `Fin.cons` at an index known by its value -/

section Cons

variable {α : Type} {k : ℕ}

theorem cons_of_val_zero (v : α) (τs : Fin k → α) (j : Fin (k + 1)) (h : (j : ℕ) = 0) :
    (Fin.cons v τs : Fin (k + 1) → α) j = v := by
  have hj : j = 0 := Fin.ext (by simp [h])
  rw [hj, Fin.cons_zero]

theorem cons_of_val_succ (v : α) (τs : Fin k → α) (j : Fin (k + 1)) (m : Fin k)
    (h : (j : ℕ) = (m : ℕ) + 1) : (Fin.cons v τs : Fin (k + 1) → α) j = τs m := by
  have hj : j = m.succ := Fin.ext (by simp [h])
  rw [hj, Fin.cons_succ]

end Cons

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : ExpExpansion L} {T : Type} [Finite T] {d n Dm : ℕ}
variable {A : Type} [instL : L.Structure A] [LinearOrder A]

/-! ### Filling the last rounds -/

/-- The rounds `ρs` with the last `k` overwritten by `τs`, in order. -/
noncomputable def fillRounds {k : ℕ} (hk : k ≤ n) (ρs : Fin n → X.pointBlock.Assignment A)
    (τs : Fin k → X.pointBlock.Assignment A) : Fin n → X.pointBlock.Assignment A :=
  fun i =>
    if _ : n - k ≤ (i : ℕ) then τs ⟨(i : ℕ) - (n - k), by have := i.isLt; omega⟩ else ρs i

omit instL [LinearOrder A] in
theorem fillRounds_zero (hk : 0 ≤ n) (ρs : Fin n → X.pointBlock.Assignment A)
    (τs : Fin 0 → X.pointBlock.Assignment A) : fillRounds hk ρs τs = ρs := by
  funext i
  rw [fillRounds, dif_neg]
  have := i.isLt
  omega

omit instL [LinearOrder A] in
/-- **Filling one more round is filling one fewer round of the state the move
enters**, provided that state differs from the one it leaves only at the round
being filled. -/
theorem fillRounds_succ (k : ℕ) (hk : k + 1 ≤ n)
    (ρs σs : Fin n → X.pointBlock.Assignment A) (τs : Fin k → X.pointBlock.Assignment A)
    (r : Fin n) (hr : (r : ℕ) = n - (k + 1)) (hag : ∀ i, i ≠ r → ρs i = σs i) :
    fillRounds hk ρs (Fin.cons (σs r) τs) =
      fillRounds (X := X) (n := n) (k := k) (Nat.le_of_succ_le hk) σs τs := by
  classical
  funext i
  have hi := i.isLt
  simp only [fillRounds]
  rcases Nat.lt_or_ge (i : ℕ) (n - (k + 1)) with hlt | hge
  · have hne : i ≠ r := by
      intro hc
      have : (i : ℕ) = (r : ℕ) := congrArg Fin.val hc
      omega
    rw [dif_neg (by omega), dif_neg (by omega)]
    exact hag i hne
  · rcases eq_or_ne (i : ℕ) (n - (k + 1)) with heq | hne
    · have hir : i = r := Fin.ext (by omega)
      rw [dif_pos (by omega), dif_neg (by omega), show σs i = σs r from congrArg σs hir]
      exact cons_of_val_zero _ τs _ (show (i : ℕ) - (n - (k + 1)) = 0 by omega)
    · rw [dif_pos (by omega), dif_pos (by omega)]
      refine cons_of_val_succ _ τs _ ⟨(i : ℕ) - (n - k), by omega⟩ ?_
      change (i : ℕ) - (n - (k + 1)) = ((i : ℕ) - (n - k)) + 1
      omega

/-! ### The moves out of a prefix phase -/

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}
variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

theorem movesFrom_pre_zero (hk : 0 < Dm + 1) (s : Sub) (tx ty : T) (pol : Bool) :
    movesFrom hn D hD (.pre s tx ty ⟨0, hk⟩ pol) = [] :=
  rfl

theorem movesFrom_pre_succ (k : ℕ) (hk : k + 1 < Dm + 1) (r : Fin n)
    (hr : (r : ℕ) = n - (k + 1)) (s : Sub) (tx ty : T) (pol : Bool) :
    movesFrom hn D hD (.pre s tx ty ⟨k + 1, hk⟩ pol) =
      [⟨.pre s tx ty ⟨k, by omega⟩ (!pol), keepOff n (fun i => decide (i = r)), []⟩] := by
  have hreq : (⟨n - (k + 1), by omega⟩ : Fin n) = r := Fin.ext hr.symm
  rw [← hreq]
  rfl

/-! ### The prefix phases -/

/-- **A prefix phase plays the prefix.** From `pre s tx ty j pol` the game fills
the last `j` rounds, alternating from `pol`, and the kernel of `s` decides the
leaf. -/
theorem wins_pre : ∀ (k : ℕ) (hk : k < Dm + 1) (pol : Bool) (s : Sub) (tx ty : T)
    (ρs : Fin n → X.pointBlock.Assignment A),
    ((graphGame X hn D hD K).Wins (stateAssign (.pre s tx ty ⟨k, hk⟩ pol) ρs) ↔
      altBlockQuant A X.pointBlock k
        (fun τs => @Sentence.Realize _ A
          (roundStructure X (fillRounds (X := X) (n := n) (by omega) ρs τs))
          (K s tx ty)) pol) := by
  intro k
  induction k with
  | zero =>
    intro hk pol s tx ty ρs
    have hnomove : ∀ τ, ¬(graphGame X hn D hD K).Move
        (stateAssign (.pre s tx ty ⟨0, hk⟩ pol) ρs) τ := by
      intro τ hm
      obtain ⟨q, σs, rfl⟩ := graphGame_move_shape hm
      obtain ⟨m, hmem, -⟩ := (graphGame_move _ _ _ _).mp hm
      rw [movesFrom_pre_zero] at hmem
      simp at hmem
    have hnu : ¬(graphGame X hn D hD K).IsUniv
        (stateAssign (.pre s tx ty ⟨0, hk⟩ pol) ρs) := by
      rw [graphGame_isUniv]
      rintro ⟨h0, -⟩
      exact h0 rfl
    have hwon : ((graphGame X hn D hD K).IsWon
        (stateAssign (.pre s tx ty ⟨0, hk⟩ pol) ρs) ↔
      @Sentence.Realize _ A
        ((repMerged X.pointBlock n).structure₁ (L := L.sum Language.order)
          (repBlockAssign X.pointBlock A n ρs)) (K s tx ty)) := by
      rw [graphGame_isWon]
      constructor
      · rintro ⟨s', tx', ty', pol', heq, hr⟩
        injection heq with h1 h2 h3 h4 h5
        subst h1
        subst h2
        subst h3
        exact hr
      · intro hr
        exact ⟨s, tx, ty, pol, rfl, hr⟩
    have key : ∀ τ, (graphGame X hn D hD K).Wins τ →
        τ = stateAssign (.pre s tx ty ⟨0, hk⟩ pol) ρs →
        (graphGame X hn D hD K).IsWon τ := by
      intro τ h
      cases h with
      | won hw => intro _; exact hw
      | @ex a b _ hm _ => intro hτ; subst hτ; exact absurd hm (hnomove _)
      | @all a hu _ _ => intro hτ; subst hτ; exact absurd hu hnu
    rw [altBlockQuant, fillRounds_zero]
    exact ⟨fun h => hwon.mp (key _ h rfl), fun h => .won (hwon.mpr h)⟩
  | succ k ih =>
    intro hk pol s tx ty ρs
    have hkk : k < Dm + 1 := by omega
    have hrlt : n - (k + 1) < n := by omega
    set r : Fin n := ⟨n - (k + 1), hrlt⟩ with hrdef
    have hrv : (r : ℕ) = n - (k + 1) := rfl
    have hmv : ∀ (q : Ph T Dm) (σs : Fin n → X.pointBlock.Assignment A),
        ((graphGame X hn D hD K).Move (stateAssign (.pre s tx ty ⟨k + 1, hk⟩ pol) ρs)
            (stateAssign q σs) ↔
          q = .pre s tx ty ⟨k, hkk⟩ (!pol) ∧ ∀ i, i ≠ r → ρs i = σs i) := by
      intro q σs
      rw [graphGame_move, movesFrom_pre_succ k hk r hrv]
      constructor
      · rintro ⟨m, hmem, htgt, hkeep, -⟩
        rw [List.mem_singleton] at hmem
        subst hmem
        exact ⟨htgt.symm, fun i hi =>
          (forall_keepOff _ ρs σs).mp hkeep i (by simpa using hi)⟩
      · rintro ⟨rfl, hag⟩
        exact ⟨_, List.mem_singleton_self _, rfl,
          (forall_keepOff _ ρs σs).mpr fun i hi => hag i (by simpa using hi), by simp⟩
    have hnotwon : ¬(graphGame X hn D hD K).IsWon
        (stateAssign (.pre s tx ty ⟨k + 1, hk⟩ pol) ρs) := by
      rw [graphGame_isWon]
      rintro ⟨s', tx', ty', pol', heq, -⟩
      injection heq with h1 h2 h3 h4 h5
      exact absurd (congrArg Fin.val h4) (Nat.succ_ne_zero k)
    have hshape : ∀ τ, (graphGame X hn D hD K).Move
        (stateAssign (.pre s tx ty ⟨k + 1, hk⟩ pol) ρs) τ →
        ∃ σs, τ = stateAssign (.pre s tx ty ⟨k, hkk⟩ (!pol)) σs := by
      intro τ hm
      obtain ⟨q, σs, rfl⟩ := graphGame_move_shape hm
      obtain ⟨rfl, -⟩ := (hmv q σs).mp hm
      exact ⟨σs, rfl⟩
    have hstep : ∀ (σs : Fin n → X.pointBlock.Assignment A), (∀ i, i ≠ r → ρs i = σs i) →
        ((graphGame X hn D hD K).Wins (stateAssign (.pre s tx ty ⟨k, hkk⟩ (!pol)) σs) ↔
          altBlockQuant A X.pointBlock k
            (fun τs => @Sentence.Realize _ A
              (roundStructure X (fillRounds (X := X) (n := n) (by omega) ρs
                (Fin.cons (σs r) τs))) (K s tx ty)) (!pol)) := by
      intro σs hag
      refine (ih hkk (!pol) s tx ty σs).trans (altBlockQuant_congr k _ _ (fun τs => ?_) (!pol))
      rw [fillRounds_succ k (by omega) ρs σs τs r hrv hag]
    have hagupd : ∀ v : X.pointBlock.Assignment A, ∀ i, i ≠ r → ρs i = Function.update ρs r v i :=
      fun v i hi => (Function.update_of_ne hi _ _).symm
    cases pol with
    | true =>
      have hnu : ¬(graphGame X hn D hD K).IsUniv
          (stateAssign (.pre s tx ty ⟨k + 1, hk⟩ true) ρs) := by
        rw [graphGame_isUniv]
        rintro ⟨-, h2⟩
        exact absurd h2 (by simp)
      have key : ∀ τ, (graphGame X hn D hD K).Wins τ →
          τ = stateAssign (.pre s tx ty ⟨k + 1, hk⟩ true) ρs →
          ∃ σs : Fin n → X.pointBlock.Assignment A, (∀ i, i ≠ r → ρs i = σs i) ∧
            (graphGame X hn D hD K).Wins (stateAssign (.pre s tx ty ⟨k, hkk⟩ false) σs) := by
        intro τ h
        cases h with
        | won hw => intro hτ; subst hτ; exact absurd hw hnotwon
        | @ex a b _ hm hwin =>
          intro hτ
          subst hτ
          obtain ⟨σs, rfl⟩ := hshape b hm
          exact ⟨σs, ((hmv _ σs).mp hm).2, hwin⟩
        | @all a hu _ _ => intro hτ; subst hτ; exact absurd hu hnu
      rw [altBlockQuant]
      constructor
      · intro h
        obtain ⟨σs, hag, hwin⟩ := key _ h rfl
        exact ⟨σs r, (hstep σs hag).mp hwin⟩
      · rintro ⟨v, hv⟩
        refine .ex hnu ((hmv _ _).mpr ⟨rfl, hagupd v⟩)
          ((hstep _ (hagupd v)).mpr ?_)
        rw [Function.update_self]
        exact hv
    | false =>
      have hu : (graphGame X hn D hD K).IsUniv
          (stateAssign (.pre s tx ty ⟨k + 1, hk⟩ false) ρs) :=
        (graphGame_isUniv _ _).mpr ⟨Nat.succ_ne_zero k, rfl⟩
      have key : ∀ τ, (graphGame X hn D hD K).Wins τ →
          τ = stateAssign (.pre s tx ty ⟨k + 1, hk⟩ false) ρs →
          ∀ σs : Fin n → X.pointBlock.Assignment A, (∀ i, i ≠ r → ρs i = σs i) →
            (graphGame X hn D hD K).Wins (stateAssign (.pre s tx ty ⟨k, hkk⟩ true) σs) := by
        intro τ h
        cases h with
        | won hw => intro hτ; subst hτ; exact absurd hw hnotwon
        | @ex a b hnu' _ _ => intro hτ; subst hτ; exact absurd hu hnu'
        | @all a hu' hex hall =>
          intro hτ
          subst hτ
          exact fun σs hag => hall _ ((hmv _ _).mpr ⟨rfl, hag⟩)
      rw [altBlockQuant]
      constructor
      · intro h v
        have hw := (hstep _ (hagupd v)).mp (key _ h rfl _ (hagupd v))
        rwa [Function.update_self] at hw
      · intro h
        refine .all hu ⟨_, (hmv _ _).mpr ⟨rfl, hagupd (X.pointBlock.botAssign A)⟩⟩ ?_
        intro τ hm
        obtain ⟨σs, rfl⟩ := hshape τ hm
        exact (hstep σs ((hmv _ σs).mp hm).2).mpr (h (σs r))

end ExpExpansion

end DescriptiveComplexity
