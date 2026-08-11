/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.AltQuant

/-!
# Levels a prefix's matrix does not read

The EXPSPACE program runs the quantifier prefix of a step formula on its VAL
register, one **inner argument block per level**: level `j` of the pack is
block `j`, whatever the pack. The register, though, has one block per level
of the *longest* pack (`ki`), and the enumeration it can run – the binary
increment from the empty address to the inner top – plays **every** block.
So the machine plays a prefix that is too long at both ends:

* the levels **below** the pack's free-variable count are played although the
  matrix reads them off the working address (the MIRROR register) and not off
  VAL;
* the levels **above** the pack's own length are played although nothing
  reads them at all.

Both are harmless, and this file is why: a level whose matrix ignores it may
be skipped, whatever its polarity (`DescriptiveComplexity.Pfp.altQuantFrom_skip`,
over a nonempty domain), and a matrix reading only the first `n` of `N`
coordinates plays as its restriction
(`DescriptiveComplexity.Pfp.altQuantFrom_pad`). The third lemma,
`DescriptiveComplexity.Pfp.altQuantFrom_congr_mat`, is the one that lets the
machine's leaf predicate differ from the pack's away from the valuations the
walk can reach: from level `j` the walk only ever changes coordinates at or
above `j`, so what the matrix does below them is the caller's business.

Everything here is about `DescriptiveComplexity.altQuantFrom` alone; no
machine, no encoding.
-/

namespace DescriptiveComplexity

namespace Pfp

variable {α : Type*} {pol : ℕ → Bool}

/-! ### The matrix is only read where the walk can go -/

/-- **Two matrices agreeing on the valuations the walk reaches play the
same.** From level `j` the prefix only ever changes coordinates at or above
`j`, so the matrix is read only at valuations agreeing with the starting one
below `j`. -/
theorem altQuantFrom_congr_mat {n : ℕ} {P P' : (Fin n → α) → Prop} {j : ℕ}
    {v : Fin n → α}
    (h : ∀ w : Fin n → α, (∀ i : Fin n, (i : ℕ) < j → w i = v i) → (P w ↔ P' w)) :
    altQuantFrom pol P j v ↔ altQuantFrom pol P' j v := by
  have key : ∀ (r j : ℕ) (v : Fin n → α), n - j ≤ r →
      (∀ w : Fin n → α, (∀ i : Fin n, (i : ℕ) < j → w i = v i) → (P w ↔ P' w)) →
      (altQuantFrom pol P j v ↔ altQuantFrom pol P' j v) := by
    intro r
    induction r with
    | zero =>
      intro j v hr h
      rw [altQuantFrom_of_le (by omega), altQuantFrom_of_le (by omega)]
      exact h v fun _ _ => rfl
    | succ r ih =>
      intro j v hr h
      by_cases hjn : j < n
      · have hstep : ∀ a : α, ∀ w : Fin n → α,
            (∀ i : Fin n, (i : ℕ) < j + 1 → w i = Function.update v ⟨j, hjn⟩ a i) →
            (P w ↔ P' w) := by
          intro a w hw
          refine h w fun i hi => (hw i (by omega)).trans ?_
          exact Function.update_of_ne
            (fun hc => absurd (congrArg Fin.val hc) (Nat.ne_of_lt hi)) _ _
        by_cases hp : pol j = true
        · rw [altQuantFrom_ex hjn hp, altQuantFrom_ex hjn hp]
          exact exists_congr fun a => ih (j + 1) _ (by omega) (hstep a)
        · rw [altQuantFrom_all hjn (by simpa using hp),
            altQuantFrom_all hjn (by simpa using hp)]
          exact forall_congr' fun a => ih (j + 1) _ (by omega) (hstep a)
      · rw [altQuantFrom_of_le (by omega), altQuantFrom_of_le (by omega)]
        exact h v fun _ _ => rfl
  exact key _ j v le_rfl h

/-! ### Levels the matrix ignores -/

/-- **A coordinate the matrix ignores may be overwritten** at any point of the
walk: the prefix's value does not change. -/
theorem altQuantFrom_update_irrel {n : ℕ} {P : (Fin n → α) → Prop} {ℓ : Fin n}
    (hirr : ∀ (w : Fin n → α) (a : α), P (Function.update w ℓ a) ↔ P w) :
    ∀ (j : ℕ) (v : Fin n → α) (a : α),
      altQuantFrom pol P j (Function.update v ℓ a) ↔ altQuantFrom pol P j v := by
  have key : ∀ (r j : ℕ) (v : Fin n → α) (a : α), n - j ≤ r →
      (altQuantFrom pol P j (Function.update v ℓ a) ↔ altQuantFrom pol P j v) := by
    intro r
    induction r with
    | zero =>
      intro j v a hr
      rw [altQuantFrom_of_le (by omega), altQuantFrom_of_le (by omega)]
      exact hirr v a
    | succ r ih =>
      intro j v a hr
      by_cases hjn : j < n
      · by_cases hlj : ℓ = ⟨j, hjn⟩
        · subst hlj
          by_cases hp : pol j = true
          · rw [altQuantFrom_ex hjn hp, altQuantFrom_ex hjn hp]
            exact exists_congr fun b => by rw [Function.update_idem]
          · rw [altQuantFrom_all hjn (by simpa using hp),
              altQuantFrom_all hjn (by simpa using hp)]
            exact forall_congr' fun b => by rw [Function.update_idem]
        · have hcomm : ∀ b : α,
              Function.update (Function.update v ℓ a) ⟨j, hjn⟩ b =
                Function.update (Function.update v ⟨j, hjn⟩ b) ℓ a :=
            fun b => Function.update_comm hlj _ _ v
          by_cases hp : pol j = true
          · rw [altQuantFrom_ex hjn hp, altQuantFrom_ex hjn hp]
            refine exists_congr fun b => ?_
            rw [hcomm b]
            exact ih (j + 1) _ a (by omega)
          · rw [altQuantFrom_all hjn (by simpa using hp),
              altQuantFrom_all hjn (by simpa using hp)]
            refine forall_congr' fun b => ?_
            rw [hcomm b]
            exact ih (j + 1) _ a (by omega)
      · rw [altQuantFrom_of_le (by omega), altQuantFrom_of_le (by omega)]
        exact hirr v a
  exact fun j v a => key _ j v a le_rfl

variable [Nonempty α]

/-- **A stretch of levels the matrix ignores may be skipped**: playing them
changes nothing, whichever player they belong to. This is what lets the
machine's inner loop enumerate the blocks the pack's free variables occupy –
the matrix reads those off the working address – and the blocks past its
prefix. -/
theorem altQuantFrom_skip {n : ℕ} {P : (Fin n → α) → Prop} {j j' : ℕ}
    (hjj : j ≤ j')
    (hirr : ∀ ℓ : Fin n, j ≤ (ℓ : ℕ) → (ℓ : ℕ) < j' →
      ∀ (w : Fin n → α) (a : α), P (Function.update w ℓ a) ↔ P w)
    (v : Fin n → α) : altQuantFrom pol P j v ↔ altQuantFrom pol P j' v := by
  have key : ∀ (r j : ℕ), j ≤ j' → j' - j ≤ r →
      (∀ ℓ : Fin n, j ≤ (ℓ : ℕ) → (ℓ : ℕ) < j' →
        ∀ (w : Fin n → α) (a : α), P (Function.update w ℓ a) ↔ P w) →
      ∀ v : Fin n → α, (altQuantFrom pol P j v ↔ altQuantFrom pol P j' v) := by
    intro r
    induction r with
    | zero =>
      intro j hjj' hr _ v
      rw [show j = j' by omega]
    | succ r ih =>
      intro j hjj' hr hirr' v
      rcases Nat.eq_or_lt_of_le hjj' with rfl | hlt
      · rfl
      by_cases hjn : j < n
      · have hnext : ∀ ℓ : Fin n, j + 1 ≤ (ℓ : ℕ) → (ℓ : ℕ) < j' →
            ∀ (w : Fin n → α) (a : α), P (Function.update w ℓ a) ↔ P w :=
          fun ℓ h1 h2 => hirr' ℓ (by omega) h2
        have hbody : ∀ a : α,
            altQuantFrom pol P (j + 1) (Function.update v ⟨j, hjn⟩ a) ↔
              altQuantFrom pol P j' v := by
          intro a
          refine (ih (j + 1) (by omega) (by omega) hnext _).trans ?_
          exact altQuantFrom_update_irrel (hirr' ⟨j, hjn⟩ le_rfl hlt) j' v a
        by_cases hp : pol j = true
        · rw [altQuantFrom_ex hjn hp]
          exact ⟨fun ⟨a, ha⟩ => (hbody a).mp ha,
            fun hc => ⟨Classical.arbitrary α, (hbody _).mpr hc⟩⟩
        · rw [altQuantFrom_all hjn (by simpa using hp)]
          exact ⟨fun hc => (hbody (Classical.arbitrary α)).mp (hc _),
            fun hc a => (hbody a).mpr hc⟩
      · rw [altQuantFrom_of_le (by omega), altQuantFrom_of_le (by omega)]
  exact key _ j hjj le_rfl hirr v

/-! ### A prefix padded with unread levels -/

/-- **A prefix over more coordinates than its matrix reads plays as its
restriction**: the machine's register has one block per level of the longest
pack, and the extra ones are the innermost quantifiers over variables nothing
reads. -/
theorem altQuantFrom_pad {n N : ℕ} (hnN : n ≤ N) {P : (Fin n → α) → Prop}
    {j : ℕ} (hj : j ≤ n) (v : Fin N → α) :
    altQuantFrom pol (fun w : Fin N → α => P fun i : Fin n => w (Fin.castLE hnN i)) j v ↔
      altQuantFrom pol P j fun i : Fin n => v (Fin.castLE hnN i) := by
  have hirr : ∀ ℓ : Fin N, n ≤ (ℓ : ℕ) → (ℓ : ℕ) < N →
      ∀ (w : Fin N → α) (a : α),
        (fun w : Fin N → α => P fun i : Fin n => w (Fin.castLE hnN i))
          (Function.update w ℓ a) ↔
        (fun w : Fin N → α => P fun i : Fin n => w (Fin.castLE hnN i)) w := by
    intro ℓ hℓ _ w a
    refine iff_of_eq (congrArg P (funext fun i => ?_))
    have hne : (Fin.castLE hnN i : Fin N) ≠ ℓ := by
      intro hc
      have hval : ((Fin.castLE hnN i : Fin N) : ℕ) = (i : ℕ) := rfl
      have hi : (ℓ : ℕ) = (i : ℕ) := by rw [← hc, hval]
      have := i.isLt
      omega
    exact Function.update_of_ne hne _ _
  have hbase : ∀ v : Fin N → α,
      (altQuantFrom pol (fun w : Fin N → α => P fun i : Fin n => w (Fin.castLE hnN i)) n v ↔
        altQuantFrom pol P n fun i : Fin n => v (Fin.castLE hnN i)) := by
    intro v
    have h1 :
        altQuantFrom pol (fun w : Fin N → α => P fun i : Fin n => w (Fin.castLE hnN i)) n v ↔
          altQuantFrom pol (fun w : Fin N → α => P fun i : Fin n => w (Fin.castLE hnN i)) N v :=
      altQuantFrom_skip hnN (fun ℓ h1 h2 => hirr ℓ h1 h2) v
    have h2 :
        altQuantFrom pol (fun w : Fin N → α => P fun i : Fin n => w (Fin.castLE hnN i)) N v =
          P fun i : Fin n => v (Fin.castLE hnN i) := altQuantFrom_of_le le_rfl v
    have h3 : altQuantFrom pol P n (fun i : Fin n => v (Fin.castLE hnN i)) =
        P fun i : Fin n => v (Fin.castLE hnN i) := altQuantFrom_of_le le_rfl _
    rw [h3]
    exact h1.trans (iff_of_eq h2)
  have key : ∀ (r j : ℕ), j ≤ n → n - j ≤ r → ∀ v : Fin N → α,
      (altQuantFrom pol (fun w : Fin N → α => P fun i : Fin n => w (Fin.castLE hnN i)) j v ↔
        altQuantFrom pol P j fun i : Fin n => v (Fin.castLE hnN i)) := by
    intro r
    induction r with
    | zero =>
      intro j hjn hr v
      have hje : j = n := by omega
      rw [hje]
      exact hbase v
    | succ r ih =>
      intro j hjn hr v
      rcases Nat.eq_or_lt_of_le hjn with heq | hlt
      · rw [heq]
        exact hbase v
      · have hjN : j < N := lt_of_lt_of_le hlt hnN
        have hupd : ∀ a : α,
            (fun i : Fin n => Function.update v ⟨j, hjN⟩ a (Fin.castLE hnN i)) =
              Function.update (fun i : Fin n => v (Fin.castLE hnN i)) ⟨j, hlt⟩ a := by
          intro a
          funext i
          by_cases hij : i = ⟨j, hlt⟩
          · subst hij
            rw [Function.update_self]
            exact Function.update_self _ _ _
          · have hne : (Fin.castLE hnN i : Fin N) ≠ ⟨j, hjN⟩ := by
              intro hc
              have hval : ((Fin.castLE hnN i : Fin N) : ℕ) = j := congrArg Fin.val hc
              exact hij (Fin.ext hval)
            rw [Function.update_of_ne hij]
            exact Function.update_of_ne hne _ _
        by_cases hp : pol j = true
        · rw [altQuantFrom_ex hjN hp, altQuantFrom_ex hlt hp]
          refine exists_congr fun a => ?_
          rw [← hupd a]
          exact ih (j + 1) (by omega) (by omega) _
        · rw [altQuantFrom_all hjN (by simpa using hp),
            altQuantFrom_all hlt (by simpa using hp)]
          refine forall_congr' fun a => ?_
          rw [← hupd a]
          exact ih (j + 1) (by omega) (by omega) _
  exact key _ j hj le_rfl v

end Pfp

end DescriptiveComplexity
