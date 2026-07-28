/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Parts

/-!
# Peeling the blocks of the prefix

The prefix of the constructed instance is read block by block: the two endpoints
(`DescriptiveComplexity.tEnds`), then for each level in increasing order its
midpoint (`DescriptiveComplexity.tZ`), its universal bit
(`DescriptiveComplexity.tB`) and the pair it passes below
(`DescriptiveComplexity.tUV`), and finally the auxiliary variables
(`DescriptiveComplexity.tAux`).

The whole of that reading is the five transition lemmas below
(`DescriptiveComplexity.step_ends`, `DescriptiveComplexity.step_z`,
`DescriptiveComplexity.step_b`, `DescriptiveComplexity.step_uv`,
`DescriptiveComplexity.step_last`), each an instance of
`DescriptiveComplexity.qPlayed_step`: recognizing which block comes next is a
computation on block coordinates, and every variable's block coordinates are one
of three shapes (`DescriptiveComplexity.keyTriple_cases`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Peel

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The block coordinates of a variable** are those of the endpoints, of a
slot of a level, or of the auxiliary variables. -/
theorem keyTriple_cases {v : QVarTag} {p q : A} (h : QVarOn v p q) :
    keyTriple v p q = (0, qBot A, 0) ∨
      (∃ ℓ : A, IsSV ℓ ∧ ∃ s : ℕ, s ≤ 2 ∧ keyTriple v p q = (1, ℓ, s)) ∨
      keyTriple v p q = (2, qBot A, 0) := by
  cases v <;> simp only [QVarOn, isBot_iff_eq_qBot] at h
  · exact Or.inl (by rw [keyTriple_sS, h.2])
  · exact Or.inl (by rw [keyTriple_sT, h.2])
  · exact Or.inr (Or.inl ⟨p, h.1, 0, by omega, rfl⟩)
  · exact Or.inr (Or.inl ⟨p, h.1, 2, by omega, rfl⟩)
  · exact Or.inr (Or.inl ⟨p, h.1, 2, by omega, rfl⟩)
  · exact Or.inr (Or.inl ⟨p, h.1, 1, by omega, rfl⟩)
  · exact Or.inr (Or.inr (by rw [keyTriple_aS, h]))
  · exact Or.inr (Or.inr (by rw [keyTriple_aT, h]))
  · exact Or.inr (Or.inr (by rw [keyTriple_aP, h]))
  · exact Or.inr (Or.inr (by rw [keyTriple_sE, h.2]))

/-! ### Comparing block coordinates -/

omit [Language.transSys.Structure A] [Finite A] [Nonempty A] in
theorem tripleLt_mk (g s g' s' : ℕ) (a a' : A) :
    TripleLt ((g, a, s) : ℕ × A × ℕ) (g', a', s') ↔
      (g < g' ∨ (g = g' ∧ (a < a' ∨ (a = a' ∧ s < s')))) := Iff.rfl

omit [Language.transSys.Structure A] [Finite A] [Nonempty A] in
theorem tripleLt_grp {g g' s s' : ℕ} {a a' : A} (h : g < g') :
    TripleLt ((g, a, s) : ℕ × A × ℕ) (g', a', s') := Or.inl h

omit [Language.transSys.Structure A] [Finite A] [Nonempty A] in
theorem not_tripleLt_grp {g g' s s' : ℕ} {a a' : A} (h : g' < g) :
    ¬TripleLt ((g, a, s) : ℕ × A × ℕ) (g', a', s') := by
  rw [tripleLt_mk]
  rintro (h1 | ⟨h1, -⟩) <;> omega

omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem triple_ne_grp {g g' s s' : ℕ} {a a' : A} (h : g ≠ g') :
    ((g, a, s) : ℕ × A × ℕ) ≠ (g', a', s') := fun he => h (congrArg Prod.fst he)

omit [Language.transSys.Structure A] [Finite A] [Nonempty A] in
theorem tripleLt_lev {ℓ'' ℓ : A} {s k : ℕ} :
    TripleLt ((1, ℓ'', s) : ℕ × A × ℕ) (1, ℓ, k) ↔ (ℓ'' < ℓ ∨ (ℓ'' = ℓ ∧ s < k)) := by
  rw [tripleLt_mk]
  simp

omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem triple_eq_lev {ℓ'' ℓ : A} {s k : ℕ} :
    ((1, ℓ'', s) : ℕ × A × ℕ) = (1, ℓ, k) ↔ (ℓ'' = ℓ ∧ s = k) := by
  simp [Prod.mk.injEq]

/-! ### The five transitions -/

/-- Before the endpoints nothing has been quantified. -/
theorem qPlayed_tEnds : QPlayed (tEnds A) = fun _ : QM A => False := by
  funext x
  refine propext ⟨?_, False.elim⟩
  rintro ⟨v, p, q, -, hv, hlt⟩
  rcases keyTriple_cases hv with h | ⟨ℓ, -, s, -, h⟩ | h <;> rw [h, tEnds] at hlt
  · exact tripleLt_irrefl _ hlt
  · exact not_tripleLt_grp (by omega) hlt
  · exact not_tripleLt_grp (by omega) hlt

/-- After the endpoints comes the midpoint of the first level. -/
theorem step_ends {ℓ : A} (hmin : IsMinSV ℓ) :
    qUnion (QPlayed (tEnds A)) (QBlk (tEnds A)) = QPlayed (tZ ℓ) := by
  refine qPlayed_step fun v p q hv => ?_
  rcases keyTriple_cases hv with h | ⟨ℓ'', hℓ'', s, hs, h⟩ | h <;> rw [h, tEnds, tZ]
  · exact iff_of_true (tripleLt_grp (by omega)) (Or.inr rfl)
  · refine iff_of_false ?_ ?_
    · rw [tripleLt_lev]
      rintro (h2 | ⟨-, h3⟩)
      · exact hmin.2 ℓ'' hℓ'' h2
      · omega
    · rintro (h1 | h1)
      · exact not_tripleLt_grp (by omega) h1
      · exact triple_ne_grp (by omega) h1
  · refine iff_of_false (not_tripleLt_grp (by omega)) ?_
    rintro (h1 | h1)
    · exact not_tripleLt_grp (by omega) h1
    · exact triple_ne_grp (by omega) h1

/-- After the midpoint of a level comes its universal bit. -/
theorem step_z (ℓ : A) :
    qUnion (QPlayed (tZ ℓ)) (QBlk (tZ ℓ)) = QPlayed (tB (A := A) ℓ) := by
  refine qPlayed_step fun v p q hv => ?_
  rcases keyTriple_cases hv with h | ⟨ℓ'', -, s, hs, h⟩ | h <;> rw [h, tZ, tB]
  · exact iff_of_true (tripleLt_grp (by omega)) (Or.inl (tripleLt_grp (by omega)))
  · rw [tripleLt_lev]
    constructor
    · rintro (h2 | ⟨h2, h3⟩)
      · exact Or.inl (tripleLt_lev.mpr (Or.inl h2))
      · exact Or.inr (triple_eq_lev.mpr ⟨h2, by omega⟩)
    · rintro (h1 | h1)
      · rcases tripleLt_lev.mp h1 with h2 | ⟨-, h3⟩
        · exact Or.inl h2
        · omega
      · obtain ⟨h2, h3⟩ := triple_eq_lev.mp h1
        exact Or.inr ⟨h2, by omega⟩
  · refine iff_of_false (not_tripleLt_grp (by omega)) ?_
    rintro (h1 | h1)
    · exact not_tripleLt_grp (by omega) h1
    · exact triple_ne_grp (by omega) h1

/-- After the universal bit of a level comes the pair it passes below. -/
theorem step_b (ℓ : A) :
    qUnion (QPlayed (tB ℓ)) (QBlk (tB ℓ)) = QPlayed (tUV (A := A) ℓ) := by
  refine qPlayed_step fun v p q hv => ?_
  rcases keyTriple_cases hv with h | ⟨ℓ'', -, s, hs, h⟩ | h <;> rw [h, tB, tUV]
  · exact iff_of_true (tripleLt_grp (by omega)) (Or.inl (tripleLt_grp (by omega)))
  · rw [tripleLt_lev]
    constructor
    · rintro (h2 | ⟨h2, h3⟩)
      · exact Or.inl (tripleLt_lev.mpr (Or.inl h2))
      · rcases Nat.lt_or_ge s 1 with h4 | h4
        · exact Or.inl (tripleLt_lev.mpr (Or.inr ⟨h2, h4⟩))
        · exact Or.inr (triple_eq_lev.mpr ⟨h2, by omega⟩)
    · rintro (h1 | h1)
      · rcases tripleLt_lev.mp h1 with h2 | ⟨h2, h3⟩
        · exact Or.inl h2
        · exact Or.inr ⟨h2, by omega⟩
      · obtain ⟨h2, h3⟩ := triple_eq_lev.mp h1
        exact Or.inr ⟨h2, by omega⟩
  · refine iff_of_false (not_tripleLt_grp (by omega)) ?_
    rintro (h1 | h1)
    · exact not_tripleLt_grp (by omega) h1
    · exact triple_ne_grp (by omega) h1

/-- After the pair of a level comes the midpoint of the next one. -/
theorem step_uv {ℓ ℓ' : A} (hpred : IsPredSV ℓ ℓ') :
    qUnion (QPlayed (tUV ℓ)) (QBlk (tUV ℓ)) = QPlayed (tZ (A := A) ℓ') := by
  refine qPlayed_step fun v p q hv => ?_
  rcases keyTriple_cases hv with h | ⟨ℓ'', hℓ'', s, hs, h⟩ | h <;> rw [h, tUV, tZ]
  · exact iff_of_true (tripleLt_grp (by omega)) (Or.inl (tripleLt_grp (by omega)))
  · rw [tripleLt_lev]
    constructor
    · rintro (h2 | ⟨-, h3⟩)
      · have hle : ℓ'' ≤ ℓ := by
          rcases lt_or_ge ℓ'' ℓ with h4 | h4
          · exact h4.le
          · rcases h4.lt_or_eq with h5 | h5
            · exact absurd ⟨h5, h2⟩ (hpred.2.2.2 ℓ'' hℓ'')
            · exact h5.ge
        rcases hle.lt_or_eq with h4 | h4
        · exact Or.inl (tripleLt_lev.mpr (Or.inl h4))
        · rcases Nat.lt_or_ge s 2 with h5 | h5
          · exact Or.inl (tripleLt_lev.mpr (Or.inr ⟨h4, h5⟩))
          · exact Or.inr (triple_eq_lev.mpr ⟨h4, by omega⟩)
      · omega
    · rintro (h1 | h1)
      · rcases tripleLt_lev.mp h1 with h2 | ⟨h2, -⟩
        · exact Or.inl (h2.trans hpred.2.2.1)
        · exact Or.inl (h2 ▸ hpred.2.2.1)
      · exact Or.inl ((triple_eq_lev.mp h1).1 ▸ hpred.2.2.1)
  · refine iff_of_false (not_tripleLt_grp (by omega)) ?_
    rintro (h1 | h1)
    · exact not_tripleLt_grp (by omega) h1
    · exact triple_ne_grp (by omega) h1

/-- After the pair of the last level come the auxiliary variables. -/
theorem step_last {ℓ : A} (hmax : IsMaxSV ℓ) :
    qUnion (QPlayed (tUV ℓ)) (QBlk (tUV ℓ)) = QPlayed (tAux A) := by
  refine qPlayed_step fun v p q hv => ?_
  rcases keyTriple_cases hv with h | ⟨ℓ'', hℓ'', s, hs, h⟩ | h <;> rw [h, tUV, tAux]
  · exact iff_of_true (tripleLt_grp (by omega)) (Or.inl (tripleLt_grp (by omega)))
  · refine iff_of_true (tripleLt_grp (by omega)) ?_
    rcases (hmax.le hℓ'').lt_or_eq with h4 | h4
    · exact Or.inl (tripleLt_lev.mpr (Or.inl h4))
    · rcases Nat.lt_or_ge s 2 with h5 | h5
      · exact Or.inl (tripleLt_lev.mpr (Or.inr ⟨h4, h5⟩))
      · exact Or.inr (triple_eq_lev.mpr ⟨h4, by omega⟩)
  · refine iff_of_false (tripleLt_irrefl _) ?_
    rintro (h1 | h1)
    · exact not_tripleLt_grp (by omega) h1
    · exact triple_ne_grp (by omega) h1

/-- Once the auxiliary variables are quantified, everything is. -/
theorem all_played :
    ∀ x : QM A, IsQVar x → qUnion (QPlayed (tAux A)) (QBlk (tAux A)) x := by
  intro x hx
  rcases qm_cases x with ⟨v, p, q, rfl⟩ | ⟨c, p, q, rfl⟩
  · have hv := (isQVar_qVar v p q).mp hx
    rcases keyTriple_cases hv with h | ⟨ℓ, -, s, -, h⟩ | h
    · exact Or.inl (qPlayed_qVar hv (by rw [h, tAux]; exact tripleLt_grp (by omega)))
    · exact Or.inl (qPlayed_qVar hv (by rw [h, tAux]; exact tripleLt_grp (by omega)))
    · exact Or.inr (qBlk_qVar hv (by rw [h, tAux]))
  · exact absurd hx (not_isQVar_qCl c p q)

/-! ### The polarity of each block -/

omit [Finite A] [Nonempty A] in
theorem blk_ex {T : ℕ × A × ℕ}
    (h : ∀ (v : QVarTag) (p q : A), QVarOn v p q → keyTriple v p q = T → v ≠ .sB) :
    ∀ x : QM A, QBlk T x → ¬IsQAll x := by
  rintro x ⟨v, p, q, rfl, hv, he⟩ hall
  exact h v p q hv he ((isQAll_qVar v p q).mp hall).1

omit [Finite A] [Nonempty A] in
theorem blk_all {T : ℕ × A × ℕ}
    (h : ∀ (v : QVarTag) (p q : A), QVarOn v p q → keyTriple v p q = T → v = .sB) :
    ∀ x : QM A, QBlk T x → IsQAll x := by
  rintro x ⟨v, p, q, rfl, hv, he⟩
  exact (isQAll_qVar v p q).mpr ⟨h v p q hv he, hv⟩

theorem blk_ex_tEnds : ∀ x : QM A, QBlk (tEnds A) x → ¬IsQAll x := by
  refine blk_ex fun v p q hv he => ?_
  cases v <;> simp_all [tEnds, Prod.mk.injEq]

omit [Finite A] [Nonempty A] in
theorem blk_ex_tZ (ℓ : A) : ∀ x : QM A, QBlk (tZ ℓ) x → ¬IsQAll x := by
  refine blk_ex fun v p q hv he => ?_
  cases v <;> simp_all [tZ, Prod.mk.injEq]

omit [Finite A] [Nonempty A] in
theorem blk_ex_tUV (ℓ : A) : ∀ x : QM A, QBlk (tUV ℓ) x → ¬IsQAll x := by
  refine blk_ex fun v p q hv he => ?_
  cases v <;> simp_all [tUV, Prod.mk.injEq]

theorem blk_ex_tAux : ∀ x : QM A, QBlk (tAux A) x → ¬IsQAll x := by
  refine blk_ex fun v p q hv he => ?_
  cases v <;> simp_all [tAux, Prod.mk.injEq]

omit [Finite A] [Nonempty A] in
theorem blk_all_tB (ℓ : A) : ∀ x : QM A, QBlk (tB ℓ) x → IsQAll x := by
  refine blk_all fun v p q hv he => ?_
  cases v <;> simp_all [tB, Prod.mk.injEq]

end Peel

end DescriptiveComplexity
