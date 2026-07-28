/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Peel

/-!
# The innermost block: the base case of the recursion

The last block of the prefix quantifies the three auxiliary valuations and the
bit `sE`, and is immediately followed by the matrix. Peeling it
(`DescriptiveComplexity.game_aux`) turns the position it opens into exactly three
independent conditions – the source endpoint is a start state, the target
endpoint is a goal state, and the pair passed below the last level is one move
of the walk (`DescriptiveComplexity.SavStep`) – together with the level clauses,
which the auxiliary variables do not touch.

The three conditions are independent because the three valuations are read on
disjoint sets of elements, which is what lets the single existential quantifier
over the block be split (`DescriptiveComplexity.auxVal`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Leaf

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### Readouts a block does not touch -/

omit [Finite A] [Nonempty A] in
theorem not_qBlk_of_ne {T : ℕ × A × ℕ} {v : QVarTag} {p q : A} (h : keyTriple v p q ≠ T) :
    ¬QBlk T (qVar v p q) := fun hb => h (qBlk_iff.mp hb).2

omit [Finite A] [Nonempty A] in
theorem readout_out {T : ℕ × A × ℕ} {v : QVarTag} {p q : A} (τ ν : QM A → Prop)
    (h : keyTriple v p q ≠ T) : qOver (QBlk T) τ ν (qVar v p q) ↔ τ (qVar v p q) :=
  qOver_out τ ν (not_qBlk_of_ne h)

omit [Finite A] [Nonempty A] in
theorem readout_in {T : ℕ × A × ℕ} {v : QVarTag} {p q : A} (τ ν : QM A → Prop)
    (hv : QVarOn v p q) (h : keyTriple v p q = T) :
    qOver (QBlk T) τ ν (qVar v p q) ↔ ν (qVar v p q) :=
  qOver_in τ ν (qBlk_iff.mpr ⟨hv, h⟩)

@[simp]
theorem stS_over_tAux (τ ν : QM A → Prop) : stS (qOver (QBlk (tAux A)) τ ν) = stS τ := by
  funext a
  exact propext (readout_out τ ν (by simp [tAux]))

@[simp]
theorem stT_over_tAux (τ ν : QM A → Prop) : stT (qOver (QBlk (tAux A)) τ ν) = stT τ := by
  funext a
  exact propext (readout_out τ ν (by simp [tAux]))

@[simp]
theorem stU_over_tAux (τ ν : QM A → Prop) (ℓ : A) :
    stU (qOver (QBlk (tAux A)) τ ν) ℓ = stU τ ℓ := by
  funext a
  exact propext (readout_out τ ν (by simp [tAux]))

@[simp]
theorem stV_over_tAux (τ ν : QM A → Prop) (ℓ : A) :
    stV (qOver (QBlk (tAux A)) τ ν) ℓ = stV τ ℓ := by
  funext a
  exact propext (readout_out τ ν (by simp [tAux]))

@[simp]
theorem stZ_over_tAux (τ ν : QM A → Prop) (ℓ : A) :
    stZ (qOver (QBlk (tAux A)) τ ν) ℓ = stZ τ ℓ := by
  funext a
  exact propext (readout_out τ ν (by simp [tAux]))

@[simp]
theorem bitB_over_tAux (τ ν : QM A → Prop) (ℓ : A) :
    bitB (qOver (QBlk (tAux A)) τ ν) ℓ ↔ bitB τ ℓ :=
  readout_out τ ν (by simp [tAux])

theorem levSat_over_tAux (τ ν : QM A → Prop) (b w s : Bool) (ℓ x : A) :
    LevSat (qOver (QBlk (tAux A)) τ ν) b w s ℓ x ↔ LevSat τ b w s ℓ x := by
  simp only [LevSat, stS_over_tAux, stT_over_tAux, stU_over_tAux, stV_over_tAux,
    stZ_over_tAux, bitB_over_tAux]

/-! ### Splitting the last existential quantifier -/

/-- The assignment of the last block made of three valuations and a bit. -/
def auxVal (f g h : A → Prop) (e : Prop) : QM A → Prop := fun y =>
  (∃ a : A, y = qVar .aS a (qBot A) ∧ f a) ∨ (∃ a : A, y = qVar .aT a (qBot A) ∧ g a) ∨
    (∃ a : A, y = qVar .aP a (qBot A) ∧ h a) ∨ (y = qVar .sE (qBot A) (qBot A) ∧ e)

omit [Finite A] [Nonempty A] in
private theorem qVar_ne {v v' : QVarTag} (hv : v ≠ v') (p q p' q' : A) :
    qVar v p q ≠ qVar v' p' q' := fun he => hv (qVar_inj he).1

@[simp]
theorem valS_over_tAux (τ : QM A → Prop) (f g h : A → Prop) (e : Prop) :
    valS (qOver (QBlk (tAux A)) τ (auxVal f g h e)) = f := by
  funext a
  refine propext ((readout_in τ _ (by simp [QVarOn]) (by simp [tAux])).trans ?_)
  simp only [auxVal]
  constructor
  · rintro (⟨a', he, hf⟩ | ⟨a', he, -⟩ | ⟨a', he, -⟩ | ⟨he, -⟩)
    · exact (qVar_inj he).2.1 ▸ hf
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
  · exact fun hf => Or.inl ⟨a, rfl, hf⟩

@[simp]
theorem valT_over_tAux (τ : QM A → Prop) (f g h : A → Prop) (e : Prop) :
    valT (qOver (QBlk (tAux A)) τ (auxVal f g h e)) = g := by
  funext a
  refine propext ((readout_in τ _ (by simp [QVarOn]) (by simp [tAux])).trans ?_)
  simp only [auxVal]
  constructor
  · rintro (⟨a', he, -⟩ | ⟨a', he, hg⟩ | ⟨a', he, -⟩ | ⟨he, -⟩)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact (qVar_inj he).2.1 ▸ hg
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
  · exact fun hg => Or.inr (Or.inl ⟨a, rfl, hg⟩)

@[simp]
theorem valP_over_tAux (τ : QM A → Prop) (f g h : A → Prop) (e : Prop) :
    valP (qOver (QBlk (tAux A)) τ (auxVal f g h e)) = h := by
  funext a
  refine propext ((readout_in τ _ (by simp [QVarOn]) (by simp [tAux])).trans ?_)
  simp only [auxVal]
  constructor
  · rintro (⟨a', he, -⟩ | ⟨a', he, -⟩ | ⟨a', he, hh⟩ | ⟨he, -⟩)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact (qVar_inj he).2.1 ▸ hh
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
  · exact fun hh => Or.inr (Or.inr (Or.inl ⟨a, rfl, hh⟩))

@[simp]
theorem bitE_over_tAux (τ : QM A → Prop) (f g h : A → Prop) (e : Prop) :
    bitE (qOver (QBlk (tAux A)) τ (auxVal f g h e)) ↔ e := by
  refine (readout_in τ _ (by simp [QVarOn]) (by simp [tAux])).trans ?_
  simp only [auxVal]
  constructor
  · rintro (⟨a', he, -⟩ | ⟨a', he, -⟩ | ⟨a', he, -⟩ | ⟨-, he⟩)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact absurd he (qVar_ne (by decide) _ _ _ _)
    · exact he
  · exact fun he => Or.inr (Or.inr (Or.inr ⟨trivial, he⟩))

/-! ### The base case -/

/-- **The innermost block, played**: the auxiliary valuations witness that the
source endpoint is a start state, that the target endpoint is a goal state, and
that the pair passed below the last level is one move of the walk; the level
clauses do not mention them. -/
theorem game_aux (τ : QM A → Prop) :
    QsatWins (QPlayed (tAux A)) τ ↔
      IsStart A (stS τ) ∧ IsGoal A (stT τ) ∧ LevPart τ ∧
        ∀ m : A, IsMaxSV m → SavStep (stCls (A := A)) (StepRel A) (stU τ m) (stV τ m) := by
  classical
  rw [qsatWins_block_ex qsatWf_qsatInterp (qDownClosed_qPlayed _) (qBlock_qBlk _) blk_ex_tAux]
  have hleaf : ∀ ν : QM A → Prop,
      QsatWins (qUnion (QPlayed (tAux A)) (QBlk (tAux A))) (qOver (QBlk (tAux A)) τ ν) ↔
        SrcPart (qOver (QBlk (tAux A)) τ ν) ∧ TgtPart (qOver (QBlk (tAux A)) τ ν) ∧
          StepPart (qOver (QBlk (tAux A)) τ ν) ∧ LevPart (qOver (QBlk (tAux A)) τ ν) :=
    fun ν => (qsatWins_leaf_iff all_played).trans (qsatMatrix_iff_parts _)
  simp only [hleaf]
  constructor
  · rintro ⟨ν, ⟨hs1, hs2⟩, ⟨ht1, ht2⟩, hstep, hlev⟩
    rw [stS_over_tAux] at hs2
    rw [stT_over_tAux] at ht2
    refine ⟨⟨_, hs1, hs2⟩, ⟨_, ht1, ht2⟩, fun b w s ℓ x hl hx =>
      (levSat_over_tAux τ ν b w s ℓ x).mp (hlev b w s ℓ x hl hx), fun m hm => ?_⟩
    by_cases he : bitE (qOver (QBlk (tAux A)) τ ν)
    · refine Or.inl (stCls_eq_iff.mpr ?_)
      have := (hstep.2.2.2 m hm).resolve_left (not_not_intro he)
      rw [stU_over_tAux, stV_over_tAux] at this
      exact this
    · refine Or.inr ⟨_, hstep.1.resolve_left he, ?_, ?_⟩
      · have := (hstep.2.1 m hm).resolve_left he
        rwa [stU_over_tAux] at this
      · have := (hstep.2.2.1 m hm).resolve_left he
        rwa [stV_over_tAux] at this
  · rintro ⟨⟨f, hf1, hf2⟩, ⟨g, hg1, hg2⟩, hlev, hsav⟩
    have hlev' : ∀ (h : A → Prop) (e : Prop),
        LevPart (qOver (QBlk (tAux A)) τ (auxVal f g h e)) :=
      fun h e b w s ℓ x hl hx => (levSat_over_tAux τ _ b w s ℓ x).mpr (hlev b w s ℓ x hl hx)
    by_cases hex : ∃ m : A, IsMaxSV m
    · obtain ⟨m₀, hm₀⟩ := hex
      rcases hsav m₀ hm₀ with hcls | ⟨h', hch, hrc, hwn⟩
      · refine ⟨auxVal f g (fun _ => False) True, ⟨by simpa using hf1, by simpa using hf2⟩,
          ⟨by simpa using hg1, by simpa using hg2⟩, ⟨Or.inl (by simp), fun m hm => Or.inl (by simp),
            fun m hm => Or.inl (by simp), fun m hm => ?_⟩, hlev' _ _⟩
        refine Or.inr fun x hx => ?_
        rw [stU_over_tAux, stV_over_tAux, isMaxSV_unique hm hm₀]
        exact stCls_eq_iff.mp hcls x hx
      · refine ⟨auxVal f g h' False, ⟨by simpa using hf1, by simpa using hf2⟩,
          ⟨by simpa using hg1, by simpa using hg2⟩,
          ⟨Or.inr (by simpa using hch), fun m hm => Or.inr ?_, fun m hm => Or.inr ?_,
            fun m hm => Or.inl (by simp)⟩, hlev' _ _⟩
        · rw [stU_over_tAux, isMaxSV_unique hm hm₀]
          simpa using hrc
        · rw [stV_over_tAux, isMaxSV_unique hm hm₀]
          simpa using hwn
    · refine ⟨auxVal f g (fun _ => False) True, ⟨by simpa using hf1, by simpa using hf2⟩,
        ⟨by simpa using hg1, by simpa using hg2⟩, ⟨Or.inl (by simp), fun m hm => absurd ⟨m, hm⟩ hex,
          fun m hm => absurd ⟨m, hm⟩ hex, fun m hm => absurd ⟨m, hm⟩ hex⟩, hlev' _ _⟩

end Leaf

end DescriptiveComplexity
