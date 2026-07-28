/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Matrix

/-!
# The blocks of the prefix, and what the matrix says

The five kinds of block the prefix of the constructed instance splits into –
the endpoints, then a midpoint, a universal bit and a pair per level, then the
auxiliary variables (`DescriptiveComplexity.tEnds`, `DescriptiveComplexity.tZ`,
`DescriptiveComplexity.tB`, `DescriptiveComplexity.tUV`,
`DescriptiveComplexity.tAux`) – together with the reading of the matrix they make
possible.

Grouping the clause tags by what they talk about turns the matrix into four
conditions (`DescriptiveComplexity.qsatMatrix_iff_parts`): the source valuation
witnesses `DescriptiveComplexity.IsStart` for the first endpoint
(`DescriptiveComplexity.SrcPart`), the target valuation witnesses
`DescriptiveComplexity.IsGoal` for the second (`DescriptiveComplexity.TgtPart`),
the transition valuation and the bit `sE` witness one move of the walk at the
bottom level (`DescriptiveComplexity.StepPart`), and every level relates its own
pair to the pair it receives from above (`DescriptiveComplexity.LevPart`).

Each group is the conjunction of two clauses of opposite signs, which is why the
conditions come out as equivalences rather than implications.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The block coordinates -/

section Triples

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sS (p q : A) : keyTriple .sS p q = (0, q, 0) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sT (p q : A) : keyTriple .sT p q = (0, q, 0) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sZ (p q : A) : keyTriple .sZ p q = (1, p, 0) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sB (p q : A) : keyTriple .sB p q = (1, p, 1) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sU (p q : A) : keyTriple .sU p q = (1, p, 2) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sV (p q : A) : keyTriple .sV p q = (1, p, 2) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_aS (p q : A) : keyTriple .aS p q = (2, q, 0) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_aT (p q : A) : keyTriple .aT p q = (2, q, 0) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_aP (p q : A) : keyTriple .aP p q = (2, q, 0) := rfl
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sE (p q : A) : keyTriple .sE p q = (2, q, 0) := rfl

variable (A) in
/-- The block coordinates of the two endpoints of the walk: the first block. -/
noncomputable def tEnds : ℕ × A × ℕ := (0, qBot A, 0)

/-- The block coordinates of the midpoint guessed at level `ℓ`. -/
def tZ (ℓ : A) : ℕ × A × ℕ := (1, ℓ, 0)

/-- The block coordinates of the universal bit of level `ℓ`. -/
def tB (ℓ : A) : ℕ × A × ℕ := (1, ℓ, 1)

/-- The block coordinates of the pair passed below level `ℓ`. -/
def tUV (ℓ : A) : ℕ × A × ℕ := (1, ℓ, 2)

variable (A) in
/-- The block coordinates of the auxiliary variables: the last block. -/
noncomputable def tAux : ℕ × A × ℕ := (2, qBot A, 0)

end Triples

/-! ### Overriding a block -/

section Over

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {B : QM A → Prop} (τ ν : QM A → Prop)

omit [Finite A] [Nonempty A] in
theorem qOver_out {v : QVarTag} {p q : A} (h : ¬B (qVar v p q)) :
    qOver B τ ν (qVar v p q) ↔ τ (qVar v p q) :=
  ⟨fun hx => (hx.resolve_left fun hh => h hh.1).2, fun hx => Or.inr ⟨h, hx⟩⟩

omit [Finite A] [Nonempty A] in
theorem qOver_in {v : QVarTag} {p q : A} (h : B (qVar v p q)) :
    qOver B τ ν (qVar v p q) ↔ ν (qVar v p q) :=
  ⟨fun hx => (hx.resolve_right fun hh => hh.1 h).2, fun hx => Or.inl ⟨h, hx⟩⟩

end Over

/-! ### Two clauses of opposite signs make an equivalence -/

section Pairs

theorem iff_of_or_not {P Q : Prop} (h0 : ¬P ∨ Q) (h1 : P ∨ ¬Q) : P ↔ Q :=
  ⟨fun hp => h0.resolve_left (not_not_intro hp), fun hq => h1.resolve_right (not_not_intro hq)⟩

theorem or_forall_of_forall_or {ι : Sort*} {R : Prop} {P : ι → Prop} (h : ∀ i, R ∨ P i) :
    R ∨ ∀ i, P i := by
  classical
  by_cases hR : R
  · exact Or.inl hR
  · exact Or.inr fun i => (h i).resolve_left hR

end Pairs

/-! ### What the matrix says -/

section Parts

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable (σ : QM A → Prop)

/-- The source valuation satisfies the source clauses and reads the source
endpoint of the walk. -/
def SrcPart : Prop :=
  ClausesHold A (valS σ) tsSrcCl ∧ ReadsCur A (valS σ) (stS σ)

/-- The target valuation satisfies the target clauses and reads the target
endpoint of the walk. -/
def TgtPart : Prop :=
  ClausesHold A (valT σ) tsTgtCl ∧ ReadsCur A (valT σ) (stT σ)

/-- The base case of the recursion: either the equality branch, or the
transition valuation satisfying the transition clauses while reading the first
component of the bottom pair and writing the second. -/
def StepPart : Prop :=
  (bitE σ ∨ ClausesHold A (valP σ) tsStepCl) ∧
    (∀ m : A, IsMaxSV m → (bitE σ ∨ ReadsCur A (valP σ) (stU σ m))) ∧
    (∀ m : A, IsMaxSV m → (bitE σ ∨ WritesNext A (valP σ) (stV σ m))) ∧
    ∀ m : A, IsMaxSV m → (¬bitE σ ∨ ∀ x : A, IsSV x → (stU σ m x ↔ stV σ m x))

/-- Every level relates its pair to the pair it receives from above. -/
def LevPart : Prop :=
  ∀ (b w s : Bool) (ℓ x : A), IsSV ℓ → IsSV x → LevSat σ b w s ℓ x

theorem matrix_cSrc_iff :
    (∀ p q : A, QClOn .cSrc p q → ClSat σ .cSrc p q) ↔ ClausesHold A (valS σ) tsSrcCl :=
  ⟨fun h c hc => (clSat_cSrc σ c (qBot A)).mp (h c (qBot A) ⟨hc, isBot_qBot A⟩),
    fun h p q hg => (clSat_cSrc σ p q).mpr (h p hg.1)⟩

theorem matrix_cTgt_iff :
    (∀ p q : A, QClOn .cTgt p q → ClSat σ .cTgt p q) ↔ ClausesHold A (valT σ) tsTgtCl :=
  ⟨fun h c hc => (clSat_cTgt σ c (qBot A)).mp (h c (qBot A) ⟨hc, isBot_qBot A⟩),
    fun h p q hg => (clSat_cTgt σ p q).mpr (h p hg.1)⟩

theorem matrix_cStep_iff :
    (∀ p q : A, QClOn .cStep p q → ClSat σ .cStep p q) ↔
      (bitE σ ∨ ClausesHold A (valP σ) tsStepCl) := by
  constructor
  · intro h
    refine or_forall_of_forall_or fun c => or_forall_of_forall_or fun hc => ?_
    exact (clSat_cStep σ c (qBot A)).mp (h c (qBot A) ⟨hc, isBot_qBot A⟩)
  · rintro (hb | h) p q hg
    · exact (clSat_cStep σ p q).mpr (Or.inl hb)
    · exact (clSat_cStep σ p q).mpr (Or.inr (h p hg.1))

theorem matrix_lS_iff :
    (∀ (s : Bool) (p q : A), QClOn (.lS s) p q → ClSat σ (.lS s) p q) ↔
      ReadsCur A (valS σ) (stS σ) := by
  classical
  constructor
  · intro h x hx
    have h0 := (clSat_lS σ false ⟨hx, isBot_qBot A⟩).mp (h false x (qBot A) ⟨hx, isBot_qBot A⟩)
    have h1 := (clSat_lS σ true ⟨hx, isBot_qBot A⟩).mp (h true x (qBot A) ⟨hx, isBot_qBot A⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    exact iff_of_or_not h0 h1
  · intro h s p q hg
    rw [clSat_lS σ s hg]
    have hp := h p hg.1
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : valS σ p
      · exact Or.inr (hp.mp hv)
      · exact Or.inl hv
    · by_cases hv : valS σ p
      · exact Or.inl hv
      · exact Or.inr fun hs => hv (hp.mpr hs)

theorem matrix_lT_iff :
    (∀ (s : Bool) (p q : A), QClOn (.lT s) p q → ClSat σ (.lT s) p q) ↔
      ReadsCur A (valT σ) (stT σ) := by
  classical
  constructor
  · intro h x hx
    have h0 := (clSat_lT σ false ⟨hx, isBot_qBot A⟩).mp (h false x (qBot A) ⟨hx, isBot_qBot A⟩)
    have h1 := (clSat_lT σ true ⟨hx, isBot_qBot A⟩).mp (h true x (qBot A) ⟨hx, isBot_qBot A⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    exact iff_of_or_not h0 h1
  · intro h s p q hg
    rw [clSat_lT σ s hg]
    have hp := h p hg.1
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : valT σ p
      · exact Or.inr (hp.mp hv)
      · exact Or.inl hv
    · by_cases hv : valT σ p
      · exact Or.inl hv
      · exact Or.inr fun hs => hv (hp.mpr hs)

theorem matrix_lU_iff :
    (∀ (s : Bool) (p q : A), QClOn (.lU s) p q → ClSat σ (.lU s) p q) ↔
      ∀ m : A, IsMaxSV m → (bitE σ ∨ ReadsCur A (valP σ) (stU σ m)) := by
  classical
  constructor
  · intro h m hm
    refine or_forall_of_forall_or fun x => or_forall_of_forall_or fun hx => ?_
    have h0 := (clSat_lU σ false ⟨hx, isBot_qBot A⟩).mp (h false x (qBot A) ⟨hx, isBot_qBot A⟩)
    have h1 := (clSat_lU σ true ⟨hx, isBot_qBot A⟩).mp (h true x (qBot A) ⟨hx, isBot_qBot A⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    rcases h0 with hb | h0
    · exact Or.inl hb
    rcases h1 with hb | h1
    · exact Or.inl hb
    refine Or.inr (iff_of_or_not ?_ ?_)
    · rcases h0 with hn | ⟨m', hm', hu⟩
      · exact Or.inl hn
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hu)
    · rcases h1 with hv | ⟨m', hm', hu⟩
      · exact Or.inl hv
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hu)
  · intro h s p q hg
    rw [clSat_lU σ s hg]
    obtain ⟨m, hm⟩ := exists_isMaxSV hg.1
    rcases h m hm with hb | hr
    · exact Or.inl hb
    have hp := hr p hg.1
    refine Or.inr ?_
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : valP σ p
      · exact Or.inr ⟨m, hm, hp.mp hv⟩
      · exact Or.inl hv
    · by_cases hv : valP σ p
      · exact Or.inl hv
      · exact Or.inr ⟨m, hm, fun hu => hv (hp.mpr hu)⟩

theorem matrix_lV_iff :
    (∀ (s : Bool) (p q : A), QClOn (.lV s) p q → ClSat σ (.lV s) p q) ↔
      ∀ m : A, IsMaxSV m → (bitE σ ∨ WritesNext A (valP σ) (stV σ m)) := by
  classical
  constructor
  · intro h m hm
    refine or_forall_of_forall_or fun x => or_forall_of_forall_or fun y =>
      or_forall_of_forall_or fun hx => or_forall_of_forall_or fun hxy => ?_
    have h0 := (clSat_lV σ false ⟨hx, hxy⟩).mp (h false x y ⟨hx, hxy⟩)
    have h1 := (clSat_lV σ true ⟨hx, hxy⟩).mp (h true x y ⟨hx, hxy⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    rcases h0 with hb | h0
    · exact Or.inl hb
    rcases h1 with hb | h1
    · exact Or.inl hb
    refine Or.inr (iff_of_or_not ?_ ?_)
    · rcases h0 with hn | ⟨m', hm', hu⟩
      · exact Or.inl hn
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hu)
    · rcases h1 with hv | ⟨m', hm', hu⟩
      · exact Or.inl hv
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hu)
  · intro h s p q hg
    rw [clSat_lV σ s hg]
    obtain ⟨m, hm⟩ := exists_isMaxSV hg.1
    rcases h m hm with hb | hw
    · exact Or.inl hb
    have hp := hw p q hg.1 hg.2
    refine Or.inr ?_
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : valP σ q
      · exact Or.inr ⟨m, hm, hp.mp hv⟩
      · exact Or.inl hv
    · by_cases hv : valP σ q
      · exact Or.inl hv
      · exact Or.inr ⟨m, hm, fun hu => hv (hp.mpr hu)⟩

theorem matrix_bE_iff :
    (∀ (s : Bool) (p q : A), QClOn (.bE s) p q → ClSat σ (.bE s) p q) ↔
      ∀ m : A, IsMaxSV m → (¬bitE σ ∨ ∀ x : A, IsSV x → (stU σ m x ↔ stV σ m x)) := by
  classical
  constructor
  · intro h m hm
    refine or_forall_of_forall_or fun x => or_forall_of_forall_or fun hx => ?_
    have h0 := (clSat_bE σ false ⟨hx, isBot_qBot A⟩).mp (h false x (qBot A) ⟨hx, isBot_qBot A⟩)
    have h1 := (clSat_bE σ true ⟨hx, isBot_qBot A⟩).mp (h true x (qBot A) ⟨hx, isBot_qBot A⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    rcases h0 with hb | h0
    · exact Or.inl hb
    rcases h1 with hb | h1
    · exact Or.inl hb
    refine Or.inr (iff_of_or_not ?_ ?_)
    · rcases h0 with ⟨m', hm', hu⟩ | ⟨m', hm', hv⟩
      · exact Or.inl (isMaxSV_unique hm' hm ▸ hu)
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hv)
    · rcases h1 with ⟨m', hm', hu⟩ | ⟨m', hm', hv⟩
      · exact Or.inl (isMaxSV_unique hm' hm ▸ hu)
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hv)
  · intro h s p q hg
    rw [clSat_bE σ s hg]
    obtain ⟨m, hm⟩ := exists_isMaxSV hg.1
    rcases h m hm with hb | hu
    · exact Or.inl hb
    have hp := hu p hg.1
    refine Or.inr ?_
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : stU σ m p
      · exact Or.inr ⟨m, hm, hp.mp hv⟩
      · exact Or.inl ⟨m, hm, hv⟩
    · by_cases hv : stU σ m p
      · exact Or.inl ⟨m, hm, hv⟩
      · exact Or.inr ⟨m, hm, fun hw => hv (hp.mpr hw)⟩

theorem matrix_lev_iff :
    (∀ (b w s : Bool) (ℓ x : A), QClOn (.lev b w s) ℓ x → ClSat σ (.lev b w s) ℓ x) ↔
      LevPart σ :=
  ⟨fun h b w s ℓ x hl hx => (clSat_lev σ b w s ⟨hl, hx⟩).mp (h b w s ℓ x ⟨hl, hx⟩),
    fun h b w s ℓ x hg => (clSat_lev σ b w s hg).mpr (h b w s ℓ x hg.1 hg.2)⟩

/-- **The matrix, read semantically.** -/
theorem qsatMatrix_iff_parts :
    QsatMatrix σ ↔ SrcPart σ ∧ TgtPart σ ∧ StepPart σ ∧ LevPart σ := by
  rw [qsatMatrix_iff]
  constructor
  · intro h
    exact ⟨⟨(matrix_cSrc_iff σ).mp fun p q => h .cSrc p q,
        (matrix_lS_iff σ).mp fun s p q => h (.lS s) p q⟩,
      ⟨(matrix_cTgt_iff σ).mp fun p q => h .cTgt p q,
        (matrix_lT_iff σ).mp fun s p q => h (.lT s) p q⟩,
      ⟨(matrix_cStep_iff σ).mp fun p q => h .cStep p q,
        (matrix_lU_iff σ).mp fun s p q => h (.lU s) p q,
        (matrix_lV_iff σ).mp fun s p q => h (.lV s) p q,
        (matrix_bE_iff σ).mp fun s p q => h (.bE s) p q⟩,
      (matrix_lev_iff σ).mp fun b w s ℓ x => h (.lev b w s) ℓ x⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6, h7, h8⟩, h9⟩ c p q
    cases c with
    | cSrc => exact (matrix_cSrc_iff σ).mpr h1 p q
    | cTgt => exact (matrix_cTgt_iff σ).mpr h3 p q
    | cStep => exact (matrix_cStep_iff σ).mpr h5 p q
    | lS s => exact (matrix_lS_iff σ).mpr h2 s p q
    | lT s => exact (matrix_lT_iff σ).mpr h4 s p q
    | lU s => exact (matrix_lU_iff σ).mpr h6 s p q
    | lV s => exact (matrix_lV_iff σ).mpr h7 s p q
    | bE s => exact (matrix_bE_iff σ).mpr h8 s p q
    | lev b w s => exact (matrix_lev_iff σ).mpr h9 b w s p q

end Parts

end DescriptiveComplexity
