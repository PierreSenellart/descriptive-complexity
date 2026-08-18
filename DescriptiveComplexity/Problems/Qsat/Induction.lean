/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Leaf

/-!
# One level of the recursion

Playing the three blocks of a level – its midpoint, its universal bit, its pair –
is one step of Savitch's recursion (`DescriptiveComplexity.game_step`): the
midpoint is the existentially chosen intermediate state, the universal bit
chooses which of the two halves is checked, and the level clauses force the pair
passed below to be the endpoints of that half. So the position opened by a level
computes `DescriptiveComplexity.SavPow` at one more than the depth its successor
computes.

Iterating that step down the levels and finishing with
`DescriptiveComplexity.game_aux` gives `DescriptiveComplexity.game_level`: the
position opened by a level computes reachability in at most `2 ^ k` moves, `k`
the number of levels from it to the last one.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Induction

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### Readouts the three blocks of a level do not touch -/

@[simp] theorem stS_over_tZ (τ ν : QM A → Prop) (ℓ : A) :
    stS (qOver (QBlk (tZ ℓ)) τ ν) = stS τ := by
  funext a; exact propext (readout_out τ ν (by simp [tZ]))

@[simp] theorem stT_over_tZ (τ ν : QM A → Prop) (ℓ : A) :
    stT (qOver (QBlk (tZ ℓ)) τ ν) = stT τ := by
  funext a; exact propext (readout_out τ ν (by simp [tZ]))

omit [Finite A] [Nonempty A] in
@[simp] theorem stU_over_tZ (τ ν : QM A → Prop) (ℓ ℓ' : A) :
    stU (qOver (QBlk (tZ ℓ)) τ ν) ℓ' = stU τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tZ]))

omit [Finite A] [Nonempty A] in
@[simp] theorem stV_over_tZ (τ ν : QM A → Prop) (ℓ ℓ' : A) :
    stV (qOver (QBlk (tZ ℓ)) τ ν) ℓ' = stV τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tZ]))

@[simp] theorem bitB_over_tZ (τ ν : QM A → Prop) (ℓ ℓ' : A) :
    bitB (qOver (QBlk (tZ ℓ)) τ ν) ℓ' ↔ bitB τ ℓ' :=
  readout_out τ ν (by simp [tZ])

omit [Finite A] [Nonempty A] in
theorem stZ_over_tZ_ne (τ ν : QM A → Prop) {ℓ ℓ' : A} (h : ℓ' ≠ ℓ) :
    stZ (qOver (QBlk (tZ ℓ)) τ ν) ℓ' = stZ τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tZ, h]))

@[simp] theorem stS_over_tB (τ ν : QM A → Prop) (ℓ : A) :
    stS (qOver (QBlk (tB ℓ)) τ ν) = stS τ := by
  funext a; exact propext (readout_out τ ν (by simp [tB]))

@[simp] theorem stT_over_tB (τ ν : QM A → Prop) (ℓ : A) :
    stT (qOver (QBlk (tB ℓ)) τ ν) = stT τ := by
  funext a; exact propext (readout_out τ ν (by simp [tB]))

omit [Finite A] [Nonempty A] in
@[simp] theorem stU_over_tB (τ ν : QM A → Prop) (ℓ ℓ' : A) :
    stU (qOver (QBlk (tB ℓ)) τ ν) ℓ' = stU τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tB]))

omit [Finite A] [Nonempty A] in
@[simp] theorem stV_over_tB (τ ν : QM A → Prop) (ℓ ℓ' : A) :
    stV (qOver (QBlk (tB ℓ)) τ ν) ℓ' = stV τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tB]))

omit [Finite A] [Nonempty A] in
@[simp] theorem stZ_over_tB (τ ν : QM A → Prop) (ℓ ℓ' : A) :
    stZ (qOver (QBlk (tB ℓ)) τ ν) ℓ' = stZ τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tB]))

theorem bitB_over_tB_ne (τ ν : QM A → Prop) {ℓ ℓ' : A} (h : ℓ' ≠ ℓ) :
    bitB (qOver (QBlk (tB ℓ)) τ ν) ℓ' ↔ bitB τ ℓ' :=
  readout_out τ ν (by simp [tB, h])

@[simp] theorem stS_over_tUV (τ ν : QM A → Prop) (ℓ : A) :
    stS (qOver (QBlk (tUV ℓ)) τ ν) = stS τ := by
  funext a; exact propext (readout_out τ ν (by simp [tUV]))

@[simp] theorem stT_over_tUV (τ ν : QM A → Prop) (ℓ : A) :
    stT (qOver (QBlk (tUV ℓ)) τ ν) = stT τ := by
  funext a; exact propext (readout_out τ ν (by simp [tUV]))

omit [Finite A] [Nonempty A] in
@[simp] theorem stZ_over_tUV (τ ν : QM A → Prop) (ℓ ℓ' : A) :
    stZ (qOver (QBlk (tUV ℓ)) τ ν) ℓ' = stZ τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tUV]))

@[simp] theorem bitB_over_tUV (τ ν : QM A → Prop) (ℓ ℓ' : A) :
    bitB (qOver (QBlk (tUV ℓ)) τ ν) ℓ' ↔ bitB τ ℓ' :=
  readout_out τ ν (by simp [tUV])

omit [Finite A] [Nonempty A] in
theorem stU_over_tUV_ne (τ ν : QM A → Prop) {ℓ ℓ' : A} (h : ℓ' ≠ ℓ) :
    stU (qOver (QBlk (tUV ℓ)) τ ν) ℓ' = stU τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tUV, h]))

omit [Finite A] [Nonempty A] in
theorem stV_over_tUV_ne (τ ν : QM A → Prop) {ℓ ℓ' : A} (h : ℓ' ≠ ℓ) :
    stV (qOver (QBlk (tUV ℓ)) τ ν) ℓ' = stV τ ℓ' := by
  funext a; exact propext (readout_out τ ν (by simp [tUV, h]))

/-! ### Assignments of the three blocks of a level -/

/-- The assignment of a midpoint block. -/
def zVal (ℓ : A) (Z : A → Prop) : QM A → Prop := fun y => ∃ a : A, y = qVar .sZ ℓ a ∧ Z a

/-- The assignment of a universal-bit block. -/
def bVal (ℓ : A) (β : Prop) : QM A → Prop := fun y => y = qVar .sB ℓ (qBot A) ∧ β

/-- The assignment of a pair block. -/
def uvVal (ℓ : A) (U V : A → Prop) : QM A → Prop := fun y =>
  (∃ a : A, y = qVar .sU ℓ a ∧ U a) ∨ ∃ a : A, y = qVar .sV ℓ a ∧ V a

omit [Finite A] [Nonempty A] in
theorem stZ_over_zVal (τ : QM A → Prop) {ℓ : A} (hℓ : IsSV ℓ) (Z : A → Prop) {a : A}
    (ha : IsSV a) : stZ (qOver (QBlk (tZ ℓ)) τ (zVal ℓ Z)) ℓ a ↔ Z a := by
  refine (readout_in (v := .sZ) τ _ ⟨hℓ, ha⟩ (by simp [tZ])).trans ?_
  refine ⟨fun ⟨a', he, hz⟩ => (qVar_inj he).2.2 ▸ hz, fun hz => ⟨a, rfl, hz⟩⟩

theorem bitB_over_bVal (τ : QM A → Prop) {ℓ : A} (hℓ : IsSV ℓ) (β : Prop) :
    bitB (qOver (QBlk (tB ℓ)) τ (bVal ℓ β)) ℓ ↔ β := by
  refine (readout_in (v := .sB) τ _ ⟨hℓ, isBot_qBot A⟩ (by simp [tB])).trans ?_
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

omit [Finite A] [Nonempty A] in
theorem stU_over_uvVal (τ : QM A → Prop) {ℓ : A} (hℓ : IsSV ℓ) (U V : A → Prop) {a : A}
    (ha : IsSV a) : stU (qOver (QBlk (tUV ℓ)) τ (uvVal ℓ U V)) ℓ a ↔ U a := by
  refine (readout_in (v := .sU) τ _ ⟨hℓ, ha⟩ (by simp [tUV])).trans ?_
  constructor
  · rintro (⟨a', he, hu⟩ | ⟨a', he, -⟩)
    · exact (qVar_inj he).2.2 ▸ hu
    · exact absurd (qVar_inj he).1 (by decide)
  · exact fun hu => Or.inl ⟨a, rfl, hu⟩

omit [Finite A] [Nonempty A] in
theorem stV_over_uvVal (τ : QM A → Prop) {ℓ : A} (hℓ : IsSV ℓ) (U V : A → Prop) {a : A}
    (ha : IsSV a) : stV (qOver (QBlk (tUV ℓ)) τ (uvVal ℓ U V)) ℓ a ↔ V a := by
  refine (readout_in (v := .sV) τ _ ⟨hℓ, ha⟩ (by simp [tUV])).trans ?_
  constructor
  · rintro (⟨a', he, -⟩ | ⟨a', he, hv⟩)
    · exact absurd (qVar_inj he).1 (by decide)
    · exact (qVar_inj he).2.2 ▸ hv
  · exact fun hv => Or.inr ⟨a, rfl, hv⟩

/-! ### The pair a level receives, and the clauses of the levels above -/

open Classical in
/-- The first component of the pair a level receives: the source endpoint at the
first level, the first component of the level above otherwise. -/
noncomputable def inFst (ℓ : A) (τ : QM A → Prop) : A → Prop :=
  if h : ∃ d : A, IsPredSV d ℓ then stU τ h.choose else stS τ

open Classical in
/-- The second component of the pair a level receives. -/
noncomputable def inSnd (ℓ : A) (τ : QM A → Prop) : A → Prop :=
  if h : ∃ d : A, IsPredSV d ℓ then stV τ h.choose else stT τ

theorem inFst_of_isMinSV {ℓ : A} (h : IsMinSV ℓ) (τ : QM A → Prop) : inFst ℓ τ = stS τ := by
  rw [inFst, dif_neg]
  rintro ⟨d, hd⟩
  exact hd.not_isMinSV h

theorem inSnd_of_isMinSV {ℓ : A} (h : IsMinSV ℓ) (τ : QM A → Prop) : inSnd ℓ τ = stT τ := by
  rw [inSnd, dif_neg]
  rintro ⟨d, hd⟩
  exact hd.not_isMinSV h

theorem inFst_of_isPredSV {d ℓ : A} (h : IsPredSV d ℓ) (τ : QM A → Prop) :
    inFst ℓ τ = stU τ d := by
  have hex : ∃ d : A, IsPredSV d ℓ := ⟨d, h⟩
  rw [inFst, dif_pos hex, isPredSV_unique hex.choose_spec h]

theorem inSnd_of_isPredSV {d ℓ : A} (h : IsPredSV d ℓ) (τ : QM A → Prop) :
    inSnd ℓ τ = stV τ d := by
  have hex : ∃ d : A, IsPredSV d ℓ := ⟨d, h⟩
  rw [inSnd, dif_pos hex, isPredSV_unique hex.choose_spec h]

/-- The clauses of every level strictly above `ℓ` hold. -/
def LevBelow (ℓ : A) (τ : QM A → Prop) : Prop :=
  ∀ (b w s : Bool) (ℓ'' x : A), IsSV ℓ'' → ℓ'' < ℓ → IsSV x → LevSat τ b w s ℓ'' x

/-- The clauses of every level down to `ℓ` hold. -/
def LevUpto (ℓ : A) (τ : QM A → Prop) : Prop :=
  ∀ (b w s : Bool) (ℓ'' x : A), IsSV ℓ'' → ℓ'' ≤ ℓ → IsSV x → LevSat τ b w s ℓ'' x

theorem levUpto_iff {ℓ : A} (hℓ : IsSV ℓ) (τ : QM A → Prop) :
    LevUpto ℓ τ ↔ LevBelow ℓ τ ∧ ∀ (b w s : Bool) (x : A), IsSV x → LevSat τ b w s ℓ x := by
  constructor
  · exact fun h => ⟨fun b w s ℓ'' x hl hlt hx => h b w s ℓ'' x hl hlt.le hx,
      fun b w s x hx => h b w s ℓ x hℓ le_rfl hx⟩
  · rintro ⟨h1, h2⟩ b w s ℓ'' x hl hle hx
    rcases hle.lt_or_eq with hlt | heq
    · exact h1 b w s ℓ'' x hl hlt hx
    · exact heq ▸ h2 b w s x hx

/-- The input value a level clause compares its own component to. -/
theorem levIn_fst_iff {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) (s : Bool) :
    ((IsMinSV ℓ ∧ (stS σ x ↔ s = true)) ∨
        (∃ d : A, IsPredSV d ℓ ∧ (stU σ d x ↔ s = true))) ↔ (inFst ℓ σ x ↔ s = true) := by
  by_cases hmin : IsMinSV ℓ
  · rw [inFst_of_isMinSV hmin]
    constructor
    · rintro (⟨-, h⟩ | ⟨d, hd, -⟩)
      · exact h
      · exact absurd hmin hd.not_isMinSV
    · exact fun h => Or.inl ⟨hmin, h⟩
  · obtain ⟨d, hd⟩ := exists_isPredSV hℓ hmin
    rw [inFst_of_isPredSV hd]
    constructor
    · rintro (⟨h, -⟩ | ⟨d', hd', hu⟩)
      · exact absurd h hmin
      · rwa [isPredSV_unique hd' hd] at hu
    · exact fun h => Or.inr ⟨d, hd, h⟩

theorem levIn_snd_iff {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) (s : Bool) :
    ((IsMinSV ℓ ∧ (stT σ x ↔ s = true)) ∨
        (∃ d : A, IsPredSV d ℓ ∧ (stV σ d x ↔ s = true))) ↔ (inSnd ℓ σ x ↔ s = true) := by
  by_cases hmin : IsMinSV ℓ
  · rw [inSnd_of_isMinSV hmin]
    constructor
    · rintro (⟨-, h⟩ | ⟨d, hd, -⟩)
      · exact h
      · exact absurd hmin hd.not_isMinSV
    · exact fun h => Or.inl ⟨hmin, h⟩
  · obtain ⟨d, hd⟩ := exists_isPredSV hℓ hmin
    rw [inSnd_of_isPredSV hd]
    constructor
    · rintro (⟨h, -⟩ | ⟨d', hd', hv⟩)
      · exact absurd h hmin
      · rwa [isPredSV_unique hd' hd] at hv
    · exact fun h => Or.inr ⟨d, hd, h⟩

/-- **A level clause, spelled out**: the polarity of the universal bit, the
component of the pair it constrains, and the value that component must copy. -/
theorem levSat_iff {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (b w s : Bool) (x : A) :
    LevSat σ b w s ℓ x ↔
      ((bitB σ ℓ ↔ (!b) = true) ∨
        (((if w then stV σ ℓ x else stU σ ℓ x) ↔ (!s) = true) ∨
          ((if b = w then stZ σ ℓ x else if b then inFst ℓ σ x else inSnd ℓ σ x) ↔ s = true))) := by
  rw [LevSat]
  refine or_congr Iff.rfl (or_congr Iff.rfl ?_)
  by_cases hbw : b = w
  · rw [if_pos hbw, if_pos hbw]
  · rw [if_neg hbw, if_neg hbw]
    cases b
    · rw [if_neg (by decide : ¬((false : Bool) = true)),
        if_neg (by decide : ¬((false : Bool) = true))]
      exact levIn_snd_iff hℓ x s
    · rw [if_pos (rfl : (true : Bool) = true), if_pos (rfl : (true : Bool) = true)]
      exact levIn_fst_iff hℓ x s

theorem levSat_tff {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) :
    LevSat σ true false false ℓ x ↔ (¬bitB σ ℓ ∨ stU σ ℓ x ∨ ¬inFst ℓ σ x) := by
  simp [levSat_iff hℓ]

theorem levSat_tft {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) :
    LevSat σ true false true ℓ x ↔ (¬bitB σ ℓ ∨ ¬stU σ ℓ x ∨ inFst ℓ σ x) := by
  simp [levSat_iff hℓ]

theorem levSat_ttf {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) :
    LevSat σ true true false ℓ x ↔ (¬bitB σ ℓ ∨ stV σ ℓ x ∨ ¬stZ σ ℓ x) := by
  simp [levSat_iff hℓ]

theorem levSat_ttt {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) :
    LevSat σ true true true ℓ x ↔ (¬bitB σ ℓ ∨ ¬stV σ ℓ x ∨ stZ σ ℓ x) := by
  simp [levSat_iff hℓ]

theorem levSat_fff {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) :
    LevSat σ false false false ℓ x ↔ (bitB σ ℓ ∨ stU σ ℓ x ∨ ¬stZ σ ℓ x) := by
  simp [levSat_iff hℓ]

theorem levSat_fft {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) :
    LevSat σ false false true ℓ x ↔ (bitB σ ℓ ∨ ¬stU σ ℓ x ∨ stZ σ ℓ x) := by
  simp [levSat_iff hℓ]

theorem levSat_ftf {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) :
    LevSat σ false true false ℓ x ↔ (bitB σ ℓ ∨ stV σ ℓ x ∨ ¬inSnd ℓ σ x) := by
  simp [levSat_iff hℓ]

theorem levSat_ftt {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) (x : A) :
    LevSat σ false true true ℓ x ↔ (bitB σ ℓ ∨ ¬stV σ ℓ x ∨ inSnd ℓ σ x) := by
  simp [levSat_iff hℓ]

/-- **What the eight clauses of a level say**: the pair passed below is the first
half of the level when its universal bit holds, the second half otherwise. -/
theorem levSat_all_iff {σ : QM A → Prop} {ℓ : A} (hℓ : IsSV ℓ) :
    (∀ (b w s : Bool) (x : A), IsSV x → LevSat σ b w s ℓ x) ↔
      ((bitB σ ℓ → ∀ x : A, IsSV x →
          ((stU σ ℓ x ↔ inFst ℓ σ x) ∧ (stV σ ℓ x ↔ stZ σ ℓ x))) ∧
        (¬bitB σ ℓ → ∀ x : A, IsSV x →
          ((stU σ ℓ x ↔ stZ σ ℓ x) ∧ (stV σ ℓ x ↔ inSnd ℓ σ x)))) := by
  classical
  constructor
  · intro h
    refine ⟨fun hb x hx => ⟨?_, ?_⟩, fun hb x hx => ⟨?_, ?_⟩⟩
    · exact iff_of_or_not (((levSat_tft hℓ x).mp (h true false true x hx)).resolve_left
        (not_not_intro hb)) (((levSat_tff hℓ x).mp (h true false false x hx)).resolve_left
        (not_not_intro hb))
    · exact iff_of_or_not (((levSat_ttt hℓ x).mp (h true true true x hx)).resolve_left
        (not_not_intro hb)) (((levSat_ttf hℓ x).mp (h true true false x hx)).resolve_left
        (not_not_intro hb))
    · exact iff_of_or_not (((levSat_fft hℓ x).mp (h false false true x hx)).resolve_left hb)
        (((levSat_fff hℓ x).mp (h false false false x hx)).resolve_left hb)
    · exact iff_of_or_not (((levSat_ftt hℓ x).mp (h false true true x hx)).resolve_left hb)
        (((levSat_ftf hℓ x).mp (h false true false x hx)).resolve_left hb)
  · rintro ⟨h1, h2⟩ b w s x hx
    by_cases hb : bitB σ ℓ
    · obtain ⟨hu, hv⟩ := h1 hb x hx
      cases b
      · cases w <;> cases s
        · exact (levSat_fff hℓ x).mpr (Or.inl hb)
        · exact (levSat_fft hℓ x).mpr (Or.inl hb)
        · exact (levSat_ftf hℓ x).mpr (Or.inl hb)
        · exact (levSat_ftt hℓ x).mpr (Or.inl hb)
      · cases w <;> cases s
        · exact (levSat_tff hℓ x).mpr (Or.inr ((em (stU σ ℓ x)).imp id
            fun hn hh => hn (hu.mpr hh)))
        · exact (levSat_tft hℓ x).mpr (Or.inr ((em (stU σ ℓ x)).symm.imp id hu.mp))
        · exact (levSat_ttf hℓ x).mpr (Or.inr ((em (stV σ ℓ x)).imp id
            fun hn hh => hn (hv.mpr hh)))
        · exact (levSat_ttt hℓ x).mpr (Or.inr ((em (stV σ ℓ x)).symm.imp id hv.mp))
    · obtain ⟨hu, hv⟩ := h2 hb x hx
      cases b
      · cases w <;> cases s
        · exact (levSat_fff hℓ x).mpr (Or.inr ((em (stU σ ℓ x)).imp id
            fun hn hh => hn (hu.mpr hh)))
        · exact (levSat_fft hℓ x).mpr (Or.inr ((em (stU σ ℓ x)).symm.imp id hu.mp))
        · exact (levSat_ftf hℓ x).mpr (Or.inr ((em (stV σ ℓ x)).imp id
            fun hn hh => hn (hv.mpr hh)))
        · exact (levSat_ftt hℓ x).mpr (Or.inr ((em (stV σ ℓ x)).symm.imp id hv.mp))
      · cases w <;> cases s
        · exact (levSat_tff hℓ x).mpr (Or.inl hb)
        · exact (levSat_tft hℓ x).mpr (Or.inl hb)
        · exact (levSat_ttf hℓ x).mpr (Or.inl hb)
        · exact (levSat_ttt hℓ x).mpr (Or.inl hb)

/-! ### The three blocks of a level leave the other levels alone -/

/-- The abbreviation for the valuation obtained by playing the three blocks of
level `ℓ`. -/
def levOver (ℓ : A) (τ νZ νB νUV : QM A → Prop) : QM A → Prop :=
  qOver (QBlk (tUV ℓ)) (qOver (QBlk (tB ℓ)) (qOver (QBlk (tZ ℓ)) τ νZ) νB) νUV

theorem levSat_congr {σ σ' : QM A → Prop} {ℓ'' : A}
    (hs : stS σ = stS σ') (ht : stT σ = stT σ')
    (hz : stZ σ ℓ'' = stZ σ' ℓ'') (hb : bitB σ ℓ'' ↔ bitB σ' ℓ'')
    (hu : stU σ ℓ'' = stU σ' ℓ'') (hv : stV σ ℓ'' = stV σ' ℓ'')
    (hup : ∀ d : A, IsPredSV d ℓ'' → stU σ d = stU σ' d)
    (hvp : ∀ d : A, IsPredSV d ℓ'' → stV σ d = stV σ' d)
    (b w s : Bool) (x : A) : LevSat σ b w s ℓ'' x ↔ LevSat σ' b w s ℓ'' x := by
  simp only [LevSat, hs, ht, hz, hu, hv]
  refine or_congr (iff_congr hb Iff.rfl) (or_congr Iff.rfl ?_)
  split_ifs with _ _
  · exact Iff.rfl
  · exact or_congr Iff.rfl (exists_congr fun d =>
      and_congr_right fun hd => by rw [hup d hd])
  · exact or_congr Iff.rfl (exists_congr fun d =>
      and_congr_right fun hd => by rw [hvp d hd])

@[simp] theorem stS_levOver (ℓ : A) (τ νZ νB νUV : QM A → Prop) :
    stS (levOver ℓ τ νZ νB νUV) = stS τ := by simp [levOver]

@[simp] theorem stT_levOver (ℓ : A) (τ νZ νB νUV : QM A → Prop) :
    stT (levOver ℓ τ νZ νB νUV) = stT τ := by simp [levOver]

omit [Finite A] [Nonempty A] in
@[simp] theorem stZ_levOver (ℓ : A) (τ νZ νB νUV : QM A → Prop) (ℓ'' : A) :
    stZ (levOver ℓ τ νZ νB νUV) ℓ'' = stZ (qOver (QBlk (tZ ℓ)) τ νZ) ℓ'' := by
  simp [levOver]

omit [Finite A] [Nonempty A] in
theorem stU_levOver_ne (ℓ : A) (τ νZ νB νUV : QM A → Prop) {ℓ'' : A} (h : ℓ'' ≠ ℓ) :
    stU (levOver ℓ τ νZ νB νUV) ℓ'' = stU τ ℓ'' := by
  simp [levOver, stU_over_tUV_ne _ _ h]

omit [Finite A] [Nonempty A] in
theorem stV_levOver_ne (ℓ : A) (τ νZ νB νUV : QM A → Prop) {ℓ'' : A} (h : ℓ'' ≠ ℓ) :
    stV (levOver ℓ τ νZ νB νUV) ℓ'' = stV τ ℓ'' := by
  simp [levOver, stV_over_tUV_ne _ _ h]

theorem bitB_levOver_ne (ℓ : A) (τ νZ νB νUV : QM A → Prop) {ℓ'' : A} (h : ℓ'' ≠ ℓ) :
    bitB (levOver ℓ τ νZ νB νUV) ℓ'' ↔ bitB τ ℓ'' := by
  simp [levOver, bitB_over_tB_ne _ _ h]

theorem inFst_levOver (ℓ : A) (τ νZ νB νUV : QM A → Prop) :
    inFst ℓ (levOver ℓ τ νZ νB νUV) = inFst ℓ τ := by
  by_cases hmin : IsMinSV ℓ
  · rw [inFst_of_isMinSV hmin, inFst_of_isMinSV hmin, stS_levOver]
  · by_cases hex : ∃ d : A, IsPredSV d ℓ
    · obtain ⟨d, hd⟩ := hex
      rw [inFst_of_isPredSV hd, inFst_of_isPredSV hd, stU_levOver_ne ℓ τ νZ νB νUV hd.2.2.1.ne]
    · rw [inFst, inFst, dif_neg hex, dif_neg hex, stS_levOver]

theorem inSnd_levOver (ℓ : A) (τ νZ νB νUV : QM A → Prop) :
    inSnd ℓ (levOver ℓ τ νZ νB νUV) = inSnd ℓ τ := by
  by_cases hmin : IsMinSV ℓ
  · rw [inSnd_of_isMinSV hmin, inSnd_of_isMinSV hmin, stT_levOver]
  · by_cases hex : ∃ d : A, IsPredSV d ℓ
    · obtain ⟨d, hd⟩ := hex
      rw [inSnd_of_isPredSV hd, inSnd_of_isPredSV hd, stV_levOver_ne ℓ τ νZ νB νUV hd.2.2.1.ne]
    · rw [inSnd, inSnd, dif_neg hex, dif_neg hex, stT_levOver]

/-- **The three blocks of a level leave the levels above it alone.** -/
theorem levBelow_levOver (ℓ : A) (τ νZ νB νUV : QM A → Prop) :
    LevBelow ℓ (levOver ℓ τ νZ νB νUV) ↔ LevBelow ℓ τ := by
  have key : ∀ (ℓ'' : A), ℓ'' < ℓ → ∀ (b w s : Bool) (x : A),
      LevSat (levOver ℓ τ νZ νB νUV) b w s ℓ'' x ↔ LevSat τ b w s ℓ'' x := by
    intro ℓ'' hlt b w s x
    refine levSat_congr (stS_levOver ℓ τ νZ νB νUV) (stT_levOver ℓ τ νZ νB νUV) ?_
      (bitB_levOver_ne ℓ τ νZ νB νUV hlt.ne) (stU_levOver_ne ℓ τ νZ νB νUV hlt.ne)
      (stV_levOver_ne ℓ τ νZ νB νUV hlt.ne) (fun d hd => ?_) (fun d hd => ?_) b w s x
    · rw [stZ_levOver, stZ_over_tZ_ne _ _ hlt.ne]
    · exact stU_levOver_ne ℓ τ νZ νB νUV (hd.2.2.1.trans hlt).ne
    · exact stV_levOver_ne ℓ τ νZ νB νUV (hd.2.2.1.trans hlt).ne
  exact ⟨fun h b w s ℓ'' x hl hlt hx => (key ℓ'' hlt b w s x).mp (h b w s ℓ'' x hl hlt hx),
    fun h b w s ℓ'' x hl hlt hx => (key ℓ'' hlt b w s x).mpr (h b w s ℓ'' x hl hlt hx)⟩

omit [Finite A] [Nonempty A] in
theorem levOver_eq (ℓ : A) (τ νZ νB νUV : QM A → Prop) :
    qOver (QBlk (tUV ℓ)) (qOver (QBlk (tB ℓ)) (qOver (QBlk (tZ ℓ)) τ νZ) νB) νUV
      = levOver ℓ τ νZ νB νUV := rfl

theorem bitB_levOver_bVal {ℓ : A} (hℓ : IsSV ℓ) (τ νZ νUV : QM A → Prop) (β : Prop) :
    bitB (levOver ℓ τ νZ (bVal ℓ β) νUV) ℓ ↔ β := by
  rw [levOver, bitB_over_tUV]
  exact bitB_over_bVal _ hℓ β

omit [Finite A] [Nonempty A] in
theorem stU_levOver_uvVal {ℓ : A} (hℓ : IsSV ℓ) (τ νZ νB : QM A → Prop) (U V : A → Prop)
    {a : A} (ha : IsSV a) : stU (levOver ℓ τ νZ νB (uvVal ℓ U V)) ℓ a ↔ U a :=
  stU_over_uvVal _ hℓ U V ha

omit [Finite A] [Nonempty A] in
theorem stV_levOver_uvVal {ℓ : A} (hℓ : IsSV ℓ) (τ νZ νB : QM A → Prop) (U V : A → Prop)
    {a : A} (ha : IsSV a) : stV (levOver ℓ τ νZ νB (uvVal ℓ U V)) ℓ a ↔ V a :=
  stV_over_uvVal _ hℓ U V ha

omit [Finite A] [Nonempty A] in
theorem stZ_levOver_zVal {ℓ : A} (hℓ : IsSV ℓ) (τ : QM A → Prop) (Z : A → Prop)
    {a : A} (ha : IsSV a) : stZ (qOver (QBlk (tZ ℓ)) τ (zVal ℓ Z)) ℓ a ↔ Z a :=
  stZ_over_zVal τ hℓ Z ha

/-! ### One level of the recursion -/

/-- **Playing the three blocks of a level is one step of Savitch's recursion.**
The midpoint is the intermediate state, the universal bit chooses which half is
checked, and the level clauses force the pair passed below to be the endpoints of
that half. -/
theorem game_step {ℓ : A} (hℓ : IsSV ℓ) {k : ℕ} {nxt : ℕ × A × ℕ}
    (hnxt : qUnion (QPlayed (tUV ℓ)) (QBlk (tUV ℓ)) = QPlayed nxt)
    (IH : ∀ σ : QM A → Prop, QsatWins (QPlayed nxt) σ ↔
      IsStart A (stS σ) ∧ IsGoal A (stT σ) ∧ LevUpto ℓ σ ∧
        SavPow (stCls (A := A)) (StepRel A) k (stU σ ℓ) (stV σ ℓ))
    (τ : QM A → Prop) :
    QsatWins (QPlayed (tZ ℓ)) τ ↔
      IsStart A (stS τ) ∧ IsGoal A (stT τ) ∧ LevBelow ℓ τ ∧
        SavPow (stCls (A := A)) (StepRel A) (k + 1) (inFst ℓ τ) (inSnd ℓ τ) := by
  classical
  have hZ : QsatWins (QPlayed (tZ ℓ)) τ ↔
      ∃ νZ, QsatWins (QPlayed (tB ℓ)) (qOver (QBlk (tZ ℓ)) τ νZ) := by
    rw [qsatWins_block_ex qsatWf_qsatInterp (qDownClosed_qPlayed _) (qBlock_qBlk _)
      (blk_ex_tZ ℓ), step_z ℓ]
  have hB : ∀ σ : QM A → Prop, QsatWins (QPlayed (tB ℓ)) σ ↔
      ∀ νB, QsatWins (QPlayed (tUV ℓ)) (qOver (QBlk (tB ℓ)) σ νB) := fun σ => by
    rw [qsatWins_block_all qsatWf_qsatInterp (qDownClosed_qPlayed _) (qBlock_qBlk _)
      (blk_all_tB ℓ), step_b ℓ]
  have hUV : ∀ σ : QM A → Prop, QsatWins (QPlayed (tUV ℓ)) σ ↔
      ∃ νUV, QsatWins (QPlayed nxt) (qOver (QBlk (tUV ℓ)) σ νUV) := fun σ => by
    rw [qsatWins_block_ex qsatWf_qsatInterp (qDownClosed_qPlayed _) (qBlock_qBlk _)
      (blk_ex_tUV ℓ), hnxt]
  rw [hZ]
  simp only [hB, hUV, levOver_eq, IH, levUpto_iff hℓ, levSat_all_iff hℓ, stS_levOver,
    stT_levOver, levBelow_levOver, inFst_levOver, inSnd_levOver, stZ_levOver]
  constructor
  · rintro ⟨νZ, h⟩
    obtain ⟨νUV₁, hs, hg, ⟨hbel, hc₁, -⟩, hsav₁⟩ := h (bVal ℓ True)
    obtain ⟨νUV₂, -, -, ⟨-, -, hc₂⟩, hsav₂⟩ := h (bVal ℓ False)
    have hb₁ := hc₁ ((bitB_levOver_bVal hℓ τ νZ νUV₁ True).mpr trivial)
    have hb₂ := hc₂ (fun hh => (bitB_levOver_bVal hℓ τ νZ νUV₂ False).mp hh)
    refine ⟨hs, hg, hbel, stZ (qOver (QBlk (tZ ℓ)) τ νZ) ℓ, ?_, ?_⟩
    · exact savPow_congr savInv_stepRel k (stCls_eq_iff.mpr fun x hx => (hb₁ x hx).1)
        (stCls_eq_iff.mpr fun x hx => (hb₁ x hx).2) hsav₁
    · exact savPow_congr savInv_stepRel k (stCls_eq_iff.mpr fun x hx => (hb₂ x hx).1)
        (stCls_eq_iff.mpr fun x hx => (hb₂ x hx).2) hsav₂
  · rintro ⟨hs, hg, hbel, Z, hsav₁, hsav₂⟩
    refine ⟨zVal ℓ Z, fun νB => ?_⟩
    by_cases hβ : bitB (qOver (QBlk (tB ℓ)) (qOver (QBlk (tZ ℓ)) τ (zVal ℓ Z)) νB) ℓ
    · refine ⟨uvVal ℓ (inFst ℓ τ) Z, hs, hg, ⟨hbel, fun _ x hx => ?_, fun hnb => ?_⟩, ?_⟩
      · exact ⟨stU_levOver_uvVal hℓ τ (zVal ℓ Z) νB _ _ hx,
          (stV_levOver_uvVal hℓ τ (zVal ℓ Z) νB _ _ hx).trans (stZ_levOver_zVal hℓ τ Z hx).symm⟩
      · exact absurd (by simpa [levOver] using hβ) hnb
      · refine savPow_congr savInv_stepRel k (stCls_eq_iff.mpr fun x hx => ?_)
          (stCls_eq_iff.mpr fun x hx => ?_) hsav₁
        · exact (stU_levOver_uvVal hℓ τ (zVal ℓ Z) νB _ _ hx).symm
        · exact (stV_levOver_uvVal hℓ τ (zVal ℓ Z) νB (inFst ℓ τ) Z hx).symm
    · refine ⟨uvVal ℓ Z (inSnd ℓ τ), hs, hg, ⟨hbel, fun hb => ?_, fun _ x hx => ?_⟩, ?_⟩
      · exact absurd (by simpa [levOver] using hb) hβ
      · exact ⟨(stU_levOver_uvVal hℓ τ (zVal ℓ Z) νB _ _ hx).trans
            (stZ_levOver_zVal hℓ τ Z hx).symm,
          stV_levOver_uvVal hℓ τ (zVal ℓ Z) νB _ _ hx⟩
      · refine savPow_congr savInv_stepRel k (stCls_eq_iff.mpr fun x hx => ?_)
          (stCls_eq_iff.mpr fun x hx => ?_) hsav₂
        · exact (stU_levOver_uvVal hℓ τ (zVal ℓ Z) νB Z (inSnd ℓ τ) hx).symm
        · exact (stV_levOver_uvVal hℓ τ (zVal ℓ Z) νB Z
            (inSnd ℓ τ) hx).symm

/-! ### Down the levels -/

theorem levPart_iff_levUpto {σ : QM A → Prop} {ℓ : A} (hmax : IsMaxSV ℓ) :
    LevPart σ ↔ LevUpto ℓ σ :=
  ⟨fun h b w s ℓ'' x hl _ hx => h b w s ℓ'' x hl hx,
    fun h b w s ℓ'' x hl hx => h b w s ℓ'' x hl (hmax.le hl) hx⟩

theorem levBelow_iff_levUpto {σ : QM A → Prop} {ℓ ℓ' : A} (hpred : IsPredSV ℓ ℓ') :
    LevBelow ℓ' σ ↔ LevUpto ℓ σ := by
  constructor
  · exact fun h b w s ℓ'' x hl hle hx => h b w s ℓ'' x hl (lt_of_le_of_lt hle hpred.2.2.1) hx
  · intro h b w s ℓ'' x hl hlt hx
    refine h b w s ℓ'' x hl ?_ hx
    rcases le_or_gt ℓ'' ℓ with hle | hgt
    · exact hle
    · exact absurd ⟨hgt, hlt⟩ (hpred.2.2.2 ℓ'' hl)

/-- **The position opened by a level computes reachability in at most `2 ^ k`
moves**, `k` the number of levels from it down to the last one. -/
theorem game_level : ∀ (n : ℕ) (ℓ : A), IsSV ℓ → svAbove ℓ ≤ n → ∀ τ : QM A → Prop,
    (QsatWins (QPlayed (tZ ℓ)) τ ↔
      IsStart A (stS τ) ∧ IsGoal A (stT τ) ∧ LevBelow ℓ τ ∧
        SavPow (stCls (A := A)) (StepRel A) (svAbove ℓ) (inFst ℓ τ) (inSnd ℓ τ)) := by
  intro n
  induction n with
  | zero =>
    intro ℓ hℓ hle
    exact absurd hle (not_le.mpr (svAbove_pos hℓ))
  | succ n ih =>
    intro ℓ hℓ hle τ
    by_cases hmax : IsMaxSV ℓ
    · have hone : svAbove ℓ = 0 + 1 := by rw [svAbove_of_isMaxSV hmax]
      rw [hone]
      refine game_step hℓ (step_last hmax) (fun σ => ?_) τ
      rw [game_aux, levPart_iff_levUpto hmax]
      refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
      exact ⟨fun h => h ℓ hmax, fun h m hm => isMaxSV_unique hm hmax ▸ h⟩
    · obtain ⟨ℓ', hpred⟩ := exists_isSuccSV hℓ hmax
      have hℓ' : IsSV ℓ' := hpred.2.1
      have hcard : svAbove ℓ = svAbove ℓ' + 1 := svAbove_of_isPredSV hpred
      rw [hcard]
      refine game_step hℓ (step_uv hpred) (fun σ => ?_) τ
      rw [ih ℓ' hℓ' (by omega) σ, levBelow_iff_levUpto hpred, inFst_of_isPredSV hpred,
        inSnd_of_isPredSV hpred]

end Induction

end DescriptiveComplexity
