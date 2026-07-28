/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Levels

/-!
# The matrix of the constructed instance

What the matrix of the QSAT instance built by the Savitch reduction says, clause
tag by clause tag.

A clause is satisfied when one of the literals of its list
(`DescriptiveComplexity.qLits`) is (`DescriptiveComplexity.ClSat`), and a literal
is satisfied when the variable its link points at gets the literal's sign
(`DescriptiveComplexity.LitSat`). Since every link pins the coordinates of that
variable, the existential quantifier of a literal collapses
(`DescriptiveComplexity.litSat_atP` and its companions, one per
`DescriptiveComplexity.QLink`), and each clause tag turns into a plain condition
on what the valuation reads (`DescriptiveComplexity.clSat_cSrc` and its
companions).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Matrix

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- A literal of a clause sitting at `(p, q)` is satisfied by the valuation
`σ`: the variable its link points at gets its sign. -/
def LitSat (σ : QM A → Prop) (p q : A) (l : QLit) : Prop :=
  ∃ r s : A, QVarOn l.vt r s ∧ LinkOn l.link p q r s ∧ (σ (qVar l.vt r s) ↔ l.sign = true)

/-- A clause of the constructed instance is satisfied by the valuation `σ`. -/
def ClSat (σ : QM A → Prop) (c : QClTag) (p q : A) : Prop :=
  ∃ l ∈ qLits c, LitSat σ p q l

omit [Finite A] [Nonempty A] in
/-- **The matrix of the constructed instance**: every guarded clause tag is
satisfied. -/
theorem qsatMatrix_iff (σ : QM A → Prop) :
    QsatMatrix σ ↔ ∀ (c : QClTag) (p q : A), QClOn c p q → ClSat σ c p q := by
  constructor
  · intro hm c p q hcl
    obtain ⟨x, hxv, hlit⟩ := hm (qCl c p q) ((isClause_qCl c p q).mpr hcl)
    rcases qm_cases x with ⟨v, r, s, rfl⟩ | ⟨c', r, s, rfl⟩
    · rcases hlit with ⟨hp, hσ⟩ | ⟨hn, hσ⟩
      · obtain ⟨l, hl, hlv, hls, -, hvr, hlk⟩ := (posIn_qCl_qVar c v p q r s).mp hp
        subst hlv
        exact ⟨l, hl, r, s, hvr, hlk, iff_of_true hσ hls⟩
      · obtain ⟨l, hl, hlv, hls, -, hvr, hlk⟩ := (negIn_qCl_qVar c v p q r s).mp hn
        subst hlv
        exact ⟨l, hl, r, s, hvr, hlk, iff_of_false hσ (by rw [hls]; exact Bool.false_ne_true)⟩
    · exact absurd hxv (not_isQVar_qCl c' r s)
  · intro h x hx
    rcases qm_cases x with ⟨v, p, q, rfl⟩ | ⟨c, p, q, rfl⟩
    · exact absurd hx (not_isClause_qVar v p q)
    · have hcl := (isClause_qCl c p q).mp hx
      obtain ⟨l, hl, r, s, hvr, hlk, hval⟩ := h c p q hcl
      refine ⟨qVar l.vt r s, (isQVar_qVar _ _ _).mpr hvr, ?_⟩
      cases hs : l.sign
      · refine Or.inr ⟨(negIn_qCl_qVar c l.vt p q r s).mpr ⟨l, hl, rfl, hs, hcl, hvr, hlk⟩, ?_⟩
        exact fun hσ => Bool.false_ne_true (hs ▸ hval.mp hσ)
      · exact Or.inl ⟨(posIn_qCl_qVar c l.vt p q r s).mpr ⟨l, hl, rfl, hs, hcl, hvr, hlk⟩,
          hval.mpr hs⟩

/-! ### Collapsing the quantifier of a literal

Every link pins the coordinates of the variable it points at, except the two
that range over the literals of a clause of the input. -/

variable {σ : QM A → Prop} {p q : A} {vt : QVarTag} {sgn : Bool}

@[simp]
theorem litSat_atP :
    LitSat σ p q ⟨vt, sgn, .atP⟩ ↔
      (QVarOn vt p (qBot A) ∧ (σ (qVar vt p (qBot A)) ↔ sgn = true)) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hr, hs⟩, hval⟩
    subst hr
    rw [eq_qBot hs] at hv hval
    exact ⟨hv, hval⟩
  · rintro ⟨hv, hval⟩
    exact ⟨p, qBot A, hv, ⟨rfl, isBot_qBot A⟩, hval⟩

@[simp]
theorem litSat_atQ :
    LitSat σ p q ⟨vt, sgn, .atQ⟩ ↔
      (QVarOn vt q (qBot A) ∧ (σ (qVar vt q (qBot A)) ↔ sgn = true)) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hr, hs⟩, hval⟩
    subst hr
    rw [eq_qBot hs] at hv hval
    exact ⟨hv, hval⟩
  · rintro ⟨hv, hval⟩
    exact ⟨q, qBot A, hv, ⟨rfl, isBot_qBot A⟩, hval⟩

@[simp]
theorem litSat_botBoth :
    LitSat σ p q ⟨vt, sgn, .botBoth⟩ ↔
      (QVarOn vt (qBot A) (qBot A) ∧ (σ (qVar vt (qBot A) (qBot A)) ↔ sgn = true)) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hr, hs⟩, hval⟩
    rw [eq_qBot hr, eq_qBot hs] at hv hval
    exact ⟨hv, hval⟩
  · rintro ⟨hv, hval⟩
    exact ⟨qBot A, qBot A, hv, ⟨isBot_qBot A, isBot_qBot A⟩, hval⟩

omit [Finite A] [Nonempty A] in
@[simp]
theorem litSat_same :
    LitSat σ p q ⟨vt, sgn, .same⟩ ↔
      (QVarOn vt p q ∧ (σ (qVar vt p q) ↔ sgn = true)) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hr, hs⟩, hval⟩
    subst hr
    subst hs
    exact ⟨hv, hval⟩
  · rintro ⟨hv, hval⟩
    exact ⟨p, q, hv, ⟨rfl, rfl⟩, hval⟩

omit [Finite A] [Nonempty A] in
@[simp]
theorem litSat_maxAtP :
    LitSat σ p q ⟨vt, sgn, .maxAtP⟩ ↔
      ∃ m : A, IsMaxSV m ∧ QVarOn vt m p ∧ (σ (qVar vt m p) ↔ sgn = true) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hm, hs⟩, hval⟩
    subst hs
    exact ⟨r, hm, hv, hval⟩
  · rintro ⟨m, hm, hv, hval⟩
    exact ⟨m, p, hv, ⟨hm, rfl⟩, hval⟩

@[simp]
theorem litSat_minAtQ :
    LitSat σ p q ⟨vt, sgn, .minAtQ⟩ ↔
      (IsMinSV p ∧ QVarOn vt q (qBot A) ∧ (σ (qVar vt q (qBot A)) ↔ sgn = true)) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hmin, hr, hs⟩, hval⟩
    subst hr
    rw [eq_qBot hs] at hv hval
    exact ⟨hmin, hv, hval⟩
  · rintro ⟨hmin, hv, hval⟩
    exact ⟨q, qBot A, hv, ⟨hmin, rfl, isBot_qBot A⟩, hval⟩

omit [Finite A] [Nonempty A] in
@[simp]
theorem litSat_predAtQ :
    LitSat σ p q ⟨vt, sgn, .predAtQ⟩ ↔
      ∃ d : A, IsPredSV d p ∧ QVarOn vt d q ∧ (σ (qVar vt d q) ↔ sgn = true) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hd, hs⟩, hval⟩
    subst hs
    exact ⟨r, hd, hv, hval⟩
  · rintro ⟨d, hd, hv, hval⟩
    exact ⟨d, q, hv, ⟨hd, rfl⟩, hval⟩

@[simp]
theorem litSat_occPos :
    LitSat σ p q ⟨vt, sgn, .occPos⟩ ↔
      ∃ r : A, RelMap tsPosIn ![p, r] ∧ QVarOn vt r (qBot A) ∧
        (σ (qVar vt r (qBot A)) ↔ sgn = true) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hocc, hs⟩, hval⟩
    rw [eq_qBot hs] at hv hval
    exact ⟨r, hocc, hv, hval⟩
  · rintro ⟨r, hocc, hv, hval⟩
    exact ⟨r, qBot A, hv, ⟨hocc, isBot_qBot A⟩, hval⟩

@[simp]
theorem litSat_occNeg :
    LitSat σ p q ⟨vt, sgn, .occNeg⟩ ↔
      ∃ r : A, RelMap tsNegIn ![p, r] ∧ QVarOn vt r (qBot A) ∧
        (σ (qVar vt r (qBot A)) ↔ sgn = true) := by
  constructor
  · rintro ⟨r, s, hv, ⟨hocc, hs⟩, hval⟩
    rw [eq_qBot hs] at hv hval
    exact ⟨r, hocc, hv, hval⟩
  · rintro ⟨r, hocc, hv, hval⟩
    exact ⟨r, qBot A, hv, ⟨hocc, isBot_qBot A⟩, hval⟩

end Matrix

/-! ### What each clause says -/

section PerTag

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
@[simp]
theorem and_isSV_of_isMaxSV {m : A} {P : Prop} : (IsMaxSV m ∧ IsSV m ∧ P) ↔ (IsMaxSV m ∧ P) :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.isSV, h.2⟩⟩

omit [Finite A] [Nonempty A] in
@[simp]
theorem and_isSV_of_isPredSV {d ℓ : A} {P : Prop} :
    (IsPredSV d ℓ ∧ IsSV d ∧ P) ↔ (IsPredSV d ℓ ∧ P) :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.1, h.2⟩⟩

variable (σ : QM A → Prop)

/-- A copy of a source clause reads its literals on the source valuation. -/
theorem clSat_cSrc (p q : A) :
    ClSat σ .cSrc p q ↔
      ∃ x : A, (RelMap tsPosIn ![p, x] ∧ valS σ x) ∨ (RelMap tsNegIn ![p, x] ∧ ¬valS σ x) := by
  simp [ClSat, qLits, QVarOn, valS, exists_or]

/-- A copy of a target clause reads its literals on the target valuation. -/
theorem clSat_cTgt (p q : A) :
    ClSat σ .cTgt p q ↔
      ∃ x : A, (RelMap tsPosIn ![p, x] ∧ valT σ x) ∨ (RelMap tsNegIn ![p, x] ∧ ¬valT σ x) := by
  simp [ClSat, qLits, QVarOn, valT, exists_or]

/-- A copy of a transition clause reads its literals on the transition
valuation, unless the base case is the equality branch. -/
theorem clSat_cStep (p q : A) :
    ClSat σ .cStep p q ↔ bitE σ ∨
      ∃ x : A, (RelMap tsPosIn ![p, x] ∧ valP σ x) ∨ (RelMap tsNegIn ![p, x] ∧ ¬valP σ x) := by
  simp [ClSat, qLits, QVarOn, valP, bitE, exists_or]

/-- The source valuation reads the source endpoint. -/
theorem clSat_lS (s : Bool) {p q : A} (hg : QClOn (.lS s) p q) :
    ClSat σ (.lS s) p q ↔ (valS σ p ↔ s = true) ∨ (stS σ p ↔ (!s) = true) := by
  simp [ClSat, qLits, QVarOn, valS, stS, hg.1]

/-- The target valuation reads the target endpoint. -/
theorem clSat_lT (s : Bool) {p q : A} (hg : QClOn (.lT s) p q) :
    ClSat σ (.lT s) p q ↔ (valT σ p ↔ s = true) ∨ (stT σ p ↔ (!s) = true) := by
  simp [ClSat, qLits, QVarOn, valT, stT, hg.1]

/-- The transition valuation reads the first component of the bottom pair. -/
theorem clSat_lU (s : Bool) {p q : A} (hg : QClOn (.lU s) p q) :
    ClSat σ (.lU s) p q ↔ bitE σ ∨ (valP σ p ↔ s = true) ∨
      ∃ m : A, IsMaxSV m ∧ (stU σ m p ↔ (!s) = true) := by
  simp [ClSat, qLits, QVarOn, bitE, valP, stU, hg.1]

/-- The transition valuation writes the second component of the bottom pair. -/
theorem clSat_lV (s : Bool) {p q : A} (hg : QClOn (.lV s) p q) :
    ClSat σ (.lV s) p q ↔ bitE σ ∨ (valP σ q ↔ s = true) ∨
      ∃ m : A, IsMaxSV m ∧ (stV σ m p ↔ (!s) = true) := by
  simp [ClSat, qLits, QVarOn, bitE, valP, stV, hg.1]

/-- The equality branch of the base case. -/
theorem clSat_bE (s : Bool) {p q : A} (hg : QClOn (.bE s) p q) :
    ClSat σ (.bE s) p q ↔ ¬bitE σ ∨ (∃ m : A, IsMaxSV m ∧ (stU σ m p ↔ s = true)) ∨
      ∃ m : A, IsMaxSV m ∧ (stV σ m p ↔ (!s) = true) := by
  simp [ClSat, qLits, QVarOn, bitE, stU, stV, hg.1]

/-- What one of the eight clauses of a level says: the branch of the universal
bit, the component of the pair it constrains, and the value that component must
copy – the midpoint, or the endpoint the level receives from above. -/
def LevSat (b w s : Bool) (ℓ x : A) : Prop :=
  (bitB σ ℓ ↔ (!b) = true) ∨
    ((if w then stV σ ℓ x else stU σ ℓ x) ↔ (!s) = true) ∨
    (if b = w then (stZ σ ℓ x ↔ s = true)
     else if b then (IsMinSV ℓ ∧ (stS σ x ↔ s = true)) ∨
       (∃ d : A, IsPredSV d ℓ ∧ (stU σ d x ↔ s = true))
     else (IsMinSV ℓ ∧ (stT σ x ↔ s = true)) ∨
       (∃ d : A, IsPredSV d ℓ ∧ (stV σ d x ↔ s = true)))

/-- **A level clause** says exactly what `DescriptiveComplexity.LevSat` says. -/
theorem clSat_lev (b w s : Bool) {ℓ x : A} (hg : QClOn (.lev b w s) ℓ x) :
    ClSat σ (.lev b w s) ℓ x ↔ LevSat σ b w s ℓ x := by
  obtain ⟨hl, hx⟩ := hg
  cases b <;> cases w <;>
    simp [ClSat, qLits, levInLits, LevSat, QVarOn, bitB, stZ, stU, stV, stS, stT, hl, hx]

end PerTag

end DescriptiveComplexity
