/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Interp
import DescriptiveComplexity.Problems.Qsat.Blocks

/-!
# The quantifier prefix of the constructed instance

The constructed instance is well formed (`DescriptiveComplexity.qsatWf_qsatInterp`),
and its prefix splits into the blocks the correctness proof peels off.

An element of the constructed instance is a tagged pair, named
`DescriptiveComplexity.qVar` when its tag is a variable tag and
`DescriptiveComplexity.qCl` when it is a clause tag; every relation of the instance
is read on those named constructors rather than on raw pairs, since the universe
of an interpretation is a non-reducible definition.

A **block** is a set of variables sharing their block coordinates
`DescriptiveComplexity.keyTriple`, and the position just before it is the set of
variables whose coordinates are strictly smaller
(`DescriptiveComplexity.QPlayed`). The two facts the peeling lemmas of
`DescriptiveComplexity.Problems.Qsat.Blocks` ask for – being the next block, and
downward closure of the position – hold for *every* triple
(`DescriptiveComplexity.qBlock_qBlk`, `DescriptiveComplexity.qDownClosed_qPlayed`),
so a peeling step is only ever a matter of recognizing which triple comes next
(`DescriptiveComplexity.qPlayed_step`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Elements

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A]

/-- The element standing for the variable `v` at the coordinates `(p, q)`. -/
def qVar (v : QVarTag) (p q : A) : QM A := (Sum.inl v, ![p, q])

/-- The element standing for the clause `c` at the coordinates `(p, q)`. -/
def qCl (c : QClTag) (p q : A) : QM A := (Sum.inr c, ![p, q])

theorem qVar_inj {v v' : QVarTag} {p q p' q' : A} (h : qVar v p q = qVar v' p' q') :
    v = v' ∧ p = p' ∧ q = q' := by
  have h1 : (Sum.inl v : QTag) = Sum.inl v' := congrArg Prod.fst h
  have h2 : (![p, q] : Fin 2 → A) = ![p', q'] := congrArg Prod.snd h
  exact ⟨Sum.inl.inj h1, congrFun h2 0, congrFun h2 1⟩

/-- Every element is a variable or a clause at some pair of coordinates. -/
theorem qm_cases (x : QM A) :
    (∃ v p q, x = qVar v p q) ∨ (∃ c p q, x = qCl c p q) := by
  obtain ⟨t, w⟩ := x
  have hw : w = ![w 0, w 1] := by
    funext j
    fin_cases j <;> rfl
  cases t with
  | inl v => exact Or.inl ⟨v, w 0, w 1, by rw [qVar, ← hw]⟩
  | inr c => exact Or.inr ⟨c, w 0, w 1, by rw [qCl, ← hw]⟩

/-! ### The relations, read on the named constructors -/

@[simp]
theorem isQVar_qVar (v : QVarTag) (p q : A) : IsQVar (qVar v p q) ↔ QVarOn v p q := by
  rw [qVar]
  simpa using qsat_isVar v ![p, q]

@[simp]
theorem not_isQVar_qCl (c : QClTag) (p q : A) : ¬IsQVar (qCl c p q) :=
  qsat_not_isVar c ![p, q]

@[simp]
theorem isQAll_qVar (v : QVarTag) (p q : A) :
    IsQAll (qVar v p q) ↔ (v = .sB ∧ QVarOn v p q) := by
  rw [qVar]
  simpa using qsat_isAll v ![p, q]

@[simp]
theorem not_isQAll_qCl (c : QClTag) (p q : A) : ¬IsQAll (qCl c p q) :=
  qsat_not_isAll_cl c ![p, q]

@[simp]
theorem isClause_qCl (c : QClTag) (p q : A) :
    RelMap (M := QM A) qsIsClause ![qCl c p q] ↔ QClOn c p q := by
  rw [qCl]
  simpa using qsat_isClause c ![p, q]

@[simp]
theorem not_isClause_qVar (v : QVarTag) (p q : A) :
    ¬RelMap (M := QM A) qsIsClause ![qVar v p q] :=
  qsat_not_isClause v ![p, q]

@[simp]
theorem qPrec_qVar (v v' : QVarTag) (p q p' q' : A) :
    QPrec (qVar v p q) (qVar v' p' q') ↔
      QVarOn v p q ∧ QVarOn v' p' q' ∧ KeyLt v p q v' p' q' := by
  rw [qVar, qVar]
  simpa using qsat_prec v v' ![p, q] ![p', q']

@[simp]
theorem posIn_qCl_qVar (c : QClTag) (v : QVarTag) (p q r s : A) :
    RelMap (M := QM A) qsPosIn ![qCl c p q, qVar v r s] ↔
      ∃ l ∈ qLits c, l.vt = v ∧ l.sign = true ∧
        QClOn c p q ∧ QVarOn v r s ∧ LinkOn l.link p q r s := by
  rw [qCl, qVar]
  simpa using qsat_posIn c v ![p, q] ![r, s]

@[simp]
theorem negIn_qCl_qVar (c : QClTag) (v : QVarTag) (p q r s : A) :
    RelMap (M := QM A) qsNegIn ![qCl c p q, qVar v r s] ↔
      ∃ l ∈ qLits c, l.vt = v ∧ l.sign = false ∧
        QClOn c p q ∧ QVarOn v r s ∧ LinkOn l.link p q r s := by
  rw [qCl, qVar]
  simpa using qsat_negIn c v ![p, q] ![r, s]

end Elements

/-! ### Well-formedness -/

section Wf

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A]

/-- **The constructed instance is well formed**: the prefix is the lexicographic
comparison of the keys, which is a strict linear order on the variables because
a variable is determined by its key and its coordinates. -/
theorem qsatWf_qsatInterp : QsatWf (QM A) where
  isVar_of_prec x y hxy := by
    rcases qm_cases x with ⟨v, p, q, rfl⟩ | ⟨c, p, q, rfl⟩
    · rcases qm_cases y with ⟨v', p', q', rfl⟩ | ⟨c', p', q', rfl⟩
      · obtain ⟨h1, h2, -⟩ := (qPrec_qVar v v' p q p' q').mp hxy
        exact ⟨(isQVar_qVar v p q).mpr h1, (isQVar_qVar v' p' q').mpr h2⟩
      · exact absurd hxy (qsat_not_prec_right c' _ ![p', q'])
    · exact absurd hxy (qsat_not_prec_left c _ ![p, q])
  irrefl x hx := by
    rcases qm_cases x with ⟨v, p, q, rfl⟩ | ⟨c, p, q, rfl⟩
    · exact keyLt_irrefl v p q ((qPrec_qVar v v p q p q).mp hx).2.2
    · exact qsat_not_prec_left c _ ![p, q] hx
  trans x y z hxy hyz := by
    rcases qm_cases x with ⟨v, p, q, rfl⟩ | ⟨c, p, q, rfl⟩
    on_goal 2 => exact absurd hxy (qsat_not_prec_left c _ ![p, q])
    rcases qm_cases y with ⟨v', p', q', rfl⟩ | ⟨c', p', q', rfl⟩
    on_goal 2 => exact absurd hxy (qsat_not_prec_right c' _ ![p', q'])
    rcases qm_cases z with ⟨v'', p'', q'', rfl⟩ | ⟨c'', p'', q'', rfl⟩
    on_goal 2 => exact absurd hyz (qsat_not_prec_right c'' _ ![p'', q''])
    obtain ⟨h1, -, h3⟩ := (qPrec_qVar v v' p q p' q').mp hxy
    obtain ⟨-, h5, h6⟩ := (qPrec_qVar v' v'' p' q' p'' q'').mp hyz
    exact (qPrec_qVar v v'' p q p'' q'').mpr ⟨h1, h5, keyLt_trans h3 h6⟩
  total x y hx hy hne := by
    rcases qm_cases x with ⟨v, p, q, rfl⟩ | ⟨c, p, q, rfl⟩
    on_goal 2 => exact absurd hx (not_isQVar_qCl c p q)
    rcases qm_cases y with ⟨v', p', q', rfl⟩ | ⟨c', p', q', rfl⟩
    on_goal 2 => exact absurd hy (not_isQVar_qCl c' p' q')
    have hne' : ¬(v = v' ∧ p = p' ∧ q = q') := by
      rintro ⟨rfl, rfl, rfl⟩
      exact hne rfl
    have hvx := (isQVar_qVar v p q).mp hx
    have hvy := (isQVar_qVar v' p' q').mp hy
    exact (keyLt_total hne').imp (fun h => (qPrec_qVar v v' p q p' q').mpr ⟨hvx, hvy, h⟩)
      (fun h => (qPrec_qVar v' v p' q' p q).mpr ⟨hvy, hvx, h⟩)

end Wf

/-! ### Blocks -/

section Blocks

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A]

/-- The variables of the block with block coordinates `T`. -/
def QBlk (T : ℕ × A × ℕ) : QM A → Prop := fun x =>
  ∃ v p q, x = qVar v p q ∧ QVarOn v p q ∧ keyTriple v p q = T

/-- The variables quantified before the block with block coordinates `T`. -/
def QPlayed (T : ℕ × A × ℕ) : QM A → Prop := fun x =>
  ∃ v p q, x = qVar v p q ∧ QVarOn v p q ∧ TripleLt (keyTriple v p q) T

theorem qBlk_qVar {T : ℕ × A × ℕ} {v : QVarTag} {p q : A} (hv : QVarOn v p q)
    (h : keyTriple v p q = T) : QBlk T (qVar v p q) :=
  ⟨v, p, q, rfl, hv, h⟩

theorem qPlayed_qVar {T : ℕ × A × ℕ} {v : QVarTag} {p q : A} (hv : QVarOn v p q)
    (h : TripleLt (keyTriple v p q) T) : QPlayed T (qVar v p q) :=
  ⟨v, p, q, rfl, hv, h⟩

theorem qBlk_iff {T : ℕ × A × ℕ} {v : QVarTag} {p q : A} :
    QBlk T (qVar v p q) ↔ QVarOn v p q ∧ keyTriple v p q = T := by
  refine ⟨fun ⟨v', p', q', he, hv, h⟩ => ?_, fun h => ⟨v, p, q, rfl, h.1, h.2⟩⟩
  obtain ⟨rfl, rfl, rfl⟩ := qVar_inj he
  exact ⟨hv, h⟩

theorem qPlayed_iff {T : ℕ × A × ℕ} {v : QVarTag} {p q : A} :
    QPlayed T (qVar v p q) ↔ QVarOn v p q ∧ TripleLt (keyTriple v p q) T := by
  refine ⟨fun ⟨v', p', q', he, hv, h⟩ => ?_, fun h => ⟨v, p, q, rfl, h.1, h.2⟩⟩
  obtain ⟨rfl, rfl, rfl⟩ := qVar_inj he
  exact ⟨hv, h⟩

/-- **The block is the next one to be quantified** at its position. -/
theorem qBlock_qBlk (T : ℕ × A × ℕ) : QBlock (QPlayed T) (QBlk (A := A) T) where
  isVar x hx := by
    obtain ⟨v, p, q, rfl, hv, -⟩ := hx
    exact (isQVar_qVar v p q).mpr hv
  unplayed x hx hp := by
    obtain ⟨v, p, q, rfl, -, he⟩ := hx
    exact tripleLt_irrefl _ (he ▸ (qPlayed_iff.mp hp).2)
  first x y hx hy hpy hby := by
    obtain ⟨v, p, q, rfl, hv, he⟩ := hx
    rcases qm_cases y with ⟨v', p', q', rfl⟩ | ⟨c', p', q', rfl⟩
    · have hv' := (isQVar_qVar v' p' q').mp hy
      have hne : keyTriple v' p' q' ≠ T := fun h => hby (qBlk_iff.mpr ⟨hv', h⟩)
      have hnl : ¬TripleLt (keyTriple v' p' q') T := fun h => hpy (qPlayed_iff.mpr ⟨hv', h⟩)
      refine (qPrec_qVar v v' p q p' q').mpr ⟨hv, hv', keyLt_of_tripleLt ?_⟩
      rw [he]
      exact ((tripleLt_total (Ne.symm hne)).resolve_right hnl)
    · exact absurd hy (not_isQVar_qCl c' p' q')

/-- **The position is downward closed**, so the peeling lemmas can be
iterated. -/
theorem qDownClosed_qPlayed (T : ℕ × A × ℕ) : QDownClosed (QPlayed (A := A) T) := by
  intro y z hy hyz hz
  rcases qm_cases y with ⟨v, p, q, rfl⟩ | ⟨c, p, q, rfl⟩
  · rcases qm_cases z with ⟨v', p', q', rfl⟩ | ⟨c', p', q', rfl⟩
    · obtain ⟨hv, -, hlt⟩ := (qPrec_qVar v v' p q p' q').mp hyz
      obtain ⟨-, hz'⟩ := qPlayed_iff.mp hz
      refine qPlayed_qVar hv ?_
      rcases tripleLt_or_eq_of_keyLt hlt with h | h
      · exact tripleLt_trans h hz'
      · exact h ▸ hz'
    · exact absurd hyz (qsat_not_prec_right c' _ ![p', q'])
  · exact absurd hy (not_isQVar_qCl c p q)

/-- **Passing to the next block**: the variables played before the block `T'`
are those played before `T` together with those of `T`, as soon as the block
coordinates of every variable say so. -/
theorem qPlayed_step {T T' : ℕ × A × ℕ}
    (h : ∀ (v : QVarTag) (p q : A), QVarOn v p q →
      (TripleLt (keyTriple v p q) T' ↔
        (TripleLt (keyTriple v p q) T ∨ keyTriple v p q = T))) :
    qUnion (QPlayed T) (QBlk (A := A) T) = QPlayed T' := by
  funext x
  refine propext ⟨fun hx => ?_, fun hx => ?_⟩
  · rcases hx with ⟨v, p, q, rfl, hv, hlt⟩ | ⟨v, p, q, rfl, hv, he⟩
    · exact qPlayed_qVar hv ((h v p q hv).mpr (Or.inl hlt))
    · exact qPlayed_qVar hv ((h v p q hv).mpr (Or.inr he))
  · obtain ⟨v, p, q, rfl, hv, hlt⟩ := hx
    exact ((h v p q hv).mp hlt).imp (qPlayed_qVar hv) (qBlk_qVar hv)

end Blocks

end DescriptiveComplexity
