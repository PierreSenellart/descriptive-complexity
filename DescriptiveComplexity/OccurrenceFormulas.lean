/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OccurrenceOrder
import DescriptiveComplexity.Ordered

/-!
# First-order formulas for literal occurrences, over the ordered expansion

First-order counterpart of `DescriptiveComplexity.OccurrenceOrder`, shared by the
reductions *from* SAT (to 3-colorability, to 3SAT, …): parameterized formula
builders over the ordered expansion `Language.sat.sum Language.order`
(`DescriptiveComplexity.SatOcc.satOrd`) mirroring the semantic predicates on literal
occurrences — `occF` for `OccIn`, `minOccF`/`maxOccF` for `MinOcc`/`MaxOcc`,
`succOccF` for `SuccOcc`, `chainedF` for `Chained`, `emptyClF` for `EmptyCl`,
… — together with their realization lemmas (`realize_occF`, …).

All builders are parameterized by the indices of their free variables, so that
they can be instantiated at any variable type (in particular under
quantifiers). Occurrence *signs* are static (Lean-level) `Bool` parameters:
a quantification over signs becomes a finite conjunction or disjunction of
formulas.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

/-- The ordered expansion of the language of CNF instances. -/
abbrev satOrd : Language := Language.sat.sum Language.order

/-- The symbol for "is a clause" in the ordered expansion. -/
abbrev clSym : satOrd.Relations 1 := Sum.inl satIsClause

/-- The symbol for "occurs positively in" in the ordered expansion. -/
abbrev posSym : satOrd.Relations 2 := Sum.inl satPosIn

/-- The symbol for "occurs negatively in" in the ordered expansion. -/
abbrev negSym : satOrd.Relations 2 := Sum.inl satNegIn

/-! ### Formula builders -/

section Builders

variable {α : Type}

/-- `c` is a clause, as a formula. -/
def clF (c : α) : satOrd.Formula α :=
  Relations.formula₁ clSym (Term.var c)

/-- `x` occurs positively in `c`, as a formula. -/
def posF (c x : α) : satOrd.Formula α :=
  Relations.formula₂ posSym (Term.var c) (Term.var x)

/-- `x` occurs negatively in `c`, as a formula. -/
def negF (c x : α) : satOrd.Formula α :=
  Relations.formula₂ negSym (Term.var c) (Term.var x)

/-- `x ≤ y`, as a formula. -/
def leF (x y : α) : satOrd.Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x = y`, as a formula. -/
def eqF (x y : α) : satOrd.Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- `x < y`, as a formula. -/
def ltF (x y : α) : satOrd.Formula α :=
  leF x y ⊓ ∼(eqF x y)

/-- The literal `(x, s)` occurs in the clause `c`, as a formula. -/
def occF (s : Bool) (c x : α) : satOrd.Formula α :=
  clF c ⊓ if s then posF c x else negF c x

/-- The occurrence position `(x, s)` precedes `(y, t)`, as a formula (the
signs are fixed parameters, so this is just `≤` or `<` on the variables). -/
def occLtF (s t : Bool) (x y : α) : satOrd.Formula α :=
  if s < t then leF x y else ltF x y

/-- Some occurrence of `c` lies strictly before `(x, s)`, as a formula. -/
noncomputable def existsEarlierF (s : Bool) (c x : α) : satOrd.Formula α :=
  ((occF false (.inl c) (.inr ()) ⊓ occLtF false s (.inr ()) (.inl x)) ⊔
    (occF true (.inl c) (.inr ()) ⊓ occLtF true s (.inr ()) (.inl x))).iExs Unit

/-- Some occurrence of `c` lies strictly after `(x, s)`, as a formula. -/
noncomputable def existsLaterF (s : Bool) (c x : α) : satOrd.Formula α :=
  ((occF false (.inl c) (.inr ()) ⊓ occLtF s false (.inl x) (.inr ())) ⊔
    (occF true (.inl c) (.inr ()) ⊓ occLtF s true (.inl x) (.inr ()))).iExs Unit

/-- `(x, s)` is the first occurrence of `c`, as a formula. -/
noncomputable def minOccF (s : Bool) (c x : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(existsEarlierF s c x)

/-- `(x, s)` is the last occurrence of `c`, as a formula. -/
noncomputable def maxOccF (s : Bool) (c x : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(existsLaterF s c x)

/-- `(x, s)` is a non-first occurrence of `c`, as a formula. -/
noncomputable def chainedF (s : Bool) (c x : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(minOccF s c x)

/-- `(x, s)` is an occurrence of `c` immediately preceded by the occurrence
`(y, t)`, as a formula. -/
noncomputable def succOccF (t s : Bool) (c y x : α) : satOrd.Formula α :=
  occF t c y ⊓ occF s c x ⊓ occLtF t s y x ⊓
    ∼((((occF false (.inl c) (.inr ()) ⊓ occLtF t false (.inl y) (.inr ())) ⊓
          occLtF false s (.inr ()) (.inl x)) ⊔
        ((occF true (.inl c) (.inr ()) ⊓ occLtF t true (.inl y) (.inr ())) ⊓
          occLtF true s (.inr ()) (.inl x))).iExs Unit)

/-- `(x, s)` is the unique literal of some clause, as a formula. -/
noncomputable def unitLitF (s : Bool) (x : α) : satOrd.Formula α :=
  (minOccF s (.inr ()) (.inl x) ⊓ maxOccF s (.inr ()) (.inl x)).iExs Unit

/-- `c` is an empty clause, as a formula. -/
noncomputable def emptyClF (c : α) : satOrd.Formula α :=
  clF c ⊓ ∼((occF false (.inl c) (.inr ()) ⊔ occF true (.inl c) (.inr ())).iExs Unit)

end Builders

/-! ### Realization lemmas -/

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

omit [Language.sat.Structure A] in
private theorem occLt_iff_le {x y : A} {s t : Bool} (h : s < t) : occLt x s y t ↔ x ≤ y := by
  constructor
  · rintro (h' | ⟨rfl, -⟩)
    exacts [h'.le, le_rfl]
  · intro h'
    rcases h'.lt_or_eq with h'' | rfl
    exacts [Or.inl h'', Or.inr ⟨rfl, h⟩]

omit [Language.sat.Structure A] in
private theorem occLt_iff_lt {x y : A} {s t : Bool} (h : ¬s < t) : occLt x s y t ↔ x < y := by
  constructor
  · rintro (h' | ⟨-, h''⟩)
    exacts [h', absurd h'' h]
  · exact Or.inl

@[simp]
theorem realize_clF {c : α} : (clF c).Realize v ↔ IsCl (v c) := by
  rw [clF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_posF {c x : α} : (posF c x).Realize v ↔ PosIn (v c) (v x) := by
  rw [posF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_negF {c x : α} : (negF c x).Realize v ↔ NegIn (v c) (v x) := by
  rw [negF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_leF {x y : α} : (leF x y).Realize v ↔ v x ≤ v y := by
  simp [leF, Formula.realize_rel₂]

@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]

@[simp]
theorem realize_ltF {x y : α} : (ltF x y).Realize v ↔ v x < v y := by
  simp [ltF, lt_iff_le_and_ne]

@[simp]
theorem realize_occF {s : Bool} {c x : α} :
    (occF s c x).Realize v ↔ OccIn (v c) (v x) s := by
  cases s <;> simp [occF, OccIn]

@[simp]
theorem realize_occLtF {s t : Bool} {x y : α} :
    (occLtF s t x y).Realize v ↔ occLt (v x) s (v y) t := by
  by_cases h : s < t
  · simp [occLtF, h, occLt_iff_le h]
  · simp [occLtF, h, occLt_iff_lt h]

@[simp]
theorem realize_existsEarlierF {s : Bool} {c x : α} :
    (existsEarlierF s c x).Realize v ↔ ∃ y t, OccIn (v c) y t ∧ occLt y t (v x) s := by
  simp only [existsEarlierF, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    exacts [⟨i (), false, h1, h2⟩, ⟨i (), true, h1, h2⟩]
  · rintro ⟨y, t, h1, h2⟩
    cases t
    exacts [⟨fun _ => y, Or.inl ⟨h1, h2⟩⟩, ⟨fun _ => y, Or.inr ⟨h1, h2⟩⟩]

@[simp]
theorem realize_existsLaterF {s : Bool} {c x : α} :
    (existsLaterF s c x).Realize v ↔ ∃ y t, OccIn (v c) y t ∧ occLt (v x) s y t := by
  simp only [existsLaterF, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    exacts [⟨i (), false, h1, h2⟩, ⟨i (), true, h1, h2⟩]
  · rintro ⟨y, t, h1, h2⟩
    cases t
    exacts [⟨fun _ => y, Or.inl ⟨h1, h2⟩⟩, ⟨fun _ => y, Or.inr ⟨h1, h2⟩⟩]

@[simp]
theorem realize_minOccF {s : Bool} {c x : α} :
    (minOccF s c x).Realize v ↔ MinOcc (v c) (v x) s := by
  simp only [minOccF, Formula.realize_inf, Formula.realize_not, realize_occF,
    realize_existsEarlierF]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun y t hyt hlt => h2 ⟨y, t, hyt, hlt⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨y, t, hyt, hlt⟩ => h2 y t hyt hlt⟩

@[simp]
theorem realize_maxOccF {s : Bool} {c x : α} :
    (maxOccF s c x).Realize v ↔ MaxOcc (v c) (v x) s := by
  simp only [maxOccF, Formula.realize_inf, Formula.realize_not, realize_occF,
    realize_existsLaterF]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun y t hyt hlt => h2 ⟨y, t, hyt, hlt⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨y, t, hyt, hlt⟩ => h2 y t hyt hlt⟩

@[simp]
theorem realize_chainedF {s : Bool} {c x : α} :
    (chainedF s c x).Realize v ↔ Chained (v c) (v x) s := by
  simp [chainedF, Chained]

@[simp]
theorem realize_succOccF {t s : Bool} {c y x : α} :
    (succOccF t s c y x).Realize v ↔ SuccOcc (v c) (v y) t (v x) s := by
  simp only [succOccF, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    Formula.realize_sup, realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun z u hz hb => h4 ?_⟩
    cases u
    exacts [⟨fun _ => z, Or.inl ⟨⟨hz, hb.1⟩, hb.2⟩⟩, ⟨fun _ => z, Or.inr ⟨⟨hz, hb.1⟩, hb.2⟩⟩]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    rintro ⟨i, ⟨⟨hz, hl1⟩, hl2⟩ | ⟨⟨hz, hl1⟩, hl2⟩⟩
    exacts [h4 (i ()) false hz ⟨hl1, hl2⟩, h4 (i ()) true hz ⟨hl1, hl2⟩]

@[simp]
theorem realize_unitLitF {s : Bool} {x : α} :
    (unitLitF s x).Realize v ↔ ∃ c, MinOcc c (v x) s ∧ MaxOcc c (v x) s := by
  simp only [unitLitF, Formula.realize_iExs, Formula.realize_inf, realize_minOccF,
    realize_maxOccF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i (), h1, h2⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨fun _ => c, h1, h2⟩

@[simp]
theorem realize_emptyClF {c : α} : (emptyClF c).Realize v ↔ EmptyCl (v c) := by
  simp only [emptyClF, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    Formula.realize_sup, realize_clF, realize_occF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x s hxs => h2 ?_⟩
    cases s
    exacts [⟨fun _ => x, Or.inl hxs⟩, ⟨fun _ => x, Or.inr hxs⟩]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨i, h | h⟩
    exacts [h2 (i ()) false h, h2 (i ()) true h]

end Realize

end SatOcc

end DescriptiveComplexity
