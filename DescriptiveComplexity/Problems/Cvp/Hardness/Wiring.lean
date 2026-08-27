/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Cvp.Hardness.Interp

/-!
# The drawn circuit, gate by gate

What the interpretation of
`DescriptiveComplexity.Problems.Cvp.Hardness.Interp` marks and wires, read
back as statements about *named points* – `bdPt`, `hdPt` … – rather than
about raw tagged tuples. Two kinds of lemma are needed downstream and both are
proved here once:

* the **marks**: which points are gates of which kind, and which point is the
  output;
* the **wires**: for each gate, an `iff` naming its left and right inputs, so
  that a derivation can be *built* (the `mpr` direction, used to evaluate the
  circuit) and *inverted* (the `mp` direction, used to prove that nothing else
  evaluates to `1`).

Everything is stated relative to a minimum `m` and a maximum `M` of the
universe, which a finite nonempty linear order supplies; the coordinates a tag
does not use are pinned to `m`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc CvpInterp

namespace CvpDraw

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-! ### The points -/

/-- The constant `1` gate. -/
def ttPt (m : A) : cvpInterp.Map A := (.tt, fun _ => m)

/-- The constant `0` gate. -/
def ffPt (m : A) : cvpInterp.Map A := (.ff, fun _ => m)

/-- The conjunction chain of the clause `c` up to the literal `y`, at stage
`s`. -/
def bdPt (c y s : A) : cvpInterp.Map A := (.bd, ![c, y, s])

/-- The conjunction chain of the clause `c` up to `y`, read at the last
stage. -/
def bdTopPt (m c y : A) : cvpInterp.Map A := (.bdTop, ![c, y, m])

/-- The propagation chain forcing `x` from the clauses up to `c`, at stage
`s`. -/
def hdPt (x c s : A) : cvpInterp.Map A := (.hd, ![x, c, s])

/-- The goal chain over the clauses up to `c`. -/
def glPt (m c : A) : cvpInterp.Map A := (.gl, ![c, m, m])

/-! ### The marks -/

section Marks

/-- Only the canonical `tt` point is a constant `1`. -/
theorem isTrue_iff (t : CvpTag) (w : Fin 3 → A) :
    RelMap (M := cvpInterp.Map A) circIsTrue ![(t, w)] ↔
      t = .tt ∧ (∀ a : A, w 0 ≤ a) ∧ (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a) := by
  rw [FOInterpretation.relMap_map]
  cases t <;>
    simp [cvpInterp, allMinF, realize_minF, and_assoc]

/-- The conjunction gates are the two conjunction chains. -/
theorem isAnd_iff (t : CvpTag) (w : Fin 3 → A) :
    RelMap (M := cvpInterp.Map A) circIsAnd ![(t, w)] ↔
      t = .bd ∨ (t = .bdTop ∧ ∀ a : A, w 2 ≤ a) := by
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [cvpInterp, realize_minF]

/-- The disjunction gates are the propagation chain and the goal chain. -/
theorem isOr_iff (t : CvpTag) (w : Fin 3 → A) :
    RelMap (M := cvpInterp.Map A) circIsOr ![(t, w)] ↔
      t = .hd ∨ (t = .gl ∧ (∀ a : A, w 1 ≤ a) ∧ ∀ a : A, w 2 ≤ a) := by
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [cvpInterp, realize_minF]

/-- **The circuit is monotone**: it has no negation gate. -/
theorem not_isNot (t : CvpTag) (w : Fin 3 → A) :
    ¬RelMap (M := cvpInterp.Map A) circIsNot ![(t, w)] := by
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [cvpInterp]

/-- The output is the top of the goal chain. -/
theorem out_iff (t : CvpTag) (w : Fin 3 → A) :
    RelMap (M := cvpInterp.Map A) circOut ![(t, w)] ↔
      t = .gl ∧ (∀ a : A, a ≤ w 0) ∧ (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a) := by
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [cvpInterp, realize_minF, realize_maxF, and_assoc]

end Marks

/-! ### The wires

Each gate names its left and its right input. The `mpr` direction builds a
derivation, the `mp` direction inverts one; the constants have no input at
all. -/

section Wires

variable {m : A}

omit [Language.sat.Structure A] in
/-- Being pinned to the minimum at every coordinate identifies a padded
point. -/
theorem eq_pad (hm : ∀ a : A, m ≤ a) {w : Fin 3 → A} (h0 : ∀ a : A, w 0 ≤ a)
    (h1 : ∀ a : A, w 1 ≤ a) (h2 : ∀ a : A, w 2 ≤ a) : w = fun _ => m := by
  funext j
  fin_cases j
  · exact le_antisymm (h0 m) (hm _)
  · exact le_antisymm (h1 m) (hm _)
  · exact le_antisymm (h2 m) (hm _)

omit [Language.sat.Structure A] in
/-- In a linear order with a minimum `m`, being below everything is being
`m`: the rewrite that turns the padding conditions into equations. -/
theorem isBot_iff_eq (hm : ∀ a : A, m ≤ a) (x : A) : (∀ a : A, x ≤ a) ↔ x = m :=
  ⟨fun h => le_antisymm (h m) (hm x), fun h a => h ▸ hm a⟩

/-- The left input of a conjunction chain: the constant `1` at the bottom of
the walk, the previous link otherwise. -/
theorem left_bd (hm : ∀ a : A, m ≤ a) (w : Fin 3 → A) (q : cvpInterp.Map A) :
    RelMap (M := cvpInterp.Map A) circLeft ![(CvpTag.bd, w), q] ↔
      ((∀ a : A, w 1 ≤ a) ∧ q = ttPt m) ∨ ∃ y', y' ⋖ w 1 ∧ q = bdPt (w 0) y' (w 2) := by
  obtain ⟨t', w'⟩ := q
  rw [FOInterpretation.relMap_map]
  cases t' <;>
    simp [cvpInterp, allMinF, ttPt, bdPt, realize_minF, realize_eqF, CovBy,
      FOInterpretation.Map, Prod.ext_iff, funext_iff, Fin.forall_fin_succ, isBot_iff_eq hm,
      and_assoc]

omit [Language.sat.Structure A] in
/-- Dually, being above everything is being the maximum. -/
theorem isTop_iff_eq {M : A} (hM : ∀ a : A, a ≤ M) (x : A) : (∀ a : A, a ≤ x) ↔ x = M :=
  ⟨fun h => le_antisymm (hM x) (h M), fun h a => h ▸ hM a⟩

/-- The left input of the top-stage conjunction chain. -/
theorem left_bdTop (hm : ∀ a : A, m ≤ a) (w : Fin 3 → A) (q : cvpInterp.Map A) :
    RelMap (M := cvpInterp.Map A) circLeft ![(CvpTag.bdTop, w), q] ↔
      ((∀ a : A, w 2 ≤ a) ∧ (∀ a : A, w 1 ≤ a) ∧ q = ttPt m) ∨
        ((∀ a : A, w 2 ≤ a) ∧ ∃ y', y' ⋖ w 1 ∧ q = bdTopPt m (w 0) y') := by
  obtain ⟨t', w'⟩ := q
  rw [FOInterpretation.relMap_map]
  cases t' <;>
    simp [cvpInterp, allMinF, ttPt, bdTopPt, realize_minF,
      realize_eqF,
      CovBy, FOInterpretation.Map, Prod.ext_iff, funext_iff, Fin.forall_fin_succ,
      isBot_iff_eq hm, and_assoc]
  all_goals tauto

/-- The left input of the propagation chain: the constant `0` at the bottom of
the walk over clauses, the previous link otherwise. -/
theorem left_hd (hm : ∀ a : A, m ≤ a) (w : Fin 3 → A) (q : cvpInterp.Map A) :
    RelMap (M := cvpInterp.Map A) circLeft ![(CvpTag.hd, w), q] ↔
      ((∀ a : A, w 1 ≤ a) ∧ q = ffPt m) ∨ ∃ c', c' ⋖ w 1 ∧ q = hdPt (w 0) c' (w 2) := by
  obtain ⟨t', w'⟩ := q
  rw [FOInterpretation.relMap_map]
  cases t' <;>
    simp [cvpInterp, allMinF, ffPt, hdPt, realize_minF,
      realize_eqF,
      CovBy, FOInterpretation.Map, Prod.ext_iff, funext_iff, Fin.forall_fin_succ,
      isBot_iff_eq hm, and_assoc]

/-- The left input of the goal chain. At the bottom of the walk it is the
constant `1` exactly when the instance is not Horn, which is what makes a
non-Horn instance a yes-instance outright. -/
theorem left_gl (hm : ∀ a : A, m ≤ a) (w : Fin 3 → A) (q : cvpInterp.Map A)
    (h1 : ∀ a : A, w 1 ≤ a) (h2 : ∀ a : A, w 2 ≤ a) :
    RelMap (M := cvpInterp.Map A) circLeft ![(CvpTag.gl, w), q] ↔
      ((∀ a : A, w 0 ≤ a) ∧ AtMostOnePositive A ∧ q = ffPt m) ∨
        ((∀ a : A, w 0 ≤ a) ∧ ¬AtMostOnePositive A ∧ q = ttPt m) ∨
          ∃ c', c' ⋖ w 0 ∧ q = glPt m c' := by
  have e1 : w 1 = m := le_antisymm (h1 m) (hm _)
  have e2 : w 2 = m := le_antisymm (h2 m) (hm _)
  obtain ⟨t', w'⟩ := q
  rw [FOInterpretation.relMap_map]
  cases t' <;>
    simp [cvpInterp, allMinF, ttPt, ffPt, glPt, realize_minF,
      realize_hornCondF,
      CovBy, FOInterpretation.Map, Prod.ext_iff, funext_iff, Fin.forall_fin_succ,
      isBot_iff_eq hm, and_assoc, e1, e2]

/-- The right input of a conjunction chain: the constant `1` when the literal
is not a negative literal of the clause, the constant `0` at the bottom stage,
and the propagation gate of the previous stage otherwise. -/
theorem right_bd (hm : ∀ a : A, m ≤ a) {M : A} (hM : ∀ a : A, a ≤ M) (w : Fin 3 → A)
    (q : cvpInterp.Map A) :
    RelMap (M := cvpInterp.Map A) circRight ![(CvpTag.bd, w), q] ↔
      (¬NegIn (w 0) (w 1) ∧ q = ttPt m) ∨
        (NegIn (w 0) (w 1) ∧ (∀ a : A, w 2 ≤ a) ∧ q = ffPt m) ∨
          (NegIn (w 0) (w 1) ∧ ∃ s', s' ⋖ w 2 ∧ q = hdPt (w 1) M s') := by
  obtain ⟨t', w'⟩ := q
  rw [FOInterpretation.relMap_map]
  cases t' <;>
    simp [cvpInterp, allMinF, ttPt, ffPt, hdPt, realize_minF, realize_maxF,
      realize_eqF, realize_negF,
      CovBy, FOInterpretation.Map, Prod.ext_iff, funext_iff, Fin.forall_fin_succ,
      isBot_iff_eq hm, isTop_iff_eq hM, and_assoc]
  tauto

/-- The right input of the top-stage conjunction chain reads the propagation
gate at the last stage. -/
theorem right_bdTop (hm : ∀ a : A, m ≤ a) {M : A} (hM : ∀ a : A, a ≤ M) (w : Fin 3 → A)
    (q : cvpInterp.Map A) (h2 : ∀ a : A, w 2 ≤ a) :
    RelMap (M := cvpInterp.Map A) circRight ![(CvpTag.bdTop, w), q] ↔
      (¬NegIn (w 0) (w 1) ∧ q = ttPt m) ∨ (NegIn (w 0) (w 1) ∧ q = hdPt (w 1) M M) := by
  have e2 : w 2 = m := le_antisymm (h2 m) (hm _)
  obtain ⟨t', w'⟩ := q
  rw [FOInterpretation.relMap_map]
  cases t' <;>
    simp [cvpInterp, allMinF, ttPt, hdPt, realize_minF, realize_maxF,
      realize_eqF, realize_negF,
      FOInterpretation.Map, Prod.ext_iff, funext_iff, Fin.forall_fin_succ,
      isBot_iff_eq hm, isTop_iff_eq hM, and_assoc, e2]

/-- The right input of the propagation chain: the body of the clause at hand
when that clause has the right positive literal, the constant `0` otherwise. -/
theorem right_hd (hm : ∀ a : A, m ≤ a) {M : A} (hM : ∀ a : A, a ≤ M) (w : Fin 3 → A)
    (q : cvpInterp.Map A) :
    RelMap (M := cvpInterp.Map A) circRight ![(CvpTag.hd, w), q] ↔
      ((IsCl (w 1) ∧ PosIn (w 1) (w 0)) ∧ q = bdPt (w 1) M (w 2)) ∨
        (¬(IsCl (w 1) ∧ PosIn (w 1) (w 0)) ∧ q = ffPt m) := by
  obtain ⟨t', w'⟩ := q
  rw [FOInterpretation.relMap_map]
  cases t' <;>
    simp [cvpInterp, allMinF, ffPt, bdPt, realize_minF, realize_maxF,
      realize_eqF, realize_clF, realize_posF,
      FOInterpretation.Map, Prod.ext_iff, funext_iff, Fin.forall_fin_succ,
      isBot_iff_eq hm, isTop_iff_eq hM, and_assoc]

/-- The right input of the goal chain: the top-stage body of the clause at
hand when it is a goal clause, the constant `0` otherwise. -/
theorem right_gl (hm : ∀ a : A, m ≤ a) {M : A} (hM : ∀ a : A, a ≤ M) (w : Fin 3 → A)
    (q : cvpInterp.Map A) (h1 : ∀ a : A, w 1 ≤ a) (h2 : ∀ a : A, w 2 ≤ a) :
    RelMap (M := cvpInterp.Map A) circRight ![(CvpTag.gl, w), q] ↔
      ((IsCl (w 0) ∧ ∀ x : A, ¬PosIn (w 0) x) ∧ q = bdTopPt m (w 0) M) ∨
        (¬(IsCl (w 0) ∧ ∀ x : A, ¬PosIn (w 0) x) ∧ q = ffPt m) := by
  have e1 : w 1 = m := le_antisymm (h1 m) (hm _)
  have e2 : w 2 = m := le_antisymm (h2 m) (hm _)
  obtain ⟨t', w'⟩ := q
  rw [FOInterpretation.relMap_map]
  cases t' <;>
    simp [cvpInterp, allMinF, ffPt, bdTopPt, realize_minF, realize_maxF,
      realize_eqF, realize_noPosClF,
      FOInterpretation.Map, Prod.ext_iff, funext_iff, Fin.forall_fin_succ,
      isBot_iff_eq hm, isTop_iff_eq hM, and_assoc, e1, e2]

end Wires

end CvpDraw

end DescriptiveComplexity
