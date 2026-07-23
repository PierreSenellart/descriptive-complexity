/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MaxCut.Defs
import DescriptiveComplexity.Problems.NaeThreeSat

/-!
# The gadget graph of the reduction from NAE-3SAT to Max Cut

This file builds the interpretation `DescriptiveComplexity.MaxCutInterp.mcInterp` of
Max Cut instances in ordered CNF instances, and characterizes its two
relations. The correctness of the reduction is in
`DescriptiveComplexity.Problems.MaxCut.Reduction`.

## The gadget

Vertices come in three tags over pairs `(Fin 2 → A)`:

* `litPt s x`, the *literal vertex* of `(x, s)`, on diagonal pairs;
* `occPt s c x`, the *occurrence vertex* of the occurrence `(x, s)` of the
  clause `c`;
* `penPt c`, an isolated *penalty vertex*, used only to carry a threshold
  unit.

and edges in three families:

* `litPt s x — litPt (!s) x`, one per element of the universe;
* `occPt s c x — litPt s x`, one per occurrence;
* `occPt s c x — occPt t c y`, for distinct occurrences of the same clause.

The threshold marks one pair per element (the variable edge), one pair per
occurrence (the occurrence edge), one pair per *non-maximal* occurrence of a
clause (charged against the maximal one, so `k − 1` per clause of width `k`),
and one pair per clause with at most one occurrence – a penalty, since such a
clause is never not-all-equal satisfiable while its gadget carries no edge at
all.

Two design points are worth recording.

* Giving every *occurrence* its own vertex, joined to its literal vertex by a
  single edge, is what makes the three edge families live on disjoint pairs of
  tags, hence edge-disjoint: putting the clause gadgets directly on literal
  vertices would let two clauses over the same two literals share an edge, and
  a clause containing both `x` and `¬x` reuse a variable edge, and the count
  would break. The occurrence vertex then carries the *negation* of its
  literal, which is harmless: not-all-equal satisfaction is invariant under
  flipping all the literals of a clause.
* No edge weight or multiplicity is needed anywhere. The cut splits as a sum
  over the three families, each maximal on its own, so a single edge per
  variable already forces the two literal vertices apart.

Everything is gated on the first-order width check `ThreeSatToSat.Wide`, as in
the reduction of 3SAT to SAT: on a wide input the graph has no edge at all,
while the threshold stays positive, so the output is a no-instance. The gate
is what makes the per-clause budget `k − 1` an upper bound, a clique on `k`
vertices having a larger cut as soon as `k ≥ 4`.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace MaxCutInterp

open Language Structure SatOcc

/-- Tags for the gadget graph: literal vertices, occurrence vertices, and the
isolated penalty vertices carrying a threshold unit for degenerate clauses. -/
inductive MCTag : Type
  /-- `litPt s x` is the vertex of the literal `(x, s)`. -/
  | lit (s : Bool)
  /-- `occPt s c x` is the vertex of the occurrence `(x, s)` of the clause `c`. -/
  | occ (s : Bool)
  /-- `penPt c` is the isolated penalty vertex of the clause `c`. -/
  | pen
  deriving DecidableEq, Fintype, Nonempty

/-! ### Two more formulas over the ordered expansion -/

section Builders

variable {α : Type}

/-- Some clause has at least four distinct literal occurrences, as a formula
over the ordered expansion: the same check as `ThreeSatToSat.wideS`, whose
negation gates the whole gadget. -/
noncomputable def wideF : satOrd.Formula α :=
  (Formula.iSup fun s : Fin 4 → Bool =>
      (Formula.iInf fun i : Fin 4 => occF (s i) (Sum.inr 0) (Sum.inr i.succ)) ⊓
      Formula.iInf fun p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2 ∧ s p.1 = s p.2} =>
        ∼(eqF (Sum.inr (p.1.1.succ : Fin 5)) (Sum.inr p.1.2.succ))).iExs (Fin 5)

/-- No occurrence of `c` is a non-first one, as a formula: this says exactly
that the clause `c` has at most one occurrence. -/
noncomputable def noChainedF (c : α) : satOrd.Formula α :=
  ∼((chainedF false (Sum.inl c) (Sum.inr ()) ⊔
      chainedF true (Sum.inl c) (Sum.inr ())).iExs Unit)

end Builders

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

@[simp]
theorem realize_wideF : (wideF (α := α)).Realize v ↔ ThreeSatToSat.Wide A := by
  simp only [wideF, Formula.realize_iExs, Formula.realize_iSup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_not, realize_occF, realize_eqF, Sum.elim_inr]
  constructor
  · rintro ⟨e, s, hocc, hdist⟩
    exact ⟨e 0, fun i => e i.succ, s, hocc, fun i j hij hs => hdist ⟨(i, j), hij, hs⟩⟩
  · rintro ⟨c, x, s, hocc, hdist⟩
    refine ⟨Fin.cases c x, s, fun i => ?_, fun p => ?_⟩
    · simpa using hocc i
    · simpa using hdist p.1.1 p.1.2 p.2.1 p.2.2

@[simp]
theorem realize_noChainedF {c : α} :
    (noChainedF c).Realize v ↔ ∀ x s, ¬Chained (v c) x s := by
  simp only [noChainedF, Formula.realize_not, Formula.realize_iExs, Formula.realize_sup,
    realize_chainedF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h x s hx
    cases s with
    | false => exact h ⟨fun _ => x, Or.inl hx⟩
    | true => exact h ⟨fun _ => x, Or.inr hx⟩
  · rintro h ⟨i, hi | hi⟩
    exacts [h (i ()) false hi, h (i ()) true hi]

end Realize

/-! ### The interpretation -/

/-- Defining formula for adjacency, before the width gate: the three edge
families. -/
noncomputable def adjF : MCTag → MCTag → satOrd.Formula (Fin 2 × Fin 2)
  | .lit s, .lit t =>
      if s = t then ⊥
      else eqF (0, 0) (0, 1) ⊓ eqF (1, 0) (1, 1) ⊓ eqF (0, 0) (1, 0)
  | .occ s, .lit t =>
      if s = t then occF s (0, 0) (0, 1) ⊓ eqF (1, 0) (1, 1) ⊓ eqF (0, 1) (1, 0) else ⊥
  | .lit t, .occ s =>
      if s = t then occF s (1, 0) (1, 1) ⊓ eqF (0, 0) (0, 1) ⊓ eqF (1, 1) (0, 0) else ⊥
  | .occ s, .occ t =>
      occF s (0, 0) (0, 1) ⊓ occF t (1, 0) (1, 1) ⊓ eqF (0, 0) (1, 0) ⊓
        (if s = t then ∼(eqF (0, 1) (1, 1)) else ⊤)
  | _, _ => ⊥

/-- Defining formula for the threshold marks: one pair per element, one per
occurrence, one per non-maximal occurrence, one per degenerate clause. -/
noncomputable def markF : MCTag → MCTag → satOrd.Formula (Fin 2 × Fin 2)
  | .lit true, .lit false => eqF (0, 0) (0, 1) ⊓ eqF (1, 0) (1, 1) ⊓ eqF (0, 0) (1, 0)
  | .occ s, .lit t =>
      if s = t then occF s (0, 0) (0, 1) ⊓ eqF (1, 0) (1, 1) ⊓ eqF (0, 1) (1, 0) else ⊥
  | .occ s, .occ t =>
      occF s (0, 0) (0, 1) ⊓ maxOccF t (1, 0) (1, 1) ⊓ eqF (0, 0) (1, 0) ⊓
        (if s = t then ∼(eqF (0, 1) (1, 1)) else ⊤)
  | .pen, .pen =>
      eqF (0, 0) (0, 1) ⊓ eqF (1, 0) (1, 1) ⊓ eqF (0, 0) (1, 0) ⊓ clF (0, 0) ⊓
        noChainedF (0, 0)
  | _, _ => ⊥

/-- The interpretation of Max Cut instances in ordered CNF instances: the
gadget graph, with every edge gated on the width check. -/
noncomputable def mcInterp : FOInterpretation satOrd Language.markedArcGraph MCTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t => adjF (t 0) (t 1) ⊓ ∼wideF
    | _, .markedArc => fun t => markF (t 0) (t 1)

/-! ### The vertices -/

section Points

variable {A : Type}

/-- The literal vertex of `(x, s)`. -/
def litPt (s : Bool) (x : A) : mcInterp.Map A := (MCTag.lit s, fun _ => x)

/-- The occurrence vertex of the occurrence `(x, s)` of `c`. -/
def occPt (s : Bool) (c x : A) : mcInterp.Map A := (MCTag.occ s, ![c, x])

/-- The penalty vertex of the clause `c`. -/
def penPt (c : A) : mcInterp.Map A := (MCTag.pen, fun _ => c)

theorem litPt_eq_iff {s t : Bool} {x y : A} : litPt s x = litPt t y ↔ s = t ∧ x = y := by
  constructor
  · intro h
    exact ⟨by simpa [litPt] using congrArg (fun p : mcInterp.Map A => p.1) h,
      by simpa [litPt] using congrArg (fun p : mcInterp.Map A => p.2 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem occPt_eq_iff {s t : Bool} {c d x y : A} :
    occPt s c x = occPt t d y ↔ s = t ∧ c = d ∧ x = y := by
  constructor
  · intro h
    refine ⟨by simpa [occPt] using congrArg (fun p : mcInterp.Map A => p.1) h, ?_, ?_⟩
    · simpa [occPt] using congrArg (fun p : mcInterp.Map A => p.2 0) h
    · simpa [occPt] using congrArg (fun p : mcInterp.Map A => p.2 1) h
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem litPt_ne_occPt {s t : Bool} {c x y : A} : litPt s x ≠ occPt t c y := fun h => by
  simpa [litPt, occPt] using congrArg (fun p : mcInterp.Map A => p.1) h

theorem litPt_ne_penPt {s : Bool} {c x : A} : litPt s x ≠ penPt c := fun h => by
  simpa [litPt, penPt] using congrArg (fun p : mcInterp.Map A => p.1) h

theorem occPt_ne_penPt {s : Bool} {c d x : A} : occPt s c x ≠ penPt d := fun h => by
  simpa [occPt, penPt] using congrArg (fun p : mcInterp.Map A => p.1) h

@[simp]
theorem litPt_eq_occPt_iff {s t : Bool} {c x y : A} : (litPt s x = occPt t c y) ↔ False :=
  iff_of_false litPt_ne_occPt (fun h => h.elim)

@[simp]
theorem occPt_eq_litPt_iff {s t : Bool} {c x y : A} : (occPt t c y = litPt s x) ↔ False :=
  iff_of_false litPt_ne_occPt.symm (fun h => h.elim)

@[simp]
theorem litPt_eq_penPt_iff {s : Bool} {c x : A} : (litPt s x = penPt c) ↔ False :=
  iff_of_false litPt_ne_penPt (fun h => h.elim)

@[simp]
theorem penPt_eq_litPt_iff {s : Bool} {c x : A} : (penPt c = litPt s x) ↔ False :=
  iff_of_false litPt_ne_penPt.symm (fun h => h.elim)

@[simp]
theorem occPt_eq_penPt_iff {s : Bool} {c d x : A} : (occPt s c x = penPt d) ↔ False :=
  iff_of_false occPt_ne_penPt (fun h => h.elim)

@[simp]
theorem penPt_eq_occPt_iff {s : Bool} {c d x : A} : (penPt d = occPt s c x) ↔ False :=
  iff_of_false occPt_ne_penPt.symm (fun h => h.elim)

theorem litPt_eta {s : Bool} {w : Fin 2 → A} (h : w 0 = w 1) :
    ((MCTag.lit s, w) : mcInterp.Map A) = litPt s (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [litPt, h]⟩

theorem occPt_eta {s : Bool} {w : Fin 2 → A} :
    ((MCTag.occ s, w) : mcInterp.Map A) = occPt s (w 0) (w 1) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [occPt]⟩

theorem penPt_eta {w : Fin 2 → A} (h : w 0 = w 1) :
    ((MCTag.pen, w) : mcInterp.Map A) = penPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [penPt, h]⟩

end Points

/-! ### Characterization of the two relations -/

section Shapes

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The shape of an edge, read on tags and coordinates. -/
def AdjShape : MCTag → MCTag → (Fin 2 → A) → (Fin 2 → A) → Prop
  | .lit s, .lit t, w₁, w₂ => s ≠ t ∧ w₁ 0 = w₁ 1 ∧ w₂ 0 = w₂ 1 ∧ w₁ 0 = w₂ 0
  | .occ s, .lit t, w₁, w₂ => s = t ∧ OccIn (w₁ 0) (w₁ 1) s ∧ w₂ 0 = w₂ 1 ∧ w₁ 1 = w₂ 0
  | .lit t, .occ s, w₁, w₂ => s = t ∧ OccIn (w₂ 0) (w₂ 1) s ∧ w₁ 0 = w₁ 1 ∧ w₂ 1 = w₁ 0
  | .occ s, .occ t, w₁, w₂ =>
      OccIn (w₁ 0) (w₁ 1) s ∧ OccIn (w₂ 0) (w₂ 1) t ∧ w₁ 0 = w₂ 0 ∧ ¬(w₁ 1 = w₂ 1 ∧ s = t)
  | _, _, _, _ => False

/-- The shape of a threshold mark, read on tags and coordinates. -/
def MarkShape : MCTag → MCTag → (Fin 2 → A) → (Fin 2 → A) → Prop
  | .lit s, .lit t, w₁, w₂ =>
      s = true ∧ t = false ∧ w₁ 0 = w₁ 1 ∧ w₂ 0 = w₂ 1 ∧ w₁ 0 = w₂ 0
  | .occ s, .lit t, w₁, w₂ => s = t ∧ OccIn (w₁ 0) (w₁ 1) s ∧ w₂ 0 = w₂ 1 ∧ w₁ 1 = w₂ 0
  | .occ s, .occ t, w₁, w₂ =>
      OccIn (w₁ 0) (w₁ 1) s ∧ MaxOcc (w₂ 0) (w₂ 1) t ∧ w₁ 0 = w₂ 0 ∧
        ¬(w₁ 1 = w₂ 1 ∧ s = t)
  | .pen, .pen, w₁, w₂ =>
      w₁ 0 = w₁ 1 ∧ w₂ 0 = w₂ 1 ∧ w₁ 0 = w₂ 0 ∧ IsCl (w₁ 0) ∧ ∀ x s, ¬Chained (w₁ 0) x s
  | _, _, _, _ => False

/-- **The edges of the gadget graph**, on tagged tuples. -/
theorem adj_iff_aux (t₁ t₂ : MCTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := mcInterp.Map A) magAdj ![(t₁, w₁), (t₂, w₂)] ↔
      ¬ThreeSatToSat.Wide A ∧ AdjShape t₁ t₂ w₁ w₂ := by
  rw [FOInterpretation.relMap_map]
  cases t₁ with
  | lit s =>
    cases t₂ with
    | lit t =>
      rcases eq_or_ne s t with rfl | hst
      · simp [mcInterp, adjF, AdjShape]
      · simp [mcInterp, adjF, AdjShape, hst, and_assoc, and_comm]
        tauto
    | occ t =>
      rcases eq_or_ne t s with rfl | hst
      · simp [mcInterp, adjF, AdjShape, and_assoc, and_comm]
        tauto
      · simp [mcInterp, adjF, AdjShape, hst]
    | pen => simp [mcInterp, adjF, AdjShape]
  | occ s =>
    cases t₂ with
    | lit t =>
      rcases eq_or_ne s t with rfl | hst
      · simp [mcInterp, adjF, AdjShape, and_assoc, and_comm]
        tauto
      · simp [mcInterp, adjF, AdjShape, hst]
    | occ t =>
      rcases eq_or_ne s t with rfl | hst
      · simp [mcInterp, adjF, AdjShape, and_assoc]
        tauto
      · simp [mcInterp, adjF, AdjShape, hst, and_assoc]
        tauto
    | pen => simp [mcInterp, adjF, AdjShape]
  | pen => cases t₂ <;> simp [mcInterp, adjF, AdjShape]

/-- **The threshold marks of the gadget graph**, on tagged tuples. -/
theorem marked_iff_aux (t₁ t₂ : MCTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := mcInterp.Map A) magMarked ![(t₁, w₁), (t₂, w₂)] ↔ MarkShape t₁ t₂ w₁ w₂ := by
  rw [FOInterpretation.relMap_map]
  cases t₁ with
  | lit s =>
    cases t₂ with
    | lit t =>
      cases s <;> cases t <;> simp [mcInterp, markF, MarkShape, and_assoc]
    | occ t => simp [mcInterp, markF, MarkShape]
    | pen => simp [mcInterp, markF, MarkShape]
  | occ s =>
    cases t₂ with
    | lit t =>
      rcases eq_or_ne s t with rfl | hst
      · simp [mcInterp, markF, MarkShape, and_assoc, and_comm]
        tauto
      · simp [mcInterp, markF, MarkShape, hst]
    | occ t =>
      rcases eq_or_ne s t with rfl | hst
      · simp [mcInterp, markF, MarkShape, and_assoc]
      · simp [mcInterp, markF, MarkShape, hst, and_assoc]
    | pen => simp [mcInterp, markF, MarkShape]
  | pen =>
    cases t₂ with
    | lit t => simp [mcInterp, markF, MarkShape]
    | occ t => simp [mcInterp, markF, MarkShape]
    | pen => simp [mcInterp, markF, MarkShape, and_assoc]

end Shapes

section Characterizations

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- Every edge of the gadget graph belongs to one of the three families. -/
theorem adj_cases {p q : mcInterp.Map A} (h : MAGAdj p q) :
    ¬ThreeSatToSat.Wide A ∧
      ((∃ s x, p = litPt s x ∧ q = litPt (!s) x) ∨
        (∃ s c x, OccIn c x s ∧ p = occPt s c x ∧ q = litPt s x) ∨
        (∃ s c x, OccIn c x s ∧ p = litPt s x ∧ q = occPt s c x) ∨
        ∃ s t c x y, OccIn c x s ∧ OccIn c y t ∧ ¬(x = y ∧ s = t) ∧
          p = occPt s c x ∧ q = occPt t c y) := by
  obtain ⟨t₁, w₁⟩ := p
  obtain ⟨t₂, w₂⟩ := q
  obtain ⟨hw, hs⟩ := (adj_iff_aux t₁ t₂ w₁ w₂).mp h
  refine ⟨hw, ?_⟩
  cases t₁ with
  | lit s =>
    cases t₂ with
    | lit t =>
      obtain ⟨hst, h1, h2, h3⟩ := hs
      have ht : t = !s := by cases s <;> cases t <;> simp_all
      refine Or.inl ⟨s, w₁ 0, litPt_eta h1, ?_⟩
      rw [litPt_eta h2, ← h3, ht]
    | occ t =>
      obtain ⟨rfl, hocc, h1, h2⟩ := hs
      refine Or.inr (Or.inr (Or.inl ⟨t, w₂ 0, w₂ 1, hocc, ?_, occPt_eta⟩))
      rw [litPt_eta h1, ← h2]
    | pen => exact hs.elim
  | occ s =>
    cases t₂ with
    | lit t =>
      obtain ⟨rfl, hocc, h1, h2⟩ := hs
      refine Or.inr (Or.inl ⟨s, w₁ 0, w₁ 1, hocc, occPt_eta, ?_⟩)
      rw [litPt_eta h1, ← h2]
    | occ t =>
      obtain ⟨h1, h2, h3, h4⟩ := hs
      refine Or.inr (Or.inr (Or.inr ⟨s, t, w₁ 0, w₁ 1, w₂ 1, h1, ?_, ?_, occPt_eta, ?_⟩))
      · rw [← h3] at h2
        exact h2
      · exact h4
      · rw [occPt_eta, ← h3]
    | pen => exact hs.elim
  | pen => cases t₂ <;> exact hs.elim

/-- Every threshold mark belongs to one of the four families. -/
theorem marked_cases {p q : mcInterp.Map A} (h : MAGMarked p q) :
    (∃ x, p = litPt true x ∧ q = litPt false x) ∨
      (∃ s c x, OccIn c x s ∧ p = occPt s c x ∧ q = litPt s x) ∨
      (∃ s t c x y, OccIn c x s ∧ MaxOcc c y t ∧ ¬(x = y ∧ s = t) ∧
        p = occPt s c x ∧ q = occPt t c y) ∨
      ∃ c, IsCl c ∧ (∀ x s, ¬Chained c x s) ∧ p = penPt c ∧ q = penPt c := by
  obtain ⟨t₁, w₁⟩ := p
  obtain ⟨t₂, w₂⟩ := q
  have hs := (marked_iff_aux t₁ t₂ w₁ w₂).mp h
  cases t₁ with
  | lit s =>
    cases t₂ with
    | lit t =>
      obtain ⟨rfl, rfl, h1, h2, h3⟩ := hs
      refine Or.inl ⟨w₁ 0, litPt_eta h1, ?_⟩
      rw [litPt_eta h2, ← h3]
    | occ t => exact hs.elim
    | pen => exact hs.elim
  | occ s =>
    cases t₂ with
    | lit t =>
      obtain ⟨rfl, hocc, h1, h2⟩ := hs
      refine Or.inr (Or.inl ⟨s, w₁ 0, w₁ 1, hocc, occPt_eta, ?_⟩)
      rw [litPt_eta h1, ← h2]
    | occ t =>
      obtain ⟨h1, h2, h3, h4⟩ := hs
      refine Or.inr (Or.inr (Or.inl ⟨s, t, w₁ 0, w₁ 1, w₂ 1, h1, ?_, h4, occPt_eta, ?_⟩))
      · rw [← h3] at h2
        exact h2
      · rw [occPt_eta, ← h3]
    | pen => exact hs.elim
  | pen =>
    cases t₂ with
    | lit t => exact hs.elim
    | occ t => exact hs.elim
    | pen =>
      obtain ⟨h1, h2, h3, hcl, hch⟩ := hs
      refine Or.inr (Or.inr (Or.inr ⟨w₁ 0, hcl, hch, penPt_eta h1, ?_⟩))
      rw [penPt_eta h2, ← h3]

/-- The variable edge of an element. -/
theorem adj_lit_lit (hw : ¬ThreeSatToSat.Wide A) {s t : Bool} (hst : s ≠ t) (x : A) :
    MAGAdj (litPt s x) (litPt t x) :=
  (adj_iff_aux _ _ _ _).mpr ⟨hw, hst, rfl, rfl, rfl⟩

/-- The edge joining an occurrence vertex to its literal vertex. -/
theorem adj_occ_lit (hw : ¬ThreeSatToSat.Wide A) {s : Bool} {c x : A} (h : OccIn c x s) :
    MAGAdj (occPt s c x) (litPt s x) :=
  (adj_iff_aux _ _ _ _).mpr ⟨hw, rfl, h, rfl, rfl⟩

/-- The edge joining a literal vertex to an occurrence vertex. -/
theorem adj_lit_occ (hw : ¬ThreeSatToSat.Wide A) {s : Bool} {c x : A} (h : OccIn c x s) :
    MAGAdj (litPt s x) (occPt s c x) :=
  (adj_iff_aux _ _ _ _).mpr ⟨hw, rfl, h, rfl, rfl⟩

/-- The edges of the gadget of a clause. -/
theorem adj_occ_occ (hw : ¬ThreeSatToSat.Wide A) {s t : Bool} {c x y : A}
    (hx : OccIn c x s) (hy : OccIn c y t) (hne : ¬(x = y ∧ s = t)) :
    MAGAdj (occPt s c x) (occPt t c y) :=
  (adj_iff_aux _ _ _ _).mpr ⟨hw, hx, hy, rfl, hne⟩

/-- The threshold mark of an element. -/
theorem marked_lit (x : A) : MAGMarked (litPt true x) (litPt false x) :=
  (marked_iff_aux _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The threshold mark of an occurrence. -/
theorem marked_occ_lit {s : Bool} {c x : A} (h : OccIn c x s) :
    MAGMarked (occPt s c x) (litPt s x) :=
  (marked_iff_aux _ _ _ _).mpr ⟨rfl, h, rfl, rfl⟩

/-- The threshold mark of a non-maximal occurrence, charged against the
maximal occurrence of its clause. -/
theorem marked_tri {s t : Bool} {c x y : A} (hx : OccIn c x s) (hy : MaxOcc c y t)
    (hne : ¬(x = y ∧ s = t)) : MAGMarked (occPt s c x) (occPt t c y) :=
  (marked_iff_aux _ _ _ _).mpr ⟨hx, hy, rfl, hne⟩

/-- The penalty mark of a clause with at most one occurrence. -/
theorem marked_pen {c : A} (hcl : IsCl c) (hch : ∀ x s, ¬Chained c x s) :
    MAGMarked (penPt c) (penPt c) :=
  (marked_iff_aux _ _ _ _).mpr ⟨rfl, rfl, rfl, hcl, hch⟩

end Characterizations

end MaxCutInterp

end DescriptiveComplexity
