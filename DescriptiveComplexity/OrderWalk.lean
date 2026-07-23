/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import DescriptiveComplexity.Padding

/-!
# Walking a finite linear order, first-order

Shared machinery for constructions that traverse a finite linear order – or the
lexicographic order on tuples – one step at a time, with each step described by
a first-order guard over the ordered expansion `L.sum Language.order`.

Two clients, one technique. The SO-Horn definition of HORN-SAT
(`DescriptiveComplexity.Problems.HornSat.Definability`) assembles the unbounded body of
an input clause by walking the order of its elements; the translation of
FO(LFP) into SO-Horn (`DescriptiveComplexity.FixedPointHorn`) walks the lexicographic
order of *stage* and *valuation* tuples to derive the complement of a fixed
point. Both need the same three ingredients, provided here:

* **guards**: formulas `DescriptiveComplexity.minF`, `DescriptiveComplexity.maxF`,
  `DescriptiveComplexity.succF` – being minimal, maximal, the immediate successor – and
  their tuple analogues `DescriptiveComplexity.minTupF`, `DescriptiveComplexity.maxTupF`,
  `DescriptiveComplexity.succTupF` for the lexicographic order, with realization lemmas
  phrased purely in terms of the order of the structure;
* **induction**: `DescriptiveComplexity.order_induction`, walking any finite linear order
  from its minimum along immediate successors – applied not only to the
  universe of a structure but to lexicographic tuple orders over it;
* **the bridge to `Lex`**: the coordinatewise conditions realized by the tuple
  guards characterize bottom, top and covering
  (`DescriptiveComplexity.tupSucc_iff_covBy`…) in `Lex (Fin D → A)`, and
  `DescriptiveComplexity.prodLex_covBy_iff`/`DescriptiveComplexity.finCovBy_iff` do the same for
  the lexicographic product heading a static index; so a walk described by
  guards is a walk along covers of a bona fide finite linear order.

Finally `DescriptiveComplexity.orank` – the rank of an element of a finite linear order,
the number of its strict predecessors – converts that walk into arithmetic:
rank `0` at the bottom (`DescriptiveComplexity.orank_eq_zero`), `+1` along a cover
(`DescriptiveComplexity.orank_covBy`), `Nat.card - 1` at the top
(`DescriptiveComplexity.orank_isTop`). This is how a fixed-point stage indexed by a
tuple is matched with the `ℕ`-indexed stages of
`DescriptiveComplexity.derivesIn`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Order guards -/

section Guards

variable {L : Language.{0, 0}} {α : Type}

/-- `t₁ ≤ t₂`, as a formula over the ordered expansion. -/
noncomputable def leF (t₁ t₂ : (L.sum Language.order).Term α) :
    (L.sum Language.order).Formula α :=
  Relations.formula₂ leSymb t₁ t₂

/-- `t₁ < t₂`, as a formula over the ordered expansion. -/
noncomputable def ltF (t₁ t₂ : (L.sum Language.order).Term α) :
    (L.sum Language.order).Formula α :=
  leF t₁ t₂ ⊓ ∼(leF t₂ t₁)

/-- The variable `x` holds a minimum. -/
noncomputable def minF (x : α) : (L.sum Language.order).Formula α :=
  (leF (Term.var (Sum.inl x)) (Term.var (Sum.inr 0))).iAlls (Fin 1)

/-- The variable `x` holds a maximum. -/
noncomputable def maxF (x : α) : (L.sum Language.order).Formula α :=
  (leF (Term.var (Sum.inr 0)) (Term.var (Sum.inl x))).iAlls (Fin 1)

/-- `w` holds the immediate predecessor of `z`. -/
noncomputable def succF (w z : α) : (L.sum Language.order).Formula α :=
  ltF (Term.var w) (Term.var z) ⊓
    (show (L.sum Language.order).Formula (α ⊕ Fin 1) from
      ∼(ltF (Term.var (Sum.inl w)) (Term.var (Sum.inr 0)) ⊓
        ltF (Term.var (Sum.inr 0)) (Term.var (Sum.inl z)))).iAlls (Fin 1)

variable {A : Type} [L.Structure A] [LinearOrder A] {v : α → A}

@[simp]
theorem realize_leF (t₁ t₂ : (L.sum Language.order).Term α) :
    (leF t₁ t₂).Realize v ↔ t₁.realize v ≤ t₂.realize v := by
  rw [leF, Formula.realize_rel₂, relMap_leSymb]
  exact Iff.rfl

@[simp]
theorem realize_ltF (t₁ t₂ : (L.sum Language.order).Term α) :
    (ltF t₁ t₂).Realize v ↔ t₁.realize v < t₂.realize v := by
  rw [ltF, Formula.realize_inf, Formula.realize_not, realize_leF, realize_leF]
  exact lt_iff_le_not_ge.symm

@[simp]
theorem realize_minF (x : α) : (minF (L := L) x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [minF]
  simp only [Formula.realize_iAlls, realize_leF, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

@[simp]
theorem realize_maxF (x : α) : (maxF (L := L) x).Realize v ↔ ∀ a : A, a ≤ v x := by
  rw [maxF]
  simp only [Formula.realize_iAlls, realize_leF, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

@[simp]
theorem realize_succF (w z : α) :
    (succF (L := L) w z).Realize v ↔ v w < v z ∧ ∀ a : A, ¬(v w < a ∧ a < v z) := by
  rw [succF]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_not, realize_ltF,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

end Guards

/-! ### Immediate predecessors, and induction along a finite linear order -/

section Pred

variable {A : Type} [LinearOrder A] [Finite A]

/-- In a finite linear order, an element that is not a minimum has an
immediate predecessor. -/
theorem exists_succ_of_not_min {z : A} (hz : ¬∀ a : A, z ≤ a) :
    ∃ w : A, w < z ∧ ∀ a : A, ¬(w < a ∧ a < z) := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ.filter fun a : A => a < z).Nonempty := by
    push Not at hz
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨(Finset.univ.filter fun a : A => a < z).max' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp ((Finset.univ.filter fun a : A => a < z).max'_mem hne)).2
  · rintro a ⟨hwa, haz⟩
    exact absurd ((Finset.univ.filter fun a : A => a < z).le_max'
      a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, haz⟩)) (not_le.mpr hwa)

/-- Induction along a finite linear order: from the minimum, one immediate
successor at a time. -/
theorem order_induction {P : A → Prop} (hmin : ∀ z : A, (∀ a : A, z ≤ a) → P z)
    (hstep : ∀ w z : A, w < z → (∀ a : A, ¬(w < a ∧ a < z)) → P w → P z) (z : A) : P z := by
  induction z using (Finite.to_wellFoundedLT (α := A)).wf.induction with
  | _ z ih =>
    by_cases hz : ∀ a : A, z ≤ a
    · exact hmin z hz
    · obtain ⟨w, hwz, hnb⟩ := exists_succ_of_not_min hz
      exact hstep w z hwz hnb (ih w hwz)

end Pred

/-! ### The lexicographic successor of a tuple, coordinatewise -/

section TupSucc

variable {D : ℕ} {A : Type} [LinearOrder A]

/-- The tuple `t'` is the immediate successor of `t` in the lexicographic
order (most significant coordinate first), stated coordinatewise: the two
tuples agree before some position `p`, at `p` the second covers the first, and
after `p` the first is all maxima and the second all minima. This is the
condition the guard `DescriptiveComplexity.succTupF` realizes;
`DescriptiveComplexity.tupSucc_iff_covBy` identifies it with covering in
`Lex (Fin D → A)`. -/
def TupSucc (t t' : Fin D → A) : Prop :=
  ∃ p : Fin D, (∀ j, j < p → t j = t' j) ∧
    (t p < t' p ∧ ∀ a : A, ¬(t p < a ∧ a < t' p)) ∧
    ∀ j, p < j → (∀ a : A, a ≤ t j) ∧ (∀ a : A, t' j ≤ a)

end TupSucc

/-! ### Tuple guards, for the lexicographic order -/

section TupGuards

variable {D : ℕ} {L : Language.{0, 0}} {γ : Type}

/-- The variables `sel` hold a lexicographically minimal tuple: every
coordinate is minimal. -/
noncomputable def minTupF (sel : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun p => minF (sel p))

/-- The variables `sel` hold a lexicographically maximal tuple. -/
noncomputable def maxTupF (sel : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun p => maxF (sel p))

/-- The tuple held by `sel'` is the immediate lexicographic successor of the
one held by `sel`. -/
noncomputable def succTupF (sel sel' : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listSup ((List.finRange D).map fun p =>
    listInf (((List.finRange D).filter fun j => j < p).map fun j =>
      Term.equal (Term.var (sel j)) (Term.var (sel' j))) ⊓
    succF (sel p) (sel' p) ⊓
    listInf (((List.finRange D).filter fun j => p < j).map fun j =>
      maxF (sel j) ⊓ minF (sel' j)))

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_minTupF (sel : Fin D → γ) :
    (minTupF (L := L) sel).Realize v ↔ ∀ (p : Fin D) (a : A), v (sel p) ≤ a := by
  rw [minTupF, realize_listInf]
  constructor
  · intro h p
    have := h _ (List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩)
    rwa [realize_minF] at this
  · rintro h φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    exact (realize_minF _).mpr (h p)

@[simp]
theorem realize_maxTupF (sel : Fin D → γ) :
    (maxTupF (L := L) sel).Realize v ↔ ∀ (p : Fin D) (a : A), a ≤ v (sel p) := by
  rw [maxTupF, realize_listInf]
  constructor
  · intro h p
    have := h _ (List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩)
    rwa [realize_maxF] at this
  · rintro h φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    exact (realize_maxF _).mpr (h p)

theorem realize_succTupF (sel sel' : Fin D → γ) :
    (succTupF (L := L) sel sel').Realize v ↔ TupSucc (v ∘ sel) (v ∘ sel') := by
  rw [succTupF, realize_listSup]
  constructor
  · rintro ⟨φ, hφ, hr⟩
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_inf, Formula.realize_inf, realize_listInf, realize_listInf,
      realize_succF] at hr
    refine ⟨p, fun j hj => ?_, hr.1.2, fun j hj => ?_⟩
    · have := hr.1.1 _ (List.mem_map.mpr
        ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩)
      rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
    · have := hr.2 _ (List.mem_map.mpr
        ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩)
      rw [Formula.realize_inf, realize_maxF, realize_minF] at this
      exact this
  · rintro ⟨p, hbefore, hsucc, hafter⟩
    refine ⟨_, List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩, ?_⟩
    rw [Formula.realize_inf, Formula.realize_inf, realize_listInf, realize_listInf,
      realize_succF]
    refine ⟨⟨fun φ hφ => ?_, hsucc⟩, fun φ hφ => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
      rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
      exact hbefore j (by simpa using (List.mem_filter.mp hj).2)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
      rw [Formula.realize_inf, realize_maxF, realize_minF]
      exact hafter j (by simpa using (List.mem_filter.mp hj).2)

end TupGuards

/-! ### The bridge to `Lex`: bottom, top and covering, coordinatewise

The tuple guards above speak coordinatewise; the walk they describe is along
the finite linear order `Lex (Fin D → A)`. These lemmas identify the two
languages. (`Lex` is a type synonym, so `Finite` and `Nonempty` instances are
provided for it here.) -/

section LexBridge

instance {α : Type*} [Finite α] : Finite (Lex α) := Finite.of_equiv α toLex
instance {α : Type*} [Nonempty α] : Nonempty (Lex α) := Nonempty.map toLex ‹_›

variable {D : ℕ} {A : Type} [LinearOrder A]

theorem lex_lt_iff {t t' : Fin D → A} :
    toLex t < toLex t' ↔ ∃ p, (∀ j, j < p → t j = t' j) ∧ t p < t' p :=
  Iff.rfl

/-- A tuple is a lexicographic bottom iff each coordinate is minimal. -/
theorem tup_isBot_iff {t : Fin D → A} :
    (∀ u : Lex (Fin D → A), toLex t ≤ u) ↔ ∀ (p : Fin D) (a : A), t p ≤ a := by
  classical
  constructor
  · intro h p a
    by_contra hlt
    push Not at hlt
    have := h (toLex (Function.update t p a))
    rcases this.lt_or_eq with hl | he
    · obtain ⟨q, hq, hql⟩ := lex_lt_iff.mp hl
      rcases lt_trichotomy q p with h' | h' | h'
      · rw [Function.update_of_ne (ne_of_lt h')] at hql
        exact absurd hql (lt_irrefl _)
      · rw [h', Function.update_self] at hql
        exact absurd hql (not_lt.mpr hlt.le)
      · have := hq p h'
        rw [Function.update_self] at this
        exact absurd this (ne_of_gt hlt)
    -- the update is strictly below `t`, so equality is impossible too
    · have := congrFun (toLex_inj.mp he) p
      rw [Function.update_self] at this
      exact absurd this (ne_of_gt hlt)
  · intro h u
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, hql⟩ := (lex_lt_iff (t := ofLex u) (t' := t)).mp hlt
    exact absurd hql (not_lt.mpr (h q _))

/-- A tuple is a lexicographic top iff each coordinate is maximal. -/
theorem tup_isTop_iff {t : Fin D → A} :
    (∀ u : Lex (Fin D → A), u ≤ toLex t) ↔ ∀ (p : Fin D) (a : A), a ≤ t p := by
  classical
  constructor
  · intro h p a
    by_contra hlt
    push Not at hlt
    have := h (toLex (Function.update t p a))
    rcases this.lt_or_eq with hl | he
    · obtain ⟨q, hq, hql⟩ := lex_lt_iff.mp hl
      rcases lt_trichotomy q p with h' | h' | h'
      · rw [Function.update_of_ne (ne_of_lt h')] at hql
        exact absurd hql (lt_irrefl _)
      · rw [h', Function.update_self] at hql
        exact absurd hql (not_lt.mpr hlt.le)
      · have := hq p h'
        rw [Function.update_self] at this
        exact absurd this (ne_of_gt hlt)
    · have := congrFun (toLex_inj.mp he) p
      rw [Function.update_self] at this
      exact absurd this (ne_of_gt hlt)
  · intro h u
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, hql⟩ := (lex_lt_iff (t := t) (t' := ofLex u)).mp hlt
    exact absurd hql (not_lt.mpr (h q _))

/-- **Coordinatewise successors are lexicographic covers**: the condition of
the guard `DescriptiveComplexity.succTupF` says exactly that the second tuple covers
the first in `Lex (Fin D → A)`. -/
theorem tupSucc_iff_covBy {t t' : Fin D → A} :
    TupSucc t t' ↔ toLex t ⋖ toLex t' := by
  classical
  constructor
  · rintro ⟨p, hbefore, ⟨hplt, hpnb⟩, hafter⟩
    refine ⟨lex_lt_iff.mpr ⟨p, hbefore, hplt⟩, ?_⟩
    rintro u htu hut
    obtain ⟨i₁, h₁e, h₁l⟩ := (lex_lt_iff (t := t) (t' := ofLex u)).mp htu
    obtain ⟨i₂, h₂e, h₂l⟩ := (lex_lt_iff (t := ofLex u) (t' := t')).mp hut
    rcases lt_trichotomy i₁ p with hip | hip | hip
    · rcases lt_trichotomy i₂ i₁ with hii | hii | hii
      · rw [← h₁e _ hii, ← hbefore _ (hii.trans hip)] at h₂l
        exact absurd h₂l (lt_irrefl _)
      · rw [hii, ← hbefore _ hip] at h₂l
        exact absurd (h₁l.trans h₂l) (lt_irrefl _)
      · rw [h₂e _ hii, ← hbefore _ hip] at h₁l
        exact absurd h₁l (lt_irrefl _)
    · rw [hip] at h₁e h₁l
      rcases lt_trichotomy i₂ p with hii | hii | hii
      · rw [← h₁e _ hii, ← hbefore _ hii] at h₂l
        exact absurd h₂l (lt_irrefl _)
      · rw [hii] at h₂l
        exact hpnb _ ⟨h₁l, h₂l⟩
      · exact absurd h₂l (not_lt.mpr ((hafter _ hii).2 _))
    · exact absurd h₁l (not_lt.mpr ((hafter _ hip).1 _))
  · rintro ⟨hlt, hnb⟩
    obtain ⟨p, hbefore, hpl⟩ := lex_lt_iff.mp hlt
    refine ⟨p, hbefore, ⟨hpl, fun b hb => ?_⟩, fun j hj => ⟨fun a => ?_, fun a => ?_⟩⟩
    · have h1 : toLex t < toLex (Function.update t p b) :=
        lex_lt_iff.mpr ⟨p, fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)],
          by rw [Function.update_self]; exact hb.1⟩
      have h2 : toLex (Function.update t p b) < toLex t' :=
        lex_lt_iff.mpr ⟨p,
          fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)]; exact hbefore j hj,
          by rw [Function.update_self]; exact hb.2⟩
      exact hnb h1 h2
    · by_contra hlt'
      push Not at hlt'
      have h1 : toLex t < toLex (Function.update t j a) :=
        lex_lt_iff.mpr ⟨j, fun i hi => by rw [Function.update_of_ne (ne_of_lt hi)],
          by rw [Function.update_self]; exact hlt'⟩
      have h2 : toLex (Function.update t j a) < toLex t' :=
        lex_lt_iff.mpr ⟨p,
          fun i hi => by
            rw [Function.update_of_ne (ne_of_lt (hi.trans hj))]; exact hbefore i hi,
          by rw [Function.update_of_ne (ne_of_lt hj)]; exact hpl⟩
      exact hnb h1 h2
    · by_contra hlt'
      push Not at hlt'
      have h1 : toLex t < toLex (Function.update t' j a) :=
        lex_lt_iff.mpr ⟨p,
          fun i hi => by
            rw [Function.update_of_ne (ne_of_lt (hi.trans hj))]; exact hbefore i hi,
          by rw [Function.update_of_ne (ne_of_lt hj)]; exact hpl⟩
      have h2 : toLex (Function.update t' j a) < toLex t' :=
        lex_lt_iff.mpr ⟨j, fun i hi => by rw [Function.update_of_ne (ne_of_lt hi)],
          by rw [Function.update_self]; exact hlt'⟩
      exact hnb h1 h2

/-! #### The lexicographic product with a static head -/

variable {J B : Type} [LinearOrder J] [LinearOrder B]

theorem prodLex_le_iff {a a' : J} {b b' : B} :
    toLex (a, b) ≤ toLex (a', b') ↔ a < a' ∨ a = a' ∧ b ≤ b' :=
  Prod.Lex.toLex_le_toLex

theorem prodLex_lt_iff {a a' : J} {b b' : B} :
    toLex (a, b) < toLex (a', b') ↔ a < a' ∨ a = a' ∧ b < b' :=
  Prod.Lex.toLex_lt_toLex

theorem prodLex_isBot_iff {a : J} {b : B} :
    (∀ u : J ×ₗ B, toLex (a, b) ≤ u) ↔ (∀ x : J, a ≤ x) ∧ ∀ y : B, b ≤ y := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun y => ?_⟩
    · rcases prodLex_le_iff.mp (h (toLex (x, b))) with hl | ⟨he, -⟩
      · exact hl.le
      · exact he.le
    · rcases prodLex_le_iff.mp (h (toLex (a, y))) with hl | ⟨-, hy⟩
      · exact absurd hl (lt_irrefl _)
      · exact hy
  · rintro ⟨ha, hb⟩ u
    have : toLex (a, b) ≤ toLex (ofLex u) := by
      rcases eq_or_lt_of_le (ha (ofLex u).1) with he | hl
      · exact prodLex_le_iff.mpr (Or.inr ⟨he, hb _⟩)
      · exact prodLex_le_iff.mpr (Or.inl hl)
    exact this

theorem prodLex_isTop_iff {a : J} {b : B} :
    (∀ u : J ×ₗ B, u ≤ toLex (a, b)) ↔ (∀ x : J, x ≤ a) ∧ ∀ y : B, y ≤ b := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun y => ?_⟩
    · rcases prodLex_le_iff.mp (h (toLex (x, b))) with hl | ⟨he, -⟩
      · exact hl.le
      · exact he.le
    · rcases prodLex_le_iff.mp (h (toLex (a, y))) with hl | ⟨-, hy⟩
      · exact absurd hl (lt_irrefl _)
      · exact hy
  · rintro ⟨ha, hb⟩ u
    have : toLex (ofLex u) ≤ toLex (a, b) := by
      rcases eq_or_lt_of_le (ha (ofLex u).1) with he | hl
      · exact prodLex_le_iff.mpr (Or.inr ⟨he, hb _⟩)
      · exact prodLex_le_iff.mpr (Or.inl hl)
    exact this

/-- Covering in a lexicographic product: either the heads agree and the tails
cover, or the heads cover, the first tail is a top and the second a bottom. -/
theorem prodLex_covBy_iff [Nonempty B] {a a' : J} {b b' : B} :
    toLex (a, b) ⋖ toLex (a', b') ↔
      (a = a' ∧ b ⋖ b') ∨
        (a ⋖ a' ∧ (∀ y : B, y ≤ b) ∧ ∀ y : B, b' ≤ y) := by
  constructor
  · rintro ⟨hlt, hnb⟩
    rcases prodLex_lt_iff.mp hlt with hl | ⟨he, hb⟩
    · refine Or.inr ⟨⟨hl, fun c hac hca' => ?_⟩, fun y => ?_, fun y => ?_⟩
      · obtain ⟨y⟩ := ‹Nonempty B›
        have h1 : toLex (a, b) < toLex (c, y) := prodLex_lt_iff.mpr (Or.inl hac)
        have h2 : toLex (c, y) < toLex (a', b') := prodLex_lt_iff.mpr (Or.inl hca')
        exact hnb h1 h2
      · by_contra hy
        push Not at hy
        have h1 : toLex (a, b) < toLex (a, y) := prodLex_lt_iff.mpr (Or.inr ⟨rfl, hy⟩)
        have h2 : toLex (a, y) < toLex (a', b') := prodLex_lt_iff.mpr (Or.inl hl)
        exact hnb h1 h2
      · by_contra hy
        push Not at hy
        have h1 : toLex (a, b) < toLex (a', y) := prodLex_lt_iff.mpr (Or.inl hl)
        have h2 : toLex (a', y) < toLex (a', b') := prodLex_lt_iff.mpr (Or.inr ⟨rfl, hy⟩)
        exact hnb h1 h2
    · refine Or.inl ⟨he, hb, fun d hbd hdb' => ?_⟩
      have h1 : toLex (a, b) < toLex (a, d) := prodLex_lt_iff.mpr (Or.inr ⟨rfl, hbd⟩)
      have h2 : toLex (a, d) < toLex (a', b') := prodLex_lt_iff.mpr (Or.inr ⟨he, hdb'⟩)
      exact hnb h1 h2
  · rintro (⟨he, hbcov⟩ | ⟨hacov, htop, hbot⟩)
    · obtain ⟨hblt, hbnb⟩ := hbcov
      refine ⟨prodLex_lt_iff.mpr (Or.inr ⟨he, hblt⟩), ?_⟩
      rintro u h₁ h₂
      rcases (prodLex_lt_iff (a := a) (b := b) (a' := (ofLex u).1) (b' := (ofLex u).2)).mp h₁
        with hl₁ | ⟨he₁, hb₁⟩ <;>
        rcases (prodLex_lt_iff (a := (ofLex u).1) (b := (ofLex u).2) (a' := a')
          (b' := b')).mp h₂ with hl₂ | ⟨he₂, hb₂⟩
      · exact absurd (he ▸ hl₁.trans hl₂) (lt_irrefl _)
      · exact absurd (he ▸ he₂ ▸ hl₁) (lt_irrefl _)
      · exact absurd (he ▸ he₁ ▸ hl₂) (lt_irrefl _)
      · exact hbnb hb₁ hb₂
    · obtain ⟨halt, hanb⟩ := hacov
      refine ⟨prodLex_lt_iff.mpr (Or.inl halt), ?_⟩
      rintro u h₁ h₂
      rcases (prodLex_lt_iff (a := a) (b := b) (a' := (ofLex u).1) (b' := (ofLex u).2)).mp h₁
        with hl₁ | ⟨he₁, hb₁⟩
      · rcases (prodLex_lt_iff (a := (ofLex u).1) (b := (ofLex u).2) (a' := a')
          (b' := b')).mp h₂ with hl₂ | ⟨he₂, hb₂⟩
        · exact hanb hl₁ hl₂
        · exact absurd hb₂ (not_lt.mpr (hbot _))
      · exact absurd hb₁ (not_lt.mpr (htop _))

/-- Covering in `Fin n` is incrementing the value. -/
theorem finCovBy_iff {n : ℕ} {j j' : Fin n} : j ⋖ j' ↔ (j : ℕ) + 1 = (j' : ℕ) := by
  constructor
  · rintro ⟨hlt, hnb⟩
    have hv : (j : ℕ) < (j' : ℕ) := hlt
    by_contra hne
    have hlt2 : (j : ℕ) + 1 < (j' : ℕ) := by omega
    have h1 : j < ⟨(j : ℕ) + 1, hlt2.trans j'.isLt⟩ := Fin.lt_def.mpr (Nat.lt_succ_self _)
    have h2 : (⟨(j : ℕ) + 1, hlt2.trans j'.isLt⟩ : Fin n) < j' := Fin.lt_def.mpr hlt2
    exact hnb h1 h2
  · intro h
    refine ⟨Fin.lt_def.mpr (by omega), fun c hjc hcj' => ?_⟩
    rw [Fin.lt_def] at hjc hcj'
    omega

end LexBridge

/-! ### Reaching an element from below a cover -/

section CovByCases

variable {α : Type*} [LinearOrder α]

/-- Whatever is below a cover is below its base, or is the cover itself. -/
theorem covBy_le_cases {a b c : α} (h : a ⋖ b) (hc : c ≤ b) : c ≤ a ∨ c = b := by
  rcases lt_or_eq_of_le hc with hlt | he
  · exact Or.inl ((covBy_iff_lt_iff_le_left.mp h).mp hlt)
  · exact Or.inr he

end CovByCases

/-! ### The rank of an element of a finite linear order -/

section Rank

variable {A : Type} [LinearOrder A]

/-- The rank of an element of a finite linear order: the number of its strict
predecessors. This converts a walk along covers into arithmetic, matching
tuple-indexed fixed-point stages with the `ℕ`-indexed
`DescriptiveComplexity.derivesIn`. -/
noncomputable def orank (z : A) : ℕ :=
  {y : A | y < z}.ncard

/-- A minimum has rank `0`. -/
theorem orank_eq_zero {z : A} (hz : ∀ a : A, z ≤ a) : orank z = 0 := by
  rw [orank]
  have : {y : A | y < z} = ∅ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hz y
  simp [this]

variable [Finite A]

/-- Rank increases by one along a cover. -/
theorem orank_covBy {w z : A} (h : w ⋖ z) : orank z = orank w + 1 := by
  rw [orank, orank]
  have hset : {y : A | y < z} = insert w {y : A | y < w} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    rw [covBy_iff_lt_iff_le_left.mp h]
    exact le_iff_eq_or_lt
  rw [hset, Set.ncard_insert_of_notMem (by simp)]

/-- A maximum has rank `Nat.card A - 1`. -/
theorem orank_isTop {z : A} (hz : ∀ a : A, a ≤ z) : orank z = Nat.card A - 1 := by
  rw [orank]
  have hset : {y : A | y < z} = {z}ᶜ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨ne_of_lt, fun h => lt_of_le_of_ne (hz y) h⟩
  rw [hset, Set.ncard_compl, Set.ncard_singleton]

end Rank

end DescriptiveComplexity
