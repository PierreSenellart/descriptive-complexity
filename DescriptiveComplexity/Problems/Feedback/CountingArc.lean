/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Feedback.Counting
import DescriptiveComplexity.Counting.SizedPairs

/-!
# #Feedback Arc Set: counting the feedback arc sets of the threshold size

The counting version of `DescriptiveComplexity.FeedbackArcSet`: the number of sets of
*arcs*, with exactly as many elements as the marked relation, whose removal
leaves an acyclic digraph (`DescriptiveComplexity.FasOfSize`).

A solution is a set of arcs of the graph. The decision problem does not ask for
that – removing a pair that is not an arc removes nothing – but a count has to:
otherwise every solution could be padded with pairs that are not arcs, in as
many ways as there are such pairs.

**The support is not the decision problem**, for the reason it is not for Set
Cover: a feedback arc set smaller than the threshold extends to one of exactly
that size only while arcs remain, so with a threshold above the number of arcs
Feedback Arc Set may hold and the count be `0`. The support is “some feedback
arc set has exactly the threshold size”
(`DescriptiveComplexity.sharpFeedbackArcSet_support_iff`).

Membership in `#P` (`DescriptiveComplexity.sharpFeedbackArcSet_mem_sharpP`) combines the
two unique certificates at hand: the transitive closure for acyclicity
(`DescriptiveComplexity.IsAcyclicClosure`), and the monotone bijection between two
sets of pairs for the size (`DescriptiveComplexity.sharpPDefinable_of_sizedPairs`).
Parsimonious hardness is in
`DescriptiveComplexity.Problems.Feedback.CountingArcHardness`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The relation `F` is a set of arcs whose removal leaves an acyclic digraph,
with exactly as many pairs as the marked relation. -/
def FasOfSizeOn (Adjp Kp : A → A → Prop) (F : A → A → Prop) : Prop :=
  (∀ a b, F a b → Adjp a b) ∧ AcyclicRel (UncutArc Adjp F) ∧
    {p : A × A | F p.1 p.2}.ncard = {p : A × A | Kp p.1 p.2}.ncard

/-- The feedback arc sets of the threshold size transport along an equivalence
commuting with the two relations. -/
def fasOfSizeEquiv (u : B ≃ A) {AdjB KB : B → B → Prop} {AdjA KA : A → A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b'))
    (hK : ∀ b b', KB b b' ↔ KA (u b) (u b')) :
    {F : B → B → Prop // Finite B ∧ FasOfSizeOn AdjB KB F} ≃
      {F : A → A → Prop // Finite A ∧ FasOfSizeOn AdjA KA F} where
  toFun F := ⟨fun a a' => F.1 (u.symm a) (u.symm a'), u.finite_iff.mp F.2.1,
    fun a a' h => by
      have h' := (hadj _ _).mp (F.2.2.1 _ _ h)
      simpa using h',
    AcyclicRel.of_equiv u (fun a a' haa' =>
      ⟨(hadj (u.symm a) (u.symm a')).mpr (by simpa using haa'.1), haa'.2⟩) F.2.2.2.1,
    (ncard_setOf_equiv₂ (RB := F.1) (RA := fun a a' => F.1 (u.symm a) (u.symm a')) u
      (fun b b' => by simp)).symm.trans (F.2.2.2.2.trans (ncard_setOf_equiv₂ u hK))⟩
  invFun T := ⟨fun b b' => T.1 (u b) (u b'), u.finite_iff.mpr T.2.1,
    fun b b' h => (hadj b b').mpr (T.2.2.1 _ _ h),
    AcyclicRel.of_equiv u.symm (RB := UncutArc AdjA T.1) (fun b b' hbb' =>
      ⟨(hadj b b').mp hbb'.1, hbb'.2⟩) T.2.2.2.1,
    ((ncard_setOf_equiv₂ (RB := fun b b' => T.1 (u b) (u b')) (RA := T.1) u
      fun _ _ => Iff.rfl).trans T.2.2.2.2).trans (ncard_setOf_equiv₂ u hK).symm⟩
  left_inv F := Subtype.ext (funext fun b => funext fun b' => by simp)
  right_inv T := Subtype.ext (funext fun a => funext fun a' => by simp)

end Generic

/-! ### The counting problem -/

section Problem

variable (A : Type) [Language.markedArcGraph.Structure A]

/-- The relation `F` is a feedback arc set with exactly as many arcs as the
marked relation has pairs, in a finite arc-marked digraph. -/
def FasOfSize (F : A → A → Prop) : Prop :=
  Finite A ∧ FasOfSizeOn (fun a b : A => MAGAdj a b) (fun a b => MAGMarked a b) F

end Problem

/-- **#Feedback Arc Set**: the number of feedback arc sets with exactly as many
arcs as the marked relation has pairs. -/
noncomputable def SharpFeedbackArcSet : CountingProblem Language.markedArcGraph where
  Count := fun A inst => Nat.card {F : A → A → Prop // @FasOfSize A inst F}
  iso_invariant := fun e => Nat.card_congr
    (fasOfSizeEquiv e.toEquiv (fun a a' => relMap_equiv₂ e magAdj a a')
      fun a a' => relMap_equiv₂ e magMarked a a')

theorem sharpFeedbackArcSet_apply (A : Type) [Language.markedArcGraph.Structure A] :
    SharpFeedbackArcSet A = Nat.card {F : A → A → Prop // FasOfSize A F} :=
  rfl

/-- The support of #Feedback Arc Set: some feedback arc set has exactly the
threshold size. -/
theorem sharpFeedbackArcSet_support_iff (A : Type) [Language.markedArcGraph.Structure A]
    [Finite A] : SharpFeedbackArcSet.support A ↔ ∃ F : A → A → Prop, FasOfSize A F := by
  rw [CountingProblem.support_iff, sharpFeedbackArcSet_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨F⟩, _⟩ => ⟨F.1, F.2⟩, fun ⟨F, hF⟩ => ⟨⟨⟨F, hF⟩⟩, inferInstance⟩⟩

/-- The support of #Feedback Arc Set implies Feedback Arc Set; the converse
fails when the threshold exceeds the number of arcs. -/
theorem feedbackArcSet_of_sharpFeedbackArcSet_support (A : Type)
    [Language.markedArcGraph.Structure A] [Finite A] (h : SharpFeedbackArcSet.support A) :
    FeedbackArcSet A := by
  obtain ⟨F, hfin, -, hac, hcard⟩ := (sharpFeedbackArcSet_support_iff A).mp h
  exact ⟨hfin, F, hac, hcard.le⟩

/-! ### Membership -/

/-- The block of the counting definition of Feedback Arc Set: the removed
arcs, and the transitive closure of the others. -/
fo_block fasCountBlock over Language.markedArcGraph mag into fasCountLang with fa where
  /-- The removed arcs. -/
  cut : 2
  /-- The transitive closure of the arcs that are not removed. -/
  tc : 2

/-- The order-free kernel of #Feedback Arc Set: the removed pairs are arcs, and
the second relation is the transitive closure of the other arcs, irreflexive. -/
noncomputable def fasCountKernel : fasCountLang.Sentence :=
  fo% (∀ x y, faCutSym(x, y) → faAdjSym(x, y)) ∧
    (∀ x y, (faAdjSym(x, y) ∧ ¬ faCutSym(x, y)) → faTcSym(x, y)) ∧
    (∀ x y z, faTcSym(x, y) ∧ faTcSym(y, z) → faTcSym(x, z)) ∧
    (∀ x, ¬ faTcSym(x, x)) ∧
    (∀ x y, faTcSym(x, y) → (faAdjSym(x, y) ∧ ¬ faCutSym(x, y)) ∨
      ∃ z, (faAdjSym(x, z) ∧ ¬ faCutSym(x, z)) ∧ faTcSym(z, y))

section Kernel

variable {A : Type} [Language.markedArcGraph.Structure A]

/-- Realization of the order-free kernel of #Feedback Arc Set. -/
theorem realize_fasCountKernel (ρ : fasCountBlock.Assignment A) :
    (@Sentence.Realize fasCountLang A
        (@sumStructure _ _ A _ (fasCountBlock.structure ρ)) fasCountKernel) ↔
      (∀ a b : A, ρ .cut ![a, b] → MAGAdj a b) ∧
        IsAcyclicClosure (UncutArc (fun a b : A => MAGAdj a b) fun a b => ρ .cut ![a, b])
          fun a b => ρ .tc ![a, b] := by
  let := fasCountBlock.structure ρ
  have hcut : ∀ (w : Fin 2 → A), RelMap (L := fasCountLang) (M := A) faCutSym w ↔ ρ .cut w :=
    fun _ => Iff.rfl
  have htc : ∀ (w : Fin 2 → A), RelMap (L := fasCountLang) (M := A) faTcSym w ↔ ρ .tc w :=
    fun _ => Iff.rfl
  rw [fasCountKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_sup, Formula.realize_iExs, Formula.realize_not, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hcut, htc,
    IsAcyclicClosure, UncutArc]
  refine and_congr ⟨fun h a b hab => h ![a, b] hab, fun h i hi => h (i 0) (i 1) hi⟩
    (and_congr ⟨fun h x y hxy => h ![x, y] hxy, fun h i hi => h (i 0) (i 1) hi⟩
      (and_congr ⟨fun h x y z h₁ h₂ => h ![x, y, z] ⟨h₁, h₂⟩,
          fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩
        (and_congr ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩
          ⟨fun h x y hT => (h ![x, y] hT).imp id fun ⟨z, hz⟩ => ⟨z 0, hz⟩,
            fun h i hi => (h (i 0) (i 1) hi).imp id fun ⟨z, hz⟩ => ⟨fun _ => z, hz⟩⟩)))

/-- The certificate of a set of arcs: the set, and the transitive closure of
the arcs its removal leaves. -/
def fasCertOf (F : A → A → Prop) : fasCountBlock.Assignment A :=
  fun i => match i with
    | .cut => fun w : Fin 2 → A => F (w 0) (w 1)
    | .tc => fun w : Fin 2 → A =>
        Relation.TransGen (UncutArc (fun a b : A => MAGAdj a b) F) (w 0) (w 1)

variable (A) [Finite A]

/-- **The feedback arc sets of the threshold size are the witnesses of the
kernel of that size**, bijectively. -/
noncomputable def fasEquiv :
    {ρ : fasCountBlock.Assignment A //
        (@Sentence.Realize fasCountLang A
          (@sumStructure _ _ A _ (fasCountBlock.structure ρ)) fasCountKernel) ∧
        {p : A × A | ρ .cut (pairArg fasCountBlock .cut rfl p.1 p.2)}.ncard =
          {p : A × A | RelMap magMarked ![p.1, p.2]}.ncard} ≃
      {F : A → A → Prop // FasOfSize A F} where
  toFun ρ := ⟨fun a b => ρ.1 .cut ![a, b], ‹Finite A›,
    ((realize_fasCountKernel ρ.1).mp ρ.2.1).1,
    ((realize_fasCountKernel ρ.1).mp ρ.2.1).2.acyclic, ρ.2.2⟩
  invFun F := ⟨fasCertOf F.1,
    (realize_fasCountKernel _).mpr ⟨F.2.2.1, isAcyclicClosure_transGen F.2.2.2.1⟩,
    F.2.2.2.2⟩
  left_inv := by
    rintro ⟨ρ, hρ, hcard⟩
    have heq := ((realize_fasCountKernel ρ).mp hρ).2.eq_transGen
    refine Subtype.ext (funext fun i => ?_)
    cases i with
    | cut =>
      refine funext fun (w : Fin 2 → A) => ?_
      exact congrArg (ρ .cut) (funext fun k => by fin_cases k <;> rfl)
    | tc =>
      refine funext fun (w : Fin 2 → A) => ?_
      exact (congrFun (congrFun heq (w 0)) (w 1)).symm.trans
        (congrArg (ρ .tc) (funext fun k => by fin_cases k <;> rfl))
  right_inv := fun _ => rfl

end Kernel

/-- **#Feedback Arc Set is in `#P`**: the size is certified by the monotone
bijection between pairs, and acyclicity by the transitive closure. -/
theorem sharpFeedbackArcSet_mem_sharpP : SharpFeedbackArcSet ∈ SharpP :=
  sharpPDefinable_of_sizedPairs SharpFeedbackArcSet fasCountBlock magMarked .cut rfl
    fasCountKernel fun A _ _ => (Nat.card_congr (fasEquiv A)).symm

end DescriptiveComplexity
