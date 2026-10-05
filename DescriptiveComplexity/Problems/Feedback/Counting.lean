/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Feedback.Reductions
import DescriptiveComplexity.Problems.CliqueFamily.CountingReductions
import DescriptiveComplexity.Counting.Sized

/-!
# #Feedback Vertex Set

The counting version of `DescriptiveComplexity.FeedbackVertexSet`: the number of sets
of vertices, with exactly as many elements as the marked set, whose removal
leaves an acyclic digraph (`DescriptiveComplexity.FvsOfSize`). Its support is Feedback
Vertex Set (`DescriptiveComplexity.sharpFeedbackVertexSet_support_iff`), and it is
parsimoniously `#P`-complete
(`DescriptiveComplexity.sharpFeedbackVertexSet_sharpP_parsimoniousComplete`).

## The certificate of acyclicity

Acyclicity is not first-order, and the `Σ₁` definition of the decision problem
certifies it by *a* strict partial order containing the surviving arcs
(`DescriptiveComplexity.acyclicRel_iff_exists_order`). There are many – any linear
extension will do – so they cannot be counted. The counting kernel asks for
the least one, the transitive closure, which is first-order *checkable* though
not first-order definable: a transitive irreflexive relation containing the
arcs is their transitive closure as soon as each of its pairs starts with an
arc (`DescriptiveComplexity.IsAcyclicClosure`,
`DescriptiveComplexity.IsAcyclicClosure.eq_transGen`). Irreflexivity is what makes that
last condition bite: without it, a relation relating everything to everything
on a cycle would pass.

## Hardness

The reduction from Vertex Cover of
`DescriptiveComplexity.Problems.Feedback.Reductions` is parsimonious as it stands: it
turns every edge into a 2-cycle, so the feedback vertex sets of the output are
the vertex covers of the input, the same sets
(`DescriptiveComplexity.cover_iff_acyclic_symmetrized`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The transitive closure of an acyclic relation, first-order -/

section Closure

variable {A : Type}

/-- The relation `T` is a transitive, irreflexive relation containing `E`, each
pair of which starts with a pair of `E`: on a finite type, the transitive
closure of `E`, which is then acyclic. -/
def IsAcyclicClosure (E T : A → A → Prop) : Prop :=
  (∀ x y, E x y → T x y) ∧ (∀ x y z, T x y → T y z → T x z) ∧ (∀ x, ¬T x x) ∧
    ∀ x y, T x y → E x y ∨ ∃ z, E x z ∧ T z y

/-- The transitive closure of an acyclic relation is one. -/
theorem isAcyclicClosure_transGen {E : A → A → Prop} (h : AcyclicRel E) :
    IsAcyclicClosure E (Relation.TransGen E) := by
  refine ⟨fun _ _ he => .single he, fun _ _ _ h₁ h₂ => h₁.trans h₂, h, fun x y hxy => ?_⟩
  induction hxy with
  | single he => exact Or.inl he
  | tail _ he ih =>
    rcases ih with h₁ | ⟨z, hxz, hzb⟩
    · exact Or.inr ⟨_, h₁, .single he⟩
    · exact Or.inr ⟨z, hxz, hzb.tail he⟩

/-- A relation with such a closure is acyclic. -/
theorem IsAcyclicClosure.acyclic {E T : A → A → Prop} (h : IsAcyclicClosure E T) :
    AcyclicRel E :=
  (acyclicRel_iff_exists_order E).mpr ⟨T, h.2.1, h.2.2.1, h.1⟩

/-- **The certificate is unique**: it is the transitive closure. -/
theorem IsAcyclicClosure.eq_transGen [Finite A] {E T : A → A → Prop}
    (h : IsAcyclicClosure E T) : T = Relation.TransGen E := by
  funext x y
  apply propext
  constructor
  · intro hT
    induction hn : {w | T x w ∧ T w y}.ncard using Nat.strong_induction_on generalizing x with
    | _ n ih =>
      rcases h.2.2.2 x y hT with he | ⟨z, hxz, hzy⟩
      · exact .single he
      · have hlt : {w | T z w ∧ T w y}.ncard < {w | T x w ∧ T w y}.ncard := by
          refine Set.ncard_lt_ncard ⟨fun w hw => ⟨h.2.1 _ _ _ (h.1 _ _ hxz) hw.1, hw.2⟩,
            fun hsub => ?_⟩
          exact h.2.2.1 z (hsub (show z ∈ {w | T x w ∧ T w y} from ⟨h.1 _ _ hxz, hzy⟩)).1
        exact Relation.TransGen.head hxz (ih _ (hn ▸ hlt) z hzy rfl)
  · intro hxy
    induction hxy with
    | single he => exact h.1 _ _ he
    | tail _ he ih => exact h.2.1 _ _ _ ih (h.1 _ _ he)

end Closure

/-! ### The generic property -/

section Generic

variable {A B : Type}

/-- The removal of the set `C` leaves an acyclic digraph, and `C` has exactly
as many elements as the `Kp`-marked set. -/
def FeedbackOfSizeOn (Adjp : A → A → Prop) (Kp : A → Prop) (C : A → Prop) : Prop :=
  AcyclicRel (SurvivingArc Adjp C) ∧ {x | C x}.ncard = {x | Kp x}.ncard

/-- The feedback vertex sets of the threshold size transport along an
equivalence commuting with the two predicates. -/
def feedbackOfSizeEquiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    {C : B → Prop // Finite B ∧ FeedbackOfSizeOn AdjB KB C} ≃
      {C : A → Prop // Finite A ∧ FeedbackOfSizeOn AdjA KA C} where
  toFun C := ⟨fun a => C.1 (u.symm a), u.finite_iff.mp C.2.1,
    AcyclicRel.of_equiv u (fun a a' haa' =>
      ⟨haa'.1, haa'.2.1, (hadj (u.symm a) (u.symm a')).mpr (by simpa using haa'.2.2)⟩) C.2.2.1,
    (ncard_setOf_symm u C.1).symm.trans (C.2.2.2.trans (ncard_setOf_equiv u hK))⟩
  invFun T := ⟨fun b => T.1 (u b), u.finite_iff.mpr T.2.1,
    AcyclicRel.of_equiv u.symm (RB := SurvivingArc AdjA T.1) (fun b b' hbb' =>
      ⟨hbb'.1, hbb'.2.1, (hadj b b').mp hbb'.2.2⟩) T.2.2.1,
    ((ncard_setOf_equiv u (KB := fun b => T.1 (u b)) (KA := T.1) fun _ => Iff.rfl).trans
      T.2.2.2).trans (ncard_setOf_equiv u hK).symm⟩
  left_inv C := Subtype.ext (funext fun b => by simp)
  right_inv T := Subtype.ext (funext fun a => by simp)

/-- **A set meets every edge iff its removal leaves the symmetrized graph
acyclic**: every edge has become a 2-cycle, and killing the 2-cycles removes
every arc. -/
theorem cover_iff_acyclic_symmetrized (Adjp : A → A → Prop) (C : A → Prop) :
    (∀ x y, x ≠ y → Adjp x y → C x ∨ C y) ↔
      AcyclicRel (SurvivingArc (fun x y => x ≠ y ∧ (Adjp x y ∨ Adjp y x)) C) := by
  constructor
  · intro hcov
    have hempty : ∀ a b, ¬SurvivingArc (fun x y => x ≠ y ∧ (Adjp x y ∨ Adjp y x)) C a b := by
      rintro a b ⟨ha, hb, hne, hab⟩
      rcases hab with hab | hab
      · exact (hcov a b hne hab).elim ha hb
      · exact (hcov b a (Ne.symm hne) hab).elim hb ha
    intro x hx
    cases hx with
    | single h => exact hempty _ _ h
    | tail _ h₂ => exact hempty _ _ h₂
  · intro hac x y hxy hadj
    rcases Classical.em (C x) with hx | hx
    · exact Or.inl hx
    rcases Classical.em (C y) with hy | hy
    · exact Or.inr hy
    exact absurd (Relation.TransGen.tail (.single ⟨hx, hy, hxy, Or.inl hadj⟩)
      ⟨hy, hx, Ne.symm hxy, Or.inr hadj⟩) (hac x)

end Generic

/-! ### The counting problem -/

section Problem

variable (A : Type) [Language.markedGraph.Structure A]

/-- The set `C` is a feedback vertex set with exactly as many vertices as the
marked set, in a finite marked digraph. -/
def FvsOfSize (C : A → Prop) : Prop :=
  Finite A ∧ FeedbackOfSizeOn (fun x y : A => MGAdj x y) (fun x => MGMarked x) C

end Problem

/-- **#Feedback Vertex Set**: the number of feedback vertex sets with exactly
as many vertices as the marked set. -/
noncomputable def SharpFeedbackVertexSet : CountingProblem Language.markedGraph where
  Count := fun A inst => Nat.card {C : A → Prop // @FvsOfSize A inst C}
  iso_invariant := fun e => Nat.card_congr
    (feedbackOfSizeEquiv e.toEquiv (fun a a' => relMap_equiv₂ e mgAdj a a')
      fun a => relMap_equiv₁ e mgMarked a)

theorem sharpFeedbackVertexSet_apply (A : Type) [Language.markedGraph.Structure A] :
    SharpFeedbackVertexSet A = Nat.card {C : A → Prop // FvsOfSize A C} :=
  rfl

/-- **The support of #Feedback Vertex Set is Feedback Vertex Set**: a feedback
vertex set at most as large as the marked set extends to one of exactly that
size. -/
theorem sharpFeedbackVertexSet_support_iff (A : Type) [Language.markedGraph.Structure A]
    [Finite A] : SharpFeedbackVertexSet.support A ↔ FeedbackVertexSet A := by
  rw [CountingProblem.support_iff, sharpFeedbackVertexSet_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨C, hfin, hac, hcard⟩, -⟩
    exact ⟨hfin, C, hac, hcard.le⟩
  · rintro ⟨hfin, C, hac, hcard⟩
    obtain ⟨T, hCT, hT⟩ := exists_superset_ncard_eq hcard
      (Set.ncard_le_card {v : A | MGMarked v})
    have hsub : ∀ a b, SurvivingArc (fun x y : A => MGAdj x y) (fun v => v ∈ T) a b →
        SurvivingArc (fun x y : A => MGAdj x y) C a b := fun a b hab =>
      ⟨fun h => hab.1 (hCT h), fun h => hab.2.1 (hCT h), hab.2.2⟩
    have hmono : ∀ a b,
        Relation.TransGen (SurvivingArc (fun x y : A => MGAdj x y) fun v => v ∈ T) a b →
        Relation.TransGen (SurvivingArc (fun x y : A => MGAdj x y) C) a b := by
      intro a b hab
      induction hab with
      | single h => exact .single (hsub _ _ h)
      | tail _ h₂ ih => exact ih.tail (hsub _ _ h₂)
    exact ⟨⟨⟨fun v => v ∈ T, hfin, fun x hx => hac x (hmono x x hx), hT⟩⟩, inferInstance⟩

/-! ### Membership -/

/-- The block of the counting definition of Feedback Vertex Set: the removed
set, and the transitive closure of the surviving arcs. -/
fo_block fvsCountBlock over Language.markedGraph mg into fvsCountLang with fc where
  /-- The removed set. -/
  sel : 1
  /-- The transitive closure of the surviving arcs. -/
  tc : 2

/-- The order-free kernel of #Feedback Vertex Set: the guessed binary relation
is the transitive closure of the surviving arcs, and it is irreflexive. -/
noncomputable def fvsCountKernel : fvsCountLang.Sentence :=
  fo% (∀ x y, (¬ fcSelSym(x) ∧ ¬ fcSelSym(y) ∧ fcAdjSym(x, y)) → fcTcSym(x, y)) ∧
    (∀ x y z, fcTcSym(x, y) ∧ fcTcSym(y, z) → fcTcSym(x, z)) ∧
    (∀ x, ¬ fcTcSym(x, x)) ∧
    (∀ x y, fcTcSym(x, y) → (¬ fcSelSym(x) ∧ ¬ fcSelSym(y) ∧ fcAdjSym(x, y)) ∨
      ∃ z, (¬ fcSelSym(x) ∧ ¬ fcSelSym(z) ∧ fcAdjSym(x, z)) ∧ fcTcSym(z, y))

section Kernel

variable {A : Type} [Language.markedGraph.Structure A]

/-- Realization of the order-free kernel of #Feedback Vertex Set. -/
theorem realize_fvsCountKernel (ρ : fvsCountBlock.Assignment A) :
    (@Sentence.Realize fvsCountLang A
        (@sumStructure _ _ A _ (fvsCountBlock.structure ρ)) fvsCountKernel) ↔
      IsAcyclicClosure (SurvivingArc (fun x y : A => MGAdj x y) fun a => ρ .sel fun _ => a)
        fun a b => ρ .tc ![a, b] := by
  let := fvsCountBlock.structure ρ
  have hsel : ∀ (w : Fin 1 → A),
      RelMap (L := fvsCountLang) (M := A) fcSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  have htc : ∀ (w : Fin 2 → A), RelMap (L := fvsCountLang) (M := A) fcTcSym w ↔ ρ .tc w :=
    fun _ => Iff.rfl
  rw [fvsCountKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_sup, Formula.realize_iExs, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl,
    hsel, htc, Matrix.cons_val_zero, IsAcyclicClosure, SurvivingArc]
  refine and_congr ⟨fun h x y hxy => h ![x, y] hxy, fun h i hi => h (i 0) (i 1) hi⟩
    (and_congr ⟨fun h x y z h₁ h₂ => h ![x, y, z] ⟨h₁, h₂⟩,
        fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩
      (and_congr ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩
        ⟨fun h x y hT => (h ![x, y] hT).imp id fun ⟨z, hz⟩ => ⟨z 0, hz⟩,
          fun h i hi => (h (i 0) (i 1) hi).imp id fun ⟨z, hz⟩ => ⟨fun _ => z, hz⟩⟩))

/-- The certificate of a set: the set, and the transitive closure of the arcs
its removal leaves. -/
def fvsCertOf (C : A → Prop) : fvsCountBlock.Assignment A :=
  fun i => match i with
    | .sel => fun w : Fin 1 → A => C (w 0)
    | .tc => fun w : Fin 2 → A =>
        Relation.TransGen (SurvivingArc (fun x y : A => MGAdj x y) C) (w 0) (w 1)

variable (A) [Finite A]

/-- **The feedback vertex sets of the threshold size are the witnesses of the
kernel of that size**, bijectively: the transitive closure is the one
certificate. -/
noncomputable def fvsEquiv :
    {ρ : fvsCountBlock.Assignment A //
        (@Sentence.Realize fvsCountLang A
          (@sumStructure _ _ A _ (fvsCountBlock.structure ρ)) fvsCountKernel) ∧
        {a | ρ .sel fun _ => a}.ncard = {a : A | RelMap mgMarked ![a]}.ncard} ≃
      {C : A → Prop // FvsOfSize A C} where
  toFun ρ := ⟨fun a => ρ.1 .sel fun _ => a, ‹Finite A›,
    ((realize_fvsCountKernel ρ.1).mp ρ.2.1).acyclic, ρ.2.2⟩
  invFun C := ⟨fvsCertOf C.1,
    (realize_fvsCountKernel _).mpr (isAcyclicClosure_transGen C.2.2.1), C.2.2.2⟩
  left_inv := by
    rintro ⟨ρ, hρ, hcard⟩
    have heq := ((realize_fvsCountKernel ρ).mp hρ).eq_transGen
    refine Subtype.ext (funext fun i => ?_)
    cases i with
    | sel =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .sel) (funext fun (j : Fin 1) => congrArg w (Subsingleton.elim 0 j))
    | tc =>
      refine funext fun (w : Fin 2 → A) => ?_
      exact (congrFun (congrFun heq (w 0)) (w 1)).symm.trans
        (congrArg (ρ .tc) (funext fun k => by fin_cases k <;> rfl))
  right_inv := fun _ => rfl

end Kernel

/-- **#Feedback Vertex Set is in `#P`**: the size is certified by the monotone
bijection with the marked set, and acyclicity by the transitive closure. -/
theorem sharpFeedbackVertexSet_mem_sharpP : SharpFeedbackVertexSet ∈ SharpP :=
  sharpPDefinable_of_sized SharpFeedbackVertexSet fvsCountBlock mgMarked .sel rfl
    fvsCountKernel fun A _ _ => (Nat.card_congr (fvsEquiv A)).symm

/-! ### Hardness -/

section Hardness

variable (A : Type) [Language.markedGraph.Structure A]

private theorem symmetrize_adj_iff :
    ∀ b b' : symmetrizeInterp.Map A,
      MGAdj b b' ↔ (symmetrizeInterp.mapEquivSelf A b ≠ symmetrizeInterp.mapEquivSelf A b' ∧
        (MGAdj (symmetrizeInterp.mapEquivSelf A b) (symmetrizeInterp.mapEquivSelf A b') ∨
          MGAdj (symmetrizeInterp.mapEquivSelf A b') (symmetrizeInterp.mapEquivSelf A b))) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact symmetrize_adj w w'

private theorem symmetrize_marked_iff :
    ∀ b : symmetrizeInterp.Map A,
      MGMarked b ↔ MGMarked (symmetrizeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact symmetrize_marked w

/-- The feedback vertex sets of the symmetrized graph are the vertex covers. -/
theorem sharpFeedbackVertexSet_symmetrize_map :
    SharpFeedbackVertexSet (symmetrizeInterp.Map A) = SharpVertexCover A :=
  (Nat.card_congr (feedbackOfSizeEquiv (symmetrizeInterp.mapEquivSelf A)
    (AdjA := fun x y : A => x ≠ y ∧ (MGAdj x y ∨ MGAdj y x)) (symmetrize_adj_iff A)
    (symmetrize_marked_iff A))).trans
    (Nat.card_congr (Equiv.subtypeEquivRight fun C =>
      and_congr Iff.rfl (and_congr (cover_iff_acyclic_symmetrized _ C).symm Iff.rfl)))

end Hardness

/-- **#Vertex Cover reduces parsimoniously to #Feedback Vertex Set**, by
symmetrizing the adjacency relation. -/
noncomputable def sharpVertexCover_parsimonious_sharpFeedbackVertexSet :
    SharpVertexCover ≤ᵖ SharpFeedbackVertexSet where
  Tag := Unit
  dim := 1
  toInterpretation := symmetrizeInterp
  correct A _ _ _ := (sharpFeedbackVertexSet_symmetrize_map A).symm

/-- #Feedback Vertex Set is parsimoniously `#P`-hard. -/
theorem sharpFeedbackVertexSet_sharpP_parsimoniousHard :
    SharpP.ParsimoniousHard SharpFeedbackVertexSet :=
  SharpP.parsimoniousHard_of_parsimonious sharpVertexCover_parsimonious_sharpFeedbackVertexSet
    sharpVertexCover_sharpP_parsimoniousHard

/-- **#Feedback Vertex Set is parsimoniously `#P`-complete**, counting the
feedback vertex sets of exactly the threshold size. -/
theorem sharpFeedbackVertexSet_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpFeedbackVertexSet :=
  ⟨sharpFeedbackVertexSet_mem_sharpP, sharpFeedbackVertexSet_sharpP_parsimoniousHard⟩

end DescriptiveComplexity
