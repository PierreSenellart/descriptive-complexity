/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Problems.Feedback.Reductions
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingReductions
import Lax280166Proofs.DescriptiveComplexity.Counting.Sized
import Lax280166Proofs.DescriptiveComplexity.Counting.Subtractive
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax280166.CountingFeedbackSets
end Lax280166.CountingFeedbackSets

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.Feedback
end Lax799700.Feedback

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingFeedbackSets (FeedbackOfSizeOn FvsOfSize)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Feedback (AcyclicRel SurvivingArc)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

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

namespace Lax280166Proofs.DescriptiveComplexity

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
theorem isAcyclicClosure_transGen {E : A → A → Prop} (h : Lax799700.Feedback.AcyclicRel E) :
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
    Lax799700.Feedback.AcyclicRel E :=
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

/-- The feedback vertex sets of the threshold size transport along an
equivalence commuting with the two predicates. -/
def feedbackOfSizeEquiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    {C : B → Prop // Finite B ∧ Lax280166.CountingFeedbackSets.FeedbackOfSizeOn AdjB KB C} ≃
      {C : A → Prop // Finite A ∧ Lax280166.CountingFeedbackSets.FeedbackOfSizeOn AdjA KA C} where
  toFun C := ⟨fun a => C.1 (u.symm a), u.finite_iff.mp C.2.1,
    AcyclicRel.of_equiv u (fun a a' haa' =>
      ⟨haa'.1, haa'.2.1, (hadj (u.symm a) (u.symm a')).mpr (by simpa using haa'.2.2)⟩) C.2.2.1,
    (ncard_setOf_symm u C.1).symm.trans (C.2.2.2.trans (ncard_setOf_equiv u hK))⟩
  invFun T := ⟨fun b => T.1 (u b), u.finite_iff.mpr T.2.1,
    AcyclicRel.of_equiv u.symm (RB := Lax799700.Feedback.SurvivingArc AdjA T.1) (fun b b' hbb' =>
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
      Lax799700.Feedback.AcyclicRel (Lax799700.Feedback.SurvivingArc (fun x y => x ≠ y ∧ (Adjp x y ∨ Adjp y x)) C) := by
  constructor
  · intro hcov
    have hempty : ∀ a b, ¬Lax799700.Feedback.SurvivingArc (fun x y => x ≠ y ∧ (Adjp x y ∨ Adjp y x)) C a b := by
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

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

end Problem

/-- **#Feedback Vertex Set**: the number of feedback vertex sets with exactly
as many vertices as the marked set. -/
noncomputable def SharpFeedbackVertexSet : Lax366625.CountingProblems.CountingProblem Lax799700.CliqueFamily.markedGraph where
  Count := fun A inst => Nat.card {C : A → Prop // @Lax280166.CountingFeedbackSets.FvsOfSize A inst C}
  iso_invariant := fun e => Nat.card_congr
    (feedbackOfSizeEquiv e.toEquiv (fun a a' => relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj a a')
      fun a => relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a)

theorem sharpFeedbackVertexSet_apply (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpFeedbackVertexSet A = Nat.card {C : A → Prop // Lax280166.CountingFeedbackSets.FvsOfSize A C} :=
  rfl

/-- **The support of #Feedback Vertex Set is Feedback Vertex Set**: a feedback
vertex set at most as large as the marked set extends to one of exactly that
size. -/
theorem sharpFeedbackVertexSet_support_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]
    [Finite A] : SharpFeedbackVertexSet.support A ↔ FeedbackVertexSet A := by
  rw [CountingProblem.support_iff, sharpFeedbackVertexSet_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨C, hfin, hac, hcard⟩, -⟩
    exact ⟨hfin, C, hac, hcard.le⟩
  · rintro ⟨hfin, C, hac, hcard⟩
    obtain ⟨T, hCT, hT⟩ := exists_superset_ncard_eq hcard
      (Set.ncard_le_card {v : A | Lax799700.CliqueFamily.MGMarked v})
    have hsub : ∀ a b, Lax799700.Feedback.SurvivingArc (fun x y : A => Lax799700.CliqueFamily.MGAdj x y) (fun v => v ∈ T) a b →
        Lax799700.Feedback.SurvivingArc (fun x y : A => Lax799700.CliqueFamily.MGAdj x y) C a b := fun a b hab =>
      ⟨fun h => hab.1 (hCT h), fun h => hab.2.1 (hCT h), hab.2.2⟩
    have hmono : ∀ a b,
        Relation.TransGen (Lax799700.Feedback.SurvivingArc (fun x y : A => Lax799700.CliqueFamily.MGAdj x y) fun v => v ∈ T) a b →
        Relation.TransGen (Lax799700.Feedback.SurvivingArc (fun x y : A => Lax799700.CliqueFamily.MGAdj x y) C) a b := by
      intro a b hab
      induction hab with
      | single h => exact .single (hsub _ _ h)
      | tail _ h₂ ih => exact ih.tail (hsub _ _ h₂)
    exact ⟨⟨⟨fun v => v ∈ T, hfin, fun x hx => hac x (hmono x x hx), hT⟩⟩, inferInstance⟩

/-! ### Membership -/

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive FvsCountBlockIx where
/-- The removed set. -/

  | sel
/-- The transitive closure of the surviving arcs. -/

  | tc
  deriving DecidableEq

instance : Fintype _root_.Lax280166Proofs.DescriptiveComplexity.FvsCountBlockIx :=
  ⟨List.toFinset [.sel, .tc], by intro x; cases x <;> simp⟩

/-- The block of the counting definition of Feedback Vertex Set: the removed
set, and the transitive closure of the surviving arcs. -/
def fvsCountBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax280166Proofs.DescriptiveComplexity.FvsCountBlockIx
  arity := fun i =>
    match i with
    | .sel => 1
    | .tc => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev fvsCountLang : FirstOrder.Language :=
  (Lax799700.CliqueFamily.markedGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.fvsCountBlock)

/-- The `adj` symbol over the sum. -/
abbrev fcAdjSym : (_root_.Lax280166Proofs.DescriptiveComplexity.fvsCountLang).Relations 2 :=
  Sum.inl Lax799700.CliqueFamily.mgAdj

/-- The `marked` symbol over the sum. -/
abbrev fcMarkedSym : (_root_.Lax280166Proofs.DescriptiveComplexity.fvsCountLang).Relations 1 :=
  Sum.inl Lax799700.CliqueFamily.mgMarked

/-- The `sel` relation variable. -/
def fcSelRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.fvsCountBlock).Relations 1 :=
  ⟨.sel, rfl⟩

/-- The `sel` symbol over the sum. -/
abbrev fcSelSym : (_root_.Lax280166Proofs.DescriptiveComplexity.fvsCountLang).Relations 1 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.fcSelRel

/-- The `tc` relation variable. -/
def fcTcRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.fvsCountBlock).Relations 2 :=
  ⟨.tc, rfl⟩

/-- The `tc` symbol over the sum. -/
abbrev fcTcSym : (_root_.Lax280166Proofs.DescriptiveComplexity.fvsCountLang).Relations 2 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.fcTcRel

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The order-free kernel of #Feedback Vertex Set: the guessed binary relation
is the transitive closure of the surviving arcs, and it is irreflexive. -/
noncomputable def fvsCountKernel : fvsCountLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
        ((FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₁ fcSelSym (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
              (FirstOrder.Language.BoundedFormula.not
                  (FirstOrder.Language.Relations.formula₁ fcSelSym (FirstOrder.Language.Term.var (Sum.inr 1))) ⊓
                FirstOrder.Language.Relations.formula₂ fcAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1)))).imp
          (FirstOrder.Language.Relations.formula₂ fcTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 1)))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 3)
          ((FirstOrder.Language.Relations.formula₂ fcTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                FirstOrder.Language.Relations.formula₂ fcTcSym (FirstOrder.Language.Term.var (Sum.inr 1))
                  (FirstOrder.Language.Term.var (Sum.inr 2))).imp
            (FirstOrder.Language.Relations.formula₂ fcTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 2)))) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 1)
            (FirstOrder.Language.BoundedFormula.not
              (FirstOrder.Language.Relations.formula₂ fcTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 0)))) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 2)
            ((FirstOrder.Language.Relations.formula₂ fcTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1))).imp
              (FirstOrder.Language.BoundedFormula.not
                    (FirstOrder.Language.Relations.formula₁ fcSelSym (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
                  (FirstOrder.Language.BoundedFormula.not
                      (FirstOrder.Language.Relations.formula₁ fcSelSym (FirstOrder.Language.Term.var (Sum.inr 1))) ⊓
                    FirstOrder.Language.Relations.formula₂ fcAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                      (FirstOrder.Language.Term.var (Sum.inr 1))) ⊔
                FirstOrder.Language.Formula.iExs (Fin 1)
                  (FirstOrder.Language.BoundedFormula.not
                        (FirstOrder.Language.Relations.formula₁ fcSelSym
                          (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))) ⊓
                      (FirstOrder.Language.BoundedFormula.not
                          (FirstOrder.Language.Relations.formula₁ fcSelSym (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
                        FirstOrder.Language.Relations.formula₂ fcAdjSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                          (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
                    FirstOrder.Language.Relations.formula₂ fcTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                      (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 1))))))))

section Kernel

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

/-- Realization of the order-free kernel of #Feedback Vertex Set. -/
theorem realize_fvsCountKernel (ρ : fvsCountBlock.Assignment A) :
    (@Sentence.Realize fvsCountLang A
        (@sumStructure _ _ A _ (fvsCountBlock.structure ρ)) fvsCountKernel) ↔
      IsAcyclicClosure (Lax799700.Feedback.SurvivingArc (fun x y : A => Lax799700.CliqueFamily.MGAdj x y) fun a => ρ .sel fun _ => a)
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
    hsel, htc, Matrix.cons_val_zero, IsAcyclicClosure, Lax799700.Feedback.SurvivingArc]
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
        Relation.TransGen (Lax799700.Feedback.SurvivingArc (fun x y : A => Lax799700.CliqueFamily.MGAdj x y) C) (w 0) (w 1)

variable (A) [Finite A]

/-- **The feedback vertex sets of the threshold size are the witnesses of the
kernel of that size**, bijectively: the transitive closure is the one
certificate. -/
noncomputable def fvsEquiv :
    {ρ : fvsCountBlock.Assignment A //
        (@Sentence.Realize fvsCountLang A
          (@sumStructure _ _ A _ (fvsCountBlock.structure ρ)) fvsCountKernel) ∧
        {a | ρ .sel fun _ => a}.ncard = {a : A | RelMap Lax799700.CliqueFamily.mgMarked ![a]}.ncard} ≃
      {C : A → Prop // Lax280166.CountingFeedbackSets.FvsOfSize A C} where
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
  sharpPDefinable_of_sized SharpFeedbackVertexSet fvsCountBlock Lax799700.CliqueFamily.mgMarked .sel rfl
    fvsCountKernel fun A _ _ => (Nat.card_congr (fvsEquiv A)).symm

/-! ### Hardness -/

section Hardness

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

private theorem symmetrize_adj_iff :
    ∀ b b' : symmetrizeInterp.Map A,
      Lax799700.CliqueFamily.MGAdj b b' ↔ (symmetrizeInterp.mapEquivSelf A b ≠ symmetrizeInterp.mapEquivSelf A b' ∧
        (Lax799700.CliqueFamily.MGAdj (symmetrizeInterp.mapEquivSelf A b) (symmetrizeInterp.mapEquivSelf A b') ∨
          Lax799700.CliqueFamily.MGAdj (symmetrizeInterp.mapEquivSelf A b') (symmetrizeInterp.mapEquivSelf A b))) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact symmetrize_adj w w'

private theorem symmetrize_marked_iff :
    ∀ b : symmetrizeInterp.Map A,
      Lax799700.CliqueFamily.MGMarked b ↔ Lax799700.CliqueFamily.MGMarked (symmetrizeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact symmetrize_marked w

/-- The feedback vertex sets of the symmetrized graph are the vertex covers. -/
theorem sharpFeedbackVertexSet_symmetrize_map :
    SharpFeedbackVertexSet (symmetrizeInterp.Map A) = SharpVertexCover A :=
  (Nat.card_congr (feedbackOfSizeEquiv (symmetrizeInterp.mapEquivSelf A)
    (AdjA := fun x y : A => x ≠ y ∧ (Lax799700.CliqueFamily.MGAdj x y ∨ Lax799700.CliqueFamily.MGAdj y x)) (symmetrize_adj_iff A)
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

end Lax280166Proofs.DescriptiveComplexity


