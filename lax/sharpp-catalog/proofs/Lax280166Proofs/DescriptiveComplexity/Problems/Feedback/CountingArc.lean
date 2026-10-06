/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Feedback.Counting
import Lax280166Proofs.DescriptiveComplexity.Counting.SizedPairs
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

namespace Lax799700.Feedback
end Lax799700.Feedback

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingFeedbackSets (FasOfSize FasOfSizeOn)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Feedback (AcyclicRel MAGAdj MAGMarked UncutArc)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Feedback (magAdj magMarked markedArcGraph)
end FirstOrder.Language

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

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The feedback arc sets of the threshold size transport along an equivalence
commuting with the two relations. -/
def fasOfSizeEquiv (u : B ≃ A) {AdjB KB : B → B → Prop} {AdjA KA : A → A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b'))
    (hK : ∀ b b', KB b b' ↔ KA (u b) (u b')) :
    {F : B → B → Prop // Finite B ∧ Lax280166.CountingFeedbackSets.FasOfSizeOn AdjB KB F} ≃
      {F : A → A → Prop // Finite A ∧ Lax280166.CountingFeedbackSets.FasOfSizeOn AdjA KA F} where
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
    AcyclicRel.of_equiv u.symm (RB := Lax799700.Feedback.UncutArc AdjA T.1) (fun b b' hbb' =>
      ⟨(hadj b b').mp hbb'.1, hbb'.2⟩) T.2.2.2.1,
    ((ncard_setOf_equiv₂ (RB := fun b b' => T.1 (u b) (u b')) (RA := T.1) u
      fun _ _ => Iff.rfl).trans T.2.2.2.2).trans (ncard_setOf_equiv₂ u hK).symm⟩
  left_inv F := Subtype.ext (funext fun b => funext fun b' => by simp)
  right_inv T := Subtype.ext (funext fun a => funext fun a' => by simp)

end Generic

/-! ### The counting problem -/

section Problem

variable (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A]

end Problem

/-- **#Feedback Arc Set**: the number of feedback arc sets with exactly as many
arcs as the marked relation has pairs. -/
noncomputable def SharpFeedbackArcSet : Lax366625.CountingProblems.CountingProblem Lax799700.Feedback.markedArcGraph where
  Count := fun A inst => Nat.card {F : A → A → Prop // @Lax280166.CountingFeedbackSets.FasOfSize A inst F}
  iso_invariant := fun e => Nat.card_congr
    (fasOfSizeEquiv e.toEquiv (fun a a' => relMap_equiv₂ e Lax799700.Feedback.magAdj a a')
      fun a a' => relMap_equiv₂ e Lax799700.Feedback.magMarked a a')

theorem sharpFeedbackArcSet_apply (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] :
    SharpFeedbackArcSet A = Nat.card {F : A → A → Prop // Lax280166.CountingFeedbackSets.FasOfSize A F} :=
  rfl

/-- The support of #Feedback Arc Set: some feedback arc set has exactly the
threshold size. -/
theorem sharpFeedbackArcSet_support_iff (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A]
    [Finite A] : SharpFeedbackArcSet.support A ↔ ∃ F : A → A → Prop, Lax280166.CountingFeedbackSets.FasOfSize A F := by
  rw [CountingProblem.support_iff, sharpFeedbackArcSet_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨F⟩, _⟩ => ⟨F.1, F.2⟩, fun ⟨F, hF⟩ => ⟨⟨⟨F, hF⟩⟩, inferInstance⟩⟩

/-- The support of #Feedback Arc Set implies Feedback Arc Set; the converse
fails when the threshold exceeds the number of arcs. -/
theorem feedbackArcSet_of_sharpFeedbackArcSet_support (A : Type)
    [Lax799700.Feedback.markedArcGraph.Structure A] [Finite A] (h : SharpFeedbackArcSet.support A) :
    FeedbackArcSet A := by
  obtain ⟨F, hfin, -, hac, hcard⟩ := (sharpFeedbackArcSet_support_iff A).mp h
  exact ⟨hfin, F, hac, hcard.le⟩

/-! ### Membership -/

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive FasCountBlockIx where
/-- The removed arcs. -/

  | cut
/-- The transitive closure of the arcs that are not removed. -/

  | tc
  deriving DecidableEq

instance : Fintype _root_.Lax280166Proofs.DescriptiveComplexity.FasCountBlockIx :=
  ⟨List.toFinset [.cut, .tc], by intro x; cases x <;> simp⟩

/-- The block of the counting definition of Feedback Arc Set: the removed
arcs, and the transitive closure of the others. -/
def fasCountBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax280166Proofs.DescriptiveComplexity.FasCountBlockIx
  arity := fun i =>
    match i with
    | .cut => 2
    | .tc => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev fasCountLang : FirstOrder.Language :=
  (Lax799700.Feedback.markedArcGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.fasCountBlock)

/-- The `adj` symbol over the sum. -/
abbrev faAdjSym : (_root_.Lax280166Proofs.DescriptiveComplexity.fasCountLang).Relations 2 :=
  Sum.inl Lax799700.Feedback.magAdj

/-- The `marked` symbol over the sum. -/
abbrev faMarkedSym : (_root_.Lax280166Proofs.DescriptiveComplexity.fasCountLang).Relations 2 :=
  Sum.inl Lax799700.Feedback.magMarked

/-- The `cut` relation variable. -/
def faCutRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.fasCountBlock).Relations 2 :=
  ⟨.cut, rfl⟩

/-- The `cut` symbol over the sum. -/
abbrev faCutSym : (_root_.Lax280166Proofs.DescriptiveComplexity.fasCountLang).Relations 2 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.faCutRel

/-- The `tc` relation variable. -/
def faTcRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.fasCountBlock).Relations 2 :=
  ⟨.tc, rfl⟩

/-- The `tc` symbol over the sum. -/
abbrev faTcSym : (_root_.Lax280166Proofs.DescriptiveComplexity.fasCountLang).Relations 2 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.faTcRel

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The order-free kernel of #Feedback Arc Set: the removed pairs are arcs, and
the second relation is the transitive closure of the other arcs, irreflexive. -/
noncomputable def fasCountKernel : fasCountLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
        ((FirstOrder.Language.Relations.formula₂ faCutSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          (FirstOrder.Language.Relations.formula₂ faAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 1)))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 2)
          ((FirstOrder.Language.Relations.formula₂ faAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                FirstOrder.Language.BoundedFormula.not
                  (FirstOrder.Language.Relations.formula₂ faCutSym (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inr 1)))).imp
            (FirstOrder.Language.Relations.formula₂ faTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1)))) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 3)
            ((FirstOrder.Language.Relations.formula₂ faTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                  FirstOrder.Language.Relations.formula₂ faTcSym (FirstOrder.Language.Term.var (Sum.inr 1))
                    (FirstOrder.Language.Term.var (Sum.inr 2))).imp
              (FirstOrder.Language.Relations.formula₂ faTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 2)))) ⊓
          (FirstOrder.Language.Formula.iAlls (Fin 1)
              (FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₂ faTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 0)))) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 2)
              ((FirstOrder.Language.Relations.formula₂ faTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inr 1))).imp
                (FirstOrder.Language.Relations.formula₂ faAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                      (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                    FirstOrder.Language.BoundedFormula.not
                      (FirstOrder.Language.Relations.formula₂ faCutSym (FirstOrder.Language.Term.var (Sum.inr 0))
                        (FirstOrder.Language.Term.var (Sum.inr 1))) ⊔
                  FirstOrder.Language.Formula.iExs (Fin 1)
                    (FirstOrder.Language.Relations.formula₂ faAdjSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                          (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                        FirstOrder.Language.BoundedFormula.not
                          (FirstOrder.Language.Relations.formula₂ faCutSym
                            (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                            (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
                      FirstOrder.Language.Relations.formula₂ faTcSym (FirstOrder.Language.Term.var (Sum.inr 0))
                        (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 1)))))))))

section Kernel

variable {A : Type} [Lax799700.Feedback.markedArcGraph.Structure A]

/-- Realization of the order-free kernel of #Feedback Arc Set. -/
theorem realize_fasCountKernel (ρ : fasCountBlock.Assignment A) :
    (@Sentence.Realize fasCountLang A
        (@sumStructure _ _ A _ (fasCountBlock.structure ρ)) fasCountKernel) ↔
      (∀ a b : A, ρ .cut ![a, b] → Lax799700.Feedback.MAGAdj a b) ∧
        IsAcyclicClosure (Lax799700.Feedback.UncutArc (fun a b : A => Lax799700.Feedback.MAGAdj a b) fun a b => ρ .cut ![a, b])
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
    IsAcyclicClosure, Lax799700.Feedback.UncutArc]
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
        Relation.TransGen (Lax799700.Feedback.UncutArc (fun a b : A => Lax799700.Feedback.MAGAdj a b) F) (w 0) (w 1)

variable (A) [Finite A]

/-- **The feedback arc sets of the threshold size are the witnesses of the
kernel of that size**, bijectively. -/
noncomputable def fasEquiv :
    {ρ : fasCountBlock.Assignment A //
        (@Sentence.Realize fasCountLang A
          (@sumStructure _ _ A _ (fasCountBlock.structure ρ)) fasCountKernel) ∧
        {p : A × A | ρ .cut (pairArg fasCountBlock .cut rfl p.1 p.2)}.ncard =
          {p : A × A | RelMap Lax799700.Feedback.magMarked ![p.1, p.2]}.ncard} ≃
      {F : A → A → Prop // Lax280166.CountingFeedbackSets.FasOfSize A F} where
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
  sharpPDefinable_of_sizedPairs SharpFeedbackArcSet fasCountBlock Lax799700.Feedback.magMarked .cut rfl
    fasCountKernel fun A _ _ => (Nat.card_congr (fasEquiv A)).symm

end Lax280166Proofs.DescriptiveComplexity


