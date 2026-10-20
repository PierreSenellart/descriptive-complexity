/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.CountingPacking
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.Reductions
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

namespace Lax280166.CountingCliques
end Lax280166.CountingCliques

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingCliques (CoverOfSize)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (CoverFamOfSizeOn HittingSetOfSize SetCoverOfSize)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.SetFamily (SSElem SSFam SSMarked SSMem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem ssElem ssFam ssMarked ssMem)
end FirstOrder.Language

/-!
# #Set Cover and #Hitting Set

The counting versions of `DescriptiveComplexity.SetCover` and
`DescriptiveComplexity.HittingSet`, each counting the solutions of *exactly* the
threshold size:

* `DescriptiveComplexity.SharpSetCover`: the covering subfamilies with as many sets
  as the marked set;
* `DescriptiveComplexity.SharpHittingSet`: the hitting sets with as many elements as
  the marked set.

Both are parsimoniously `#P`-complete
(`DescriptiveComplexity.sharpSetCover_sharpP_parsimoniousComplete`,
`DescriptiveComplexity.sharpHittingSet_sharpP_parsimoniousComplete`). Membership of
#Set Cover is the generic argument for a solution of the threshold size
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`); its hardness is the
edge-incidence interpretation unchanged, from #Vertex Cover, the sets of the
interpreted system being the vertices, one each
(`DescriptiveComplexity.coverEquiv`). #Hitting Set is #Set Cover transposed, in both
directions.

**The support is not the decision problem.** A cover smaller than the threshold
extends to one of exactly that size only while unused sets remain: with a
threshold above the size of the family, Set Cover may hold and the count be
`0`. The support of these counts is “some cover has exactly the threshold
size” (`DescriptiveComplexity.sharpSetCover_support_iff`), which implies Set Cover
(`DescriptiveComplexity.setCover_of_sharpSetCover_support`) and is not implied by it.
This is unlike #Vertex Cover, where the family is the whole universe.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic property -/

section Generic

variable {A B : Type}

/-- The covers of the threshold size transport along an equivalence commuting
with the four predicates. -/
def coverFamOfSizeEquiv (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop} (hE : ∀ b, EB b ↔ EA (u b))
    (hF : ∀ b, FB b ↔ FA (u b)) (hM : ∀ b b', MB b b' ↔ MA (u b) (u b'))
    (hK : ∀ b, KB b ↔ KA (u b)) :
    {G : B → Prop // Finite B ∧ Lax280166.CountingSetFamilies.CoverFamOfSizeOn EB FB MB KB G} ≃
      {G : A → Prop // Finite A ∧ Lax280166.CountingSetFamilies.CoverFamOfSizeOn EA FA MA KA G} where
  toFun G := ⟨fun a => G.1 (u.symm a), u.finite_iff.mp G.2.1, fun s hs => by
      have h := (hF (u.symm s)).mp (G.2.2.1 _ hs)
      simpa using h, fun x hx => by
      obtain ⟨s, hs, hm⟩ := G.2.2.2.1 (u.symm x) ((hE _).mpr (by simpa using hx))
      have h := (hM _ _).mp hm
      exact ⟨u s, by simpa using hs, by simpa using h⟩,
    (ncard_setOf_symm u G.1).symm.trans (G.2.2.2.2.trans (ncard_setOf_equiv u hK))⟩
  invFun T := ⟨fun b => T.1 (u b), u.finite_iff.mpr T.2.1,
    fun s hs => (hF s).mpr (T.2.2.1 _ hs), fun x hx => by
      obtain ⟨s, hs, hm⟩ := T.2.2.2.1 (u x) ((hE x).mp hx)
      exact ⟨u.symm s, by simpa using hs, (hM _ _).mpr (by simpa using hm)⟩,
    ((ncard_setOf_equiv u (KB := fun b => T.1 (u b)) (KA := T.1) fun _ => Iff.rfl).trans
      T.2.2.2.2).trans (ncard_setOf_equiv u hK).symm⟩
  left_inv G := Subtype.ext (funext fun b => by simp)
  right_inv T := Subtype.ext (funext fun a => by simp)

end Generic

/-! ### The two counting problems -/

section Problems

variable (A : Type) [Lax799700.SetFamily.setSystem.Structure A]

end Problems

/-- **#Set Cover**: the number of covering subfamilies with exactly as many
sets as the marked set. -/
noncomputable def SharpSetCover : Lax366625.CountingProblems.CountingProblem Lax799700.SetFamily.setSystem where
  Count := fun A inst => Nat.card {G : A → Prop // @Lax280166.CountingSetFamilies.SetCoverOfSize A inst G}
  iso_invariant := fun e => Nat.card_congr
    (coverFamOfSizeEquiv e.toEquiv (fun a => relMap_equiv₁ e Lax799700.SetFamily.ssElem a)
      (fun a => relMap_equiv₁ e Lax799700.SetFamily.ssFam a) (fun a a' => relMap_equiv₂ e Lax799700.SetFamily.ssMem a a')
      fun a => relMap_equiv₁ e Lax799700.SetFamily.ssMarked a)

/-- **#Hitting Set**: the number of hitting sets with exactly as many elements
as the marked set. -/
noncomputable def SharpHittingSet : Lax366625.CountingProblems.CountingProblem Lax799700.SetFamily.setSystem where
  Count := fun A inst => Nat.card {H : A → Prop // @Lax280166.CountingSetFamilies.HittingSetOfSize A inst H}
  iso_invariant := fun e => Nat.card_congr
    (coverFamOfSizeEquiv e.toEquiv (fun a => relMap_equiv₁ e Lax799700.SetFamily.ssFam a)
      (fun a => relMap_equiv₁ e Lax799700.SetFamily.ssElem a) (fun a a' => relMap_equiv₂ e Lax799700.SetFamily.ssMem a' a)
      fun a => relMap_equiv₁ e Lax799700.SetFamily.ssMarked a)

section Apply

variable (A : Type) [Lax799700.SetFamily.setSystem.Structure A]

theorem sharpSetCover_apply :
    SharpSetCover A = Nat.card {G : A → Prop // Lax280166.CountingSetFamilies.SetCoverOfSize A G} :=
  rfl

theorem sharpHittingSet_apply :
    SharpHittingSet A = Nat.card {H : A → Prop // Lax280166.CountingSetFamilies.HittingSetOfSize A H} :=
  rfl

/-- The support of #Set Cover: some cover has exactly the threshold size. -/
theorem sharpSetCover_support_iff [Finite A] :
    SharpSetCover.support A ↔ ∃ G : A → Prop, Lax280166.CountingSetFamilies.SetCoverOfSize A G := by
  rw [CountingProblem.support_iff, sharpSetCover_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨G⟩, _⟩ => ⟨G.1, G.2⟩, fun ⟨G, hG⟩ => ⟨⟨⟨G, hG⟩⟩, inferInstance⟩⟩

/-- The support of #Hitting Set: some hitting set has exactly the threshold
size. -/
theorem sharpHittingSet_support_iff [Finite A] :
    SharpHittingSet.support A ↔ ∃ H : A → Prop, Lax280166.CountingSetFamilies.HittingSetOfSize A H := by
  rw [CountingProblem.support_iff, sharpHittingSet_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨H⟩, _⟩ => ⟨H.1, H.2⟩, fun ⟨H, hH⟩ => ⟨⟨⟨H, hH⟩⟩, inferInstance⟩⟩

/-- The support of #Set Cover implies Set Cover; the converse fails when the
threshold exceeds the size of the family. -/
theorem setCover_of_sharpSetCover_support [Finite A] (h : SharpSetCover.support A) :
    SetCover A := by
  obtain ⟨G, hfin, hfam, hcov, hcard⟩ := (sharpSetCover_support_iff A).mp h
  exact ⟨hfin, G, hfam, hcov, hcard.le⟩

/-- The support of #Hitting Set implies Hitting Set. -/
theorem hittingSet_of_sharpHittingSet_support [Finite A] (h : SharpHittingSet.support A) :
    HittingSet A := by
  obtain ⟨H, hfin, helem, hhit, hcard⟩ := (sharpHittingSet_support_iff A).mp h
  exact ⟨hfin, H, helem, hhit, hcard.le⟩

/-! ### Transposition, for counting -/

private theorem transpose_elem_iff :
    ∀ b : transposeInterp.Map A,
      Lax799700.SetFamily.SSElem b ↔ Lax799700.SetFamily.SSFam (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_elem w

private theorem transpose_fam_iff :
    ∀ b : transposeInterp.Map A,
      Lax799700.SetFamily.SSFam b ↔ Lax799700.SetFamily.SSElem (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_fam w

private theorem transpose_mem_iff :
    ∀ b b' : transposeInterp.Map A,
      Lax799700.SetFamily.SSMem b b' ↔ Lax799700.SetFamily.SSMem (transposeInterp.mapEquivSelf A b')
        (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact transpose_mem w w'

private theorem transpose_marked_iff :
    ∀ b : transposeInterp.Map A,
      Lax799700.SetFamily.SSMarked b ↔ Lax799700.SetFamily.SSMarked (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_marked w

/-- The hitting sets of the transposed system are the covers. -/
theorem sharpHittingSet_transpose_map :
    SharpHittingSet (transposeInterp.Map A) = SharpSetCover A :=
  Nat.card_congr (coverFamOfSizeEquiv (transposeInterp.mapEquivSelf A)
    (transpose_fam_iff A) (transpose_elem_iff A) (fun b b' => transpose_mem_iff A b' b)
    (transpose_marked_iff A))

/-- The covers of the transposed system are the hitting sets. -/
theorem sharpSetCover_transpose_map :
    SharpSetCover (transposeInterp.Map A) = SharpHittingSet A :=
  Nat.card_congr (coverFamOfSizeEquiv (transposeInterp.mapEquivSelf A)
    (transpose_elem_iff A) (transpose_fam_iff A) (fun b b' => transpose_mem_iff A b b')
    (transpose_marked_iff A))

end Apply

/-! ### Membership -/

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive CoverSelBlockIx where
/-- The cover. -/

  | sel
  deriving DecidableEq

instance : Fintype _root_.Lax280166Proofs.DescriptiveComplexity.CoverSelBlockIx :=
  ⟨List.toFinset [.sel], by intro x; cases x <;> simp⟩

/-- The block of the counting definition of Set Cover: the cover itself. -/
def coverSelBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax280166Proofs.DescriptiveComplexity.CoverSelBlockIx
  arity := fun i =>
    match i with
    | .sel => 1

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev coverSelLang : FirstOrder.Language :=
  (Lax799700.SetFamily.setSystem).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.coverSelBlock)

/-- The `elem` symbol over the sum. -/
abbrev cvElemSym : (_root_.Lax280166Proofs.DescriptiveComplexity.coverSelLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssElem

/-- The `fam` symbol over the sum. -/
abbrev cvFamSym : (_root_.Lax280166Proofs.DescriptiveComplexity.coverSelLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssFam

/-- The `mem` symbol over the sum. -/
abbrev cvMemSym : (_root_.Lax280166Proofs.DescriptiveComplexity.coverSelLang).Relations 2 :=
  Sum.inl Lax799700.SetFamily.ssMem

/-- The `marked` symbol over the sum. -/
abbrev cvMarkedSym : (_root_.Lax280166Proofs.DescriptiveComplexity.coverSelLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssMarked

/-- The `sel` relation variable. -/
def cvSelRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.coverSelBlock).Relations 1 :=
  ⟨.sel, rfl⟩

/-- The `sel` symbol over the sum. -/
abbrev cvSelSym : (_root_.Lax280166Proofs.DescriptiveComplexity.coverSelLang).Relations 1 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.cvSelRel

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

instance : Subsingleton coverSelBlock.ι :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The order-free kernel of #Set Cover: the guessed subfamily consists of sets
of the family and covers every ground element. -/
noncomputable def coverSelKernel : coverSelLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
        ((FirstOrder.Language.Relations.formula₁ cvSelSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
          (FirstOrder.Language.Relations.formula₁ cvFamSym (FirstOrder.Language.Term.var (Sum.inr 0)))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 1)
        ((FirstOrder.Language.Relations.formula₁ cvElemSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
          (FirstOrder.Language.Formula.iExs (Fin 1)
            (FirstOrder.Language.Relations.formula₁ cvSelSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₂ cvMemSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                (FirstOrder.Language.Term.var (Sum.inr 0)))))

/-- Realization of the order-free kernel of #Set Cover. -/
theorem realize_coverSelKernel {A : Type} [Lax799700.SetFamily.setSystem.Structure A]
    (ρ : coverSelBlock.Assignment A) :
    (@Sentence.Realize coverSelLang A
        (@sumStructure _ _ A _ (coverSelBlock.structure ρ)) coverSelKernel) ↔
      (∀ s : A, (ρ .sel fun _ => s) → Lax799700.SetFamily.SSFam s) ∧
        ∀ x : A, Lax799700.SetFamily.SSElem x → ∃ s : A, (ρ .sel fun _ => s) ∧ Lax799700.SetFamily.SSMem x s := by
  let := coverSelBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := coverSelLang) (M := A) cvSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [coverSelKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_iExs, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsub,
    Matrix.cons_val_zero]
  refine and_congr ⟨fun h s hs => h (fun _ => s) hs, fun h i hi => h (i 0) hi⟩
    ⟨fun h x hx => ?_, fun h i hi => ?_⟩
  · obtain ⟨s, hs⟩ := h (fun _ => x) hx
    exact ⟨s 0, hs⟩
  · obtain ⟨s, hs⟩ := h (i 0) hi
    exact ⟨fun _ => s, hs⟩

/-- **#Set Cover is in `#P`.** -/
theorem sharpSetCover_mem_sharpP : SharpSetCover ∈ SharpP :=
  sharpPDefinable_of_sized_set SharpSetCover coverSelBlock Lax799700.SetFamily.ssMarked .sel rfl coverSelKernel
    (fun A _ G => (∀ s : A, G s → Lax799700.SetFamily.SSFam s) ∧ ∀ x : A, Lax799700.SetFamily.SSElem x → ∃ s : A, G s ∧ Lax799700.SetFamily.SSMem x s)
    (fun _ _ ρ => realize_coverSelKernel ρ)
    fun _ _ hfin => Nat.card_congr
      (Equiv.subtypeEquivRight fun _ => (and_iff_right hfin).trans and_assoc.symm)

/-! ### Hardness of #Set Cover -/

section Hardness

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

/-- The vertex-sets of a vertex cover of the threshold size are a cover of the
threshold size. -/
theorem setCoverOfSize_vertexFamily {C : A → Prop} (h : Lax280166.CountingCliques.CoverOfSize A C) :
    Lax280166.CountingSetFamilies.SetCoverOfSize (edgeIncidenceInterp.Map A) (vertexFamily C) := by
  obtain ⟨hfin, hcov, hcard⟩ := h
  have := hfin
  refine ⟨edgeIncidenceInterp.map_finite A, ?_, ?_,
    (ncard_vertexFamily C).trans (hcard.trans (ncard_marked A).symm)⟩
  · rintro s ⟨v, -, rfl⟩
    exact (edgeIncidence_fam ![v, v]).mpr (by simp)
  · rintro ⟨⟨⟩, w⟩ hx
    obtain ⟨hadj, hne⟩ := (edgeIncidence_elem w).mp hx
    rcases hcov (w 0) (w 1) hne hadj with h0 | h1
    · exact ⟨diagPt (w 0), ⟨w 0, h0, rfl⟩,
        (edgeIncidence_mem w ![w 0, w 0]).mpr ⟨by simp, Or.inl (by simp)⟩⟩
    · exact ⟨diagPt (w 1), ⟨w 1, h1, rfl⟩,
        (edgeIncidence_mem w ![w 1, w 1]).mpr ⟨by simp, Or.inr (by simp)⟩⟩

/-- A cover of the interpreted system consists of vertex-sets. -/
theorem setCover_diag {G : edgeIncidenceInterp.Map A → Prop}
    (h : Lax280166.CountingSetFamilies.SetCoverOfSize (edgeIncidenceInterp.Map A) G) :
    ∀ p : edgeIncidenceInterp.Map A, G p → ∃ v, p = diagPt v := by
  rintro ⟨⟨⟩, w⟩ hw
  exact ⟨w 0, (eq_diagPt_iff () w (w 0)).mpr
    ⟨rfl, ((edgeIncidence_fam w).mp (h.2.1 _ hw)).symm⟩⟩

/-- The vertices of a cover of the threshold size are a vertex cover of the
threshold size. -/
theorem coverOfSize_of_setCover {G : edgeIncidenceInterp.Map A → Prop}
    (h : Lax280166.CountingSetFamilies.SetCoverOfSize (edgeIncidenceInterp.Map A) G) :
    Lax280166.CountingCliques.CoverOfSize A fun v => G (diagPt v) := by
  have hdiag := setCover_diag h
  obtain ⟨hfin, -, hcov, hcard⟩ := h
  refine ⟨Finite.of_injective _ (diagPt_injective (A := A)), fun x y hxy hadj => ?_,
    (ncard_diag_eq _ G hdiag fun _ => Iff.rfl).symm.trans (hcard.trans (ncard_marked A))⟩
  obtain ⟨s, hsG, hsMem⟩ := hcov ((), ![x, y])
    ((edgeIncidence_elem ![x, y]).mpr ⟨hadj, hxy⟩)
  obtain ⟨v, rfl⟩ := hdiag s hsG
  obtain ⟨-, hend⟩ := (edgeIncidence_mem ![x, y] ![v, v]).mp hsMem
  rcases hend with h | h
  · exact Or.inl (by simpa [show v = x by simpa using h] using hsG)
  · exact Or.inr (by simpa [show v = y by simpa using h] using hsG)

variable (A) in
/-- **The covers of the threshold size of the edge-incidence system are the
vertex covers of the threshold size**, bijectively. -/
def coverEquiv :
    {C : A → Prop // Lax280166.CountingCliques.CoverOfSize A C} ≃
      {G : edgeIncidenceInterp.Map A → Prop //
        Lax280166.CountingSetFamilies.SetCoverOfSize (edgeIncidenceInterp.Map A) G} where
  toFun C := ⟨vertexFamily C.1, setCoverOfSize_vertexFamily C.2⟩
  invFun G := ⟨fun v => G.1 (diagPt v), coverOfSize_of_setCover G.2⟩
  left_inv C := Subtype.ext (funext fun v => propext
    ⟨fun ⟨_, hv', heq⟩ => diagPt_injective heq ▸ hv', fun hv => ⟨v, hv, rfl⟩⟩)
  right_inv G := Subtype.ext (funext fun p => propext
    ⟨by
      rintro ⟨v, hv, rfl⟩
      exact hv,
    fun hp => by
      obtain ⟨v, rfl⟩ := setCover_diag G.2 p hp
      exact ⟨v, hp, rfl⟩⟩)

end Hardness

/-! ### The reductions and the completeness theorems -/

/-- **#Vertex Cover reduces parsimoniously to #Set Cover**, by the
edge-incidence interpretation. -/
noncomputable def sharpVertexCover_parsimonious_sharpSetCover :
    SharpVertexCover ≤ᵖ SharpSetCover where
  Tag := Unit
  dim := 2
  toInterpretation := edgeIncidenceInterp
  correct A _ _ _ := Nat.card_congr (coverEquiv A)

/-- **#Set Cover reduces parsimoniously to #Hitting Set**, by transposition. -/
noncomputable def sharpSetCover_parsimonious_sharpHittingSet :
    SharpSetCover ≤ᵖ SharpHittingSet where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ _ := (sharpHittingSet_transpose_map A).symm

/-- **#Hitting Set reduces parsimoniously to #Set Cover**, by transposition. -/
noncomputable def sharpHittingSet_parsimonious_sharpSetCover :
    SharpHittingSet ≤ᵖ SharpSetCover where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ _ := (sharpSetCover_transpose_map A).symm

/-- #Set Cover is parsimoniously `#P`-hard. -/
theorem sharpSetCover_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpSetCover :=
  SharpP.parsimoniousHard_of_parsimonious sharpVertexCover_parsimonious_sharpSetCover
    sharpVertexCover_sharpP_parsimoniousHard

/-- **#Set Cover is parsimoniously `#P`-complete**, counting the covers of
exactly the threshold size. -/
theorem sharpSetCover_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpSetCover :=
  ⟨sharpSetCover_mem_sharpP, sharpSetCover_sharpP_parsimoniousHard⟩

/-- **#Hitting Set is in `#P`.** -/
theorem sharpHittingSet_mem_sharpP : SharpHittingSet ∈ SharpP :=
  SharpP.mem_of_parsimonious sharpHittingSet_parsimonious_sharpSetCover
    sharpSetCover_mem_sharpP

/-- #Hitting Set is parsimoniously `#P`-hard. -/
theorem sharpHittingSet_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpHittingSet :=
  SharpP.parsimoniousHard_of_parsimonious sharpSetCover_parsimonious_sharpHittingSet
    sharpSetCover_sharpP_parsimoniousHard

/-- **#Hitting Set is parsimoniously `#P`-complete**, counting the hitting sets
of exactly the threshold size. -/
theorem sharpHittingSet_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpHittingSet :=
  ⟨sharpHittingSet_mem_sharpP, sharpHittingSet_sharpP_parsimoniousHard⟩

end Lax280166Proofs.DescriptiveComplexity


