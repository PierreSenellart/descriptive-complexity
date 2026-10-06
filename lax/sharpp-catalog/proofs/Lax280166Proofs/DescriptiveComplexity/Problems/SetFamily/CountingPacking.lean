/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.FromGraphs
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingReductions
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

namespace Lax280166Proofs.DescriptiveComplexity.PackingOfSize
end Lax280166Proofs.DescriptiveComplexity.PackingOfSize

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingCliques (IndepOfSize)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (PackingOfSize)
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
# #Set Packing

The counting version of `DescriptiveComplexity.SetPacking`: the number of pairwise
disjoint subfamilies with exactly as many sets as the marked set
(`DescriptiveComplexity.PackingOfSize`). It is parsimoniously `#P`-complete
(`DescriptiveComplexity.sharpSetPacking_sharpP_parsimoniousComplete`).

Membership is the generic argument for a solution of the threshold size
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`), the order-free part being
“the subfamily is a packing”. Hardness is the edge-incidence interpretation of
`DescriptiveComplexity.Problems.SetFamily.FromGraphs` unchanged: the sets of the
interpreted system are the vertices, one each, so its packings of a size are
the independent sets of that size, bijectively
(`DescriptiveComplexity.packEquiv`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Lax799700.SetFamily.setSystem.Structure A]

variable {A} {B : Type} [Lax799700.SetFamily.setSystem.Structure B]

/-- Packings of the threshold size transport along an isomorphism. -/
theorem PackingOfSize.map (e : A ≃[Lax799700.SetFamily.setSystem] B) {G : A → Prop}
    (h : Lax280166.CountingSetFamilies.PackingOfSize A G) : Lax280166.CountingSetFamilies.PackingOfSize B fun b => G (e.toEquiv.symm b) := by
  obtain ⟨hfin, hfam, hdisj, hcard⟩ := h
  have hsymm : ∀ b : B, e (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply
  refine ⟨Finite.of_equiv A e.toEquiv, fun s hs => ?_, fun s s' hs hs' hne x hx hmem => ?_, ?_⟩
  · have h := (relMap_equiv₁ e Lax799700.SetFamily.ssFam (e.toEquiv.symm s)).mp (hfam _ hs)
    rw [hsymm] at h
    exact h
  · refine hdisj _ _ hs hs' (fun h => hne (e.toEquiv.symm.injective h)) (e.toEquiv.symm x)
      ((relMap_equiv₁ e Lax799700.SetFamily.ssElem (e.toEquiv.symm x)).mpr ?_)
      ⟨(relMap_equiv₂ e Lax799700.SetFamily.ssMem (e.toEquiv.symm x) (e.toEquiv.symm s)).mpr ?_,
        (relMap_equiv₂ e Lax799700.SetFamily.ssMem (e.toEquiv.symm x) (e.toEquiv.symm s')).mpr ?_⟩
    · rw [hsymm]
      exact hx
    · rw [hsymm, hsymm]
      exact hmem.1
    · rw [hsymm, hsymm]
      exact hmem.2
  · exact ((ncard_setOf_symm e.toEquiv G).symm.trans hcard).trans
      (ncard_setOf_equiv e.toEquiv fun a => relMap_equiv₁ e Lax799700.SetFamily.ssMarked a)

end Solutions

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166.CountingSetFamilies.PackingOfSize

export Lax280166Proofs.DescriptiveComplexity.PackingOfSize (map)

end Lax280166.CountingSetFamilies.PackingOfSize

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Lax799700.SetFamily.setSystem.Structure A]

variable {A} {B : Type} [Lax799700.SetFamily.setSystem.Structure B]

end Solutions

/-- **#Set Packing**: the number of pairwise disjoint subfamilies with exactly
as many sets as the marked set. -/
noncomputable def SharpSetPacking : Lax366625.CountingProblems.CountingProblem Lax799700.SetFamily.setSystem where
  Count := fun A inst => Nat.card {G : A → Prop // @Lax280166.CountingSetFamilies.PackingOfSize A inst G}
  iso_invariant := fun {A B} _ _ e => by
    refine Nat.card_congr
      { toFun := fun G => ⟨fun b => G.1 (e.toEquiv.symm b), G.2.map e⟩
        invFun := fun T => ⟨fun a => T.1 (e.toEquiv a), ?_⟩
        left_inv := fun G => Subtype.ext (funext fun a => by simp)
        right_inv := fun T => Subtype.ext (funext fun b => by simp) }
    have h := T.2.map e.symm
    exact h

theorem sharpSetPacking_apply (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    SharpSetPacking A = Nat.card {G : A → Prop // Lax280166.CountingSetFamilies.PackingOfSize A G} :=
  rfl

/-- **The support of #Set Packing is Set Packing**: a packing at least as large
as the marked set contains one of exactly that size. -/
theorem sharpSetPacking_support_iff (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A] :
    SharpSetPacking.support A ↔ SetPacking A := by
  rw [CountingProblem.support_iff, sharpSetPacking_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨G, hfin, hfam, hdisj, hcard⟩, -⟩
    exact ⟨hfin, G, hfam, hdisj, hcard.ge⟩
  · rintro ⟨hfin, G, hfam, hdisj, hcard⟩
    obtain ⟨T, hTG, hT⟩ := Set.exists_subset_card_eq hcard
    exact ⟨⟨⟨fun s => s ∈ T, hfin, fun s hs => hfam s (hTG hs),
      fun s s' hs hs' => hdisj s s' (hTG hs) (hTG hs'), hT⟩⟩, inferInstance⟩

/-! ### Membership -/

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive PackSelBlockIx where
/-- The packing. -/

  | sel
  deriving DecidableEq

instance : Fintype _root_.Lax280166Proofs.DescriptiveComplexity.PackSelBlockIx :=
  ⟨List.toFinset [.sel], by intro x; cases x <;> simp⟩

/-- The block of the counting definition of Set Packing: the packing
itself. -/
def packSelBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax280166Proofs.DescriptiveComplexity.PackSelBlockIx
  arity := fun i =>
    match i with
    | .sel => 1

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev packSelLang : FirstOrder.Language :=
  (Lax799700.SetFamily.setSystem).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.packSelBlock)

/-- The `elem` symbol over the sum. -/
abbrev psElemSym : (_root_.Lax280166Proofs.DescriptiveComplexity.packSelLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssElem

/-- The `fam` symbol over the sum. -/
abbrev psFamSym : (_root_.Lax280166Proofs.DescriptiveComplexity.packSelLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssFam

/-- The `mem` symbol over the sum. -/
abbrev psMemSym : (_root_.Lax280166Proofs.DescriptiveComplexity.packSelLang).Relations 2 :=
  Sum.inl Lax799700.SetFamily.ssMem

/-- The `marked` symbol over the sum. -/
abbrev psMarkedSym : (_root_.Lax280166Proofs.DescriptiveComplexity.packSelLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssMarked

/-- The `sel` relation variable. -/
def psSelRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.packSelBlock).Relations 1 :=
  ⟨.sel, rfl⟩

/-- The `sel` symbol over the sum. -/
abbrev psSelSym : (_root_.Lax280166Proofs.DescriptiveComplexity.packSelLang).Relations 1 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.psSelRel

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

instance : Subsingleton packSelBlock.ι :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The order-free kernel of #Set Packing: the guessed subfamily consists of
sets of the family, pairwise disjoint. -/
noncomputable def packSelKernel : packSelLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
        ((FirstOrder.Language.Relations.formula₁ psSelSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
          (FirstOrder.Language.Relations.formula₁ psFamSym (FirstOrder.Language.Term.var (Sum.inr 0)))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 3)
        ((FirstOrder.Language.Relations.formula₁ psSelSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                  FirstOrder.Language.Relations.formula₁ psSelSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                FirstOrder.Language.BoundedFormula.not
                  (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inr 1))) ⊓
              FirstOrder.Language.Relations.formula₁ psElemSym (FirstOrder.Language.Term.var (Sum.inr 2))).imp
          (FirstOrder.Language.BoundedFormula.not
            (FirstOrder.Language.Relations.formula₂ psMemSym (FirstOrder.Language.Term.var (Sum.inr 2))
                (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₂ psMemSym (FirstOrder.Language.Term.var (Sum.inr 2))
                (FirstOrder.Language.Term.var (Sum.inr 1)))))

/-- Realization of the order-free kernel of #Set Packing. -/
theorem realize_packSelKernel {A : Type} [Lax799700.SetFamily.setSystem.Structure A]
    (ρ : packSelBlock.Assignment A) :
    (@Sentence.Realize packSelLang A
        (@sumStructure _ _ A _ (packSelBlock.structure ρ)) packSelKernel) ↔
      (∀ s : A, (ρ .sel fun _ => s) → Lax799700.SetFamily.SSFam s) ∧
        ∀ s s' : A, (ρ .sel fun _ => s) → (ρ .sel fun _ => s') → s ≠ s' →
          ∀ x : A, Lax799700.SetFamily.SSElem x → ¬(Lax799700.SetFamily.SSMem x s ∧ Lax799700.SetFamily.SSMem x s') := by
  let := packSelBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := packSelLang) (M := A) psSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [packSelKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub,
    Matrix.cons_val_zero]
  refine and_congr ⟨fun h s hs => h (fun _ => s) hs, fun h i hi => h (i 0) hi⟩
    ⟨fun h s s' hs hs' hne x hx => h ![s, s', x] ⟨⟨⟨hs, hs'⟩, hne⟩, hx⟩,
      fun h i hi => h (i 0) (i 1) hi.1.1.1 hi.1.1.2 hi.1.2 (i 2) hi.2⟩

/-- **#Set Packing is in `#P`.** -/
theorem sharpSetPacking_mem_sharpP : SharpSetPacking ∈ SharpP :=
  sharpPDefinable_of_sized_set SharpSetPacking packSelBlock Lax799700.SetFamily.ssMarked .sel rfl packSelKernel
    (fun A _ G => (∀ s : A, G s → Lax799700.SetFamily.SSFam s) ∧
      ∀ s s' : A, G s → G s' → s ≠ s' → ∀ x : A, Lax799700.SetFamily.SSElem x → ¬(Lax799700.SetFamily.SSMem x s ∧ Lax799700.SetFamily.SSMem x s'))
    (fun _ _ ρ => realize_packSelKernel ρ)
    fun _ _ hfin => Nat.card_congr
      (Equiv.subtypeEquivRight fun _ => (and_iff_right hfin).trans and_assoc.symm)

/-! ### Hardness -/

section Hardness

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

/-- The vertex-sets of an independent set of the threshold size are a packing
of the threshold size. -/
theorem packingOfSize_vertexFamily {S : A → Prop} (h : Lax280166.CountingCliques.IndepOfSize A S) :
    Lax280166.CountingSetFamilies.PackingOfSize (edgeIncidenceInterp.Map A) (vertexFamily S) := by
  obtain ⟨hfin, hS, hcard⟩ := h
  have := hfin
  refine ⟨edgeIncidenceInterp.map_finite A, ?_, ?_,
    (ncard_vertexFamily S).trans (hcard.trans (ncard_marked A).symm)⟩
  · rintro s ⟨v, -, rfl⟩
    exact (edgeIncidence_fam ![v, v]).mpr (by simp)
  · rintro s s' ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ hne x hx ⟨hmu, hmv⟩
    have huv : u ≠ v := fun h => hne (by rw [h])
    rcases (exists_elem_mem_both_iff huv).mp ⟨x, hx, hmu, hmv⟩ with h | h
    · exact hS u v hu hv huv h
    · exact hS v u hv hu huv.symm h

/-- A packing of the interpreted system consists of vertex-sets. -/
theorem packing_diag {G : edgeIncidenceInterp.Map A → Prop}
    (h : Lax280166.CountingSetFamilies.PackingOfSize (edgeIncidenceInterp.Map A) G) :
    ∀ p : edgeIncidenceInterp.Map A, G p → ∃ v, p = diagPt v := by
  rintro ⟨⟨⟩, w⟩ hw
  exact ⟨w 0, (eq_diagPt_iff () w (w 0)).mpr
    ⟨rfl, ((edgeIncidence_fam w).mp (h.2.1 _ hw)).symm⟩⟩

/-- The vertices of a packing of the threshold size are an independent set of
the threshold size. -/
theorem indepOfSize_of_packing {G : edgeIncidenceInterp.Map A → Prop}
    (h : Lax280166.CountingSetFamilies.PackingOfSize (edgeIncidenceInterp.Map A) G) :
    Lax280166.CountingCliques.IndepOfSize A fun v => G (diagPt v) := by
  have hdiag := packing_diag h
  obtain ⟨hfin, -, hdisj, hcard⟩ := h
  refine ⟨Finite.of_injective _ (diagPt_injective (A := A)), fun u v hu hv huv hadj => ?_,
    (ncard_diag_eq _ G hdiag fun _ => Iff.rfl).symm.trans (hcard.trans (ncard_marked A))⟩
  obtain ⟨x, hx, hmu, hmv⟩ := (exists_elem_mem_both_iff huv).mpr (Or.inl hadj)
  exact hdisj _ _ hu hv (fun h => huv (diagPt_injective h)) x hx ⟨hmu, hmv⟩

variable (A) in
/-- **The packings of the threshold size of the edge-incidence system are the
independent sets of the threshold size**, bijectively. -/
def packEquiv :
    {S : A → Prop // Lax280166.CountingCliques.IndepOfSize A S} ≃
      {G : edgeIncidenceInterp.Map A → Prop //
        Lax280166.CountingSetFamilies.PackingOfSize (edgeIncidenceInterp.Map A) G} where
  toFun S := ⟨vertexFamily S.1, packingOfSize_vertexFamily S.2⟩
  invFun G := ⟨fun v => G.1 (diagPt v), indepOfSize_of_packing G.2⟩
  left_inv S := Subtype.ext (funext fun v => propext
    ⟨fun ⟨_, hv', heq⟩ => diagPt_injective heq ▸ hv', fun hv => ⟨v, hv, rfl⟩⟩)
  right_inv G := Subtype.ext (funext fun p => propext
    ⟨by
      rintro ⟨v, hv, rfl⟩
      exact hv,
    fun hp => by
      obtain ⟨v, rfl⟩ := packing_diag G.2 p hp
      exact ⟨v, hp, rfl⟩⟩)

end Hardness

/-- **#Independent Set reduces parsimoniously to #Set Packing**, by the
edge-incidence interpretation. -/
noncomputable def sharpIndependentSet_parsimonious_sharpSetPacking :
    SharpIndependentSet ≤ᵖ SharpSetPacking where
  Tag := Unit
  dim := 2
  toInterpretation := edgeIncidenceInterp
  correct A _ _ _ := Nat.card_congr (packEquiv A)

/-- #Set Packing is parsimoniously `#P`-hard. -/
theorem sharpSetPacking_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpSetPacking :=
  SharpP.parsimoniousHard_of_parsimonious sharpIndependentSet_parsimonious_sharpSetPacking
    sharpIndependentSet_sharpP_parsimoniousHard

/-- **#Set Packing is parsimoniously `#P`-complete**, counting the packings of
exactly the threshold size. -/
theorem sharpSetPacking_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpSetPacking :=
  ⟨sharpSetPacking_mem_sharpP, sharpSetPacking_sharpP_parsimoniousHard⟩

end Lax280166Proofs.DescriptiveComplexity


