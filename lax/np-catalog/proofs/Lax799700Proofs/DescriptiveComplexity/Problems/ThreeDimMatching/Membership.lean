/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeDimMatching.Defs
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# 3-dimensional matching is existential second-order definable

The membership half of its NP-completeness
(`Lax799700Proofs.DescriptiveComplexity.threeDimMatching_sigmaSODefinable`): a matching *is* a
relation, so a single existential block guesses it – ternary, the first of the
catalog – and the kernel spells out the seven conditions of
`Lax799700Proofs.DescriptiveComplexity.IsMatchingOn`: that the guessed triples are available ones
inside the three classes, that every marked element is covered, and that no
two triples share a coordinate.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive TdmGuessBlockIx where
/-- The guessed matching. -/

  | matching
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.TdmGuessBlockIx :=
  ⟨List.toFinset [.matching], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition: the matching, a
ternary relation. -/
def tdmGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.TdmGuessBlockIx
  arity := fun i =>
    match i with
    | .matching => 3

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev tdmSOLang : FirstOrder.Language :=
  (Lax799700.ThreeDimMatching.tripleSys).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.tdmGuessBlock)

/-- The `xEl` symbol over the sum. -/
abbrev tXElSym : (_root_.Lax799700Proofs.DescriptiveComplexity.tdmSOLang).Relations 1 :=
  Sum.inl Lax799700.ThreeDimMatching.tsXEl

/-- The `yEl` symbol over the sum. -/
abbrev tYElSym : (_root_.Lax799700Proofs.DescriptiveComplexity.tdmSOLang).Relations 1 :=
  Sum.inl Lax799700.ThreeDimMatching.tsYEl

/-- The `zEl` symbol over the sum. -/
abbrev tZElSym : (_root_.Lax799700Proofs.DescriptiveComplexity.tdmSOLang).Relations 1 :=
  Sum.inl Lax799700.ThreeDimMatching.tsZEl

/-- The `trip` symbol over the sum. -/
abbrev tTripSym : (_root_.Lax799700Proofs.DescriptiveComplexity.tdmSOLang).Relations 3 :=
  Sum.inl Lax799700.ThreeDimMatching.tsTrip

/-- The `matching` relation variable. -/
def tMatchingRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.tdmGuessBlock).Relations 3 :=
  ⟨.matching, rfl⟩

/-- The `matching` symbol over the sum. -/
abbrev tMatchingSym : (_root_.Lax799700Proofs.DescriptiveComplexity.tdmSOLang).Relations 3 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.tMatchingRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- The guessed matching, as an atom. -/
private def matF {α : Type} (x y z : α) : tdmSOLang.Formula α :=
  FirstOrder.Language.Relations.formula tMatchingSym
      ![FirstOrder.Language.Term.var x, FirstOrder.Language.Term.var y, FirstOrder.Language.Term.var z]

/-- The available triples, as an atom. -/
private def tripF {α : Type} (x y z : α) : tdmSOLang.Formula α :=
  FirstOrder.Language.Relations.formula tTripSym
      ![FirstOrder.Language.Term.var x, FirstOrder.Language.Term.var y, FirstOrder.Language.Term.var z]

/-- Kernel conjunct: the guessed triples are available ones, inside the three
classes. -/
private noncomputable def tdmSubClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((matF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).imp
        (tripF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓
              FirstOrder.Language.Relations.formula₁ tXElSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            FirstOrder.Language.Relations.formula₁ tYElSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
          FirstOrder.Language.Relations.formula₁ tZElSym (FirstOrder.Language.Term.var (Sum.inr 2))))

/-- Kernel conjunct: every element of the first class is covered. -/
private noncomputable def tdmCovXClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ tXElSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 2) (matF (Sum.inl (Sum.inr 0)) (Sum.inr 0) (Sum.inr 1))))

/-- Kernel conjunct: every element of the second class is covered. -/
private noncomputable def tdmCovYClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ tYElSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 2) (matF (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 1))))

/-- Kernel conjunct: every element of the third class is covered. -/
private noncomputable def tdmCovZClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ tZElSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 2) (matF (Sum.inr 0) (Sum.inr 1) (Sum.inl (Sum.inr 0)))))

/-- Kernel conjunct: two triples sharing their first coordinate coincide. -/
private noncomputable def tdmUniqXClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 5)
      ((matF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ matF (Sum.inr 0) (Sum.inr 3) (Sum.inr 4)).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
            (FirstOrder.Language.Term.var (Sum.inr 3)) ⊓
          FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 2))
            (FirstOrder.Language.Term.var (Sum.inr 4))))

/-- Kernel conjunct: two triples sharing their second coordinate coincide. -/
private noncomputable def tdmUniqYClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 5)
      ((matF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ matF (Sum.inr 3) (Sum.inr 1) (Sum.inr 4)).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 3)) ⊓
          FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 2))
            (FirstOrder.Language.Term.var (Sum.inr 4))))

/-- Kernel conjunct: two triples sharing their third coordinate coincide. -/
private noncomputable def tdmUniqZClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 5)
      ((matF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ matF (Sum.inr 3) (Sum.inr 4) (Sum.inr 2)).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 3)) ⊓
          FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
            (FirstOrder.Language.Term.var (Sum.inr 4))))

/-- The first-order kernel of the `Σ₁` definition: the guessed relation is a
matching. -/
noncomputable def tdmKernel : tdmSOLang.Sentence :=
  tdmSubClause ⊓ (tdmCovXClause ⊓ (tdmCovYClause ⊓ (tdmCovZClause ⊓
    (tdmUniqXClause ⊓ (tdmUniqYClause ⊓ tdmUniqZClause)))))

section Realize

variable {A : Type} [Lax799700.ThreeDimMatching.tripleSys.Structure A]

/-- Realization of the kernel under an assignment of the guessed matching. -/
private theorem realize_tdmKernel (ρ : tdmGuessBlock.Assignment A) :
    (@Sentence.Realize tdmSOLang A
        (@sumStructure _ _ A _ (tdmGuessBlock.structure ρ)) tdmKernel) ↔
      Lax799700.ThreeDimMatching.IsMatchingOn (Lax799700.ThreeDimMatching.TSXEl (A := A)) Lax799700.ThreeDimMatching.TSYEl Lax799700.ThreeDimMatching.TSZEl Lax799700.ThreeDimMatching.TSTrip
        (fun x y z => ρ .matching ![x, y, z]) := by
  let := tdmGuessBlock.structure ρ
  have hsub : ∀ w : Fin 3 → A, RelMap (L := tdmSOLang) (M := A) tMatchingSym w ↔ ρ .matching w :=
    fun _ => Iff.rfl
  rw [tdmKernel, Lax799700.ThreeDimMatching.IsMatchingOn]
  simp only [tdmSubClause, tdmCovXClause, tdmCovYClause, tdmCovZClause, tdmUniqXClause,
    tdmUniqYClause, tdmUniqZClause, matF, tripF, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_imp, Formula.realize_equal,
    Formula.realize_rel₁, realize_rel₃, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  refine and_congr ⟨fun h x y z hm => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
      (and_congr ⟨fun h y hy => ?_, fun h i hi => ?_⟩
        (and_congr ⟨fun h z hz => ?_, fun h i hi => ?_⟩
          (and_congr ⟨fun h x y z y' z' h₁ h₂ => ?_, fun h i hi => ?_⟩
            (and_congr ⟨fun h x y z x' z' h₁ h₂ => ?_, fun h i hi => ?_⟩
              ⟨fun h x y z x' y' h₁ h₂ => ?_, fun h i hi => ?_⟩)))))
  · have h' := h ![x, y, z] hm
    exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩
  · have h' := h (i 0) (i 1) (i 2) hi
    exact ⟨⟨⟨h'.1, h'.2.1⟩, h'.2.2.1⟩, h'.2.2.2⟩
  · obtain ⟨w, hw⟩ := h (fun _ => x) hx
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨y, z, hyz⟩ := h (i 0) hi
    exact ⟨![y, z], hyz⟩
  · obtain ⟨w, hw⟩ := h (fun _ => y) hy
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨x, z, hxz⟩ := h (i 0) hi
    exact ⟨![x, z], hxz⟩
  · obtain ⟨w, hw⟩ := h (fun _ => z) hz
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨x, y, hxy⟩ := h (i 0) hi
    exact ⟨![x, y], hxy⟩
  · exact h ![x, y, z, y', z'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2
  · exact h ![x, y, z, x', z'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2
  · exact h ![x, y, z, x', y'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2

end Realize

/-- **3-dimensional matching is `Σ₁`-definable**: existentially guess the
matching – a ternary relation – then check first-order that it is one. Since
NP is defined as `Σ₁`-definability, this is the membership half of its
NP-completeness. -/
theorem threeDimMatching_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 ThreeDimMatching := by
  refine ⟨[tdmGuessBlock], rfl, tdmKernel, ?_⟩
  intro A _ _ _
  rw [show ThreeDimMatching.Holds A = Lax799700.ThreeDimMatching.HasThreeDimMatching A from rfl, Lax799700.ThreeDimMatching.HasThreeDimMatching,
    and_iff_right ‹Finite A›]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨fun i => match i with | .matching => fun w : Fin 3 → A => M (w 0) (w 1) (w 2),
      (realize_tdmKernel _).mpr hM⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨_, (realize_tdmKernel ρ).mp hρ⟩

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity


