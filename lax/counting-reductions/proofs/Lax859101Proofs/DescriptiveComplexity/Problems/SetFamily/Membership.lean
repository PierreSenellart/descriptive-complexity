/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax859101Proofs.DescriptiveComplexity.Problems.SetFamily.Defs
import Lax859101Proofs.DescriptiveComplexity.SecondOrder
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SigmaSODefinable)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.SetFamily (SSElem SSFam SSMarked SSMem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (ExactCoverBy)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem)
end FirstOrder.Language

/-!
# The set family is existential second-order definable

The membership half of the NP-completeness of Set Cover and Set Packing:
both are `Σ₁`-definable in the sense of `DescriptiveComplexity.SecondOrder`
(`DescriptiveComplexity.setCover_sigmaSODefinable`,
`DescriptiveComplexity.setPacking_sigmaSODefinable`). Hitting Set needs no definition
of its own: it FO-reduces to Set Cover
(`DescriptiveComplexity.Problems.SetFamily.Reductions`).

The two definitions share everything but their goal clause. A single
existential block (`DescriptiveComplexity.familyGuessBlock`) guesses a unary
relation – the subfamily – and a binary one – an injection witnessing the
threshold – and the first-order kernel is a conjunction of clauses built from
a common kit:

* `DescriptiveComplexity.sfFamClause`: the guessed subfamily consists of sets of the
  family (shared);
* the goal clause: `DescriptiveComplexity.sfCoverClause` (every ground element belongs
  to a guessed set) for Set Cover, `DescriptiveComplexity.sfDisjClause` (no ground
  element belongs to two distinct guessed sets) for Set Packing;
* the threshold clauses `DescriptiveComplexity.sfGuessToMarkedClause` (Set Cover, an
  upper bound: the subfamily injects into the marked set) or
  `DescriptiveComplexity.sfMarkedToGuessClause` (Set Packing, a lower bound: the marked
  set injects into the subfamily), together with the shared injectivity clause
  `DescriptiveComplexity.sfInjClause`.

The direction of the injection is the *only* semantic difference the threshold
makes, which is exactly what the embedding forms of
`DescriptiveComplexity.Problems.SetFamily.Defs`
(`DescriptiveComplexity.coversOn_iff_embedding`,
`DescriptiveComplexity.packsOn_iff_embedding`) say. This mirrors
`DescriptiveComplexity.clique_sigmaSODefinable`, whose threshold is a lower bound like
Set Packing's.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive FamilyGuessBlockIx where
/-- The guessed subfamily. -/

  | guess
/-- The injection witnessing the threshold. -/

  | inj
  deriving DecidableEq

instance : Fintype _root_.Lax859101Proofs.DescriptiveComplexity.FamilyGuessBlockIx :=
  ⟨List.toFinset [.guess, .inj], by intro x; cases x <;> simp⟩

/-- The single existential block shared by the `Σ₁` definitions of the set
family: a unary relation variable (the guessed subfamily) and a binary one
(the injection witnessing the threshold). -/
def familyGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax859101Proofs.DescriptiveComplexity.FamilyGuessBlockIx
  arity := fun i =>
    match i with
    | .guess => 1
    | .inj => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev setFamilySOLang : FirstOrder.Language :=
  (Lax799700.SetFamily.setSystem).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax859101Proofs.DescriptiveComplexity.familyGuessBlock)

/-- The `elem` symbol over the sum. -/
abbrev sfElemSym : (_root_.Lax859101Proofs.DescriptiveComplexity.setFamilySOLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssElem

/-- The `fam` symbol over the sum. -/
abbrev sfFamSym : (_root_.Lax859101Proofs.DescriptiveComplexity.setFamilySOLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssFam

/-- The `mem` symbol over the sum. -/
abbrev sfMemSym : (_root_.Lax859101Proofs.DescriptiveComplexity.setFamilySOLang).Relations 2 :=
  Sum.inl Lax799700.SetFamily.ssMem

/-- The `marked` symbol over the sum. -/
abbrev sfMarkedSym : (_root_.Lax859101Proofs.DescriptiveComplexity.setFamilySOLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssMarked

/-- The `guess` relation variable. -/
def sfGuessRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax859101Proofs.DescriptiveComplexity.familyGuessBlock).Relations 1 :=
  ⟨.guess, rfl⟩

/-- The `guess` symbol over the sum. -/
abbrev sfGuessSym : (_root_.Lax859101Proofs.DescriptiveComplexity.setFamilySOLang).Relations 1 :=
  Sum.inr _root_.Lax859101Proofs.DescriptiveComplexity.sfGuessRel

/-- The `inj` relation variable. -/
def sfInjRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax859101Proofs.DescriptiveComplexity.familyGuessBlock).Relations 2 :=
  ⟨.inj, rfl⟩

/-- The `inj` symbol over the sum. -/
abbrev sfInjSym : (_root_.Lax859101Proofs.DescriptiveComplexity.setFamilySOLang).Relations 2 :=
  Sum.inr _root_.Lax859101Proofs.DescriptiveComplexity.sfInjRel

end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-! ### The clauses -/

/-- Kernel clause: the binary relation variable of the block is empty. Exact
Cover does not use it, and a definition that *counts* the witnesses has to say
so, or each exact cover would be counted once per binary relation. -/
noncomputable def sfNoInjClause : setFamilySOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      (FirstOrder.Language.BoundedFormula.not
        (FirstOrder.Language.Relations.formula₂ sfInjSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- Kernel clause (Set Splitting): every set of the family contains a
colored ground element. -/
noncomputable def sfSplitInClause : setFamilySOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ sfFamSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₁ sfElemSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₂ sfMemSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0))) ⊓
            FirstOrder.Language.Relations.formula₁ sfGuessSym (FirstOrder.Language.Term.var (Sum.inr 0)))))

/-- Kernel clause (Set Splitting): every set of the family contains an
uncolored ground element. -/
noncomputable def sfSplitOutClause : setFamilySOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ sfFamSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₁ sfElemSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₂ sfMemSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0))) ⊓
            FirstOrder.Language.BoundedFormula.not
              (FirstOrder.Language.Relations.formula₁ sfGuessSym (FirstOrder.Language.Term.var (Sum.inr 0))))))

/-- The first-order kernel of the `Σ₁` definition of Set Splitting: the
guessed relation is read as one color class, and every set of the family
meets it and its complement. -/
noncomputable def setSplittingKernel : setFamilySOLang.Sentence :=
  sfSplitInClause ⊓ sfSplitOutClause

/-- Kernel clause: the guessed relation holds only of ground elements. -/
noncomputable def sfGuessElemClause : setFamilySOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ sfGuessSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Relations.formula₁ sfElemSym (FirstOrder.Language.Term.var (Sum.inr 0))))

/-- The kernel of the witness-counting definition of Set Splitting: a color
class of ground elements splitting every set, the unused relation variable
pinned. -/
noncomputable def sharpSetSplittingKernel : setFamilySOLang.Sentence :=
  setSplittingKernel ⊓ (sfGuessElemClause ⊓ sfNoInjClause)

/-! ### Realization of the clauses -/

section Realize

variable {A : Type} [Lax799700.SetFamily.setSystem.Structure A] (ρ : familyGuessBlock.Assignment A)

/-- Realization at a set system expanded by an assignment of the block. -/
private abbrev SFRealize (φ : setFamilySOLang.Sentence) : Prop :=
  @Sentence.Realize setFamilySOLang A
    (@sumStructure _ _ A _ (familyGuessBlock.structure ρ)) φ

private theorem realize_sfNoInjClause :
    SFRealize ρ sfNoInjClause ↔ ∀ x y : A, ¬ρ .inj ![x, y] := by
  let := familyGuessBlock.structure ρ
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := setFamilySOLang) (M := A) sfInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [sfNoInjClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, hsubI]
  exact ⟨fun h x y => h ![x, y], fun h i => h (i 0) (i 1)⟩

private theorem realize_sfSplitInClause :
    SFRealize ρ sfSplitInClause ↔
      ∀ f : A, Lax799700.SetFamily.SSFam f → ∃ x : A, Lax799700.SetFamily.SSElem x ∧ Lax799700.SetFamily.SSMem x f ∧ ρ .guess ![x] := by
  let := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ .guess w := fun _ => Iff.rfl
  rw [sfSplitInClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsub]
  constructor
  · intro h f hf
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := h (fun _ => f) hf
    exact ⟨x 0, hx1, hx2, hx3⟩
  · intro h i hi
    obtain ⟨x, hx1, hx2, hx3⟩ := h (i 0) hi
    exact ⟨fun _ => x, ⟨hx1, hx2⟩, hx3⟩

private theorem realize_sfSplitOutClause :
    SFRealize ρ sfSplitOutClause ↔
      ∀ f : A, Lax799700.SetFamily.SSFam f → ∃ x : A, Lax799700.SetFamily.SSElem x ∧ Lax799700.SetFamily.SSMem x f ∧ ¬ρ .guess ![x] := by
  let := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ .guess w := fun _ => Iff.rfl
  rw [sfSplitOutClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  constructor
  · intro h f hf
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := h (fun _ => f) hf
    exact ⟨x 0, hx1, hx2, hx3⟩
  · intro h i hi
    obtain ⟨x, hx1, hx2, hx3⟩ := h (i 0) hi
    exact ⟨fun _ => x, ⟨hx1, hx2⟩, hx3⟩

/-- Realization of the Set Splitting kernel. -/
private theorem realize_setSplittingKernel :
    SFRealize ρ setSplittingKernel ↔
      (∀ f : A, Lax799700.SetFamily.SSFam f → ∃ x : A, Lax799700.SetFamily.SSElem x ∧ Lax799700.SetFamily.SSMem x f ∧ ρ .guess ![x]) ∧
        ∀ f : A, Lax799700.SetFamily.SSFam f → ∃ x : A, Lax799700.SetFamily.SSElem x ∧ Lax799700.SetFamily.SSMem x f ∧ ¬ρ .guess ![x] := by
  rw [setSplittingKernel]
  simp only [SFRealize, Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_sfSplitInClause ρ) (realize_sfSplitOutClause ρ)

private theorem realize_sfGuessElemClause :
    SFRealize ρ sfGuessElemClause ↔ ∀ x : A, ρ .guess ![x] → Lax799700.SetFamily.SSElem x := by
  let := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ .guess w := fun _ => Iff.rfl
  rw [sfGuessElemClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub]
  constructor
  · intro h x hx
    exact h (fun _ => x) hx
  · intro h i hi
    have hi' : ρ .guess ![i 0] := by
      convert hi using 2
    exact h (i 0) hi'

/-- Realization of the counting kernel of Set Splitting. -/
theorem realize_sharpSetSplittingKernel :
    (@Sentence.Realize setFamilySOLang A
        (@sumStructure _ _ A _ (familyGuessBlock.structure ρ)) sharpSetSplittingKernel) ↔
      ((∀ f : A, Lax799700.SetFamily.SSFam f → ∃ x : A, Lax799700.SetFamily.SSElem x ∧ Lax799700.SetFamily.SSMem x f ∧ ρ .guess ![x]) ∧
        ∀ f : A, Lax799700.SetFamily.SSFam f → ∃ x : A, Lax799700.SetFamily.SSElem x ∧ Lax799700.SetFamily.SSMem x f ∧ ¬ρ .guess ![x]) ∧
      (∀ x : A, ρ .guess ![x] → Lax799700.SetFamily.SSElem x) ∧ ∀ x y : A, ¬ρ .inj ![x, y] := by
  have h1 := realize_setSplittingKernel ρ
  have h2 := realize_sfGuessElemClause ρ
  have h3 := realize_sfNoInjClause ρ
  let := familyGuessBlock.structure ρ
  rw [sharpSetSplittingKernel, Sentence.Realize, Formula.realize_inf, Formula.realize_inf]
  exact and_congr h1 (and_congr h2 h3)

end Realize

/-! ### The two definitions -/

end SigmaOne

end Lax859101Proofs.DescriptiveComplexity


