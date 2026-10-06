/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.Defs
import Lax280166Proofs.DescriptiveComplexity.SecondOrder
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

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (ExactCoverBy)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SigmaSODefinable)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.SetFamily (SSElem SSFam SSMarked SSMem)
end Lax280166Proofs.DescriptiveComplexity

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

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive FamilyGuessBlockIx where
/-- The guessed subfamily. -/

  | guess
/-- The injection witnessing the threshold. -/

  | inj
  deriving DecidableEq

instance : Fintype _root_.Lax280166Proofs.DescriptiveComplexity.FamilyGuessBlockIx :=
  ⟨List.toFinset [.guess, .inj], by intro x; cases x <;> simp⟩

/-- The single existential block shared by the `Σ₁` definitions of the set
family: a unary relation variable (the guessed subfamily) and a binary one
(the injection witnessing the threshold). -/
def familyGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax280166Proofs.DescriptiveComplexity.FamilyGuessBlockIx
  arity := fun i =>
    match i with
    | .guess => 1
    | .inj => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev setFamilySOLang : FirstOrder.Language :=
  (Lax799700.SetFamily.setSystem).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.familyGuessBlock)

/-- The `elem` symbol over the sum. -/
abbrev sfElemSym : (_root_.Lax280166Proofs.DescriptiveComplexity.setFamilySOLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssElem

/-- The `fam` symbol over the sum. -/
abbrev sfFamSym : (_root_.Lax280166Proofs.DescriptiveComplexity.setFamilySOLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssFam

/-- The `mem` symbol over the sum. -/
abbrev sfMemSym : (_root_.Lax280166Proofs.DescriptiveComplexity.setFamilySOLang).Relations 2 :=
  Sum.inl Lax799700.SetFamily.ssMem

/-- The `marked` symbol over the sum. -/
abbrev sfMarkedSym : (_root_.Lax280166Proofs.DescriptiveComplexity.setFamilySOLang).Relations 1 :=
  Sum.inl Lax799700.SetFamily.ssMarked

/-- The `guess` relation variable. -/
def sfGuessRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.familyGuessBlock).Relations 1 :=
  ⟨.guess, rfl⟩

/-- The `guess` symbol over the sum. -/
abbrev sfGuessSym : (_root_.Lax280166Proofs.DescriptiveComplexity.setFamilySOLang).Relations 1 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.sfGuessRel

/-- The `inj` relation variable. -/
def sfInjRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.familyGuessBlock).Relations 2 :=
  ⟨.inj, rfl⟩

/-- The `inj` symbol over the sum. -/
abbrev sfInjSym : (_root_.Lax280166Proofs.DescriptiveComplexity.setFamilySOLang).Relations 2 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.sfInjRel

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-! ### The clauses -/

/-- Kernel clause: the guessed subfamily consists of sets of the family. -/
noncomputable def sfFamClause : setFamilySOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ sfGuessSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Relations.formula₁ sfFamSym (FirstOrder.Language.Term.var (Sum.inr 0))))

/-- Kernel clause (Set Cover): every ground element belongs to a guessed
set. -/
noncomputable def sfCoverClause : setFamilySOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ sfElemSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₁ sfGuessSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            FirstOrder.Language.Relations.formula₂ sfMemSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
              (FirstOrder.Language.Term.var (Sum.inr 0)))))

/-- Kernel clause (Set Packing): no ground element belongs to two distinct
guessed sets. -/
noncomputable def sfDisjClause : setFamilySOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₁ sfGuessSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                FirstOrder.Language.Relations.formula₁ sfGuessSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1))) ⊓
            FirstOrder.Language.Relations.formula₁ sfElemSym (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        (FirstOrder.Language.BoundedFormula.not
          (FirstOrder.Language.Relations.formula₂ sfMemSym (FirstOrder.Language.Term.var (Sum.inr 2))
              (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            FirstOrder.Language.Relations.formula₂ sfMemSym (FirstOrder.Language.Term.var (Sum.inr 2))
              (FirstOrder.Language.Term.var (Sum.inr 1)))))

/-- The first-order kernel of the `Σ₁` definition of Exact Cover: the same
kit again, this time asking for a subfamily that both covers and is pairwise
disjoint – and, exactness replacing the threshold, no injection clause. -/
noncomputable def exactCoverKernel : setFamilySOLang.Sentence :=
  sfFamClause ⊓ (sfCoverClause ⊓ sfDisjClause)

/-- Kernel clause: the binary relation variable of the block is empty. Exact
Cover does not use it, and a definition that *counts* the witnesses has to say
so, or each exact cover would be counted once per binary relation. -/
noncomputable def sfNoInjClause : setFamilySOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      (FirstOrder.Language.BoundedFormula.not
        (FirstOrder.Language.Relations.formula₂ sfInjSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- The kernel of the witness-counting definition of Exact Cover: the kernel of
its `Σ₁` definition, with the unused relation variable pinned. -/
noncomputable def sharpExactCoverKernel : setFamilySOLang.Sentence :=
  exactCoverKernel ⊓ sfNoInjClause

/-! ### Realization of the clauses -/

section Realize

variable {A : Type} [Lax799700.SetFamily.setSystem.Structure A] (ρ : familyGuessBlock.Assignment A)

/-- Realization at a set system expanded by an assignment of the block. -/
private abbrev SFRealize (φ : setFamilySOLang.Sentence) : Prop :=
  @Sentence.Realize setFamilySOLang A
    (@sumStructure _ _ A _ (familyGuessBlock.structure ρ)) φ

private theorem realize_sfFamClause :
    SFRealize ρ sfFamClause ↔ ∀ s : A, ρ .guess ![s] → Lax799700.SetFamily.SSFam s := by
  let := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ .guess w := fun _ => Iff.rfl
  rw [sfFamClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub]
  exact ⟨fun h s hs => h (fun _ => s) hs, fun h i hi => h (i 0) hi⟩

private theorem realize_sfCoverClause :
    SFRealize ρ sfCoverClause ↔ ∀ x : A, Lax799700.SetFamily.SSElem x → ∃ s : A, ρ .guess ![s] ∧ Lax799700.SetFamily.SSMem x s := by
  let := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ .guess w := fun _ => Iff.rfl
  rw [sfCoverClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsub]
  constructor
  · intro h x hx
    obtain ⟨s, hs1, hs2⟩ := h (fun _ => x) hx
    exact ⟨s 0, hs1, hs2⟩
  · intro h i hi
    obtain ⟨s, hs1, hs2⟩ := h (i 0) hi
    exact ⟨fun _ => s, hs1, hs2⟩

private theorem realize_sfDisjClause :
    SFRealize ρ sfDisjClause ↔ ∀ s s' x : A, ρ .guess ![s] → ρ .guess ![s'] → s ≠ s' →
      Lax799700.SetFamily.SSElem x → ¬(Lax799700.SetFamily.SSMem x s ∧ Lax799700.SetFamily.SSMem x s') := by
  let := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ .guess w := fun _ => Iff.rfl
  rw [sfDisjClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub]
  exact ⟨fun h s s' x hs hs' hne hx => h ![s, s', x] ⟨⟨⟨hs, hs'⟩, hne⟩, hx⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1.1.1 hi.1.1.2 hi.1.2 hi.2⟩

/-- Realization of the Exact Cover kernel: the guessed subfamily consists of
sets of the family, covers every ground element, and no element belongs to two
distinct members. -/
private theorem realize_exactCoverKernel :
    SFRealize ρ exactCoverKernel ↔
      (∀ s : A, ρ .guess ![s] → Lax799700.SetFamily.SSFam s) ∧
        (∀ x : A, Lax799700.SetFamily.SSElem x → ∃ s : A, ρ .guess ![s] ∧ Lax799700.SetFamily.SSMem x s) ∧
        ∀ s s' x : A, ρ .guess ![s] → ρ .guess ![s'] → s ≠ s' → Lax799700.SetFamily.SSElem x →
          ¬(Lax799700.SetFamily.SSMem x s ∧ Lax799700.SetFamily.SSMem x s') := by
  rw [exactCoverKernel]
  simp only [SFRealize, Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_sfFamClause ρ)
    (and_congr (realize_sfCoverClause ρ) (realize_sfDisjClause ρ))

private theorem realize_sfNoInjClause :
    SFRealize ρ sfNoInjClause ↔ ∀ x y : A, ¬ρ .inj ![x, y] := by
  let := familyGuessBlock.structure ρ
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := setFamilySOLang) (M := A) sfInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [sfNoInjClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, hsubI]
  exact ⟨fun h x y => h ![x, y], fun h i => h (i 0) (i 1)⟩

/-- Realization of the counting kernel of Exact Cover: the guessed subfamily is
an exact cover, and the unused relation variable is empty. -/
theorem realize_sharpExactCoverKernel :
    (@Sentence.Realize setFamilySOLang A
        (@sumStructure _ _ A _ (familyGuessBlock.structure ρ)) sharpExactCoverKernel) ↔
      Lax280166.CountingSetFamilies.ExactCoverBy (Lax799700.SetFamily.SSElem (A := A)) Lax799700.SetFamily.SSFam Lax799700.SetFamily.SSMem (fun s => ρ .guess ![s]) ∧
        ∀ x y : A, ¬ρ .inj ![x, y] := by
  have h1 := realize_exactCoverKernel ρ
  have h2 := realize_sfNoInjClause ρ
  let := familyGuessBlock.structure ρ
  rw [sharpExactCoverKernel, Sentence.Realize, Formula.realize_inf]
  refine and_congr (h1.trans ?_) h2
  exact ⟨fun ⟨hf, hc, hd⟩ => ⟨hf, hc, fun s s' hs hs' hne x hx => hd s s' x hs hs' hne hx⟩,
    fun ⟨hf, hc, hd⟩ => ⟨hf, hc, fun s s' x hs hs' hne hx => hd s s' hs hs' hne x hx⟩⟩

end Realize

/-! ### The two definitions -/

end SigmaOne

end Lax280166Proofs.DescriptiveComplexity


