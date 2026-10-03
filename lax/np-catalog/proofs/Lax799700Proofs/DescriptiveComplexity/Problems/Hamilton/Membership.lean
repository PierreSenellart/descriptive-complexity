/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.Hamilton.Defs
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
# The Hamilton circuit problems are existential second-order definable

The membership half of the NP-completeness of both problems:
`Lax799700Proofs.DescriptiveComplexity.dirHamCircuit_sigmaSODefinable` and
`Lax799700Proofs.DescriptiveComplexity.hamCircuit_sigmaSODefinable`.

Being a Hamilton circuit is not a first-order property of a graph, but a
circuit *is* a first-order object: a linear order of the universe
(`Lax799700Proofs.DescriptiveComplexity.TourOn`). So a single existential block guesses one binary
relation, and the kernel checks

* that it is a linear order – reflexive, transitive, antisymmetric, total;
* that every element is adjacent to its immediate successor, “immediate”
  being the first-order “nothing strictly in between”;
* that the last element is adjacent to the first.

The two problems share the block and the four order clauses, and differ only
in how the last two read the arc relation: as it stands for the directed
problem, symmetrized for the undirected one.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive HamGuessBlockIx where
/-- The guessed order. -/

  | le
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.HamGuessBlockIx :=
  ⟨List.toFinset [.le], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definitions: the circuit,
guessed as a linear order of the universe. -/
def hamGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.HamGuessBlockIx
  arity := fun i =>
    match i with
    | .le => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev hamSOLang : FirstOrder.Language :=
  (Lax799700.Hamilton.digraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.hamGuessBlock)

/-- The `arc` symbol over the sum. -/
abbrev hArcSym : (_root_.Lax799700Proofs.DescriptiveComplexity.hamSOLang).Relations 2 :=
  Sum.inl Lax799700.Hamilton.dgArc

/-- The `le` relation variable. -/
def hLeRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.hamGuessBlock).Relations 2 :=
  ⟨.le, rfl⟩

/-- The `le` symbol over the sum. -/
abbrev hLeSym : (_root_.Lax799700Proofs.DescriptiveComplexity.hamSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.hLeRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- The guessed order, as an atom. -/
private def leF {α : Type} (x y : α) : hamSOLang.Formula α :=
  FirstOrder.Language.Relations.formula₂ hLeSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- Adjacency, as the problem at hand reads it: the arc itself when `dir` is
true, the arc in either direction otherwise. -/
private def adjF (dir : Bool) {α : Type} (x y : α) : hamSOLang.Formula α :=
  if dir then
      FirstOrder.Language.Relations.formula₂ hArcSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)
    else
      FirstOrder.Language.Relations.formula₂ hArcSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y) ⊔
        FirstOrder.Language.Relations.formula₂ hArcSym (FirstOrder.Language.Term.var y) (FirstOrder.Language.Term.var x)

/-- Kernel conjunct: the guessed order is reflexive. -/
private noncomputable def hamReflClause : hamSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (leF (Sum.inr 0) (Sum.inr 0))

/-- Kernel conjunct: the guessed order is transitive. -/
private noncomputable def hamTransClause : hamSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((leF (Sum.inr 0) (Sum.inr 1) ⊓ leF (Sum.inr 1) (Sum.inr 2)).imp (leF (Sum.inr 0) (Sum.inr 2)))

/-- Kernel conjunct: the guessed order is antisymmetric. -/
private noncomputable def hamAntisymClause : hamSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((leF (Sum.inr 0) (Sum.inr 1) ⊓ leF (Sum.inr 1) (Sum.inr 0)).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- Kernel conjunct: the guessed order is total. -/
private noncomputable def hamTotalClause : hamSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2) (leF (Sum.inr 0) (Sum.inr 1) ⊔ leF (Sum.inr 1) (Sum.inr 0))

/-- Kernel conjunct: every element is adjacent to its immediate successor. -/
private noncomputable def hamSuccClause (dir : Bool) : hamSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((leF (Sum.inr 0) (Sum.inr 1) ⊓
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1))) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 1)
              ((leF (Sum.inl (Sum.inr 0)) (Sum.inr 0) ⊓ leF (Sum.inr 0) (Sum.inl (Sum.inr 1))).imp
                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0))) ⊔
                  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 1)))))).imp
        ((adjF dir) (Sum.inr 0) (Sum.inr 1)))

/-- Kernel conjunct: the last element is adjacent to the first. -/
private noncomputable def hamWrapClause (dir : Bool) : hamSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Formula.iAlls (Fin 1) (leF (Sum.inl (Sum.inr 0)) (Sum.inr 0)) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 1) (leF (Sum.inr 0) (Sum.inl (Sum.inr 1)))).imp
        ((adjF dir) (Sum.inr 1) (Sum.inr 0)))

/-- The first-order kernel of the `Σ₁` definitions: the guessed relation is a
linear order carrying a tour. -/
noncomputable def hamKernel (dir : Bool) : hamSOLang.Sentence :=
  hamReflClause ⊓ (hamTransClause ⊓ (hamAntisymClause ⊓
    (hamTotalClause ⊓ (hamSuccClause dir ⊓ hamWrapClause dir))))

section Realize

variable {A : Type} [Lax799700.Hamilton.digraph.Structure A]

/-- Adjacency, as the kernel reads it. -/
private theorem realize_adjF (dir : Bool) (ρ : hamGuessBlock.Assignment A) {α : Type}
    (v : α → A) (x y : α) :
    (@Formula.Realize hamSOLang A (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) _
        (adjF dir x y) v) ↔ (if dir then Lax799700.Hamilton.DGArc (v x) (v y) else Lax799700.Hamilton.DGEdge (v x) (v y)) := by
  let := hamGuessBlock.structure ρ
  cases dir <;>
    simp [adjF, Lax799700.Hamilton.DGArc, Lax799700.Hamilton.DGEdge, Language.relMap_sumInl, Formula.realize_rel₂]

/-- Realization of the kernel under an assignment of the guessed order. -/
private theorem realize_hamKernel (dir : Bool) (ρ : hamGuessBlock.Assignment A) :
    (@Sentence.Realize hamSOLang A
        (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) (hamKernel dir)) ↔
      Lax904597.Machines.IsLinOrd (fun x y : A => ρ .le ![x, y]) ∧
        (∀ x y : A, Lax799700.Hamilton.SuccOf (fun x y : A => ρ .le ![x, y]) x y →
          (if dir then Lax799700.Hamilton.DGArc x y else Lax799700.Hamilton.DGEdge x y)) ∧
        ∀ x y : A, (∀ z, ρ .le ![x, z]) → (∀ z, ρ .le ![z, y]) →
          (if dir then Lax799700.Hamilton.DGArc y x else Lax799700.Hamilton.DGEdge y x) := by
  let := hamGuessBlock.structure ρ
  have hsub : ∀ w : Fin 2 → A, RelMap (L := hamSOLang) (M := A) hLeSym w ↔ ρ .le w :=
    fun _ => Iff.rfl
  rw [hamKernel]
  simp only [hamReflClause, hamTransClause, hamAntisymClause, hamTotalClause, hamSuccClause,
    hamWrapClause, leF, Sentence.Realize, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_not, Formula.realize_equal,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl, hsub,
    realize_adjF dir ρ]
  simp only [Lax904597.Machines.IsLinOrd, Lax799700.Hamilton.SuccOf, and_assoc]
  refine and_congr ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩
    (and_congr ⟨fun h x y z h₁ h₂ => h ![x, y, z] ⟨h₁, h₂⟩,
        fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩
      (and_congr ⟨fun h x y h₁ h₂ => h ![x, y] ⟨h₁, h₂⟩,
          fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩
        (and_congr ⟨fun h x y => h ![x, y], fun h i => h (i 0) (i 1)⟩
          (and_congr ⟨fun h x y hs => ?_, fun h i hi => ?_⟩
            ⟨fun h x y h₁ h₂ => h ![x, y] ⟨fun _ => h₁ _, fun _ => h₂ _⟩,
              fun h i hi => h (i 0) (i 1) (fun z => hi.1 fun _ => z)
                fun z => hi.2 fun _ => z⟩))))
  · exact h ![x, y] ⟨hs.1, hs.2.1, fun z hz => hs.2.2 (z 0) hz.1 hz.2⟩
  · exact h (i 0) (i 1) ⟨hi.1, hi.2.1, fun z h₁ h₂ => hi.2.2 (fun _ => z) ⟨h₁, h₂⟩⟩

end Realize

/-! ### The two definability theorems -/

section Definable

variable {A : Type} [Lax799700.Hamilton.digraph.Structure A]

private theorem tourOn_iff_exists (dir : Bool) :
    Lax799700.Hamilton.TourOn (fun x y : A => if dir then Lax799700.Hamilton.DGArc x y else Lax799700.Hamilton.DGEdge x y) ↔
      ∃ ρ : hamGuessBlock.Assignment A,
        @Sentence.Realize hamSOLang A
          (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) (hamKernel dir) := by
  constructor
  · rintro ⟨Le, hlin, hsucc, hwrap⟩
    refine ⟨fun i => match i with | .le => fun w : Fin 2 → A => Le (w 0) (w 1),
      (realize_hamKernel dir _).mpr ⟨hlin, hsucc, hwrap⟩⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hlin, hsucc, hwrap⟩ := (realize_hamKernel dir ρ).mp hρ
    exact ⟨fun x y => ρ .le ![x, y], hlin, hsucc, hwrap⟩

end Definable

/-- **Directed Hamilton Circuit is `Σ₁`-definable**: existentially guess the
circuit as a linear order of the universe, then check first-order that it is
one and that it follows the arcs. -/
theorem dirHamCircuit_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 DirHamCircuit := by
  refine ⟨[hamGuessBlock], rfl, hamKernel true, ?_⟩
  intro A _ _ _
  rw [show DirHamCircuit.Holds A = Lax799700.Hamilton.HasDirHamCircuit A from rfl, Lax799700.Hamilton.HasDirHamCircuit,
    and_iff_right ‹Finite A›]
  exact tourOn_iff_exists true

/-- **Hamilton Circuit is `Σ₁`-definable**: the same certificate, the two
adjacency clauses reading the arc relation symmetrically. -/
theorem hamCircuit_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 HamCircuit := by
  refine ⟨[hamGuessBlock], rfl, hamKernel false, ?_⟩
  intro A _ _ _
  rw [show HamCircuit.Holds A = Lax799700.Hamilton.HasHamCircuit A from rfl, Lax799700.Hamilton.HasHamCircuit,
    and_iff_right ‹Finite A›]
  exact tourOn_iff_exists false

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity


