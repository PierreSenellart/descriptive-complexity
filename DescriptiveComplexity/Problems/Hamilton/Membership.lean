/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Hamilton.Defs
import DescriptiveComplexity.SecondOrder

/-!
# The Hamilton circuit problems are existential second-order definable

The membership half of the NP-completeness of both problems:
`DescriptiveComplexity.dirHamCircuit_sigmaSODefinable` and
`DescriptiveComplexity.hamCircuit_sigmaSODefinable`.

Being a Hamilton circuit is not a first-order property of a graph, but a
circuit *is* a first-order object: a linear order of the universe
(`DescriptiveComplexity.TourOn`). So a single existential block guesses one binary
relation, and the kernel checks

* that it is a linear order – reflexive, transitive, antisymmetric, total;
* that every element is adjacent to its immediate successor, “immediate”
  being the first-order “nothing strictly in between”;
* that the last element is adjacent to the first.

The two problems share the block and the four order clauses, and differ only
in how the last two read the arc relation: as it stands for the directed
problem, symmetrized for the undirected one.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block of the `Σ₁` definitions: the circuit,
guessed as a linear order of the universe. -/
fo_block hamGuessBlock over Language.digraph dg into hamSOLang with h where
  /-- The guessed order. -/
  le : 2

/-- The guessed order, as an atom. -/
private def leF {α : Type} (x y : α) : hamSOLang.Formula α :=
  fo%[x, y] hLeSym(x, y)

/-- Adjacency, as the problem at hand reads it: the arc itself when `dir` is
true, the arc in either direction otherwise. -/
private def adjF (dir : Bool) {α : Type} (x y : α) : hamSOLang.Formula α :=
  fo%[x, y] if dir then hArcSym(x, y) else hArcSym(x, y) ∨ hArcSym(y, x)

/-- Kernel conjunct: the guessed order is reflexive. -/
private noncomputable def hamReflClause : hamSOLang.Sentence :=
  fo% ∀ x, leF⟨x, x⟩

/-- Kernel conjunct: the guessed order is transitive. -/
private noncomputable def hamTransClause : hamSOLang.Sentence :=
  fo% ∀ x y z, leF⟨x, y⟩ ∧ leF⟨y, z⟩ → leF⟨x, z⟩

/-- Kernel conjunct: the guessed order is antisymmetric. -/
private noncomputable def hamAntisymClause : hamSOLang.Sentence :=
  fo% ∀ x y, leF⟨x, y⟩ ∧ leF⟨y, x⟩ → x ≐ y

/-- Kernel conjunct: the guessed order is total. -/
private noncomputable def hamTotalClause : hamSOLang.Sentence :=
  fo% ∀ x y, leF⟨x, y⟩ ∨ leF⟨y, x⟩

/-- Kernel conjunct: every element is adjacent to its immediate successor. -/
private noncomputable def hamSuccClause (dir : Bool) : hamSOLang.Sentence :=
  fo% ∀ x y,
    (leF⟨x, y⟩ ∧ ¬ x ≐ y) ∧ (∀ z, leF⟨x, z⟩ ∧ leF⟨z, y⟩ → z ≐ x ∨ z ≐ y) →
      (adjF dir)⟨x, y⟩

/-- Kernel conjunct: the last element is adjacent to the first. -/
private noncomputable def hamWrapClause (dir : Bool) : hamSOLang.Sentence :=
  fo% ∀ x y, (∀ z, leF⟨x, z⟩) ∧ (∀ z, leF⟨z, y⟩) → (adjF dir)⟨y, x⟩

/-- The first-order kernel of the `Σ₁` definitions: the guessed relation is a
linear order carrying a tour. -/
noncomputable def hamKernel (dir : Bool) : hamSOLang.Sentence :=
  hamReflClause ⊓ (hamTransClause ⊓ (hamAntisymClause ⊓
    (hamTotalClause ⊓ (hamSuccClause dir ⊓ hamWrapClause dir))))

section Realize

variable {A : Type} [Language.digraph.Structure A]

/-- Adjacency, as the kernel reads it. -/
private theorem realize_adjF (dir : Bool) (ρ : hamGuessBlock.Assignment A) {α : Type}
    (v : α → A) (x y : α) :
    (@Formula.Realize hamSOLang A (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) _
        (adjF dir x y) v) ↔ (if dir then DGArc (v x) (v y) else DGEdge (v x) (v y)) := by
  let := hamGuessBlock.structure ρ
  cases dir <;>
    simp [adjF, DGArc, DGEdge, Language.relMap_sumInl, Formula.realize_rel₂]

/-- Realization of the kernel under an assignment of the guessed order. -/
private theorem realize_hamKernel (dir : Bool) (ρ : hamGuessBlock.Assignment A) :
    (@Sentence.Realize hamSOLang A
        (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) (hamKernel dir)) ↔
      IsLinOrd (fun x y : A => ρ .le ![x, y]) ∧
        (∀ x y : A, SuccOf (fun x y : A => ρ .le ![x, y]) x y →
          (if dir then DGArc x y else DGEdge x y)) ∧
        ∀ x y : A, (∀ z, ρ .le ![x, z]) → (∀ z, ρ .le ![z, y]) →
          (if dir then DGArc y x else DGEdge y x) := by
  let := hamGuessBlock.structure ρ
  have hsub : ∀ w : Fin 2 → A, RelMap (L := hamSOLang) (M := A) hLeSym w ↔ ρ .le w :=
    fun _ => Iff.rfl
  rw [hamKernel]
  simp only [hamReflClause, hamTransClause, hamAntisymClause, hamTotalClause, hamSuccClause,
    hamWrapClause, leF, Sentence.Realize, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_not, Formula.realize_equal,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl, hsub,
    realize_adjF dir ρ]
  simp only [IsLinOrd, SuccOf, and_assoc]
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

variable {A : Type} [Language.digraph.Structure A]

private theorem tourOn_iff_exists (dir : Bool) :
    TourOn (fun x y : A => if dir then DGArc x y else DGEdge x y) ↔
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
theorem dirHamCircuit_sigmaSODefinable : SigmaSODefinable 1 DirHamCircuit := by
  refine ⟨[hamGuessBlock], rfl, hamKernel true, ?_⟩
  intro A _ _ _
  rw [show DirHamCircuit.Holds A = HasDirHamCircuit A from rfl, HasDirHamCircuit,
    and_iff_right ‹Finite A›]
  exact tourOn_iff_exists true

/-- **Hamilton Circuit is `Σ₁`-definable**: the same certificate, the two
adjacency clauses reading the arc relation symmetrically. -/
theorem hamCircuit_sigmaSODefinable : SigmaSODefinable 1 HamCircuit := by
  refine ⟨[hamGuessBlock], rfl, hamKernel false, ?_⟩
  intro A _ _ _
  rw [show HamCircuit.Holds A = HasHamCircuit A from rfl, HasHamCircuit,
    and_iff_right ‹Finite A›]
  exact tourOn_iff_exists false

end SigmaOne

end DescriptiveComplexity
