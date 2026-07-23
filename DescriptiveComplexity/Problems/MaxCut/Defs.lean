/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Feedback.Defs

/-!
# Max Cut: the problem

MAX CUT ([Karp 1972][karp1972reducibility]): is there a set `S` of vertices
such that at least `k` edges have exactly one endpoint in `S`? Here, as
everywhere in this library, the threshold `k` is carried by the instance in
representation (A) – and, since a cut can have quadratically many edges, at
arity 2: `k` is the number of pairs in the marked relation of
`FirstOrder.Language.markedArcGraph`, the vocabulary introduced for Feedback Arc Set
and reused here unchanged.

The cut itself is read as a set of *ordered* pairs
(`DescriptiveComplexity.CutRel`): the pairs `(u, v)` with `u` adjacent to `v`, `u`
inside `S` and `v` outside. On a symmetric adjacency relation this counts
every cut edge exactly once, which is what makes the threshold comparison the
intended one without any division by two.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Semantics

variable {A : Type}

/-- The cut determined by `S`, as a relation: `a` is adjacent to `b`, `a` lies
inside `S` and `b` outside. Reading the cut as a set of ordered pairs of this
shape counts every cut edge of a symmetric adjacency relation once. -/
def CutRel (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  Adjp a b ∧ S a ∧ ¬S b

/-- Some cut is at least as large as the number encoded by the `Kp`-marked
pairs: “some cut has at least `k` edges”. -/
def MaxCutOn (Adjp : A → A → Prop) (Kp : A → A → Prop) : Prop :=
  ∃ S : A → Prop,
    {p : A × A | Kp p.1 p.2}.ncard ≤ {p : A × A | CutRel Adjp S p.1 p.2}.ncard

/-- The max-cut property, with the threshold certified by an injection of the
marked pairs into the cut – the shape the second-order definition guesses. -/
theorem maxCutOn_iff_certificate [Finite A] (Adjp : A → A → Prop) (Kp : A → A → Prop) :
    MaxCutOn Adjp Kp ↔ ∃ S : A → Prop,
      Nonempty ({p : A × A // Kp p.1 p.2} ↪ {p : A × A // CutRel Adjp S p.1 p.2}) :=
  exists_congr fun S => (nonempty_embedding_iff_ncard_le₂ Kp (CutRel Adjp S)).symm

variable {B : Type}

/-- `MaxCutOn` transports along an equivalence commuting with the two
relations. -/
theorem MaxCutOn.of_equiv (u : B ≃ A) {AdjB KB : B → B → Prop} {AdjA KA : A → A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b'))
    (hK : ∀ b b', KB b b' ↔ KA (u b) (u b')) (h : MaxCutOn AdjB KB) :
    MaxCutOn AdjA KA := by
  obtain ⟨S, hcard⟩ := h
  refine ⟨fun a => S (u.symm a), ?_⟩
  rw [← ncard_setOf_equiv₂ u hK,
    ← ncard_setOf_equiv₂ (RB := CutRel AdjB S)
      (RA := CutRel AdjA fun a => S (u.symm a)) u (fun b b' => by simp [CutRel, hadj])]
  exact hcard

private theorem maxCut_symm (u : B ≃ A) {RB : B → B → Prop} {RA : A → A → Prop}
    (h : ∀ b b', RB b b' ↔ RA (u b) (u b')) (a a' : A) :
    RA a a' ↔ RB (u.symm a) (u.symm a') := by
  rw [h]
  simp

/-- `MaxCutOn` transports along an equivalence, iff version. -/
theorem MaxCutOn.equiv_iff (u : B ≃ A) {AdjB KB : B → B → Prop} {AdjA KA : A → A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b'))
    (hK : ∀ b b', KB b b' ↔ KA (u b) (u b')) :
    MaxCutOn AdjB KB ↔ MaxCutOn AdjA KA :=
  ⟨MaxCutOn.of_equiv u hadj hK,
    MaxCutOn.of_equiv u.symm (maxCut_symm u hadj) (maxCut_symm u hK)⟩

end Semantics

section Problem

/-- An arc-marked graph has a cut at least as large as its marked relation.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasLargeCut (A : Type) [Language.markedArcGraph.Structure A] : Prop :=
  Finite A ∧ MaxCutOn (MAGAdj (A := A)) (MAGMarked (A := A))

/-- Having a large cut is isomorphism-invariant. -/
theorem hasLargeCut_iso {A B : Type} [Language.markedArcGraph.Structure A]
    [Language.markedArcGraph.Structure B] (e : A ≃[Language.markedArcGraph] B) :
    HasLargeCut A ↔ HasLargeCut B :=
  and_congr e.toEquiv.finite_iff
    (MaxCutOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e magAdj a b)
      fun a b => relMap_equiv₂ e magMarked a b)

/-- MAX CUT, as a problem on arc-marked graphs: is there a set of vertices
whose cut is at least as large as the marked relation? -/
def MaxCut : DecisionProblem Language.markedArcGraph where
  Holds := fun A inst => @HasLargeCut A inst
  iso_invariant := fun e => hasLargeCut_iso e

end Problem

end DescriptiveComplexity
