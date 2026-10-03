/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Problems.Feedback.Defs
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
# Max Cut: the problem

MAX CUT ([Karp 1972][karp1972reducibility]): is there a set `S` of vertices
such that at least `k` edges have exactly one endpoint in `S`? Here, as
everywhere in this library, the threshold `k` is carried by the instance in
the *unary representation* of `Lax799700Proofs.DescriptiveComplexity.Numbers.Unary` – and,
since a cut can have quadratically many edges, at arity 2: `k` is the number
of pairs in the marked relation of
`FirstOrder.Language.markedArcGraph`, the vocabulary introduced for Feedback Arc Set
and reused here unchanged.

The cut itself is read as a set of *ordered* pairs
(`Lax799700Proofs.DescriptiveComplexity.CutRel`): the pairs `(u, v)` with `u` adjacent to `v`, `u`
inside `S` and `v` outside. On a symmetric adjacency relation this counts
every cut edge exactly once, which is what makes the threshold comparison the
intended one without any division by two.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Semantics

variable {A : Type}

/-- The max-cut property, with the threshold certified by an injection of the
marked pairs into the cut – the shape the second-order definition guesses. -/
theorem maxCutOn_iff_certificate [Finite A] (Adjp : A → A → Prop) (Kp : A → A → Prop) :
    Lax799700.MaxCut.MaxCutOn Adjp Kp ↔ ∃ S : A → Prop,
      Nonempty ({p : A × A // Kp p.1 p.2} ↪ {p : A × A // Lax799700.MaxCut.CutRel Adjp S p.1 p.2}) :=
  exists_congr fun S => (nonempty_embedding_iff_ncard_le₂ Kp (Lax799700.MaxCut.CutRel Adjp S)).symm

variable {B : Type}

/-- `MaxCutOn` transports along an equivalence commuting with the two
relations. -/
theorem MaxCutOn.of_equiv (u : B ≃ A) {AdjB KB : B → B → Prop} {AdjA KA : A → A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b'))
    (hK : ∀ b b', KB b b' ↔ KA (u b) (u b')) (h : Lax799700.MaxCut.MaxCutOn AdjB KB) :
    Lax799700.MaxCut.MaxCutOn AdjA KA := by
  obtain ⟨S, hcard⟩ := h
  refine ⟨fun a => S (u.symm a), ?_⟩
  rw [← ncard_setOf_equiv₂ u hK,
    ← ncard_setOf_equiv₂ (RB := Lax799700.MaxCut.CutRel AdjB S)
      (RA := Lax799700.MaxCut.CutRel AdjA fun a => S (u.symm a)) u (fun b b' => by simp [Lax799700.MaxCut.CutRel, hadj])]
  exact hcard

end Semantics

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700.MaxCut.MaxCutOn

export Lax799700Proofs.DescriptiveComplexity.MaxCutOn (of_equiv)

end Lax799700.MaxCut.MaxCutOn

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Semantics

variable {A : Type}

variable {B : Type}

private theorem maxCut_symm (u : B ≃ A) {RB : B → B → Prop} {RA : A → A → Prop}
    (h : ∀ b b', RB b b' ↔ RA (u b) (u b')) (a a' : A) :
    RA a a' ↔ RB (u.symm a) (u.symm a') := by
  rw [h]
  simp

/-- `MaxCutOn` transports along an equivalence, iff version. -/
theorem MaxCutOn.equiv_iff (u : B ≃ A) {AdjB KB : B → B → Prop} {AdjA KA : A → A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b'))
    (hK : ∀ b b', KB b b' ↔ KA (u b) (u b')) :
    Lax799700.MaxCut.MaxCutOn AdjB KB ↔ Lax799700.MaxCut.MaxCutOn AdjA KA :=
  ⟨MaxCutOn.of_equiv u hadj hK,
    MaxCutOn.of_equiv u.symm (maxCut_symm u hadj) (maxCut_symm u hK)⟩

end Semantics

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700.MaxCut.MaxCutOn

export Lax799700Proofs.DescriptiveComplexity.MaxCutOn (equiv_iff)

end Lax799700.MaxCut.MaxCutOn

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Semantics

variable {A : Type}

variable {B : Type}

end Semantics

section Problem

/-- Having a large cut is isomorphism-invariant. -/
theorem hasLargeCut_iso {A B : Type} [Lax799700.Feedback.markedArcGraph.Structure A]
    [Lax799700.Feedback.markedArcGraph.Structure B] (e : A ≃[Lax799700.Feedback.markedArcGraph] B) :
    Lax799700.MaxCut.HasLargeCut A ↔ Lax799700.MaxCut.HasLargeCut B :=
  and_congr e.toEquiv.finite_iff
    (MaxCutOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e Lax799700.Feedback.magAdj a b)
      fun a b => relMap_equiv₂ e Lax799700.Feedback.magMarked a b)

/-- MAX CUT, as a problem on arc-marked graphs: is there a set of vertices
whose cut is at least as large as the marked relation? -/
def MaxCut : Lax904597.Problems.DecisionProblem Lax799700.Feedback.markedArcGraph where
  Holds := fun A inst => @Lax799700.MaxCut.HasLargeCut A inst
  iso_invariant := fun e => hasLargeCut_iso e

end Problem

end Lax799700Proofs.DescriptiveComplexity


