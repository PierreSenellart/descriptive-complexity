/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Counting.Relativized
import Mathlib.SetTheory.Cardinal.Finite
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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

namespace Lax794877Proofs.DescriptiveComplexity.PolyTerm
end Lax794877Proofs.DescriptiveComplexity.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity.PostTerm
end Lax794877Proofs.DescriptiveComplexity.PostTerm

namespace Lax859101.OneCallReductions
end Lax859101.OneCallReductions

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax859101.OneCallReductions (PolyTerm PostTerm)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Post-processing terms

The arithmetic a counting reduction may apply to the answer of its one oracle
call (`DescriptiveComplexity.Counting.Reduction`). Two layers, kept apart so
that every number written stays of polynomially many bits:

* `DescriptiveComplexity.PolyTerm`: numerals, **definable cardinalities** – the
  number of tagged tuples of the instance satisfying first-order formulas over
  the ordered expansion – sums and products. Its values are polynomial in the
  size of the instance.
* `DescriptiveComplexity.PostTerm`: the oracle's answer, a polynomial term, a
  power of two *whose exponent is a polynomial term*, sums, products,
  truncated differences, quotients and remainders.

So a post-processing term is a fixed arithmetic expression over the oracle's
answer and first-order definable counts: it can be evaluated in polynomial
time, and it does no counting of its own beyond tuples of the instance.

Both layers are **pulled back** along a relativized interpretation
(`DescriptiveComplexity.PolyTerm.pull`, `DescriptiveComplexity.PostTerm.pull`):
a definable cardinality of the interpreted structure is a definable
cardinality of the instance. A cardinality is stored as the universe of a
relativized interpretation into the empty vocabulary, so the pullback is the
composition of relativized interpretations and needs nothing new. With
substitution for the oracle's answer (`DescriptiveComplexity.PostTerm.subst`),
this is what makes one-call reductions compose.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Polynomial terms -/

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The relativized interpretation into the empty vocabulary whose universe
is the set of tuples satisfying a formula. -/
def cardInterp {k : ℕ} (φ : (L.sum Language.order).Formula (Fin k)) :
    Lax904597.Relativized.RelFOInterpretation (L.sum Language.order) Language.empty Unit k where
  relFormula := fun R => isEmptyElim R
  domFormula := fun _ => φ

end PolyTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PolyTerm

export Lax794877Proofs.DescriptiveComplexity.PolyTerm (cardInterp)

end Lax859101.OneCallReductions.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The number of `k`-tuples satisfying a first-order formula over the ordered
expansion. -/
def count {k : ℕ} (φ : (L.sum Language.order).Formula (Fin k)) : Lax859101.OneCallReductions.PolyTerm L :=
  Lax859101.OneCallReductions.PolyTerm.card (cardInterp φ)

end PolyTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PolyTerm

export Lax794877Proofs.DescriptiveComplexity.PolyTerm (count)

end Lax859101.OneCallReductions.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

theorem eval_count (A : Type) [L.Structure A] [LinearOrder A] {k : ℕ}
    (φ : (L.sum Language.order).Formula (Fin k)) :
    (count φ).eval A = Nat.card {w : Fin k → A // φ.Realize w} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.2, x.2⟩
      invFun := fun w => ⟨((), w.1), w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end PolyTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PolyTerm

export Lax794877Proofs.DescriptiveComplexity.PolyTerm (eval_count)

end Lax859101.OneCallReductions.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The number of elements satisfying a first-order formula over the ordered
expansion, as a cardinality of a set of elements. -/
theorem eval_count_one (A : Type) [L.Structure A] [LinearOrder A]
    (φ : (L.sum Language.order).Formula (Fin 1)) :
    (count φ).eval A = Nat.card {a : A // φ.Realize fun _ => a} := by
  rw [eval_count]
  exact Nat.card_congr
    { toFun := fun w => ⟨w.1 0, by
        have h : (fun _ => w.1 0) = w.1 := funext fun j => congrArg w.1 (Subsingleton.elim _ _)
        rw [h]
        exact w.2⟩
      invFun := fun a => ⟨fun _ => a.1, a.2⟩
      left_inv := fun w => Subtype.ext (funext fun j => congrArg w.1 (Subsingleton.elim _ _))
      right_inv := fun _ => rfl }

end PolyTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PolyTerm

export Lax794877Proofs.DescriptiveComplexity.PolyTerm (eval_count_one)

end Lax859101.OneCallReductions.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The number of elements of the instance. -/
def univ : Lax859101.OneCallReductions.PolyTerm L :=
  count (⊤ : (L.sum Language.order).Formula (Fin 1))

end PolyTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PolyTerm

export Lax794877Proofs.DescriptiveComplexity.PolyTerm (univ)

end Lax859101.OneCallReductions.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

theorem eval_univ (A : Type) [L.Structure A] [LinearOrder A] :
    (univ : Lax859101.OneCallReductions.PolyTerm L).eval A = Nat.card A := by
  rw [univ, eval_count_one]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => Formula.realize_top.mpr trivial)

end PolyTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PolyTerm

export Lax794877Proofs.DescriptiveComplexity.PolyTerm (eval_univ)

end Lax859101.OneCallReductions.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

section Pull

variable [L₂.IsRelational] {T : Type} [LinearOrder T] [Finite T] {d : ℕ}

/-- The pullback of a polynomial term along a relativized interpretation: a
definable cardinality of the interpreted structure, ordered lexicographically,
is the size of the universe of a composite interpretation. -/
noncomputable def pull (I : Lax904597.Relativized.RelFOInterpretation (L₁.sum Language.order) L₂ T d) :
    Lax859101.OneCallReductions.PolyTerm L₂ → Lax859101.OneCallReductions.PolyTerm L₁
  | Lax859101.OneCallReductions.PolyTerm.num k => Lax859101.OneCallReductions.PolyTerm.num k
  | Lax859101.OneCallReductions.PolyTerm.card J => Lax859101.OneCallReductions.PolyTerm.card (J.compRel I.ordExtendRel)
  | Lax859101.OneCallReductions.PolyTerm.add p q => Lax859101.OneCallReductions.PolyTerm.add ((pull I p)) ((pull I q))
  | Lax859101.OneCallReductions.PolyTerm.mul p q => Lax859101.OneCallReductions.PolyTerm.mul ((pull I p)) ((pull I q))

end Pull

end PolyTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PolyTerm

export Lax794877Proofs.DescriptiveComplexity.PolyTerm (pull)

end Lax859101.OneCallReductions.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

section Pull

variable [L₂.IsRelational] {T : Type} [LinearOrder T] [Finite T] {d : ℕ}

/-- A pulled-back polynomial term has, at the instance, the value of the
original term at the interpreted structure. -/
theorem eval_pull (I : Lax904597.Relativized.RelFOInterpretation (L₁.sum Language.order) L₂ T d)
    (A : Type) [L₁.Structure A] [LinearOrder A] (p : Lax859101.OneCallReductions.PolyTerm L₂) :
    (p.pull I).eval A =
      (letI := I.mapRelLinearOrder A; p.eval (I.MapRel A)) := by
  let := I.mapRelLinearOrder A
  induction p with
  | num k => rfl
  | card J =>
    have e1 := I.ordExtendRelLEquiv A
    have e2 := J.mapRelLEquiv e1
    have e3 := J.compLEquivRel I.ordExtendRel (A := A)
    exact Nat.card_congr (e2.comp e3).toEquiv
  | add p q hp hq => exact congrArg₂ (· + ·) hp hq
  | mul p q hp hq => exact congrArg₂ (· * ·) hp hq

end Pull

end PolyTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PolyTerm

export Lax794877Proofs.DescriptiveComplexity.PolyTerm (eval_pull)

end Lax859101.OneCallReductions.PolyTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

section Pull

variable [L₂.IsRelational] {T : Type} [LinearOrder T] [Finite T] {d : ℕ}

end Pull

end PolyTerm

/-! ### Post-processing terms -/

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- Substitution of a term for the answer of the oracle. -/
def subst : Lax859101.OneCallReductions.PostTerm L → Lax859101.OneCallReductions.PostTerm L → Lax859101.OneCallReductions.PostTerm L
  | Lax859101.OneCallReductions.PostTerm.oracle, u => u
  | Lax859101.OneCallReductions.PostTerm.poly p, _ => Lax859101.OneCallReductions.PostTerm.poly p
  | Lax859101.OneCallReductions.PostTerm.pow2 p, _ => Lax859101.OneCallReductions.PostTerm.pow2 p
  | Lax859101.OneCallReductions.PostTerm.add s t, u => Lax859101.OneCallReductions.PostTerm.add ((subst s) u) ((subst t) u)
  | Lax859101.OneCallReductions.PostTerm.mul s t, u => Lax859101.OneCallReductions.PostTerm.mul ((subst s) u) ((subst t) u)
  | Lax859101.OneCallReductions.PostTerm.sub s t, u => Lax859101.OneCallReductions.PostTerm.sub ((subst s) u) ((subst t) u)
  | Lax859101.OneCallReductions.PostTerm.div s t, u => Lax859101.OneCallReductions.PostTerm.div ((subst s) u) ((subst t) u)
  | Lax859101.OneCallReductions.PostTerm.mod s t, u => Lax859101.OneCallReductions.PostTerm.mod ((subst s) u) ((subst t) u)

end PostTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PostTerm

export Lax794877Proofs.DescriptiveComplexity.PostTerm (subst)

end Lax859101.OneCallReductions.PostTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

theorem eval_subst (A : Type) [L.Structure A] [LinearOrder A] (c : ℕ) (s u : Lax859101.OneCallReductions.PostTerm L) :
    (s.subst u).eval A c = s.eval A (u.eval A c) := by
  induction s with
  | oracle => rfl
  | poly p => rfl
  | pow2 p => rfl
  | add s t hs ht => exact congrArg₂ (· + ·) hs ht
  | mul s t hs ht => exact congrArg₂ (· * ·) hs ht
  | sub s t hs ht => exact congrArg₂ (· - ·) hs ht
  | div s t hs ht => exact congrArg₂ (· / ·) hs ht
  | mod s t hs ht => exact congrArg₂ (· % ·) hs ht

end PostTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PostTerm

export Lax794877Proofs.DescriptiveComplexity.PostTerm (eval_subst)

end Lax859101.OneCallReductions.PostTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

section Pull

variable [L₂.IsRelational] {T : Type} [LinearOrder T] [Finite T] {d : ℕ}

/-- The pullback of a post-processing term along a relativized interpretation,
its polynomial terms being pulled back. -/
noncomputable def pull (I : Lax904597.Relativized.RelFOInterpretation (L₁.sum Language.order) L₂ T d) :
    Lax859101.OneCallReductions.PostTerm L₂ → Lax859101.OneCallReductions.PostTerm L₁
  | Lax859101.OneCallReductions.PostTerm.oracle => Lax859101.OneCallReductions.PostTerm.oracle
  | Lax859101.OneCallReductions.PostTerm.poly p => Lax859101.OneCallReductions.PostTerm.poly (p.pull I)
  | Lax859101.OneCallReductions.PostTerm.pow2 p => Lax859101.OneCallReductions.PostTerm.pow2 (p.pull I)
  | Lax859101.OneCallReductions.PostTerm.add s t => Lax859101.OneCallReductions.PostTerm.add ((pull I s)) ((pull I t))
  | Lax859101.OneCallReductions.PostTerm.mul s t => Lax859101.OneCallReductions.PostTerm.mul ((pull I s)) ((pull I t))
  | Lax859101.OneCallReductions.PostTerm.sub s t => Lax859101.OneCallReductions.PostTerm.sub ((pull I s)) ((pull I t))
  | Lax859101.OneCallReductions.PostTerm.div s t => Lax859101.OneCallReductions.PostTerm.div ((pull I s)) ((pull I t))
  | Lax859101.OneCallReductions.PostTerm.mod s t => Lax859101.OneCallReductions.PostTerm.mod ((pull I s)) ((pull I t))

end Pull

end PostTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PostTerm

export Lax794877Proofs.DescriptiveComplexity.PostTerm (pull)

end Lax859101.OneCallReductions.PostTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

section Pull

variable [L₂.IsRelational] {T : Type} [LinearOrder T] [Finite T] {d : ℕ}

/-- A pulled-back post-processing term has, at the instance, the value of the
original term at the interpreted structure. -/
theorem eval_pull (I : Lax904597.Relativized.RelFOInterpretation (L₁.sum Language.order) L₂ T d)
    (A : Type) [L₁.Structure A] [LinearOrder A] (c : ℕ) (s : Lax859101.OneCallReductions.PostTerm L₂) :
    (s.pull I).eval A c =
      (letI := I.mapRelLinearOrder A; s.eval (I.MapRel A) c) := by
  let := I.mapRelLinearOrder A
  induction s with
  | oracle => rfl
  | poly p => exact p.eval_pull I A
  | pow2 p => exact congrArg (2 ^ ·) (p.eval_pull I A)
  | add s t hs ht => exact congrArg₂ (· + ·) hs ht
  | mul s t hs ht => exact congrArg₂ (· * ·) hs ht
  | sub s t hs ht => exact congrArg₂ (· - ·) hs ht
  | div s t hs ht => exact congrArg₂ (· / ·) hs ht
  | mod s t hs ht => exact congrArg₂ (· % ·) hs ht

end Pull

end PostTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.PostTerm

export Lax794877Proofs.DescriptiveComplexity.PostTerm (eval_pull)

end Lax859101.OneCallReductions.PostTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

section Pull

variable [L₂.IsRelational] {T : Type} [LinearOrder T] [Finite T] {d : ℕ}

end Pull

end PostTerm

end Lax794877Proofs.DescriptiveComplexity


