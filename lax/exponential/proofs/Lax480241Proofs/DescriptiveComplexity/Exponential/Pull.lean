/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Expansion
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (replicate replicateAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Pulling an exponential expansion back through an interpretation

**An interpretation followed by an expansion is an expansion.** Given an
ordered first-order interpretation `I` of `L'` in `L` and an exponential
expansion `X` of `L'`-structures, the composite `A ↦ X.Map (I.Map A)` is again
an exponential expansion of `L`-structures,
`DescriptiveComplexity.ExpExpansion.pullOrdered`. This is what makes
`DescriptiveComplexity.ExpDefinable` closed under (ordered) first-order
reductions, hence `DescriptiveComplexity.ComplexityClass.exp` a genuine
complexity class; and, read the other way round, it is the formal content of
the side condition the succinctness literature attaches to its upgrade theorem
– that the reduction must act on the *description* rather than on the described
instance.

Three existing pieces do the work, and no new mathematics is needed.

* **The order of the interpreted universe is definable**
  (`DescriptiveComplexity.FOInterpretation.ordExtend`): an expansion's
  sentences see the order of the structure they expand, so pulling them back
  through `I` requires `I` to define that order. It does, lexicographically,
  and `DescriptiveComplexity.FOInterpretation.ordExtendLEquiv` says the
  extended interpretation produces exactly the interpreted structure with the
  lexicographic order.
* **A block pulls back through an interpretation**
  (`DescriptiveComplexity.SOBlock.pull`,
  `DescriptiveComplexity.FOInterpretation.extendSO`): an `a`-ary relation
  variable on `Tag × A^d` becomes one `(a·d)`-ary relation variable on `A` per
  tuple of tags, and assignments correspond bijectively
  (`DescriptiveComplexity.SOBlock.pullAssignEquiv`).
* **Replication commutes with that pullback**
  (`DescriptiveComplexity.SOBlock.homAssign_replicatePullHom`), definitionally,
  which is why the defining sentences of the composite are the pulled ones read
  through a renaming of relation variables and nothing more.

The chain of transports is the one
`DescriptiveComplexity.SecondOrderTransitiveClosurePull` runs for an
`DescriptiveComplexity.SOTCSpec`, stated here over an arbitrary block so that
one lemma – `DescriptiveComplexity.ExpExpansion.realize_extendSO_pullSentence`
– serves both the domain sentence (one copy of the block) and every defining
sentence (as many copies as the symbol has arguments).
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L L' : Language.{0, 0}} [L'.IsRelational]

variable {T : Type} [Finite T] [LinearOrder T] {d : ℕ}

variable (X : Lax480241.Expansions.ExpExpansion L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' T d)

variable (A : Type) [L.Structure A] [LinearOrder A]

/-! ### Realizing a pulled block-expanded sentence -/

/-- **The transport lemma.** A sentence over the ordered vocabulary of `L'`
expanded by a block, read in the interpreted universe with the block
interpreted by `ρ`, says in `A` exactly what its pullback says with the pulled
block interpreted by the pulled assignment.

The three steps are the three ingredients of the module docstring: pull the
sentence through the block-extended interpretation, identify the interpreted
structure of the block extension with the block expansion of the interpreted
structure, and identify the order the extended interpretation defines with the
lexicographic order of
`DescriptiveComplexity.FOInterpretation.mapLinearOrder`. -/
theorem realize_extendSO_pullSentence (Bk : Lax904597.SecondOrder.SOBlock)
    (φ : ((L'.sum Language.order).sum Bk.lang).Sentence) (ρ : Bk.Assignment (I.Map A)) :
    letI := I.mapLinearOrder A
    @Sentence.Realize _ A
        ((Bk.pull T d).structure₁ (L := L.sum Language.order) (Bk.pullAssign ρ))
        ((I.ordExtendSO Bk).pullSentence φ) ↔
      @Sentence.Realize _ (I.Map A) (Bk.structure₁ (L := L'.sum Language.order) ρ) φ := by
  let := I.mapLinearOrder A
  let := (Bk.pull T d).structure₁ (L := L.sum Language.order) (Bk.pullAssign ρ)
  exact ((I.ordExtendSO Bk).realize_pullSentence φ A).trans
    ((realize_sentence_of_equiv (I.ordExtend.extendSOEquiv Bk A ρ) φ).trans
      (realize_sentence_of_equiv (Bk.extendEquiv (I.ordExtendLEquiv A) ρ) φ))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_extendSO_pullSentence)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L L' : Language.{0, 0}} [L'.IsRelational]

variable {T : Type} [Finite T] [LinearOrder T] {d : ℕ}

variable (X : Lax480241.Expansions.ExpExpansion L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' T d)

variable (A : Type) [L.Structure A] [LinearOrder A]

/-! ### The pulled expansion -/

variable [Nonempty T]

/-- **An interpretation followed by an expansion is an expansion**: the tags
and the expanded vocabulary are unchanged, the block is pulled back, and every
sentence is pulled back through the order-extended, block-extended
interpretation – the defining sentences also being read through the renaming of
relation variables that identifies the pullback of a replicated block with the
replication of the pulled block. -/
noncomputable def pullOrdered : Lax480241.Expansions.ExpExpansion L where
  Tag := X.Tag
  B := X.B.pull T d
  E := X.E
  dom t := (I.ordExtendSO X.B).pullSentence (X.dom t)
  relSentence {n} r τ :=
    (LHom.sumMap (LHom.id (L.sum Language.order)) (X.B.replicatePullLHom T d n)).onSentence
      ((I.ordExtendSO (X.B.replicate n)).pullSentence (X.relSentence r τ))
  dom_nonempty := by
    intro A _ _ _ _
    let := I.mapLinearOrder A
    have : Finite (I.Map A) := I.map_finite A
    have : Nonempty (I.Map A) := I.map_nonempty A
    obtain ⟨t, ρ, h⟩ := X.dom_nonempty (I.Map A)
    exact ⟨t, X.B.pullAssign ρ,
      (realize_extendSO_pullSentence I A X.B (X.dom t) ρ).mpr h⟩

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pullOrdered)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L L' : Language.{0, 0}} [L'.IsRelational]

variable {T : Type} [Finite T] [LinearOrder T] {d : ℕ}

variable (X : Lax480241.Expansions.ExpExpansion L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' T d)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable [Nonempty T]

/-! ### The universes and the relations match

The pulled expansion has the *same* expanded vocabulary as the original, by
definition; but `DescriptiveComplexity.ExpExpansion.pullOrdered` is not
reducible, so the expanded structure has to be named rather than found by
instance search. `DescriptiveComplexity.ExpExpansion.pullOrderedStructure` is
that name, and it is the very term a goal about `X.pullOrdered I` elaborates
to. -/

/-- The expanded structure of the pulled expansion, at the vocabulary of the
original expansion – the two vocabularies being equal by definition. -/
@[instance_reducible]
noncomputable def pullOrderedStructure : X.E.Structure ((X.pullOrdered I).Map A) :=
  Lax480241.Expansions.ExpExpansion.mapStructure (X.pullOrdered I) A

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pullOrderedStructure)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L L' : Language.{0, 0}} [L'.IsRelational]

variable {T : Type} [Finite T] [LinearOrder T] {d : ℕ}

variable (X : Lax480241.Expansions.ExpExpansion L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' T d)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable [Nonempty T]

/-- The domain condition of the pulled expansion, at the assignment pulled from
the interpreted universe, is the domain condition of the original expansion. -/
theorem domHolds_pullOrdered (t : X.Tag) (ρ : X.B.Assignment (I.Map A)) :
    letI := I.mapLinearOrder A
    Lax480241.Expansions.ExpExpansion.DomHolds (X := X.pullOrdered I) (t, X.B.pullAssign ρ) ↔ Lax480241.Expansions.ExpExpansion.DomHolds (X := X) (t, ρ) :=
  realize_extendSO_pullSentence I A X.B (X.dom t) ρ

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (domHolds_pullOrdered)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L L' : Language.{0, 0}} [L'.IsRelational]

variable {T : Type} [Finite T] [LinearOrder T] {d : ℕ}

variable (X : Lax480241.Expansions.ExpExpansion L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' T d)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable [Nonempty T]

/-- The domain condition of the pulled expansion, read at a base assignment:
the same condition on the assignment it merges to. This is
`DescriptiveComplexity.ExpExpansion.domHolds_pullOrdered` in the direction the
inverse of the universe bijection consumes it, stated at a *variable*
assignment so that the round-trip rewrite happens away from any subtype
coercion. -/
theorem domHolds_pullOrdered_merge (t : X.Tag) (σ : (X.B.pull T d).Assignment A) :
    letI := I.mapLinearOrder A
    Lax480241.Expansions.ExpExpansion.DomHolds (X := X.pullOrdered I) (t, σ) ↔
      Lax480241.Expansions.ExpExpansion.DomHolds (X := X) (A := I.Map A) (t, X.B.mergeAssign σ) := by
  let := I.mapLinearOrder A
  have h := X.domHolds_pullOrdered I A t (X.B.mergeAssign σ)
  rwa [SOBlock.pullAssign_mergeAssign] at h

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (domHolds_pullOrdered_merge)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L L' : Language.{0, 0}} [L'.IsRelational]

variable {T : Type} [Finite T] [LinearOrder T] {d : ℕ}

variable (X : Lax480241.Expansions.ExpExpansion L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' T d)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable [Nonempty T]

/-- **The relations match**: the defining sentence of the pulled expansion, at
the pulled assignments, says what the original defining sentence says of the
points of the expansion of the interpreted structure. -/
theorem relMap_pullOrdered {n : ℕ} (r : X.E.Relations n)
    (ys : Fin n → (letI := I.mapLinearOrder A; X.Map (I.Map A)))
    (h : ∀ i, Lax480241.Expansions.ExpExpansion.DomHolds (X := X.pullOrdered I) ((ys i).1.1, X.B.pullAssign (ys i).1.2)) :
    letI := I.mapLinearOrder A
    letI := X.pullOrderedStructure I A
    RelMap r (fun i => Lax480241.Expansions.ExpExpansion.pt (X := X.pullOrdered I) (ys i).1.1
        (X.B.pullAssign (ys i).1.2) (h i)) ↔ RelMap r ys := by
  let := I.mapLinearOrder A
  let := X.pullOrderedStructure I A
  refine Iff.trans ?_ (realize_extendSO_pullSentence I A (X.B.replicate n)
    (X.relSentence r fun i => (ys i).1.1) (X.B.replicateAssign fun i => (ys i).1.2))
  exact SOBlock.realize_homSentence (X.B.replicatePullHom T d n)
    (X.B.replicatePullHom_arity T d n)
    ((X.B.pull T d).replicateAssign fun i => X.B.pullAssign (ys i).1.2)
    ((I.ordExtendSO (X.B.replicate n)).pullSentence (X.relSentence r fun i => (ys i).1.1))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (relMap_pullOrdered)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L L' : Language.{0, 0}} [L'.IsRelational]

variable {T : Type} [Finite T] [LinearOrder T] {d : ℕ}

variable (X : Lax480241.Expansions.ExpExpansion L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' T d)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable [Nonempty T]

/-- **The expanded universes are isomorphic**: the expansion of the interpreted
structure is the pulled expansion of the base structure.

The bijection is `DescriptiveComplexity.SOBlock.pullAssign` on assignments,
with `DescriptiveComplexity.SOBlock.mergeAssign` as its inverse; the tags are
carried unchanged. -/
noncomputable def pullOrderedLEquiv :
    letI := I.mapLinearOrder A
    letI := X.pullOrderedStructure I A
    X.Map (I.Map A) ≃[X.E] (X.pullOrdered I).Map A :=
  letI := I.mapLinearOrder A
  letI := X.pullOrderedStructure I A
  { toFun := fun y =>
      Lax480241.Expansions.ExpExpansion.pt (X := X.pullOrdered I) y.1.1 (X.B.pullAssign y.1.2)
        ((X.domHolds_pullOrdered I A y.1.1 y.1.2).mpr y.2)
    invFun := fun x =>
      Lax480241.Expansions.ExpExpansion.pt (X := X) x.1.1 (X.B.mergeAssign x.1.2)
        ((X.domHolds_pullOrdered_merge I A x.1.1 x.1.2).mp x.2)
    left_inv := fun y => map_ext rfl (X.B.mergeAssign_pullAssign y.1.2)
    right_inv := fun x => map_ext rfl (X.B.pullAssign_mergeAssign x.1.2)
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun r ys => X.relMap_pullOrdered I A r ys _ }

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pullOrderedLEquiv)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L L' : Language.{0, 0}} [L'.IsRelational]

variable {T : Type} [Finite T] [LinearOrder T] {d : ℕ}

variable (X : Lax480241.Expansions.ExpExpansion L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' T d)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable [Nonempty T]

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


