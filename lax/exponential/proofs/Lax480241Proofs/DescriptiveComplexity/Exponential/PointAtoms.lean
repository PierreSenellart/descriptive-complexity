/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Rounds
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

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (replicate replicateAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# The atoms of the translation

An atom of a sentence over an expansion says one of three things about the
points its variables hold: that a relation of the expanded vocabulary holds of
them, that two of them are equal, or that one is below another. This file writes
each of those as a sentence of the quantifier prefix, and proves it right.

All three follow one pattern. The corresponding sentence of the expansion –
`DescriptiveComplexity.ExpExpansion.relSentence`,
`DescriptiveComplexity.SOBlock.eqAssignF`,
`DescriptiveComplexity.ExpExpansion.ordSentence` – is indexed by a **static**
tuple of tags, because everywhere else in this development a tag is chosen at
formula-construction time. Here the tags are *guessed*, so the sentence appears
once per tuple of tags, guarded by the tag bits of the rounds involved
(`DescriptiveComplexity.ExpExpansion.roundTagBitF`). Finitely many tuples, so
the disjunction is a `DescriptiveComplexity.listSup`; exactly one bit per round
is set, so exactly one disjunct can fire.

Equality is the exception and is cheaper: rather than a disjunction over tag
pairs it compares the tag bits round by round, which says the tags agree without
naming them.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The rounds of the prefix that hold a given tuple of points. -/
def roundAssign (pts : Fin m → X.Map A) : Fin m → X.pointBlock.Assignment A :=
  fun i => SOBlock.tagAssign (pts i).1.1 (pts i).1.2

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundAssign)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The structure the kernel of the translation is realized against. -/
@[instance_reducible]
noncomputable def prefixStructure (pts : Fin m → X.Map A) :
    ((L.sum Language.order).sum (repMerged X.pointBlock m).lang).Structure A :=
  (repMerged X.pointBlock m).structure₁ (L := L.sum Language.order)
    (repBlockAssign X.pointBlock A m (roundAssign pts))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (prefixStructure)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The tag bits of a round -/

variable (X m) in
/-- The atom “round `i` carries the tag `t`”: the tag bit of the guessed point,
read at that round. -/
noncomputable def roundTagBitF (i : Fin m) (t : X.Tag) :
    ((L.sum Language.order).sum (repMerged X.pointBlock m).lang).Sentence :=
  (roundOneLHom i X).onSentence (SOBlock.tagBitF X.B X.Tag t)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundTagBitF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
theorem realize_roundTagBitF (pts : Fin m → X.Map A) (i : Fin m) (t : X.Tag) :
    (@Sentence.Realize _ A (prefixStructure pts) (roundTagBitF X m i t) ↔ t = (pts i).1.1) :=
  (realize_roundOneLHom i X (roundAssign pts) _).trans
    (SOBlock.realize_tagBitF (L := L.sum Language.order) (roundAssign pts i) t)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_roundTagBitF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable (X m) in
/-- The guard “round `i` holds a point of the expanded universe”, read at that
round: what a peeled quantifier carries. -/
noncomputable def roundPointGuardF (i : Fin m) :
    ((L.sum Language.order).sum (repMerged X.pointBlock m).lang).Sentence :=
  (roundOneLHom i X).onSentence X.pointGuardF

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundPointGuardF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
theorem realize_roundPointGuardF (ρs : Fin m → X.pointBlock.Assignment A) (i : Fin m) :
    (@Sentence.Realize _ A
        ((repMerged X.pointBlock m).structure₁ (L := L.sum Language.order)
          (repBlockAssign X.pointBlock A m ρs))
        (roundPointGuardF X m i) ↔
      ∃ (t : X.Tag) (ρ : X.B.Assignment A),
        ρs i = SOBlock.tagAssign t ρ ∧ Lax480241.Expansions.ExpExpansion.DomHolds (X := X) (t, ρ)) :=
  (realize_roundOneLHom i X ρs _).trans (realize_pointGuardF (ρs i))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_roundPointGuardF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### Equality of two points -/

variable (X m) in
/-- The atom “the points of rounds `i₀` and `i₁` are equal”: their tag bits
agree round by round, and their assignments hold of the same atoms. -/
noncomputable def pointEqF (i₀ i₁ : Fin m) :
    ((L.sum Language.order).sum (repMerged X.pointBlock m).lang).Sentence :=
  listInf ((finEnum X.Tag).map fun t => roundTagBitF X m i₀ t ⇔ roundTagBitF X m i₁ t) ⊓
    (roundLHom ![i₀, i₁] X).onSentence (X.B.eqAssignF (L := L))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pointEqF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] in
theorem realize_pointEqF (pts : Fin m → X.Map A) (i₀ i₁ : Fin m) :
    (@Sentence.Realize _ A (prefixStructure pts) (pointEqF X m i₀ i₁) ↔ pts i₀ = pts i₁) := by
  let := prefixStructure pts
  rw [pointEqF, Sentence.Realize, Formula.realize_inf, realize_listInf]
  have hassign :
      (@Sentence.Realize _ A (prefixStructure pts)
          ((roundLHom ![i₀, i₁] X).onSentence (X.B.eqAssignF (L := L))) ↔
        (pts i₀).1.2 = (pts i₁).1.2) := by
    refine (realize_roundLHom ![i₀, i₁] X (roundAssign pts) _).trans ?_
    refine (X.B.realize_eqAssignF _).trans ?_
    exact ⟨fun h => X.B.atomSet_injective h, fun h => congrArg _ h⟩
  constructor
  · rintro ⟨htag, hass⟩
    refine map_ext ?_ (hassign.mp hass)
    have h := htag _ (List.mem_map.mpr ⟨(pts i₀).1.1, mem_finEnum _, rfl⟩)
    rw [Formula.realize_iff] at h
    exact (realize_roundTagBitF pts i₁ (pts i₀).1.1).mp
      (h.mp ((realize_roundTagBitF pts i₀ (pts i₀).1.1).mpr rfl))
  · intro h
    refine ⟨fun ψ hψ => ?_, hassign.mpr (congrArg (fun x => x.1.2) h)⟩
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_iff]
    exact (realize_roundTagBitF pts i₀ t).trans
      ((by rw [h] : (t = (pts i₀).1.1) ↔ (t = (pts i₁).1.1)).trans
        (realize_roundTagBitF pts i₁ t).symm)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_pointEqF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### A relation of the expanded vocabulary -/

variable (X m) in
/-- The atom “the relation `r` holds of the points of the rounds `idx`”: one
disjunct per tuple of tags, guarded by the tag bits of those rounds. -/
noncomputable def pointRelF {k : ℕ} (r : X.E.Relations k) (idx : Fin k → Fin m) :
    ((L.sum Language.order).sum (repMerged X.pointBlock m).lang).Sentence :=
  listSup ((finEnum (Fin k → X.Tag)).map fun τ =>
    listInf ((List.finRange k).map fun j => roundTagBitF X m (idx j) (τ j)) ⊓
      (roundLHom idx X).onSentence (X.relSentence r τ))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pointRelF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
theorem realize_pointRelF (pts : Fin m → X.Map A) {k : ℕ} (r : X.E.Relations k)
    (idx : Fin k → Fin m) :
    (@Sentence.Realize _ A (prefixStructure pts) (pointRelF X m r idx) ↔
      RelMap r fun j => pts (idx j)) := by
  let := prefixStructure pts
  have hbody : ∀ τ : Fin k → X.Tag,
      (@Sentence.Realize _ A (prefixStructure pts)
          ((roundLHom idx X).onSentence (X.relSentence r τ)) ↔
        @Sentence.Realize _ A
          ((X.B.replicate k).structure₁ (L := L.sum Language.order)
            (X.B.replicateAssign fun j => (pts (idx j)).1.2)) (X.relSentence r τ)) :=
    fun τ => realize_roundLHom idx X (roundAssign pts) _
  rw [pointRelF, Sentence.Realize, realize_listSup, relMap_map]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_inf, realize_listInf] at hr
    obtain ⟨htags, hrel⟩ := hr
    have hτ : τ = fun j => (pts (idx j)).1.1 := by
      funext j
      exact (realize_roundTagBitF pts (idx j) (τ j)).mp
        (htags _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
    rw [hτ] at hrel
    exact (hbody _).mp hrel
  · intro h
    refine ⟨_, List.mem_map.mpr ⟨fun j => (pts (idx j)).1.1, mem_finEnum _, rfl⟩, ?_⟩
    rw [Formula.realize_inf, realize_listInf]
    refine ⟨fun ψ hψ => ?_, (hbody _).mpr h⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    exact (realize_roundTagBitF pts (idx j) _).mpr rfl

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_pointRelF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The order on two points -/

variable (X m) in
/-- The atom “the point of round `i₀` is below that of round `i₁`”: one disjunct
per pair of tags, guarded by the two tag bits. -/
noncomputable def pointLeF (i₀ i₁ : Fin m) :
    ((L.sum Language.order).sum (repMerged X.pointBlock m).lang).Sentence :=
  listSup ((finEnum (X.Tag × X.Tag)).map fun p =>
    (roundTagBitF X m i₀ p.1 ⊓ roundTagBitF X m i₁ p.2) ⊓
      (roundLHom ![i₀, i₁] X).onSentence (X.ordSentence p.1 p.2))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pointLeF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

theorem realize_pointLeF (pts : Fin m → X.Map A) (i₀ i₁ : Fin m) :
    (@Sentence.Realize _ A (prefixStructure pts) (pointLeF X m i₀ i₁) ↔
      (X.mapLinearOrder A).le (pts i₀) (pts i₁)) := by
  let := prefixStructure pts
  have hbody : ∀ t₁ t₂ : X.Tag,
      (@Sentence.Realize _ A (prefixStructure pts)
          ((roundLHom ![i₀, i₁] X).onSentence (X.ordSentence t₁ t₂)) ↔
        (X.pointLinearOrder A).le (t₁, (pts i₀).1.2) (t₂, (pts i₁).1.2)) := fun t₁ t₂ =>
    (realize_roundLHom ![i₀, i₁] X (roundAssign pts) _).trans
      (X.realize_ordSentence A t₁ t₂ _)
  rw [pointLeF, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨⟨t₁, t₂⟩, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_inf, Formula.realize_inf] at hr
    obtain ⟨⟨hb₀, hb₁⟩, hord⟩ := hr
    have h₀ : t₁ = (pts i₀).1.1 := (realize_roundTagBitF pts i₀ t₁).mp hb₀
    have h₁ : t₂ = (pts i₁).1.1 := (realize_roundTagBitF pts i₁ t₂).mp hb₁
    subst h₀; subst h₁
    exact (hbody _ _).mp hord
  · intro h
    refine ⟨_, List.mem_map.mpr ⟨((pts i₀).1.1, (pts i₁).1.1), mem_finEnum _, rfl⟩, ?_⟩
    rw [Formula.realize_inf, Formula.realize_inf]
    exact ⟨⟨(realize_roundTagBitF pts i₀ _).mpr rfl, (realize_roundTagBitF pts i₁ _).mpr rfl⟩,
      (hbody _ _).mpr h⟩

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_pointLeF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


