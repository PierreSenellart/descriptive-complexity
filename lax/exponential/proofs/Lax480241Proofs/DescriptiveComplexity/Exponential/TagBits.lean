/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.OrdExtend
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

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.SOBlock
end Lax480241Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Guessing a point of an expanded universe

The translation lemma (`DescriptiveComplexity.ExpExpansion.exists_translate`) –
*an FO sentence over an expansion is a second-order sentence over the base* –
peels one quantifier at a time into one
second-order block. What that block has to hold is a **point** of the expanded
universe: a tag together with an assignment of the expansion's block.

The assignment half is what a block quantifier already ranges over. The tag half
is the problem: everywhere else in this development a tag is *static*, chosen at
formula-construction time (`relSentence` is indexed by a tuple of tags,
`ordSentence` compares two of them by trichotomy). A quantified point chooses its
tag at *evaluation* time, so the tag has to become part of the guessed object.

The encoding: extend the block by **one arity-0 relation variable per tag**
(`DescriptiveComplexity.SOBlock.withTag`). An arity-0 variable is a bit – the
same observation `DescriptiveComplexity.PSpace`'s docstring makes about finite
control in an SO(TC) walk – so a tag is a bit vector, and
`DescriptiveComplexity.SOBlock.tagGuardF` is the sentence saying exactly one bit
is set. Its correctness
(`DescriptiveComplexity.SOBlock.realize_tagGuardF`) says the guard holds of an
assignment exactly when that assignment *is* a tagged assignment, which is the
form the peeling step consumes.

Nothing here depends on the expansion, only on a block and a finite tag type.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Classical in
/-- An enumeration of a finite type, as a list. (`SOBlock.ivars` is this list at
a block's index type; fold the two together when the translation lands.) -/
noncomputable def finEnum (T : Type) [Finite T] : List T :=
  letI : Fintype T := Fintype.ofFinite T
  (Finset.univ : Finset T).toList

open Classical in
theorem mem_finEnum {T : Type} [Finite T] (t : T) : t ∈ finEnum T := by
  let : Fintype T := Fintype.ofFinite T
  exact Finset.mem_toList.mpr (Finset.mem_univ t)

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

/-! ### The block extended by tag bits -/

/-- A block extended with one **arity-0** relation variable per tag. An arity-0
variable is a bit, so an assignment of this block is an assignment of `B`
together with a bit vector naming a tag.

An `abbrev` deliberately: with a semireducible `def` in between, instance
search cannot see that the arity of a tag variable is `0`, and `Fin 0 → A`
stops being recognized as a subsingleton. -/
abbrev withTag : Lax904597.SecondOrder.SOBlock where
  ι := T ⊕ B.ι
  arity := Sum.elim (fun _ => 0) B.arity

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (withTag)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

/-- The assignment of the extended block carrying a given tag and a given
assignment: the bit of `t'` says `t' = t`. -/
def tagAssign (t : T) (ρ : B.Assignment A) : (B.withTag T).Assignment A :=
  fun i => match i with
    | Sum.inl t' => fun _ => t' = t
    | Sum.inr j => ρ j

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (tagAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

/-- A tag variable has arity `0`, so its argument tuple is the empty one. Stated
as an instance because `Fin ((B.withTag T).arity (Sum.inl t))` is not
syntactically `Fin 0`, and the `Subsingleton`/`Inhabited` facts the correctness
proof needs are found through it. -/
instance instIsEmptyTagArity {t : T} : IsEmpty (Fin ((B.withTag T).arity (Sum.inl t))) :=
  inferInstanceAs (IsEmpty (Fin 0))

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (instIsEmptyTagArity)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

/-- The assignment an extended assignment carries, forgetting the tag bits. -/
def dropTag (σ : (B.withTag T).Assignment A) : B.Assignment A :=
  fun j => σ (Sum.inr j)

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (dropTag)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

@[simp]
theorem dropTag_tagAssign (t : T) (ρ : B.Assignment A) :
    dropTag (tagAssign (B := B) t ρ) = ρ :=
  rfl

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (dropTag_tagAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

/-! ### The exactly-one guard -/

variable (B T) in
/-- The atom “the bit of the tag `t` is set”. -/
noncomputable def tagBitF (t : T) : (L.sum (B.withTag T).lang).Formula Empty :=
  Relations.formula (Sum.inr (⟨Sum.inl t, rfl⟩ : (B.withTag T).lang.Relations 0)) Fin.elim0

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (tagBitF)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

open Classical in
variable (B T) in
/-- **Exactly one tag bit is set**: the sentence saying that an assignment of
the extended block names a tag. -/
noncomputable def tagGuardF : (L.sum (B.withTag T).lang).Sentence :=
  listSup ((finEnum T).map fun t =>
    tagBitF B T t ⊓
      listInf (((finEnum T).map fun t' => if t' = t then ⊤ else ∼(tagBitF B T t'))))

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (tagGuardF)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

variable [L.Structure A]

theorem realize_tagBitF (σ : (B.withTag T).Assignment A) (t : T) :
    (@Formula.Realize _ A ((B.withTag T).structure₁ (L := L) σ) _ (tagBitF B T t) default ↔
      σ (Sum.inl t) default) := by
  let := (B.withTag T).structure₁ (L := L) σ
  exact iff_of_eq (congrArg (σ (Sum.inl t)) (Subsingleton.elim _ _))

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (realize_tagBitF)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

variable [L.Structure A]

/-- **The guard says the assignment is a tagged one.** -/
theorem realize_tagGuardF (σ : (B.withTag T).Assignment A) :
    (@Sentence.Realize _ A ((B.withTag T).structure₁ (L := L) σ) (tagGuardF B T) ↔
      ∃ (t : T) (ρ : B.Assignment A), σ = tagAssign t ρ) := by
  let := (B.withTag T).structure₁ (L := L) σ
  rw [tagGuardF, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_inf, realize_listInf] at hr
    obtain ⟨hset, hrest⟩ := hr
    refine ⟨t, dropTag σ, ?_⟩
    funext i x
    match i with
    | Sum.inr j => rfl
    | Sum.inl t' =>
      rw [Subsingleton.elim x default]
      have := hrest _ (List.mem_map.mpr ⟨t', mem_finEnum t', rfl⟩)
      rcases eq_or_ne t' t with rfl | hne
      · rw [if_pos rfl] at this
        exact propext ⟨fun _ => rfl, fun _ => (realize_tagBitF σ t').mp hset⟩
      · rw [if_neg hne, Formula.realize_not, realize_tagBitF] at this
        exact propext ⟨fun h => absurd h this, fun h => absurd h hne⟩
  · rintro ⟨t, ρ, rfl⟩
    refine ⟨_, List.mem_map.mpr ⟨t, mem_finEnum t, rfl⟩, ?_⟩
    rw [Formula.realize_inf, realize_listInf]
    refine ⟨(realize_tagBitF _ t).mpr rfl, fun ψ hψ => ?_⟩
    obtain ⟨t', -, rfl⟩ := List.mem_map.mp hψ
    rcases eq_or_ne t' t with rfl | hne
    · rw [if_pos rfl]
      exact Formula.realize_top.mpr trivial
    · rw [if_neg hne, Formula.realize_not, realize_tagBitF]
      exact hne

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (realize_tagGuardF)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T]

variable {B T} {A : Type}

variable [L.Structure A]

end SOBlock

end Lax480241Proofs.DescriptiveComplexity


