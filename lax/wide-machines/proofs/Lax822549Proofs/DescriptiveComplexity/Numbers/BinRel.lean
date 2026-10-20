/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax799700.Common
end Lax799700.Common

namespace Lax822549.WideTilings
end Lax822549.WideTilings

namespace Lax822549Proofs.DescriptiveComplexity.IsLinOrd
end Lax822549Proofs.DescriptiveComplexity.IsLinOrd

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideTilings (MaxPos)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd MinPos SuccPos)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax799700.Common (binNum bitRank)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Binary numbers carried by a relation

The layer between `DescriptiveComplexity.Numbers.Binary`, which decodes a set of bits
sitting on a genuine `LinearOrder`, and the problems carrying binary numbers,
whose order is a *relation symbol* of the vocabulary and therefore an
arbitrary binary relation until the yes-instances say otherwise.

* `DescriptiveComplexity.IsLinOrd` – being a linear order, as a property of a relation,
  first-order and foldable into the yes-instances;
* `DescriptiveComplexity.bitRank` – the rank of a position, the number of positions
  strictly below it, defined for an arbitrary relation;
* `DescriptiveComplexity.binNum` – the decoding `∑ 2 ^ rank`, over a *set* of positions
  via `finsum`, so that it is total and needs no finiteness to be stated.

Everything transports along equivalences commuting with the relations, which
is what the `DecisionProblem.iso_invariant` proofs of the group need.

The arithmetic the `Σ₁` definitions need – that a bitwise ripple-carry chain
computes an addition – is built on `DescriptiveComplexity.binNum_peel_min`, which
peels the lowest position off a decoded number: `binNum = bit at the bottom +
2 * (the rest)`, the recursion binary numbers actually satisfy. The same
recursion gives the two facts a kernel needs about *whole* numbers rather than
their bits: `DescriptiveComplexity.binNum_inj_on`, two numbers are equal exactly when
their bits agree, and `DescriptiveComplexity.binNum_lt_iff`, one is smaller exactly
when they differ and the higher bit is the second's – both bitwise, hence
first-order, which is why a kernel can compare numbers it has guessed.
-/

namespace Lax822549Proofs.DescriptiveComplexity

/-! ### Linear orders, as a property of a relation -/

section LinOrd

variable {A : Type}

/-- Linearity transports along an equivalence. -/
theorem IsLinOrd.of_equiv {B : Type} (u : B ≃ A) {LeB : B → B → Prop} {LeA : A → A → Prop}
    (hle : ∀ b b', LeB b b' ↔ LeA (u b) (u b')) (h : Lax904597.Machines.IsLinOrd LeB) : Lax904597.Machines.IsLinOrd LeA := by
  obtain ⟨hrefl, htrans, hanti, htot⟩ := h
  refine ⟨fun a => ?_, fun a b c hab hbc => ?_, fun a b hab hba => ?_, fun a b => ?_⟩
  · simpa using (hle (u.symm a) (u.symm a)).mp (hrefl _)
  · have h1 := (hle (u.symm a) (u.symm b)).mpr (by simpa using hab)
    have h2 := (hle (u.symm b) (u.symm c)).mpr (by simpa using hbc)
    simpa using (hle (u.symm a) (u.symm c)).mp (htrans _ _ _ h1 h2)
  · have h1 := (hle (u.symm a) (u.symm b)).mpr (by simpa using hab)
    have h2 := (hle (u.symm b) (u.symm a)).mpr (by simpa using hba)
    simpa using congrArg u (hanti _ _ h1 h2)
  · rcases htot (u.symm a) (u.symm b) with h | h
    · exact Or.inl (by simpa using (hle _ _).mp h)
    · exact Or.inr (by simpa using (hle _ _).mp h)

end LinOrd

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.IsLinOrd

export Lax822549Proofs.DescriptiveComplexity.IsLinOrd (of_equiv)

end Lax904597.Machines.IsLinOrd

namespace Lax822549Proofs.DescriptiveComplexity

section LinOrd

variable {A : Type}

/-! ### Building linear orders

Reductions into a problem carrying binary numbers have to *construct* the
order of the instance they produce, and a `Σ₁` certificate sometimes has to
exhibit one. Both do it the same way: read the elements through a key into a
lexicographic product of orders already at hand. -/

section Build

variable {α β : Type} {Ra : α → α → Prop} {Rb : β → β → Prop}

/-- The lexicographic product of two relations. -/
def lexRel (Ra : α → α → Prop) (Rb : β → β → Prop) : α × β → α × β → Prop := fun u v =>
  (Ra u.1 v.1 ∧ u.1 ≠ v.1) ∨ (u.1 = v.1 ∧ Rb u.2 v.2)

/-- The lexicographic product of two linear orders is a linear order. -/
theorem isLinOrd_lexRel (ha : Lax904597.Machines.IsLinOrd Ra) (hb : Lax904597.Machines.IsLinOrd Rb) : Lax904597.Machines.IsLinOrd (lexRel Ra Rb) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄⟩ := ha
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hb
  refine ⟨fun u => Or.inr ⟨rfl, hb₁ _⟩, fun u v w h₁ h₂ => ?_, fun u v h₁ h₂ => ?_,
    fun u v => ?_⟩
  · rcases h₁ with ⟨h₁, hne₁⟩ | ⟨he₁, h₁⟩ <;> rcases h₂ with ⟨h₂, hne₂⟩ | ⟨he₂, h₂⟩
    · refine Or.inl ⟨ha₂ _ _ _ h₁ h₂, fun he => ?_⟩
      exact hne₁ (ha₃ _ _ h₁ (he ▸ h₂))
    · exact Or.inl ⟨he₂ ▸ h₁, he₂ ▸ hne₁⟩
    · exact Or.inl ⟨he₁ ▸ h₂, he₁ ▸ hne₂⟩
    · exact Or.inr ⟨he₁.trans he₂, hb₂ _ _ _ h₁ h₂⟩
  · rcases h₁ with ⟨h₁, hne₁⟩ | ⟨he₁, h₁⟩ <;> rcases h₂ with ⟨h₂, hne₂⟩ | ⟨he₂, h₂⟩
    · exact absurd (ha₃ _ _ h₁ h₂) hne₁
    · exact absurd he₂.symm hne₁
    · exact absurd he₁.symm hne₂
    · exact Prod.ext he₁ (hb₃ _ _ h₁ h₂)
  · rcases eq_or_ne u.1 v.1 with he | hne
    · exact (hb₄ u.2 v.2).imp (fun h => Or.inr ⟨he, h⟩) fun h => Or.inr ⟨he.symm, h⟩
    · exact (ha₄ u.1 v.1).imp (fun h => Or.inl ⟨h, hne⟩) fun h => Or.inl ⟨h, hne.symm⟩

end Build

/-- A relation read through an injective key into a linear order is a linear
order. -/
theorem isLinOrd_of_key {M K : Type} {LeK : K → K → Prop} {R : M → M → Prop}
    (hK : Lax904597.Machines.IsLinOrd LeK) (key : M → K) (hinj : Function.Injective key)
    (h : ∀ a b, R a b ↔ LeK (key a) (key b)) : Lax904597.Machines.IsLinOrd R :=
  ⟨fun a => (h a a).mpr (hK.1 _),
    fun a b c hab hbc => (h a c).mpr (hK.2.1 _ _ _ ((h a b).mp hab) ((h b c).mp hbc)),
    fun a b hab hba => hinj (hK.2.2.1 _ _ ((h a b).mp hab) ((h b a).mp hba)),
    fun a b => (hK.2.2.2 (key a) (key b)).imp (h a b).mpr (h b a).mpr⟩

open Classical in
/-- A relation that *is* a linear order induces a `LinearOrder` structure,
which is what Mathlib's order library asks for. Guessed orders – a schedule, a
circuit – arrive as relations, so this is the bridge to it. -/
@[instance_reducible]
noncomputable def IsLinOrd.toLinearOrder {A : Type} {Le : A → A → Prop} (h : Lax904597.Machines.IsLinOrd Le) :
    LinearOrder A where
  le := Le
  lt a b := Le a b ∧ ¬Le b a
  le_refl := h.1
  le_trans := h.2.1
  le_antisymm := h.2.2.1
  le_total := h.2.2.2
  lt_iff_le_not_ge _ _ := Iff.rfl
  toDecidableLE := Classical.decRel _

end LinOrd

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.IsLinOrd

export Lax822549Proofs.DescriptiveComplexity.IsLinOrd (toLinearOrder)

end Lax904597.Machines.IsLinOrd

namespace Lax822549Proofs.DescriptiveComplexity

section LinOrd

variable {A : Type}

/-- The natural order of a linear order, as a relation. -/
theorem isLinOrd_le {α : Type} [LinearOrder α] : Lax904597.Machines.IsLinOrd (· ≤ · : α → α → Prop) :=
  ⟨fun _ => le_rfl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩

end LinOrd

/-! ### Decoding a set of positions -/

section Decode

variable {A : Type}

/-! On a finite universe both are finite sums over `Finset`s, which is what a
decoder computes. The `Decidable` arguments are what makes those `Finset`s
constructible; nothing here needs the relations to be well-behaved. -/

section Finite

end Finite

end Decode

/-! ### Peeling the lowest position -/

section Peel

end Peel

/-! ### The full adder -/

section Adder

end Adder

/-! ### Ripple-carry addition -/

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- A nonempty set of positions has a lowest one: minimize the rank. -/
theorem exists_minPos (hlin : Lax904597.Machines.IsLinOrd Le) (hne : ∃ p, Posn p) :
    ∃ p, Lax904597.Machines.MinPos Le Posn p := by
  classical
  obtain ⟨p₀, hp₀, hmin⟩ :=
    Set.exists_min_image {p : A | Posn p} (Lax799700.Common.bitRank Le Posn) (Set.toFinite _) hne
  refine ⟨p₀, hp₀, fun q hq => ?_⟩
  by_contra hle
  have hql : Le q p₀ := (hlin.2.2.2 p₀ q).resolve_left hle
  have hne' : q ≠ p₀ := fun h => hle (h ▸ hlin.1 q)
  have hsub : {r : A | Posn r ∧ Le r q ∧ r ≠ q} ⊆ {r : A | Posn r ∧ Le r p₀ ∧ r ≠ p₀} := by
    rintro r ⟨hr, hrq, hrne⟩
    refine ⟨hr, hlin.2.1 r q p₀ hrq hql, fun hcon => ?_⟩
    exact hrne (hlin.2.2.1 r q hrq (hcon ▸ hql))
  have hmem : q ∈ {r : A | Posn r ∧ Le r p₀ ∧ r ≠ p₀} := ⟨hq, hql, hne'⟩
  have hnot : q ∉ {r : A | Posn r ∧ Le r q ∧ r ≠ q} := fun h => h.2.2 rfl
  have hlt : Lax799700.Common.bitRank Le Posn q < Lax799700.Common.bitRank Le Posn p₀ :=
    Set.ncard_lt_ncard ⟨hsub, fun hcon => hnot (hcon hmem)⟩ (Set.toFinite _)
  exact absurd (hmin q hq) (by omega)

/-- Rank is strictly monotone: a lower position has a smaller rank. -/
theorem bitRank_lt (hlin : Lax904597.Machines.IsLinOrd Le) {p q : A} (hp : Posn p) (hle : Le p q)
    (hne : p ≠ q) : Lax799700.Common.bitRank Le Posn p < Lax799700.Common.bitRank Le Posn q := by
  have hsub : {r : A | Posn r ∧ Le r p ∧ r ≠ p} ⊆ {r : A | Posn r ∧ Le r q ∧ r ≠ q} := by
    rintro r ⟨hr, hrp, hrne⟩
    refine ⟨hr, hlin.2.1 r p q hrp hle, fun hcon => ?_⟩
    exact hrne (hlin.2.2.1 r p hrp (hcon ▸ hle))
  have hmem : p ∈ {r : A | Posn r ∧ Le r q ∧ r ≠ q} := ⟨hp, hle, hne⟩
  have hnot : p ∉ {r : A | Posn r ∧ Le r p ∧ r ≠ p} := fun h => h.2.2 rfl
  exact Set.ncard_lt_ncard ⟨hsub, fun hcon => hnot (hcon hmem)⟩ (Set.toFinite _)

omit [Finite A] in
/-- The element immediately below a given one is unique. -/
theorem succPos_left_unique (hlin : Lax904597.Machines.IsLinOrd Le) {p p' q : A}
    (h : Lax904597.Machines.SuccPos Le Posn p q) (h' : Lax904597.Machines.SuccPos Le Posn p' q) : p = p' := by
  rcases hlin.2.2.2 p p' with hle | hle
  · rcases h.2.2.2.2 p' h'.1 hle h'.2.2.1 with h1 | h1
    · exact h1.symm
    · exact absurd h1 h'.2.2.2.1
  · rcases h'.2.2.2.2 p h.1 hle h.2.2.1 with h1 | h1
    · exact h1
    · exact absurd h1 h.2.2.2.1

omit [Finite A] in
/-- The reverse of a linear order is a linear order. -/
theorem IsLinOrd.reverse (hlin : Lax904597.Machines.IsLinOrd Le) : Lax904597.Machines.IsLinOrd (fun a b => Le b a) :=
  ⟨hlin.1, fun a b c hab hbc => hlin.2.1 c b a hbc hab,
    fun a b hab hba => hlin.2.2.1 a b hba hab, fun a b => hlin.2.2.2 b a⟩

end Ripple

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.IsLinOrd

export Lax822549Proofs.DescriptiveComplexity.IsLinOrd (reverse)

end Lax904597.Machines.IsLinOrd

namespace Lax822549Proofs.DescriptiveComplexity

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- A nonempty set of positions has a highest one. -/
theorem exists_maxPos (hlin : Lax904597.Machines.IsLinOrd Le) (hne : ∃ p, Posn p) :
    ∃ p, Lax822549.WideTilings.MaxPos Le Posn p := by
  obtain ⟨p, hp, hmax⟩ := exists_minPos hlin.reverse hne
  exact ⟨p, hp, hmax⟩

/-- Every position that is not the lowest has one immediately below it. -/
theorem exists_predPos (hlin : Lax904597.Machines.IsLinOrd Le) {p : A} (hp : Posn p)
    (hmin : ¬Lax904597.Machines.MinPos Le Posn p) : ∃ q, Lax904597.Machines.SuccPos Le Posn q p := by
  have hne : ∃ q, Posn q ∧ Le q p ∧ q ≠ p := by
    by_contra hcon
    push Not at hcon
    refine hmin ⟨hp, fun q hq => ?_⟩
    rcases hlin.2.2.2 p q with h | h
    · exact h
    · rcases eq_or_ne q p with rfl | hqne
      · exact hlin.1 q
      · exact absurd h (fun hle => hqne (hcon q hq hle))
  obtain ⟨m, ⟨hm, hmle, hmne⟩, hmmax⟩ :=
    exists_maxPos (Posn := fun q => Posn q ∧ Le q p ∧ q ≠ p) hlin hne
  refine ⟨m, hm, hp, hmle, hmne, fun r hr hmr hrp => ?_⟩
  rcases eq_or_ne r p with rfl | hrne
  · exact Or.inr rfl
  · exact Or.inl (hlin.2.2.1 r m (hmmax r ⟨hr, hrp, hrne⟩) hmr)

end Ripple

end Lax822549Proofs.DescriptiveComplexity


