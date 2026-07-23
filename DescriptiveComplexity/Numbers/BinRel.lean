/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.Unary
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Binary numbers carried by a relation

The layer between `DescriptiveComplexity.Numbers.Binary`, which decodes a set of bits
sitting on a genuine `LinearOrder`, and the problems of representation (C),
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

namespace DescriptiveComplexity

/-! ### Linear orders, as a property of a relation -/

section LinOrd

variable {A : Type}

/-- A binary relation is a linear order: reflexive, transitive, antisymmetric
and total. -/
def IsLinOrd (Le : A → A → Prop) : Prop :=
  (∀ a, Le a a) ∧ (∀ a b c, Le a b → Le b c → Le a c) ∧
    (∀ a b, Le a b → Le b a → a = b) ∧ ∀ a b, Le a b ∨ Le b a

/-- Linearity transports along an equivalence. -/
theorem IsLinOrd.of_equiv {B : Type} (u : B ≃ A) {LeB : B → B → Prop} {LeA : A → A → Prop}
    (hle : ∀ b b', LeB b b' ↔ LeA (u b) (u b')) (h : IsLinOrd LeB) : IsLinOrd LeA := by
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

/-! ### Building linear orders

Reductions into a problem of representation (C) have to *construct* the order
of the instance they produce, and a `Σ₁` certificate sometimes has to exhibit
one. Both do it the same way: read the elements through a key into a
lexicographic product of orders already at hand. -/

section Build

variable {α β : Type} {Ra : α → α → Prop} {Rb : β → β → Prop}

/-- The lexicographic product of two relations. -/
def lexRel (Ra : α → α → Prop) (Rb : β → β → Prop) : α × β → α × β → Prop := fun u v =>
  (Ra u.1 v.1 ∧ u.1 ≠ v.1) ∨ (u.1 = v.1 ∧ Rb u.2 v.2)

/-- The lexicographic product of two linear orders is a linear order. -/
theorem isLinOrd_lexRel (ha : IsLinOrd Ra) (hb : IsLinOrd Rb) : IsLinOrd (lexRel Ra Rb) := by
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
    (hK : IsLinOrd LeK) (key : M → K) (hinj : Function.Injective key)
    (h : ∀ a b, R a b ↔ LeK (key a) (key b)) : IsLinOrd R :=
  ⟨fun a => (h a a).mpr (hK.1 _),
    fun a b c hab hbc => (h a c).mpr (hK.2.1 _ _ _ ((h a b).mp hab) ((h b c).mp hbc)),
    fun a b hab hba => hinj (hK.2.2.1 _ _ ((h a b).mp hab) ((h b a).mp hba)),
    fun a b => (hK.2.2.2 (key a) (key b)).imp (h a b).mpr (h b a).mpr⟩

open Classical in
/-- A relation that *is* a linear order induces a `LinearOrder` structure,
which is what Mathlib's order library asks for. Guessed orders – a schedule, a
circuit – arrive as relations, so this is the bridge to it. -/
@[instance_reducible]
noncomputable def IsLinOrd.toLinearOrder {A : Type} {Le : A → A → Prop} (h : IsLinOrd Le) :
    LinearOrder A where
  le := Le
  lt a b := Le a b ∧ ¬Le b a
  le_refl := h.1
  le_trans := h.2.1
  le_antisymm := h.2.2.1
  le_total := h.2.2.2
  lt_iff_le_not_ge _ _ := Iff.rfl
  toDecidableLE := Classical.decRel _

/-- The natural order of a linear order, as a relation. -/
theorem isLinOrd_le {α : Type} [LinearOrder α] : IsLinOrd (· ≤ · : α → α → Prop) :=
  ⟨fun _ => le_rfl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩

end LinOrd

/-! ### Decoding a set of positions -/

section Decode

variable {A : Type}

/-- The rank of a position: the number of positions strictly below it. This is
the place value's exponent. -/
noncomputable def bitRank (Le : A → A → Prop) (Posn : A → Prop) (p : A) : ℕ :=
  ({q | Posn q ∧ Le q p ∧ q ≠ p} : Set A).ncard

/-- The number encoded by the set `b` of positions: `∑ 2 ^ rank`. -/
noncomputable def binNum (Le : A → A → Prop) (Posn b : A → Prop) : ℕ :=
  ∑ᶠ p ∈ {p | Posn p ∧ b p}, 2 ^ bitRank Le Posn p

theorem binNum_congr {Le : A → A → Prop} {Posn b b' : A → Prop} (h : ∀ p, b p ↔ b' p) :
    binNum Le Posn b = binNum Le Posn b' := by
  have : {p | Posn p ∧ b p} = {p | Posn p ∧ b' p} := by
    ext p
    simp [h p]
  rw [binNum, binNum, this]

/-- Only the bits at positions matter. -/
theorem binNum_congr_on {Le : A → A → Prop} {Posn b b' : A → Prop}
    (h : ∀ p, Posn p → (b p ↔ b' p)) : binNum Le Posn b = binNum Le Posn b' := by
  have hset : {p | Posn p ∧ b p} = {p | Posn p ∧ b' p} := by
    ext p
    exact and_congr_right fun hp => h p hp
  rw [binNum, binNum, hset]

/-- The value of the empty set of positions is zero. -/
@[simp]
theorem binNum_bot (Le : A → A → Prop) (Posn : A → Prop) :
    binNum Le Posn (fun _ => False) = 0 := by
  have : {p | Posn p ∧ False} = (∅ : Set A) := by
    ext p
    simp
  rw [binNum, this, finsum_mem_empty]

variable {B : Type}

/-- The rank of a position transports along an equivalence commuting with the
two relations. -/
theorem bitRank_equiv (u : B ≃ A) {LeB : B → B → Prop} {PosnB : B → Prop}
    {LeA : A → A → Prop} {PosnA : A → Prop}
    (hle : ∀ b b', LeB b b' ↔ LeA (u b) (u b')) (hp : ∀ b, PosnB b ↔ PosnA (u b)) (p : B) :
    bitRank LeB PosnB p = bitRank LeA PosnA (u p) := by
  refine ncard_setOf_equiv u fun q => ?_
  rw [hp q, hle q p]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h he => h (u.injective he), fun h he => h (congrArg u he)⟩

/-- The decoded number transports along an equivalence commuting with the
three relations. -/
theorem binNum_equiv (u : B ≃ A) {LeB : B → B → Prop} {PosnB bB : B → Prop}
    {LeA : A → A → Prop} {PosnA bA : A → Prop}
    (hle : ∀ b b', LeB b b' ↔ LeA (u b) (u b')) (hp : ∀ b, PosnB b ↔ PosnA (u b))
    (hb : ∀ b, bB b ↔ bA (u b)) :
    binNum LeB PosnB bB = binNum LeA PosnA bA := by
  refine finsum_mem_eq_of_bijOn u ?_ fun p hp' => ?_
  · refine ⟨fun p hp' => ⟨(hp p).mp hp'.1, (hb p).mp hp'.2⟩, u.injective.injOn, fun q hq => ?_⟩
    exact ⟨u.symm q, ⟨(hp _).mpr (by simpa using hq.1), (hb _).mpr (by simpa using hq.2)⟩,
      by simp⟩
  · rw [bitRank_equiv u hle hp p]

end Decode


/-! ### Peeling the lowest position -/

section Peel

variable {A : Type} [Finite A]

open Classical in
/-- The decoded value, as a sum over a finite set. -/
theorem binNum_eq_sum (Le : A → A → Prop) (Posn b : A → Prop) :
    binNum Le Posn b =
      ∑ p ∈ (Set.toFinite {p : A | Posn p ∧ b p}).toFinset, 2 ^ bitRank Le Posn p :=
  finsum_mem_eq_finite_toFinset_sum _ _

/-- Removing the lowest position lowers every other rank by one. -/
theorem bitRank_erase_min {Le : A → A → Prop} {Posn : A → Prop} {p₀ : A}
    (h₀ : Posn p₀) (hmin : ∀ q, Posn q → Le p₀ q) {p : A} (hp : Posn p) (hne : p ≠ p₀) :
    bitRank Le Posn p = bitRank Le (fun q => Posn q ∧ q ≠ p₀) p + 1 := by
  have hsplit : {q : A | Posn q ∧ Le q p ∧ q ≠ p} =
      insert p₀ {q : A | (Posn q ∧ q ≠ p₀) ∧ Le q p ∧ q ≠ p} := by
    ext q
    constructor
    · rintro ⟨hq, hle, hqp⟩
      rcases eq_or_ne q p₀ with rfl | hq₀
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨⟨hq, hq₀⟩, hle, hqp⟩
    · rintro (rfl | ⟨⟨hq, -⟩, hle, hqp⟩)
      · exact ⟨h₀, hmin p hp, Ne.symm hne⟩
      · exact ⟨hq, hle, hqp⟩
  have hnot : p₀ ∉ {q : A | (Posn q ∧ q ≠ p₀) ∧ Le q p ∧ q ≠ p} := by
    rintro ⟨⟨-, hcon⟩, -, -⟩
    exact hcon rfl
  rw [bitRank, bitRank, hsplit, Set.ncard_insert_of_notMem hnot (Set.toFinite _)]

open Classical in
/-- **The recursion binary numbers satisfy**: the value is the lowest bit plus
twice the value of the rest. -/
theorem binNum_peel_min {Le : A → A → Prop} {Posn b : A → Prop} {p₀ : A}
    (hlin : IsLinOrd Le) (h₀ : Posn p₀) (hmin : ∀ q, Posn q → Le p₀ q) :
    binNum Le Posn b =
      (if b p₀ then 1 else 0) + 2 * binNum Le (fun q => Posn q ∧ q ≠ p₀) b := by
  classical
  have hrank₀ : bitRank Le Posn p₀ = 0 := by
    have : {q : A | Posn q ∧ Le q p₀ ∧ q ≠ p₀} = (∅ : Set A) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hq, hle, hne⟩
      exact hne (hlin.2.2.1 q p₀ hle (hmin q hq))
    rw [bitRank, this, Set.ncard_empty]
  -- split the sum at the lowest position
  have hsplit : {p : A | Posn p ∧ b p} =
      {p : A | (Posn p ∧ p ≠ p₀) ∧ b p} ∪ {p : A | p = p₀ ∧ b p} := by
    ext p
    constructor
    · rintro ⟨hp, hb⟩
      rcases eq_or_ne p p₀ with rfl | hne
      · exact Or.inr ⟨rfl, hb⟩
      · exact Or.inl ⟨⟨hp, hne⟩, hb⟩
    · rintro (⟨⟨hp, -⟩, hb⟩ | ⟨rfl, hb⟩)
      · exact ⟨hp, hb⟩
      · exact ⟨h₀, hb⟩
  have hdisj : Disjoint {p : A | (Posn p ∧ p ≠ p₀) ∧ b p} {p : A | p = p₀ ∧ b p} := by
    rw [Set.disjoint_left]
    rintro p ⟨⟨-, hne⟩, -⟩ ⟨rfl, -⟩
    exact hne rfl
  rw [binNum, hsplit, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)]
  have hsecond : (∑ᶠ p ∈ {p : A | p = p₀ ∧ b p}, 2 ^ bitRank Le Posn p)
      = if b p₀ then 1 else 0 := by
    by_cases hb : b p₀
    · have : {p : A | p = p₀ ∧ b p} = {p₀} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hb⟩⟩
      rw [this, finsum_mem_singleton, hrank₀, if_pos hb, pow_zero]
    · have : {p : A | p = p₀ ∧ b p} = (∅ : Set A) := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨rfl, hcon⟩
        exact hb hcon
      rw [this, finsum_mem_empty, if_neg hb]
  have hfirst : (∑ᶠ p ∈ {p : A | (Posn p ∧ p ≠ p₀) ∧ b p}, 2 ^ bitRank Le Posn p)
      = 2 * binNum Le (fun q => Posn q ∧ q ≠ p₀) b := by
    rw [binNum, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (Posn p ∧ p ≠ p₀) ∧ b p := by simpa using hp
    rw [bitRank_erase_min h₀ hmin hp'.1.1 hp'.1.2, pow_succ]
    ring
  rw [hfirst, hsecond, Nat.add_comm]

end Peel

/-! ### The full adder -/

section Adder

/-- The majority of three propositions: the carry produced by a full adder. -/
def maj (x y z : Prop) : Prop := (x ∧ y) ∨ (x ∧ z) ∨ (y ∧ z)

open Classical in
/-- **The full-adder identity**: the sum bit plus twice the carry is the sum
of the three input bits. -/
theorem fullAdder (x y z : Prop) :
    (if Xor x (Xor y z) then 1 else 0) + 2 * (if maj x y z then 1 else 0) =
      (if x then 1 else 0) + ((if y then 1 else 0) + (if z then 1 else 0)) := by
  by_cases hx : x <;> by_cases hy : y <;> by_cases hz : z <;>
    simp [Xor, maj, hx, hy, hz]

end Adder

/-! ### Ripple-carry addition -/

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- `p` is a lowest position. -/
def MinPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le p q

/-- `p` is a highest position. -/
def MaxPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le q p

/-- `q` is the next position above `p`. -/
def SuccPos (Le : A → A → Prop) (Posn : A → Prop) (p q : A) : Prop :=
  Posn p ∧ Posn q ∧ Le p q ∧ p ≠ q ∧ ∀ r, Posn r → Le p r → Le r q → r = p ∨ r = q

/-- A nonempty set of positions has a lowest one: minimize the rank. -/
theorem exists_minPos (hlin : IsLinOrd Le) (hne : ∃ p, Posn p) :
    ∃ p, MinPos Le Posn p := by
  classical
  obtain ⟨p₀, hp₀, hmin⟩ :=
    Set.exists_min_image {p : A | Posn p} (bitRank Le Posn) (Set.toFinite _) hne
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
  have hlt : bitRank Le Posn q < bitRank Le Posn p₀ :=
    Set.ncard_lt_ncard ⟨hsub, fun hcon => hnot (hcon hmem)⟩ (Set.toFinite _)
  exact absurd (hmin q hq) (by omega)

/-- Rank is strictly monotone: a lower position has a smaller rank. -/
theorem bitRank_lt (hlin : IsLinOrd Le) {p q : A} (hp : Posn p) (hle : Le p q)
    (hne : p ≠ q) : bitRank Le Posn p < bitRank Le Posn q := by
  have hsub : {r : A | Posn r ∧ Le r p ∧ r ≠ p} ⊆ {r : A | Posn r ∧ Le r q ∧ r ≠ q} := by
    rintro r ⟨hr, hrp, hrne⟩
    refine ⟨hr, hlin.2.1 r p q hrp hle, fun hcon => ?_⟩
    exact hrne (hlin.2.2.1 r p hrp (hcon ▸ hle))
  have hmem : p ∈ {r : A | Posn r ∧ Le r q ∧ r ≠ q} := ⟨hp, hle, hne⟩
  have hnot : p ∉ {r : A | Posn r ∧ Le r p ∧ r ≠ p} := fun h => h.2.2 rfl
  exact Set.ncard_lt_ncard ⟨hsub, fun hcon => hnot (hcon hmem)⟩ (Set.toFinite _)

omit [Finite A] in
/-- The element immediately below a given one is unique. -/
theorem succPos_left_unique (hlin : IsLinOrd Le) {p p' q : A}
    (h : SuccPos Le Posn p q) (h' : SuccPos Le Posn p' q) : p = p' := by
  rcases hlin.2.2.2 p p' with hle | hle
  · rcases h.2.2.2.2 p' h'.1 hle h'.2.2.1 with h1 | h1
    · exact h1.symm
    · exact absurd h1 h'.2.2.2.1
  · rcases h'.2.2.2.2 p h.1 hle h.2.2.1 with h1 | h1
    · exact h1
    · exact absurd h1 h.2.2.2.1

omit [Finite A] in
/-- The reverse of a linear order is a linear order. -/
theorem IsLinOrd.reverse (hlin : IsLinOrd Le) : IsLinOrd (fun a b => Le b a) :=
  ⟨hlin.1, fun a b c hab hbc => hlin.2.1 c b a hbc hab,
    fun a b hab hba => hlin.2.2.1 a b hba hab, fun a b => hlin.2.2.2 b a⟩

/-- A nonempty set of positions has a highest one. -/
theorem exists_maxPos (hlin : IsLinOrd Le) (hne : ∃ p, Posn p) :
    ∃ p, MaxPos Le Posn p := by
  obtain ⟨p, hp, hmax⟩ := exists_minPos hlin.reverse hne
  exact ⟨p, hp, hmax⟩

/-- Every position that is not the lowest has one immediately below it. -/
theorem exists_predPos (hlin : IsLinOrd Le) {p : A} (hp : Posn p)
    (hmin : ¬MinPos Le Posn p) : ∃ q, SuccPos Le Posn q p := by
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

open Classical in
/-- **Ripple-carry addition is addition.** If `s` is the bitwise sum of `a`
and `b` with carries `c` – each bit the exclusive or of the three, each carry
the majority of the three below – then the decoded numbers add up, the carry
in at the bottom and the carry out at the top accounting for the
difference. -/
theorem binNum_ripple (hlin : IsLinOrd Le) {a b s : A → Prop} :
    ∀ (n : ℕ) (Posn c : A → Prop) (cin cout : Prop),
      ({p : A | Posn p} : Set A).ncard = n →
      (∀ p, Posn p → (s p ↔ Xor (a p) (Xor (b p) (c p)))) →
      (∀ p q, SuccPos Le Posn p q → (c q ↔ maj (a p) (b p) (c p))) →
      (∀ p, MinPos Le Posn p → (c p ↔ cin)) →
      (∀ p, MaxPos Le Posn p → (cout ↔ maj (a p) (b p) (c p))) →
      ((∀ p, ¬Posn p) → (cout ↔ cin)) →
      binNum Le Posn s + 2 ^ n * (if cout then 1 else 0) =
        binNum Le Posn a + binNum Le Posn b + (if cin then 1 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn c cin cout hn hsum hstep hbot htop hemp
    by_cases hne : ∃ p, Posn p
    · -- peel the lowest position
      obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin hne
      have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
        ext p
        simp
      have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]
        exact hne
      have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
        rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
          ← hn]
        omega
      -- the successor of the lowest position is the lowest of the rest
      have hsucc : ∀ p, MinPos Le (fun q => Posn q ∧ q ≠ p₀) p → SuccPos Le Posn p₀ p := by
        rintro p ⟨⟨hp, hpne⟩, hpmin⟩
        refine ⟨hp₀, hp, hminp p hp, Ne.symm hpne, fun r hr hr₀ hrp => ?_⟩
        rcases eq_or_ne r p₀ with hrp₀ | hrne
        · exact Or.inl hrp₀
        · exact Or.inr (hlin.2.2.1 r p hrp (hpmin r ⟨hr, hrne⟩))
      -- the hypotheses, restricted to the remaining positions
      have hsum' : ∀ p, (Posn p ∧ p ≠ p₀) → (s p ↔ Xor (a p) (Xor (b p) (c p))) :=
        fun p hp => hsum p hp.1
      have hstep' : ∀ p q, SuccPos Le (fun q => Posn q ∧ q ≠ p₀) p q →
          (c q ↔ maj (a p) (b p) (c p)) := by
        rintro p q ⟨⟨hp, hpne⟩, ⟨hq, hqne⟩, hpq, hne', hbet⟩
        refine hstep p q ⟨hp, hq, hpq, hne', fun r hr hpr hrq => ?_⟩
        rcases eq_or_ne r p₀ with hrp₀ | hrne
        · exact absurd (hlin.2.2.1 p p₀ (hrp₀ ▸ hpr) (hminp p hp)) hpne
        · exact hbet r ⟨hr, hrne⟩ hpr hrq
      have hbot' : ∀ p, MinPos Le (fun q => Posn q ∧ q ≠ p₀) p →
          (c p ↔ maj (a p₀) (b p₀) (c p₀)) := fun p hp => hstep p₀ p (hsucc p hp)
      have htop' : ∀ p, MaxPos Le (fun q => Posn q ∧ q ≠ p₀) p →
          (cout ↔ maj (a p) (b p) (c p)) := by
        rintro p ⟨⟨hp, hpne⟩, hpmax⟩
        refine htop p ⟨hp, fun q hq => ?_⟩
        rcases eq_or_ne q p₀ with hqp₀ | hqne
        · exact hqp₀ ▸ hminp p hp
        · exact hpmax q ⟨hq, hqne⟩
      have hemp' : (∀ p, ¬(Posn p ∧ p ≠ p₀)) → (cout ↔ maj (a p₀) (b p₀) (c p₀)) := by
        intro hempty
        refine htop p₀ ⟨hp₀, fun q hq => ?_⟩
        rcases eq_or_ne q p₀ with hqp₀ | hqne
        · exact hqp₀ ▸ hlin.1 q
        · exact absurd ⟨hq, hqne⟩ (hempty q)
      have hIH := IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
        (fun q => Posn q ∧ q ≠ p₀) c (maj (a p₀) (b p₀) (c p₀)) cout rfl
        hsum' hstep' hbot' htop' hemp'
      -- peel each of the three numbers and use the full adder at the bottom
      rw [binNum_peel_min hlin hp₀ hminp (b := s), binNum_peel_min hlin hp₀ hminp (b := a),
        binNum_peel_min hlin hp₀ hminp (b := b), ← hcard, pow_succ]
      have hs₀ : (if s p₀ then 1 else 0) =
          (if Xor (a p₀) (Xor (b p₀) (c p₀)) then 1 else 0) :=
        if_congr (hsum p₀ hp₀) rfl rfl
      have hc₀ : (if cin then 1 else 0) = (if c p₀ then 1 else 0) :=
        (if_congr (hbot p₀ ⟨hp₀, hminp⟩) rfl rfl).symm
      have hadd := fullAdder (a p₀) (b p₀) (c p₀)
      have hpow : 2 ^ ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard * 2 *
          (if cout then 1 else 0) =
          2 * (2 ^ ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard * (if cout then 1 else 0)) := by
        ring
      rw [hs₀, hc₀, hpow]
      omega
    · -- no position at all: every number is zero
      have hempty : ∀ p, ¬Posn p := fun p hp => hne ⟨p, hp⟩
      have hzero : ∀ x : A → Prop, binNum Le Posn x = 0 := by
        intro x
        have hset : {p : A | Posn p ∧ x p} = (∅ : Set A) := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hempty p h.1
        rw [binNum, hset, finsum_mem_empty]
      have hn0 : n = 0 := by
        rw [← hn, Set.ncard_eq_zero (Set.toFinite _)]
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hempty p
      rw [hzero s, hzero a, hzero b, hn0, if_congr (hemp hempty) rfl rfl]
      simp

/-- A decoded number is smaller than `2` to the number of positions. -/
theorem binNum_lt_two_pow (hlin : IsLinOrd Le) :
    ∀ (n : ℕ) (Posn : A → Prop), ({p : A | Posn p} : Set A).ncard = n →
      ∀ b : A → Prop, binNum Le Posn b < 2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn hn b
    classical
    by_cases hne : ∃ p, Posn p
    · obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin hne
      have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
        ext p
        simp
      have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]
        exact hne
      have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
        rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
          ← hn]
        omega
      have hIH := IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
        (fun q => Posn q ∧ q ≠ p₀) rfl b
      rw [binNum_peel_min hlin hp₀ hminp, ← hcard, pow_succ]
      have : (if b p₀ then 1 else 0) ≤ 1 := by
        split <;> omega
      omega
    · have hempty : ∀ p, ¬Posn p := fun p hp => hne ⟨p, hp⟩
      have hzero : binNum Le Posn b = 0 := by
        have hset : {p : A | Posn p ∧ b p} = (∅ : Set A) := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hempty p h.1
        rw [binNum, hset, finsum_mem_empty]
      rw [hzero]
      exact Nat.two_pow_pos n

open Classical in
/-- **A ripple-carry certificate exists.** Whenever the sum fits in the
available positions, the bitwise sum and the carries that witness it can be
produced – this is the certificate that the `Σ₁` definition of a
binary-weighted problem guesses. -/
theorem exists_ripple (hlin : IsLinOrd Le) :
    ∀ (n : ℕ) (Posn a b : A → Prop) (cin : Prop),
      ({p : A | Posn p} : Set A).ncard = n →
      binNum Le Posn a + binNum Le Posn b + (if cin then 1 else 0) < 2 ^ n →
      ∃ s c : A → Prop,
        (∀ p, Posn p → (s p ↔ Xor (a p) (Xor (b p) (c p)))) ∧
        (∀ p q, SuccPos Le Posn p q → (c q ↔ maj (a p) (b p) (c p))) ∧
        (∀ p, MinPos Le Posn p → (c p ↔ cin)) ∧
        (∀ p, MaxPos Le Posn p → ¬maj (a p) (b p) (c p)) ∧
        binNum Le Posn s =
          binNum Le Posn a + binNum Le Posn b + (if cin then 1 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn a b cin hn hlt
    by_cases hne : ∃ p, Posn p
    · obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin hne
      have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
        ext p
        simp
      have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]
        exact hne
      have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
        rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
          ← hn]
        omega
      -- the bound survives the peeling, by the full adder
      have hpeela := binNum_peel_min hlin hp₀ hminp (b := a)
      have hpeelb := binNum_peel_min hlin hp₀ hminp (b := b)
      have hadd := fullAdder (a p₀) (b p₀) cin
      have hbound : binNum Le (fun q => Posn q ∧ q ≠ p₀) a +
          binNum Le (fun q => Posn q ∧ q ≠ p₀) b +
          (if maj (a p₀) (b p₀) cin then 1 else 0) <
            2 ^ ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard := by
        rw [← hcard, pow_succ] at hlt
        rw [hpeela, hpeelb] at hlt
        have hs0 : (if Xor (a p₀) (Xor (b p₀) cin) then 1 else 0) ≤ 1 := by
          split <;> omega
        omega
      obtain ⟨s', c', hsum', hstep', hbot', htop', hval'⟩ :=
        IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
          (fun q => Posn q ∧ q ≠ p₀) a b (maj (a p₀) (b p₀) cin) rfl hbound
      refine ⟨fun p => (p = p₀ ∧ Xor (a p₀) (Xor (b p₀) cin)) ∨ (p ≠ p₀ ∧ s' p),
        fun p => (p = p₀ ∧ cin) ∨ (p ≠ p₀ ∧ c' p), ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases eq_or_ne p p₀ with hpp₀ | hpne
        · simp [hpp₀]
        · simpa [hpne] using hsum' p ⟨hp, hpne⟩
      · rintro p q ⟨hp, hq, hpq, hpqne, hbet⟩
        have hqne : q ≠ p₀ := by
          rintro rfl
          exact hpqne (hlin.2.2.1 p q hpq (hminp p hp))
        rcases eq_or_ne p p₀ with hpp₀ | hpne
        · -- `q` is the lowest of the remaining positions
          have hq_min : MinPos Le (fun r => Posn r ∧ r ≠ p₀) q := by
            refine ⟨⟨hq, hqne⟩, fun r hr => ?_⟩
            rcases hlin.2.2.2 q r with h | h
            · exact h
            · rcases hbet r hr.1 (hpp₀ ▸ hminp r hr.1) h with h1 | h1
              · exact absurd (h1.trans hpp₀) hr.2
              · exact h1 ▸ hlin.1 r
          have hcq := hbot' q hq_min
          simp only [hpp₀, hqne, false_and, or_false, true_and, ne_eq, not_false_iff,
            not_true_eq_false]
          simpa [hqne] using hcq
        · have hstep := hstep' p q ⟨⟨hp, hpne⟩, ⟨hq, hqne⟩, hpq, hpqne,
            fun r hr hpr hrq => hbet r hr.1 hpr hrq⟩
          simpa [hpne, hqne] using hstep
      · rintro p ⟨hp, hpmin⟩
        have hpp₀ : p = p₀ := hlin.2.2.1 p p₀ (hpmin p₀ hp₀) (hminp p hp)
        simp [hpp₀]
      · rintro p ⟨hp, hpmax⟩
        rcases eq_or_ne p p₀ with hpp₀ | hpne
        · -- the only position: the bound forces the carry out to vanish
          have hzero : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard = 0 := by
            rw [Set.ncard_eq_zero (Set.toFinite _)]
            ext r
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hr, hrne⟩
            exact hrne (hlin.2.2.1 r p₀ (hpp₀ ▸ hpmax r hr) (hminp r hr))
          rw [hzero] at hbound
          have hcin' : ¬maj (a p₀) (b p₀) cin := by
            intro hcon
            rw [if_pos hcon] at hbound
            omega
          simpa [hpp₀] using hcin'
        · have := htop' p ⟨⟨hp, hpne⟩, fun q hq => hpmax q hq.1⟩
          simpa [hpne] using this
      · have hpeels := binNum_peel_min hlin hp₀ hminp
          (b := fun p => (p = p₀ ∧ Xor (a p₀) (Xor (b p₀) cin)) ∨ (p ≠ p₀ ∧ s' p))
        have hrest : binNum Le (fun q => Posn q ∧ q ≠ p₀)
            (fun p => (p = p₀ ∧ Xor (a p₀) (Xor (b p₀) cin)) ∨ (p ≠ p₀ ∧ s' p)) =
            binNum Le (fun q => Posn q ∧ q ≠ p₀) s' :=
          binNum_congr_on fun p hp => by simp [hp.2]
        rw [hrest] at hpeels
        rw [hpeels, hpeela, hpeelb, hval', Nat.mul_add, Nat.mul_add]
        simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
        omega
    · -- no positions: the sum is zero and the carry in cannot be set
      have hempty : ∀ p, ¬Posn p := fun p hp => hne ⟨p, hp⟩
      have hzero : ∀ x : A → Prop, binNum Le Posn x = 0 := by
        intro x
        have hset : {p : A | Posn p ∧ x p} = (∅ : Set A) := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hempty p h.1
        rw [binNum, hset, finsum_mem_empty]
      have hn0 : n = 0 := by
        rw [← hn, Set.ncard_eq_zero (Set.toFinite _)]
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hempty p
      rw [hzero a, hzero b, hn0] at hlt
      have hcin : ¬cin := by
        intro hc
        rw [if_pos hc] at hlt
        omega
      exact ⟨fun _ => False, fun _ => False,
        fun p hp => absurd hp (hempty p), fun p q hpq => absurd hpq.1 (hempty p),
        fun p hp => absurd hp.1 (hempty p), fun p hp => absurd hp.1 (hempty p),
        by rw [hzero, hzero a, hzero b, if_neg hcin]⟩

open Classical in
/-- **Every number that fits can be written**: a value below `2` to the number
of positions is decoded from some set of bits. -/
theorem exists_binNum (hlin : IsLinOrd Le) :
    ∀ (n : ℕ) (Posn : A → Prop), ({p : A | Posn p} : Set A).ncard = n →
      ∀ k < 2 ^ n, ∃ b : A → Prop, binNum Le Posn b = k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn hn k hk
    by_cases hne : ∃ p, Posn p
    · obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin hne
      have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
        ext p
        simp
      have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]
        exact hne
      have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
        rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
          ← hn]
        omega
      have hhalf : k / 2 < 2 ^ ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard := by
        rw [← hcard, pow_succ] at hk
        omega
      obtain ⟨b', hb'⟩ := IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
        (fun q => Posn q ∧ q ≠ p₀) rfl (k / 2) hhalf
      refine ⟨fun p => (p = p₀ ∧ k % 2 = 1) ∨ (p ≠ p₀ ∧ b' p), ?_⟩
      have hpeel := binNum_peel_min hlin hp₀ hminp
        (b := fun p => (p = p₀ ∧ k % 2 = 1) ∨ (p ≠ p₀ ∧ b' p))
      have hrest : binNum Le (fun q => Posn q ∧ q ≠ p₀)
          (fun p => (p = p₀ ∧ k % 2 = 1) ∨ (p ≠ p₀ ∧ b' p)) =
          binNum Le (fun q => Posn q ∧ q ≠ p₀) b' :=
        binNum_congr_on fun p hp => by simp [hp.2]
      rw [hrest, hb'] at hpeel
      rw [hpeel]
      simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
      rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with hpar | hpar
      · rw [if_neg (by omega)]
        omega
      · rw [if_pos hpar]
        omega
    · have hempty : ∀ p, ¬Posn p := fun p hp => hne ⟨p, hp⟩
      have hn0 : n = 0 := by
        rw [← hn, Set.ncard_eq_zero (Set.toFinite _)]
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hempty p
      subst hn0
      have hk0 : k = 0 := by simpa using hk
      refine ⟨fun _ => False, ?_⟩
      have hset : {p : A | Posn p ∧ False} = (∅ : Set A) := by
        ext p
        simp
      rw [binNum, hset, finsum_mem_empty, hk0]

open Classical in
/-- **The decoding is injective on the positions**: two sets of bits with the
same value agree wherever it matters. -/
theorem binNum_inj_on (hlin : IsLinOrd Le) :
    ∀ (n : ℕ) (Posn : A → Prop), ({p : A | Posn p} : Set A).ncard = n →
      ∀ b b' : A → Prop, binNum Le Posn b = binNum Le Posn b' →
        ∀ p, Posn p → (b p ↔ b' p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn hn b b' heq p hp
    obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin ⟨p, hp⟩
    have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
      ext r
      simp
    have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
      rw [Set.ncard_pos (Set.toFinite _)]
      exact ⟨p, hp⟩
    have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
      rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
        ← hn]
      omega
    rw [binNum_peel_min hlin hp₀ hminp (b := b),
      binNum_peel_min hlin hp₀ hminp (b := b')] at heq
    -- the lowest bits agree, since they are the parities
    have hbit : (if b p₀ then 1 else 0) = (if b' p₀ then (1 : ℕ) else 0) := by
      by_cases h : b p₀ <;> by_cases h' : b' p₀ <;> simp [h, h'] at heq ⊢ <;> omega
    have hrest : binNum Le (fun q => Posn q ∧ q ≠ p₀) b =
        binNum Le (fun q => Posn q ∧ q ≠ p₀) b' := by omega
    rcases eq_or_ne p p₀ with hpp₀ | hpne
    · rw [hpp₀]
      by_cases h : b p₀ <;> by_cases h' : b' p₀
      · exact iff_of_true h h'
      · simp [h, h'] at hbit
      · simp [h, h'] at hbit
      · exact iff_of_false h h'
    · exact IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
        (fun q => Posn q ∧ q ≠ p₀) rfl b b' hrest p ⟨hp, hpne⟩

open Classical in
/-- **Comparison by the highest differing position**: one decoded number is
smaller than another exactly when there is a position carrying `0` in the
first and `1` in the second above which the two agree. Unlike the value
itself, this is a *first-order* reading of `<`, which is what a kernel
comparing two guessed numbers writes. -/
theorem binNum_lt_iff (hlin : IsLinOrd Le) :
    ∀ (n : ℕ) (Posn : A → Prop), ({p : A | Posn p} : Set A).ncard = n →
      ∀ b b' : A → Prop, (binNum Le Posn b < binNum Le Posn b' ↔
        ∃ p, Posn p ∧ ¬b p ∧ b' p ∧ ∀ q, Posn q → Le p q → q ≠ p → (b q ↔ b' q)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn hn b b'
    classical
    by_cases hne : ∃ p, Posn p
    · obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin hne
      have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]
        exact hne
      have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
        ext r
        simp
      have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
        rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
          ← hn]
        omega
      have hIH := IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
        (fun q => Posn q ∧ q ≠ p₀) rfl b b'
      -- above the lowest position, equality of the two values is agreement
      have heq : (binNum Le (fun q => Posn q ∧ q ≠ p₀) b =
          binNum Le (fun q => Posn q ∧ q ≠ p₀) b') ↔
            ∀ q, Posn q → q ≠ p₀ → (b q ↔ b' q) :=
        ⟨fun h q hq hq₀ => binNum_inj_on hlin _ _ rfl b b' h q ⟨hq, hq₀⟩,
          fun h => binNum_congr_on fun q hq => h q hq.1 hq.2⟩
      -- a witness is either the lowest position or one above it, and nothing
      -- lies above `p₀` that is not a position of its own
      have hsplit : (∃ p, Posn p ∧ ¬b p ∧ b' p ∧
            ∀ q, Posn q → Le p q → q ≠ p → (b q ↔ b' q)) ↔
          (∃ p, (Posn p ∧ p ≠ p₀) ∧ ¬b p ∧ b' p ∧
            ∀ q, (Posn q ∧ q ≠ p₀) → Le p q → q ≠ p → (b q ↔ b' q)) ∨
          ((∀ q, Posn q → q ≠ p₀ → (b q ↔ b' q)) ∧ ¬b p₀ ∧ b' p₀) := by
        constructor
        · rintro ⟨p, hp, hbp, hb'p, habove⟩
          rcases eq_or_ne p p₀ with rfl | hpne
          · exact Or.inr ⟨fun q hq hq₀ => habove q hq (hminp q hq) hq₀, hbp, hb'p⟩
          · exact Or.inl ⟨p, ⟨hp, hpne⟩, hbp, hb'p,
              fun q hq hle hqp => habove q hq.1 hle hqp⟩
        · rintro (⟨p, ⟨hp, hpne⟩, hbp, hb'p, habove⟩ | ⟨hag, hbp, hb'p⟩)
          · refine ⟨p, hp, hbp, hb'p, fun q hq hle hqp => ?_⟩
            rcases eq_or_ne q p₀ with rfl | hq₀
            · exact absurd (hlin.2.2.1 p q hle (hminp p hp)) hpne
            · exact habove q ⟨hq, hq₀⟩ hle hqp
          · exact ⟨p₀, hp₀, hbp, hb'p, fun q hq _ hq₀ => hag q hq hq₀⟩
      rw [binNum_peel_min hlin hp₀ hminp (b := b),
        binNum_peel_min hlin hp₀ hminp (b := b'), hsplit, ← hIH, ← heq]
      by_cases h : b p₀ <;> by_cases h' : b' p₀ <;> simp [h, h'] <;> omega
    · have hempty : ∀ p, ¬Posn p := fun p hp => hne ⟨p, hp⟩
      have hzero : ∀ c : A → Prop, binNum Le Posn c = 0 := by
        intro c
        have hset : {p : A | Posn p ∧ c p} = (∅ : Set A) := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hempty p h.1
        rw [binNum, hset, finsum_mem_empty]
      rw [hzero b, hzero b']
      simp only [lt_self_iff_false, false_iff, not_exists]
      exact fun p hcon => hempty p hcon.1

end Ripple

end DescriptiveComplexity
