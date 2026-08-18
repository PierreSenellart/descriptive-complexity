/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.OrdFormula

/-!
# The binary increment on a block's atoms

`DescriptiveComplexity.Exponential.OrdFormula` writes the *order* on an
expanded universe as a first-order sentence over the base. Walking that universe
needs one thing more: its **covering relation**, and the two endpoints of the
order. An assignment is read as a binary number – the set of atoms it makes
true, most significant at the smallest atom – so the immediate successor is the
schoolchild's increment: find the greatest atom the assignment misses, put it
in, and take out every atom above it.

This file proves that at the level of **sets** over a finite linearly ordered
index (`DescriptiveComplexity.setSucc_iff`: the increment *is* the covering
relation of `DescriptiveComplexity.setLinearOrder`), gives the two endpoints
their sentences (`DescriptiveComplexity.SOBlock.botAssignF`,
`DescriptiveComplexity.SOBlock.topAssignF`), and writes the increment down as a
sentence over the base plus two copies of the block
(`DescriptiveComplexity.SOBlock.succAssignF`), by the same quantification over
positions that `DescriptiveComplexity.SOBlock.ordLtF` already uses.

## The padding trap, and the honest atoms

A padded atom (`DescriptiveComplexity.SOBlock.AtomIx`) is a relation variable
with a tuple of the block's *maximal* arity, of which
`DescriptiveComplexity.SOBlock.atomSet` reads only the first `B.arity i`
coordinates – so the sets in the image of `atomSet` are exactly the
**padding-invariant** ones, and the binary increment of such a set is in general
not one: it flips a single padded atom, while padding-invariance forces every
padded atom with the same truncation to move together. **The successor of an
assignment is therefore not the increment of its padded atom set.**

The order is unaffected – two assignments differ first at a padded atom exactly
when they differ first at the *real* atom `Σ i, Fin (B.arity i) → A` it
truncates to – and the honest atoms are what this file works with. Over them an
assignment is an arbitrary subset (`DescriptiveComplexity.SOBlock.realSet` is a
bijection), so the set-level increment applies unchanged, and
`DescriptiveComplexity.SOBlock.assignSucc_iff` reads it back as *the immediate
successor in the order the expanded universe carries*. The two indices are
matched by `DescriptiveComplexity.SOBlock.atomSet_lt_iff_realSet`, whose whole
content is that a real atom has a **least** padded representative – the tuple
padded with the least element of `A` – so that comparing representatives is
comparing real atoms.

Accordingly the sentence takes its lexicographic comparisons on the
**truncated** selectors: `DescriptiveComplexity.lexSelLtF` accepts a selector of
any width, so the atoms it compares are the real ones.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The increment, on subsets of a finite linear order -/

section SetOrder

variable {I : Type} [LinearOrder I] [Finite I]

/-- **The binary increment of a set**: at some index the first is out and the
second in, they agree strictly below it, and above it the first is in and the
second out. -/
def SetSucc (S T : I → Prop) : Prop :=
  ∃ p, (∀ q, q < p → (S q ↔ T q)) ∧ ¬S p ∧ T p ∧ ∀ q, p < q → (S q ∧ ¬T q)

/-- **Covering** in the binary-number order, spelled with the order as a plain
relation: `DescriptiveComplexity.setLinearOrder` is not an instance, and the
function type `I → Prop` carries a competing pointwise order of its own, so `⋖`
would resolve to the wrong one. -/
def SetCovBy (S T : I → Prop) : Prop :=
  (setLinearOrder I).lt S T ∧ ∀ U, (setLinearOrder I).lt S U → ¬(setLinearOrder I).lt U T

/-- Nothing is below the empty set: the order compares at the least differing
index, where being out is being smaller. -/
theorem setLinearOrder_bot_le (S : I → Prop) :
    (setLinearOrder I).le (fun _ => False) S := by
  refine (@not_lt _ (setLinearOrder I) _ _).mp fun h => ?_
  obtain ⟨-, -, -, hbot⟩ := (setLinearOrder_lt_iff S fun _ => False).mp h
  exact hbot

/-- Nothing is above the full set. -/
theorem setLinearOrder_le_top (S : I → Prop) :
    (setLinearOrder I).le S (fun _ => True) := by
  refine (@not_lt _ (setLinearOrder I) _ _).mp fun h => ?_
  obtain ⟨-, -, htop, -⟩ := (setLinearOrder_lt_iff (fun _ => True) S).mp h
  exact htop trivial

/-- The increment is the covering relation, half one: an incremented set is
above, and nothing fits in between. -/
private theorem setCovBy_of_setSucc {S T : I → Prop} (h : SetSucc S T) : SetCovBy S T := by
  obtain ⟨p, hbelow, hnp, hp, habove⟩ := h
  refine ⟨(setLinearOrder_lt_iff S T).mpr ⟨p, hbelow, hnp, hp⟩, fun U hSU hUT => ?_⟩
  obtain ⟨p₁, hb₁, hn₁, hu₁⟩ := (setLinearOrder_lt_iff S U).mp hSU
  obtain ⟨p₂, hb₂, hn₂, ht₂⟩ := (setLinearOrder_lt_iff U T).mp hUT
  have hle₁ : p₁ ≤ p := not_lt.mp fun hlt => hn₁ (habove p₁ hlt).1
  have hle₂ : p₂ ≤ p := not_lt.mp fun hlt => (habove p₂ hlt).2 ht₂
  rcases lt_or_eq_of_le hle₁ with h₁ | h₁
  · -- `p₁ < p`: the first difference of `S` and `U` is below the increment
    have hT₁ : ¬T p₁ := fun hT => hn₁ ((hbelow p₁ h₁).mpr hT)
    have hne : ¬p₁ < p₂ := fun hlt => hT₁ ((hb₂ p₁ hlt).mp hu₁)
    rcases lt_or_eq_of_le (not_lt.mp hne) with h₂ | h₂
    · have hS₂ : ¬S p₂ := fun hS => hn₂ ((hb₁ p₂ h₂).mp hS)
      exact hS₂ ((hbelow p₂ (h₂.trans h₁)).mpr ht₂)
    · exact hn₂ (h₂ ▸ hu₁)
  · -- `p₁ = p`: the first difference is at the incremented atom
    subst h₁
    rcases lt_or_eq_of_le hle₂ with h₂ | h₂
    · exact hn₂ ((hb₁ p₂ h₂).mp ((hbelow p₂ h₂).mpr ht₂))
    · exact hn₂ (h₂ ▸ hu₁)

/-- **The increment is the covering relation** of the binary-number order on
subsets. -/
theorem setSucc_iff (S T : I → Prop) : SetSucc S T ↔ SetCovBy S T := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  refine ⟨setCovBy_of_setSucc, fun hcov => ?_⟩
  -- the increment position: the greatest atom `S` misses
  have hmiss : (Finset.univ.filter fun q => ¬S q).Nonempty := by
    obtain ⟨p, -, hnp, -⟩ := (setLinearOrder_lt_iff S T).mp hcov.1
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hnp⟩⟩
  set p := (Finset.univ.filter fun q => ¬S q).max' hmiss with hp
  have hnp : ¬S p := (Finset.mem_filter.mp ((Finset.univ.filter fun q => ¬S q).max'_mem hmiss)).2
  have habove : ∀ q, p < q → S q := by
    intro q hq
    by_contra hS
    exact absurd (Finset.le_max' _ q (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hS⟩))
      (not_le.mpr hq)
  have hT' : SetSucc S fun q => (q < p ∧ S q) ∨ q = p := by
    refine ⟨p, fun q hq => ?_, hnp, Or.inr rfl, fun q hq => ⟨habove q hq, ?_⟩⟩
    · refine ⟨fun hs => Or.inl ⟨hq, hs⟩, ?_⟩
      rintro (⟨-, hs⟩ | rfl)
      · exact hs
      · exact absurd hq (lt_irrefl _)
    · rintro (⟨hlt, -⟩ | rfl)
      · exact absurd (hq.trans hlt) (lt_irrefl _)
      · exact absurd hq (lt_irrefl _)
  have hcov' := setCovBy_of_setSucc hT'
  have heq : T = fun q => (q < p ∧ S q) ∨ q = p :=
    @le_antisymm _ (setLinearOrder I).toPartialOrder _ _
      ((@not_lt _ (setLinearOrder I) _ _).mp fun h => hcov.2 _ hcov'.1 h)
      ((@not_lt _ (setLinearOrder I) _ _).mp fun h => hcov'.2 _ hcov.1 h)
  rw [heq]
  exact hT'

end SetOrder

/-! ### The honest atom index

An assignment is an arbitrary subset of the **real** atoms `Σ i, Fin (arity i) → A`
– unlike the padded atoms, where only the padding-invariant subsets occur – so
the increment of §the module docstring applies to the real ones unchanged. The
two index types order assignments the same way, which is
`DescriptiveComplexity.SOBlock.atomSet_lt_iff_realSet`: a real atom has a
*least* padded representative, the one padded with the least element of `A`, and
comparing those representatives is comparing the real atoms. -/

section RealAtoms

/-- The least element of a finite nonempty linear order. -/
private noncomputable def minEl (A : Type) [LinearOrder A] [Finite A] [Nonempty A] : A :=
  (Finite.exists_min (id : A → A)).choose

private theorem minEl_le {A : Type} [LinearOrder A] [Finite A] [Nonempty A] (a : A) :
    minEl A ≤ a :=
  (Finite.exists_min (id : A → A)).choose_spec a

namespace SOBlock

variable (B : SOBlock) {A : Type} [LinearOrder A] [Finite A] [Nonempty A]

variable (A) in
/-- The **real** atoms of a block: a relation variable together with a tuple of
*its own* arity. An assignment is an arbitrary subset of these. -/
abbrev RealIx : Type := (i : B.ι) × (Fin (B.arity i) → A)

/-- The real atoms an assignment makes true – the assignment itself, uncurried,
so this is a bijection onto the subsets. -/
def realSet (ρ : B.Assignment A) : B.RealIx A → Prop := fun P => ρ P.1 P.2

/-- The real atom a padded one stands for. -/
noncomputable def realOf (p : B.AtomIx A) : B.RealIx A :=
  ⟨p.1, fun j => p.2 (Fin.castLE (arity_le_blockArityBound B p.1) j)⟩

/-- A tuple of the arity of `i`, padded out with the least element – the
*least* padded representative of a real atom. -/
noncomputable def padMin (i : B.ι) (u : Fin (B.arity i) → A) :
    Fin (blockArityBound B) → A :=
  fun k => if h : (k : ℕ) < B.arity i then u ⟨k, h⟩ else minEl A

/-- The least padded representative of a real atom. -/
noncomputable def keyIx (P : B.RealIx A) : B.AtomIx A := (P.1, B.padMin P.1 P.2)

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem atomSet_eq_realSet (ρ : B.Assignment A) (p : B.AtomIx A) :
    B.atomSet ρ p = B.realSet ρ (B.realOf p) := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem realSet_surjective : Function.Surjective (B.realSet (A := A)) :=
  fun S => ⟨fun i u => S ⟨i, u⟩, rfl⟩

theorem padMin_apply_of_lt (i : B.ι) (u : Fin (B.arity i) → A)
    (k : Fin (blockArityBound B)) (hk : (k : ℕ) < B.arity i) :
    B.padMin i u k = u ⟨k, hk⟩ := by
  simp only [padMin, dif_pos hk]

theorem padMin_apply_of_ge (i : B.ι) (u : Fin (B.arity i) → A)
    (k : Fin (blockArityBound B)) (hk : ¬(k : ℕ) < B.arity i) :
    B.padMin i u k = minEl A := by
  simp only [padMin, dif_neg hk]

theorem padMin_castLE (i : B.ι) (u : Fin (B.arity i) → A) (j : Fin (B.arity i)) :
    B.padMin i u (Fin.castLE (arity_le_blockArityBound B i) j) = u j := by
  rw [B.padMin_apply_of_lt i u _ j.isLt]
  exact congrArg u (Fin.val_injective rfl)

@[simp]
theorem realOf_keyIx (P : B.RealIx A) : B.realOf (B.keyIx P) = P := by
  obtain ⟨i, u⟩ := P
  exact Sigma.ext rfl (heq_of_eq (funext fun j => B.padMin_castLE i u j))

theorem keyIx_injective : Function.Injective (B.keyIx (A := A)) := by
  intro P Q h
  rw [← B.realOf_keyIx P, ← B.realOf_keyIx Q, h]

variable (A) in
/-- **The real atoms are linearly ordered**, by their least padded
representatives. -/
@[instance_reducible]
noncomputable def realIxLinearOrder : LinearOrder (B.RealIx A) :=
  letI := B.atomIxLinearOrder A
  LinearOrder.lift' B.keyIx B.keyIx_injective

theorem realIx_lt_iff (P Q : B.RealIx A) :
    ((B.realIxLinearOrder A).lt P Q ↔ B.atomLt (B.keyIx P) (B.keyIx Q)) :=
  B.atomIx_lt_iff _ _

/-- Comparing least padded representatives is comparing the tuples they pad. -/
theorem padMin_lt_iff (i : B.ι) (u v : Fin (B.arity i) → A) :
    (toLex (B.padMin i u) < toLex (B.padMin i v) ↔ toLex u < toLex v) := by
  constructor
  · rintro ⟨k, hag, hlt⟩
    have hag' : ∀ j : Fin (blockArityBound B), j < k → B.padMin i u j = B.padMin i v j := hag
    have hlt' : B.padMin i u k < B.padMin i v k := hlt
    have hk : (k : ℕ) < B.arity i := by
      by_contra hk
      rw [B.padMin_apply_of_ge i u k hk, B.padMin_apply_of_ge i v k hk] at hlt'
      exact absurd hlt' (lt_irrefl _)
    refine ⟨⟨k, hk⟩, fun j hj => ?_, ?_⟩
    · change u j = v j
      have hcast : (Fin.castLE (arity_le_blockArityBound B i) j : Fin (blockArityBound B)) < k :=
        Fin.lt_def.mpr (Fin.lt_def.mp hj)
      have h := hag' _ hcast
      rwa [B.padMin_castLE, B.padMin_castLE] at h
    · change u ⟨k, hk⟩ < v ⟨k, hk⟩
      rw [← B.padMin_apply_of_lt i u k hk, ← B.padMin_apply_of_lt i v k hk]
      exact hlt'
  · rintro ⟨j, hag, hlt⟩
    have hag' : ∀ m : Fin (B.arity i), m < j → u m = v m := hag
    have hlt' : u j < v j := hlt
    refine ⟨Fin.castLE (arity_le_blockArityBound B i) j, fun k hk => ?_, ?_⟩
    · change B.padMin i u k = B.padMin i v k
      have hkv : (k : ℕ) < (j : ℕ) := Fin.lt_def.mp hk
      have hk' : (k : ℕ) < B.arity i := lt_trans hkv j.isLt
      rw [B.padMin_apply_of_lt i u k hk', B.padMin_apply_of_lt i v k hk']
      exact hag' ⟨k, hk'⟩ (Fin.lt_def.mpr hkv)
    · change B.padMin i u _ < B.padMin i v _
      rw [B.padMin_castLE, B.padMin_castLE]
      exact hlt'

/-- **The least padded representative is least**: no padded atom of the same
real atom is below it. -/
theorem keyIx_realOf_le (p : B.AtomIx A) :
    (B.atomIxLinearOrder A).le (B.keyIx (B.realOf p)) p := by
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  refine (@not_lt _ (B.atomIxLinearOrder A) _ _).mp fun h => ?_
  rcases (B.atomIx_lt_iff p (B.keyIx (B.realOf p))).mp h with h1 | ⟨-, h2⟩
  · exact absurd h1 (lt_irrefl _)
  · obtain ⟨k, -, hlt⟩ := h2
    have hlt' : p.2 k < B.padMin p.1 (B.realOf p).2 k := hlt
    by_cases hk : (k : ℕ) < B.arity p.1
    · rw [B.padMin_apply_of_lt p.1 (B.realOf p).2 k hk] at hlt'
      have heq : (B.realOf p).2 ⟨(k : ℕ), hk⟩ = p.2 k :=
        congrArg p.2 (Fin.val_injective rfl)
      exact absurd (lt_of_lt_of_eq hlt' heq) (lt_irrefl _)
    · rw [B.padMin_apply_of_ge p.1 (B.realOf p).2 k hk] at hlt'
      exact absurd hlt' (not_lt.mpr (minEl_le _))

/-- **The two atom indices order assignments the same way.** -/
theorem atomSet_lt_iff_realSet (ρ σ : B.Assignment A) :
    letI := B.atomIxLinearOrder A
    letI := B.realIxLinearOrder A
    ((setLinearOrder (B.AtomIx A)).lt (B.atomSet ρ) (B.atomSet σ) ↔
      (setLinearOrder (B.RealIx A)).lt (B.realSet ρ) (B.realSet σ)) := by
  letI := B.realIxLinearOrder A
  letI := B.atomIxLinearOrder A
  rw [B.atomSet_lt_iff ρ σ, setLinearOrder_lt_iff]
  constructor
  · rintro ⟨p, hbelow, hnp, hp⟩
    refine ⟨B.realOf p, fun Q hQ => ?_, hnp, hp⟩
    have h1 : (B.atomIxLinearOrder A).lt (B.keyIx Q) p :=
      @lt_of_lt_of_le _ (B.atomIxLinearOrder A).toPreorder _ _ _
        ((B.atomIx_lt_iff _ _).mpr ((B.realIx_lt_iff Q (B.realOf p)).mp hQ))
        (B.keyIx_realOf_le p)
    have := hbelow (B.keyIx Q) ((B.atomIx_lt_iff _ _).mp h1)
    rwa [B.atomSet_eq_realSet, B.atomSet_eq_realSet, B.realOf_keyIx] at this
  · rintro ⟨P, hbelow, hnp, hp⟩
    refine ⟨B.keyIx P, fun q hq => ?_, ?_, ?_⟩
    · have h1 : (B.atomIxLinearOrder A).lt (B.keyIx (B.realOf q)) (B.keyIx P) :=
        lt_of_le_of_lt (B.keyIx_realOf_le q) ((B.atomIx_lt_iff _ _).mpr hq)
      have := hbelow (B.realOf q) ((B.realIx_lt_iff _ _).mpr ((B.atomIx_lt_iff _ _).mp h1))
      rwa [← B.atomSet_eq_realSet, ← B.atomSet_eq_realSet] at this
    · rwa [B.atomSet_eq_realSet, B.realOf_keyIx]
    · rwa [B.atomSet_eq_realSet, B.realOf_keyIx]

/-- **The successor of an assignment is the increment at its real atoms**: the
right-hand side says that no assignment lies strictly between. -/
theorem assignSucc_iff (ρ σ : B.Assignment A) :
    letI := B.atomIxLinearOrder A
    letI := B.realIxLinearOrder A
    (SetSucc (B.realSet ρ) (B.realSet σ) ↔
      ((setLinearOrder (B.AtomIx A)).lt (B.atomSet ρ) (B.atomSet σ) ∧
        ∀ τ : B.Assignment A, (setLinearOrder (B.AtomIx A)).lt (B.atomSet ρ) (B.atomSet τ) →
          ¬(setLinearOrder (B.AtomIx A)).lt (B.atomSet τ) (B.atomSet σ))) := by
  letI := B.realIxLinearOrder A
  rw [setSucc_iff, SetCovBy]
  refine and_congr (B.atomSet_lt_iff_realSet ρ σ).symm ?_
  constructor
  · intro h τ hτ
    exact fun hτ' => h (B.realSet τ) ((B.atomSet_lt_iff_realSet ρ τ).mp hτ)
      ((B.atomSet_lt_iff_realSet τ σ).mp hτ')
  · intro h U hU hU'
    obtain ⟨τ, rfl⟩ := B.realSet_surjective U
    exact h τ ((B.atomSet_lt_iff_realSet ρ τ).mpr hU) ((B.atomSet_lt_iff_realSet τ σ).mpr hU')

end SOBlock

end RealAtoms

/-! ### The increment as a sentence -/

namespace SOBlock

variable {L : Language.{0, 0}} (B : SOBlock)

/-- The relation variables strictly above `i`, in the arbitrary order on the
block's index type – the mirror of
`DescriptiveComplexity.SOBlock.ivarsBelow`, and the atoms the increment clears. -/
noncomputable def ivarsAbove (i : B.ι) : List B.ι :=
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  B.ivars.filter fun j => decide (i < j)

theorem mem_ivarsAbove (i j : B.ι) :
    letI : LinearOrder B.ι := finiteLinearOrder B.ι
    (j ∈ B.ivarsAbove i ↔ i < j) := by
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  rw [ivarsAbove, List.mem_filter]
  simp [B.mem_ivars j]

open Classical in
variable (L) in
/-- **The increment, as a sentence**: at some atom the first copy is false and
the second true; the copies agree strictly below it; and strictly above it the
first is true and the second false. Each of the two conditions on the other
atoms splits, as in `DescriptiveComplexity.SOBlock.ordLtF`, into a static part
over the earlier (or later) relation variables and a lexicographic part at the
same variable – taken on the **truncated** tuples, so that it compares *real*
atoms and not their padded representatives (see the padding trap above). -/
noncomputable def succAssignF : ((L.sum Language.order).sum (B.replicate 2).lang).Sentence :=
  listSup (B.ivars.map fun i =>
    Formula.iExs (Fin (blockArityBound B))
      ((∼(B.atomF L 0 i Sum.inr) ⊓ B.atomF L 1 i Sum.inr)
        ⊓ ((listInf ((B.ivarsBelow i).map fun j =>
              Formula.iAlls (Fin (blockArityBound B))
                (B.atomF L 0 j Sum.inr ⇔ B.atomF L 1 j Sum.inr))
            ⊓ Formula.iAlls (Fin (blockArityBound B))
                (LHom.sumInl.onFormula (lexSelLtF (L := L)
                    (fun j : Fin (B.arity i) =>
                      Sum.inr (Fin.castLE (arity_le_blockArityBound B i) j))
                    (fun j : Fin (B.arity i) =>
                      Sum.inl (Sum.inr (Fin.castLE (arity_le_blockArityBound B i) j))))
                  ⟹ (B.atomF L 0 i Sum.inr ⇔ B.atomF L 1 i Sum.inr)))
          ⊓ (listInf ((B.ivarsAbove i).map fun j =>
                Formula.iAlls (Fin (blockArityBound B))
                  (B.atomF L 0 j Sum.inr ⊓ ∼(B.atomF L 1 j Sum.inr)))
            ⊓ Formula.iAlls (Fin (blockArityBound B))
                (LHom.sumInl.onFormula (lexSelLtF (L := L)
                    (fun j : Fin (B.arity i) =>
                      Sum.inl (Sum.inr (Fin.castLE (arity_le_blockArityBound B i) j)))
                    (fun j : Fin (B.arity i) =>
                      Sum.inr (Fin.castLE (arity_le_blockArityBound B i) j)))
                  ⟹ (B.atomF L 0 i Sum.inr ⊓ ∼(B.atomF L 1 i Sum.inr)))))))

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- Quantifying a padded tuple is quantifying its truncation: every tuple of the
arity of `i` is the truncation of one, namely of its least padded
representative. -/
theorem forall_trunc_iff (i : B.ι) (P : (Fin (B.arity i) → A) → Prop) :
    ((∀ y : Fin (blockArityBound B) → A,
        P fun j => y (Fin.castLE (arity_le_blockArityBound B i) j)) ↔ ∀ v, P v) := by
  constructor
  · intro h v
    have h' := h (B.padMin i v)
    rwa [funext fun j => B.padMin_castLE i v j] at h'
  · intro h y
    exact h _

/-- The two agreement conjuncts say exactly “the copies agree at every real atom
strictly below the witnessed one”. -/
theorem agree_below_real (ρs : Fin 2 → B.Assignment A) (i : B.ι) (u : Fin (B.arity i) → A) :
    (((∀ j ∈ B.ivarsBelow i, ∀ v : Fin (B.arity j) → A, (ρs 0 j v ↔ ρs 1 j v)) ∧
        ∀ v : Fin (B.arity i) → A, toLex v < toLex u → (ρs 0 i v ↔ ρs 1 i v)) ↔
      ∀ Q : B.RealIx A, B.atomLt (B.keyIx Q) (B.keyIx ⟨i, u⟩) →
        (B.realSet (ρs 0) Q ↔ B.realSet (ρs 1) Q)) := by
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  constructor
  · rintro ⟨hb, hs⟩ ⟨j, v⟩ hq
    rcases hq with hji | ⟨rfl, hv⟩
    · exact hb j ((B.mem_ivarsBelow i j).mpr hji) v
    · exact hs v ((B.padMin_lt_iff j v u).mp hv)
  · intro h
    refine ⟨fun j hj v => h ⟨j, v⟩ ?_, fun v hv => h ⟨i, v⟩ ?_⟩
    · exact Or.inl ((B.mem_ivarsBelow i j).mp hj)
    · exact Or.inr ⟨rfl, (B.padMin_lt_iff i v u).mpr hv⟩

/-- The two clearing conjuncts say exactly “the first copy holds and the second
does not, at every real atom strictly above the witnessed one”. -/
theorem clear_above_real (ρs : Fin 2 → B.Assignment A) (i : B.ι) (u : Fin (B.arity i) → A) :
    (((∀ j ∈ B.ivarsAbove i, ∀ v : Fin (B.arity j) → A, (ρs 0 j v ∧ ¬ρs 1 j v)) ∧
        ∀ v : Fin (B.arity i) → A, toLex u < toLex v → (ρs 0 i v ∧ ¬ρs 1 i v)) ↔
      ∀ Q : B.RealIx A, B.atomLt (B.keyIx ⟨i, u⟩) (B.keyIx Q) →
        (B.realSet (ρs 0) Q ∧ ¬B.realSet (ρs 1) Q)) := by
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  constructor
  · rintro ⟨hb, hs⟩ ⟨j, v⟩ hq
    rcases hq with hij | ⟨rfl, hv⟩
    · exact hb j ((B.mem_ivarsAbove i j).mpr hij) v
    · exact hs v ((B.padMin_lt_iff i u v).mp hv)
  · intro h
    refine ⟨fun j hj v => h ⟨j, v⟩ ?_, fun v hv => h ⟨i, v⟩ ?_⟩
    · exact Or.inl ((B.mem_ivarsAbove i j).mp hj)
    · exact Or.inr ⟨rfl, (B.padMin_lt_iff i u v).mpr hv⟩

/-- **What the increment sentence says**, spelled out at real atoms. -/
theorem realize_succAssignF_aux (ρs : Fin 2 → B.Assignment A) :
    (@Sentence.Realize _ A
        ((B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs))
        (B.succAssignF L) ↔
      ∃ (i : B.ι) (u : Fin (B.arity i) → A),
        ((∀ j ∈ B.ivarsBelow i, ∀ v : Fin (B.arity j) → A, (ρs 0 j v ↔ ρs 1 j v)) ∧
            ∀ v : Fin (B.arity i) → A, toLex v < toLex u → (ρs 0 i v ↔ ρs 1 i v)) ∧
          ¬ρs 0 i u ∧ ρs 1 i u ∧
          ((∀ j ∈ B.ivarsAbove i, ∀ v : Fin (B.arity j) → A, (ρs 0 j v ∧ ¬ρs 1 j v)) ∧
            ∀ v : Fin (B.arity i) → A, toLex u < toLex v → (ρs 0 i v ∧ ¬ρs 1 i v))) := by
  letI := (B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs)
  rw [succAssignF, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨φ, hφ, hr⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hφ
    simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_not,
      B.realize_atomF ρs, Sum.elim_inr] at hr
    obtain ⟨x, ⟨h0, h1⟩, ⟨hbelow, hsame⟩, hclear, habove⟩ := hr
    refine ⟨i, fun j => x (Fin.castLE (arity_le_blockArityBound B i) j),
      ⟨fun j hj v => ?_, fun v hv => ?_⟩, h0, h1, fun j hj v => ?_, fun v hv => ?_⟩
    · refine (B.forall_trunc_iff j fun w => (ρs 0 j w ↔ ρs 1 j w)).mp (fun y => ?_) v
      have h2 := Formula.realize_iAlls.mp
        ((realize_listInf _).mp hbelow _ (List.mem_map.mpr ⟨j, hj, rfl⟩)) y
      simpa only [Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr, atomSet] using h2
    · refine (B.forall_trunc_iff i fun w => toLex w <
        toLex (fun j => x (Fin.castLE (arity_le_blockArityBound B i) j)) →
          (ρs 0 i w ↔ ρs 1 i w)).mp (fun y => ?_) v hv
      intro hy
      have h2 := Formula.realize_iAlls.mp hsame y
      simp only [Formula.realize_imp, LHom.realize_onFormula, realize_lexSelLtF,
        Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr, Sum.elim_inl,
        Function.comp_def] at h2
      exact h2 hy
    · refine (B.forall_trunc_iff j fun w => (ρs 0 j w ∧ ¬ρs 1 j w)).mp (fun y => ?_) v
      have h2 := Formula.realize_iAlls.mp
        ((realize_listInf _).mp hclear _ (List.mem_map.mpr ⟨j, hj, rfl⟩)) y
      simpa only [Formula.realize_inf, Formula.realize_not, B.realize_atomF ρs,
        Sum.elim_inr, atomSet] using h2
    · refine (B.forall_trunc_iff i fun w =>
        toLex (fun j => x (Fin.castLE (arity_le_blockArityBound B i) j)) < toLex w →
          (ρs 0 i w ∧ ¬ρs 1 i w)).mp (fun y => ?_) v hv
      intro hy
      have h2 := Formula.realize_iAlls.mp habove y
      simp only [Formula.realize_imp, LHom.realize_onFormula, realize_lexSelLtF,
        Formula.realize_inf, Formula.realize_not, B.realize_atomF ρs, Sum.elim_inr,
        Sum.elim_inl, Function.comp_def] at h2
      exact h2 hy
  · rintro ⟨i, u, ⟨hbelow, hsame⟩, h0, h1, hclear, habove⟩
    refine ⟨_, List.mem_map.mpr ⟨i, B.mem_ivars i, rfl⟩,
      Formula.realize_iExs.mpr ⟨B.padMin i u, ?_⟩⟩
    have hpad : (fun j => B.padMin i u (Fin.castLE (arity_le_blockArityBound B i) j)) = u :=
      funext fun j => B.padMin_castLE i u j
    refine Formula.realize_inf.mpr ⟨Formula.realize_inf.mpr ⟨?_, ?_⟩,
      Formula.realize_inf.mpr ⟨Formula.realize_inf.mpr ⟨?_, ?_⟩,
        Formula.realize_inf.mpr ⟨?_, ?_⟩⟩⟩
    · simp only [Formula.realize_not, B.realize_atomF ρs, Sum.elim_inr]
      change ¬ρs 0 i (fun j => B.padMin i u (Fin.castLE (arity_le_blockArityBound B i) j))
      rwa [hpad]
    · simp only [B.realize_atomF ρs, Sum.elim_inr]
      change ρs 1 i (fun j => B.padMin i u (Fin.castLE (arity_le_blockArityBound B i) j))
      rwa [hpad]
    · refine (realize_listInf _).mpr fun ψ hψ => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hψ
      refine Formula.realize_iAlls.mpr fun y => ?_
      simpa only [Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr, atomSet]
        using hbelow j hj _
    · refine Formula.realize_iAlls.mpr fun y => ?_
      simp only [Formula.realize_imp, LHom.realize_onFormula, realize_lexSelLtF,
        Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr, Sum.elim_inl,
        Function.comp_def]
      rw [hpad]
      exact hsame _
    · refine (realize_listInf _).mpr fun ψ hψ => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hψ
      refine Formula.realize_iAlls.mpr fun y => ?_
      simpa only [Formula.realize_inf, Formula.realize_not, B.realize_atomF ρs,
        Sum.elim_inr, atomSet] using hclear j hj _
    · refine Formula.realize_iAlls.mpr fun y => ?_
      simp only [Formula.realize_imp, LHom.realize_onFormula, realize_lexSelLtF,
        Formula.realize_inf, Formula.realize_not, B.realize_atomF ρs, Sum.elim_inr,
        Sum.elim_inl, Function.comp_def]
      rw [hpad]
      exact habove _

/-- **The increment sentence is the successor of an assignment**: it holds of
two assignments exactly when the second is the increment of the first at their
real atoms – which, by
`DescriptiveComplexity.SOBlock.assignSucc_iff`, is exactly the immediate
successor in the order the expanded universe carries. -/
theorem realize_succAssignF (ρs : Fin 2 → B.Assignment A) :
    letI := B.realIxLinearOrder A
    (@Sentence.Realize _ A
        ((B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs))
        (B.succAssignF L) ↔
      SetSucc (B.realSet (ρs 0)) (B.realSet (ρs 1))) := by
  letI := B.realIxLinearOrder A
  rw [B.realize_succAssignF_aux ρs]
  constructor
  · rintro ⟨i, u, hbelow, h0, h1, habove⟩
    exact ⟨⟨i, u⟩, fun Q hQ => (B.agree_below_real ρs i u).mp hbelow Q
        ((B.realIx_lt_iff _ _).mp hQ), h0, h1,
      fun Q hQ => (B.clear_above_real ρs i u).mp habove Q ((B.realIx_lt_iff _ _).mp hQ)⟩
  · rintro ⟨⟨i, u⟩, hbelow, h0, h1, habove⟩
    exact ⟨i, u, (B.agree_below_real ρs i u).mpr
        (fun Q hQ => hbelow Q ((B.realIx_lt_iff _ _).mpr hQ)), h0, h1,
      (B.clear_above_real ρs i u).mpr fun Q hQ => habove Q ((B.realIx_lt_iff _ _).mpr hQ)⟩

/-! ### The two endpoints -/

open Classical in
variable (L) in
/-- The copy `c` of the block holds of no padded atom. -/
noncomputable def botAssignF (c : Fin 2) :
    ((L.sum Language.order).sum (B.replicate 2).lang).Sentence :=
  listInf (B.ivars.map fun i =>
    Formula.iAlls (Fin (blockArityBound B)) (∼(B.atomF L c i Sum.inr)))

open Classical in
variable (L) in
/-- The copy `c` of the block holds of every padded atom. -/
noncomputable def topAssignF (c : Fin 2) :
    ((L.sum Language.order).sum (B.replicate 2).lang).Sentence :=
  listInf (B.ivars.map fun i =>
    Formula.iAlls (Fin (blockArityBound B)) (B.atomF L c i Sum.inr))

omit [Finite A] [Nonempty A] in
theorem realize_botAssignF (ρs : Fin 2 → B.Assignment A) (c : Fin 2) :
    (@Sentence.Realize _ A
        ((B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs))
        (B.botAssignF L c) ↔ B.atomSet (ρs c) = fun _ => False) := by
  letI := (B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs)
  rw [botAssignF, Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext q
    obtain ⟨i, x⟩ := q
    have h2 := Formula.realize_iAlls.mp (h _ (List.mem_map.mpr ⟨i, B.mem_ivars i, rfl⟩)) x
    simp only [Formula.realize_not, B.realize_atomF ρs, Sum.elim_inr] at h2
    exact propext ⟨fun hx => absurd hx h2, fun hx => hx.elim⟩
  · intro h ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    refine Formula.realize_iAlls.mpr fun x => ?_
    simp only [Formula.realize_not, B.realize_atomF ρs, Sum.elim_inr]
    exact fun hx => (h ▸ hx : (fun _ => False) (i, x))

omit [Finite A] [Nonempty A] in
theorem realize_topAssignF (ρs : Fin 2 → B.Assignment A) (c : Fin 2) :
    (@Sentence.Realize _ A
        ((B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs))
        (B.topAssignF L c) ↔ B.atomSet (ρs c) = fun _ => True) := by
  letI := (B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs)
  rw [topAssignF, Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext q
    obtain ⟨i, x⟩ := q
    have h2 := Formula.realize_iAlls.mp (h _ (List.mem_map.mpr ⟨i, B.mem_ivars i, rfl⟩)) x
    simp only [B.realize_atomF ρs, Sum.elim_inr] at h2
    exact propext ⟨fun _ => trivial, fun _ => h2⟩
  · intro h ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    refine Formula.realize_iAlls.mpr fun x => ?_
    simp only [B.realize_atomF ρs, Sum.elim_inr]
    exact (h ▸ trivial : B.atomSet (ρs c) (i, x))

variable (A) in
/-- The assignment holding of everything – the greatest one. -/
def topAssign : B.Assignment A := fun _ _ => True

end SOBlock

/-! ### The endpoints and the successor, at the points of an expansion

What a machine walking an expanded universe asks of its order
(`DescriptiveComplexity.HeadMove`): which point is least, which is greatest, and
which is the immediate successor of which. Tag first and then the assignment, so
each answer splits: the tag part is *static* – finitely many tags, compared at
formula-construction time – and the assignment part is the increment above. The
lexicographic bookkeeping is `DescriptiveComplexity.prodLex_le_iff` and its
siblings, with one caveat: a point's second component is an *assignment*, not an
arbitrary set, so the witnesses put between two points must be assignments too –
the empty one, the full one, and the ones the walk itself carries. -/

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : ExpExpansion L) (A : Type)
variable [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [L.Structure A] in
theorem pointLe_iff (p q : X.Point A) :
    letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
    letI := X.B.atomIxLinearOrder A
    ((X.pointLinearOrder A).le p q ↔
      p.1 < q.1 ∨ (p.1 = q.1 ∧
        (setLinearOrder (X.B.AtomIx A)).le (X.B.atomSet p.2) (X.B.atomSet q.2))) := by
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  letI := X.B.atomIxLinearOrder A
  letI := setLinearOrder (X.B.AtomIx A)
  exact prodLex_le_iff

omit [L.Structure A] in
theorem pointLt_iff (p q : X.Point A) :
    letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
    letI := X.B.atomIxLinearOrder A
    ((X.pointLinearOrder A).lt p q ↔
      p.1 < q.1 ∨ (p.1 = q.1 ∧
        (setLinearOrder (X.B.AtomIx A)).lt (X.B.atomSet p.2) (X.B.atomSet q.2))) := by
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  letI := X.B.atomIxLinearOrder A
  letI := setLinearOrder (X.B.AtomIx A)
  exact prodLex_lt_iff

omit [L.Structure A] in
/-- **The least point**: the least tag, holding of nothing. -/
theorem pointIsBot_iff (p : X.Point A) :
    letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
    ((∀ q : X.Point A, (X.pointLinearOrder A).le p q) ↔
      ((∀ t : X.Tag, p.1 ≤ t) ∧ X.B.atomSet p.2 = fun _ => False)) := by
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  letI := X.B.atomIxLinearOrder A
  have hbot : X.B.atomSet (X.B.botAssign A) = fun _ => False := rfl
  constructor
  · intro h
    refine ⟨fun t => ?_, ?_⟩
    · rcases (X.pointLe_iff A p (t, X.B.botAssign A)).mp (h _) with hl | ⟨he, -⟩
      · exact hl.le
      · exact he.le
    · rcases (X.pointLe_iff A p (p.1, X.B.botAssign A)).mp (h _) with hl | ⟨-, hle⟩
      · exact absurd hl (lt_irrefl _)
      · rw [hbot] at hle
        exact @le_antisymm _ (setLinearOrder (X.B.AtomIx A)).toPartialOrder _ _ hle
          (setLinearOrder_bot_le _)
  · rintro ⟨ht, hb⟩ q
    refine (X.pointLe_iff A p q).mpr ?_
    rcases eq_or_lt_of_le (ht q.1) with he | hl
    · exact Or.inr ⟨he, by rw [hb]; exact setLinearOrder_bot_le _⟩
    · exact Or.inl hl

omit [L.Structure A] in
/-- **The greatest point**: the greatest tag, holding of everything. -/
theorem pointIsTop_iff (p : X.Point A) :
    letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
    ((∀ q : X.Point A, (X.pointLinearOrder A).le q p) ↔
      ((∀ t : X.Tag, t ≤ p.1) ∧ X.B.atomSet p.2 = fun _ => True)) := by
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  letI := X.B.atomIxLinearOrder A
  have htop : X.B.atomSet (X.B.topAssign A) = fun _ => True := rfl
  constructor
  · intro h
    refine ⟨fun t => ?_, ?_⟩
    · rcases (X.pointLe_iff A (t, X.B.topAssign A) p).mp (h _) with hl | ⟨he, -⟩
      · exact hl.le
      · exact he.le
    · rcases (X.pointLe_iff A (p.1, X.B.topAssign A) p).mp (h _) with hl | ⟨-, hle⟩
      · exact absurd hl (lt_irrefl _)
      · rw [htop] at hle
        exact @le_antisymm _ (setLinearOrder (X.B.AtomIx A)).toPartialOrder _ _
          (setLinearOrder_le_top _) hle
  · rintro ⟨ht, hb⟩ q
    refine (X.pointLe_iff A q p).mpr ?_
    rcases eq_or_lt_of_le (ht q.1) with he | hl
    · exact Or.inr ⟨he, by rw [hb]; exact setLinearOrder_le_top _⟩
    · exact Or.inl hl

omit [L.Structure A] in
/-- **The successor of a point**: either the tag stays and the assignment is
incremented, or the tag steps and the assignment rolls over from full to
empty. -/
theorem pointCovBy_iff (p q : X.Point A) :
    letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
    letI := X.B.realIxLinearOrder A
    (((X.pointLinearOrder A).lt p q ∧
        ∀ r : X.Point A, ¬((X.pointLinearOrder A).lt p r ∧ (X.pointLinearOrder A).lt r q)) ↔
      ((p.1 = q.1 ∧ SetSucc (X.B.realSet p.2) (X.B.realSet q.2)) ∨
        (p.1 < q.1 ∧ (∀ t : X.Tag, ¬(p.1 < t ∧ t < q.1)) ∧
          X.B.atomSet p.2 = (fun _ => True) ∧ X.B.atomSet q.2 = fun _ => False))) := by
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  letI := X.B.atomIxLinearOrder A
  letI := X.B.realIxLinearOrder A
  have hbot : X.B.atomSet (X.B.botAssign A) = fun _ => False := rfl
  have htop : X.B.atomSet (X.B.topAssign A) = fun _ => True := rfl
  constructor
  · rintro ⟨hlt, hnb⟩
    rcases (X.pointLt_iff A p q).mp hlt with htag | ⟨he, hass⟩
    · refine Or.inr ⟨htag, fun t ht => ?_, ?_, ?_⟩
      · exact hnb (t, X.B.botAssign A)
          ⟨(X.pointLt_iff A _ _).mpr (Or.inl ht.1), (X.pointLt_iff A _ _).mpr (Or.inl ht.2)⟩
      · refine @le_antisymm _ (setLinearOrder (X.B.AtomIx A)).toPartialOrder _ _
          (setLinearOrder_le_top _) ?_
        refine (@not_lt _ (setLinearOrder (X.B.AtomIx A)) _ _).mp fun hp => ?_
        exact hnb (p.1, X.B.topAssign A)
          ⟨(X.pointLt_iff A _ _).mpr (Or.inr ⟨rfl, by rw [htop]; exact hp⟩),
            (X.pointLt_iff A _ _).mpr (Or.inl htag)⟩
      · refine @le_antisymm _ (setLinearOrder (X.B.AtomIx A)).toPartialOrder _ _ ?_
          (setLinearOrder_bot_le _)
        refine (@not_lt _ (setLinearOrder (X.B.AtomIx A)) _ _).mp fun hq => ?_
        exact hnb (q.1, X.B.botAssign A)
          ⟨(X.pointLt_iff A _ _).mpr (Or.inl htag),
            (X.pointLt_iff A _ _).mpr (Or.inr ⟨rfl, by rw [hbot]; exact hq⟩)⟩
    · refine Or.inl ⟨he, (X.B.assignSucc_iff p.2 q.2).mpr ⟨hass, fun τ hτ hτ' => ?_⟩⟩
      exact hnb (p.1, τ) ⟨(X.pointLt_iff A _ _).mpr (Or.inr ⟨rfl, hτ⟩),
        (X.pointLt_iff A _ _).mpr (Or.inr ⟨he, hτ'⟩)⟩
  · rintro (⟨he, hsucc⟩ | ⟨htag, htcov, hp, hq⟩)
    · obtain ⟨hass, hno⟩ := (X.B.assignSucc_iff p.2 q.2).mp hsucc
      refine ⟨(X.pointLt_iff A _ _).mpr (Or.inr ⟨he, hass⟩), fun r hr => ?_⟩
      rcases (X.pointLt_iff A p r).mp hr.1 with h₁ | ⟨he₁, ha₁⟩ <;>
        rcases (X.pointLt_iff A r q).mp hr.2 with h₂ | ⟨he₂, ha₂⟩
      · exact absurd (he ▸ h₁.trans h₂) (lt_irrefl _)
      · exact absurd (he ▸ he₂ ▸ h₁) (lt_irrefl _)
      · exact absurd (he ▸ he₁ ▸ h₂) (lt_irrefl _)
      · exact hno r.2 ha₁ ha₂
    · refine ⟨(X.pointLt_iff A _ _).mpr (Or.inl htag), fun r hr => ?_⟩
      rcases (X.pointLt_iff A p r).mp hr.1 with h₁ | ⟨-, ha₁⟩
      · rcases (X.pointLt_iff A r q).mp hr.2 with h₂ | ⟨-, ha₂⟩
        · exact htcov r.1 ⟨h₁, h₂⟩
        · rw [hq] at ha₂
          exact absurd ha₂ ((@not_lt _ (setLinearOrder (X.B.AtomIx A)) _ _).mpr
            (setLinearOrder_bot_le _))
      · rw [hp] at ha₁
        exact absurd ha₁ ((@not_lt _ (setLinearOrder (X.B.AtomIx A)) _ _).mpr
          (setLinearOrder_le_top _))

end ExpExpansion

end DescriptiveComplexity
