/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.DominatingSet.Defs
import DescriptiveComplexity.Counting.Sized
import DescriptiveComplexity.Counting.Class

/-!
# #Dominating Set: counting the dominating sets of the threshold size

The counting version of `DescriptiveComplexity.DominatingSet`: the number of
dominating sets with *exactly* as many vertices as the marked set
(`DescriptiveComplexity.DomSetOfSize`). Its support is Dominating Set, a dominating
set smaller than the threshold extending to one of exactly that size
(`DescriptiveComplexity.sharpDominatingSet_support_iff`).

Membership in `#P` (`DescriptiveComplexity.sharpDominatingSet_mem_sharpP`) is the
generic argument for a solution of the threshold size
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`), domination being first-order.
Parsimonious hardness is in
`DescriptiveComplexity.Problems.DominatingSet.CountingHardness`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The set `D` dominates every vertex and has exactly as many elements as the
`Kp`-marked set. -/
def DomOfSizeOn (Adjp : A → A → Prop) (Kp : A → Prop) (D : A → Prop) : Prop :=
  (∀ v, D v ∨ ∃ u, D u ∧ Adjp u v) ∧ {v | D v}.ncard = {v | Kp v}.ncard

/-- The dominating sets of the threshold size transport along an equivalence
commuting with the two predicates. -/
def domOfSizeEquiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    {D : B → Prop // Finite B ∧ DomOfSizeOn AdjB KB D} ≃
      {D : A → Prop // Finite A ∧ DomOfSizeOn AdjA KA D} where
  toFun D := ⟨fun a => D.1 (u.symm a), u.finite_iff.mp D.2.1, fun v => by
      rcases D.2.2.1 (u.symm v) with h | ⟨w, hw, hadjw⟩
      · exact Or.inl h
      · have h := (hadj w (u.symm v)).mp hadjw
        exact Or.inr ⟨u w, by simpa using hw, by simpa using h⟩,
    (ncard_setOf_symm u D.1).symm.trans (D.2.2.2.trans (ncard_setOf_equiv u hK))⟩
  invFun T := ⟨fun b => T.1 (u b), u.finite_iff.mpr T.2.1, fun v => by
      rcases T.2.2.1 (u v) with h | ⟨w, hw, hadjw⟩
      · exact Or.inl h
      · exact Or.inr ⟨u.symm w, by simpa using hw, (hadj _ _).mpr (by simpa using hadjw)⟩,
    ((ncard_setOf_equiv u (KB := fun b => T.1 (u b)) (KA := T.1) fun _ => Iff.rfl).trans
      T.2.2.2).trans (ncard_setOf_equiv u hK).symm⟩
  left_inv D := Subtype.ext (funext fun b => by simp)
  right_inv T := Subtype.ext (funext fun a => by simp)

end Generic

section Solutions

variable (A : Type) [Language.markedGraph.Structure A]

/-- The set `D` is a dominating set with exactly as many vertices as the marked
set, in a finite marked graph. -/
def DomSetOfSize (D : A → Prop) : Prop :=
  Finite A ∧ DomOfSizeOn (fun u v : A => MGAdj u v) (fun v => MGMarked v) D

end Solutions

/-- **#Dominating Set**: the number of dominating sets with exactly as many
vertices as the marked set. -/
noncomputable def SharpDominatingSet : CountingProblem Language.markedGraph where
  Count := fun A inst => Nat.card {D : A → Prop // @DomSetOfSize A inst D}
  iso_invariant := fun e => Nat.card_congr
    (domOfSizeEquiv e.toEquiv (fun a a' => relMap_equiv₂ e mgAdj a a')
      fun a => relMap_equiv₁ e mgMarked a)

theorem sharpDominatingSet_apply (A : Type) [Language.markedGraph.Structure A] :
    SharpDominatingSet A = Nat.card {D : A → Prop // DomSetOfSize A D} :=
  rfl

/-- **The support of #Dominating Set is Dominating Set**: a dominating set at
most as large as the marked set extends to one of exactly that size. -/
theorem sharpDominatingSet_support_iff (A : Type) [Language.markedGraph.Structure A]
    [Finite A] : SharpDominatingSet.support A ↔ DominatingSet A := by
  rw [CountingProblem.support_iff, sharpDominatingSet_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨D, hfin, hdom, hcard⟩, -⟩
    exact ⟨hfin, D, hdom, hcard.le⟩
  · rintro ⟨hfin, D, hdom, hcard⟩
    have hcompl := Set.ncard_add_ncard_compl {v | D v}
    have hK := Set.ncard_le_card {v : A | MGMarked v}
    obtain ⟨T, hT, hTcard⟩ := Set.exists_subset_card_eq
      (s := {v | D v}ᶜ) (n := {v : A | MGMarked v}.ncard - {v | D v}.ncard) (by omega)
    have hunion : ({v | D v} ∪ T).ncard = {v : A | MGMarked v}.ncard := by
      rw [Set.ncard_union_eq (Set.disjoint_left.mpr fun v hv hvT => hT hvT hv), hTcard]
      omega
    refine ⟨⟨⟨fun v => v ∈ {v | D v} ∪ T, hfin, fun v => ?_, hunion⟩⟩, inferInstance⟩
    rcases hdom v with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨u, Or.inl hu, hadj⟩

/-! ### Membership -/

/-- The block of the counting definition of Dominating Set: the dominating set
itself. -/
fo_block domSelBlock over Language.markedGraph mg into domSelLang with dm where
  /-- The dominating set. -/
  sel : 1

instance : Subsingleton domSelBlock.ι :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The order-free kernel of #Dominating Set: every vertex is in the guessed
set or has a neighbor in it. -/
noncomputable def domSelKernel : domSelLang.Sentence :=
  fo% ∀ v, dmSelSym(v) ∨ ∃ u, dmSelSym(u) ∧ dmAdjSym(u, v)

/-- Realization of the order-free kernel of #Dominating Set. -/
theorem realize_domSelKernel {A : Type} [Language.markedGraph.Structure A]
    (ρ : domSelBlock.Assignment A) :
    (@Sentence.Realize domSelLang A
        (@sumStructure _ _ A _ (domSelBlock.structure ρ)) domSelKernel) ↔
      ∀ v : A, (ρ .sel fun _ => v) ∨ ∃ u : A, (ρ .sel fun _ => u) ∧ MGAdj u v := by
  let := domSelBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := domSelLang) (M := A) dmSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [domSelKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_sup,
    Formula.realize_inf, Formula.realize_iExs, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsub,
    Matrix.cons_val_zero]
  constructor
  · intro h v
    rcases h (fun _ => v) with h | ⟨u, hu⟩
    exacts [Or.inl h, Or.inr ⟨u 0, hu⟩]
  · intro h i
    rcases h (i 0) with h | ⟨u, hu⟩
    exacts [Or.inl h, Or.inr ⟨fun _ => u, hu⟩]

/-- **#Dominating Set is in `#P`.** -/
theorem sharpDominatingSet_mem_sharpP : SharpDominatingSet ∈ SharpP :=
  sharpPDefinable_of_sized_set SharpDominatingSet domSelBlock mgMarked .sel rfl domSelKernel
    (fun A _ D => ∀ v : A, D v ∨ ∃ u : A, D u ∧ MGAdj u v)
    (fun _ _ ρ => realize_domSelKernel ρ)
    fun _ _ hfin => Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hfin)

end DescriptiveComplexity
