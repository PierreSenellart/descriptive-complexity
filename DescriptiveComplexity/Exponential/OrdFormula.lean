/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Order

/-!
# The defining sentence of the order on an expanded universe

`DescriptiveComplexity.Exponential.Order` orders the points of an expansion –
tag first, then the assignment read as a binary number. This file writes that
order down as a **first-order sentence over the base vocabulary and two copies
of the block**, and proves it defines exactly that order
(`DescriptiveComplexity.SOBlock.realize_ordLtF`).

Everything is first-order because a padded atom is a relation variable – of
which there are finitely many, so the choice is a static disjunction – together
with a tuple of *base* elements, which an ordinary quantifier can range over.
The sentence says:

> at some atom, the first copy is false and the second true, while the two
> copies agree at every strictly smaller atom

and “strictly smaller” splits into the two ways
`DescriptiveComplexity.SOBlock.atomIx_lt_iff` allows: a strictly earlier
relation variable – a static condition, so a finite conjunction – or the same
variable at a lexicographically earlier tuple, which is
`DescriptiveComplexity.lexSelLtF`.

The three quantifier blocks over `Fin (blockArityBound B)` are `Formula.iExs`
and `Formula.iAlls`, so the free-variable bookkeeping is `Sum.inr` for the
innermost tuple and `Sum.inl ∘ Sum.inr` for the one bound outside it.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : SOBlock)

/-! ### An enumeration of the relation variables -/

open Classical in
/-- The relation variables of a block, as a list: the finite disjunction and
conjunction of the comparison sentence range over it. -/
noncomputable def ivars : List B.ι :=
  letI : Fintype B.ι := Fintype.ofFinite B.ι
  (Finset.univ : Finset B.ι).toList

open Classical in
theorem mem_ivars (i : B.ι) : i ∈ B.ivars := by
  letI : Fintype B.ι := Fintype.ofFinite B.ι
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

/-! ### The atom of one copy -/

variable (L) in
/-- The atom “copy `c` of the block holds of the tuple selected by `sel`”: the
relation variable `i` of that copy, applied to the first `B.arity i` of the
selected variables. -/
noncomputable def atomF (c : Fin 2) (i : B.ι) {γ : Type} (sel : Fin (blockArityBound B) → γ) :
    ((L.sum Language.order).sum (B.replicate 2).lang).Formula γ :=
  Relations.formula (Sum.inr (B.replicateSym c (⟨i, rfl⟩ : B.lang.Relations (B.arity i))))
    fun j => Term.var (sel (Fin.castLE (arity_le_blockArityBound B i) j))

/-- **The atom says what it should**: the copy's assignment, at the padded atom
the selected variables name. -/
theorem realize_atomF {A : Type} [L.Structure A] [LinearOrder A]
    (ρs : Fin 2 → B.Assignment A) (c : Fin 2) (i : B.ι) {γ : Type}
    (sel : Fin (blockArityBound B) → γ) (v : γ → A) :
    @Formula.Realize _ A
        ((B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs)) _
        (B.atomF L c i sel) v ↔
      B.atomSet (ρs c) (i, fun k => v (sel k)) := by
  letI := (B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs)
  exact Iff.rfl

/-- The relation variables strictly below `i`, in the arbitrary order on the
block's index type. Factored out so that the order on `B.ι` – the one thing in
the comparison sentence that is resolved statically – is confined to this
definition and its characterization, and the sentence itself never has to be
unfolded past them. -/
noncomputable def ivarsBelow (i : B.ι) : List B.ι :=
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  B.ivars.filter fun j => decide (j < i)

theorem mem_ivarsBelow (i j : B.ι) :
    letI : LinearOrder B.ι := finiteLinearOrder B.ι
    (j ∈ B.ivarsBelow i ↔ j < i) := by
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  rw [ivarsBelow, List.mem_filter]
  simp [B.mem_ivars j]

/-! ### The comparison sentence -/

open Classical in
variable (L) in
/-- **The defining sentence of the order on an expanded universe**: at some
padded atom the first copy is false and the second true, and the two copies
agree at every strictly smaller atom – at every earlier relation variable
(statically many), and at the same variable on every lexicographically earlier
tuple. -/
noncomputable def ordLtF : ((L.sum Language.order).sum (B.replicate 2).lang).Sentence :=
  listSup (B.ivars.map fun i =>
    Formula.iExs (Fin (blockArityBound B))
      ((∼(B.atomF L 0 i Sum.inr) ⊓ B.atomF L 1 i Sum.inr)
        ⊓ listInf ((B.ivarsBelow i).map fun j =>
            Formula.iAlls (Fin (blockArityBound B))
              (B.atomF L 0 j Sum.inr ⇔ B.atomF L 1 j Sum.inr))
        ⊓ Formula.iAlls (Fin (blockArityBound B))
            (LHom.sumInl.onFormula (lexSelLtF (L := L) Sum.inr fun j => Sum.inl (Sum.inr j))
              ⟹ (B.atomF L 0 i Sum.inr ⇔ B.atomF L 1 i Sum.inr))))

/-! ### Correctness -/

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The two agreement conjuncts of the sentence say exactly “the copies agree
strictly below the witnessed atom”, by
`DescriptiveComplexity.SOBlock.atomIx_lt_iff`: an atom is below `(i, x)` either
at a strictly earlier relation variable, or at `i` on a lexicographically
earlier tuple. -/
theorem agree_below_iff (ρs : Fin 2 → B.Assignment A) (i : B.ι)
    (x : Fin (blockArityBound B) → A) :
    ((∀ j ∈ B.ivarsBelow i, ∀ y, (B.atomSet (ρs 0) (j, y) ↔ B.atomSet (ρs 1) (j, y))) ∧
        ∀ y, toLex y < toLex x → (B.atomSet (ρs 0) (i, y) ↔ B.atomSet (ρs 1) (i, y))) ↔
      ∀ q, B.atomLt q (i, x) → (B.atomSet (ρs 0) q ↔ B.atomSet (ρs 1) q) := by
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  constructor
  · rintro ⟨hb, hs⟩ ⟨j, y⟩ hq
    rcases hq with hji | ⟨rfl, hy⟩
    · exact hb j ((B.mem_ivarsBelow i j).mpr hji) y
    · exact hs y hy
  · intro h
    refine ⟨fun j hj y => h (j, y) ?_, fun y hy => h (i, y) ?_⟩
    · exact Or.inl ((B.mem_ivarsBelow i j).mp hj)
    · exact Or.inr ⟨rfl, hy⟩

/-- **The comparison sentence is the order**: it holds of two assignments
exactly when the first is below the second in the binary-number order on their
padded atoms. -/
theorem realize_ordLtF [Finite A] (ρs : Fin 2 → B.Assignment A) :
    letI := B.atomIxLinearOrder A
    (@Sentence.Realize _ A
        ((B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs))
        (B.ordLtF L) ↔
      (setLinearOrder (B.AtomIx A)).lt (B.atomSet (ρs 0)) (B.atomSet (ρs 1))) := by
  letI := B.atomIxLinearOrder A
  letI := (B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs)
  rw [B.atomSet_lt_iff (ρs 0) (ρs 1), ordLtF, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨φ, hφ, hr⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hφ
    simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_not,
      B.realize_atomF ρs, Sum.elim_inr] at hr
    obtain ⟨x, ⟨⟨h0, h1⟩, hbelow⟩, hsame⟩ := hr
    refine ⟨(i, x), (B.agree_below_iff ρs i x).mp ⟨fun j hj y => ?_, fun y hy => ?_⟩, h0, h1⟩
    · have h2 := Formula.realize_iAlls.mp
        ((realize_listInf _).mp hbelow _ (List.mem_map.mpr ⟨j, hj, rfl⟩)) y
      simpa only [Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr] using h2
    · have h2 := Formula.realize_iAlls.mp hsame y
      simp only [Formula.realize_imp, LHom.realize_onFormula, realize_lexSelLtF,
        Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr, Sum.elim_inl,
        Function.comp_def] at h2
      exact h2 hy
  · rintro ⟨⟨i, x⟩, hag, h0, h1⟩
    obtain ⟨hbelow, hsame⟩ := (B.agree_below_iff ρs i x).mpr hag
    refine ⟨_, List.mem_map.mpr ⟨i, B.mem_ivars i, rfl⟩, Formula.realize_iExs.mpr ⟨x, ?_⟩⟩
    refine Formula.realize_inf.mpr ⟨Formula.realize_inf.mpr ⟨Formula.realize_inf.mpr
      ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simpa only [Formula.realize_not, B.realize_atomF ρs, Sum.elim_inr] using h0
    · simpa only [B.realize_atomF ρs, Sum.elim_inr] using h1
    · refine (realize_listInf _).mpr fun ψ hψ => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hψ
      refine Formula.realize_iAlls.mpr fun y => ?_
      simpa only [Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr] using hbelow j hj y
    · refine Formula.realize_iAlls.mpr fun y => ?_
      simp only [Formula.realize_imp, LHom.realize_onFormula, realize_lexSelLtF,
        Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr, Sum.elim_inl,
        Function.comp_def]
      exact hsame y

/-! ### From the strict order to `≤`

An expansion defines its order by the symbol `leSymb`, so what
`DescriptiveComplexity.ExpExpansion.ordExtend` needs is the reflexive
comparison. Equality of assignments is definable in the same breath – the two
copies hold of exactly the same padded atoms – and `≤` is the disjunction. -/

variable (L) in
/-- The two copies of the block hold of exactly the same padded atoms. -/
noncomputable def eqAssignF : ((L.sum Language.order).sum (B.replicate 2).lang).Sentence :=
  listInf (B.ivars.map fun i =>
    Formula.iAlls (Fin (blockArityBound B)) (B.atomF L 0 i Sum.inr ⇔ B.atomF L 1 i Sum.inr))

theorem realize_eqAssignF (ρs : Fin 2 → B.Assignment A) :
    (@Sentence.Realize _ A
        ((B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs))
        (B.eqAssignF L) ↔ B.atomSet (ρs 0) = B.atomSet (ρs 1)) := by
  letI := (B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs)
  rw [eqAssignF, Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext p
    obtain ⟨i, x⟩ := p
    have h2 := Formula.realize_iAlls.mp
      (h _ (List.mem_map.mpr ⟨i, B.mem_ivars i, rfl⟩)) x
    simp only [Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr] at h2
    exact propext h2
  · intro h ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    refine Formula.realize_iAlls.mpr fun x => ?_
    simp only [Formula.realize_iff, B.realize_atomF ρs, Sum.elim_inr]
    exact iff_of_eq (congrFun h (i, x))

variable (L) in
/-- **The reflexive comparison of two assignments**: strictly below, or
equal. -/
noncomputable def ordLeF : ((L.sum Language.order).sum (B.replicate 2).lang).Sentence :=
  B.ordLtF L ⊔ B.eqAssignF L

theorem realize_ordLeF [Finite A] (ρs : Fin 2 → B.Assignment A) :
    letI := B.atomIxLinearOrder A
    (@Sentence.Realize _ A
        ((B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs))
        (B.ordLeF L) ↔
      (setLinearOrder (B.AtomIx A)).le (B.atomSet (ρs 0)) (B.atomSet (ρs 1))) := by
  letI := B.atomIxLinearOrder A
  letI := setLinearOrder (B.AtomIx A)
  letI := (B.replicate 2).structure₁ (L := L.sum Language.order) (B.replicateAssign ρs)
  rw [ordLeF, Sentence.Realize, Formula.realize_sup]
  rw [show (Formula.Realize (B.ordLtF L) default ↔ _) from B.realize_ordLtF ρs,
    show (Formula.Realize (B.eqAssignF L) default ↔ _) from B.realize_eqAssignF ρs]
  exact (@le_iff_lt_or_eq _ (setLinearOrder (B.AtomIx A)).toPartialOrder
    (B.atomSet (ρs 0)) (B.atomSet (ρs 1))).symm

end SOBlock

end DescriptiveComplexity
