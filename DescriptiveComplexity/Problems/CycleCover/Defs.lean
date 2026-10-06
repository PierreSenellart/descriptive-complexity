/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Hamilton.Defs
import DescriptiveComplexity.Counting.Class
import DescriptiveComplexity.Permanent.Basic

/-!
# #Cycle Cover: the permanent of a 0-1 matrix

A **cycle cover** of a digraph is a set of arcs leaving every vertex exactly
once and entering every vertex exactly once: a permutation of the vertices
along the arcs. The number of cycle covers is the **permanent** of the
adjacency matrix (`DescriptiveComplexity.sharpCycleCover_eq_bperm`), and
the number of perfect matchings of the bipartite graph whose two sides are
two copies of the vertices, joined along the arcs. This is the problem
[Valiant 1979][valiant1979complexity] proved `#P`-complete; its completeness
is in `DescriptiveComplexity.Problems.CycleCover.Completeness`.

`DescriptiveComplexity.SharpCycleCover` is in `#P`
(`DescriptiveComplexity.sharpCycleCover_mem_sharpP`): the cover is a guessed
binary relation, checked first-order to be a bijection along the arcs.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Cover

variable {A : Type}

/-- **`F` is a cycle cover of the relation `R`**: a bijection of the universe
along `R`. -/
def IsCycleCover (R F : A → A → Prop) : Prop :=
  (∀ x, ∃! y, F x y) ∧ (∀ y, ∃! x, F x y) ∧ ∀ x y, F x y → R x y

/-- A cycle cover, as a permutation: `x` goes to the unique `y` with `F x y`. -/
noncomputable def IsCycleCover.toFun {R F : A → A → Prop} (h : IsCycleCover R F) (x : A) : A :=
  Classical.choose (h.1 x).exists

theorem IsCycleCover.rel_toFun {R F : A → A → Prop} (h : IsCycleCover R F) (x : A) :
    F x (h.toFun x) :=
  Classical.choose_spec (h.1 x).exists

theorem IsCycleCover.eq_toFun {R F : A → A → Prop} (h : IsCycleCover R F) {x y : A}
    (hxy : F x y) : y = h.toFun x :=
  (h.1 x).unique hxy (h.rel_toFun x)

theorem IsCycleCover.toFun_injective {R F : A → A → Prop} (h : IsCycleCover R F) :
    Function.Injective h.toFun := fun x x' hxx' =>
  (h.2.1 (h.toFun x)).unique (h.rel_toFun x) (hxx' ▸ h.rel_toFun x')

/-- The relation of a permutation along `R` is a cycle cover. -/
theorem isCycleCover_of_equiv {R : A → A → Prop} (e : A ≃ A) (he : ∀ x, R x (e x)) :
    IsCycleCover R fun x y => e x = y :=
  ⟨fun x => ⟨e x, rfl, fun _ h => h.symm⟩,
    fun y => ⟨e.symm y, e.apply_symm_apply y, fun _ h => by rw [← h, e.symm_apply_apply]⟩,
    fun x y h => h ▸ he x⟩

/-- **The cycle covers of a finite digraph are the permutations along its
arcs.** -/
noncomputable def cycleCoverEquiv [Finite A] (R : A → A → Prop) :
    {F : A → A → Prop // IsCycleCover R F} ≃ {e : A ≃ A // ∀ x, R x (e x)} where
  toFun F := ⟨Equiv.ofBijective F.2.toFun (Finite.injective_iff_bijective.mp
    F.2.toFun_injective), fun x => F.2.2.2 x _ (F.2.rel_toFun x)⟩
  invFun e := ⟨fun x y => e.1 x = y, isCycleCover_of_equiv e.1 e.2⟩
  left_inv F := Subtype.ext (funext fun x => funext fun _ => propext
    ⟨fun h => h ▸ F.2.rel_toFun x, fun h => (F.2.eq_toFun h).symm⟩)
  right_inv e := Subtype.ext (Equiv.ext fun x =>
    ((isCycleCover_of_equiv e.1 e.2).eq_toFun (rfl : e.1 x = e.1 x)).symm)

/-- **The number of cycle covers is the permanent of the adjacency matrix.** -/
theorem card_isCycleCover_eq_bperm [Fintype A] [DecidableEq A] (R : A → A → Prop)
    [DecidableRel R] :
    Nat.card {F : A → A → Prop // IsCycleCover R F} =
      bperm fun x y => if R x y then (1 : ℕ) else 0 := by
  rw [bperm_boole, Nat.cast_id, Nat.card_congr (cycleCoverEquiv R), Nat.card_eq_fintype_card]

end Cover

/-! ### The kernel -/

section Kernel

open SOBlock

/-- The existential block of the `Σ₁` definition: the cover, guessed as a
binary relation. -/
fo_block coverGuessBlock over Language.digraph dg into coverSOLang with cv where
  /-- The guessed cover: `nxt x y` when the cover uses the arc from `x` to `y`. -/
  nxt : 2

/-- The guessed cover, as an atom. -/
private def nxtF {α : Type} (x y : α) : coverSOLang.Formula α :=
  fo%[x, y] cvNxtSym(x, y)

/-- The first-order kernel: the guessed relation leaves and enters every
element exactly once, along the arcs. -/
noncomputable def cycleCoverKernel : coverSOLang.Sentence :=
  (fo% ∀ x, ∃ y, nxtF⟨x, y⟩) ⊓ ((fo% ∀ x y z, nxtF⟨x, y⟩ ∧ nxtF⟨x, z⟩ → y ≐ z) ⊓
    ((fo% ∀ y, ∃ x, nxtF⟨x, y⟩) ⊓ ((fo% ∀ x y z, nxtF⟨x, z⟩ ∧ nxtF⟨y, z⟩ → x ≐ y) ⊓
      (fo% ∀ x y, nxtF⟨x, y⟩ → cvArcSym(x, y)))))

variable {A : Type} [Language.digraph.Structure A]

/-- Realization of the kernel under an assignment of the guessed cover. -/
theorem realize_cycleCoverKernel (ρ : coverGuessBlock.Assignment A) :
    (@Sentence.Realize coverSOLang A
        (@sumStructure _ _ A _ (coverGuessBlock.structure ρ)) cycleCoverKernel) ↔
      IsCycleCover (fun x y : A => DGArc x y) fun x y : A => ρ .nxt ![x, y] := by
  let := coverGuessBlock.structure ρ
  have hsub : ∀ w : Fin 2 → A, RelMap (L := coverSOLang) (M := A) cvNxtSym w ↔ ρ .nxt w :=
    fun _ => Iff.rfl
  rw [cycleCoverKernel]
  simp only [nxtF, Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_iExs, Formula.realize_imp, Formula.realize_equal, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, hsub, Language.relMap_sumInl]
  simp only [IsCycleCover, DGArc, ExistsUnique]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun x => ?_, fun y => ?_, fun x y => h5 ![x, y]⟩
    · obtain ⟨y, hy⟩ := h1 fun _ => x
      exact ⟨y 0, hy, fun y' hy' => h2 ![x, y', y 0] ⟨hy', hy⟩⟩
    · obtain ⟨x, hx⟩ := h3 fun _ => y
      exact ⟨x 0, hx, fun x' hx' => h4 ![x', x 0, y] ⟨hx', hx⟩⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, fun i hi => ?_, fun i => ?_, fun i hi => ?_, fun i => h3 (i 0) (i 1)⟩
    · obtain ⟨y, hy, -⟩ := h1 (i 0)
      exact ⟨fun _ => y, hy⟩
    · obtain ⟨y, -, huniq⟩ := h1 (i 0)
      exact (huniq _ hi.1).trans (huniq _ hi.2).symm
    · obtain ⟨x, hx, -⟩ := h2 (i 0)
      exact ⟨fun _ => x, hx⟩
    · obtain ⟨x, -, huniq⟩ := h2 (i 2)
      exact (huniq _ hi.1).trans (huniq _ hi.2).symm

/-- A binary relation, as an assignment of the block guessing the cover. -/
def coverAssignEquiv (A : Type) : coverGuessBlock.Assignment A ≃ (A → A → Prop) where
  toFun ρ := fun x y => ρ .nxt ![x, y]
  invFun F := fun i => match i with
    | .nxt => fun w : Fin 2 → A => F (w 0) (w 1)
  left_inv ρ := by
    funext i
    cases i
    refine funext fun (w : Fin 2 → A) => ?_
    exact congrArg (ρ .nxt) (funext fun k => by fin_cases k <;> rfl)
  right_inv _ := rfl

/-- The number of cycle covers is the number of witnesses of the kernel. -/
theorem card_isCycleCover_eq_witnessCount (A : Type) [Language.digraph.Structure A] :
    Nat.card {F : A → A → Prop // IsCycleCover (fun x y : A => DGArc x y) F} =
      witnessCount coverGuessBlock cycleCoverKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (coverAssignEquiv A) fun F => by
    rw [realize_cycleCoverKernel]
    rfl).symm

end Kernel

/-! ### The problem -/

/-- **#Cycle Cover**: the number of cycle covers of a digraph, i.e., the
permanent of its adjacency matrix. -/
noncomputable def SharpCycleCover : CountingProblem Language.digraph where
  Count := fun A inst =>
    Nat.card {F : A → A → Prop // IsCycleCover (fun x y : A => @DGArc A inst x y) F}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_isCycleCover_eq_witnessCount A, card_isCycleCover_eq_witnessCount B]
    exact witnessCount_iso coverGuessBlock cycleCoverKernel e

theorem sharpCycleCover_apply (A : Type) [Language.digraph.Structure A] :
    SharpCycleCover A = Nat.card {F : A → A → Prop // IsCycleCover (fun x y : A => DGArc x y) F} :=
  rfl

/-- **#Cycle Cover is the permanent of the adjacency matrix.** -/
theorem sharpCycleCover_eq_bperm (A : Type) [Language.digraph.Structure A] [Fintype A]
    [DecidableEq A] [DecidableRel fun x y : A => DGArc x y] :
    SharpCycleCover A = bperm fun x y : A => if DGArc x y then (1 : ℕ) else 0 :=
  card_isCycleCover_eq_bperm _

/-- **#Cycle Cover is in `#P`.** -/
theorem sharpCycleCover_mem_sharpP : SharpCycleCover ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_isCycleCover_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel coverGuessBlock cycleCoverKernel)

end DescriptiveComplexity
