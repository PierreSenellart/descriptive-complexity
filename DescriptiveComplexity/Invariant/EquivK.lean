/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.Pebble
import Mathlib.ModelTheory.Semantics

/-!
# `k`-variable equivalence over a structure

The instantiation of the abstract pebble refinement
(`DescriptiveComplexity.Invariant.Pebble`) at a structure: the initial
relation is *agreement on the atomic type*
(`DescriptiveComplexity.atomicAgreeOn` – same equalities between coordinates,
same base relations at every selection of coordinates), and
`DescriptiveComplexity.EquivK (atomicAgreeOn S A k)` is `k`-variable
equivalence `≡ᵏ` of `k`-tuples over the structure `A`.

Agreement is *relative to a family `S` of relation symbols*: over an infinite
vocabulary, full atomic agreement is not captured by any formula, and every
consumer of the invariant layer – a `DescriptiveComplexity.StepDef`, whose
formulas mention finitely many symbols
(`DescriptiveComplexity.StepDef.exists_usesRels`) – needs the refinement
relative to the finite family it actually reads, which is what makes the
refinement itself definable. The full-agreement instance is
`DescriptiveComplexity.atomicAgree` (`S = Set.univ`).

The theorem of this file is the **`k`-variable invariance lemma**
(`DescriptiveComplexity.realize_equivK`): a first-order formula over a
relational vocabulary, whose relation symbols lie in `S`
(`DescriptiveComplexity.RelsIn`), cannot separate `≡ᵏ`-equivalent tuples,
when its free variables read the tuples through an arbitrary selection of
coordinates, its bound variables are placed injectively outside that
selection, and the positions not in use leave room for its quantifier depth
(`DescriptiveComplexity.qdepth`). The proof is the textbook pebble argument
([Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 3): each quantifier spends
one fresh pebble, placed by the game move
`DescriptiveComplexity.EquivK.update`; atomic formulas are decided by the
initial agreement. No syntactic `k`-variable fragment is ever defined – the
budget hypothesis of the lemma *is* «this formula has at most `k` variables»,
in the only form the invariance argument needs.

A second consequence of the game formulation is inheritance by pair
substructures (`DescriptiveComplexity.equivK_atomicAgreeOn_of_pairSub`, the
structure instance of `DescriptiveComplexity.equivK_of_pairSub`): rearranging,
selecting and repeating coordinates preserves `≡ᵏ` – the well-definedness of
every coordinate manipulation on `≡ᵏ`-classes.

The vocabulary is required to be relational, as everywhere in the invariant
layer: atomic agreement at selections of coordinates is only the atomic type
when terms are variables. (Everything a `StepDef` runs on in the
Abiteboul–Vianu development is relational or expanded from relational.)
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ}

/-! ### Agreement on the atomic type -/

/-- Agreement on the atomic type over the relation symbols of the family `S`:
two `k`-tuples agree on all equalities between their coordinates and on all
base relations of `S` at every selection of coordinates. This is the initial
relation of the `k`-pebble refinement over a structure, relative to the
finitely many symbols a definition mentions. -/
def atomicAgreeOn (S : Set (Σ n, L.Relations n)) (A : Type) [L.Structure A]
    (k : ℕ) : PebbleRel A k :=
  fun v w =>
    (∀ i j : Fin k, v i = v j ↔ w i = w j) ∧
    ∀ {l : ℕ} (R : L.Relations l), ⟨l, R⟩ ∈ S → ∀ g : Fin l → Fin k,
      ((RelMap R fun p => v (g p)) ↔ RelMap R fun p => w (g p))

/-- Agreement on the full atomic type: the special case `S = Set.univ` of
`DescriptiveComplexity.atomicAgreeOn`. -/
abbrev atomicAgree (L : Language.{0, 0}) (A : Type) [L.Structure A] (k : ℕ) :
    PebbleRel A k :=
  atomicAgreeOn (Set.univ : Set (Σ n, L.Relations n)) A k

/-- Agreement on the atomic type is monotone (antitone in the family): fewer
symbols, coarser agreement. -/
theorem atomicAgreeOn_mono [L.Structure A] {S S' : Set (Σ n, L.Relations n)}
    (h : S ⊆ S') : (atomicAgreeOn S' A k).Le (atomicAgreeOn S A k) :=
  fun _ _ hvw => ⟨hvw.1, fun R hR g => hvw.2 R (h hR) g⟩

/-- Agreement on the atomic type is an equivalence. -/
theorem atomicAgreeOn_equivalence [L.Structure A] {S : Set (Σ n, L.Relations n)} :
    Equivalence (atomicAgreeOn S A k) where
  refl _ := ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  symm h := ⟨fun i j => (h.1 i j).symm, fun R hR g => (h.2 R hR g).symm⟩
  trans h h' := ⟨fun i j => (h.1 i j).trans (h'.1 i j),
    fun R hR g => (h.2 R hR g).trans (h'.2 R hR g)⟩

/-- `≡ᵏ` over a structure is an equivalence. -/
theorem equivK_atomicAgreeOn_equivalence [L.Structure A]
    {S : Set (Σ n, L.Relations n)} :
    Equivalence (EquivK (atomicAgreeOn S A k)) :=
  equivK_equivalence atomicAgreeOn_equivalence

/-- Agreement on the atomic type passes to pair substructures: selecting,
permuting and repeating coordinate pairs preserves it. -/
theorem atomicAgreeOn_of_pairSub [L.Structure A] {S : Set (Σ n, L.Relations n)}
    {x y u v : Fin k → A} (hsub : ∀ j, ∃ i, x j = u i ∧ y j = v i)
    (h : atomicAgreeOn S A k u v) : atomicAgreeOn S A k x y := by
  choose I hI using hsub
  constructor
  · intro i j
    rw [(hI i).1, (hI i).2, (hI j).1, (hI j).2]
    exact h.1 (I i) (I j)
  · intro l R hR g
    have hx : (fun p => x (g p)) = fun p => u (I (g p)) :=
      funext fun p => (hI (g p)).1
    have hy : (fun p => y (g p)) = fun p => v (I (g p)) :=
      funext fun p => (hI (g p)).2
    rw [hx, hy]
    exact h.2 R hR fun p => I (g p)

/-- **`≡ᵏ` is inherited by pair substructures** over a structure: the
instance of `DescriptiveComplexity.equivK_of_pairSub` at atomic agreement.
This is the well-definedness of every coordinate manipulation on
`≡ᵏ`-classes – substitution and rearrangement relations included. -/
theorem equivK_atomicAgreeOn_of_pairSub [L.Structure A] [Finite A]
    {S : Set (Σ n, L.Relations n)} {x y u v : Fin k → A}
    (hsub : ∀ j, ∃ i, x j = u i ∧ y j = v i)
    (huv : EquivK (atomicAgreeOn S A k) u v) :
    EquivK (atomicAgreeOn S A k) x y :=
  equivK_of_pairSub (fun hs h₀ => atomicAgreeOn_of_pairSub hs h₀) hsub huv

/-! ### Quantifier depth and the relation symbols of a formula -/

/-- The quantifier depth of a bounded formula: the number of pebbles the
invariance argument spends on it. -/
def qdepth {α : Type*} : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f₁ f₂ => max (qdepth f₁) (qdepth f₂)
  | _, .all f => qdepth f + 1

/-- The relation symbols of a bounded formula all lie in the family `S`. -/
def RelsIn (S : Set (Σ n, L.Relations n)) {α : Type*} :
    ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | _, .falsum => True
  | _, .equal _ _ => True
  | _, .rel R _ => ⟨_, R⟩ ∈ S
  | _, .imp f₁ f₂ => RelsIn S f₁ ∧ RelsIn S f₂
  | _, .all f => RelsIn S f

/-- Containment of relation symbols is monotone in the family. -/
theorem RelsIn.mono {S S' : Set (Σ n, L.Relations n)} (hS : S ⊆ S') {α : Type*}
    {n : ℕ} {φ : L.BoundedFormula α n} (h : RelsIn S φ) : RelsIn S' φ := by
  induction φ with
  | falsum => trivial
  | equal => trivial
  | rel => exact hS h
  | imp f₁ f₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | all f ih => exact ih h

/-- The set of relation symbols occurring in a bounded formula. -/
def relsOf {α : Type*} : ∀ {n : ℕ}, L.BoundedFormula α n → Set (Σ n, L.Relations n)
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel R _ => {⟨_, R⟩}
  | _, .imp f₁ f₂ => relsOf f₁ ∪ relsOf f₂
  | _, .all f => relsOf f

/-- A formula mentions finitely many relation symbols. -/
theorem relsOf_finite {α : Type*} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), (relsOf φ).Finite
  | _, .falsum => Set.finite_empty
  | _, .equal _ _ => Set.finite_empty
  | _, .rel _ _ => Set.finite_singleton _
  | _, .imp f₁ f₂ => (relsOf_finite f₁).union (relsOf_finite f₂)
  | _, .all f => relsOf_finite f

/-- A formula's relation symbols lie in the set of its relation symbols. -/
theorem relsIn_relsOf {α : Type*} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), RelsIn (relsOf φ) φ
  | _, .falsum => trivial
  | _, .equal _ _ => trivial
  | _, .rel _ _ => Set.mem_singleton _
  | _, .imp f₁ f₂ => ⟨(relsIn_relsOf f₁).mono Set.subset_union_left,
      (relsIn_relsOf f₂).mono Set.subset_union_right⟩
  | _, .all f => relsIn_relsOf f

/-! ### Terms of a relational vocabulary are variables -/

/-- In a relational vocabulary, every term is a variable. -/
theorem exists_eq_var_of_isRelational [L.IsRelational] {α : Type*} (t : L.Term α) :
    ∃ x, t = Term.var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | func f _ => exact isEmptyElim f

/-! ### Placing a fresh pebble -/

section Snoc

variable {n : ℕ} {h : Fin n → Fin k} {p : Fin k}

theorem snoc_injective (hinj : Function.Injective h)
    (hp : ∀ j, h j ≠ p) : Function.Injective (Fin.snoc h p : Fin (n + 1) → Fin k) := by
  intro j₁ j₂ heq
  induction j₁ using Fin.lastCases with
  | last =>
    induction j₂ using Fin.lastCases with
    | last => rfl
    | cast q₂ =>
      rw [Fin.snoc_last, Fin.snoc_castSucc] at heq
      exact absurd heq.symm (hp q₂)
  | cast q₁ =>
    induction j₂ using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Fin.snoc_castSucc] at heq
      exact absurd heq (hp q₁)
    | cast q₂ =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at heq
      exact congrArg Fin.castSucc (hinj heq)

theorem image_snoc_subset :
    Finset.image (Fin.snoc h p : Fin (n + 1) → Fin k) Finset.univ ⊆
      insert p (Finset.image h Finset.univ) := by
  intro y hy
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
  induction j using Fin.lastCases with
  | last => rw [Fin.snoc_last]; exact Finset.mem_insert_self p _
  | cast q =>
    rw [Fin.snoc_castSucc]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem h (Finset.mem_univ q))

end Snoc

/-! ### The `k`-variable invariance lemma -/

section Invariance

variable [L.IsRelational] [L.Structure A] [Finite A] {S : Set (Σ n, L.Relations n)}

/-- **The `k`-variable invariance lemma.** A first-order formula over a
relational vocabulary, with relation symbols in the family `S`, cannot
separate tuples `≡ᵏ`-equivalent relative to `S`: its free variables read the
tuples through an arbitrary selection `g` of coordinates, its bound variables
through an injective selection `h` disjoint from `g`, and the coordinates not
in use leave room for its quantifier depth. Each quantifier spends one fresh
pebble, placed by the game move (`DescriptiveComplexity.EquivK.update`);
atomic formulas are decided by the initial agreement
(`DescriptiveComplexity.atomicAgreeOn`). -/
theorem realize_equivK {m : ℕ} :
    ∀ {n : ℕ} (φ : L.BoundedFormula (Fin m) n) (g : Fin m → Fin k)
      (h : Fin n → Fin k), Function.Injective h → (∀ i j, g i ≠ h j) →
      (Finset.image g Finset.univ ∪ Finset.image h Finset.univ).card + qdepth φ ≤ k →
      RelsIn S φ →
      ∀ v w : Fin k → A, EquivK (atomicAgreeOn S A k) v w →
      ((φ.Realize (fun i => v (g i)) fun j => v (h j)) ↔
        φ.Realize (fun i => w (g i)) fun j => w (h j)) := by
  intro n φ
  induction φ with
  | falsum => exact fun _ _ _ _ _ _ _ _ _ => Iff.rfl
  | @equal n t₁ t₂ =>
    intro g h _ _ _ _ v w hvw
    obtain ⟨x₁, rfl⟩ := exists_eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := exists_eq_var_of_isRelational t₂
    rcases x₁ with i₁ | j₁ <;> rcases x₂ with i₂ | j₂
    · exact hvw.initial.1 (g i₁) (g i₂)
    · exact hvw.initial.1 (g i₁) (h j₂)
    · exact hvw.initial.1 (h j₁) (g i₂)
    · exact hvw.initial.1 (h j₁) (h j₂)
  | @rel n l R ts =>
    intro g h _ _ _ hS v w hvw
    have hts : ∀ j, ∃ x, ts j = Term.var x :=
      fun j => exists_eq_var_of_isRelational (ts j)
    choose x hx using hts
    have hsub : ts = fun j => Term.var (x j) := funext hx
    subst hsub
    have key : ∀ u : Fin k → A,
        (fun j => Term.realize
            (Sum.elim (fun i => u (g i)) fun j' => u (h j'))
            (Term.var (x j) : L.Term (Fin m ⊕ Fin n))) =
          fun j => u (Sum.elim g h (x j)) := by
      intro u
      funext j
      rcases x j with i | j' <;> rfl
    exact Iff.trans (iff_of_eq (congrArg (RelMap R) (key v)))
      (Iff.trans (hvw.initial.2 R hS fun j => Sum.elim g h (x j))
        (iff_of_eq (congrArg (RelMap R) (key w))).symm)
  | @imp n f₁ f₂ ih₁ ih₂ =>
    intro g h hinj hdisj hroom hS v w hvw
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp]
    have h₁ := ih₁ g h hinj hdisj
      (by have := le_max_left (qdepth f₁) (qdepth f₂); simp only [qdepth] at hroom; omega)
      hS.1 v w hvw
    have h₂ := ih₂ g h hinj hdisj
      (by have := le_max_right (qdepth f₁) (qdepth f₂); simp only [qdepth] at hroom; omega)
      hS.2 v w hvw
    exact imp_congr h₁ h₂
  | @all n ψ ih =>
    intro g h hinj hdisj hroom hS v w hvw
    rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
    -- pick a fresh pebble `p`, outside the coordinates in use
    have hcard : (Finset.image g Finset.univ ∪ Finset.image h Finset.univ).card <
        (Finset.univ : Finset (Fin k)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      simp only [qdepth] at hroom
      omega
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hpg : ∀ i, g i ≠ p := fun i heq =>
      hp (Finset.mem_union_left _ (heq ▸ Finset.mem_image_of_mem g (Finset.mem_univ i)))
    have hph : ∀ j, h j ≠ p := fun j heq =>
      hp (Finset.mem_union_right _ (heq ▸ Finset.mem_image_of_mem h (Finset.mem_univ j)))
    -- the extended selections for the body, and their budget
    have hinj' : Function.Injective (Fin.snoc h p : Fin (n + 1) → Fin k) :=
      snoc_injective hinj hph
    have hdisj' : ∀ i j, g i ≠ (Fin.snoc h p : Fin (n + 1) → Fin k) j := by
      intro i j
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hpg i
      | cast q => rw [Fin.snoc_castSucc]; exact hdisj i q
    have hroom' : (Finset.image g Finset.univ ∪
          Finset.image (Fin.snoc h p : Fin (n + 1) → Fin k) Finset.univ).card +
        qdepth ψ ≤ k := by
      have hsub : Finset.image g Finset.univ ∪
            Finset.image (Fin.snoc h p : Fin (n + 1) → Fin k) Finset.univ ⊆
          insert p (Finset.image g Finset.univ ∪ Finset.image h Finset.univ) := by
        refine Finset.union_subset ?_ ?_
        · exact fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)
        · refine image_snoc_subset.trans ?_
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hy')
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le p
        (Finset.image g Finset.univ ∪ Finset.image h Finset.univ)
      simp only [qdepth] at hroom
      omega
    -- transporting a stage valuation across an update at the fresh pebble
    have hval : ∀ (u : Fin k → A) (c : A),
        ((fun i => Function.update u p c (g i)) = fun i => u (g i)) ∧
          (fun j => Function.update u p c ((Fin.snoc h p : Fin (n + 1) → Fin k) j)) =
            Fin.snoc (fun j => u (h j)) c := by
      intro u c
      refine ⟨funext fun i => Function.update_of_ne (hpg i) .., funext fun j => ?_⟩
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last, Fin.snoc_last, Function.update_self]
      | cast q =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact Function.update_of_ne (hph q) ..
    constructor
    · intro hall b
      obtain ⟨c, hc⟩ := hvw.update_right p b
      have hih := ih g (Fin.snoc h p) hinj' hdisj' hroom' hS
        (Function.update v p c) (Function.update w p b) hc
      rw [(hval v c).1, (hval v c).2, (hval w b).1, (hval w b).2] at hih
      exact hih.mp (hall c)
    · intro hall c
      obtain ⟨b, hb⟩ := hvw.update p c
      have hih := ih g (Fin.snoc h p) hinj' hdisj' hroom' hS
        (Function.update v p c) (Function.update w p b) hb
      rw [(hval v c).1, (hval v c).2, (hval w b).1, (hval w b).2] at hih
      exact hih.mpr (hall b)

/-- The `k`-variable invariance lemma, for formulas: a formula over a
relational vocabulary, with relation symbols in `S` and room for its
quantifier depth beyond the selection of coordinates its free variables read,
cannot separate `≡ᵏ`-equivalent tuples. -/
theorem realize_formula_equivK {m : ℕ} (φ : L.Formula (Fin m)) (g : Fin m → Fin k)
    (hroom : (Finset.image g Finset.univ).card + qdepth φ ≤ k)
    (hS : RelsIn S φ) {v w : Fin k → A} (hvw : EquivK (atomicAgreeOn S A k) v w) :
    (φ.Realize fun i => v (g i)) ↔ φ.Realize fun i => w (g i) := by
  have h := realize_equivK φ g Fin.elim0 (Function.injective_of_subsingleton _)
    (fun _ j => j.elim0)
    (by
      have himg : Finset.image (Fin.elim0 : Fin 0 → Fin k) Finset.univ = ∅ := by
        simp
      rw [himg, Finset.union_empty]
      exact hroom)
    hS v w hvw
  rw [Formula.Realize, Formula.Realize]
  refine Iff.trans (iff_of_eq (congrArg _ (Subsingleton.elim _ _))) (Iff.trans h ?_)
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

end Invariance

end DescriptiveComplexity
