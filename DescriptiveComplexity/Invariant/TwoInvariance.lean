/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.TwoPebble

/-!
# The `k`-variable invariance lemma, across two structures

`DescriptiveComplexity.realize_equivK` says a formula with room for its
quantifier depth cannot separate two `≡ᵏ`-equivalent tuples *of one*
structure. This file proves the same for tuples of *two* structures
(`DescriptiveComplexity.realize_equivK₂`), against the game of
`DescriptiveComplexity.Invariant.TwoPebble` – the proof is the textbook pebble
argument once more, each quantifier spending one fresh pebble, placed by the
game move `DescriptiveComplexity.EquivK₂.update`, with the two sides of the
quantifier now ranging over different universes.

Read at a sentence, this is what separates a *Boolean* query: two structures
with a `k`-pebble equivalent pair of tuples satisfy the same formulas of
`k` variables.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} {k : ℕ}

/-- Transporting a valuation across an update at a pebble no selection uses:
the free variables do not see it, and the bound ones see it as the last
coordinate. -/
private theorem update_sel {P α : Type} {n : ℕ} {g : α → Fin k} {h : Fin n → Fin k}
    {p : Fin k} (hpg : ∀ i, g i ≠ p) (hph : ∀ j, h j ≠ p) (u : Fin k → P) (c : P) :
    ((fun i => Function.update u p c (g i)) = fun i => u (g i)) ∧
      (fun j => Function.update u p c ((Fin.snoc h p : Fin (n + 1) → Fin k) j)) =
        Fin.snoc (fun j => u (h j)) c := by
  refine ⟨funext fun i => Function.update_of_ne (hpg i) .., funext fun j => ?_⟩
  induction j using Fin.lastCases with
  | last => rw [Fin.snoc_last, Fin.snoc_last, Function.update_self]
  | cast q => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact Function.update_of_ne (hph q) ..

variable [L.IsRelational] [L.Structure M] [L.Structure N] [Finite M] [Finite N]
  {S : Set (Σ n, L.Relations n)}

/-- **The `k`-variable invariance lemma, between two structures.** A formula
over a relational vocabulary, with relation symbols in `S`, cannot separate a
pair of `k`-pebble equivalent tuples of two structures: its free variables
read the tuples through an arbitrary selection of coordinates, its bound
variables through an injective selection disjoint from it, and the coordinates
left over leave room for its quantifier depth. -/
theorem realize_equivK₂ {α : Type} [Fintype α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (g : α → Fin k)
      (h : Fin n → Fin k), Function.Injective h → (∀ i j, g i ≠ h j) →
      (Finset.image g Finset.univ ∪ Finset.image h Finset.univ).card + qdepth φ ≤ k →
      RelsIn S φ →
      ∀ (v : Fin k → M) (w : Fin k → N), EquivK₂ (atomicAgreeOn₂ S M N k) v w →
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
    have key : ∀ {P : Type} [L.Structure P] (u : Fin k → P),
        (fun j => Term.realize
            (Sum.elim (fun i => u (g i)) fun j' => u (h j'))
            (Term.var (x j) : L.Term (α ⊕ Fin n))) =
          fun j => u (Sum.elim g h (x j)) := by
      intro P _ u
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
    -- a fresh pebble, outside the coordinates in use
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
    constructor
    · intro hall b
      obtain ⟨c, hc⟩ := hvw.update_right p b
      have hih := ih g (Fin.snoc h p) hinj' hdisj' hroom' hS
        (Function.update v p c) (Function.update w p b) hc
      rw [(update_sel hpg hph v c).1, (update_sel hpg hph v c).2,
        (update_sel hpg hph w b).1, (update_sel hpg hph w b).2] at hih
      exact hih.mp (hall c)
    · intro hall c
      obtain ⟨b, hb⟩ := hvw.update p c
      have hih := ih g (Fin.snoc h p) hinj' hdisj' hroom' hS
        (Function.update v p c) (Function.update w p b) hb
      rw [(update_sel hpg hph v c).1, (update_sel hpg hph v c).2,
        (update_sel hpg hph w b).1, (update_sel hpg hph w b).2] at hih
      exact hih.mpr (hall b)

/-- **The formula form**: a formula whose free variables read the tuples
through a selection of coordinates, with room left for its quantifier depth,
cannot separate an equivalent pair. -/
theorem realize_formula_equivK₂ {α : Type} [Fintype α] (φ : L.Formula α) (g : α → Fin k)
    (hroom : (Finset.image g Finset.univ).card + qdepth φ ≤ k)
    (hS : RelsIn S φ) {v : Fin k → M} {w : Fin k → N}
    (hvw : EquivK₂ (atomicAgreeOn₂ S M N k) v w) :
    (φ.Realize fun i => v (g i)) ↔ φ.Realize fun i => w (g i) := by
  have h := realize_equivK₂ φ g Fin.elim0 (Function.injective_of_subsingleton _)
    (fun _ j => j.elim0)
    (by
      have himg : Finset.image (Fin.elim0 : Fin 0 → Fin k) Finset.univ = ∅ := by simp
      rw [himg, Finset.union_empty]
      exact hroom)
    hS v w hvw
  rw [Formula.Realize, Formula.Realize]
  refine Iff.trans (iff_of_eq (congrArg _ (Subsingleton.elim _ _))) (Iff.trans h ?_)
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- **The sentence form**: two structures carrying a `k`-pebble equivalent
pair of `k`-tuples satisfy the same sentences of quantifier depth at most
`k`. -/
theorem realize_sentence_equivK₂ (φ : L.Sentence) (hdepth : qdepth φ ≤ k)
    (hS : RelsIn S φ) {v : Fin k → M} {w : Fin k → N}
    (hvw : EquivK₂ (atomicAgreeOn₂ S M N k) v w) : M ⊨ φ ↔ N ⊨ φ := by
  have h := realize_equivK₂ (α := Empty) (k := k) φ Empty.elim Fin.elim0
    (Function.injective_of_subsingleton _) (fun i _ => i.elim)
    (by
      have himg : Finset.image (Empty.elim : Empty → Fin k) Finset.univ = ∅ := by simp
      have himg' : Finset.image (Fin.elim0 : Fin 0 → Fin k) Finset.univ = ∅ := by simp
      rw [himg, himg', Finset.union_empty, Finset.card_empty]
      omega)
    hS v w hvw
  rw [Sentence.Realize, Sentence.Realize, Formula.Realize, Formula.Realize]
  refine Iff.trans ?_ (Iff.trans h ?_) <;>
    exact iff_of_eq (congrArg₂ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end DescriptiveComplexity
