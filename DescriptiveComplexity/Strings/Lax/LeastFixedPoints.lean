/-
Mirror of `Lax751879.LeastFixedPoints`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
# Least fixed points on finite relations

For a monotone operator `F` on sets, its least fixed point is the intersection
of all sets `R` satisfying `F R ⊆ R`. Starting from the empty set, iterate `F`:
on a finite set of `N` possible elements, stage `N` is already the least fixed
point (`finiteConvergence`). The intersection definition is total even for
nonmonotone operators; the fixed-point and convergence statements explicitly
require monotonicity.
-/

namespace DescriptiveComplexity.Strings.Lax.LeastFixedPoints

/-- The intersection of the pre-fixed points of an operator. -/
def leastFixedPoint {α : Type} (F : Set α → Set α) : Set α :=
  sInf {R | F R ⊆ R}

/-- The iteration of an operator from the empty set. -/
def stage {α : Type} (F : Set α → Set α) : Nat → Set α
  | 0 => ∅
  | t + 1 => F (stage F t)

theorem least {α : Type} (F : Set α → Set α) (R : Set α)
    (hR : F R ⊆ R) : leastFixedPoint F ⊆ R :=
  sInf_le hR

theorem fixedPoint {α : Type} (F : Set α → Set α) (hF : Monotone F) :
    F (leastFixedPoint F) = leastFixedPoint F := by
  have h₁ : F (leastFixedPoint F) ⊆ leastFixedPoint F :=
    le_sInf fun R hR => (hF (sInf_le hR)).trans hR
  exact Set.Subset.antisymm h₁ (least F _ (hF h₁))

/-- The stages of a monotone operator grow. -/
private theorem stage_mono_succ {α : Type} (F : Set α → Set α) (hF : Monotone F) (t : Nat) :
    stage F t ⊆ stage F (t + 1) := by
  induction t with
  | zero => exact Set.empty_subset _
  | succ t ih => exact hF ih

private theorem stage_mono {α : Type} (F : Set α → Set α) (hF : Monotone F) {s t : Nat} (h : s ≤
    t) :
    stage F s ⊆ stage F t := by
  induction h with
  | refl => exact Set.Subset.rfl
  | step _ ih => exact ih.trans (stage_mono_succ F hF _)

/-- The stages stay below every pre-fixed point. -/
private theorem stage_subset {α : Type} (F : Set α → Set α) (hF : Monotone F) {R : Set α}
    (hR : F R ⊆ R) (t : Nat) : stage F t ⊆ R := by
  induction t with
  | zero => exact Set.empty_subset _
  | succ t ih => exact (hF ih).trans hR

/-- A chain with no repetition among its first stages has at least `t` elements at stage `t`. -/
private theorem card_stage_of_ne {α : Type} [Finite α] (F : Set α → Set α) (hF : Monotone F)
    (t : Nat) (h : ∀ s < t, stage F s ≠ stage F (s + 1)) : t ≤ Set.ncard (stage F t) := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    have h₁ := ih fun s hs => h s (by omega)
    have h₂ : stage F t ⊂ stage F (t + 1) :=
      Set.ssubset_iff_subset_ne.mpr ⟨stage_mono_succ F hF t, h t (by omega)⟩
    have h₃ := Set.ncard_lt_ncard h₂ (Set.toFinite _)
    omega

/-- Some stage within the cardinality is a pre-fixed point. -/
private theorem exists_prefixed_stage {α : Type} [Fintype α] (F : Set α → Set α)
    (hF : Monotone F) : ∃ s ≤ Fintype.card α, F (stage F s) ⊆ stage F s := by
  by_cases h : ∀ s < Fintype.card α, stage F s ≠ stage F (s + 1)
  · refine ⟨_, le_rfl, ?_⟩
    have hc := card_stage_of_ne F hF _ h
    have hu : stage F (Fintype.card α) = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
        (by rwa [Set.ncard_univ, Nat.card_eq_fintype_card])
    rw [hu]
    exact Set.subset_univ _
  · push Not at h
    obtain ⟨s, hs, heq⟩ := h
    exact ⟨s, hs.le, (show F (stage F s) = stage F s from heq.symm).subset⟩

theorem finiteConvergence {α : Type} [Fintype α]
    (F : Set α → Set α) (hF : Monotone F) :
    stage F (Fintype.card α) = leastFixedPoint F := by
  obtain ⟨s, hs, hpre⟩ := exists_prefixed_stage F hF
  refine Set.Subset.antisymm ?_ ((least F _ hpre).trans (stage_mono F hF hs))
  exact stage_subset F hF (fixedPoint F hF).subset _

end DescriptiveComplexity.Strings.Lax.LeastFixedPoints
