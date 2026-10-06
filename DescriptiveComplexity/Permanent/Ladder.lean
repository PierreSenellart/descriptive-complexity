/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Permanent.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Cover

/-!
# Expanding a weighted graph into a 0-1 graph: ladders

A matrix of natural numbers is the adjacency matrix of a digraph with
parallel edges, and its permanent counts its cycle covers, an edge of weight
`k` counting `k` times. The **ladder expansion**
(`DescriptiveComplexity.ladder`) replaces every edge `a → b` by a ladder: a
sequence of *levels* `ℓ : Λ`, a finite linear order with a least and a
greatest level, with `wd a b ℓ` *rungs* at level `ℓ`; `a` reaches every rung
of the least level, every rung reaches every rung of the next level, every
rung of the greatest level reaches `b`, and every rung loops on itself. The
result is a 0-1 matrix, and its permanent is the permanent of the matrix of
the products `∏ ℓ, wd a b ℓ` (`DescriptiveComplexity.bperm_ladder`): a cycle
cover of the ladder graph is a cycle cover of the weighted graph together
with a choice of one rung at each level of each edge it uses, the other
rungs looping.

Series and parallel composition at once, which is what a reduction needs: an
edge of weight `2 ^ n` costs `n` levels of two rungs, an edge of weight `3` a
single level of three rungs.
-/

namespace DescriptiveComplexity

open Finset

section Defs

variable {V Λ : Type}

/-- **The rungs of the ladders**: the copy `j` of the level `ℓ` of the ladder
from `a` to `b`, for `j < wd a b ℓ`. -/
def Rung (K : ℕ) (wd : V → V → Λ → ℕ) : Type :=
  {q : V × V × Λ × Fin K // q.2.2.2.val < wd q.1 q.2.1 q.2.2.1}

namespace Rung

variable {K : ℕ} {wd : V → V → Λ → ℕ}

instance [Fintype V] [Fintype Λ] : Fintype (Rung K wd) := Subtype.fintype _

instance [Finite V] [Finite Λ] : Finite (Rung K wd) :=
  inferInstanceAs (Finite {q : V × V × Λ × Fin K // q.2.2.2.val < wd q.1 q.2.1 q.2.2.1})

instance [DecidableEq V] [DecidableEq Λ] : DecidableEq (Rung K wd) := Subtype.instDecidableEq

/-- The source of the ladder a rung belongs to. -/
abbrev src (q : Rung K wd) : V := q.1.1

/-- The target of the ladder a rung belongs to. -/
abbrev tgt (q : Rung K wd) : V := q.1.2.1

/-- The level of a rung. -/
abbrev lvl (q : Rung K wd) : Λ := q.1.2.2.1

/-- The index of a rung at its level. -/
abbrev idx (q : Rung K wd) : Fin K := q.1.2.2.2

theorem ext {q q' : Rung K wd} (ha : q.src = q'.src) (hb : q.tgt = q'.tgt) (hℓ : q.lvl = q'.lvl)
    (hj : q.idx = q'.idx) : q = q' :=
  Subtype.ext (Prod.ext ha (Prod.ext hb (Prod.ext hℓ hj)))

end Rung

variable [LinearOrder Λ] [BoundedOrder Λ]

/-- **The edges of the ladder graph.** -/
inductive LadderEdge (K : ℕ) (wd : V → V → Λ → ℕ) : V ⊕ Rung K wd → V ⊕ Rung K wd → Prop
  /-- The source reaches every rung of the least level. -/
  | enter (q : Rung K wd) (h : q.lvl = ⊥) : LadderEdge K wd (Sum.inl q.src) (Sum.inr q)
  /-- Every rung loops. -/
  | loop (q : Rung K wd) : LadderEdge K wd (Sum.inr q) (Sum.inr q)
  /-- Every rung reaches every rung of the next level. -/
  | step (q q' : Rung K wd) (ha : q.src = q'.src) (hb : q.tgt = q'.tgt) (hℓ : q.lvl ⋖ q'.lvl) :
      LadderEdge K wd (Sum.inr q) (Sum.inr q')
  /-- Every rung of the greatest level reaches the target. -/
  | leave (q : Rung K wd) (h : q.lvl = ⊤) : LadderEdge K wd (Sum.inr q) (Sum.inl q.tgt)

open Classical in
/-- **The ladder expansion** of a weighted matrix: the 0-1 adjacency matrix
of the ladder graph. -/
noncomputable def ladder (K : ℕ) (wd : V → V → Λ → ℕ) (n n' : V ⊕ Rung K wd) : ℕ :=
  if LadderEdge K wd n n' then 1 else 0

variable {K : ℕ} {wd : V → V → Λ → ℕ}

theorem ladderEdge_inl_inl (a b : V) : ¬LadderEdge K wd (Sum.inl a) (Sum.inl b) := by
  intro h
  cases h

theorem ladderEdge_inl_inr {a : V} {q : Rung K wd} :
    LadderEdge K wd (Sum.inl a) (Sum.inr q) ↔ q.src = a ∧ q.lvl = ⊥ := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, ‹_›⟩
  · rintro ⟨rfl, h⟩
    exact .enter q h

theorem ladderEdge_inr_inl {q : Rung K wd} {b : V} :
    LadderEdge K wd (Sum.inr q) (Sum.inl b) ↔ q.tgt = b ∧ q.lvl = ⊤ := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, ‹_›⟩
  · rintro ⟨rfl, h⟩
    exact .leave q h

theorem ladderEdge_inr_inr {q q' : Rung K wd} :
    LadderEdge K wd (Sum.inr q) (Sum.inr q') ↔
      q = q' ∨ (q.src = q'.src ∧ q.tgt = q'.tgt ∧ q.lvl ⋖ q'.lvl) := by
  constructor
  · intro h
    cases h with
    | loop => exact Or.inl rfl
    | step _ _ ha hb hℓ => exact Or.inr ⟨ha, hb, hℓ⟩
  · rintro (rfl | ⟨ha, hb, hℓ⟩)
    · exact .loop q
    · exact .step q q' ha hb hℓ

end Defs

/-! ### Levels -/

section Levels

variable {Λ : Type} [LinearOrder Λ]

/-- The next level is unique. -/
theorem covBy_right_unique {ℓ ℓ₁ ℓ₂ : Λ} (h₁ : ℓ ⋖ ℓ₁) (h₂ : ℓ ⋖ ℓ₂) : ℓ₁ = ℓ₂ :=
  le_antisymm (h₁.ge_of_gt h₂.lt) (h₂.ge_of_gt h₁.lt)

/-- The previous level is unique. -/
theorem covBy_left_unique {ℓ₁ ℓ₂ ℓ : Λ} (h₁ : ℓ₁ ⋖ ℓ) (h₂ : ℓ₂ ⋖ ℓ) : ℓ₁ = ℓ₂ :=
  le_antisymm (h₂.le_of_lt h₁.lt) (h₁.le_of_lt h₂.lt)

variable [Finite Λ] [BoundedOrder Λ]

/-- The next level, when there is one. -/
noncomputable def lvlSucc (ℓ : Λ) : Λ :=
  if h : ℓ = ⊤ then ℓ
  else Classical.choose (exists_covBy_of_wellFoundedLT (isMax_iff_eq_top.not.mpr h))

theorem covBy_lvlSucc {ℓ : Λ} (h : ℓ ≠ ⊤) : ℓ ⋖ lvlSucc ℓ := by
  rw [lvlSucc, dif_neg h]
  exact Classical.choose_spec (exists_covBy_of_wellFoundedLT (isMax_iff_eq_top.not.mpr h))

theorem lvlSucc_injective {ℓ ℓ' : Λ} (h : ℓ ≠ ⊤) (h' : ℓ' ≠ ⊤) (he : lvlSucc ℓ = lvlSucc ℓ') :
    ℓ = ℓ' :=
  covBy_left_unique (covBy_lvlSucc h) (he ▸ covBy_lvlSucc h')

theorem lvlSucc_ne_bot {ℓ : Λ} (h : ℓ ≠ ⊤) : lvlSucc ℓ ≠ ⊥ :=
  fun hb => (hb ▸ (covBy_lvlSucc h).lt).not_ge bot_le

theorem lvlSucc_ne {ℓ : Λ} (h : ℓ ≠ ⊤) : lvlSucc ℓ ≠ ℓ :=
  (covBy_lvlSucc h).lt.ne'

end Levels

/-! ### Choices -/

section Choice

variable {V Λ : Type} {K : ℕ} {wd : V → V → Λ → ℕ}

/-- **A choice**: a cycle cover of the weighted graph with one rung chosen at
each level of each edge it uses. -/
abbrev Choice (wd : V → V → Λ → ℕ) : Type :=
  Σ σ : V ≃ V, ∀ a ℓ, Fin (wd a (σ a) ℓ)

variable (hK : ∀ a b ℓ, wd a b ℓ ≤ K)
include hK

/-- The rung a choice picks at level `ℓ` of the edge leaving `a`. -/
def act (c : Choice wd) (a : V) (ℓ : Λ) : Rung K wd :=
  ⟨(a, c.1 a, ℓ, ⟨(c.2 a ℓ).val, lt_of_lt_of_le (c.2 a ℓ).2 (hK a (c.1 a) ℓ)⟩), (c.2 a ℓ).2⟩

theorem act_src (c : Choice wd) (a : V) (ℓ : Λ) : (act hK c a ℓ).src = a := rfl

theorem act_tgt (c : Choice wd) (a : V) (ℓ : Λ) : (act hK c a ℓ).tgt = c.1 a := rfl

theorem act_lvl (c : Choice wd) (a : V) (ℓ : Λ) : (act hK c a ℓ).lvl = ℓ := rfl

theorem act_idx_val (c : Choice wd) (a : V) (ℓ : Λ) :
    (act hK c a ℓ).idx.val = (c.2 a ℓ).val := rfl

theorem act_injective (c : Choice wd) {a a' : V} {ℓ ℓ' : Λ}
    (h : act hK c a ℓ = act hK c a' ℓ') : a = a' ∧ ℓ = ℓ' :=
  ⟨congrArg Rung.src h, congrArg Rung.lvl h⟩

/-- A rung is **picked** by a choice. -/
def IsAct (c : Choice wd) (q : Rung K wd) : Prop :=
  q.tgt = c.1 q.src ∧ q.idx.val = (c.2 q.src q.lvl).val

theorem isAct_iff (c : Choice wd) (q : Rung K wd) : IsAct c q ↔ q = act hK c q.src q.lvl := by
  constructor
  · rintro ⟨hb, hj⟩
    exact Rung.ext rfl hb rfl (Fin.ext hj)
  · intro h
    exact ⟨congrArg Rung.tgt h, congrArg (fun q : Rung K wd => q.idx.val) h⟩

theorem isAct_act (c : Choice wd) (a : V) (ℓ : Λ) : IsAct c (act hK c a ℓ) :=
  (isAct_iff hK c _).mpr rfl

variable [LinearOrder Λ] [Finite Λ] [BoundedOrder Λ]

open Classical in
/-- **The cycle cover of the ladder graph determined by a choice**: the
source of each edge goes to the picked rung of the least level, each picked
rung to the picked rung of the next level, or to the target from the greatest
level, and every other rung loops. -/
noncomputable def toCover (c : Choice wd) : V ⊕ Rung K wd → V ⊕ Rung K wd
  | Sum.inl a => Sum.inr (act hK c a ⊥)
  | Sum.inr q =>
      if IsAct c q then
        if q.lvl = ⊤ then Sum.inl q.tgt else Sum.inr (act hK c q.src (lvlSucc q.lvl))
      else Sum.inr q

theorem toCover_inl (c : Choice wd) (a : V) : toCover hK c (Sum.inl a) = Sum.inr (act hK c a ⊥) :=
  rfl

theorem toCover_inr_of_not (c : Choice wd) {q : Rung K wd} (h : ¬IsAct c q) :
    toCover hK c (Sum.inr q) = Sum.inr q := by
  rw [toCover, if_neg h]

theorem toCover_inr_top (c : Choice wd) {q : Rung K wd} (h : IsAct c q) (ht : q.lvl = ⊤) :
    toCover hK c (Sum.inr q) = Sum.inl q.tgt := by
  rw [toCover, if_pos h, if_pos ht]

theorem toCover_inr_of_ne_top (c : Choice wd) {q : Rung K wd} (h : IsAct c q)
    (ht : q.lvl ≠ ⊤) : toCover hK c (Sum.inr q) = Sum.inr (act hK c q.src (lvlSucc q.lvl)) := by
  rw [toCover, if_pos h, if_neg ht]

/-- Every edge of the cover determined by a choice is an edge of the ladder
graph. -/
theorem ladderEdge_toCover (c : Choice wd) (n : V ⊕ Rung K wd) :
    LadderEdge K wd n (toCover hK c n) := by
  rcases n with a | q
  · exact .enter (act hK c a ⊥) rfl
  · by_cases h : IsAct c q
    · by_cases ht : q.lvl = ⊤
      · rw [toCover_inr_top hK c h ht]
        exact .leave q ht
      · rw [toCover_inr_of_ne_top hK c h ht]
        exact .step _ _ rfl ((isAct_iff hK c q).mp h ▸ rfl) (covBy_lvlSucc ht)
    · rw [toCover_inr_of_not hK c h]
      exact .loop q

theorem toCover_inr_ne (c : Choice wd) {q : Rung K wd} (h : IsAct c q) :
    toCover hK c (Sum.inr q) ≠ Sum.inr q := by
  by_cases ht : q.lvl = ⊤
  · rw [toCover_inr_top hK c h ht]
    exact Sum.inl_ne_inr
  · rw [toCover_inr_of_ne_top hK c h ht]
    intro he
    exact lvlSucc_ne ht (congrArg Rung.lvl (Sum.inr.inj he))

/-- The cover determined by a choice is injective. -/
theorem toCover_injective (c : Choice wd) : Function.Injective (toCover hK c) := by
  intro n n' h
  rcases n with a | q <;> rcases n' with a' | q'
  · exact congrArg Sum.inl (act_injective hK c (Sum.inr.inj h)).1
  · exfalso
    rw [toCover_inl] at h
    by_cases hq : IsAct c q'
    · by_cases ht : q'.lvl = ⊤
      · rw [toCover_inr_top hK c hq ht] at h
        exact Sum.inr_ne_inl h
      · rw [toCover_inr_of_ne_top hK c hq ht] at h
        exact lvlSucc_ne_bot ht (act_injective hK c (Sum.inr.inj h)).2.symm
    · rw [toCover_inr_of_not hK c hq] at h
      obtain rfl : q' = act hK c a ⊥ := (Sum.inr.inj h).symm
      exact hq (isAct_act hK c a ⊥)
  · exfalso
    rw [toCover_inl] at h
    by_cases hq : IsAct c q
    · by_cases ht : q.lvl = ⊤
      · rw [toCover_inr_top hK c hq ht] at h
        exact Sum.inl_ne_inr h
      · rw [toCover_inr_of_ne_top hK c hq ht] at h
        exact lvlSucc_ne_bot ht (act_injective hK c (Sum.inr.inj h)).2
    · rw [toCover_inr_of_not hK c hq] at h
      obtain rfl : q = act hK c a' ⊥ := Sum.inr.inj h
      exact hq (isAct_act hK c a' ⊥)
  · by_cases hq : IsAct c q <;> by_cases hq' : IsAct c q'
    · have hidx : ∀ hs : q.src = q'.src, q.lvl = q'.lvl → q = q' := fun hs hℓ =>
        Rung.ext hs (by rw [hq.1, hq'.1, hs]) hℓ (Fin.ext (by
          rw [hq.2, hq'.2]
          exact congrArg (fun p : V × Λ => (c.2 p.1 p.2).val)
            (Prod.ext (x := (q.src, q.lvl)) (y := (q'.src, q'.lvl)) hs hℓ)))
      by_cases ht : q.lvl = ⊤ <;> by_cases ht' : q'.lvl = ⊤
      · rw [toCover_inr_top hK c hq ht, toCover_inr_top hK c hq' ht'] at h
        have hs : c.1 q.src = c.1 q'.src := by
          rw [← hq.1, ← hq'.1]
          exact Sum.inl.inj h
        exact congrArg Sum.inr (hidx (c.1.injective hs) (ht.trans ht'.symm))
      · rw [toCover_inr_top hK c hq ht, toCover_inr_of_ne_top hK c hq' ht'] at h
        exact absurd h Sum.inl_ne_inr
      · rw [toCover_inr_of_ne_top hK c hq ht, toCover_inr_top hK c hq' ht'] at h
        exact absurd h Sum.inr_ne_inl
      · rw [toCover_inr_of_ne_top hK c hq ht, toCover_inr_of_ne_top hK c hq' ht'] at h
        obtain ⟨hs, hℓ⟩ := act_injective hK c (Sum.inr.inj h)
        exact congrArg Sum.inr (hidx hs (lvlSucc_injective ht ht' hℓ))
    · rw [toCover_inr_of_not hK c hq'] at h
      by_cases ht : q.lvl = ⊤
      · rw [toCover_inr_top hK c hq ht] at h
        exact absurd h Sum.inl_ne_inr
      · rw [toCover_inr_of_ne_top hK c hq ht] at h
        obtain rfl : q' = act hK c q.src (lvlSucc q.lvl) := (Sum.inr.inj h).symm
        exact absurd (isAct_act hK c _ _) hq'
    · rw [toCover_inr_of_not hK c hq] at h
      by_cases ht : q'.lvl = ⊤
      · rw [toCover_inr_top hK c hq' ht] at h
        exact absurd h Sum.inr_ne_inl
      · rw [toCover_inr_of_ne_top hK c hq' ht] at h
        obtain rfl : q = act hK c q'.src (lvlSucc q'.lvl) := Sum.inr.inj h
        exact absurd (isAct_act hK c _ _) hq
    · rw [toCover_inr_of_not hK c hq, toCover_inr_of_not hK c hq'] at h
      exact h

variable [Finite V]

/-- The cover determined by a choice, as an element of the set of cycle
covers of the ladder graph. -/
noncomputable def toCoverEquiv (c : Choice wd) :
    {e : V ⊕ Rung K wd ≃ V ⊕ Rung K wd // ∀ n, LadderEdge K wd n (e n)} :=
  ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (toCover_injective hK c)),
    ladderEdge_toCover hK c⟩

theorem toCoverEquiv_apply (c : Choice wd) (n : V ⊕ Rung K wd) :
    (toCoverEquiv hK c).1 n = toCover hK c n :=
  rfl

/-- Distinct choices determine distinct covers. -/
theorem toCoverEquiv_injective : Function.Injective (toCoverEquiv hK) := by
  rintro ⟨σ, r⟩ ⟨σ', r'⟩ h
  have h' : ∀ n, toCover hK ⟨σ, r⟩ n = toCover hK ⟨σ', r'⟩ n := fun n =>
    (toCoverEquiv_apply hK _ n).symm.trans ((congrArg (fun e => e.1 n) h).trans
      (toCoverEquiv_apply hK _ n))
  have hσ : σ = σ' := Equiv.ext fun a =>
    congrArg Rung.tgt (Sum.inr.inj (h' (Sum.inl a)))
  subst hσ
  refine Sigma.ext rfl (heq_of_eq (funext fun a => funext fun ℓ => Fin.ext ?_))
  by_cases hq : IsAct ⟨σ, r'⟩ (act hK ⟨σ, r⟩ a ℓ)
  · exact hq.2
  · exact absurd ((h' _).trans (toCover_inr_of_not hK ⟨σ, r'⟩ hq))
      (toCover_inr_ne hK ⟨σ, r⟩ (isAct_act hK ⟨σ, r⟩ a ℓ))

end Choice

/-! ### Every cover comes from a choice -/

section OfCover

variable {V Λ : Type} [LinearOrder Λ] [BoundedOrder Λ] {K : ℕ} {wd : V → V → Λ → ℕ}
  (e : V ⊕ Rung K wd ≃ V ⊕ Rung K wd) (he : ∀ n, LadderEdge K wd n (e n))

/-- A rung is **active** in a cover when it does not loop. -/
def Act (q : Rung K wd) : Prop :=
  e (Sum.inr q) ≠ Sum.inr q

omit [LinearOrder Λ] [BoundedOrder Λ] in
theorem act_of_eq_inl {a : V} {q : Rung K wd} (h : e (Sum.inl a) = Sum.inr q) : Act e q :=
  fun h' => Sum.inl_ne_inr (e.injective (h.trans h'.symm))

omit [LinearOrder Λ] [BoundedOrder Λ] in
theorem act_of_eq_inr {q' q : Rung K wd} (h : e (Sum.inr q') = Sum.inr q) (hne : q' ≠ q) :
    Act e q :=
  fun h' => hne (Sum.inr.inj (e.injective (h.trans h'.symm)))

include he in
/-- The edge entering an active rung: from the source at the least level, or
from an active rung of the previous level. -/
theorem of_act {q : Rung K wd} (h : Act e q) :
    (q.lvl = ⊥ ∧ e (Sum.inl q.src) = Sum.inr q) ∨
      ∃ q' : Rung K wd, q'.src = q.src ∧ q'.tgt = q.tgt ∧ q'.lvl ⋖ q.lvl ∧ Act e q' ∧
        e (Sum.inr q') = Sum.inr q := by
  have hm := he (e.symm (Sum.inr q))
  rw [Equiv.apply_symm_apply] at hm
  generalize hn : e.symm (Sum.inr q) = n at hm
  have hen : e n = Sum.inr q := by rw [← hn, Equiv.apply_symm_apply]
  rcases n with a | q'
  · obtain ⟨ha, hℓ⟩ := ladderEdge_inl_inr.mp hm
    exact Or.inl ⟨hℓ, by rw [ha]; exact hen⟩
  · rcases ladderEdge_inr_inr.mp hm with rfl | ⟨ha, hb, hℓ⟩
    · exact absurd hen h
    · exact Or.inr ⟨q', ha, hb, hℓ,
        fun h' => hℓ.lt.ne (congrArg Rung.lvl (Sum.inr.inj (hen.symm.trans h'))).symm, hen⟩

include he in
/-- The edge leaving an active rung: to the target from the greatest level,
to an active rung of the next level otherwise. -/
theorem act_step {q : Rung K wd} (h : Act e q) :
    (q.lvl = ⊤ ∧ e (Sum.inr q) = Sum.inl q.tgt) ∨
      ∃ q' : Rung K wd, q'.src = q.src ∧ q'.tgt = q.tgt ∧ q.lvl ⋖ q'.lvl ∧ Act e q' ∧
        e (Sum.inr q) = Sum.inr q' := by
  have hm := he (Sum.inr q)
  generalize hn : e (Sum.inr q) = n at hm
  rcases n with b | q'
  · obtain ⟨hb, hℓ⟩ := ladderEdge_inr_inl.mp hm
    exact Or.inl ⟨hℓ, (congrArg Sum.inl hb).symm⟩
  · rcases ladderEdge_inr_inr.mp hm with rfl | ⟨ha, hb, hℓ⟩
    · exact absurd hn h
    · exact Or.inr ⟨q', ha.symm, hb.symm, hℓ,
        act_of_eq_inr e hn fun h' : q = q' => hℓ.lt.ne (congrArg Rung.lvl h'), rfl⟩

include he in
theorem act_top {q : Rung K wd} (h : Act e q) (ht : q.lvl = ⊤) :
    e (Sum.inr q) = Sum.inl q.tgt := by
  rcases act_step e he h with ⟨_, h'⟩ | ⟨q', _, _, hℓ, _, _⟩
  · exact h'
  · exact absurd hℓ.lt (ht ▸ not_top_lt)

/-- The target of the edge leaving `a`: where the cover sends `a`. -/
def tgt (a : V) : V :=
  Sum.elim (fun _ => a) Rung.tgt (e (Sum.inl a))

omit [LinearOrder Λ] [BoundedOrder Λ] in
theorem tgt_eq {a : V} {q : Rung K wd} (h : e (Sum.inl a) = Sum.inr q) : tgt e a = q.tgt := by
  rw [tgt, h]
  rfl

include he in
/-- The cover sends `a` to a rung of the least level of the edge to
`tgt e a`. -/
theorem exists_act_bot (a : V) :
    ∃ q : Rung K wd, q.src = a ∧ q.tgt = tgt e a ∧ q.lvl = ⊥ ∧ Act e q ∧
      e (Sum.inl a) = Sum.inr q := by
  have hm := he (Sum.inl a)
  generalize hn : e (Sum.inl a) = n at hm
  rcases n with b | q
  · exact absurd hm (ladderEdge_inl_inl a b)
  · obtain ⟨ha, hℓ⟩ := ladderEdge_inl_inr.mp hm
    exact ⟨q, ha, (tgt_eq e hn).symm, hℓ, act_of_eq_inl e hn, rfl⟩

variable [Finite Λ]

include he in
/-- **No rung of an unused edge is active.** -/
theorem not_act_of_ne (q : Rung K wd) (hq : q.tgt ≠ tgt e q.src) : ¬Act e q := by
  induction hℓ : q.lvl using WellFoundedLT.induction generalizing q with
  | _ ℓ ih =>
  intro h
  rcases of_act e he h with ⟨_, h'⟩ | ⟨q', ha, hb, hℓ', hact, _⟩
  · exact hq (tgt_eq e h').symm
  · exact ih q'.lvl (hℓ ▸ hℓ'.lt) q' (by rw [hb, ha]; exact hq) rfl hact

include he in
/-- **Every level of a used edge has exactly one active rung.** -/
theorem existsUnique_act (a : V) (ℓ : Λ) :
    ∃! q : Rung K wd, q.src = a ∧ q.tgt = tgt e a ∧ q.lvl = ℓ ∧ Act e q := by
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
  by_cases hb : ℓ = ⊥
  · subst hb
    obtain ⟨q, ha, ht, hℓ, hact, hq⟩ := exists_act_bot e he a
    refine ⟨q, ⟨ha, ht, hℓ, hact⟩, fun q' ⟨ha', _, hℓ', hact'⟩ => ?_⟩
    rcases of_act e he hact' with ⟨_, h'⟩ | ⟨_, _, _, hℓ'', _, _⟩
    · exact Sum.inr.inj (h'.symm.trans (ha' ▸ hq))
    · exact absurd hℓ''.lt (hℓ' ▸ not_lt_bot)
  · obtain ⟨ℓ₀, hℓ₀⟩ := exists_covBy_of_wellFoundedGT (isMin_iff_eq_bot.not.mpr hb)
    obtain ⟨q₀, ⟨ha₀, ht₀, hℓ₀', hact₀⟩, huniq₀⟩ := ih ℓ₀ hℓ₀.lt
    rcases act_step e he hact₀ with ⟨htop, _⟩ | ⟨q, ha, ht, hℓ, hact, hq⟩
    · exact absurd hℓ₀.lt (hℓ₀' ▸ htop ▸ not_top_lt)
    · have hqℓ : q.lvl = ℓ := covBy_right_unique (hℓ₀' ▸ hℓ) hℓ₀
      refine ⟨q, ⟨ha ▸ ha₀, ht ▸ ht₀, hqℓ, hact⟩, fun q' ⟨ha', ht', hℓ', hact'⟩ => ?_⟩
      rcases of_act e he hact' with ⟨hb', _⟩ | ⟨q₀', ha₀', ht₀', hℓ₀'', hact₀', hq'⟩
      · exact absurd (hℓ'.symm.trans hb') hb
      · have : q₀' = q₀ := huniq₀ q₀' ⟨ha₀'.trans ha', ht₀'.trans ht',
          covBy_left_unique (hℓ' ▸ hℓ₀'') (hℓ₀' ▸ hℓ₀), hact₀'⟩
        exact Sum.inr.inj (hq'.symm.trans (this ▸ hq))

/-- The active rung of a level of a used edge. -/
noncomputable def actRung (a : V) (ℓ : Λ) : Rung K wd :=
  Classical.choose (existsUnique_act e he a ℓ).exists

theorem actRung_spec (a : V) (ℓ : Λ) :
    (actRung e he a ℓ).src = a ∧ (actRung e he a ℓ).tgt = tgt e a ∧
      (actRung e he a ℓ).lvl = ℓ ∧ Act e (actRung e he a ℓ) :=
  Classical.choose_spec (existsUnique_act e he a ℓ).exists

theorem eq_actRung {q : Rung K wd} (h : Act e q) : q = actRung e he q.src q.lvl :=
  (existsUnique_act e he q.src q.lvl).unique
    ⟨rfl, by_contra fun h' => not_act_of_ne e he q h' h, rfl, h⟩ (actRung_spec e he _ _)

include he in
/-- The target map of a cover is injective: the active rung of the greatest
level is the only way into the target. -/
theorem tgt_injective : Function.Injective (tgt e) := by
  intro a a' h
  have h1 := act_top e he (actRung_spec e he a ⊤).2.2.2 (actRung_spec e he a ⊤).2.2.1
  have h2 := act_top e he (actRung_spec e he a' ⊤).2.2.2 (actRung_spec e he a' ⊤).2.2.1
  rw [(actRung_spec e he a ⊤).2.1] at h1
  rw [(actRung_spec e he a' ⊤).2.1, ← h] at h2
  have := Sum.inr.inj (e.injective (h1.trans h2.symm))
  rw [← (actRung_spec e he a ⊤).1, this, (actRung_spec e he a' ⊤).1]

variable [Finite V]

/-- **The choice underneath a cover.** -/
noncomputable def ofCover : Choice wd :=
  ⟨Equiv.ofBijective (tgt e) (Finite.injective_iff_bijective.mp (tgt_injective e he)),
    fun a ℓ => ⟨(actRung e he a ℓ).idx.val, by
      have h := (actRung e he a ℓ).2
      change (actRung e he a ℓ).idx.val <
        wd (actRung e he a ℓ).src (actRung e he a ℓ).tgt (actRung e he a ℓ).lvl at h
      rw [(actRung_spec e he a ℓ).1, (actRung_spec e he a ℓ).2.1,
        (actRung_spec e he a ℓ).2.2.1] at h
      exact h⟩⟩

theorem act_ofCover (hK : ∀ a b ℓ, wd a b ℓ ≤ K) (a : V) (ℓ : Λ) :
    act hK (ofCover e he) a ℓ = actRung e he a ℓ :=
  Rung.ext (actRung_spec e he a ℓ).1.symm (actRung_spec e he a ℓ).2.1.symm
    (actRung_spec e he a ℓ).2.2.1.symm (Fin.ext rfl)

theorem isAct_ofCover_iff (hK : ∀ a b ℓ, wd a b ℓ ≤ K) (q : Rung K wd) :
    IsAct (ofCover e he) q ↔ Act e q := by
  rw [isAct_iff hK, act_ofCover e he hK]
  constructor
  · intro h
    rw [h]
    exact (actRung_spec e he _ _).2.2.2
  · exact eq_actRung e he

/-- **The cover of the choice underneath a cover is that cover.** -/
theorem toCover_ofCover (hK : ∀ a b ℓ, wd a b ℓ ≤ K) (n : V ⊕ Rung K wd) :
    toCover hK (ofCover e he) n = e n := by
  rcases n with a | q
  · rw [toCover_inl, act_ofCover e he hK]
    obtain ⟨q, ha, ht, hℓ, hact, hq⟩ := exists_act_bot e he a
    rw [hq, eq_actRung e he hact, ha, hℓ]
  · by_cases h : Act e q
    · have h' := (isAct_ofCover_iff e he hK q).mpr h
      by_cases ht : q.lvl = ⊤
      · rw [toCover_inr_top hK _ h' ht, act_top e he h ht]
      · rw [toCover_inr_of_ne_top hK _ h' ht, act_ofCover e he hK]
        rcases act_step e he h with ⟨htop, _⟩ | ⟨q', ha, _, hℓ, hact, hq⟩
        · exact absurd htop ht
        · rw [hq, eq_actRung e he hact, ha, covBy_right_unique hℓ (covBy_lvlSucc ht)]
    · rw [toCover_inr_of_not hK _ (fun h' => h ((isAct_ofCover_iff e he hK q).mp h'))]
      exact (not_not.mp h).symm

end OfCover

section Main

variable {V Λ : Type} [LinearOrder Λ] [BoundedOrder Λ] {K : ℕ} {wd : V → V → Λ → ℕ}

/-- **The covers of the ladder graph are the choices.** -/
theorem toCoverEquiv_bijective [Finite V] [Finite Λ] (hK : ∀ a b ℓ, wd a b ℓ ≤ K) :
    Function.Bijective (toCoverEquiv hK) :=
  ⟨toCoverEquiv_injective hK, fun ⟨e, he⟩ => ⟨ofCover e he, Subtype.ext (Equiv.ext fun n =>
    (toCoverEquiv_apply hK _ n).trans (toCover_ofCover e he hK n))⟩⟩

/-- **The permanent of the ladder expansion is the permanent of the matrix of
the products of the widths.** -/
theorem bperm_ladder [Fintype V] [DecidableEq V] [Fintype Λ] (hK : ∀ a b ℓ, wd a b ℓ ≤ K) :
    bperm (ladder K wd) = bperm fun a b => ∏ ℓ, wd a b ℓ := by
  classical
  rw [show ladder K wd = fun n n' => if LadderEdge K wd n n' then 1 else 0 from rfl, bperm_boole,
    ← Fintype.card_of_bijective (toCoverEquiv_bijective hK),
    Fintype.card_sigma, bperm, Nat.cast_id]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun a _ => by rw [Fintype.card_pi]; simp only [Fintype.card_fin]

end Main

end DescriptiveComplexity
