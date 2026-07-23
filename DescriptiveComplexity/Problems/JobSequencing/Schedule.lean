/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.JobSequencing.Defs

/-!
# What a schedule can achieve

The one semantic fact about job sequencing that a reduction into it needs:
when every job carries the **same deadline** and its penalty equals its
execution time, a schedule is nothing but a choice of the jobs that meet the
deadline. Two halves:

* `DescriptiveComplexity.finsum_onTime_le` – the jobs a schedule leaves on time weigh
  at most the deadline. They are exactly the jobs at or before the *last* of
  them, so their total execution time is that job's completion time, and that
  job is on time;
* `DescriptiveComplexity.exists_schedule_onTime` – conversely, any set of jobs
  weighing at most the deadline can be put first, by ordering the universe
  through the key “not chosen, then the ambient order”
  (`DescriptiveComplexity.isLinOrd_of_key`), and then all of it is on time.

Together they give `DescriptiveComplexity.hasGoodSchedule_iff_exists_subset` and, when
the jobs weigh twice the deadline and the bound is the deadline,
`DescriptiveComplexity.hasGoodSchedule_iff_exists_half`: the instance is a
yes-instance exactly when some set of jobs weighs *exactly* the deadline.
That last form is Partition's condition, which is why a reduction into job
sequencing can be built out of a balanced-split gadget – provided it also
writes the deadline, its double and the bound, which is what constrains the
gadget (see `ROADMAP.md`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Schedule

variable {A : Type} [Finite A] [Language.jobSeq.Structure A]

/-! ### Sums over sets of jobs -/

omit [Language.jobSeq.Structure A] in
/-- A sum of naturals over a smaller set is smaller. -/
private theorem finsum_mem_mono {P Q : A → Prop} (h : ∀ a, P a → Q a) (w : A → ℕ) :
    (∑ᶠ a ∈ {a : A | P a}, w a) ≤ ∑ᶠ a ∈ {a : A | Q a}, w a := by
  classical
  have hset : {a : A | Q a} = {a : A | P a} ∪ {a : A | Q a ∧ ¬P a} := by
    ext a
    constructor
    · intro ha
      by_cases hp : P a
      · exact Or.inl hp
      · exact Or.inr ⟨ha, hp⟩
    · rintro (hp | ⟨hq, -⟩)
      · exact h a hp
      · exact hq
  have hdisj : Disjoint {a : A | P a} {a : A | Q a ∧ ¬P a} := by
    rw [Set.disjoint_left]
    rintro a hp ⟨-, hnp⟩
    exact hnp hp
  rw [hset, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)]
  exact Nat.le_add_right _ _

omit [Language.jobSeq.Structure A] in
/-- Splitting the jobs into a chosen set and the rest. -/
private theorem finsum_split {S : A → Prop} {Job : A → Prop} (hS : ∀ j, S j → Job j)
    (w : A → ℕ) :
    (∑ᶠ j ∈ {j : A | S j}, w j) + ∑ᶠ j ∈ {j : A | Job j ∧ ¬S j}, w j
      = ∑ᶠ j ∈ {j : A | Job j}, w j := by
  classical
  have hset : {j : A | Job j} = {j : A | S j} ∪ {j : A | Job j ∧ ¬S j} := by
    ext j
    constructor
    · intro hj
      by_cases hs : S j
      · exact Or.inl hs
      · exact Or.inr ⟨hj, hs⟩
    · rintro (hs | ⟨hj, -⟩)
      · exact hS j hs
      · exact hj
  have hdisj : Disjoint {j : A | S j} {j : A | Job j ∧ ¬S j} := by
    rw [Set.disjoint_left]
    rintro j hs ⟨-, hns⟩
    exact hns hs
  rw [hset, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)]

/-! ### Completion times along a schedule -/

/-- Completion times grow along the schedule. -/
theorem jsCompletion_mono {sched : A → A → Prop} (hs : IsLinOrd sched) {i j : A}
    (hij : sched i j) : JSCompletion sched i ≤ JSCompletion sched j :=
  finsum_mem_mono (fun a ha => ⟨ha.1, hs.2.1 a i j ha.2 hij⟩) JSTimeVal

variable {D : ℕ}

/-- With a common deadline, being on time is inherited backwards along the
schedule: the on-time jobs form a prefix. -/
theorem not_jsLate_of_sched {sched : A → A → Prop} (hs : IsLinOrd sched)
    (hdl : ∀ j : A, JSJob j → JSDlineVal j = D) {i j : A} (hi : JSJob i) (hj : JSJob j)
    (hij : sched i j) (hnl : ¬JSLate sched j) : ¬JSLate sched i := by
  intro hlate
  refine hnl ?_
  rw [JSLate, hdl j hj]
  rw [JSLate, hdl i hi] at hlate
  exact lt_of_lt_of_le hlate (jsCompletion_mono hs hij)

/-- **The jobs a schedule leaves on time weigh at most the deadline**: they are
the jobs at or before the last of them, so their total execution time is that
job's completion time. -/
theorem finsum_onTime_le {sched : A → A → Prop} (hs : IsLinOrd sched)
    (hdl : ∀ j : A, JSJob j → JSDlineVal j = D) :
    (∑ᶠ j ∈ {j : A | JSJob j ∧ ¬JSLate sched j}, JSTimeVal j) ≤ D := by
  classical
  by_cases hne : ∃ j : A, JSJob j ∧ ¬JSLate sched j
  · obtain ⟨j₀, hj₀, hmax⟩ := exists_maxPos hs hne
    have hset : {j : A | JSJob j ∧ ¬JSLate sched j} = {j : A | JSJob j ∧ sched j j₀} := by
      ext j
      constructor
      · exact fun hj => ⟨hj.1, hmax j hj⟩
      · rintro ⟨hj, hle⟩
        exact ⟨hj, not_jsLate_of_sched hs hdl hj hj₀.1 hle hj₀.2⟩
    rw [hset]
    have hnl := hj₀.2
    rw [JSLate, not_lt, hdl j₀ hj₀.1] at hnl
    exact hnl
  · have hempty : {j : A | JSJob j ∧ ¬JSLate sched j} = (∅ : Set A) := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hj => hne ⟨j, hj⟩
    rw [hempty, finsum_mem_empty]
    exact Nat.zero_le _

/-! ### Putting a set of jobs first -/

variable [LinearOrder A]

/-- **Any set of jobs weighing at most the deadline can be scheduled first**,
by ordering the universe through the key “not chosen, then the ambient
order”. Everything chosen is then on time. -/
theorem exists_schedule_onTime {S : A → Prop}
    (hsum : (∑ᶠ j ∈ {j : A | S j}, JSTimeVal j) ≤ D)
    (hdl : ∀ j : A, JSJob j → JSDlineVal j = D) :
    ∃ sched : A → A → Prop, IsLinOrd sched ∧ ∀ j : A, JSJob j → S j → ¬JSLate sched j := by
  classical
  set key : A → ℕ × A := fun a => (if S a then 0 else 1, a) with hkey
  set sched : A → A → Prop := fun a b => lexRel (· ≤ ·) (· ≤ ·) (key a) (key b) with hsched
  have hslin : IsLinOrd sched :=
    isLinOrd_of_key (isLinOrd_lexRel isLinOrd_le isLinOrd_le) key
      (fun a b h => congrArg Prod.snd h) fun _ _ => Iff.rfl
  refine ⟨sched, hslin, fun j hj hSj hlate => ?_⟩
  -- everything at or before a chosen job is chosen
  have hpre : ∀ k : A, JSJob k ∧ sched k j → S k := by
    rintro k ⟨-, hk⟩
    rcases hk with ⟨hle, hne⟩ | ⟨he, -⟩
    · by_contra hSk
      simp only [hkey, if_pos hSj, if_neg hSk] at hle
      exact absurd (Nat.le_zero.mp hle) one_ne_zero
    · by_contra hSk
      simp only [hkey, if_pos hSj, if_neg hSk] at he
      exact absurd he one_ne_zero
  have hle : JSCompletion sched j ≤ ∑ᶠ k ∈ {k : A | S k}, JSTimeVal k :=
    finsum_mem_mono hpre JSTimeVal
  rw [JSLate, hdl j hj] at hlate
  exact absurd (le_trans hle hsum) (Nat.not_le.mpr hlate)

/-! ### The characterization -/

/-- **A schedule is a choice of the jobs that meet the deadline**: when all
deadlines agree and each penalty is its job's execution time, the instance is
a yes-instance exactly when some set of jobs fits in the deadline while the
jobs it leaves out fit in the bound. -/
theorem hasGoodSchedule_iff_exists_subset (hlin : IsLinOrd (JSLe (A := A)))
    (hdl : ∀ j : A, JSJob j → JSDlineVal j = D)
    (hpt : ∀ j : A, JSJob j → JSPenVal j = JSTimeVal j) :
    HasGoodSchedule A ↔ ∃ S : A → Prop, (∀ j, S j → JSJob j) ∧
      (∑ᶠ j ∈ {j : A | S j}, JSTimeVal j) ≤ D ∧
      (∑ᶠ j ∈ {j : A | JSJob j ∧ ¬S j}, JSTimeVal j) ≤ JSBound A := by
  constructor
  · rintro ⟨-, -, sched, hslin, hpen⟩
    refine ⟨fun j => JSJob j ∧ ¬JSLate sched j, fun j hj => hj.1,
      finsum_onTime_le hslin hdl, ?_⟩
    have hset : {j : A | JSJob j ∧ ¬(JSJob j ∧ ¬JSLate sched j)} =
        {j : A | JSJob j ∧ JSLate sched j} := by
      ext j
      simp only [Set.mem_setOf_eq, not_and, not_not]
      exact and_congr_right fun hj => ⟨fun h => h hj, fun h _ => h⟩
    rw [hset]
    refine le_trans (le_of_eq ?_) hpen
    exact (finsum_mem_congr rfl fun j hj => hpt j hj.1).symm
  · rintro ⟨S, hSj, hSsum, hrest⟩
    obtain ⟨sched, hslin, honTime⟩ := exists_schedule_onTime hSsum hdl
    refine ⟨‹Finite A›, hlin, sched, hslin, ?_⟩
    have hpen : JSPenalty sched =
        ∑ᶠ j ∈ {j : A | JSJob j ∧ JSLate sched j}, JSTimeVal j :=
      finsum_mem_congr rfl fun j hj => hpt j hj.1
    have hmono : (∑ᶠ j ∈ {j : A | JSJob j ∧ JSLate sched j}, JSTimeVal j) ≤
        ∑ᶠ j ∈ {j : A | JSJob j ∧ ¬S j}, JSTimeVal j := by
      refine finsum_mem_mono ?_ JSTimeVal
      rintro j ⟨hj, hlate⟩
      exact ⟨hj, fun hSjj => honTime j hj hSjj hlate⟩
    rw [hpen]
    exact le_trans hmono hrest

/-- **The balanced form**: when the jobs weigh twice the deadline and the bound
is the deadline, a good schedule is a set of jobs weighing *exactly* the
deadline. This is Partition's condition, and it is what a reduction into job
sequencing has to produce – together with the deadline, its double and the
bound, all three written in binary. -/
theorem hasGoodSchedule_iff_exists_half (hlin : IsLinOrd (JSLe (A := A)))
    (hdl : ∀ j : A, JSJob j → JSDlineVal j = D)
    (hpt : ∀ j : A, JSJob j → JSPenVal j = JSTimeVal j)
    (htot : (∑ᶠ j ∈ {j : A | JSJob j}, JSTimeVal j) = 2 * D) (hbnd : JSBound A = D) :
    HasGoodSchedule A ↔ ∃ S : A → Prop, (∀ j, S j → JSJob j) ∧
      (∑ᶠ j ∈ {j : A | S j}, JSTimeVal j) = D := by
  rw [hasGoodSchedule_iff_exists_subset hlin hdl hpt]
  constructor
  · rintro ⟨S, hSj, hSsum, hrest⟩
    refine ⟨S, hSj, ?_⟩
    have hsplit := finsum_split hSj JSTimeVal
    rw [htot] at hsplit
    rw [hbnd] at hrest
    omega
  · rintro ⟨S, hSj, hSsum⟩
    have hsplit := finsum_split hSj JSTimeVal
    rw [htot] at hsplit
    refine ⟨S, hSj, le_of_eq hSsum, ?_⟩
    rw [hbnd]
    omega

end Schedule

end DescriptiveComplexity
