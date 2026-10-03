/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Problems.JobSequencing.Defs
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# What a schedule can achieve

The one semantic fact about job sequencing that a reduction into it needs:
when every job carries the **same deadline** and its penalty equals its
execution time, a schedule is nothing but a choice of the jobs that meet the
deadline. Two halves:

* `Lax799700Proofs.DescriptiveComplexity.finsum_onTime_le` – the jobs a schedule leaves on time weigh
  at most the deadline. They are exactly the jobs at or before the *last* of
  them, so their total execution time is that job's completion time, and that
  job is on time;
* `Lax799700Proofs.DescriptiveComplexity.exists_schedule_onTime` – conversely, any set of jobs
  weighing at most the deadline can be put first, by ordering the universe
  through the key “not chosen, then the ambient order”
  (`Lax799700Proofs.DescriptiveComplexity.isLinOrd_of_key`), and then all of it is on time.

Together they give `Lax799700Proofs.DescriptiveComplexity.hasGoodSchedule_iff_exists_subset` and, when
the jobs weigh twice the deadline and the bound is the deadline,
`Lax799700Proofs.DescriptiveComplexity.hasGoodSchedule_iff_exists_half`: the instance is a
yes-instance exactly when some set of jobs weighs *exactly* the deadline.
That last form is Partition's condition, which is why a reduction into job
sequencing can be built out of a balanced-split gadget – provided it also
writes the deadline, its double and the bound, which is what constrains the
gadget.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Schedule

variable {A : Type} [Finite A] [Lax799700.JobSequencing.jobSeq.Structure A]

/-! ### Sums over sets of jobs -/

omit [Lax799700.JobSequencing.jobSeq.Structure A] in
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

omit [Lax799700.JobSequencing.jobSeq.Structure A] in
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
theorem jsCompletion_mono {sched : A → A → Prop} (hs : Lax904597.Machines.IsLinOrd sched) {i j : A}
    (hij : sched i j) : Lax799700.JobSequencing.JSCompletion sched i ≤ Lax799700.JobSequencing.JSCompletion sched j :=
  finsum_mem_mono (fun a ha => ⟨ha.1, hs.2.1 a i j ha.2 hij⟩) Lax799700.JobSequencing.JSTimeVal

variable {D : ℕ}

/-- With a common deadline, being on time is inherited backwards along the
schedule: the on-time jobs form a prefix. -/
theorem not_jsLate_of_sched {sched : A → A → Prop} (hs : Lax904597.Machines.IsLinOrd sched)
    (hdl : ∀ j : A, Lax799700.JobSequencing.JSJob j → Lax799700.JobSequencing.JSDlineVal j = D) {i j : A} (hi : Lax799700.JobSequencing.JSJob i) (hj : Lax799700.JobSequencing.JSJob j)
    (hij : sched i j) (hnl : ¬Lax799700.JobSequencing.JSLate sched j) : ¬Lax799700.JobSequencing.JSLate sched i := by
  intro hlate
  refine hnl ?_
  rw [Lax799700.JobSequencing.JSLate, hdl j hj]
  rw [Lax799700.JobSequencing.JSLate, hdl i hi] at hlate
  exact lt_of_lt_of_le hlate (jsCompletion_mono hs hij)

/-- **The jobs a schedule leaves on time weigh at most the deadline**: they are
the jobs at or before the last of them, so their total execution time is that
job's completion time. -/
theorem finsum_onTime_le {sched : A → A → Prop} (hs : Lax904597.Machines.IsLinOrd sched)
    (hdl : ∀ j : A, Lax799700.JobSequencing.JSJob j → Lax799700.JobSequencing.JSDlineVal j = D) :
    (∑ᶠ j ∈ {j : A | Lax799700.JobSequencing.JSJob j ∧ ¬Lax799700.JobSequencing.JSLate sched j}, Lax799700.JobSequencing.JSTimeVal j) ≤ D := by
  classical
  by_cases hne : ∃ j : A, Lax799700.JobSequencing.JSJob j ∧ ¬Lax799700.JobSequencing.JSLate sched j
  · obtain ⟨j₀, hj₀, hmax⟩ := exists_maxPos hs hne
    have hset : {j : A | Lax799700.JobSequencing.JSJob j ∧ ¬Lax799700.JobSequencing.JSLate sched j} = {j : A | Lax799700.JobSequencing.JSJob j ∧ sched j j₀} := by
      ext j
      constructor
      · exact fun hj => ⟨hj.1, hmax j hj⟩
      · rintro ⟨hj, hle⟩
        exact ⟨hj, not_jsLate_of_sched hs hdl hj hj₀.1 hle hj₀.2⟩
    rw [hset]
    have hnl := hj₀.2
    rw [Lax799700.JobSequencing.JSLate, not_lt, hdl j₀ hj₀.1] at hnl
    exact hnl
  · have hempty : {j : A | Lax799700.JobSequencing.JSJob j ∧ ¬Lax799700.JobSequencing.JSLate sched j} = (∅ : Set A) := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hj => hne ⟨j, hj⟩
    rw [hempty, finsum_mem_empty]
    exact Nat.zero_le _

/-! ### Putting a set of jobs first -/

variable [LinearOrder A]

/-- **Any set of jobs weighing at most the deadline can be scheduled first**,
by ordering the universe through the key “not chosen, then the ambient
order”. Everything chosen is then on time. -/
theorem exists_schedule_onTime {S : A → Prop}
    (hsum : (∑ᶠ j ∈ {j : A | S j}, Lax799700.JobSequencing.JSTimeVal j) ≤ D)
    (hdl : ∀ j : A, Lax799700.JobSequencing.JSJob j → Lax799700.JobSequencing.JSDlineVal j = D) :
    ∃ sched : A → A → Prop, Lax904597.Machines.IsLinOrd sched ∧ ∀ j : A, Lax799700.JobSequencing.JSJob j → S j → ¬Lax799700.JobSequencing.JSLate sched j := by
  classical
  set key : A → ℕ × A := fun a => (if S a then 0 else 1, a) with hkey
  set sched : A → A → Prop := fun a b => lexRel (· ≤ ·) (· ≤ ·) (key a) (key b) with hsched
  have hslin : Lax904597.Machines.IsLinOrd sched :=
    isLinOrd_of_key (isLinOrd_lexRel isLinOrd_le isLinOrd_le) key
      (fun a b h => congrArg Prod.snd h) fun _ _ => Iff.rfl
  refine ⟨sched, hslin, fun j hj hSj hlate => ?_⟩
  -- everything at or before a chosen job is chosen
  have hpre : ∀ k : A, Lax799700.JobSequencing.JSJob k ∧ sched k j → S k := by
    rintro k ⟨-, hk⟩
    rcases hk with ⟨hle, hne⟩ | ⟨he, -⟩
    · by_contra hSk
      simp only [hkey, if_pos hSj, if_neg hSk] at hle
      exact absurd (Nat.le_zero.mp hle) one_ne_zero
    · by_contra hSk
      simp only [hkey, if_pos hSj, if_neg hSk] at he
      exact absurd he one_ne_zero
  have hle : Lax799700.JobSequencing.JSCompletion sched j ≤ ∑ᶠ k ∈ {k : A | S k}, Lax799700.JobSequencing.JSTimeVal k :=
    finsum_mem_mono hpre Lax799700.JobSequencing.JSTimeVal
  rw [Lax799700.JobSequencing.JSLate, hdl j hj] at hlate
  exact absurd (le_trans hle hsum) (Nat.not_le.mpr hlate)

/-! ### The characterization -/

/-- **A schedule is a choice of the jobs that meet the deadline**: when all
deadlines agree and each penalty is its job's execution time, the instance is
a yes-instance exactly when some set of jobs fits in the deadline while the
jobs it leaves out fit in the bound. -/
theorem hasGoodSchedule_iff_exists_subset (hlin : Lax904597.Machines.IsLinOrd (Lax799700.JobSequencing.JSLe (A := A)))
    (hdl : ∀ j : A, Lax799700.JobSequencing.JSJob j → Lax799700.JobSequencing.JSDlineVal j = D)
    (hpt : ∀ j : A, Lax799700.JobSequencing.JSJob j → Lax799700.JobSequencing.JSPenVal j = Lax799700.JobSequencing.JSTimeVal j) :
    Lax799700.JobSequencing.HasGoodSchedule A ↔ ∃ S : A → Prop, (∀ j, S j → Lax799700.JobSequencing.JSJob j) ∧
      (∑ᶠ j ∈ {j : A | S j}, Lax799700.JobSequencing.JSTimeVal j) ≤ D ∧
      (∑ᶠ j ∈ {j : A | Lax799700.JobSequencing.JSJob j ∧ ¬S j}, Lax799700.JobSequencing.JSTimeVal j) ≤ Lax799700.JobSequencing.JSBound A := by
  constructor
  · rintro ⟨-, -, sched, hslin, hpen⟩
    refine ⟨fun j => Lax799700.JobSequencing.JSJob j ∧ ¬Lax799700.JobSequencing.JSLate sched j, fun j hj => hj.1,
      finsum_onTime_le hslin hdl, ?_⟩
    have hset : {j : A | Lax799700.JobSequencing.JSJob j ∧ ¬(Lax799700.JobSequencing.JSJob j ∧ ¬Lax799700.JobSequencing.JSLate sched j)} =
        {j : A | Lax799700.JobSequencing.JSJob j ∧ Lax799700.JobSequencing.JSLate sched j} := by
      ext j
      simp only [Set.mem_ofPred_eq, not_and, not_not]
      exact and_congr_right fun hj => ⟨fun h => h hj, fun h _ => h⟩
    rw [hset]
    refine le_trans (le_of_eq ?_) hpen
    exact (finsum_mem_congr rfl fun j hj => hpt j hj.1).symm
  · rintro ⟨S, hSj, hSsum, hrest⟩
    obtain ⟨sched, hslin, honTime⟩ := exists_schedule_onTime hSsum hdl
    refine ⟨‹Finite A›, hlin, sched, hslin, ?_⟩
    have hpen : Lax799700.JobSequencing.JSPenalty sched =
        ∑ᶠ j ∈ {j : A | Lax799700.JobSequencing.JSJob j ∧ Lax799700.JobSequencing.JSLate sched j}, Lax799700.JobSequencing.JSTimeVal j :=
      finsum_mem_congr rfl fun j hj => hpt j hj.1
    have hmono : (∑ᶠ j ∈ {j : A | Lax799700.JobSequencing.JSJob j ∧ Lax799700.JobSequencing.JSLate sched j}, Lax799700.JobSequencing.JSTimeVal j) ≤
        ∑ᶠ j ∈ {j : A | Lax799700.JobSequencing.JSJob j ∧ ¬S j}, Lax799700.JobSequencing.JSTimeVal j := by
      refine finsum_mem_mono ?_ Lax799700.JobSequencing.JSTimeVal
      rintro j ⟨hj, hlate⟩
      exact ⟨hj, fun hSjj => honTime j hj hSjj hlate⟩
    rw [hpen]
    exact le_trans hmono hrest

/-- **The balanced form**: when the jobs weigh twice the deadline and the bound
is the deadline, a good schedule is a set of jobs weighing *exactly* the
deadline. This is Partition's condition, and it is what a reduction into job
sequencing has to produce – together with the deadline, its double and the
bound, all three written in binary. -/
theorem hasGoodSchedule_iff_exists_half (hlin : Lax904597.Machines.IsLinOrd (Lax799700.JobSequencing.JSLe (A := A)))
    (hdl : ∀ j : A, Lax799700.JobSequencing.JSJob j → Lax799700.JobSequencing.JSDlineVal j = D)
    (hpt : ∀ j : A, Lax799700.JobSequencing.JSJob j → Lax799700.JobSequencing.JSPenVal j = Lax799700.JobSequencing.JSTimeVal j)
    (htot : (∑ᶠ j ∈ {j : A | Lax799700.JobSequencing.JSJob j}, Lax799700.JobSequencing.JSTimeVal j) = 2 * D) (hbnd : Lax799700.JobSequencing.JSBound A = D) :
    Lax799700.JobSequencing.HasGoodSchedule A ↔ ∃ S : A → Prop, (∀ j, S j → Lax799700.JobSequencing.JSJob j) ∧
      (∑ᶠ j ∈ {j : A | S j}, Lax799700.JobSequencing.JSTimeVal j) = D := by
  rw [hasGoodSchedule_iff_exists_subset hlin hdl hpt]
  constructor
  · rintro ⟨S, hSj, hSsum, hrest⟩
    refine ⟨S, hSj, ?_⟩
    have hsplit := finsum_split hSj Lax799700.JobSequencing.JSTimeVal
    rw [htot] at hsplit
    rw [hbnd] at hrest
    omega
  · rintro ⟨S, hSj, hSsum⟩
    have hsplit := finsum_split hSj Lax799700.JobSequencing.JSTimeVal
    rw [htot] at hsplit
    refine ⟨S, hSj, le_of_eq hSsum, ?_⟩
    rw [hbnd]
    omega

end Schedule

end Lax799700Proofs.DescriptiveComplexity


