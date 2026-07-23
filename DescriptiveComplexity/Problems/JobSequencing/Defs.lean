/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel
import DescriptiveComplexity.Interpretation
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Job sequencing: definition

SEQUENCING ([Karp 1972][karp1972reducibility]): given jobs with execution
times, deadlines and penalties, and a bound, is there a one-processor schedule
whose jobs missing their deadline carry a total penalty at most the bound?
Like Knapsack it belongs to **representation (C)** – times, deadlines,
penalties and the bound are written in binary – since under the unary
representation the problem is solvable in polynomial time by dynamic
programming and is therefore not NP-hard at all.

## The vocabulary

`FirstOrder.Language.jobSeq` carries

* `job j` and `posn p`, the jobs and the bit positions;
* `time j p`, `dline j p` and `pen j p`, the bits of the execution time, of
  the deadline and of the penalty of `j`;
* `bnd p`, the bits of the penalty bound;
* `le`, a linear order fixing the place values, folded into the yes-instances
  (`DescriptiveComplexity.IsLinOrd`) as everywhere in representation (C).

## The schedule

A schedule is a **linear order on the universe** rather than a permutation of
an initial segment: on a finite universe the two are the same thing, and a
relation is what a `Σ₁` certificate can guess and what a first-order kernel
can constrain. A job's completion time is then the total execution time of the
jobs at or before it (`DescriptiveComplexity.JSCompletion`), it is late when that
exceeds its deadline, and the schedule is good when the late jobs' penalties
sum to at most the bound. Only jobs are summed over, so the elements of the
universe that are bit positions ride along in the order harmlessly.
-/

/- The language of job-sequencing instances lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.graph` and
`Language.order`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of job-sequencing instances. -/
inductive jobSeqRel : ℕ → Type
  /-- `job j`: `j` is a job. -/
  | job : jobSeqRel 1
  /-- `posn p`: `p` is a bit position. -/
  | posn : jobSeqRel 1
  /-- `time j p`: the execution time of `j` has bit 1 at position `p`. -/
  | time : jobSeqRel 2
  /-- `dline j p`: the deadline of `j` has bit 1 at position `p`. -/
  | dline : jobSeqRel 2
  /-- `pen j p`: the penalty of `j` has bit 1 at position `p`. -/
  | pen : jobSeqRel 2
  /-- `bnd p`: the penalty bound has bit 1 at position `p`. -/
  | bnd : jobSeqRel 1
  /-- `le a b`: the linear order carrying the place values. -/
  | le : jobSeqRel 2
  deriving DecidableEq

/-- The relational language of job-sequencing instances: jobs and bit
positions, the bits of each job's execution time, deadline and penalty, the
bits of the penalty bound, and a linear order. -/
protected def jobSeq : Language :=
  ⟨fun _ => Empty, jobSeqRel⟩
  deriving IsRelational

/-- The job symbol. -/
abbrev jsJob : Language.jobSeq.Relations 1 := .job

/-- The position symbol. -/
abbrev jsPosn : Language.jobSeq.Relations 1 := .posn

/-- The execution-time symbol. -/
abbrev jsTime : Language.jobSeq.Relations 2 := .time

/-- The deadline symbol. -/
abbrev jsDline : Language.jobSeq.Relations 2 := .dline

/-- The penalty symbol. -/
abbrev jsPen : Language.jobSeq.Relations 2 := .pen

/-- The bound symbol. -/
abbrev jsBnd : Language.jobSeq.Relations 1 := .bnd

/-- The order symbol. -/
abbrev jsLe : Language.jobSeq.Relations 2 := .le

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Language.jobSeq.Structure A]

/-- Being a job. -/
def JSJob (a : A) : Prop := RelMap jsJob ![a]

/-- Being a bit position. -/
def JSPosn (a : A) : Prop := RelMap jsPosn ![a]

/-- The bits of a job's execution time. -/
def JSTime (j p : A) : Prop := RelMap jsTime ![j, p]

/-- The bits of a job's deadline. -/
def JSDline (j p : A) : Prop := RelMap jsDline ![j, p]

/-- The bits of a job's penalty. -/
def JSPen (j p : A) : Prop := RelMap jsPen ![j, p]

/-- The bits of the penalty bound. -/
def JSBnd (p : A) : Prop := RelMap jsBnd ![p]

/-- The order carrying the place values. -/
def JSLe (a b : A) : Prop := RelMap jsLe ![a, b]

/-- The execution time of a job, decoded. -/
noncomputable def JSTimeVal (j : A) : ℕ := binNum JSLe JSPosn (JSTime j)

/-- The deadline of a job, decoded. -/
noncomputable def JSDlineVal (j : A) : ℕ := binNum JSLe JSPosn (JSDline j)

/-- The penalty of a job, decoded. -/
noncomputable def JSPenVal (j : A) : ℕ := binNum JSLe JSPosn (JSPen j)

end Shorthands

/-- The penalty bound of an instance, decoded. -/
noncomputable def JSBound (A : Type) [Language.jobSeq.Structure A] : ℕ :=
  binNum (JSLe (A := A)) JSPosn JSBnd

/-! ### Schedules -/

section Schedule

variable {A : Type} [Language.jobSeq.Structure A]

/-- The completion time of a job under a schedule: the total execution time of
the jobs scheduled at or before it. -/
noncomputable def JSCompletion (sched : A → A → Prop) (j : A) : ℕ :=
  ∑ᶠ i ∈ {i : A | JSJob i ∧ sched i j}, JSTimeVal i

/-- A job is late under a schedule when it completes after its deadline. -/
def JSLate (sched : A → A → Prop) (j : A) : Prop :=
  JSDlineVal j < JSCompletion sched j

/-- The total penalty of the jobs a schedule leaves late. -/
noncomputable def JSPenalty (sched : A → A → Prop) : ℕ :=
  ∑ᶠ j ∈ {j : A | JSJob j ∧ JSLate sched j}, JSPenVal j

end Schedule

/-! ### The problem -/

section Problem

variable (A : Type) [Language.jobSeq.Structure A]

/-- A job-sequencing instance is a yes-instance when its order is a linear
order and some schedule – some linear order on the universe – leaves late only
jobs whose penalties sum to at most the bound. -/
def HasGoodSchedule : Prop :=
  Finite A ∧ IsLinOrd (JSLe (A := A)) ∧
    ∃ sched : A → A → Prop, IsLinOrd sched ∧ JSPenalty sched ≤ JSBound A

end Problem

section Iso

variable {A B : Type} [Language.jobSeq.Structure A] [Language.jobSeq.Structure B]

private theorem hasGoodSchedule_of_iso (e : A ≃[Language.jobSeq] B)
    (h : HasGoodSchedule A) : HasGoodSchedule B := by
  obtain ⟨hfin, hlin, sched, hslin, hbound⟩ := h
  have hle : ∀ a a' : A, JSLe a a' ↔ JSLe (e a) (e a') := fun a a' =>
    relMap_equiv₂ e jsLe a a'
  have hposn : ∀ a : A, JSPosn a ↔ JSPosn (e a) := fun a => relMap_equiv₁ e jsPosn a
  have hjob : ∀ a : A, JSJob a ↔ JSJob (e a) := fun a => relMap_equiv₁ e jsJob a
  have htime : ∀ a a' : A, JSTime a a' ↔ JSTime (e a) (e a') := fun a a' =>
    relMap_equiv₂ e jsTime a a'
  have hdline : ∀ a a' : A, JSDline a a' ↔ JSDline (e a) (e a') := fun a a' =>
    relMap_equiv₂ e jsDline a a'
  have hpen : ∀ a a' : A, JSPen a a' ↔ JSPen (e a) (e a') := fun a a' =>
    relMap_equiv₂ e jsPen a a'
  have hbnd : ∀ a : A, JSBnd a ↔ JSBnd (e a) := fun a => relMap_equiv₁ e jsBnd a
  have htv : ∀ a : A, JSTimeVal a = JSTimeVal (e a) := fun a =>
    binNum_equiv e.toEquiv hle hposn (htime a)
  have hdv : ∀ a : A, JSDlineVal a = JSDlineVal (e a) := fun a =>
    binNum_equiv e.toEquiv hle hposn (hdline a)
  have hpv : ∀ a : A, JSPenVal a = JSPenVal (e a) := fun a =>
    binNum_equiv e.toEquiv hle hposn (hpen a)
  have hbv : JSBound A = JSBound B := binNum_equiv e.toEquiv hle hposn hbnd
  have hsymm : ∀ b : B, e (e.toEquiv.symm b) = b := fun b => e.toEquiv.apply_symm_apply b
  have hsymm' : ∀ a : A, e.toEquiv.symm (e a) = a := fun a => e.toEquiv.symm_apply_apply a
  have hjob' : ∀ b : B, JSJob b ↔ JSJob (e.toEquiv.symm b) := fun b => by
    rw [hjob (e.toEquiv.symm b), hsymm b]
  -- a sum of decoded numbers is carried along the equivalence
  have htransport : ∀ w : A → ℕ, ∀ w' : B → ℕ, (∀ a, w a = w' (e a)) → ∀ P : A → Prop,
      (∑ᶠ a ∈ {a : A | P a}, w a) = ∑ᶠ b ∈ {b : B | P (e.toEquiv.symm b)}, w' b := by
    intro w w' hw P
    refine finsum_mem_eq_of_bijOn e.toEquiv ?_ fun a _ => hw a
    refine ⟨fun a ha => ?_, e.toEquiv.injective.injOn,
      fun b hb => ⟨e.toEquiv.symm b, hb, e.toEquiv.apply_symm_apply b⟩⟩
    simpa using ha
  -- the schedule, read on the other side
  set σ : B → B → Prop := fun b b' => sched (e.toEquiv.symm b) (e.toEquiv.symm b') with hσ
  have hcompl : ∀ a : A, JSCompletion σ (e a) = JSCompletion sched a := by
    intro a
    rw [JSCompletion, JSCompletion,
      htransport JSTimeVal JSTimeVal htv fun x => JSJob x ∧ sched x a]
    refine finsum_mem_congr (Set.ext fun b => ?_) fun _ _ => rfl
    simp only [Set.mem_setOf_eq, hσ, hsymm' a]
    exact and_congr_left fun _ => hjob' b
  have hlate : ∀ a : A, JSLate σ (e a) ↔ JSLate sched a := by
    intro a
    rw [JSLate, JSLate, hcompl a, ← hdv a]
  have hlate' : ∀ b : B, JSLate σ b ↔ JSLate sched (e.toEquiv.symm b) := by
    intro b
    have h := hlate (e.toEquiv.symm b)
    rwa [hsymm b] at h
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin, σ,
    IsLinOrd.of_equiv e.toEquiv (fun a a' => by
      simp only [hσ, e.toEquiv.symm_apply_apply]) hslin, ?_⟩
  refine le_trans (le_of_eq ?_) (hbv ▸ hbound)
  rw [JSPenalty, JSPenalty,
    htransport JSPenVal JSPenVal hpv fun x => JSJob x ∧ JSLate sched x]
  refine finsum_mem_congr (Set.ext fun b => ?_) fun _ _ => rfl
  simp only [Set.mem_setOf_eq]
  exact and_congr (hjob' b) (hlate' b)

/-- Being a yes-instance of job sequencing is isomorphism-invariant. -/
theorem hasGoodSchedule_iso (e : A ≃[Language.jobSeq] B) :
    HasGoodSchedule A ↔ HasGoodSchedule B :=
  ⟨hasGoodSchedule_of_iso e, hasGoodSchedule_of_iso e.symm⟩

end Iso

/-- SEQUENCING, as a problem on job-sequencing instances: is there a schedule
whose late jobs carry a total penalty at most the bound? The times, deadlines,
penalties and bound are written in *binary*, which is what makes the problem
NP-hard rather than polynomial-time. -/
def JobSequencing : DecisionProblem Language.jobSeq where
  Holds := fun A inst => @HasGoodSchedule A inst
  iso_invariant := fun e => hasGoodSchedule_iso e

end DescriptiveComplexity
