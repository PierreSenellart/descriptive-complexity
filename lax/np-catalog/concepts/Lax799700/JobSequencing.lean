import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Syntax
import Lax799700.Common
import Lax904597.Machines
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Job sequencing
type: theorem
---
SEQUENCING: given jobs with execution times, deadlines and penalties, and
a bound, is there a one-processor schedule whose jobs missing their
deadline carry a total penalty at most the bound? Numbers are written in
binary, as for Knapsack. A schedule is a linear order on the universe,
which a certificate can guess and a first-order kernel can constrain; a
job's completion time is the total execution time of the jobs at or
before it (JSCompletion), it is late when that exceeds its deadline, and
the schedule is good when the late jobs' penalties sum to at most the
bound. Membership is by an existential second-order definition, hardness
by an ordered first-order reduction from NAE-3SAT.

-/

namespace Lax799700.JobSequencing

open Lax799700.Common Lax904597.Machines

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive jobSeqRel : ℕ → Type where
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
def jobSeq : FirstOrder.Language :=
  ⟨fun _ => Empty, jobSeqRel⟩

instance instIsRelationalJobSeq : FirstOrder.Language.IsRelational jobSeq := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `job j`: `j` is a job. -/
abbrev jsJob : jobSeq.Relations 1 :=
  .job

/-- `posn p`: `p` is a bit position. -/
abbrev jsPosn : jobSeq.Relations 1 :=
  .posn

/-- `time j p`: the execution time of `j` has bit 1 at position `p`. -/
abbrev jsTime : jobSeq.Relations 2 :=
  .time

/-- `dline j p`: the deadline of `j` has bit 1 at position `p`. -/
abbrev jsDline : jobSeq.Relations 2 :=
  .dline

/-- `pen j p`: the penalty of `j` has bit 1 at position `p`. -/
abbrev jsPen : jobSeq.Relations 2 :=
  .pen

/-- `bnd p`: the penalty bound has bit 1 at position `p`. -/
abbrev jsBnd : jobSeq.Relations 1 :=
  .bnd

/-- `le a b`: the linear order carrying the place values. -/
abbrev jsLe : jobSeq.Relations 2 :=
  .le

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [jobSeq.Structure A]

/-- `job j`: `j` is a job.  -/
def JSJob {A : Type} [jobSeq.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsJob ![a0]

/-- `posn p`: `p` is a bit position.  -/
def JSPosn {A : Type} [jobSeq.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsPosn ![a0]

/-- `time j p`: the execution time of `j` has bit 1 at position `p`.  -/
def JSTime {A : Type} [jobSeq.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsTime ![a0, a1]

/-- `dline j p`: the deadline of `j` has bit 1 at position `p`.  -/
def JSDline {A : Type} [jobSeq.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsDline ![a0, a1]

/-- `pen j p`: the penalty of `j` has bit 1 at position `p`.  -/
def JSPen {A : Type} [jobSeq.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsPen ![a0, a1]

/-- `bnd p`: the penalty bound has bit 1 at position `p`.  -/
def JSBnd {A : Type} [jobSeq.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsBnd ![a0]

/-- `le a b`: the linear order carrying the place values.  -/
def JSLe {A : Type} [jobSeq.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsLe ![a0, a1]

/-- The execution time of a job, decoded. -/
noncomputable def JSTimeVal (j : A) : ℕ := binNum JSLe JSPosn (JSTime j)

/-- The deadline of a job, decoded. -/
noncomputable def JSDlineVal (j : A) : ℕ := binNum JSLe JSPosn (JSDline j)

/-- The penalty of a job, decoded. -/
noncomputable def JSPenVal (j : A) : ℕ := binNum JSLe JSPosn (JSPen j)

end Shorthands

/-- The penalty bound of an instance, decoded. -/
noncomputable def JSBound (A : Type) [jobSeq.Structure A] : ℕ :=
  binNum (JSLe (A := A)) JSPosn JSBnd

section Schedule

variable {A : Type} [jobSeq.Structure A]

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

section Problem

variable (A : Type) [jobSeq.Structure A]

/-- A job-sequencing instance is a yes-instance when its order is a linear
order and some schedule – some linear order on the universe – leaves late only
jobs whose penalties sum to at most the bound. -/
def HasGoodSchedule : Prop :=
  Finite A ∧ IsLinOrd (JSLe (A := A)) ∧
    ∃ sched : A → A → Prop, IsLinOrd sched ∧ JSPenalty sched ≤ JSBound A

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasGoodSchedule` is isomorphism-invariant. -/
axiom hasGoodSchedule_iso : ∀ {A B : Type} [Lax799700.JobSequencing.jobSeq.Structure A] [Lax799700.JobSequencing.jobSeq.Structure B],
  (A ≃[Lax799700.JobSequencing.jobSeq] B) → (HasGoodSchedule A ↔ HasGoodSchedule B)

/-- The problem JobSequencing: does the structure satisfy `HasGoodSchedule`? -/
def JobSequencing : DecisionProblem Lax799700.JobSequencing.jobSeq :=
  DecisionProblem.ofPred HasGoodSchedule

/-- The yes-instances of JobSequencing are exactly the structures satisfying
`HasGoodSchedule`. -/
axiom jobSequencing_iff : ∀ (A : Type) [Lax799700.JobSequencing.jobSeq.Structure A], JobSequencing A ↔ HasGoodSchedule A

/-- JobSequencing is NP-complete. -/
axiom jobSequencing_NP_complete : NP.Complete JobSequencing

end Lax799700.JobSequencing
