/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Vocabulary
import Lax799700Proofs.DescriptiveComplexity.Numbers.BinRel
import Lax799700Proofs.DescriptiveComplexity.Interpretation
import Mathlib.Algebra.BigOperators.Finprod
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
# Job sequencing: definition

SEQUENCING ([Karp 1972][karp1972reducibility]): given jobs with execution
times, deadlines and penalties, and a bound, is there a one-processor schedule
whose jobs missing their deadline carry a total penalty at most the bound?
Like Knapsack it is written in **binary**
(`Lax799700Proofs.DescriptiveComplexity.Numbers.BinRel`) – times, deadlines, penalties and the
bound – since under the unary encoding the problem is solvable in polynomial
time by dynamic programming and is therefore not NP-hard at all.

## The vocabulary

`FirstOrder.Language.jobSeq` carries

* `job j` and `posn p`, the jobs and the bit positions;
* `time j p`, `dline j p` and `pen j p`, the bits of the execution time, of
  the deadline and of the penalty of `j`;
* `bnd p`, the bits of the penalty bound;
* `le`, a linear order fixing the place values, folded into the yes-instances
  (`Lax799700Proofs.DescriptiveComplexity.IsLinOrd`) as everywhere in the binary encoding.

## The schedule

A schedule is a **linear order on the universe** rather than a permutation of
an initial segment: on a finite universe the two are the same thing, and a
relation is what a `Σ₁` certificate can guess and what a first-order kernel
can constrain. A job's completion time is then the total execution time of the
jobs at or before it (`Lax799700Proofs.DescriptiveComplexity.JSCompletion`), it is late when that
exceeds its deadline, and the schedule is good when the late jobs' penalties
sum to at most the bound. Only jobs are summed over, so the elements of the
universe that are bit positions ride along in the order harmlessly.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax799700.JobSequencing.jobSeq.Structure A]

end Shorthands

/-! ### Schedules -/

section Schedule

variable {A : Type} [Lax799700.JobSequencing.jobSeq.Structure A]

end Schedule

/-! ### The problem -/

section Problem

variable (A : Type) [Lax799700.JobSequencing.jobSeq.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.JobSequencing.jobSeq.Structure A] [Lax799700.JobSequencing.jobSeq.Structure B]

private theorem hasGoodSchedule_of_iso (e : A ≃[Lax799700.JobSequencing.jobSeq] B)
    (h : Lax799700.JobSequencing.HasGoodSchedule A) : Lax799700.JobSequencing.HasGoodSchedule B := by
  obtain ⟨hfin, hlin, sched, hslin, hbound⟩ := h
  have hle : ∀ a a' : A, Lax799700.JobSequencing.JSLe a a' ↔ Lax799700.JobSequencing.JSLe (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.JobSequencing.jsLe a a'
  have hposn : ∀ a : A, Lax799700.JobSequencing.JSPosn a ↔ Lax799700.JobSequencing.JSPosn (e a) := fun a => relMap_equiv₁ e Lax799700.JobSequencing.jsPosn a
  have hjob : ∀ a : A, Lax799700.JobSequencing.JSJob a ↔ Lax799700.JobSequencing.JSJob (e a) := fun a => relMap_equiv₁ e Lax799700.JobSequencing.jsJob a
  have htime : ∀ a a' : A, Lax799700.JobSequencing.JSTime a a' ↔ Lax799700.JobSequencing.JSTime (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.JobSequencing.jsTime a a'
  have hdline : ∀ a a' : A, Lax799700.JobSequencing.JSDline a a' ↔ Lax799700.JobSequencing.JSDline (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.JobSequencing.jsDline a a'
  have hpen : ∀ a a' : A, Lax799700.JobSequencing.JSPen a a' ↔ Lax799700.JobSequencing.JSPen (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.JobSequencing.jsPen a a'
  have hbnd : ∀ a : A, Lax799700.JobSequencing.JSBnd a ↔ Lax799700.JobSequencing.JSBnd (e a) := fun a => relMap_equiv₁ e Lax799700.JobSequencing.jsBnd a
  have htv : ∀ a : A, Lax799700.JobSequencing.JSTimeVal a = Lax799700.JobSequencing.JSTimeVal (e a) := fun a =>
    binNum_equiv e.toEquiv hle hposn (htime a)
  have hdv : ∀ a : A, Lax799700.JobSequencing.JSDlineVal a = Lax799700.JobSequencing.JSDlineVal (e a) := fun a =>
    binNum_equiv e.toEquiv hle hposn (hdline a)
  have hpv : ∀ a : A, Lax799700.JobSequencing.JSPenVal a = Lax799700.JobSequencing.JSPenVal (e a) := fun a =>
    binNum_equiv e.toEquiv hle hposn (hpen a)
  have hbv : Lax799700.JobSequencing.JSBound A = Lax799700.JobSequencing.JSBound B := binNum_equiv e.toEquiv hle hposn hbnd
  have hsymm : ∀ b : B, e (e.toEquiv.symm b) = b := fun b => e.toEquiv.apply_symm_apply b
  have hsymm' : ∀ a : A, e.toEquiv.symm (e a) = a := fun a => e.toEquiv.symm_apply_apply a
  have hjob' : ∀ b : B, Lax799700.JobSequencing.JSJob b ↔ Lax799700.JobSequencing.JSJob (e.toEquiv.symm b) := fun b => by
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
  have hcompl : ∀ a : A, Lax799700.JobSequencing.JSCompletion σ (e a) = Lax799700.JobSequencing.JSCompletion sched a := by
    intro a
    rw [Lax799700.JobSequencing.JSCompletion, Lax799700.JobSequencing.JSCompletion,
      htransport Lax799700.JobSequencing.JSTimeVal Lax799700.JobSequencing.JSTimeVal htv fun x => Lax799700.JobSequencing.JSJob x ∧ sched x a]
    refine finsum_mem_congr (Set.ext fun b => ?_) fun _ _ => rfl
    simp only [Set.mem_ofPred_eq, hσ, hsymm' a]
    exact and_congr_left fun _ => hjob' b
  have hlate : ∀ a : A, Lax799700.JobSequencing.JSLate σ (e a) ↔ Lax799700.JobSequencing.JSLate sched a := by
    intro a
    rw [Lax799700.JobSequencing.JSLate, Lax799700.JobSequencing.JSLate, hcompl a, ← hdv a]
  have hlate' : ∀ b : B, Lax799700.JobSequencing.JSLate σ b ↔ Lax799700.JobSequencing.JSLate sched (e.toEquiv.symm b) := by
    intro b
    have h := hlate (e.toEquiv.symm b)
    rwa [hsymm b] at h
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin, σ,
    IsLinOrd.of_equiv e.toEquiv (fun a a' => by
      simp only [hσ, e.toEquiv.symm_apply_apply]) hslin, ?_⟩
  refine le_trans (le_of_eq ?_) (hbv ▸ hbound)
  rw [Lax799700.JobSequencing.JSPenalty, Lax799700.JobSequencing.JSPenalty,
    htransport Lax799700.JobSequencing.JSPenVal Lax799700.JobSequencing.JSPenVal hpv fun x => Lax799700.JobSequencing.JSJob x ∧ Lax799700.JobSequencing.JSLate sched x]
  refine finsum_mem_congr (Set.ext fun b => ?_) fun _ _ => rfl
  simp only [Set.mem_ofPred_eq]
  exact and_congr (hjob' b) (hlate' b)

/-- Being a yes-instance of job sequencing is isomorphism-invariant. -/
theorem hasGoodSchedule_iso (e : A ≃[Lax799700.JobSequencing.jobSeq] B) :
    Lax799700.JobSequencing.HasGoodSchedule A ↔ Lax799700.JobSequencing.HasGoodSchedule B :=
  ⟨hasGoodSchedule_of_iso e, hasGoodSchedule_of_iso e.symm⟩

end Iso

/-- SEQUENCING, as a problem on job-sequencing instances: is there a schedule
whose late jobs carry a total penalty at most the bound? The times, deadlines,
penalties and bound are written in *binary*, which is what makes the problem
NP-hard rather than polynomial-time. -/
def JobSequencing : Lax904597.Problems.DecisionProblem Lax799700.JobSequencing.jobSeq where
  Holds := fun A inst => @Lax799700.JobSequencing.HasGoodSchedule A inst
  iso_invariant := fun e => hasGoodSchedule_iso e

end Lax799700Proofs.DescriptiveComplexity


