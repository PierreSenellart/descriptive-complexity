/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.JobSequencing.Schedule
import DescriptiveComplexity.Problems.Knapsack.Chain
import DescriptiveComplexity.Numbers.Wide
import DescriptiveComplexity.SecondOrder

/-!
# The certificate of job sequencing

The syntax of the `Σ₁` definition of `DescriptiveComplexity.JobSequencing`: the
existential block and the first-order kernel. What is guessed is

* `sched`, the schedule – a binary relation the kernel forces to be a linear
  order, which on a finite universe is a permutation;
* `late`, the jobs that miss their deadline;
* `ps s` and `cy s`, the running totals and the carries of **two** walks: at
  `s = true` the completion times, walking the jobs along `sched` and adding
  execution times, and at `s = false` the penalties of the late jobs, walking
  them along the instance's own order.

Both walks run on the *wide* positions of `DescriptiveComplexity.Numbers.Wide`, since
a completion time is a sum of every execution time and a penalty total a sum
of every penalty; neither need fit where the instance writes. They are the
same five clauses read twice, so the clause family is a function of `s`, as in
`DescriptiveComplexity.Problems.Partition.Membership`.

What is new here, and what job sequencing needs that no earlier problem did,
is **comparing** two numbers rather than adding them: a job is late when its
deadline is smaller than its completion time, and the schedule is good when
the bound is not smaller than the penalty total. Both are written by the
highest differing position (`DescriptiveComplexity.binNum_lt_iff`), the deadline and
the bound being read on the wide positions through their lowest block
(`DescriptiveComplexity.binNum_wide_bot`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-! ### The existential block -/

/-- The relation variables of the certificate: the schedule, the late jobs,
and the running totals and carries of the two walks. -/
inductive JIdx : Type
  /-- The schedule. -/
  | sched
  /-- The jobs that miss their deadline. -/
  | late
  /-- The running total of the walk `s`. -/
  | ps (s : Bool)
  /-- The carries of the walk `s`. -/
  | cy (s : Bool)
  deriving DecidableEq

instance : Fintype JIdx where
  elems := {JIdx.sched, JIdx.late, JIdx.ps true, JIdx.ps false, JIdx.cy true, JIdx.cy false}
  complete := by
    intro t
    cases t with
    | sched => decide
    | late => decide
    | ps s => cases s <;> decide
    | cy s => cases s <;> decide

/-- The single existential block of the `Σ₁` definition of job sequencing: the
schedule (binary), the late jobs (unary), and, for each walk, the running
totals and the carries (ternary: a job and a wide position, itself a pair). -/
def jobSeqGuessBlock : SOBlock where
  ι := JIdx
  arity := fun i => match i with
    | .sched => 2
    | .late => 1
    | .ps _ => 3
    | .cy _ => 3

/-- The symbol of the schedule relation variable. -/
def jqSchedRel : jobSeqGuessBlock.lang.Relations 2 := ⟨.sched, rfl⟩

/-- The symbol of the late-jobs relation variable. -/
def jqLateRel : jobSeqGuessBlock.lang.Relations 1 := ⟨.late, rfl⟩

/-- The symbol of the running total of the walk `s`. -/
def jqPSRel (s : Bool) : jobSeqGuessBlock.lang.Relations 3 := ⟨.ps s, rfl⟩

/-- The symbol of the carries of the walk `s`. -/
def jqCyRel (s : Bool) : jobSeqGuessBlock.lang.Relations 3 := ⟨.cy s, rfl⟩

/-- The vocabulary of the kernel. -/
abbrev jqSOLang : Language := Language.jobSeq.sum jobSeqGuessBlock.lang

/-- The job symbol in the kernel's vocabulary. -/
abbrev jqJobSym : jqSOLang.Relations 1 := Sum.inl jsJob

/-- The position symbol in the kernel's vocabulary. -/
abbrev jqPosnSym : jqSOLang.Relations 1 := Sum.inl jsPosn

/-- The execution-time symbol in the kernel's vocabulary. -/
abbrev jqTimeSym : jqSOLang.Relations 2 := Sum.inl jsTime

/-- The deadline symbol in the kernel's vocabulary. -/
abbrev jqDlineSym : jqSOLang.Relations 2 := Sum.inl jsDline

/-- The penalty symbol in the kernel's vocabulary. -/
abbrev jqPenSym : jqSOLang.Relations 2 := Sum.inl jsPen

/-- The bound symbol in the kernel's vocabulary. -/
abbrev jqBndSym : jqSOLang.Relations 1 := Sum.inl jsBnd

/-- The order symbol in the kernel's vocabulary. -/
abbrev jqLeSym : jqSOLang.Relations 2 := Sum.inl jsLe

/-- The schedule symbol in the kernel's vocabulary. -/
abbrev jqSchedSym : jqSOLang.Relations 2 := Sum.inr jqSchedRel

/-- The late-jobs symbol in the kernel's vocabulary. -/
abbrev jqLateSym : jqSOLang.Relations 1 := Sum.inr jqLateRel

/-- The running-total symbol of the walk `s` in the kernel's vocabulary. -/
abbrev jqPSSym (s : Bool) : jqSOLang.Relations 3 := Sum.inr (jqPSRel s)

/-- The carry symbol of the walk `s` in the kernel's vocabulary. -/
abbrev jqCySym (s : Bool) : jqSOLang.Relations 3 := Sum.inr (jqCyRel s)

/-! ### Formula builders -/

section Builders

variable {α : Type}

/-- `x` is a job, as a formula. -/
def jqJobF (x : α) : jqSOLang.Formula α := Relations.formula₁ jqJobSym (Term.var x)

/-- `x` is a bit position, as a formula. -/
def jqPosnF (x : α) : jqSOLang.Formula α := Relations.formula₁ jqPosnSym (Term.var x)

/-- The execution time of `j` has bit 1 at `p`, as a formula. -/
def jqTimeF (j p : α) : jqSOLang.Formula α :=
  Relations.formula₂ jqTimeSym (Term.var j) (Term.var p)

/-- The deadline of `j` has bit 1 at `p`, as a formula. -/
def jqDlineF (j p : α) : jqSOLang.Formula α :=
  Relations.formula₂ jqDlineSym (Term.var j) (Term.var p)

/-- The penalty of `j` has bit 1 at `p`, as a formula. -/
def jqPenF (j p : α) : jqSOLang.Formula α :=
  Relations.formula₂ jqPenSym (Term.var j) (Term.var p)

/-- The bound has bit 1 at `p`, as a formula. -/
def jqBndF (p : α) : jqSOLang.Formula α := Relations.formula₁ jqBndSym (Term.var p)

/-- `x ≤ y`, as a formula. -/
def jqLeF (x y : α) : jqSOLang.Formula α :=
  Relations.formula₂ jqLeSym (Term.var x) (Term.var y)

/-- `x = y`, as a formula. -/
def jqEqF (x y : α) : jqSOLang.Formula α := Term.equal (Term.var x) (Term.var y)

/-- `x` is scheduled at or before `y`, as a formula. -/
def jqSchedF (x y : α) : jqSOLang.Formula α :=
  Relations.formula₂ jqSchedSym (Term.var x) (Term.var y)

/-- `x` is late, as a formula. -/
def jqLateF (x : α) : jqSOLang.Formula α := Relations.formula₁ jqLateSym (Term.var x)

/-- Bit `(x, p)` of the running total of the walk `s` at `i`, as a formula. -/
def jqPSF (s : Bool) (i x p : α) : jqSOLang.Formula α :=
  (jqPSSym s).formula ![Term.var i, Term.var x, Term.var p]

/-- The carry at `(x, p)` of the step appending `i` to the walk `s`, as a
formula. -/
def jqCyF (s : Bool) (i x p : α) : jqSOLang.Formula α :=
  (jqCySym s).formula ![Term.var i, Term.var x, Term.var p]

/-- The order the walk `s` follows: the schedule for the completion times, the
instance's own order for the penalties. -/
def jqOrdF (s : Bool) (x y : α) : jqSOLang.Formula α :=
  match s with
  | true => jqSchedF x y
  | false => jqLeF x y

/-- The jobs the walk `s` adds up: all of them for the completion times, the
late ones for the penalties. -/
def jqSelF (s : Bool) (i : α) : jqSOLang.Formula α :=
  match s with
  | true => jqJobF i
  | false => jqLateF i

/-- The number the walk `s` adds: the execution time, or the penalty. -/
def jqWtF (s : Bool) (i p : α) : jqSOLang.Formula α :=
  match s with
  | true => jqTimeF i p
  | false => jqPenF i p

/-- `x` is a minimum of the order, as a formula. -/
noncomputable def jqBotF (x : α) : jqSOLang.Formula α :=
  Formula.iAlls Unit (jqLeF (Sum.inl x) (Sum.inr ()))

/-- `x` is a maximum of the order, as a formula. -/
noncomputable def jqTopF (x : α) : jqSOLang.Formula α :=
  Formula.iAlls Unit (jqLeF (Sum.inr ()) (Sum.inl x))

/-- The bit the job `i` contributes to the walk `s` at the wide position
`(x, p)`: its number's bit, in the lowest block, if the walk adds it up. -/
noncomputable def jqAddF (s : Bool) (i x p : α) : jqSOLang.Formula α :=
  jqSelF s i ⊓ (jqBotF x ⊓ jqWtF s i p)

/-- Bit `(x, p)` of the deadline of `j`, read on the wide positions. -/
noncomputable def jqDlineWF (j x p : α) : jqSOLang.Formula α := jqBotF x ⊓ jqDlineF j p

/-- Bit `(x, p)` of the bound, read on the wide positions. -/
noncomputable def jqBndWF (x p : α) : jqSOLang.Formula α := jqBotF x ⊓ jqBndF p

/-- The exclusive or of three formulas, as `x ↔ (y ↔ z)`. -/
def jqXor3F (x y z : jqSOLang.Formula α) : jqSOLang.Formula α := x.iff (y.iff z)

/-- The majority of three formulas. -/
def jqMaj3F (x y z : jqSOLang.Formula α) : jqSOLang.Formula α :=
  (x ⊓ y) ⊔ ((x ⊓ z) ⊔ (y ⊓ z))

/-- `i` is the first job of the walk `s`, as a formula. -/
noncomputable def jqMinItemF (s : Bool) (i : α) : jqSOLang.Formula α :=
  jqJobF i ⊓ Formula.iAlls Unit
    ((jqJobF (Sum.inr ())).imp (jqOrdF s (Sum.inl i) (Sum.inr ())))

/-- `i` is the last job of the walk `s`, as a formula. -/
noncomputable def jqMaxItemF (s : Bool) (i : α) : jqSOLang.Formula α :=
  jqJobF i ⊓ Formula.iAlls Unit
    ((jqJobF (Sum.inr ())).imp (jqOrdF s (Sum.inr ()) (Sum.inl i)))

/-- `j` is the job right after `i` in the walk `s`, as a formula. -/
noncomputable def jqSuccItemF (s : Bool) (i j : α) : jqSOLang.Formula α :=
  jqJobF i ⊓ (jqJobF j ⊓ (jqOrdF s i j ⊓ (∼(jqEqF i j) ⊓
    Formula.iAlls Unit
      ((jqJobF (Sum.inr ())).imp ((jqOrdF s (Sum.inl i) (Sum.inr ())).imp
        ((jqOrdF s (Sum.inr ()) (Sum.inl j)).imp
          (jqEqF (Sum.inr ()) (Sum.inl i) ⊔ jqEqF (Sum.inr ()) (Sum.inl j))))))))

/-- `p` is the lowest position, as a formula. -/
noncomputable def jqMinPosnF (p : α) : jqSOLang.Formula α :=
  jqPosnF p ⊓ Formula.iAlls Unit
    ((jqPosnF (Sum.inr ())).imp (jqLeF (Sum.inl p) (Sum.inr ())))

/-- `p` is the highest position, as a formula. -/
noncomputable def jqMaxPosnF (p : α) : jqSOLang.Formula α :=
  jqPosnF p ⊓ Formula.iAlls Unit
    ((jqPosnF (Sum.inr ())).imp (jqLeF (Sum.inr ()) (Sum.inl p)))

/-- `q` is the position right above `p`, as a formula. -/
noncomputable def jqSuccPosnF (p q : α) : jqSOLang.Formula α :=
  jqPosnF p ⊓ (jqPosnF q ⊓ (jqLeF p q ⊓ (∼(jqEqF p q) ⊓
    Formula.iAlls Unit
      ((jqPosnF (Sum.inr ())).imp ((jqLeF (Sum.inl p) (Sum.inr ())).imp
        ((jqLeF (Sum.inr ()) (Sum.inl q)).imp
          (jqEqF (Sum.inr ()) (Sum.inl p) ⊔ jqEqF (Sum.inr ()) (Sum.inl q))))))))

/-- `y` is the element right after `x` in the whole universe, as a formula. -/
noncomputable def jqSuccAllF (x y : α) : jqSOLang.Formula α :=
  jqLeF x y ⊓ (∼(jqEqF x y) ⊓
    Formula.iAlls Unit
      ((jqLeF (Sum.inl x) (Sum.inr ())).imp
        ((jqLeF (Sum.inr ()) (Sum.inl y)).imp
          (jqEqF (Sum.inr ()) (Sum.inl x) ⊔ jqEqF (Sum.inr ()) (Sum.inl y)))))

/-- `(x, p)` is the lowest wide position, as a formula. -/
noncomputable def jqMinWideF (x p : α) : jqSOLang.Formula α := jqBotF x ⊓ jqMinPosnF p

/-- `(x, p)` is the highest wide position, as a formula. -/
noncomputable def jqMaxWideF (x p : α) : jqSOLang.Formula α := jqTopF x ⊓ jqMaxPosnF p

/-- `(y, q)` is the wide position right above `(x, p)`, as a formula. -/
noncomputable def jqSuccWideF (x p y q : α) : jqSOLang.Formula α :=
  (jqEqF x y ⊓ jqSuccPosnF p q) ⊔ (jqSuccAllF x y ⊓ (jqMaxPosnF p ⊓ jqMinPosnF q))

/-- `(x, p) ≤ (y, q)` on the wide positions, as a formula. -/
def jqWideLeF (x p y q : α) : jqSOLang.Formula α :=
  (jqLeF x y ⊓ ∼(jqEqF x y)) ⊔ (jqEqF x y ⊓ jqLeF p q)

/-- `(y, q) ≠ (x, p)` on the wide positions, as a formula. -/
def jqWideNeF (x p y q : α) : jqSOLang.Formula α := ∼(jqEqF y x) ⊔ ∼(jqEqF q p)

end Builders

/-! ### The clauses -/

/-- Kernel clause: the order is reflexive. -/
noncomputable def jqReflClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 1) (jqLeF (Sum.inr 0) (Sum.inr 0))

/-- Kernel clause: the order is transitive. -/
noncomputable def jqTransClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((jqLeF (Sum.inr 0) (Sum.inr 1) ⊓ jqLeF (Sum.inr 1) (Sum.inr 2)).imp
      (jqLeF (Sum.inr 0) (Sum.inr 2)))

/-- Kernel clause: the order is antisymmetric. -/
noncomputable def jqAntisymmClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    ((jqLeF (Sum.inr 0) (Sum.inr 1) ⊓ jqLeF (Sum.inr 1) (Sum.inr 0)).imp
      (jqEqF (Sum.inr 0) (Sum.inr 1)))

/-- Kernel clause: the order is total. -/
noncomputable def jqTotalClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 2) (jqLeF (Sum.inr 0) (Sum.inr 1) ⊔ jqLeF (Sum.inr 1) (Sum.inr 0))

/-- Kernel clause: the schedule is reflexive. -/
noncomputable def jqSchedReflClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 1) (jqSchedF (Sum.inr 0) (Sum.inr 0))

/-- Kernel clause: the schedule is transitive. -/
noncomputable def jqSchedTransClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((jqSchedF (Sum.inr 0) (Sum.inr 1) ⊓ jqSchedF (Sum.inr 1) (Sum.inr 2)).imp
      (jqSchedF (Sum.inr 0) (Sum.inr 2)))

/-- Kernel clause: the schedule is antisymmetric. -/
noncomputable def jqSchedAntisymmClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    ((jqSchedF (Sum.inr 0) (Sum.inr 1) ⊓ jqSchedF (Sum.inr 1) (Sum.inr 0)).imp
      (jqEqF (Sum.inr 0) (Sum.inr 1)))

/-- Kernel clause: the schedule is total. -/
noncomputable def jqSchedTotalClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    (jqSchedF (Sum.inr 0) (Sum.inr 1) ⊔ jqSchedF (Sum.inr 1) (Sum.inr 0))

/-- Kernel clause: only jobs are late. -/
noncomputable def jqLateJobClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 1) ((jqLateF (Sum.inr 0)).imp (jqJobF (Sum.inr 0)))

/-- Kernel clause: at the first job of the walk `s` the running total is that
job's contribution. -/
noncomputable def jqBaseClause (s : Bool) : jqSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((jqMinItemF s (Sum.inr 0) ⊓ jqPosnF (Sum.inr 2)).imp
      ((jqPSF s (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).iff
        (jqAddF s (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))))

/-- Kernel clause: each step of the walk `s` adds a bit. -/
noncomputable def jqSumClause (s : Bool) : jqSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((jqSuccItemF s (Sum.inr 0) (Sum.inr 1) ⊓ jqPosnF (Sum.inr 3)).imp
      ((jqPSF s (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)).iff
        (jqXor3F (jqPSF s (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
          (jqAddF s (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
          (jqCyF s (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)))))

/-- Kernel clause: each step of the walk `s` propagates its carry. -/
noncomputable def jqCarryClause (s : Bool) : jqSOLang.Sentence :=
  Formula.iAlls (Fin 6)
    ((jqSuccItemF s (Sum.inr 0) (Sum.inr 1) ⊓
        jqSuccWideF (Sum.inr 2) (Sum.inr 3) (Sum.inr 4) (Sum.inr 5)).imp
      ((jqCyF s (Sum.inr 1) (Sum.inr 4) (Sum.inr 5)).iff
        (jqMaj3F (jqPSF s (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
          (jqAddF s (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
          (jqCyF s (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)))))

/-- Kernel clause: nothing is carried into the lowest wide position. -/
noncomputable def jqBottomClause (s : Bool) : jqSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((jqSuccItemF s (Sum.inr 0) (Sum.inr 1) ⊓ jqMinWideF (Sum.inr 2) (Sum.inr 3)).imp
      ∼(jqCyF s (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)))

/-- Kernel clause: nothing is carried out of the highest wide position. -/
noncomputable def jqTopClause (s : Bool) : jqSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((jqSuccItemF s (Sum.inr 0) (Sum.inr 1) ⊓ jqMaxWideF (Sum.inr 2) (Sum.inr 3)).imp
      ∼(jqMaj3F (jqPSF s (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
        (jqAddF s (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
        (jqCyF s (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))))

/-- The clauses of one walk. -/
noncomputable def jqWalkClauses (s : Bool) : jqSOLang.Sentence :=
  jqBaseClause s ⊓ (jqSumClause s ⊓ (jqCarryClause s ⊓
    (jqBottomClause s ⊓ jqTopClause s)))

/-- Kernel clause: a job is late exactly when its deadline is smaller than its
completion time, compared at the highest wide position where the two differ. -/
noncomputable def jqLateDefClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((jqJobF (Sum.inr 0)).imp
      ((jqLateF (Sum.inr 0)).iff
        (Formula.iExs (Fin 2)
          (jqPosnF (Sum.inr 1) ⊓
            (∼(jqDlineWF (Sum.inl (Sum.inr 0)) (Sum.inr 0) (Sum.inr 1)) ⊓
              (jqPSF true (Sum.inl (Sum.inr 0)) (Sum.inr 0) (Sum.inr 1) ⊓
                Formula.iAlls (Fin 2)
                  ((jqPosnF (Sum.inr 1) ⊓
                      (jqWideLeF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1))
                          (Sum.inr 0) (Sum.inr 1) ⊓
                        jqWideNeF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1))
                          (Sum.inr 0) (Sum.inr 1))).imp
                    ((jqDlineWF (Sum.inl (Sum.inl (Sum.inr 0))) (Sum.inr 0)
                        (Sum.inr 1)).iff
                      (jqPSF true (Sum.inl (Sum.inl (Sum.inr 0))) (Sum.inr 0)
                        (Sum.inr 1))))))))))

/-- Kernel clause: the penalty total the second walk ends on does not exceed
the bound – there is no wide position carrying the total's bit above which the
two agree. -/
noncomputable def jqFinalClause : jqSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((jqMaxItemF false (Sum.inr 0)).imp
      ∼(Formula.iExs (Fin 2)
        (jqPosnF (Sum.inr 1) ⊓
          (∼(jqBndWF (Sum.inr 0) (Sum.inr 1)) ⊓
            (jqPSF false (Sum.inl (Sum.inr 0)) (Sum.inr 0) (Sum.inr 1) ⊓
              Formula.iAlls (Fin 2)
                ((jqPosnF (Sum.inr 1) ⊓
                    (jqWideLeF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1))
                        (Sum.inr 0) (Sum.inr 1) ⊓
                      jqWideNeF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1))
                        (Sum.inr 0) (Sum.inr 1))).imp
                  ((jqBndWF (Sum.inr 0) (Sum.inr 1)).iff
                    (jqPSF false (Sum.inl (Sum.inl (Sum.inr 0))) (Sum.inr 0)
                      (Sum.inr 1)))))))))

/-- The first-order kernel of the `Σ₁` definition of job sequencing. -/
noncomputable def jobSequencingKernel : jqSOLang.Sentence :=
  ((jqReflClause ⊓ (jqTransClause ⊓ (jqAntisymmClause ⊓ jqTotalClause))) ⊓
    (jqSchedReflClause ⊓ (jqSchedTransClause ⊓
      (jqSchedAntisymmClause ⊓ jqSchedTotalClause)))) ⊓
    (jqLateJobClause ⊓ (jqWalkClauses true ⊓ (jqWalkClauses false ⊓
      (jqLateDefClause ⊓ jqFinalClause))))

/-! ### Reading an assignment

What the guessed relations mean, and what the numbers the kernel talks about
decode to. Everything the walks carry lives on the wide positions, so each
number of the instance appears there through its lowest block – named by
minimality, since that is all a formula can say, which is why the predicates
below quantify over `Unit → A` the way the kernel's `∀` produces. -/

section Reading

variable {A : Type} [Language.jobSeq.Structure A]

/-- A number of the instance, read on the wide positions: its own bits, in the
lowest block. -/
def JWide (b : A → Prop) (u : A × A) : Prop := (∀ y : Unit → A, JSLe u.1 (y ())) ∧ b u.2

theorem jWide_iff {b : A → Prop} {u : A × A} :
    JWide b u ↔ ((∀ y : A, JSLe u.1 y) ∧ b u.2) :=
  and_congr ⟨fun h y => h fun _ => y, fun h y => h (y ())⟩ Iff.rfl

/-- **Read on the wide positions, a number still has its value.** -/
theorem binNum_jWide [Finite A] (hlin : IsLinOrd (JSLe (A := A))) {a₀ : A}
    (h₀ : ∀ y : A, JSLe a₀ y) (b : A → Prop) :
    binNum (wideLe JSLe) (WidePosn JSPosn) (JWide b) = binNum JSLe JSPosn b := by
  rw [show binNum (wideLe JSLe) (WidePosn JSPosn) (JWide b) =
    binNum (wideLe JSLe) (WidePosn JSPosn) (fun u => (∀ y : A, JSLe u.1 y) ∧ b u.2) from
    binNum_congr fun _ => jWide_iff]
  exact binNum_wide_bot hlin h₀ b

/-- The bits the walk `s` adds up: the execution times, or the penalties. -/
def JBit (s : Bool) (i p : A) : Prop :=
  match s with
  | true => JSTime i p
  | false => JSPen i p

/-- The number the walk `s` adds up: the execution time, or the penalty. -/
noncomputable def JVal (s : Bool) (i : A) : ℕ :=
  match s with
  | true => JSTimeVal i
  | false => JSPenVal i

/-- The bit the walk `s` reads at a wide position. -/
def JWt (s : Bool) (i : A) : A × A → Prop := JWide (JBit s i)

/-- The deadline of a job, read on the wide positions. -/
def JDlineW (j : A) : A × A → Prop := JWide (JSDline j)

/-- The bound, read on the wide positions. -/
def JBndW : A × A → Prop := JWide (JSBnd (A := A))

theorem binNum_jWt [Finite A] (hlin : IsLinOrd (JSLe (A := A))) {a₀ : A}
    (h₀ : ∀ y : A, JSLe a₀ y) (s : Bool) (i : A) :
    binNum (wideLe JSLe) (WidePosn JSPosn) (JWt s i) = JVal s i := by
  rw [JWt, binNum_jWide hlin h₀]
  cases s <;> rfl

theorem binNum_jDlineW [Finite A] (hlin : IsLinOrd (JSLe (A := A))) {a₀ : A}
    (h₀ : ∀ y : A, JSLe a₀ y) (j : A) :
    binNum (wideLe JSLe) (WidePosn JSPosn) (JDlineW j) = JSDlineVal j :=
  binNum_jWide hlin h₀ (JSDline j)

theorem binNum_jBndW [Finite A] (hlin : IsLinOrd (JSLe (A := A))) {a₀ : A}
    (h₀ : ∀ y : A, JSLe a₀ y) :
    binNum (wideLe JSLe) (WidePosn JSPosn) (JBndW (A := A)) = JSBound A :=
  binNum_jWide hlin h₀ JSBnd

variable (ρ : jobSeqGuessBlock.Assignment A)

/-- The schedule, read off an assignment of the block. -/
def JSched (a b : A) : Prop := ρ .sched ![a, b]

/-- The late jobs, read off an assignment of the block. -/
def JLate (j : A) : Prop := ρ .late ![j]

/-- The running total of the walk `s`, read off an assignment of the block. -/
def JPS (s : Bool) (i : A) (u : A × A) : Prop := ρ (.ps s) ![i, u.1, u.2]

/-- The carries of the walk `s`, read off an assignment of the block. -/
def JCy (s : Bool) (i : A) (u : A × A) : Prop := ρ (.cy s) ![i, u.1, u.2]

/-- The order the walk `s` follows: the guessed schedule for the completion
times, the instance's own order for the penalties. -/
def JOrd (s : Bool) : A → A → Prop :=
  match s with
  | true => JSched ρ
  | false => JSLe

/-- The jobs the walk `s` adds up: all of them for the completion times, the
late ones for the penalties. -/
def JSel (s : Bool) : A → Prop :=
  match s with
  | true => JSJob
  | false => JLate ρ

end Reading

end SigmaOne

end DescriptiveComplexity
