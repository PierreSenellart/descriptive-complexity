/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Hierarchy
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax564036.QuantifiedBooleanFormulas
end Lax564036.QuantifiedBooleanFormulas

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.QuantifiedBooleanFormulas (CnfSat CnfSatWith DnfSat QbfMatrix altQuant qbfVal)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax564036.QuantifiedBooleanFormulas (instIsRelationalQbf qbf qbfBlock qbfIsClause qbfNegIn qbfPosIn qbfRel)
end FirstOrder.Language

/-!
# QBF: quantified Boolean formulas with bounded alternation

The problems `QBF k` – quantified Boolean formulas with `k` alternating
blocks of propositional quantifiers – as decision problems on first-order
structures. The vocabulary `FirstOrder.Language.qbf k` is that of SAT
(`FirstOrder.Language.sat`: clauses, positive and negative occurrences)
together with `k` unary *block marks* `qbfBlock i` splitting the
propositional variables into the `k` quantifier blocks.

The semantics is the alternating quantification `DescriptiveComplexity.altQuant`: block
`0` is quantified outermost, block `k - 1` innermost, and the polarities
alternate starting from `start`. Each quantifier picks a truth assignment for
its own block; the combined truth value of a variable
(`DescriptiveComplexity.qbfVal`) is given by the assignment of a block that marks it.

The innermost quantifier-free *matrix* comes in two shapes, selected by a
Boolean parameter:

* `DescriptiveComplexity.CnfSat` – conjunctive: every clause contains a true literal;
* `DescriptiveComplexity.DnfSat` – disjunctive: some term has all its literals true.

Both shapes are needed. The hardness proof
(`DescriptiveComplexity.Problems.Qbf.Hardness`) encodes the first-order kernel of a
second-order definition by a Tseitin translation
([Tseitin 1968][tseitin1968complexity]), which introduces auxiliary *gate*
variables; these are functionally determined by the block variables, so they
can be absorbed into the innermost quantifier only when that quantifier is
existential. For a prefix starting existentially the innermost quantifier is
existential exactly when `k` is odd, which is why
`DescriptiveComplexity.QBF` takes a conjunctive matrix for odd `k` and a disjunctive one
for even `k` – the standard form of the `Σₖᵖ`-complete quantified Boolean
formula problems ([Stockmeyer 1976][stockmeyer1976polynomial]; [Wrathall
1976][wrathall1976complete]).
-/

namespace FirstOrder

namespace Language

variable {k : ℕ}

end Language

end FirstOrder

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Alternating quantification over truth assignments -/

/-- Alternating quantification only depends on the quantified predicate up to
pointwise equivalence. -/
theorem altQuant_congr {A : Type} :
    ∀ (k : ℕ) (P Q : (Fin k → A → Prop) → Prop), (∀ νs, P νs ↔ Q νs) →
      ∀ pol : Bool, Lax564036.QuantifiedBooleanFormulas.altQuant A k P pol ↔ Lax564036.QuantifiedBooleanFormulas.altQuant A k Q pol := by
  intro k
  induction k with
  | zero => intro P Q h pol; exact h _
  | succ k ih =>
    intro P Q h pol
    cases pol with
    | true => exact exists_congr fun ν => ih _ _ (fun νs => h _) false
    | false => exact forall_congr' fun ν => ih _ _ (fun νs => h _) true

/-- Transport of alternating quantification along an equivalence of
universes: quantifying over assignments on `B` and reading them back through
`e` is quantifying over assignments on `A`. -/
theorem altQuant_equiv {A B : Type} (e : A ≃ B) :
    ∀ (k : ℕ) (P : (Fin k → A → Prop) → Prop) (pol : Bool),
      Lax564036.QuantifiedBooleanFormulas.altQuant B k (fun νs => P fun i a => νs i (e a)) pol ↔ Lax564036.QuantifiedBooleanFormulas.altQuant A k P pol := by
  intro k
  induction k with
  | zero =>
    intro P pol
    exact iff_of_eq (congrArg P (funext fun i => i.elim0))
  | succ k ih =>
    intro P pol
    have key : ∀ (ν : B → Prop) (νs : Fin k → B → Prop),
        (fun (i : Fin (k + 1)) (a : A) => (Fin.cons ν νs : Fin (k + 1) → B → Prop) i (e a)) =
          Fin.cons (fun a => ν (e a)) fun i a => νs i (e a) := by
      intro ν νs
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    have key' : ∀ (ν : A → Prop) (νs : Fin k → B → Prop),
        (fun (i : Fin (k + 1)) (a : A) =>
            (Fin.cons (fun b => ν (e.symm b)) νs : Fin (k + 1) → B → Prop) i (e a)) =
          Fin.cons ν fun i a => νs i (e a) := by
      intro ν νs
      refine (key _ νs).trans (congrArg₂ Fin.cons (funext fun a => ?_) rfl)
      exact congrArg ν (e.symm_apply_apply a)
    cases pol with
    | true =>
      constructor
      · rintro ⟨ν, hν⟩
        refine ⟨fun a => ν (e a), (ih (fun νs => P (Fin.cons (fun a => ν (e a)) νs)) false).mp ?_⟩
        refine (altQuant_congr k _ _ (fun νs => ?_) false).mp hν
        exact iff_of_eq (congrArg P (key ν νs))
      · rintro ⟨ν, hν⟩
        refine ⟨fun b => ν (e.symm b), ?_⟩
        refine (altQuant_congr k _ _ (fun νs => ?_) false).mpr
          ((ih (fun νs => P (Fin.cons ν νs)) false).mpr hν)
        exact iff_of_eq (congrArg P (key' ν νs))
    | false =>
      constructor
      · intro h ν
        refine (ih (fun νs => P (Fin.cons ν νs)) true).mp ?_
        refine (altQuant_congr k _ _ (fun νs => ?_) true).mp (h fun b => ν (e.symm b))
        exact iff_of_eq (congrArg P (key' ν νs))
      · intro h ν
        refine (altQuant_congr k _ _ (fun νs => ?_) true).mpr
          ((ih (fun νs => P (Fin.cons (fun a => ν (e a)) νs)) true).mpr (h _))
        exact iff_of_eq (congrArg P (key ν νs))

/-! ### The matrix of a quantified Boolean formula -/

section Matrix

variable {k : ℕ} {A : Type} [(Lax564036.QuantifiedBooleanFormulas.qbf k).Structure A]

/-- **Propositional duality**: the disjunctive matrix is the negation of the
conjunctive one with the sign of every literal swapped. This is what lets a
single Tseitin translation serve both parities of `k`: at even `k` the
innermost quantifier is universal, and it absorbs the gate variables through
this negation. -/
theorem dnfSat_iff_not_cnfSatWith_true (νs : Fin k → A → Prop) :
    Lax564036.QuantifiedBooleanFormulas.DnfSat νs ↔ ¬Lax564036.QuantifiedBooleanFormulas.CnfSatWith true νs := by
  constructor
  · rintro ⟨c, hc, h⟩ hcnf
    obtain ⟨x, hx⟩ := hcnf c hc
    rcases hx with ⟨hneg, hval⟩ | ⟨hpos, hval⟩
    · exact (h x).2 hneg hval
    · exact hval ((h x).1 hpos)
  · intro h
    by_contra hd
    refine h fun c hc => ?_
    have hnc : ¬∀ x : A, (RelMap (Lax564036.QuantifiedBooleanFormulas.qbfPosIn (k := k)) ![c, x] → Lax564036.QuantifiedBooleanFormulas.qbfVal νs x) ∧
        (RelMap (Lax564036.QuantifiedBooleanFormulas.qbfNegIn (k := k)) ![c, x] → ¬Lax564036.QuantifiedBooleanFormulas.qbfVal νs x) := fun hall => hd ⟨c, hc, hall⟩
    obtain ⟨x, hx⟩ := not_forall.mp hnc
    rcases Classical.em (RelMap (Lax564036.QuantifiedBooleanFormulas.qbfPosIn (k := k)) ![c, x] ∧ ¬Lax564036.QuantifiedBooleanFormulas.qbfVal νs x) with hp | hp
    · exact ⟨x, Or.inr hp⟩
    · have h1 : RelMap (Lax564036.QuantifiedBooleanFormulas.qbfPosIn (k := k)) ![c, x] → Lax564036.QuantifiedBooleanFormulas.qbfVal νs x := fun hpos =>
        Classical.byContradiction fun hv => hp ⟨hpos, hv⟩
      have h2 : ¬(RelMap (Lax564036.QuantifiedBooleanFormulas.qbfNegIn (k := k)) ![c, x] → ¬Lax564036.QuantifiedBooleanFormulas.qbfVal νs x) := fun h2' => hx ⟨h1, h2'⟩
      rcases Classical.em (RelMap (Lax564036.QuantifiedBooleanFormulas.qbfNegIn (k := k)) ![c, x]) with hn | hn
      · exact ⟨x, Or.inl ⟨hn, Classical.byContradiction fun hv => h2 fun _ => hv⟩⟩
      · exact absurd (fun hn' => absurd hn' hn) h2

/-- Optional negation, indexed by a Boolean. -/
def xorP (b : Bool) (P : Prop) : Prop :=
  match b with
  | true => ¬P
  | false => P

theorem xorP_congr (b : Bool) {P Q : Prop} (h : P ↔ Q) : xorP b P ↔ xorP b Q := by
  cases b
  · exact h
  · exact not_congr h

/-- **The two matrix shapes, uniformly**: whichever matrix `QBF` uses at a
given parity is the conjunctive one with the corresponding sign swap, negated
exactly when the swap happens. This is what lets the hardness proof treat both
parities at once. -/
theorem qbfMatrix_eq_xorP (sw : Bool) (νs : Fin k → A → Prop) :
    Lax564036.QuantifiedBooleanFormulas.QbfMatrix (!sw) νs ↔ xorP sw (Lax564036.QuantifiedBooleanFormulas.CnfSatWith sw νs) := by
  cases sw
  · exact Iff.rfl
  · exact dnfSat_iff_not_cnfSatWith_true νs

end Matrix

/-! ### Isomorphism-invariance -/

section Iso

variable {k : ℕ} {A B : Type} [(Lax564036.QuantifiedBooleanFormulas.qbf k).Structure A] [(Lax564036.QuantifiedBooleanFormulas.qbf k).Structure B]

/-- The truth value of a variable transports along an isomorphism. -/
private theorem qbfVal_equiv (e : A ≃[Lax564036.QuantifiedBooleanFormulas.qbf k] B) (νs : Fin k → B → Prop) (x : A) :
    Lax564036.QuantifiedBooleanFormulas.qbfVal (fun i a => νs i (e a)) x ↔ Lax564036.QuantifiedBooleanFormulas.qbfVal νs (e x) :=
  exists_congr fun i => and_congr_left' (relMap_equiv₁ e (Lax564036.QuantifiedBooleanFormulas.qbfBlock i) x)

private theorem cnfSatWith_equiv (swap : Bool) (e : A ≃[Lax564036.QuantifiedBooleanFormulas.qbf k] B)
    (νs : Fin k → B → Prop) :
    Lax564036.QuantifiedBooleanFormulas.CnfSatWith swap (fun i a => νs i (e a)) ↔ Lax564036.QuantifiedBooleanFormulas.CnfSatWith swap νs := by
  unfold Lax564036.QuantifiedBooleanFormulas.CnfSatWith
  constructor
  · intro h c hc
    obtain ⟨x, hx⟩ := h (e.symm c) ((relMap_equiv₁ e.symm (Lax564036.QuantifiedBooleanFormulas.qbfIsClause (k := k)) c).mp hc)
    refine ⟨e x, ?_⟩
    rcases hx with ⟨hp, hv⟩ | ⟨hn, hv⟩
    · refine Or.inl ⟨?_, (qbfVal_equiv e νs x).mp hv⟩
      simpa using (relMap_equiv₂ e _ (e.symm c) x).mp hp
    · refine Or.inr ⟨?_, fun hv' => hv ((qbfVal_equiv e νs x).mpr hv')⟩
      simpa using (relMap_equiv₂ e _ (e.symm c) x).mp hn
  · intro h c hc
    obtain ⟨x, hx⟩ := h (e c) ((relMap_equiv₁ e (Lax564036.QuantifiedBooleanFormulas.qbfIsClause (k := k)) c).mp hc)
    refine ⟨e.symm x, ?_⟩
    rcases hx with ⟨hp, hv⟩ | ⟨hn, hv⟩
    · refine Or.inl ⟨(relMap_equiv₂ e _ c (e.symm x)).mpr (by simpa using hp), ?_⟩
      exact (qbfVal_equiv e νs (e.symm x)).mpr (by simpa using hv)
    · refine Or.inr ⟨(relMap_equiv₂ e _ c (e.symm x)).mpr (by simpa using hn), ?_⟩
      exact fun hv' => hv (by simpa using (qbfVal_equiv e νs (e.symm x)).mp hv')

private theorem dnfSat_equiv (e : A ≃[Lax564036.QuantifiedBooleanFormulas.qbf k] B) (νs : Fin k → B → Prop) :
    Lax564036.QuantifiedBooleanFormulas.DnfSat (fun i a => νs i (e a)) ↔ Lax564036.QuantifiedBooleanFormulas.DnfSat νs := by
  unfold Lax564036.QuantifiedBooleanFormulas.DnfSat
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨e c, (relMap_equiv₁ e (Lax564036.QuantifiedBooleanFormulas.qbfIsClause (k := k)) c).mp hc, fun x => ?_⟩
    refine ⟨fun hp => ?_, fun hn hv => ?_⟩
    · have := (h (e.symm x)).1 ((relMap_equiv₂ e _ c (e.symm x)).mpr (by simpa using hp))
      simpa using (qbfVal_equiv e νs (e.symm x)).mp this
    · refine (h (e.symm x)).2 ((relMap_equiv₂ e _ c (e.symm x)).mpr (by simpa using hn)) ?_
      exact (qbfVal_equiv e νs (e.symm x)).mpr (by simpa using hv)
  · rintro ⟨c, hc, h⟩
    refine ⟨e.symm c, (relMap_equiv₁ e.symm (Lax564036.QuantifiedBooleanFormulas.qbfIsClause (k := k)) c).mp hc, fun x => ?_⟩
    refine ⟨fun hp => ?_, fun hn hv => ?_⟩
    · refine (qbfVal_equiv e νs x).mpr ((h (e x)).1 ?_)
      simpa using (relMap_equiv₂ e _ (e.symm c) x).mp hp
    · refine (h (e x)).2 ?_ ((qbfVal_equiv e νs x).mp hv)
      simpa using (relMap_equiv₂ e _ (e.symm c) x).mp hn

private theorem qbfMatrix_equiv (cnf : Bool) (e : A ≃[Lax564036.QuantifiedBooleanFormulas.qbf k] B)
    (νs : Fin k → B → Prop) :
    Lax564036.QuantifiedBooleanFormulas.QbfMatrix cnf (fun i a => νs i (e a)) ↔ Lax564036.QuantifiedBooleanFormulas.QbfMatrix cnf νs := by
  cases cnf
  · exact dnfSat_equiv e νs
  · exact cnfSatWith_equiv false e νs

end Iso

/-! ### The decision problems -/

/-- Quantified Boolean formulas with `k` alternating quantifier blocks: the
prefix starts with an existential block when `start` is `true`, and the matrix
is conjunctive when `cnf` is `true`. -/
def QbfProblem (k : ℕ) (start cnf : Bool) : Lax904597.Problems.DecisionProblem (Lax564036.QuantifiedBooleanFormulas.qbf k) where
  Holds := fun A inst => Lax564036.QuantifiedBooleanFormulas.altQuant A k (fun νs => @Lax564036.QuantifiedBooleanFormulas.QbfMatrix k A inst cnf νs) start
  iso_invariant := fun {_A _B} _ _ e =>
    ((altQuant_congr k _ _ (fun νs => (qbfMatrix_equiv cnf e νs).symm) start).trans
      (altQuant_equiv e.toEquiv k _ start)).symm

/-- **QBF with `k` alternating blocks**, the canonical `Σₖᵖ`-complete problem:
an existential outermost block, and a matrix whose shape follows the parity of
`k` – conjunctive when the innermost quantifier is existential (`k` odd),
disjunctive when it is universal (`k` even). See
`DescriptiveComplexity.Problems.Qbf` for the completeness theorem. -/
def QBF (k : ℕ) : Lax904597.Problems.DecisionProblem (Lax564036.QuantifiedBooleanFormulas.qbf k) :=
  QbfProblem k true (k % 2 == 1)

/-- The dual family, with a universal outermost block: the canonical
`Πₖᵖ`-complete problem. -/
def QBFPi (k : ℕ) : Lax904597.Problems.DecisionProblem (Lax564036.QuantifiedBooleanFormulas.qbf k) :=
  QbfProblem k false (k % 2 == 0)

end Lax564036Proofs.DescriptiveComplexity


