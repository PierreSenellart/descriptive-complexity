/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Vocabulary
import Lax822549Proofs.DescriptiveComplexity.PSpace
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.Qsat
end Lax134656.Qsat

namespace Lax822549Proofs.DescriptiveComplexity.QLeast
end Lax822549Proofs.DescriptiveComplexity.QLeast

namespace Lax904597.Problems
end Lax904597.Problems

namespace FirstOrder.Language
export Lax134656.Qsat (qsAllVar qsIsClause qsIsVar qsNegIn qsPosIn qsPrefixLt qsat)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.Qsat (IsQAll IsQVar QLeast QPrec QsatHolds QsatMatrix QsatWf QsatWins qAdd qUpd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# QSAT: quantified Boolean formulas with an unbounded prefix

The vocabulary and semantics of the canonical PSPACE-complete problem
(`DescriptiveComplexity.QSAT`, also known as TQBF or QBF): is a fully quantified
Boolean formula in prenex conjunctive normal form true? Unlike the bounded
families `DescriptiveComplexity.QBF k` of `DescriptiveComplexity.Problems.Qbf` – where the
number of alternations is fixed by the *problem* and only the matrix comes
with the instance – here the quantifier prefix is part of the instance, so a
single problem carries arbitrarily many alternations. That is exactly the step
from the polynomial hierarchy to PSPACE.

## The instance

An instance is a `FirstOrder.Language.qsat`-structure. As in
`FirstOrder.Language.sat`, its elements are propositional variables and clauses
at once, with

* `isVar x`: the element `x` is a quantified propositional variable;
* `allVar x`: the variable `x` is quantified universally (existentially
  otherwise);
* `prefixLt x y`: the variable `x` is quantified *outside* the variable `y`;
* `isClause c`, `posIn c x`, `negIn c x`: the clauses of the matrix and the
  literal occurrences, exactly as for SAT.

An instance is *well formed* (`DescriptiveComplexity.QsatWf`) when `prefixLt` is a
strict linear order on the marked variables; a malformed instance is a
no-instance. Well-formedness is a first-order condition, which is what lets the
membership proof check it inside the walk.

## The semantics

Reading a quantifier prefix means recursing along `prefixLt`, and the recursion
is over a set of *remaining* variables rather than over a syntactic list. It is
packaged as an inductive predicate `DescriptiveComplexity.QsatWins`: a *position* is a
pair `(D, τ)` of a set `D` of already-quantified variables and a valuation `τ`,
and `QsatWins D τ` says that the existential player wins the game that
quantifies the variables outside `D`, innermost-first, and ends in the matrix.
An inductive definition is used rather than a recursion so that the semantics
is available on an arbitrary (possibly infinite) structure, as
`DescriptiveComplexity.DecisionProblem` requires; on a finite well-formed structure it is
the usual game value, since the three rules are then mutually exclusive and
exhaustive (`DescriptiveComplexity.qsatWins_all_iff`,
`DescriptiveComplexity.qsatWins_ex_iff`, `DescriptiveComplexity.qsatWins_leaf_iff`, proved by
inversion alone).

The quantified variable at a position is the `prefixLt`-least one not yet in
`D` (`DescriptiveComplexity.QLeast`), so the prefix is read outermost-first and the
players move in the order the instance prescribes.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Reading an instance -/

section Reading

variable {A : Type} [Lax134656.Qsat.qsat.Structure A]

/-- The matrix only depends on the valuation through its values on the
quantified variables. -/
theorem qsatMatrix_congr {τ τ' : A → Prop} (h : ∀ y : A, Lax134656.Qsat.IsQVar y → (τ y ↔ τ' y))
    (hm : Lax134656.Qsat.QsatMatrix τ) : Lax134656.Qsat.QsatMatrix τ' := by
  intro c hc
  obtain ⟨x, hx, hlit⟩ := hm c hc
  refine ⟨x, hx, ?_⟩
  rcases hlit with ⟨hp, hv⟩ | ⟨hn, hv⟩
  · exact Or.inl ⟨hp, (h x hx).mp hv⟩
  · exact Or.inr ⟨hn, fun hv' => hv ((h x hx).mpr hv')⟩

omit [Lax134656.Qsat.qsat.Structure A] in
@[simp]
theorem qAdd_self (D : A → Prop) (x : A) : Lax134656.Qsat.qAdd D x x := Or.inl rfl

omit [Lax134656.Qsat.qsat.Structure A] in
@[simp]
theorem qUpd_self (τ : A → Prop) (x : A) (b : Bool) : Lax134656.Qsat.qUpd τ x b x ↔ b = true := by
  refine ⟨fun h => ?_, fun h => Or.inl ⟨rfl, h⟩⟩
  rcases h with ⟨-, hb⟩ | ⟨hne, -⟩
  · exact hb
  · exact absurd rfl hne

omit [Lax134656.Qsat.qsat.Structure A] in
theorem qUpd_ne (τ : A → Prop) {x y : A} (b : Bool) (h : y ≠ x) : Lax134656.Qsat.qUpd τ x b y ↔ τ y := by
  refine ⟨fun hy => ?_, fun hy => Or.inr ⟨h, hy⟩⟩
  rcases hy with ⟨he, -⟩ | ⟨-, hy⟩
  · exact absurd he h
  · exact hy

/-- The next variable to quantify is unique, by totality of the prefix
order. -/
theorem QLeast.unique (hwf : Lax134656.Qsat.QsatWf A) {D : A → Prop} {x y : A}
    (hx : Lax134656.Qsat.QLeast D x) (hy : Lax134656.Qsat.QLeast D y) : x = y := by
  by_contra hne
  rcases hwf.total x y hx.1 hy.1 hne with h | h
  · exact hy.2.2 x hx.1 hx.2.1 h
  · exact hx.2.2 y hy.1 hy.2.1 h

end Reading

end Lax822549Proofs.DescriptiveComplexity

namespace Lax134656.Qsat.QLeast

export Lax822549Proofs.DescriptiveComplexity.QLeast (unique)

end Lax134656.Qsat.QLeast

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Reading

variable {A : Type} [Lax134656.Qsat.qsat.Structure A]

end Reading

/-! ### The game

`QsatWins D τ` is the value of the position in which the variables of `D` have
already been given their values by `τ` and the remaining ones are still to be
quantified, innermost-first along the prefix order. -/

section Game

variable {A : Type} [Lax134656.Qsat.qsat.Structure A]

/-- **A position only depends on the values already given**: two valuations
agreeing on the quantified part `D` win the same positions. This is what makes
`(D, τ)` a position rather than a full state: the values of `τ` outside `D` are
about to be overwritten by the quantifiers. -/
theorem qsatWins_congr {D τ : A → Prop} (h : Lax134656.Qsat.QsatWins D τ) :
    ∀ τ' : A → Prop, (∀ y : A, D y → (τ y ↔ τ' y)) → Lax134656.Qsat.QsatWins D τ' := by
  classical
  induction h with
  | leaf hD hm => exact fun τ' hτ => .leaf hD (qsatMatrix_congr (fun y hy => hτ y (hD y hy)) hm)
  | @ex D τ x hx hq b _ ih =>
    refine fun τ' hτ => .ex hx hq b (ih _ fun y hy => ?_)
    by_cases hyx : y = x
    · subst hyx
      exact (qUpd_self τ y b).trans (qUpd_self τ' y b).symm
    · rw [qUpd_ne τ b hyx, qUpd_ne τ' b hyx]
      exact hτ y (hy.resolve_left hyx)
  | @all D τ x hx hq _ ih =>
    refine fun τ' hτ => .all hx hq fun b => (ih b _ fun y hy => ?_)
    by_cases hyx : y = x
    · subst hyx
      exact (qUpd_self τ y b).trans (qUpd_self τ' y b).symm
    · rw [qUpd_ne τ b hyx, qUpd_ne τ' b hyx]
      exact hτ y (hy.resolve_left hyx)

/-! #### The three rules read backwards

Together with `DescriptiveComplexity.QLeast.unique` the constructors are
mutually exclusive, so each of them is an equivalence: the inductive predicate
*is* the game value, and no induction is needed to see it. -/

/-- At a position where every variable is quantified, winning is satisfying the
matrix. -/
theorem qsatWins_leaf_iff {D τ : A → Prop} (hD : ∀ x : A, Lax134656.Qsat.IsQVar x → D x) :
    Lax134656.Qsat.QsatWins D τ ↔ Lax134656.Qsat.QsatMatrix τ := by
  refine ⟨fun h => ?_, fun h => .leaf hD h⟩
  cases h with
  | leaf _ hm => exact hm
  | ex hx _ _ _ => exact absurd (hD _ hx.1) hx.2.1
  | all hx _ _ => exact absurd (hD _ hx.1) hx.2.1

/-- At a position whose next variable is existential, winning is winning after
one of its two values. -/
theorem qsatWins_ex_iff (hwf : Lax134656.Qsat.QsatWf A) {D τ : A → Prop} {x : A} (hx : Lax134656.Qsat.QLeast D x)
    (hq : ¬Lax134656.Qsat.IsQAll x) :
    Lax134656.Qsat.QsatWins D τ ↔ ∃ b : Bool, Lax134656.Qsat.QsatWins (Lax134656.Qsat.qAdd D x) (Lax134656.Qsat.qUpd τ x b) := by
  refine ⟨fun h => ?_, fun ⟨b, hb⟩ => .ex hx hq b hb⟩
  cases h with
  | leaf hD _ => exact absurd (hD _ hx.1) hx.2.1
  | ex hy _ b hb => exact ⟨b, (hy.unique hwf hx) ▸ hb⟩
  | all hy hq' _ => exact absurd ((hy.unique hwf hx) ▸ hq') hq

/-- At a position whose next variable is universal, winning is winning after
both of its values. -/
theorem qsatWins_all_iff (hwf : Lax134656.Qsat.QsatWf A) {D τ : A → Prop} {x : A} (hx : Lax134656.Qsat.QLeast D x)
    (hq : Lax134656.Qsat.IsQAll x) :
    Lax134656.Qsat.QsatWins D τ ↔ ∀ b : Bool, Lax134656.Qsat.QsatWins (Lax134656.Qsat.qAdd D x) (Lax134656.Qsat.qUpd τ x b) := by
  refine ⟨fun h => ?_, fun h => .all hx hq h⟩
  cases h with
  | leaf hD _ => exact absurd (hD _ hx.1) hx.2.1
  | ex hy hq' _ _ => exact absurd hq ((hy.unique hwf hx) ▸ hq')
  | all hy _ h => exact (hy.unique hwf hx) ▸ h

end Game

/-! ### Isomorphism-invariance -/

section Iso

variable {A B : Type} [Lax134656.Qsat.qsat.Structure A] [Lax134656.Qsat.qsat.Structure B]

/-- The push-forward of a predicate along an isomorphism. -/
private def pushQ (e : A ≃[Lax134656.Qsat.qsat] B) (ν : A → Prop) : B → Prop :=
  fun b => ν (e.symm b)

private theorem pushQ_apply (e : A ≃[Lax134656.Qsat.qsat] B) (ν : A → Prop) (a : A) :
    pushQ e ν (e a) ↔ ν a :=
  iff_of_eq (congrArg ν (e.symm_apply_apply a))

private theorem pushQ_qAdd (e : A ≃[Lax134656.Qsat.qsat] B) (D : A → Prop) (x : A) :
    pushQ e (Lax134656.Qsat.qAdd D x) = Lax134656.Qsat.qAdd (pushQ e D) (e x) := by
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | h
    · exact Or.inl ((e.toEquiv.symm_apply_eq).mp h)
    · exact Or.inr h
  · rcases h with h | h
    · exact Or.inl ((e.toEquiv.symm_apply_eq).mpr h)
    · exact Or.inr h

private theorem pushQ_qUpd (e : A ≃[Lax134656.Qsat.qsat] B) (τ : A → Prop) (x : A) (b : Bool) :
    pushQ e (Lax134656.Qsat.qUpd τ x b) = Lax134656.Qsat.qUpd (pushQ e τ) (e x) b := by
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨he, hb⟩ | ⟨hne, hy⟩
    · exact Or.inl ⟨(e.toEquiv.symm_apply_eq).mp he, hb⟩
    · exact Or.inr ⟨fun hy' => hne ((e.toEquiv.symm_apply_eq).mpr hy'), hy⟩
  · rcases h with ⟨he, hb⟩ | ⟨hne, hy⟩
    · exact Or.inl ⟨(e.toEquiv.symm_apply_eq).mpr he, hb⟩
    · exact Or.inr ⟨fun hy' => hne ((e.toEquiv.symm_apply_eq).mp hy'), hy⟩

private theorem isQVar_push (e : A ≃[Lax134656.Qsat.qsat] B) (x : A) :
    Lax134656.Qsat.IsQVar (e x) ↔ Lax134656.Qsat.IsQVar x :=
  (relMap_equiv₁ e Lax134656.Qsat.qsIsVar x).symm

private theorem isQAll_push (e : A ≃[Lax134656.Qsat.qsat] B) (x : A) :
    Lax134656.Qsat.IsQAll (e x) ↔ Lax134656.Qsat.IsQAll x :=
  (relMap_equiv₁ e Lax134656.Qsat.qsAllVar x).symm

private theorem qPrec_push (e : A ≃[Lax134656.Qsat.qsat] B) (x y : A) :
    Lax134656.Qsat.QPrec (e x) (e y) ↔ Lax134656.Qsat.QPrec x y :=
  (relMap_equiv₂ e Lax134656.Qsat.qsPrefixLt x y).symm

private theorem qsatMatrix_push (e : A ≃[Lax134656.Qsat.qsat] B) {τ : A → Prop}
    (h : Lax134656.Qsat.QsatMatrix τ) : Lax134656.Qsat.QsatMatrix (pushQ e τ) := by
  intro c hc
  obtain ⟨x, hvar, hx⟩ := h (e.symm c) ((relMap_equiv₁ e.symm Lax134656.Qsat.qsIsClause c).mp hc)
  refine ⟨e x, (isQVar_push e x).mpr hvar, ?_⟩
  rcases hx with ⟨hp, hv⟩ | ⟨hn, hv⟩
  · refine Or.inl ⟨?_, (pushQ_apply e τ x).mpr hv⟩
    simpa using (relMap_equiv₂ e Lax134656.Qsat.qsPosIn (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, fun hv' => hv ((pushQ_apply e τ x).mp hv')⟩
    simpa using (relMap_equiv₂ e Lax134656.Qsat.qsNegIn (e.symm c) x).mp hn

private theorem qLeast_push (e : A ≃[Lax134656.Qsat.qsat] B) {D : A → Prop} {x : A}
    (h : Lax134656.Qsat.QLeast D x) : Lax134656.Qsat.QLeast (pushQ e D) (e x) := by
  refine ⟨(isQVar_push e x).mpr h.1, fun hd => h.2.1 ((pushQ_apply e D x).mp hd), ?_⟩
  intro y hy hd hlt
  refine h.2.2 (e.symm y) ((isQVar_push e (e.symm y)).mp (by rwa [e.apply_symm_apply])) hd ?_
  have := (qPrec_push e (e.symm y) x).mp (by rwa [e.apply_symm_apply])
  exact this

private theorem qsatWins_push (e : A ≃[Lax134656.Qsat.qsat] B) {D τ : A → Prop}
    (h : Lax134656.Qsat.QsatWins D τ) : Lax134656.Qsat.QsatWins (pushQ e D) (pushQ e τ) := by
  induction h with
  | leaf hD hm =>
    refine .leaf (fun y hy => ?_) (qsatMatrix_push e hm)
    have := hD (e.symm y) ((isQVar_push e (e.symm y)).mp (by rwa [e.apply_symm_apply]))
    exact this
  | ex hx hq b _ ih =>
    refine .ex (qLeast_push e hx) (fun hq' => hq ((isQAll_push e _).mp hq')) b ?_
    rwa [pushQ_qAdd, pushQ_qUpd] at ih
  | all hx hq _ ih =>
    refine .all (qLeast_push e hx) ((isQAll_push e _).mpr hq) (fun b => ?_)
    have := ih b
    rwa [pushQ_qAdd, pushQ_qUpd] at this

private theorem isQVar_symm (e : A ≃[Lax134656.Qsat.qsat] B) (x : B) :
    Lax134656.Qsat.IsQVar x ↔ Lax134656.Qsat.IsQVar (e.symm x) := by
  rw [← isQVar_push e (e.symm x), e.apply_symm_apply]

private theorem qPrec_symm (e : A ≃[Lax134656.Qsat.qsat] B) (x y : B) :
    Lax134656.Qsat.QPrec x y ↔ Lax134656.Qsat.QPrec (e.symm x) (e.symm y) := by
  rw [← qPrec_push e (e.symm x) (e.symm y), e.apply_symm_apply, e.apply_symm_apply]

private theorem qsatWf_push (e : A ≃[Lax134656.Qsat.qsat] B) (h : Lax134656.Qsat.QsatWf A) : Lax134656.Qsat.QsatWf B where
  isVar_of_prec x y hxy :=
    let ⟨h1, h2⟩ := h.isVar_of_prec _ _ ((qPrec_symm e x y).mp hxy)
    ⟨(isQVar_symm e x).mpr h1, (isQVar_symm e y).mpr h2⟩
  irrefl x hx := h.irrefl (e.symm x) ((qPrec_symm e x x).mp hx)
  trans x y z hxy hyz := (qPrec_symm e x z).mpr
    (h.trans _ (e.symm y) _ ((qPrec_symm e x y).mp hxy) ((qPrec_symm e y z).mp hyz))
  total x y hx hy hne := by
    refine (h.total (e.symm x) (e.symm y) ((isQVar_symm e x).mp hx) ((isQVar_symm e y).mp hy)
      (fun hh => hne ?_)).imp (qPrec_symm e x y).mpr (qPrec_symm e y x).mpr
    rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, hh]

end Iso

/-! ### The decision problem -/

section Problem

variable {A : Type} [Lax134656.Qsat.qsat.Structure A]

private theorem qsatHolds_of_iso {B : Type} [Lax134656.Qsat.qsat.Structure B]
    (e : A ≃[Lax134656.Qsat.qsat] B) (h : Lax134656.Qsat.QsatHolds A) : Lax134656.Qsat.QsatHolds B := by
  obtain ⟨hwf, hw⟩ := h
  refine ⟨qsatWf_push e hwf, ?_⟩
  have := qsatWins_push e hw
  have hD : pushQ e (fun _ : A => False) = (fun _ : B => False) := rfl
  rwa [hD] at this

end Problem

/-- **QSAT**, as a problem on `FirstOrder.Language.qsat`-structures: is the fully
quantified Boolean formula described by the instance true? -/
def QSAT : Lax904597.Problems.DecisionProblem Lax134656.Qsat.qsat where
  Holds := fun A inst => @Lax134656.Qsat.QsatHolds A inst
  iso_invariant := fun e => ⟨qsatHolds_of_iso e, qsatHolds_of_iso e.symm⟩

end Lax822549Proofs.DescriptiveComplexity


