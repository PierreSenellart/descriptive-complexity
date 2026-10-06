/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax564036Proofs.DescriptiveComplexity.Problems.Sat.Hardness
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

namespace Lax564036.Tautology
end Lax564036.Tautology

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.Tautology (Tautology)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# TAUT: propositional tautology

The problem TAUT – is a formula in disjunctive normal form a tautology? – the
archetypical coNP-complete problem. Its instances are the structures of the
SAT vocabulary `FirstOrder.Language.sat`, *read disjunctively*: a CNF formula
and a DNF formula are the same data, a set of clauses (here: terms) with the
positive and negative occurrences of the variables in each. The reading is in
`DescriptiveComplexity.Tautology`: every truth assignment satisfies all the literals of
some term.

Both halves of the coNP-completeness come from SAT by the *same* interpretation
`DescriptiveComplexity.swapSignInterp`, which keeps the universe and the terms and
exchanges positive with negative occurrences. It witnesses De Morgan's law: a
DNF is a tautology exactly when the CNF obtained by negating every literal is
unsatisfiable (`DescriptiveComplexity.tautology_iff_not_satisfiable`). Hence

* `DescriptiveComplexity.taut_mem_coNP`: `TAUTᶜ` FO-reduces to SAT, so it is in NP, so
  TAUT is in coNP;
* `DescriptiveComplexity.taut_hard_of_piSODefinable`: a `Π₁`-definable problem has a
  `Σ₁`-definable complement, which reduces to SAT by the Cook–Levin discharge
  `DescriptiveComplexity.sat_hard_of_sigmaSODefinable`; complementing that reduction
  (`DescriptiveComplexity.OrderedFOReduction.compl`) and composing with `SATᶜ ≤ᶠᵒ TAUT`
  discharges coNP-hardness.

No new second-order argument is needed: TAUT is coNP-complete
(`DescriptiveComplexity.TAUT_coNP_complete`) purely by the complement machinery of
`DescriptiveComplexity.Complexity` and the duality
`DescriptiveComplexity.piSODefinable_iff_compl`.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### The disjunctive reading -/

section Taut

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end Taut

/-! ### De Morgan: tautology is unsatisfiability of the sign swap -/

section DeMorgan

variable {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]

/-- **De Morgan's law, structurally**: a DNF formula is a tautology iff the CNF
formula obtained by negating every literal is unsatisfiable. The equivalence
`e` presents `B` as the *sign swap* of `A`: same terms, positive and negative
occurrences exchanged. -/
theorem tautology_iff_not_satisfiable (e : A ≃ B)
    (hcl : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] ↔ RelMap Lax904597.Sat.satIsClause ![e c])
    (hpos : ∀ c x : A, RelMap Lax904597.Sat.satPosIn ![c, x] ↔ RelMap Lax904597.Sat.satNegIn ![e c, e x])
    (hneg : ∀ c x : A, RelMap Lax904597.Sat.satNegIn ![c, x] ↔ RelMap Lax904597.Sat.satPosIn ![e c, e x]) :
    Lax564036.Tautology.Tautology A ↔ ¬Lax904597.Sat.Satisfiable B := by
  constructor
  · rintro h ⟨μ, hμ⟩
    obtain ⟨c, hc, hall⟩ := h fun a => μ (e a)
    obtain ⟨y, hy⟩ := hμ (e c) ((hcl c).mp hc)
    rcases hy with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · refine (hall (e.symm y)).2 ((hneg c (e.symm y)).mpr ?_) ?_
      · simpa using hp
      · simpa using hT
    · refine hT ?_
      have := (hall (e.symm y)).1 ((hpos c (e.symm y)).mpr (by simpa using hn))
      simpa using this
  · intro h ν
    have hno : ¬∀ d : B, RelMap Lax904597.Sat.satIsClause ![d] → ∃ y : B,
        (RelMap Lax904597.Sat.satPosIn ![d, y] ∧ ν (e.symm y)) ∨
          (RelMap Lax904597.Sat.satNegIn ![d, y] ∧ ¬ν (e.symm y)) :=
      fun hall => h ⟨fun b => ν (e.symm b), hall⟩
    obtain ⟨d, hd⟩ := not_forall.mp hno
    obtain ⟨hd, hy⟩ := Classical.not_imp.mp hd
    refine ⟨e.symm d, (hcl (e.symm d)).mpr (by simpa using hd), fun x => ?_⟩
    have hy' := not_exists.mp hy (e x)
    rw [not_or] at hy'
    constructor
    · intro hp
      have := (hpos (e.symm d) x).mp hp
      rw [Equiv.apply_symm_apply] at this
      have := not_and.mp hy'.2 this
      simpa using not_not.mp this
    · intro hn
      have := (hneg (e.symm d) x).mp hn
      rw [Equiv.apply_symm_apply] at this
      have := not_and.mp hy'.1 this
      simpa using this

end DeMorgan

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

variable {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]

private theorem tautology_of_iso (e : A ≃[Lax904597.Sat.sat] B) (h : Lax564036.Tautology.Tautology A) :
    Lax564036.Tautology.Tautology B := by
  intro ν
  obtain ⟨c, hc, hall⟩ := h fun a => ν (e a)
  refine ⟨e c, (relMap_equiv₁ e Lax904597.Sat.satIsClause c).mp hc, fun y => ?_⟩
  constructor
  · intro hp
    have := (hall (e.symm y)).1
      ((relMap_equiv₂ e Lax904597.Sat.satPosIn c (e.symm y)).mpr (by simpa using hp))
    simpa using this
  · intro hn
    have := (hall (e.symm y)).2
      ((relMap_equiv₂ e Lax904597.Sat.satNegIn c (e.symm y)).mpr (by simpa using hn))
    simpa using this

/-- Being a tautology is isomorphism-invariant. -/
theorem tautology_iso (e : A ≃[Lax904597.Sat.sat] B) : Lax564036.Tautology.Tautology A ↔ Lax564036.Tautology.Tautology B :=
  ⟨tautology_of_iso e, tautology_of_iso e.symm⟩

end Iso

/-- TAUT, as a problem on `Language.sat`-structures read disjunctively: is
every truth assignment a model of some term? -/
def TAUT : Lax904597.Problems.DecisionProblem Lax904597.Sat.sat where
  Holds := fun A inst => @Lax564036.Tautology.Tautology A inst
  iso_invariant := fun e => tautology_iso e

/-! ### The sign-swapping interpretation -/

/-- The sign-swapping interpretation: same universe, same terms, positive and
negative occurrences exchanged. One-dimensional, single-tagged and
quantifier-free. -/
def swapSignInterp : Lax904597.Interpretations.FOInterpretation Lax904597.Sat.sat Lax904597.Sat.sat Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun _ => FirstOrder.Language.Relations.formula₁ Lax904597.Sat.satIsClause (FirstOrder.Language.Term.var (0, 0))
    | _, .posIn => fun _ => FirstOrder.Language.Relations.formula₂ Lax904597.Sat.satNegIn (FirstOrder.Language.Term.var (0, 0))
                                (FirstOrder.Language.Term.var (1, 0))
    | _, .negIn => fun _ => FirstOrder.Language.Relations.formula₂ Lax904597.Sat.satPosIn (FirstOrder.Language.Term.var (0, 0))
                                (FirstOrder.Language.Term.var (1, 0))

section Characterizations

variable {A : Type} [Lax904597.Sat.sat.Structure A]

@[simp]
theorem swapSign_isClause (w : Fin 1 → A) :
    RelMap (M := swapSignInterp.Map A) Lax904597.Sat.satIsClause ![((), w)] ↔ RelMap Lax904597.Sat.satIsClause ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [swapSignInterp, Formula.realize_rel₁]

@[simp]
theorem swapSign_posIn (w₁ w₂ : Fin 1 → A) :
    RelMap (M := swapSignInterp.Map A) Lax904597.Sat.satPosIn ![((), w₁), ((), w₂)] ↔
      RelMap Lax904597.Sat.satNegIn ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [swapSignInterp, Formula.realize_rel₂]

@[simp]
theorem swapSign_negIn (w₁ w₂ : Fin 1 → A) :
    RelMap (M := swapSignInterp.Map A) Lax904597.Sat.satNegIn ![((), w₁), ((), w₂)] ↔
      RelMap Lax904597.Sat.satPosIn ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [swapSignInterp, Formula.realize_rel₂]

end Characterizations

/-! ### Correctness of the swap, in both directions -/

section Correctness

variable (A : Type) [Lax904597.Sat.sat.Structure A]

/-- A DNF formula is a tautology iff its sign swap, read as a CNF formula, is
unsatisfiable. -/
theorem tautology_iff_not_satisfiable_map :
    Lax564036.Tautology.Tautology A ↔ ¬Lax904597.Sat.Satisfiable (swapSignInterp.Map A) := by
  refine tautology_iff_not_satisfiable (swapSignInterp.mapEquivSelf A).symm
    (fun c => (swapSign_isClause (A := A) fun _ => c).symm)
    (fun c x => (swapSign_negIn (A := A) (fun _ => c) fun _ => x).symm)
    fun c x => (swapSign_posIn (A := A) (fun _ => c) fun _ => x).symm

/-- Dually: the sign swap of a CNF formula, read as a DNF formula, is a
tautology iff the CNF formula is unsatisfiable. -/
theorem tautology_map_iff_not_satisfiable :
    Lax564036.Tautology.Tautology (swapSignInterp.Map A) ↔ ¬Lax904597.Sat.Satisfiable A := by
  refine tautology_iff_not_satisfiable (swapSignInterp.mapEquivSelf A) ?_ ?_ ?_
  · rintro ⟨⟨⟩, w⟩
    exact swapSign_isClause w
  · rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
    exact swapSign_posIn w w'
  · rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
    exact swapSign_negIn w w'

end Correctness

/-! ### The reductions -/

/-- **The complement of SAT FO-reduces to TAUT**, by the same swap. -/
def sat_compl_fo_reduction_taut : Lax904597.Sat.SATᶜ ≤ᶠᵒ TAUT where
  Tag := Unit
  dim := 1
  toInterpretation := swapSignInterp
  correct A _ _ _ := (tautology_map_iff_not_satisfiable A).symm

/-- **The complement of TAUT FO-reduces to SAT**: a DNF formula fails to be a
tautology exactly when its sign swap is satisfiable. -/
def taut_compl_fo_reduction_sat : TAUTᶜ ≤ᶠᵒ Lax904597.Sat.SAT where
  Tag := Unit
  dim := 1
  toInterpretation := swapSignInterp
  correct A _ _ _ := (not_congr (tautology_iff_not_satisfiable_map A)).trans not_not

/-! ### coNP-completeness -/

/-- **TAUT is in coNP**: its complement FO-reduces to SAT, hence is in NP. -/
theorem taut_mem_coNP : TAUT ∈ coNP :=
  (mem_piP_iff 1 TAUT).mpr (NP.mem_of_foReduction taut_compl_fo_reduction_sat sat_mem_NP)

/-- **coNP-hardness of TAUT**, by complementing the Cook–Levin discharge: a
`Π₁`-definable problem has a `Σ₁`-definable complement, which reduces to SAT;
complementing that reduction lands in `SATᶜ`, which the sign swap turns into
TAUT. -/
theorem taut_hard_of_piSODefinable :
    ∀ {L : Language.{0, 0}} [L.IsRelational] (Q : Lax904597.Problems.DecisionProblem L),
      Lax904597.SecondOrder.PiSODefinable 1 Q → Nonempty (Q ≤ᶠᵒ[≤] TAUT) := by
  intro L _ Q hQ
  obtain ⟨g⟩ := sat_hard_of_sigmaSODefinable Qᶜ ((piSODefinable_iff_compl 1 Q).mp hQ)
  exact ⟨(g.compl.congrSource fun A _ _ => not_not).trans_fo sat_compl_fo_reduction_taut⟩

/-- **TAUT is coNP-complete.** Membership is `DescriptiveComplexity.taut_mem_coNP` and
hardness `DescriptiveComplexity.taut_hard_of_piSODefinable`; both are the Cook–Levin
theorem read through the complement, with no second-order argument of their
own. -/
theorem TAUT_coNP_complete : coNP.Complete TAUT :=
  ⟨taut_mem_coNP,
    (hard_piP_succ_iff 0 TAUT).mpr fun Q hQ =>
      (taut_hard_of_piSODefinable Q hQ).map OrderedFOReduction.toRel⟩

end Lax564036Proofs.DescriptiveComplexity


