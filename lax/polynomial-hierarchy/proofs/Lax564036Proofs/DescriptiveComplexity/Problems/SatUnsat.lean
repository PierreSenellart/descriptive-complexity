/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax564036Proofs.DescriptiveComplexity.Problems.Sat
import Lax564036Proofs.DescriptiveComplexity.Difference
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

namespace Lax564036.SatUnsat
end Lax564036.SatUnsat

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.SatUnsat (SatWith)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SigmaSODefinable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax564036.SatUnsat (satPair satPairRel spIsCl₁ spIsCl₂ spNeg₁ spNeg₂ spPos₁ spPos₂)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# SAT-UNSAT, the canonical DP problem

**SAT-UNSAT** ([Papadimitriou & Yannakakis 1984][papadimitriou1984complexity]):
given *two* CNF formulas, is the first satisfiable *and* the second not? It is
the prototypical problem of `DescriptiveComplexity.DP`, the class of differences of
NP problems, and it wears its DP definition on its sleeve – one half is an NP
condition, the other a coNP one, and they are imposed on disjoint parts of the
vocabulary.

## The vocabulary

An instance carries the two formulas side by side: `Language.satPair` is two
copies of `Language.sat`, one per side. Both live on the same universe – there
is no need to keep the two formulas' variables apart, since each side's clauses
only mention their own occurrence relations, and a truth assignment for one
side is free to do as it likes on the other side's variables.

## What is here, and what is not

The vocabulary, the semantics and isomorphism-invariance, and the three
problems: `DescriptiveComplexity.SATUNSAT` itself together with its two halves
`DescriptiveComplexity.SatFirst` (an NP condition) and
`DescriptiveComplexity.UnsatSecond` (a coNP one), which are what a DP definition of
it will conjoin. Satisfiability of a side is stated once, parameterized by the
triple of relation symbols to read (`DescriptiveComplexity.SatWith`), since the two
sides differ only in that.

**Membership in DP** (`DescriptiveComplexity.satUnsat_mem_DP`) is proved without
writing a single new kernel: each side is *projected* onto a plain
`Language.sat` instance by a one-dimensional, single-tag interpretation
(`DescriptiveComplexity.sideInterp`), so `SatFirst` reduces to SAT and `SatSecond`
does too; `Σ₁`-definability of the first half and `Π₁`-definability of the
second then come from `DescriptiveComplexity.sat_sigmaSODefinable` by closure of the
levels under FO reductions, the second after complementing the reduction.

**DP-hardness** is in `DescriptiveComplexity.Problems.SatUnsat.Hardness`
(`DescriptiveComplexity.satUnsat_hard_of_dpDefinable`, whence
`DescriptiveComplexity.SATUNSAT_DP_complete`): the Cook–Levin discharge of the `Σ₁`
half and that of the complement of the `Π₁` half, run side by side into a
single paired instance. The lemma below on satisfiability along a
clause-covering embedding is the step it needs.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Satisfiability of one side -/

section Defs

variable (A : Type) [Lax564036.SatUnsat.satPair.Structure A]

end Defs

section Iso

variable {A B : Type} [Lax564036.SatUnsat.satPair.Structure A] [Lax564036.SatUnsat.satPair.Structure B]

private theorem satWith_of_iso (e : A ≃[Lax564036.SatUnsat.satPair] B)
    (isCl : Lax564036.SatUnsat.satPair.Relations 1) (pos neg : Lax564036.SatUnsat.satPair.Relations 2)
    (h : Lax564036.SatUnsat.SatWith A isCl pos neg) : Lax564036.SatUnsat.SatWith B isCl pos neg := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨x, hx⟩ := hν (e.symm c) ((relMap_equiv₁ e.symm isCl c).mp hc)
  refine ⟨e x, ?_⟩
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · refine Or.inl ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e pos (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e neg (e.symm c) x).mp hn

/-- Satisfiability of a side is isomorphism-invariant. -/
theorem satWith_iso (e : A ≃[Lax564036.SatUnsat.satPair] B) (isCl : Lax564036.SatUnsat.satPair.Relations 1)
    (pos neg : Lax564036.SatUnsat.satPair.Relations 2) :
    Lax564036.SatUnsat.SatWith A isCl pos neg ↔ Lax564036.SatUnsat.SatWith B isCl pos neg :=
  ⟨satWith_of_iso e isCl pos neg, satWith_of_iso e.symm isCl pos neg⟩

end Iso

/-- The first formula of the pair is satisfiable: the NP half of SAT-UNSAT. -/
def SatFirst : Lax904597.Problems.DecisionProblem Lax564036.SatUnsat.satPair where
  Holds := fun A inst => @Lax564036.SatUnsat.SatWith A inst Lax564036.SatUnsat.spIsCl₁ Lax564036.SatUnsat.spPos₁ Lax564036.SatUnsat.spNeg₁
  iso_invariant := fun e => satWith_iso e _ _ _

/-- The second formula of the pair is unsatisfiable: the coNP half. -/
def UnsatSecond : Lax904597.Problems.DecisionProblem Lax564036.SatUnsat.satPair where
  Holds := fun A inst => ¬@Lax564036.SatUnsat.SatWith A inst Lax564036.SatUnsat.spIsCl₂ Lax564036.SatUnsat.spPos₂ Lax564036.SatUnsat.spNeg₂
  iso_invariant := fun e => not_congr (satWith_iso e _ _ _)

/-- **SAT-UNSAT**: the first formula of the pair is satisfiable and the second
is not. -/
def SATUNSAT : Lax904597.Problems.DecisionProblem Lax564036.SatUnsat.satPair where
  Holds := fun A inst =>
    @Lax564036.SatUnsat.SatWith A inst Lax564036.SatUnsat.spIsCl₁ Lax564036.SatUnsat.spPos₁ Lax564036.SatUnsat.spNeg₁ ∧ ¬@Lax564036.SatUnsat.SatWith A inst Lax564036.SatUnsat.spIsCl₂ Lax564036.SatUnsat.spPos₂ Lax564036.SatUnsat.spNeg₂
  iso_invariant := fun e =>
    and_congr (satWith_iso e _ _ _) (not_congr (satWith_iso e _ _ _))

/-! ### Reading one side as a plain CNF instance

Rather than restate SAT's `Σ₁` kernel for a pair of formulas, each side is
*projected* onto a plain `Language.sat` instance by a one-dimensional,
single-tag interpretation. Definability of both halves is then inherited from
`DescriptiveComplexity.sat_sigmaSODefinable` by closure under FO reductions – no new
kernel, and no second copy of its realization proof. -/

section Projection

/-- The interpretation reading the side given by a triple of symbols as a
plain CNF instance: same universe, the three relations renamed. -/
def sideInterp (isCl : Lax564036.SatUnsat.satPair.Relations 1)
    (pos neg : Lax564036.SatUnsat.satPair.Relations 2) :
    Lax904597.Interpretations.FOInterpretation Lax564036.SatUnsat.satPair Lax904597.Sat.sat Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun _ => FirstOrder.Language.Relations.formula₁ isCl (FirstOrder.Language.Term.var (0, 0))
    | _, .posIn => fun _ => FirstOrder.Language.Relations.formula₂ pos (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .negIn => fun _ => FirstOrder.Language.Relations.formula₂ neg (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))

variable {A : Type} [Lax564036.SatUnsat.satPair.Structure A]

variable (isCl : Lax564036.SatUnsat.satPair.Relations 1) (pos neg : Lax564036.SatUnsat.satPair.Relations 2)

@[simp]
theorem sideInterp_isClause (w : Fin 1 → A) :
    RelMap (M := (sideInterp isCl pos neg).Map A) Lax904597.Sat.satIsClause ![((), w)] ↔
      RelMap isCl ![w 0] := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_rel₁

@[simp]
theorem sideInterp_posIn (w w' : Fin 1 → A) :
    RelMap (M := (sideInterp isCl pos neg).Map A) Lax904597.Sat.satPosIn ![((), w), ((), w')] ↔
      RelMap pos ![w 0, w' 0] := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_rel₂

@[simp]
theorem sideInterp_negIn (w w' : Fin 1 → A) :
    RelMap (M := (sideInterp isCl pos neg).Map A) Lax904597.Sat.satNegIn ![((), w), ((), w')] ↔
      RelMap neg ![w 0, w' 0] := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_rel₂

/-- The projected instance is satisfiable exactly when that side is. -/
theorem satisfiable_sideInterp :
    Lax904597.Sat.Satisfiable ((sideInterp isCl pos neg).Map A) ↔ Lax564036.SatUnsat.SatWith A isCl pos neg := by
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨fun a => ν ((), fun _ => a), fun c hc => ?_⟩
    obtain ⟨x, hx⟩ := hν ((), fun _ => c) ((sideInterp_isClause isCl pos neg _).mpr hc)
    obtain ⟨⟨⟩, w⟩ := x
    have hw : (fun _ : Fin 1 => w 0) = w := funext fun j => congrArg w (Subsingleton.elim 0 j)
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨w 0, Or.inl ⟨(sideInterp_posIn isCl pos neg _ _).mp hp, by
        change ν ((), fun _ => w 0); rw [hw]; exact hT⟩⟩
    · exact ⟨w 0, Or.inr ⟨(sideInterp_negIn isCl pos neg _ _).mp hn, by
        change ¬ν ((), fun _ => w 0); rw [hw]; exact hT⟩⟩
  · rintro ⟨ν, hν⟩
    refine ⟨fun p => ν (p.2 0), ?_⟩
    rintro ⟨⟨⟩, w⟩ hc
    obtain ⟨x, hx⟩ := hν (w 0) ((sideInterp_isClause isCl pos neg w).mp hc)
    refine ⟨((), fun _ => x), ?_⟩
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨(sideInterp_posIn isCl pos neg w _).mpr hp, hT⟩
    · exact Or.inr ⟨(sideInterp_negIn isCl pos neg w _).mpr hn, hT⟩

end Projection

/-! ### Satisfiability ignores elements outside the formula

The step both halves of a DP-hardness pairing will need. Pairing two
reductions into one instance forces a common dimension and a common universe,
so each side's formula ends up sitting inside a larger structure: the other
side's points are there too, and so are the tuples the shorter side does not
use. Those extra elements are *not* harmless by fiat, but they are harmless
once they are neither clauses nor occurrences, which is what the lemma below
says.

It is stated as transfer along an injection `j` that reflects the three
relations, hits every clause, and hits every element occurring in a clause of
its image. Elements outside the image are then pure spectators: a truth
assignment may do as it likes on them. -/

section Cover

variable {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]

/-- **Satisfiability transfers along a clause-covering embedding.** The extra
elements of `A` – those outside the image of `j` – are neither clauses nor
occurrences, so they constrain nothing and a satisfying assignment of `B`
extends to them arbitrarily. -/
theorem satisfiable_iff_of_cover (j : B → A) (hj : Function.Injective j)
    (hcl : ∀ b : B, RelMap Lax904597.Sat.satIsClause ![j b] ↔ RelMap Lax904597.Sat.satIsClause ![b])
    (hpos : ∀ b b' : B, RelMap Lax904597.Sat.satPosIn ![j b, j b'] ↔ RelMap Lax904597.Sat.satPosIn ![b, b'])
    (hneg : ∀ b b' : B, RelMap Lax904597.Sat.satNegIn ![j b, j b'] ↔ RelMap Lax904597.Sat.satNegIn ![b, b'])
    (hclImg : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ b : B, c = j b)
    (hoccImg : ∀ (b : B) (x : A),
      RelMap Lax904597.Sat.satPosIn ![j b, x] ∨ RelMap Lax904597.Sat.satNegIn ![j b, x] → ∃ b' : B, x = j b') :
    Lax904597.Sat.Satisfiable A ↔ Lax904597.Sat.Satisfiable B := by
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨fun b => ν (j b), fun c hc => ?_⟩
    obtain ⟨x, hx⟩ := hν (j c) ((hcl c).mpr hc)
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · obtain ⟨c', rfl⟩ := hoccImg c x (Or.inl hp)
      exact ⟨c', Or.inl ⟨(hpos c c').mp hp, hT⟩⟩
    · obtain ⟨c', rfl⟩ := hoccImg c x (Or.inr hn)
      exact ⟨c', Or.inr ⟨(hneg c c').mp hn, hT⟩⟩
  · rintro ⟨ν, hν⟩
    refine ⟨fun a => ∃ b : B, a = j b ∧ ν b, fun c hc => ?_⟩
    have himg : ∀ b : B, (∃ b' : B, j b = j b' ∧ ν b') ↔ ν b := by
      refine fun b => ⟨?_, fun h => ⟨b, rfl, h⟩⟩
      rintro ⟨b', hb', hν'⟩
      exact hj hb' ▸ hν'
    obtain ⟨c', rfl⟩ := hclImg c hc
    obtain ⟨x, hx⟩ := hν c' ((hcl c').mp hc)
    refine ⟨j x, ?_⟩
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨(hpos c' x).mpr hp, (himg x).mpr hT⟩
    · exact Or.inr ⟨(hneg c' x).mpr hn, fun h => hT ((himg x).mp h)⟩

end Cover

/-! ### Membership in DP -/

/-- The second formula of the pair is satisfiable: the problem
`DescriptiveComplexity.UnsatSecond` complements. -/
def SatSecond : Lax904597.Problems.DecisionProblem Lax564036.SatUnsat.satPair where
  Holds := fun A inst => @Lax564036.SatUnsat.SatWith A inst Lax564036.SatUnsat.spIsCl₂ Lax564036.SatUnsat.spPos₂ Lax564036.SatUnsat.spNeg₂
  iso_invariant := fun e => satWith_iso e _ _ _

/-- Projecting the first side is a reduction of `SatFirst` to SAT. -/
def satFirst_le_sat : SatFirst ≤ᶠᵒ Lax904597.Sat.SAT where
  Tag := Unit
  dim := 1
  toInterpretation := sideInterp Lax564036.SatUnsat.spIsCl₁ Lax564036.SatUnsat.spPos₁ Lax564036.SatUnsat.spNeg₁
  correct _ _ _ _ := (satisfiable_sideInterp Lax564036.SatUnsat.spIsCl₁ Lax564036.SatUnsat.spPos₁ Lax564036.SatUnsat.spNeg₁).symm

/-- Projecting the second side is a reduction of `SatSecond` to SAT. -/
def satSecond_le_sat : SatSecond ≤ᶠᵒ Lax904597.Sat.SAT where
  Tag := Unit
  dim := 1
  toInterpretation := sideInterp Lax564036.SatUnsat.spIsCl₂ Lax564036.SatUnsat.spPos₂ Lax564036.SatUnsat.spNeg₂
  correct _ _ _ _ := (satisfiable_sideInterp Lax564036.SatUnsat.spIsCl₂ Lax564036.SatUnsat.spPos₂ Lax564036.SatUnsat.spNeg₂).symm

/-- **The first side's satisfiability is `Σ₁`-definable**, inherited from SAT
along the projection. -/
theorem satFirst_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 SatFirst :=
  sat_sigmaSODefinable.of_foReduction satFirst_le_sat

/-- `UnsatSecond` is the complement of `SatSecond`. -/
theorem unsatSecond_eq_compl : UnsatSecond = SatSecondᶜ :=
  DecisionProblem.ext fun _ _ => Iff.rfl

/-- **The second side's unsatisfiability is `Π₁`-definable**: the complement of
an NP condition, the reduction complementing along with it. -/
theorem unsatSecond_piSODefinable : Lax904597.SecondOrder.PiSODefinable 1 UnsatSecond := by
  rw [unsatSecond_eq_compl]
  exact PiSODefinable.of_foReduction satSecond_le_sat.compl
    ((compl_mem_coNP_iff Lax904597.Sat.SAT).mpr sat_sigmaSODefinable)

/-- **SAT-UNSAT is in DP**, by its very shape: an NP condition on one side and
a coNP condition on the other, imposed together. -/
theorem satUnsat_mem_DP : SATUNSAT ∈ DP :=
  ⟨SatFirst, UnsatSecond, satFirst_sigmaSODefinable, unsatSecond_piSODefinable,
    fun _ _ _ _ => Iff.rfl⟩

end Lax564036Proofs.DescriptiveComplexity


