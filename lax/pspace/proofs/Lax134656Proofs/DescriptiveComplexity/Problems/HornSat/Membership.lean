/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax134656Proofs.DescriptiveComplexity.Problems.HornSat.Defs
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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

namespace Lax535992.HornSat
end Lax535992.HornSat

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SigmaSODefinable)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.HornSat (AtMostOnePositive)
end Lax134656Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# HORN-SAT is existential second-order definable

HORN-SAT is `Σ₁`-definable (`DescriptiveComplexity.hornSat_sigmaSODefinable`), hence in
NP: its kernel is the one of SAT (`DescriptiveComplexity.satKernel` – every clause
contains a true literal) conjoined with the *first-order* Horn condition
(`DescriptiveComplexity.hornCondKernel` – no clause has two distinct positive literals),
over the same single existential block guessing a truth assignment.

Membership in NP is of course not the sharp statement: Horn satisfiability is
decidable in linear time ([Dowling & Gallier 1984][dowling1984linear]), and
HORN-SAT is the canonical complete problem for polynomial time. What the
library can state without a definition of PTIME is the hardness half, in
`DescriptiveComplexity.Problems.HornSat.Hardness`.
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- The first-order Horn condition, in the kernel's vocabulary: two variables
occurring positively in the same clause coincide. -/
noncomputable def hornCondKernel : satSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₁ kIsClSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
            FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
          (FirstOrder.Language.Term.var (Sum.inr 2))))

/-- Realization of the Horn condition: it does not depend on the guessed truth
assignment, and says exactly that every clause has at most one positive
literal. -/
theorem realize_hornCondKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) hornCondKernel) ↔
      Lax535992.HornSat.AtMostOnePositive A := by
  let := satAssignBlock.structure ρ
  rw [hornCondKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl]
  constructor
  · intro h c x y hc hx hy
    exact h ![c, x, y] ⟨⟨hc, hx⟩, hy⟩
  · intro h i hi
    exact h (i 0) (i 1) (i 2) hi.1.1 hi.1.2 hi.2

/-- Realization of the full kernel: the Horn condition and the SAT kernel. -/
private theorem realize_hornSatKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) (hornCondKernel ⊓ satKernel)) ↔
      Lax535992.HornSat.AtMostOnePositive A ∧
        ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
          (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
            (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) := by
  let := satAssignBlock.structure ρ
  exact Formula.realize_inf.trans
    (and_congr (realize_hornCondKernel ρ) (realize_satKernel ρ))

/-- **HORN-SAT is `Σ₁`-definable**: guess a truth assignment and check, in
first-order logic, that every clause contains a true literal and that no clause
has two positive literals. Since NP is defined as `Σ₁`-definability, this is
the statement `HORNSAT ∈ NP`. -/
theorem hornSat_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 HORNSAT := by
  refine ⟨[satAssignBlock], rfl, hornCondKernel ⊓ satKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨hhorn, ν, hν⟩
    exact ⟨fun _ x => ν (x ⟨0, Nat.one_pos⟩),
      (realize_hornSatKernel _).mpr ⟨hhorn, fun c hc => hν c hc⟩⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hhorn, hsat⟩ := (realize_hornSatKernel ρ).mp hρ
    exact ⟨hhorn, fun a => ρ satNuSym.1 fun _ => a, hsat⟩

/-- HORN-SAT is in NP. -/
theorem hornSat_mem_NP : HORNSAT ∈ NP :=
  hornSat_sigmaSODefinable

end SigmaOne

end Lax134656Proofs.DescriptiveComplexity


