/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Tactic.FinCases
import Lax564036Proofs.DescriptiveComplexity.Vocabulary
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# SAT: propositional satisfiability

The problem SAT, as a decision problem on first-order structures. A CNF
formula is a `FirstOrder.Language.sat`-structure: elements are clauses and
propositional variables, `satIsClause c` distinguishes the clauses, and
`satPosIn c x` / `satNegIn c x` say that the literal `x` / `¬x` occurs in
clause `c`. `DescriptiveComplexity.Satisfiable` is the usual satisfiability, and
`DescriptiveComplexity.SAT` the bundled decision problem.

SAT is the archetypical NP-complete problem: this is the Cook–Levin theorem
([Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal];
`DescriptiveComplexity.SAT_NP_complete`, in `DescriptiveComplexity.Problems.Sat.Hardness`). With
NP *defined* as existential-second-order definability
(`DescriptiveComplexity.Hierarchy`), its membership half is the theorem
`DescriptiveComplexity.sat_sigmaSODefinable` proved here – “there is a truth assignment
making every clause true” – and its hardness half is the machine-free,
Dahlhaus-style ([Dahlhaus 1983][dahlhaus1983reduction]) generic reduction
`DescriptiveComplexity.sat_hard_of_sigmaSODefinable`
of `DescriptiveComplexity.Problems.Sat.Hardness`. Other problems' NP-completeness
proofs derive from it through first-order reductions; see e.g.,
`DescriptiveComplexity.Problems.ThreeColorability`.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Sat

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end Sat

section Iso

private theorem satisfiable_of_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) (h : Lax904597.Sat.Satisfiable A) :
    Lax904597.Sat.Satisfiable B := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨x, hx⟩ := hν (e.symm c) ((relMap_equiv₁ e.symm Lax904597.Sat.satIsClause c).mp hc)
  refine ⟨e x, ?_⟩
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · refine Or.inl ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e Lax904597.Sat.satPosIn (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e Lax904597.Sat.satNegIn (e.symm c) x).mp hn

/-- Satisfiability is isomorphism-invariant. -/
theorem satisfiable_iso {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) : Lax904597.Sat.Satisfiable A ↔ Lax904597.Sat.Satisfiable B :=
  ⟨satisfiable_of_iso e, satisfiable_of_iso e.symm⟩

end Iso

/-! ### SAT is existential second-order definable

SAT is `Σ₁`-definable in the sense of `DescriptiveComplexity.SecondOrder` – “there
exists a truth assignment (a unary relation) making every clause true”, the
inner part being first-order. Since NP is *defined* as `Σ₁`-definability,
this is the membership half of the Cook–Levin theorem. -/

section SigmaOne

open Lax904597.SecondOrder.SOBlock

/-- The single existential block of the `Σ₁` definition of SAT: one unary
relation variable, the truth assignment. -/
def satAssignBlock : Lax904597.SecondOrder.SOBlock where
  ι := Unit
  arity := fun _ => 1

/-- The symbol of the truth-assignment relation variable. -/
def satNuSym : satAssignBlock.lang.Relations 1 := ⟨(), rfl⟩

/-- The vocabulary of the kernel: CNF instances together with the
truth-assignment relation variable. -/
abbrev satSOLang : Language := Lax904597.Sat.sat.sum satAssignBlock.lang

/-- The symbol for “is a clause” in the kernel's vocabulary. -/
abbrev kIsClSym : satSOLang.Relations 1 := Sum.inl Lax904597.Sat.satIsClause

/-- The symbol for “occurs positively in” in the kernel's vocabulary. -/
abbrev kPosSym : satSOLang.Relations 2 := Sum.inl Lax904597.Sat.satPosIn

/-- The symbol for “occurs negatively in” in the kernel's vocabulary. -/
abbrev kNegSym : satSOLang.Relations 2 := Sum.inl Lax904597.Sat.satNegIn

/-- The truth-assignment symbol in the kernel's vocabulary. -/
abbrev kNuSym : satSOLang.Relations 1 := Sum.inr satNuSym

/-- The first-order kernel of the `Σ₁` definition of SAT: every clause
contains a true literal. The universally quantified variable is the clause,
the existentially quantified one the literal's variable. -/
noncomputable def satKernel : satSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ kIsClSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊔
            FirstOrder.Language.Relations.formula₂ kNegSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 0))))))

/-- Realization of the kernel under an assignment of the truth-assignment
variable: every clause contains a true literal. (Reused by the membership
proof of HORN-SAT, whose kernel is this one conjoined with the first-order
Horn condition.) -/
theorem realize_satKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) satKernel) ↔
      ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
        (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
          (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [satKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  constructor
  · intro h c hc
    obtain ⟨x, hx⟩ := h (fun _ => c) hc
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨x 0, Or.inl ⟨hp, hT⟩⟩
    · exact ⟨x 0, Or.inr ⟨hn, hT⟩⟩
  · intro h i hc
    obtain ⟨x, hx⟩ := h (i 0) hc
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨fun _ => x, Or.inl ⟨hp, hT⟩⟩
    · exact ⟨fun _ => x, Or.inr ⟨hn, hT⟩⟩

/-- **SAT is `Σ₁`-definable**: satisfiability of a CNF structure is expressed
by existentially quantifying a truth assignment and checking, in first-order
logic, that every clause contains a true literal. -/
theorem sat_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 Lax904597.Sat.SAT := by
  refine ⟨[satAssignBlock], rfl, satKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨ν, hν⟩
    exact ⟨fun _ x => ν (x ⟨0, Nat.one_pos⟩),
      (realize_satKernel _).mpr fun c hc => hν c hc⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨fun a => ρ satNuSym.1 fun _ => a, fun c hc => (realize_satKernel ρ).mp hρ c hc⟩

end SigmaOne

end Lax564036Proofs.DescriptiveComplexity


