/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Problems.Sat
import Lax280166Proofs.DescriptiveComplexity.OccurrenceOrder
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax799700.OneInSat
end Lax799700.OneInSat

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SigmaSODefinable)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.OneInSat (OneInProper OneInSatisfiable)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue NegIn OccIn PosIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

/-!
# 1-in-SAT: the problem, and its membership in NP

EXACTLY-ONE SATISFIABILITY: is there a truth assignment giving every clause
*exactly one* true literal? Like NAE-SAT, it lives on the vocabulary
`FirstOrder.Language.sat` unchanged and only its notion of satisfaction differs
(`DescriptiveComplexity.OneInProper`), so this adds a problem rather than a language.
It is the second Schaefer-style variant of satisfiability
([Schaefer 1978][schaefer1978complexity]) in the catalog.

Its value is as a reduction *source*, and specifically for Exact Cover: a
1-in-SAT instance becomes an exact cover with no counting and no gadget at
all, one set per literal `(x, s)` gathering `x` itself and the clauses where
`(x, s)` occurs. Covering the element `x` exactly once picks exactly one of
the two literals of `x` – an assignment – and covering a clause exactly once
*is* exactly-one satisfaction. That works at any clause width, which is why
the catalog wants unrestricted 1-in-SAT rather than a width-three restriction.

Membership reuses SAT's kernel (`DescriptiveComplexity.realize_satKernel`, “every clause
has a true literal”) and adds uniqueness, as three clauses – one per pattern
of signs, the mixed pattern being simply forbidden.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock SatOcc

/-! ### The problem -/

section Semantics

variable {A : Type} [Lax904597.Sat.sat.Structure A]

end Semantics

section Problem

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]

/-- Isomorphisms preserve literal occurrences. -/
theorem occIn_iso (e : A ≃[Lax904597.Sat.sat] B) {c x : A} {s : Bool} :
    Lax799700.Common.SatOcc.OccIn c x s ↔ Lax799700.Common.SatOcc.OccIn (e c) (e x) s := by
  cases s with
  | false => exact and_congr (relMap_equiv₁ e Lax904597.Sat.satIsClause c) (relMap_equiv₂ e Lax904597.Sat.satNegIn c x)
  | true => exact and_congr (relMap_equiv₁ e Lax904597.Sat.satIsClause c) (relMap_equiv₂ e Lax904597.Sat.satPosIn c x)

private theorem oneInSatisfiable_of_iso (e : A ≃[Lax904597.Sat.sat] B)
    (h : Lax799700.OneInSat.OneInSatisfiable A) : Lax799700.OneInSat.OneInSatisfiable B := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨x, s, hx, hT, huniq⟩ :=
    hν (e.symm c) ((relMap_equiv₁ e.symm Lax904597.Sat.satIsClause c).mp hc)
  refine ⟨e x, s, by simpa using (occIn_iso e).mp hx, ?_, fun y t hy hTy => ?_⟩
  · cases s <;> simpa [Lax799700.Common.SatOcc.LitTrue] using hT
  · obtain ⟨h1, h2⟩ := huniq (e.symm y) t ((occIn_iso e.symm).mp hy)
      (by cases t <;> simpa [Lax799700.Common.SatOcc.LitTrue] using hTy)
    exact ⟨by simpa using congrArg e h1, h2⟩

/-- Exactly-one satisfiability is isomorphism-invariant. -/
theorem oneInSatisfiable_iso (e : A ≃[Lax904597.Sat.sat] B) :
    Lax799700.OneInSat.OneInSatisfiable A ↔ Lax799700.OneInSat.OneInSatisfiable B :=
  ⟨oneInSatisfiable_of_iso e, oneInSatisfiable_of_iso e.symm⟩

end Iso

/-- 1-in-SAT, as a problem on CNF instances: is there an assignment giving
every clause exactly one true literal? -/
def OneInSAT : Lax904597.Problems.DecisionProblem Lax904597.Sat.sat where
  Holds := fun A inst => @Lax799700.OneInSat.OneInSatisfiable A inst
  iso_invariant := fun e => oneInSatisfiable_iso e

/-! ### Membership -/

section SigmaOne

/-- Kernel conjunct: a clause has at most one true *positive* literal. -/
private noncomputable def oiPPClause : satSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₁ kIsClSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            (FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              (FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
                FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 2))))).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
          (FirstOrder.Language.Term.var (Sum.inr 2))))

/-- Kernel conjunct: a clause has at most one true *negative* literal. -/
private noncomputable def oiNNClause : satSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₁ kIsClSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            (FirstOrder.Language.Relations.formula₂ kNegSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                FirstOrder.Language.BoundedFormula.not
                  (FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 1))) ⊓
              (FirstOrder.Language.Relations.formula₂ kNegSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
                FirstOrder.Language.BoundedFormula.not
                  (FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 2)))))).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
          (FirstOrder.Language.Term.var (Sum.inr 2))))

/-- Kernel conjunct: a clause has no true positive *and* true negative
literal. -/
private noncomputable def oiPNClause : satSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      (FirstOrder.Language.BoundedFormula.not
        (FirstOrder.Language.Relations.formula₁ kIsClSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
          (FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
            (FirstOrder.Language.Relations.formula₂ kNegSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 2)))))))

/-- The first-order kernel of the `Σ₁` definition of 1-in-SAT: SAT's kernel
together with the three uniqueness clauses. -/
noncomputable def oneInKernel : satSOLang.Sentence :=
  satKernel ⊓ (oiPPClause ⊓ (oiNNClause ⊓ oiPNClause))

section Realize

variable {A : Type} [Lax904597.Sat.sat.Structure A] (ρ : satAssignBlock.Assignment A)

private theorem realize_oiPPClause :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oiPPClause) ↔
      ∀ c x y : A, Lax799700.Common.SatOcc.IsCl c → Lax799700.Common.SatOcc.PosIn c x → (ρ satNuSym.1 fun _ => x) → Lax799700.Common.SatOcc.PosIn c y →
        (ρ satNuSym.1 fun _ => y) → x = y := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [oiPPClause]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl,
    hsub]
  exact ⟨fun h c x y h1 h2 h3 h4 h5 => h ![c, x, y] ⟨h1, ⟨h2, h3⟩, h4, h5⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2.1.1 hi.2.1.2 hi.2.2.1 hi.2.2.2⟩

private theorem realize_oiNNClause :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oiNNClause) ↔
      ∀ c x y : A, Lax799700.Common.SatOcc.IsCl c → Lax799700.Common.SatOcc.NegIn c x → ¬(ρ satNuSym.1 fun _ => x) → Lax799700.Common.SatOcc.NegIn c y →
        ¬(ρ satNuSym.1 fun _ => y) → x = y := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [oiNNClause]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr,
    Language.relMap_sumInl, hsub]
  exact ⟨fun h c x y h1 h2 h3 h4 h5 => h ![c, x, y] ⟨h1, ⟨h2, h3⟩, h4, h5⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2.1.1 hi.2.1.2 hi.2.2.1 hi.2.2.2⟩

private theorem realize_oiPNClause :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oiPNClause) ↔
      ∀ c x y : A, Lax799700.Common.SatOcc.IsCl c → Lax799700.Common.SatOcc.PosIn c x → (ρ satNuSym.1 fun _ => x) → Lax799700.Common.SatOcc.NegIn c y →
        (ρ satNuSym.1 fun _ => y) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [oiPNClause]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, Language.relMap_sumInl, hsub]
  constructor
  · intro h c x y h1 h2 h3 h4
    by_contra h5
    exact h ![c, x, y] ⟨h1, ⟨h2, h3⟩, h4, h5⟩
  · rintro h i ⟨h1, ⟨h2, h3⟩, h4, h5⟩
    exact h5 (h (i 0) (i 1) (i 2) h1 h2 h3 h4)

private theorem realize_oneInKernel :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oneInKernel) ↔
      (∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
          (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
            (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x)) ∧
        (∀ c x y : A, Lax799700.Common.SatOcc.IsCl c → Lax799700.Common.SatOcc.PosIn c x → (ρ satNuSym.1 fun _ => x) → Lax799700.Common.SatOcc.PosIn c y →
            (ρ satNuSym.1 fun _ => y) → x = y) ∧
        (∀ c x y : A, Lax799700.Common.SatOcc.IsCl c → Lax799700.Common.SatOcc.NegIn c x → ¬(ρ satNuSym.1 fun _ => x) → Lax799700.Common.SatOcc.NegIn c y →
            ¬(ρ satNuSym.1 fun _ => y) → x = y) ∧
        ∀ c x y : A, Lax799700.Common.SatOcc.IsCl c → Lax799700.Common.SatOcc.PosIn c x → (ρ satNuSym.1 fun _ => x) → Lax799700.Common.SatOcc.NegIn c y →
          (ρ satNuSym.1 fun _ => y) := by
  rw [oneInKernel]
  simp only [Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_satKernel ρ)
    (and_congr (realize_oiPPClause ρ)
      (and_congr (realize_oiNNClause ρ) (realize_oiPNClause ρ)))

end Realize

/-- **The kernel says exactly what it should**: the guessed assignment gives
every clause exactly one true literal. -/
theorem realize_oneInKernel_iff_oneInProper {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oneInKernel) ↔
      Lax799700.OneInSat.OneInProper fun x => ρ satNuSym.1 fun _ => x := by
  rw [realize_oneInKernel]
  constructor
  · rintro ⟨hsat, hPP, hNN, hPN⟩ c hc
    obtain ⟨x, s, hx, hT⟩ := satClauses_occ hsat c hc
    refine ⟨x, s, hx, hT, fun y t hy hTy => ?_⟩
    cases s with
    | false =>
      cases t with
      | false => exact ⟨hNN c y x hc hy.2 hTy hx.2 hT, rfl⟩
      | true => exact absurd (hPN c y x hc hy.2 hTy hx.2) hT
    | true =>
      cases t with
      | false => exact absurd (hPN c x y hc hx.2 hT hy.2) hTy
      | true => exact ⟨hPP c y x hc hy.2 hTy hx.2 hT, rfl⟩
  · intro hν
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨x, s, hx, hT, -⟩ := hν c hc
      cases s with
      | false => exact ⟨x, Or.inr ⟨hx.2, hT⟩⟩
      | true => exact ⟨x, Or.inl ⟨hx.2, hT⟩⟩
    · intro c x y hc hx hTx hy hTy
      obtain ⟨z, u, -, -, huniq⟩ := hν c hc
      obtain ⟨h1, -⟩ := huniq x true ⟨hc, hx⟩ hTx
      obtain ⟨h2, -⟩ := huniq y true ⟨hc, hy⟩ hTy
      exact h1.trans h2.symm
    · intro c x y hc hx hTx hy hTy
      obtain ⟨z, u, -, -, huniq⟩ := hν c hc
      obtain ⟨h1, -⟩ := huniq x false ⟨hc, hx⟩ hTx
      obtain ⟨h2, -⟩ := huniq y false ⟨hc, hy⟩ hTy
      exact h1.trans h2.symm
    · intro c x y hc hx hTx hy
      by_contra hTy
      obtain ⟨z, u, -, -, huniq⟩ := hν c hc
      obtain ⟨-, h1⟩ := huniq x true ⟨hc, hx⟩ hTx
      obtain ⟨-, h2⟩ := huniq y false ⟨hc, hy⟩ hTy
      exact Bool.noConfusion (h1.trans h2.symm)

end SigmaOne

end Lax280166Proofs.DescriptiveComplexity


