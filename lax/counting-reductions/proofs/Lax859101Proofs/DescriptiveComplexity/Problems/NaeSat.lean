/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax859101Proofs.DescriptiveComplexity.OrderWalk
import Lax859101Proofs.DescriptiveComplexity.OccurrenceOrder
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax799700.NaeSat
end Lax799700.NaeSat

namespace Lax859101Proofs.DescriptiveComplexity.NAEProper
end Lax859101Proofs.DescriptiveComplexity.NAEProper

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SigmaSODefinable)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.NaeSat (NAEProper NAESatisfiable)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax859101Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (LitTrue OccIn)
end Lax859101Proofs.DescriptiveComplexity.SatOcc

/-!
# NAE-SAT is NP-complete

NOT-ALL-EQUAL SAT: is there a truth assignment giving every clause both a
true and a false literal? It lives on the very same vocabulary as SAT,
`FirstOrder.Language.sat`, and only its notion of satisfaction differs
(`DescriptiveComplexity.NAEProper`), so this file adds a problem rather than a
language.

NAE-SAT is the first of the Schaefer-style variants of satisfiability
([Schaefer 1978][schaefer1978complexity]) in the catalog. Their value is as
reduction *sources*: their symmetry makes gadgets far more local than SAT's,
which is what the classical reduction to Max Cut runs on.

## The symmetry, and the fresh variable

The defining feature is that `DescriptiveComplexity.NAEProper` is closed under flipping
the assignment (`DescriptiveComplexity.NAEProper.not`): swapping true and false swaps
the two conjuncts of the condition. That symmetry is exactly what the
reduction from SAT exploits. Given a CNF formula, add one fresh variable `s`
occurring positively in every clause; then a NAE-assignment can be normalized
(by flipping, if needed) to one with `s` false, and once `s` is false the “some
true literal” half is a satisfying assignment of the original formula.

“One fresh variable” is what makes this an *ordered* reduction
(`DescriptiveComplexity.sat_ordered_fo_reduction_naeSat`, tag `Bool`, dimension 1): an
interpretation adds elements only by tags, and a tag contributes a whole copy
of the universe, so the single fresh variable has to be picked out inside its
copy – as the minimum, via `DescriptiveComplexity.minF`. One fresh variable *per
clause* would not do: with its own private `s`, every clause could be
satisfied by choosing `s` opposite to one of its literals, and the reduction
would be false.

Membership reuses SAT's kernel verbatim
(`DescriptiveComplexity.realize_satKernel`): the NAE kernel is that one conjoined with
its mirror image, the clause stating that every clause also has a *false*
literal.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock BoundedFormula SatOcc

/-! ### The problem -/

section Semantics

variable {A : Type} [Lax904597.Sat.sat.Structure A]

/-- **The defining symmetry**: flipping a not-all-equal proper assignment
gives a not-all-equal proper assignment, the two halves of the condition
exchanging roles. -/
theorem NAEProper.not {ν : A → Prop} (h : Lax799700.NaeSat.NAEProper ν) : Lax799700.NaeSat.NAEProper fun x => ¬ν x := by
  intro c hc
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h c hc
  constructor
  · refine ⟨y, ?_⟩
    rcases hy with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨hp, hT⟩
    · exact Or.inr ⟨hn, not_not_intro hT⟩
  · refine ⟨x, ?_⟩
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨hp, not_not_intro hT⟩
    · exact Or.inr ⟨hn, hT⟩

end Semantics

end Lax859101Proofs.DescriptiveComplexity

namespace Lax799700.NaeSat.NAEProper

export Lax859101Proofs.DescriptiveComplexity.NAEProper (not)

end Lax799700.NaeSat.NAEProper

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock BoundedFormula SatOcc

section Semantics

variable {A : Type} [Lax904597.Sat.sat.Structure A]

/-- Occurrence form of not-all-equal properness: every clause has a true and a
false literal occurrence. -/
theorem naeProper_occ {ν : A → Prop} (h : Lax799700.NaeSat.NAEProper ν) (c : A)
    (hc : RelMap Lax904597.Sat.satIsClause ![c]) :
    (∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ Lax799700.Common.SatOcc.LitTrue ν x s) ∧ ∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ ¬Lax799700.Common.SatOcc.LitTrue ν x s := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h c hc
  constructor
  · rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨x, true, ⟨hc, hp⟩, hT⟩
    · exact ⟨x, false, ⟨hc, hn⟩, hT⟩
  · rcases hy with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨y, true, ⟨hc, hp⟩, hT⟩
    · exact ⟨y, false, ⟨hc, hn⟩, not_not_intro hT⟩

/-- Not-all-equal properness from the occurrence form. -/
theorem naeProper_of_occ {ν : A → Prop}
    (h : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] →
      (∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ Lax799700.Common.SatOcc.LitTrue ν x s) ∧ ∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ ¬Lax799700.Common.SatOcc.LitTrue ν x s) :
    Lax799700.NaeSat.NAEProper ν := by
  intro c hc
  obtain ⟨⟨x, s, hx, hT⟩, ⟨y, t, hy, hF⟩⟩ := h c hc
  constructor
  · cases s with
    | true => exact ⟨x, Or.inl ⟨hx.2, hT⟩⟩
    | false => exact ⟨x, Or.inr ⟨hx.2, hT⟩⟩
  · cases t with
    | true => exact ⟨y, Or.inl ⟨hy.2, hF⟩⟩
    | false => exact ⟨y, Or.inr ⟨hy.2, not_not.mp hF⟩⟩

end Semantics

section Problem

end Problem

section Iso

end Iso

/-! ### SAT reduces to NAE-SAT -/

/-- The “is a clause” symbol over the ordered expansion. -/
abbrev oIsClSym : (Lax904597.Sat.sat.sum Language.order).Relations 1 := Sum.inl Lax904597.Sat.satIsClause

/-- The “occurs positively in” symbol over the ordered expansion. -/
abbrev oPosSym : (Lax904597.Sat.sat.sum Language.order).Relations 2 := Sum.inl Lax904597.Sat.satPosIn

/-- The “occurs negatively in” symbol over the ordered expansion. -/
abbrev oNegSym : (Lax904597.Sat.sat.sum Language.order).Relations 2 := Sum.inl Lax904597.Sat.satNegIn

/-- The interpretation of SAT into NAE-SAT: keep the formula on the copy of
tag `true`, and let the minimum of the copy of tag `false` be a fresh variable
occurring positively in every clause. -/
noncomputable def naeInterp :
    Lax904597.Interpretations.FOInterpretation (Lax904597.Sat.sat.sum Language.order) Lax904597.Sat.sat Bool 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
        if t 0 then Relations.formula₁ oIsClSym (Term.var (0, 0)) else ⊥
    | _, .posIn => fun t =>
        if t 0 then
          (if t 1 then Relations.formula₂ oPosSym (Term.var (0, 0)) (Term.var (1, 0))
          else Relations.formula₁ oIsClSym (Term.var (0, 0)) ⊓ minF (1, 0))
        else ⊥
    | _, .negIn => fun t =>
        if t 0 then
          (if t 1 then Relations.formula₂ oNegSym (Term.var (0, 0)) (Term.var (1, 0))
          else ⊥)
        else ⊥

section Points

variable {A : Type}

/-- The copy of an element carrying the original formula. -/
def oPt (v : A) : naeInterp.Map A := (true, fun _ => v)

/-- The copy of an element carrying the fresh variable (only its minimum is
used). -/
def xPt (v : A) : naeInterp.Map A := (false, fun _ => v)

theorem oPt_eta (w : Fin 1 → A) : ((true, w) : naeInterp.Map A) = oPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

theorem xPt_eta (w : Fin 1 → A) : ((false, w) : naeInterp.Map A) = xPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

/-- Every element of the interpreted universe is a copy of an element. -/
theorem eq_oPt_or_xPt (p : naeInterp.Map A) : (∃ v, p = oPt v) ∨ ∃ v, p = xPt v := by
  rcases p with ⟨b, w⟩
  cases b
  · exact Or.inr ⟨w 0, xPt_eta w⟩
  · exact Or.inl ⟨w 0, oPt_eta w⟩

end Points

section Characterizations

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

@[simp]
theorem nae_isClause_o (v : A) :
    RelMap (M := naeInterp.Map A) Lax904597.Sat.satIsClause ![oPt v] ↔ RelMap Lax904597.Sat.satIsClause ![v] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₁]

@[simp]
theorem nae_isClause_x (v : A) :
    ¬RelMap (M := naeInterp.Map A) Lax904597.Sat.satIsClause ![xPt v] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

@[simp]
theorem nae_pos_oo (c x : A) :
    RelMap (M := naeInterp.Map A) Lax904597.Sat.satPosIn ![oPt c, oPt x] ↔ RelMap Lax904597.Sat.satPosIn ![c, x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₂]

@[simp]
theorem nae_pos_ox (c x : A) :
    RelMap (M := naeInterp.Map A) Lax904597.Sat.satPosIn ![oPt c, xPt x] ↔
      RelMap Lax904597.Sat.satIsClause ![c] ∧ ∀ a : A, x ≤ a := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, xPt, Formula.realize_rel₁, realize_minF]

@[simp]
theorem nae_pos_x (p : naeInterp.Map A) (x : A) :
    ¬RelMap (M := naeInterp.Map A) Lax904597.Sat.satPosIn ![xPt x, p] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

@[simp]
theorem nae_neg_oo (c x : A) :
    RelMap (M := naeInterp.Map A) Lax904597.Sat.satNegIn ![oPt c, oPt x] ↔ RelMap Lax904597.Sat.satNegIn ![c, x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₂]

@[simp]
theorem nae_neg_ox (c x : A) :
    ¬RelMap (M := naeInterp.Map A) Lax904597.Sat.satNegIn ![oPt c, xPt x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, xPt]

@[simp]
theorem nae_neg_x (p : naeInterp.Map A) (x : A) :
    ¬RelMap (M := naeInterp.Map A) Lax904597.Sat.satNegIn ![xPt x, p] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

end Characterizations

section Correctness

end Correctness

/-! ### Membership -/

section SigmaOne

/-- The mirror of `DescriptiveComplexity.satKernel`: every clause contains a *false*
literal. Together they say that no clause is all-equal. -/
noncomputable def naeFalseKernel : satSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ kIsClSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 0))) ⊔
            FirstOrder.Language.Relations.formula₂ kNegSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 0)))))

/-- The first-order kernel of the `Σ₁` definition of NAE-SAT: SAT's kernel
conjoined with its mirror image. -/
noncomputable def naeKernel : satSOLang.Sentence := satKernel ⊓ naeFalseKernel

theorem realize_naeFalseKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) naeFalseKernel) ↔
      ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
        (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) ∨
          (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [naeFalseKernel]
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

theorem realize_naeKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) naeKernel) ↔
      (∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
        (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
          (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x)) ∧
      ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
        (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) ∨
          (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) := by
  rw [naeKernel]
  simp only [Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_satKernel ρ) (realize_naeFalseKernel ρ)

end SigmaOne

/-! ### NP-completeness -/

end Lax859101Proofs.DescriptiveComplexity


