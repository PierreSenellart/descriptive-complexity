/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax859101Proofs.DescriptiveComplexity.Block
import Lax859101Proofs.DescriptiveComplexity.Composition
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.FromSat
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.Reductions
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax859101Proofs.DescriptiveComplexity.Problems.SetFamily.Defs
import Lax859101Proofs.DescriptiveComplexity.Problems.SetFamily.Membership
import Lax859101Proofs.DescriptiveComplexity.SecondOrder
import Lax859101Proofs.DescriptiveComplexity.OccurrenceFormulas
import Lax859101Proofs.DescriptiveComplexity.Problems.NaeSat
import Lax859101Proofs.DescriptiveComplexity.Problems.ThreeSat.Defs
import Lax859101Proofs.DescriptiveComplexity.Problems.ThreeSat.ToSat
import Lax859101Proofs.DescriptiveComplexity.Problems.ThreeSat.ToSat
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

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.SetFamily (HasSetSplitting SSElem SSFam SSMem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.NaeSat (NAESatisfiable)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem)
end FirstOrder.Language

namespace Lax859101Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue OccIn)
end Lax859101Proofs.DescriptiveComplexity.SatOcc

/-!
# Set Splitting is NP-complete

SET SPLITTING, also known as hypergraph 2-colorability: can the ground
elements of a set system be colored with two colors so that no set of the
family is monochromatic? Like Exact Cover it lives on
`FirstOrder.Language.setSystem` unchanged (`DescriptiveComplexity.SetSplitting`,
`DescriptiveComplexity.Problems.SetFamily.Defs`) and carries no threshold – the
coloring, not a cardinality, is the whole question.

Hardness comes from NAE-SAT (`DescriptiveComplexity.Problems.NaeSat`) by a reduction
with **no gadget and no counting**, order-free and of dimension 1:

* the ground elements are the *literals* `(x, s)`;
* the family has one set `{x, ¬x}` per variable, and one set per clause,
  holding its literals.

A two-coloring splits the pair `{x, ¬x}` exactly when it gives the two
literals of `x` opposite colors – that *is* a truth assignment – and it
splits a clause set exactly when the clause has both a true and a false
literal, which is not-all-equal satisfaction. The correspondence is so direct
that the reduction is essentially the identity on clauses; only the pair sets
are new, and they are what turns an arbitrary coloring into an assignment.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

namespace SetSplitRed

open Language Structure SatOcc

/-- Tags of the reduction: the ground element of a literal, the set of a
variable, and the set of a clause. -/
inductive SplTag : Type
  /-- The ground element of the literal `(x, s)`. -/
  | lit (s : Bool)
  /-- The set `{x, ¬x}` of the variable `x`. -/
  | pairSet
  /-- The set of the literals of a clause. -/
  | clSet
  deriving DecidableEq

instance : Fintype SplTag where
  elems := {SplTag.lit true, SplTag.lit false, SplTag.pairSet, SplTag.clSet}
  complete := by
    intro t
    cases t with
    | lit s => cases s <;> decide
    | pairSet => decide
    | clSet => decide

instance : Nonempty SplTag := ⟨SplTag.pairSet⟩

/-! ### The interpretation -/

/-- Defining formula for the ground elements: the literals. -/
noncomputable def elemF : SplTag → Lax904597.Sat.sat.Formula (Fin 1 × Fin 1)
  | .lit _ => ⊤
  | _ => ⊥

/-- Defining formula for the family: one set per variable and one per
clause. -/
noncomputable def famF : SplTag → Lax904597.Sat.sat.Formula (Fin 1 × Fin 1)
  | .pairSet => ⊤
  | .clSet => ThreeSatToSat.clF (0, 0)
  | .lit _ => ⊥

/-- Defining formula for incidence: the pair set of `x` holds both literals of
`x`, and the set of a clause holds the literals occurring in it. -/
noncomputable def memF : SplTag → SplTag → Lax904597.Sat.sat.Formula (Fin 2 × Fin 1)
  | .lit _, .pairSet => ThreeSatToSat.eqF (0, 0) (1, 0)
  | .lit s, .clSet => ThreeSatToSat.occF s (1, 0) (0, 0)
  | _, _ => ⊥

/-- The interpretation of Set Splitting instances in CNF instances. -/
noncomputable def splInterp : Lax904597.Interpretations.FOInterpretation Lax904597.Sat.sat Lax799700.SetFamily.setSystem SplTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .elem => fun t => elemF (t 0)
    | _, .fam => fun t => famF (t 0)
    | _, .mem => fun t => memF (t 0) (t 1)
    | _, .marked => fun _ => ⊥

/-! ### The points -/

section Points

variable {A : Type}

/-- The point of tag `t` over the element `x`. -/
def splPt (t : SplTag) (x : A) : splInterp.Map A := (t, fun _ => x)

theorem splPt_eq_iff {t t' : SplTag} {x x' : A} :
    splPt t x = splPt t' x' ↔ t = t' ∧ x = x' := by
  constructor
  · intro h
    exact ⟨by simpa [splPt] using congrArg (fun p : splInterp.Map A => p.1) h,
      by simpa [splPt] using congrArg (fun p : splInterp.Map A => p.2 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem splPt_surj (q : splInterp.Map A) : ∃ t x, q = splPt t x :=
  ⟨q.1, q.2 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg q.2 (Subsingleton.elim i 0)⟩⟩

end Points

/-! ### Characterization of the four relations -/

section Characterizations

variable {A : Type} [Lax904597.Sat.sat.Structure A]

@[simp]
theorem ssElem_lit (s : Bool) (x : A) : Lax799700.SetFamily.SSElem (splPt (.lit s) x) := by
  rw [Lax799700.SetFamily.SSElem, splPt, FOInterpretation.relMap_map]
  simp [splInterp, elemF]

@[simp]
theorem ssElem_pairSet (x : A) : ¬Lax799700.SetFamily.SSElem (splPt .pairSet x) := by
  rw [Lax799700.SetFamily.SSElem, splPt, FOInterpretation.relMap_map]
  simp [splInterp, elemF]

@[simp]
theorem ssElem_clSet (x : A) : ¬Lax799700.SetFamily.SSElem (splPt .clSet x) := by
  rw [Lax799700.SetFamily.SSElem, splPt, FOInterpretation.relMap_map]
  simp [splInterp, elemF]

@[simp]
theorem ssFam_pairSet (x : A) : Lax799700.SetFamily.SSFam (splPt .pairSet x) := by
  rw [Lax799700.SetFamily.SSFam, splPt, FOInterpretation.relMap_map]
  simp [splInterp, famF]

@[simp]
theorem ssFam_clSet (c : A) : Lax799700.SetFamily.SSFam (splPt .clSet c) ↔ Lax799700.Common.SatOcc.IsCl c := by
  rw [Lax799700.SetFamily.SSFam, splPt, FOInterpretation.relMap_map]
  simp [splInterp, famF, ThreeSatToSat.realize_clF, Lax799700.Common.SatOcc.IsCl]

@[simp]
theorem ssFam_lit (s : Bool) (x : A) : ¬Lax799700.SetFamily.SSFam (splPt (.lit s) x) := by
  rw [Lax799700.SetFamily.SSFam, splPt, FOInterpretation.relMap_map]
  simp [splInterp, famF]

@[simp]
theorem ssMem_lit_pairSet (s : Bool) (x y : A) :
    Lax799700.SetFamily.SSMem (splPt (.lit s) x) (splPt .pairSet y) ↔ x = y := by
  rw [Lax799700.SetFamily.SSMem, splPt, splPt, FOInterpretation.relMap_map]
  simp [splInterp, memF, ThreeSatToSat.realize_eqF]

@[simp]
theorem ssMem_lit_clSet (s : Bool) (x c : A) :
    Lax799700.SetFamily.SSMem (splPt (.lit s) x) (splPt .clSet c) ↔ Lax799700.Common.SatOcc.OccIn c x s := by
  rw [Lax799700.SetFamily.SSMem, splPt, splPt, FOInterpretation.relMap_map]
  simp [splInterp, memF, ThreeSatToSat.realize_occF]

/-- The ground elements are exactly the literals. -/
theorem ssElem_cases {q : splInterp.Map A} (h : Lax799700.SetFamily.SSElem q) : ∃ s x, q = splPt (.lit s) x := by
  obtain ⟨t, x, rfl⟩ := splPt_surj q
  cases t with
  | lit s => exact ⟨s, x, rfl⟩
  | pairSet => exact absurd h (ssElem_pairSet x)
  | clSet => exact absurd h (ssElem_clSet x)

/-- The sets of the family are the pair sets and the clause sets. -/
theorem ssFam_cases {q : splInterp.Map A} (h : Lax799700.SetFamily.SSFam q) :
    (∃ x, q = splPt .pairSet x) ∨ ∃ c, Lax799700.Common.SatOcc.IsCl c ∧ q = splPt .clSet c := by
  obtain ⟨t, x, rfl⟩ := splPt_surj q
  cases t with
  | lit s => exact absurd h (ssFam_lit s x)
  | pairSet => exact Or.inl ⟨x, rfl⟩
  | clSet => exact Or.inr ⟨x, (ssFam_clSet x).mp h, rfl⟩

end Characterizations

/-! ### Correctness -/

section Correctness

end Correctness

end SetSplitRed

/-! ### NP-completeness -/

end Lax859101Proofs.DescriptiveComplexity


