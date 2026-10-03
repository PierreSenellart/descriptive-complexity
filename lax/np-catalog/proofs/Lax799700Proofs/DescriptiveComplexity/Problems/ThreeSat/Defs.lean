/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.OccurrenceOrder
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

/-!
# 3SAT: definition

The problem 3SAT, over the same vocabulary `FirstOrder.Language.sat` as SAT: a
CNF structure is a yes-instance iff every clause has at most three literal
occurrences (`Lax799700Proofs.DescriptiveComplexity.WidthAtMostThree`) *and* the CNF is satisfiable
(`Lax799700Proofs.DescriptiveComplexity.ThreeSatisfiable`, bundled as `Lax799700Proofs.DescriptiveComplexity.ThreeSAT`).

Folding the width bound into the yes-instances (rather than into the
vocabulary) is what makes 3SAT a decision problem on arbitrary
`Language.sat`-structures; the bound “at most three” is expressed without
counting, as: among any four literal occurrences of a clause, two coincide.

The reductions to and from SAT, and NP-completeness, are in
`Lax799700Proofs.DescriptiveComplexity.Problems.ThreeSat`.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

section ThreeSat

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end ThreeSat

section Iso

/-- Isomorphisms preserve literal occurrences. -/
private theorem occIn_map {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) {c x : A} {s : Bool} (h : Lax799700.Common.SatOcc.OccIn c x s) : Lax799700.Common.SatOcc.OccIn (e c) (e x) s := by
  obtain ⟨hc, hs⟩ := h
  constructor
  · exact (relMap_equiv₁ e Lax904597.Sat.satIsClause c).mp hc
  · cases s with
    | false => exact (relMap_equiv₂ e Lax904597.Sat.satNegIn c x).mp hs
    | true => exact (relMap_equiv₂ e Lax904597.Sat.satPosIn c x).mp hs

private theorem widthAtMostThree_of_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) (h : Lax799700.ThreeSat.WidthAtMostThree A) :
    Lax799700.ThreeSat.WidthAtMostThree B := by
  intro c x s hocc
  obtain ⟨i, j, hij, hx, hs⟩ :=
    h (e.symm c) (fun i => e.symm (x i)) s fun i => occIn_map e.symm (hocc i)
  refine ⟨i, j, hij, ?_, hs⟩
  have := congrArg e hx
  simpa using this

/-- The width bound is isomorphism-invariant. -/
theorem widthAtMostThree_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) :
    Lax799700.ThreeSat.WidthAtMostThree A ↔ Lax799700.ThreeSat.WidthAtMostThree B :=
  ⟨widthAtMostThree_of_iso e, widthAtMostThree_of_iso e.symm⟩

/-- 3-satisfiability is isomorphism-invariant. -/
theorem threeSatisfiable_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) :
    Lax799700.ThreeSat.ThreeSatisfiable A ↔ Lax799700.ThreeSat.ThreeSatisfiable B :=
  and_congr (widthAtMostThree_iso e) (satisfiable_iso e)

end Iso

/-- 3SAT, as a problem on `Language.sat`-structures: the same vocabulary as
SAT, with the width bound folded into the yes-instances. -/
def ThreeSAT : Lax904597.Problems.DecisionProblem Lax904597.Sat.sat where
  Holds := fun A inst => @Lax799700.ThreeSat.ThreeSatisfiable A inst
  iso_invariant := fun e => threeSatisfiable_iso e

end Lax799700Proofs.DescriptiveComplexity


