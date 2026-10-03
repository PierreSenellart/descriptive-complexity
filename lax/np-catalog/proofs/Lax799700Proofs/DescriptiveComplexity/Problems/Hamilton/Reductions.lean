/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.Hamilton.Defs
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
# Hamilton Circuit reduces to Directed Hamilton Circuit

The undirected problem is the directed one on the *symmetrized* instance, so
the reduction between them is a one-dimensional, single-tag interpretation
that replaces each edge by its two arcs
(`Lax799700Proofs.DescriptiveComplexity.hamCircuit_fo_reduction_dirHamCircuit`). It is what carries
the hardness of HAMILTON CIRCUIT over to DIRECTED HAMILTON CIRCUIT, which is
why the gadget work (from Vertex Cover) only has to be done once, on the
undirected side.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace HamRed

/-- The interpretation of a digraph in a graph: the universe is unchanged and
each edge becomes a pair of opposite arcs. -/
def symInterp : Lax904597.Interpretations.FOInterpretation Lax799700.Hamilton.digraph Lax799700.Hamilton.digraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .arc => fun _ => FirstOrder.Language.Relations.formula₂ Lax799700.Hamilton.dgArc (FirstOrder.Language.Term.var (0, 0))
                                (FirstOrder.Language.Term.var (1, 0)) ⊔
                              FirstOrder.Language.Relations.formula₂ Lax799700.Hamilton.dgArc (FirstOrder.Language.Term.var (1, 0))
                                (FirstOrder.Language.Term.var (0, 0))

section Points

variable {A : Type}

/-- The point of the interpreted structure over `a`. -/
def sPt (a : A) : symInterp.Map A := ((), fun _ => a)

/-- The interpreted universe is a copy of the original one. -/
def sEquiv : A ≃ symInterp.Map A := (symInterp.mapEquivSelf A).symm

@[simp]
theorem sEquiv_apply (a : A) : sEquiv a = sPt a := rfl

theorem sPt_surj (q : symInterp.Map A) : q = sPt (q.2 0) :=
  (symInterp.mapEquivSelf A).symm_apply_apply q ▸ rfl

end Points

variable {A : Type} [Lax799700.Hamilton.digraph.Structure A]

/-- The arcs of the interpreted structure are the edges of the original
one. -/
@[simp]
theorem sArc_iff (a b : A) : Lax799700.Hamilton.DGArc (sPt a) (sPt b) ↔ Lax799700.Hamilton.DGEdge a b := by
  rw [Lax799700.Hamilton.DGArc, sPt, sPt, FOInterpretation.relMap_map]
  simp [symInterp, Lax799700.Hamilton.DGEdge, Lax799700.Hamilton.DGArc]

/-- **Correctness**: a graph has a Hamilton circuit exactly when its
symmetrization has a directed one. -/
theorem hasHamCircuit_iff (A : Type) [Lax799700.Hamilton.digraph.Structure A] :
    Lax799700.Hamilton.HasHamCircuit A ↔ Lax799700.Hamilton.HasDirHamCircuit (symInterp.Map A) := by
  constructor
  · rintro ⟨hfin, htour⟩
    exact ⟨(Equiv.finite_iff (sEquiv (A := A))).mp hfin,
      tourOn_of_equiv sEquiv (fun a a' => (sArc_iff a a').symm) htour⟩
  · rintro ⟨hfin, htour⟩
    refine ⟨(Equiv.finite_iff (sEquiv (A := A))).mpr hfin, tourOn_of_equiv sEquiv.symm ?_ htour⟩
    intro q q'
    change Lax799700.Hamilton.DGArc q q' ↔ Lax799700.Hamilton.DGEdge (q.2 0) (q'.2 0)
    conv_lhs => rw [sPt_surj q, sPt_surj q']
    exact sArc_iff _ _

end HamRed

open HamRed in
/-- **HAMILTON CIRCUIT FO-reduces to DIRECTED HAMILTON CIRCUIT**: replace each
edge by its two arcs, the universe unchanged. -/
def hamCircuit_fo_reduction_dirHamCircuit : HamCircuit ≤ᶠᵒ DirHamCircuit where
  Tag := Unit
  dim := 1
  toInterpretation := symInterp
  correct A _ _ _ := hasHamCircuit_iff A

end Lax799700Proofs.DescriptiveComplexity


