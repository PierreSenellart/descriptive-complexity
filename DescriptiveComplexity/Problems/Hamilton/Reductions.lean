/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Defs

/-!
# Hamilton Circuit reduces to Directed Hamilton Circuit

The undirected problem is the directed one on the *symmetrized* instance, so
the reduction between them is a one-dimensional, single-tag interpretation
that replaces each edge by its two arcs
(`DescriptiveComplexity.hamCircuit_fo_reduction_dirHamCircuit`). It is what carries
the hardness of HAMILTON CIRCUIT over to DIRECTED HAMILTON CIRCUIT, which is
why the gadget work (from Vertex Cover) only has to be done once, on the
undirected side.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace HamRed

/-- The interpretation of a digraph in a graph: the universe is unchanged and
each edge becomes a pair of opposite arcs. -/
def symInterp : FOInterpretation Language.digraph Language.digraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .arc => fun _ =>
        Relations.formula₂ dgArc (Term.var (0, 0)) (Term.var (1, 0)) ⊔
          Relations.formula₂ dgArc (Term.var (1, 0)) (Term.var (0, 0))

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

variable {A : Type} [Language.digraph.Structure A]

/-- The arcs of the interpreted structure are the edges of the original
one. -/
@[simp]
theorem sArc_iff (a b : A) : DGArc (sPt a) (sPt b) ↔ DGEdge a b := by
  rw [DGArc, sPt, sPt, FOInterpretation.relMap_map]
  simp [symInterp, DGEdge, DGArc]

/-- **Correctness**: a graph has a Hamilton circuit exactly when its
symmetrization has a directed one. -/
theorem hasHamCircuit_iff (A : Type) [Language.digraph.Structure A] :
    HasHamCircuit A ↔ HasDirHamCircuit (symInterp.Map A) := by
  constructor
  · rintro ⟨hfin, htour⟩
    exact ⟨(Equiv.finite_iff (sEquiv (A := A))).mp hfin,
      tourOn_of_equiv sEquiv (fun a a' => (sArc_iff a a').symm) htour⟩
  · rintro ⟨hfin, htour⟩
    refine ⟨(Equiv.finite_iff (sEquiv (A := A))).mpr hfin, tourOn_of_equiv sEquiv.symm ?_ htour⟩
    intro q q'
    change DGArc q q' ↔ DGEdge (q.2 0) (q'.2 0)
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
  correct A _ _ := hasHamCircuit_iff A

end DescriptiveComplexity
