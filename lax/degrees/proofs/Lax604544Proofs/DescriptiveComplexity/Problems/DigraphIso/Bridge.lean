/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax604544Proofs.DescriptiveComplexity.Problems.DigraphIso
import Lax604544Proofs.DescriptiveComplexity.GadgetDouble
import Lax604544Proofs.DescriptiveComplexity.Degree
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
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
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

namespace Lax604544.RelationIsomorphism
end Lax604544.RelationIsomorphism

namespace Lax799700.SubgraphIso
end Lax799700.SubgraphIso

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.RelationIsomorphism (RelIsoOn)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax799700.SubgraphIso (TGHostE TGHostV TGPatE TGPatV)
end Lax604544Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.SubgraphIso (tgHostE tgHostV tgPatE tgPatV twoGraphs)
end FirstOrder.Language

/-!
# Digraph Isomorphism is the generic isomorphism problem of the graph vocabulary

`DescriptiveComplexity.DigraphIso` was stated over the hand-rolled
`FirstOrder.Language.twoGraphs` before the generic
`FirstOrder.Language.twoCopies` existed. The two vocabularies are the same up
to renaming – `patV`/`patE` against the pattern mark and the pattern copy of
`adj` – and this file proves the problems are FO-interreducible, in both
directions, by the interpretation that renames the symbols.

The payoff is
`DescriptiveComplexity.below_digraphIso_eq_below_twoCopiesIso`: the degree of
`DescriptiveComplexity.DigraphIso` *is* the degree of
`DescriptiveComplexity.TwoCopiesIso FirstOrder.Language.graph`, and hence the
GI degree. A problem stated over `twoCopies` – as every entry added from here
on is meant to be – therefore reaches the degree through
`DescriptiveComplexity.isoReflecting_fo_reduction` and this bridge, with no
further vocabulary bookkeeping.
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace DigraphBridge

/-! ### Renaming the hand-rolled vocabulary to the generic one -/

/-- The interpretation renaming `twoGraphs` to `twoCopies graph`: one tag, one
dimension, each symbol to its counterpart. -/
def toTC : Lax904597.Interpretations.FOInterpretation Lax799700.SubgraphIso.twoGraphs (Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies Language.graph) Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patMark => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.SubgraphIso.tgPatV (FirstOrder.Language.Term.var (0, 0))
    | _, .hostMark => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.SubgraphIso.tgHostV (FirstOrder.Language.Term.var (0, 0))
    | _, .pat .adj => fun _ => FirstOrder.Language.Relations.formula₂ Lax799700.SubgraphIso.tgPatE (FirstOrder.Language.Term.var (0, 0))
                                   (FirstOrder.Language.Term.var (1, 0))
    | _, .host .adj => fun _ => FirstOrder.Language.Relations.formula₂ Lax799700.SubgraphIso.tgHostE (FirstOrder.Language.Term.var (0, 0))
                                    (FirstOrder.Language.Term.var (1, 0))

/-- The interpretation renaming `twoCopies graph` back to `twoGraphs`. -/
def ofTC : Lax904597.Interpretations.FOInterpretation (Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies Language.graph) Lax799700.SubgraphIso.twoGraphs Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun _ => FirstOrder.Language.Relations.formula₁ (Lax604544Proofs.Foreign.FirstOrder.Language.tcPatMark Language.graph) (FirstOrder.Language.Term.var (0, 0))
    | _, .hostV => fun _ => FirstOrder.Language.Relations.formula₁ (Lax604544Proofs.Foreign.FirstOrder.Language.tcHostMark Language.graph) (FirstOrder.Language.Term.var (0, 0))
    | _, .patE => fun _ => FirstOrder.Language.Relations.formula₂ (Lax604544Proofs.Foreign.FirstOrder.Language.tcPat Language.adj) (FirstOrder.Language.Term.var (0, 0))
                               (FirstOrder.Language.Term.var (1, 0))
    | _, .hostE => fun _ => FirstOrder.Language.Relations.formula₂ (Lax604544Proofs.Foreign.FirstOrder.Language.tcHost Language.adj) (FirstOrder.Language.Term.var (0, 0))
                                (FirstOrder.Language.Term.var (1, 0))

/-! ### The one-dimensional universe -/

section Points

variable {A : Type}

/-- The unique copy of an element, going to the generic vocabulary. -/
def toPt (v : A) : toTC.Map A := ((), fun _ => v)

/-- The unique copy of an element, coming back. -/
def ofPt (v : A) : ofTC.Map A := ((), fun _ => v)

/-- The image universe is a copy of the original. -/
def toEquivMap : toTC.Map A ≃ A where
  toFun p := p.2 0
  invFun := toPt
  left_inv p := Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg p.2 (Subsingleton.elim 0 i)⟩
  right_inv _ := rfl

/-- The image universe is a copy of the original, coming back. -/
def ofEquivMap : ofTC.Map A ≃ A where
  toFun p := p.2 0
  invFun := ofPt
  left_inv p := Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg p.2 (Subsingleton.elim 0 i)⟩
  right_inv _ := rfl

end Points

/-! ### What the renamings realize -/

section Realize

variable {A : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A]

theorem toTC_patMark (p : toTC.Map A) :
    TCPatMark (L₁ := Language.graph) p ↔ Lax799700.SubgraphIso.TGPatV (p.2 0) := by
  rw [TCPatMark, FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₁, Lax799700.SubgraphIso.TGPatV]

theorem toTC_hostMark (p : toTC.Map A) :
    TCHostMark (L₁ := Language.graph) p ↔ Lax799700.SubgraphIso.TGHostV (p.2 0) := by
  rw [TCHostMark, FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₁, Lax799700.SubgraphIso.TGHostV]

theorem toTC_patAdj (p q : toTC.Map A) :
    RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcPat Language.adj) ![p, q] ↔ Lax799700.SubgraphIso.TGPatE (p.2 0) (q.2 0) := by
  rw [FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₂, Lax799700.SubgraphIso.TGPatE]

theorem toTC_hostAdj (p q : toTC.Map A) :
    RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcHost Language.adj) ![p, q] ↔ Lax799700.SubgraphIso.TGHostE (p.2 0) (q.2 0) := by
  rw [FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₂, Lax799700.SubgraphIso.TGHostE]

end Realize

section RealizeBack

variable {A : Type} [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies Language.graph).Structure A]

theorem ofTC_patV (p : ofTC.Map A) :
    Lax799700.SubgraphIso.TGPatV p ↔ TCPatMark (L₁ := Language.graph) (p.2 0) := by
  rw [Lax799700.SubgraphIso.TGPatV, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₁, TCPatMark]

theorem ofTC_hostV (p : ofTC.Map A) :
    Lax799700.SubgraphIso.TGHostV p ↔ TCHostMark (L₁ := Language.graph) (p.2 0) := by
  rw [Lax799700.SubgraphIso.TGHostV, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₁, TCHostMark]

theorem ofTC_patE (p q : ofTC.Map A) :
    Lax799700.SubgraphIso.TGPatE p q ↔ RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcPat Language.adj) ![p.2 0, q.2 0] := by
  rw [Lax799700.SubgraphIso.TGPatE, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₂]

theorem ofTC_hostE (p q : ofTC.Map A) :
    Lax799700.SubgraphIso.TGHostE p q ↔ RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcHost Language.adj) ![p.2 0, q.2 0] := by
  rw [Lax799700.SubgraphIso.TGHostE, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₂]

end RealizeBack

/-! ### The generic side condition, as a relation isomorphism -/

section Generic

variable {B : Type} [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies Language.graph).Structure B]

/-- The pattern relation of a `twoCopies graph`-structure. -/
def TCPatAdj (x y : B) : Prop := RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcPat Language.adj) ![x, y]

/-- The host relation of a `twoCopies graph`-structure. -/
def TCHostAdj (x y : B) : Prop := RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcHost Language.adj) ![x, y]

/-- The pattern side's adjacency, read on the ambient structure. -/
theorem patSide_relMap (a b : {x : B // TCPatMark (L₁ := Language.graph) x}) :
    RelMap (L := Language.graph) Language.adj ![a, b] ↔ TCPatAdj a.1 b.1 := by
  change RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcPat Language.adj)
    (fun i => ((![a, b] : Fin 2 → {x : B // TCPatMark (L₁ := Language.graph) x}) i).1) ↔ _
  rw [show (fun i => ((![a, b] : Fin 2 → {x : B // TCPatMark (L₁ := Language.graph) x}) i).1)
      = ![a.1, b.1] by funext i; fin_cases i <;> rfl]
  exact Iff.rfl

/-- The host side's adjacency, read on the ambient structure. -/
theorem hostSide_relMap (a b : {x : B // TCHostMark (L₁ := Language.graph) x}) :
    RelMap (L := Language.graph) Language.adj ![a, b] ↔ TCHostAdj a.1 b.1 := by
  change RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcHost Language.adj)
    (fun i => ((![a, b] : Fin 2 → {x : B // TCHostMark (L₁ := Language.graph) x}) i).1) ↔ _
  rw [show (fun i => ((![a, b] : Fin 2 → {x : B // TCHostMark (L₁ := Language.graph) x}) i).1)
      = ![a.1, b.1] by funext i; fin_cases i <;> rfl]
  exact Iff.rfl

/-- **The generic isomorphism condition is the concrete one**: an isomorphism
of the two sides, over the graph vocabulary, is a bijection of the two marks
preserving the two relations. Stated through
`DescriptiveComplexity.relIsoOn_iff_equiv`, whose right-hand side mentions no
structure, so the two presentations of a side never have to be identified as
instances. -/
theorem nonempty_tcSideEquiv_iff_relIsoOn :
    Nonempty (TCSideEquiv (L₁ := Language.graph) B) ↔
      Lax604544.RelationIsomorphism.RelIsoOn (TCPatMark (L₁ := Language.graph)) (TCHostMark (L₁ := Language.graph))
        (TCPatAdj (B := B)) TCHostAdj := by
  rw [relIsoOn_iff_equiv]
  constructor
  · rintro ⟨e⟩
    refine ⟨e.toEquiv, fun x y => ?_⟩
    have h := e.map_rel' Language.adj ![x, y]
    rw [show (e.toFun ∘ ![x, y]) = ![e.toEquiv x, e.toEquiv y] by
      funext i; fin_cases i <;> rfl, hostSide_relMap, patSide_relMap] at h
    exact h.symm
  · rintro ⟨e, hedge⟩
    refine ⟨{ toEquiv := e, map_fun' := fun f => isEmptyElim f, map_rel' := ?_ }⟩
    intro n r x
    cases r
    rw [show x = ![x 0, x 1] by funext i; fin_cases i <;> rfl]
    rw [show (e.toFun ∘ ![x 0, x 1]) = ![e.toFun (x 0), e.toFun (x 1)] by
      funext i; fin_cases i <;> rfl, hostSide_relMap, patSide_relMap]
    exact (hedge (x 0) (x 1)).symm

end Generic

/-! ### Correctness of the two renamings -/

section Correctness

/-- Going to the generic vocabulary preserves the answer. -/
theorem toTC_correct (A : Type) [Lax799700.SubgraphIso.twoGraphs.Structure A] [Finite A] :
    DigraphIso.Holds A ↔ (TwoCopiesIso Language.graph).Holds (toTC.Map A) := by
  have hrel : Lax604544.RelationIsomorphism.RelIsoOn (TCPatMark (L₁ := Language.graph)) TCHostMark
      (TCPatAdj (B := toTC.Map A)) TCHostAdj ↔
      Lax604544.RelationIsomorphism.RelIsoOn (Lax799700.SubgraphIso.TGPatV (A := A)) Lax799700.SubgraphIso.TGHostV Lax799700.SubgraphIso.TGPatE Lax799700.SubgraphIso.TGHostE :=
    RelIsoOn.equiv_iff toEquivMap (fun p => toTC_patMark p) (fun p => toTC_hostMark p)
      (fun p q => toTC_patAdj p q) fun p q => toTC_hostAdj p q
  constructor
  · rintro ⟨-, h⟩
    exact ⟨toTC.map_finite A,
      (nonempty_tcSideEquiv_iff_relIsoOn).mpr (hrel.mpr h)⟩
  · rintro ⟨-, h⟩
    exact ⟨‹Finite A›, hrel.mp ((nonempty_tcSideEquiv_iff_relIsoOn).mp h)⟩

/-- Coming back preserves the answer. -/
theorem ofTC_correct (A : Type) [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies Language.graph).Structure A] [Finite A] :
    (TwoCopiesIso Language.graph).Holds A ↔ DigraphIso.Holds (ofTC.Map A) := by
  have hrel : Lax604544.RelationIsomorphism.RelIsoOn (Lax799700.SubgraphIso.TGPatV (A := ofTC.Map A)) Lax799700.SubgraphIso.TGHostV Lax799700.SubgraphIso.TGPatE Lax799700.SubgraphIso.TGHostE ↔
      Lax604544.RelationIsomorphism.RelIsoOn (TCPatMark (L₁ := Language.graph)) TCHostMark (TCPatAdj (B := A)) TCHostAdj :=
    RelIsoOn.equiv_iff ofEquivMap (fun p => ofTC_patV p) (fun p => ofTC_hostV p)
      (fun p q => ofTC_patE p q) fun p q => ofTC_hostE p q
  constructor
  · rintro ⟨-, h⟩
    exact ⟨ofTC.map_finite A, hrel.mpr ((nonempty_tcSideEquiv_iff_relIsoOn).mp h)⟩
  · rintro ⟨-, h⟩
    exact ⟨‹Finite A›, (nonempty_tcSideEquiv_iff_relIsoOn).mpr (hrel.mp h)⟩

end Correctness

end DigraphBridge

/-! ### The two reductions, and the degree -/

/-- **Digraph Isomorphism reduces to the generic isomorphism problem** of the
graph vocabulary, by renaming the symbols. -/
def digraphIso_fo_reduction_twoCopiesIso : DigraphIso ≤ᶠᵒ TwoCopiesIso Language.graph where
  Tag := Unit
  dim := 1
  toInterpretation := DigraphBridge.toTC
  correct A _ _ _ := DigraphBridge.toTC_correct A

end Lax604544Proofs.DescriptiveComplexity


