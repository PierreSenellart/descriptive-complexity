/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax604544Proofs.DescriptiveComplexity.Problems.DagIso.Defs
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

namespace Lax604544.DagIsomorphism
end Lax604544.DagIsomorphism

namespace Lax604544.GraphIsomorphism
end Lax604544.GraphIsomorphism

namespace Lax799700.SubgraphIso
end Lax799700.SubgraphIso

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.GraphIsomorphism (HasDigraphIso)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.DagIsomorphism (HasDagIso TDHostArc TDHostLt TDHostV TDPatArc TDPatLt TDPatV TopoOn)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax799700.SubgraphIso (TGHostE TGHostV TGPatE TGPatV)
end Lax604544Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax604544.DagIsomorphism (tdHostArc tdHostLt tdHostV tdPatArc tdPatLt tdPatV twoDags)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.SubgraphIso (twoGraphs)
end FirstOrder.Language

/-!
# DAG Isomorphism reduces to Digraph Isomorphism

The easy half of GI-completeness, and the half that pays for the design of
`DescriptiveComplexity.Problems.DagIso.Defs`: since
`FirstOrder.Language.twoGraphs` carries two *arbitrary* binary relations –
nothing asks them to be symmetric –
`DescriptiveComplexity.DigraphIso` is already isomorphism of two directed graphs,
so a DAG instance only has to forget its two topological orders.

What it may not forget is well-formedness. The reduction is a one-dimensional,
single-tag interpretation that first tests, first-order, that both order
relations really are topological orders of their arcs
(`DescriptiveComplexity.TopoOn`, the sentence
`DescriptiveComplexity.DagIso.topoSentence`): if the test passes it copies the
two marked arc relations over, and if it fails it emits a pattern with no
vertices facing a host with all of them – no bijection, hence a no-instance,
matching the no-instance the ill-formed input is. This test is the whole reason
the instances carry their acyclicity witness: acyclicity itself is not
first-order, so no interpretation could gate on it.
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace DagIso

/-! ### The well-formedness sentence -/

/-- `Lt` is a topological order of `Arc` on `V`, as a first-order sentence
(over any variable type, so that it can be conjoined inside the defining
formulas of an interpretation): irreflexive and transitive on the marked set,
and containing the arcs. -/
noncomputable def topoIrreflClause {α : Type} (V : Lax604544.DagIsomorphism.twoDags.Relations 1)
    (Lt : Lax604544.DagIsomorphism.twoDags.Relations 2) : Lax604544.DagIsomorphism.twoDags.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.BoundedFormula.not
          (FirstOrder.Language.Relations.formula₂ Lt (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 0)))))

@[inherit_doc topoIrreflClause]
noncomputable def topoTransClause {α : Type} (V : Lax604544.DagIsomorphism.twoDags.Relations 1)
    (Lt : Lax604544.DagIsomorphism.twoDags.Relations 2) : Lax604544.DagIsomorphism.twoDags.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                  FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
              FirstOrder.Language.Relations.formula₂ Lt (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
            FirstOrder.Language.Relations.formula₂ Lt (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        (FirstOrder.Language.Relations.formula₂ Lt (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 2))))

@[inherit_doc topoIrreflClause]
noncomputable def topoMonoClause {α : Type} (V : Lax604544.DagIsomorphism.twoDags.Relations 1)
    (Lt Arc : Lax604544.DagIsomorphism.twoDags.Relations 2) : Lax604544.DagIsomorphism.twoDags.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
            FirstOrder.Language.Relations.formula₂ Arc (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1))).imp
        (FirstOrder.Language.Relations.formula₂ Lt (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

@[inherit_doc topoIrreflClause]
noncomputable def topoSentence {α : Type} (V : Lax604544.DagIsomorphism.twoDags.Relations 1)
    (Lt Arc : Lax604544.DagIsomorphism.twoDags.Relations 2) : Lax604544.DagIsomorphism.twoDags.Formula α :=
  topoIrreflClause V Lt ⊓ (topoTransClause V Lt ⊓ topoMonoClause V Lt Arc)

/-- The sentence says what it is named after. -/
theorem realize_topoSentence {A : Type} [Lax604544.DagIsomorphism.twoDags.Structure A] {α : Type} (v : α → A)
    (V : Lax604544.DagIsomorphism.twoDags.Relations 1) (Lt Arc : Lax604544.DagIsomorphism.twoDags.Relations 2) :
    (topoSentence V Lt Arc).Realize v ↔
      Lax604544.DagIsomorphism.TopoOn (fun a : A => RelMap V ![a]) (fun a b : A => RelMap Lt ![a, b])
        fun a b : A => RelMap Arc ![a, b] := by
  simp only [topoSentence, topoIrreflClause, topoTransClause, topoMonoClause, Lax604544.DagIsomorphism.TopoOn,
    Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr]
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨fun x hx => h₁ (fun _ => x) hx, fun x y z hx hy hz l₁ l₂ =>
      h₂ ![x, y, z] ⟨⟨⟨⟨hx, hy⟩, hz⟩, l₁⟩, l₂⟩, fun x y hx hy ha => h₃ ![x, y] ⟨⟨hx, hy⟩, ha⟩⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨fun i hi => h₁ (i 0) hi, fun i hi =>
      h₂ (i 0) (i 1) (i 2) hi.1.1.1.1 hi.1.1.1.2 hi.1.1.2 hi.1.2 hi.2,
      fun i hi => h₃ (i 0) (i 1) hi.1.1 hi.1.2 hi.2⟩⟩

/-- Both sides of the instance are well formed. -/
noncomputable def wfSentence {α : Type} : Lax604544.DagIsomorphism.twoDags.Formula α :=
  topoSentence Lax604544.DagIsomorphism.tdPatV Lax604544.DagIsomorphism.tdPatLt Lax604544.DagIsomorphism.tdPatArc ⊓ topoSentence Lax604544.DagIsomorphism.tdHostV Lax604544.DagIsomorphism.tdHostLt Lax604544.DagIsomorphism.tdHostArc

theorem realize_wfSentence {A : Type} [Lax604544.DagIsomorphism.twoDags.Structure A] {α : Type} (v : α → A) :
    (wfSentence.Realize v) ↔
      Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDPatV (A := A)) Lax604544.DagIsomorphism.TDPatLt Lax604544.DagIsomorphism.TDPatArc ∧ Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDHostV (A := A)) Lax604544.DagIsomorphism.TDHostLt Lax604544.DagIsomorphism.TDHostArc := by
  rw [wfSentence, Formula.realize_inf, realize_topoSentence, realize_topoSentence]
  rfl

/-! ### The interpretation -/

/-- The interpretation of DAG Isomorphism into Digraph Isomorphism: one
dimension, one tag. If the instance is well formed, the two marked arc
relations are copied verbatim – `FirstOrder.Language.twoGraphs` holds arbitrary
binary relations, so a DAG needs no encoding. If it is not, the pattern is
emptied while the host keeps every element, so the two sides cannot be
isomorphic. -/
noncomputable def dagInterp :
    Lax904597.Interpretations.FOInterpretation Lax604544.DagIsomorphism.twoDags Lax799700.SubgraphIso.twoGraphs Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun _ => wfSentence ⊓ FirstOrder.Language.Relations.formula₁ Lax604544.DagIsomorphism.tdPatV (FirstOrder.Language.Term.var (0, 0))
    | _, .hostV => fun _ => wfSentence ⊓ FirstOrder.Language.Relations.formula₁ Lax604544.DagIsomorphism.tdHostV (FirstOrder.Language.Term.var (0, 0)) ⊔
                                FirstOrder.Language.BoundedFormula.not wfSentence
    | _, .patE => fun _ => wfSentence ⊓
                               FirstOrder.Language.Relations.formula₂ Lax604544.DagIsomorphism.tdPatArc (FirstOrder.Language.Term.var (0, 0))
                                 (FirstOrder.Language.Term.var (1, 0))
    | _, .hostE => fun _ => wfSentence ⊓
                                FirstOrder.Language.Relations.formula₂ Lax604544.DagIsomorphism.tdHostArc (FirstOrder.Language.Term.var (0, 0))
                                  (FirstOrder.Language.Term.var (1, 0))

section Points

variable {A : Type}

/-- The unique copy of a vertex. -/
def dagPt (v : A) : dagInterp.Map A := ((), fun _ => v)

theorem dagPt_eta (t : Unit) (w : Fin 1 → A) : ((t, w) : dagInterp.Map A) = dagPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

/-- The map is a copy of the universe: dimension one, one tag. -/
def dagEquiv : dagInterp.Map A ≃ A where
  toFun p := p.2 0
  invFun := dagPt
  left_inv p := (dagPt_eta p.1 p.2).symm
  right_inv _ := rfl

end Points

/-! ### What the interpretation realizes -/

section Realize

variable {A : Type} [Lax604544.DagIsomorphism.twoDags.Structure A]

/-- Well-formedness is a sentence: its realization does not depend on the
valuation. -/
private theorem wf_iff {α : Type} (v : α → A) :
    (wfSentence.Realize v) ↔
      Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDPatV (A := A)) Lax604544.DagIsomorphism.TDPatLt Lax604544.DagIsomorphism.TDPatArc ∧ Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDHostV (A := A)) Lax604544.DagIsomorphism.TDHostLt Lax604544.DagIsomorphism.TDHostArc :=
  realize_wfSentence v

variable (hwf : Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDPatV (A := A)) Lax604544.DagIsomorphism.TDPatLt Lax604544.DagIsomorphism.TDPatArc ∧
  Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDHostV (A := A)) Lax604544.DagIsomorphism.TDHostLt Lax604544.DagIsomorphism.TDHostArc)

include hwf

theorem patV_map (p : dagInterp.Map A) : Lax799700.SubgraphIso.TGPatV p ↔ Lax604544.DagIsomorphism.TDPatV (dagEquiv p) := by
  rw [Lax799700.SubgraphIso.TGPatV, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(wf_iff _).mpr hwf, h⟩⟩

theorem hostV_map (p : dagInterp.Map A) : Lax799700.SubgraphIso.TGHostV p ↔ Lax604544.DagIsomorphism.TDHostV (dagEquiv p) := by
  rw [Lax799700.SubgraphIso.TGHostV, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h => h.elim (fun h => h.2) fun h => absurd ((wf_iff _).mpr hwf) h,
    fun h => Or.inl ⟨(wf_iff _).mpr hwf, h⟩⟩

theorem patE_map (p q : dagInterp.Map A) :
    Lax799700.SubgraphIso.TGPatE p q ↔ Lax604544.DagIsomorphism.TDPatArc (dagEquiv p) (dagEquiv q) := by
  rw [Lax799700.SubgraphIso.TGPatE, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_inf, Formula.realize_rel₂, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(wf_iff _).mpr hwf, h⟩⟩

theorem hostE_map (p q : dagInterp.Map A) :
    Lax799700.SubgraphIso.TGHostE p q ↔ Lax604544.DagIsomorphism.TDHostArc (dagEquiv p) (dagEquiv q) := by
  rw [Lax799700.SubgraphIso.TGHostE, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_inf, Formula.realize_rel₂, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(wf_iff _).mpr hwf, h⟩⟩

end Realize

section IllFormed

variable {A : Type} [Lax604544.DagIsomorphism.twoDags.Structure A]

/-- When the instance is ill formed, no element of the image is a pattern
vertex. -/
theorem not_patV_map_of_not_wf
    (hwf : ¬(Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDPatV (A := A)) Lax604544.DagIsomorphism.TDPatLt Lax604544.DagIsomorphism.TDPatArc ∧
      Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDHostV (A := A)) Lax604544.DagIsomorphism.TDHostLt Lax604544.DagIsomorphism.TDHostArc)) (p : dagInterp.Map A) : ¬Lax799700.SubgraphIso.TGPatV p := by
  rw [Lax799700.SubgraphIso.TGPatV, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact fun h => hwf ((realize_wfSentence _).mp h.1)

/-- When the instance is ill formed, every element of the image is a host
vertex. -/
theorem hostV_map_of_not_wf
    (hwf : ¬(Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDPatV (A := A)) Lax604544.DagIsomorphism.TDPatLt Lax604544.DagIsomorphism.TDPatArc ∧
      Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDHostV (A := A)) Lax604544.DagIsomorphism.TDHostLt Lax604544.DagIsomorphism.TDHostArc)) (p : dagInterp.Map A) : Lax799700.SubgraphIso.TGHostV p := by
  rw [Lax799700.SubgraphIso.TGHostV, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var]
  exact Or.inr fun h => hwf ((realize_wfSentence _).mp h)

end IllFormed

/-! ### Correctness -/

section Correctness

variable {A : Type} [Lax604544.DagIsomorphism.twoDags.Structure A]

/-- Correctness of the interpretation: the image is a yes-instance of Graph
Isomorphism exactly when the input is one of DAG Isomorphism. -/
theorem hasDagIso_iff_hasDigraphIso_map (A : Type) [Lax604544.DagIsomorphism.twoDags.Structure A] [Finite A]
    [Nonempty A] :
    Lax604544.DagIsomorphism.HasDagIso A ↔ Lax604544.GraphIsomorphism.HasDigraphIso (dagInterp.Map A) := by
  by_cases hwf : Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDPatV (A := A)) Lax604544.DagIsomorphism.TDPatLt Lax604544.DagIsomorphism.TDPatArc ∧
      Lax604544.DagIsomorphism.TopoOn (Lax604544.DagIsomorphism.TDHostV (A := A)) Lax604544.DagIsomorphism.TDHostLt Lax604544.DagIsomorphism.TDHostArc
  · have hiso := RelIsoOn.equiv_iff (A := A) (B := dagInterp.Map A) dagEquiv
      (patV_map hwf) (hostV_map hwf) (patE_map hwf) (hostE_map hwf)
    constructor
    · rintro ⟨-, -, -, h⟩
      exact ⟨dagInterp.map_finite A, hiso.mpr h⟩
    · rintro ⟨-, h⟩
      exact ⟨‹Finite A›, hwf.1, hwf.2, hiso.mp h⟩
  · refine ⟨fun h => absurd ⟨h.2.1, h.2.2.1⟩ hwf, fun h => absurd ?_ hwf⟩
    obtain ⟨-, f, -, -, hsurj, -⟩ := h
    obtain ⟨x, hx, -⟩ := hsurj (dagPt (Classical.arbitrary A)) (hostV_map_of_not_wf hwf _)
    exact absurd hx (not_patV_map_of_not_wf hwf x)

end Correctness

end DagIso

/-- **DAG Isomorphism FO-reduces to Digraph Isomorphism**: forget the two
topological orders, after checking first-order that they are ones. The
reduction is order-free. -/
noncomputable def dagIso_fo_reduction_digraphIso : DagIso ≤ᶠᵒ DigraphIso where
  Tag := Unit
  dim := 1
  toInterpretation := DagIso.dagInterp
  correct A _ _ _ := DagIso.hasDagIso_iff_hasDigraphIso_map A

end Lax604544Proofs.DescriptiveComplexity


