/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax604544Proofs.DescriptiveComplexity.Problems.DigraphIso
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

namespace Lax604544.GraphIsomorphism
end Lax604544.GraphIsomorphism

namespace Lax604544.RelationIsomorphism
end Lax604544.RelationIsomorphism

namespace Lax604544Proofs.DescriptiveComplexity.SimpleOn
end Lax604544Proofs.DescriptiveComplexity.SimpleOn

namespace Lax799700.SubgraphIso
end Lax799700.SubgraphIso

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.RelationIsomorphism (RelIsoOn)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.GraphIsomorphism (HasDigraphIso HasGraphIso SimpleOn)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
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
# Graph Isomorphism: vocabulary, semantics, and membership in the GI degree

GRAPH ISOMORPHISM, as the literature means it: are the two *simple* graphs of
the instance isomorphic? `DescriptiveComplexity.DigraphIso` is the same
question over `FirstOrder.Language.twoGraphs` with no condition on the two
binary relations, hence for directed graphs; this problem is that one
restricted to instances whose relations are symmetric and irreflexive.

Unlike acyclicity (`DescriptiveComplexity.Problems.DagIso`), that restriction
*is* first-order, so nothing has to be carried by the instance: the reduction
into `DigraphIso` simply tests it. This file also **defines the GI degree**
(`DescriptiveComplexity.GI`), on this problem: it is what the literature means
by graph isomorphism, so it is what the degree should be named after. The
directed problem is complete for it too – the two are interreducible – but that
needs the gadget of `DescriptiveComplexity.Problems.GraphIso.Hardness`, so it is
proved there.
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic property -/

section Generic

variable {A : Type}

variable {B : Type}

/-- `SimpleOn` transports along an equivalence commuting with the two
predicates. -/
theorem SimpleOn.of_equiv (u : B ≃ A) {VB : B → Prop} {EB : B → B → Prop}
    {VA : A → Prop} {EA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hE : ∀ b b', EB b b' ↔ EA (u b) (u b'))
    (h : Lax604544.GraphIsomorphism.SimpleOn VB EB) : Lax604544.GraphIsomorphism.SimpleOn VA EA := by
  obtain ⟨hsymm, hirr⟩ := h
  refine ⟨fun x y hx hy hxy => ?_, fun x hx hxx => ?_⟩
  · have := hsymm (u.symm x) (u.symm y) ((hV _).mpr (by simpa using hx))
      ((hV _).mpr (by simpa using hy)) ((hE _ _).mpr (by simpa using hxy))
    simpa using (hE (u.symm y) (u.symm x)).mp this
  · exact hirr (u.symm x) ((hV _).mpr (by simpa using hx)) ((hE _ _).mpr (by simpa using hxx))

end Generic

end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544.GraphIsomorphism.SimpleOn

export Lax604544Proofs.DescriptiveComplexity.SimpleOn (of_equiv)

end Lax604544.GraphIsomorphism.SimpleOn

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `SimpleOn` transports along an equivalence, iff version. -/
theorem SimpleOn.equiv_iff (u : B ≃ A) {VB : B → Prop} {EB : B → B → Prop}
    {VA : A → Prop} {EA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hE : ∀ b b', EB b b' ↔ EA (u b) (u b')) :
    Lax604544.GraphIsomorphism.SimpleOn VB EB ↔ Lax604544.GraphIsomorphism.SimpleOn VA EA :=
  ⟨SimpleOn.of_equiv u hV hE,
    SimpleOn.of_equiv u.symm (fun a => by rw [hV]; simp) fun a a' => by rw [hE]; simp⟩

end Generic

end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544.GraphIsomorphism.SimpleOn

export Lax604544Proofs.DescriptiveComplexity.SimpleOn (equiv_iff)

end Lax604544.GraphIsomorphism.SimpleOn

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

end Generic

/-! ### The problem -/

section Problem

variable (A : Type) [Lax799700.SubgraphIso.twoGraphs.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A] [Lax799700.SubgraphIso.twoGraphs.Structure B]

/-- The graph-isomorphism property is isomorphism-invariant. -/
theorem hasGraphIso_iso (e : A ≃[Lax799700.SubgraphIso.twoGraphs] B) :
    Lax604544.GraphIsomorphism.HasGraphIso A ↔ Lax604544.GraphIsomorphism.HasGraphIso B :=
  and_congr e.toEquiv.finite_iff
    (and_congr
      (SimpleOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e Lax799700.SubgraphIso.tgPatV a)
        fun a b => relMap_equiv₂ e Lax799700.SubgraphIso.tgPatE a b)
      (and_congr
        (SimpleOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e Lax799700.SubgraphIso.tgHostV a)
          fun a b => relMap_equiv₂ e Lax799700.SubgraphIso.tgHostE a b)
        (RelIsoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e Lax799700.SubgraphIso.tgPatV a)
          (fun a => relMap_equiv₁ e Lax799700.SubgraphIso.tgHostV a) (fun a b => relMap_equiv₂ e Lax799700.SubgraphIso.tgPatE a b)
          fun a b => relMap_equiv₂ e Lax799700.SubgraphIso.tgHostE a b)))

end Iso

/-- GRAPH ISOMORPHISM: are the two marked *simple* graphs isomorphic?
Simplicity is part of the yes-condition, and is first-order, so a reduction can
test it – unlike acyclicity in `DescriptiveComplexity.DagIso`, which has to be
carried by the instance. -/
def GraphIso : Lax904597.Problems.DecisionProblem Lax799700.SubgraphIso.twoGraphs where
  Holds := fun A inst => @Lax604544.GraphIsomorphism.HasGraphIso A inst
  iso_invariant := fun e => hasGraphIso_iso e

/-! ### Membership: forget nothing, just check simplicity -/

namespace GraphIso

/-- `E` is symmetric and irreflexive on `V`, as a first-order sentence over any
variable type, so that it can be conjoined inside the defining formulas of an
interpretation. -/
noncomputable def simpleSentence {α : Type} (V : Lax799700.SubgraphIso.twoGraphs.Relations 1)
    (E : Lax799700.SubgraphIso.twoGraphs.Relations 2) : Lax799700.SubgraphIso.twoGraphs.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
        ((FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              FirstOrder.Language.Relations.formula₂ E (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          (FirstOrder.Language.Relations.formula₂ E (FirstOrder.Language.Term.var (Sum.inr 1))
            (FirstOrder.Language.Term.var (Sum.inr 0)))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 1)
        ((FirstOrder.Language.Relations.formula₁ V (FirstOrder.Language.Term.var (Sum.inr 0))).imp
          (FirstOrder.Language.BoundedFormula.not
            (FirstOrder.Language.Relations.formula₂ E (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 0)))))

theorem realize_simpleSentence {A : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A] {α : Type}
    (v : α → A) (V : Lax799700.SubgraphIso.twoGraphs.Relations 1) (E : Lax799700.SubgraphIso.twoGraphs.Relations 2) :
    (simpleSentence V E).Realize v ↔
      Lax604544.GraphIsomorphism.SimpleOn (fun a : A => RelMap V ![a]) fun a b : A => RelMap E ![a, b] := by
  simp only [simpleSentence, Lax604544.GraphIsomorphism.SimpleOn, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun x y hx hy hxy => h₁ ![x, y] ⟨⟨hx, hy⟩, hxy⟩,
      fun x hx => h₂ (fun _ => x) hx⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun i hi => h₁ (i 0) (i 1) hi.1.1 hi.1.2 hi.2, fun i hi => h₂ (i 0) hi⟩⟩

/-- Both sides of the instance are simple graphs. -/
noncomputable def wfSentence {α : Type} : Lax799700.SubgraphIso.twoGraphs.Formula α :=
  simpleSentence Lax799700.SubgraphIso.tgPatV Lax799700.SubgraphIso.tgPatE ⊓ simpleSentence Lax799700.SubgraphIso.tgHostV Lax799700.SubgraphIso.tgHostE

theorem realize_wfSentence {A : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A] {α : Type} (v : α → A) :
    (wfSentence.Realize v) ↔
      Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGPatV (A := A)) Lax799700.SubgraphIso.TGPatE ∧ Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGHostV (A := A)) Lax799700.SubgraphIso.TGHostE := by
  rw [wfSentence, Formula.realize_inf, realize_simpleSentence, realize_simpleSentence]
  rfl

/-- The interpretation of Graph Isomorphism into Digraph Isomorphism: copy both
marked graphs if they are simple, and otherwise emit a pattern with no vertices
facing a host with all of them. -/
noncomputable def simpleInterp :
    Lax904597.Interpretations.FOInterpretation Lax799700.SubgraphIso.twoGraphs Lax799700.SubgraphIso.twoGraphs Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun _ => wfSentence ⊓ FirstOrder.Language.Relations.formula₁ Lax799700.SubgraphIso.tgPatV (FirstOrder.Language.Term.var (0, 0))
    | _, .hostV => fun _ => wfSentence ⊓ FirstOrder.Language.Relations.formula₁ Lax799700.SubgraphIso.tgHostV (FirstOrder.Language.Term.var (0, 0)) ⊔
                                FirstOrder.Language.BoundedFormula.not wfSentence
    | _, .patE => fun _ => wfSentence ⊓
                               FirstOrder.Language.Relations.formula₂ Lax799700.SubgraphIso.tgPatE (FirstOrder.Language.Term.var (0, 0))
                                 (FirstOrder.Language.Term.var (1, 0))
    | _, .hostE => fun _ => wfSentence ⊓
                                FirstOrder.Language.Relations.formula₂ Lax799700.SubgraphIso.tgHostE (FirstOrder.Language.Term.var (0, 0))
                                  (FirstOrder.Language.Term.var (1, 0))

section Points

variable {A : Type}

/-- The unique copy of a vertex. -/
def uPt (v : A) : simpleInterp.Map A := ((), fun _ => v)

theorem uPt_eta (t : Unit) (w : Fin 1 → A) : ((t, w) : simpleInterp.Map A) = uPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

/-- The map is a copy of the universe: dimension one, one tag. -/
def uEquiv : simpleInterp.Map A ≃ A where
  toFun p := p.2 0
  invFun := uPt
  left_inv p := (uPt_eta p.1 p.2).symm
  right_inv _ := rfl

end Points

section Realize

variable {A : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A]

variable (hwf : Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGPatV (A := A)) Lax799700.SubgraphIso.TGPatE ∧ Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGHostV (A := A)) Lax799700.SubgraphIso.TGHostE)

include hwf

theorem patV_map (p : simpleInterp.Map A) : Lax799700.SubgraphIso.TGPatV p ↔ Lax799700.SubgraphIso.TGPatV (uEquiv p) := by
  rw [Lax799700.SubgraphIso.TGPatV, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(realize_wfSentence _).mpr hwf, h⟩⟩

theorem hostV_map (p : simpleInterp.Map A) : Lax799700.SubgraphIso.TGHostV p ↔ Lax799700.SubgraphIso.TGHostV (uEquiv p) := by
  rw [Lax799700.SubgraphIso.TGHostV, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h => h.elim (fun h => h.2) fun h => absurd ((realize_wfSentence _).mpr hwf) h,
    fun h => Or.inl ⟨(realize_wfSentence _).mpr hwf, h⟩⟩

theorem patE_map (p q : simpleInterp.Map A) :
    Lax799700.SubgraphIso.TGPatE p q ↔ Lax799700.SubgraphIso.TGPatE (uEquiv p) (uEquiv q) := by
  rw [Lax799700.SubgraphIso.TGPatE, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_inf, Formula.realize_rel₂, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(realize_wfSentence _).mpr hwf, h⟩⟩

theorem hostE_map (p q : simpleInterp.Map A) :
    Lax799700.SubgraphIso.TGHostE p q ↔ Lax799700.SubgraphIso.TGHostE (uEquiv p) (uEquiv q) := by
  rw [Lax799700.SubgraphIso.TGHostE, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_inf, Formula.realize_rel₂, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(realize_wfSentence _).mpr hwf, h⟩⟩

end Realize

section IllFormed

variable {A : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A]

theorem not_patV_map_of_not_wf
    (hwf : ¬(Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGPatV (A := A)) Lax799700.SubgraphIso.TGPatE ∧ Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGHostV (A := A)) Lax799700.SubgraphIso.TGHostE))
    (p : simpleInterp.Map A) : ¬Lax799700.SubgraphIso.TGPatV p := by
  rw [Lax799700.SubgraphIso.TGPatV, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact fun h => hwf ((realize_wfSentence _).mp h.1)

theorem hostV_map_of_not_wf
    (hwf : ¬(Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGPatV (A := A)) Lax799700.SubgraphIso.TGPatE ∧ Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGHostV (A := A)) Lax799700.SubgraphIso.TGHostE))
    (p : simpleInterp.Map A) : Lax799700.SubgraphIso.TGHostV p := by
  rw [Lax799700.SubgraphIso.TGHostV, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var]
  exact Or.inr fun h => hwf ((realize_wfSentence _).mp h)

end IllFormed

section Correctness

/-- Correctness: the image is a yes-instance of Digraph Isomorphism exactly
when the input is one of Graph Isomorphism. -/
theorem hasGraphIso_iff_hasDigraphIso_map (A : Type) [Lax799700.SubgraphIso.twoGraphs.Structure A] [Finite A]
    [Nonempty A] :
    Lax604544.GraphIsomorphism.HasGraphIso A ↔ Lax604544.GraphIsomorphism.HasDigraphIso (simpleInterp.Map A) := by
  by_cases hwf : Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGPatV (A := A)) Lax799700.SubgraphIso.TGPatE ∧ Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGHostV (A := A)) Lax799700.SubgraphIso.TGHostE
  · have hiso := RelIsoOn.equiv_iff (A := A) (B := simpleInterp.Map A) uEquiv
      (patV_map hwf) (hostV_map hwf) (patE_map hwf) (hostE_map hwf)
    constructor
    · rintro ⟨-, -, -, h⟩
      exact ⟨simpleInterp.map_finite A, hiso.mpr h⟩
    · rintro ⟨-, h⟩
      exact ⟨‹Finite A›, hwf.1, hwf.2, hiso.mp h⟩
  · refine ⟨fun h => absurd ⟨h.2.1, h.2.2.1⟩ hwf, fun h => absurd ?_ hwf⟩
    obtain ⟨-, f, -, -, hsurj, -⟩ := h
    obtain ⟨x, hx, -⟩ := hsurj (uPt (Classical.arbitrary A)) (hostV_map_of_not_wf hwf _)
    exact absurd hx (not_patV_map_of_not_wf hwf x)

end Correctness

end GraphIso

/-- **Graph Isomorphism FO-reduces to Digraph Isomorphism**: check simplicity
first-order, then copy. -/
noncomputable def graphIso_fo_reduction_digraphIso : GraphIso ≤ᶠᵒ DigraphIso where
  Tag := Unit
  dim := 1
  toInterpretation := GraphIso.simpleInterp
  correct A _ _ _ := GraphIso.hasGraphIso_iff_hasDigraphIso_map A

/-! ### The degree -/

/-- **The GI degree**: the problems that (ordered) first-order reduce to Graph
Isomorphism, as a complexity class
(`DescriptiveComplexity.ComplexityClass.below`). A problem is *GI-complete* –
in this library's finer, first-order sense – when it is
`DescriptiveComplexity.ComplexityClass.Complete` for `GI`.

The degree is named after the *undirected* problem, as the literature is: the
directed one has the same degree
(`DescriptiveComplexity.GI_eq_below_digraphIso`), but is not what “GI” means. -/
noncomputable def GI : ComplexityClass :=
  .below GraphIso

/-- Graph Isomorphism is in NP: it reduces to the directed problem, which is. -/
theorem graphIso_mem_NP : GraphIso ∈ NP :=
  NP.mem_of_foReduction graphIso_fo_reduction_digraphIso digraphIso_mem_NP

/-- The whole GI degree lies inside NP, since Graph Isomorphism does and
membership travels backward along reductions. (Whether the inclusion is strict
is the open question; the framework decides no such thing.) -/
theorem GI_subset_NP : GI ⊆ NP :=
  fun _ _ _ h => NP.mem_of_orderedReduction h.some graphIso_mem_NP

end Lax604544Proofs.DescriptiveComplexity


