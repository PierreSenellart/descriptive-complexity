/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.DagIso.Defs

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace DagIso

/-! ### The well-formedness sentence -/

/-- `Lt` is a topological order of `Arc` on `V`, as a first-order sentence
(over any variable type, so that it can be conjoined inside the defining
formulas of an interpretation): irreflexive and transitive on the marked set,
and containing the arcs. -/
noncomputable def topoIrreflClause {α : Type} (V : Language.twoDags.Relations 1)
    (Lt : Language.twoDags.Relations 2) : Language.twoDags.Formula α :=
  fo% ∀ x, V(x) → ¬ Lt(x, x)

@[inherit_doc topoIrreflClause]
noncomputable def topoTransClause {α : Type} (V : Language.twoDags.Relations 1)
    (Lt : Language.twoDags.Relations 2) : Language.twoDags.Formula α :=
  fo% ∀ x y z, (((V(x) ∧ V(y)) ∧ V(z)) ∧ Lt(x, y)) ∧ Lt(y, z) → Lt(x, z)

@[inherit_doc topoIrreflClause]
noncomputable def topoMonoClause {α : Type} (V : Language.twoDags.Relations 1)
    (Lt Arc : Language.twoDags.Relations 2) : Language.twoDags.Formula α :=
  fo% ∀ x y, (V(x) ∧ V(y)) ∧ Arc(x, y) → Lt(x, y)

@[inherit_doc topoIrreflClause]
noncomputable def topoSentence {α : Type} (V : Language.twoDags.Relations 1)
    (Lt Arc : Language.twoDags.Relations 2) : Language.twoDags.Formula α :=
  topoIrreflClause V Lt ⊓ (topoTransClause V Lt ⊓ topoMonoClause V Lt Arc)

/-- The sentence says what it is named after. -/
theorem realize_topoSentence {A : Type} [Language.twoDags.Structure A] {α : Type} (v : α → A)
    (V : Language.twoDags.Relations 1) (Lt Arc : Language.twoDags.Relations 2) :
    (topoSentence V Lt Arc).Realize v ↔
      TopoOn (fun a : A => RelMap V ![a]) (fun a b : A => RelMap Lt ![a, b])
        fun a b : A => RelMap Arc ![a, b] := by
  simp only [topoSentence, topoIrreflClause, topoTransClause, topoMonoClause, TopoOn,
    Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr]
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨fun x hx => h₁ (fun _ => x) hx, fun x y z hx hy hz l₁ l₂ =>
      h₂ ![x, y, z] ⟨⟨⟨⟨hx, hy⟩, hz⟩, l₁⟩, l₂⟩, fun x y hx hy ha => h₃ ![x, y] ⟨⟨hx, hy⟩, ha⟩⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨fun i hi => h₁ (i 0) hi, fun i hi =>
      h₂ (i 0) (i 1) (i 2) hi.1.1.1.1 hi.1.1.1.2 hi.1.1.2 hi.1.2 hi.2,
      fun i hi => h₃ (i 0) (i 1) hi.1.1 hi.1.2 hi.2⟩⟩

/-- Both sides of the instance are well formed. -/
noncomputable def wfSentence {α : Type} : Language.twoDags.Formula α :=
  topoSentence tdPatV tdPatLt tdPatArc ⊓ topoSentence tdHostV tdHostLt tdHostArc

theorem realize_wfSentence {A : Type} [Language.twoDags.Structure A] {α : Type} (v : α → A) :
    (wfSentence.Realize v) ↔
      TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧ TopoOn (TDHostV (A := A)) TDHostLt TDHostArc := by
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
    FOInterpretation Language.twoDags Language.twoGraphs Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun _ => fo%⟨u⟩ !wfSentence ∧ tdPatV(u)
    | _, .hostV => fun _ => fo%⟨u⟩ (!wfSentence ∧ tdHostV(u)) ∨ ¬ !wfSentence
    | _, .patE => fun _ => fo%⟨u, v⟩ !wfSentence ∧ tdPatArc(u, v)
    | _, .hostE => fun _ => fo%⟨u, v⟩ !wfSentence ∧ tdHostArc(u, v)

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

variable {A : Type} [Language.twoDags.Structure A]

/-- Well-formedness is a sentence: its realization does not depend on the
valuation. -/
private theorem wf_iff {α : Type} (v : α → A) :
    (wfSentence.Realize v) ↔
      TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧ TopoOn (TDHostV (A := A)) TDHostLt TDHostArc :=
  realize_wfSentence v

variable (hwf : TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧
  TopoOn (TDHostV (A := A)) TDHostLt TDHostArc)

include hwf

theorem patV_map (p : dagInterp.Map A) : TGPatV p ↔ TDPatV (dagEquiv p) := by
  rw [TGPatV, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(wf_iff _).mpr hwf, h⟩⟩

theorem hostV_map (p : dagInterp.Map A) : TGHostV p ↔ TDHostV (dagEquiv p) := by
  rw [TGHostV, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h => h.elim (fun h => h.2) fun h => absurd ((wf_iff _).mpr hwf) h,
    fun h => Or.inl ⟨(wf_iff _).mpr hwf, h⟩⟩

theorem patE_map (p q : dagInterp.Map A) :
    TGPatE p q ↔ TDPatArc (dagEquiv p) (dagEquiv q) := by
  rw [TGPatE, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_inf, Formula.realize_rel₂, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(wf_iff _).mpr hwf, h⟩⟩

theorem hostE_map (p q : dagInterp.Map A) :
    TGHostE p q ↔ TDHostArc (dagEquiv p) (dagEquiv q) := by
  rw [TGHostE, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_inf, Formula.realize_rel₂, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(wf_iff _).mpr hwf, h⟩⟩

end Realize

section IllFormed

variable {A : Type} [Language.twoDags.Structure A]

/-- When the instance is ill formed, no element of the image is a pattern
vertex. -/
theorem not_patV_map_of_not_wf
    (hwf : ¬(TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧
      TopoOn (TDHostV (A := A)) TDHostLt TDHostArc)) (p : dagInterp.Map A) : ¬TGPatV p := by
  rw [TGPatV, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact fun h => hwf ((realize_wfSentence _).mp h.1)

/-- When the instance is ill formed, every element of the image is a host
vertex. -/
theorem hostV_map_of_not_wf
    (hwf : ¬(TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧
      TopoOn (TDHostV (A := A)) TDHostLt TDHostArc)) (p : dagInterp.Map A) : TGHostV p := by
  rw [TGHostV, FOInterpretation.relMap_map]
  simp only [dagInterp, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var]
  exact Or.inr fun h => hwf ((realize_wfSentence _).mp h)

end IllFormed

/-! ### Correctness -/

section Correctness

variable {A : Type} [Language.twoDags.Structure A]

/-- Correctness of the interpretation: the image is a yes-instance of Graph
Isomorphism exactly when the input is one of DAG Isomorphism. -/
theorem hasDagIso_iff_hasDigraphIso_map (A : Type) [Language.twoDags.Structure A] [Finite A]
    [Nonempty A] :
    HasDagIso A ↔ HasDigraphIso (dagInterp.Map A) := by
  by_cases hwf : TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧
      TopoOn (TDHostV (A := A)) TDHostLt TDHostArc
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

end DescriptiveComplexity
