/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.DigraphIso
import DescriptiveComplexity.Degree

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic property -/

section Generic

variable {A : Type}

/-- The relation `E` is symmetric and irreflexive on the marked set `V`: a
simple graph, as opposed to an arbitrary binary relation. -/
def SimpleOn (V : A → Prop) (E : A → A → Prop) : Prop :=
  (∀ x y, V x → V y → E x y → E y x) ∧ ∀ x, V x → ¬E x x

variable {B : Type}

/-- `SimpleOn` transports along an equivalence commuting with the two
predicates. -/
theorem SimpleOn.of_equiv (u : B ≃ A) {VB : B → Prop} {EB : B → B → Prop}
    {VA : A → Prop} {EA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hE : ∀ b b', EB b b' ↔ EA (u b) (u b'))
    (h : SimpleOn VB EB) : SimpleOn VA EA := by
  obtain ⟨hsymm, hirr⟩ := h
  refine ⟨fun x y hx hy hxy => ?_, fun x hx hxx => ?_⟩
  · have := hsymm (u.symm x) (u.symm y) ((hV _).mpr (by simpa using hx))
      ((hV _).mpr (by simpa using hy)) ((hE _ _).mpr (by simpa using hxy))
    simpa using (hE (u.symm y) (u.symm x)).mp this
  · exact hirr (u.symm x) ((hV _).mpr (by simpa using hx)) ((hE _ _).mpr (by simpa using hxx))

/-- `SimpleOn` transports along an equivalence, iff version. -/
theorem SimpleOn.equiv_iff (u : B ≃ A) {VB : B → Prop} {EB : B → B → Prop}
    {VA : A → Prop} {EA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hE : ∀ b b', EB b b' ↔ EA (u b) (u b')) :
    SimpleOn VB EB ↔ SimpleOn VA EA :=
  ⟨SimpleOn.of_equiv u hV hE,
    SimpleOn.of_equiv u.symm (fun a => by rw [hV]; simp) fun a a' => by rw [hE]; simp⟩

end Generic

/-! ### The problem -/

section Problem

variable (A : Type) [Language.twoGraphs.Structure A]

/-- Both marked graphs are simple, and they are isomorphic. -/
def HasGraphIso : Prop :=
  Finite A ∧ SimpleOn (TGPatV (A := A)) TGPatE ∧ SimpleOn (TGHostV (A := A)) TGHostE ∧
    RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

section Iso

variable {A B : Type} [Language.twoGraphs.Structure A] [Language.twoGraphs.Structure B]

/-- The graph-isomorphism property is isomorphism-invariant. -/
theorem hasGraphIso_iso (e : A ≃[Language.twoGraphs] B) :
    HasGraphIso A ↔ HasGraphIso B :=
  and_congr e.toEquiv.finite_iff
    (and_congr
      (SimpleOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tgPatV a)
        fun a b => relMap_equiv₂ e tgPatE a b)
      (and_congr
        (SimpleOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tgHostV a)
          fun a b => relMap_equiv₂ e tgHostE a b)
        (RelIsoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tgPatV a)
          (fun a => relMap_equiv₁ e tgHostV a) (fun a b => relMap_equiv₂ e tgPatE a b)
          fun a b => relMap_equiv₂ e tgHostE a b)))

end Iso

/-- GRAPH ISOMORPHISM: are the two marked *simple* graphs isomorphic?
Simplicity is part of the yes-condition, and is first-order, so a reduction can
test it – unlike acyclicity in `DescriptiveComplexity.DagIso`, which has to be
carried by the instance. -/
def GraphIso : DecisionProblem Language.twoGraphs where
  Holds := fun A inst => @HasGraphIso A inst
  iso_invariant := fun e => hasGraphIso_iso e

/-! ### Membership: forget nothing, just check simplicity -/

namespace GraphIso

/-- `E` is symmetric and irreflexive on `V`, as a first-order sentence over any
variable type, so that it can be conjoined inside the defining formulas of an
interpretation. -/
noncomputable def simpleSentence {α : Type} (V : Language.twoGraphs.Relations 1)
    (E : Language.twoGraphs.Relations 2) : Language.twoGraphs.Formula α :=
  (((Relations.formula₁ V (Term.var (Sum.inr 0)) ⊓ Relations.formula₁ V (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ E (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
    (Relations.formula₂ E (Term.var (Sum.inr 1)) (Term.var (Sum.inr 0)))).iAlls (Fin 2)) ⊓
    (((Relations.formula₁ V (Term.var (Sum.inr 0))).imp
      ∼(Relations.formula₂ E (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0)))).iAlls (Fin 1))

theorem realize_simpleSentence {A : Type} [Language.twoGraphs.Structure A] {α : Type}
    (v : α → A) (V : Language.twoGraphs.Relations 1) (E : Language.twoGraphs.Relations 2) :
    (simpleSentence V E).Realize v ↔
      SimpleOn (fun a : A => RelMap V ![a]) fun a b : A => RelMap E ![a, b] := by
  simp only [simpleSentence, SimpleOn, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun x y hx hy hxy => h₁ ![x, y] ⟨⟨hx, hy⟩, hxy⟩,
      fun x hx => h₂ (fun _ => x) hx⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun i hi => h₁ (i 0) (i 1) hi.1.1 hi.1.2 hi.2, fun i hi => h₂ (i 0) hi⟩⟩

/-- Both sides of the instance are simple graphs. -/
noncomputable def wfSentence {α : Type} : Language.twoGraphs.Formula α :=
  simpleSentence tgPatV tgPatE ⊓ simpleSentence tgHostV tgHostE

theorem realize_wfSentence {A : Type} [Language.twoGraphs.Structure A] {α : Type} (v : α → A) :
    (wfSentence.Realize v) ↔
      SimpleOn (TGPatV (A := A)) TGPatE ∧ SimpleOn (TGHostV (A := A)) TGHostE := by
  rw [wfSentence, Formula.realize_inf, realize_simpleSentence, realize_simpleSentence]
  rfl

/-- The interpretation of Graph Isomorphism into Digraph Isomorphism: copy both
marked graphs if they are simple, and otherwise emit a pattern with no vertices
facing a host with all of them. -/
noncomputable def simpleInterp :
    FOInterpretation Language.twoGraphs Language.twoGraphs Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun _ => wfSentence ⊓ Relations.formula₁ tgPatV (Term.var (0, 0))
    | _, .hostV => fun _ =>
        (wfSentence ⊓ Relations.formula₁ tgHostV (Term.var (0, 0))) ⊔ ∼wfSentence
    | _, .patE => fun _ =>
        wfSentence ⊓ Relations.formula₂ tgPatE (Term.var (0, 0)) (Term.var (1, 0))
    | _, .hostE => fun _ =>
        wfSentence ⊓ Relations.formula₂ tgHostE (Term.var (0, 0)) (Term.var (1, 0))

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

variable {A : Type} [Language.twoGraphs.Structure A]

variable (hwf : SimpleOn (TGPatV (A := A)) TGPatE ∧ SimpleOn (TGHostV (A := A)) TGHostE)

include hwf

theorem patV_map (p : simpleInterp.Map A) : TGPatV p ↔ TGPatV (uEquiv p) := by
  rw [TGPatV, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(realize_wfSentence _).mpr hwf, h⟩⟩

theorem hostV_map (p : simpleInterp.Map A) : TGHostV p ↔ TGHostV (uEquiv p) := by
  rw [TGHostV, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h => h.elim (fun h => h.2) fun h => absurd ((realize_wfSentence _).mpr hwf) h,
    fun h => Or.inl ⟨(realize_wfSentence _).mpr hwf, h⟩⟩

theorem patE_map (p q : simpleInterp.Map A) :
    TGPatE p q ↔ TGPatE (uEquiv p) (uEquiv q) := by
  rw [TGPatE, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_inf, Formula.realize_rel₂, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(realize_wfSentence _).mpr hwf, h⟩⟩

theorem hostE_map (p q : simpleInterp.Map A) :
    TGHostE p q ↔ TGHostE (uEquiv p) (uEquiv q) := by
  rw [TGHostE, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_inf, Formula.realize_rel₂, Term.realize_var]
  exact ⟨fun h => h.2, fun h => ⟨(realize_wfSentence _).mpr hwf, h⟩⟩

end Realize

section IllFormed

variable {A : Type} [Language.twoGraphs.Structure A]

theorem not_patV_map_of_not_wf
    (hwf : ¬(SimpleOn (TGPatV (A := A)) TGPatE ∧ SimpleOn (TGHostV (A := A)) TGHostE))
    (p : simpleInterp.Map A) : ¬TGPatV p := by
  rw [TGPatV, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact fun h => hwf ((realize_wfSentence _).mp h.1)

theorem hostV_map_of_not_wf
    (hwf : ¬(SimpleOn (TGPatV (A := A)) TGPatE ∧ SimpleOn (TGHostV (A := A)) TGHostE))
    (p : simpleInterp.Map A) : TGHostV p := by
  rw [TGHostV, FOInterpretation.relMap_map]
  simp only [simpleInterp, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var]
  exact Or.inr fun h => hwf ((realize_wfSentence _).mp h)

end IllFormed

section Correctness

/-- Correctness: the image is a yes-instance of Digraph Isomorphism exactly
when the input is one of Graph Isomorphism. -/
theorem hasGraphIso_iff_hasDigraphIso_map (A : Type) [Language.twoGraphs.Structure A] [Finite A]
    [Nonempty A] :
    HasGraphIso A ↔ HasDigraphIso (simpleInterp.Map A) := by
  by_cases hwf : SimpleOn (TGPatV (A := A)) TGPatE ∧ SimpleOn (TGHostV (A := A)) TGHostE
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

/-- Graph Isomorphism belongs to its own degree. -/
theorem graphIso_mem_GI : GraphIso ∈ GI :=
  ComplexityClass.mem_below_self GraphIso

/-- Graph Isomorphism is in NP: it reduces to the directed problem, which is. -/
theorem graphIso_mem_NP : GraphIso ∈ NP :=
  NP.mem_of_foReduction graphIso_fo_reduction_digraphIso digraphIso_mem_NP

/-- The whole GI degree lies inside NP, since Graph Isomorphism does and
membership travels backward along reductions. (Whether the inclusion is strict
is the open question; the framework decides no such thing.) -/
theorem GI_subset_NP : GI ⊆ NP :=
  fun _ _ _ h => NP.mem_of_orderedReduction h.some graphIso_mem_NP

end DescriptiveComplexity
