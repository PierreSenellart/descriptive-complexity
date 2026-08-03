/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SubgraphIso
import DescriptiveComplexity.IsoGadget

/-!
# Digraph Isomorphism, and the degree it defines

DIGRAPH ISOMORPHISM: are the two *directed* graphs of the instance isomorphic?
The vocabulary is the pattern-and-host one of
`DescriptiveComplexity.Problems.SubgraphIso`
(`FirstOrder.Language.twoGraphs`, two marks and two binary relations – nothing
asks them to be symmetric, which is what makes this the directed problem), and
the yes-instances are the structures whose two marked subgraphs are isomorphic
(`DescriptiveComplexity.RelIsoOn`); as everywhere in the catalog, elements
outside both marks are junk that no condition mentions.

The undirected problem, which is what the literature calls graph isomorphism,
is `DescriptiveComplexity.GraphIso` (`DescriptiveComplexity.Problems.GraphIso`);
it reduces to this one by testing simplicity first-order. The converse
reduction – the classical digraph-to-graph gadget – is what the degree below is
still anchored on this problem for.

Two things make this problem worth its own file.

**It is the library's first problem conjecturally neither in P nor
NP-complete.** Membership is a textbook `Σ₁` – guess a binary relation, check
first-order that it is a bijection of the pattern vertices onto the host
vertices preserving adjacency in both directions – with no order, no counting
and no threshold, so `DescriptiveComplexity.digraphIso_mem_NP` is cheap. No
hardness result accompanies it, and none is expected: the problem is in NP,
is not known to be in P, and is not known to be NP-complete ([Babai
2016][babai2016graph] gives a quasipolynomial algorithm; [Köbler, Schöning and
Torán 1993][kobler1993graph] is the structural account).

**It is one half of the reason `DescriptiveComplexity.ComplexityClass.below`
exists.** “GI-complete” is the standard example of completeness for the degree
of a *problem* rather than for a logically defined class. The degree itself
(`DescriptiveComplexity.GI`) is defined on the *undirected* problem, in
`DescriptiveComplexity.Problems.GraphIso.Defs`, since that is what the
literature names GI; this problem is complete for it too
(`DescriptiveComplexity.digraphIso_GI_complete`), the two being
interreducible.

There is also a pleasant circularity worth noting: a decision problem in this
library is by definition an isomorphism-invariant property of finite structures
(`DescriptiveComplexity.DecisionProblem`), so isomorphism is the problem of
deciding the very equivalence the framework quotients by. That reading is
`DescriptiveComplexity.relIsoOn_iff_equiv`: the semantic condition is
literally the existence of an equivalence between the two marked sets carrying
one adjacency relation to the other.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock


/-! ### The problem -/

section Problem

variable (A : Type) [Language.twoGraphs.Structure A]

/-- The two marked graphs of the instance are isomorphic. -/
def HasDigraphIso : Prop :=
  Finite A ∧ RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

section Iso

variable {A B : Type} [Language.twoGraphs.Structure A] [Language.twoGraphs.Structure B]

/-- The graph-isomorphism property is isomorphism-invariant. -/
theorem hasDigraphIso_iso (e : A ≃[Language.twoGraphs] B) :
    HasDigraphIso A ↔ HasDigraphIso B :=
  and_congr e.toEquiv.finite_iff
    (RelIsoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tgPatV a)
      (fun a => relMap_equiv₁ e tgHostV a) (fun a b => relMap_equiv₂ e tgPatE a b)
      fun a b => relMap_equiv₂ e tgHostE a b)

end Iso

/-- DIGRAPH ISOMORPHISM, as a problem on pattern-and-host structures: are the
two marked directed graphs isomorphic? -/
def DigraphIso : DecisionProblem Language.twoGraphs where
  Holds := fun A inst => @HasDigraphIso A inst
  iso_invariant := fun e => hasDigraphIso_iso e

/-! ### Membership -/

section SigmaOne

/-- Kernel clause: every pattern vertex is mapped to some host vertex. -/
private noncomputable def giTotalClause : subgraphSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr 0))).imp
      ((Relations.formula₂ sgMapSym (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓
        Relations.formula₁ sgHostVSym (Term.var (Sum.inr ()))).iExs Unit))

/-- Kernel clause: the guessed map is a function on the pattern. -/
private noncomputable def giFuncClause : subgraphSOLang.Sentence :=
  ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel clause: the guessed map is injective on the pattern. -/
private noncomputable def giInjClause : subgraphSOLang.Sentence :=
  ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ sgPatVSym (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- Kernel clause: every host vertex is hit – what makes the map onto, and the
one clause Subgraph Isomorphism does not have. -/
private noncomputable def giSurjClause : subgraphSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ sgHostVSym (Term.var (Sum.inr 0))).imp
      ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr ())) ⊓
        Relations.formula₂ sgMapSym (Term.var (Sum.inr ()))
          (Term.var (Sum.inl (Sum.inr 0)))).iExs Unit))

/-- Kernel clause: the guessed map carries pattern edges to host edges. -/
private noncomputable def giEdgeClause : subgraphSOLang.Sentence :=
  ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ sgPatVSym (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ sgPatESym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 3))).imp
    (Relations.formula₂ sgHostESym (Term.var (Sum.inr 2))
      (Term.var (Sum.inr 3)))).iAlls (Fin 4)

/-- Kernel clause: the guessed map reflects host edges to pattern edges – the
other clause distinguishing isomorphism from an injective homomorphism. -/
private noncomputable def giEdgeBackClause : subgraphSOLang.Sentence :=
  ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ sgPatVSym (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 3)) ⊓
      Relations.formula₂ sgHostESym (Term.var (Sum.inr 2)) (Term.var (Sum.inr 3))).imp
    (Relations.formula₂ sgPatESym (Term.var (Sum.inr 0))
      (Term.var (Sum.inr 1)))).iAlls (Fin 4)

/-- The first-order kernel of the `Σ₁` definition of Digraph Isomorphism: the
guessed relation is a bijection of the pattern vertices onto the host vertices,
preserving and reflecting adjacency. -/
noncomputable def digraphIsoKernel : subgraphSOLang.Sentence :=
  giTotalClause ⊓ (giFuncClause ⊓ (giInjClause ⊓
    (giSurjClause ⊓ (giEdgeClause ⊓ giEdgeBackClause))))

/-- Realization of the kernel under an assignment of the guessed map. -/
private theorem realize_digraphIsoKernel {A : Type} [Language.twoGraphs.Structure A]
    (ρ : isoGuessBlock.Assignment A) :
    (@Sentence.Realize subgraphSOLang A
        (@sumStructure _ _ A _ (isoGuessBlock.structure ρ)) digraphIsoKernel) ↔
      (∀ x : A, TGPatV x → ∃ y : A, ρ () ![x, y] ∧ TGHostV y) ∧
        (∀ x y y' : A, TGPatV x → ρ () ![x, y] → ρ () ![x, y'] → y = y') ∧
        (∀ x x' y : A, TGPatV x → TGPatV x' → ρ () ![x, y] → ρ () ![x', y] → x = x') ∧
        (∀ y : A, TGHostV y → ∃ x : A, TGPatV x ∧ ρ () ![x, y]) ∧
        (∀ x x' y y' : A, TGPatV x → TGPatV x' → TGPatE x x' → ρ () ![x, y] →
          ρ () ![x', y'] → TGHostE y y') ∧
        ∀ x x' y y' : A, TGPatV x → TGPatV x' → ρ () ![x, y] → ρ () ![x', y'] →
          TGHostE y y' → TGPatE x x' := by
  letI := isoGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 2 → A),
      RelMap (L := subgraphSOLang) (M := A) sgMapSym w ↔ ρ () w := fun _ => Iff.rfl
  rw [digraphIsoKernel]
  simp only [giTotalClause, giFuncClause, giInjClause, giSurjClause, giEdgeClause,
    giEdgeBackClause, Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iExs, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  refine and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x y y' hx h₁ h₂ => ?_, fun h i hi => ?_⟩
      (and_congr ⟨fun h x x' y hx hx' h₁ h₂ => ?_, fun h i hi => ?_⟩
        (and_congr ⟨fun h y hy => ?_, fun h i hi => ?_⟩
          (and_congr ⟨fun h x x' y y' hx hx' hpe h₁ h₂ => ?_, fun h i hi => ?_⟩
            ⟨fun h x x' y y' hx hx' h₁ h₂ hhe => ?_, fun h i hi => ?_⟩))))
  · obtain ⟨y, hy1, hy2⟩ := h (fun _ => x) hx
    exact ⟨y (), hy1, hy2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy1, hy2⟩
  · exact h ![x, y, y'] ⟨⟨hx, h₁⟩, h₂⟩
  · exact h (i 0) (i 1) (i 2) hi.1.1 hi.1.2 hi.2
  · exact h ![x, x', y] ⟨⟨⟨hx, hx'⟩, h₁⟩, h₂⟩
  · exact h (i 0) (i 1) (i 2) hi.1.1.1 hi.1.1.2 hi.1.2 hi.2
  · obtain ⟨x, hx1, hx2⟩ := h (fun _ => y) hy
    exact ⟨x (), hx1, hx2⟩
  · obtain ⟨x, hx1, hx2⟩ := h (i 0) hi
    exact ⟨fun _ => x, hx1, hx2⟩
  · exact h ![x, x', y, y'] ⟨⟨⟨⟨hx, hx'⟩, hpe⟩, h₁⟩, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) hi.1.1.1.1 hi.1.1.1.2 hi.1.1.2 hi.1.2 hi.2
  · exact h ![x, x', y, y'] ⟨⟨⟨⟨hx, hx'⟩, h₁⟩, h₂⟩, hhe⟩
  · exact h (i 0) (i 1) (i 2) (i 3) hi.1.1.1.1 hi.1.1.1.2 hi.1.1.2 hi.1.2 hi.2

/-- **Digraph Isomorphism is `Σ₁`-definable**: existentially guess the map, then
check first-order that it is a bijection of the pattern vertices onto the host
vertices preserving adjacency in both directions. One binary relation variable,
no order, no counting, no threshold. -/
theorem digraphIso_sigmaSODefinable : SigmaSODefinable 1 DigraphIso := by
  refine ⟨[isoGuessBlock], rfl, digraphIsoKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, f, hmaps, hinj, hsurj, hedge⟩
    refine ⟨fun i => match i with | () => fun w : Fin 2 → A => f (w 0) = w 1,
      (realize_digraphIsoKernel _).mpr ⟨fun x hx => ⟨f x, rfl, hmaps x hx⟩,
        fun x y y' _ h₁ h₂ => h₁.symm.trans h₂,
        fun x x' y hx hx' h₁ h₂ => hinj x x' hx hx' (h₁.trans h₂.symm),
        fun y hy => ?_, ?_, ?_⟩⟩
    · obtain ⟨x, hx, hfx⟩ := hsurj y hy
      exact ⟨x, hx, hfx⟩
    · intro x x' y y' hx hx' hpe h₁ h₂
      have h₁' : f x = y := h₁
      have h₂' : f x' = y' := h₂
      rw [← h₁', ← h₂']
      exact (hedge x x' hx hx').mp hpe
    · intro x x' y y' hx hx' h₁ h₂ hhe
      have h₁' : f x = y := h₁
      have h₂' : f x' = y' := h₂
      rw [← h₁', ← h₂'] at hhe
      exact (hedge x x' hx hx').mpr hhe
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htot, hfunc, hinj, hsurj, hedge, hedgeBack⟩ := (realize_digraphIsoKernel ρ).mp hρ
    classical
    have hch : ∀ x : {x : A // TGPatV x}, ∃ y : A, ρ () ![x.1, y] ∧ TGHostV y :=
      fun x => htot x.1 x.2
    choose g hg1 hg2 using hch
    refine ⟨‹Finite A›, fun x => if h : TGPatV x then g ⟨x, h⟩ else x, fun x hx => ?_,
      fun x y hx hy hxy => ?_, fun y hy => ?_, fun x y hx hy => ?_⟩
    · change TGHostV (if h : TGPatV x then g ⟨x, h⟩ else x)
      rw [dif_pos hx]
      exact hg2 ⟨x, hx⟩
    · have hxy' : (if h : TGPatV x then g ⟨x, h⟩ else x) =
          if h : TGPatV y then g ⟨y, h⟩ else y := hxy
      rw [dif_pos hx, dif_pos hy] at hxy'
      exact hinj x y (g ⟨x, hx⟩) hx hy (hg1 ⟨x, hx⟩) (hxy' ▸ hg1 ⟨y, hy⟩)
    · obtain ⟨x, hx, hxy⟩ := hsurj y hy
      refine ⟨x, hx, ?_⟩
      change (if h : TGPatV x then g ⟨x, h⟩ else x) = y
      rw [dif_pos hx]
      exact hfunc x (g ⟨x, hx⟩) y hx (hg1 ⟨x, hx⟩) hxy
    · change TGPatE x y ↔ TGHostE (if h : TGPatV x then g ⟨x, h⟩ else x)
        (if h : TGPatV y then g ⟨y, h⟩ else y)
      rw [dif_pos hx, dif_pos hy]
      exact ⟨fun hpe => hedge x y _ _ hx hy hpe (hg1 ⟨x, hx⟩) (hg1 ⟨y, hy⟩),
        fun hhe => hedgeBack x y _ _ hx hy (hg1 ⟨x, hx⟩) (hg1 ⟨y, hy⟩) hhe⟩

end SigmaOne

/-- Digraph Isomorphism is in NP: it is `Σ₁`-definable. -/
theorem digraphIso_mem_NP : DigraphIso ∈ NP :=
  digraphIso_sigmaSODefinable

end DescriptiveComplexity
