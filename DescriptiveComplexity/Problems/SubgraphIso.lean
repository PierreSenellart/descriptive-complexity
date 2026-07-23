/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily
import DescriptiveComplexity.SecondOrder

/-!
# Subgraph Isomorphism is NP-complete

SUBGRAPH ISOMORPHISM: does the *host* graph contain a subgraph isomorphic to
the *pattern* graph? Equivalently – and this is the definition used here,
`DescriptiveComplexity.SubgraphIsoOn` – is there an injective homomorphism of the
pattern into the host? (Not an *induced* subgraph: non-edges of the pattern
are unconstrained, which is the standard reading and the one that makes Clique
a special case.)

## Two graphs in one structure

An instance carries two graphs, so `FirstOrder.Language.twoGraphs` has two
unary marks separating the pattern vertices from the host vertices and two
binary relations for the two adjacency relations. As with the set systems of
`DescriptiveComplexity.Problems.SetFamily`, nothing forces an element of the universe
to be a vertex of either graph: elements outside both marks are junk that no
condition mentions, which is exactly what lets a first-order interpretation
build such a structure inside a tagged power of its input universe. The
guessed map is likewise unconstrained off the pattern.

This vocabulary pattern – several structures side by side in one universe,
separated by marks – is the natural home for the remaining
combinatorial-packing problems (Exact Cover, 3-Dimensional Matching), where
the same trick applies.

## Hardness: a clique is a complete pattern

The reduction is from Clique (`DescriptiveComplexity.clique_fo_reduction_subgraphIso`,
tag `Bool`, dimension 1, quantifier-free): the host is the input graph and the
pattern is the *complete* graph on its marked set, so an injective
homomorphism of the pattern is precisely a clique at least as large as the
marked set. The threshold of Clique is thus consumed by the shape of the
pattern rather than by a counting argument – no `Set.ncard` reasoning appears
in this file beyond the embedding form
`DescriptiveComplexity.cliqueOn_iff_embedding` that Clique already provides.
-/

/- The language of two-graph structures lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.graph` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of pattern-and-host graphs. -/
inductive twoGraphsRel : ℕ → Type
  /-- `patV a`: `a` is a vertex of the pattern graph. -/
  | patV : twoGraphsRel 1
  /-- `hostV a`: `a` is a vertex of the host graph. -/
  | hostV : twoGraphsRel 1
  /-- `patE a b`: there is an edge of the pattern from `a` to `b`. -/
  | patE : twoGraphsRel 2
  /-- `hostE a b`: there is an edge of the host from `a` to `b`. -/
  | hostE : twoGraphsRel 2
  deriving DecidableEq

/-- The relational language of pattern-and-host graphs: two graphs sharing a
universe, each with its own vertex mark and adjacency relation. -/
protected def twoGraphs : Language :=
  ⟨fun _ => Empty, twoGraphsRel⟩
  deriving IsRelational

/-- The pattern-vertex symbol. -/
abbrev tgPatV : Language.twoGraphs.Relations 1 := .patV

/-- The host-vertex symbol. -/
abbrev tgHostV : Language.twoGraphs.Relations 1 := .hostV

/-- The pattern-adjacency symbol. -/
abbrev tgPatE : Language.twoGraphs.Relations 2 := .patE

/-- The host-adjacency symbol. -/
abbrev tgHostE : Language.twoGraphs.Relations 2 := .hostE

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

/-! ### The generic property -/

section Generic

variable {A : Type}

/-- Some map sends the `PV`-vertices injectively into the `HV`-vertices,
carrying `PE`-edges to `HE`-edges: an injective homomorphism of the pattern
into the host. -/
def SubgraphIsoOn (PV HV : A → Prop) (PE HE : A → A → Prop) : Prop :=
  ∃ f : A → A, (∀ x, PV x → HV (f x)) ∧
    (∀ x y, PV x → PV y → f x = f y → x = y) ∧
    ∀ x y, PV x → PV y → PE x y → HE (f x) (f y)

variable {B : Type}

/-- `SubgraphIsoOn` transports along an equivalence commuting with the four
predicates. -/
theorem SubgraphIsoOn.of_equiv (u : B ≃ A) {PVB HVB : B → Prop} {PEB HEB : B → B → Prop}
    {PVA HVA : A → Prop} {PEA HEA : A → A → Prop}
    (hPV : ∀ b, PVB b ↔ PVA (u b)) (hHV : ∀ b, HVB b ↔ HVA (u b))
    (hPE : ∀ b b', PEB b b' ↔ PEA (u b) (u b'))
    (hHE : ∀ b b', HEB b b' ↔ HEA (u b) (u b'))
    (h : SubgraphIsoOn PVB HVB PEB HEB) : SubgraphIsoOn PVA HVA PEA HEA := by
  obtain ⟨f, hmaps, hinj, hedge⟩ := h
  refine ⟨fun a => u (f (u.symm a)), fun x hx => ?_, fun x y hx hy hxy => ?_,
    fun x y hx hy hxy => ?_⟩
  · exact (hHV (f (u.symm x))).mp (hmaps _ ((hPV (u.symm x)).mpr (by simpa using hx)))
  · have hux : u.symm x = u.symm y :=
      hinj _ _ ((hPV _).mpr (by simpa using hx)) ((hPV _).mpr (by simpa using hy))
        (u.injective hxy)
    simpa using congrArg u hux
  · refine (hHE (f (u.symm x)) (f (u.symm y))).mp (hedge _ _ ((hPV _).mpr (by simpa using hx))
      ((hPV _).mpr (by simpa using hy)) ((hPE _ _).mpr (by simpa using hxy)))

/-- `SubgraphIsoOn` transports along an equivalence, iff version. -/
theorem SubgraphIsoOn.equiv_iff (u : B ≃ A) {PVB HVB : B → Prop} {PEB HEB : B → B → Prop}
    {PVA HVA : A → Prop} {PEA HEA : A → A → Prop}
    (hPV : ∀ b, PVB b ↔ PVA (u b)) (hHV : ∀ b, HVB b ↔ HVA (u b))
    (hPE : ∀ b b', PEB b b' ↔ PEA (u b) (u b'))
    (hHE : ∀ b b', HEB b b' ↔ HEA (u b) (u b')) :
    SubgraphIsoOn PVB HVB PEB HEB ↔ SubgraphIsoOn PVA HVA PEA HEA :=
  ⟨SubgraphIsoOn.of_equiv u hPV hHV hPE hHE,
    SubgraphIsoOn.of_equiv u.symm (fun a => by rw [hPV]; simp) (fun a => by rw [hHV]; simp)
      (fun a a' => by rw [hPE]; simp) fun a a' => by rw [hHE]; simp⟩

end Generic

/-! ### The problem -/

section Problem

section Shorthands

variable {A : Type} [Language.twoGraphs.Structure A]

/-- Being a vertex of the pattern graph. -/
def TGPatV (a : A) : Prop := RelMap tgPatV ![a]

/-- Being a vertex of the host graph. -/
def TGHostV (a : A) : Prop := RelMap tgHostV ![a]

/-- Adjacency in the pattern graph. -/
def TGPatE (a b : A) : Prop := RelMap tgPatE ![a, b]

/-- Adjacency in the host graph. -/
def TGHostE (a b : A) : Prop := RelMap tgHostE ![a, b]

end Shorthands

variable (A : Type) [Language.twoGraphs.Structure A]

/-- The host graph contains a subgraph isomorphic to the pattern graph.
(Finiteness of the universe is required only for uniformity with the rest of
the catalog; the property itself makes sense in general.) -/
def HasSubgraphIso : Prop :=
  Finite A ∧ SubgraphIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

section Iso

variable {A B : Type} [Language.twoGraphs.Structure A] [Language.twoGraphs.Structure B]

/-- The subgraph-isomorphism property is isomorphism-invariant. -/
theorem hasSubgraphIso_iso (e : A ≃[Language.twoGraphs] B) :
    HasSubgraphIso A ↔ HasSubgraphIso B :=
  and_congr e.toEquiv.finite_iff
    (SubgraphIsoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tgPatV a)
      (fun a => relMap_equiv₁ e tgHostV a) (fun a b => relMap_equiv₂ e tgPatE a b)
      fun a b => relMap_equiv₂ e tgHostE a b)

end Iso

/-- SUBGRAPH ISOMORPHISM, as a problem on pattern-and-host structures: does
the host contain a subgraph isomorphic to the pattern? -/
def SubgraphIso : DecisionProblem Language.twoGraphs where
  Holds := fun A inst => @HasSubgraphIso A inst
  iso_invariant := fun e => hasSubgraphIso_iso e

/-! ### Clique reduces to Subgraph Isomorphism -/

/-- The interpretation of Clique into Subgraph Isomorphism: the tag `true`
carries the pattern – the complete graph on the marked set – and the tag
`false` the host, which is the input graph. -/
def cliquePatternInterp :
    FOInterpretation Language.markedGraph Language.twoGraphs Bool 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun t =>
        if t 0 then mgMarked.formula₁ (Term.var (0, 0)) else ⊥
    | _, .hostV => fun t => if t 0 then ⊥ else ⊤
    | _, .patE => fun t =>
        if t 0 then
          (if t 1 then
            ∼(Term.equal (Term.var (0, 0)) (Term.var (1, 0))) ⊓
              (mgMarked.formula₁ (Term.var (0, 0)) ⊓ mgMarked.formula₁ (Term.var (1, 0)))
          else ⊥)
        else ⊥
    | _, .hostE => fun t =>
        if t 0 then ⊥
        else
          (if t 1 then ⊥
          else
            ∼(Term.equal (Term.var (0, 0)) (Term.var (1, 0))) ⊓
              mgAdj.formula₂ (Term.var (0, 0)) (Term.var (1, 0)))

section Points

variable {A : Type}

/-- The pattern copy of a vertex. -/
def patPt (v : A) : cliquePatternInterp.Map A := (true, fun _ => v)

/-- The host copy of a vertex. -/
def hostPt (v : A) : cliquePatternInterp.Map A := (false, fun _ => v)

theorem patPt_injective : Function.Injective (patPt (A := A)) :=
  fun _ _ h => congrArg (fun p : Bool × (Fin 1 → A) => p.2 0) h

theorem hostPt_injective : Function.Injective (hostPt (A := A)) :=
  fun _ _ h => congrArg (fun p : Bool × (Fin 1 → A) => p.2 0) h

theorem patPt_eta (w : Fin 1 → A) : ((true, w) : cliquePatternInterp.Map A) = patPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

theorem hostPt_eta (w : Fin 1 → A) : ((false, w) : cliquePatternInterp.Map A) = hostPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

end Points

section Characterizations

variable {A : Type} [Language.markedGraph.Structure A]

@[simp]
theorem clPat_patV (v : A) : TGPatV (patPt v) ↔ MGMarked v := by
  rw [TGPatV, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, patPt, MGMarked, Formula.realize_rel₁]

@[simp]
theorem clPat_patV_host (v : A) : ¬TGPatV (hostPt v) := by
  rw [TGPatV, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, hostPt]

@[simp]
theorem clPat_hostV (v : A) : TGHostV (hostPt v) := by
  rw [TGHostV, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, hostPt]

@[simp]
theorem clPat_hostV_pat (v : A) : ¬TGHostV (patPt v) := by
  rw [TGHostV, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, patPt]

@[simp]
theorem clPat_patE (u v : A) :
    TGPatE (patPt u) (patPt v) ↔ u ≠ v ∧ MGMarked u ∧ MGMarked v := by
  rw [TGPatE, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, patPt, MGMarked, Formula.realize_rel₁]

@[simp]
theorem clPat_hostE (u v : A) :
    TGHostE (hostPt u) (hostPt v) ↔ u ≠ v ∧ MGAdj u v := by
  rw [TGHostE, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, hostPt, MGAdj, Formula.realize_rel₂]

/-- Only pattern copies are pattern vertices. -/
theorem patV_eq_patPt {p : cliquePatternInterp.Map A} (h : TGPatV p) : ∃ v, p = patPt v := by
  rcases p with ⟨(_ | _), w⟩
  · exact absurd h (by rw [hostPt_eta w]; exact clPat_patV_host (w 0))
  · exact ⟨w 0, patPt_eta w⟩

/-- Only host copies are host vertices, so the image of a pattern vertex is a
host copy. -/
theorem hostV_eq_hostPt {p : cliquePatternInterp.Map A} (h : TGHostV p) :
    ∃ v, p = hostPt v := by
  rcases p with ⟨(_ | _), w⟩
  · exact ⟨w 0, hostPt_eta w⟩
  · exact absurd h (by rw [patPt_eta w]; exact clPat_hostV_pat (w 0))

end Characterizations

section Correctness

variable {A : Type} [Language.markedGraph.Structure A]

open Classical in
/-- Where a vertex goes under the embedding of the pattern: a marked vertex to
its image under the guessed injection into the clique, anything else to
itself – a value no condition of the problem mentions. -/
private noncomputable def cliqueVertex {S : A → Prop}
    (e : {x : A // MGMarked x} ↪ {x : A // S x}) (v : A) : A :=
  if h : MGMarked v then (e ⟨v, h⟩).1 else v

private theorem cliqueVertex_marked {S : A → Prop}
    (e : {x : A // MGMarked x} ↪ {x : A // S x}) {v : A} (h : MGMarked v) :
    cliqueVertex e v = (e ⟨v, h⟩).1 := by
  classical
  rw [cliqueVertex, dif_pos h]

/-- Correctness of the interpretation: a graph has a clique at least as large
as its marked set iff the complete graph on that marked set embeds into it. -/
theorem hasLargeClique_iff_subgraphIso_map (A : Type) [Language.markedGraph.Structure A] :
    HasLargeClique A ↔ HasSubgraphIso (cliquePatternInterp.Map A) := by
  constructor
  · rintro ⟨hfin, hcl⟩
    haveI := hfin
    obtain ⟨S, hS, ⟨e⟩⟩ := (cliqueOn_iff_embedding _ _).mp hcl
    refine ⟨cliquePatternInterp.map_finite A,
      fun p => hostPt (cliqueVertex e (p.2 0)), fun p _ => clPat_hostV _, ?_, ?_⟩
    · intro p q hp hq hpq
      obtain ⟨u, rfl⟩ := patV_eq_patPt hp
      obtain ⟨v, rfl⟩ := patV_eq_patPt hq
      have hu : MGMarked u := (clPat_patV u).mp hp
      have hv : MGMarked v := (clPat_patV v).mp hq
      have hval : cliqueVertex e u = cliqueVertex e v := hostPt_injective hpq
      rw [cliqueVertex_marked e hu, cliqueVertex_marked e hv] at hval
      exact congrArg patPt (congrArg Subtype.val (e.injective (Subtype.ext hval)))
    · intro p q hp hq hpe
      obtain ⟨u, rfl⟩ := patV_eq_patPt hp
      obtain ⟨v, rfl⟩ := patV_eq_patPt hq
      have hu : MGMarked u := (clPat_patV u).mp hp
      have hv : MGMarked v := (clPat_patV v).mp hq
      obtain ⟨hne, -, -⟩ := (clPat_patE u v).mp hpe
      have hne' : (e ⟨u, hu⟩).1 ≠ (e ⟨v, hv⟩).1 := fun h =>
        hne (congrArg Subtype.val (e.injective (Subtype.ext h)))
      change TGHostE (hostPt (cliqueVertex e u)) (hostPt (cliqueVertex e v))
      rw [cliqueVertex_marked e hu, cliqueVertex_marked e hv]
      exact (clPat_hostE _ _).mpr ⟨hne', hS _ _ (e ⟨u, hu⟩).2 (e ⟨v, hv⟩).2 hne'⟩
  · rintro ⟨hfin, f, hmaps, hinj, hedge⟩
    have hA : Finite A := Finite.of_injective _ (hostPt_injective (A := A))
    haveI := hA
    have hval : ∀ m : {x : A // MGMarked x}, ∃ w : A, f (patPt m.1) = hostPt w := fun m =>
      hostV_eq_hostPt (hmaps _ ((clPat_patV m.1).mpr m.2))
    choose g hg using hval
    refine ⟨hA, (cliqueOn_iff_embedding _ _).mpr
      ⟨fun w => ∃ v, MGMarked v ∧ f (patPt v) = hostPt w, ?_,
        ⟨⟨fun m => ⟨g m, m.1, m.2, hg m⟩, fun m m' hmm' => ?_⟩⟩⟩⟩
    · rintro x y ⟨u, hu, hfu⟩ ⟨v, hv, hfv⟩ hxy
      have hpat : TGPatE (patPt u) (patPt v) :=
        (clPat_patE u v).mpr ⟨fun h => hxy (hostPt_injective (by rw [← hfu, ← hfv, h])), hu, hv⟩
      have hE := hedge _ _ ((clPat_patV u).mpr hu) ((clPat_patV v).mpr hv) hpat
      rw [hfu, hfv] at hE
      exact ((clPat_hostE x y).mp hE).2
    · have hgg : g m = g m' := congrArg Subtype.val hmm'
      have hfm : f (patPt m.1) = f (patPt m'.1) := by rw [hg m, hg m', hgg]
      exact Subtype.ext (patPt_injective
        (hinj _ _ ((clPat_patV m.1).mpr m.2) ((clPat_patV m'.1).mpr m'.2) hfm))

end Correctness

/-- **Clique FO-reduces to Subgraph Isomorphism**: the pattern is the
complete graph on the marked set, the host is the input graph. -/
def clique_fo_reduction_subgraphIso : Clique ≤ᶠᵒ SubgraphIso where
  Tag := Bool
  dim := 1
  toInterpretation := cliquePatternInterp
  correct A _ _ := hasLargeClique_iff_subgraphIso_map A

/-! ### Membership -/

section SigmaOne

/-- The single existential block of the `Σ₁` definition of Subgraph
Isomorphism: one binary relation variable, the guessed map. -/
def isoGuessBlock : SOBlock where
  ι := Unit
  arity := fun _ => 2

/-- The symbol of the guessed map. -/
def sgMapRel : isoGuessBlock.lang.Relations 2 := ⟨(), rfl⟩

/-- The vocabulary of the kernel: pattern-and-host structures together with
the guessed map. -/
abbrev subgraphSOLang : Language := Language.twoGraphs.sum isoGuessBlock.lang

/-- The pattern-vertex symbol in the kernel's vocabulary. -/
abbrev sgPatVSym : subgraphSOLang.Relations 1 := Sum.inl tgPatV

/-- The host-vertex symbol in the kernel's vocabulary. -/
abbrev sgHostVSym : subgraphSOLang.Relations 1 := Sum.inl tgHostV

/-- The pattern-adjacency symbol in the kernel's vocabulary. -/
abbrev sgPatESym : subgraphSOLang.Relations 2 := Sum.inl tgPatE

/-- The host-adjacency symbol in the kernel's vocabulary. -/
abbrev sgHostESym : subgraphSOLang.Relations 2 := Sum.inl tgHostE

/-- The guessed-map symbol in the kernel's vocabulary. -/
abbrev sgMapSym : subgraphSOLang.Relations 2 := Sum.inr sgMapRel

/-- Kernel clause: every pattern vertex is mapped to some host vertex. -/
private noncomputable def sgTotalClause : subgraphSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr 0))).imp
      ((Relations.formula₂ sgMapSym (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓
        Relations.formula₁ sgHostVSym (Term.var (Sum.inr ()))).iExs Unit))

/-- Kernel clause: the guessed map is injective on the pattern. -/
private noncomputable def sgInjClause : subgraphSOLang.Sentence :=
  ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ sgPatVSym (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- Kernel clause: the guessed map carries pattern edges to host edges. -/
private noncomputable def sgEdgeClause : subgraphSOLang.Sentence :=
  ((Relations.formula₁ sgPatVSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ sgPatVSym (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ sgPatESym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ sgMapSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 3))).imp
    (Relations.formula₂ sgHostESym (Term.var (Sum.inr 2))
      (Term.var (Sum.inr 3)))).iAlls (Fin 4)

/-- The first-order kernel of the `Σ₁` definition of Subgraph
Isomorphism. -/
noncomputable def subgraphKernel : subgraphSOLang.Sentence :=
  sgTotalClause ⊓ (sgInjClause ⊓ sgEdgeClause)

/-- Realization of the kernel under an assignment of the guessed map. -/
private theorem realize_subgraphKernel {A : Type} [Language.twoGraphs.Structure A]
    (ρ : isoGuessBlock.Assignment A) :
    (@Sentence.Realize subgraphSOLang A
        (@sumStructure _ _ A _ (isoGuessBlock.structure ρ)) subgraphKernel) ↔
      (∀ x : A, TGPatV x → ∃ y : A, ρ () ![x, y] ∧ TGHostV y) ∧
        (∀ x x' y : A, TGPatV x → TGPatV x' → ρ () ![x, y] → ρ () ![x', y] → x = x') ∧
        ∀ x x' y y' : A, TGPatV x → TGPatV x' → TGPatE x x' → ρ () ![x, y] →
          ρ () ![x', y'] → TGHostE y y' := by
  letI := isoGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 2 → A),
      RelMap (L := subgraphSOLang) (M := A) sgMapSym w ↔ ρ () w := fun _ => Iff.rfl
  rw [subgraphKernel]
  simp only [sgTotalClause, sgInjClause, sgEdgeClause, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  refine and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x x' y hx hx' h₁ h₂ => ?_, fun h i hi => ?_⟩
      ⟨fun h x x' y y' hx hx' hpe h₁ h₂ => ?_, fun h i hi => ?_⟩)
  · obtain ⟨y, hy1, hy2⟩ := h (fun _ => x) hx
    exact ⟨y (), hy1, hy2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy1, hy2⟩
  · exact h ![x, x', y] ⟨⟨⟨hx, hx'⟩, h₁⟩, h₂⟩
  · exact h (i 0) (i 1) (i 2) hi.1.1.1 hi.1.1.2 hi.1.2 hi.2
  · exact h ![x, x', y, y'] ⟨⟨⟨⟨hx, hx'⟩, hpe⟩, h₁⟩, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) hi.1.1.1.1 hi.1.1.1.2 hi.1.1.2 hi.1.2 hi.2

/-- **Subgraph Isomorphism is `Σ₁`-definable**: existentially guess the map,
then check first-order that it sends pattern vertices to host vertices,
injectively, carrying pattern edges to host edges. -/
theorem subgraphIso_sigmaSODefinable : SigmaSODefinable 1 SubgraphIso := by
  refine ⟨[isoGuessBlock], rfl, subgraphKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, f, hmaps, hinj, hedge⟩
    refine ⟨fun i => match i with | () => fun w : Fin 2 → A => f (w 0) = w 1,
      (realize_subgraphKernel _).mpr ⟨fun x hx => ⟨f x, rfl, hmaps x hx⟩,
        fun x x' y hx hx' h₁ h₂ => hinj x x' hx hx' (h₁.trans h₂.symm), ?_⟩⟩
    intro x x' y y' hx hx' hpe h₁ h₂
    have h₁' : f x = y := h₁
    have h₂' : f x' = y' := h₂
    rw [← h₁', ← h₂']
    exact hedge x x' hx hx' hpe
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htot, hinj, hedge⟩ := (realize_subgraphKernel ρ).mp hρ
    classical
    have hch : ∀ x : {x : A // TGPatV x}, ∃ y : A, ρ () ![x.1, y] ∧ TGHostV y :=
      fun x => htot x.1 x.2
    choose g hg1 hg2 using hch
    refine ⟨‹Finite A›, fun x => if h : TGPatV x then g ⟨x, h⟩ else x, fun x hx => ?_,
      fun x y hx hy hxy => ?_, fun x y hx hy hxy => ?_⟩
    · change TGHostV (if h : TGPatV x then g ⟨x, h⟩ else x)
      rw [dif_pos hx]
      exact hg2 ⟨x, hx⟩
    · have hxy' : (if h : TGPatV x then g ⟨x, h⟩ else x) =
          if h : TGPatV y then g ⟨y, h⟩ else y := hxy
      rw [dif_pos hx, dif_pos hy] at hxy'
      exact hinj x y (g ⟨x, hx⟩) hx hy (hg1 ⟨x, hx⟩) (hxy' ▸ hg1 ⟨y, hy⟩)
    · change TGHostE (if h : TGPatV x then g ⟨x, h⟩ else x)
        (if h : TGPatV y then g ⟨y, h⟩ else y)
      rw [dif_pos hx, dif_pos hy]
      exact hedge x y _ _ hx hy hxy (hg1 ⟨x, hx⟩) (hg1 ⟨y, hy⟩)

end SigmaOne

/-! ### NP-completeness -/

/-- Subgraph Isomorphism is in NP: it is `Σ₁`-definable. -/
theorem subgraphIso_mem_NP : SubgraphIso ∈ NP :=
  subgraphIso_sigmaSODefinable

/-- Subgraph Isomorphism is NP-hard: Clique, which is NP-hard, reduces to it
by taking the complete graph on the marked set as pattern. -/
theorem subgraphIso_NP_hard : NP.Hard SubgraphIso :=
  NP.hard_of_foReduction clique_fo_reduction_subgraphIso clique_NP_hard

/-- **Subgraph Isomorphism is NP-complete**, derived from the first-order
reductions of this library and the Cook–Levin theorem. -/
theorem subgraphIso_NP_complete : NP.Complete SubgraphIso :=
  ⟨subgraphIso_mem_NP, subgraphIso_NP_hard⟩

end DescriptiveComplexity
