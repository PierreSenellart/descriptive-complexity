/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases
import Lax799700Proofs.DescriptiveComplexity.Composition
import Lax799700Proofs.DescriptiveComplexity.Ordered
import Lax799700Proofs.DescriptiveComplexity.Padding
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.FromSat
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Reductions
import Lax799700Proofs.DescriptiveComplexity.Problems.Sat
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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
# Subgraph Isomorphism is NP-complete

SUBGRAPH ISOMORPHISM: does the *host* graph contain a subgraph isomorphic to
the *pattern* graph? Equivalently – and this is the definition used here,
`Lax799700Proofs.DescriptiveComplexity.SubgraphIsoOn` – is there an injective homomorphism of the
pattern into the host? (Not an *induced* subgraph: non-edges of the pattern
are unconstrained, which is the standard reading and the one that makes Clique
a special case.)

## Two graphs in one structure

An instance carries two graphs, so `FirstOrder.Language.twoGraphs` has two
unary marks separating the pattern vertices from the host vertices and two
binary relations for the two adjacency relations. As with the set systems of
`Lax799700Proofs.DescriptiveComplexity.Problems.SetFamily`, nothing forces an element of the universe
to be a vertex of either graph: elements outside both marks are junk that no
condition mentions, which is exactly what lets a first-order interpretation
build such a structure inside a tagged power of its input universe. The
guessed map is likewise unconstrained off the pattern.

This vocabulary pattern – several structures side by side in one universe,
separated by marks – is the natural home for the remaining
combinatorial-packing problems (Exact Cover, 3-Dimensional Matching), where
the same trick applies.

## Hardness: a clique is a complete pattern

The reduction is from Clique (`Lax799700Proofs.DescriptiveComplexity.clique_fo_reduction_subgraphIso`,
tag `Bool`, dimension 1, quantifier-free): the host is the input graph and the
pattern is the *complete* graph on its marked set, so an injective
homomorphism of the pattern is precisely a clique at least as large as the
marked set. The threshold of Clique is thus consumed by the shape of the
pattern rather than by a counting argument – no `Set.ncard` reasoning appears
in this file beyond the embedding form
`Lax799700Proofs.DescriptiveComplexity.cliqueOn_iff_embedding` that Clique already provides.

The problem on *concrete* graphs – two edge sets on `Fin p` and `Fin h` – and
its encoding, faithfulness and decoding are in
`Lax799700Proofs.DescriptiveComplexity.Problems.SubgraphIso.Encoding`.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

/-! ### The generic property -/

section Generic

variable {A : Type}

variable {B : Type}

/-- `SubgraphIsoOn` transports along an equivalence commuting with the four
predicates. -/
theorem SubgraphIsoOn.of_equiv (u : B ≃ A) {PVB HVB : B → Prop} {PEB HEB : B → B → Prop}
    {PVA HVA : A → Prop} {PEA HEA : A → A → Prop}
    (hPV : ∀ b, PVB b ↔ PVA (u b)) (hHV : ∀ b, HVB b ↔ HVA (u b))
    (hPE : ∀ b b', PEB b b' ↔ PEA (u b) (u b'))
    (hHE : ∀ b b', HEB b b' ↔ HEA (u b) (u b'))
    (h : Lax799700.SubgraphIso.SubgraphIsoOn PVB HVB PEB HEB) : Lax799700.SubgraphIso.SubgraphIsoOn PVA HVA PEA HEA := by
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

end Generic

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700.SubgraphIso.SubgraphIsoOn

export Lax799700Proofs.DescriptiveComplexity.SubgraphIsoOn (of_equiv)

end Lax799700.SubgraphIso.SubgraphIsoOn

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Generic

variable {A : Type}

variable {B : Type}

/-- `SubgraphIsoOn` transports along an equivalence, iff version. -/
theorem SubgraphIsoOn.equiv_iff (u : B ≃ A) {PVB HVB : B → Prop} {PEB HEB : B → B → Prop}
    {PVA HVA : A → Prop} {PEA HEA : A → A → Prop}
    (hPV : ∀ b, PVB b ↔ PVA (u b)) (hHV : ∀ b, HVB b ↔ HVA (u b))
    (hPE : ∀ b b', PEB b b' ↔ PEA (u b) (u b'))
    (hHE : ∀ b b', HEB b b' ↔ HEA (u b) (u b')) :
    Lax799700.SubgraphIso.SubgraphIsoOn PVB HVB PEB HEB ↔ Lax799700.SubgraphIso.SubgraphIsoOn PVA HVA PEA HEA :=
  ⟨SubgraphIsoOn.of_equiv u hPV hHV hPE hHE,
    SubgraphIsoOn.of_equiv u.symm (fun a => by rw [hPV]; simp) (fun a => by rw [hHV]; simp)
      (fun a a' => by rw [hPE]; simp) fun a a' => by rw [hHE]; simp⟩

end Generic

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700.SubgraphIso.SubgraphIsoOn

export Lax799700Proofs.DescriptiveComplexity.SubgraphIsoOn (equiv_iff)

end Lax799700.SubgraphIso.SubgraphIsoOn

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Generic

variable {A : Type}

variable {B : Type}

end Generic

/-! ### The problem -/

section Problem

section Shorthands

variable {A : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A]

end Shorthands

variable (A : Type) [Lax799700.SubgraphIso.twoGraphs.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A] [Lax799700.SubgraphIso.twoGraphs.Structure B]

/-- The subgraph-isomorphism property is isomorphism-invariant. -/
theorem hasSubgraphIso_iso (e : A ≃[Lax799700.SubgraphIso.twoGraphs] B) :
    Lax799700.SubgraphIso.HasSubgraphIso A ↔ Lax799700.SubgraphIso.HasSubgraphIso B :=
  and_congr e.toEquiv.finite_iff
    (SubgraphIsoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e Lax799700.SubgraphIso.tgPatV a)
      (fun a => relMap_equiv₁ e Lax799700.SubgraphIso.tgHostV a) (fun a b => relMap_equiv₂ e Lax799700.SubgraphIso.tgPatE a b)
      fun a b => relMap_equiv₂ e Lax799700.SubgraphIso.tgHostE a b)

end Iso

/-- SUBGRAPH ISOMORPHISM, as a problem on pattern-and-host structures: does
the host contain a subgraph isomorphic to the pattern? -/
def SubgraphIso : Lax904597.Problems.DecisionProblem Lax799700.SubgraphIso.twoGraphs where
  Holds := fun A inst => @Lax799700.SubgraphIso.HasSubgraphIso A inst
  iso_invariant := fun e => hasSubgraphIso_iso e

/-! ### Clique reduces to Subgraph Isomorphism -/

/-- The interpretation of Clique into Subgraph Isomorphism: the tag `true`
carries the pattern – the complete graph on the marked set – and the tag
`false` the host, which is the input graph. -/
def cliquePatternInterp :
    Lax904597.Interpretations.FOInterpretation Lax799700.CliqueFamily.markedGraph Lax799700.SubgraphIso.twoGraphs Bool 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun t => if t 0 then FirstOrder.Language.Relations.formula₁ Lax799700.CliqueFamily.mgMarked (FirstOrder.Language.Term.var (0, 0)) else Bot.bot
    | _, .hostV => fun t => if t 0 then ⊥ else ⊤
    | _, .patE => fun t => if t 0 then
                               if t 1 then
                                 FirstOrder.Language.BoundedFormula.not
                                     (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))) ⊓
                                   (FirstOrder.Language.Relations.formula₁ Lax799700.CliqueFamily.mgMarked (FirstOrder.Language.Term.var (0, 0)) ⊓
                                     FirstOrder.Language.Relations.formula₁ Lax799700.CliqueFamily.mgMarked (FirstOrder.Language.Term.var (1, 0)))
                               else Bot.bot
                             else Bot.bot
    | _, .hostE => fun t => if t 0 then Bot.bot
                              else
                                if t 1 then Bot.bot
                                else
                                  FirstOrder.Language.BoundedFormula.not
                                      (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))) ⊓
                                    FirstOrder.Language.Relations.formula₂ Lax799700.CliqueFamily.mgAdj (FirstOrder.Language.Term.var (0, 0))
                                      (FirstOrder.Language.Term.var (1, 0))

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

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

@[simp]
theorem clPat_patV (v : A) : Lax799700.SubgraphIso.TGPatV (patPt v) ↔ Lax799700.CliqueFamily.MGMarked v := by
  rw [Lax799700.SubgraphIso.TGPatV, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, patPt, Lax799700.CliqueFamily.MGMarked, Formula.realize_rel₁]

@[simp]
theorem clPat_patV_host (v : A) : ¬Lax799700.SubgraphIso.TGPatV (hostPt v) := by
  rw [Lax799700.SubgraphIso.TGPatV, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, hostPt]

@[simp]
theorem clPat_hostV (v : A) : Lax799700.SubgraphIso.TGHostV (hostPt v) := by
  rw [Lax799700.SubgraphIso.TGHostV, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, hostPt]

@[simp]
theorem clPat_hostV_pat (v : A) : ¬Lax799700.SubgraphIso.TGHostV (patPt v) := by
  rw [Lax799700.SubgraphIso.TGHostV, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, patPt]

@[simp]
theorem clPat_patE (u v : A) :
    Lax799700.SubgraphIso.TGPatE (patPt u) (patPt v) ↔ u ≠ v ∧ Lax799700.CliqueFamily.MGMarked u ∧ Lax799700.CliqueFamily.MGMarked v := by
  rw [Lax799700.SubgraphIso.TGPatE, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, patPt, Lax799700.CliqueFamily.MGMarked, Formula.realize_rel₁]

@[simp]
theorem clPat_hostE (u v : A) :
    Lax799700.SubgraphIso.TGHostE (hostPt u) (hostPt v) ↔ u ≠ v ∧ Lax799700.CliqueFamily.MGAdj u v := by
  rw [Lax799700.SubgraphIso.TGHostE, FOInterpretation.relMap_map]
  simp [cliquePatternInterp, hostPt, Lax799700.CliqueFamily.MGAdj, Formula.realize_rel₂]

/-- Only pattern copies are pattern vertices. -/
theorem patV_eq_patPt {p : cliquePatternInterp.Map A} (h : Lax799700.SubgraphIso.TGPatV p) : ∃ v, p = patPt v := by
  rcases p with ⟨(_ | _), w⟩
  · exact absurd h (by rw [hostPt_eta w]; exact clPat_patV_host (w 0))
  · exact ⟨w 0, patPt_eta w⟩

/-- Only host copies are host vertices, so the image of a pattern vertex is a
host copy. -/
theorem hostV_eq_hostPt {p : cliquePatternInterp.Map A} (h : Lax799700.SubgraphIso.TGHostV p) :
    ∃ v, p = hostPt v := by
  rcases p with ⟨(_ | _), w⟩
  · exact ⟨w 0, hostPt_eta w⟩
  · exact absurd h (by rw [patPt_eta w]; exact clPat_hostV_pat (w 0))

end Characterizations

section Correctness

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

open Classical in
/-- Where a vertex goes under the embedding of the pattern: a marked vertex to
its image under the guessed injection into the clique, anything else to
itself – a value no condition of the problem mentions. -/
private noncomputable def cliqueVertex {S : A → Prop}
    (e : {x : A // Lax799700.CliqueFamily.MGMarked x} ↪ {x : A // S x}) (v : A) : A :=
  if h : Lax799700.CliqueFamily.MGMarked v then (e ⟨v, h⟩).1 else v

private theorem cliqueVertex_marked {S : A → Prop}
    (e : {x : A // Lax799700.CliqueFamily.MGMarked x} ↪ {x : A // S x}) {v : A} (h : Lax799700.CliqueFamily.MGMarked v) :
    cliqueVertex e v = (e ⟨v, h⟩).1 := by
  classical
  rw [cliqueVertex, dif_pos h]

/-- Correctness of the interpretation: a graph has a clique at least as large
as its marked set iff the complete graph on that marked set embeds into it. -/
theorem hasLargeClique_iff_subgraphIso_map (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    Lax799700.CliqueFamily.HasLargeClique A ↔ Lax799700.SubgraphIso.HasSubgraphIso (cliquePatternInterp.Map A) := by
  constructor
  · rintro ⟨hfin, hcl⟩
    have := hfin
    obtain ⟨S, hS, ⟨e⟩⟩ := (cliqueOn_iff_embedding _ _).mp hcl
    refine ⟨cliquePatternInterp.map_finite A,
      fun p => hostPt (cliqueVertex e (p.2 0)), fun p _ => clPat_hostV _, ?_, ?_⟩
    · intro p q hp hq hpq
      obtain ⟨u, rfl⟩ := patV_eq_patPt hp
      obtain ⟨v, rfl⟩ := patV_eq_patPt hq
      have hu : Lax799700.CliqueFamily.MGMarked u := (clPat_patV u).mp hp
      have hv : Lax799700.CliqueFamily.MGMarked v := (clPat_patV v).mp hq
      have hval : cliqueVertex e u = cliqueVertex e v := hostPt_injective hpq
      rw [cliqueVertex_marked e hu, cliqueVertex_marked e hv] at hval
      exact congrArg patPt (congrArg Subtype.val (e.injective (Subtype.ext hval)))
    · intro p q hp hq hpe
      obtain ⟨u, rfl⟩ := patV_eq_patPt hp
      obtain ⟨v, rfl⟩ := patV_eq_patPt hq
      have hu : Lax799700.CliqueFamily.MGMarked u := (clPat_patV u).mp hp
      have hv : Lax799700.CliqueFamily.MGMarked v := (clPat_patV v).mp hq
      obtain ⟨hne, -, -⟩ := (clPat_patE u v).mp hpe
      have hne' : (e ⟨u, hu⟩).1 ≠ (e ⟨v, hv⟩).1 := fun h =>
        hne (congrArg Subtype.val (e.injective (Subtype.ext h)))
      change Lax799700.SubgraphIso.TGHostE (hostPt (cliqueVertex e u)) (hostPt (cliqueVertex e v))
      rw [cliqueVertex_marked e hu, cliqueVertex_marked e hv]
      exact (clPat_hostE _ _).mpr ⟨hne', hS _ _ (e ⟨u, hu⟩).2 (e ⟨v, hv⟩).2 hne'⟩
  · rintro ⟨hfin, f, hmaps, hinj, hedge⟩
    have hA : Finite A := Finite.of_injective _ (hostPt_injective (A := A))
    have := hA
    have hval : ∀ m : {x : A // Lax799700.CliqueFamily.MGMarked x}, ∃ w : A, f (patPt m.1) = hostPt w := fun m =>
      hostV_eq_hostPt (hmaps _ ((clPat_patV m.1).mpr m.2))
    choose g hg using hval
    refine ⟨hA, (cliqueOn_iff_embedding _ _).mpr
      ⟨fun w => ∃ v, Lax799700.CliqueFamily.MGMarked v ∧ f (patPt v) = hostPt w, ?_,
        ⟨⟨fun m => ⟨g m, m.1, m.2, hg m⟩, fun m m' hmm' => ?_⟩⟩⟩⟩
    · rintro x y ⟨u, hu, hfu⟩ ⟨v, hv, hfv⟩ hxy
      have hpat : Lax799700.SubgraphIso.TGPatE (patPt u) (patPt v) :=
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
  correct A _ _ _ := hasLargeClique_iff_subgraphIso_map A

/-! ### Membership -/

section SigmaOne

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive IsoGuessBlockIx where
/-- The guessed map from the pattern to the host. -/

  | map
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.IsoGuessBlockIx :=
  ⟨List.toFinset [.map], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition of Subgraph
Isomorphism: one binary relation variable, the guessed map. -/
def isoGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.IsoGuessBlockIx
  arity := fun i =>
    match i with
    | .map => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev subgraphSOLang : FirstOrder.Language :=
  (Lax799700.SubgraphIso.twoGraphs).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.isoGuessBlock)

/-- The `patV` symbol over the sum. -/
abbrev sgPatVSym : (_root_.Lax799700Proofs.DescriptiveComplexity.subgraphSOLang).Relations 1 :=
  Sum.inl Lax799700.SubgraphIso.tgPatV

/-- The `hostV` symbol over the sum. -/
abbrev sgHostVSym : (_root_.Lax799700Proofs.DescriptiveComplexity.subgraphSOLang).Relations 1 :=
  Sum.inl Lax799700.SubgraphIso.tgHostV

/-- The `patE` symbol over the sum. -/
abbrev sgPatESym : (_root_.Lax799700Proofs.DescriptiveComplexity.subgraphSOLang).Relations 2 :=
  Sum.inl Lax799700.SubgraphIso.tgPatE

/-- The `hostE` symbol over the sum. -/
abbrev sgHostESym : (_root_.Lax799700Proofs.DescriptiveComplexity.subgraphSOLang).Relations 2 :=
  Sum.inl Lax799700.SubgraphIso.tgHostE

/-- The `map` relation variable. -/
def sgMapRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.isoGuessBlock).Relations 2 :=
  ⟨.map, rfl⟩

/-- The `map` symbol over the sum. -/
abbrev sgMapSym : (_root_.Lax799700Proofs.DescriptiveComplexity.subgraphSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.sgMapRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- Kernel clause: every pattern vertex is mapped to some host vertex. -/
private noncomputable def sgTotalClause : subgraphSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ sgPatVSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₂ sgMapSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
              (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            FirstOrder.Language.Relations.formula₁ sgHostVSym (FirstOrder.Language.Term.var (Sum.inr 0)))))

/-- Kernel clause: the guessed map is injective on the pattern. -/
private noncomputable def sgInjClause : subgraphSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₁ sgPatVSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                FirstOrder.Language.Relations.formula₁ sgPatVSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              FirstOrder.Language.Relations.formula₂ sgMapSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
            FirstOrder.Language.Relations.formula₂ sgMapSym (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- Kernel clause: the guessed map carries pattern edges to host edges. -/
private noncomputable def sgEdgeClause : subgraphSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
      ((FirstOrder.Language.Relations.formula₁ sgPatVSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                  FirstOrder.Language.Relations.formula₁ sgPatVSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
                FirstOrder.Language.Relations.formula₂ sgPatESym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              FirstOrder.Language.Relations.formula₂ sgMapSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
            FirstOrder.Language.Relations.formula₂ sgMapSym (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 3))).imp
        (FirstOrder.Language.Relations.formula₂ sgHostESym (FirstOrder.Language.Term.var (Sum.inr 2))
          (FirstOrder.Language.Term.var (Sum.inr 3))))

/-- The first-order kernel of the `Σ₁` definition of Subgraph
Isomorphism. -/
noncomputable def subgraphKernel : subgraphSOLang.Sentence :=
  sgTotalClause ⊓ (sgInjClause ⊓ sgEdgeClause)

/-- Realization of the kernel under an assignment of the guessed map. -/
private theorem realize_subgraphKernel {A : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A]
    (ρ : isoGuessBlock.Assignment A) :
    (@Sentence.Realize subgraphSOLang A
        (@sumStructure _ _ A _ (isoGuessBlock.structure ρ)) subgraphKernel) ↔
      (∀ x : A, Lax799700.SubgraphIso.TGPatV x → ∃ y : A, ρ .map ![x, y] ∧ Lax799700.SubgraphIso.TGHostV y) ∧
        (∀ x x' y : A, Lax799700.SubgraphIso.TGPatV x → Lax799700.SubgraphIso.TGPatV x' → ρ .map ![x, y] → ρ .map ![x', y] → x = x') ∧
        ∀ x x' y y' : A, Lax799700.SubgraphIso.TGPatV x → Lax799700.SubgraphIso.TGPatV x' → Lax799700.SubgraphIso.TGPatE x x' → ρ .map ![x, y] →
          ρ .map ![x', y'] → Lax799700.SubgraphIso.TGHostE y y' := by
  let := isoGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 2 → A),
      RelMap (L := subgraphSOLang) (M := A) sgMapSym w ↔ ρ .map w := fun _ => Iff.rfl
  rw [subgraphKernel]
  simp only [sgTotalClause, sgInjClause, sgEdgeClause, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  refine and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x x' y hx hx' h₁ h₂ => ?_, fun h i hi => ?_⟩
      ⟨fun h x x' y y' hx hx' hpe h₁ h₂ => ?_, fun h i hi => ?_⟩)
  · obtain ⟨y, hy1, hy2⟩ := h (fun _ => x) hx
    exact ⟨y 0, hy1, hy2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy1, hy2⟩
  · exact h ![x, x', y] ⟨⟨⟨hx, hx'⟩, h₁⟩, h₂⟩
  · exact h (i 0) (i 1) (i 2) hi.1.1.1 hi.1.1.2 hi.1.2 hi.2
  · exact h ![x, x', y, y'] ⟨⟨⟨⟨hx, hx'⟩, hpe⟩, h₁⟩, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) hi.1.1.1.1 hi.1.1.1.2 hi.1.1.2 hi.1.2 hi.2

/-- **Subgraph Isomorphism is `Σ₁`-definable**: existentially guess the map,
then check first-order that it sends pattern vertices to host vertices,
injectively, carrying pattern edges to host edges. -/
theorem subgraphIso_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 SubgraphIso := by
  refine ⟨[isoGuessBlock], rfl, subgraphKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, f, hmaps, hinj, hedge⟩
    refine ⟨fun i => match i with | .map => fun w : Fin 2 → A => f (w 0) = w 1,
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
    have hch : ∀ x : {x : A // Lax799700.SubgraphIso.TGPatV x}, ∃ y : A, ρ .map ![x.1, y] ∧ Lax799700.SubgraphIso.TGHostV y :=
      fun x => htot x.1 x.2
    choose g hg1 hg2 using hch
    refine ⟨‹Finite A›, fun x => if h : Lax799700.SubgraphIso.TGPatV x then g ⟨x, h⟩ else x, fun x hx => ?_,
      fun x y hx hy hxy => ?_, fun x y hx hy hxy => ?_⟩
    · change Lax799700.SubgraphIso.TGHostV (if h : Lax799700.SubgraphIso.TGPatV x then g ⟨x, h⟩ else x)
      rw [dif_pos hx]
      exact hg2 ⟨x, hx⟩
    · have hxy' : (if h : Lax799700.SubgraphIso.TGPatV x then g ⟨x, h⟩ else x) =
          if h : Lax799700.SubgraphIso.TGPatV y then g ⟨y, h⟩ else y := hxy
      rw [dif_pos hx, dif_pos hy] at hxy'
      exact hinj x y (g ⟨x, hx⟩) hx hy (hg1 ⟨x, hx⟩) (hxy' ▸ hg1 ⟨y, hy⟩)
    · change Lax799700.SubgraphIso.TGHostE (if h : Lax799700.SubgraphIso.TGPatV x then g ⟨x, h⟩ else x)
        (if h : Lax799700.SubgraphIso.TGPatV y then g ⟨y, h⟩ else y)
      rw [dif_pos hx, dif_pos hy]
      exact hedge x y _ _ hx hy hxy (hg1 ⟨x, hx⟩) (hg1 ⟨y, hy⟩)

end SigmaOne

/-! ### NP-completeness -/

end Lax799700Proofs.DescriptiveComplexity


