/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.DigraphIso
import DescriptiveComplexity.GadgetDouble
import DescriptiveComplexity.Degree

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace DigraphBridge

/-! ### Renaming the hand-rolled vocabulary to the generic one -/

/-- The interpretation renaming `twoGraphs` to `twoCopies graph`: one tag, one
dimension, each symbol to its counterpart. -/
def toTC : FOInterpretation Language.twoGraphs (Language.twoCopies Language.graph) Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patMark => fun _ => fo%⟨u⟩ tgPatV(u)
    | _, .hostMark => fun _ => fo%⟨u⟩ tgHostV(u)
    | _, .pat .adj => fun _ => fo%⟨u, v⟩ tgPatE(u, v)
    | _, .host .adj => fun _ => fo%⟨u, v⟩ tgHostE(u, v)

/-- The interpretation renaming `twoCopies graph` back to `twoGraphs`. -/
def ofTC : FOInterpretation (Language.twoCopies Language.graph) Language.twoGraphs Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun _ => fo%⟨u⟩ (tcPatMark Language.graph)(u)
    | _, .hostV => fun _ => fo%⟨u⟩ (tcHostMark Language.graph)(u)
    | _, .patE => fun _ => fo%⟨u, v⟩ (tcPat Language.adj)(u, v)
    | _, .hostE => fun _ => fo%⟨u, v⟩ (tcHost Language.adj)(u, v)

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

variable {A : Type} [Language.twoGraphs.Structure A]

theorem toTC_patMark (p : toTC.Map A) :
    TCPatMark (L₁ := Language.graph) p ↔ TGPatV (p.2 0) := by
  rw [TCPatMark, FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₁, TGPatV]

theorem toTC_hostMark (p : toTC.Map A) :
    TCHostMark (L₁ := Language.graph) p ↔ TGHostV (p.2 0) := by
  rw [TCHostMark, FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₁, TGHostV]

theorem toTC_patAdj (p q : toTC.Map A) :
    RelMap (tcPat Language.adj) ![p, q] ↔ TGPatE (p.2 0) (q.2 0) := by
  rw [FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₂, TGPatE]

theorem toTC_hostAdj (p q : toTC.Map A) :
    RelMap (tcHost Language.adj) ![p, q] ↔ TGHostE (p.2 0) (q.2 0) := by
  rw [FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₂, TGHostE]

end Realize

section RealizeBack

variable {A : Type} [(Language.twoCopies Language.graph).Structure A]

theorem ofTC_patV (p : ofTC.Map A) :
    TGPatV p ↔ TCPatMark (L₁ := Language.graph) (p.2 0) := by
  rw [TGPatV, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₁, TCPatMark]

theorem ofTC_hostV (p : ofTC.Map A) :
    TGHostV p ↔ TCHostMark (L₁ := Language.graph) (p.2 0) := by
  rw [TGHostV, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₁, TCHostMark]

theorem ofTC_patE (p q : ofTC.Map A) :
    TGPatE p q ↔ RelMap (tcPat Language.adj) ![p.2 0, q.2 0] := by
  rw [TGPatE, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₂]

theorem ofTC_hostE (p q : ofTC.Map A) :
    TGHostE p q ↔ RelMap (tcHost Language.adj) ![p.2 0, q.2 0] := by
  rw [TGHostE, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₂]

end RealizeBack

/-! ### The generic side condition, as a relation isomorphism -/

section Generic

variable {B : Type} [(Language.twoCopies Language.graph).Structure B]

/-- The pattern relation of a `twoCopies graph`-structure. -/
def TCPatAdj (x y : B) : Prop := RelMap (tcPat Language.adj) ![x, y]

/-- The host relation of a `twoCopies graph`-structure. -/
def TCHostAdj (x y : B) : Prop := RelMap (tcHost Language.adj) ![x, y]

/-- The pattern side's adjacency, read on the ambient structure. -/
theorem patSide_relMap (a b : {x : B // TCPatMark (L₁ := Language.graph) x}) :
    RelMap (L := Language.graph) Language.adj ![a, b] ↔ TCPatAdj a.1 b.1 := by
  change RelMap (tcPat Language.adj)
    (fun i => ((![a, b] : Fin 2 → {x : B // TCPatMark (L₁ := Language.graph) x}) i).1) ↔ _
  rw [show (fun i => ((![a, b] : Fin 2 → {x : B // TCPatMark (L₁ := Language.graph) x}) i).1)
      = ![a.1, b.1] by funext i; fin_cases i <;> rfl]
  exact Iff.rfl

/-- The host side's adjacency, read on the ambient structure. -/
theorem hostSide_relMap (a b : {x : B // TCHostMark (L₁ := Language.graph) x}) :
    RelMap (L := Language.graph) Language.adj ![a, b] ↔ TCHostAdj a.1 b.1 := by
  change RelMap (tcHost Language.adj)
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
      RelIsoOn (TCPatMark (L₁ := Language.graph)) (TCHostMark (L₁ := Language.graph))
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
theorem toTC_correct (A : Type) [Language.twoGraphs.Structure A] [Finite A] :
    DigraphIso.Holds A ↔ (TwoCopiesIso Language.graph).Holds (toTC.Map A) := by
  have hrel : RelIsoOn (TCPatMark (L₁ := Language.graph)) TCHostMark
      (TCPatAdj (B := toTC.Map A)) TCHostAdj ↔
      RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE :=
    RelIsoOn.equiv_iff toEquivMap (fun p => toTC_patMark p) (fun p => toTC_hostMark p)
      (fun p q => toTC_patAdj p q) fun p q => toTC_hostAdj p q
  constructor
  · rintro ⟨-, h⟩
    exact ⟨toTC.map_finite A,
      (nonempty_tcSideEquiv_iff_relIsoOn).mpr (hrel.mpr h)⟩
  · rintro ⟨-, h⟩
    exact ⟨‹Finite A›, hrel.mp ((nonempty_tcSideEquiv_iff_relIsoOn).mp h)⟩

/-- Coming back preserves the answer. -/
theorem ofTC_correct (A : Type) [(Language.twoCopies Language.graph).Structure A] [Finite A] :
    (TwoCopiesIso Language.graph).Holds A ↔ DigraphIso.Holds (ofTC.Map A) := by
  have hrel : RelIsoOn (TGPatV (A := ofTC.Map A)) TGHostV TGPatE TGHostE ↔
      RelIsoOn (TCPatMark (L₁ := Language.graph)) TCHostMark (TCPatAdj (B := A)) TCHostAdj :=
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

/-- And back. -/
def twoCopiesIso_fo_reduction_digraphIso : TwoCopiesIso Language.graph ≤ᶠᵒ DigraphIso where
  Tag := Unit
  dim := 1
  toInterpretation := DigraphBridge.ofTC
  correct A _ _ _ := DigraphBridge.ofTC_correct A

/-- **Digraph Isomorphism and the generic isomorphism problem of the graph
vocabulary have the same degree.** A problem stated over `twoCopies` reaches the
GI degree through this equality, so
`DescriptiveComplexity.isoReflecting_fo_reduction` – a gadget on single
structures – is all a new entry needs. -/
theorem below_digraphIso_eq_below_twoCopiesIso :
    ComplexityClass.below DigraphIso = ComplexityClass.below (TwoCopiesIso Language.graph) :=
  ComplexityClass.below_congr ⟨digraphIso_fo_reduction_twoCopiesIso.toOrdered⟩
    ⟨twoCopiesIso_fo_reduction_digraphIso.toOrdered⟩

end DescriptiveComplexity
