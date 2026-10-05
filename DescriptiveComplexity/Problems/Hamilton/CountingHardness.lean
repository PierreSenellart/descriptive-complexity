/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.CountingReverse
import DescriptiveComplexity.Problems.OneInSat.CountingFromSat
import DescriptiveComplexity.Counting.Relativized

/-!
# #Directed Hamilton Circuit is parsimoniously `#P`-complete

`DescriptiveComplexity.sharpDirHamCircuit_sharpP_parsimoniousComplete`, by a relativized
reduction from #1-in-SAT
(`DescriptiveComplexity.sharpOneInSat_rel_ordered_parsimonious_sharpDirHamCircuit`).

The mathematics is in the three files before this one: the row graph of a CNF
formula (`DescriptiveComplexity.Problems.Hamilton.CountingGadget`) has exactly the
exactly-one models of the formula as Hamilton circuits
(`DescriptiveComplexity.HamGadget.modelEquiv`). What is left is to *draw* that graph
in the formula, first-order: a vertex is a tag and a pair of elements
(`DescriptiveComplexity.HamGadget.toVtx`), the vertices that exist are cut out by the
domain formula of a relativized interpretation
(`DescriptiveComplexity.HamGadget.domF`), and an arc is a formula on two such pairs
(`DescriptiveComplexity.HamGadget.stepF`). The interpreted universe is then the
vertex type of the row graph, arcs included
(`DescriptiveComplexity.HamGadget.vtxEquiv`, `DescriptiveComplexity.HamGadget.dgArc_iff`).

The reduction is relativized because a circuit spans the universe: a tagged
pair that is no vertex would have to lie on every circuit. It is ordered
because the rows are: the occurrences of a variable are laid out in the order
of the instance, and so are the variables.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace HamGadget

open Language Structure SatOcc

/-- Tags of the interpretation: the kinds of vertices of the row graph. -/
inductive HTag : Type
  /-- The entry of a row. -/
  | top
  /-- The left end of a row. -/
  | lft
  /-- The right end of a row. -/
  | rgt
  /-- The first padding of a row. -/
  | pad0
  /-- The left vertex of an occurrence of sign `s`. -/
  | ain (s : Bool)
  /-- The right vertex of an occurrence of sign `s`. -/
  | bout (s : Bool)
  /-- The padding after an occurrence of sign `s`. -/
  | pad (s : Bool)
  /-- A clause vertex. -/
  | cls
  /-- The vertex of a formula with no clause. -/
  | zero
  deriving DecidableEq

instance : Finite HTag := by
  let enc : HTag → Fin 9 × Bool := fun t =>
    match t with
    | .top => (0, false)
    | .lft => (1, false)
    | .rgt => (2, false)
    | .pad0 => (3, false)
    | .ain s => (4, s)
    | .bout s => (5, s)
    | .pad s => (6, s)
    | .cls => (7, false)
    | .zero => (8, false)
  refine Finite.of_injective enc fun u v h => ?_
  cases u <;> cases v <;> simp_all [enc]

/-- The vertex a tagged pair stands for. -/
def toVtx {A : Type} : HTag → A → A → Vtx A
  | .top, x, _ => .top x
  | .lft, x, _ => .lft x
  | .rgt, x, _ => .rgt x
  | .pad0, x, _ => .pad0 x
  | .ain s, x, c => .ain s x c
  | .bout s, x, c => .bout s x c
  | .pad s, x, c => .pad s x c
  | .cls, c, _ => .cls c
  | .zero, _, _ => .zero

/-! ### The formulas -/

section Formulas

variable {α : Type}

/-- `x` is a variable of the formula, as a formula. -/
noncomputable def varF (x : α) : satOrd.Formula α :=
  (clF (.inr ()) ⊓ (posF (.inr ()) (.inl x) ⊔ negF (.inr ()) (.inl x))).iExs Unit

/-- There is no clause, as a formula. -/
noncomputable def noClF : satOrd.Formula α :=
  ∼((clF (.inr ())).iExs Unit)

/-- `x` is the least element, as a formula. -/
noncomputable def botF (x : α) : satOrd.Formula α :=
  (leF (.inl x) (.inr ())).iAlls Unit

/-- `DescriptiveComplexity.HamGadget.VFirst`, as a formula. -/
noncomputable def vFirstF (x : α) : satOrd.Formula α :=
  varF x ⊓ Formula.iAlls Unit (varF (Sum.inr ()) ⟹ leF (Sum.inl x) (Sum.inr ()))

/-- `DescriptiveComplexity.HamGadget.VLast`, as a formula. -/
noncomputable def vLastF (x : α) : satOrd.Formula α :=
  varF x ⊓ Formula.iAlls Unit (varF (Sum.inr ()) ⟹ leF (Sum.inr ()) (Sum.inl x))

/-- `DescriptiveComplexity.HamGadget.VStep`, as a formula. -/
noncomputable def vStepF (x y : α) : satOrd.Formula α :=
  ((varF x ⊓ varF y) ⊓ ltF x y) ⊓
    ∼(((varF (.inr ()) ⊓ ltF (.inl x) (.inr ())) ⊓ ltF (.inr ()) (.inl y)).iExs Unit)

/-- `DescriptiveComplexity.HamGadget.NextVar`, as a formula. -/
noncomputable def nextVarF (x y : α) : satOrd.Formula α :=
  vStepF x y ⊔ (vLastF x ⊓ vFirstF y)

/-- A sign condition, as a formula. -/
def boolF (b : Bool) : satOrd.Formula α := if b then ⊤ else ⊥

/-- The domain formulas: which tagged pairs are vertices. -/
noncomputable def domF : HTag → satOrd.Formula (Fin 2)
  | .top => eqF 0 1 ⊓ varF 0
  | .lft => eqF 0 1 ⊓ varF 0
  | .rgt => eqF 0 1 ⊓ varF 0
  | .pad0 => eqF 0 1 ⊓ varF 0
  | .ain s => occF s 1 0
  | .bout s => occF s 1 0
  | .pad s => occF s 1 0
  | .cls => eqF 0 1 ⊓ clF 0
  | .zero => (eqF 0 1 ⊓ botF 0) ⊓ noClF

/-- The arc formulas, by tags: `DescriptiveComplexity.HamGadget.Step`, drawn. The free
variable `(i, j)` is the `j`-th component of the `i`-th vertex. -/
noncomputable def stepF : HTag → HTag → satOrd.Formula (Fin 2 × Fin 2)
  | .lft, .pad0 => eqF (0, 0) (1, 0)
  | .pad0, .lft => eqF (0, 0) (1, 0)
  | .pad0, .ain s => eqF (0, 0) (1, 0) ⊓ varMinF s (0, 0) (1, 1)
  | .ain s, .pad0 => eqF (1, 0) (0, 0) ⊓ varMinF s (1, 0) (0, 1)
  | .bout s, .pad s' => boolF (s == s') ⊓ (eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1))
  | .pad s, .bout s' => boolF (s == s') ⊓ (eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1))
  | .pad s, .ain s' => eqF (0, 0) (1, 0) ⊓ varStepF s s' (0, 0) (0, 1) (1, 1)
  | .ain s', .pad s => eqF (1, 0) (0, 0) ⊓ varStepF s s' (1, 0) (1, 1) (0, 1)
  | .pad s, .rgt => eqF (0, 0) (1, 0) ⊓ varMaxF s (0, 0) (0, 1)
  | .rgt, .pad s => eqF (1, 0) (0, 0) ⊓ varMaxF s (1, 0) (1, 1)
  | .ain s, .cls => boolF s ⊓ eqF (0, 1) (1, 0)
  | .cls, .bout s => boolF s ⊓ eqF (1, 1) (0, 0)
  | .bout s, .ain s' =>
      boolF s ⊓ (boolF s' ⊓ (eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1)))
  | .bout s, .cls => boolF (!s) ⊓ eqF (0, 1) (1, 0)
  | .cls, .ain s => boolF (!s) ⊓ eqF (1, 1) (0, 0)
  | .ain s, .bout s' =>
      boolF (!s) ⊓ (boolF (!s') ⊓ (eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1)))
  | .top, .lft => eqF (0, 0) (1, 0)
  | .top, .rgt => eqF (0, 0) (1, 0)
  | .lft, .top => nextVarF (0, 0) (1, 0)
  | .rgt, .top => nextVarF (0, 0) (1, 0)
  | .zero, .zero => ⊤
  | _, _ => ⊥

end Formulas

/-- The relativized interpretation drawing the row graph of a CNF formula. -/
noncomputable def hamInterp : RelFOInterpretation satOrd Language.digraph HTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .arc => fun t => stepF (t 0) (t 1)
  domFormula := domF

/-! ### Realization -/

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

theorem realize_varF {x : α} : (varF x).Realize v ↔ SatOccurs A (v x) := by
  simp only [varF, Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup, realize_clF,
    realize_posF, realize_negF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, h⟩ => ⟨i (), h⟩, fun ⟨c, h⟩ => ⟨fun _ => c, h⟩⟩

theorem realize_noClF : (noClF (α := α)).Realize v ↔ ¬∃ c : A, IsCl c := by
  simp only [noClF, Formula.realize_not, Formula.realize_iExs, realize_clF, Sum.elim_inr]
  exact not_congr ⟨fun ⟨i, h⟩ => ⟨i (), h⟩, fun ⟨c, h⟩ => ⟨fun _ => c, h⟩⟩

theorem realize_botF {x : α} : (botF x).Realize v ↔ IsBot (v x) := by
  simp only [botF, Formula.realize_iAlls, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h z => h fun _ => z, fun h i => h (i ())⟩

theorem realize_vFirstF {x : α} : (vFirstF x).Realize v ↔ VFirst (v x) := by
  simp only [vFirstF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_varF, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h z hz => h (fun _ => z) hz, fun h i hi => h (i ()) hi⟩

theorem realize_vLastF {x : α} : (vLastF x).Realize v ↔ VLast (v x) := by
  simp only [vLastF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_varF, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h z hz => h (fun _ => z) hz, fun h i hi => h (i ()) hi⟩

theorem realize_vStepF {x y : α} : (vStepF x y).Realize v ↔ VStep (v x) (v y) := by
  simp only [vStepF, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    realize_varF, realize_ltF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
    exact ⟨h₁, h₂, h₃, fun z hz hzz => h₄ ⟨fun _ => z, ⟨hz, hzz.1⟩, hzz.2⟩⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨i, ⟨hz, h₅⟩, h₆⟩ => h₄ (i ()) hz ⟨h₅, h₆⟩⟩

theorem realize_nextVarF {x y : α} : (nextVarF x y).Realize v ↔ NextVar (v x) (v y) := by
  simp only [nextVarF, Formula.realize_sup, Formula.realize_inf, realize_vStepF,
    realize_vLastF, realize_vFirstF, NextVar]

theorem realize_boolF {b : Bool} : (boolF (α := α) b).Realize v ↔ b = true := by
  cases b <;> simp [boolF]

/-- Which pairs of elements are vertices, by tag. -/
def Dom : HTag → A → A → Prop
  | .top, x, y => x = y ∧ SatOccurs A x
  | .lft, x, y => x = y ∧ SatOccurs A x
  | .rgt, x, y => x = y ∧ SatOccurs A x
  | .pad0, x, y => x = y ∧ SatOccurs A x
  | .ain s, x, c => OccIn c x s
  | .bout s, x, c => OccIn c x s
  | .pad s, x, c => OccIn c x s
  | .cls, c, y => c = y ∧ IsCl c
  | .zero, x, y => (x = y ∧ IsBot x) ∧ ¬∃ c : A, IsCl c

theorem realize_domF {t : HTag} {w : Fin 2 → A} :
    (domF t).Realize w ↔ Dom t (w 0) (w 1) := by
  cases t <;>
    simp only [domF, Dom, Formula.realize_inf, realize_eqF, realize_varF, realize_occF,
      realize_clF, realize_botF, realize_noClF]

theorem realize_stepF {t₁ t₂ : HTag} {v : Fin 2 × Fin 2 → A} :
    (stepF t₁ t₂).Realize v ↔
      Step (toVtx t₁ (v (0, 0)) (v (0, 1))) (toVtx t₂ (v (1, 0)) (v (1, 1))) := by
  cases t₁ <;> cases t₂ <;>
    simp [stepF, Step, toVtx, realize_boolF, realize_varMinF, realize_varMaxF,
      realize_varStepF, realize_nextVarF]

end Realize

/-! ### The interpreted universe is the vertex type of the row graph -/

section Universe

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

theorem valid_toVtx {t : HTag} {x y : A} (h : Dom t x y) : Valid (toVtx t x y) := by
  cases t
  exacts [h.2, h.2, h.2, h.2, h, h, h, h.2, h.2]

theorem toVtx_inj {t t' : HTag} {x y x' y' : A} (h : Dom t x y) (h' : Dom t' x' y')
    (he : toVtx t x y = toVtx t' x' y') : t = t' ∧ x = x' ∧ y = y' := by
  cases t <;> cases t' <;>
    simp only [toVtx, Vtx.top.injEq, Vtx.lft.injEq, Vtx.rgt.injEq, Vtx.pad0.injEq,
      Vtx.ain.injEq, Vtx.bout.injEq, Vtx.pad.injEq, Vtx.cls.injEq, reduceCtorEq] at he
  all_goals
    first
      | exact ⟨rfl, he, h.1.symm.trans (he.trans h'.1)⟩
      | exact ⟨by rw [he.1], he.2.1, he.2.2⟩
      | exact ⟨rfl, le_antisymm (h.1.2 _) (h'.1.2 _),
          (h.1.1.symm.trans (le_antisymm (h.1.2 _) (h'.1.2 _))).trans h'.1.1⟩

/-- The vertex of a point of the interpreted universe. -/
def vtxOf (p : hamInterp.MapRel A) : {v : Vtx A // Valid v} :=
  ⟨toVtx p.1.1 (p.1.2 0) (p.1.2 1), valid_toVtx (realize_domF.mp p.2)⟩

theorem vtxOf_injective : Function.Injective (vtxOf (A := A)) := by
  intro p q hpq
  obtain ⟨ht, h0, h1⟩ := toVtx_inj (realize_domF.mp p.2) (realize_domF.mp q.2)
    (congrArg Subtype.val hpq)
  refine Subtype.ext (Prod.ext ht (funext fun j => ?_))
  fin_cases j
  exacts [h0, h1]

theorem vtxOf_surjective [Finite A] [Nonempty A] : Function.Surjective (vtxOf (A := A)) := by
  have mk : ∀ (t : HTag) (x y : A), Dom t x y →
      ∃ p : hamInterp.MapRel A, (vtxOf p).1 = toVtx t x y := fun t x y h =>
    ⟨⟨(t, ![x, y]), realize_domF.mpr h⟩, rfl⟩
  rintro ⟨v, hv⟩
  suffices h : ∃ p : hamInterp.MapRel A, (vtxOf p).1 = v by
    obtain ⟨p, hp⟩ := h
    exact ⟨p, Subtype.ext hp⟩
  cases v with
  | top x => exact mk .top x x ⟨rfl, hv⟩
  | lft x => exact mk .lft x x ⟨rfl, hv⟩
  | rgt x => exact mk .rgt x x ⟨rfl, hv⟩
  | pad0 x => exact mk .pad0 x x ⟨rfl, hv⟩
  | ain s x c => exact mk (.ain s) x c hv
  | bout s x c => exact mk (.bout s) x c hv
  | pad s x c => exact mk (.pad s) x c hv
  | cls c => exact mk .cls c c ⟨rfl, hv⟩
  | zero =>
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
    exact mk .zero a₀ a₀ ⟨⟨rfl, ha₀⟩, hv⟩

/-- **The interpreted universe is the vertex type of the row graph.** -/
noncomputable def vtxEquiv (A : Type) [Language.sat.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] : hamInterp.MapRel A ≃ {v : Vtx A // Valid v} :=
  Equiv.ofBijective vtxOf ⟨vtxOf_injective, vtxOf_surjective⟩

/-- **The interpreted arcs are the arcs of the row graph.** -/
theorem dgArc_iff (p q : hamInterp.MapRel A) : DGArc p q ↔ Arc (vtxOf p).1 (vtxOf q).1 := by
  have h := realize_stepF (A := A) (t₁ := p.1.1) (t₂ := q.1.1)
    (v := fun pr : Fin 2 × Fin 2 => (![p, q] pr.1).1.2 pr.2)
  change RelMap dgArc ![p, q] ↔ _
  rw [RelFOInterpretation.relMap_mapRel]
  exact h.trans ⟨fun hs => ⟨(vtxOf p).2, (vtxOf q).2, hs⟩, fun ha => ha.2.2⟩

variable (A) [Finite A] [Nonempty A]

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpDirHamCircuit_mapRel :
    SharpDirHamCircuit (hamInterp.MapRel A) = SharpOneInSAT A := by
  have := hamInterp.mapRel_finite A
  have hW : Finite {v : Vtx A // Valid v} := Finite.of_equiv _ (vtxEquiv A)
  rw [sharpDirHamCircuit_apply, sharpOneInSat_apply]
  refine (Nat.card_congr (circuitEquiv (vtxEquiv A) (RB := fun u v => Arc u.1 v.1)
    fun p q => dgArc_iff p q)).trans ?_
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hW)).trans ?_
  exact (Nat.card_congr (modelEquiv A)).symm

end Universe

end HamGadget

open HamGadget in
/-- **#1-in-SAT reduces parsimoniously to #Directed Hamilton Circuit**, by a
relativized interpretation: the tagged pairs that are no vertex of the row
graph are left out of the universe. -/
noncomputable def sharpOneInSat_rel_ordered_parsimonious_sharpDirHamCircuit :
    SharpOneInSAT ≤ʳᵖ[≤] SharpDirHamCircuit where
  Tag := HTag
  dim := 2
  toRelInterpretation := hamInterp
  dom_nonempty A _ _ _ _ := by
    have hW : Nonempty {v : Vtx A // Valid v} := by
      by_cases hcl : ∃ c : A, SatOcc.IsCl c
      · obtain ⟨c, hc⟩ := hcl
        exact ⟨⟨.cls c, hc⟩⟩
      · exact ⟨⟨.zero, hcl⟩⟩
    obtain ⟨w⟩ := hW
    obtain ⟨⟨⟨t, x⟩, hp⟩, -⟩ := vtxOf_surjective w
    exact ⟨t, x, hp⟩
  correct A _ _ _ _ := (sharpDirHamCircuit_mapRel A).symm

/-- #Directed Hamilton Circuit is parsimoniously `#P`-hard. -/
theorem sharpDirHamCircuit_sharpP_parsimoniousHard :
    SharpP.ParsimoniousHard SharpDirHamCircuit :=
  SharpP.parsimoniousHard_of_relOrderedParsimonious
    sharpOneInSat_rel_ordered_parsimonious_sharpDirHamCircuit
    sharpOneInSat_sharpP_parsimoniousHard

/-- **#Directed Hamilton Circuit is parsimoniously `#P`-complete**: counting
the Hamilton circuits of a digraph. -/
theorem sharpDirHamCircuit_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpDirHamCircuit :=
  ⟨sharpDirHamCircuit_mem_sharpP, sharpDirHamCircuit_sharpP_parsimoniousHard⟩

end DescriptiveComplexity
