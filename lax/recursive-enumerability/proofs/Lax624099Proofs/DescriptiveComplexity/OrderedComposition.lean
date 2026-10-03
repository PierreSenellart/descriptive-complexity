/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Composition
import Lax624099Proofs.DescriptiveComplexity.Ordered
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099Proofs.DescriptiveComplexity.FOInterpretation
end Lax624099Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax624099Proofs.DescriptiveComplexity.FOReduction
end Lax624099Proofs.DescriptiveComplexity.FOReduction

namespace Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction

/-!
# Composition of ordered first-order reductions

Transitivity of `P ≤ᶠᵒ[≤] Q` (`Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction.trans`), and the
mixed variants with plain FO reductions.

The obstacle to composing two ordered reductions with the plain composition
of `Lax624099Proofs.DescriptiveComplexity.Composition` is that the outer reduction's formulas mention
the *order of the intermediate structure*, which is not part of the inner
interpretation's output. The fix is classical: the interpreted universe
`Tag × A^dim` carries a linear order that is first-order definable from the
order of `A` – the lexicographic order comparing tags first (by an arbitrary
fixed linear order on the finite tag type; tag comparisons are static, i.e.,
resolved at formula-construction time), then the tuple coordinates in order.

Concretely:

* `Lax624099Proofs.DescriptiveComplexity.tagTupleLe` is the lexicographic order on `Tag × (Fin d → A)`,
  bundled as `Lax624099Proofs.DescriptiveComplexity.tagTupleOrder : LinearOrder (Tag × (Fin d → A))`
  (via Mathlib's `Prod.Lex` and `Pi.Lex`);
* `Lax624099Proofs.DescriptiveComplexity.lexLeF` is the corresponding first-order formula over the
  ordered expansion, with realization lemma `Lax624099Proofs.DescriptiveComplexity.realize_lexLeF`;
* `Lax624099Proofs.DescriptiveComplexity.FOInterpretation.ordExtend` extends an interpretation with
  target `L₂` to one with target `L₂.sum Language.order`, interpreting the
  order symbol by `lexLeF`; the interpreted structure is isomorphic to the
  original one equipped with the lexicographic order
  (`Lax624099Proofs.DescriptiveComplexity.FOInterpretation.ordExtendLEquiv`);
* `Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction.trans` composes the outer interpretation
  with the extended inner one, using `FOInterpretation.comp`;
* `Lax624099Proofs.DescriptiveComplexity.FOReduction.toOrdered` upgrades a plain FO reduction to an
  ordered one (lifting its formulas along `LHom.sumInl`), giving the mixed
  transitivity variants `Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction.trans_fo` and
  `Lax624099Proofs.DescriptiveComplexity.FOReduction.trans_ordered`, and `Trans` instances for all
  combinations.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### A linear order on any finite type -/

/-- An arbitrary linear order on a finite type, obtained by pulling back the
order of `Fin n` along an arbitrary enumeration. Used to order tags. -/
@[instance_reducible]
noncomputable def finiteLinearOrder (T : Type) [Finite T] : LinearOrder T :=
  letI := Fintype.ofFinite T
  LinearOrder.lift' (Fintype.equivFin T) (Fintype.equivFin T).injective

/-! ### The lexicographic order on tagged tuples -/

section LexOrder

variable {Tag : Type} [LinearOrder Tag] {d : ℕ} {A : Type} [LinearOrder A]

/-- Lexicographic comparison of tuples: equality, or agreement up to a
position where the left tuple is smaller. -/
def tupLeLex (x y : Fin d → A) : Prop :=
  x = y ∨ ∃ j, (∀ i, i < j → x i = y i) ∧ x j < y j

/-- The lexicographic order on tagged tuples: tags first, then the
coordinates in order. -/
def tagTupleLe (p q : Tag × (Fin d → A)) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ tupLeLex p.2 q.2)

/-- Embedding into Mathlib's lexicographic order types. -/
private def lexEmbed (p : Tag × (Fin d → A)) : Tag ×ₗ Lex (Fin d → A) :=
  toLex (p.1, toLex p.2)

omit [LinearOrder Tag] [LinearOrder A] in
private theorem lexEmbed_injective :
    Function.Injective (lexEmbed (Tag := Tag) (d := d) (A := A)) := by
  intro p q h
  have h' : (p.1, toLex p.2) = (q.1, toLex q.2) := toLex.injective h
  obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ h'
  exact Prod.ext_iff.mpr ⟨h1, toLex.injective h2⟩

private theorem tagTupleLe_iff (p q : Tag × (Fin d → A)) :
    tagTupleLe p q ↔ lexEmbed p ≤ lexEmbed q := by
  rw [lexEmbed, lexEmbed, Prod.Lex.toLex_le_toLex]
  constructor
  · rintro (h | ⟨he, he2 | hlt⟩)
    · exact Or.inl h
    · exact Or.inr ⟨he, le_of_eq (congrArg toLex he2)⟩
    · exact Or.inr ⟨he, le_of_lt hlt⟩
  · rintro (h | ⟨he, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨he, ?_⟩
      rcases lt_or_eq_of_le h2 with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (toLex.injective heq)

/-- The lexicographic linear order on tagged tuples, lifted along
`lexEmbed`; its `≤` is characterized by `tagTupleLe_iff`. -/
@[instance_reducible]
noncomputable def tagTupleOrder : LinearOrder (Tag × (Fin d → A)) :=
  LinearOrder.lift' lexEmbed lexEmbed_injective

/-- The relation `tagTupleLe` is the `≤` of `tagTupleOrder`. (Public companion
to the private `tagTupleLe_iff`, for use in relativized composition.) -/
theorem tagTupleLe_iff_le (p q : Tag × (Fin d → A)) :
    tagTupleLe p q ↔ (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le p q :=
  tagTupleLe_iff p q

end LexOrder

/-! ### First-order formulas for the lexicographic order -/

section LexFormulas

variable {L : Language.{0, 0}}

/-- `x = y`, as a formula over the ordered expansion. -/
private def oEqF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- `x ≤ y`, as a formula over the ordered expansion. -/
private def oLeF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x < y`, as a formula over the ordered expansion. -/
private def oLtF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  oLeF x y ⊓ ∼(oEqF x y)

variable {A : Type} [L.Structure A] [LinearOrder A] {α : Type} {v : α → A}

@[simp]
private theorem realize_oEqF {x y : α} : (oEqF (L := L) x y).Realize v ↔ v x = v y := by
  simp [oEqF]

@[simp]
private theorem realize_oLeF {x y : α} : (oLeF (L := L) x y).Realize v ↔ v x ≤ v y := by
  simp [oLeF, Formula.realize_rel₂]

@[simp]
private theorem realize_oLtF {x y : α} : (oLtF (L := L) x y).Realize v ↔ v x < v y := by
  simp [oLtF, lt_iff_le_and_ne]

variable (L) in
/-- Lexicographic comparison of two `d`-tuples (the two arguments of a binary
relation), as a formula over the ordered expansion. -/
noncomputable def lexTupleLeF (d : ℕ) : (L.sum Language.order).Formula (Fin 2 × Fin d) :=
  (Formula.iInf fun i : Fin d => oEqF (0, i) (1, i)) ⊔
    Formula.iSup fun j : Fin d =>
      (Formula.iInf fun i : {i : Fin d // i < j} => oEqF (0, i.1) (1, i.1)) ⊓
        oLtF (0, j) (1, j)

theorem realize_lexTupleLeF {d : ℕ} {v : Fin 2 × Fin d → A} :
    (lexTupleLeF L d).Realize v ↔
      tupLeLex (fun i => v (0, i)) (fun i => v (1, i)) := by
  simp only [lexTupleLeF, Formula.realize_sup, Formula.realize_iSup, Formula.realize_iInf,
    Formula.realize_inf, realize_oEqF, realize_oLtF, Subtype.forall]
  rw [tupLeLex, funext_iff]

open Classical in
variable (L) in
/-- The full lexicographic comparison of tagged tuples, as a formula over the
ordered expansion: the tags are compared statically. -/
noncomputable def lexLeF {Tag : Type} [LinearOrder Tag] (d : ℕ) (t₁ t₂ : Tag) :
    (L.sum Language.order).Formula (Fin 2 × Fin d) :=
  if t₁ = t₂ then lexTupleLeF L d else if t₁ < t₂ then ⊤ else ⊥

theorem realize_lexLeF {Tag : Type} [LinearOrder Tag] {d : ℕ} {t₁ t₂ : Tag}
    {v : Fin 2 × Fin d → A} :
    (lexLeF L d t₁ t₂).Realize v ↔
      tagTupleLe (t₁, fun i => v (0, i)) (t₂, fun i => v (1, i)) := by
  rcases eq_or_ne t₁ t₂ with rfl | hne
  · rw [lexLeF, if_pos rfl, realize_lexTupleLeF]
    simp [tagTupleLe]
  · rw [lexLeF, if_neg hne]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [if_pos hlt]
      simp [tagTupleLe, hlt]
    · rw [if_neg (not_lt_of_gt hgt)]
      simp only [Formula.realize_bot, false_iff]
      rintro (h | ⟨he, -⟩)
      · exact absurd h (not_lt_of_gt hgt)
      · exact hne he

end LexFormulas

/-! ### Extending an interpretation with the lexicographic order -/

section OrdExtend

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational]

variable {T : Type} [LinearOrder T] {d : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation (L₁.sum Language.order) L₂ T d)

variable (A : Type) [L₁.Structure A] [LinearOrder A]

end OrdExtend

/-! ### Transitivity -/

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂} {R : Lax904597.Problems.DecisionProblem L₃}

/-- A plain FO reduction is in particular an ordered FO reduction: lift its
defining formulas to the ordered expansion (they simply ignore the order). -/
noncomputable def FOReduction.toOrdered (g : P ≤ᶠᵒ Q) : P ≤ᶠᵒ[≤] Q :=
  letI := g.tagFinite
  letI := g.tagNonempty
  { Tag := g.Tag
    dim := g.dim
    toInterpretation :=
      { relFormula := fun R t => LHom.sumInl.onFormula (g.toInterpretation.relFormula R t) }
    correct := fun A _ _ _ _ => by
      refine (g.correct A).trans (Q.iso_invariant ?_)
      exact
        { toEquiv := Equiv.refl _
          map_fun' := fun f => isEmptyElim f
          map_rel' := fun {n} R x => by
            rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
            exact LHom.realize_onFormula _ _ } }

end Trans

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOReduction

export Lax624099Proofs.DescriptiveComplexity.FOReduction (toOrdered)

end Lax904597.Interpretations.FOReduction

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂} {R : Lax904597.Problems.DecisionProblem L₃}

end Trans

end Lax624099Proofs.DescriptiveComplexity


