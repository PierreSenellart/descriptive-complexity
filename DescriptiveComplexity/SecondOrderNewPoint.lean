/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewRead
import DescriptiveComplexity.Exponential.Expansion

/-!
# Which invented values are points, and what the expanded relations say of them

An invented value stands for a tagged assignment of the expansion's block: the
assignment is what the guessed meaning relations give it
(`DescriptiveComplexity.SecondOrderNewRead`), and the tag is carried the same
way, by one nullary variable of the block per tag – so a unary symbol on the
extended universe. Neither is a *point* of the expanded universe on its own:
a point carries exactly one tag, and its assignment satisfies that tag's domain
sentence. Both are first-order statements about the value, and this file writes
them.

* `DescriptiveComplexity.isPointF` – “this value is a point”: exactly one tag
  symbol holds of it, and the domain sentence of that tag, read through the
  meanings among the original elements, holds.
* `DescriptiveComplexity.pointRelF` – “this relation of the expanded vocabulary
  holds of these values”: one disjunct per tuple of tags, guarded by the tag
  symbols of the values, whose body is the defining sentence at that tuple, read
  the same way. The tags are guessed here, where everywhere else in the library
  they are chosen when the formula is built, so a static tuple will not do;
  there are finitely many, so the disjunction is finite.

Both are written over an abstract target vocabulary
(`DescriptiveComplexity.PointSyms` names the symbols and nothing else), and both
are formulas with free variables of an arbitrary type, so that the assembly can
plug them under whatever quantifiers it needs.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure ExpExpansion

variable {L Lt : Language.{0, 0}} [L.IsRelational] {X : ExpExpansion L}

/-! ### The symbols -/

/-- The symbols the point formulas use in the target vocabulary: those the
translation through the meanings needs, one unary symbol per tag, and the marker
of the original elements. -/
structure PointSyms (L : Language.{0, 0}) (X : ExpExpansion L) (Lt : Language.{0, 0}) where
  /-- The symbols the defining sentences are read at. -/
  read : ReadSyms L X.B Lt
  /-- “this value carries the tag `t`”. -/
  tag : X.Tag → Lt.Relations 1
  /-- The marker of the original elements. -/
  old : Lt.Relations 1

variable (P : PointSyms L X Lt) {α : Type}

/-! ### The formulas -/

/-- The atom “the value held by `v` carries the tag `t`”. -/
def tagF (t : X.Tag) (v : α) : Lt.Formula α :=
  Relations.formula (P.tag t) fun _ => Term.var v

open Classical in
/-- **“The value held by `v` is a point of the expanded universe”**: it carries
exactly one tag, and the domain sentence of that tag holds of the assignment it
means. -/
noncomputable def isPointF (v : α) : Lt.Formula α :=
  Formula.iSup fun t : X.Tag =>
    (tagF P t v ⊓ Formula.iInf fun t' : X.Tag => if t' = t then ⊤ else ∼(tagF P t' v)) ⊓
      Formula.relabel (fun _ => v)
        ((readHom₁ P.read).relOnSentenceF P.old (X.dom t))

/-- **“The relation `r` of the expanded vocabulary holds of the values held by
`vs`”**: one disjunct per tuple of tags, guarded by the tag atoms of those
values, whose body is the defining sentence at that tuple, read through the
meanings among the original elements. -/
noncomputable def pointRelF {k : ℕ} (r : X.E.Relations k) (vs : Fin k → α) : Lt.Formula α :=
  Formula.iSup fun τ : Fin k → X.Tag =>
    (Formula.iInf fun j : Fin k => tagF P (τ j) (vs j)) ⊓
      Formula.relabel vs ((readHom P.read k).relOnSentenceF P.old (X.relSentence r τ))

/-! ### What they say -/

section Realize

variable {P} {M A : Type} [Lt.Structure M] [L.Structure A] [LinearOrder A]
variable {e : A → M} {means : M → X.B.Assignment A} {tags : M → X.Tag → Prop}

/-- The readings the point formulas promise, beyond those of
`DescriptiveComplexity.ReadOn`: the tag symbols are the tags a value carries,
and the marker marks the original elements. -/
structure PointOn (P : PointSyms L X Lt) (e : A → M) (means : M → X.B.Assignment A)
    (tags : M → X.Tag → Prop) : Prop where
  /-- The translation reads what it should. -/
  read : ReadOn P.read e means
  /-- The original elements are exactly the marked ones. -/
  old : ∀ x : M, RelMap P.old ![x] ↔ ∃ a : A, e a = x
  /-- The tag symbols are the tags a value carries. -/
  tag : ∀ (v : M) (t : X.Tag), RelMap (P.tag t) (fun _ => v) ↔ tags v t

variable (hinj : Function.Injective e) (h : PointOn P e means tags)

omit [L.IsRelational] in
include h in
theorem realize_tagF (t : X.Tag) (v : α) (w : α → M) :
    (tagF P t v).Realize w ↔ tags (w v) t := by
  rw [tagF, Formula.realize_rel]
  exact h.tag (w v) t

include hinj h in
/-- **`DescriptiveComplexity.isPointF` says that the value is a point**: it
carries one tag and no other, and its assignment satisfies that tag's domain
sentence. -/
theorem realize_isPointF (v : α) (w : α → M) :
    (isPointF P v).Realize w ↔
      ∃ t : X.Tag, tags (w v) t ∧ (∀ t' : X.Tag, tags (w v) t' → t' = t) ∧
        DomHolds (X := X) (t, means (w v)) := by
  classical
  rw [isPointF, Formula.realize_iSup]
  refine exists_congr fun t => ?_
  rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_iInf,
    Formula.realize_relabel, realize_tagF h]
  have hdom : ((readHom₁ P.read).relOnSentenceF P.old (X.dom t)).Realize
      (w ∘ fun _ : Unit => v) ↔ DomHolds (X := X) (t, means (w v)) :=
    realize_readHom₁ h.read hinj h.old (w v) (X.dom t)
  rw [hdom]
  rw [and_assoc]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine forall_congr' fun t' => ?_
  by_cases ht : t' = t
  · rw [if_pos ht]
    exact ⟨fun _ h' => ht, fun _ => Formula.realize_top.mpr trivial⟩
  · rw [if_neg ht, Formula.realize_not, realize_tagF h]
    exact ⟨fun hn h' => absurd h' hn, fun hn h' => ht (hn h')⟩

include hinj h in
/-- **`DescriptiveComplexity.pointRelF` says that the relation holds**, provided
the values carry the tags: some tuple of tags is the one the values carry, and
the defining sentence at that tuple holds of the assignments they mean. -/
theorem realize_pointRelF {k : ℕ} (r : X.E.Relations k) (vs : Fin k → α) (w : α → M) :
    (pointRelF P r vs).Realize w ↔
      ∃ τ : Fin k → X.Tag, (∀ j, tags (w (vs j)) (τ j)) ∧
        @Sentence.Realize _ A
          ((X.B.replicate k).structure₁ (L := L.sum Language.order)
            (X.B.replicateAssign fun j => means (w (vs j))))
          (X.relSentence r τ) := by
  rw [pointRelF, Formula.realize_iSup]
  refine exists_congr fun τ => ?_
  rw [Formula.realize_inf, Formula.realize_iInf, Formula.realize_relabel]
  refine and_congr (forall_congr' fun j => realize_tagF h _ _ _) ?_
  exact realize_readHom h.read hinj h.old (fun j => w (vs j)) (X.relSentence r τ)

end Realize

end DescriptiveComplexity
