/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.IsoGadget

/-!
# Two marked copies of a vocabulary, and the isomorphism problem they carry

Every problem of the GI degree has the same shape: one universe holding two
marked structures over the same vocabulary, and the question whether they are
isomorphic. `DescriptiveComplexity.Problems.DigraphIso` and
`DescriptiveComplexity.Problems.DagIso` each hand-roll that shape
(`FirstOrder.Language.twoGraphs`, `FirstOrder.Language.twoDags`), which is fine
for one problem and wasteful for a family.

`FirstOrder.Language.twoCopies L₁` builds it once: two unary marks, and two
copies of every relation symbol of `L₁`. A structure over it carries an
`L₁`-structure on each marked set
(`DescriptiveComplexity.patSideStructure`,
`DescriptiveComplexity.hostSideStructure`), and
`DescriptiveComplexity.TwoCopiesIso` is the decision problem asking whether
those two `L₁`-structures are isomorphic.

The reason to have it is the *gadget* layer this file is written for: a
construction on single `L₁`-structures can be doubled – run relativized to each
mark – only if the target vocabulary is known to be two copies of something,
since the defining formulas have to be given symbol by symbol. Problems added
to the degree from here on should be stated over `twoCopies`; the two existing
hand-rolled vocabularies stay as they are, their results being already proved.
-/

namespace FirstOrder

namespace Language

/-- Relation symbols of the two-copy vocabulary: a mark for each side, and two
copies of every relation symbol of the base vocabulary. -/
inductive twoCopiesRel (L₁ : Language.{0, 0}) : ℕ → Type
  /-- `patMark a`: `a` belongs to the pattern side. -/
  | patMark : twoCopiesRel L₁ 1
  /-- `hostMark a`: `a` belongs to the host side. -/
  | hostMark : twoCopiesRel L₁ 1
  /-- The pattern copy of a relation symbol of the base vocabulary. -/
  | pat {n : ℕ} (r : L₁.Relations n) : twoCopiesRel L₁ n
  /-- The host copy of a relation symbol of the base vocabulary. -/
  | host {n : ℕ} (r : L₁.Relations n) : twoCopiesRel L₁ n

/-- Two marked copies of a relational vocabulary, sharing one universe. -/
protected def twoCopies (L₁ : Language.{0, 0}) : Language :=
  ⟨fun _ => Empty, twoCopiesRel L₁⟩

instance twoCopies_isRelational (L₁ : Language.{0, 0}) : (Language.twoCopies L₁).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- The pattern mark. -/
abbrev tcPatMark (L₁ : Language.{0, 0}) : (Language.twoCopies L₁).Relations 1 := .patMark

/-- The host mark. -/
abbrev tcHostMark (L₁ : Language.{0, 0}) : (Language.twoCopies L₁).Relations 1 := .hostMark

/-- The pattern copy of a base relation symbol. -/
abbrev tcPat {L₁ : Language.{0, 0}} {n : ℕ} (r : L₁.Relations n) :
    (Language.twoCopies L₁).Relations n := .pat r

/-- The host copy of a base relation symbol. -/
abbrev tcHost {L₁ : Language.{0, 0}} {n : ℕ} (r : L₁.Relations n) :
    (Language.twoCopies L₁).Relations n := .host r

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Sides

variable {L₁ : Language.{0, 0}} [L₁.IsRelational] {A : Type}
variable [(Language.twoCopies L₁).Structure A]

/-- Belonging to the pattern side. -/
def TCPatMark (a : A) : Prop := RelMap (tcPatMark L₁) ![a]

/-- Belonging to the host side. -/
def TCHostMark (a : A) : Prop := RelMap (tcHostMark L₁) ![a]

/-- The pattern side, as a structure over the base vocabulary. -/
instance patSideStructure : L₁.Structure {x : A // TCPatMark (L₁ := L₁) x} where
  funMap f := isEmptyElim f
  RelMap {_} r w := RelMap (tcPat r) fun i => (w i).1

/-- The host side, as a structure over the base vocabulary. -/
instance hostSideStructure : L₁.Structure {x : A // TCHostMark (L₁ := L₁) x} where
  funMap f := isEmptyElim f
  RelMap {_} r w := RelMap (tcHost r) fun i => (w i).1

/-- An isomorphism of the two sides, over the base vocabulary. -/
abbrev TCSideEquiv (A : Type) [(Language.twoCopies L₁).Structure A] : Type :=
  {x : A // TCPatMark (L₁ := L₁) x} ≃[L₁] {y : A // TCHostMark (L₁ := L₁) y}

end Sides

/-! ### Isomorphism-invariance -/

section Invariance

variable {L₁ : Language.{0, 0}} [L₁.IsRelational] {A B : Type}
variable [(Language.twoCopies L₁).Structure A] [(Language.twoCopies L₁).Structure B]

/-- An isomorphism of the ambient structures restricts to the pattern sides. -/
def patSideMap (e : A ≃[Language.twoCopies L₁] B) (x : {x : A // TCPatMark (L₁ := L₁) x}) :
    {y : B // TCPatMark (L₁ := L₁) y} :=
  ⟨e x.1, by
    have h := relMap_equiv₁ e (tcPatMark L₁) x.1
    exact h.mp x.2⟩

/-- An isomorphism of the ambient structures restricts to the host sides. -/
def hostSideMap (e : A ≃[Language.twoCopies L₁] B) (x : {x : A // TCHostMark (L₁ := L₁) x}) :
    {y : B // TCHostMark (L₁ := L₁) y} :=
  ⟨e x.1, by
    have h := relMap_equiv₁ e (tcHostMark L₁) x.1
    exact h.mp x.2⟩

/-- The restriction of an ambient isomorphism to the pattern sides is itself an
isomorphism over the base vocabulary. -/
def patSideEquiv (e : A ≃[Language.twoCopies L₁] B) :
    {x : A // TCPatMark (L₁ := L₁) x} ≃[L₁] {y : B // TCPatMark (L₁ := L₁) y} where
  toFun := patSideMap e
  invFun := patSideMap e.symm
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_fun' f := isEmptyElim f
  map_rel' {n} r x := by
    have h := e.map_rel' (tcPat r) fun i => (x i).1
    exact h

/-- The restriction of an ambient isomorphism to the host sides. -/
def hostSideEquiv (e : A ≃[Language.twoCopies L₁] B) :
    {x : A // TCHostMark (L₁ := L₁) x} ≃[L₁] {y : B // TCHostMark (L₁ := L₁) y} where
  toFun := hostSideMap e
  invFun := hostSideMap e.symm
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_fun' f := isEmptyElim f
  map_rel' {n} r x := by
    have h := e.map_rel' (tcHost r) fun i => (x i).1
    exact h

/-- Isomorphic sides transport along an isomorphism of the ambient
structures. -/
theorem nonempty_tcSideEquiv_congr (e : A ≃[Language.twoCopies L₁] B) :
    Nonempty (TCSideEquiv (L₁ := L₁) A) ↔ Nonempty (TCSideEquiv (L₁ := L₁) B) :=
  ⟨fun ⟨i⟩ => ⟨((hostSideEquiv e).comp i).comp (patSideEquiv e).symm⟩,
    fun ⟨i⟩ => ⟨((hostSideEquiv e).symm.comp i).comp (patSideEquiv e)⟩⟩

end Invariance

/-- **The isomorphism problem of a vocabulary**: are the two marked
`L₁`-structures of the instance isomorphic? Every entry of the GI degree added
from here on is an instance of this shape. -/
def TwoCopiesIso (L₁ : Language.{0, 0}) [L₁.IsRelational] :
    DecisionProblem (Language.twoCopies L₁) where
  Holds := fun A _inst => Finite A ∧ Nonempty (TCSideEquiv (L₁ := L₁) A)
  iso_invariant := fun e => and_congr e.toEquiv.finite_iff (nonempty_tcSideEquiv_congr e)

end DescriptiveComplexity
