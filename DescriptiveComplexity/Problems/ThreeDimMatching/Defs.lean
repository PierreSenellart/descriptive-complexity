/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation

/-!
# 3-dimensional matching: definition

3-DIMENSIONAL MATCHING ([Karp 1972][karp1972reducibility]): given three
marked classes and a set of triples, one element from each class, is there a
set of triples covering every marked element **exactly once**?

The vocabulary `FirstOrder.Language.tripleSys` carries three unary marks
`xEl`, `yEl`, `zEl` and one ternary relation `trip`. A yes-instance is one
admitting a *matching* (`DescriptiveComplexity.IsMatchingOn`): a sub-relation of
`trip`, inside the three classes, that covers each marked element exactly
once. Nothing asks the three classes to be disjoint or to exhaust the
universe: elements outside them ride along, and the reduction of
`DescriptiveComplexity.Problems.ThreeDimMatching.Hardness` produces disjoint ones
anyway.

Perfect matchings force the three classes to have the same size, which is why
the problem is the tripartite form of Exact Cover with sets of size three, and
why it is the natural source of the exact-cover family.
-/

/- The language of triple systems lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of triple systems. -/
inductive tripleSysRel : ℕ → Type
  /-- `xEl a`: `a` belongs to the first class. -/
  | xEl : tripleSysRel 1
  /-- `yEl a`: `a` belongs to the second class. -/
  | yEl : tripleSysRel 1
  /-- `zEl a`: `a` belongs to the third class. -/
  | zEl : tripleSysRel 1
  /-- `trip a b c`: `(a, b, c)` is one of the available triples. -/
  | trip : tripleSysRel 3
  deriving DecidableEq

/-- The relational language of triple systems: three marked classes and a
ternary relation. -/
protected def tripleSys : Language :=
  ⟨fun _ => Empty, tripleSysRel⟩
  deriving IsRelational

/-- The first-class symbol. -/
abbrev tsX : Language.tripleSys.Relations 1 := .xEl

/-- The second-class symbol. -/
abbrev tsY : Language.tripleSys.Relations 1 := .yEl

/-- The third-class symbol. -/
abbrev tsZ : Language.tripleSys.Relations 1 := .zEl

/-- The triple symbol. -/
abbrev tsTrip : Language.tripleSys.Relations 3 := .trip

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Language.tripleSys.Structure A]

/-- Belonging to the first class. -/
def TSXEl (a : A) : Prop := RelMap tsX ![a]

/-- Belonging to the second class. -/
def TSYEl (a : A) : Prop := RelMap tsY ![a]

/-- Belonging to the third class. -/
def TSZEl (a : A) : Prop := RelMap tsZ ![a]

/-- Being an available triple. -/
def TSTrip (a b c : A) : Prop := RelMap tsTrip ![a, b, c]

end Shorthands

/-! ### Matchings -/

section Matching

variable {A : Type}

/-- A **matching**: a set of triples, taken from `T` and lying in the three
classes, covering every marked element exactly once. -/
def IsMatchingOn (X Y Z : A → Prop) (T : A → A → A → Prop) (M : A → A → A → Prop) : Prop :=
  (∀ x y z, M x y z → T x y z ∧ X x ∧ Y y ∧ Z z) ∧
    (∀ x, X x → ∃ y z, M x y z) ∧ (∀ y, Y y → ∃ x z, M x y z) ∧
    (∀ z, Z z → ∃ x y, M x y z) ∧
    (∀ x y z y' z', M x y z → M x y' z' → y = y' ∧ z = z') ∧
    (∀ x y z x' z', M x y z → M x' y z' → x = x' ∧ z = z') ∧
    ∀ x y z x' y', M x y z → M x' y' z → x = x' ∧ y = y'

end Matching

/-! ### The problem -/

section Problem

variable (A : Type) [Language.tripleSys.Structure A]

/-- A triple system is a yes-instance when some subset of its triples covers
each marked element exactly once. -/
def HasThreeDimMatching : Prop :=
  Finite A ∧ ∃ M : A → A → A → Prop,
    IsMatchingOn (TSXEl (A := A)) TSYEl TSZEl TSTrip M

end Problem

section Iso

variable {A B : Type} [Language.tripleSys.Structure A] [Language.tripleSys.Structure B]

private theorem hasThreeDimMatching_of_iso (e : A ≃[Language.tripleSys] B)
    (h : HasThreeDimMatching A) : HasThreeDimMatching B := by
  obtain ⟨hfin, M, hsub, hx, hy, hz, hux, huy, huz⟩ := h
  have hX : ∀ a : A, TSXEl a ↔ TSXEl (e a) := fun a => relMap_equiv₁ e tsX a
  have hY : ∀ a : A, TSYEl a ↔ TSYEl (e a) := fun a => relMap_equiv₁ e tsY a
  have hZ : ∀ a : A, TSZEl a ↔ TSZEl (e a) := fun a => relMap_equiv₁ e tsZ a
  have hT : ∀ a b c : A, TSTrip a b c ↔ TSTrip (e a) (e b) (e c) := fun a b c =>
    relMap_equiv₃ e tsTrip a b c
  refine ⟨e.toEquiv.finite_iff.mp hfin,
    fun x y z => M (e.symm x) (e.symm y) (e.symm z), fun x y z hm => ?_, fun x hx' => ?_,
    fun y hy' => ?_, fun z hz' => ?_, fun x y z y' z' h₁ h₂ => ?_,
    fun x y z x' z' h₁ h₂ => ?_, fun x y z x' y' h₁ h₂ => ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hsub _ _ _ hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using (hT _ _ _).mp h₁
    · simpa using (hX _).mp h₂
    · simpa using (hY _).mp h₃
    · simpa using (hZ _).mp h₄
  · obtain ⟨y, z, hyz⟩ := hx (e.symm x) ((hX _).mpr (by simpa using hx'))
    exact ⟨e y, e z, by simpa using hyz⟩
  · obtain ⟨x, z, hxz⟩ := hy (e.symm y) ((hY _).mpr (by simpa using hy'))
    exact ⟨e x, e z, by simpa using hxz⟩
  · obtain ⟨x, y, hxy⟩ := hz (e.symm z) ((hZ _).mpr (by simpa using hz'))
    exact ⟨e x, e y, by simpa using hxy⟩
  · obtain ⟨h₃, h₄⟩ := hux _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩
  · obtain ⟨h₃, h₄⟩ := huy _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩
  · obtain ⟨h₃, h₄⟩ := huz _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩

/-- Having a 3-dimensional matching is isomorphism-invariant. -/
theorem hasThreeDimMatching_iso (e : A ≃[Language.tripleSys] B) :
    HasThreeDimMatching A ↔ HasThreeDimMatching B :=
  ⟨hasThreeDimMatching_of_iso e, hasThreeDimMatching_of_iso e.symm⟩

end Iso

/-- 3-DIMENSIONAL MATCHING, as a problem on triple systems: do some of the
triples cover every marked element exactly once? -/
def ThreeDimMatching : DecisionProblem Language.tripleSys where
  Holds := fun A inst => @HasThreeDimMatching A inst
  iso_invariant := fun e => hasThreeDimMatching_iso e

end DescriptiveComplexity
