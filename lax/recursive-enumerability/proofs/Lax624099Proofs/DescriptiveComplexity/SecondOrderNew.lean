/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.SecondOrderLift
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

namespace Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax624099Proofs.Foreign.FirstOrder.Language
end Lax624099Proofs.Foreign.FirstOrder.Language

/-!
# Existential second-order logic with value invention

The logic `∃SO[new]` defining the class RE of recursively enumerable problems:
existential second-order logic whose relation variables range over a universe
*extended by finitely many invented values*, in the style of the
object-creating query languages of ([Abiteboul–Hull–Vianu 1995]
[abiteboul1995foundations], ch. 18).

Bounding the certificate by the instance is what keeps a second-order class
inside NP: a `Σ₁` sentence guesses relations over `A` itself, so the search
space is exponential in `|A|`. Value invention
removes exactly that bound and nothing else: the certificate is a finite
extension `A ⊕ Fin m` of the universe – with `m` *unbounded* – together with
relations over it, checked by a fixed first-order kernel. The witness is still
a finite object and the kernel is still decidable on a finite structure, so
the yes-instances are those found by an unbounded search over finite
witnesses: this is a logical definition of *recursive enumerability*, with no
machine model. (The converse inclusion, RE ⊆ `∃SO[new]`, is the
Trakhtenbrot-style encoding of an accepting run into invented values; it lives
with the machine bridge, not here.)

## The extended structure

An instance `A` and a number `m` of invented values determine an extended
structure over the vocabulary `Lax624099Proofs.DescriptiveComplexity.newLang L`, the base
vocabulary `L` together with one unary predicate `old`:

* its universe is `A ⊕ Fin m`;
* the symbols of `L` hold exactly where they hold in `A`, on original
  elements only – invented values are related to nothing
  (`Lax624099Proofs.DescriptiveComplexity.extBase`);
* `old` marks the original elements (`Lax624099Proofs.DescriptiveComplexity.IsOld`).

The vocabulary is relational, as every vocabulary of a
`Lax624099Proofs.DescriptiveComplexity.DecisionProblem` is, so invented values carry no
structure at all until the certificate's relations put some on them.

## Main definitions and results

* `Lax624099Proofs.DescriptiveComplexity.SigmaSONewDefinable`: definability by an `∃SO[new]`
  sentence – one existential second-order block over the extended universe and
  a first-order kernel, reusing the alternation machinery of
  `Lax624099Proofs.DescriptiveComplexity.SecondOrder` at a one-block list;
* `Lax624099Proofs.DescriptiveComplexity.extEquiv`: extended structures are functorial in the
  base isomorphism, so `∃SO[new]` expresses isomorphism-invariant properties;
* `Lax624099Proofs.DescriptiveComplexity.sigmaSONewDefinable_congr`: definability depends only
  on the finite instances of a problem;
* `Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable.toNew`: `Σ₁ ⊆ ∃SO[new]`, by
  inventing nothing – the kernel is guarded by
  `Lax624099Proofs.DescriptiveComplexity.noNewSentence`, “every element is original”, which
  pins the number of invented values to zero. As a statement about classes this
  is `Lax624099Proofs.DescriptiveComplexity.NP_subset_RE`.

No alternation hierarchy is built on top of `∃SO[new]`, deliberately:
alternating second-order blocks over a *finite* extended universe are still
checked by an unbounded search over finite witnesses, so the levels would
collapse into RE rather than stack. (That collapse is a semantic remark, not a
theorem here: proving it inside the logic needs the same encoding as the
inclusion RE ⊆ `∃SO[new]`.)
-/

namespace FirstOrder

namespace Language

/-- The symbol marking the original elements. -/
abbrev _root_.Lax624099Proofs.Foreign.FirstOrder.Language.oldSym : Lax624099.ValueInvention.oldMark.Relations 1 := .old

export Lax624099Proofs.Foreign.FirstOrder.Language (oldSym)

end Language

end FirstOrder

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The extended universe -/

section Extended

variable {L : Language.{0, 0}} {A A' : Type} {m m' : ℕ}

@[simp]
theorem isOld_inl (a : A) : Lax624099.ValueInvention.IsOld (Sum.inl a : A ⊕ Fin m) := trivial

@[simp]
theorem not_isOld_inr (i : Fin m) : ¬Lax624099.ValueInvention.IsOld (Sum.inr i : A ⊕ Fin m) := id

theorem isOld_iff {x : A ⊕ Fin m} : Lax624099.ValueInvention.IsOld x ↔ ∃ a : A, x = Sum.inl a := by
  cases x <;> simp

theorem relMap_ext_iff [L.IsRelational] [L.Structure A] {k : ℕ} (r : L.Relations k)
    (x : Fin k → A ⊕ Fin m) :
    RelMap (L := Lax624099.ValueInvention.newLang L) (Sum.inl r) x ↔ ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap r y :=
  Iff.rfl

/-- On original elements, the extended structure is the original one. -/
@[simp]
theorem relMap_ext_inl [L.IsRelational] [L.Structure A] {k : ℕ} (r : L.Relations k)
    (y : Fin k → A) :
    RelMap (L := Lax624099.ValueInvention.newLang L) (M := A ⊕ Fin m) (Sum.inl r) (fun i => Sum.inl (y i)) ↔
      RelMap r y := by
  rw [relMap_ext_iff]
  refine ⟨fun h => ?_, fun h => ⟨y, fun _ => rfl, h⟩⟩
  obtain ⟨y', hy', h⟩ := h
  have hyy : y = y' := funext fun i => Sum.inl_injective (hy' i)
  exact hyy ▸ h

@[simp]
theorem relMap_ext_old [L.IsRelational] [L.Structure A] (x : Fin 1 → A ⊕ Fin m) :
    RelMap (L := Lax624099.ValueInvention.newLang L) (Sum.inr Lax624099Proofs.Foreign.FirstOrder.Language.oldSym) x ↔ Lax624099.ValueInvention.IsOld (x 0) :=
  Iff.rfl

/-! ### Functoriality in the base structure -/

end Extended

/-! ### Definability

`SORealize` is reused at the one-block list `[B]`, so that an `∃SO[new]`
sentence is literally an `∃SO` sentence – over the extended vocabulary, read
in the extended structure. -/

section Definability

variable {L : Language.{0, 0}}

/-- Unfolding of alternating satisfaction at a single existential block. -/
theorem sorealize_singleton (A : Type) [inst : L.Structure A] (B : Lax904597.SecondOrder.SOBlock)
    (φ : (Lax904597.SecondOrder.soLang L [B]).Sentence) :
    Lax904597.SecondOrder.SORealize L A [B] φ true ↔
      ∃ ρ : B.Assignment A, @Sentence.Realize (L.sum B.lang) A
        (@sumStructure L B.lang A inst (B.structure ρ)) φ :=
  Iff.rfl

/-- `∃SO[new]`-definability only depends on the finite instances of a
problem. -/
theorem sigmaSONewDefinable_congr [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax624099.ValueInvention.SigmaSONewDefinable P ↔ Lax624099.ValueInvention.SigmaSONewDefinable Q := by
  constructor <;> rintro ⟨B, φ, hφ⟩ <;> refine ⟨B, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

end Definability

/-! ### Inventing nothing

The `Σ₁` sentences are the `∃SO[new]` sentences that invent nothing: the
kernel is guarded by `Lax624099Proofs.DescriptiveComplexity.noNewSentence`, which forces the
extended universe to be the original one. -/

section NoNew

variable (L : Language.{0, 0})

/-- The atom `old x`, over the extended vocabulary. -/
private def oldF {α : Type} (x : α) : (Lax624099.ValueInvention.newLang L).Formula α :=
  Relations.formula₁ (Sum.inr Lax624099Proofs.Foreign.FirstOrder.Language.oldSym) (Term.var x)

/-- The sentence “nothing was invented”: every element of the universe is an
original element. -/
noncomputable def noNewSentence : (Lax624099.ValueInvention.newLang L).Sentence :=
  (oldF L (Sum.inr 0)).iAlls (Fin 1)

theorem realize_noNewSentence [L.IsRelational] (A : Type) [L.Structure A] (m : ℕ) :
    @Sentence.Realize (Lax624099.ValueInvention.newLang L) (A ⊕ Fin m) _ (noNewSentence L) ↔
      ∀ x : A ⊕ Fin m, Lax624099.ValueInvention.IsOld x := by
  simp only [noNewSentence, oldF, Sentence.Realize, Formula.realize_iAlls]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

/-- The mark of the original elements on the original universe itself: every
element is original. -/
@[instance_reducible]
def allOldMarkStructure (A : Type) : Lax624099.ValueInvention.oldMark.Structure A where
  RelMap | .old => fun _ => True

/-- The instance itself, over the extended vocabulary: nothing is invented, so
every element is marked as original. -/
@[instance_reducible]
def allOldStructure (A : Type) [L.Structure A] : (Lax624099.ValueInvention.newLang L).Structure A :=
  @sumStructure L Lax624099.ValueInvention.oldMark A _ (allOldMarkStructure A)

/-- With no invented values, the extended structure is the instance itself. -/
def extEquivNoNew [L.IsRelational] (A : Type) [L.Structure A] (m : ℕ)
    [IsEmpty (Fin m)] :
    @Language.Equiv (Lax624099.ValueInvention.newLang L) A (A ⊕ Fin m) (allOldStructure L A) (Lax624099.ValueInvention.extStructure L A m) :=
  letI := allOldStructure L A
  { toEquiv := (Equiv.sumEmpty A (Fin m)).symm
    map_fun' := fun {_n} f _ => isEmptyElim f
    map_rel' := fun {_k} r x => by
      cases r with
      | inl s => exact relMap_ext_inl s x
      | inr s =>
        cases s with
        | old => exact iff_of_true (isOld_inl (m := m) (x 0)) trivial }

end NoNew

/-! ### `Σ₁ ⊆ ∃SO[new]` -/

variable {L : Language.{0, 0}}

/-- **The guarded sentence, read over an extended universe**: it holds exactly
when nothing was invented and the original sentence holds over the instance
itself. This is the whole content of inventing nothing, and it is what both
`Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable.toNew` and its bounded twin read. -/
theorem sorealize_guardNoNew_iff [L.IsRelational] {B : Lax904597.SecondOrder.SOBlock}
    (φ : (Lax904597.SecondOrder.soLang L [B]).Sentence) (A : Type) [instA : L.Structure A] (m : ℕ) :
    Lax904597.SecondOrder.SORealize (Lax624099.ValueInvention.newLang L) (A ⊕ Fin m) [B]
      ((soLangEmbed [B] (Lax624099.ValueInvention.newLang L)).onSentence (noNewSentence L) ⊓
        (soLangLift [B] L (Lax624099.ValueInvention.newLang L) LHom.sumInl).onSentence φ) true ↔
      (IsEmpty (Fin m) ∧ Lax904597.SecondOrder.SORealize L A [B] φ true) := by
  let instAll := allOldStructure L A
  rw [sorealize_inf_embed [B] (Lax624099.ValueInvention.newLang L) (A ⊕ Fin m) _ (noNewSentence L) _ true,
    realize_noNewSentence L A m]
  constructor
  · rintro ⟨hno, hrest⟩
    have : IsEmpty (Fin m) := ⟨fun i => not_isOld_inr i (hno (Sum.inr i))⟩
    refine ⟨inferInstance, ?_⟩
    have h1 := (@sorealize_iso (Lax624099.ValueInvention.newLang L) A (A ⊕ Fin m) instAll _
      (extEquivNoNew L A m) [B] _ true).mpr hrest
    exact (sorealize_soLangLift [B] L (Lax624099.ValueInvention.newLang L) LHom.sumInl A instA instAll
      (by let := allOldMarkStructure A; infer_instance) φ true).mp h1
  · rintro ⟨hempty, hφA⟩
    have := hempty
    refine ⟨fun x => ?_, ?_⟩
    · cases x with
      | inl a => exact isOld_inl a
      | inr i => exact (hempty.false i).elim
    · have h1 := (sorealize_soLangLift [B] L (Lax624099.ValueInvention.newLang L) LHom.sumInl A instA instAll
        (by let := allOldMarkStructure A; infer_instance) φ true).mpr hφA
      exact (@sorealize_iso (Lax624099.ValueInvention.newLang L) A (A ⊕ Fin m) instAll _
        (extEquivNoNew L A m) [B] _ true).mp h1

/-- **Existential second-order definability implies `∃SO[new]`-definability**:
an `∃SO` sentence becomes an `∃SO[new]` sentence when guarded by “nothing was
invented”. Once RE is a complexity class, this is the inclusion `NP ⊆ RE`. -/
theorem SigmaSODefinable.toNew [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax904597.SecondOrder.SigmaSODefinable 1 P) : Lax624099.ValueInvention.SigmaSONewDefinable P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  obtain ⟨B, rfl⟩ : ∃ B, Bs = [B] := by
    match Bs, hk with
    | [B], _ => exact ⟨B, rfl⟩
  refine ⟨B, (soLangEmbed [B] (Lax624099.ValueInvention.newLang L)).onSentence (noNewSentence L) ⊓
    (soLangLift [B] L (Lax624099.ValueInvention.newLang L) LHom.sumInl).onSentence φ, ?_⟩
  intro A instA _ _
  constructor
  · intro hP
    exact ⟨0, (sorealize_guardNoNew_iff φ A 0).mpr ⟨inferInstance, (hφ A).mp hP⟩⟩
  · rintro ⟨m, hm⟩
    exact (hφ A).mpr ((sorealize_guardNoNew_iff φ A m).mp hm).2

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SigmaSODefinable

export Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable (toNew)

end Lax904597.SecondOrder.SigmaSODefinable

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

end Lax624099Proofs.DescriptiveComplexity


