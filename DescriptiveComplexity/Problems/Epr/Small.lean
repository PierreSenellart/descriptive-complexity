/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Epr.Defs

/-!
# The small-model property of `∃*∀*` sentences

What makes EPR a *bounded* problem: a satisfiable `∃*∀*` sentence has a model
whose universe is the instance itself. The witnesses of the existential
variables are the only elements a model needs – everything else the sentence
says is universally quantified, and a universal statement survives passing to a
subuniverse containing those witnesses.

The proof counts nothing. Map the instance onto the model by `x ↦ ε x` at an
existential variable and by a fixed element elsewhere
(`DescriptiveComplexity.Epr.collapse`); read the interpretation back through
that map, and let every variable stand for itself. What makes the reading
legitimate is **locality** together with well-formedness: the value of a symbol
is decided by the argument positions its signature declares, an atom names
exactly one variable at each of them, and those variables' values are the ones
the collapse carries.

This is the form the membership proof uses: with the universe fixed to the
instance, an interpretation is a relation on the instance and an assignment of
the universal variables is a *function* on it – one point of an exponential
expansion.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Epr

section Small

variable {A : Type} [Language.epr.Structure A]

/-- **A model on the instance itself**: an interpretation of the symbols by
relations on the instance, and a witness for the existential variables among
its elements. -/
def SelfModel (A : Type) [Language.epr.Structure A] : Prop :=
  ∃ (I : A → (A → A) → Prop) (ε : A → A),
    Local I ∧ ∀ u : A → A, MatrixTrue I (eprVal ε u)

variable {M : Type}

open Classical in
/-- **The instance, mapped into a model**: the witness of an existential
variable, and a fixed element elsewhere. Its image is the subuniverse the
sentence can speak of. -/
noncomputable def collapse (ε : A → M) (m₀ : M) : A → M :=
  fun x => if EVarG x then ε x else m₀

theorem collapse_eVar {ε : A → M} {m₀ : M} {x : A} (h : EVarG x) :
    collapse ε m₀ x = ε x := by
  classical
  rw [collapse, if_pos h]

/-- **The collapse commutes with the two environments**: the value a variable
takes when it stands for itself, mapped into the model, is the value it takes
in the model. -/
theorem collapse_val (ε : A → M) (m₀ : M) (u : A → A) (x : A) :
    collapse ε m₀ (eprVal (fun y => y) u x) =
      eprVal ε (fun y => collapse ε m₀ (u y)) x := by
  classical
  rw [eprVal, eprVal]
  by_cases hx : EVarG x
  · rw [if_pos hx, if_pos hx, collapse_eVar hx]
  · rw [if_neg hx, if_neg hx]

open Classical in
/-- **The arguments of a literal, as an assignment of its positions**: the
value of the variable the encoding names there, when every variable stands for
itself. Well-formedness makes the choice unambiguous. -/
noncomputable def argAssign (u : A → A) (l : A) : A → A :=
  fun p => if h : ∃ x, ArgG l p x then eprVal (fun y : A => y) u h.choose else u p

theorem argAssign_eq (hwf : IsWF A) (u : A → A) {l p x : A} (h : ArgG l p x) :
    argAssign u l p = eprVal (fun y : A => y) u x := by
  classical
  have hex : ∃ x, ArgG l p x := ⟨x, h⟩
  rw [argAssign, dif_pos hex, hwf.1 l p hex.choose x hex.choose_spec h]

/-- **A model becomes one on the instance**: read every symbol through the
collapse, and take each variable to stand for itself. -/
theorem selfModel_of_eprSatOn (hwf : IsWF A) (h : EprSatOn A) : SelfModel A := by
  classical
  obtain ⟨M, -, hne, I, ε, hlocal, hsat⟩ := h
  obtain ⟨m₀⟩ := hne
  refine ⟨fun s w => I s (fun p => collapse ε m₀ (w p)), fun y => y, ?_, ?_⟩
  · -- locality survives the reading
    intro s w w' hw
    exact hlocal s _ _ fun p hp => congrArg (collapse ε m₀) (hw p hp)
  · -- and so does the matrix, at every assignment
    intro u c hc
    obtain ⟨l, hl, htrue⟩ := hsat (fun y => collapse ε m₀ (u y)) c hc
    refine ⟨l, hl, ?_⟩
    -- the assignment of the argument positions, read on the instance
    have hkey : ∀ (s : A), (PosG l s ∨ NegG l s) → ∀ W : A → M,
        (∀ p x, ArgG l p x → W p = eprVal ε (fun y => collapse ε m₀ (u y)) x) →
        ((∀ p x, ArgG l p x → argAssign u l p = eprVal (fun y : A => y) u x) ∧
          (I s (fun p => collapse ε m₀ (argAssign u l p)) ↔ I s W)) := by
      intro s hs W hW
      refine ⟨fun p x hp => argAssign_eq hwf u hp, hlocal s _ _ fun p hp => ?_⟩
      obtain ⟨x, hx⟩ := hwf.2 l s p hs hp
      rw [argAssign_eq hwf u hx, collapse_val, hW p x hx]
    rcases htrue with ⟨s, hs, W, hW, hI⟩ | ⟨s, hs, W, hW, hI⟩
    · obtain ⟨harg, hiff⟩ := hkey s (Or.inl hs) W hW
      exact Or.inl ⟨s, hs, argAssign u l, harg, hiff.mpr hI⟩
    · obtain ⟨harg, hiff⟩ := hkey s (Or.inr hs) W hW
      exact Or.inr ⟨s, hs, argAssign u l, harg, fun hc => hI (hiff.mp hc)⟩

/-- **And a model on the instance is a model**: the instance is a finite
nonempty universe like any other. -/
theorem eprSatOn_of_selfModel [Finite A] [Nonempty A] (h : SelfModel A) : EprSatOn A := by
  obtain ⟨I, ε, hlocal, hsat⟩ := h
  exact ⟨A, inferInstance, inferInstance, I, ε, hlocal, hsat⟩

/-- **The small-model property**: a well-formed instance is satisfiable exactly
when it is satisfiable on its own universe. -/
theorem eprSatOn_iff_selfModel [Finite A] [Nonempty A] (hwf : IsWF A) :
    EprSatOn A ↔ SelfModel A :=
  ⟨selfModel_of_eprSatOn hwf, eprSatOn_of_selfModel⟩

end Small

end Epr

end DescriptiveComplexity
