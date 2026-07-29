/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Fintype.Pi

/-!
# Deciding first-order satisfaction on a finite structure

The first step of the bridge to Mathlib's computability layer: on a *finite*
structure whose relations are decidable and whose equality is decidable,
`FirstOrder.Language.BoundedFormula.Realize` is decidable, by recursion on the
formula – quantifiers going through `Fintype.decidableForallFintype`.

Mathlib has no such instance (`Realize` is a `Prop`-valued recursion, and
Mathlib's model theory never needs to run it), so it is supplied here. It is
the first formal justification of the claim, elsewhere by inspection, that
first-order interpretations are *effective*: everything a reduction of this
library computes is an evaluation of a fixed formula in a finite structure.

The instance is deliberately independent of the rest of the bridge: it
mentions no encoding of structures, and it is useful on its own wherever a
first-order condition has to be checked by `decide`.
-/

namespace FirstOrder

namespace Language

open Structure

namespace BoundedFormula

variable {L : Language} {α M : Type*} [L.Structure M]

/-- **Satisfaction is decidable on a finite structure** whose relations and
whose equality are decidable: a recursion on the formula, the quantifier case
being a decidable quantification over a `Fintype`.

The realization of a *term* needs no hypothesis: it is an ordinary function
into the universe, and only the equality test it feeds needs
`DecidableEq M`. -/
instance decidableRealize [DecidableEq M] [Fintype M]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (RelMap R x)] :
    ∀ {l : ℕ} (φ : L.BoundedFormula α l) (v : α → M) (xs : Fin l → M),
      Decidable (φ.Realize v xs)
  | _, .falsum, _, _ => inferInstanceAs (Decidable False)
  | _, .equal _ _, _, _ => inferInstanceAs (Decidable (_ = _))
  | _, .rel _ _, _, _ => inferInstanceAs (Decidable (RelMap _ _))
  | _, .imp φ₁ φ₂, v, xs =>
      letI := decidableRealize φ₁ v xs
      letI := decidableRealize φ₂ v xs
      inferInstanceAs (Decidable (_ → _))
  | _, .all φ, v, xs =>
      letI := fun x : M => decidableRealize φ v (Fin.snoc xs x)
      inferInstanceAs (Decidable (∀ _x : M, _))

end BoundedFormula

namespace Formula

variable {L : Language} {α M : Type*} [L.Structure M]

/-- Satisfaction of a formula (no bound variables left) is decidable on a
finite structure with decidable relations. -/
instance decidableRealize [DecidableEq M] [Fintype M]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (RelMap R x)]
    (φ : L.Formula α) (v : α → M) : Decidable (φ.Realize v) :=
  inferInstanceAs (Decidable (BoundedFormula.Realize _ _ _))

end Formula

namespace Sentence

variable {L : Language} {M : Type*} [L.Structure M]

/-- Satisfaction of a sentence is decidable on a finite structure with
decidable relations. -/
instance decidableRealize [DecidableEq M] [Fintype M]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (RelMap R x)]
    (φ : L.Sentence) : Decidable (φ.Realize M) :=
  inferInstanceAs (Decidable (Formula.Realize _ _))

end Sentence

end Language

end FirstOrder
