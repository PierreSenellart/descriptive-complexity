/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Relativized
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Post-processing terms

The arithmetic a counting reduction may apply to the answer of its one oracle
call (`DescriptiveComplexity.Counting.Reduction`). Two layers, kept apart so
that every number written stays of polynomially many bits:

* `DescriptiveComplexity.PolyTerm`: numerals, **definable cardinalities** – the
  number of tagged tuples of the instance satisfying first-order formulas over
  the ordered expansion – sums and products. Its values are polynomial in the
  size of the instance.
* `DescriptiveComplexity.PostTerm`: the oracle's answer, a polynomial term, a
  power of two *whose exponent is a polynomial term*, sums, products,
  truncated differences, quotients and remainders.

So a post-processing term is a fixed arithmetic expression over the oracle's
answer and first-order definable counts: it can be evaluated in polynomial
time, and it does no counting of its own beyond tuples of the instance.

Both layers are **pulled back** along a relativized interpretation
(`DescriptiveComplexity.PolyTerm.pull`, `DescriptiveComplexity.PostTerm.pull`):
a definable cardinality of the interpreted structure is a definable
cardinality of the instance. A cardinality is stored as the universe of a
relativized interpretation into the empty vocabulary, so the pullback is the
composition of relativized interpretations and needs nothing new. With
substitution for the oracle's answer (`DescriptiveComplexity.PostTerm.subst`),
this is what makes one-call reductions compose.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Polynomial terms -/

/-- Terms denoting numbers polynomial in the size of the instance: numerals,
definable cardinalities, sums and products. -/
inductive PolyTerm (L : Language.{0, 0}) : Type 1
  /-- A numeral. -/
  | num (k : ℕ) : PolyTerm L
  /-- The number of tagged tuples satisfying their tag's domain formula, i.e.,
  the size of the universe of a relativized interpretation. -/
  | card {Tag : Type} [Finite Tag] {dim : ℕ}
      (J : RelFOInterpretation (L.sum Language.order) Language.empty Tag dim) : PolyTerm L
  /-- A sum. -/
  | add (p q : PolyTerm L) : PolyTerm L
  /-- A product. -/
  | mul (p q : PolyTerm L) : PolyTerm L

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The value of a polynomial term at an ordered structure. -/
noncomputable def eval (A : Type) [L.Structure A] [LinearOrder A] : PolyTerm L → ℕ
  | num k => k
  | card J => Nat.card (J.MapRel A)
  | add p q => p.eval A + q.eval A
  | mul p q => p.eval A * q.eval A

/-- The relativized interpretation into the empty vocabulary whose universe
is the set of tuples satisfying a formula. -/
def cardInterp {k : ℕ} (φ : (L.sum Language.order).Formula (Fin k)) :
    RelFOInterpretation (L.sum Language.order) Language.empty Unit k where
  relFormula := fun R => isEmptyElim R
  domFormula := fun _ => φ

/-- The number of `k`-tuples satisfying a first-order formula over the ordered
expansion. -/
def count {k : ℕ} (φ : (L.sum Language.order).Formula (Fin k)) : PolyTerm L :=
  card (cardInterp φ)

theorem eval_count (A : Type) [L.Structure A] [LinearOrder A] {k : ℕ}
    (φ : (L.sum Language.order).Formula (Fin k)) :
    (count φ).eval A = Nat.card {w : Fin k → A // φ.Realize w} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.2, x.2⟩
      invFun := fun w => ⟨((), w.1), w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The number of elements satisfying a first-order formula over the ordered
expansion, as a cardinality of a set of elements. -/
theorem eval_count_one (A : Type) [L.Structure A] [LinearOrder A]
    (φ : (L.sum Language.order).Formula (Fin 1)) :
    (count φ).eval A = Nat.card {a : A // φ.Realize fun _ => a} := by
  rw [eval_count]
  exact Nat.card_congr
    { toFun := fun w => ⟨w.1 0, by
        have h : (fun _ => w.1 0) = w.1 := funext fun j => congrArg w.1 (Subsingleton.elim _ _)
        rw [h]
        exact w.2⟩
      invFun := fun a => ⟨fun _ => a.1, a.2⟩
      left_inv := fun w => Subtype.ext (funext fun j => congrArg w.1 (Subsingleton.elim _ _))
      right_inv := fun _ => rfl }

/-- The number of elements of the instance. -/
def univ : PolyTerm L :=
  count (⊤ : (L.sum Language.order).Formula (Fin 1))

theorem eval_univ (A : Type) [L.Structure A] [LinearOrder A] :
    (univ : PolyTerm L).eval A = Nat.card A := by
  rw [univ, eval_count_one]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => Formula.realize_top.mpr trivial)

section Pull

variable [L₂.IsRelational] {T : Type} [LinearOrder T] [Finite T] {d : ℕ}

/-- The pullback of a polynomial term along a relativized interpretation: a
definable cardinality of the interpreted structure, ordered lexicographically,
is the size of the universe of a composite interpretation. -/
noncomputable def pull (I : RelFOInterpretation (L₁.sum Language.order) L₂ T d) :
    PolyTerm L₂ → PolyTerm L₁
  | num k => num k
  | card J => card (J.compRel I.ordExtendRel)
  | add p q => add (p.pull I) (q.pull I)
  | mul p q => mul (p.pull I) (q.pull I)

/-- A pulled-back polynomial term has, at the instance, the value of the
original term at the interpreted structure. -/
theorem eval_pull (I : RelFOInterpretation (L₁.sum Language.order) L₂ T d)
    (A : Type) [L₁.Structure A] [LinearOrder A] (p : PolyTerm L₂) :
    (p.pull I).eval A =
      (letI := I.mapRelLinearOrder A; p.eval (I.MapRel A)) := by
  let := I.mapRelLinearOrder A
  induction p with
  | num k => rfl
  | card J =>
    have e1 := I.ordExtendRelLEquiv A
    have e2 := J.mapRelLEquiv e1
    have e3 := J.compLEquivRel I.ordExtendRel (A := A)
    exact Nat.card_congr (e2.comp e3).toEquiv
  | add p q hp hq => exact congrArg₂ (· + ·) hp hq
  | mul p q hp hq => exact congrArg₂ (· * ·) hp hq

end Pull

end PolyTerm

/-! ### Post-processing terms -/

/-- The arithmetic applied to the answer of an oracle call: polynomial terms,
powers of two with a polynomial exponent, and the operations `+`, `*`,
truncated `-`, `/` and `%` of the natural numbers. -/
inductive PostTerm (L : Language.{0, 0}) : Type 1
  /-- The answer of the oracle. -/
  | oracle : PostTerm L
  /-- A polynomial term. -/
  | poly (p : PolyTerm L) : PostTerm L
  /-- Two to the power of a polynomial term. -/
  | pow2 (p : PolyTerm L) : PostTerm L
  /-- A sum. -/
  | add (s t : PostTerm L) : PostTerm L
  /-- A product. -/
  | mul (s t : PostTerm L) : PostTerm L
  /-- A truncated difference. -/
  | sub (s t : PostTerm L) : PostTerm L
  /-- A quotient. -/
  | div (s t : PostTerm L) : PostTerm L
  /-- A remainder. -/
  | mod (s t : PostTerm L) : PostTerm L

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The value of a post-processing term at an ordered structure, given the
answer `c` of the oracle. -/
noncomputable def eval (A : Type) [L.Structure A] [LinearOrder A] (c : ℕ) : PostTerm L → ℕ
  | oracle => c
  | poly p => p.eval A
  | pow2 p => 2 ^ p.eval A
  | add s t => s.eval A c + t.eval A c
  | mul s t => s.eval A c * t.eval A c
  | sub s t => s.eval A c - t.eval A c
  | div s t => s.eval A c / t.eval A c
  | mod s t => s.eval A c % t.eval A c

/-- Substitution of a term for the answer of the oracle. -/
def subst : PostTerm L → PostTerm L → PostTerm L
  | oracle, u => u
  | poly p, _ => poly p
  | pow2 p, _ => pow2 p
  | add s t, u => add (s.subst u) (t.subst u)
  | mul s t, u => mul (s.subst u) (t.subst u)
  | sub s t, u => sub (s.subst u) (t.subst u)
  | div s t, u => div (s.subst u) (t.subst u)
  | mod s t, u => mod (s.subst u) (t.subst u)

theorem eval_subst (A : Type) [L.Structure A] [LinearOrder A] (c : ℕ) (s u : PostTerm L) :
    (s.subst u).eval A c = s.eval A (u.eval A c) := by
  induction s with
  | oracle => rfl
  | poly p => rfl
  | pow2 p => rfl
  | add s t hs ht => exact congrArg₂ (· + ·) hs ht
  | mul s t hs ht => exact congrArg₂ (· * ·) hs ht
  | sub s t hs ht => exact congrArg₂ (· - ·) hs ht
  | div s t hs ht => exact congrArg₂ (· / ·) hs ht
  | mod s t hs ht => exact congrArg₂ (· % ·) hs ht

section Pull

variable [L₂.IsRelational] {T : Type} [LinearOrder T] [Finite T] {d : ℕ}

/-- The pullback of a post-processing term along a relativized interpretation,
its polynomial terms being pulled back. -/
noncomputable def pull (I : RelFOInterpretation (L₁.sum Language.order) L₂ T d) :
    PostTerm L₂ → PostTerm L₁
  | oracle => oracle
  | poly p => poly (p.pull I)
  | pow2 p => pow2 (p.pull I)
  | add s t => add (s.pull I) (t.pull I)
  | mul s t => mul (s.pull I) (t.pull I)
  | sub s t => sub (s.pull I) (t.pull I)
  | div s t => div (s.pull I) (t.pull I)
  | mod s t => mod (s.pull I) (t.pull I)

/-- A pulled-back post-processing term has, at the instance, the value of the
original term at the interpreted structure. -/
theorem eval_pull (I : RelFOInterpretation (L₁.sum Language.order) L₂ T d)
    (A : Type) [L₁.Structure A] [LinearOrder A] (c : ℕ) (s : PostTerm L₂) :
    (s.pull I).eval A c =
      (letI := I.mapRelLinearOrder A; s.eval (I.MapRel A) c) := by
  let := I.mapRelLinearOrder A
  induction s with
  | oracle => rfl
  | poly p => exact p.eval_pull I A
  | pow2 p => exact congrArg (2 ^ ·) (p.eval_pull I A)
  | add s t hs ht => exact congrArg₂ (· + ·) hs ht
  | mul s t hs ht => exact congrArg₂ (· * ·) hs ht
  | sub s t hs ht => exact congrArg₂ (· - ·) hs ht
  | div s t hs ht => exact congrArg₂ (· / ·) hs ht
  | mod s t hs ht => exact congrArg₂ (· % ·) hs ht

end Pull

end PostTerm

end DescriptiveComplexity
