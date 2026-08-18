/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInterp
import DescriptiveComplexity.Relativize

/-!
# A base that is never a singleton

Every track of the EXPSPACE machine is an *element* of the base universe, so the
whole construction needs two of them (`DescriptiveComplexity.Draw.Env.hzo`,
`DescriptiveComplexity.Draw.Table.zero_ne_one`) – and a reduction has to be
correct at one-element structures too. The fix is to run the machinery not at the
instance but at a **doubled** universe, which is never a singleton, and which is
an ordinary first-order interpretation of the instance so that nothing is lost:

* the universe is `Bool × (Fin 1 → A)`, i.e., two copies of `A`;
* the copy tagged `false` carries the instance's own relations, and is marked by
  the `old` symbol of `DescriptiveComplexity.newLang`;
* the copy tagged `true` is **junk**: no relation of the vocabulary touches it.

So the doubled universe is the extended universe of value invention
(`DescriptiveComplexity.SecondOrderNew`) with `|A|` invented values, and
`DescriptiveComplexity.relativizeTo` is what reads a formula about the instance
inside it. What the reduction then has to do – and what
`DescriptiveComplexity.Problems.Wide.RelExpansion` does – is relativize the
*expansion* the same way, so that its points are still the instance's.

The interpretation is plain (not relativized) and one-dimensional, so composing
it under the wide interpretation multiplies the dimension by one and the tags by
`Bool ^ dd`: the composite is again a tagged-tuple interpretation of the
instance, with the same dimension.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The interpretation -/

section Dbl

variable (L : Language.{0, 0}) [L.IsRelational]

/-- **A relation of the instance's vocabulary, inside the extended one**: named,
because a raw `Sum.inl` is not recognized at the transparency `rw` matches at. -/
abbrev newSym {L : Language.{0, 0}} {n : ℕ} (r : L.Relations n) :
    (newLang L).Relations n := Sum.inl r

/-- **The mark of the original elements**, named for the same reason. -/
abbrev oldNewSym : (newLang L).Relations 1 := Sum.inr Language.oldSym

open Classical in
/-- **The doubled universe, as an interpretation**: the `false` copy carries the
instance and is marked `old`, the `true` copy is junk. -/
noncomputable def dblInterp : FOInterpretation (L.sum Language.order) (newLang L) Bool 1 where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl r => fun t =>
      sideF _ (∀ i, t i = false) ⊓
        Relations.formula (baseSym r) fun j => Term.var ((j, 0) : Fin _ × Fin 1)
    | _, Sum.inr .old => fun t => sideF _ (t 0 = false)

variable {L}
variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The point of the doubled universe carried by a tag and an element. -/
abbrev dblPt (b : Bool) (a : A) : (dblInterp L).Map A := (b, fun _ => a)

omit [L.IsRelational] [L.Structure A] [LinearOrder A] in
@[simp] theorem dblPt_fst (b : Bool) (a : A) : (dblPt (L := L) b a).1 = b := rfl

omit [L.IsRelational] [L.Structure A] [LinearOrder A] in
@[simp] theorem dblPt_snd (b : Bool) (a : A) (j : Fin 1) :
    (dblPt (L := L) b a).2 j = a := rfl

omit [L.IsRelational] [L.Structure A] [LinearOrder A] in
/-- A point of the doubled universe is its tag and its single coordinate. -/
theorem dblPt_eta (p : (dblInterp L).Map A) : p = dblPt p.1 (p.2 0) :=
  Prod.ext rfl (funext fun j => by rw [Subsingleton.elim j 0])

/-- **A relation of the instance's vocabulary** holds in the doubled universe
exactly on the marked copy, of the elements it carries. -/
theorem relMap_dbl_inl {n : ℕ} (r : L.Relations n) (xs : Fin n → (dblInterp L).Map A) :
    RelMap (M := (dblInterp L).Map A) (newSym r) xs ↔
      ((∀ i, (xs i).1 = false) ∧ RelMap r fun i => (xs i).2 0) := by
  rw [FOInterpretation.relMap_map]
  simp only [dblInterp, newSym, Formula.realize_inf, realize_sideF]
  refine and_congr Iff.rfl ?_
  simp only [Formula.realize_rel, Term.realize_var]
  exact relMap_sumInl r _

/-- **The mark** holds exactly on the copy that carries the instance. -/
theorem relMap_dbl_old (xs : Fin 1 → (dblInterp L).Map A) :
    RelMap (M := (dblInterp L).Map A) (oldNewSym L) xs ↔ (xs 0).1 = false := by
  rw [FOInterpretation.relMap_map]
  exact realize_sideF

omit [L.IsRelational] [L.Structure A] [LinearOrder A] in
/-- **The doubled universe is never a singleton**: that is the whole point. -/
theorem dblPt_ne [Nonempty A] :
    dblPt (L := L) false (Classical.arbitrary A) ≠ dblPt true (Classical.arbitrary A) :=
  fun h => Bool.false_ne_true (congrArg Prod.fst h)

end Dbl

/-! ### An environment to name constants in

The rule-definability discharge (`DescriptiveComplexity.Draw.Data.uRulesDefinable_progOf`)
asks for one `DescriptiveComplexity.Draw.Env`, and only to name the gate
dispatch's default tag – a *nonemptiness* of a type the instance does not
mention, so any environment will do. The two-element one below is the cheapest:
the structure in which nothing holds. -/

section BoolEnv

variable (L : Language.{0, 0}) [L.IsRelational]

/-- **The two-element environment** over a relational vocabulary: the structure
in which nothing holds, with the two Booleans as its designated elements. -/
noncomputable def boolEnv : Env L where
  α := Bool
  str := ⟨fun f => isEmptyElim f, fun _ _ => False⟩
  zero := false
  one := true
  hbot := fun b => by cases b <;> simp
  htop := fun b => by cases b <;> simp
  hzo := by simp

end BoolEnv

end Draw

end DescriptiveComplexity
