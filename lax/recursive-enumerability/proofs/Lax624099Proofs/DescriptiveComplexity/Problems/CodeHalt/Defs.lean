/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.PartrecCode
import Lax624099Proofs.DescriptiveComplexity.Interpretation
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

/-!
# CODEHALT: does the partial recursive code drawn in the instance halt?

The instance is a **syntax tree**, drawn with one element per node: a node
carries one of the eight constructor marks of `Nat.Partrec.Code`, and its
children are named by two binary symbols. The yes-instances are those whose
root draws a code that halts on input `0`.

This is the catalog problem the *undecidability* of the whole development goes
through. Its point is that the passage from Mathlib's halting problem to an
instance is a plain tree encoding – `Lax624099Proofs.DescriptiveComplexity.codeStruct`, in
`Lax624099Proofs.DescriptiveComplexity.Computability.CodeHalt` – rather than the simulation of
a machine: the code *is* the instance, and only the computation has to be
guessed. That is what makes the map `c ↦ instance` primitive recursive, which
the machine route could not deliver: Mathlib's universal machine is not
finite-state, so a machine instance cannot carry the program it runs.

## The semantics

`Lax624099Proofs.DescriptiveComplexity.DecodesTo` relates a node of the instance to a
`Nat.Partrec.Code`, by recursion on the code: a node decodes to `zero` when it
carries the `zero` mark, to `pair cf cg` when it carries the `pair` mark and
its two children decode to `cf` and `cg`, and so on. A yes-instance is one
whose root decodes to a code halting on `0`.

Reading the semantics off an *existential* over codes, rather than as a fixed
point computed inside the instance, is what keeps this file small: the
encoding direction is then immediate, and the converse needs only that
decoding is unique (`Lax624099Proofs.DescriptiveComplexity.decodesTo_unique`), which holds as
soon as the marks are exclusive and the child relations are functional
(`Lax624099Proofs.DescriptiveComplexity.CodeWF`).
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax624099.CodeHalting.code.Structure A]

end Shorthands

/-! ### Decoding a node into a code -/

section Decode

variable {A : Type} [Lax624099.CodeHalting.code.Structure A]

/-- The eight constructors of `Nat.Partrec.Code`, as a tag. Naming them makes
the exclusivity of the marks one statement instead of twenty-eight, and the
uniqueness of decoding a uniform argument instead of sixty-four cases. -/
inductive CodeTag
  /-- The tag of `zero`. -/
  | zero
  /-- The tag of `succ`. -/
  | succ
  /-- The tag of `left`. -/
  | left
  /-- The tag of `right`. -/
  | right
  /-- The tag of `pair`. -/
  | pair
  /-- The tag of `comp`. -/
  | comp
  /-- The tag of `prec`. -/
  | prec
  /-- The tag of `rfind'`. -/
  | rfind
  deriving DecidableEq

/-- The mark a tag stands for. -/
def Mark : CodeTag → A → Prop
  | .zero => Lax624099.CodeHalting.CZero
  | .succ => Lax624099.CodeHalting.CSucc
  | .left => Lax624099.CodeHalting.CLeft
  | .right => Lax624099.CodeHalting.CRight
  | .pair => Lax624099.CodeHalting.CPair
  | .comp => Lax624099.CodeHalting.CComp
  | .prec => Lax624099.CodeHalting.CPrec
  | .rfind => Lax624099.CodeHalting.CRfind

/-- The tag of a code. -/
def tagOf : Nat.Partrec.Code → CodeTag
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair _ _ => .pair
  | .comp _ _ => .comp
  | .prec _ _ => .prec
  | .rfind' _ => .rfind

theorem decodesTo_mark : ∀ (c : Nat.Partrec.Code) (n : A), Lax624099.CodeHalting.DecodesTo n c → Mark (tagOf c) n
  | .zero, _, h => h
  | .succ, _, h => h
  | .left, _, h => h
  | .right, _, h => h
  | .pair _ _, _, h => h.1
  | .comp _ _, _, h => h.1
  | .prec _ _, _, h => h.1
  | .rfind' _, _, h => h.1

/-- **Well-formedness of a code instance**: at most one constructor mark per
node, and functional child relations. This is what makes decoding unique; it
is *not* folded into the yes-instances, because the problem is stated by an
existential over codes and a junk instance simply decodes to nothing. -/
structure CodeWF (A : Type) [Lax624099.CodeHalting.code.Structure A] : Prop where
  /-- At most one constructor mark per node. -/
  exclusive : ∀ (a : A) (t t' : CodeTag), Mark t a → Mark t' a → t = t'
  /-- The first child is unique. -/
  arg1_fun : ∀ a b b' : A, Lax624099.CodeHalting.CArg1 a b → Lax624099.CodeHalting.CArg1 a b' → b = b'
  /-- The second child is unique. -/
  arg2_fun : ∀ a b b' : A, Lax624099.CodeHalting.CArg2 a b → Lax624099.CodeHalting.CArg2 a b' → b = b'

theorem tag_eq_of_decodesTo (h : CodeWF A) {c c' : Nat.Partrec.Code} {n : A}
    (h1 : Lax624099.CodeHalting.DecodesTo n c) (h2 : Lax624099.CodeHalting.DecodesTo n c') : tagOf c = tagOf c' :=
  h.exclusive n _ _ (decodesTo_mark c n h1) (decodesTo_mark c' n h2)

/-- **Decoding is unique** on a well-formed instance. -/
theorem decodesTo_unique (h : CodeWF A) :
    ∀ (c c' : Nat.Partrec.Code) (n : A), Lax624099.CodeHalting.DecodesTo n c → Lax624099.CodeHalting.DecodesTo n c' → c = c' := by
  intro c
  induction c with
  | zero =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case zero => rfl
    all_goals exact absurd ht (by simp [tagOf])
  | succ =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case succ => rfl
    all_goals exact absurd ht (by simp [tagOf])
  | left =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case left => rfl
    all_goals exact absurd ht (by simp [tagOf])
  | right =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case right => rfl
    all_goals exact absurd ht (by simp [tagOf])
  | pair cf cg ihf ihg =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case pair cf' cg' =>
      obtain ⟨-, a, b, ha, hb, hf, hg⟩ := h1
      obtain ⟨-, a', b', ha', hb', hf', hg'⟩ := h2
      rw [h.arg1_fun n a' a ha' ha] at hf'
      rw [h.arg2_fun n b' b hb' hb] at hg'
      rw [ihf cf' a hf hf', ihg cg' b hg hg']
    all_goals exact absurd ht (by simp [tagOf])
  | comp cf cg ihf ihg =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case comp cf' cg' =>
      obtain ⟨-, a, b, ha, hb, hf, hg⟩ := h1
      obtain ⟨-, a', b', ha', hb', hf', hg'⟩ := h2
      rw [h.arg1_fun n a' a ha' ha] at hf'
      rw [h.arg2_fun n b' b hb' hb] at hg'
      rw [ihf cf' a hf hf', ihg cg' b hg hg']
    all_goals exact absurd ht (by simp [tagOf])
  | prec cf cg ihf ihg =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case prec cf' cg' =>
      obtain ⟨-, a, b, ha, hb, hf, hg⟩ := h1
      obtain ⟨-, a', b', ha', hb', hf', hg'⟩ := h2
      rw [h.arg1_fun n a' a ha' ha] at hf'
      rw [h.arg2_fun n b' b hb' hb] at hg'
      rw [ihf cf' a hf hf', ihg cg' b hg hg']
    all_goals exact absurd ht (by simp [tagOf])
  | rfind' cf ihf =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case rfind' cf' =>
      obtain ⟨-, a, ha, hf⟩ := h1
      obtain ⟨-, a', ha', hf'⟩ := h2
      rw [h.arg1_fun n a' a ha' ha] at hf'
      rw [ihf cf' a hf hf']
    all_goals exact absurd ht (by simp [tagOf])

end Decode

/-! ### Isomorphism-invariance -/

section Iso

variable {A B : Type} [Lax624099.CodeHalting.code.Structure A] [Lax624099.CodeHalting.code.Structure B]

private theorem mark_equiv (e : A ≃[Lax624099.CodeHalting.code] B) (r : Lax624099.CodeHalting.code.Relations 1) (n : A) :
    (RelMap r ![n] : Prop) ↔ RelMap r ![(e n : B)] := relMap_equiv₁ e r n

private theorem arg_equiv_symm (e : A ≃[Lax624099.CodeHalting.code] B) (r : Lax624099.CodeHalting.code.Relations 2)
    (n : A) (b : B) : (RelMap r ![n, e.symm b] : Prop) ↔ RelMap r ![(e n : B), b] := by
  have h := relMap_equiv₂ e r n (e.symm b)
  rwa [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b] at h

/-- **Decoding transports along an isomorphism**: what a node draws is a
first-order property of the instance. -/
theorem decodesTo_equiv (e : A ≃[Lax624099.CodeHalting.code] B) :
    ∀ (c : Nat.Partrec.Code) (n : A), Lax624099.CodeHalting.DecodesTo n c ↔ Lax624099.CodeHalting.DecodesTo (e n) c := by
  intro c
  induction c with
  | zero => intro n; exact mark_equiv e Lax624099.CodeHalting.cZero n
  | succ => intro n; exact mark_equiv e Lax624099.CodeHalting.cSucc n
  | left => intro n; exact mark_equiv e Lax624099.CodeHalting.cLeft n
  | right => intro n; exact mark_equiv e Lax624099.CodeHalting.cRight n
  | pair cf cg ihf ihg =>
    intro n
    refine and_congr (mark_equiv e Lax624099.CodeHalting.cPair n) ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      exact ⟨e a, e b, (relMap_equiv₂ e Lax624099.CodeHalting.cArg1 n a).mp ha, (relMap_equiv₂ e Lax624099.CodeHalting.cArg2 n b).mp hb,
        (ihf a).mp hf, (ihg b).mp hg⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      refine ⟨e.symm a, e.symm b, (arg_equiv_symm e Lax624099.CodeHalting.cArg1 n a).mpr ha,
        (arg_equiv_symm e Lax624099.CodeHalting.cArg2 n b).mpr hb, ?_, ?_⟩
      · refine (ihf (e.symm a)).mpr ?_
        rwa [show (e (e.symm a) : B) = a from e.toEquiv.apply_symm_apply a]
      · refine (ihg (e.symm b)).mpr ?_
        rwa [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b]
  | comp cf cg ihf ihg =>
    intro n
    refine and_congr (mark_equiv e Lax624099.CodeHalting.cComp n) ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      exact ⟨e a, e b, (relMap_equiv₂ e Lax624099.CodeHalting.cArg1 n a).mp ha, (relMap_equiv₂ e Lax624099.CodeHalting.cArg2 n b).mp hb,
        (ihf a).mp hf, (ihg b).mp hg⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      refine ⟨e.symm a, e.symm b, (arg_equiv_symm e Lax624099.CodeHalting.cArg1 n a).mpr ha,
        (arg_equiv_symm e Lax624099.CodeHalting.cArg2 n b).mpr hb, ?_, ?_⟩
      · refine (ihf (e.symm a)).mpr ?_
        rwa [show (e (e.symm a) : B) = a from e.toEquiv.apply_symm_apply a]
      · refine (ihg (e.symm b)).mpr ?_
        rwa [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b]
  | prec cf cg ihf ihg =>
    intro n
    refine and_congr (mark_equiv e Lax624099.CodeHalting.cPrec n) ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      exact ⟨e a, e b, (relMap_equiv₂ e Lax624099.CodeHalting.cArg1 n a).mp ha, (relMap_equiv₂ e Lax624099.CodeHalting.cArg2 n b).mp hb,
        (ihf a).mp hf, (ihg b).mp hg⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      refine ⟨e.symm a, e.symm b, (arg_equiv_symm e Lax624099.CodeHalting.cArg1 n a).mpr ha,
        (arg_equiv_symm e Lax624099.CodeHalting.cArg2 n b).mpr hb, ?_, ?_⟩
      · refine (ihf (e.symm a)).mpr ?_
        rwa [show (e (e.symm a) : B) = a from e.toEquiv.apply_symm_apply a]
      · refine (ihg (e.symm b)).mpr ?_
        rwa [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b]
  | rfind' cf ihf =>
    intro n
    refine and_congr (mark_equiv e Lax624099.CodeHalting.cRfind n) ⟨?_, ?_⟩
    · rintro ⟨a, ha, hf⟩
      exact ⟨e a, (relMap_equiv₂ e Lax624099.CodeHalting.cArg1 n a).mp ha, (ihf a).mp hf⟩
    · rintro ⟨a, ha, hf⟩
      refine ⟨e.symm a, (arg_equiv_symm e Lax624099.CodeHalting.cArg1 n a).mpr ha, (ihf (e.symm a)).mpr ?_⟩
      rwa [show (e (e.symm a) : B) = a from e.toEquiv.apply_symm_apply a]

end Iso

/-! ### The problem -/

/-- **CODEHALT**: does the partial recursive code drawn by the root of the
instance halt on input `0`?

The yes-instances are stated by an existential over `Nat.Partrec.Code`: some
node is the root, it draws some code, and that code halts on `0`. Nothing is
promised of the instance, so a junk one simply draws nothing and is a
no-instance. -/
def CODEHALT : Lax904597.Problems.DecisionProblem Lax624099.CodeHalting.code where
  Holds A _ := ∃ (n : A) (c : Nat.Partrec.Code),
    Lax624099.CodeHalting.CRoot n ∧ Lax624099.CodeHalting.DecodesTo n c ∧ (Nat.Partrec.Code.eval c 0).Dom
  iso_invariant := fun {A B} _ _ e => by
    constructor
    · rintro ⟨n, c, hr, hd, hh⟩
      exact ⟨e n, c, (mark_equiv e Lax624099.CodeHalting.cRoot n).mp hr, (decodesTo_equiv e c n).mp hd, hh⟩
    · rintro ⟨m, c, hr, hd, hh⟩
      refine ⟨e.symm m, c, ?_, ?_, hh⟩
      · have hm := mark_equiv e Lax624099.CodeHalting.cRoot (e.symm m)
        rw [show (e (e.symm m) : B) = m from e.toEquiv.apply_symm_apply m] at hm
        exact hm.mpr hr
      · refine (decodesTo_equiv e c (e.symm m)).mpr ?_
        rwa [show (e (e.symm m) : B) = m from e.toEquiv.apply_symm_apply m]

@[simp]
theorem codehalt_holds_iff (A : Type) [Lax624099.CodeHalting.code.Structure A] :
    CODEHALT A ↔ ∃ (n : A) (c : Nat.Partrec.Code),
      Lax624099.CodeHalting.CRoot n ∧ Lax624099.CodeHalting.DecodesTo n c ∧ (Nat.Partrec.Code.eval c 0).Dom :=
  Iff.rfl

end Lax624099Proofs.DescriptiveComplexity


