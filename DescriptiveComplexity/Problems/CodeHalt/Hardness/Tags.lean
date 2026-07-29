/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Finite.Sum
import DescriptiveComplexity.Problems.CodeHalt.Hardness.Value
import DescriptiveComplexity.Problems.CodeHalt.Defs

/-!
# The elements of the CODEHALT instance an instance is drawn as

The tags of the reduction `P ≤ᶠᵒ[≤] CODEHALT`, and the positions of the one
*abstract* code it mentions.

## The abstract code is drawn one tag per node

The reduction composes a fixed code `cP` – the semi-decision procedure of the
source problem, which Mathlib's `Nat.Partrec.Code.exists_code` *supplies*
rather than has to be built – with the value the instance is written as. The
subtree of `cP` has no reason to be indexed by the input structure, so it is
drawn with one tag per node: `DescriptiveComplexity.SubPos cP`, the positions
of a code's syntax tree, defined by recursion on the code so that a position's
subterm (`DescriptiveComplexity.subAt`) and children
(`DescriptiveComplexity.sub1`, `DescriptiveComplexity.sub2`) are read off
definitionally. Tags cost nothing at any instance size, which is what makes
this compatible with hardness being cofinal in the reduction order.

## The rest of the tags

| tag | coordinates | draws |
| --- | --- | --- |
| `root` | – | `comp cP (pair numeral nest)` |
| `cp p` | – | the node `p` of `cP` |
| `pairN` | – | the `pair` of the numeral and the nest |
| `numN` | `(x, ⊥, …)` | the `comp succ …` chain of the numeral, from `x` on |
| `symN i` | – | the nest of the blocks of the symbols, from `i` on |
| `chainN i l` | `(x₀, …, x_l, ⊥, …)` | the level-`l` chain of the block of `i`, from `x_l` on |
| `oneN` | – | `succ`: the value `1` |
| `zeroN` | – | `zero`: the value `0`, and every empty tail |

Two of them are *shared*: `oneN` and `zeroN` are single elements, pointed at by
every chain that ends and by every bit of the table. A drawing is a relation on
the elements, so an element may have several parents – and sharing is what keeps
the bit of a tuple an *edge* of the drawing rather than a conditional mark, so
that every tag has one constructor (`DescriptiveComplexity.ProgTag.mark`) and
exclusivity of the marks is immediate.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Nat.Partrec (Code)

/-! ### The positions of a code's syntax tree -/

/-- The positions of the syntax tree of a code, by recursion on the code. -/
def SubPos : Code → Type
  | .zero => Unit
  | .succ => Unit
  | .left => Unit
  | .right => Unit
  | .pair cf cg => Unit ⊕ SubPos cf ⊕ SubPos cg
  | .comp cf cg => Unit ⊕ SubPos cf ⊕ SubPos cg
  | .prec cf cg => Unit ⊕ SubPos cf ⊕ SubPos cg
  | .rfind' cf => Unit ⊕ SubPos cf

instance instFiniteSubPos : ∀ c : Code, Finite (SubPos c)
  | .zero => inferInstanceAs (Finite Unit)
  | .succ => inferInstanceAs (Finite Unit)
  | .left => inferInstanceAs (Finite Unit)
  | .right => inferInstanceAs (Finite Unit)
  | .pair cf cg =>
      letI := instFiniteSubPos cf
      letI := instFiniteSubPos cg
      inferInstanceAs (Finite (Unit ⊕ SubPos cf ⊕ SubPos cg))
  | .comp cf cg =>
      letI := instFiniteSubPos cf
      letI := instFiniteSubPos cg
      inferInstanceAs (Finite (Unit ⊕ SubPos cf ⊕ SubPos cg))
  | .prec cf cg =>
      letI := instFiniteSubPos cf
      letI := instFiniteSubPos cg
      inferInstanceAs (Finite (Unit ⊕ SubPos cf ⊕ SubPos cg))
  | .rfind' cf =>
      letI := instFiniteSubPos cf
      inferInstanceAs (Finite (Unit ⊕ SubPos cf))

instance instDecidableEqSubPos : ∀ c : Code, DecidableEq (SubPos c)
  | .zero => inferInstanceAs (DecidableEq Unit)
  | .succ => inferInstanceAs (DecidableEq Unit)
  | .left => inferInstanceAs (DecidableEq Unit)
  | .right => inferInstanceAs (DecidableEq Unit)
  | .pair cf cg =>
      letI := instDecidableEqSubPos cf
      letI := instDecidableEqSubPos cg
      inferInstanceAs (DecidableEq (Unit ⊕ SubPos cf ⊕ SubPos cg))
  | .comp cf cg =>
      letI := instDecidableEqSubPos cf
      letI := instDecidableEqSubPos cg
      inferInstanceAs (DecidableEq (Unit ⊕ SubPos cf ⊕ SubPos cg))
  | .prec cf cg =>
      letI := instDecidableEqSubPos cf
      letI := instDecidableEqSubPos cg
      inferInstanceAs (DecidableEq (Unit ⊕ SubPos cf ⊕ SubPos cg))
  | .rfind' cf =>
      letI := instDecidableEqSubPos cf
      inferInstanceAs (DecidableEq (Unit ⊕ SubPos cf))

/-- The root position of a code's syntax tree. -/
def codeRootPos : ∀ c : Code, SubPos c
  | .zero | .succ | .left | .right => ()
  | .pair _ _ | .comp _ _ | .prec _ _ | .rfind' _ => Sum.inl ()

instance instNonemptySubPos (c : Code) : Nonempty (SubPos c) := ⟨codeRootPos c⟩

/-- The subterm sitting at a position. -/
def subAt : ∀ (c : Code), SubPos c → Code
  | .zero, _ => .zero
  | .succ, _ => .succ
  | .left, _ => .left
  | .right, _ => .right
  | .pair cf cg, Sum.inl _ => .pair cf cg
  | .pair cf _, Sum.inr (Sum.inl p) => subAt cf p
  | .pair _ cg, Sum.inr (Sum.inr p) => subAt cg p
  | .comp cf cg, Sum.inl _ => .comp cf cg
  | .comp cf _, Sum.inr (Sum.inl p) => subAt cf p
  | .comp _ cg, Sum.inr (Sum.inr p) => subAt cg p
  | .prec cf cg, Sum.inl _ => .prec cf cg
  | .prec cf _, Sum.inr (Sum.inl p) => subAt cf p
  | .prec _ cg, Sum.inr (Sum.inr p) => subAt cg p
  | .rfind' cf, Sum.inl _ => .rfind' cf
  | .rfind' cf, Sum.inr p => subAt cf p

/-- The position of the first child of a position, if it has one. -/
def sub1 : ∀ (c : Code), SubPos c → Option (SubPos c)
  | .zero, _ => none
  | .succ, _ => none
  | .left, _ => none
  | .right, _ => none
  | .pair cf _, Sum.inl _ => some (Sum.inr (Sum.inl (codeRootPos cf)))
  | .pair _ _, Sum.inr (Sum.inl p) => (sub1 _ p).map (fun q => Sum.inr (Sum.inl q))
  | .pair _ _, Sum.inr (Sum.inr p) => (sub1 _ p).map (fun q => Sum.inr (Sum.inr q))
  | .comp cf _, Sum.inl _ => some (Sum.inr (Sum.inl (codeRootPos cf)))
  | .comp _ _, Sum.inr (Sum.inl p) => (sub1 _ p).map (fun q => Sum.inr (Sum.inl q))
  | .comp _ _, Sum.inr (Sum.inr p) => (sub1 _ p).map (fun q => Sum.inr (Sum.inr q))
  | .prec cf _, Sum.inl _ => some (Sum.inr (Sum.inl (codeRootPos cf)))
  | .prec _ _, Sum.inr (Sum.inl p) => (sub1 _ p).map (fun q => Sum.inr (Sum.inl q))
  | .prec _ _, Sum.inr (Sum.inr p) => (sub1 _ p).map (fun q => Sum.inr (Sum.inr q))
  | .rfind' cf, Sum.inl _ => some (Sum.inr (codeRootPos cf))
  | .rfind' _, Sum.inr p => (sub1 _ p).map Sum.inr

/-- The position of the second child of a position, if it has one. -/
def sub2 : ∀ (c : Code), SubPos c → Option (SubPos c)
  | .zero, _ => none
  | .succ, _ => none
  | .left, _ => none
  | .right, _ => none
  | .pair _ cg, Sum.inl _ => some (Sum.inr (Sum.inr (codeRootPos cg)))
  | .pair _ _, Sum.inr (Sum.inl p) => (sub2 _ p).map (fun q => Sum.inr (Sum.inl q))
  | .pair _ _, Sum.inr (Sum.inr p) => (sub2 _ p).map (fun q => Sum.inr (Sum.inr q))
  | .comp _ cg, Sum.inl _ => some (Sum.inr (Sum.inr (codeRootPos cg)))
  | .comp _ _, Sum.inr (Sum.inl p) => (sub2 _ p).map (fun q => Sum.inr (Sum.inl q))
  | .comp _ _, Sum.inr (Sum.inr p) => (sub2 _ p).map (fun q => Sum.inr (Sum.inr q))
  | .prec _ cg, Sum.inl _ => some (Sum.inr (Sum.inr (codeRootPos cg)))
  | .prec _ _, Sum.inr (Sum.inl p) => (sub2 _ p).map (fun q => Sum.inr (Sum.inl q))
  | .prec _ _, Sum.inr (Sum.inr p) => (sub2 _ p).map (fun q => Sum.inr (Sum.inr q))
  | .rfind' _, Sum.inl _ => none
  | .rfind' _, Sum.inr p => (sub2 _ p).map Sum.inr

@[simp] theorem subAt_codeRootPos : ∀ c : Code, subAt c (codeRootPos c) = c
  | .zero | .succ | .left | .right => rfl
  | .pair _ _ | .comp _ _ | .prec _ _ | .rfind' _ => rfl

/-! ### The tags -/

variable {L : Language.{0, 0}}

/-- **The tags of the reduction into CODEHALT.** -/
inductive ProgTag (V : FinVocab L) (cP : Code) where
  /-- The root: the `comp` of the procedure with the value of the instance. -/
  | root
  /-- A node of the fixed code `cP`. -/
  | cp (p : SubPos cP)
  /-- The `pair` of the numeral and the nest of the tables. -/
  | pairN
  /-- The numeral chain, from the element held in the first coordinate on. -/
  | numN
  /-- The nest of the blocks of the symbols, from the symbol `i` on. -/
  | symN (i : Fin V.numSyms)
  /-- The level-`l` chain of the block of the symbol `i`, from the element
  held in the coordinate `l` on. -/
  | chainN (i : Fin V.numSyms) (l : Fin (dimOf V))
  /-- The shared `succ` node: the value `1`. -/
  | oneN
  /-- The shared `zero` node: the value `0`, and the tail of every chain. -/
  | zeroN

namespace ProgTag

variable {V : FinVocab L} {cP : Code}

/-- The numbering that makes the tags a finite type. -/
def idx : ProgTag V cP →
    Option (SubPos cP) × Option (Fin V.numSyms) × Option (Fin (dimOf V)) × Fin 8
  | .root => (none, none, none, 0)
  | .cp p => (some p, none, none, 1)
  | .pairN => (none, none, none, 2)
  | .numN => (none, none, none, 3)
  | .symN i => (none, some i, none, 4)
  | .chainN i l => (none, some i, some l, 5)
  | .oneN => (none, none, none, 6)
  | .zeroN => (none, none, none, 7)

theorem idx_injective : Function.Injective (idx (V := V) (cP := cP)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [idx]

instance : Finite (ProgTag V cP) := Finite.of_injective idx idx_injective

instance : Nonempty (ProgTag V cP) := ⟨.root⟩

instance : DecidableEq (ProgTag V cP) := fun _ _ =>
  decidable_of_iff _ ⟨fun h => idx_injective h, congrArg idx⟩

/-- **The constructor each tag draws.** Every tag draws exactly one, which is
what makes the exclusivity of the marks immediate. -/
def mark : ProgTag V cP → CodeTag
  | .root => .comp
  | .cp p => tagOf (subAt cP p)
  | .pairN => .pair
  | .numN => .comp
  | .symN _ => .pair
  | .chainN _ _ => .pair
  | .oneN => .succ
  | .zeroN => .zero

/-- The number of coordinates a tag uses; the others are padded with the
minimum of the input order. -/
def used : ProgTag V cP → ℕ
  | .root => 0
  | .cp _ => 0
  | .pairN => 0
  | .numN => 1
  | .symN _ => 0
  | .chainN _ l => (l : ℕ) + 1
  | .oneN => 0
  | .zeroN => 0

end ProgTag

end DescriptiveComplexity
