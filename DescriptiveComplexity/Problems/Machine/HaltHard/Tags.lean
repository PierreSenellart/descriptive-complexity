/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Finite.Sum
import DescriptiveComplexity.Problems.Pcp.Hardness.ConfigWord

/-!
# The alphabet of the machine simulating a `ToPartrec` code

The static data of the RE-hardness of `DescriptiveComplexity.HALT`: the
machine `M(c)` that the reduction draws simulates
the sequential semantics `Turing.ToPartrec.step` of a **fixed** code `c`, so
its states and symbols are indexed by the *positions of the syntax tree of
`c`* – a finite type built by recursion on `c`, the `SubPos` pattern of the
CODEHALT reduction – and by nothing else. This file carries those positions
(`DescriptiveComplexity.HaltHard.CPos`), the continuations restricted to
subcodes (`DescriptiveComplexity.HaltHard.PCont`), the tape alphabet
(`DescriptiveComplexity.HaltHard.SimSym`) and the encoding of a configuration
as a tape word:

    bk … bk endL ⟦TOP⟧ gap ⟦…⟧ gap ⟦BASE⟧ gap mid gap ⟦value, mirrored⟧ endR bk …

* the **value** `[n₁, …, nₖ]` sits between the fixed separator `mid` and the
  movable right marker `endR`, written **mirrored**: blocks in reverse order,
  each block `com` first, so the word reads `com 1^nₖ … com 1^n₁` and the head
  block's digits end at `endR`. The mirroring is what gives every operation on
  the head of the value unbounded room: prepending grows the word at `endR`,
  into the blank half-tape, and no marker ever has to move over another
  letter. The cell right of `mid` is kept blank, so a block separator can
  always be closed next to an empty value;
* a continuation frame is a header letter – carrying the position of its
  code, if it has one – followed by its stored value: a `cons₁` frame stores
  it *straight* (`encVal`), which is what one marked copy loop writes at
  `endL`, and a `cons₂` frame stores it *mirrored*, which is what the
  destructive move of the exchange writes; the top frame sits leftmost;
* frames may be separated by blank gaps – erasing a consumed frame just
  leaves one – and the frame region is bounded by the movable left marker
  `endL` and the fixed separator `mid`.

Every code in a continuation frame reached from `stepNormal c … `/`stepRet`
is a subcode of `c`, so the positioned continuations `PCont` mirror
`Turing.ToPartrec.Cont` with positions for codes;
`DescriptiveComplexity.HaltHard.PCont.toCont` projects back, and the
simulation is stated over `PCont` throughout.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec

/-! ### The positions of the syntax tree of a code -/

/-- The positions of the syntax tree of a `ToPartrec` code, by recursion on
the code: one tag per node, so that drawing the machine of a fixed code costs
nothing at any instance size. -/
def CPos : Code → Type
  | .zero' => Unit
  | .succ => Unit
  | .tail => Unit
  | .cons f fs => Unit ⊕ CPos f ⊕ CPos fs
  | .comp f g => Unit ⊕ CPos f ⊕ CPos g
  | .case f g => Unit ⊕ CPos f ⊕ CPos g
  | .fix f => Unit ⊕ CPos f

instance instFiniteCPos : ∀ c : Code, Finite (CPos c)
  | .zero' => inferInstanceAs (Finite Unit)
  | .succ => inferInstanceAs (Finite Unit)
  | .tail => inferInstanceAs (Finite Unit)
  | .cons f fs =>
      letI := instFiniteCPos f
      letI := instFiniteCPos fs
      inferInstanceAs (Finite (Unit ⊕ CPos f ⊕ CPos fs))
  | .comp f g =>
      letI := instFiniteCPos f
      letI := instFiniteCPos g
      inferInstanceAs (Finite (Unit ⊕ CPos f ⊕ CPos g))
  | .case f g =>
      letI := instFiniteCPos f
      letI := instFiniteCPos g
      inferInstanceAs (Finite (Unit ⊕ CPos f ⊕ CPos g))
  | .fix f =>
      letI := instFiniteCPos f
      inferInstanceAs (Finite (Unit ⊕ CPos f))

instance instDecidableEqCPos : ∀ c : Code, DecidableEq (CPos c)
  | .zero' => inferInstanceAs (DecidableEq Unit)
  | .succ => inferInstanceAs (DecidableEq Unit)
  | .tail => inferInstanceAs (DecidableEq Unit)
  | .cons f fs =>
      letI := instDecidableEqCPos f
      letI := instDecidableEqCPos fs
      inferInstanceAs (DecidableEq (Unit ⊕ CPos f ⊕ CPos fs))
  | .comp f g =>
      letI := instDecidableEqCPos f
      letI := instDecidableEqCPos g
      inferInstanceAs (DecidableEq (Unit ⊕ CPos f ⊕ CPos g))
  | .case f g =>
      letI := instDecidableEqCPos f
      letI := instDecidableEqCPos g
      inferInstanceAs (DecidableEq (Unit ⊕ CPos f ⊕ CPos g))
  | .fix f =>
      letI := instDecidableEqCPos f
      inferInstanceAs (DecidableEq (Unit ⊕ CPos f))

/-- The root position. -/
def cRoot : ∀ c : Code, CPos c
  | .zero' => ()
  | .succ => ()
  | .tail => ()
  | .cons _ _ => Sum.inl ()
  | .comp _ _ => Sum.inl ()
  | .case _ _ => Sum.inl ()
  | .fix _ => Sum.inl ()

instance (c : Code) : Nonempty (CPos c) := ⟨cRoot c⟩

/-- The subcode sitting at a position. -/
def codeAt : ∀ {c : Code}, CPos c → Code
  | .zero', _ => .zero'
  | .succ, _ => .succ
  | .tail, _ => .tail
  | .cons f fs, p =>
    match p with
    | .inl _ => .cons f fs
    | .inr (.inl q) => codeAt q
    | .inr (.inr q) => codeAt q
  | .comp f g, p =>
    match p with
    | .inl _ => .comp f g
    | .inr (.inl q) => codeAt q
    | .inr (.inr q) => codeAt q
  | .case f g, p =>
    match p with
    | .inl _ => .case f g
    | .inr (.inl q) => codeAt q
    | .inr (.inr q) => codeAt q
  | .fix f, p =>
    match p with
    | .inl _ => .fix f
    | .inr q => codeAt q

@[simp] theorem codeAt_cRoot : ∀ c : Code, codeAt (cRoot c) = c
  | .zero' => rfl
  | .succ => rfl
  | .tail => rfl
  | .cons _ _ => rfl
  | .comp _ _ => rfl
  | .case _ _ => rfl
  | .fix _ => rfl

/-- The positions of the immediate subterms: the first child of a binary
node. -/
def child₁ : ∀ {c : Code}, CPos c → Option (CPos c)
  | .zero', _ => none
  | .succ, _ => none
  | .tail, _ => none
  | .cons f _, p =>
    match p with
    | .inl _ => some (Sum.inr (Sum.inl (cRoot f)))
    | .inr (.inl q) => (child₁ q).map fun r => Sum.inr (Sum.inl r)
    | .inr (.inr q) => (child₁ q).map fun r => Sum.inr (Sum.inr r)
  | .comp f _, p =>
    match p with
    | .inl _ => some (Sum.inr (Sum.inl (cRoot f)))
    | .inr (.inl q) => (child₁ q).map fun r => Sum.inr (Sum.inl r)
    | .inr (.inr q) => (child₁ q).map fun r => Sum.inr (Sum.inr r)
  | .case f _, p =>
    match p with
    | .inl _ => some (Sum.inr (Sum.inl (cRoot f)))
    | .inr (.inl q) => (child₁ q).map fun r => Sum.inr (Sum.inl r)
    | .inr (.inr q) => (child₁ q).map fun r => Sum.inr (Sum.inr r)
  | .fix f, p =>
    match p with
    | .inl _ => some (Sum.inr (cRoot f))
    | .inr q => (child₁ q).map fun r => Sum.inr r

/-- The positions of the immediate subterms: the second child of a binary
node. -/
def child₂ : ∀ {c : Code}, CPos c → Option (CPos c)
  | .zero', _ => none
  | .succ, _ => none
  | .tail, _ => none
  | .cons _ fs, p =>
    match p with
    | .inl _ => some (Sum.inr (Sum.inr (cRoot fs)))
    | .inr (.inl q) => (child₂ q).map fun r => Sum.inr (Sum.inl r)
    | .inr (.inr q) => (child₂ q).map fun r => Sum.inr (Sum.inr r)
  | .comp _ g, p =>
    match p with
    | .inl _ => some (Sum.inr (Sum.inr (cRoot g)))
    | .inr (.inl q) => (child₂ q).map fun r => Sum.inr (Sum.inl r)
    | .inr (.inr q) => (child₂ q).map fun r => Sum.inr (Sum.inr r)
  | .case _ g, p =>
    match p with
    | .inl _ => some (Sum.inr (Sum.inr (cRoot g)))
    | .inr (.inl q) => (child₂ q).map fun r => Sum.inr (Sum.inl r)
    | .inr (.inr q) => (child₂ q).map fun r => Sum.inr (Sum.inr r)
  | .fix _, p =>
    match p with
    | .inl _ => none
    | .inr q => (child₂ q).map fun r => Sum.inr r

/-! ### The codes at the children

The step function dispatches on the *code* at a position and moves to its
children, so the simulation needs to read the child positions' codes off the
parent's. The two functions below are the code-level shadows of
`DescriptiveComplexity.HaltHard.child₁`/`child₂`, and the lemmas identify the
two readings. -/

/-- The left immediate subterm of a code. -/
def lchild? : Code → Option Code
  | .cons f _ => some f
  | .comp f _ => some f
  | .case f _ => some f
  | .fix f => some f
  | _ => none

/-- The right immediate subterm of a code. -/
def rchild? : Code → Option Code
  | .cons _ fs => some fs
  | .comp _ g => some g
  | .case _ g => some g
  | _ => none

/-- The code at the first child is the first subterm of the code at the
position. -/
theorem codeAt_child₁ : ∀ {c : Code} (p : CPos c),
    (child₁ p).map (fun q => codeAt q) = lchild? (codeAt p)
  | .zero', _ => rfl
  | .succ, _ => rfl
  | .tail, _ => rfl
  | .cons f _, .inl _ => congrArg some (codeAt_cRoot f)
  | .cons _ _, .inr (.inl q) => (Option.map_map _ _ _).trans (codeAt_child₁ q)
  | .cons _ _, .inr (.inr q) => (Option.map_map _ _ _).trans (codeAt_child₁ q)
  | .comp f _, .inl _ => congrArg some (codeAt_cRoot f)
  | .comp _ _, .inr (.inl q) => (Option.map_map _ _ _).trans (codeAt_child₁ q)
  | .comp _ _, .inr (.inr q) => (Option.map_map _ _ _).trans (codeAt_child₁ q)
  | .case f _, .inl _ => congrArg some (codeAt_cRoot f)
  | .case _ _, .inr (.inl q) => (Option.map_map _ _ _).trans (codeAt_child₁ q)
  | .case _ _, .inr (.inr q) => (Option.map_map _ _ _).trans (codeAt_child₁ q)
  | .fix f, .inl _ => congrArg some (codeAt_cRoot f)
  | .fix _, .inr q => (Option.map_map _ _ _).trans (codeAt_child₁ q)

/-- The code at the second child is the second subterm of the code at the
position. -/
theorem codeAt_child₂ : ∀ {c : Code} (p : CPos c),
    (child₂ p).map (fun q => codeAt q) = rchild? (codeAt p)
  | .zero', _ => rfl
  | .succ, _ => rfl
  | .tail, _ => rfl
  | .cons _ fs, .inl _ => congrArg some (codeAt_cRoot fs)
  | .cons _ _, .inr (.inl q) => (Option.map_map _ _ _).trans (codeAt_child₂ q)
  | .cons _ _, .inr (.inr q) => (Option.map_map _ _ _).trans (codeAt_child₂ q)
  | .comp _ g, .inl _ => congrArg some (codeAt_cRoot g)
  | .comp _ _, .inr (.inl q) => (Option.map_map _ _ _).trans (codeAt_child₂ q)
  | .comp _ _, .inr (.inr q) => (Option.map_map _ _ _).trans (codeAt_child₂ q)
  | .case _ g, .inl _ => congrArg some (codeAt_cRoot g)
  | .case _ _, .inr (.inl q) => (Option.map_map _ _ _).trans (codeAt_child₂ q)
  | .case _ _, .inr (.inr q) => (Option.map_map _ _ _).trans (codeAt_child₂ q)
  | .fix _, .inl _ => rfl
  | .fix _, .inr q => (Option.map_map _ _ _).trans (codeAt_child₂ q)

variable {c : Code}

/-- The first child of the code at `p`, defaulting to the root – the default
is never taken at the positions the machine visits. -/
def c₁ (p : CPos c) : CPos c := (child₁ p).getD (cRoot c)

/-- The second child of the code at `p`. -/
def c₂ (p : CPos c) : CPos c := (child₂ p).getD (cRoot c)

/-- The code at the first child, when the position holds a code with a first
subterm. -/
theorem codeAt_c₁ {p : CPos c} {f : Code} (h : lchild? (codeAt p) = some f) :
    codeAt (c₁ p) = f := by
  have hm := codeAt_child₁ p
  rw [h] at hm
  rcases hq : child₁ p with - | q
  · rw [hq] at hm
    exact absurd hm (by simp)
  · rw [hq, Option.map_some] at hm
    rw [c₁, hq, Option.getD_some]
    exact Option.some_injective _ hm

/-- The code at the second child, when the position holds a code with a
second subterm. -/
theorem codeAt_c₂ {p : CPos c} {g : Code} (h : rchild? (codeAt p) = some g) :
    codeAt (c₂ p) = g := by
  have hm := codeAt_child₂ p
  rw [h] at hm
  rcases hq : child₂ p with - | q
  · rw [hq] at hm
    exact absurd hm (by simp)
  · rw [hq, Option.map_some] at hm
    rw [c₂, hq, Option.getD_some]
    exact Option.some_injective _ hm

@[simp] theorem codeAt_c₁_cons {p : CPos c} {f fs : Code} (h : codeAt p = .cons f fs) :
    codeAt (c₁ p) = f := codeAt_c₁ (by rw [h]; rfl)

@[simp] theorem codeAt_c₂_cons {p : CPos c} {f fs : Code} (h : codeAt p = .cons f fs) :
    codeAt (c₂ p) = fs := codeAt_c₂ (by rw [h]; rfl)

@[simp] theorem codeAt_c₁_comp {p : CPos c} {f g : Code} (h : codeAt p = .comp f g) :
    codeAt (c₁ p) = f := codeAt_c₁ (by rw [h]; rfl)

@[simp] theorem codeAt_c₂_comp {p : CPos c} {f g : Code} (h : codeAt p = .comp f g) :
    codeAt (c₂ p) = g := codeAt_c₂ (by rw [h]; rfl)

@[simp] theorem codeAt_c₁_case {p : CPos c} {f g : Code} (h : codeAt p = .case f g) :
    codeAt (c₁ p) = f := codeAt_c₁ (by rw [h]; rfl)

@[simp] theorem codeAt_c₂_case {p : CPos c} {f g : Code} (h : codeAt p = .case f g) :
    codeAt (c₂ p) = g := codeAt_c₂ (by rw [h]; rfl)

@[simp] theorem codeAt_c₁_fix {p : CPos c} {f : Code} (h : codeAt p = .fix f) :
    codeAt (c₁ p) = f := codeAt_c₁ (by rw [h]; rfl)

/-! ### Continuations over positions

Every code stored in a continuation reached from `stepNormal c`/`stepRet` is
a subcode of `c`, so the simulation works with continuations carrying
*positions* and projects back to `Turing.ToPartrec.Cont` when it meets the
library semantics. -/

/-- A continuation whose codes are positions of the syntax tree of `c`. -/
inductive PCont (c : Code) : Type
  /-- The empty continuation. -/
  | halt : PCont c
  /-- The first half of a `cons`: evaluate the second component on the
  stored value. -/
  | cons₁ : CPos c → List ℕ → PCont c → PCont c
  /-- The second half of a `cons`: prepend the stored head. -/
  | cons₂ : List ℕ → PCont c → PCont c
  /-- A pending composition. -/
  | comp : CPos c → PCont c → PCont c
  /-- A pending fixpoint. -/
  | fix : CPos c → PCont c → PCont c

/-- The continuation a positioned continuation stands for. -/
def PCont.toCont : PCont c → Cont
  | .halt => .halt
  | .cons₁ p as k => .cons₁ (codeAt p) as k.toCont
  | .cons₂ ns k => .cons₂ ns k.toCont
  | .comp p k => .comp (codeAt p) k.toCont
  | .fix p k => .fix (codeAt p) k.toCont

/-! ### The tape alphabet -/

/-- The tape alphabet of the simulating machine: the blank, the unary digit
and the block separator (each with a primed copy for the one non-destructive
copy loop), the three markers – the movable `endL` and `endR` and the fixed
`mid` – and one header letter per continuation frame shape, the ones carrying
a code carrying its position. -/
inductive SimSym (c : Code) : Type
  /-- The blank. -/
  | bk : SimSym c
  /-- The unary digit. -/
  | one : SimSym c
  /-- The marked unary digit, inside a copy loop. -/
  | one' : SimSym c
  /-- The block separator closing each number. -/
  | com : SimSym c
  /-- The marked block separator, inside a copy loop. -/
  | com' : SimSym c
  /-- The movable left end of the frame region. -/
  | endL : SimSym c
  /-- The fixed separator between the frames and the value. -/
  | mid : SimSym c
  /-- The movable right end of the value region. -/
  | endR : SimSym c
  /-- The header of a `cons₁` frame, carrying the position of its code. -/
  | hCons₁ : CPos c → SimSym c
  /-- The header of a `cons₂` frame. -/
  | hCons₂ : SimSym c
  /-- The header of a `comp` frame, carrying the position of its code. -/
  | hComp : CPos c → SimSym c
  /-- The header of a `fix` frame, carrying the position of its code. -/
  | hFix : CPos c → SimSym c

instance : Finite (SimSym c) := by
  refine Finite.of_injective (fun s : SimSym c =>
    (match s with
      | .bk => Sum.inl 0
      | .one => Sum.inl 1
      | .one' => Sum.inl 2
      | .com => Sum.inl 3
      | .com' => Sum.inl 4
      | .endL => Sum.inl 5
      | .mid => Sum.inl 6
      | .endR => Sum.inl 7
      | .hCons₂ => Sum.inl 8
      | .hCons₁ p => Sum.inr (Sum.inl p)
      | .hComp p => Sum.inr (Sum.inr (Sum.inl p))
      | .hFix p => Sum.inr (Sum.inr (Sum.inr p)) :
      Fin 9 ⊕ (CPos c ⊕ (CPos c ⊕ CPos c)))) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

/-! ### Words -/

/-- The word of one number: its unary digits, closed by a separator. -/
def encNum (n : ℕ) : List (SimSym c) := List.replicate n .one ++ [.com]

/-- The word of a value, head block leftmost. The value *region* of the tape
holds `(encVal v).reverse` – blocks in reverse order, each separator before
its digits – so that the head block ends at the movable marker `endR` and
every operation on it has the blank half-tape to grow into. -/
def encVal (v : List ℕ) : List (SimSym c) := v.flatMap encNum

/-- The word of one continuation frame: its header, then its stored value –
straight in a `cons₁` frame (what the marked copy loop writes), mirrored in a
`cons₂` frame (what the destructive move of the exchange writes). -/
def encFrame : PCont c → List (SimSym c)
  | .halt => []
  | .cons₁ p as _ => .hCons₁ p :: encVal as
  | .cons₂ ns _ => .hCons₂ :: (encVal ns).reverse
  | .comp p _ => [.hComp p]
  | .fix p _ => [.hFix p]

@[simp] theorem encNum_ne_nil (n : ℕ) : encNum (c := c) n ≠ [] := by
  simp [encNum]

@[simp] theorem length_encNum (n : ℕ) : (encNum (c := c) n).length = n + 1 := by
  simp [encNum]

@[simp] theorem encVal_nil : encVal (c := c) [] = [] := rfl

@[simp] theorem encVal_cons (n : ℕ) (v : List ℕ) :
    encVal (c := c) (n :: v) = encNum n ++ encVal v := rfl

theorem length_encVal (v : List ℕ) :
    (encVal (c := c) v).length = v.sum + v.length := by
  induction v with
  | nil => rfl
  | cons n v ih =>
    rw [encVal_cons, List.length_append, ih, length_encNum, List.sum_cons, List.length_cons]
    omega

end HaltHard

end DescriptiveComplexity
