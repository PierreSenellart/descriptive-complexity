/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Fintype.Sort
import DescriptiveComplexity.Computability.Eval

/-!
# The number an instance is written as, and the code that writes it

The arithmetic half of the reduction `P ≤ᶠᵒ[≤] CODEHALT`: the *value* the
drawn code computes on input `0`, and the concrete finite structure that value
is decoded back into. Nothing here mentions a formula – the first-order side
is `DescriptiveComplexity.Problems.CodeHalt.Hardness.Interp`.

## The shape of the value

Every branch of the drawn code is evaluated at input `0`, so a constructor
node computes a constant: `zero` is `0`, `succ` is `1`, and
`Nat.pair` is what `pair` does. A *nest* is therefore a list of numbers, held
as `Nat.pair a₀ (Nat.pair a₁ (…))` with `0` for the empty list
(`DescriptiveComplexity.natNestFrom`), and reading its `d`-th entry is
following `d` links (`DescriptiveComplexity.nestGet`).

The value an instance is written as is

```
Nat.pair card (nest over the symbols of the vocabulary)
```

where the entry of a symbol is a nest of nests, `dim` levels deep, one level
per coordinate of a tuple: at the bottom of the `j`-th chain sits `1` if the
symbol holds of the tuple the chain positions spell out, and `0` if it does
not. The point of nesting by coordinate rather than numbering tuples in a
mixed radix is that *each level is a plain walk of the input order*, which is
what a first-order guard can describe, and no arithmetic on positions has to
be proved anywhere.

## Reading a value back

`DescriptiveComplexity.structOf` is the decoding, a
`FirstOrder.Language.FinStruct` over the same vocabulary: the universe size is
the first component, and a relation holds of a tuple exactly when following
the tuple's coordinates down the nests reaches `1`. It is primitive recursive
(`DescriptiveComplexity.primrec_structOf`), which is what lets the reduction
compose with the semi-decision procedure of the source problem.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Nat.Partrec (Code)

/-! ### Nests of numbers -/

section Nest

/-- Following `d` links of a nest. -/
def nestDrop (v d : ℕ) : ℕ := (fun w : ℕ => w.unpair.2)^[d] v

/-- The `d`-th entry of a nest. -/
def nestGet (v d : ℕ) : ℕ := (nestDrop v d).unpair.1

/-- Following the coordinates of a tuple down a nest of nests. -/
def nestLeaf (v : ℕ) (ds : List ℕ) : ℕ := ds.foldl nestGet v

@[simp] theorem nestDrop_zero (v : ℕ) : nestDrop v 0 = v := rfl

theorem nestDrop_succ (a b d : ℕ) : nestDrop (Nat.pair a b) (d + 1) = nestDrop b d := by
  rw [nestDrop, Function.iterate_succ_apply, Nat.unpair_pair, nestDrop]

@[simp] theorem nestDrop_zero_left (d : ℕ) : nestDrop 0 d = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show (0 : ℕ) = Nat.pair 0 0 from rfl, nestDrop_succ]
    exact ih

@[simp] theorem nestGet_zero_left (d : ℕ) : nestGet 0 d = 0 := by
  simp [nestGet]

@[simp] theorem nestGet_pair_zero (a b : ℕ) : nestGet (Nat.pair a b) 0 = a := by
  rw [nestGet, nestDrop_zero, Nat.unpair_pair]

theorem nestGet_pair_succ (a b d : ℕ) : nestGet (Nat.pair a b) (d + 1) = nestGet b d := by
  rw [nestGet, nestDrop_succ, nestGet]

@[simp] theorem nestLeaf_nil (v : ℕ) : nestLeaf v [] = v := rfl

@[simp] theorem nestLeaf_cons (v d : ℕ) (ds : List ℕ) :
    nestLeaf v (d :: ds) = nestLeaf (nestGet v d) ds := rfl

end Nest

/-! ### Nests, as values and as codes

A nest is written by a chain of `pair` nodes, whose tail is the constant `0`.
Both the chain of values and the chain of codes are indexed by a starting
position, because that is what the first-order interpretation has one element
for: the node standing at position `k` of the chain. -/

section NestFrom

variable {m : ℕ}

/-- The nest of the entries `g k, g (k+1), …`, as a number. -/
def natNestFrom (g : Fin m → ℕ) (k : ℕ) : ℕ :=
  if h : k < m then Nat.pair (g ⟨k, h⟩) (natNestFrom g (k + 1)) else 0
  termination_by m - k

/-- The nest of the entries `g k, g (k+1), …`, as a code. -/
def codeNestFrom (g : Fin m → Code) (k : ℕ) : Code :=
  if h : k < m then Code.pair (g ⟨k, h⟩) (codeNestFrom g (k + 1)) else Code.zero
  termination_by m - k

theorem natNestFrom_of_lt (g : Fin m → ℕ) {k : ℕ} (h : k < m) :
    natNestFrom g k = Nat.pair (g ⟨k, h⟩) (natNestFrom g (k + 1)) := by
  rw [natNestFrom, dif_pos h]

theorem natNestFrom_of_ge (g : Fin m → ℕ) {k : ℕ} (h : ¬k < m) : natNestFrom g k = 0 := by
  rw [natNestFrom, dif_neg h]

theorem codeNestFrom_of_lt (g : Fin m → Code) {k : ℕ} (h : k < m) :
    codeNestFrom g k = Code.pair (g ⟨k, h⟩) (codeNestFrom g (k + 1)) := by
  rw [codeNestFrom, dif_pos h]

theorem codeNestFrom_of_ge (g : Fin m → Code) {k : ℕ} (h : ¬k < m) :
    codeNestFrom g k = Code.zero := by
  rw [codeNestFrom, dif_neg h]

/-- **Reading an entry of a nest**: `d` links past the start `k` sits the
entry `k + d`, and `0` past the end. -/
theorem nestGet_natNestFrom (g : Fin m → ℕ) (d k : ℕ) :
    nestGet (natNestFrom g k) d = if h : k + d < m then g ⟨k + d, h⟩ else 0 := by
  induction d generalizing k with
  | zero =>
    by_cases h : k < m
    · rw [natNestFrom_of_lt g h, nestGet_pair_zero, dif_pos (by simpa using h)]
      simp
    · rw [natNestFrom_of_ge g h, nestGet_zero_left, dif_neg (by simpa using h)]
  | succ d ih =>
    by_cases h : k < m
    · rw [natNestFrom_of_lt g h, nestGet_pair_succ, ih,
        show k + 1 + d = k + (d + 1) from by omega]
    · rw [natNestFrom_of_ge g h, nestGet_zero_left, dif_neg (by omega)]

end NestFrom

/-! ### The evaluation of the codes that write a value -/

section Eval

open Nat.Partrec.Code

theorem eval_pair_zero {cf cg : Code} {a b : ℕ} (hf : eval cf 0 = Part.some a)
    (hg : eval cg 0 = Part.some b) : eval (Code.pair cf cg) 0 = Part.some (Nat.pair a b) := by
  simp [eval, hf, hg, Seq.seq]

theorem eval_comp_zero {cf cg : Code} {b : ℕ} (hg : eval cg 0 = Part.some b) :
    eval (Code.comp cf cg) 0 = eval cf b := by
  simp only [eval, hg]
  exact Part.bind_some _ _

/-- The code of a numeral: `n` applications of `succ` to `zero`. -/
def numCode : ℕ → Code
  | 0 => Code.zero
  | n + 1 => Code.comp Code.succ (numCode n)

theorem eval_numCode : ∀ n : ℕ, eval (numCode n) 0 = Part.some n
  | 0 => rfl
  | n + 1 => by
    rw [numCode, eval_comp_zero (eval_numCode n)]
    rfl

/-- The chain of codes writes the chain of values. -/
theorem eval_codeNestFrom {m : ℕ} (gc : Fin m → Code) (gv : Fin m → ℕ)
    (h : ∀ j, eval (gc j) 0 = Part.some (gv j)) (k : ℕ) :
    eval (codeNestFrom gc k) 0 = Part.some (natNestFrom gv k) := by
  by_cases hk : k < m
  · rw [codeNestFrom_of_lt gc hk, natNestFrom_of_lt gv hk]
    exact eval_pair_zero (h _) (eval_codeNestFrom gc gv h (k + 1))
  · rw [codeNestFrom_of_ge gc hk, natNestFrom_of_ge gv hk]
    rfl
  termination_by m - k

end Eval

/-! ### The dimension of the interpretation -/

section Dim

variable {L : Language.{0, 0}}

/-- The dimension the reduction works in: one more than the greatest arity of
the vocabulary, so that every symbol's arguments fit in a tuple and the tuples
have at least one coordinate (which the numeral chain walks). -/
def dimOf (V : FinVocab L) : ℕ := (Finset.univ.sup fun i : Fin V.numSyms => V.arity i) + 1

theorem arity_lt_dimOf (V : FinVocab L) (i : Fin V.numSyms) : V.arity i < dimOf V :=
  Nat.lt_succ_of_le (Finset.le_sup (f := fun i : Fin V.numSyms => V.arity i) (Finset.mem_univ i))

theorem arity_le_dimOf (V : FinVocab L) (i : Fin V.numSyms) : V.arity i ≤ dimOf V :=
  (arity_lt_dimOf V i).le

theorem dimOf_pos (V : FinVocab L) : 0 < dimOf V := Nat.succ_pos _

end Dim

/-! ### The value an ordered structure is written as -/

section Write

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L) {A : Type} [L.Structure A]

/-- Overwriting one coordinate of a tuple. -/
def setCo (j : ℕ) (a : A) (t : Fin (dimOf V) → A) : Fin (dimOf V) → A :=
  fun j' => if (j' : ℕ) = j then a else t j'

omit [L.IsRelational] [L.Structure A] in
theorem setCo_apply_self (j : ℕ) (hj : j < dimOf V) (a : A) (t : Fin (dimOf V) → A) :
    setCo V j a t ⟨j, hj⟩ = a := by rw [setCo, if_pos rfl]

omit [L.IsRelational] [L.Structure A] in
theorem setCo_apply_ne {j : ℕ} {j' : Fin (dimOf V)} (h : (j' : ℕ) ≠ j) (a : A)
    (t : Fin (dimOf V) → A) : setCo V j a t j' = t j' := by rw [setCo, if_neg h]

open Classical in
/-- Whether the symbol `i` holds of the first `V.arity i` coordinates of the
tuple `t`: the bit at the bottom of the chains. -/
noncomputable def bitOf (i : Fin V.numSyms) (t : Fin (dimOf V) → A) : Prop :=
  RelMap (V.sym i) fun j => t (Fin.castLE (arity_le_dimOf V i) j)

open Classical in
/-- **The value of a symbol's block, from `m` levels above the bottom.** At
the bottom it is the bit; one level up it is the nest of the values below,
indexed by the coordinate `dimOf V - m`, walked in the order of the input. -/
noncomputable def levelVal (n : ℕ) (f : Fin n → A) (i : Fin V.numSyms) :
    ℕ → (Fin (dimOf V) → A) → ℕ
  | 0, t => if bitOf V i t then 1 else 0
  | m + 1, t =>
      natNestFrom (fun d : Fin n => levelVal n f i m (setCo V (dimOf V - (m + 1)) (f d) t)) 0

open Classical in
/-- The code writing `DescriptiveComplexity.levelVal`. -/
noncomputable def levelCode (n : ℕ) (f : Fin n → A) (i : Fin V.numSyms) :
    ℕ → (Fin (dimOf V) → A) → Code
  | 0, t => if bitOf V i t then Code.succ else Code.zero
  | m + 1, t =>
      codeNestFrom (fun d : Fin n => levelCode n f i m (setCo V (dimOf V - (m + 1)) (f d) t)) 0

variable {V}

open Classical in
omit [L.IsRelational] in
theorem levelVal_zero (n : ℕ) (f : Fin n → A) (i : Fin V.numSyms) (t : Fin (dimOf V) → A) :
    levelVal V n f i 0 t = if bitOf V i t then 1 else 0 := by
  rw [levelVal]

open Classical in
omit [L.IsRelational] in
theorem levelCode_zero (n : ℕ) (f : Fin n → A) (i : Fin V.numSyms) (t : Fin (dimOf V) → A) :
    levelCode V n f i 0 t = if bitOf V i t then Code.succ else Code.zero := by
  rw [levelCode]

omit [L.IsRelational] in
theorem levelVal_succ (n : ℕ) (f : Fin n → A) (i : Fin V.numSyms) (m : ℕ)
    (t : Fin (dimOf V) → A) :
    levelVal V n f i (m + 1) t =
      natNestFrom (fun d : Fin n =>
        levelVal V n f i m (setCo V (dimOf V - (m + 1)) (f d) t)) 0 := by
  rw [levelVal]

omit [L.IsRelational] in
theorem levelCode_succ (n : ℕ) (f : Fin n → A) (i : Fin V.numSyms) (m : ℕ)
    (t : Fin (dimOf V) → A) :
    levelCode V n f i (m + 1) t =
      codeNestFrom (fun d : Fin n =>
        levelCode V n f i m (setCo V (dimOf V - (m + 1)) (f d) t)) 0 := by
  rw [levelCode]

omit [L.IsRelational] in
theorem eval_levelCode (n : ℕ) (f : Fin n → A) (i : Fin V.numSyms) :
    ∀ (m : ℕ) (t : Fin (dimOf V) → A),
      Nat.Partrec.Code.eval (levelCode V n f i m t) 0 = Part.some (levelVal V n f i m t)
  | 0, t => by
    classical
    rw [levelCode_zero, levelVal_zero]
    by_cases h : bitOf V i t
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl
  | m + 1, t => by
    rw [levelCode_succ, levelVal_succ]
    exact eval_codeNestFrom _ _ (fun d => eval_levelCode n f i m _) 0

variable (V)

open Classical in
/-- The value of the block of the symbol `i`: its chains, all `dimOf V` of
them, over an arbitrary starting tuple (every coordinate is overwritten on the
way down). -/
noncomputable def blockVal (n : ℕ) (f : Fin n → A) (t₀ : Fin (dimOf V) → A)
    (i : Fin V.numSyms) : ℕ :=
  levelVal V n f i (dimOf V) t₀

open Classical in
/-- The code of the block of the symbol `i`. -/
noncomputable def blockCode (n : ℕ) (f : Fin n → A) (t₀ : Fin (dimOf V) → A)
    (i : Fin V.numSyms) : Code :=
  levelCode V n f i (dimOf V) t₀

open Classical in
/-- **The value of a structure**: its size, paired with the nest of the blocks
of its symbols. -/
noncomputable def structVal (n : ℕ) (f : Fin n → A) (t₀ : Fin (dimOf V) → A) : ℕ :=
  Nat.pair n (natNestFrom (blockVal V n f t₀) 0)

end Write

/-! ### Reading a value back as a concrete structure -/

section Read

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)

/-- The leaf of the nests reached by the coordinates `ds`, in the block of the
symbol numbered `i`. -/
def leafOf (N : ℕ) (i : ℕ) (ds : List ℕ) : ℕ := nestLeaf (nestGet N.unpair.2 i) ds

/-- **The concrete structure a value denotes**: the universe has as many
elements as the first component says, and a symbol holds of a tuple exactly
when the coordinates of that tuple lead to `1` in the symbol's block. -/
def structOf (N : ℕ) : FinStruct V :=
  FinStruct.ofTable V (N.unpair.1 - 1) fun {a} R x =>
    decide (leafOf N (V.index R)
      (List.ofFn fun j : Fin (dimOf V) =>
        if h : (j : ℕ) < a then ((x ⟨j, h⟩ : Fin (N.unpair.1 - 1 + 1)) : ℕ) else 0) = 1)

omit [L.IsRelational] in
@[simp] theorem card_structOf (N : ℕ) : (structOf V N).card = N.unpair.1 - 1 + 1 := rfl

omit [L.IsRelational] in
theorem relMapBool_structOf (N : ℕ) {a : ℕ} (R : L.Relations a)
    (x : Fin a → (structOf V N).Univ) :
    (structOf V N).relMapBool R x =
      decide (leafOf N (V.index R)
        (List.ofFn fun j : Fin (dimOf V) =>
          if h : (j : ℕ) < a then ((x ⟨j, h⟩ : Fin (N.unpair.1 - 1 + 1)) : ℕ) else 0) = 1) :=
  FinStruct.relMapBool_ofTable _ _ _ R x

end Read

/-! ### The value is read back as the structure it was written from -/

section Roundtrip

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L) {A : Type} [L.Structure A]

open Classical in
omit [L.IsRelational] in
/-- **Following the coordinates of a tuple down the chains reaches the bit of
that tuple.** The induction is on the level: one coordinate is consumed at
each step, and the tuple built so far is the one the chains have already
walked. -/
theorem nestLeaf_levelVal (n : ℕ) (f : Fin n → A) (i : Fin V.numSyms)
    (ds : Fin (dimOf V) → ℕ) (hds : ∀ j, ds j < n) :
    ∀ (m : ℕ), m ≤ dimOf V → ∀ t : Fin (dimOf V) → A,
      (∀ j : Fin (dimOf V), (j : ℕ) < dimOf V - m → t j = f ⟨ds j, hds j⟩) →
      nestLeaf (levelVal V n f i m t) ((List.ofFn ds).drop (dimOf V - m)) =
        if bitOf V i (fun j => f ⟨ds j, hds j⟩) then 1 else 0 := by
  intro m
  induction m with
  | zero =>
    intro _ t ht
    have htt : t = fun j => f ⟨ds j, hds j⟩ := funext fun j => ht j (by simp)
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), nestLeaf_nil, levelVal_zero, htt]
  | succ m ih =>
    intro hm t ht
    have hp : dimOf V - (m + 1) < dimOf V := by omega
    have hp1 : dimOf V - (m + 1) + 1 = dimOf V - m := by omega
    set p : ℕ := dimOf V - (m + 1) with hpdef
    have hdrop : (List.ofFn ds).drop p = ds ⟨p, hp⟩ :: (List.ofFn ds).drop (p + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hp)]
      simp
    rw [levelVal_succ, hdrop, nestLeaf_cons, nestGet_natNestFrom]
    rw [dif_pos (show 0 + ds ⟨p, hp⟩ < n from by simpa using hds _)]
    rw [hp1]
    refine ih (by omega) _ fun j hj => ?_
    rw [← hp1] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · rw [setCo_apply_ne V (by omega) _ _]
      exact ht j (by omega)
    · rw [show j = (⟨p, hp⟩ : Fin (dimOf V)) from Fin.ext hj', setCo_apply_self V p hp]
      exact congrArg f (Fin.ext (by simp))

omit [L.IsRelational] in
@[simp] theorem unpair_structVal_fst (n : ℕ) (f : Fin n → A) (t₀ : Fin (dimOf V) → A) :
    (structVal V n f t₀).unpair.1 = n := by rw [structVal, Nat.unpair_pair]

omit [L.IsRelational] in
@[simp] theorem unpair_structVal_snd (n : ℕ) (f : Fin n → A) (t₀ : Fin (dimOf V) → A) :
    (structVal V n f t₀).unpair.2 = natNestFrom (blockVal V n f t₀) 0 := by
  rw [structVal, Nat.unpair_pair]

open Classical in
omit [L.IsRelational] in
/-- The leaf of the value of a structure is the bit of the tuple the
coordinates spell out. -/
theorem leafOf_structVal (n : ℕ) (f : Fin n → A) (t₀ : Fin (dimOf V) → A)
    (i : Fin V.numSyms) (ds : Fin (dimOf V) → ℕ) (hds : ∀ j, ds j < n) :
    leafOf (structVal V n f t₀) (i : ℕ) (List.ofFn ds) =
      if bitOf V i (fun j => f ⟨ds j, hds j⟩) then 1 else 0 := by
  rw [leafOf, unpair_structVal_snd, nestGet_natNestFrom,
    dif_pos (show 0 + (i : ℕ) < V.numSyms from by simp)]
  have hb : blockVal V n f t₀ ⟨0 + (i : ℕ), by simp⟩ =
      levelVal V n f i (dimOf V) t₀ := by
    rw [blockVal]
    exact congrArg (fun j => levelVal V n f j (dimOf V) t₀) (Fin.ext (by simp))
  rw [hb]
  have := nestLeaf_levelVal V n f i ds hds (dimOf V) le_rfl t₀ (by simp)
  rwa [Nat.sub_self, List.drop_zero] at this

omit [L.IsRelational] in
/-- Reading a relation through the number of its symbol: the arity dependency
of `FirstOrder.Language.FinVocab`, discharged for a `Prop`-valued reading. -/
theorem relMap_heq {m a : ℕ} (h : m = a) (R : L.Relations m) (R' : L.Relations a)
    (hR : HEq R R') (y : Fin m → A) (z : Fin a → A) (hy : ∀ j, y j = z (Fin.cast h j)) :
    (RelMap R y : Prop) ↔ RelMap R' z := by
  subst h
  have hyz : y = z := funext fun j => by simpa using hy j
  subst hyz
  rw [eq_of_heq hR]

open Classical in
omit [L.IsRelational] in
/-- **Reading the decoded structure is reading the structure it was written
from**, once the two tuples are matched by their numbers. -/
theorem relMapBool_structVal (n : ℕ) (hn : 0 < n) (f : Fin n → A)
    (t₀ : Fin (dimOf V) → A) {a : ℕ} (R : L.Relations a)
    (y : Fin a → (structOf V (structVal V n f t₀)).Univ) (z : Fin a → Fin n)
    (hyz : ∀ j, ((y j : Fin _) : ℕ) = ((z j : Fin n) : ℕ)) :
    (structOf V (structVal V n f t₀)).relMapBool R y =
      decide (RelMap R fun j => f (z j)) := by
  have hcard : (structVal V n f t₀).unpair.1 - 1 + 1 = n := by
    rw [unpair_structVal_fst]; omega
  have hds : ∀ j : Fin (dimOf V),
      (if h : (j : ℕ) < a then ((y ⟨j, h⟩ : Fin _) : ℕ) else 0) < n := by
    intro j
    by_cases h : (j : ℕ) < a
    · rw [dif_pos h]
      have h2 : ((y ⟨j, h⟩ : (structOf V (structVal V n f t₀)).Univ) : ℕ) <
        (structVal V n f t₀).unpair.1 - 1 + 1 := (y ⟨j, h⟩).isLt
      omega
    · rw [dif_neg h]
      exact hn
  have ha : V.arity (V.index R) = a := V.arity_index R
  have hbit : (bitOf V (V.index R) fun j' =>
      f ⟨if h : (j' : ℕ) < a then ((y ⟨j', h⟩ : Fin _) : ℕ) else 0, hds j'⟩) ↔
      RelMap R fun j => f (z j) := by
    refine relMap_heq ha (V.sym (V.index R)) R (V.sym_index R) _ _ fun j => ?_
    have hj : ((Fin.castLE (arity_le_dimOf V (V.index R)) j : Fin (dimOf V)) : ℕ) < a := by
      have hjl := j.isLt
      have hcst : ((Fin.castLE (arity_le_dimOf V (V.index R)) j : Fin (dimOf V)) : ℕ) =
        (j : ℕ) := rfl
      omega
    refine congrArg f (Fin.ext ?_)
    change (if h : ((Fin.castLE (arity_le_dimOf V (V.index R)) j : Fin (dimOf V)) : ℕ) < a then
      ((y ⟨_, h⟩ : Fin _) : ℕ) else 0) = ((z (Fin.cast ha j) : Fin n) : ℕ)
    rw [dif_pos hj]
    exact (hyz ⟨_, hj⟩).trans (congrArg (fun w => ((z w : Fin n) : ℕ)) (Fin.ext rfl))
  rw [relMapBool_structOf, leafOf_structVal V n f t₀ (V.index R) _ hds]
  by_cases hb : (bitOf V (V.index R) fun j' =>
      f ⟨if h : (j' : ℕ) < a then ((y ⟨j', h⟩ : Fin _) : ℕ) else 0, hds j'⟩)
  · rw [if_pos hb]
    simp [hbit.mp hb]
  · rw [if_neg hb]
    have hnr : ¬(RelMap R fun j => f (z j) : Prop) := fun hr => hb (hbit.mpr hr)
    simp [hnr]

open Classical in
/-- **The decoding of the value of a structure is that structure**, along the
numbering the value was written with. This is the one mathematical fact the
reduction rests on: a semi-decision procedure reading concrete instances,
applied to the value drawn in the instance, answers about the instance
itself. -/
noncomputable def structValEquiv (n : ℕ) (hn : 0 < n) (f : Fin n ≃ A)
    (t₀ : Fin (dimOf V) → A) :
    (structOf V (structVal V n (⇑f) t₀)).Univ ≃[L] A where
  toEquiv :=
    (finCongr (show (structVal V n (⇑f) t₀).unpair.1 - 1 + 1 = n by
      rw [unpair_structVal_fst]; omega)).trans f
  map_fun' g := isEmptyElim g
  map_rel' {a} R y := by
    have hcard : (structVal V n (⇑f) t₀).unpair.1 - 1 + 1 = n := by
      rw [unpair_structVal_fst]; omega
    change (RelMap R fun j => f (finCongr hcard (y j)) : Prop) ↔ _
    rw [FinStruct.relMap_iff,
      relMapBool_structVal V n hn (⇑f) t₀ R y (fun j => finCongr hcard (y j)) (fun _ => rfl),
      decide_eq_true_eq]

end Roundtrip

/-! ### The decoding is primitive recursive -/

section Primrec

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)

theorem primrec_nestGet : Primrec₂ nestGet := by
  have hdrop : Primrec fun q : ℕ × ℕ => nestDrop q.1 q.2 :=
    (Primrec.nat_iterate Primrec.snd Primrec.fst
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  exact (Primrec.fst.comp (Primrec.unpair.comp hdrop)).of_eq fun _ => rfl

theorem primrec_nestLeaf : Primrec₂ nestLeaf :=
  (Primrec.list_foldl Primrec.snd Primrec.fst
    (primrec_nestGet.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).to₂

omit [L.IsRelational] in
/-- **The decoding is primitive recursive**: this is what lets the reduction
compose with a semi-decision procedure of the source problem. -/
theorem primrec_structOf : Primrec (structOf V) := by
  have hn : Primrec fun N : ℕ => N.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hk : Primrec fun N : ℕ => N.unpair.1 - 1 :=
    Primrec.nat_sub.comp hn (Primrec.const 1)
  refine ((FinStruct.primrec_mk V).comp hk (Primrec.list_ofFn ?_)).of_eq fun _ => rfl
  intro i'
  refine Primrec.list_map
    (Primrec.list_range.comp
      ((FirstOrder.Language.primrec_pow_const (V.arity i')).comp
        (Primrec.succ.comp hk))) ?_
  have hcard : Primrec fun q : ℕ × ℕ => q.1.unpair.1 - 1 + 1 :=
    Primrec.succ.comp (hk.comp Primrec.fst)
  have hds : Primrec fun q : ℕ × ℕ =>
      List.ofFn fun j : Fin (dimOf V) =>
        if (j : ℕ) < V.arity i' then
          FirstOrder.Language.digitAt (q.1.unpair.1 - 1 + 1) q.2 (j : ℕ) else 0 := by
    refine Primrec.list_ofFn fun j => ?_
    by_cases hj : (j : ℕ) < V.arity i'
    · simp only [if_pos hj]
      exact (FirstOrder.Language.primrec_digitAt (j : ℕ)).comp hcard Primrec.snd
    · simp only [if_neg hj]
      exact Primrec.const 0
  have hleaf : Primrec fun q : ℕ × ℕ =>
      nestLeaf (nestGet q.1.unpair.2 (i' : ℕ))
        (List.ofFn fun j : Fin (dimOf V) =>
          if (j : ℕ) < V.arity i' then
            FirstOrder.Language.digitAt (q.1.unpair.1 - 1 + 1) q.2 (j : ℕ) else 0) :=
    primrec_nestLeaf.comp
      (primrec_nestGet.comp
        ((Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))) (Primrec.const (i' : ℕ)))
      hds
  refine ((Primrec.eq.comp hleaf (Primrec.const 1)).decide).of_eq fun q => ?_
  simp only [leafOf, V.index_sym i']
  rfl

end Primrec

end DescriptiveComplexity
