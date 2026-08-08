/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadArith
import DescriptiveComplexity.ArithmeticDefinable
import DescriptiveComplexity.HeadCaptureDet

/-!
# Evaluating an arithmetic formula with heads, and `AC⁰ ⊆ LOGSPACE`

The last step of the machine route to the bottom class: **a deterministic
multi-head automaton decides any fixed sentence of `FO(≤, +, ×)`**, whence
`DescriptiveComplexity.ac0Definable_mem_LOGSPACE`.

## What is new here, against `HeadEval`

`DescriptiveComplexity.HeadProgram.evalP` already evaluates a first-order formula
of the head positions: atoms are quantifier-free *guards*, implication is a
branch, and a quantifier is a sweep of two fresh heads. It cannot be used as it
stands, for the reason the whole file exists: the formula to evaluate lives over
`L.sum Language.arith`, while the machine's guards live over
`L.sum Language.order`. A guard may not read `plus` or `times` – they are not
relations of the instance at all, but functions of the order – so those two atoms
must be *computed*, not read.

So this is `evalP` with one case split four ways
(`DescriptiveComplexity.HeadProgram.arithAtomP`):

* an atom of the input vocabulary, and an atom of `≤`, stay **guards**, their
  terms carried across the two languages by
  `DescriptiveComplexity.relTerm` (both languages being relational, a term is a
  variable, so the map is the identity on variables);
* a `plus` atom becomes the **program** `DescriptiveComplexity.HeadProgram.plusP`
  on the three heads its arguments live in, and a `times` atom becomes
  `DescriptiveComplexity.HeadProgram.timesP` – the two deciders of
  `DescriptiveComplexity.HeadArith`, which is what
  `DescriptiveComplexity.HeadProgram.wireP` lets a *node* of a control graph be.

Everything else – the sweep, the branch, the head accounting – is reused from
`HeadEval` unchanged, which is why this file is short.

## The head layout

`DescriptiveComplexity.HeadProgram.ArithScratch` pins the seven heads the
arithmetic needs to the seven positions above the quantifier region: the four
working heads of a multiplication first, then the three scratch heads of an
addition. It has to be *above* the quantifier region because the fragments' own
protection level is the evaluator's current level `d`, which grows as the
evaluation enters quantifiers – and the invariant that makes the induction go
through is that `d + qdepth` does not change.

## The result, and what it does not say

`DescriptiveComplexity.ac0Definable_mem_LOGSPACE`: everything AC⁰ definable is in
`DescriptiveComplexity.LOGSPACE`. With
`DescriptiveComplexity.exists_ac0Definable_not_foDefinable` and
`DescriptiveComplexity.parity_mem_LOGSPACE` this pins the bottom of the ladder:

> `FO(≤) ⊊ AC⁰ ⊆ LOGSPACE ⊆ NL ⊆ PTIME`

with the first inclusion strict and the second's strictness *exactly* the
switching lemma (PARITY is in LOGSPACE here, and outside AC⁰ classically), which
this library does not prove. It also supersedes
`DescriptiveComplexity.ac0Definable_mem_PTIME`, which the fixed-point route gave
for a tenth of the work; that route is kept, both because it is the cheap way to
the same corollaries and because the two together say something the machine route
alone does not – that the numeric predicates are *simultaneously* one induction
and one deterministic walk.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Terms of a relational language -/

section RelTerm

variable {L L' : Language.{0, 0}} [L.IsRelational] {β : Type}

/-- **The variable a term of a relational vocabulary is**: with no function
symbols, a term is nothing else. -/
def relVar : L.Term β → β
  | .var v => v
  | .func f _ => isEmptyElim f

/-- A term of a relational vocabulary, read as a term of another vocabulary: the
identity on variables, and there is nothing else. -/
def relTerm : L.Term β → L'.Term β
  | .var v => .var v
  | .func f _ => isEmptyElim f

variable {A : Type} [L.Structure A]

@[simp]
theorem realize_relVar (v : β → A) (t : L.Term β) : t.realize v = v (relVar t) := by
  cases t with
  | var w => rfl
  | func f _ => exact isEmptyElim f

@[simp]
theorem realize_relTerm [L'.Structure A] (v : β → A) (t : L.Term β) :
    (relTerm (L' := L') t).realize v = t.realize v := by
  cases t with
  | var w => rfl
  | func f _ => exact isEmptyElim f

end RelTerm

namespace HeadProgram

variable {L : Language.{0, 0}} [L.IsRelational] {K : ℕ} {α : Type}

/-! ### The quantifier budget of an arithmetic formula -/

/-- **How many heads an arithmetic evaluation needs**: two per nested quantifier,
exactly as for `DescriptiveComplexity.HeadProgram.qdepth`, the arithmetic atoms
needing none of their own (they have their scratch heads at the top). -/
def qdepthA : ∀ {n : ℕ}, (L.sum Language.arith).BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ₁ φ₂ => max (qdepthA φ₁) (qdepthA φ₂)
  | _, .all φ => qdepthA φ + 2

/-! ### The layout of the arithmetic scratch heads -/

/-- The seven heads the arithmetic fragments need, pinned to the seven positions
from `S` on: a multiplication's four working heads, then an addition's three
scratch heads. `S` is the top of the quantifier region, so every level the
evaluator reaches is at most `S`. -/
structure ArithScratch (acc cnt cand tmk a b mk : Fin K) (S : ℕ) : Prop where
  /-- The accumulator sits at `S`. -/
  hacc : (acc : ℕ) = S
  /-- The round counter sits at `S + 1`. -/
  hcnt : (cnt : ℕ) = S + 1
  /-- The scan's candidate sits at `S + 2`. -/
  hcand : (cand : ℕ) = S + 2
  /-- The scan's marker sits at `S + 3`. -/
  htmk : (tmk : ℕ) = S + 3
  /-- The addition's running head sits at `S + 4`. -/
  ha : (a : ℕ) = S + 4
  /-- The addition's counter sits at `S + 5`. -/
  hb : (b : ℕ) = S + 5
  /-- The addition's marker sits at `S + 6`. -/
  hmk : (mk : ℕ) = S + 6

namespace ArithScratch

variable {acc cnt cand tmk a b mk : Fin K} {S d : ℕ}

/-- The layout gives an addition the head discipline it asks for, at any level
the evaluator can reach. -/
theorem plusHeads (hs : ArithScratch acc cnt cand tmk a b mk S) {i j k : Fin K}
    (hi : (i : ℕ) < d) (hj : (j : ℕ) < d) (hk : (k : ℕ) < d) (hd : d ≤ S) :
    PlusHeads i j k a b mk d where
  hi := hi
  hj := hj
  hk := hk
  ha := by have := hs.ha; omega
  hb := by have := hs.hb; omega
  hmk := by have := hs.hmk; omega
  hab := fun he => by
    have h1 := hs.ha
    have h2 := hs.hb
    rw [he] at h1
    omega
  hamk := fun he => by
    have h1 := hs.ha
    have h2 := hs.hmk
    rw [he] at h1
    omega
  hbmk := fun he => by
    have h1 := hs.hb
    have h2 := hs.hmk
    rw [he] at h1
    omega

/-- The layout gives a multiplication the three-level head discipline it asks
for, the middle level being the top of its four working heads. -/
theorem timesHeads (hs : ArithScratch acc cnt cand tmk a b mk S) {i j k : Fin K}
    (hi : (i : ℕ) < d) (hj : (j : ℕ) < d) (hk : (k : ℕ) < d) (hd : d ≤ S) :
    TimesHeads i j k acc cnt cand tmk a b mk d (S + 4) where
  hi := hi
  hj := hj
  hk := hk
  hacc := by have := hs.hacc; omega
  hcnt := by have := hs.hcnt; omega
  hcand := by have := hs.hcand; omega
  htmk := by have := hs.htmk; omega
  hplus :=
    { hi := by have := hs.hacc; omega
      hj := by omega
      hk := by have := hs.hcand; omega
      ha := by have := hs.ha; omega
      hb := by have := hs.hb; omega
      hmk := by have := hs.hmk; omega
      hab := fun he => by
        have h1 := hs.ha
        have h2 := hs.hb
        rw [he] at h1
        omega
      hamk := fun he => by
        have h1 := hs.ha
        have h2 := hs.hmk
        rw [he] at h1
        omega
      hbmk := fun he => by
        have h1 := hs.hb
        have h2 := hs.hmk
        rw [he] at h1
        omega }
  hac := fun he => by
    have h1 := hs.hacc
    have h2 := hs.hcnt
    rw [he] at h1
    omega
  haca := fun he => by
    have h1 := hs.hacc
    have h2 := hs.hcand
    rw [he] at h1
    omega
  hacm := fun he => by
    have h1 := hs.hacc
    have h2 := hs.htmk
    rw [he] at h1
    omega
  hcc := fun he => by
    have h1 := hs.hcnt
    have h2 := hs.hcand
    rw [he] at h1
    omega
  hcm := fun he => by
    have h1 := hs.hcnt
    have h2 := hs.htmk
    rw [he] at h1
    omega
  hcam := fun he => by
    have h1 := hs.hcand
    have h2 := hs.htmk
    rw [he] at h1
    omega

end ArithScratch

/-! ### The atoms -/

/-- **An arithmetic atom, as a program**: the input vocabulary and `≤` are read
as guards, `plus` and `times` are *computed* by the deciders of
`DescriptiveComplexity.HeadArith`. -/
noncomputable def arithAtomP (acc cnt cand tmk a b mk : Fin K) {n l : ℕ}
    (hv : α ⊕ Fin l → Fin K) :
    ∀ (_R : (L.sum Language.arith).Relations n),
      (Fin n → (L.sum Language.arith).Term (α ⊕ Fin l)) → HeadProgram L K
  | Sum.inl r, ts =>
      leafP (atomGuard hv (BoundedFormula.rel (Sum.inl r) fun i => relTerm (ts i)))
        (isQF_atomGuard hv (BoundedFormula.IsAtomic.rel _ _).isQF)
  | Sum.inr .le, ts =>
      leafP (atomGuard hv (BoundedFormula.rel (Sum.inr .le) fun i => relTerm (ts i)))
        (isQF_atomGuard hv (BoundedFormula.IsAtomic.rel _ _).isQF)
  | Sum.inr .plus, ts =>
      plusP (hv (relVar (ts 0))) (hv (relVar (ts 1))) (hv (relVar (ts 2))) a b mk
  | Sum.inr .times, ts =>
      timesP (hv (relVar (ts 0))) (hv (relVar (ts 1))) (hv (relVar (ts 2)))
        acc cnt cand tmk a b mk

/-! ### The evaluator -/

/-- **The evaluator of an arithmetic formula**: `evalP` with the arithmetic atoms
computed instead of read. -/
noncomputable def evalArithP (sh : ℕ → Fin K) (acc cnt cand tmk a b mk : Fin K) :
    ∀ {n : ℕ}, ℕ → (α ⊕ Fin n → Fin K) → (L.sum Language.arith).BoundedFormula α n →
      HeadProgram L K
  | _, _, _, .falsum => exitP false
  | _, _, hv, .equal t₁ t₂ =>
      leafP (atomGuard hv (BoundedFormula.equal (relTerm t₁) (relTerm t₂)))
        (isQF_atomGuard hv (BoundedFormula.IsAtomic.equal _ _).isQF)
  | _, _, hv, .rel R ts => arithAtomP acc cnt cand tmk a b mk hv R ts
  | _, d, hv, .imp φ₁ φ₂ =>
      iteP (evalArithP sh acc cnt cand tmk a b mk d hv φ₁)
        (evalArithP sh acc cnt cand tmk a b mk d hv φ₂) (exitP true)
  | _, d, hv, .all φ => scanP (sh d) (sh (d + 1))
      (evalArithP sh acc cnt cand tmk a b mk (d + 2)
        (Sum.elim (fun a => hv (Sum.inl a)) (Fin.snoc (fun i => hv (Sum.inr i)) (sh d))) φ)

/-! ### Correctness -/

section Eval

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {acc cnt cand tmk a b mk : Fin K} {S : ℕ}

omit [Finite A] [L.IsRelational] in
/-- What an arithmetic formula says of the heads depends only on the heads its
variables live in – the arithmetic twin of
`DescriptiveComplexity.HeadProgram.headLocal_realize`. -/
theorem headLocalA_realize {n d : ℕ} (hv : α ⊕ Fin n → Fin K)
    (ψ : (L.sum Language.arith).BoundedFormula α n) (hlow : ∀ v, (hv v : ℕ) < d) :
    HeadLocal d fun x : Fin K → A =>
      ψ.Realize (fun v => x (hv (Sum.inl v))) (fun i => x (hv (Sum.inr i))) := by
  intro x y hxy
  have h1 : (fun v => x (hv (Sum.inl v))) = fun v => y (hv (Sum.inl v)) :=
    funext fun v => hxy _ (hlow _)
  have h2 : (fun i => x (hv (Sum.inr i))) = fun i => y (hv (Sum.inr i)) :=
    funext fun i => hxy _ (hlow _)
  change ψ.Realize (fun v => x (hv (Sum.inl v))) (fun i => x (hv (Sum.inr i))) ↔
    ψ.Realize (fun v => y (hv (Sum.inl v))) (fun i => y (hv (Sum.inr i)))
  rw [h1, h2]

/-- **An arithmetic atom is decided**: read as a guard where it is an input
relation or the order, computed by a fragment where it is `plus` or `times`. -/
theorem decides_arithAtomP (hs : ArithScratch acc cnt cand tmk a b mk S) (hSK : S + 7 ≤ K)
    {n l d : ℕ} (hv : α ⊕ Fin l → Fin K) (hlow : ∀ v, (hv v : ℕ) < d) (hd : d ≤ S)
    (R : (L.sum Language.arith).Relations n)
    (ts : Fin n → (L.sum Language.arith).Term (α ⊕ Fin l)) :
    (arithAtomP acc cnt cand tmk a b mk hv R ts).Decides A d fun x =>
      (BoundedFormula.rel R ts).Realize (fun v => x (hv (Sum.inl v)))
        (fun i => x (hv (Sum.inr i))) := by
  rcases R with r | ar
  · refine (decides_leafP (atomGuard hv (BoundedFormula.rel (Sum.inl r) fun i => relTerm (ts i)))
      (isQF_atomGuard hv (BoundedFormula.IsAtomic.rel _ _).isQF)).congr fun x => ?_
    rw [realize_atomGuard hv _ x]
    change RelMap r (fun i => (relTerm (L' := L.sum Language.order) (ts i)).realize
        (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i)))) ↔
      RelMap r (fun i => (ts i).realize
        (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))))
    exact Iff.of_eq (congrArg (RelMap r) (funext fun i => realize_relTerm _ _))
  cases ar with
  | le =>
    refine (decides_leafP
      (atomGuard hv (BoundedFormula.rel (Sum.inr .le) fun i => relTerm (ts i)))
      (isQF_atomGuard hv (BoundedFormula.IsAtomic.rel _ _).isQF)).congr fun x => ?_
    rw [realize_atomGuard hv _ x]
    change (relTerm (L' := L.sum Language.order) (ts 0)).realize
          (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))) ≤
        (relTerm (L' := L.sum Language.order) (ts 1)).realize
          (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))) ↔
      (ts 0).realize (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))) ≤
        (ts 1).realize (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i)))
    rw [realize_relTerm, realize_relTerm]
  | plus =>
    refine (decides_plusP (hs.plusHeads (hlow _) (hlow _) (hlow _) hd) (by omega)).congr
      fun x => ?_
    change orank (x (hv (relVar (ts 0)))) + orank (x (hv (relVar (ts 1))))
        = orank (x (hv (relVar (ts 2)))) ↔
      orank ((ts 0).realize (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))))
          + orank ((ts 1).realize
            (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))))
        = orank ((ts 2).realize
            (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))))
    have helim : ∀ w : α ⊕ Fin l,
        Sum.elim (fun v => x (hv (Sum.inl v))) (fun i => x (hv (Sum.inr i))) w = x (hv w) := by
      rintro (v | i) <;> rfl
    simp only [realize_relVar, helim]
  | times =>
    refine (decides_timesP (hs.timesHeads (hlow _) (hlow _) (hlow _) hd) (by omega)).congr
      fun x => ?_
    change orank (x (hv (relVar (ts 0)))) * orank (x (hv (relVar (ts 1))))
        = orank (x (hv (relVar (ts 2)))) ↔
      orank ((ts 0).realize (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))))
          * orank ((ts 1).realize
            (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))))
        = orank ((ts 2).realize
            (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))))
    have helim : ∀ w : α ⊕ Fin l,
        Sum.elim (fun v => x (hv (Sum.inl v))) (fun i => x (hv (Sum.inr i))) w = x (hv w) := by
      rintro (v | i) <;> rfl
    simp only [realize_relVar, helim]

/-- **The arithmetic evaluator is correct**: it decides the formula, reading its
variables off the heads they live in, and gives those heads back untouched. -/
theorem decides_evalArithP (sh : ℕ → Fin K) (hsh : ∀ i : ℕ, i < K → (sh i : ℕ) = i)
    (hs : ArithScratch acc cnt cand tmk a b mk S) (hSK : S + 7 ≤ K) :
    ∀ {n : ℕ} (ψ : (L.sum Language.arith).BoundedFormula α n) (d : ℕ)
      (hv : α ⊕ Fin n → Fin K), (∀ v, (hv v : ℕ) < d) → d + qdepthA ψ ≤ S →
      (evalArithP sh acc cnt cand tmk a b mk d hv ψ).Decides A d fun x =>
        ψ.Realize (fun v => x (hv (Sum.inl v))) (fun i => x (hv (Sum.inr i))) := by
  intro n ψ
  induction ψ with
  | falsum =>
    intro d hv _ _
    exact (decides_exitP_false d).congr fun _ => Iff.rfl
  | equal t₁ t₂ =>
    intro d hv _ _
    refine (decides_leafP (atomGuard hv (BoundedFormula.equal (relTerm t₁) (relTerm t₂)))
      (isQF_atomGuard hv (BoundedFormula.IsAtomic.equal _ _).isQF)).congr fun x => ?_
    rw [realize_atomGuard hv _ x]
    change (relTerm (L' := L.sum Language.order) t₁).realize
          (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))) =
        (relTerm (L' := L.sum Language.order) t₂).realize
          (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))) ↔
      t₁.realize (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))) =
        t₂.realize (Sum.elim (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i)))
    rw [realize_relTerm, realize_relTerm]
  | rel R ts =>
    intro d hv hlow hK
    refine decides_arithAtomP hs hSK hv hlow ?_ R ts
    have h0 : qdepthA (L := L) (α := α) (BoundedFormula.rel R ts) = 0 := rfl
    rw [h0] at hK
    omega
  | imp φ₁ φ₂ ih₁ ih₂ =>
    intro d hv hlow hK
    have hKm : d + max (qdepthA φ₁) (qdepthA φ₂) ≤ S := hK
    have hK₁ : d + qdepthA φ₁ ≤ S := le_trans (Nat.add_le_add_left (le_max_left _ _) d) hKm
    have hK₂ : d + qdepthA φ₂ ≤ S := le_trans (Nat.add_le_add_left (le_max_right _ _) d) hKm
    refine (decides_iteP (ih₁ d hv hlow hK₁) (ih₂ d hv hlow hK₂) (decides_exitP_true d)
      (headLocalA_realize hv φ₁ hlow) (headLocalA_realize hv φ₂ hlow)
      (fun _ _ _ => Iff.rfl)).congr fun x => ?_
    rw [BoundedFormula.realize_imp]
    exact ⟨fun hor hp => by
        rcases hor with ⟨-, hq⟩ | ⟨hnp, -⟩
        · exact hq
        · exact absurd hp hnp,
      fun himp => by
        by_cases hp : φ₁.Realize (fun v => x (hv (Sum.inl v))) fun i => x (hv (Sum.inr i))
        · exact Or.inl ⟨hp, himp hp⟩
        · exact Or.inr ⟨hp, trivial⟩⟩
  | @all n φ ih =>
    intro d hv hlow hK
    have hqd : d + (qdepthA φ + 2) ≤ S := hK
    have hdK : d < K := by omega
    have hd1K : d + 1 < K := by omega
    have hh : ((sh d : Fin K) : ℕ) = d := hsh d hdK
    have hhm : ((sh (d + 1) : Fin K) : ℕ) = d + 1 := hsh (d + 1) hd1K
    set hv' : α ⊕ Fin (n + 1) → Fin K :=
      Sum.elim (fun v => hv (Sum.inl v)) (Fin.snoc (fun i => hv (Sum.inr i)) (sh d)) with hv'def
    have hbvlast : (Fin.snoc (fun i => hv (Sum.inr i)) (sh d) : Fin (n + 1) → Fin K)
        (Fin.last n) = sh d := Fin.snoc_last ..
    have hbvcast : ∀ j : Fin n, (Fin.snoc (fun i => hv (Sum.inr i)) (sh d) : Fin (n + 1) → Fin K)
        j.castSucc = hv (Sum.inr j) := fun j => Fin.snoc_castSucc ..
    have hlow' : ∀ v, (hv' v : ℕ) < d + 1 := by
      rintro (v | i)
      · exact lt_trans (hlow _) (by omega)
      · refine Fin.lastCases ?_ ?_ i
        · have hx : (hv' (Sum.inr (Fin.last n)) : Fin K) = sh d := hbvlast
          rw [hx, hh]
          omega
        · intro j
          have hx : (hv' (Sum.inr j.castSucc) : Fin K) = hv (Sum.inr j) := hbvcast j
          rw [hx]
          exact lt_trans (hlow _) (by omega)
    have hbody := ih (d + 2) hv' (fun v => lt_trans (hlow' v) (by omega)) (by omega)
    refine (decides_scanP hh hhm hbody (headLocalA_realize hv' φ hlow')).congr fun x => ?_
    rw [BoundedFormula.realize_all]
    refine forall_congr' fun e => ?_
    have hnesh : ∀ v : α ⊕ Fin n, hv v ≠ sh d := by
      intro v he
      have hx := hlow v
      rw [he, hh] at hx
      omega
    have hfree : ∀ w : α, Function.update x (sh d) e (hv' (Sum.inl w)) = x (hv (Sum.inl w)) := by
      intro w
      have hx : (hv' (Sum.inl w) : Fin K) = hv (Sum.inl w) := rfl
      rw [hx]
      exact Function.update_of_ne (hnesh _) _ _
    have hbound : ∀ i : Fin (n + 1), Function.update x (sh d) e (hv' (Sum.inr i)) =
        (Fin.snoc (fun i => x (hv (Sum.inr i))) e : Fin (n + 1) → A) i := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · have hx : (hv' (Sum.inr (Fin.last n)) : Fin K) = sh d := hbvlast
        rw [hx, Function.update_self, Fin.snoc_last]
      · intro j
        have hx : (hv' (Sum.inr j.castSucc) : Fin K) = hv (Sum.inr j) := hbvcast j
        rw [hx, Function.update_of_ne (hnesh _) _ _, Fin.snoc_castSucc]
    rw [funext hfree, funext hbound]

omit [Finite A] in
/-- **The arithmetic evaluator is deterministic**: it sweeps and it computes, it
does not guess – the two arithmetic fragments being deterministic too. -/
theorem deterministic_evalArithP (sh : ℕ → Fin K) :
    ∀ {n : ℕ} (ψ : (L.sum Language.arith).BoundedFormula α n) (d : ℕ)
      (hv : α ⊕ Fin n → Fin K),
      (evalArithP sh acc cnt cand tmk a b mk d hv ψ).Deterministic A := by
  intro n ψ
  induction ψ with
  | falsum => exact fun d hv => deterministic_exitP false
  | equal t₁ t₂ =>
    exact fun d hv => deterministic_leafP (atomGuard hv
      (BoundedFormula.equal (relTerm t₁) (relTerm t₂)))
      (isQF_atomGuard hv (BoundedFormula.IsAtomic.equal _ _).isQF)
  | rel R ts =>
    intro d hv
    rcases R with r | ar
    · exact deterministic_leafP (atomGuard hv
        (BoundedFormula.rel (Sum.inl r) fun i => relTerm (ts i)))
        (isQF_atomGuard hv (BoundedFormula.IsAtomic.rel _ _).isQF)
    cases ar with
    | le =>
      exact deterministic_leafP (atomGuard hv
        (BoundedFormula.rel (Sum.inr .le) fun i => relTerm (ts i)))
        (isQF_atomGuard hv (BoundedFormula.IsAtomic.rel _ _).isQF)
    | plus => exact deterministic_plusP _ _ _ _ _ _
    | times => exact deterministic_timesP _ _ _ _ _ _ _ _ _ _
  | imp φ₁ φ₂ ih₁ ih₂ =>
    exact fun d hv => deterministic_iteP (ih₁ d hv) (ih₂ d hv) (deterministic_exitP true)
  | @all n φ ih => exact fun d hv => deterministic_scanP (ih (d + 2) _)

end Eval

end HeadProgram

/-! ### AC⁰ ⊆ LOGSPACE -/

section Inclusion

open HeadProgram

variable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}

/-- **AC⁰ ⊆ FO(DTC)**: the sentence is evaluated by a deterministic multi-head
automaton – the quantifiers swept, the input atoms and the order read as guards,
and the two numeric atoms *computed* by
`DescriptiveComplexity.HeadProgram.plusP` and
`DescriptiveComplexity.HeadProgram.timesP`.

The machine has `qdepthA φ + 7` heads: two per nested quantifier, then the four
working heads of a multiplication and the three scratch heads of an addition. -/
theorem AC0Definable.dtcDefinable (h : AC0Definable P) : DTCDefinable P := by
  classical
  obtain ⟨φ, hφ⟩ := h
  set S := qdepthA (L := L) (α := Empty) φ with hS
  set K := S + 7 with hK
  set sh : ℕ → Fin K := fun i => if hi : i < K then ⟨i, hi⟩ else ⟨0, by omega⟩ with hsh0
  have hsh : ∀ i : ℕ, i < K → (sh i : ℕ) = i := by
    intro i hi
    rw [hsh0]
    simp only [dif_pos hi]
  set acc : Fin K := ⟨S, by omega⟩ with hacc
  set cnt : Fin K := ⟨S + 1, by omega⟩ with hcnt
  set cand : Fin K := ⟨S + 2, by omega⟩ with hcand
  set tmk : Fin K := ⟨S + 3, by omega⟩ with htmk
  set a : Fin K := ⟨S + 4, by omega⟩ with ha
  set b : Fin K := ⟨S + 5, by omega⟩ with hb
  set mk : Fin K := ⟨S + 6, by omega⟩ with hmk
  have hs : ArithScratch acc cnt cand tmk a b mk S :=
    { hacc := rfl, hcnt := rfl, hcand := rfl, htmk := rfl, ha := rfl, hb := rfl, hmk := rfl }
  set hv : Empty ⊕ Fin 0 → Fin K := fun v => v.elim (fun e => e.elim) Fin.elim0 with hvdef
  have hlow : ∀ v, ((hv v : Fin K) : ℕ) < 0 := fun v => v.elim (fun e => e.elim) Fin.elim0
  refine dtcDefinable_iff_automaton.mpr
    ⟨K, (evalArithP sh acc cnt cand tmk a b mk 0 hv φ).compile true,
      isDeterministic_compile_true _, ?_⟩
  intro A _ _ _ _
  have hdec := decides_evalArithP (A := A) sh hsh hs (by omega) φ 0 hv hlow (by omega)
  have hpred : ∀ x : Fin K → A,
      BoundedFormula.Realize φ (fun v => x (hv (Sum.inl v)))
        (fun i => x (hv (Sum.inr i))) ↔ A ⊨ φ := by
    intro x
    have h1 : (fun v => x (hv (Sum.inl v))) = (default : Empty → A) := funext fun e => e.elim
    have h2 : (fun i => x (hv (Sum.inr i))) = (default : Fin 0 → A) := funext fun i => i.elim0
    rw [h1, h2]
    exact Iff.rfl
  rw [hφ A, accepts_compile_true _ (deterministic_evalArithP sh φ 0 hv)]
  constructor
  · -- the sentence holds, so the evaluation reaches the accepting exit
    intro hsat
    obtain ⟨m0, hm0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    obtain ⟨y, -, hreach⟩ := hdec.complete (x := fun _ => m0) (b := true) (y := fun _ => m0)
      ⟨⟨fun _ => (hpred (fun _ => m0)).mpr hsat, fun _ => rfl⟩, fun j hj => by omega⟩
    exact ⟨fun _ => m0, y, fun j e => isMin_of_orank_eq_zero hm0 e, hreach⟩
  · -- an accepting run means the evaluation answered `true`
    rintro ⟨x, y, -, hreach⟩
    exact (hpred x).mp (by simpa using (hdec.sound hreach).1)

/-- **AC⁰ ⊆ LOGSPACE.** The bottom of the ladder, pinned: with
`DescriptiveComplexity.FODefinable.ac0Definable` and
`DescriptiveComplexity.exists_ac0Definable_not_foDefinable` on one side and
`DescriptiveComplexity.LOGSPACE_subset_NL` on the other,

`FO(≤) ⊊ AC⁰ ⊆ LOGSPACE ⊆ NL ⊆ PTIME`,

with the first inclusion strict and the strictness of the second exactly the
switching lemma – `DescriptiveComplexity.PARITY` is in LOGSPACE here and outside
AC⁰ classically, which this library does not prove. -/
theorem ac0Definable_mem_LOGSPACE (h : AC0Definable P) : P ∈ LOGSPACE :=
  (mem_LOGSPACE_iff P).mpr h.dtcDefinable

/-- **AC⁰ ⊆ NL**, by the inclusion of LOGSPACE. -/
theorem ac0Definable_mem_NL (h : AC0Definable P) : P ∈ NL :=
  LOGSPACE_subset_NL (ac0Definable_mem_LOGSPACE h)

end Inclusion

end DescriptiveComplexity
