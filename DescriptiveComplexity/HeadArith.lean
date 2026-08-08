/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadEval
import DescriptiveComplexity.Arithmetic

/-!
# Arithmetic with heads: addition of ranks

A head holds an element of the universe, that is – through
`DescriptiveComplexity.orank` – a number below `Nat.card A`. This file teaches a
`DescriptiveComplexity.HeadProgram` to *add* two of them, which is the first of
the fragments the inclusion `AC⁰ ⊆ LOGSPACE` needs: the numeric predicates of
`DescriptiveComplexity.Language.arith` have to be decided by a machine whose
guards are quantifier-free, and “these two heads are equal” is all such a guard
can say.

## The walk

`DescriptiveComplexity.HeadProgram.plusP i j k a b mk` decides
`orank (x i) + orank (x j) = orank (x k)` with two scratch heads `a`, `b` and a
marker head `mk`. It is a five-node control graph
(`DescriptiveComplexity.HeadProgram.PlusNode`), every node a `leafP` or a
`moveP`:

| node | fragment | `true` → | `false` → |
| --- | --- | --- | --- |
| `init` | `a := copy i`, `b := toMin` | `test` | `test` |
| `test` | `b = j`? | `check` | `over` |
| `check` | `a = k`? | exit `true` | exit `false` |
| `over` | `a = mk`? | exit `false` | `step` |
| `step` | `a := succ a`, `b := succ b` | `test` | `test` |

so `a` runs up from `x i` while `b` counts up from the least element, and the
answer is read off when `b` arrives at `x j`. The invariant is
`DescriptiveComplexity.HeadProgram.PlusBase`: `orank (x i) + orank (z b) =
orank (z a)`, the counter is still below `orank (x j)`, and the marker has not
been passed.

## Why the marker, and why the specification is not the clean statement

“This head is at the greatest element” is not a quantifier-free fact of one
head, while “these two heads are equal” is, so the overflow test compares `a`
with a head parked at the maximum – the `dmk` idiom of
`DescriptiveComplexity.HeadCaptureDet`. Overflow must **exit `false`** rather
than die: a disabled `succ` transition is sound but not complete.

Accordingly `DescriptiveComplexity.HeadProgram.plusRel` is stated by the
*marker's value*, exactly as `DescriptiveComplexity.HeadProgram.lexRel` is, and
it has two disjuncts because the walk has three regimes:

* the marker is reached strictly before the counter arrives – equivalently
  `orank (x i) ≤ orank (x mk) < orank (x i) + orank (x j)` – and the answer is
  `false`;
* it is not, and the sum fits in the universe: the answer is the truth of
  `orank (x i) + orank (x j) = orank (x k)`;
* it is not and the sum does *not* fit: `succ` is disabled, the run has **no
  exit at all**, and the specification claims none.

Where the caller has parked `mk` at the greatest element only the second regime
survives, and `DescriptiveComplexity.HeadProgram.decides_plusP` is the clean
statement one wants.

## Where the levels go

The control walk is assembled at protection level `K` – every head protected –
because a fragment relation that mentions the scratch heads is *not* local at
the caller's level, and `DescriptiveComplexity.HeadProgram.runs_wireP` needs
locality. At level `K` locality is free
(`DescriptiveComplexity.HeadProgram.headLocal2_top`), and the result is weakened
to the caller's level afterwards, which is where the scratch heads are forgotten.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {K : ℕ}

namespace HeadProgram

/-! ### Locality is free at the top -/

section Top

variable {A : Type}

/-- **Every relation is local at level `K`**: there is no head beyond the last
one to differ in. This is what lets a control walk over fragments that use
scratch heads be assembled without any locality proof, the protection level
being lowered only afterwards. -/
theorem headLocal2_top (R : (Fin K → A) → Bool → (Fin K → A) → Prop) :
    HeadLocal2 K R := by
  intro x x' y y' hx hy b
  have hxx : x = x' := funext fun p => hx p p.isLt
  have hyy : y = y' := funext fun p => hy p p.isLt
  rw [hxx, hyy]

end Top

/-! ### The control graph of an addition -/

/-- The control nodes of an addition: initialize the two scratch heads, test
whether the counter has arrived, read the answer off, test for overflow, step. -/
inductive PlusNode
  /-- Copy the first summand onto `a` and send the counter `b` to the least
  element. -/
  | init : PlusNode
  /-- Has the counter reached the second summand? -/
  | test : PlusNode
  /-- It has: is `a` the claimed sum? -/
  | check : PlusNode
  /-- It has not: is `a` at the marker, i.e. would the next step overflow? -/
  | over : PlusNode
  /-- Step both scratch heads. -/
  | step : PlusNode
  deriving DecidableEq

instance : Finite PlusNode := by
  refine Finite.of_injective (fun c : PlusNode => match c with
      | .init => (0 : Fin 5)
      | .test => 1
      | .check => 2
      | .over => 3
      | .step => 4) ?_
  rintro (_ | _ | _ | _ | _) (_ | _ | _ | _ | _) h <;> simp_all

/-- The wiring of an addition: the loop `test → over → step → test`, with the
two answers hanging off `check` and the overflow answer off `over`. -/
def plusWire : PlusNode → Bool → PlusNode ⊕ Bool
  | .init, _ => Sum.inl .test
  | .test, b => if b then Sum.inl .check else Sum.inl .over
  | .check, b => Sum.inr b
  | .over, b => if b then Sum.inr false else Sum.inl .step
  | .step, _ => Sum.inl .test

open Classical in
/-- The moves of the initialization: the running head copies the first summand,
the counter goes to the least element. -/
noncomputable def plusInitMoves (i a b : Fin K) : Fin K → HeadMove K :=
  fun h => if h = a then .copy i else if h = b then .toMin else .stay

open Classical in
/-- The moves of one step: both scratch heads advance. -/
noncomputable def plusStepMoves (a b : Fin K) : Fin K → HeadMove K :=
  fun h => if h = a then .succ a else if h = b then .succ b else .stay

/-- The fragments of an addition. -/
noncomputable def plusFam (i j k a b mk : Fin K) : PlusNode → HeadProgram L K
  | .init => moveP (plusInitMoves i a b)
  | .test => leafP (HeadMove.eqVarF L b j) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .check => leafP (HeadMove.eqVarF L a k) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .over => leafP (HeadMove.eqVarF L a mk) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .step => moveP (plusStepMoves a b)

/-- **Addition**: decide `orank (x i) + orank (x j) = orank (x k)`, using the
scratch heads `a`, `b` and a marker `mk`. -/
noncomputable def plusP (i j k a b mk : Fin K) : HeadProgram L K :=
  wireP (plusFam (L := L) i j k a b mk) plusWire .init

/-! ### What the fragments run -/

section Fam

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The relations the fragments of an addition run, at the top protection
level. -/
noncomputable def plusFamRel (i j k a b mk : Fin K) :
    PlusNode → (Fin K → A) → Bool → (Fin K → A) → Prop
  | .init => fun x c y => c = true ∧ ∀ h, (plusInitMoves i a b h).Holds x h (y h)
  | .test => fun x c y => (c = true ↔ x b = x j) ∧ y = x
  | .check => fun x c y => (c = true ↔ x a = x k) ∧ y = x
  | .over => fun x c y => (c = true ↔ x a = x mk) ∧ y = x
  | .step => fun x c y => c = true ∧ ∀ h, (plusStepMoves a b h).Holds x h (y h)

/-- An equality test between two heads, as a fragment at the top protection
level: it answers the equality and moves nothing. -/
theorem runs_eqLeafP (u v : Fin K) :
    (leafP (L := L) (K := K) (HeadMove.eqVarF L u v)
        ((BoundedFormula.IsAtomic.equal _ _).isQF)).Runs A K
      (fun x c y => (c = true ↔ x u = x v) ∧ y = x) := by
  refine (decides_leafP (L := L) (K := K) (HeadMove.eqVarF L u v)
    ((BoundedFormula.IsAtomic.equal _ _).isQF)).mono ?_ ?_ <;> intro x c y h
  · exact ⟨h.1.trans (HeadMove.realize_eqVarF _ _), funext fun p => (h.2 p p.isLt).symm⟩
  · exact ⟨y, HeadAgree.refl y, h.1.trans (HeadMove.realize_eqVarF _ _).symm,
      fun p _ => by rw [h.2]⟩

theorem runs_plusFam (i j k a b mk : Fin K) (c : PlusNode) :
    (plusFam (L := L) i j k a b mk c).Runs A K (plusFamRel i j k a b mk c) := by
  cases c with
  | init => exact runs_moveP _
  | step => exact runs_moveP _
  | test => exact runs_eqLeafP b j
  | check => exact runs_eqLeafP a k
  | over => exact runs_eqLeafP a mk

end Fam

/-! ### The relation an addition runs -/

section Rel

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]

/-- **The marker is reached before the counter arrives**: the condition under
which the walk answers `false` without ever reading `k`. -/
def PlusHits (i j mk : Fin K) (x : Fin K → A) : Prop :=
  orank (x i) ≤ orank (x mk) ∧ orank (x mk) < orank (x i) + orank (x j)

/-- **What an addition runs**, stated by the marker's value rather than by
maximality: either the marker is reached first and the answer is `false`, or it
is not and the sum fits, in which case the answer is the truth of the addition.
The remaining case – the marker is not reached and the sum does not fit – has no
exit, and is claimed by neither disjunct. -/
def plusRel (i j k mk : Fin K) (prot : ℕ) :
    (Fin K → A) → Bool → (Fin K → A) → Prop := fun x c y =>
  HeadAgree prot x y ∧
    ((PlusHits i j mk x ∧ c = false) ∨
      (¬PlusHits i j mk x ∧ orank (x i) + orank (x j) < Nat.card A ∧
        (c = true ↔ orank (x i) + orank (x j) = orank (x k))))

/-- The invariant of the loop, at the nodes inside it: the running head is the
first summand plus the counter, the counter has not passed the second summand,
and the marker has not been passed. -/
def PlusBase (i j a b mk : Fin K) (x z : Fin K → A) : Prop :=
  (∀ p : Fin K, p ≠ a → p ≠ b → z p = x p) ∧
    orank (x i) + orank (z b) = orank (z a) ∧
      orank (z b) ≤ orank (x j) ∧
        ∀ t : ℕ, t < orank (z b) → orank (x i) + t ≠ orank (x mk)

/-- The invariant of the control walk of an addition, node by node. -/
def PlusInv (i j a b mk : Fin K) (x : Fin K → A) : PlusNode → (Fin K → A) → Prop
  | .init => fun z => z = x
  | .test => fun z => PlusBase i j a b mk x z
  | .check => fun z => PlusBase i j a b mk x z ∧ z b = x j
  | .over => fun z => PlusBase i j a b mk x z ∧ z b ≠ x j
  | .step => fun z => PlusBase i j a b mk x z ∧ z b ≠ x j ∧ z a ≠ x mk

end Rel

/-! ### Soundness: the invariant of the control walk -/

section Sound

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {i j k a b mk : Fin K} {prot : ℕ}

/-- The head indices a caller must respect: the four interface heads are
protected, the two scratch heads are not. -/
structure PlusHeads (i j k a b mk : Fin K) (prot : ℕ) : Prop where
  /-- The first summand is protected. -/
  hi : (i : ℕ) < prot
  /-- The second summand is protected. -/
  hj : (j : ℕ) < prot
  /-- The claimed sum is protected. -/
  hk : (k : ℕ) < prot
  /-- The marker is protected. -/
  hmk : (mk : ℕ) < prot
  /-- The running head is scratch. -/
  ha : prot ≤ (a : ℕ)
  /-- The counter is scratch. -/
  hb : prot ≤ (b : ℕ)
  /-- The two scratch heads are distinct: being scratch does not make them so. -/
  hab : a ≠ b

namespace PlusHeads

/-- `i` and `a` are distinct heads, being on opposite sides of the
protection level. -/
theorem ia (h : PlusHeads i j k a b mk prot) : i ≠ a := by
  intro he
  have h1 := h.hi
  have h2 := h.ha
  rw [he] at h1
  omega

/-- `i` and `b` are distinct heads, being on opposite sides of the
protection level. -/
theorem ib (h : PlusHeads i j k a b mk prot) : i ≠ b := by
  intro he
  have h1 := h.hi
  have h2 := h.hb
  rw [he] at h1
  omega

/-- `j` and `a` are distinct heads, being on opposite sides of the
protection level. -/
theorem ja (h : PlusHeads i j k a b mk prot) : j ≠ a := by
  intro he
  have h1 := h.hj
  have h2 := h.ha
  rw [he] at h1
  omega

/-- `j` and `b` are distinct heads, being on opposite sides of the
protection level. -/
theorem jb (h : PlusHeads i j k a b mk prot) : j ≠ b := by
  intro he
  have h1 := h.hj
  have h2 := h.hb
  rw [he] at h1
  omega

/-- `k` and `a` are distinct heads, being on opposite sides of the
protection level. -/
theorem ka (h : PlusHeads i j k a b mk prot) : k ≠ a := by
  intro he
  have h1 := h.hk
  have h2 := h.ha
  rw [he] at h1
  omega

/-- `k` and `b` are distinct heads, being on opposite sides of the
protection level. -/
theorem kb (h : PlusHeads i j k a b mk prot) : k ≠ b := by
  intro he
  have h1 := h.hk
  have h2 := h.hb
  rw [he] at h1
  omega

/-- `mk` and `a` are distinct heads, being on opposite sides of the
protection level. -/
theorem mka (h : PlusHeads i j k a b mk prot) : mk ≠ a := by
  intro he
  have h1 := h.hmk
  have h2 := h.ha
  rw [he] at h1
  omega

/-- `mk` and `b` are distinct heads, being on opposite sides of the
protection level. -/
theorem mkb (h : PlusHeads i j k a b mk prot) : mk ≠ b := by
  intro he
  have h1 := h.hmk
  have h2 := h.hb
  rw [he] at h1
  omega

/-- The two scratch heads are distinct, by fiat. -/
theorem ab (h : PlusHeads i j k a b mk prot) : a ≠ b := h.hab

end PlusHeads

omit [Finite A] in
/-- The moves of the initialization, read off. -/
theorem holds_plusInitMoves {x y : Fin K → A} (hh : PlusHeads i j k a b mk prot)
    (hmv : ∀ h, (plusInitMoves i a b h).Holds x h (y h)) :
    y a = x i ∧ (∀ e : A, y b ≤ e) ∧ ∀ p : Fin K, p ≠ a → p ≠ b → y p = x p := by
  classical
  refine ⟨?_, ?_, fun p hpa hpb => ?_⟩
  · have := hmv a
    rw [plusInitMoves, if_pos rfl] at this
    exact this
  · have := hmv b
    rw [plusInitMoves, if_neg (Ne.symm hh.ab), if_pos rfl] at this
    exact this
  · have := hmv p
    rw [plusInitMoves, if_neg hpa, if_neg hpb] at this
    exact this

omit [Finite A] in
/-- The moves of a step, read off. -/
theorem holds_plusStepMoves {x y : Fin K → A} (hh : PlusHeads i j k a b mk prot)
    (hmv : ∀ h, (plusStepMoves a b h).Holds x h (y h)) :
    x a ⋖ y a ∧ x b ⋖ y b ∧ ∀ p : Fin K, p ≠ a → p ≠ b → y p = x p := by
  classical
  refine ⟨?_, ?_, fun p hpa hpb => ?_⟩
  · have := hmv a
    rw [plusStepMoves, if_pos rfl] at this
    exact ⟨this.1, fun e h1 h2 => this.2 e ⟨h1, h2⟩⟩
  · have := hmv b
    rw [plusStepMoves, if_neg (Ne.symm hh.ab), if_pos rfl] at this
    exact ⟨this.1, fun e h1 h2 => this.2 e ⟨h1, h2⟩⟩
  · have := hmv p
    rw [plusStepMoves, if_neg hpa, if_neg hpb] at this
    exact this

/-- **The invariant holds all along the control walk**: this is the whole
soundness argument, the exits being read off it. -/
theorem plusInv_of_walk (hh : PlusHeads i j k a b mk prot) (x : Fin K → A) :
    ∀ u : PlusNode × (Fin K → A),
      Relation.ReflTransGen (wireStep (plusFamRel (A := A) i j k a b mk) plusWire) (.init, x) u →
        PlusInv i j a b mk x u.1 u.2 := by
  intro u hu
  induction hu with
  | refl => exact rfl
  | @tail v w hv hvw ih =>
    obtain ⟨c, hrel, hwire⟩ := hvw
    cases hnode : v.1 with
    | init =>
      have hvx : v.2 = x := by
        have := ih
        rw [hnode] at this
        exact this
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      rw [hvx] at hmv
      obtain ⟨hya, hyb, hyp⟩ := holds_plusInitMoves hh hmv
      have hw : w.1 = .test := by
        rw [plusWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hb0 : orank (w.2 b) = 0 := orank_eq_zero hyb
      rw [hw]
      refine ⟨hyp, ?_, by rw [hb0]; omega, by rw [hb0]; omega⟩
      rw [hb0, hya]
      omega
    | test =>
      have hbase : PlusBase i j a b mk x v.2 := by
        have := ih
        rw [hnode] at this
        exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hyx⟩ := hrel
      have hjeq : v.2 j = x j := hbase.1 j hh.ja hh.jb
      cases c with
      | true =>
        have hw : w.1 = .check := by
          rw [plusWire, if_pos rfl] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hw, hyx]
        exact ⟨hbase, by rw [hc.mp rfl, hjeq]⟩
      | false =>
        have hw : w.1 = .over := by
          rw [plusWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hw, hyx]
        refine ⟨hbase, fun he => ?_⟩
        rw [← hjeq] at he
        exact absurd (hc.mpr he) (by simp)
    | check =>
      rw [hnode, plusWire] at hwire
      exact absurd hwire (by simp)
    | over =>
      have hov : PlusBase i j a b mk x v.2 ∧ v.2 b ≠ x j := by
        have := ih
        rw [hnode] at this
        exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hyx⟩ := hrel
      cases c with
      | true =>
        rw [plusWire, if_pos rfl] at hwire
        exact absurd hwire (by simp)
      | false =>
        have hw : w.1 = .step := by
          rw [plusWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hw, hyx]
        refine ⟨hov.1, hov.2, fun he => ?_⟩
        rw [← hov.1.1 mk hh.mka hh.mkb] at he
        exact absurd (hc.mpr he) (by simp)
    | step =>
      have hst : PlusBase i j a b mk x v.2 ∧ v.2 b ≠ x j ∧ v.2 a ≠ x mk := by
        have := ih
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hbj, hamk⟩ := hst
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hcova, hcovb, hyp⟩ := holds_plusStepMoves hh hmv
      have hw : w.1 = .test := by
        rw [plusWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hra : orank (w.2 a) = orank (v.2 a) + 1 := orank_covBy hcova
      have hrb : orank (w.2 b) = orank (v.2 b) + 1 := orank_covBy hcovb
      have hblt : orank (v.2 b) < orank (x j) := by
        refine lt_of_le_of_ne hbase.2.2.1 fun he => hbj ?_
        exact orank_inj he
      rw [hw]
      refine ⟨fun p hpa hpb => (hyp p hpa hpb).trans (hbase.1 p hpa hpb), ?_, ?_, ?_⟩
      · rw [hra, hrb, ← hbase.2.1]
        omega
      · rw [hrb]
        omega
      · intro t ht
        rw [hrb] at ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
        · exact hbase.2.2.2 t hlt
        · rw [heq, hbase.2.1]
          intro hcon
          exact hamk (orank_inj hcon)

end Sound

/-! ### Completeness: building the walk -/

section Complete

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {i j k a b mk : Fin K} {prot : ℕ}

/-- **The state after `t` iterations is reachable**, as long as the counter has
not passed the second summand, the running head still fits in the universe, and
the marker has not been passed. -/
theorem exists_walk_test (hh : PlusHeads i j k a b mk prot) (x : Fin K → A) :
    ∀ t : ℕ, t ≤ orank (x j) → orank (x i) + t < Nat.card A →
      (∀ t' : ℕ, t' < t → orank (x i) + t' ≠ orank (x mk)) →
      ∃ z : Fin K → A,
        Relation.ReflTransGen (wireStep (plusFamRel (A := A) i j k a b mk) plusWire)
            (.init, x) (.test, z) ∧
          (∀ p : Fin K, p ≠ a → p ≠ b → z p = x p) ∧
            orank (z a) = orank (x i) + t ∧ orank (z b) = t := by
  classical
  haveI : Nonempty A := ⟨x i⟩
  intro t
  induction t with
  | zero =>
    intro _ _ _
    obtain ⟨m0, hm0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    refine ⟨Function.update (Function.update x a (x i)) b m0, ?_, ?_, ?_, ?_⟩
    · refine Relation.ReflTransGen.single ⟨true, ⟨rfl, fun h => ?_⟩, rfl⟩
      by_cases hha : h = a
      · rw [plusInitMoves, if_pos hha, hha]
        change Function.update (Function.update x a (x i)) b m0 a = x i
        rw [Function.update_of_ne hh.ab, Function.update_self]
      · by_cases hhb : h = b
        · rw [plusInitMoves, if_neg hha, if_pos hhb, hhb]
          change ∀ e : A, Function.update (Function.update x a (x i)) b m0 b ≤ e
          rw [Function.update_self]
          exact fun e => isMin_of_orank_eq_zero hm0 e
        · rw [plusInitMoves, if_neg hha, if_neg hhb]
          change Function.update (Function.update x a (x i)) b m0 h = x h
          rw [Function.update_of_ne hhb, Function.update_of_ne hha]
    · intro p hpa hpb
      rw [Function.update_of_ne hpb, Function.update_of_ne hpa]
    · rw [Function.update_of_ne hh.ab, Function.update_self]
      omega
    · rw [Function.update_self, hm0]
  | succ t ih =>
    intro htj hfit hno
    obtain ⟨z, hwalk, hzp, hza, hzb⟩ := ih (by omega) (by omega) fun t' ht' => hno t' (by omega)
    -- the counter has not arrived, so the test fails
    have hzj : z j = x j := hzp j hh.ja hh.jb
    have hbne : z b ≠ z j := by
      rw [hzj]
      intro he
      rw [← he, hzb] at htj
      omega
    -- the marker has not been reached, so the overflow test fails
    have hzmk : z mk = x mk := hzp mk hh.mka hh.mkb
    have hamk : z a ≠ z mk := by
      rw [hzmk]
      intro he
      exact hno t (by omega) (hza ▸ congrArg orank he)
    -- the two scratch heads step
    obtain ⟨za', hza'⟩ := exists_orank_eq (A := A) (m := orank (x i) + (t + 1)) hfit
    obtain ⟨zb', hzb'⟩ := exists_orank_eq (A := A) (m := t + 1)
      (lt_of_le_of_lt htj (orank_lt_card (x j)))
    set z' := Function.update (Function.update z a za') b zb' with hz'
    have hz'a : z' a = za' := by
      rw [hz', Function.update_of_ne hh.ab, Function.update_self]
    have hz'b : z' b = zb' := by
      rw [hz', Function.update_self]
    have hz'p : ∀ p : Fin K, p ≠ a → p ≠ b → z' p = z p := by
      intro p hpa hpb
      rw [hz', Function.update_of_ne hpb, Function.update_of_ne hpa]
    have s1 : wireStep (plusFamRel (A := A) i j k a b mk) plusWire
        (.test, z) (.over, z) := ⟨false, ⟨by simp [hbne], rfl⟩, rfl⟩
    have s2 : wireStep (plusFamRel (A := A) i j k a b mk) plusWire
        (.over, z) (.step, z) := ⟨false, ⟨by simp [hamk], rfl⟩, rfl⟩
    have s3 : wireStep (plusFamRel (A := A) i j k a b mk) plusWire
        (.step, z) (.test, z') := by
      refine ⟨true, ⟨rfl, fun h => ?_⟩, rfl⟩
      by_cases hha : h = a
      · rw [plusStepMoves, if_pos hha, hha]
        have hcov : z a ⋖ za' := covBy_of_orank_succ (by rw [hza', hza]; omega)
        change z a < z' a ∧ ∀ e : A, ¬(z a < e ∧ e < z' a)
        rw [hz'a]
        exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
      · by_cases hhb : h = b
        · rw [plusStepMoves, if_neg hha, if_pos hhb, hhb]
          have hcov : z b ⋖ zb' := covBy_of_orank_succ (by rw [hzb', hzb])
          change z b < z' b ∧ ∀ e : A, ¬(z b < e ∧ e < z' b)
          rw [hz'b]
          exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
        · rw [plusStepMoves, if_neg hha, if_neg hhb]
          exact hz'p h hha hhb
    refine ⟨z', ((hwalk.tail s1).tail s2).tail s3, ?_, ?_, ?_⟩
    · intro p hpa hpb
      exact (hz'p p hpa hpb).trans (hzp p hpa hpb)
    · rw [hz'a, hza']
    · rw [hz'b, hzb']

/-! ### What an addition runs -/

/-- **The specification of an addition**: soundness from the invariant of the
control walk, completeness from the walk built above. -/
theorem runs_plusP (hh : PlusHeads i j k a b mk prot) (hprotK : prot ≤ K) :
    (plusP (L := L) i j k a b mk).Runs A prot (plusRel i j k mk prot) := by
  refine (((runs_wireP (plusFam (L := L) i j k a b mk) plusWire
    (runs_plusFam (A := A) i j k a b mk) (fun c => headLocal2_top _) .init).weaken
      hprotK).mono ?_ ?_)
  · -- soundness
    rintro x c y ⟨u, hwalk, c', hrel, hwire⟩
    have hinv := plusInv_of_walk hh x u hwalk
    cases hnode : u.1 with
    | init =>
      rw [hnode, plusWire] at hwire
      exact absurd hwire (by simp)
    | step =>
      rw [hnode, plusWire] at hwire
      exact absurd hwire (by simp)
    | test =>
      rw [hnode, plusWire] at hwire
      cases c' <;> simp at hwire
    | check =>
      have hck : PlusBase i j a b mk x u.2 ∧ u.2 b = x j := by
        have := hinv
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hbj⟩ := hck
      rw [hnode] at hrel hwire
      obtain ⟨hc, hyu⟩ := hrel
      rw [plusWire] at hwire
      have hcc : c' = c := Sum.inr.inj hwire
      have hsum : orank (x i) + orank (x j) = orank (u.2 a) := by
        rw [← hbj]
        exact hbase.2.1
      have hnohit : ¬PlusHits i j mk x := by
        rintro ⟨h1, h2⟩
        refine hbase.2.2.2 (orank (x mk) - orank (x i)) (by rw [hbj]; omega) (by omega)
      refine ⟨fun p hp => ?_, Or.inr ⟨hnohit, ?_, ?_⟩⟩
      · rw [hyu]
        exact (hbase.1 p (fun he => by rw [he] at hp; exact absurd hh.ha (by omega))
          (fun he => by rw [he] at hp; exact absurd hh.hb (by omega))).symm
      · rw [hsum]
        exact orank_lt_card _
      · rw [← hcc, hc, ← hbase.1 k hh.ka hh.kb, ← orank_inj_iff (A := A), hsum]
    | over =>
      have hov : PlusBase i j a b mk x u.2 ∧ u.2 b ≠ x j := by
        have := hinv
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hbj⟩ := hov
      rw [hnode] at hrel hwire
      obtain ⟨hc, hyu⟩ := hrel
      cases c' with
      | false =>
        rw [plusWire, if_neg (by simp)] at hwire
        exact absurd hwire (by simp)
      | true =>
        rw [plusWire, if_pos rfl] at hwire
        have hcf : c = false := (Sum.inr.inj hwire).symm
        have hmkeq : orank (u.2 a) = orank (x mk) := by
          rw [hc.mp rfl, hbase.1 mk hh.mka hh.mkb]
        have hblt : orank (u.2 b) < orank (x j) :=
          lt_of_le_of_ne hbase.2.2.1 fun he => hbj (orank_inj he)
        refine ⟨fun p hp => ?_, Or.inl ⟨⟨?_, ?_⟩, hcf⟩⟩
        · rw [hyu]
          exact (hbase.1 p (fun he => by rw [he] at hp; exact absurd hh.ha (by omega))
            (fun he => by rw [he] at hp; exact absurd hh.hb (by omega))).symm
        · rw [← hmkeq, ← hbase.2.1]
          omega
        · rw [← hmkeq, ← hbase.2.1]
          omega
  · -- completeness
    rintro x c y ⟨hag, hcase⟩
    have hxy : ∀ (z : Fin K → A), (∀ p : Fin K, p ≠ a → p ≠ b → z p = x p) →
        HeadAgree prot y z := by
      intro z hzp p hp
      rw [← hag p hp]
      exact (hzp p (fun he => by rw [he] at hp; exact absurd hh.ha (by omega))
        (fun he => by rw [he] at hp; exact absurd hh.hb (by omega))).symm
    rcases hcase with ⟨hhits, hcf⟩ | ⟨hnot, hfits, hc⟩
    · obtain ⟨hh1, hh2⟩ := hhits
      obtain ⟨z, hwalk, hzp, hza, hzb⟩ :=
        exists_walk_test hh x (orank (x mk) - orank (x i)) (by omega)
          (by rw [show orank (x i) + (orank (x mk) - orank (x i)) = orank (x mk) by omega]
              exact orank_lt_card _)
          (fun t' ht' hcon => by omega)
      have hzj : z j = x j := hzp j hh.ja hh.jb
      have hblt : orank (z b) < orank (x j) := by
        rw [hzb]
        omega
      have hbne : z b ≠ z j := by
        rw [hzj]
        intro he
        rw [he] at hblt
        omega
      have hamk : z a = z mk := by
        refine orank_inj ?_
        rw [hza, hzp mk hh.mka hh.mkb]
        omega
      have s1 : wireStep (plusFamRel (A := A) i j k a b mk) plusWire
          (.test, z) (.over, z) := ⟨false, ⟨by simp [hbne], rfl⟩, rfl⟩
      refine ⟨z, hxy z hzp, (.over, z), hwalk.tail s1, true, ⟨by simp [hamk], rfl⟩, ?_⟩
      rw [hcf]
      rfl
    · obtain ⟨z, hwalk, hzp, hza, hzb⟩ := exists_walk_test hh x (orank (x j)) le_rfl hfits
        (fun t' ht' hcon => hnot ⟨by omega, by omega⟩)
      have hzj : z j = x j := hzp j hh.ja hh.jb
      have hbeq : z b = z j := by
        rw [hzj]
        exact orank_inj (by rw [hzb])
      have hkeq : z k = x k := hzp k hh.ka hh.kb
      have s1 : wireStep (plusFamRel (A := A) i j k a b mk) plusWire
          (.test, z) (.check, z) := ⟨true, ⟨by simp [hbeq], rfl⟩, rfl⟩
      refine ⟨z, hxy z hzp, (.check, z), hwalk.tail s1, c, ⟨?_, rfl⟩, rfl⟩
      change c = true ↔ z a = z k
      rw [hc, hkeq, ← orank_inj_iff (A := A), hza]

/-- **What an addition decides where the marker is at the greatest element**: the
addition, on the nose. This is the form a caller uses, having parked the marker
once and for all; the three regimes of
`DescriptiveComplexity.HeadProgram.plusRel` collapse because a sum that does not
fit is not the rank of anything either. -/
theorem plusRel_iff_of_isMax {x y : Fin K → A} {c : Bool}
    (hmax : ∀ e : A, e ≤ x mk) :
    plusRel i j k mk prot x c y ↔
      ((c = true ↔ orank (x i) + orank (x j) = orank (x k)) ∧ HeadAgree prot x y) := by
  have hM : orank (x mk) = Nat.card A - 1 := orank_isTop hmax
  have hik : orank (x i) < Nat.card A := orank_lt_card _
  have hkk : orank (x k) < Nat.card A := orank_lt_card _
  constructor
  · rintro ⟨hagr, hcase⟩
    rcases hcase with ⟨hhits, hcf⟩ | ⟨-, -, hc⟩
    · refine ⟨?_, hagr⟩
      obtain ⟨-, h2⟩ := hhits
      rw [hcf]
      simp only [Bool.false_eq_true, false_iff]
      omega
    · exact ⟨hc, hagr⟩
  · rintro ⟨hc, hagr⟩
    refine ⟨hagr, ?_⟩
    by_cases hfits : orank (x i) + orank (x j) < Nat.card A
    · exact Or.inr ⟨fun hhits => by have := hhits.2; omega, hfits, hc⟩
    · refine Or.inl ⟨⟨by omega, by omega⟩, ?_⟩
      cases c with
      | false => rfl
      | true => exact absurd (hc.mp rfl) (by omega)

omit [Finite A] in
/-- **The addition fragment is deterministic**: every node of the control graph
is, and `DescriptiveComplexity.HeadProgram.wireP` inherits it. This is what makes
the assembled machine a *deterministic* automaton, hence FO(DTC) rather than
merely FO(TC). -/
theorem deterministic_plusP (i j k a b mk : Fin K) :
    (plusP (L := L) i j k a b mk).Deterministic A := by
  refine deterministic_wireP _ _ _ ?_
  rintro (_ | _ | _ | _ | _)
  · exact deterministic_moveP _
  · exact deterministic_leafP (HeadMove.eqVarF L b j)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_leafP (HeadMove.eqVarF L a k)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_leafP (HeadMove.eqVarF L a mk)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_moveP _

end Complete

end HeadProgram

end DescriptiveComplexity
