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
| `init` | `a := copy i`, `b := toMin`, `mk := toMax` | `test` | `test` |
| `test` | `b = j`? | `check` | `over` |
| `check` | `a = k`? | exit `true` | exit `false` |
| `over` | `a = mk`? | exit `false` | `step` |
| `step` | `a := succ a`, `b := succ b` | `test` | `test` |

so `a` runs up from `x i` while `b` counts up from the least element, and the
answer is read off when `b` arrives at `x j`. The invariant is
`DescriptiveComplexity.HeadProgram.PlusBase`: `orank (x i) + orank (z b) =
orank (z a)`, the counter is still below `orank (x j)`, and the marker has not
been passed.

## Why the marker, and why the fragment parks it itself

“This head is at the greatest element” is not a quantifier-free fact of one head,
while “these two heads are equal” is, so the overflow test compares `a` with a
head parked at the maximum – the `dmk` idiom of
`DescriptiveComplexity.HeadCaptureDet`. Overflow must **exit `false`** rather
than die: a disabled `succ` transition is sound but not complete.

The marker is *not* an input the caller has to have parked, as in
`DescriptiveComplexity.HeadProgram.lexNextP`: it is a **third scratch head, sent
to the greatest element by the fragment's own first move** (`HeadMove.toMax`).
That single choice is what makes the specification clean. A caller-supplied
marker can sit anywhere, and the walk then has three regimes – exit `false`
early, answer correctly, or run off the end with no exit at all – so its
specification would have to be stated by the marker's *value*, as `lexRel` is.
Parking it internally collapses all of that: the marker is the maximum, so a sum
that does not fit is detected exactly when it does not fit, and a sum that does
not fit is not the rank of anything either. What the fragment runs is therefore
just `DescriptiveComplexity.HeadProgram.Decides`, with no side condition
(`DescriptiveComplexity.HeadProgram.decides_plusP`).

## Where the levels go

The control walk is assembled at protection level `K` – every head protected –
because a fragment relation that mentions the scratch heads is *not* local at
the caller's level, and `DescriptiveComplexity.HeadProgram.runs_wireP` needs
locality. At level `K` locality is free
(`DescriptiveComplexity.HeadProgram.headLocal2_top`), and the result is weakened
to the caller's level afterwards, which is where the three scratch heads are
forgotten.
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
  /-- It has not: is `a` at the marker, i.e., would the next step overflow? -/
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
the counter goes to the least element, and the marker is parked at the greatest
element – which is what makes the specification of the fragment clean. -/
noncomputable def plusInitMoves (i a b mk : Fin K) : Fin K → HeadMove K :=
  fun h => if h = a then .copy i else if h = b then .toMin else
    if h = mk then .toMax else .stay

open Classical in
/-- The moves of one step: both scratch heads advance. -/
noncomputable def plusStepMoves (a b : Fin K) : Fin K → HeadMove K :=
  fun h => if h = a then .succ a else if h = b then .succ b else .stay

/-- The fragments of an addition. -/
noncomputable def plusFam (i j k a b mk : Fin K) : PlusNode → HeadProgram L K
  | .init => moveP (plusInitMoves i a b mk)
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
  | .init => fun x c y => c = true ∧ ∀ h, (plusInitMoves i a b mk h).Holds x h (y h)
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

/-- The invariant of the loop, at the nodes inside it: the running head is the
first summand plus the counter, the counter has not passed the second summand,
and the marker is parked at the greatest element. Nothing has to be said about
the marker having been passed: a rank below the running head's is below the
maximum. -/
def PlusBase (i j a b mk : Fin K) (x z : Fin K → A) : Prop :=
  (∀ p : Fin K, p ≠ a → p ≠ b → p ≠ mk → z p = x p) ∧
    orank (x i) + orank (z b) = orank (z a) ∧
      orank (z b) ≤ orank (x j) ∧
        ∀ e : A, e ≤ z mk

/-- The invariant of the control walk of an addition, node by node. -/
def PlusInv (i j a b mk : Fin K) (x : Fin K → A) : PlusNode → (Fin K → A) → Prop
  | .init => fun z => z = x
  | .test => fun z => PlusBase i j a b mk x z
  | .check => fun z => PlusBase i j a b mk x z ∧ z b = x j
  | .over => fun z => PlusBase i j a b mk x z ∧ z b ≠ x j
  | .step => fun z => PlusBase i j a b mk x z ∧ z b ≠ x j

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
  /-- The running head is scratch. -/
  ha : prot ≤ (a : ℕ)
  /-- The counter is scratch. -/
  hb : prot ≤ (b : ℕ)
  /-- The marker is scratch too: the fragment parks it itself. -/
  hmk : prot ≤ (mk : ℕ)
  /-- The three scratch heads are distinct: being scratch does not make them
  so. -/
  hab : a ≠ b
  /-- The running head is not the marker. -/
  hamk : a ≠ mk
  /-- The counter is not the marker. -/
  hbmk : b ≠ mk

namespace PlusHeads

/-- `i` and `mk` are distinct heads, being on opposite sides of the
protection level. -/
theorem imk (h : PlusHeads i j k a b mk prot) : i ≠ mk := by
  intro he
  have h1 := h.hi
  have h2 := h.hmk
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

/-- `j` and `mk` are distinct heads, being on opposite sides of the
protection level. -/
theorem jmk (h : PlusHeads i j k a b mk prot) : j ≠ mk := by
  intro he
  have h1 := h.hj
  have h2 := h.hmk
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

/-- `k` and `mk` are distinct heads, being on opposite sides of the
protection level. -/
theorem kmk (h : PlusHeads i j k a b mk prot) : k ≠ mk := by
  intro he
  have h1 := h.hk
  have h2 := h.hmk
  rw [he] at h1
  omega

/-- The two arithmetic scratch heads are distinct, by fiat. -/
theorem ab (h : PlusHeads i j k a b mk prot) : a ≠ b := h.hab

/-- The running head is not the marker, by fiat. -/
theorem amk (h : PlusHeads i j k a b mk prot) : a ≠ mk := h.hamk

/-- The counter is not the marker, by fiat. -/
theorem bmk (h : PlusHeads i j k a b mk prot) : b ≠ mk := h.hbmk

end PlusHeads

omit [Finite A] in
/-- The moves of the initialization, read off: the running head, the counter, the
marker, and everything else. -/
theorem holds_plusInitMoves {x y : Fin K → A} (hh : PlusHeads i j k a b mk prot)
    (hmv : ∀ h, (plusInitMoves i a b mk h).Holds x h (y h)) :
    y a = x i ∧ (∀ e : A, y b ≤ e) ∧ (∀ e : A, e ≤ y mk) ∧
      ∀ p : Fin K, p ≠ a → p ≠ b → p ≠ mk → y p = x p := by
  classical
  refine ⟨?_, ?_, ?_, fun p hpa hpb hpmk => ?_⟩
  · have := hmv a
    rw [plusInitMoves, if_pos rfl] at this
    exact this
  · have := hmv b
    rw [plusInitMoves, if_neg (Ne.symm hh.ab), if_pos rfl] at this
    exact this
  · have := hmv mk
    rw [plusInitMoves, if_neg (Ne.symm hh.amk), if_neg (Ne.symm hh.bmk), if_pos rfl] at this
    exact this
  · have := hmv p
    rw [plusInitMoves, if_neg hpa, if_neg hpb, if_neg hpmk] at this
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
      obtain ⟨hya, hyb, hymk, hyp⟩ := holds_plusInitMoves hh hmv
      have hw : w.1 = .test := by
        rw [plusWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hb0 : orank (w.2 b) = 0 := orank_eq_zero hyb
      rw [hw]
      refine ⟨hyp, ?_, by rw [hb0]; omega, hymk⟩
      rw [hb0, hya]
      omega
    | test =>
      have hbase : PlusBase i j a b mk x v.2 := by
        have := ih
        rw [hnode] at this
        exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hyx⟩ := hrel
      have hjeq : v.2 j = x j := hbase.1 j hh.ja hh.jb hh.jmk
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
      obtain ⟨-, hyx⟩ := hrel
      cases c with
      | true =>
        rw [plusWire, if_pos rfl] at hwire
        exact absurd hwire (by simp)
      | false =>
        have hw : w.1 = .step := by
          rw [plusWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hw, hyx]
        exact hov
    | step =>
      have hst : PlusBase i j a b mk x v.2 ∧ v.2 b ≠ x j := by
        have := ih
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hbj⟩ := hst
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hcova, hcovb, hyp⟩ := holds_plusStepMoves hh hmv
      have hw : w.1 = .test := by
        rw [plusWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hra : orank (w.2 a) = orank (v.2 a) + 1 := orank_covBy hcova
      have hrb : orank (w.2 b) = orank (v.2 b) + 1 := orank_covBy hcovb
      have hblt : orank (v.2 b) < orank (x j) :=
        lt_of_le_of_ne hbase.2.2.1 fun he => hbj (orank_inj he)
      rw [hw]
      refine ⟨fun p hpa hpb hpmk => (hyp p hpa hpb).trans (hbase.1 p hpa hpb hpmk), ?_, ?_, ?_⟩
      · rw [hra, hrb, ← hbase.2.1]
        omega
      · rw [hrb]
        omega
      · intro e
        rw [hyp mk (Ne.symm hh.amk) (Ne.symm hh.bmk)]
        exact hbase.2.2.2 e

end Sound

/-! ### Completeness: building the walk -/

section Complete

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {i j k a b mk : Fin K} {prot : ℕ}

/-- **The state after `t` iterations is reachable**, as long as the counter has
not passed the second summand and the running head still fits in the universe.
No condition on the marker: the walk parks it itself, at the top, so it is
reached exactly when the sum does not fit. -/
theorem exists_walk_test (hh : PlusHeads i j k a b mk prot) (x : Fin K → A) :
    ∀ t : ℕ, t ≤ orank (x j) → orank (x i) + t < Nat.card A →
      ∃ z : Fin K → A,
        Relation.ReflTransGen (wireStep (plusFamRel (A := A) i j k a b mk) plusWire)
            (.init, x) (.test, z) ∧
          (∀ p : Fin K, p ≠ a → p ≠ b → p ≠ mk → z p = x p) ∧
            orank (z a) = orank (x i) + t ∧ orank (z b) = t := by
  classical
  haveI : Nonempty A := ⟨x i⟩
  intro t
  induction t with
  | zero =>
    intro _ _
    obtain ⟨m0, hm0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    obtain ⟨mx, hmx⟩ := exists_orank_eq (A := A) (m := Nat.card A - 1) (by
      have := Nat.card_pos (α := A)
      omega)
    have hmxtop : ∀ e : A, e ≤ mx := fun e =>
      orank_le_iff.mp (by have := orank_lt_card e; omega)
    refine ⟨Function.update (Function.update (Function.update x a (x i)) b m0) mk mx,
      ?_, ?_, ?_, ?_⟩
    · refine Relation.ReflTransGen.single ⟨true, ⟨rfl, fun h => ?_⟩, rfl⟩
      by_cases hha : h = a
      · rw [plusInitMoves, if_pos hha, hha]
        change Function.update (Function.update (Function.update x a (x i)) b m0) mk mx a = x i
        rw [Function.update_of_ne hh.amk, Function.update_of_ne hh.ab,
          Function.update_self]
      · by_cases hhb : h = b
        · rw [plusInitMoves, if_neg hha, if_pos hhb, hhb]
          change ∀ e : A,
            Function.update (Function.update (Function.update x a (x i)) b m0) mk mx b ≤ e
          rw [Function.update_of_ne hh.bmk, Function.update_self]
          exact fun e => isMin_of_orank_eq_zero hm0 e
        · by_cases hhmk : h = mk
          · rw [plusInitMoves, if_neg hha, if_neg hhb, if_pos hhmk, hhmk]
            change ∀ e : A,
              e ≤ Function.update (Function.update (Function.update x a (x i)) b m0) mk mx mk
            rw [Function.update_self]
            exact hmxtop
          · rw [plusInitMoves, if_neg hha, if_neg hhb, if_neg hhmk]
            change Function.update (Function.update (Function.update x a (x i)) b m0) mk mx h = x h
            rw [Function.update_of_ne hhmk, Function.update_of_ne hhb, Function.update_of_ne hha]
    · intro p hpa hpb hpmk
      rw [Function.update_of_ne hpmk, Function.update_of_ne hpb, Function.update_of_ne hpa]
    · rw [Function.update_of_ne hh.amk, Function.update_of_ne hh.ab,
        Function.update_self]
      omega
    · rw [Function.update_of_ne hh.bmk, Function.update_self, hm0]
  | succ t ih =>
    intro htj hfit
    obtain ⟨z, hwalk, hzp, hza, hzb⟩ := ih (by omega) (by omega)
    -- the counter has not arrived, so the test fails
    have hzj : z j = x j := hzp j hh.ja hh.jb hh.jmk
    have hbne : z b ≠ z j := by
      rw [hzj]
      intro he
      rw [← he, hzb] at htj
      omega
    -- the marker is at the top and the sum still fits, so the overflow test fails
    have hmax : ∀ e : A, e ≤ z mk := by
      have := plusInv_of_walk hh x (.test, z) hwalk
      exact this.2.2.2
    have hamk : z a ≠ z mk := by
      intro he
      have hmkr : orank (z mk) = Nat.card A - 1 := orank_isTop hmax
      rw [← he, hza] at hmkr
      omega
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
    · intro p hpa hpb hpmk
      exact (hz'p p hpa hpb).trans (hzp p hpa hpb hpmk)
    · rw [hz'a, hza']
    · rw [hz'b, hzb']

/-! ### What an addition decides -/

/-- **The addition fragment decides the addition**, with no side condition: it
parks its own marker, so overflow is detected exactly where the sum leaves the
universe, and a sum that leaves the universe is not the rank of the third head
either. -/
theorem decides_plusP (hh : PlusHeads i j k a b mk prot) (hprotK : prot ≤ K) :
    (plusP (L := L) i j k a b mk).Decides A prot
      (fun x => orank (x i) + orank (x j) = orank (x k)) := by
  refine (((runs_wireP (plusFam (L := L) i j k a b mk) plusWire
    (runs_plusFam (A := A) i j k a b mk) (fun c => headLocal2_top _) .init).weaken
      hprotK).mono ?_ ?_)
  · -- soundness
    rintro x c y ⟨u, hwalk, c', hrel, hwire⟩
    have hinv := plusInv_of_walk hh x u hwalk
    have hprotect : ∀ z : Fin K → A, (∀ p : Fin K, p ≠ a → p ≠ b → p ≠ mk → z p = x p) →
        HeadAgree prot x z := by
      intro z hzp p hp
      exact (hzp p (fun he => by rw [he] at hp; exact absurd hh.ha (by omega))
        (fun he => by rw [he] at hp; exact absurd hh.hb (by omega))
        (fun he => by rw [he] at hp; exact absurd hh.hmk (by omega))).symm
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
      refine ⟨?_, ?_⟩
      · change c = true ↔ orank (x i) + orank (x j) = orank (x k)
        rw [← hcc, hc, ← hbase.1 k hh.ka hh.kb hh.kmk, ← orank_inj_iff (A := A), hsum]
      · rw [hyu]
        exact hprotect u.2 hbase.1
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
        have hmkr : orank (u.2 mk) = Nat.card A - 1 := orank_isTop hbase.2.2.2
        have hatop : orank (u.2 a) = Nat.card A - 1 := by
          rw [hc.mp rfl]
          exact hmkr
        have hblt : orank (u.2 b) < orank (x j) :=
          lt_of_le_of_ne hbase.2.2.1 fun he => hbj (orank_inj he)
        have hkk : orank (x k) < Nat.card A := orank_lt_card _
        refine ⟨?_, ?_⟩
        · change c = true ↔ orank (x i) + orank (x j) = orank (x k)
          rw [hcf]
          simp only [Bool.false_eq_true, false_iff]
          have := hbase.2.1
          omega
        · rw [hyu]
          exact hprotect u.2 hbase.1
  · -- completeness
    rintro x c y ⟨hc, hag⟩
    change c = true ↔ orank (x i) + orank (x j) = orank (x k) at hc
    have hxy : ∀ z : Fin K → A, (∀ p : Fin K, p ≠ a → p ≠ b → p ≠ mk → z p = x p) →
        HeadAgree prot y z := by
      intro z hzp p hp
      rw [← hag p hp]
      exact (hzp p (fun he => by rw [he] at hp; exact absurd hh.ha (by omega))
        (fun he => by rw [he] at hp; exact absurd hh.hb (by omega))
        (fun he => by rw [he] at hp; exact absurd hh.hmk (by omega))).symm
    have hkk : orank (x k) < Nat.card A := orank_lt_card _
    by_cases hfits : orank (x i) + orank (x j) < Nat.card A
    · obtain ⟨z, hwalk, hzp, hza, hzb⟩ := exists_walk_test hh x (orank (x j)) le_rfl hfits
      have hzj : z j = x j := hzp j hh.ja hh.jb hh.jmk
      have hbeq : z b = z j := by
        rw [hzj]
        exact orank_inj (by rw [hzb])
      have hkeq : z k = x k := hzp k hh.ka hh.kb hh.kmk
      have s1 : wireStep (plusFamRel (A := A) i j k a b mk) plusWire
          (.test, z) (.check, z) := ⟨true, ⟨by simp [hbeq], rfl⟩, rfl⟩
      refine ⟨z, hxy z hzp, (.check, z), hwalk.tail s1, c, ⟨?_, rfl⟩, rfl⟩
      change c = true ↔ z a = z k
      rw [hc, hkeq, ← orank_inj_iff (A := A), hza]
    · have hik : orank (x i) < Nat.card A := orank_lt_card _
      obtain ⟨z, hwalk, hzp, hza, hzb⟩ :=
        exists_walk_test hh x (Nat.card A - 1 - orank (x i)) (by omega) (by omega)
      have hmax : ∀ e : A, e ≤ z mk := (plusInv_of_walk hh x (.test, z) hwalk).2.2.2
      have hzj : z j = x j := hzp j hh.ja hh.jb hh.jmk
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
        rw [hza, orank_isTop hmax]
        omega
      have hcf : c = false := by
        cases c with
        | false => rfl
        | true => exact absurd (hc.mp rfl) (by omega)
      have s1 : wireStep (plusFamRel (A := A) i j k a b mk) plusWire
          (.test, z) (.over, z) := ⟨false, ⟨by simp [hbne], rfl⟩, rfl⟩
      refine ⟨z, hxy z hzp, (.over, z), hwalk.tail s1, true, ⟨by simp [hamk], rfl⟩, ?_⟩
      rw [hcf]
      rfl

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

/-! ### The control graph of a multiplication -/

/-- The control nodes of a multiplication: an outer loop counting the rounds and,
inside it, a scan looking for the element that carries the next partial
product. -/
inductive TimesNode
  /-- Send the accumulator and the round counter to the least element, and the
  scan's marker to the greatest. -/
  | init : TimesNode
  /-- Has the round counter reached the second factor? -/
  | outer : TimesNode
  /-- It has: is the accumulator the claimed product? -/
  | final : TimesNode
  /-- It has not: start the scan at the least element. -/
  | scanInit : TimesNode
  /-- Does the candidate carry the accumulator plus the first factor? -/
  | probe : TimesNode
  /-- It does not: is the candidate at the marker, i.e., would the product
  overflow? -/
  | scanOver : TimesNode
  /-- Step the candidate. -/
  | scanStep : TimesNode
  /-- The candidate carries the next partial product: take it, and count the
  round. -/
  | commit : TimesNode
  deriving DecidableEq

instance : Finite TimesNode := by
  refine Finite.of_injective (fun c : TimesNode => match c with
      | .init => (0 : Fin 8)
      | .outer => 1
      | .final => 2
      | .scanInit => 3
      | .probe => 4
      | .scanOver => 5
      | .scanStep => 6
      | .commit => 7) ?_
  rintro (_ | _ | _ | _ | _ | _ | _ | _) (_ | _ | _ | _ | _ | _ | _ | _) h <;> simp_all

/-- The wiring of a multiplication: the outer loop `outer → scan → commit →
outer`, the scan `probe → scanOver → scanStep → probe`, and the two answers
hanging off `final` and off the scan's overflow test. -/
def timesWire : TimesNode → Bool → TimesNode ⊕ Bool
  | .init, _ => Sum.inl .outer
  | .outer, c => if c then Sum.inl .final else Sum.inl .scanInit
  | .final, c => Sum.inr c
  | .scanInit, _ => Sum.inl .probe
  | .probe, c => if c then Sum.inl .commit else Sum.inl .scanOver
  | .scanOver, c => if c then Sum.inr false else Sum.inl .scanStep
  | .scanStep, _ => Sum.inl .probe
  | .commit, _ => Sum.inl .outer

open Classical in
/-- The moves that start a multiplication: accumulator and round counter to the
least element, the scan's marker to the greatest. -/
noncomputable def timesInitMoves (acc cnt tmk : Fin K) : Fin K → HeadMove K :=
  fun h => if h = acc then .toMin else if h = cnt then .toMin else
    if h = tmk then .toMax else .stay

open Classical in
/-- The move that starts a scan: the candidate to the least element. -/
noncomputable def timesScanInitMoves (cand : Fin K) : Fin K → HeadMove K :=
  fun h => if h = cand then .toMin else .stay

open Classical in
/-- The move of one scan step: the candidate advances. -/
noncomputable def timesScanStepMoves (cand : Fin K) : Fin K → HeadMove K :=
  fun h => if h = cand then .succ cand else .stay

open Classical in
/-- The moves that close a round: the accumulator takes the candidate's value and
the round counter advances. -/
noncomputable def timesCommitMoves (acc cnt cand : Fin K) : Fin K → HeadMove K :=
  fun h => if h = acc then .copy cand else if h = cnt then .succ cnt else .stay

/-- The fragments of a multiplication. The `probe` node is a whole addition
program (`DescriptiveComplexity.HeadProgram.plusP`), which is what makes the
scan work: it asks whether the candidate carries the accumulator plus the first
factor. -/
noncomputable def timesFam (i j k acc cnt cand tmk a b mk : Fin K) :
    TimesNode → HeadProgram L K
  | .init => moveP (timesInitMoves acc cnt tmk)
  | .outer => leafP (HeadMove.eqVarF L cnt j) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .final => leafP (HeadMove.eqVarF L acc k) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .scanInit => moveP (timesScanInitMoves cand)
  | .probe => plusP acc i cand a b mk
  | .scanOver => leafP (HeadMove.eqVarF L cand tmk) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .scanStep => moveP (timesScanStepMoves cand)
  | .commit => moveP (timesCommitMoves acc cnt cand)

/-- **Multiplication**: decide `orank (x i) * orank (x j) = orank (x k)`, by
adding the first factor to an accumulator once per round. -/
noncomputable def timesP (i j k acc cnt cand tmk a b mk : Fin K) : HeadProgram L K :=
  wireP (timesFam (L := L) i j k acc cnt cand tmk a b mk) timesWire .init

/-! ### The head layout of a multiplication -/

/-- The head indices a caller of a multiplication must respect. Three levels: the
interface below `p`, the four working heads between `p` and `m`, and the
addition's own three scratch heads at `m` and above – the last group being
exactly what `DescriptiveComplexity.HeadProgram.PlusHeads` asks of the addition
called at the `probe` node. -/
structure TimesHeads (i j k acc cnt cand tmk a b mk : Fin K) (p m : ℕ) : Prop where
  /-- The first factor is interface. -/
  hi : (i : ℕ) < p
  /-- The second factor is interface. -/
  hj : (j : ℕ) < p
  /-- The claimed product is interface. -/
  hk : (k : ℕ) < p
  /-- The accumulator is a working head. -/
  hacc : p ≤ (acc : ℕ)
  /-- The round counter is a working head. -/
  hcnt : p ≤ (cnt : ℕ) ∧ (cnt : ℕ) < m
  /-- The scan's candidate is a working head. -/
  hcand : p ≤ (cand : ℕ)
  /-- The scan's marker is a working head. -/
  htmk : p ≤ (tmk : ℕ) ∧ (tmk : ℕ) < m
  /-- The addition at the `probe` node has the layout it needs, which also places
  `acc`, `i` and `cand` below `m` and `a`, `b`, `mk` at `m` or above. -/
  hplus : PlusHeads acc i cand a b mk m
  /-- The accumulator is not the round counter. -/
  hac : acc ≠ cnt
  /-- The accumulator is not the candidate. -/
  haca : acc ≠ cand
  /-- The accumulator is not the scan's marker. -/
  hacm : acc ≠ tmk
  /-- The round counter is not the candidate. -/
  hcc : cnt ≠ cand
  /-- The round counter is not the scan's marker. -/
  hcm : cnt ≠ tmk
  /-- The candidate is not the scan's marker. -/
  hcam : cand ≠ tmk

/-! ### What the fragments of a multiplication run -/

section TimesFam

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {i j k acc cnt cand tmk a b mk : Fin K} {p m : ℕ}

/-- The relations the fragments of a multiplication run, at the level `m` that
protects the working heads and leaves the addition's scratch heads free. -/
noncomputable def timesFamRel (i j k acc cnt cand tmk : Fin K) (m : ℕ) :
    TimesNode → (Fin K → A) → Bool → (Fin K → A) → Prop
  | .init => fun x c y => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (timesInitMoves acc cnt tmk q).Holds x q (y q)
  | .outer => fun x c y => (c = true ↔ x cnt = x j) ∧ HeadAgree m x y
  | .final => fun x c y => (c = true ↔ x acc = x k) ∧ HeadAgree m x y
  | .scanInit => fun x c y => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (timesScanInitMoves cand q).Holds x q (y q)
  | .probe => fun x c y =>
      (c = true ↔ orank (x acc) + orank (x i) = orank (x cand)) ∧ HeadAgree m x y
  | .scanOver => fun x c y => (c = true ↔ x cand = x tmk) ∧ HeadAgree m x y
  | .scanStep => fun x c y => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (timesScanStepMoves cand q).Holds x q (y q)
  | .commit => fun x c y => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (timesCommitMoves acc cnt cand q).Holds x q (y q)

theorem runs_timesFam (hh : TimesHeads i j k acc cnt cand tmk a b mk p m) (hmK : m ≤ K)
    (c : TimesNode) :
    (timesFam (L := L) i j k acc cnt cand tmk a b mk c).Runs A m
      (timesFamRel i j k acc cnt cand tmk m c) := by
  classical
  cases c with
  | init =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ acc := fun he => by rw [he] at hq; exact absurd hh.hplus.hi (by omega)
    have h2 : q ≠ cnt := fun he => by rw [he] at hq; exact absurd hh.hcnt.2 (by omega)
    have h3 : q ≠ tmk := fun he => by rw [he] at hq; exact absurd hh.htmk.2 (by omega)
    rw [timesInitMoves, if_neg h1, if_neg h2, if_neg h3]
  | scanInit =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ cand := fun he => by rw [he] at hq; exact absurd hh.hplus.hk (by omega)
    rw [timesScanInitMoves, if_neg h1]
  | scanStep =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ cand := fun he => by rw [he] at hq; exact absurd hh.hplus.hk (by omega)
    rw [timesScanStepMoves, if_neg h1]
  | commit =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ acc := fun he => by rw [he] at hq; exact absurd hh.hplus.hi (by omega)
    have h2 : q ≠ cnt := fun he => by rw [he] at hq; exact absurd hh.hcnt.2 (by omega)
    rw [timesCommitMoves, if_neg h1, if_neg h2]
  | outer =>
    exact (decides_leafP (HeadMove.eqVarF L cnt j)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)).congr fun x => by simp
  | final =>
    exact (decides_leafP (HeadMove.eqVarF L acc k)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)).congr fun x => by simp
  | scanOver =>
    exact (decides_leafP (HeadMove.eqVarF L cand tmk)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)).congr fun x => by simp
  | probe => exact decides_plusP hh.hplus hmK

omit [Finite A] in
theorem headLocal2_timesFamRel (hh : TimesHeads i j k acc cnt cand tmk a b mk p m)
    (c : TimesNode) :
    HeadLocal2 m (timesFamRel (A := A) i j k acc cnt cand tmk m c) := by
  have hacc : (acc : ℕ) < m := hh.hplus.hi
  have hi' : (i : ℕ) < m := hh.hplus.hj
  have hcand : (cand : ℕ) < m := hh.hplus.hk
  have hcnt : (cnt : ℕ) < m := hh.hcnt.2
  have htmk : (tmk : ℕ) < m := hh.htmk.2
  have hj' : (j : ℕ) < m := by have := hh.hj; have := hh.hcnt.1; omega
  have hk' : (k : ℕ) < m := by have := hh.hk; have := hh.hcnt.1; omega
  cases c with
  | init =>
    refine headLocal2_moveP fun q _ => ?_
    rw [timesInitMoves]
    split_ifs <;> trivial
  | scanInit =>
    refine headLocal2_moveP fun q _ => ?_
    rw [timesScanInitMoves]
    split_ifs <;> trivial
  | scanStep =>
    refine headLocal2_moveP fun q _ => ?_
    rw [timesScanStepMoves]
    split_ifs with h
    · exact hcand
    · trivial
  | commit =>
    refine headLocal2_moveP fun q _ => ?_
    rw [timesCommitMoves]
    split_ifs with h1 h2
    · exact hcand
    · exact hcnt
    · trivial
  | outer =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hcnt, hx _ hj']
  | final =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hacc, hx _ hk']
  | scanOver =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hcand, hx _ htmk]
  | probe =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hacc, hx _ hi', hx _ hcand]

omit [Finite A] in
/-- **A multiplication is deterministic**: every node of its control graph is –
the `probe` node because an addition is
(`DescriptiveComplexity.HeadProgram.deterministic_plusP`). -/
theorem deterministic_timesP (i j k acc cnt cand tmk a b mk : Fin K) :
    (timesP (L := L) i j k acc cnt cand tmk a b mk).Deterministic A := by
  refine deterministic_wireP _ _ _ ?_
  rintro (_ | _ | _ | _ | _ | _ | _ | _)
  · exact deterministic_moveP _
  · exact deterministic_leafP (HeadMove.eqVarF L cnt j)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_leafP (HeadMove.eqVarF L acc k)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_moveP _
  · exact deterministic_plusP _ _ _ _ _ _
  · exact deterministic_leafP (HeadMove.eqVarF L cand tmk)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_moveP _
  · exact deterministic_moveP _

/-! ### The invariant of a multiplication -/

/-- The invariant of both loops: the accumulator carries the first factor times
the round counter, the round counter has not passed the second factor, the scan's
marker is at the greatest element, and nothing else below `m` has moved. -/
def TimesBase (i j acc cnt cand tmk : Fin K) (m : ℕ) (x z : Fin K → A) : Prop :=
  (∀ q : Fin K, (q : ℕ) < m → q ≠ acc → q ≠ cnt → q ≠ cand → q ≠ tmk → z q = x q) ∧
    orank (z acc) = orank (x i) * orank (z cnt) ∧
      orank (z cnt) ≤ orank (x j) ∧
        ∀ e : A, e ≤ z tmk

/-- The invariant of the control walk of a multiplication, node by node. Inside
the scan it also records how far the candidate has got: below the target while
the probe keeps failing, at it when the probe succeeds. -/
def TimesInv (i j acc cnt cand tmk : Fin K) (m : ℕ) (x : Fin K → A) :
    TimesNode → (Fin K → A) → Prop
  | .init => fun z => z = x
  | .outer => fun z => TimesBase i j acc cnt cand tmk m x z
  | .final => fun z => TimesBase i j acc cnt cand tmk m x z ∧ z cnt = x j
  | .scanInit => fun z => TimesBase i j acc cnt cand tmk m x z ∧ z cnt ≠ x j
  | .probe => fun z => TimesBase i j acc cnt cand tmk m x z ∧ z cnt ≠ x j ∧
      orank (z cand) ≤ orank (z acc) + orank (x i)
  | .scanOver => fun z => TimesBase i j acc cnt cand tmk m x z ∧ z cnt ≠ x j ∧
      orank (z cand) < orank (z acc) + orank (x i)
  | .scanStep => fun z => TimesBase i j acc cnt cand tmk m x z ∧ z cnt ≠ x j ∧
      orank (z cand) < orank (z acc) + orank (x i)
  | .commit => fun z => TimesBase i j acc cnt cand tmk m x z ∧ z cnt ≠ x j ∧
      orank (z cand) = orank (z acc) + orank (x i)

section TimesSound

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {i j k acc cnt cand tmk a b mk : Fin K} {p m : ℕ}

omit [Finite A] [LinearOrder A] in
/-- The interface heads a multiplication must not disturb are below every working
head. -/
theorem timesBase_headAgree (hh : TimesHeads i j k acc cnt cand tmk a b mk p m)
    {x z : Fin K → A}
    (hz : ∀ q : Fin K, (q : ℕ) < m → q ≠ acc → q ≠ cnt → q ≠ cand → q ≠ tmk → z q = x q) :
    HeadAgree p x z := by
  intro q hq
  have hpm : p ≤ m := by have := hh.hcnt; omega
  refine (hz q (by omega) ?_ ?_ ?_ ?_).symm
  · exact fun he => by rw [he] at hq; exact absurd hh.hacc (by omega)
  · exact fun he => by rw [he] at hq; exact absurd hh.hcnt.1 (by omega)
  · exact fun he => by rw [he] at hq; exact absurd hh.hcand (by omega)
  · exact fun he => by rw [he] at hq; exact absurd hh.htmk.1 (by omega)

omit [Finite A] in
/-- The invariant reads only the heads below `m`, so it survives a fragment that
dirties the addition's scratch heads. -/
theorem TimesBase.congr (hh : TimesHeads i j k acc cnt cand tmk a b mk p m)
    {x z z' : Fin K → A} (hb : TimesBase i j acc cnt cand tmk m x z)
    (hzz : HeadAgree m z z') : TimesBase i j acc cnt cand tmk m x z' := by
  have h1 : z' acc = z acc := (hzz acc hh.hplus.hi).symm
  have h2 : z' cnt = z cnt := (hzz cnt hh.hcnt.2).symm
  have h4 : z' tmk = z tmk := (hzz tmk hh.htmk.2).symm
  refine ⟨fun q hq h5 h6 h7 h8 => ?_, ?_, ?_, ?_⟩
  · rw [← hzz q hq]
    exact hb.1 q hq h5 h6 h7 h8
  · rw [h1, h2]
    exact hb.2.1
  · rw [h2]
    exact hb.2.2.1
  · rw [h4]
    exact hb.2.2.2

omit [Finite A] in
/-- The moves that start a multiplication, read off. -/
theorem holds_timesInitMoves (hh : TimesHeads i j k acc cnt cand tmk a b mk p m)
    {x y : Fin K → A}
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (timesInitMoves acc cnt tmk q).Holds x q (y q)) :
    (∀ e : A, y acc ≤ e) ∧ (∀ e : A, y cnt ≤ e) ∧ (∀ e : A, e ≤ y tmk) ∧
      ∀ q : Fin K, (q : ℕ) < m → q ≠ acc → q ≠ cnt → q ≠ tmk → y q = x q := by
  classical
  refine ⟨?_, ?_, ?_, fun q hq h1 h2 h3 => ?_⟩
  · have := hmv acc hh.hplus.hi
    rw [timesInitMoves, if_pos rfl] at this
    exact this
  · have := hmv cnt hh.hcnt.2
    rw [timesInitMoves, if_neg (Ne.symm hh.hac), if_pos rfl] at this
    exact this
  · have := hmv tmk hh.htmk.2
    rw [timesInitMoves, if_neg (Ne.symm hh.hacm), if_neg (Ne.symm hh.hcm), if_pos rfl] at this
    exact this
  · have := hmv q hq
    rw [timesInitMoves, if_neg h1, if_neg h2, if_neg h3] at this
    exact this

omit [Finite A] in
/-- The move that starts a scan, read off. -/
theorem holds_timesScanInitMoves (hh : TimesHeads i j k acc cnt cand tmk a b mk p m)
    {x y : Fin K → A}
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (timesScanInitMoves cand q).Holds x q (y q)) :
    (∀ e : A, y cand ≤ e) ∧ ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → y q = x q := by
  classical
  refine ⟨?_, fun q hq h1 => ?_⟩
  · have := hmv cand hh.hplus.hk
    rw [timesScanInitMoves, if_pos rfl] at this
    exact this
  · have := hmv q hq
    rw [timesScanInitMoves, if_neg h1] at this
    exact this

omit [Finite A] in
/-- The move of one scan step, read off. -/
theorem holds_timesScanStepMoves (hh : TimesHeads i j k acc cnt cand tmk a b mk p m)
    {x y : Fin K → A}
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (timesScanStepMoves cand q).Holds x q (y q)) :
    x cand ⋖ y cand ∧ ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → y q = x q := by
  classical
  refine ⟨?_, fun q hq h1 => ?_⟩
  · have := hmv cand hh.hplus.hk
    rw [timesScanStepMoves, if_pos rfl] at this
    exact ⟨this.1, fun e h1 h2 => this.2 e ⟨h1, h2⟩⟩
  · have := hmv q hq
    rw [timesScanStepMoves, if_neg h1] at this
    exact this

omit [Finite A] in
/-- The moves that close a round, read off. -/
theorem holds_timesCommitMoves (hh : TimesHeads i j k acc cnt cand tmk a b mk p m)
    {x y : Fin K → A}
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (timesCommitMoves acc cnt cand q).Holds x q (y q)) :
    y acc = x cand ∧ x cnt ⋖ y cnt ∧
      ∀ q : Fin K, (q : ℕ) < m → q ≠ acc → q ≠ cnt → y q = x q := by
  classical
  refine ⟨?_, ?_, fun q hq h1 h2 => ?_⟩
  · have := hmv acc hh.hplus.hi
    rw [timesCommitMoves, if_pos rfl] at this
    exact this
  · have := hmv cnt hh.hcnt.2
    rw [timesCommitMoves, if_neg (Ne.symm hh.hac), if_pos rfl] at this
    exact ⟨this.1, fun e h1 h2 => this.2 e ⟨h1, h2⟩⟩
  · have := hmv q hq
    rw [timesCommitMoves, if_neg h1, if_neg h2] at this
    exact this

/-- **The invariant holds all along the control walk of a multiplication.** -/
theorem timesInv_of_walk (hh : TimesHeads i j k acc cnt cand tmk a b mk p m) (x : Fin K → A) :
    ∀ u : TimesNode × (Fin K → A),
      Relation.ReflTransGen
          (wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire) (.init, x) u →
        TimesInv i j acc cnt cand tmk m x u.1 u.2 := by
  have hjm : (j : ℕ) < m := by
    have := hh.hj
    have := hh.hcnt.1
    have := hh.hcnt.2
    omega
  have hjne : j ≠ acc ∧ j ≠ cnt ∧ j ≠ cand ∧ j ≠ tmk := by
    have h0 := hh.hj
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have := hh.hacc
      rw [he] at h0
      omega
    · have := hh.hcnt.1
      rw [he] at h0
      omega
    · have := hh.hcand
      rw [he] at h0
      omega
    · have := hh.htmk.1
      rw [he] at h0
      omega
  have hine : (i : ℕ) < m ∧ i ≠ acc ∧ i ≠ cnt ∧ i ≠ cand ∧ i ≠ tmk := by
    have h0 := hh.hi
    refine ⟨hh.hplus.hj, fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have := hh.hacc
      rw [he] at h0
      omega
    · have := hh.hcnt.1
      rw [he] at h0
      omega
    · have := hh.hcand
      rw [he] at h0
      omega
    · have := hh.htmk.1
      rw [he] at h0
      omega
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
      obtain ⟨hacc0, hcnt0, htmax, hyq⟩ := holds_timesInitMoves hh hmv
      have hw : w.1 = .outer := by
        rw [timesWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      rw [hw]
      refine ⟨fun q hq h1 h2 _ h4 => hyq q hq h1 h2 h4, ?_, ?_, htmax⟩
      · rw [orank_eq_zero hacc0, orank_eq_zero hcnt0]
        omega
      · rw [orank_eq_zero hcnt0]
        omega
    | outer =>
      have hbase : TimesBase i j acc cnt cand tmk m x v.2 := by
        have := ih
        rw [hnode] at this
        exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      have hbase' := hbase.congr hh hag
      have hcnteq : w.2 cnt = v.2 cnt := (hag cnt hh.hcnt.2).symm
      have hjeq : v.2 j = x j := hbase.1 j hjm hjne.1 hjne.2.1 hjne.2.2.1 hjne.2.2.2
      cases c with
      | true =>
        have hw : w.1 = .final := by
          rw [timesWire, if_pos rfl] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hw]
        exact ⟨hbase', by rw [hcnteq, hc.mp rfl, hjeq]⟩
      | false =>
        have hw : w.1 = .scanInit := by
          rw [timesWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hw]
        refine ⟨hbase', fun he => ?_⟩
        rw [hcnteq, ← hjeq] at he
        exact absurd (hc.mpr he) (by simp)
    | final =>
      rw [hnode, timesWire] at hwire
      exact absurd hwire (by simp)
    | scanInit =>
      have hsi : TimesBase i j acc cnt cand tmk m x v.2 ∧ v.2 cnt ≠ x j := by
        have := ih
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hne⟩ := hsi
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hcand0, hyq⟩ := holds_timesScanInitMoves hh hmv
      have hw : w.1 = .probe := by
        rw [timesWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hacceq : w.2 acc = v.2 acc := hyq acc hh.hplus.hi hh.haca
      have hcnteq : w.2 cnt = v.2 cnt := hyq cnt hh.hcnt.2 hh.hcc
      have htmkeq : w.2 tmk = v.2 tmk := hyq tmk hh.htmk.2 (Ne.symm hh.hcam)
      rw [hw]
      refine ⟨⟨fun q hq h1 h2 h3 h4 => (hyq q hq h3).trans (hbase.1 q hq h1 h2 h3 h4), ?_, ?_, ?_⟩,
        ?_, ?_⟩
      · rw [hacceq, hcnteq]
        exact hbase.2.1
      · rw [hcnteq]
        exact hbase.2.2.1
      · rw [htmkeq]
        exact hbase.2.2.2
      · rw [hcnteq]
        exact hne
      · rw [orank_eq_zero hcand0]
        omega
    | probe =>
      have hpr : TimesBase i j acc cnt cand tmk m x v.2 ∧ v.2 cnt ≠ x j ∧
          orank (v.2 cand) ≤ orank (v.2 acc) + orank (x i) := by
        have := ih
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hne, hle⟩ := hpr
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      have hbase' := hbase.congr hh hag
      have hacceq : w.2 acc = v.2 acc := (hag acc hh.hplus.hi).symm
      have hcnteq : w.2 cnt = v.2 cnt := (hag cnt hh.hcnt.2).symm
      have hcandeq : w.2 cand = v.2 cand := (hag cand hh.hplus.hk).symm
      have hieq : v.2 i = x i :=
        hbase.1 i hine.1 hine.2.1 hine.2.2.1 hine.2.2.2.1 hine.2.2.2.2
      cases c with
      | true =>
        have hw : w.1 = .commit := by
          rw [timesWire, if_pos rfl] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hw]
        refine ⟨hbase', by rw [hcnteq]; exact hne, ?_⟩
        rw [hacceq, hcandeq, ← hieq]
        exact (hc.mp rfl).symm
      | false =>
        have hw : w.1 = .scanOver := by
          rw [timesWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hw]
        refine ⟨hbase', by rw [hcnteq]; exact hne, ?_⟩
        rw [hacceq, hcandeq]
        refine lt_of_le_of_ne hle fun he => ?_
        rw [hieq] at hc
        exact absurd (hc.mpr he.symm) (by simp)
    | scanOver =>
      have hso : TimesBase i j acc cnt cand tmk m x v.2 ∧ v.2 cnt ≠ x j ∧
          orank (v.2 cand) < orank (v.2 acc) + orank (x i) := by
        have := ih
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hne, hlt⟩ := hso
      rw [hnode] at hrel hwire
      obtain ⟨-, hag⟩ := hrel
      cases c with
      | true =>
        rw [timesWire, if_pos rfl] at hwire
        exact absurd hwire (by simp)
      | false =>
        have hw : w.1 = .scanStep := by
          rw [timesWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        have hacceq : w.2 acc = v.2 acc := (hag acc hh.hplus.hi).symm
        have hcnteq : w.2 cnt = v.2 cnt := (hag cnt hh.hcnt.2).symm
        have hcandeq : w.2 cand = v.2 cand := (hag cand hh.hplus.hk).symm
        rw [hw]
        refine ⟨hbase.congr hh hag, by rw [hcnteq]; exact hne, ?_⟩
        rw [hacceq, hcandeq]
        exact hlt
    | scanStep =>
      have hss : TimesBase i j acc cnt cand tmk m x v.2 ∧ v.2 cnt ≠ x j ∧
          orank (v.2 cand) < orank (v.2 acc) + orank (x i) := by
        have := ih
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hne, hlt⟩ := hss
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hcov, hyq⟩ := holds_timesScanStepMoves hh hmv
      have hw : w.1 = .probe := by
        rw [timesWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hacceq : w.2 acc = v.2 acc := hyq acc hh.hplus.hi hh.haca
      have hcnteq : w.2 cnt = v.2 cnt := hyq cnt hh.hcnt.2 hh.hcc
      have htmkeq : w.2 tmk = v.2 tmk := hyq tmk hh.htmk.2 (Ne.symm hh.hcam)
      rw [hw]
      refine ⟨⟨fun q hq h1 h2 h3 h4 => (hyq q hq h3).trans (hbase.1 q hq h1 h2 h3 h4), ?_, ?_, ?_⟩,
        ?_, ?_⟩
      · rw [hacceq, hcnteq]
        exact hbase.2.1
      · rw [hcnteq]
        exact hbase.2.2.1
      · rw [htmkeq]
        exact hbase.2.2.2
      · rw [hcnteq]
        exact hne
      · rw [orank_covBy hcov, hacceq]
        omega
    | commit =>
      have hcm : TimesBase i j acc cnt cand tmk m x v.2 ∧ v.2 cnt ≠ x j ∧
          orank (v.2 cand) = orank (v.2 acc) + orank (x i) := by
        have := ih
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hne, heq⟩ := hcm
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hacceq, hcov, hyq⟩ := holds_timesCommitMoves hh hmv
      have hw : w.1 = .outer := by
        rw [timesWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have htmkeq : w.2 tmk = v.2 tmk := hyq tmk hh.htmk.2 (Ne.symm hh.hacm) (Ne.symm hh.hcm)
      have hcntlt : orank (v.2 cnt) < orank (x j) :=
        lt_of_le_of_ne hbase.2.2.1 fun he => hne (orank_inj he)
      rw [hw]
      refine ⟨fun q hq h1 h2 h3 h4 => (hyq q hq h1 h2).trans (hbase.1 q hq h1 h2 h3 h4), ?_, ?_,
        by rw [htmkeq]; exact hbase.2.2.2⟩
      · rw [hacceq, heq, orank_covBy hcov, hbase.2.1, Nat.mul_succ]
      · rw [orank_covBy hcov]
        omega

/-! ### Completeness: building the two walks -/

/-- **The scan reaches every candidate up to its target**: from the start of a
scan, the walk can be continued until the candidate has any prescribed rank at
most the target's, the probe failing at every earlier one. -/
theorem exists_walk_probe (hh : TimesHeads i j k acc cnt cand tmk a b mk p m)
    (z₀ : Fin K → A) (hz₀ : orank (z₀ cand) = 0) (hmax : ∀ e : A, e ≤ z₀ tmk) :
    ∀ t : ℕ, t ≤ orank (z₀ acc) + orank (z₀ i) → t < Nat.card A →
      ∃ z : Fin K → A,
        Relation.ReflTransGen
            (wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire)
            (.probe, z₀) (.probe, z) ∧
          (∀ q : Fin K, (q : ℕ) < m → q ≠ cand → z q = z₀ q) ∧ orank (z cand) = t := by
  classical
  intro t
  induction t with
  | zero =>
    intro _ _
    exact ⟨z₀, .refl, fun _ _ _ => rfl, hz₀⟩
  | succ t ih =>
    intro htar hlt
    obtain ⟨z, hwalk, hzq, hzc⟩ := ih (by omega) (by omega)
    have hacceq : z acc = z₀ acc := hzq acc hh.hplus.hi hh.haca
    have hieq : z i = z₀ i := by
      refine hzq i hh.hplus.hj fun he => ?_
      have h1 := hh.hi
      have h2 := hh.hcand
      rw [he] at h1
      omega
    have htmkeq : z tmk = z₀ tmk := hzq tmk hh.htmk.2 (Ne.symm hh.hcam)
    -- the probe fails, the candidate not having reached the target
    have hprobe : ¬(orank (z acc) + orank (z i) = orank (z cand)) := by
      rw [hacceq, hieq, hzc]
      omega
    -- the candidate is not at the marker either, the target fitting in the universe
    have hcandmk : z cand ≠ z tmk := by
      intro he
      have := orank_isTop (htmkeq ▸ hmax)
      rw [he, htmkeq, orank_isTop hmax] at hzc
      omega
    -- so the candidate steps
    obtain ⟨c', hc'⟩ := exists_orank_eq (A := A) (m := t + 1) hlt
    set z' := Function.update z cand c' with hz'
    have hz'c : z' cand = c' := by rw [hz', Function.update_self]
    have hz'q : ∀ q : Fin K, q ≠ cand → z' q = z q := fun q hq => by
      rw [hz', Function.update_of_ne hq]
    have s1 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
        (.probe, z) (.scanOver, z) := ⟨false, ⟨by simp [hprobe], fun _ _ => rfl⟩, rfl⟩
    have s2 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
        (.scanOver, z) (.scanStep, z) := ⟨false, ⟨by simp [hcandmk], fun _ _ => rfl⟩, rfl⟩
    have s3 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
        (.scanStep, z) (.probe, z') := by
      refine ⟨true, ⟨rfl, fun q _ => ?_⟩, rfl⟩
      by_cases hq : q = cand
      · rw [timesScanStepMoves, if_pos hq, hq]
        have hcov : z cand ⋖ c' := covBy_of_orank_succ (by rw [hc', hzc])
        change z cand < z' cand ∧ ∀ e : A, ¬(z cand < e ∧ e < z' cand)
        rw [hz'c]
        exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
      · rw [timesScanStepMoves, if_neg hq]
        exact hz'q q hq
    refine ⟨z', ((hwalk.tail s1).tail s2).tail s3, ?_, ?_⟩
    · intro q hq hqc
      exact (hz'q q hqc).trans (hzq q hq hqc)
    · rw [hz'c, hc']

/-- **The outer loop reaches every round whose partial product fits**: the state
after `r` rounds is reachable, the accumulator carrying `orank (x i) * r`. -/
theorem exists_walk_outer (hh : TimesHeads i j k acc cnt cand tmk a b mk p m) (x : Fin K → A) :
    ∀ r : ℕ, r ≤ orank (x j) → orank (x i) * r < Nat.card A →
      ∃ z : Fin K → A,
        Relation.ReflTransGen
            (wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire)
            (.init, x) (.outer, z) ∧
          (∀ q : Fin K, (q : ℕ) < m → q ≠ acc → q ≠ cnt → q ≠ cand → q ≠ tmk → z q = x q) ∧
            orank (z acc) = orank (x i) * r ∧ orank (z cnt) = r ∧ ∀ e : A, e ≤ z tmk := by
  classical
  haveI : Nonempty A := ⟨x i⟩
  have hjm : (j : ℕ) < m := by
    have := hh.hj
    have := hh.hcnt.1
    have := hh.hcnt.2
    omega
  have hjne : j ≠ acc ∧ j ≠ cnt ∧ j ≠ cand ∧ j ≠ tmk := by
    have h0 := hh.hj
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have := hh.hacc
      rw [he] at h0
      omega
    · have := hh.hcnt.1
      rw [he] at h0
      omega
    · have := hh.hcand
      rw [he] at h0
      omega
    · have := hh.htmk.1
      rw [he] at h0
      omega
  have hine : i ≠ acc ∧ i ≠ cnt ∧ i ≠ cand ∧ i ≠ tmk := by
    have h0 := hh.hi
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have := hh.hacc
      rw [he] at h0
      omega
    · have := hh.hcnt.1
      rw [he] at h0
      omega
    · have := hh.hcand
      rw [he] at h0
      omega
    · have := hh.htmk.1
      rw [he] at h0
      omega
  intro r
  induction r with
  | zero =>
    intro _ _
    obtain ⟨m0, hm0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    obtain ⟨mx, hmx⟩ := exists_orank_eq (A := A) (m := Nat.card A - 1) (by
      have := Nat.card_pos (α := A)
      omega)
    have hmxtop : ∀ e : A, e ≤ mx := fun e =>
      orank_le_iff.mp (by have := orank_lt_card e; omega)
    have hm0min : ∀ e : A, m0 ≤ e := fun e => isMin_of_orank_eq_zero hm0 e
    set z := Function.update (Function.update (Function.update x acc m0) cnt m0) tmk mx with hz
    have hzacc : z acc = m0 := by
      rw [hz, Function.update_of_ne hh.hacm, Function.update_of_ne hh.hac, Function.update_self]
    have hzcnt : z cnt = m0 := by
      rw [hz, Function.update_of_ne hh.hcm, Function.update_self]
    have hztmk : z tmk = mx := by rw [hz, Function.update_self]
    have hzq : ∀ q : Fin K, q ≠ acc → q ≠ cnt → q ≠ tmk → z q = x q := by
      intro q h1 h2 h3
      rw [hz, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
    refine ⟨z, Relation.ReflTransGen.single ⟨true, ⟨rfl, fun q _ => ?_⟩, rfl⟩,
      fun q _ h1 h2 _ h4 => hzq q h1 h2 h4, ?_, ?_, ?_⟩
    · by_cases h1 : q = acc
      · rw [timesInitMoves, if_pos h1, h1]
        change ∀ e : A, z acc ≤ e
        rw [hzacc]
        exact hm0min
      · by_cases h2 : q = cnt
        · rw [timesInitMoves, if_neg h1, if_pos h2, h2]
          change ∀ e : A, z cnt ≤ e
          rw [hzcnt]
          exact hm0min
        · by_cases h3 : q = tmk
          · rw [timesInitMoves, if_neg h1, if_neg h2, if_pos h3, h3]
            change ∀ e : A, e ≤ z tmk
            rw [hztmk]
            exact hmxtop
          · rw [timesInitMoves, if_neg h1, if_neg h2, if_neg h3]
            exact hzq q h1 h2 h3
    · rw [hzacc, hm0]
      omega
    · rw [hzcnt, hm0]
    · rw [hztmk]
      exact hmxtop
  | succ r ih =>
    intro hrj hfit
    have hfit' : orank (x i) * r < Nat.card A :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hfit
    obtain ⟨z, hwalk, hzq, hzacc, hzcnt, hztmk⟩ := ih (by omega) hfit'
    have hzj : z j = x j := hzq j hjm hjne.1 hjne.2.1 hjne.2.2.1 hjne.2.2.2
    have hzi : z i = x i := hzq i hh.hplus.hj hine.1 hine.2.1 hine.2.2.1 hine.2.2.2
    -- the round counter has not arrived
    have hcntne : z cnt ≠ z j := by
      rw [hzj]
      intro he
      rw [he] at hzcnt
      omega
    -- start the scan
    obtain ⟨m0, hm0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    set z₁ := Function.update z cand m0 with hz₁
    have hz₁c : z₁ cand = m0 := by rw [hz₁, Function.update_self]
    have hz₁q : ∀ q : Fin K, q ≠ cand → z₁ q = z q := fun q hq => by
      rw [hz₁, Function.update_of_ne hq]
    have s1 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
        (.outer, z) (.scanInit, z) := ⟨false, ⟨by simp [hcntne], fun _ _ => rfl⟩, rfl⟩
    have s2 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
        (.scanInit, z) (.probe, z₁) := by
      refine ⟨true, ⟨rfl, fun q _ => ?_⟩, rfl⟩
      by_cases hq : q = cand
      · rw [timesScanInitMoves, if_pos hq, hq]
        change ∀ e : A, z₁ cand ≤ e
        rw [hz₁c]
        exact fun e => isMin_of_orank_eq_zero hm0 e
      · rw [timesScanInitMoves, if_neg hq]
        exact hz₁q q hq
    -- scan up to the next partial product
    have h₁acc : orank (z₁ acc) = orank (x i) * r := by
      rw [hz₁q acc hh.haca, hzacc]
    have h₁i : z₁ i = x i := by rw [hz₁q i hine.2.2.1, hzi]
    have h₁tmk : ∀ e : A, e ≤ z₁ tmk := by
      rw [hz₁q tmk (Ne.symm hh.hcam)]
      exact hztmk
    obtain ⟨z₂, hwalk₂, hz₂q, hz₂c⟩ :=
      exists_walk_probe hh z₁ (by rw [hz₁c, hm0]) h₁tmk (orank (x i) * (r + 1))
        (by rw [h₁acc, h₁i, Nat.mul_succ]) hfit
    have h₂acc : z₂ acc = z₁ acc := hz₂q acc hh.hplus.hi hh.haca
    have h₂cnt : z₂ cnt = z₁ cnt := hz₂q cnt hh.hcnt.2 hh.hcc
    have h₂tmk : z₂ tmk = z₁ tmk := hz₂q tmk hh.htmk.2 (Ne.symm hh.hcam)
    have h₂i : z₂ i = z₁ i := hz₂q i hh.hplus.hj hine.2.2.1
    -- the probe now succeeds, and the round closes
    have hprobe : orank (z₂ acc) + orank (z₂ i) = orank (z₂ cand) := by
      rw [h₂acc, h₂i, h₁acc, h₁i, hz₂c, Nat.mul_succ]
    obtain ⟨cs, hcs⟩ := exists_orank_eq (A := A) (m := r + 1)
      (lt_of_le_of_lt hrj (orank_lt_card (x j)))
    set z₃ := Function.update (Function.update z₂ acc (z₂ cand)) cnt cs with hz₃
    have h₃acc : z₃ acc = z₂ cand := by
      rw [hz₃, Function.update_of_ne hh.hac, Function.update_self]
    have h₃cnt : z₃ cnt = cs := by rw [hz₃, Function.update_self]
    have h₃q : ∀ q : Fin K, q ≠ acc → q ≠ cnt → z₃ q = z₂ q := by
      intro q h1 h2
      rw [hz₃, Function.update_of_ne h2, Function.update_of_ne h1]
    have s3 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
        (.probe, z₂) (.commit, z₂) := ⟨true, ⟨by simp [hprobe], fun _ _ => rfl⟩, rfl⟩
    have s4 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
        (.commit, z₂) (.outer, z₃) := by
      refine ⟨true, ⟨rfl, fun q _ => ?_⟩, rfl⟩
      by_cases h1 : q = acc
      · rw [timesCommitMoves, if_pos h1, h1]
        change z₃ acc = z₂ cand
        exact h₃acc
      · by_cases h2 : q = cnt
        · rw [timesCommitMoves, if_neg h1, if_pos h2, h2]
          have hcov : z₂ cnt ⋖ cs := covBy_of_orank_succ (by
            rw [hcs, h₂cnt, hz₁q cnt hh.hcc, hzcnt])
          change z₂ cnt < z₃ cnt ∧ ∀ e : A, ¬(z₂ cnt < e ∧ e < z₃ cnt)
          rw [h₃cnt]
          exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
        · rw [timesCommitMoves, if_neg h1, if_neg h2]
          exact h₃q q h1 h2
    refine ⟨z₃, (((hwalk.tail s1).tail s2).trans hwalk₂).tail s3 |>.tail s4, ?_, ?_, ?_, ?_⟩
    · intro q hq h1 h2 h3 h4
      rw [h₃q q h1 h2, hz₂q q hq h3, hz₁q q h3]
      exact hzq q hq h1 h2 h3 h4
    · rw [h₃acc, hz₂c]
    · rw [h₃cnt, hcs]
    · rw [h₃q tmk (Ne.symm hh.hacm) (Ne.symm hh.hcm), h₂tmk]
      exact h₁tmk

/-! ### What a multiplication decides -/

/-- **The multiplication fragment decides the multiplication**, with no side
condition: the scan's marker is parked by the fragment itself, as the addition's
is, so a product that leaves the universe is detected in the round where it does
and is not the rank of the third head either. -/
theorem decides_timesP (hh : TimesHeads i j k acc cnt cand tmk a b mk p m) (hmK : m ≤ K) :
    (timesP (L := L) i j k acc cnt cand tmk a b mk).Decides A p
      (fun x => orank (x i) * orank (x j) = orank (x k)) := by
  classical
  have hpm : p ≤ m := by
    have := hh.hcnt.1
    have := hh.hcnt.2
    omega
  have hjm : (j : ℕ) < m := by
    have := hh.hj
    have := hh.hcnt.1
    have := hh.hcnt.2
    omega
  have hjne : j ≠ acc ∧ j ≠ cnt ∧ j ≠ cand ∧ j ≠ tmk := by
    have h0 := hh.hj
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have := hh.hacc
      rw [he] at h0
      omega
    · have := hh.hcnt.1
      rw [he] at h0
      omega
    · have := hh.hcand
      rw [he] at h0
      omega
    · have := hh.htmk.1
      rw [he] at h0
      omega
  have hkm : (k : ℕ) < m ∧ k ≠ acc ∧ k ≠ cnt ∧ k ≠ cand ∧ k ≠ tmk := by
    have h0 := hh.hk
    refine ⟨by omega, fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have := hh.hacc
      rw [he] at h0
      omega
    · have := hh.hcnt.1
      rw [he] at h0
      omega
    · have := hh.hcand
      rw [he] at h0
      omega
    · have := hh.htmk.1
      rw [he] at h0
      omega
  have hine : i ≠ acc ∧ i ≠ cnt ∧ i ≠ cand ∧ i ≠ tmk := by
    have h0 := hh.hi
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have := hh.hacc
      rw [he] at h0
      omega
    · have := hh.hcnt.1
      rw [he] at h0
      omega
    · have := hh.hcand
      rw [he] at h0
      omega
    · have := hh.htmk.1
      rw [he] at h0
      omega
  refine (((runs_wireP (timesFam (L := L) i j k acc cnt cand tmk a b mk) timesWire
    (runs_timesFam hh hmK) (headLocal2_timesFamRel hh) .init).weaken hpm).mono ?_ ?_)
  · -- soundness
    rintro x c y ⟨u, hwalk, c', hrel, hwire⟩
    have hinv := timesInv_of_walk hh x u hwalk
    have hkk : orank (x k) < Nat.card A := orank_lt_card _
    cases hnode : u.1 with
    | init =>
      rw [hnode, timesWire] at hwire
      exact absurd hwire (by simp)
    | outer =>
      rw [hnode, timesWire] at hwire
      cases c' <;> simp at hwire
    | scanInit =>
      rw [hnode, timesWire] at hwire
      exact absurd hwire (by simp)
    | probe =>
      rw [hnode, timesWire] at hwire
      cases c' <;> simp at hwire
    | scanStep =>
      rw [hnode, timesWire] at hwire
      exact absurd hwire (by simp)
    | commit =>
      rw [hnode, timesWire] at hwire
      exact absurd hwire (by simp)
    | final =>
      have hfi : TimesBase i j acc cnt cand tmk m x u.2 ∧ u.2 cnt = x j := by
        have := hinv
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hcnteq⟩ := hfi
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      rw [timesWire] at hwire
      have hcc : c' = c := Sum.inr.inj hwire
      have hkeq : u.2 k = x k := hbase.1 k hkm.1 hkm.2.1 hkm.2.2.1 hkm.2.2.2.1 hkm.2.2.2.2
      have hprod : orank (u.2 acc) = orank (x i) * orank (x j) := by
        rw [hbase.2.1, hcnteq]
      refine ⟨?_, ?_⟩
      · change c = true ↔ orank (x i) * orank (x j) = orank (x k)
        rw [← hcc, hc, hkeq, ← orank_inj_iff (A := A), hprod]
      · exact (timesBase_headAgree hh hbase.1).trans (hag.mono hpm)
    | scanOver =>
      have hso : TimesBase i j acc cnt cand tmk m x u.2 ∧ u.2 cnt ≠ x j ∧
          orank (u.2 cand) < orank (u.2 acc) + orank (x i) := by
        have := hinv
        rw [hnode] at this
        exact this
      obtain ⟨hbase, hne, hlt⟩ := hso
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      cases c' with
      | false =>
        rw [timesWire, if_neg (by simp)] at hwire
        exact absurd hwire (by simp)
      | true =>
        rw [timesWire, if_pos rfl] at hwire
        have hcf : c = false := (Sum.inr.inj hwire).symm
        have htop : orank (u.2 cand) = Nat.card A - 1 := by
          rw [hc.mp rfl]
          exact orank_isTop hbase.2.2.2
        have hcntlt : orank (u.2 cnt) < orank (x j) :=
          lt_of_le_of_ne hbase.2.2.1 fun he => hne (orank_inj he)
        have hstep : orank (x i) * (orank (u.2 cnt) + 1) ≤ orank (x i) * orank (x j) :=
          Nat.mul_le_mul_left _ (by omega)
        have hbig : Nat.card A ≤ orank (x i) * orank (x j) := by
          have h1 : orank (u.2 acc) + orank (x i) = orank (x i) * (orank (u.2 cnt) + 1) := by
            rw [hbase.2.1, Nat.mul_succ]
          omega
        refine ⟨?_, ?_⟩
        · change c = true ↔ orank (x i) * orank (x j) = orank (x k)
          rw [hcf]
          simp only [Bool.false_eq_true, false_iff]
          omega
        · exact (timesBase_headAgree hh hbase.1).trans (hag.mono hpm)
  · -- completeness
    rintro x c y ⟨hc, hag⟩
    change c = true ↔ orank (x i) * orank (x j) = orank (x k) at hc
    haveI : Nonempty A := ⟨x i⟩
    have hkk : orank (x k) < Nat.card A := orank_lt_card _
    have hpos : 0 < Nat.card A := Nat.card_pos
    have hxy : ∀ z : Fin K → A,
        (∀ q : Fin K, (q : ℕ) < m → q ≠ acc → q ≠ cnt → q ≠ cand → q ≠ tmk → z q = x q) →
        HeadAgree p y z := by
      intro z hz q hq
      rw [← hag q hq]
      exact timesBase_headAgree hh hz q hq
    by_cases hfits : orank (x i) * orank (x j) < Nat.card A
    · obtain ⟨z, hwalk, hzq, hzacc, hzcnt, hztmk⟩ :=
        exists_walk_outer hh x (orank (x j)) le_rfl hfits
      have hzj : z j = x j := hzq j hjm hjne.1 hjne.2.1 hjne.2.2.1 hjne.2.2.2
      have hzk : z k = x k := hzq k hkm.1 hkm.2.1 hkm.2.2.1 hkm.2.2.2.1 hkm.2.2.2.2
      have hcnteq : z cnt = z j := by
        rw [hzj]
        exact orank_inj (by rw [hzcnt])
      have s1 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
          (.outer, z) (.final, z) := ⟨true, ⟨by simp [hcnteq], fun _ _ => rfl⟩, rfl⟩
      refine ⟨z, hxy z hzq, (.final, z), hwalk.tail s1, c, ⟨?_, fun _ _ => rfl⟩, rfl⟩
      change c = true ↔ z acc = z k
      rw [hc, hzk, ← orank_inj_iff (A := A), hzacc]
    · -- the product overflows: find the round where the scan runs off the top
      have hex : ∃ s, Nat.card A ≤ orank (x i) * s := ⟨orank (x j), by omega⟩
      have hspec : Nat.card A ≤ orank (x i) * Nat.find hex := Nat.find_spec hex
      have hsle : Nat.find hex ≤ orank (x j) := Nat.find_min' hex (by omega)
      have hs0 : Nat.find hex ≠ 0 := by
        intro h0
        rw [h0, Nat.mul_zero] at hspec
        omega
      have hprev : orank (x i) * (Nat.find hex - 1) < Nat.card A := by
        have := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
        omega
      obtain ⟨z, hwalk, hzq, hzacc, hzcnt, hztmk⟩ :=
        exists_walk_outer hh x (Nat.find hex - 1) (by omega) hprev
      have hzj : z j = x j := hzq j hjm hjne.1 hjne.2.1 hjne.2.2.1 hjne.2.2.2
      have hzi : z i = x i := hzq i hh.hplus.hj hine.1 hine.2.1 hine.2.2.1 hine.2.2.2
      have hcntne : z cnt ≠ z j := by
        rw [hzj]
        intro he
        rw [he] at hzcnt
        omega
      obtain ⟨m0, hm0⟩ := exists_orank_eq (A := A) (m := 0) hpos
      set z₁ := Function.update z cand m0 with hz₁
      have hz₁c : z₁ cand = m0 := by rw [hz₁, Function.update_self]
      have hz₁q : ∀ q : Fin K, q ≠ cand → z₁ q = z q := fun q hq => by
        rw [hz₁, Function.update_of_ne hq]
      have s1 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
          (.outer, z) (.scanInit, z) := ⟨false, ⟨by simp [hcntne], fun _ _ => rfl⟩, rfl⟩
      have s2 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
          (.scanInit, z) (.probe, z₁) := by
        refine ⟨true, ⟨rfl, fun q _ => ?_⟩, rfl⟩
        by_cases hq : q = cand
        · rw [timesScanInitMoves, if_pos hq, hq]
          change ∀ e : A, z₁ cand ≤ e
          rw [hz₁c]
          exact fun e => isMin_of_orank_eq_zero hm0 e
        · rw [timesScanInitMoves, if_neg hq]
          exact hz₁q q hq
      have h₁acc : orank (z₁ acc) = orank (x i) * (Nat.find hex - 1) := by
        rw [hz₁q acc hh.haca, hzacc]
      have h₁i : z₁ i = x i := by rw [hz₁q i hine.2.2.1, hzi]
      have h₁tmk : ∀ e : A, e ≤ z₁ tmk := by
        rw [hz₁q tmk (Ne.symm hh.hcam)]
        exact hztmk
      have htar : orank (z₁ acc) + orank (z₁ i) = orank (x i) * Nat.find hex := by
        rw [h₁acc, h₁i, ← Nat.mul_succ]
        congr 1
        omega
      obtain ⟨z₂, hwalk₂, hz₂q, hz₂c⟩ :=
        exists_walk_probe hh z₁ (by rw [hz₁c, hm0]) h₁tmk (Nat.card A - 1)
          (by omega) (by omega)
      have h₂acc : z₂ acc = z₁ acc := hz₂q acc hh.hplus.hi hh.haca
      have h₂i : z₂ i = z₁ i := hz₂q i hh.hplus.hj hine.2.2.1
      have h₂tmk : z₂ tmk = z₁ tmk := hz₂q tmk hh.htmk.2 (Ne.symm hh.hcam)
      have hprobe : ¬(orank (z₂ acc) + orank (z₂ i) = orank (z₂ cand)) := by
        rw [h₂acc, h₂i, htar, hz₂c]
        omega
      have hcandmk : z₂ cand = z₂ tmk := by
        refine orank_inj ?_
        rw [hz₂c, h₂tmk, orank_isTop h₁tmk]
      have hcf : c = false := by
        cases c with
        | false => rfl
        | true => exact absurd (hc.mp rfl) (by omega)
      have s3 : wireStep (timesFamRel (A := A) i j k acc cnt cand tmk m) timesWire
          (.probe, z₂) (.scanOver, z₂) := ⟨false, ⟨by simp [hprobe], fun _ _ => rfl⟩, rfl⟩
      refine ⟨z₂, ?_, (.scanOver, z₂), ((hwalk.tail s1).tail s2).trans hwalk₂ |>.tail s3, true,
        ⟨by simp [hcandmk], fun _ _ => rfl⟩, ?_⟩
      · intro q hq
        rw [hxy z hzq q hq, ← hz₁q q (fun he => by
            rw [he] at hq
            have := hh.hcand
            omega), ← hz₂q q (by omega) (fun he => by
            rw [he] at hq
            have := hh.hcand
            omega)]
      · rw [hcf]
        rfl

end TimesSound

end TimesFam

end HeadProgram

end DescriptiveComplexity
