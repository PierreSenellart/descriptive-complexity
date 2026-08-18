/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadCapture

/-!
# Counting on a block of heads

A *deterministic* machine cannot guess a tuple: it has to walk the tuples one at
a time. This file gives it the odometer.

`DescriptiveComplexity.HeadProgram.lexNextP` replaces the tuple held on a block of
heads by its **lexicographic successor**, and exits `false` when there is none –
when the tuple is the greatest. It is the same chain a schoolchild uses to add
one: walk the positions from the last, and at the first position that is not at
its greatest value, step that head and reset the ones after it.

The one thing a machine cannot do directly is ask whether a head is at the
greatest element: that is not a quantifier-free fact of one head. So the block
comes with a **marker head** parked at the greatest element, and the test is the
atom “these two heads are equal” – the same device the quantifier sweep of
`DescriptiveComplexity.HeadEval` uses, here shared by every position of the block.

Accordingly the relation `DescriptiveComplexity.HeadProgram.lexRel` that the gadget runs
is stated in terms of the marker's *value*, not of maximality: it is an honest
description of what the machine does whatever the marker holds. Where the marker
is known to be at the greatest element, `DescriptiveComplexity.HeadProgram.tupSucc_of_lexRel`
turns it into `DescriptiveComplexity.TupSucc`, the coordinatewise description of
covering in `Lex (Fin n → A)`, and the walk becomes a walk along a finite linear
order like any other.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {K : ℕ}

namespace HeadProgram

/-! ### The control graph of an increment -/

/-- The control nodes of a lexicographic increment on a block of `n` heads:
`test j` has found the positions from `j` on to be at the marker and is about to
look at position `j - 1`; `bump j` steps position `j` and resets the rest. -/
inductive LexNode (n : ℕ)
  /-- Positions from `j` on are at the marker; about to test position `j - 1`. -/
  | test (j : Fin (n + 1)) : LexNode n
  /-- Step position `j`, and reset the positions after it. -/
  | bump (j : Fin n) : LexNode n

instance {n : ℕ} : Finite (LexNode n) := by
  refine Finite.of_injective (fun c : LexNode n => match c with
      | .test j => Sum.inl j
      | .bump j => Sum.inr j : LexNode n → Fin (n + 1) ⊕ Fin n) ?_
  rintro (_ | _) (_ | _) h <;> simp_all

/-- The position a test node is about to look at, if it has not run out. -/
def testPos {n : ℕ} (j : Fin (n + 1)) : Option (Fin n) :=
  if h : 0 < (j : ℕ) then some ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ else none

/-- The test node that follows, one position down. -/
def testDown {n : ℕ} (j : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩

theorem testPos_eq_none {n : ℕ} {j : Fin (n + 1)} (h : (j : ℕ) = 0) : testPos j = none := by
  rw [testPos, dif_neg (by omega)]

theorem testPos_eq_some {n : ℕ} {j : Fin (n + 1)} {p : ℕ} (h : (j : ℕ) = p + 1)
    (hp : p < n) : testPos j = some ⟨p, hp⟩ := by
  rw [testPos, dif_pos (by omega)]
  refine congrArg some (Fin.ext ?_)
  change (j : ℕ) - 1 = p
  omega

theorem testDown_val {n : ℕ} {j : Fin (n + 1)} {p : ℕ} (h : (j : ℕ) = p + 1) :
    ((testDown j : Fin (n + 1)) : ℕ) = p := by
  change (j : ℕ) - 1 = p
  omega

/-- The wiring of an increment: at the marker, look one position down; away from
it, step that position. -/
def lexWire {n : ℕ} : LexNode n → Bool → LexNode n ⊕ Bool
  | .test j, b => match testPos j with
      | none => Sum.inr false
      | some p => if b then Sum.inl (.test (testDown j)) else Sum.inl (.bump p)
  | .bump _, _ => Sum.inr true

open Classical in
/-- The moves of an increment: step position `j` of the block and send the
positions after it to the least element. -/
noncomputable def bumpMoves {n : ℕ} (blk : Fin n → Fin K) (j : Fin n) : Fin K → HeadMove K :=
  fun h => if h = blk j then .succ h else if ∃ i, j < i ∧ h = blk i then .toMin else .stay

/-- The fragments of an increment. -/
noncomputable def lexFam {n : ℕ} (blk : Fin n → Fin K) (mk : Fin K) :
    LexNode n → HeadProgram L K
  | .test j => match testPos j with
      | none => exitP false
      | some p => leafP (HeadMove.eqVarF L (blk p) mk) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .bump j => moveP (bumpMoves blk j)

/-- **The odometer**: replace the tuple on the block by its lexicographic
successor, exiting `false` when every position is at the marker. -/
noncomputable def lexNextP {n : ℕ} (blk : Fin n → Fin K) (mk : Fin K) : HeadProgram L K :=
  wireP (lexFam (L := L) blk mk) lexWire (.test ⟨n, Nat.lt_succ_self n⟩)

section Runs

variable {A : Type} [L.Structure A] [LinearOrder A] {n : ℕ}

/-- **What an increment runs**, stated by the marker's value rather than by
maximality: either some position is away from the marker – the last such one is
stepped and the positions after it are reset – or all of them are at it and the
increment fails. -/
def lexRel (blk : Fin n → Fin K) (mk : Fin K) (prot : ℕ) :
    (Fin K → A) → Bool → (Fin K → A) → Prop := fun x b y =>
  (b = true ∧ ∃ p : Fin n, x (blk p) ≠ x mk ∧
      (∀ i, p < i → x (blk i) = x mk) ∧
      (∀ i, i < p → y (blk i) = x (blk i)) ∧
      (x (blk p) < y (blk p) ∧ ∀ e : A, ¬(x (blk p) < e ∧ e < y (blk p))) ∧
      (∀ i, p < i → ∀ a : A, y (blk i) ≤ a) ∧
      ∀ j : Fin K, (j : ℕ) < prot → (∀ i, j ≠ blk i) → y j = x j) ∨
    (b = false ∧ (∀ i : Fin n, x (blk i) = x mk) ∧ HeadAgree prot x y)

/-- The relations the fragments of an increment run. -/
def lexFamRel (blk : Fin n → Fin K) (mk : Fin K) (prot : ℕ) :
    LexNode n → (Fin K → A) → Bool → (Fin K → A) → Prop
  | .test j => match testPos j with
      | none => fun x b y => b = false ∧ HeadAgree prot x y
      | some p => fun x b y => (b = true ↔ x (blk p) = x mk) ∧ HeadAgree prot x y
  | .bump j => fun x b y => b = true ∧
      ∀ h : Fin K, (h : ℕ) < prot → (bumpMoves blk j h).Holds x h (y h)

/-! ### What the increment runs -/

variable (blk : Fin n → Fin K) (mk : Fin K) (prot : ℕ)

theorem runs_lexFam (hblk : ∀ i, ((blk i : Fin K) : ℕ) < prot) (c : LexNode n) :
    (lexFam (L := L) blk mk c).Runs A prot (lexFamRel blk mk prot c) := by
  cases c with
  | test j =>
    rcases hp : testPos j with _ | p
    · simp only [lexFam, lexFamRel, hp]
      exact runs_exitP_local false prot
    · simp only [lexFam, lexFamRel, hp]
      exact (decides_leafP _ _).congr fun x => by simp
  | bump j =>
    refine runs_moveP_local _ _ fun h hh => ?_
    have h1 : h ≠ blk j := fun he => by
      rw [he] at hh
      exact absurd (hblk j) (by omega)
    have h2 : ¬∃ i, j < i ∧ h = blk i := by
      rintro ⟨i, -, rfl⟩
      exact absurd (hblk i) (by omega)
    rw [bumpMoves, if_neg h1, if_neg h2]

theorem headLocal2_lexFamRel (hblk : ∀ i, ((blk i : Fin K) : ℕ) < prot) (hmk : (mk : ℕ) < prot)
    (c : LexNode n) : HeadLocal2 prot (lexFamRel (A := A) blk mk prot c) := by
  cases c with
  | test j =>
    rcases hp : testPos j with _ | p
    · simp only [lexFamRel, hp]
      exact headLocal2_exitP false prot
    · simp only [lexFamRel, hp]
      refine headLocal2_decides fun x x' hx => ?_
      rw [hx _ (hblk p), hx _ hmk]
  | bump j =>
    refine headLocal2_moveP fun h hh => ?_
    rw [bumpMoves]
    by_cases h1 : h = blk j
    · rw [if_pos h1]
      exact hh
    · rw [if_neg h1]
      by_cases h2 : ∃ i, j < i ∧ h = blk i
      · rw [if_pos h2]
        trivial
      · rw [if_neg h2]
        trivial

theorem lexRel_local (hblk : ∀ i, ((blk i : Fin K) : ℕ) < prot) (hmk : (mk : ℕ) < prot) :
    HeadLocal2 prot (lexRel (A := A) blk mk prot) := by
  intro x x' y y' hx hy b
  have hxb : ∀ i, x (blk i) = x' (blk i) := fun i => hx _ (hblk i)
  have hyb : ∀ i, y (blk i) = y' (blk i) := fun i => hy _ (hblk i)
  have hxm : x mk = x' mk := hx _ hmk
  constructor
  · rintro (⟨rfl, p, h1, h2, h3, h4, h5, h6⟩ | ⟨rfl, h1, h2⟩)
    · exact Or.inl ⟨rfl, p, by rw [← hxb, ← hxm]; exact h1,
        fun i hi => by rw [← hxb, ← hxm]; exact h2 i hi,
        fun i hi => by rw [← hyb, ← hxb]; exact h3 i hi,
        by rw [← hxb, ← hyb]; exact h4,
        fun i hi => by rw [← hyb]; exact h5 i hi,
        fun j hj hjb => by rw [← hy j hj, ← hx j hj]; exact h6 j hj hjb⟩
    · exact Or.inr ⟨rfl, fun i => by rw [← hxb, ← hxm]; exact h1 i, hx.symm.trans (h2.trans hy)⟩
  · rintro (⟨rfl, p, h1, h2, h3, h4, h5, h6⟩ | ⟨rfl, h1, h2⟩)
    · exact Or.inl ⟨rfl, p, by rw [hxb, hxm]; exact h1,
        fun i hi => by rw [hxb, hxm]; exact h2 i hi,
        fun i hi => by rw [hyb, hxb]; exact h3 i hi,
        by rw [hxb, hyb]; exact h4,
        fun i hi => by rw [hyb]; exact h5 i hi,
        fun j hj hjb => by rw [hy j hj, hx j hj]; exact h6 j hj hjb⟩
    · exact Or.inr ⟨rfl, fun i => by rw [hxb, hxm]; exact h1 i, hx.trans (h2.trans hy.symm)⟩

/-! ### The walk of an increment -/

/-- What the increment runs once the positions from `jj` on are known to be at
the marker: the stepped position is one of those left. -/
def lexRelFrom (blk : Fin n → Fin K) (mk : Fin K) (prot : ℕ) (jj : ℕ) :
    (Fin K → A) → Bool → (Fin K → A) → Prop := fun x b y =>
  (b = true ∧ ∃ p : Fin n, (p : ℕ) < jj ∧ x (blk p) ≠ x mk ∧
      (∀ i, p < i → x (blk i) = x mk) ∧
      (∀ i, i < p → y (blk i) = x (blk i)) ∧
      (x (blk p) < y (blk p) ∧ ∀ e : A, ¬(x (blk p) < e ∧ e < y (blk p))) ∧
      (∀ i, p < i → ∀ a : A, y (blk i) ≤ a) ∧
      ∀ j : Fin K, (j : ℕ) < prot → (∀ i, j ≠ blk i) → y j = x j) ∨
    (b = false ∧ (∀ i : Fin n, x (blk i) = x mk) ∧ HeadAgree prot x y)

theorem lexRelFrom_all {x : Fin K → A} {b : Bool} {y : Fin K → A} :
    lexRelFrom blk mk prot n x b y ↔ lexRel blk mk prot x b y := by
  constructor
  · rintro (⟨rfl, p, -, hrest⟩ | h)
    · exact Or.inl ⟨rfl, p, hrest⟩
    · exact Or.inr h
  · rintro (⟨rfl, p, hrest⟩ | h)
    · exact Or.inl ⟨rfl, p, p.isLt, hrest⟩
    · exact Or.inr h

theorem lexRelFrom_mono {jj jj' : ℕ} (h : jj ≤ jj') {x : Fin K → A} {b : Bool} {y : Fin K → A}
    (hr : lexRelFrom blk mk prot jj x b y) : lexRelFrom blk mk prot jj' x b y := by
  rcases hr with ⟨rfl, p, hp, hrest⟩ | h'
  · exact Or.inl ⟨rfl, p, lt_of_lt_of_le hp h, hrest⟩
  · exact Or.inr h'

theorem lexRelFrom_local (hblk : ∀ i, ((blk i : Fin K) : ℕ) < prot) (hmk : (mk : ℕ) < prot)
    (jj : ℕ) : HeadLocal2 prot (lexRelFrom (A := A) blk mk prot jj) := by
  intro x x' y y' hx hy b
  have hxb : ∀ i, x (blk i) = x' (blk i) := fun i => hx _ (hblk i)
  have hyb : ∀ i, y (blk i) = y' (blk i) := fun i => hy _ (hblk i)
  have hxm : x mk = x' mk := hx _ hmk
  constructor
  · rintro (⟨rfl, p, hp, h1, h2, h3, h4, h5, h6⟩ | ⟨rfl, h1, h2⟩)
    · exact Or.inl ⟨rfl, p, hp, by rw [← hxb, ← hxm]; exact h1,
        fun i hi => by rw [← hxb, ← hxm]; exact h2 i hi,
        fun i hi => by rw [← hyb, ← hxb]; exact h3 i hi,
        by rw [← hxb, ← hyb]; exact h4,
        fun i hi => by rw [← hyb]; exact h5 i hi,
        fun j hj hjb => by rw [← hy j hj, ← hx j hj]; exact h6 j hj hjb⟩
    · exact Or.inr ⟨rfl, fun i => by rw [← hxb, ← hxm]; exact h1 i, hx.symm.trans (h2.trans hy)⟩
  · rintro (⟨rfl, p, hp, h1, h2, h3, h4, h5, h6⟩ | ⟨rfl, h1, h2⟩)
    · exact Or.inl ⟨rfl, p, hp, by rw [hxb, hxm]; exact h1,
        fun i hi => by rw [hxb, hxm]; exact h2 i hi,
        fun i hi => by rw [hyb, hxb]; exact h3 i hi,
        by rw [hxb, hyb]; exact h4,
        fun i hi => by rw [hyb]; exact h5 i hi,
        fun j hj hjb => by rw [hy j hj, hx j hj]; exact h6 j hj hjb⟩
    · exact Or.inr ⟨rfl, fun i => by rw [hxb, hxm]; exact h1 i, hx.trans (h2.trans hy.symm)⟩

/-- Abbreviation for the walk of an increment. -/
def LexExit (blk : Fin n → Fin K) (mk : Fin K) (prot : ℕ) (jj : ℕ) (hjj : jj < n + 1)
    (x : Fin K → A) (b : Bool) (y : Fin K → A) : Prop :=
  ∃ u, Relation.ReflTransGen (wireStep (lexFamRel (A := A) blk mk prot) lexWire)
      ((.test ⟨jj, hjj⟩ : LexNode n), x) u ∧ wireExit (lexFamRel blk mk prot) lexWire u b y

variable {blk mk prot}

/-- **Soundness of the increment**: every exit is the one the relation
describes. -/
theorem lexSound (hinj : Function.Injective blk) (hblk : ∀ i, ((blk i : Fin K) : ℕ) < prot)
    (hmk : (mk : ℕ) < prot) :
    ∀ (jj : ℕ) (hjj : jj < n + 1) (x : Fin K → A),
      (∀ i : Fin n, jj ≤ (i : ℕ) → x (blk i) = x mk) →
      ∀ b y, LexExit blk mk prot jj hjj x b y → lexRelFrom blk mk prot jj x b y := by
  intro jj
  induction jj with
  | zero =>
    rintro hjj x hinv b y ⟨u, hwalk, hexit⟩
    have hnone : testPos (⟨0, hjj⟩ : Fin (n + 1)) = none := testPos_eq_none rfl
    rcases Relation.ReflTransGen.cases_head hwalk with rfl | ⟨v, hstep, -⟩
    · obtain ⟨b', hR, hw⟩ := hexit
      simp only [lexFamRel, hnone] at hR
      obtain ⟨rfl, hag⟩ := hR
      have hb : b = false := by
        have : lexWire (n := n) (.test ⟨0, hjj⟩) false = Sum.inr b := hw
        rw [lexWire, hnone] at this
        exact (Sum.inr.inj this).symm
      exact Or.inr ⟨hb, fun i => hinv i (Nat.zero_le _), hag⟩
    · obtain ⟨b₁, -, hw⟩ := hstep
      have : lexWire (n := n) (.test ⟨0, hjj⟩) b₁ = Sum.inl v.1 := hw
      rw [lexWire, hnone] at this
      exact absurd this (by simp)
  | succ j ih =>
    rintro hjj x hinv b y ⟨u, hwalk, hexit⟩
    have hj : j < n := by omega
    have hsome : testPos (⟨j + 1, hjj⟩ : Fin (n + 1)) = some ⟨j, hj⟩ := testPos_eq_some rfl hj
    have hdown : ((testDown (⟨j + 1, hjj⟩ : Fin (n + 1)) : Fin (n + 1)) : ℕ) = j := testDown_val rfl
    rcases Relation.ReflTransGen.cases_head hwalk with rfl | ⟨v, hstep, hrest⟩
    · obtain ⟨b', -, hw⟩ := hexit
      have : lexWire (n := n) (.test ⟨j + 1, hjj⟩) b' = Sum.inr b := hw
      rw [lexWire, hsome] at this
      cases b' <;> simp at this
    · obtain ⟨b₁, hR, hw⟩ := hstep
      simp only [lexFamRel, hsome] at hR
      obtain ⟨hiff, hag⟩ : (b₁ = true ↔ x (blk ⟨j, hj⟩) = x mk) ∧ HeadAgree prot x v.2 := hR
      have hwire : lexWire (n := n) (.test ⟨j + 1, hjj⟩) b₁ = Sum.inl v.1 := hw
      rw [lexWire, hsome] at hwire
      cases b₁ with
      | true =>
        have hv1 : v.1 = LexNode.test (testDown ⟨j + 1, hjj⟩) := by
          simpa using (Sum.inl.inj hwire).symm
        have hinv' : ∀ i : Fin n, j ≤ (i : ℕ) → v.2 (blk i) = v.2 mk := by
          intro i hi
          rw [← hag _ (hblk i), ← hag _ hmk]
          rcases eq_or_lt_of_le hi with he | hlt
          · have hie : i = ⟨j, hj⟩ := Fin.ext he.symm
            rw [hie]
            exact hiff.mp rfl
          · exact hinv i (by omega)
        rw [← Prod.mk.eta (p := v), hv1] at hrest
        have hdowneq : testDown (⟨j + 1, hjj⟩ : Fin (n + 1)) = (⟨j, by omega⟩ : Fin (n + 1)) :=
          Fin.ext (by rw [hdown])
        rw [hdowneq] at hrest
        have hres := ih (by omega) v.2 hinv' b y ⟨u, hrest, hexit⟩
        exact lexRelFrom_mono blk mk prot (Nat.le_succ j)
          ((lexRelFrom_local (A := A) blk mk prot hblk hmk j x v.2 y y hag
            (HeadAgree.refl y) b).mpr hres)
      | false =>
        have hv1 : v.1 = LexNode.bump ⟨j, hj⟩ := by simpa using (Sum.inl.inj hwire).symm
        have hxne : x (blk ⟨j, hj⟩) ≠ x mk := fun he => by simpa using hiff.mpr he
        rw [← Prod.mk.eta (p := v), hv1] at hrest
        rcases Relation.ReflTransGen.cases_head hrest with rfl | ⟨w, hstep2, -⟩
        · obtain ⟨b', hR2, hw2⟩ := hexit
          obtain ⟨-, hmv⟩ : b' = true ∧ ∀ h : Fin K, (h : ℕ) < prot →
              (bumpMoves blk ⟨j, hj⟩ h).Holds v.2 h (y h) := hR2
          have hb : b = true := by
            have : lexWire (n := n) (.bump ⟨j, hj⟩) b' = Sum.inr b := hw2
            rw [lexWire] at this
            exact (Sum.inr.inj this).symm
          refine Or.inl ⟨hb, ⟨j, hj⟩, Nat.lt_succ_self j, hxne,
            fun i hi => hinv i (show j + 1 ≤ (i : ℕ) from hi), ?_, ?_, ?_, ?_⟩
          · intro i hi
            have hne : blk i ≠ blk ⟨j, hj⟩ := fun he => absurd (hinj he) (ne_of_lt hi)
            have hne2 : ¬∃ i', (⟨j, hj⟩ : Fin n) < i' ∧ blk i = blk i' := by
              rintro ⟨i', hlt, he⟩
              rw [hinj he] at hi
              exact absurd (lt_trans hi hlt) (lt_irrefl _)
            have hx := hmv (blk i) (hblk i)
            rw [bumpMoves, if_neg hne, if_neg hne2] at hx
            rw [hx, hag _ (hblk i)]
          · have hx := hmv (blk ⟨j, hj⟩) (hblk _)
            rw [bumpMoves, if_pos rfl] at hx
            rw [hag (blk ⟨j, hj⟩) (hblk _)]
            exact hx
          · intro i hi
            have hne : blk i ≠ blk ⟨j, hj⟩ := fun he => absurd (hinj he) (ne_of_gt hi)
            have hx := hmv (blk i) (hblk i)
            rw [bumpMoves, if_neg hne, if_pos ⟨i, hi, rfl⟩] at hx
            exact hx
          · intro jh hjh hnb
            have hne : jh ≠ blk ⟨j, hj⟩ := hnb _
            have hne2 : ¬∃ i', (⟨j, hj⟩ : Fin n) < i' ∧ jh = blk i' := by
              rintro ⟨i', -, he⟩
              exact hnb i' he
            have hx := hmv jh hjh
            rw [bumpMoves, if_neg hne, if_neg hne2] at hx
            rw [hx, hag jh hjh]
        · obtain ⟨b₂, -, hw2⟩ := hstep2
          have : lexWire (n := n) (.bump ⟨j, hj⟩) b₂ = Sum.inl w.1 := hw2
          rw [lexWire] at this
          exact absurd this (by simp)

open Classical in
/-- The tuple an increment produces at position `p`: the stepped and reset
positions taken from the outcome, everything else left where it was. -/
noncomputable def bumpTuple (blk : Fin n → Fin K) (p : Fin n) (x y : Fin K → A) :
    Fin K → A :=
  fun h => if h = blk p then y (blk p) else if ∃ i, p < i ∧ h = blk i then y h else x h

omit [LinearOrder A] in
theorem bumpTuple_at (blk : Fin n → Fin K) (p : Fin n) (x y : Fin K → A) :
    bumpTuple blk p x y (blk p) = y (blk p) := by
  classical
  rw [bumpTuple, if_pos rfl]

omit [LinearOrder A] in
theorem bumpTuple_after (blk : Fin n → Fin K) {p i : Fin n} (hi : p < i) (x y : Fin K → A)
    (hinj : Function.Injective blk) : bumpTuple blk p x y (blk i) = y (blk i) := by
  classical
  rw [bumpTuple, if_neg (fun he => absurd (hinj he) (ne_of_gt hi)), if_pos ⟨i, hi, rfl⟩]

omit [LinearOrder A] in
theorem bumpTuple_before (blk : Fin n → Fin K) {p i : Fin n} (hi : i < p) (x y : Fin K → A)
    (hinj : Function.Injective blk) : bumpTuple blk p x y (blk i) = x (blk i) := by
  classical
  rw [bumpTuple, if_neg (fun he => absurd (hinj he) (ne_of_lt hi)),
    if_neg (by
      rintro ⟨i', hi', he⟩
      rw [hinj he] at hi
      exact absurd (lt_trans hi hi') (lt_irrefl _))]

omit [LinearOrder A] in
theorem bumpTuple_out (blk : Fin n → Fin K) (p : Fin n) (x y : Fin K → A) {h : Fin K}
    (hh : ∀ i, h ≠ blk i) : bumpTuple blk p x y h = x h := by
  classical
  rw [bumpTuple, if_neg (hh p), if_neg (by rintro ⟨i, -, he⟩; exact hh i he)]

/-- **Completeness of the increment**: the outcome the relation describes is
reached. -/
theorem lexComplete (hinj : Function.Injective blk) (_hblk : ∀ i, ((blk i : Fin K) : ℕ) < prot)
    (_hmk : (mk : ℕ) < prot) :
    ∀ (jj : ℕ) (hjj : jj < n + 1) (x : Fin K → A),
      (∀ i : Fin n, jj ≤ (i : ℕ) → x (blk i) = x mk) →
      ∀ b y, lexRelFrom blk mk prot jj x b y →
        ∃ y', HeadAgree prot y y' ∧ LexExit blk mk prot jj hjj x b y' := by
  intro jj
  induction jj with
  | zero =>
    rintro hjj x hinv b y (⟨-, p, hp, -⟩ | ⟨rfl, -, hag⟩)
    · omega
    · have hnone : testPos (⟨0, hjj⟩ : Fin (n + 1)) = none := testPos_eq_none rfl
      refine ⟨x, hag.symm, ((.test ⟨0, hjj⟩ : LexNode n), x), Relation.ReflTransGen.refl,
        false, ?_, ?_⟩
      · simp only [lexFamRel, hnone]
        exact ⟨by trivial, HeadAgree.refl x⟩
      · rw [lexWire, hnone]
  | succ j ih =>
    intro hjj x hinv b y hr
    have hj : j < n := by omega
    have hsome : testPos (⟨j + 1, hjj⟩ : Fin (n + 1)) = some ⟨j, hj⟩ := testPos_eq_some rfl hj
    have hdowneq : testDown (⟨j + 1, hjj⟩ : Fin (n + 1)) = (⟨j, by omega⟩ : Fin (n + 1)) :=
      Fin.ext (by rw [testDown_val rfl])
    -- the step that walks one position down, taken when that position is at the marker
    have hdown : ∀ (hat : x (blk ⟨j, hj⟩) = x mk) (b' : Bool) (y' : Fin K → A),
        LexExit blk mk prot j (by omega) x b' y' → LexExit blk mk prot (j + 1) hjj x b' y' := by
      rintro hat b' y' ⟨u, hwalk, hexit⟩
      refine ⟨u, Relation.ReflTransGen.head (b := ((.test ⟨j, by omega⟩ : LexNode n), x))
        ⟨true, ?_, ?_⟩ hwalk, hexit⟩
      · simp only [lexFamRel, hsome]
        exact ⟨⟨fun _ => hat, fun _ => by trivial⟩, HeadAgree.refl x⟩
      · rw [lexWire, hsome]
        simp only [if_pos]
        exact congrArg Sum.inl (congrArg LexNode.test hdowneq)
    rcases hr with ⟨rfl, p, hp, hne, habove, hbefore, hcover, hafter, hother⟩ | ⟨rfl, hall, hag⟩
    · rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hp) with hpj | hpj
      · -- the stepped position is this one
        have hpe : p = ⟨j, hj⟩ := Fin.ext hpj
        rw [hpe] at hne habove hbefore hcover hafter
        refine ⟨bumpTuple blk ⟨j, hj⟩ x y, ?_, ?_⟩
        · intro h hh
          by_cases h1 : h = blk ⟨j, hj⟩
          · rw [h1, bumpTuple_at]
          · by_cases h2 : ∃ i, (⟨j, hj⟩ : Fin n) < i ∧ h = blk i
            · obtain ⟨i, hi, rfl⟩ := h2
              rw [bumpTuple_after blk hi x y hinj]
            · by_cases h3 : ∃ i, h = blk i
              · obtain ⟨i, rfl⟩ := h3
                have hlt : i < (⟨j, hj⟩ : Fin n) := by
                  rcases lt_trichotomy i ⟨j, hj⟩ with hlt | rfl | hgt
                  · exact hlt
                  · exact absurd rfl h1
                  · exact absurd ⟨i, hgt, rfl⟩ h2
                rw [bumpTuple_before blk hlt x y hinj]
                exact hbefore i hlt
              · rw [bumpTuple_out blk _ x y fun i he => h3 ⟨i, he⟩]
                exact hother h hh fun i he => h3 ⟨i, he⟩
        · refine ⟨((.bump ⟨j, hj⟩ : LexNode n), x), Relation.ReflTransGen.single ⟨false, ?_, ?_⟩,
            true, ⟨rfl, ?_⟩, ?_⟩
          · simp only [lexFamRel, hsome]
            exact ⟨⟨fun hc => absurd hc (by simp), fun hc => absurd hc hne⟩, HeadAgree.refl x⟩
          · rw [lexWire, hsome]
            simp
          · intro h hh
            rw [bumpMoves]
            by_cases h1 : h = blk ⟨j, hj⟩
            · rw [if_pos h1, h1, bumpTuple_at]
              exact hcover
            · rw [if_neg h1]
              by_cases h2 : ∃ i, (⟨j, hj⟩ : Fin n) < i ∧ h = blk i
              · obtain ⟨i, hi, rfl⟩ := h2
                rw [if_pos ⟨i, hi, rfl⟩, bumpTuple_after blk hi x y hinj]
                exact hafter i hi
              · rw [if_neg h2]
                by_cases h3 : ∃ i, h = blk i
                · obtain ⟨i, rfl⟩ := h3
                  have hlt : i < (⟨j, hj⟩ : Fin n) := by
                    rcases lt_trichotomy i ⟨j, hj⟩ with hlt | rfl | hgt
                    · exact hlt
                    · exact absurd rfl h1
                    · exact absurd ⟨i, hgt, rfl⟩ h2
                  exact bumpTuple_before blk hlt x y hinj
                · exact bumpTuple_out blk _ x y fun i he => h3 ⟨i, he⟩
          · rw [lexWire]
      · -- the stepped position is further down
        have hinv' : ∀ i : Fin n, j ≤ (i : ℕ) → x (blk i) = x mk := by
          intro i hi
          exact habove i (show (p : ℕ) < (i : ℕ) from lt_of_lt_of_le hpj hi)
        obtain ⟨y', hag', hexit⟩ := ih (by omega) x hinv' true y
          (Or.inl ⟨rfl, p, by omega, hne, habove, hbefore, hcover, hafter, hother⟩)
        exact ⟨y', hag', hdown (habove ⟨j, hj⟩ hpj) _ _ hexit⟩
    · obtain ⟨y', hag', hexit⟩ := ih (by omega) x (fun i _ => hall i) false y
        (Or.inr ⟨rfl, hall, hag⟩)
      exact ⟨y', hag', hdown (hall ⟨j, hj⟩) _ _ hexit⟩

/-! ### The odometer -/

/-- **What the odometer runs**: the lexicographic successor of the tuple on the
block, read through the marker. -/
theorem runs_lexNextP (hinj : Function.Injective blk) (hblk : ∀ i, ((blk i : Fin K) : ℕ) < prot)
    (hmk : (mk : ℕ) < prot) :
    (lexNextP (L := L) blk mk).Runs A prot (lexRel blk mk prot) := by
  refine (runs_wireP (C := LexNode n) (lexFam blk mk) lexWire
    (runs_lexFam (A := A) blk mk prot hblk) (headLocal2_lexFamRel (A := A) blk mk prot hblk hmk)
    (.test ⟨n, Nat.lt_succ_self n⟩)).mono ?_ ?_
  · intro x b y hr
    exact (lexRelFrom_all blk mk prot).mp (lexSound hinj hblk hmk n (Nat.lt_succ_self n) x
      (fun i hi => absurd i.isLt (by omega)) b y hr)
  · intro x b y hr
    exact lexComplete hinj hblk hmk n (Nat.lt_succ_self n) x
      (fun i hi => absurd i.isLt (by omega)) b y ((lexRelFrom_all blk mk prot).mpr hr)

theorem deterministic_lexNextP : (lexNextP (L := L) blk mk).Deterministic A := by
  refine deterministic_wireP _ _ _ ?_
  rintro (j | j)
  · rcases hp : testPos j with _ | p
    · simp only [lexFam, hp]
      exact deterministic_exitP false
    · simp only [lexFam, hp]
      exact deterministic_leafP _ _
  · exact deterministic_moveP _

/-! ### Reading the increment as a lexicographic step -/

variable {x y : Fin K → A}

/-- Where the marker holds the greatest element, a successful increment is the
lexicographic successor. -/
theorem tupSucc_of_lexRel (hmax : ∀ a : A, a ≤ x mk) (h : lexRel blk mk prot x true y) :
    TupSucc (fun i => x (blk i)) fun i => y (blk i) := by
  rcases h with ⟨-, p, -, habove, hbefore, hcover, hafter, -⟩ | ⟨hcon, -⟩
  · exact ⟨p, fun i hi => (hbefore i hi).symm, hcover,
      fun i hi => ⟨fun a => by
        change a ≤ x (blk i)
        rw [habove i hi]
        exact hmax a, hafter i hi⟩⟩
  · exact absurd hcon (by simp)

open Classical in
/-- **The increment can always be taken where the tuple is not the greatest**:
the outcome the relation describes exists. -/
theorem exists_lexRel_succ [Finite A] (hinj : Function.Injective blk)
    (hmax : ∀ a : A, a ≤ x mk) (hnotTop : ¬∀ (i : Fin n) (a : A), a ≤ x (blk i)) :
    ∃ y, lexRel blk mk prot x true y ∧ TupSucc (fun i => x (blk i)) (fun i => y (blk i)) ∧
      ∀ j : Fin K, (j : ℕ) < prot → (∀ i, j ≠ blk i) → y j = x j := by
  have hnt : ¬∀ u : Lex (Fin n → A), u ≤ toLex fun i => x (blk i) := fun hcon =>
    hnotTop (tup_isTop_iff.mp hcon)
  obtain ⟨u', hlt, hnb'⟩ := exists_gt_of_not_max hnt
  have hcov : (toLex fun i => x (blk i)) ⋖ u' := ⟨hlt, fun c h1 h2 => hnb' c ⟨h1, h2⟩⟩
  obtain ⟨p, hbefore, hcover, hafter⟩ := tupSucc_iff_covBy.mpr hcov
  refine ⟨fun j => if h : ∃ i, j = blk i then (ofLex u') h.choose else x j, ?_, ?_, ?_⟩
  all_goals
    have hyb : ∀ i : Fin n,
        (fun j => if h : ∃ i, j = blk i then (ofLex u') h.choose else x j) (blk i)
          = (ofLex u') i := by
      intro i
      change (if h : ∃ i', blk i = blk i' then (ofLex u') h.choose else x (blk i)) = (ofLex u') i
      rw [dif_pos ⟨i, rfl⟩]
      exact congrArg _ (hinj (Exists.choose_spec (⟨i, rfl⟩ : ∃ i', blk i = blk i')).symm)
    have hyo : ∀ j : Fin K, (∀ i, j ≠ blk i) →
        (fun j => if h : ∃ i, j = blk i then (ofLex u') h.choose else x j) j = x j := by
      intro j hj
      change (if h : ∃ i, j = blk i then (ofLex u') h.choose else x j) = x j
      rw [dif_neg (by rintro ⟨i, hi⟩; exact hj i hi)]
    first
      | (refine Or.inl ⟨rfl, p, ?_, ?_, ?_, ?_, ?_, ?_⟩
         · intro he
           have h1 : (ofLex u') p ≤ x mk := hmax _
           rw [← he] at h1
           exact absurd hcover.1 (not_lt.mpr h1)
         · exact fun i hi => le_antisymm (hmax _) ((hafter i hi).1 (x mk))
         · exact fun i hi => (hyb i).trans (hbefore i hi).symm
         · rw [hyb p]
           exact hcover
         · exact fun i hi a => by rw [hyb i]; exact (hafter i hi).2 a
         · exact fun j hj hjb => hyo j hjb)
      | (exact ⟨p, fun i hi => by rw [hyb i]; exact hbefore i hi, by rw [hyb p]; exact hcover,
          fun i hi => ⟨(hafter i hi).1, by rw [hyb i]; exact (hafter i hi).2⟩⟩)
      | (exact fun j hj hjb => hyo j hjb)

/-- **The increment fails exactly at the greatest tuple**, and then leaves
everything alone. -/
theorem lexRel_top (hmax : ∀ a : A, a ≤ x mk) (hall : ∀ (i : Fin n) (a : A), a ≤ x (blk i)) :
    lexRel blk mk prot x false x :=
  Or.inr ⟨rfl, fun i => le_antisymm (hmax _) (hall i _), HeadAgree.refl x⟩

end Runs

end HeadProgram

end DescriptiveComplexity
