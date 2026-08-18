/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadArith

/-!
# The bit of a rank, as a head program

The fragment `DescriptiveComplexity.HeadProgram.bitP`: a deterministic
multi-head program deciding **`BIT`**, that is, whether the bit of the rank of
one head at the index given by the rank of another is set. It is what lets the
multi-head automaton of `DescriptiveComplexity.HeadEvalArith` evaluate the
bit-level logic of `DescriptiveComplexity.LogTime` – the third arithmetic
fragment, beside `DescriptiveComplexity.HeadProgram.plusP` and
`DescriptiveComplexity.HeadProgram.timesP`.

## The algorithm: halve, then read the parity

`BIT(x, i)` is `(x / 2 ^ i) % 2 = 1`, so the program **halves the value `i`
times and then asks for its parity**. Both loops are the shape this development
already uses: an outer loop counting the rounds, and inside it a *scan* that
walks a candidate up the order asking, at each stop, whether the candidate is
the half of the current value. That question is two additions, so the scan's
probe is an addition fragment – a decider made to compute, exactly as
`timesP`'s scan reuses `plusP`.

The half of `v` is the `c` with `c + c = v` (`v` even) or `c + (c + 1) = v`
(`v` odd), and the two are tested in that order at each candidate, so the scan
stops at the first `c` that works and that `c` is `v / 2` whatever the parity.
The successor `c + 1` is not an addition but a head: the program moves `w` to
the successor of the candidate, which is why the overflow test comes *before*
that move – a successor move at the greatest element is disabled, and the walk
would be stuck rather than wrong.

## The parity, and why it needs no guard

After the last round the value is `x / 2 ^ i`, and its parity is read by a
second scan: `v` is **even** exactly when some `c` has `c + c = v`, and such a
`c` is `v / 2 ≤ v`, so the scan finds it if it exists. The scan therefore
answers `false` at the first candidate that halves `v`, and `true` when it
reaches the marker having found none. No test against zero is needed anywhere,
which is what makes the two scans the same four nodes with different exits.

## What the fragment costs

Five working heads – the value, the round counter, the scan's candidate, the
successor `w`, and the scan's marker – above the interface, and the addition's
own three scratch heads above those; the marker is parked by the fragment
itself, as `plusP`'s is, so a caller has no discipline to keep beyond the head
layout `DescriptiveComplexity.HeadProgram.BitHeads`. The clock is
`O(log n)` rounds of a scan, hence `O(n log n)` steps – irrelevant to the space
bound, which is the number of heads.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

namespace HeadProgram

variable {L : Language.{0, 0}} {K : ℕ}

/-! ### The control graph of a bit -/

/-- The control nodes of a bit: an outer loop counting the halvings, a scan
looking for the half of the current value, and a second scan reading the parity
of the value the outer loop leaves. -/
inductive BitNode
  /-- Copy the value onto the working head, the round counter to the least
  element and the scan's marker to the greatest. -/
  | init : BitNode
  /-- Has the round counter reached the index? -/
  | outer : BitNode
  /-- It has not: start the scan at the least element. -/
  | scanInit : BitNode
  /-- Is the candidate twice itself the value, that is, is the value even with
  this half? -/
  | probeE : BitNode
  /-- It is not: is the candidate at the marker, i.e., is the scan over? -/
  | scanOver : BitNode
  /-- It is not: put `w` on the successor of the candidate. -/
  | mkW : BitNode
  /-- Is the candidate plus its successor the value, that is, is the value odd
  with this half? -/
  | probeO : BitNode
  /-- Step the candidate. -/
  | scanStep : BitNode
  /-- The candidate is the half: take it, and count the round. -/
  | commit : BitNode
  /-- The rounds are over: start the parity scan. -/
  | parInit : BitNode
  /-- Does the candidate halve the value, that is, is the value even? -/
  | parProbe : BitNode
  /-- It does not: is the parity scan over? -/
  | parOver : BitNode
  /-- Step the parity scan's candidate. -/
  | parStep : BitNode
  deriving DecidableEq

instance : Finite BitNode := by
  refine Finite.of_injective (fun c : BitNode => match c with
      | .init => (0 : Fin 13)
      | .outer => 1
      | .scanInit => 2
      | .probeE => 3
      | .scanOver => 4
      | .mkW => 5
      | .probeO => 6
      | .scanStep => 7
      | .commit => 8
      | .parInit => 9
      | .parProbe => 10
      | .parOver => 11
      | .parStep => 12) ?_
  rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _)
    (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) h <;>
    first
      | rfl
      | exact absurd h (by decide)

/-- The wiring of a bit: the outer loop `outer → scan → commit → outer`, the
scan `probeE → scanOver → mkW → probeO → scanStep → probeE`, and the parity scan
`parProbe → parOver → parStep → parProbe` carrying the two answers. -/
def bitWire : BitNode → Bool → BitNode ⊕ Bool
  | .init, _ => Sum.inl .outer
  | .outer, c => if c then Sum.inl .parInit else Sum.inl .scanInit
  | .scanInit, _ => Sum.inl .probeE
  | .probeE, c => if c then Sum.inl .commit else Sum.inl .scanOver
  | .scanOver, c => if c then Sum.inr false else Sum.inl .mkW
  | .mkW, _ => Sum.inl .probeO
  | .probeO, c => if c then Sum.inl .commit else Sum.inl .scanStep
  | .scanStep, _ => Sum.inl .probeE
  | .commit, _ => Sum.inl .outer
  | .parInit, _ => Sum.inl .parProbe
  | .parProbe, c => if c then Sum.inr false else Sum.inl .parOver
  | .parOver, c => if c then Sum.inr true else Sum.inl .parStep
  | .parStep, _ => Sum.inl .parProbe

open Classical in
/-- The moves that start a bit: the working head copies the value, the round
counter goes to the least element, and the scan's marker is parked at the
greatest. -/
noncomputable def bitInitMoves (xh y cnt tmk : Fin K) : Fin K → HeadMove K :=
  fun h => if h = y then .copy xh else if h = cnt then .toMin else
    if h = tmk then .toMax else .stay

open Classical in
/-- The move that starts a scan: the candidate to the least element. -/
noncomputable def bitScanInitMoves (cand : Fin K) : Fin K → HeadMove K :=
  fun h => if h = cand then .toMin else .stay

open Classical in
/-- The move of one scan step: the candidate advances. -/
noncomputable def bitStepMoves (cand : Fin K) : Fin K → HeadMove K :=
  fun h => if h = cand then .succ cand else .stay

open Classical in
/-- The move that prepares the odd probe: `w` takes the successor of the
candidate. It is guarded by the overflow test, a successor move at the greatest
element being disabled. -/
noncomputable def bitWMoves (cand w : Fin K) : Fin K → HeadMove K :=
  fun h => if h = w then .succ cand else .stay

open Classical in
/-- The moves that close a round: the working head takes the half the scan
found, and the round counter advances. -/
noncomputable def bitCommitMoves (y cnt cand : Fin K) : Fin K → HeadMove K :=
  fun h => if h = y then .copy cand else if h = cnt then .succ cnt else .stay

/-- The fragments of a bit. The two probes are addition programs
(`DescriptiveComplexity.HeadProgram.plusP`): `probeE` asks whether the candidate
doubles to the value, `probeO` whether the candidate plus its successor does. -/
noncomputable def bitFam (ih xh y cnt cand w tmk a b mk : Fin K) :
    BitNode → HeadProgram L K
  | .init => moveP (bitInitMoves xh y cnt tmk)
  | .outer => leafP (HeadMove.eqVarF L cnt ih) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .scanInit => moveP (bitScanInitMoves cand)
  | .probeE => plusP cand cand y a b mk
  | .scanOver => leafP (HeadMove.eqVarF L cand tmk) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .mkW => moveP (bitWMoves cand w)
  | .probeO => plusP cand w y a b mk
  | .scanStep => moveP (bitStepMoves cand)
  | .commit => moveP (bitCommitMoves y cnt cand)
  | .parInit => moveP (bitScanInitMoves cand)
  | .parProbe => plusP cand cand y a b mk
  | .parOver => leafP (HeadMove.eqVarF L cand tmk) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .parStep => moveP (bitStepMoves cand)

/-- **The bit**: decide whether the bit of `orank (x xh)` at the index
`orank (x ih)` is set, by halving the value `orank (x ih)` times and reading the
parity of what is left. -/
noncomputable def bitP (ih xh y cnt cand w tmk a b mk : Fin K) : HeadProgram L K :=
  wireP (bitFam (L := L) ih xh y cnt cand w tmk a b mk) bitWire .init

/-! ### The head layout of a bit -/

/-- The head indices a caller of a bit must respect. The two interface heads are
below the caller's level `p`, the five working heads occupy `S` to `S + 4` for
some `S ≥ p`, and the addition's three scratch heads sit at `m = S + 5` – so that
every distinctness the construction needs is an arithmetic fact rather than a
hypothesis. -/
structure BitHeads (ih xh y cnt cand w tmk a b mk : Fin K) (p S m : ℕ) : Prop where
  /-- The index is interface. -/
  hih : (ih : ℕ) < p
  /-- The value is interface. -/
  hxh : (xh : ℕ) < p
  /-- The caller's level is below the fragment's scratch. -/
  hpS : p ≤ S
  /-- The working value sits at `S`. -/
  hy : (y : ℕ) = S
  /-- The round counter sits at `S + 1`. -/
  hcnt : (cnt : ℕ) = S + 1
  /-- The scan's candidate sits at `S + 2`. -/
  hcand : (cand : ℕ) = S + 2
  /-- The candidate's successor sits at `S + 3`. -/
  hw : (w : ℕ) = S + 3
  /-- The scan's marker sits at `S + 4`. -/
  htmk : (tmk : ℕ) = S + 4
  /-- The working heads end where the addition's scratch begins. -/
  hm : m = S + 5
  /-- The addition's running head sits at `m`. -/
  ha : (a : ℕ) = m
  /-- The addition's counter sits at `m + 1`. -/
  hb : (b : ℕ) = m + 1
  /-- The addition's marker sits at `m + 2`. -/
  hmk : (mk : ℕ) = m + 2

namespace BitHeads

variable {ih xh y cnt cand w tmk a b mk : Fin K} {p S m : ℕ}

theorem lt_m_y (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : (y : ℕ) < m := by
  have := h.hy; have := h.hm; omega

theorem lt_m_cnt (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : (cnt : ℕ) < m := by
  have := h.hcnt; have := h.hm; omega

theorem lt_m_cand (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : (cand : ℕ) < m := by
  have := h.hcand; have := h.hm; omega

theorem lt_m_w (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : (w : ℕ) < m := by
  have := h.hw; have := h.hm; omega

theorem lt_m_tmk (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : (tmk : ℕ) < m := by
  have := h.htmk; have := h.hm; omega

theorem lt_m_ih (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : (ih : ℕ) < m := by
  have := h.hih; have := h.hm; have := h.hpS; omega

theorem lt_m_xh (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : (xh : ℕ) < m := by
  have := h.hxh; have := h.hm; have := h.hpS; omega

theorem le_pm (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : p ≤ m := by
  have := h.hm; have := h.hpS; omega

/-- The even probe has the head layout an addition asks for. -/
theorem plusE (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) :
    PlusHeads cand cand y a b mk m where
  hi := h.lt_m_cand
  hj := h.lt_m_cand
  hk := h.lt_m_y
  ha := by have := h.ha; omega
  hb := by have := h.hb; omega
  hmk := by have := h.hmk; omega
  hab := fun he => by have h1 := h.ha; have h2 := h.hb; rw [he] at h1; omega
  hamk := fun he => by have h1 := h.ha; have h2 := h.hmk; rw [he] at h1; omega
  hbmk := fun he => by have h1 := h.hb; have h2 := h.hmk; rw [he] at h1; omega

/-- The odd probe has it too. -/
theorem plusO (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) :
    PlusHeads cand w y a b mk m where
  hi := h.lt_m_cand
  hj := h.lt_m_w
  hk := h.lt_m_y
  ha := by have := h.ha; omega
  hb := by have := h.hb; omega
  hmk := by have := h.hmk; omega
  hab := fun he => by have h1 := h.ha; have h2 := h.hb; rw [he] at h1; omega
  hamk := fun he => by have h1 := h.ha; have h2 := h.hmk; rw [he] at h1; omega
  hbmk := fun he => by have h1 := h.hb; have h2 := h.hmk; rw [he] at h1; omega

/-! #### The distinctness of the working heads, read off their positions -/

theorem ne_y_cnt (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : y ≠ cnt :=
  fun he => by have h1 := h.hy; have h2 := h.hcnt; rw [he] at h1; omega

theorem ne_y_cand (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : y ≠ cand :=
  fun he => by have h1 := h.hy; have h2 := h.hcand; rw [he] at h1; omega

theorem ne_y_w (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : y ≠ w :=
  fun he => by have h1 := h.hy; have h2 := h.hw; rw [he] at h1; omega

theorem ne_y_tmk (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : y ≠ tmk :=
  fun he => by have h1 := h.hy; have h2 := h.htmk; rw [he] at h1; omega

theorem ne_cnt_cand (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : cnt ≠ cand :=
  fun he => by have h1 := h.hcnt; have h2 := h.hcand; rw [he] at h1; omega

theorem ne_cnt_w (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : cnt ≠ w :=
  fun he => by have h1 := h.hcnt; have h2 := h.hw; rw [he] at h1; omega

theorem ne_cnt_tmk (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : cnt ≠ tmk :=
  fun he => by have h1 := h.hcnt; have h2 := h.htmk; rw [he] at h1; omega

theorem ne_cand_w (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : cand ≠ w :=
  fun he => by have h1 := h.hcand; have h2 := h.hw; rw [he] at h1; omega

theorem ne_cand_tmk (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : cand ≠ tmk :=
  fun he => by have h1 := h.hcand; have h2 := h.htmk; rw [he] at h1; omega

theorem ne_w_tmk (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) : w ≠ tmk :=
  fun he => by have h1 := h.hw; have h2 := h.htmk; rw [he] at h1; omega

/-- An interface head is none of the working ones. -/
theorem ne_int (h : BitHeads ih xh y cnt cand w tmk a b mk p S m) {q : Fin K} (hq : (q : ℕ) < p) :
    q ≠ y ∧ q ≠ cnt ∧ q ≠ cand ∧ q ≠ w ∧ q ≠ tmk := by
  have hpS := h.hpS
  refine ⟨fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
  · have := h.hy; rw [he] at hq; omega
  · have := h.hcnt; rw [he] at hq; omega
  · have := h.hcand; rw [he] at hq; omega
  · have := h.hw; rw [he] at hq; omega
  · have := h.htmk; rw [he] at hq; omega

end BitHeads

/-! ### What the fragments of a bit run -/

section BitFam

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {ih xh y cnt cand w tmk a b mk : Fin K} {p S m : ℕ}

/-- The relations the fragments of a bit run, at the level `m` that protects the
working heads and leaves the addition's scratch heads free. -/
noncomputable def bitFamRel (ih xh y cnt cand w tmk : Fin K) (m : ℕ) :
    BitNode → (Fin K → A) → Bool → (Fin K → A) → Prop
  | .init => fun x c z => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (bitInitMoves xh y cnt tmk q).Holds x q (z q)
  | .outer => fun x c z => (c = true ↔ x cnt = x ih) ∧ HeadAgree m x z
  | .scanInit => fun x c z => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (bitScanInitMoves cand q).Holds x q (z q)
  | .probeE => fun x c z =>
      (c = true ↔ orank (x cand) + orank (x cand) = orank (x y)) ∧ HeadAgree m x z
  | .scanOver => fun x c z => (c = true ↔ x cand = x tmk) ∧ HeadAgree m x z
  | .mkW => fun x c z => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (bitWMoves cand w q).Holds x q (z q)
  | .probeO => fun x c z =>
      (c = true ↔ orank (x cand) + orank (x w) = orank (x y)) ∧ HeadAgree m x z
  | .scanStep => fun x c z => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (bitStepMoves cand q).Holds x q (z q)
  | .commit => fun x c z => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (bitCommitMoves y cnt cand q).Holds x q (z q)
  | .parInit => fun x c z => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (bitScanInitMoves cand q).Holds x q (z q)
  | .parProbe => fun x c z =>
      (c = true ↔ orank (x cand) + orank (x cand) = orank (x y)) ∧ HeadAgree m x z
  | .parOver => fun x c z => (c = true ↔ x cand = x tmk) ∧ HeadAgree m x z
  | .parStep => fun x c z => c = true ∧
      ∀ q : Fin K, (q : ℕ) < m → (bitStepMoves cand q).Holds x q (z q)

theorem runs_bitFam (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) (hmK : m ≤ K)
    (c : BitNode) :
    (bitFam (L := L) ih xh y cnt cand w tmk a b mk c).Runs A m
      (bitFamRel ih xh y cnt cand w tmk m c) := by
  classical
  cases c with
  | init =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ y := fun he => by rw [he] at hq; exact absurd hh.lt_m_y (by omega)
    have h2 : q ≠ cnt := fun he => by rw [he] at hq; exact absurd hh.lt_m_cnt (by omega)
    have h3 : q ≠ tmk := fun he => by rw [he] at hq; exact absurd hh.lt_m_tmk (by omega)
    rw [bitInitMoves, if_neg h1, if_neg h2, if_neg h3]
  | scanInit =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ cand := fun he => by rw [he] at hq; exact absurd hh.lt_m_cand (by omega)
    rw [bitScanInitMoves, if_neg h1]
  | parInit =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ cand := fun he => by rw [he] at hq; exact absurd hh.lt_m_cand (by omega)
    rw [bitScanInitMoves, if_neg h1]
  | scanStep =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ cand := fun he => by rw [he] at hq; exact absurd hh.lt_m_cand (by omega)
    rw [bitStepMoves, if_neg h1]
  | parStep =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ cand := fun he => by rw [he] at hq; exact absurd hh.lt_m_cand (by omega)
    rw [bitStepMoves, if_neg h1]
  | mkW =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ w := fun he => by rw [he] at hq; exact absurd hh.lt_m_w (by omega)
    rw [bitWMoves, if_neg h1]
  | commit =>
    refine runs_moveP_local _ _ fun q hq => ?_
    have h1 : q ≠ y := fun he => by rw [he] at hq; exact absurd hh.lt_m_y (by omega)
    have h2 : q ≠ cnt := fun he => by rw [he] at hq; exact absurd hh.lt_m_cnt (by omega)
    rw [bitCommitMoves, if_neg h1, if_neg h2]
  | outer =>
    exact (decides_leafP (HeadMove.eqVarF L cnt ih)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)).congr fun x => by simp
  | scanOver =>
    exact (decides_leafP (HeadMove.eqVarF L cand tmk)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)).congr fun x => by simp
  | parOver =>
    exact (decides_leafP (HeadMove.eqVarF L cand tmk)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)).congr fun x => by simp
  | probeE => exact decides_plusP hh.plusE hmK
  | parProbe => exact decides_plusP hh.plusE hmK
  | probeO => exact decides_plusP hh.plusO hmK

omit [Finite A] in
theorem headLocal2_bitFamRel (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m)
    (c : BitNode) :
    HeadLocal2 m (bitFamRel (A := A) ih xh y cnt cand w tmk m c) := by
  have hy := hh.lt_m_y
  have hcnt := hh.lt_m_cnt
  have hcand := hh.lt_m_cand
  have hw := hh.lt_m_w
  have htmk := hh.lt_m_tmk
  have hih := hh.lt_m_ih
  have hxh := hh.lt_m_xh
  cases c with
  | init =>
    refine headLocal2_moveP fun q _ => ?_
    rw [bitInitMoves]
    split_ifs <;> trivial
  | scanInit =>
    refine headLocal2_moveP fun q _ => ?_
    rw [bitScanInitMoves]
    split_ifs <;> trivial
  | parInit =>
    refine headLocal2_moveP fun q _ => ?_
    rw [bitScanInitMoves]
    split_ifs <;> trivial
  | scanStep =>
    refine headLocal2_moveP fun q _ => ?_
    rw [bitStepMoves]
    split_ifs with h
    · exact hcand
    · trivial
  | parStep =>
    refine headLocal2_moveP fun q _ => ?_
    rw [bitStepMoves]
    split_ifs with h
    · exact hcand
    · trivial
  | mkW =>
    refine headLocal2_moveP fun q _ => ?_
    rw [bitWMoves]
    split_ifs with h
    · exact hcand
    · trivial
  | commit =>
    refine headLocal2_moveP fun q _ => ?_
    rw [bitCommitMoves]
    split_ifs with h1 h2
    · exact hcand
    · exact hcnt
    · trivial
  | outer =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hcnt, hx _ hih]
  | scanOver =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hcand, hx _ htmk]
  | parOver =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hcand, hx _ htmk]
  | probeE =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hcand, hx _ hy]
  | parProbe =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hcand, hx _ hy]
  | probeO =>
    refine headLocal2_decides fun x x' hx => ?_
    rw [hx _ hcand, hx _ hw, hx _ hy]

omit [Finite A] in
/-- **A bit is deterministic**: every node of its control graph is – the two
probes because an addition is. -/
theorem deterministic_bitP (ih xh y cnt cand w tmk a b mk : Fin K) :
    (bitP (L := L) ih xh y cnt cand w tmk a b mk).Deterministic A := by
  refine deterministic_wireP _ _ _ ?_
  rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _)
  · exact deterministic_moveP _
  · exact deterministic_leafP (HeadMove.eqVarF L cnt ih)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_moveP _
  · exact deterministic_plusP _ _ _ _ _ _
  · exact deterministic_leafP (HeadMove.eqVarF L cand tmk)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_moveP _
  · exact deterministic_plusP _ _ _ _ _ _
  · exact deterministic_moveP _
  · exact deterministic_moveP _
  · exact deterministic_moveP _
  · exact deterministic_plusP _ _ _ _ _ _
  · exact deterministic_leafP (HeadMove.eqVarF L cand tmk)
      ((BoundedFormula.IsAtomic.equal _ _).isQF)
  · exact deterministic_moveP _

end BitFam

/-! ### The invariant of the control walk -/

section Inv

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {ih xh y cnt cand w tmk a b mk : Fin K} {p S m : ℕ}

/-- The invariant of both loops: the working head carries the value halved once
per round counted, the counter has not passed the index, the marker is parked at
the greatest element, and nothing else below the protection level has moved. -/
def BitBase (ih xh y cnt cand w tmk : Fin K) (m : ℕ) (x z : Fin K → A) : Prop :=
  (∀ q : Fin K, (q : ℕ) < m → q ≠ y → q ≠ cnt → q ≠ cand → q ≠ w → q ≠ tmk → z q = x q) ∧
    orank (z y) = orank (x xh) / 2 ^ orank (z cnt) ∧
      orank (z cnt) ≤ orank (x ih) ∧
        ∀ e : A, e ≤ z tmk

/-- The invariant of the halving scan: no candidate below the current one is the
half of the value, on either parity. -/
def NoHalf (y cand : Fin K) (z : Fin K → A) : Prop :=
  ∀ c : A, c < z cand →
    orank c + orank c ≠ orank (z y) ∧ orank c + orank c + 1 ≠ orank (z y)

/-- The invariant of the parity scan: no candidate below the current one halves
the value. -/
def NoEven (y cand : Fin K) (z : Fin K → A) : Prop :=
  ∀ c : A, c < z cand → orank c + orank c ≠ orank (z y)

/-- The invariant of the control walk of a bit, node by node. -/
def BitInv (ih xh y cnt cand w tmk : Fin K) (m : ℕ) (x : Fin K → A) :
    BitNode → (Fin K → A) → Prop
  | .init => fun z => z = x
  | .outer => fun z => BitBase ih xh y cnt cand w tmk m x z
  | .scanInit => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) < orank (x ih)
  | .probeE => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) < orank (x ih) ∧ NoHalf y cand z
  | .scanOver => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) < orank (x ih) ∧ NoHalf y cand z ∧
      orank (z cand) + orank (z cand) ≠ orank (z y)
  | .mkW => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) < orank (x ih) ∧ NoHalf y cand z ∧
      orank (z cand) + orank (z cand) ≠ orank (z y) ∧ z cand ≠ z tmk
  | .probeO => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) < orank (x ih) ∧ NoHalf y cand z ∧
      orank (z cand) + orank (z cand) ≠ orank (z y) ∧ z cand ≠ z tmk ∧
      orank (z w) = orank (z cand) + 1
  | .scanStep => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) < orank (x ih) ∧ NoHalf y cand z ∧
      orank (z cand) + orank (z cand) ≠ orank (z y) ∧ z cand ≠ z tmk ∧
      orank (z cand) + orank (z cand) + 1 ≠ orank (z y)
  | .commit => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) < orank (x ih) ∧ orank (z cand) = orank (z y) / 2
  | .parInit => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) = orank (x ih)
  | .parProbe => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) = orank (x ih) ∧ NoEven y cand z
  | .parOver => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) = orank (x ih) ∧ NoEven y cand z ∧
      orank (z cand) + orank (z cand) ≠ orank (z y)
  | .parStep => fun z => BitBase ih xh y cnt cand w tmk m x z ∧
      orank (z cnt) = orank (x ih) ∧ NoEven y cand z ∧
      orank (z cand) + orank (z cand) ≠ orank (z y)

omit [Finite A] in
/-- The scan invariants only look at the value and the candidate. -/
theorem NoHalf.congr {z z' : Fin K → A} (h : NoHalf y cand z) (hy : z' y = z y)
    (hc : z' cand = z cand) : NoHalf y cand z' := by
  intro c' hc'
  rw [hy]
  rw [hc] at hc'
  exact h c' hc'

omit [Finite A] in
theorem NoEven.congr {z z' : Fin K → A} (h : NoEven y cand z) (hy : z' y = z y)
    (hc : z' cand = z cand) : NoEven y cand z' := by
  intro c' hc'
  rw [hy]
  rw [hc] at hc'
  exact h c' hc'

omit [Finite A] in
/-- The interface heads are untouched all along the walk. -/
theorem BitBase.int (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m)
    {x z : Fin K → A} (hb : BitBase ih xh y cnt cand w tmk m x z) {q : Fin K}
    (hq : (q : ℕ) < p) : z q = x q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hh.ne_int hq
  exact hb.1 q (by have := hh.hm; have := hh.hpS; omega) h1 h2 h3 h4 h5

omit [Finite A] in
/-- The invariant survives a fragment that moves nothing below the protection
level. -/
theorem BitBase.congr {x z z' : Fin K → A}
    (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m)
    (hb : BitBase ih xh y cnt cand w tmk m x z) (hz : HeadAgree m z z') :
    BitBase ih xh y cnt cand w tmk m x z' := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  refine ⟨fun q hq hy hc hca hw ht => ?_, ?_, ?_, ?_⟩
  · rw [← hz q hq]; exact h1 q hq hy hc hca hw ht
  · rw [← hz _ hh.lt_m_y, ← hz _ hh.lt_m_cnt]; exact h2
  · rw [← hz _ hh.lt_m_cnt]; exact h3
  · rw [← hz _ hh.lt_m_tmk]; exact h4

end Inv

/-! ### Reading the moves -/

section Moves

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {ih xh y cnt cand w tmk a b mk : Fin K} {p S m : ℕ}

omit [Finite A] in
theorem holds_bitInitMoves {x z : Fin K → A}
    (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m)
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (bitInitMoves xh y cnt tmk q).Holds x q (z q)) :
    z y = x xh ∧ (∀ e : A, z cnt ≤ e) ∧ (∀ e : A, e ≤ z tmk) ∧
      ∀ q : Fin K, (q : ℕ) < m → q ≠ y → q ≠ cnt → q ≠ tmk → z q = x q := by
  classical
  refine ⟨?_, ?_, ?_, fun q hq hqy hqc hqt => ?_⟩
  · have := hmv y hh.lt_m_y
    rw [bitInitMoves, if_pos rfl] at this
    exact this
  · have := hmv cnt hh.lt_m_cnt
    rw [bitInitMoves, if_neg (Ne.symm hh.ne_y_cnt), if_pos rfl] at this
    exact this
  · have := hmv tmk hh.lt_m_tmk
    rw [bitInitMoves, if_neg (Ne.symm hh.ne_y_tmk), if_neg (Ne.symm hh.ne_cnt_tmk),
      if_pos rfl] at this
    exact this
  · have := hmv q hq
    rw [bitInitMoves, if_neg hqy, if_neg hqc, if_neg hqt] at this
    exact this

omit [Finite A] in
theorem holds_bitScanInitMoves {x z : Fin K → A}
    (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m)
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (bitScanInitMoves cand q).Holds x q (z q)) :
    (∀ e : A, z cand ≤ e) ∧ ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → z q = x q := by
  classical
  refine ⟨?_, fun q hq hqc => ?_⟩
  · have := hmv cand hh.lt_m_cand
    rw [bitScanInitMoves, if_pos rfl] at this
    exact this
  · have := hmv q hq
    rw [bitScanInitMoves, if_neg hqc] at this
    exact this

omit [Finite A] in
theorem holds_bitStepMoves {x z : Fin K → A}
    (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m)
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (bitStepMoves cand q).Holds x q (z q)) :
    x cand ⋖ z cand ∧ ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → z q = x q := by
  classical
  refine ⟨?_, fun q hq hqc => ?_⟩
  · have := hmv cand hh.lt_m_cand
    rw [bitStepMoves, if_pos rfl] at this
    exact ⟨this.1, fun e h1 h2 => this.2 e ⟨h1, h2⟩⟩
  · have := hmv q hq
    rw [bitStepMoves, if_neg hqc] at this
    exact this

omit [Finite A] in
theorem holds_bitWMoves {x z : Fin K → A}
    (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m)
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (bitWMoves cand w q).Holds x q (z q)) :
    x cand ⋖ z w ∧ ∀ q : Fin K, (q : ℕ) < m → q ≠ w → z q = x q := by
  classical
  refine ⟨?_, fun q hq hqw => ?_⟩
  · have := hmv w hh.lt_m_w
    rw [bitWMoves, if_pos rfl] at this
    exact ⟨this.1, fun e h1 h2 => this.2 e ⟨h1, h2⟩⟩
  · have := hmv q hq
    rw [bitWMoves, if_neg hqw] at this
    exact this

omit [Finite A] in
theorem holds_bitCommitMoves {x z : Fin K → A}
    (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m)
    (hmv : ∀ q : Fin K, (q : ℕ) < m → (bitCommitMoves y cnt cand q).Holds x q (z q)) :
    z y = x cand ∧ x cnt ⋖ z cnt ∧ ∀ q : Fin K, (q : ℕ) < m → q ≠ y → q ≠ cnt → z q = x q := by
  classical
  refine ⟨?_, ?_, fun q hq hqy hqc => ?_⟩
  · have := hmv y hh.lt_m_y
    rw [bitCommitMoves, if_pos rfl] at this
    exact this
  · have := hmv cnt hh.lt_m_cnt
    rw [bitCommitMoves, if_neg (Ne.symm hh.ne_y_cnt), if_pos rfl] at this
    exact ⟨this.1, fun e h1 h2 => this.2 e ⟨h1, h2⟩⟩
  · have := hmv q hq
    rw [bitCommitMoves, if_neg hqy, if_neg hqc] at this
    exact this

end Moves

/-! ### Soundness: the invariant of the control walk -/

section Sound

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {ih xh y cnt cand w tmk a b mk : Fin K} {p S m : ℕ}

/-- **The invariant holds all along the control walk**: this is the whole
soundness argument, the two exits being read off it. -/
theorem bitInv_of_walk (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) (x : Fin K → A) :
    ∀ u : BitNode × (Fin K → A),
      Relation.ReflTransGen
          (wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire) (.init, x) u →
        BitInv ih xh y cnt cand w tmk m x u.1 u.2 := by
  have hym := hh.lt_m_y
  have hcntm := hh.lt_m_cnt
  have hcandm := hh.lt_m_cand
  have hwm := hh.lt_m_w
  have htmkm := hh.lt_m_tmk
  intro u hu
  induction hu with
  | refl => exact rfl
  | @tail v u' hv hvu ih' =>
    obtain ⟨c, hrel, hwire⟩ := hvu
    cases hnode : v.1 with
    | init =>
      have hvx : v.2 = x := by have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      rw [hvx] at hmv
      obtain ⟨hy0, hcnt0, htop, hrest⟩ := holds_bitInitMoves hh hmv
      have hu1 : u'.1 = .outer := by
        rw [bitWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hr0 : orank (u'.2 cnt) = 0 := orank_eq_zero hcnt0
      rw [hu1]
      refine ⟨fun q hq hqy hqc hqca hqw hqt => hrest q hq hqy hqc hqt, ?_, by rw [hr0]; omega,
        htop⟩
      rw [hr0, hy0]
      simp
    | outer =>
      have hb : BitBase ih xh y cnt cand w tmk m x v.2 := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      have hb' : BitBase ih xh y cnt cand w tmk m x u'.2 := hb.congr hh hag
      have hcnteq : u'.2 cnt = v.2 cnt := (hag cnt hcntm).symm
      have hiheq : v.2 ih = x ih := hb.int hh hh.hih
      cases c with
      | true =>
        have hu1 : u'.1 = .parInit := by
          rw [bitWire, if_pos rfl] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hb', ?_⟩
        rw [hcnteq, hc.mp rfl, hiheq]
      | false =>
        have hu1 : u'.1 = .scanInit := by
          rw [bitWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hb', ?_⟩
        rw [hcnteq]
        refine lt_of_le_of_ne hb.2.2.1 fun he => ?_
        rw [← hiheq] at he
        exact absurd (hc.mpr (orank_inj he)) (by simp)
    | scanInit =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) < orank (x ih) := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hmin, hrest⟩ := holds_bitScanInitMoves hh hmv
      have hu1 : u'.1 = .probeE := by
        rw [bitWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hb' : BitBase ih xh y cnt cand w tmk m x u'.2 := by
        obtain ⟨h1, h2, h3, h4⟩ := hi.1
        refine ⟨fun q hq hqy hqc hqca hqw hqt =>
          (hrest q hq hqca).trans (h1 q hq hqy hqc hqca hqw hqt), ?_, ?_, ?_⟩
        · rw [hrest y hym hh.ne_y_cand, hrest cnt hcntm hh.ne_cnt_cand]; exact h2
        · rw [hrest cnt hcntm hh.ne_cnt_cand]; exact h3
        · rw [hrest tmk htmkm (Ne.symm hh.ne_cand_tmk)]; exact h4
      rw [hu1]
      refine ⟨hb', by rw [hrest cnt hcntm hh.ne_cnt_cand]; exact hi.2, fun c' hc' => ?_⟩
      exact absurd (hmin c') (by simp [not_le.mpr hc'])
    | probeE =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) < orank (x ih) ∧
          NoHalf y cand v.2 := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      have hyq : u'.2 y = v.2 y := (hag y hym).symm
      have hcandq : u'.2 cand = v.2 cand := (hag cand hcandm).symm
      have hcntq : u'.2 cnt = v.2 cnt := (hag cnt hcntm).symm
      have hb' : BitBase ih xh y cnt cand w tmk m x u'.2 := hi.1.congr hh hag
      cases c with
      | true =>
        have hu1 : u'.1 = .commit := by
          rw [bitWire, if_pos rfl] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hb', by rw [hcntq]; exact hi.2.1, ?_⟩
        have := hc.mp rfl
        rw [hcandq, hyq]
        omega
      | false =>
        have hu1 : u'.1 = .scanOver := by
          rw [bitWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hb', by rw [hcntq]; exact hi.2.1, ?_, ?_⟩
        · exact hi.2.2.congr hyq hcandq
        · rw [hcandq, hyq]
          intro he
          exact absurd (hc.mpr he) (by simp)
    | scanOver =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) < orank (x ih) ∧
          NoHalf y cand v.2 ∧ orank (v.2 cand) + orank (v.2 cand) ≠ orank (v.2 y) := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      have hyq : u'.2 y = v.2 y := (hag y hym).symm
      have hcandq : u'.2 cand = v.2 cand := (hag cand hcandm).symm
      have hcntq : u'.2 cnt = v.2 cnt := (hag cnt hcntm).symm
      have htmkq : u'.2 tmk = v.2 tmk := (hag tmk htmkm).symm
      cases c with
      | true =>
        rw [bitWire, if_pos rfl] at hwire
        exact absurd hwire (by simp)
      | false =>
        have hu1 : u'.1 = .mkW := by
          rw [bitWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hi.1.congr hh hag, by rw [hcntq]; exact hi.2.1, ?_, ?_, ?_⟩
        · exact hi.2.2.1.congr hyq hcandq
        · rw [hcandq, hyq]; exact hi.2.2.2
        · rw [hcandq, htmkq]
          intro he
          exact absurd (hc.mpr he) (by simp)
    | mkW =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) < orank (x ih) ∧
          NoHalf y cand v.2 ∧ orank (v.2 cand) + orank (v.2 cand) ≠ orank (v.2 y) ∧
          v.2 cand ≠ v.2 tmk := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hcov, hrest⟩ := holds_bitWMoves hh hmv
      have hu1 : u'.1 = .probeO := by
        rw [bitWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hyq : u'.2 y = v.2 y := hrest y hym hh.ne_y_w
      have hcandq : u'.2 cand = v.2 cand := hrest cand hcandm hh.ne_cand_w
      have hcntq : u'.2 cnt = v.2 cnt := hrest cnt hcntm hh.ne_cnt_w
      have htmkq : u'.2 tmk = v.2 tmk := hrest tmk htmkm (Ne.symm hh.ne_w_tmk)
      have hb' : BitBase ih xh y cnt cand w tmk m x u'.2 := by
        obtain ⟨h1, h2, h3, h4⟩ := hi.1
        refine ⟨fun q hq hqy hqc hqca hqw hqt =>
          (hrest q hq hqw).trans (h1 q hq hqy hqc hqca hqw hqt), ?_, ?_, ?_⟩
        · rw [hyq, hcntq]; exact h2
        · rw [hcntq]; exact h3
        · rw [htmkq]; exact h4
      rw [hu1]
      refine ⟨hb', by rw [hcntq]; exact hi.2.1, ?_, ?_, ?_, ?_⟩
      · exact hi.2.2.1.congr hyq hcandq
      · rw [hcandq, hyq]; exact hi.2.2.2.1
      · rw [hcandq, htmkq]; exact hi.2.2.2.2
      · rw [hcandq]
        exact orank_covBy hcov
    | probeO =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) < orank (x ih) ∧
          NoHalf y cand v.2 ∧ orank (v.2 cand) + orank (v.2 cand) ≠ orank (v.2 y) ∧
          v.2 cand ≠ v.2 tmk ∧ orank (v.2 w) = orank (v.2 cand) + 1 := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      have hyq : u'.2 y = v.2 y := (hag y hym).symm
      have hcandq : u'.2 cand = v.2 cand := (hag cand hcandm).symm
      have hcntq : u'.2 cnt = v.2 cnt := (hag cnt hcntm).symm
      have htmkq : u'.2 tmk = v.2 tmk := (hag tmk htmkm).symm
      have hb' : BitBase ih xh y cnt cand w tmk m x u'.2 := hi.1.congr hh hag
      cases c with
      | true =>
        have hu1 : u'.1 = .commit := by
          rw [bitWire, if_pos rfl] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hb', by rw [hcntq]; exact hi.2.1, ?_⟩
        have h1 := hc.mp rfl
        have h2 := hi.2.2.2.2.2
        rw [hcandq, hyq]
        omega
      | false =>
        have hu1 : u'.1 = .scanStep := by
          rw [bitWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hb', by rw [hcntq]; exact hi.2.1, ?_, ?_, ?_, ?_⟩
        · exact hi.2.2.1.congr hyq hcandq
        · rw [hcandq, hyq]; exact hi.2.2.2.1
        · rw [hcandq, htmkq]; exact hi.2.2.2.2.1
        · rw [hcandq, hyq]
          intro he
          refine absurd (hc.mpr ?_) (by simp)
          rw [hi.2.2.2.2.2]
          omega
    | scanStep =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) < orank (x ih) ∧
          NoHalf y cand v.2 ∧ orank (v.2 cand) + orank (v.2 cand) ≠ orank (v.2 y) ∧
          v.2 cand ≠ v.2 tmk ∧
          orank (v.2 cand) + orank (v.2 cand) + 1 ≠ orank (v.2 y) := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hcov, hrest⟩ := holds_bitStepMoves hh hmv
      have hu1 : u'.1 = .probeE := by
        rw [bitWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hyq : u'.2 y = v.2 y := hrest y hym hh.ne_y_cand
      have hcntq : u'.2 cnt = v.2 cnt := hrest cnt hcntm hh.ne_cnt_cand
      have htmkq : u'.2 tmk = v.2 tmk := hrest tmk htmkm (Ne.symm hh.ne_cand_tmk)
      have hb' : BitBase ih xh y cnt cand w tmk m x u'.2 := by
        obtain ⟨h1, h2, h3, h4⟩ := hi.1
        refine ⟨fun q hq hqy hqc hqca hqw hqt =>
          (hrest q hq hqca).trans (h1 q hq hqy hqc hqca hqw hqt), ?_, ?_, ?_⟩
        · rw [hyq, hcntq]; exact h2
        · rw [hcntq]; exact h3
        · rw [htmkq]; exact h4
      rw [hu1]
      refine ⟨hb', by rw [hcntq]; exact hi.2.1, fun c' hc' => ?_⟩
      rw [hyq]
      have hle : c' ≤ v.2 cand := le_of_not_gt fun hgt => hcov.2 hgt hc'
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hi.2.2.1 c' hlt
      · rw [heq]
        exact ⟨hi.2.2.2.1, hi.2.2.2.2.2⟩
    | commit =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) < orank (x ih) ∧
          orank (v.2 cand) = orank (v.2 y) / 2 := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hycand, hcov, hrest⟩ := holds_bitCommitMoves hh hmv
      have hu1 : u'.1 = .outer := by
        rw [bitWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      obtain ⟨h1, h2, h3, h4⟩ := hi.1
      have hcntsucc : orank (u'.2 cnt) = orank (v.2 cnt) + 1 := orank_covBy hcov
      rw [hu1]
      refine ⟨fun q hq hqy hqc hqca hqw hqt =>
        (hrest q hq hqy hqc).trans (h1 q hq hqy hqc hqca hqw hqt), ?_, ?_, ?_⟩
      · rw [hycand, hcntsucc, hi.2.2, h2, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [hcntsucc]; omega
      · rw [hrest tmk htmkm (Ne.symm hh.ne_y_tmk) (Ne.symm hh.ne_cnt_tmk)]; exact h4
    | parInit =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) = orank (x ih) := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hmin, hrest⟩ := holds_bitScanInitMoves hh hmv
      have hu1 : u'.1 = .parProbe := by
        rw [bitWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hb' : BitBase ih xh y cnt cand w tmk m x u'.2 := by
        obtain ⟨h1, h2, h3, h4⟩ := hi.1
        refine ⟨fun q hq hqy hqc hqca hqw hqt =>
          (hrest q hq hqca).trans (h1 q hq hqy hqc hqca hqw hqt), ?_, ?_, ?_⟩
        · rw [hrest y hym hh.ne_y_cand, hrest cnt hcntm hh.ne_cnt_cand]; exact h2
        · rw [hrest cnt hcntm hh.ne_cnt_cand]; exact h3
        · rw [hrest tmk htmkm (Ne.symm hh.ne_cand_tmk)]; exact h4
      rw [hu1]
      refine ⟨hb', by rw [hrest cnt hcntm hh.ne_cnt_cand]; exact hi.2, fun c' hc' => ?_⟩
      exact absurd (hmin c') (by simp [not_le.mpr hc'])
    | parProbe =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) = orank (x ih) ∧
          NoEven y cand v.2 := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      have hyq : u'.2 y = v.2 y := (hag y hym).symm
      have hcandq : u'.2 cand = v.2 cand := (hag cand hcandm).symm
      have hcntq : u'.2 cnt = v.2 cnt := (hag cnt hcntm).symm
      cases c with
      | true =>
        rw [bitWire, if_pos rfl] at hwire
        exact absurd hwire (by simp)
      | false =>
        have hu1 : u'.1 = .parOver := by
          rw [bitWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hi.1.congr hh hag, by rw [hcntq]; exact hi.2.1, ?_, ?_⟩
        · exact hi.2.2.congr hyq hcandq
        · rw [hcandq, hyq]
          intro he
          exact absurd (hc.mpr he) (by simp)
    | parOver =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) = orank (x ih) ∧
          NoEven y cand v.2 ∧ orank (v.2 cand) + orank (v.2 cand) ≠ orank (v.2 y) := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      have hyq : u'.2 y = v.2 y := (hag y hym).symm
      have hcandq : u'.2 cand = v.2 cand := (hag cand hcandm).symm
      have hcntq : u'.2 cnt = v.2 cnt := (hag cnt hcntm).symm
      cases c with
      | true =>
        rw [bitWire, if_pos rfl] at hwire
        exact absurd hwire (by simp)
      | false =>
        have hu1 : u'.1 = .parStep := by
          rw [bitWire, if_neg (by simp)] at hwire
          exact (Sum.inl.inj hwire).symm ▸ rfl
        rw [hu1]
        refine ⟨hi.1.congr hh hag, by rw [hcntq]; exact hi.2.1, ?_, ?_⟩
        · exact hi.2.2.1.congr hyq hcandq
        · rw [hcandq, hyq]; exact hi.2.2.2
    | parStep =>
      have hi : BitBase ih xh y cnt cand w tmk m x v.2 ∧ orank (v.2 cnt) = orank (x ih) ∧
          NoEven y cand v.2 ∧ orank (v.2 cand) + orank (v.2 cand) ≠ orank (v.2 y) := by
        have := ih'; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨-, hmv⟩ := hrel
      obtain ⟨hcov, hrest⟩ := holds_bitStepMoves hh hmv
      have hu1 : u'.1 = .parProbe := by
        rw [bitWire] at hwire
        exact (Sum.inl.inj hwire).symm ▸ rfl
      have hyq : u'.2 y = v.2 y := hrest y hym hh.ne_y_cand
      have hcntq : u'.2 cnt = v.2 cnt := hrest cnt hcntm hh.ne_cnt_cand
      have htmkq : u'.2 tmk = v.2 tmk := hrest tmk htmkm (Ne.symm hh.ne_cand_tmk)
      have hb' : BitBase ih xh y cnt cand w tmk m x u'.2 := by
        obtain ⟨h1, h2, h3, h4⟩ := hi.1
        refine ⟨fun q hq hqy hqc hqca hqw hqt =>
          (hrest q hq hqca).trans (h1 q hq hqy hqc hqca hqw hqt), ?_, ?_, ?_⟩
        · rw [hyq, hcntq]; exact h2
        · rw [hcntq]; exact h3
        · rw [htmkq]; exact h4
      rw [hu1]
      refine ⟨hb', by rw [hcntq]; exact hi.2.1, fun c' hc' => ?_⟩
      rw [hyq]
      have hle : c' ≤ v.2 cand := le_of_not_gt fun hgt => hcov.2 hgt hc'
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hi.2.2.1 c' hlt
      · rw [heq]; exact hi.2.2.2

end Sound

/-! ### Completeness: building the walks -/

section Complete

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {ih xh y cnt cand w tmk a b mk : Fin K} {p S m : ℕ}

/-- Abbreviation for the control walk of a bit. -/
private abbrev BWalk (ih xh y cnt cand w tmk : Fin K) (m : ℕ) :
    BitNode × (Fin K → A) → BitNode × (Fin K → A) → Prop :=
  Relation.ReflTransGen (wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire)

/-- **One turn of the halving scan**: a candidate strictly below the half is
rejected by both probes, so the scan steps on. -/
theorem walk_scan_step (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) {z : Fin K → A}
    (hlt : orank (z cand) + orank (z cand) + 1 < orank (z y))
    (htop : ∀ e : A, e ≤ z tmk) :
    ∃ z' : Fin K → A, BWalk ih xh y cnt cand w tmk m (.probeE, z) (.probeE, z') ∧
      orank (z' cand) = orank (z cand) + 1 ∧
      ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → q ≠ w → z' q = z q := by
  classical
  have hcandlt : orank (z cand) < orank (z tmk) := by
    have h1 : orank (z y) ≤ orank (z tmk) := orank_le_iff.mpr (htop (z y))
    omega
  -- the successor of the candidate exists
  obtain ⟨s, hs⟩ := exists_orank_eq (A := A) (m := orank (z cand) + 1)
    (lt_of_le_of_lt (by omega) (orank_lt_card (z tmk)))
  have hcov : z cand ⋖ s := covBy_of_orank_succ (by rw [hs])
  have hne : z cand ≠ z tmk := fun he => by rw [he] at hcandlt; omega
  set z1 := Function.update z w s with hz1
  have hz1w : z1 w = s := by rw [hz1, Function.update_self]
  have hz1o : ∀ q : Fin K, q ≠ w → z1 q = z q := fun q hq => by
    rw [hz1, Function.update_of_ne hq]
  set z2 := Function.update z1 cand s with hz2
  have hz2c : z2 cand = s := by rw [hz2, Function.update_self]
  have hz2o : ∀ q : Fin K, q ≠ cand → z2 q = z1 q := fun q hq => by
    rw [hz2, Function.update_of_ne hq]
  have hprobeE : orank (z cand) + orank (z cand) ≠ orank (z y) := by omega
  have s1 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
      (.probeE, z) (.scanOver, z) := ⟨false, ⟨by simp [hprobeE], HeadAgree.refl z⟩, rfl⟩
  have s2 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
      (.scanOver, z) (.mkW, z) := ⟨false, ⟨by simp [hne], HeadAgree.refl z⟩, rfl⟩
  have s3 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
      (.mkW, z) (.probeO, z1) := by
    refine ⟨true, ⟨rfl, fun q hq => ?_⟩, rfl⟩
    by_cases hqw : q = w
    · rw [bitWMoves, if_pos hqw, hqw]
      change z cand < z1 w ∧ ∀ e : A, ¬(z cand < e ∧ e < z1 w)
      rw [hz1w]
      exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
    · rw [bitWMoves, if_neg hqw]
      change z1 q = z q
      exact hz1o q hqw
  have hprobeO : orank (z1 cand) + orank (z1 w) ≠ orank (z1 y) := by
    rw [hz1o cand hh.ne_cand_w, hz1w, hz1o y hh.ne_y_w, hs]
    omega
  have s4 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
      (.probeO, z1) (.scanStep, z1) := ⟨false, ⟨by simp [hprobeO], HeadAgree.refl z1⟩, rfl⟩
  have s5 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
      (.scanStep, z1) (.probeE, z2) := by
    refine ⟨true, ⟨rfl, fun q hq => ?_⟩, rfl⟩
    by_cases hqc : q = cand
    · rw [bitStepMoves, if_pos hqc, hqc]
      change z1 cand < z2 cand ∧ ∀ e : A, ¬(z1 cand < e ∧ e < z2 cand)
      rw [hz2c, hz1o cand hh.ne_cand_w]
      exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
    · rw [bitStepMoves, if_neg hqc]
      change z2 q = z1 q
      exact hz2o q hqc
  refine ⟨z2, ((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5, ?_, ?_⟩
  · rw [hz2c, hs]
  · intro q hq hqc hqw
    rw [hz2o q hqc, hz1o q hqw]

/-- **The halving scan reaches the half**: the candidate walks up to `v / 2`,
every earlier candidate being rejected. -/
theorem walk_scan (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) {z : Fin K → A}
    (hmin : ∀ e : A, z cand ≤ e) (htop : ∀ e : A, e ≤ z tmk) :
    ∀ t : ℕ, t ≤ orank (z y) / 2 →
      ∃ z' : Fin K → A, BWalk ih xh y cnt cand w tmk m (.probeE, z) (.probeE, z') ∧
        orank (z' cand) = t ∧ ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → q ≠ w → z' q = z q := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨z, .refl, orank_eq_zero hmin, fun q _ _ _ => rfl⟩
  | succ t iht =>
    intro hle
    obtain ⟨z', hwalk, hcandt, hrest⟩ := iht (by omega)
    have hyq : z' y = z y := hrest y hh.lt_m_y hh.ne_y_cand hh.ne_y_w
    have htmkq : z' tmk = z tmk := hrest tmk hh.lt_m_tmk (Ne.symm hh.ne_cand_tmk)
      (Ne.symm hh.ne_w_tmk)
    have hlt : orank (z' cand) + orank (z' cand) + 1 < orank (z' y) := by
      rw [hcandt, hyq]
      omega
    obtain ⟨z'', hwalk', hcand', hrest'⟩ := walk_scan_step hh hlt (by rw [htmkq]; exact htop)
    refine ⟨z'', hwalk.trans hwalk', by rw [hcand', hcandt], fun q hq hqc hqw => ?_⟩
    rw [hrest' q hq hqc hqw, hrest q hq hqc hqw]

/-- **The scan commits**: at the half, one of the two probes succeeds and the
round is closed. -/
theorem walk_commit (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) {z : Fin K → A}
    (hcandh : orank (z cand) = orank (z y) / 2) (htop : ∀ e : A, e ≤ z tmk) :
    ∃ z' : Fin K → A, BWalk ih xh y cnt cand w tmk m (.probeE, z) (.commit, z') ∧
      ∀ q : Fin K, (q : ℕ) < m → q ≠ w → z' q = z q := by
  classical
  rcases Nat.even_or_odd (orank (z y)) with hev | hodd
  · obtain ⟨k, hk⟩ := hev
    have heq : orank (z cand) + orank (z cand) = orank (z y) := by
      rw [hcandh, hk]
      omega
    exact ⟨z, Relation.ReflTransGen.single ⟨true, ⟨by simp [heq], HeadAgree.refl z⟩, rfl⟩,
      fun q _ _ => rfl⟩
  · obtain ⟨k, hk⟩ := hodd
    have hcandk : orank (z cand) = k := by rw [hcandh, hk]; omega
    have hne : orank (z cand) + orank (z cand) ≠ orank (z y) := by omega
    have hcandlt : orank (z cand) < orank (z tmk) := by
      have h1 : orank (z y) ≤ orank (z tmk) := orank_le_iff.mpr (htop (z y))
      omega
    have hnetmk : z cand ≠ z tmk := fun he => by rw [he] at hcandlt; omega
    obtain ⟨s, hs⟩ := exists_orank_eq (A := A) (m := orank (z cand) + 1)
      (lt_of_le_of_lt (by omega) (orank_lt_card (z tmk)))
    have hcov : z cand ⋖ s := covBy_of_orank_succ (by rw [hs])
    set z1 := Function.update z w s with hz1
    have hz1w : z1 w = s := by rw [hz1, Function.update_self]
    have hz1o : ∀ q : Fin K, q ≠ w → z1 q = z q := fun q hq => by
      rw [hz1, Function.update_of_ne hq]
    have hyes : orank (z1 cand) + orank (z1 w) = orank (z1 y) := by
      rw [hz1o cand hh.ne_cand_w, hz1w, hz1o y hh.ne_y_w, hs]
      omega
    have s1 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.probeE, z) (.scanOver, z) := ⟨false, ⟨by simp [hne], HeadAgree.refl z⟩, rfl⟩
    have s2 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.scanOver, z) (.mkW, z) := ⟨false, ⟨by simp [hnetmk], HeadAgree.refl z⟩, rfl⟩
    have s3 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.mkW, z) (.probeO, z1) := by
      refine ⟨true, ⟨rfl, fun q hq => ?_⟩, rfl⟩
      by_cases hqw : q = w
      · rw [bitWMoves, if_pos hqw, hqw]
        change z cand < z1 w ∧ ∀ e : A, ¬(z cand < e ∧ e < z1 w)
        rw [hz1w]
        exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
      · rw [bitWMoves, if_neg hqw]
        change z1 q = z q
        exact hz1o q hqw
    have s4 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.probeO, z1) (.commit, z1) := ⟨true, ⟨by simp [hyes], HeadAgree.refl z1⟩, rfl⟩
    exact ⟨z1, (((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4,
      fun q _ hqw => hz1o q hqw⟩

/-- **The outer loop runs**: after `t` rounds the working head carries the value
halved `t` times, and the counter has counted them. -/
theorem walk_outer (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) (x : Fin K → A) :
    ∀ t : ℕ, t ≤ orank (x ih) →
      ∃ z : Fin K → A, BWalk ih xh y cnt cand w tmk m (.init, x) (.outer, z) ∧
        orank (z cnt) = t ∧ orank (z y) = orank (x xh) / 2 ^ t ∧
        (∀ e : A, e ≤ z tmk) ∧
        ∀ q : Fin K, (q : ℕ) < m → q ≠ y → q ≠ cnt → q ≠ cand → q ≠ w → q ≠ tmk →
          z q = x q := by
  classical
  haveI : Nonempty A := ⟨x xh⟩
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨m0, hm0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    obtain ⟨mx, hmx⟩ := exists_orank_eq (A := A) (m := Nat.card A - 1) (by
      have := Nat.card_pos (α := A); omega)
    have hmxtop : ∀ e : A, e ≤ mx := fun e =>
      orank_le_iff.mp (by have := orank_lt_card e; omega)
    set z0 := Function.update (Function.update (Function.update x y (x xh)) cnt m0) tmk mx
      with hz0def
    have hz0y : z0 y = x xh := by
      rw [hz0def, Function.update_of_ne hh.ne_y_tmk, Function.update_of_ne hh.ne_y_cnt,
        Function.update_self]
    have hz0cnt : z0 cnt = m0 := by
      rw [hz0def, Function.update_of_ne hh.ne_cnt_tmk, Function.update_self]
    have hz0tmk : z0 tmk = mx := by rw [hz0def, Function.update_self]
    have hz0o : ∀ q : Fin K, q ≠ y → q ≠ cnt → q ≠ tmk → z0 q = x q := by
      intro q hqy hqc hqt
      rw [hz0def, Function.update_of_ne hqt, Function.update_of_ne hqc,
        Function.update_of_ne hqy]
    refine ⟨z0, Relation.ReflTransGen.single ⟨true, ⟨rfl, fun q hq => ?_⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
    · by_cases hqy : q = y
      · rw [bitInitMoves, if_pos hqy, hqy]
        change z0 y = x xh
        exact hz0y
      · by_cases hqc : q = cnt
        · rw [bitInitMoves, if_neg hqy, if_pos hqc, hqc]
          change ∀ e : A, z0 cnt ≤ e
          rw [hz0cnt]
          exact fun e => isMin_of_orank_eq_zero hm0 e
        · by_cases hqt : q = tmk
          · rw [bitInitMoves, if_neg hqy, if_neg hqc, if_pos hqt, hqt]
            change ∀ e : A, e ≤ z0 tmk
            rw [hz0tmk]
            exact hmxtop
          · rw [bitInitMoves, if_neg hqy, if_neg hqc, if_neg hqt]
            change z0 q = x q
            exact hz0o q hqy hqc hqt
    · rw [hz0cnt, hm0]
    · rw [hz0y]
      simp
    · rw [hz0tmk]
      exact hmxtop
    · intro q _ hqy hqc _ _ hqt
      exact hz0o q hqy hqc hqt
  | succ t iht =>
    intro hle
    obtain ⟨z, hwalk, hcnt, hy, htop, hrest⟩ := iht (by omega)
    obtain ⟨hne1, hne2, hne3, hne4, hne5⟩ := hh.ne_int hh.hih
    have hiheq : z ih = x ih :=
      hrest ih (by have := hh.hih; have := hh.hm; have := hh.hpS; omega) hne1 hne2 hne3 hne4 hne5
    have hcntne : z cnt ≠ z ih := by
      rw [hiheq]
      intro he
      rw [← orank_inj_iff (A := A), hcnt] at he
      omega
    -- the round starts: the outer test fails and the scan is reset
    obtain ⟨c0, hc0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    set z0 := Function.update z cand c0 with hz0def
    have hz0c : z0 cand = c0 := by rw [hz0def, Function.update_self]
    have hz0o : ∀ q : Fin K, q ≠ cand → z0 q = z q := fun q hq => by
      rw [hz0def, Function.update_of_ne hq]
    have s1 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.outer, z) (.scanInit, z) := ⟨false, ⟨by simp [hcntne], HeadAgree.refl z⟩, rfl⟩
    have s2 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.scanInit, z) (.probeE, z0) := by
      refine ⟨true, ⟨rfl, fun q hq => ?_⟩, rfl⟩
      by_cases hqc : q = cand
      · rw [bitScanInitMoves, if_pos hqc, hqc]
        change ∀ e : A, z0 cand ≤ e
        rw [hz0c]
        exact fun e => isMin_of_orank_eq_zero hc0 e
      · rw [bitScanInitMoves, if_neg hqc]
        change z0 q = z q
        exact hz0o q hqc
    -- the scan finds the half and the round is closed
    have hz0y : z0 y = z y := hz0o y hh.ne_y_cand
    have hz0tmk : z0 tmk = z tmk := hz0o tmk (Ne.symm hh.ne_cand_tmk)
    obtain ⟨z1, hwalk1, hcand1, hrest1⟩ := walk_scan hh (z := z0)
      (by rw [hz0c]; exact fun e => isMin_of_orank_eq_zero hc0 e)
      (by rw [hz0tmk]; exact htop) (orank (z0 y) / 2) le_rfl
    have hz1y : z1 y = z y := by
      rw [hrest1 y hh.lt_m_y hh.ne_y_cand hh.ne_y_w, hz0y]
    have hz1tmk : z1 tmk = z tmk := by
      rw [hrest1 tmk hh.lt_m_tmk (Ne.symm hh.ne_cand_tmk) (Ne.symm hh.ne_w_tmk), hz0tmk]
    obtain ⟨z2, hwalk2, hrest2⟩ := walk_commit hh (z := z1)
      (by rw [hcand1, hz1y, hz0y]) (by rw [hz1tmk]; exact htop)
    have hz2cand : orank (z2 cand) = orank (z y) / 2 := by
      rw [hrest2 cand hh.lt_m_cand hh.ne_cand_w, hcand1, hz0y]
    have hz2cnt : z2 cnt = z cnt := by
      rw [hrest2 cnt hh.lt_m_cnt hh.ne_cnt_w, hrest1 cnt hh.lt_m_cnt hh.ne_cnt_cand hh.ne_cnt_w,
        hz0o cnt hh.ne_cnt_cand]
    have hz2tmk : z2 tmk = z tmk := by
      rw [hrest2 tmk hh.lt_m_tmk (Ne.symm hh.ne_w_tmk), hz1tmk]
    have hz2o : ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → q ≠ w → z2 q = z q := by
      intro q hq hqc hqw
      rw [hrest2 q hq hqw, hrest1 q hq hqc hqw, hz0o q hqc]
    -- the commit: the working head takes the half and the counter advances
    obtain ⟨c1, hc1⟩ := exists_orank_eq (A := A) (m := t + 1)
      (lt_of_le_of_lt (by omega) (orank_lt_card (x ih)))
    have hcov : z2 cnt ⋖ c1 := covBy_of_orank_succ (by rw [hc1, hz2cnt, hcnt])
    set z3 := Function.update (Function.update z2 y (z2 cand)) cnt c1 with hz3def
    have hz3y : z3 y = z2 cand := by
      rw [hz3def, Function.update_of_ne hh.ne_y_cnt, Function.update_self]
    have hz3cnt : z3 cnt = c1 := by rw [hz3def, Function.update_self]
    have hz3o : ∀ q : Fin K, q ≠ y → q ≠ cnt → z3 q = z2 q := by
      intro q hqy hqc
      rw [hz3def, Function.update_of_ne hqc, Function.update_of_ne hqy]
    have s3 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.commit, z2) (.outer, z3) := by
      refine ⟨true, ⟨rfl, fun q hq => ?_⟩, rfl⟩
      by_cases hqy : q = y
      · rw [bitCommitMoves, if_pos hqy, hqy]
        change z3 y = z2 cand
        exact hz3y
      · by_cases hqc : q = cnt
        · rw [bitCommitMoves, if_neg hqy, if_pos hqc, hqc]
          change z2 cnt < z3 cnt ∧ ∀ e : A, ¬(z2 cnt < e ∧ e < z3 cnt)
          rw [hz3cnt]
          exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
        · rw [bitCommitMoves, if_neg hqy, if_neg hqc]
          change z3 q = z2 q
          exact hz3o q hqy hqc
    refine ⟨z3, ((((hwalk.tail s1).tail s2).trans hwalk1).trans hwalk2).tail s3, ?_, ?_, ?_, ?_⟩
    · rw [hz3cnt, hc1]
    · rw [hz3y, hz2cand, hy, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [hz3o tmk (Ne.symm hh.ne_y_tmk) (Ne.symm hh.ne_cnt_tmk), hz2tmk]
      exact htop
    · intro q hq hqy hqc hqca hqw hqt
      rw [hz3o q hqy hqc, hz2o q hq hqca hqw]
      exact hrest q hq hqy hqc hqca hqw hqt

/-- **One turn of the parity scan**: a candidate that does not halve the value,
and is not at the marker, steps on. -/
theorem walk_par_step (_hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) {z : Fin K → A}
    (hprobe : orank (z cand) + orank (z cand) ≠ orank (z y))
    (hlt : orank (z cand) < orank (z tmk)) :
    ∃ z' : Fin K → A, BWalk ih xh y cnt cand w tmk m (.parProbe, z) (.parProbe, z') ∧
      orank (z' cand) = orank (z cand) + 1 ∧
      ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → z' q = z q := by
  classical
  have hne : z cand ≠ z tmk := fun he => by rw [he] at hlt; omega
  obtain ⟨s, hs⟩ := exists_orank_eq (A := A) (m := orank (z cand) + 1)
    (lt_of_le_of_lt (by omega) (orank_lt_card (z tmk)))
  have hcov : z cand ⋖ s := covBy_of_orank_succ (by rw [hs])
  set z1 := Function.update z cand s with hz1def
  have hz1c : z1 cand = s := by rw [hz1def, Function.update_self]
  have hz1o : ∀ q : Fin K, q ≠ cand → z1 q = z q := fun q hq => by
    rw [hz1def, Function.update_of_ne hq]
  have s1 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
      (.parProbe, z) (.parOver, z) := ⟨false, ⟨by simp [hprobe], HeadAgree.refl z⟩, rfl⟩
  have s2 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
      (.parOver, z) (.parStep, z) := ⟨false, ⟨by simp [hne], HeadAgree.refl z⟩, rfl⟩
  have s3 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
      (.parStep, z) (.parProbe, z1) := by
    refine ⟨true, ⟨rfl, fun q hq => ?_⟩, rfl⟩
    by_cases hqc : q = cand
    · rw [bitStepMoves, if_pos hqc, hqc]
      change z cand < z1 cand ∧ ∀ e : A, ¬(z cand < e ∧ e < z1 cand)
      rw [hz1c]
      exact ⟨hcov.lt, fun e he => hcov.2 he.1 he.2⟩
    · rw [bitStepMoves, if_neg hqc]
      change z1 q = z q
      exact hz1o q hqc
  exact ⟨z1, ((Relation.ReflTransGen.single s1).tail s2).tail s3, by rw [hz1c, hs],
    fun q _ hqc => hz1o q hqc⟩

/-- **The parity scan walks**: as long as no candidate below has halved the
value, the scan reaches every index up to the marker. -/
theorem walk_par (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) {z : Fin K → A}
    (hmin : ∀ e : A, z cand ≤ e) :
    ∀ t : ℕ, t ≤ orank (z tmk) → (∀ d : ℕ, d < t → d + d ≠ orank (z y)) →
      ∃ z' : Fin K → A, BWalk ih xh y cnt cand w tmk m (.parProbe, z) (.parProbe, z') ∧
        orank (z' cand) = t ∧ ∀ q : Fin K, (q : ℕ) < m → q ≠ cand → z' q = z q := by
  intro t
  induction t with
  | zero => intro _ _; exact ⟨z, .refl, orank_eq_zero hmin, fun q _ _ => rfl⟩
  | succ t iht =>
    intro hle hfail
    obtain ⟨z', hwalk, hcandt, hrest⟩ := iht (by omega) fun d hd => hfail d (by omega)
    have hyq : z' y = z y := hrest y hh.lt_m_y hh.ne_y_cand
    have htq : z' tmk = z tmk := hrest tmk hh.lt_m_tmk (Ne.symm hh.ne_cand_tmk)
    obtain ⟨z'', hwalk', hcand', hrest'⟩ := walk_par_step hh (z := z')
      (by rw [hcandt, hyq]; exact hfail t (by omega)) (by rw [hcandt, htq]; omega)
    exact ⟨z'', hwalk.trans hwalk', by rw [hcand', hcandt],
      fun q hq hqc => (hrest' q hq hqc).trans (hrest q hq hqc)⟩

end Complete

/-! ### What a bit decides -/

section Decides

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {ih xh y cnt cand w tmk a b mk : Fin K} {p S m : ℕ}

/-- A parity, as a bit. -/
private theorem testBit_iff_mod {X I : ℕ} : X.testBit I = true ↔ X / 2 ^ I % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp

/-- **The bit fragment decides the bit**, with no side condition: the marker is
parked by the fragment itself, the halvings are exact, and the parity scan is
exhaustive. -/
theorem decides_bitP (hh : BitHeads ih xh y cnt cand w tmk a b mk p S m) (hmK : m ≤ K) :
    (bitP (L := L) ih xh y cnt cand w tmk a b mk).Decides A p
      (fun x => (orank (x xh)).testBit (orank (x ih)) = true) := by
  classical
  have hpm : p ≤ m := hh.le_pm
  have hym := hh.lt_m_y
  have hcntm := hh.lt_m_cnt
  have hcandm := hh.lt_m_cand
  have htmkm := hh.lt_m_tmk
  refine (((runs_wireP (bitFam (L := L) ih xh y cnt cand w tmk a b mk) bitWire
    (runs_bitFam (A := A) hh hmK) (fun c => headLocal2_bitFamRel hh c) .init).weaken
      hpm).mono ?_ ?_)
  · -- soundness: read the answer off the invariant at the two exits
    rintro x c z ⟨u, hwalk, c', hrel, hwire⟩
    have hinv := bitInv_of_walk hh x u hwalk
    have hprotect : ∀ v : Fin K → A,
        (∀ q : Fin K, (q : ℕ) < m → q ≠ y → q ≠ cnt → q ≠ cand → q ≠ w → q ≠ tmk →
          v q = x q) → HeadAgree p x v := by
      intro v hv q hq
      obtain ⟨h1, h2, h3, h4, h5⟩ := hh.ne_int hq
      exact (hv q (by omega) h1 h2 h3 h4 h5).symm
    -- the half of the value, as an element, when it lies below the candidate
    have hhalf : ∀ v : Fin K → A, (∀ e : A, e ≤ v tmk) →
        ∀ d : ℕ, d ≤ orank (v tmk) → ∃ r : A, orank r = d := by
      intro v _ d hd
      exact exists_orank_eq (lt_of_le_of_lt hd (orank_lt_card (v tmk)))
    cases hnode : u.1 with
    | init | outer | scanInit | probeE | mkW | probeO | scanStep | commit | parInit | parStep =>
      rw [hnode, bitWire] at hwire
      first
        | exact absurd hwire (by simp)
        | (cases c' <;> simp at hwire)
    | scanOver =>
      -- unreachable: the half is at or below the candidate
      exfalso
      have hi : BitBase ih xh y cnt cand w tmk m x u.2 ∧ orank (u.2 cnt) < orank (x ih) ∧
          NoHalf y cand u.2 ∧ orank (u.2 cand) + orank (u.2 cand) ≠ orank (u.2 y) := by
        have := hinv; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, -⟩ := hrel
      cases c' with
      | false => rw [bitWire, if_neg (by simp)] at hwire; exact absurd hwire (by simp)
      | true =>
        have hcandtmk : u.2 cand = u.2 tmk := hc.mp rfl
        have htop : orank (u.2 tmk) = Nat.card A - 1 := orank_isTop hi.1.2.2.2
        have hC : orank (u.2 cand) = Nat.card A - 1 := by rw [hcandtmk]; exact htop
        have hYle : orank (u.2 y) ≤ Nat.card A - 1 := by
          have := orank_lt_card (u.2 y); omega
        rcases Nat.lt_or_ge (orank (u.2 y) / 2) (orank (u.2 cand)) with hlt | hge
        · obtain ⟨r, hr⟩ := hhalf u.2 hi.1.2.2.2 (orank (u.2 y) / 2) (by omega)
          have hrlt : r < u.2 cand := by
            refine lt_of_not_ge fun hcon => ?_
            have := orank_le_iff.mpr hcon
            omega
          obtain ⟨he, ho⟩ := hi.2.2.1 r hrlt
          rw [hr] at he ho
          omega
        · have : orank (u.2 y) = 0 := by omega
          exact hi.2.2.2 (by omega)
    | parProbe =>
      have hi : BitBase ih xh y cnt cand w tmk m x u.2 ∧ orank (u.2 cnt) = orank (x ih) ∧
          NoEven y cand u.2 := by
        have := hinv; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      cases c' with
      | false => rw [bitWire, if_neg (by simp)] at hwire; exact absurd hwire (by simp)
      | true =>
        have hcf : c = false := (Sum.inr.inj hwire).symm
        have heven : orank (u.2 cand) + orank (u.2 cand) = orank (u.2 y) := hc.mp rfl
        refine ⟨?_, ?_⟩
        · change c = true ↔ (orank (x xh)).testBit (orank (x ih)) = true
          rw [hcf, testBit_iff_mod, ← hi.2.1, ← hi.1.2.1]
          simp only [Bool.false_eq_true, false_iff]
          omega
        · exact (hprotect u.2 hi.1.1).trans (hag.mono hpm)
    | parOver =>
      have hi : BitBase ih xh y cnt cand w tmk m x u.2 ∧ orank (u.2 cnt) = orank (x ih) ∧
          NoEven y cand u.2 ∧ orank (u.2 cand) + orank (u.2 cand) ≠ orank (u.2 y) := by
        have := hinv; rw [hnode] at this; exact this
      rw [hnode] at hrel hwire
      obtain ⟨hc, hag⟩ := hrel
      cases c' with
      | false => rw [bitWire, if_neg (by simp)] at hwire; exact absurd hwire (by simp)
      | true =>
        have hct : c = true := (Sum.inr.inj hwire).symm
        have hcandtmk : u.2 cand = u.2 tmk := hc.mp rfl
        have htop : orank (u.2 tmk) = Nat.card A - 1 := orank_isTop hi.1.2.2.2
        have hC : orank (u.2 cand) = Nat.card A - 1 := by rw [hcandtmk]; exact htop
        have hYle : orank (u.2 y) ≤ Nat.card A - 1 := by
          have := orank_lt_card (u.2 y); omega
        have hodd : orank (u.2 y) % 2 = 1 := by
          by_contra hcon
          have hev : orank (u.2 y) / 2 + orank (u.2 y) / 2 = orank (u.2 y) := by omega
          rcases Nat.lt_or_ge (orank (u.2 y) / 2) (orank (u.2 cand)) with hlt | hge
          · obtain ⟨r, hr⟩ := exists_orank_eq (A := A) (m := orank (u.2 y) / 2)
              (lt_of_lt_of_le hlt (le_of_lt (orank_lt_card (u.2 cand))))
            have hrlt : r < u.2 cand := by
              refine lt_of_not_ge fun hco => ?_
              have := orank_le_iff.mpr hco
              omega
            exact hi.2.2.1 r hrlt (by rw [hr]; exact hev)
          · exact hi.2.2.2 (by omega)
        refine ⟨?_, ?_⟩
        · change c = true ↔ (orank (x xh)).testBit (orank (x ih)) = true
          rw [hct, testBit_iff_mod, ← hi.2.1, ← hi.1.2.1]
          simp only [true_iff]
          omega
        · exact (hprotect u.2 hi.1.1).trans (hag.mono hpm)
  · -- completeness: run the rounds, then the parity scan
    rintro x c z ⟨hc, hag⟩
    haveI : Nonempty A := ⟨x xh⟩
    change c = true ↔ (orank (x xh)).testBit (orank (x ih)) = true at hc
    obtain ⟨v, hwalk, hvcnt, hvy, hvtop, hvrest⟩ := walk_outer hh x (orank (x ih)) le_rfl
    obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := hh.ne_int hh.hih
    have hiheq : v ih = x ih :=
      hvrest ih (by have := hh.hih; have := hh.hm; have := hh.hpS; omega) hn1 hn2 hn3 hn4 hn5
    have hcnteq : v cnt = v ih := by
      rw [hiheq, ← orank_inj_iff (A := A), hvcnt]
    have hxy : ∀ v' : Fin K → A,
        (∀ q : Fin K, (q : ℕ) < m → q ≠ y → q ≠ cnt → q ≠ cand → q ≠ w → q ≠ tmk →
          v' q = x q) → HeadAgree p z v' := by
      intro v' hv' q hq
      obtain ⟨h1, h2, h3, h4, h5⟩ := hh.ne_int hq
      rw [← hag q hq]
      exact (hv' q (by omega) h1 h2 h3 h4 h5).symm
    -- reset the parity scan
    obtain ⟨c0, hc0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    set v0 := Function.update v cand c0 with hv0def
    have hv0c : v0 cand = c0 := by rw [hv0def, Function.update_self]
    have hv0o : ∀ q : Fin K, q ≠ cand → v0 q = v q := fun q hq => by
      rw [hv0def, Function.update_of_ne hq]
    have s1 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.outer, v) (.parInit, v) := ⟨true, ⟨by simp [hcnteq], HeadAgree.refl v⟩, rfl⟩
    have s2 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
        (.parInit, v) (.parProbe, v0) := by
      refine ⟨true, ⟨rfl, fun q hq => ?_⟩, rfl⟩
      by_cases hqc : q = cand
      · rw [bitScanInitMoves, if_pos hqc, hqc]
        change ∀ e : A, v0 cand ≤ e
        rw [hv0c]
        exact fun e => isMin_of_orank_eq_zero hc0 e
      · rw [bitScanInitMoves, if_neg hqc]
        change v0 q = v q
        exact hv0o q hqc
    have hv0y : v0 y = v y := hv0o y hh.ne_y_cand
    have hv0tmk : v0 tmk = v tmk := hv0o tmk (Ne.symm hh.ne_cand_tmk)
    have hwalk0 : BWalk ih xh y cnt cand w tmk m (.init, x) (.parProbe, v0) :=
      (hwalk.tail s1).tail s2
    have htopr : orank (v0 tmk) = Nat.card A - 1 := by rw [hv0tmk]; exact orank_isTop hvtop
    have hYle : orank (v0 y) ≤ orank (v0 tmk) := by
      rw [htopr]; have := orank_lt_card (v0 y); omega
    have hrest0 : ∀ q : Fin K, (q : ℕ) < m → q ≠ y → q ≠ cnt → q ≠ cand → q ≠ w → q ≠ tmk →
        v0 q = x q := fun q hq h1 h2 h3 h4 h5 => (hv0o q h3).trans (hvrest q hq h1 h2 h3 h4 h5)
    have hval : orank (v0 y) = orank (x xh) / 2 ^ orank (x ih) := by rw [hv0y]; exact hvy
    rcases Nat.even_or_odd (orank (v0 y)) with hev | hodd
    · -- the value is even: the scan stops at its half and the answer is `false`
      obtain ⟨k, hk⟩ := hev
      obtain ⟨v1, hw1, hcand1, hrest1⟩ := walk_par hh (z := v0)
        (by rw [hv0c]; exact fun e => isMin_of_orank_eq_zero hc0 e) k (by omega)
        (fun d hd => by omega)
      have hy1 : v1 y = v0 y := hrest1 y hym hh.ne_y_cand
      have hcf : c = false := by
        cases c with
        | false => rfl
        | true =>
          rw [testBit_iff_mod, ← hval] at hc
          have := hc.mp rfl
          omega
      refine ⟨v1, hxy v1 fun q hq h1 h2 h3 h4 h5 =>
        (hrest1 q hq h3).trans (hrest0 q hq h1 h2 h3 h4 h5),
        (.parProbe, v1), hwalk0.trans hw1, true, ⟨?_, HeadAgree.refl v1⟩, ?_⟩
      · simp only [true_iff]
        rw [hcand1, hy1]
        omega
      · rw [hcf]; rfl
    · -- the value is odd: the scan runs to the marker and the answer is `true`
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨v1, hw1, hcand1, hrest1⟩ := walk_par hh (z := v0)
        (by rw [hv0c]; exact fun e => isMin_of_orank_eq_zero hc0 e) (orank (v0 tmk)) le_rfl
        (fun d hd => by omega)
      have hy1 : v1 y = v0 y := hrest1 y hym hh.ne_y_cand
      have htmk1 : v1 tmk = v0 tmk := hrest1 tmk htmkm (Ne.symm hh.ne_cand_tmk)
      have hct : c = true := by
        rw [testBit_iff_mod, ← hval] at hc
        exact hc.mpr (by omega)
      have hnp : orank (v1 cand) + orank (v1 cand) ≠ orank (v1 y) := by
        rw [hcand1, hy1, htopr]
        omega
      have hcandtmk : v1 cand = v1 tmk := by
        rw [← orank_inj_iff (A := A), hcand1, htmk1]
      have hres : ∀ q : Fin K, (q : ℕ) < m → q ≠ y → q ≠ cnt → q ≠ cand → q ≠ w → q ≠ tmk →
          v1 q = x q := fun q hq h1 h2 h3 h4 h5 =>
        (hrest1 q hq h3).trans (hrest0 q hq h1 h2 h3 h4 h5)
      have s3 : wireStep (bitFamRel (A := A) ih xh y cnt cand w tmk m) bitWire
          (.parProbe, v1) (.parOver, v1) := ⟨false, ⟨by simp [hnp], HeadAgree.refl v1⟩, rfl⟩
      refine ⟨v1, hxy v1 hres, (.parOver, v1), (hwalk0.trans hw1).tail s3, true,
        ⟨by simp [hcandtmk], HeadAgree.refl v1⟩, ?_⟩
      rw [hct]; rfl

end Decides

end HeadProgram

end DescriptiveComplexity
