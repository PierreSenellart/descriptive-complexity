/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HornTape
import DescriptiveComplexity.Problems.Machine.Hardness
import DescriptiveComplexity.Problems.HornSat

/-!
# The unit-propagation machine of a Horn formula

The program half of `HORNSAT ≤ᶠᵒ[≤] DTMAccept`, the deterministic machine
bridge: the states, symbols and transitions of the deterministic machine
computing the unit-propagation closure of a CNF instance and verifying it, on
the tape laid out in `DescriptiveComplexity.Problems.Machine.HornTape`.

## The program

```
  init:      at ⊢, dispatch – first check sweep if a clause exists, else accept
  chk(r, c):  sweep right, f := f ∧ (negIn c x → marked x)
  mark(r, c): sweep back left; if the check succeeded, mark the positive
              literal of c in passing
  … next clause; after the last clause, next round; after the last round …
  ver(c):     sweep, f := f ∨ (posIn c x ∧ marked x) ∨ (negIn c x ∧ ¬marked x),
              alternating direction; a failed clause leaves no transition
  accept     after the last verified clause – gated on the Horn condition
```

`n` rounds of one check-and-mark pass per clause compute the propagation
closure `DescriptiveComplexity.Forced` (`DescriptiveComplexity.forced_forcedIn_card` is the
stabilization), and the verification phase accepts exactly when the closure,
read as an assignment, satisfies every clause – which for a Horn instance is
satisfiability itself (`DescriptiveComplexity.satisfiable_iff_forced_model`).

The machine is **deterministic everywhere** – there is no guess phase – and
`DescriptiveComplexity.TMData.Deterministic` for the constructed machine is part of
the statement, not bookkeeping: it is what makes the image a potential
yes-instance of `DTMAccept` at all. The instance is read exactly as by the SAT
machine (`DescriptiveComplexity.SatCl`, `DescriptiveComplexity.SatPos`, …,
imported from `DescriptiveComplexity.Problems.Machine.Hardness` together with
the clause-order machinery), and the only two additions are the element order
(rounds walk it) and the Horn gate on the accept transition.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

noncomputable section HornMachine

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The elements of the machine -/

/-- The universe of the machine: tagged triples. -/
abbrev HV (A : Type) := UPTag × (Fin 3 → A)

/-- A constant of the machine: a tag on the triple of least elements. -/
def cstH (t : UPTag) : HV A := (t, fun _ => botA)

/-- A tag carrying one element. -/
def oneH (t : UPTag) (a : A) : HV A := (t, ![a, botA, botA])

/-- A tag carrying two elements. -/
def twoH (t : UPTag) (a b : A) : HV A := (t, ![a, b, botA])

omit [Language.sat.Structure A] in
theorem isMinTup3_bot : IsMinTup3 (fun _ => botA (A := A)) :=
  ⟨fun a => botA_le a, fun a => botA_le a, fun a => botA_le a⟩

/-! #### Symbols -/

/-- The left-marker symbol. -/
abbrev symHStart : HV A := cstH .sStart

/-- The right-marker symbol. -/
abbrev symHEnd : HV A := cstH .sEnd

/-- The blank symbol. -/
abbrev symHBlank : HV A := cstH .sBlank

/-- The symbol of the cell of `x`, with mark `m`. -/
abbrev symCell (m : Bool) (x : A) : HV A := oneH (if m then .sM else .sU) x

/-! #### Positions -/

/-- The left-marker cell. -/
abbrev posHStart : HV A := cstH .pStart

/-- The cell of the element `x`. -/
abbrev posHCell (x : A) : HV A := oneH .pCell x

/-- The right-marker cell. -/
abbrev posHEnd : HV A := cstH .pEnd

/-! #### States -/

/-- The dispatch state. -/
abbrev stHInit : HV A := cstH .qInit

/-- Checking the clause `c` in round `r`, flag `f`. -/
abbrev stHChk (f : Bool) (r c : A) : HV A := twoH (.qChk f) r c

/-- The return sweep of clause `c` in round `r`, marking iff `m`. -/
abbrev stHMark (m : Bool) (r c : A) : HV A := twoH (.qMark m) r c

/-- Verifying the clause `c`, flag `f`, sweeping in direction `d`. -/
abbrev stHVer (f d : Bool) (c : A) : HV A := oneH (.qVer f d) c

/-- The accepting state. -/
abbrev stHAcc : HV A := cstH .qAcc

/-! ### Reading the order of the elements -/

/-- `a` is the least element. -/
def MinElt (a : A) : Prop := ∀ b : A, a ≤ b

/-- `a` is the greatest element. -/
def MaxElt (a : A) : Prop := ∀ b : A, b ≤ a

/-- `b` is the successor of `a` in the order of the elements: rounds walk this
relation. -/
def SuccElt (a b : A) : Prop := a < b ∧ ∀ z : A, a < z → b ≤ z

/-- The satisfaction test of the verification phase: the cell `x`, with mark
`m`, satisfies the clause `c` under the marked assignment. This is
`DescriptiveComplexity.SatLit` with the marks as the valuation. -/
def MLit (c x : A) (m : Bool) : Prop :=
  (SatPos c x ∧ m = true) ∨ (SatNeg c x ∧ m = false)

/-! ### The transition table -/

/-- Which tagged triples are transitions: the payload promises. Coordinates
not pinned by the source state or the symbol read are pinned here, so that no
junk element is a transition. -/
def HTr (τ : HV A) : Prop :=
  match τ.1 with
  | .tInitChk => MinElt (τ.2 0) ∧ SatMinCl (τ.2 1) ∧ (∀ a : A, τ.2 2 ≤ a)
  | .tInitAcc => IsMinTup3 τ.2 ∧ ∀ e : A, ¬ SatCl e
  | .tChk _ _ => SatCl (τ.2 1)
  | .tChkEnd _ => SatCl (τ.2 1) ∧ ∀ a : A, τ.2 2 ≤ a
  | .tMark _ _ => SatCl (τ.2 1)
  | .tMarkEndNext _ => SatNextCl (τ.2 1) (τ.2 2)
  | .tMarkEndRound _ => SuccElt (τ.2 0) (τ.2 1) ∧ SatMaxCl (τ.2 2)
  | .tMarkEndVer _ => MaxElt (τ.2 0) ∧ SatMaxCl (τ.2 1) ∧ (∀ a : A, τ.2 2 ≤ a)
  | .tVer _ _ _ => SatCl (τ.2 0) ∧ ∀ a : A, τ.2 2 ≤ a
  | .tVerNext _ => SatNextCl (τ.2 0) (τ.2 1) ∧ (∀ a : A, τ.2 2 ≤ a)
  | .tVerAcc _ => SatMaxCl (τ.2 0) ∧ (∀ a : A, τ.2 1 ≤ a) ∧ (∀ a : A, τ.2 2 ≤ a) ∧
      AtMostOnePositive A
  | _ => False

/-- The state a transition applies in. -/
def HSrc (τ q : HV A) : Prop :=
  match τ.1 with
  | .tInitChk => q = stHInit
  | .tInitAcc => q = stHInit
  | .tChk _ f => q = stHChk f (τ.2 0) (τ.2 1)
  | .tChkEnd f => q = stHChk f (τ.2 0) (τ.2 1)
  | .tMark _ mrk => q = stHMark mrk (τ.2 0) (τ.2 1)
  | .tMarkEndNext mrk => q = stHMark mrk (τ.2 0) (τ.2 1)
  | .tMarkEndRound mrk => q = stHMark mrk (τ.2 0) (τ.2 2)
  | .tMarkEndVer mrk => q = stHMark mrk (τ.2 0) (τ.2 1)
  | .tVer _ f d => q = stHVer f d (τ.2 0)
  | .tVerNext d => q = stHVer true d (τ.2 0)
  | .tVerAcc d => q = stHVer true d (τ.2 0)
  | _ => False

/-- The symbol a transition reads. -/
def HRead (τ a : HV A) : Prop :=
  match τ.1 with
  | .tInitChk => a = symHStart
  | .tInitAcc => a = symHStart
  | .tChk m _ => a = symCell m (τ.2 2)
  | .tChkEnd _ => a = symHEnd
  | .tMark m _ => a = symCell m (τ.2 2)
  | .tMarkEndNext _ => a = symHStart
  | .tMarkEndRound _ => a = symHStart
  | .tMarkEndVer _ => a = symHStart
  | .tVer m _ _ => a = symCell m (τ.2 1)
  | .tVerNext d => a = if d then symHEnd else symHStart
  | .tVerAcc d => a = if d then symHEnd else symHStart
  | _ => False

/-- The state a transition moves to. The check and verification sweeps branch
on a first-order test of the source instance; each pair of branches is
exclusive, which is what keeps the table functional. -/
def HDst (τ q : HV A) : Prop :=
  match τ.1 with
  | .tInitChk => q = stHChk true (τ.2 0) (τ.2 1)
  | .tInitAcc => q = stHAcc
  | .tChk m f =>
      (q = stHChk true (τ.2 0) (τ.2 1) ∧ f = true ∧ (SatNeg (τ.2 1) (τ.2 2) → m = true)) ∨
        (q = stHChk false (τ.2 0) (τ.2 1) ∧
          (f = false ∨ (SatNeg (τ.2 1) (τ.2 2) ∧ m = false)))
  | .tChkEnd f => q = stHMark f (τ.2 0) (τ.2 1)
  | .tMark _ mrk => q = stHMark mrk (τ.2 0) (τ.2 1)
  | .tMarkEndNext _ => q = stHChk true (τ.2 0) (τ.2 2)
  | .tMarkEndRound _ =>
      q.1 = UPTag.qChk true ∧ q.2 0 = τ.2 1 ∧ SatMinCl (q.2 1) ∧ ∀ a : A, q.2 2 ≤ a
  | .tMarkEndVer _ =>
      q.1 = UPTag.qVer false true ∧ SatMinCl (q.2 0) ∧ (∀ a : A, q.2 1 ≤ a) ∧
        ∀ a : A, q.2 2 ≤ a
  | .tVer m f d =>
      (q = stHVer true d (τ.2 0) ∧ (f = true ∨ MLit (τ.2 0) (τ.2 1) m)) ∨
        (q = stHVer false d (τ.2 0) ∧ f = false ∧ ¬ MLit (τ.2 0) (τ.2 1) m)
  | .tVerNext d => q = stHVer false (!d) (τ.2 1)
  | .tVerAcc _ => q = stHAcc
  | _ => False

/-- The symbol a transition writes: only the return sweep of a successful
check writes anything new, and only at the positive literal of its clause. -/
def HWrite (τ a : HV A) : Prop :=
  match τ.1 with
  | .tInitChk => a = symHStart
  | .tInitAcc => a = symHStart
  | .tChk m _ => a = symCell m (τ.2 2)
  | .tChkEnd _ => a = symHEnd
  | .tMark m mrk =>
      (a = symCell true (τ.2 2) ∧ mrk = true ∧ SatPos (τ.2 1) (τ.2 2)) ∨
        (a = symCell m (τ.2 2) ∧ (mrk = false ∨ ¬ SatPos (τ.2 1) (τ.2 2)))
  | .tMarkEndNext _ => a = symHStart
  | .tMarkEndRound _ => a = symHStart
  | .tMarkEndVer _ => a = symHStart
  | .tVer m _ _ => a = symCell m (τ.2 1)
  | .tVerNext d => a = if d then symHEnd else symHStart
  | .tVerAcc d => a = if d then symHEnd else symHStart
  | _ => False

/-- Which transitions move the head right. -/
def HRight (τ : HV A) : Prop :=
  match τ.1 with
  | .tInitChk => True
  | .tInitAcc => True
  | .tChk _ _ => True
  | .tChkEnd _ => False
  | .tMark _ _ => False
  | .tMarkEndNext _ => True
  | .tMarkEndRound _ => True
  | .tMarkEndVer _ => True
  | .tVer _ _ d => d = true
  | .tVerNext d => d = false
  | .tVerAcc d => d = false
  | _ => False

/-- Accepting states. -/
def HAcc (q : HV A) : Prop := q.1 = UPTag.qAcc

/-- Start states: the dispatch state alone. -/
def HStart (q : HV A) : Prop := q.1 = UPTag.qInit ∧ IsMinTup3 q.2

/-- **The unit-propagation machine of a CNF instance.** -/
def hornMachine (A : Type) [Language.sat.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] : TMData (HV A) where
  Posn := HPosn
  Le := tagTupleLe
  Tr := HTr
  Start := HStart
  Acc := HAcc
  Blank := HBlank
  Right := HRight
  Src := HSrc
  Read := HRead
  Dst := HDst
  Write := HWrite
  Inp := HInp

/-! ### The machine is well formed -/

/-- **The machine is well formed**: every conjunct comes from the tape
layer. -/
theorem hornMachine_wellFormed : (hornMachine A).WellFormed :=
  ⟨isLinOrd_hTagTupleLe, exists_hPosn, fun _ _ _ ha hb => hInp_functional ha hb,
    exists_hBlank, fun _ _ ha hb => hBlank_unique ha hb⟩

/-! ### The machine is deterministic

There is no guess phase, so – unlike the SAT machine – the whole table is
functional: the state and the symbol read pin the transition's tag up to
promise-exclusive alternatives, the tag pins the payload, and the branching
destinations and writes are separated by their first-order tests. This
discharges the `DescriptiveComplexity.TMData.Deterministic` promise of the
constructed instance, which is part of the correctness of the reduction. -/

section Deterministic

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- Two elements agree when their tag and all three coordinates do. -/
theorem hV_ext {τ τ' : HV A} (ht : τ.1 = τ'.1) (h0 : τ.2 0 = τ'.2 0)
    (h1 : τ.2 1 = τ'.2 1) (h2 : τ.2 2 = τ'.2 2) : τ = τ' := by
  refine Prod.ext ht (funext fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

omit [Language.sat.Structure A] in
theorem oneH_eq_oneH_iff {t t' : UPTag} {a a' : A} :
    (oneH t a : HV A) = oneH t' a' ↔ t = t' ∧ a = a' := by
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, ?_⟩
    have := congrFun (congrArg Prod.snd h) 0
    simpa [oneH] using this
  · rintro ⟨rfl, rfl⟩; rfl

omit [Language.sat.Structure A] in
theorem twoH_eq_twoH_iff {t t' : UPTag} {a a' b b' : A} :
    (twoH t a b : HV A) = twoH t' a' b' ↔ t = t' ∧ a = a' ∧ b = b' := by
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, ?_, ?_⟩
    · have := congrFun (congrArg Prod.snd h) 0
      simpa [twoH] using this
    · have := congrFun (congrArg Prod.snd h) 1
      simpa [twoH] using this
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- The tag of the state a transition applies in. -/
def hStateTag : UPTag → UPTag
  | .tInitChk => .qInit
  | .tInitAcc => .qInit
  | .tChk _ f => .qChk f
  | .tChkEnd f => .qChk f
  | .tMark _ mrk => .qMark mrk
  | .tMarkEndNext mrk => .qMark mrk
  | .tMarkEndRound mrk => .qMark mrk
  | .tMarkEndVer mrk => .qMark mrk
  | .tVer _ f d => .qVer f d
  | .tVerNext d => .qVer true d
  | .tVerAcc d => .qVer true d
  | t => t

/-- The tag of the symbol a transition reads. -/
def hReadTag : UPTag → UPTag
  | .tInitChk => .sStart
  | .tInitAcc => .sStart
  | .tChk m _ => if m then .sM else .sU
  | .tChkEnd _ => .sEnd
  | .tMark m _ => if m then .sM else .sU
  | .tMarkEndNext _ => .sStart
  | .tMarkEndRound _ => .sStart
  | .tMarkEndVer _ => .sStart
  | .tVer m _ _ => if m then .sM else .sU
  | .tVerNext d => if d then .sEnd else .sStart
  | .tVerAcc d => if d then .sEnd else .sStart
  | t => t

/-- Being the tag of a transition. -/
def isHTrTag : UPTag → Bool
  | .tInitChk | .tInitAcc | .tChk _ _ | .tChkEnd _ | .tMark _ _
  | .tMarkEndNext _ | .tMarkEndRound _ | .tMarkEndVer _
  | .tVer _ _ _ | .tVerNext _ | .tVerAcc _ => true
  | _ => false

omit [Finite A] [Nonempty A] in
/-- Only transitions have transition tags. -/
theorem hTr_isHTrTag {τ : HV A} (hτ : HTr τ) : isHTrTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> first | exact False.elim hτ | rfl

omit [Language.sat.Structure A] in
/-- **The state pins the transition's tag.** -/
theorem hSrc_tag {τ q : HV A} (hs : HSrc τ q) : q.1 = hStateTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> dsimp only [HSrc] at hs <;>
    first
      | exact False.elim hs
      | (rw [hs]; rfl)

omit [Language.sat.Structure A] in
/-- **The symbol read pins the transition's tag.** -/
theorem hRead_tag {τ a : HV A} (hr : HRead τ a) : a.1 = hReadTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> dsimp only [HRead] at hr <;>
    first
      | exact False.elim hr
      | (rw [hr]; rfl)
      | (rename_i b; cases b <;> (rw [hr]; rfl))

/-- Tag classes for the promise-exclusive alternatives. -/
def isInitChk : UPTag → Bool | .tInitChk => true | _ => false

@[inherit_doc isInitChk] def isInitAcc : UPTag → Bool | .tInitAcc => true | _ => false

@[inherit_doc isInitChk] def isMarkEndNext : UPTag → Bool
  | .tMarkEndNext _ => true | _ => false

@[inherit_doc isInitChk] def isMarkEndRound : UPTag → Bool
  | .tMarkEndRound _ => true | _ => false

@[inherit_doc isInitChk] def isMarkEndVer : UPTag → Bool
  | .tMarkEndVer _ => true | _ => false

@[inherit_doc isInitChk] def isVerNext : UPTag → Bool | .tVerNext _ => true | _ => false

@[inherit_doc isInitChk] def isVerAcc : UPTag → Bool | .tVerAcc _ => true | _ => false

set_option maxRecDepth 8000 in
/-- **The state and the symbol determine the transition's tag**, up to the
promise-exclusive alternatives: the two dispatches, the three ends of a return
sweep, and the two ends of a verification sweep. A finite check over the
tags. -/
theorem hTag_cases : ∀ t t' : UPTag, isHTrTag t → isHTrTag t' →
    hStateTag t = hStateTag t' → hReadTag t = hReadTag t' →
    t = t' ∨
      ((isInitChk t ∨ isInitAcc t) ∧ (isInitChk t' ∨ isInitAcc t')) ∨
      ((isMarkEndNext t ∨ isMarkEndRound t ∨ isMarkEndVer t) ∧
        (isMarkEndNext t' ∨ isMarkEndRound t' ∨ isMarkEndVer t')) ∨
      ((isVerNext t ∨ isVerAcc t) ∧ (isVerNext t' ∨ isVerAcc t')) := by
  decide

omit [Finite A] [Nonempty A] in
/-- The lowest clause is unique. -/
theorem satMinCl_unique {c c' : A} (h : SatMinCl c) (h' : SatMinCl c') : c = c' :=
  le_antisymm (h.2 c' h'.1) (h'.2 c h.1)

omit [Finite A] [Nonempty A] in
/-- The next clause is unique. -/
theorem satNextCl_unique {c c' c'' : A} (h : SatNextCl c c') (h' : SatNextCl c c'') :
    c' = c'' :=
  le_antisymm (h.2.2.2 c'' h'.2.1 h'.2.2.1) (h'.2.2.2 c' h.2.1 h.2.2.1)

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
/-- The least element is unique. -/
theorem minElt_unique {a a' : A} (h : MinElt a) (h' : MinElt a') : a = a' :=
  le_antisymm (h a') (h' a)

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
/-- The successor of an element is unique. -/
theorem succElt_unique {a b b' : A} (h : SuccElt a b) (h' : SuccElt a b') : b = b' :=
  le_antisymm (h.2 b' h'.1) (h'.2 b h.1)

/-- **Equal tags force equal payloads**: the source state and the symbol read
pin two coordinates, the promises the rest. -/
theorem hTr_payload {τ τ' q a : HV A} (hτ : HTr τ) (hτ' : HTr τ')
    (hs : HSrc τ q) (hs' : HSrc τ' q) (hr : HRead τ a) (hr' : HRead τ' a)
    (ht : τ.1 = τ'.1) : τ = τ' := by
  have hmin : ∀ u v : A, (∀ b : A, u ≤ b) → (∀ b : A, v ≤ b) → u = v :=
    fun u v hu hv => le_antisymm (hu v) (hv u)
  obtain ⟨t, w⟩ := τ
  obtain ⟨t', w'⟩ := τ'
  cases ht
  cases t <;> dsimp only [HTr, HSrc, HRead] at hτ hτ' hs hs' hr hr'
  case tInitChk =>
    exact hV_ext rfl (minElt_unique hτ.1 hτ'.1) (satMinCl_unique hτ.2.1 hτ'.2.1)
      (hmin _ _ hτ.2.2 hτ'.2.2)
  case tInitAcc =>
    exact Prod.ext rfl (isMinTup3_unique hτ.1 hτ'.1)
  case tChk m f =>
    obtain ⟨-, h1, h2⟩ := twoH_eq_twoH_iff.mp (hs.symm.trans hs')
    exact hV_ext rfl h1 h2 (oneH_eq_oneH_iff.mp (hr.symm.trans hr')).2
  case tChkEnd f =>
    obtain ⟨-, h1, h2⟩ := twoH_eq_twoH_iff.mp (hs.symm.trans hs')
    exact hV_ext rfl h1 h2 (hmin _ _ hτ.2 hτ'.2)
  case tMark m mrk =>
    obtain ⟨-, h1, h2⟩ := twoH_eq_twoH_iff.mp (hs.symm.trans hs')
    exact hV_ext rfl h1 h2 (oneH_eq_oneH_iff.mp (hr.symm.trans hr')).2
  case tMarkEndNext mrk =>
    obtain ⟨-, h1, h2⟩ := twoH_eq_twoH_iff.mp (hs.symm.trans hs')
    refine hV_ext rfl h1 h2 ?_
    rw [h2] at hτ
    exact satNextCl_unique hτ hτ'
  case tMarkEndRound mrk =>
    obtain ⟨-, h1, h2⟩ := twoH_eq_twoH_iff.mp (hs.symm.trans hs')
    refine hV_ext rfl h1 ?_ h2
    have hsc := hτ.1
    rw [h1] at hsc
    exact succElt_unique hsc hτ'.1
  case tMarkEndVer mrk =>
    obtain ⟨-, h1, h2⟩ := twoH_eq_twoH_iff.mp (hs.symm.trans hs')
    exact hV_ext rfl h1 h2 (hmin _ _ hτ.2.2 hτ'.2.2)
  case tVer m f d =>
    obtain ⟨-, h1⟩ := oneH_eq_oneH_iff.mp (hs.symm.trans hs')
    exact hV_ext rfl h1 (oneH_eq_oneH_iff.mp (hr.symm.trans hr')).2
      (hmin _ _ hτ.2 hτ'.2)
  case tVerNext d =>
    obtain ⟨-, h1⟩ := oneH_eq_oneH_iff.mp (hs.symm.trans hs')
    refine hV_ext rfl h1 ?_ (hmin _ _ hτ.2 hτ'.2)
    have hne := hτ.1
    rw [h1] at hne
    exact satNextCl_unique hne hτ'.1
  case tVerAcc d =>
    obtain ⟨-, h1⟩ := oneH_eq_oneH_iff.mp (hs.symm.trans hs')
    exact hV_ext rfl h1 (hmin _ _ hτ.2.1 hτ'.2.1) (hmin _ _ hτ.2.2.1 hτ'.2.2.1)

/-! #### The promise-exclusive alternatives -/

omit [Finite A] [Nonempty A] in
/-- The two dispatches exclude each other. -/
theorem hTr_init_excl {τ τ' : HV A} (h : HTr τ) (h' : HTr τ')
    (hτ : τ.1 = UPTag.tInitChk) (hτ' : τ'.1 = UPTag.tInitAcc) : False := by
  unfold HTr at h h'
  rw [hτ] at h
  rw [hτ'] at h'
  exact h'.2 _ h.2.1.1

omit [Finite A] [Nonempty A] in
/-- A clause with a next one is not the last. -/
theorem hTr_next_max_excl {c c' cm : A} (hnext : SatNextCl c c') (hmax : SatMaxCl cm)
    (hc : c = cm) : False := by
  subst hc
  exact absurd (hmax.2 _ hnext.2.1) (not_le.mpr hnext.2.2.1)

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
/-- An element with a successor is not the greatest. -/
theorem succElt_maxElt_excl {r r' rm : A} (hsucc : SuccElt r r') (hmax : MaxElt rm)
    (hr : r = rm) : False := by
  subst hr
  exact absurd (hmax r') (not_le.mpr hsucc.1)

theorem isInitChk_iff {t : UPTag} : isInitChk t ↔ t = .tInitChk := by
  cases t <;> simp [isInitChk]

theorem isInitAcc_iff {t : UPTag} : isInitAcc t ↔ t = .tInitAcc := by
  cases t <;> simp [isInitAcc]

theorem isMarkEndNext_iff {t : UPTag} : isMarkEndNext t ↔ ∃ mrk, t = .tMarkEndNext mrk := by
  cases t <;> simp [isMarkEndNext]

theorem isMarkEndRound_iff {t : UPTag} : isMarkEndRound t ↔ ∃ mrk, t = .tMarkEndRound mrk := by
  cases t <;> simp [isMarkEndRound]

theorem isMarkEndVer_iff {t : UPTag} : isMarkEndVer t ↔ ∃ mrk, t = .tMarkEndVer mrk := by
  cases t <;> simp [isMarkEndVer]

theorem isVerNext_iff {t : UPTag} : isVerNext t ↔ ∃ d, t = .tVerNext d := by
  cases t <;> simp [isVerNext]

theorem isVerAcc_iff {t : UPTag} : isVerAcc t ↔ ∃ d, t = .tVerAcc d := by
  cases t <;> simp [isVerAcc]

omit [Language.sat.Structure A] in
/-- Reading `DescriptiveComplexity.HSrc` off a concrete tag: the payload equations
all flow through this. -/
theorem hSrc_eq {τ q : HV A} (hs : HSrc τ q) :
    ∀ t', τ.1 = t' →
      (match t' with
        | .tInitChk => q = stHInit
        | .tInitAcc => q = stHInit
        | .tChk _ f => q = stHChk f (τ.2 0) (τ.2 1)
        | .tChkEnd f => q = stHChk f (τ.2 0) (τ.2 1)
        | .tMark _ mrk => q = stHMark mrk (τ.2 0) (τ.2 1)
        | .tMarkEndNext mrk => q = stHMark mrk (τ.2 0) (τ.2 1)
        | .tMarkEndRound mrk => q = stHMark mrk (τ.2 0) (τ.2 2)
        | .tMarkEndVer mrk => q = stHMark mrk (τ.2 0) (τ.2 1)
        | .tVer _ f d => q = stHVer f d (τ.2 0)
        | .tVerNext d => q = stHVer true d (τ.2 0)
        | .tVerAcc d => q = stHVer true d (τ.2 0)
        | _ => False) := by
  obtain ⟨t, w⟩ := τ
  rintro t' rfl
  exact hs

omit [Finite A] [Nonempty A] in
/-- Reading `DescriptiveComplexity.HTr` off a concrete tag. -/
theorem hTr_at {τ : HV A} (hτ : HTr τ) :
    ∀ t', τ.1 = t' →
      (match t' with
        | .tInitChk => MinElt (τ.2 0) ∧ SatMinCl (τ.2 1) ∧ (∀ a : A, τ.2 2 ≤ a)
        | .tInitAcc => IsMinTup3 τ.2 ∧ ∀ e : A, ¬ SatCl e
        | .tChk _ _ => SatCl (τ.2 1)
        | .tChkEnd _ => SatCl (τ.2 1) ∧ ∀ a : A, τ.2 2 ≤ a
        | .tMark _ _ => SatCl (τ.2 1)
        | .tMarkEndNext _ => SatNextCl (τ.2 1) (τ.2 2)
        | .tMarkEndRound _ => SuccElt (τ.2 0) (τ.2 1) ∧ SatMaxCl (τ.2 2)
        | .tMarkEndVer _ => MaxElt (τ.2 0) ∧ SatMaxCl (τ.2 1) ∧ (∀ a : A, τ.2 2 ≤ a)
        | .tVer _ _ _ => SatCl (τ.2 0) ∧ ∀ a : A, τ.2 2 ≤ a
        | .tVerNext _ => SatNextCl (τ.2 0) (τ.2 1) ∧ (∀ a : A, τ.2 2 ≤ a)
        | .tVerAcc _ => SatMaxCl (τ.2 0) ∧ (∀ a : A, τ.2 1 ≤ a) ∧ (∀ a : A, τ.2 2 ≤ a) ∧
            AtMostOnePositive A
        | _ => False) := by
  obtain ⟨t, w⟩ := τ
  rintro t' rfl
  exact hτ

/-- **At most one transition applies, everywhere**: the machine has no guess
phase, so this is the whole of transition-level determinism. The three
ambiguity classes left by `DescriptiveComplexity.hTag_cases` are separated by their
promises: a clause with a next one is not the last, an element with a
successor is not the greatest, and an instance either has a clause or has
none. -/
theorem hTr_unique {τ τ' q a : HV A} (hτ : HTr τ) (hτ' : HTr τ')
    (hs : HSrc τ q) (hs' : HSrc τ' q) (hr : HRead τ a) (hr' : HRead τ' a) : τ = τ' := by
  have hst : hStateTag τ.1 = hStateTag τ'.1 := (hSrc_tag hs).symm.trans (hSrc_tag hs')
  have hrd : hReadTag τ.1 = hReadTag τ'.1 := (hRead_tag hr).symm.trans (hRead_tag hr')
  have hpay : τ.1 = τ'.1 → τ = τ' := fun h => hTr_payload hτ hτ' hs hs' hr hr' h
  rcases hTag_cases τ.1 τ'.1 (hTr_isHTrTag hτ) (hTr_isHTrTag hτ') hst hrd with
    heq | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hpay heq
  · -- the two dispatches
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hpay ((isInitChk_iff.mp h1).trans (isInitChk_iff.mp h2).symm)
    · exact absurd (hTr_init_excl hτ hτ' (isInitChk_iff.mp h1) (isInitAcc_iff.mp h2)) not_false
    · exact absurd (hTr_init_excl hτ' hτ (isInitChk_iff.mp h2) (isInitAcc_iff.mp h1)) not_false
    · exact hpay ((isInitAcc_iff.mp h1).trans (isInitAcc_iff.mp h2).symm)
  · -- the three ends of a return sweep
    have hend : ∀ {σ σ' : HV A} {m m' : Bool}, HTr σ → HTr σ' → HSrc σ q → HSrc σ' q →
        σ.1 = UPTag.tMarkEndNext m →
        (σ'.1 = UPTag.tMarkEndRound m' ∨ σ'.1 = UPTag.tMarkEndVer m') → False := by
      intro σ σ' m m' hσ hσ' hsσ hsσ' h h'
      have hnext := hTr_at hσ _ h
      have hq := hSrc_eq hsσ _ h
      rcases h' with h' | h'
      · have hq' := hSrc_eq hsσ' _ h'
        obtain ⟨-, -, hcc⟩ := twoH_eq_twoH_iff.mp (hq.symm.trans hq')
        exact hTr_next_max_excl hnext (hTr_at hσ' _ h').2 hcc
      · have hq' := hSrc_eq hsσ' _ h'
        obtain ⟨-, -, hcc⟩ := twoH_eq_twoH_iff.mp (hq.symm.trans hq')
        exact hTr_next_max_excl hnext (hTr_at hσ' _ h').2.1 hcc
    have hrv : ∀ {σ σ' : HV A} {m m' : Bool}, HTr σ → HTr σ' → HSrc σ q → HSrc σ' q →
        σ.1 = UPTag.tMarkEndRound m → σ'.1 = UPTag.tMarkEndVer m' → False := by
      intro σ σ' m m' hσ hσ' hsσ hsσ' h h'
      have hq := hSrc_eq hsσ _ h
      have hq' := hSrc_eq hsσ' _ h'
      obtain ⟨-, hrr, -⟩ := twoH_eq_twoH_iff.mp (hq.symm.trans hq')
      exact succElt_maxElt_excl (hTr_at hσ _ h).1 (hTr_at hσ' _ h').1 hrr
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
    · obtain ⟨m, hm⟩ := isMarkEndNext_iff.mp h1
      obtain ⟨m', hm'⟩ := isMarkEndNext_iff.mp h2
      obtain ⟨he, -, -⟩ := twoH_eq_twoH_iff.mp ((hSrc_eq hs _ hm).symm.trans (hSrc_eq hs' _ hm'))
      exact hpay (by rw [hm, hm', UPTag.qMark.inj he])
    · exact absurd (hend hτ hτ' hs hs' (isMarkEndNext_iff.mp h1).choose_spec
        (Or.inl (isMarkEndRound_iff.mp h2).choose_spec)) not_false
    · exact absurd (hend hτ hτ' hs hs' (isMarkEndNext_iff.mp h1).choose_spec
        (Or.inr (isMarkEndVer_iff.mp h2).choose_spec)) not_false
    · exact absurd (hend hτ' hτ hs' hs (isMarkEndNext_iff.mp h2).choose_spec
        (Or.inl (isMarkEndRound_iff.mp h1).choose_spec)) not_false
    · obtain ⟨m, hm⟩ := isMarkEndRound_iff.mp h1
      obtain ⟨m', hm'⟩ := isMarkEndRound_iff.mp h2
      obtain ⟨he, -, -⟩ := twoH_eq_twoH_iff.mp ((hSrc_eq hs _ hm).symm.trans (hSrc_eq hs' _ hm'))
      exact hpay (by rw [hm, hm', UPTag.qMark.inj he])
    · exact absurd (hrv hτ hτ' hs hs' (isMarkEndRound_iff.mp h1).choose_spec
        (isMarkEndVer_iff.mp h2).choose_spec) not_false
    · exact absurd (hend hτ' hτ hs' hs (isMarkEndNext_iff.mp h2).choose_spec
        (Or.inr (isMarkEndVer_iff.mp h1).choose_spec)) not_false
    · exact absurd (hrv hτ' hτ hs' hs (isMarkEndRound_iff.mp h2).choose_spec
        (isMarkEndVer_iff.mp h1).choose_spec) not_false
    · obtain ⟨m, hm⟩ := isMarkEndVer_iff.mp h1
      obtain ⟨m', hm'⟩ := isMarkEndVer_iff.mp h2
      obtain ⟨he, -, -⟩ := twoH_eq_twoH_iff.mp ((hSrc_eq hs _ hm).symm.trans (hSrc_eq hs' _ hm'))
      exact hpay (by rw [hm, hm', UPTag.qMark.inj he])
  · -- the two ends of a verification sweep
    have hva : ∀ {σ σ' : HV A} {d d' : Bool}, HTr σ → HTr σ' → HSrc σ q → HSrc σ' q →
        σ.1 = UPTag.tVerNext d → σ'.1 = UPTag.tVerAcc d' → False := by
      intro σ σ' d d' hσ hσ' hsσ hsσ' h h'
      have hq := hSrc_eq hsσ _ h
      have hq' := hSrc_eq hsσ' _ h'
      obtain ⟨-, hcc⟩ := oneH_eq_oneH_iff.mp (hq.symm.trans hq')
      exact hTr_next_max_excl (hTr_at hσ _ h).1 (hTr_at hσ' _ h').1 hcc
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · obtain ⟨d, hd⟩ := isVerNext_iff.mp h1
      obtain ⟨d', hd'⟩ := isVerNext_iff.mp h2
      obtain ⟨he, -⟩ := oneH_eq_oneH_iff.mp ((hSrc_eq hs _ hd).symm.trans (hSrc_eq hs' _ hd'))
      exact hpay (by rw [hd, hd', (UPTag.qVer.inj he).2])
    · exact absurd (hva hτ hτ' hs hs' (isVerNext_iff.mp h1).choose_spec
        (isVerAcc_iff.mp h2).choose_spec) not_false
    · exact absurd (hva hτ' hτ hs' hs (isVerNext_iff.mp h2).choose_spec
        (isVerAcc_iff.mp h1).choose_spec) not_false
    · obtain ⟨d, hd⟩ := isVerAcc_iff.mp h1
      obtain ⟨d', hd'⟩ := isVerAcc_iff.mp h2
      obtain ⟨he, -⟩ := oneH_eq_oneH_iff.mp ((hSrc_eq hs _ hd).symm.trans (hSrc_eq hs' _ hd'))
      exact hpay (by rw [hd, hd', (UPTag.qVer.inj he).2])

/-- A transition moves to exactly one state: the branching destinations are
separated by their flags and their first-order tests, and the two relational
destinations are pinned by uniqueness of the lowest clause. -/
theorem hDst_functional {τ q q' : HV A} (h : HDst τ q) (h' : HDst τ q') : q = q' := by
  unfold HDst at h h'
  cases hτ : τ.1 <;> rw [hτ] at h h' <;> simp only at h h'
  case tChk m f =>
    rcases h with ⟨hq, hf, hm⟩ | ⟨hq, hcase⟩ <;>
      rcases h' with ⟨hq', hf', hm'⟩ | ⟨hq', hcase'⟩
    · exact hq.trans hq'.symm
    · rcases hcase' with hf' | ⟨hneg, hm'⟩
      · exact absurd (hf.symm.trans hf') (by decide)
      · exact absurd ((hm hneg).symm.trans hm') (by decide)
    · rcases hcase with hf | ⟨hneg, hm⟩
      · exact absurd (hf'.symm.trans hf) (by decide)
      · exact absurd ((hm' hneg).symm.trans hm) (by decide)
    · exact hq.trans hq'.symm
  case tVer m f d =>
    rcases h with ⟨hq, hcase⟩ | ⟨hq, hf, hlit⟩ <;>
      rcases h' with ⟨hq', hcase'⟩ | ⟨hq', hf', hlit'⟩
    · exact hq.trans hq'.symm
    · rcases hcase with hc | hc
      · exact absurd (hc.symm.trans hf') (by decide)
      · exact absurd hc hlit'
    · rcases hcase' with hc | hc
      · exact absurd (hc.symm.trans hf) (by decide)
      · exact absurd hc hlit
    · exact hq.trans hq'.symm
  case tMarkEndRound mrk =>
    obtain ⟨ht1, ht2, hmc, hm3⟩ := h
    obtain ⟨ht1', ht2', hmc', hm3'⟩ := h'
    exact hV_ext (ht1.trans ht1'.symm) (ht2.trans ht2'.symm) (satMinCl_unique hmc hmc')
      (le_antisymm (hm3 _) (hm3' _))
  case tMarkEndVer mrk =>
    obtain ⟨ht1, hmc, hm2, hm3⟩ := h
    obtain ⟨ht1', hmc', hm2', hm3'⟩ := h'
    exact hV_ext (ht1.trans ht1'.symm) (satMinCl_unique hmc hmc')
      (le_antisymm (hm2 _) (hm2' _)) (le_antisymm (hm3 _) (hm3' _))
  all_goals exact h.trans h'.symm

/-- A transition writes exactly one symbol: the marking write's two branches
are separated by the marking bit and the positive-literal test. -/
theorem hWrite_functional {τ a a' : HV A} (h : HWrite τ a) (h' : HWrite τ a') : a = a' := by
  unfold HWrite at h h'
  cases hτ : τ.1 <;> rw [hτ] at h h' <;> simp only at h h'
  case tMark m mrk =>
    rcases h with ⟨ha, hmk, hpos⟩ | ⟨ha, hcase⟩ <;>
      rcases h' with ⟨ha', hmk', hpos'⟩ | ⟨ha', hcase'⟩
    · exact ha.trans ha'.symm
    · rcases hcase' with hmk' | hpos'
      · exact absurd (hmk.symm.trans hmk') (by decide)
      · exact absurd hpos hpos'
    · rcases hcase with hmk | hpos
      · exact absurd (hmk'.symm.trans hmk) (by decide)
      · exact absurd hpos' hpos
    · exact ha.trans ha'.symm
  all_goals exact h.trans h'.symm

/-- **The machine is deterministic** – the promise
`DescriptiveComplexity.DTMAccept` folds into its yes-instances, discharged here for
every image of the reduction, Horn or not. -/
theorem hornMachine_deterministic : (hornMachine A).Deterministic := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro q q' ⟨ht, hw⟩ ⟨ht', hw'⟩
    exact Prod.ext (ht.trans ht'.symm) (isMinTup3_unique hw hw')
  · exact fun τ τ' q a hτ hτ' hs hs' hr hr' => hTr_unique hτ hτ' hs hs' hr hr'
  · exact fun τ q q' hd hd' => hDst_functional hd hd'
  · exact fun τ a a' hw hw' => hWrite_functional hw hw'

end Deterministic

/-! ### The positions of the tape, concretely

The dimension-3 mirror of the SAT machine's marker and cell lemmas: the left
marker is the lowest position, cells follow in the order of their elements, the
right marker closes the chain, and ranks are what the budget compares. -/

section Order

omit [Language.sat.Structure A] in
theorem hPosn_posHStart : HPosn (posHStart : HV A) :=
  ⟨fun a => botA_le a, fun a => botA_le a, fun a => botA_le a⟩

omit [Language.sat.Structure A] in
theorem hPosn_posHCell (x : A) : HPosn (posHCell x : HV A) :=
  ⟨fun a => botA_le a, fun a => botA_le a⟩

omit [Language.sat.Structure A] in
theorem hPosn_posHEnd : HPosn (posHEnd : HV A) :=
  ⟨fun a => botA_le a, fun a => botA_le a, fun a => botA_le a⟩

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
theorem hTagTupleLe_refl (p : HV A) : tagTupleLe p p := Or.inr ⟨rfl, Or.inl rfl⟩

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
theorem hTagTupleLe_of_tag_lt {p q : HV A} (h : p.1 < q.1) : tagTupleLe p q := Or.inl h

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
theorem hTagTupleLe_tag_le {p q : HV A} (h : tagTupleLe p q) : p.1 ≤ q.1 := by
  rcases h with h | ⟨h, -⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- Every tag other than the left marker's is above it. -/
theorem hpStart_lt {t : UPTag} (h : t ≠ UPTag.pStart) : UPTag.pStart < t := by
  revert h; revert t; decide

omit [Language.sat.Structure A] in
/-- There is only one left marker. -/
theorem eq_posHStart_of_posn {p : HV A} (hp : HPosn p) (h : p.1 = UPTag.pStart) :
    p = posHStart := by
  obtain ⟨t, w⟩ := p
  cases h
  exact Prod.ext rfl (isMinTup3_unique hp isMinTup3_bot)

omit [Language.sat.Structure A] in
/-- There is only one right marker. -/
theorem eq_posHEnd_of_posn {p : HV A} (hp : HPosn p) (h : p.1 = UPTag.pEnd) :
    p = posHEnd := by
  obtain ⟨t, w⟩ := p
  cases h
  exact Prod.ext rfl (isMinTup3_unique hp isMinTup3_bot)

omit [Language.sat.Structure A] in
/-- A cell is the cell of the element it carries. -/
theorem eq_posHCell_of_posn {p : HV A} (hp : HPosn p) (h : p.1 = UPTag.pCell) :
    p = posHCell (p.2 0) := by
  obtain ⟨t, w⟩ := p
  cases h
  refine Prod.ext rfl (funext fun i => ?_)
  fin_cases i
  · simp [oneH]
  · exact le_antisymm (hp.1 botA) (botA_le _)
  · exact le_antisymm (hp.2 botA) (botA_le _)

omit [Language.sat.Structure A] in
/-- **The left marker is the lowest position.** -/
theorem minPos_posHStart : MinPos tagTupleLe HPosn (posHStart : HV A) := by
  refine ⟨hPosn_posHStart, fun q hq => ?_⟩
  rcases eq_or_ne q.1 UPTag.pStart with h | h
  · rw [eq_posHStart_of_posn hq h]
    exact hTagTupleLe_refl _
  · exact hTagTupleLe_of_tag_lt (hpStart_lt h)

omit [Language.sat.Structure A] in
theorem posHStart_le_posHCell (x : A) : tagTupleLe (posHStart : HV A) (posHCell x) :=
  hTagTupleLe_of_tag_lt (show UPTag.pStart < UPTag.pCell by decide)

omit [Language.sat.Structure A] in
theorem posHCell_le_posHEnd (x : A) : tagTupleLe (posHCell x : HV A) posHEnd :=
  hTagTupleLe_of_tag_lt (show UPTag.pCell < UPTag.pEnd by decide)

omit [Language.sat.Structure A] in
/-- **Cells are ordered as their elements are.** -/
theorem posHCell_le_iff {x y : A} : tagTupleLe (posHCell x : HV A) (posHCell y) ↔ x ≤ y := by
  constructor
  · rintro (h | ⟨-, h | ⟨j, hlt, hj⟩⟩)
    · exact absurd h (lt_irrefl _)
    · exact le_of_eq (by simpa [oneH] using congrFun h 0)
    · fin_cases j
      · exact le_of_lt (by simpa [oneH] using hj)
      · exact le_of_eq (by simpa [oneH] using hlt 0 (by decide))
      · exact le_of_eq (by simpa [oneH] using hlt 0 (by decide))
  · intro h
    refine Or.inr ⟨rfl, ?_⟩
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨0, fun i hi => absurd hi (by omega), by simpa [oneH] using hlt⟩

/-- Only the two lowest tags are at or below a cell's. -/
theorem htag_le_pCell {t : UPTag} (h : t ≤ UPTag.pCell) :
    t = UPTag.pStart ∨ t = UPTag.pCell := by
  revert h; revert t; decide

/-- Only the three bracketing tags are at or below the right marker's. -/
theorem htag_le_pEnd {t : UPTag} (h : t ≤ UPTag.pEnd) :
    t = UPTag.pStart ∨ t = UPTag.pCell ∨ t = UPTag.pEnd := by
  revert h; revert t; decide

/-- Only the two highest bracketing tags lie between a cell's and the right
marker's. -/
theorem htag_between {t : UPTag} (h₁ : UPTag.pCell ≤ t) (h₂ : t ≤ UPTag.pEnd) :
    t = UPTag.pCell ∨ t = UPTag.pEnd := by
  revert h₁ h₂; revert t; decide

omit [Language.sat.Structure A] in
/-- The head's first move: the cell of the least element follows `⊢`. -/
theorem succPos_posHStart_posHCell :
    SuccPos tagTupleLe HPosn (posHStart : HV A) (posHCell botA) := by
  refine ⟨hPosn_posHStart, hPosn_posHCell _, posHStart_le_posHCell _, ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (show ¬(UPTag.pStart = UPTag.pCell) by decide)
  · intro r hr h1 h2
    rcases htag_le_pCell (hTagTupleLe_tag_le h2) with h | h
    · exact Or.inl (eq_posHStart_of_posn hr h)
    · refine Or.inr ?_
      have hcell := eq_posHCell_of_posn hr h
      have hle : r.2 0 ≤ botA := posHCell_le_iff.mp (hcell ▸ h2)
      rw [hcell, le_antisymm hle (botA_le _)]

omit [Language.sat.Structure A] in
/-- The head's last move of a sweep: `⊣` follows the last cell. -/
theorem succPos_posHCell_posHEnd :
    SuccPos tagTupleLe HPosn (posHCell (topA (A := A)) : HV A) posHEnd := by
  refine ⟨hPosn_posHCell _, hPosn_posHEnd, posHCell_le_posHEnd _, ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (show ¬(UPTag.pCell = UPTag.pEnd) by decide)
  · intro r hr h1 h2
    rcases htag_between (hTagTupleLe_tag_le h1) (hTagTupleLe_tag_le h2) with h | h
    · refine Or.inl ?_
      have hcell := eq_posHCell_of_posn hr h
      have hx : topA ≤ r.2 0 := posHCell_le_iff.mp (hcell ▸ h1)
      rw [hcell, le_antisymm (le_topA _) hx]
    · exact Or.inr (eq_posHEnd_of_posn hr h)

end Order

/-! ### The intended run: marks and tapes

The machine's working state is a set of marked elements, as a `Bool`-valued
assignment. Processing one clause – a check sweep and a return sweep – applies
`DescriptiveComplexity.procB` to it: unconditionally, because when the check fails the
inner conjunction is false and nothing is added, exactly as the machine's
return sweep writes nothing when its marking bit is off. -/

section Run

open Classical in
/-- One clause processed on a marked set: if every negative literal of `c` is
marked, its positive literals join the marks. -/
noncomputable def procB (M : A → Bool) (c : A) : A → Bool := fun x =>
  M x || (decide (SatPos c x) && decide (∀ y : A, SatNeg c y → M y = true))

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- Processing a clause only adds marks. -/
theorem le_procB (M : A → Bool) (c : A) {x : A} (h : M x = true) : procB M c x = true := by
  simp [procB, h]

open Classical in
/-- **The tape carrying the marked set `M`**: markers and blanks in place, the
cell of `y` holding `(y, M y)`. A junk cell tuple reads its initial, unmarked
symbol forever – it is never written, so its value must not depend on `M`. -/
noncomputable def hTape (M : A → Bool) : HV A → HV A := fun r =>
  match r.1 with
  | .pStart => symHStart
  | .pEnd => symHEnd
  | .pCell =>
      if (∀ a : A, r.2 1 ≤ a) ∧ (∀ a : A, r.2 2 ≤ a) then symCell (M (r.2 0)) (r.2 0)
      else symCell false (r.2 0)
  | _ => symHBlank

omit [Language.sat.Structure A] in
/-- A real cell reads its element's mark. -/
theorem hTape_posHCell (M : A → Bool) (y : A) :
    hTape M (posHCell y : HV A) = symCell (M y) y := by
  classical
  simp only [hTape]
  exact if_pos ⟨fun a => botA_le a, fun a => botA_le a⟩

omit [Language.sat.Structure A] in
/-- Marked tapes agree wherever the marks do – in particular junk cells never
notice a change of marks. -/
theorem hTape_congr {M M' : A → Bool} (p : HV A)
    (h : ∀ y : A, M y = M' y) : hTape M p = hTape M' p := by
  classical
  obtain ⟨t, w⟩ := p
  cases t <;> simp only [hTape]
  case pCell =>
    by_cases hcond : (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a)
    · rw [if_pos hcond, if_pos hcond, h (w 0)]
    · rw [if_neg hcond, if_neg hcond]

open Classical in
/-- The tape during a return sweep of the clause `c` with the head at `p`,
moving left: the cells strictly above the head have been processed, the rest
still carry the old marks. -/
noncomputable def markTape (M : A → Bool) (c : A) (p : HV A) : HV A → HV A := fun r =>
  match r.1 with
  | .pStart => symHStart
  | .pEnd => symHEnd
  | .pCell =>
      if (∀ a : A, r.2 1 ≤ a) ∧ (∀ a : A, r.2 2 ≤ a) then
        (if tagTupleLe p r ∧ p ≠ r then symCell (procB M c (r.2 0)) (r.2 0)
          else symCell (M (r.2 0)) (r.2 0))
      else symCell false (r.2 0)
  | _ => symHBlank

/-! ### The intended run: configurations -/

open Classical in
/-- The flag of a check sweep with the head at `p`: every negative literal of
`c` strictly below the head is marked. -/
noncomputable def chkFlag (M : A → Bool) (c : A) (p : HV A) : Bool :=
  decide (∀ y : A, tagTupleLe (posHCell y) p → posHCell y ≠ p → SatNeg c y → M y = true)

/-- The configuration during the check sweep of clause `c` in round `r`. -/
noncomputable def confHChk (M : A → Bool) (r c : A) (p : HV A) : Config (HV A) where
  state := stHChk (chkFlag M c p) r c
  head := p
  tape := hTape M

/-- The configuration during the return sweep of clause `c` in round `r`,
with marking bit `m`. -/
noncomputable def confHMark (M : A → Bool) (m : Bool) (r c : A) (p : HV A) :
    Config (HV A) where
  state := stHMark m r c
  head := p
  tape := markTape M c p

open Classical in
/-- The flag of a verification sweep, leftwards, with the head at `p`: some
cell strictly above the head satisfies `c` under the marks – the SAT machine's
`DescriptiveComplexity.chkFlagL` with the marks as valuation. -/
noncomputable def verFlagL (M : A → Bool) (c : A) (p : HV A) : Bool :=
  decide (∃ y : A, tagTupleLe p (posHCell y) ∧ p ≠ posHCell y ∧ MLit c y (M y))

open Classical in
/-- The flag of a verification sweep, rightwards. -/
noncomputable def verFlagR (M : A → Bool) (c : A) (p : HV A) : Bool :=
  decide (∃ y : A, tagTupleLe (posHCell y) p ∧ posHCell y ≠ p ∧ MLit c y (M y))

/-- The configuration during a leftward verification sweep. -/
noncomputable def confHVerL (M : A → Bool) (c : A) (p : HV A) : Config (HV A) where
  state := stHVer (verFlagL M c p) false c
  head := p
  tape := hTape M

/-- The configuration during a rightward verification sweep. -/
noncomputable def confHVerR (M : A → Bool) (c : A) (p : HV A) : Config (HV A) where
  state := stHVer (verFlagR M c p) true c
  head := p
  tape := hTape M

/-- The initial configuration: the dispatch state at the left marker, all
cells unmarked. -/
noncomputable def confHInit : Config (HV A) where
  state := stHInit
  head := posHStart
  tape := hTape (fun _ => false)

/-- **The machine starts at the dispatch configuration**: the unmarked tape is
the initial tape. -/
theorem isInit_confHInit : (hornMachine A).IsInit (confHInit (A := A)) := by
  refine ⟨⟨rfl, isMinTup3_bot⟩, minPos_posHStart, fun q => ?_⟩
  change (hornMachine A).InitTape q (hTape (fun _ => false) q)
  cases hq : q.1 <;> simp only [hTape, hq]
  case pStart => exact Or.inl (Or.inl ⟨hq, rfl, isMinTup3_bot⟩)
  case pEnd => exact Or.inl (Or.inr (Or.inr ⟨hq, rfl, isMinTup3_bot⟩))
  case pCell =>
    rw [ite_self]
    exact Or.inl (Or.inr (Or.inl ⟨hq, rfl, rfl, fun b => botA_le b, fun b => botA_le b⟩))
  all_goals
    refine Or.inr ⟨fun b hb => ?_, rfl, isMinTup3_bot⟩
    rcases hb with ⟨h, -⟩ | ⟨h, -, -, -⟩ | ⟨h, -⟩ <;> rw [hq] at h <;> simp at h

/-! ### The flags and tapes along a sweep -/

/-- A check sweep starts with a vacuously true flag: no cell lies strictly
below the first one. -/
theorem chkFlag_botA (M : A → Bool) (c : A) :
    chkFlag M c (posHCell (botA (A := A))) = true := by
  classical
  simp only [chkFlag, decide_eq_true_eq]
  intro y hle hne
  exact absurd (congrArg posHCell (le_antisymm (posHCell_le_iff.mp hle) (botA_le y))) hne

/-- **Stepping right folds one cell into the check flag.** -/
theorem chkFlag_succ (M : A → Bool) (c : A) {p q : HV A}
    (hsucc : SuccPos tagTupleLe HPosn p q) (hp : p.1 = UPTag.pCell) :
    chkFlag M c q = true ↔
      (chkFlag M c p = true ∧ (SatNeg c (p.2 0) → M (p.2 0) = true)) := by
  classical
  have hpc : p = posHCell (p.2 0) := eq_posHCell_of_posn hsucc.1 hp
  simp only [chkFlag, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun y hle hne hy => h y (isLinOrd_hTagTupleLe.2.1 _ p q hle hsucc.2.2.1)
      (fun he => hne (isLinOrd_hTagTupleLe.2.2.1 _ _ hle (he ▸ hsucc.2.2.1))) hy, fun hy => ?_⟩
    exact h (p.2 0) (hpc ▸ hsucc.2.2.1) (hpc ▸ hsucc.2.2.2.1) hy
  · rintro ⟨hall, hown⟩ y hle hne hy
    by_cases hcase : tagTupleLe (posHCell y) p ∧ posHCell y ≠ p
    · exact hall y hcase.1 hcase.2 hy
    · have hyp : posHCell y = p := by
        by_cases hle' : tagTupleLe (posHCell y) p
        · exact not_not.mp (by simpa [hle'] using hcase)
        · rcases hsucc.2.2.2.2 (posHCell y) (hPosn_posHCell y)
            ((isLinOrd_hTagTupleLe.2.2.2 p (posHCell y)).resolve_right hle') hle with h | h
          · exact h
          · exact absurd h hne
      have hy0 : y = p.2 0 := by
        have := congrArg (fun z : HV A => z.2 0) (hyp.trans hpc)
        simpa [oneH] using this
      rw [hy0]
      exact hown (hy0 ▸ hy)

/-- **A completed check sweep has seen every cell**: at the right marker the
flag says every negative literal of the clause is marked. -/
theorem chkFlag_posHEnd (M : A → Bool) (c : A) :
    chkFlag M c (posHEnd : HV A) = true ↔ ∀ y : A, SatNeg c y → M y = true := by
  classical
  simp only [chkFlag, decide_eq_true_eq]
  constructor
  · intro h y hy
    refine h y (posHCell_le_posHEnd y) ?_ hy
    intro hcon
    exact absurd (congrArg Prod.fst hcon) (show ¬(UPTag.pCell = UPTag.pEnd) by decide)
  · exact fun h y _ _ hy => h y hy

/-- A leftward verification sweep starts with an empty flag. -/
theorem verFlagL_topA (M : A → Bool) (c : A) :
    verFlagL M c (posHCell (topA (A := A))) = false := by
  classical
  simp only [verFlagL, decide_eq_false_iff_not]
  rintro ⟨y, hle, hne, -⟩
  exact hne (congrArg _ (le_antisymm (le_topA y) (posHCell_le_iff.mp hle))).symm

/-- A rightward verification sweep starts with an empty flag. -/
theorem verFlagR_botA (M : A → Bool) (c : A) :
    verFlagR M c (posHCell (botA (A := A))) = false := by
  classical
  simp only [verFlagR, decide_eq_false_iff_not]
  rintro ⟨y, hle, hne, -⟩
  exact hne (congrArg _ (le_antisymm (posHCell_le_iff.mp hle) (botA_le y)))

/-- **Stepping down folds one cell into the leftward verification flag.** -/
theorem verFlagL_succ (M : A → Bool) (c : A) {p q : HV A}
    (hsucc : SuccPos tagTupleLe HPosn p q) (hq : q.1 = UPTag.pCell) :
    verFlagL M c p = true ↔
      (verFlagL M c q = true ∨ MLit c (q.2 0) (M (q.2 0))) := by
  classical
  have hqc : q = posHCell (q.2 0) := eq_posHCell_of_posn hsucc.2.1 hq
  simp only [verFlagL, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hle, hne, hlit⟩
    by_cases hcase : tagTupleLe q (posHCell y) ∧ q ≠ posHCell y
    · exact Or.inl ⟨y, hcase.1, hcase.2, hlit⟩
    · refine Or.inr ?_
      have hyq : posHCell y = q := by
        by_cases hle' : tagTupleLe q (posHCell y)
        · exact (not_not.mp (by simpa [hle'] using hcase : ¬ q ≠ posHCell y)).symm
        · rcases hsucc.2.2.2.2 (posHCell y) (hPosn_posHCell y) hle
            ((isLinOrd_hTagTupleLe.2.2.2 (posHCell y) q).resolve_right hle') with h | h
          · exact absurd h.symm hne
          · exact h
      have : y = q.2 0 := by
        have := congrArg (fun z : HV A => z.2 0) (hyq.trans hqc)
        simpa [oneH] using this
      rwa [← this]
  · rintro (⟨y, hle, hne, hlit⟩ | hlit)
    · refine ⟨y, isLinOrd_hTagTupleLe.2.1 p q _ hsucc.2.2.1 hle, ?_, hlit⟩
      rintro rfl
      exact hsucc.2.2.2.1 (isLinOrd_hTagTupleLe.2.2.1 _ _ hsucc.2.2.1 hle)
    · exact ⟨q.2 0, hqc ▸ hsucc.2.2.1, hqc ▸ hsucc.2.2.2.1, hlit⟩

/-- **Stepping up folds one cell into the rightward verification flag.** -/
theorem verFlagR_succ (M : A → Bool) (c : A) {p q : HV A}
    (hsucc : SuccPos tagTupleLe HPosn p q) (hp : p.1 = UPTag.pCell) :
    verFlagR M c q = true ↔
      (verFlagR M c p = true ∨ MLit c (p.2 0) (M (p.2 0))) := by
  classical
  have hpc : p = posHCell (p.2 0) := eq_posHCell_of_posn hsucc.1 hp
  simp only [verFlagR, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hle, hne, hlit⟩
    by_cases hcase : tagTupleLe (posHCell y) p ∧ posHCell y ≠ p
    · exact Or.inl ⟨y, hcase.1, hcase.2, hlit⟩
    · refine Or.inr ?_
      have hyp : posHCell y = p := by
        by_cases hle' : tagTupleLe (posHCell y) p
        · exact not_not.mp (by simpa [hle'] using hcase : ¬ posHCell y ≠ p)
        · rcases hsucc.2.2.2.2 (posHCell y) (hPosn_posHCell y)
            ((isLinOrd_hTagTupleLe.2.2.2 p (posHCell y)).resolve_right hle') hle with h | h
          · exact h
          · exact absurd h hne
      have hy : y = p.2 0 := by
        have := congrArg (fun z : HV A => z.2 0) (hyp.trans hpc)
        simpa [oneH] using this
      rwa [← hy]
  · rintro (⟨y, hle, hne, hlit⟩ | hlit)
    · refine ⟨y, isLinOrd_hTagTupleLe.2.1 _ p q hle hsucc.2.2.1, ?_, hlit⟩
      rintro rfl
      exact hne (isLinOrd_hTagTupleLe.2.2.1 _ _ hle hsucc.2.2.1)
    · exact ⟨p.2 0, hpc ▸ hsucc.2.2.1, hpc ▸ hsucc.2.2.2.1, hlit⟩

/-- **A completed leftward verification sweep has seen every cell.** -/
theorem verFlagL_posHStart (M : A → Bool) (c : A) :
    verFlagL M c (posHStart : HV A) = true ↔ ∃ y : A, MLit c y (M y) := by
  classical
  simp only [verFlagL, decide_eq_true_eq]
  constructor
  · rintro ⟨y, -, -, hlit⟩
    exact ⟨y, hlit⟩
  · rintro ⟨y, hlit⟩
    refine ⟨y, posHStart_le_posHCell y, ?_, hlit⟩
    intro h
    exact absurd (congrArg Prod.fst h) (show ¬(UPTag.pStart = UPTag.pCell) by decide)

/-- **A completed rightward verification sweep has seen every cell.** -/
theorem verFlagR_posHEnd (M : A → Bool) (c : A) :
    verFlagR M c (posHEnd : HV A) = true ↔ ∃ y : A, MLit c y (M y) := by
  classical
  simp only [verFlagR, decide_eq_true_eq]
  constructor
  · rintro ⟨y, -, -, hlit⟩
    exact ⟨y, hlit⟩
  · rintro ⟨y, hlit⟩
    refine ⟨y, posHCell_le_posHEnd y, ?_, hlit⟩
    intro h
    exact absurd (congrArg Prod.fst h) (show ¬(UPTag.pCell = UPTag.pEnd) by decide)

/-- At the top of the return sweep nothing has been processed: the tape still
carries the old marks. -/
theorem markTape_topA (M : A → Bool) (c : A) (r : HV A) :
    markTape M c (posHCell (topA (A := A))) r = hTape M r := by
  classical
  obtain ⟨t, w⟩ := r
  cases t <;> simp only [markTape, hTape]
  case pCell =>
    by_cases hcond : (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a)
    · rw [if_pos hcond, if_pos hcond, if_neg]
      rintro ⟨hle, hne⟩
      have hcw : ((UPTag.pCell, w) : HV A) = posHCell (w 0) := by
        refine hV_ext rfl ?_ ?_ ?_
        · simp [oneH]
        · exact le_antisymm (hcond.1 botA) (botA_le _)
        · exact le_antisymm (hcond.2 botA) (botA_le _)
      have := posHCell_le_iff.mp (hcw ▸ hle)
      exact hne (hcw ▸ congrArg posHCell (le_antisymm (le_topA (w 0)) this)).symm
    · rw [if_neg hcond, if_neg hcond]

/-- At the bottom of the return sweep everything has been processed: the tape
carries the new marks. -/
theorem markTape_posHStart_eq (M : A → Bool) (c : A) (r : HV A) :
    markTape M c (posHStart : HV A) r = hTape (procB M c) r := by
  classical
  obtain ⟨t, w⟩ := r
  cases t <;> simp only [markTape, hTape]
  case pCell =>
    by_cases hcond : (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a)
    · rw [if_pos hcond, if_pos hcond, if_pos]
      refine ⟨hTagTupleLe_of_tag_lt (show UPTag.pStart < UPTag.pCell by decide), ?_⟩
      intro h
      exact absurd (congrArg Prod.fst h) (show ¬(UPTag.pStart = UPTag.pCell) by decide)
    · rw [if_neg hcond, if_neg hcond]

/-- **The return sweep only ever changes the cell under the head**, exactly as
the SAT machine's guess sweep: moving the head down brings its own cell into the
processed region and nothing else. -/
theorem markTape_frame' (M : A → Bool) (c : A) {p q r : HV A}
    (hsucc : SuccPos tagTupleLe HPosn q p) (hrne : r ≠ p) :
    markTape M c q r = markTape M c p r := by
  classical
  obtain ⟨t, w⟩ := r
  cases t <;> simp only [markTape]
  case pCell =>
    by_cases hcond : (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a)
    · rw [if_pos hcond, if_pos hcond]
      have hiff : (tagTupleLe q ((UPTag.pCell, w) : HV A) ∧ q ≠ ((UPTag.pCell, w) : HV A)) ↔
          (tagTupleLe p ((UPTag.pCell, w) : HV A) ∧ p ≠ ((UPTag.pCell, w) : HV A)) := by
        have hcw : HPosn ((UPTag.pCell, w) : HV A) := hcond
        constructor
        · rintro ⟨hle, hne⟩
          refine ⟨?_, fun he => hrne (by rw [he])⟩
          by_contra hcon
          rcases hsucc.2.2.2.2 (UPTag.pCell, w) hcw hle
            ((isLinOrd_hTagTupleLe.2.2.2 (UPTag.pCell, w) p).resolve_right hcon) with h | h
          · exact hne (by rw [h])
          · exact hrne (by rw [h])
        · rintro ⟨hle, -⟩
          refine ⟨isLinOrd_hTagTupleLe.2.1 q p _ hsucc.2.2.1 hle, fun he => ?_⟩
          rw [← he] at hle
          exact hsucc.2.2.2.1 (isLinOrd_hTagTupleLe.2.2.1 _ _ hsucc.2.2.1 hle)
      exact if_congr hiff rfl rfl
    · rw [if_neg hcond, if_neg hcond]

/-- What the return sweep reads at its own head: the old mark. -/
theorem markTape_at_head (M : A → Bool) (c : A) {p : HV A} (hp : HPosn p)
    (hcell : p.1 = UPTag.pCell) :
    markTape M c p p = symCell (M (p.2 0)) (p.2 0) := by
  classical
  obtain ⟨t, w⟩ := p
  cases hcell
  have hp' : (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a) := hp
  simp only [markTape]
  rw [if_pos hp', if_neg (fun h => h.2 rfl)]

/-! ### The intended run: single steps -/

/-- **The dispatch**, when a clause exists: into the first check sweep of the
lowest round and clause, with everything unmarked. -/
theorem step_hInitChk {c₀ : A} (hc₀ : SatMinCl c₀) :
    (hornMachine A).Step confHInit (confHChk (fun _ => false) botA c₀ (posHCell botA)) := by
  refine ⟨twoH .tInitChk botA c₀, ⟨fun b => botA_le b, hc₀, fun b => botA_le b⟩, rfl, rfl,
    ?_, rfl, fun r _ => rfl, Or.inl ⟨trivial, succPos_posHStart_posHCell⟩⟩
  change stHChk (chkFlag (fun _ => false) c₀ (posHCell botA)) botA c₀ = stHChk true botA c₀
  rw [chkFlag_botA]

/-- **The dispatch**, when there is no clause at all: accept. -/
theorem step_hInitAcc (hno : ∀ e : A, ¬ SatCl e) :
    (hornMachine A).Step confHInit
      ⟨stHAcc, posHCell botA, hTape (fun _ => false)⟩ := by
  exact ⟨cstH .tInitAcc, ⟨isMinTup3_bot, hno⟩, rfl, rfl, rfl, rfl, fun r _ => rfl,
    Or.inl ⟨trivial, succPos_posHStart_posHCell⟩⟩

/-- **One step of a check sweep**: fold the cell under the head into the flag
and move right. -/
theorem step_hChk (M : A → Bool) {r c : A} (hc : SatCl c) {p q : HV A}
    (hsucc : SuccPos tagTupleLe HPosn p q) (hp : p.1 = UPTag.pCell) :
    (hornMachine A).Step (confHChk M r c p) (confHChk M r c q) := by
  classical
  have hpc : p = posHCell (p.2 0) := eq_posHCell_of_posn hsucc.1 hp
  have hread : hTape M p = symCell (M (p.2 0)) (p.2 0) := by
    rw [hpc]
    exact hTape_posHCell M _
  refine ⟨(UPTag.tChk (M (p.2 0)) (chkFlag M c p), ![r, c, p.2 0]), hc, rfl, hread, ?_,
    hread, fun r' _ => rfl, Or.inl ⟨trivial, hsucc⟩⟩
  by_cases hflag : chkFlag M c q = true
  · refine Or.inl ⟨?_, ((chkFlag_succ M c hsucc hp).mp hflag).1, ?_⟩
    · change stHChk (chkFlag M c q) r c = stHChk true r c
      rw [hflag]
    · exact fun hn => ((chkFlag_succ M c hsucc hp).mp hflag).2 hn
  · refine Or.inr ⟨?_, ?_⟩
    · change stHChk (chkFlag M c q) r c = stHChk false r c
      rw [Bool.not_eq_true] at hflag
      rw [hflag]
    · by_cases hf : chkFlag M c p = true
      · refine Or.inr ?_
        by_cases hn : SatNeg c (p.2 0)
        · refine ⟨hn, ?_⟩
          by_contra hM
          rw [Bool.not_eq_false] at hM
          exact hflag ((chkFlag_succ M c hsucc hp).mpr ⟨hf, fun _ => hM⟩)
        · exact absurd ((chkFlag_succ M c hsucc hp).mpr ⟨hf, fun h => absurd h hn⟩) hflag
      · rw [Bool.not_eq_true] at hf
        exact Or.inl hf

/-- **The turn at the right marker**: the check sweep is over, the return
sweep begins with the accumulated verdict as its marking bit. -/
theorem step_hChkEnd (M : A → Bool) {r c : A} (hc : SatCl c) :
    (hornMachine A).Step (confHChk M r c posHEnd)
      (confHMark M (chkFlag M c posHEnd) r c (posHCell topA)) := by
  refine ⟨(UPTag.tChkEnd (chkFlag M c posHEnd), ![r, c, botA]), ⟨hc, fun b => botA_le b⟩,
    rfl, rfl, rfl, rfl, fun r' _ => markTape_topA M c r', ?_⟩
  exact Or.inr ⟨fun h => h, succPos_posHCell_posHEnd⟩

/-- **One step of a return sweep**: process the cell under the head – marking
it if it is the positive literal of a successfully checked clause – and move
left. -/
theorem step_hMark (M : A → Bool) {m : Bool} {r c : A} (hc : SatCl c)
    (hm : m = true ↔ ∀ y : A, SatNeg c y → M y = true) {p q : HV A}
    (hsucc : SuccPos tagTupleLe HPosn q p) (hp : p.1 = UPTag.pCell) :
    (hornMachine A).Step (confHMark M m r c p) (confHMark M m r c q) := by
  classical
  have hread : markTape M c p p = symCell (M (p.2 0)) (p.2 0) :=
    markTape_at_head M c hsucc.2.1 hp
  have hwrite : markTape M c q p = symCell (procB M c (p.2 0)) (p.2 0) := by
    have hpc : p = posHCell (p.2 0) := eq_posHCell_of_posn hsucc.2.1 hp
    obtain ⟨t, w⟩ := p
    cases hp
    have hp' : (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a) :=
      (show HPosn ((UPTag.pCell, w) : HV A) from hsucc.2.1)
    simp only [markTape]
    rw [if_pos hp', if_pos ⟨hsucc.2.2.1, hsucc.2.2.2.1⟩]
  refine ⟨(UPTag.tMark (M (p.2 0)) m, ![r, c, p.2 0]), hc, rfl, hread, rfl, ?_,
    fun r' hr' => markTape_frame' M c hsucc hr', Or.inr ⟨fun h => h, hsucc⟩⟩
  change (hornMachine A).Write (UPTag.tMark (M (p.2 0)) m, ![r, c, p.2 0]) (markTape M c q p)
  rw [hwrite]
  by_cases hmk : m = true
  · by_cases hpos : SatPos c (p.2 0)
    · refine Or.inl ⟨?_, hmk, hpos⟩
      have hp1 : procB M c (p.2 0) = true := by
        simp only [procB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact Or.inr ⟨hpos, hm.mp hmk⟩
      rw [hp1]
      exact rfl
    · refine Or.inr ⟨?_, Or.inr hpos⟩
      have hp1 : procB M c (p.2 0) = M (p.2 0) := by
        simp [procB, hpos]
      rw [hp1]
      exact rfl
  · refine Or.inr ⟨?_, Or.inl (by rwa [Bool.not_eq_true] at hmk)⟩
    have hp1 : procB M c (p.2 0) = M (p.2 0) := by
      rw [Bool.not_eq_true] at hmk
      have hnall : ¬ ∀ y : A, SatNeg c y → M y = true := fun h => by
        rw [hm.mpr h] at hmk
        exact Bool.noConfusion hmk
      simp [procB, hnall]
    rw [hp1]
    exact rfl

/-- **The turn at the left marker, next clause**: the processed marks become
the working marks, and the next check sweep starts. -/
theorem step_hMarkEndNext (M : A → Bool) {m : Bool} {r c c' : A}
    (hnext : SatNextCl c c') :
    (hornMachine A).Step (confHMark M m r c posHStart)
      (confHChk (procB M c) r c' (posHCell botA)) := by
  refine ⟨(UPTag.tMarkEndNext m, ![r, c, c']), hnext, rfl, rfl, ?_, rfl,
    fun r' _ => (markTape_posHStart_eq M c r').symm, Or.inl ⟨trivial, succPos_posHStart_posHCell⟩⟩
  change stHChk (chkFlag (procB M c) c' (posHCell botA)) r c' = stHChk true r c'
  rw [chkFlag_botA]

/-- **The turn at the left marker, next round**: last clause processed, the
round counter advances and the checks restart at the lowest clause. -/
theorem step_hMarkEndRound (M : A → Bool) {m : Bool} {r r' c c₀ : A}
    (hsucc : SuccElt r r') (hmax : SatMaxCl c) (hmin : SatMinCl c₀) :
    (hornMachine A).Step (confHMark M m r c posHStart)
      (confHChk (procB M c) r' c₀ (posHCell botA)) := by
  refine ⟨(UPTag.tMarkEndRound m, ![r, r', c]), ⟨hsucc, hmax⟩, rfl, rfl, ?_, rfl,
    fun r'' _ => (markTape_posHStart_eq M c r'').symm,
    Or.inl ⟨trivial, succPos_posHStart_posHCell⟩⟩
  refine ⟨?_, rfl, hmin, fun a => botA_le a⟩
  change (stHChk (chkFlag (procB M c) c₀ (posHCell botA)) r' c₀).1 = UPTag.qChk true
  rw [chkFlag_botA]
  exact rfl

/-- **The turn at the left marker, into verification**: the last clause of the
last round is processed, and the final marks are verified clause by clause,
starting rightwards at the lowest clause. -/
theorem step_hMarkEndVer (M : A → Bool) {m : Bool} {r c c₀ : A}
    (hmaxr : MaxElt r) (hmax : SatMaxCl c) (hmin : SatMinCl c₀) :
    (hornMachine A).Step (confHMark M m r c posHStart)
      (confHVerR (procB M c) c₀ (posHCell botA)) := by
  refine ⟨(UPTag.tMarkEndVer m, ![r, c, botA]), ⟨hmaxr, hmax, fun a => botA_le a⟩, rfl, rfl,
    ?_, rfl, fun r'' _ => (markTape_posHStart_eq M c r'').symm,
    Or.inl ⟨trivial, succPos_posHStart_posHCell⟩⟩
  refine ⟨?_, hmin, fun a => botA_le a, fun a => botA_le a⟩
  change (stHVer (verFlagR (procB M c) c₀ (posHCell botA)) true c₀).1 = UPTag.qVer false true
  rw [verFlagR_botA]
  exact rfl

/-- **One step of a rightward verification sweep.** -/
theorem step_hVerR (M : A → Bool) {c : A} (hc : SatCl c) {p q : HV A}
    (hsucc : SuccPos tagTupleLe HPosn p q) (hp : p.1 = UPTag.pCell) :
    (hornMachine A).Step (confHVerR M c p) (confHVerR M c q) := by
  classical
  have hpc : p = posHCell (p.2 0) := eq_posHCell_of_posn hsucc.1 hp
  have hread : hTape M p = symCell (M (p.2 0)) (p.2 0) := by
    rw [hpc]
    exact hTape_posHCell M _
  refine ⟨(UPTag.tVer (M (p.2 0)) (verFlagR M c p) true, ![c, p.2 0, botA]),
    ⟨hc, fun a => botA_le a⟩, rfl, hread, ?_, hread, fun r' _ => rfl,
    Or.inl ⟨rfl, hsucc⟩⟩
  by_cases hflag : verFlagR M c q = true
  · refine Or.inl ⟨?_, (verFlagR_succ M c hsucc hp).mp hflag⟩
    change stHVer (verFlagR M c q) true c = stHVer true true c
    rw [hflag]
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · change stHVer (verFlagR M c q) true c = stHVer false true c
      rw [Bool.not_eq_true] at hflag
      rw [hflag]
    · by_contra hcon
      exact hflag ((verFlagR_succ M c hsucc hp).mpr (Or.inl (by simpa using hcon)))
    · exact fun hlit => hflag ((verFlagR_succ M c hsucc hp).mpr (Or.inr hlit))

/-- **One step of a leftward verification sweep.** -/
theorem step_hVerL (M : A → Bool) {c : A} (hc : SatCl c) {p q : HV A}
    (hsucc : SuccPos tagTupleLe HPosn p q) (hq : q.1 = UPTag.pCell) :
    (hornMachine A).Step (confHVerL M c q) (confHVerL M c p) := by
  classical
  have hqc : q = posHCell (q.2 0) := eq_posHCell_of_posn hsucc.2.1 hq
  have hread : hTape M q = symCell (M (q.2 0)) (q.2 0) := by
    rw [hqc]
    exact hTape_posHCell M _
  refine ⟨(UPTag.tVer (M (q.2 0)) (verFlagL M c q) false, ![c, q.2 0, botA]),
    ⟨hc, fun a => botA_le a⟩, rfl, hread, ?_, hread, fun r' _ => rfl,
    Or.inr ⟨Bool.false_ne_true, hsucc⟩⟩
  by_cases hflag : verFlagL M c p = true
  · refine Or.inl ⟨?_, (verFlagL_succ M c hsucc hq).mp hflag⟩
    change stHVer (verFlagL M c p) false c = stHVer true false c
    rw [hflag]
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · change stHVer (verFlagL M c p) false c = stHVer false false c
      rw [Bool.not_eq_true] at hflag
      rw [hflag]
    · by_contra hcon
      exact hflag ((verFlagL_succ M c hsucc hq).mpr (Or.inl (by simpa using hcon)))
    · exact fun hlit => hflag ((verFlagL_succ M c hsucc hq).mpr (Or.inr hlit))

/-- **The verification turn at the right marker**, another clause following:
reverse into a leftward sweep of the next clause. -/
theorem step_hVerNextR (M : A → Bool) {c c' : A} (hnext : SatNextCl c c')
    (hflag : verFlagR M c (posHEnd : HV A) = true) :
    (hornMachine A).Step (confHVerR M c posHEnd) (confHVerL M c' (posHCell topA)) := by
  refine ⟨(UPTag.tVerNext true, ![c, c', botA]), ⟨hnext, fun a => botA_le a⟩, ?_, rfl, ?_,
    rfl, fun r' _ => rfl, Or.inr ⟨fun h => Bool.noConfusion h, succPos_posHCell_posHEnd⟩⟩
  · change stHVer (verFlagR M c posHEnd) true c = stHVer true true c
    rw [hflag]
  · change stHVer (verFlagL M c' (posHCell topA)) false c' = stHVer false false c'
    rw [verFlagL_topA]

/-- **The verification turn at the left marker** – the mirror. -/
theorem step_hVerNextL (M : A → Bool) {c c' : A} (hnext : SatNextCl c c')
    (hflag : verFlagL M c (posHStart : HV A) = true) :
    (hornMachine A).Step (confHVerL M c posHStart) (confHVerR M c' (posHCell botA)) := by
  refine ⟨(UPTag.tVerNext false, ![c, c', botA]), ⟨hnext, fun a => botA_le a⟩, ?_, rfl, ?_,
    rfl, fun r' _ => rfl, Or.inl ⟨rfl, succPos_posHStart_posHCell⟩⟩
  · change stHVer (verFlagL M c posHStart) false c = stHVer true false c
    rw [hflag]
  · change stHVer (verFlagR M c' (posHCell botA)) true c' = stHVer false true c'
    rw [verFlagR_botA]

/-- **Accepting at the right marker**: the last clause is verified, and the
instance is Horn – the gate. -/
theorem step_hVerAccR (M : A → Bool) {c : A} (hmax : SatMaxCl c)
    (hhorn : AtMostOnePositive A) (hflag : verFlagR M c (posHEnd : HV A) = true) :
    (hornMachine A).Step (confHVerR M c posHEnd)
      ⟨stHAcc, posHCell topA, hTape M⟩ := by
  refine ⟨(UPTag.tVerAcc true, ![c, botA, botA]),
    ⟨hmax, fun a => botA_le a, fun a => botA_le a, hhorn⟩, ?_, rfl, rfl, rfl,
    fun r' _ => rfl, Or.inr ⟨fun h => Bool.noConfusion h, succPos_posHCell_posHEnd⟩⟩
  change stHVer (verFlagR M c posHEnd) true c = stHVer true true c
  rw [hflag]

/-- **Accepting at the left marker** – the mirror. -/
theorem step_hVerAccL (M : A → Bool) {c : A} (hmax : SatMaxCl c)
    (hhorn : AtMostOnePositive A) (hflag : verFlagL M c (posHStart : HV A) = true) :
    (hornMachine A).Step (confHVerL M c posHStart)
      ⟨stHAcc, posHCell botA, hTape M⟩ := by
  refine ⟨(UPTag.tVerAcc false, ![c, botA, botA]),
    ⟨hmax, fun a => botA_le a, fun a => botA_le a, hhorn⟩, ?_, rfl, rfl, rfl,
    fun r' _ => rfl, Or.inl ⟨rfl, succPos_posHStart_posHCell⟩⟩
  change stHVer (verFlagL M c posHStart) false c = stHVer true false c
  rw [hflag]

/-! ### Ranks, sweeps, and one whole clause -/

omit [Language.sat.Structure A] in
/-- The left marker has rank `0`. -/
theorem bitRank_posHStart : bitRank tagTupleLe HPosn (posHStart : HV A) = 0 :=
  bitRank_eq_zero_of_minPos isLinOrd_hTagTupleLe minPos_posHStart

omit [Language.sat.Structure A] in
/-- The right marker sits one step above the last cell. -/
theorem bitRank_posHEnd_eq :
    bitRank tagTupleLe HPosn (posHEnd : HV A) =
      bitRank tagTupleLe HPosn (posHCell (topA (A := A))) + 1 :=
  bitRank_succPos isLinOrd_hTagTupleLe succPos_posHCell_posHEnd

omit [Language.sat.Structure A] in
/-- The first cell has rank `1`. -/
theorem bitRank_posHCell_botA :
    bitRank tagTupleLe HPosn (posHCell (botA (A := A)) : HV A) = 1 := by
  rw [bitRank_succPos isLinOrd_hTagTupleLe succPos_posHStart_posHCell, bitRank_posHStart]

omit [Language.sat.Structure A] in
/-- **A sweep is short**: only the left marker and the cells lie below the
right marker, by injection into `Option A`. -/
theorem bitRank_posHEnd_le :
    bitRank tagTupleLe HPosn (posHEnd : HV A) ≤ Nat.card A + 1 := by
  classical
  have hcell : ∀ r : HV A, HPosn r → tagTupleLe r posHEnd → r ≠ posHEnd →
      r.1 ≠ UPTag.pStart → r.1 = UPTag.pCell := by
    intro r hr hle hne hns
    rcases htag_le_pEnd (hTagTupleLe_tag_le hle) with h | h | h
    · exact absurd h hns
    · exact h
    · exact absurd (eq_posHEnd_of_posn hr h) hne
  refine le_trans (Set.ncard_le_ncard_of_injOn
    (fun r : HV A => if r.1 = UPTag.pStart then none else some (r.2 0))
    (fun _ _ => Set.mem_univ _) ?_ (Set.toFinite _)) ?_
  · rintro r ⟨hr, hle, hne⟩ r' ⟨hr', hle', hne'⟩ heq
    by_cases hs : r.1 = UPTag.pStart <;> by_cases hs' : r'.1 = UPTag.pStart
    · rw [eq_posHStart_of_posn hr hs, eq_posHStart_of_posn hr' hs']
    · simp [hs, hs'] at heq
    · simp [hs, hs'] at heq
    · have h0 : r.2 0 = r'.2 0 := by simpa [hs, hs'] using heq
      rw [eq_posHCell_of_posn hr (hcell r hr hle hne hs),
        eq_posHCell_of_posn hr' (hcell r' hr' hle' hne' hs'), h0]
  · rw [Set.ncard_univ]
    haveI := Fintype.ofFinite A
    simp [Nat.card_eq_fintype_card]

omit [Language.sat.Structure A] in
/-- Cells only, along a rightward sweep bounded by the markers. -/
private theorem cell_of_between {p q : HV A} (hsucc : SuccPos tagTupleLe HPosn p q)
    (hlb : tagTupleLe (posHCell (botA (A := A))) p) (hub : tagTupleLe q posHEnd) :
    p.1 = UPTag.pCell := by
  rcases htag_between (hTagTupleLe_tag_le hlb)
      (hTagTupleLe_tag_le (isLinOrd_hTagTupleLe.2.1 p q posHEnd hsucc.2.2.1 hub)) with h | h
  · exact h
  · exact absurd (isLinOrd_hTagTupleLe.2.2.1 p q hsucc.2.2.1
      ((eq_posHEnd_of_posn hsucc.1 h) ▸ hub)) hsucc.2.2.2.1

/-- **A whole check sweep**, from the first cell to the right marker. -/
theorem steps_hChkAll (M : A → Bool) {r c : A} (hc : SatCl c) :
    (hornMachine A).StepsIn
      (bitRank tagTupleLe HPosn (posHEnd : HV A) -
        bitRank tagTupleLe HPosn (posHCell (botA (A := A))))
      (confHChk M r c (posHCell botA)) (confHChk M r c posHEnd) := by
  refine TMData.stepsIn_of_segment isLinOrd_hTagTupleLe (hPosn_posHCell _)
    (fun p q hsucc hlb hub => step_hChk M hc hsucc (cell_of_between hsucc hlb hub))
    posHEnd hPosn_posHEnd (posHCell_le_posHEnd _) (hTagTupleLe_refl _)

/-- **A whole return sweep**, from the last cell down to the left marker. -/
theorem steps_hMarkAll (M : A → Bool) {m : Bool} {r c : A} (hc : SatCl c)
    (hm : m = true ↔ ∀ y : A, SatNeg c y → M y = true) :
    (hornMachine A).StepsIn
      (bitRank tagTupleLe HPosn (posHCell (topA (A := A))) -
        bitRank tagTupleLe HPosn (posHStart : HV A))
      (confHMark M m r c (posHCell topA)) (confHMark M m r c posHStart) := by
  refine TMData.stepsIn_of_segment_down isLinOrd_hTagTupleLe (hPosn_posHCell _)
    (fun p q hsucc hlb hub => step_hMark M hc hm hsucc ?_) posHStart hPosn_posHStart
    (hTagTupleLe_refl _) (posHStart_le_posHCell _)
  rcases htag_le_pCell (hTagTupleLe_tag_le hub) with h | h
  · refine absurd (isLinOrd_hTagTupleLe.2.2.1 p q hsucc.2.2.1 ?_) hsucc.2.2.2.1
    rw [eq_posHStart_of_posn hsucc.2.1 h]
    exact minPos_posHStart.2 p hsucc.1
  · exact h

/-- **A whole rightward verification sweep.** -/
theorem steps_hVerRAll (M : A → Bool) {c : A} (hc : SatCl c) :
    (hornMachine A).StepsIn
      (bitRank tagTupleLe HPosn (posHEnd : HV A) -
        bitRank tagTupleLe HPosn (posHCell (botA (A := A))))
      (confHVerR M c (posHCell botA)) (confHVerR M c posHEnd) := by
  refine TMData.stepsIn_of_segment isLinOrd_hTagTupleLe (hPosn_posHCell _)
    (fun p q hsucc hlb hub => step_hVerR M hc hsucc (cell_of_between hsucc hlb hub))
    posHEnd hPosn_posHEnd (posHCell_le_posHEnd _) (hTagTupleLe_refl _)

/-- **A whole leftward verification sweep.** -/
theorem steps_hVerLAll (M : A → Bool) {c : A} (hc : SatCl c) :
    (hornMachine A).StepsIn
      (bitRank tagTupleLe HPosn (posHCell (topA (A := A))) -
        bitRank tagTupleLe HPosn (posHStart : HV A))
      (confHVerL M c (posHCell topA)) (confHVerL M c posHStart) := by
  refine TMData.stepsIn_of_segment_down isLinOrd_hTagTupleLe (hPosn_posHCell _)
    (fun p q hsucc hlb hub => step_hVerL M hc hsucc ?_) posHStart hPosn_posHStart
    (hTagTupleLe_refl _) (posHStart_le_posHCell _)
  rcases htag_le_pCell (hTagTupleLe_tag_le hub) with h | h
  · refine absurd (isLinOrd_hTagTupleLe.2.2.1 p q hsucc.2.2.1 ?_) hsucc.2.2.2.1
    rw [eq_posHStart_of_posn hsucc.2.1 h]
    exact minPos_posHStart.2 p hsucc.1
  · exact h

/-- **One whole clause**: check sweep, turn, return sweep, back at the left
marker with the processed marks, in exactly `2 R` steps for `R` the right
marker's rank. -/
theorem steps_hOneClause (M : A → Bool) {r c : A} (hc : SatCl c) :
    ∃ k ≤ 2 * bitRank tagTupleLe HPosn (posHEnd : HV A),
      (hornMachine A).StepsIn k (confHChk M r c (posHCell botA))
        (confHMark M (chkFlag M c (posHEnd : HV A)) r c posHStart) := by
  classical
  have hm : chkFlag M c (posHEnd : HV A) = true ↔ ∀ y : A, SatNeg c y → M y = true :=
    chkFlag_posHEnd M c
  have h1 := steps_hChkAll M (r := r) hc
  have h2 := (h1.trans_step (step_hChkEnd M hc)).trans (steps_hMarkAll M hc hm)
  refine ⟨_, ?_, h2⟩
  have e1 := bitRank_posHStart (A := A)
  have e2 := bitRank_posHEnd_eq (A := A)
  have e3 := bitRank_posHCell_botA (A := A)
  omega

/-! ### The folds: what the rounds compute -/

/-- Processing the clauses from `c` to the last one, relationally: the marked
set each clause leaves behind. -/
inductive ClauseFold : A → (A → Bool) → (A → Bool) → Prop
  | last {c : A} {M : A → Bool} : SatMaxCl c → ClauseFold c M (procB M c)
  | step {c c' : A} {M M' : A → Bool} : SatNextCl c c' →
      ClauseFold c' (procB M c) M' → ClauseFold c M M'

/-- Processing the rounds from `r` to the last one, each a pass over all the
clauses from `c₀`. -/
inductive RoundFold (c₀ : A) : A → (A → Bool) → (A → Bool) → Prop
  | last {r : A} {M M' : A → Bool} : MaxElt r → ClauseFold c₀ M M' → RoundFold c₀ r M M'
  | step {r r' : A} {M M' M'' : A → Bool} : SuccElt r r' → ClauseFold c₀ M M' →
      RoundFold c₀ r' M' M'' → RoundFold c₀ r M M''

omit [Finite A] [Nonempty A] in
/-- The clause fold only adds marks. -/
theorem ClauseFold.mono {c : A} {M M' : A → Bool} (h : ClauseFold c M M') {x : A}
    (hx : M x = true) : M' x = true := by
  induction h generalizing x with
  | last _ => exact le_procB _ _ hx
  | step _ _ ih => exact ih (le_procB _ _ hx)

omit [Finite A] [Nonempty A] in
/-- The round fold only adds marks. -/
theorem RoundFold.mono {c₀ r : A} {M M' : A → Bool} (h : RoundFold c₀ r M M') {x : A}
    (hx : M x = true) : M' x = true := by
  induction h generalizing x with
  | last _ hcf => exact hcf.mono hx
  | step _ hcf _ ih => exact ih (hcf.mono hx)

omit [Nonempty A] in
/-- **Soundness of the fold**: marks stay inside the propagation closure. -/
theorem ClauseFold.subset_forced {c : A} {M M' : A → Bool} (h : ClauseFold c M M')
    (hM : ∀ x : A, M x = true → Forced x) : ∀ x : A, M' x = true → Forced x := by
  classical
  induction h with
  | @last c M hmax =>
    intro x hx
    simp only [procB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
    rcases hx with hx | ⟨hpos, hall⟩
    · exact hM x hx
    · exact forced_of_allNeg hmax.1 hpos fun y hy => hM y (hall y hy)
  | @step c c' M M' hnext _ ih =>
    refine ih fun x hx => ?_
    simp only [procB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
    rcases hx with hx | ⟨hpos, hall⟩
    · exact hM x hx
    · exact forced_of_allNeg hnext.1 hpos fun y hy => hM y (hall y hy)

omit [Nonempty A] in
/-- Soundness for the rounds. -/
theorem RoundFold.subset_forced {c₀ r : A} {M M' : A → Bool} (h : RoundFold c₀ r M M')
    (hM : ∀ x : A, M x = true → Forced x) : ∀ x : A, M' x = true → Forced x := by
  induction h with
  | last _ hcf => exact hcf.subset_forced hM
  | step _ hcf _ ih => exact ih (hcf.subset_forced hM)

omit [Finite A] [Nonempty A] in
/-- **One round dominates one propagation step**: a clause whose negative
literals are all marked at the start of the round has its positive literals
marked at its end – the marks only grow until the clause's turn comes. -/
theorem ClauseFold.dominates {c₀ : A} {M M' : A → Bool} (h : ClauseFold c₀ M M')
    {c x : A} (hc : SatCl c) (hpos : SatPos c x) :
    c₀ ≤ c → (∀ y : A, SatNeg c y → M y = true) → M' x = true := by
  classical
  induction h with
  | @last cl M hmax =>
    intro hc₀ hall
    obtain rfl : c = cl := le_antisymm (hmax.2 c hc) hc₀
    simp only [procB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨hpos, hall⟩
  | @step cl cl' M M' hnext hrest ih =>
    intro hc₀ hall
    rcases eq_or_lt_of_le hc₀ with heq | hlt
    · refine hrest.mono ?_
      subst heq
      simp only [procB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨hpos, hall⟩
    · exact ih (hnext.2.2.2 c hc hlt) fun y hy => le_procB _ _ (hall y hy)

omit [Nonempty A] in
/-- **The rounds reach every propagation stage**: seed marks containing stage
`j` become, after the remaining rounds, marks containing stage `j + #rounds`.
Each round dominates one step because its marks only grow. -/
theorem RoundFold.forcedIn_subset {c₀ : A} (hmin : SatMinCl c₀) {r : A}
    {M M' : A → Bool} (h : RoundFold c₀ r M M') :
    ∀ j : ℕ, (∀ y : A, ForcedIn j y → M y = true) →
      ∀ x : A, ForcedIn (j + {e : A | r ≤ e}.ncard) x → M' x = true := by
  classical
  induction h with
  | @last r M M' hmax hcf =>
    intro j hj x hx
    have hcard : {e : A | r ≤ e}.ncard = 1 := by
      have hset : {e : A | r ≤ e} = {r} := by
        ext e
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        exact ⟨fun hle => le_antisymm (hmax e) hle, fun he => he ▸ le_refl r⟩
      rw [hset, Set.ncard_singleton]
    rw [hcard] at hx
    obtain ⟨cx, hcx, hpos, hall⟩ := hx
    exact hcf.dominates hcx hpos (hmin.2 cx hcx) fun y hy => hj y (hall y hy)
  | @step r r' M M' M'' hsucc hcf hrest ih =>
    intro j hj x hx
    have hcard : {e : A | r ≤ e}.ncard = {e : A | r' ≤ e}.ncard + 1 := by
      have hset : {e : A | r ≤ e} = insert r {e : A | r' ≤ e} := by
        ext e
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
        constructor
        · intro hle
          rcases eq_or_lt_of_le hle with heq | hlt
          · exact Or.inl heq.symm
          · exact Or.inr (hsucc.2 e hlt)
        · rintro (rfl | hle)
          · exact le_refl e
          · exact le_trans hsucc.1.le hle
      have hnotmem : r ∉ {e : A | r' ≤ e} := fun hmem => absurd hmem (not_le.mpr hsucc.1)
      rw [hset, Set.ncard_insert_of_notMem hnotmem (Set.toFinite _)]
    have hx' : ForcedIn ((j + 1) + {e : A | r' ≤ e}.ncard) x := by
      have : j + {e : A | r ≤ e}.ncard = (j + 1) + {e : A | r' ≤ e}.ncard := by
        omega
      rwa [this] at hx
    refine ih (j + 1) (fun y hy => ?_) x hx'
    obtain ⟨cy, hcy, hpos, hall⟩ := hy
    exact hcf.dominates hcy hpos (hmin.2 cy hcy) fun z hz => hj z (hall z hz)

/-! ### The machine walks the folds -/

omit [Language.sat.Structure A] [Nonempty A] in
/-- Every element that is not the greatest has a successor. -/
theorem exists_succElt {r : A} (hnmax : ¬ MaxElt r) : ∃ r' : A, SuccElt r r' := by
  have hne : ∃ z : A, r < z := by
    by_contra hcon
    push Not at hcon
    exact hnmax fun b => hcon b
  obtain ⟨r', hr', hmin⟩ :=
    exists_minPos (Le := (· ≤ · : A → A → Prop)) (Posn := fun z : A => r < z)
      ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩ hne
  exact ⟨r', hr', fun z hz => hmin z hz⟩

omit [Language.sat.Structure A] [Nonempty A] in
/-- Passing to the next round removes exactly one round from those left. -/
theorem ncard_ge_succElt {r r' : A} (hsucc : SuccElt r r') :
    {e : A | r ≤ e}.ncard = {e : A | r' ≤ e}.ncard + 1 := by
  have hset : {e : A | r ≤ e} = insert r {e : A | r' ≤ e} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · intro hle
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr (hsucc.2 e hlt)
    · rintro (rfl | hle)
      · exact le_refl e
      · exact le_trans hsucc.1.le hle
  have hnotmem : r ∉ {e : A | r' ≤ e} := fun hmem => absurd hmem (not_le.mpr hsucc.1)
  rw [hset, Set.ncard_insert_of_notMem hnotmem (Set.toFinite _)]

/-- **The machine processes the clauses from `c` to the last one**: it
computes the clause fold, and then turns – to the next round if one follows,
into verification otherwise – in at most `2R + 1` steps per clause. -/
theorem steps_hClauses {c₀ : A} (hmin : SatMinCl c₀) (r : A) :
    ∀ (c : A), SatCl c → ∀ M : A → Bool,
      ∃ M', ClauseFold c M M' ∧
        (∀ r', SuccElt r r' →
          ∃ k ≤ {e : A | SatCl e ∧ c ≤ e}.ncard *
              (2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1),
            (hornMachine A).StepsIn k (confHChk M r c (posHCell botA))
              (confHChk M' r' c₀ (posHCell botA))) ∧
        (MaxElt r →
          ∃ k ≤ {e : A | SatCl e ∧ c ≤ e}.ncard *
              (2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1),
            (hornMachine A).StepsIn k (confHChk M r c (posHCell botA))
              (confHVerR M' c₀ (posHCell botA))) := by
  intro c
  induction c using WellFoundedGT.induction with
  | ind c IH =>
    intro hc M
    have hpos : 0 < {e : A | SatCl e ∧ c ≤ e}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨c, hc, le_refl c⟩
    obtain ⟨k₁, hk₁, hsteps₁⟩ := steps_hOneClause M (r := r) hc
    by_cases hmax : SatMaxCl c
    · refine ⟨procB M c, ClauseFold.last hmax, fun r' hr' => ?_, fun hmaxr => ?_⟩
      · refine ⟨k₁ + 1, ?_, hsteps₁.trans_step (step_hMarkEndRound M hr' hmax hmin)⟩
        calc k₁ + 1 ≤ 2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1 := by omega
          _ ≤ _ := Nat.le_mul_of_pos_left _ hpos
      · refine ⟨k₁ + 1, ?_, hsteps₁.trans_step (step_hMarkEndVer M hmaxr hmax hmin)⟩
        calc k₁ + 1 ≤ 2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1 := by omega
          _ ≤ _ := Nat.le_mul_of_pos_left _ hpos
    · obtain ⟨c', hnext⟩ := exists_satNextCl hc hmax
      obtain ⟨M', hfold, hnextr, hmaxr⟩ := IH c' hnext.2.2.1 hnext.2.1 (procB M c)
      have hcount : ∀ {k' : ℕ}, k' ≤ {e : A | SatCl e ∧ c' ≤ e}.ncard *
            (2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1) →
          k₁ + 1 + k' ≤ {e : A | SatCl e ∧ c ≤ e}.ncard *
            (2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1) := by
        intro k' hk'
        rw [ncard_clauses_next hnext, Nat.succ_mul]
        have h1 : k₁ + 1 ≤ 2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1 := by omega
        calc k₁ + 1 + k' ≤ (2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1) +
              {e : A | SatCl e ∧ c' ≤ e}.ncard *
                (2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1) :=
            Nat.add_le_add h1 hk'
          _ = _ := Nat.add_comm _ _
      have hchain := hsteps₁.trans_step (step_hMarkEndNext M hnext)
      refine ⟨M', ClauseFold.step hnext hfold, fun r' hr' => ?_, fun hmaxr' => ?_⟩
      · obtain ⟨k', hk', hs'⟩ := hnextr r' hr'
        exact ⟨k₁ + 1 + k', hcount hk', hchain.trans hs'⟩
      · obtain ⟨k', hk', hs'⟩ := hmaxr hmaxr'
        exact ⟨k₁ + 1 + k', hcount hk', hchain.trans hs'⟩

/-- **The machine runs all the rounds**: from any round to the start of the
verification phase, computing the round fold. -/
theorem steps_hRounds {c₀ : A} (hmin : SatMinCl c₀) :
    ∀ (r : A) (M : A → Bool),
      ∃ M', RoundFold c₀ r M M' ∧
        ∃ k ≤ {e : A | r ≤ e}.ncard * ({e : A | SatCl e ∧ c₀ ≤ e}.ncard *
            (2 * bitRank tagTupleLe HPosn (posHEnd : HV A) + 1)),
          (hornMachine A).StepsIn k (confHChk M r c₀ (posHCell botA))
            (confHVerR M' c₀ (posHCell botA)) := by
  intro r
  induction r using WellFoundedGT.induction with
  | ind r IH =>
    intro M
    have hposr : 0 < {e : A | r ≤ e}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨r, le_refl r⟩
    by_cases hmaxr : MaxElt r
    · obtain ⟨M', hfold, -, hmax⟩ := steps_hClauses hmin r c₀ hmin.1 M
      obtain ⟨k, hk, hs⟩ := hmax hmaxr
      exact ⟨M', RoundFold.last hmaxr hfold,
        k, hk.trans (Nat.le_mul_of_pos_left _ hposr), hs⟩
    · obtain ⟨r', hr'⟩ := exists_succElt hmaxr
      obtain ⟨M₁, hfold₁, hnextr, -⟩ := steps_hClauses hmin r c₀ hmin.1 M
      obtain ⟨k₁, hk₁, hs₁⟩ := hnextr r' hr'
      obtain ⟨M', hfold', k', hk', hs'⟩ := IH r' hr'.1 M₁
      refine ⟨M', RoundFold.step hr' hfold₁ hfold', k₁ + k', ?_, hs₁.trans hs'⟩
      rw [ncard_ge_succElt hr', Nat.succ_mul]
      exact (Nat.add_le_add hk₁ hk').trans (le_of_eq (Nat.add_comm _ _))

/-! ### The verification phase -/

/-- Verifying `c` rightwards and moving on to the next clause. -/
theorem steps_hVerClauseR (M : A → Bool) {c c' : A} (hc : SatCl c)
    (hnext : SatNextCl c c') (hsat : ∃ y : A, MLit c y (M y)) :
    ∃ k ≤ bitRank tagTupleLe HPosn (posHEnd : HV A),
      (hornMachine A).StepsIn k (confHVerR M c (posHCell botA))
        (confHVerL M c' (posHCell topA)) := by
  refine ⟨_, ?_, (steps_hVerRAll M hc).trans_step
    (step_hVerNextR M hnext ((verFlagR_posHEnd M c).mpr hsat))⟩
  have e2 := bitRank_posHEnd_eq (A := A)
  have e3 := bitRank_posHCell_botA (A := A)
  omega

/-- Verifying `c` leftwards and moving on to the next clause. -/
theorem steps_hVerClauseL (M : A → Bool) {c c' : A} (hc : SatCl c)
    (hnext : SatNextCl c c') (hsat : ∃ y : A, MLit c y (M y)) :
    ∃ k ≤ bitRank tagTupleLe HPosn (posHEnd : HV A),
      (hornMachine A).StepsIn k (confHVerL M c (posHCell topA))
        (confHVerR M c' (posHCell botA)) := by
  refine ⟨_, ?_, (steps_hVerLAll M hc).trans_step
    (step_hVerNextL M hnext ((verFlagL_posHStart M c).mpr hsat))⟩
  have e1 := bitRank_posHStart (A := A)
  have e2 := bitRank_posHEnd_eq (A := A)
  omega

/-- Verifying the last clause rightwards, and accepting. -/
theorem steps_hVerClauseAccR (M : A → Bool) {c : A} (hc : SatCl c)
    (hmax : SatMaxCl c) (hhorn : AtMostOnePositive A) (hsat : ∃ y : A, MLit c y (M y)) :
    ∃ k ≤ bitRank tagTupleLe HPosn (posHEnd : HV A), ∃ cfin : Config (HV A),
      (hornMachine A).StepsIn k (confHVerR M c (posHCell botA)) cfin ∧
        HAcc cfin.state := by
  refine ⟨_, ?_, _, (steps_hVerRAll M hc).trans_step
    (step_hVerAccR M hmax hhorn ((verFlagR_posHEnd M c).mpr hsat)), rfl⟩
  have e2 := bitRank_posHEnd_eq (A := A)
  have e3 := bitRank_posHCell_botA (A := A)
  omega

/-- Verifying the last clause leftwards, and accepting. -/
theorem steps_hVerClauseAccL (M : A → Bool) {c : A} (hc : SatCl c)
    (hmax : SatMaxCl c) (hhorn : AtMostOnePositive A) (hsat : ∃ y : A, MLit c y (M y)) :
    ∃ k ≤ bitRank tagTupleLe HPosn (posHEnd : HV A), ∃ cfin : Config (HV A),
      (hornMachine A).StepsIn k (confHVerL M c (posHCell topA)) cfin ∧
        HAcc cfin.state := by
  refine ⟨_, ?_, _, (steps_hVerLAll M hc).trans_step
    (step_hVerAccL M hmax hhorn ((verFlagL_posHStart M c).mpr hsat)), rfl⟩
  have e1 := bitRank_posHStart (A := A)
  have e2 := bitRank_posHEnd_eq (A := A)
  omega

/-- **The verification phase accepts**: every remaining clause is satisfied by
the marks, so the sweeps run through and the machine accepts after the last
one – the SAT machine's clause induction, verbatim, with the marks as
valuation. -/
theorem hVer_accepts (M : A → Bool) (hhorn : AtMostOnePositive A)
    (hsat : ∀ e : A, SatCl e → ∃ y : A, MLit e y (M y)) :
    ∀ c : A, SatCl c →
      (∃ (n : ℕ) (cfin : Config (HV A)),
          n ≤ {e : A | SatCl e ∧ c ≤ e}.ncard * bitRank tagTupleLe HPosn (posHEnd : HV A) ∧
          (hornMachine A).StepsIn n (confHVerR M c (posHCell botA)) cfin ∧
            HAcc cfin.state) ∧
        ∃ (n : ℕ) (cfin : Config (HV A)),
          n ≤ {e : A | SatCl e ∧ c ≤ e}.ncard * bitRank tagTupleLe HPosn (posHEnd : HV A) ∧
          (hornMachine A).StepsIn n (confHVerL M c (posHCell topA)) cfin ∧
            HAcc cfin.state := by
  intro c
  induction c using WellFoundedGT.induction with
  | ind c IH =>
    intro hc
    have hpos : 0 < {e : A | SatCl e ∧ c ≤ e}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨c, hc, le_refl c⟩
    by_cases hmax : SatMaxCl c
    · obtain ⟨kR, hkR, cfR, hR, haR⟩ := steps_hVerClauseAccR M hc hmax hhorn (hsat c hc)
      obtain ⟨kL, hkL, cfL, hL, haL⟩ := steps_hVerClauseAccL M hc hmax hhorn (hsat c hc)
      exact ⟨⟨kR, cfR, hkR.trans (Nat.le_mul_of_pos_left _ hpos), hR, haR⟩,
        ⟨kL, cfL, hkL.trans (Nat.le_mul_of_pos_left _ hpos), hL, haL⟩⟩
    · obtain ⟨c', hnext⟩ := exists_satNextCl hc hmax
      obtain ⟨⟨nR, cfR, hnR, hR, haR⟩, ⟨nL, cfL, hnL, hL, haL⟩⟩ := IH c' hnext.2.2.1 hnext.2.1
      obtain ⟨j, hj, hstepR⟩ := steps_hVerClauseR M hc hnext (hsat c hc)
      obtain ⟨j', hj', hstepL⟩ := steps_hVerClauseL M hc hnext (hsat c hc)
      have hcount : ∀ {a b : ℕ}, a ≤ bitRank tagTupleLe HPosn (posHEnd : HV A) →
          b ≤ {e : A | SatCl e ∧ c' ≤ e}.ncard * bitRank tagTupleLe HPosn (posHEnd : HV A) →
          a + b ≤
            {e : A | SatCl e ∧ c ≤ e}.ncard * bitRank tagTupleLe HPosn (posHEnd : HV A) := by
        intro a b ha hb
        rw [ncard_clauses_next hnext, Nat.succ_mul]
        exact (Nat.add_le_add ha hb).trans (le_of_eq (Nat.add_comm _ _))
      exact ⟨⟨j + nL, cfL, hcount hj hnL, hstepR.trans hL, haL⟩,
        ⟨j' + nR, cfR, hcount hj' hnR, hstepL.trans hR, haR⟩⟩

/-! ### The machine accepts every Horn-satisfiable instance -/

/-- The final marks are exactly the propagation closure. -/
theorem roundFold_marks_eq_forced {c₀ : A} (hmin : SatMinCl c₀) {M' : A → Bool}
    (h : RoundFold c₀ botA (fun _ => false) M') :
    ∀ x : A, M' x = true ↔ Forced x := by
  classical
  intro x
  constructor
  · exact fun hx => h.subset_forced (fun y hy => absurd hy (by simp)) x hx
  · intro hx
    have hcard : {e : A | botA (A := A) ≤ e}.ncard = Nat.card A := by
      have hset : {e : A | botA (A := A) ≤ e} = Set.univ := by
        ext e
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact botA_le e
      rw [hset, Set.ncard_univ]
    refine h.forcedIn_subset hmin 0 (fun y hy => hy.elim) x ?_
    rw [Nat.zero_add, hcard]
    exact forced_forcedIn_card hx

/-- **The machine accepts every yes-instance of HORN-SAT**, within the
budget: dispatch, `n` rounds of propagation, and a verification pass that the
closure – which satisfiability makes a model – lets run to acceptance. -/
theorem hornMachine_accepts_of (hhorn : AtMostOnePositive A) (hsat : Satisfiable A) :
    (hornMachine A).Accepts := by
  classical
  have hn : 1 ≤ Nat.card A := Nat.card_pos
  have hbudget := card_le_card_hPosn A
  have hb := horn_budget hn
  by_cases hcl : ∃ e : A, SatCl e
  · obtain ⟨c₀, hc₀, hminc⟩ := exists_minPos (Le := (· ≤ · : A → A → Prop))
      (Posn := fun e : A => SatCl e)
      ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩ hcl
    have hmin : SatMinCl c₀ := ⟨hc₀, hminc⟩
    obtain ⟨M', hfold, k₁, hk₁, hs₁⟩ := steps_hRounds hmin botA (fun _ => false)
    have hMf := roundFold_marks_eq_forced hmin hfold
    have hsatM : ∀ e : A, SatCl e → ∃ y : A, MLit e y (M' y) := by
      intro e he
      obtain ⟨y, hy⟩ := (satisfiable_iff_forced_model hhorn).mp hsat e he
      rcases hy with ⟨hp, hf⟩ | ⟨hnn, hf⟩
      · exact ⟨y, Or.inl ⟨hp, (hMf y).mpr hf⟩⟩
      · refine ⟨y, Or.inr ⟨hnn, ?_⟩⟩
        rcases Bool.eq_false_or_eq_true (M' y) with h | h
        · exact absurd ((hMf y).mp h) hf
        · exact h
    obtain ⟨⟨n₂, cfin, hn₂, hs₂, hacc⟩, -⟩ := hVer_accepts M' hhorn hsatM c₀ hc₀
    have hchain := ((TMData.StepsIn.trans_step
      (show (hornMachine A).StepsIn 0 confHInit confHInit from rfl)
      (step_hInitChk hmin)).trans hs₁).trans hs₂
    refine ⟨confHInit, cfin, 0 + 1 + k₁ + n₂, isInit_confHInit, ?_, hchain, hacc⟩
    -- the budget
    have hR : bitRank tagTupleLe HPosn (posHEnd : HV A) ≤ Nat.card A + 1 :=
      bitRank_posHEnd_le
    have hm : {e : A | SatCl e ∧ c₀ ≤ e}.ncard ≤ Nat.card A := by
      have h := Set.ncard_le_ncard (Set.subset_univ {e : A | SatCl e ∧ c₀ ≤ e})
        (Set.toFinite _)
      rwa [Set.ncard_univ] at h
    have hr : {e : A | botA (A := A) ≤ e}.ncard ≤ Nat.card A := by
      have h := Set.ncard_le_ncard (Set.subset_univ {e : A | botA (A := A) ≤ e})
        (Set.toFinite _)
      rwa [Set.ncard_univ] at h
    set n := Nat.card A
    set R := bitRank tagTupleLe HPosn (posHEnd : HV A)
    set mc := {e : A | SatCl e ∧ c₀ ≤ e}.ncard
    set mr := {e : A | botA (A := A) ≤ e}.ncard
    have h1 : k₁ ≤ n * (n * (2 * (n + 1) + 1)) := by
      calc k₁ ≤ mr * (mc * (2 * R + 1)) := hk₁
        _ ≤ n * (n * (2 * (n + 1) + 1)) := by
          refine Nat.mul_le_mul hr (Nat.mul_le_mul hm ?_)
          omega
    have h2 : n₂ ≤ n * (n + 1) := by
      calc n₂ ≤ mc * R := hn₂
        _ ≤ n * (n + 1) := Nat.mul_le_mul hm hR
    have hlt : 0 + 1 + k₁ + n₂ < (2 * n * n + n + 2) * (n + 2) := by
      nlinarith [h1, h2, hn]
    exact lt_of_lt_of_le (lt_of_lt_of_le hlt (le_of_lt hb)) hbudget
  · have hno : ∀ e : A, ¬ SatCl e := fun e he => hcl ⟨e, he⟩
    refine ⟨confHInit, _, 1, isInit_confHInit, ?_,
      ⟨_, step_hInitAcc hno, rfl⟩, rfl⟩
    have h16 : 16 ≤ 16 * Nat.card A * Nat.card A * Nat.card A := by
      calc (16 : ℕ) = 16 * 1 * 1 * 1 := by norm_num
        _ ≤ 16 * Nat.card A * Nat.card A * Nat.card A :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 16) hn) hn) hn
    have hbudget' : 16 * Nat.card A * Nat.card A * Nat.card A ≤
        Nat.card {p : HV A // (hornMachine A).Posn p} := hbudget
    omega

/-! ### The machine accepts only Horn-satisfiable instances

Determinism replaces the SAT machine's run-analysis induction: the run from the
unique initial configuration *is* the intended trajectory, so it suffices that
on a non-Horn-satisfiable instance the trajectory never carries an accepting
state – either because no accept transition exists at all (the Horn gate), or
because the trajectory gets stuck at the first failing verification sweep. -/

/-- No transition applies in an accepting state: once accepted, the machine
halts, so an accepting run cannot be a strict prefix of another. -/
theorem hTag_no_stateTag_qAcc : ∀ t : UPTag, isHTrTag t → hStateTag t ≠ UPTag.qAcc := by
  decide

/-- No transition applies in a failed verification state on a marker: the run
dies there. -/
theorem hTag_verFalse_no_marker : ∀ (t : UPTag) (d : Bool), isHTrTag t →
    hStateTag t = UPTag.qVer false d →
    hReadTag t ≠ UPTag.sStart ∧ hReadTag t ≠ UPTag.sEnd := by
  decide

/-- The only transitions into an accepting state are the two accept
transitions. -/
theorem hDst_acc_cases {τ q : HV A} (hd : HDst τ q) (hq : q.1 = UPTag.qAcc) :
    τ.1 = UPTag.tInitAcc ∨ ∃ d : Bool, τ.1 = UPTag.tVerAcc d := by
  obtain ⟨t, w⟩ := τ
  cases t <;> dsimp only [HDst] at hd
  case tInitAcc => exact Or.inl rfl
  case tVerAcc d => exact Or.inr ⟨d, rfl⟩
  case tInitChk =>
    rw [hd] at hq
    exact UPTag.noConfusion hq
  case tChk m f =>
    rcases hd with ⟨hd, -⟩ | ⟨hd, -⟩ <;> (rw [hd] at hq; exact UPTag.noConfusion hq)
  case tChkEnd f =>
    rw [hd] at hq
    exact UPTag.noConfusion hq
  case tMark m mrk =>
    rw [hd] at hq
    exact UPTag.noConfusion hq
  case tMarkEndNext mrk =>
    rw [hd] at hq
    exact UPTag.noConfusion hq
  case tMarkEndRound mrk =>
    exact UPTag.noConfusion (hd.1.symm.trans hq)
  case tMarkEndVer mrk =>
    exact UPTag.noConfusion (hd.1.symm.trans hq)
  case tVer m f d =>
    rcases hd with ⟨hd, -⟩ | ⟨hd, -⟩ <;> (rw [hd] at hq; exact UPTag.noConfusion hq)
  case tVerNext d =>
    rw [hd] at hq
    exact UPTag.noConfusion hq

/-- **A failed rightward verification sweep is stuck** at the right marker. -/
theorem no_step_verR_false (M : A → Bool) {c : A}
    (hflag : verFlagR M c (posHEnd : HV A) = false) (d : Config (HV A)) :
    ¬ (hornMachine A).Step (confHVerR M c posHEnd) d := by
  rintro ⟨τ, hτ, hsrc, hread, -, -, -, -⟩
  have hst : hStateTag τ.1 = UPTag.qVer false true := by
    have h := (hSrc_tag hsrc).symm
    rwa [show (confHVerR M c posHEnd).state.1 = UPTag.qVer (verFlagR M c posHEnd) true
      from rfl, hflag] at h
  exact (hTag_verFalse_no_marker τ.1 true (hTr_isHTrTag hτ) hst).2 (hRead_tag hread).symm

/-- **A failed leftward verification sweep is stuck** at the left marker. -/
theorem no_step_verL_false (M : A → Bool) {c : A}
    (hflag : verFlagL M c (posHStart : HV A) = false) (d : Config (HV A)) :
    ¬ (hornMachine A).Step (confHVerL M c posHStart) d := by
  rintro ⟨τ, hτ, hsrc, hread, -, -, -, -⟩
  have hst : hStateTag τ.1 = UPTag.qVer false false := by
    have h := (hSrc_tag hsrc).symm
    rwa [show (confHVerL M c posHStart).state.1 = UPTag.qVer (verFlagL M c posHStart) false
      from rfl, hflag] at h
  exact (hTag_verFalse_no_marker τ.1 false (hTr_isHTrTag hτ) hst).1 (hRead_tag hread).symm

/-- **The trajectory of an unsatisfiable Horn instance gets stuck**: the
verification sweeps run through the satisfied clauses and die at the first
failing one, in a configuration that is not accepting and admits no step. -/
theorem hVer_stuck (M : A → Bool) {cf : A} (hcf : SatCl cf)
    (hfail : ¬ ∃ y : A, MLit cf y (M y)) :
    ∀ c : A, SatCl c → c ≤ cf →
      (∀ e : A, SatCl e → c ≤ e → e < cf → ∃ y : A, MLit e y (M y)) →
      (∃ (N : ℕ) (S : Config (HV A)),
          (hornMachine A).StepsIn N (confHVerR M c (posHCell botA)) S ∧
          (∀ d, ¬ (hornMachine A).Step S d) ∧ S.state.1 ≠ UPTag.qAcc) ∧
        ∃ (N : ℕ) (S : Config (HV A)),
          (hornMachine A).StepsIn N (confHVerL M c (posHCell topA)) S ∧
          (∀ d, ¬ (hornMachine A).Step S d) ∧ S.state.1 ≠ UPTag.qAcc := by
  classical
  intro c
  induction c using WellFoundedGT.induction with
  | ind c IH =>
    intro hc hle hver
    rcases eq_or_lt_of_le hle with heq | hlt
    · subst heq
      have hflagR : verFlagR M c (posHEnd : HV A) = false := by
        rcases Bool.eq_false_or_eq_true (verFlagR M c (posHEnd : HV A)) with h | h
        · exact absurd ((verFlagR_posHEnd M c).mp h) hfail
        · exact h
      have hflagL : verFlagL M c (posHStart : HV A) = false := by
        rcases Bool.eq_false_or_eq_true (verFlagL M c (posHStart : HV A)) with h | h
        · exact absurd ((verFlagL_posHStart M c).mp h) hfail
        · exact h
      refine ⟨⟨_, _, steps_hVerRAll M hc, no_step_verR_false M hflagR,
          fun h => UPTag.noConfusion h⟩,
        ⟨_, _, steps_hVerLAll M hc, no_step_verL_false M hflagL,
          fun h => UPTag.noConfusion h⟩⟩
    · have hnmax : ¬ SatMaxCl c := fun hmax => absurd (hmax.2 cf hcf) (not_le.mpr hlt)
      obtain ⟨c', hnext⟩ := exists_satNextCl hc hnmax
      have hc'le : c' ≤ cf := hnext.2.2.2 cf hcf hlt
      have hver' : ∀ e : A, SatCl e → c' ≤ e → e < cf → ∃ y : A, MLit e y (M y) :=
        fun e he hce hlt' => hver e he (le_trans hnext.2.2.1.le hce) hlt'
      obtain ⟨⟨NR, SR, hsR, hstR, haR⟩, ⟨NL, SL, hsL, hstL, haL⟩⟩ :=
        IH c' hnext.2.2.1 hnext.2.1 hc'le hver'
      have hsatc : ∃ y : A, MLit c y (M y) := hver c hc (le_refl c) hlt
      obtain ⟨jR, -, hstepR⟩ := steps_hVerClauseR M hc hnext hsatc
      obtain ⟨jL, -, hstepL⟩ := steps_hVerClauseL M hc hnext hsatc
      exact ⟨⟨jR + NL, SL, hstepR.trans hsL, hstL, haL⟩,
        ⟨jL + NR, SR, hstepL.trans hsR, hstR, haR⟩⟩

/-- **Correctness of the unit-propagation machine**: it accepts exactly the
yes-instances of HORN-SAT. -/
theorem hornMachine_accepts_iff :
    (hornMachine A).Accepts ↔ HornSatisfiable A := by
  classical
  constructor
  · intro hacc
    by_contra hns
    obtain ⟨cinit, cfin, nrun, hinit, -, hrun, haccst⟩ := hacc
    obtain rfl := TMData.isInit_unique hornMachine_wellFormed
      hornMachine_deterministic.1 hinit isInit_confHInit
    by_cases hhorn : AtMostOnePositive A
    · have hnsat : ¬ Satisfiable A := fun hs => hns ⟨hhorn, hs⟩
      have hcl : ∃ e : A, SatCl e := by
        by_contra hnocl
        push Not at hnocl
        exact hnsat ⟨fun _ => True, fun c hc => absurd hc (hnocl c)⟩
      obtain ⟨c₀, hc₀, hminc⟩ := exists_minPos (Le := (· ≤ · : A → A → Prop))
        (Posn := fun e : A => SatCl e)
        ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩ hcl
      have hmin : SatMinCl c₀ := ⟨hc₀, hminc⟩
      obtain ⟨M', hfold, k₁, -, hs₁⟩ := steps_hRounds hmin botA (fun _ => false)
      have hMf := roundFold_marks_eq_forced hmin hfold
      have hex : ∃ c : A, SatCl c ∧ ¬ ∃ y : A, MLit c y (M' y) := by
        by_contra hall
        push Not at hall
        refine hnsat ((satisfiable_iff_forced_model hhorn).mpr fun c hc => ?_)
        obtain ⟨y, hy⟩ := hall c hc
        rcases hy with ⟨hp, hM⟩ | ⟨hnn, hM⟩
        · exact ⟨y, Or.inl ⟨hp, (hMf y).mp hM⟩⟩
        · refine ⟨y, Or.inr ⟨hnn, fun hf => ?_⟩⟩
          rw [(hMf y).mpr hf] at hM
          exact Bool.noConfusion hM
      obtain ⟨cf, ⟨hcfcl, hcffail⟩, hcfmin⟩ := exists_minPos (Le := (· ≤ · : A → A → Prop))
        (Posn := fun c : A => SatCl c ∧ ¬ ∃ y : A, MLit c y (M' y))
        ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩ hex
      have hver : ∀ e : A, SatCl e → c₀ ≤ e → e < cf → ∃ y : A, MLit e y (M' y) := by
        intro e he _ hlt
        by_contra hf
        exact absurd (hcfmin e ⟨he, hf⟩) (not_le.mpr hlt)
      obtain ⟨⟨N₂, S, hsN, hstuck, hSacc⟩, -⟩ :=
        hVer_stuck M' hcfcl hcffail c₀ hc₀ (hmin.2 cf hcfcl) hver
      have htraj : (hornMachine A).StepsIn (1 + k₁ + N₂) confHInit S :=
        (TMData.StepsIn.trans (show (hornMachine A).StepsIn 1 confHInit
            (confHChk (fun _ => false) botA c₀ (posHCell botA)) from
          ⟨_, step_hInitChk hmin, rfl⟩) hs₁).trans hsN
      rcases Nat.lt_or_ge (1 + k₁ + N₂) nrun with hlt2 | hge
      · obtain ⟨e, he1, he2⟩ := TMData.stepsIn_split (m := 1 + k₁ + N₂)
          (k := nrun - (1 + k₁ + N₂))
          (by rw [Nat.add_sub_cancel' hlt2.le]; exact hrun)
        obtain rfl := TMData.stepsIn_functional hornMachine_wellFormed.1
          hornMachine_deterministic htraj he1
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.pos_iff_ne_zero.mp (by omega : 0 < nrun - (1 + k₁ + N₂)))
        rw [hm] at he2
        obtain ⟨d, hstep, -⟩ := he2
        exact hstuck d hstep
      · obtain ⟨e, he1, he2⟩ := TMData.stepsIn_split (m := nrun)
          (k := 1 + k₁ + N₂ - nrun)
          (by rw [Nat.add_sub_cancel' hge]; exact htraj)
        obtain rfl := TMData.stepsIn_functional hornMachine_wellFormed.1
          hornMachine_deterministic hrun he1
        rcases Nat.eq_zero_or_pos (1 + k₁ + N₂ - nrun) with hz | hpos2
        · rw [hz] at he2
          obtain rfl : cfin = S := he2
          exact hSacc haccst
        · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos2)
          rw [hm] at he2
          obtain ⟨d, hstep, -⟩ := he2
          obtain ⟨τ, hτ, hsrc, -, -, -, -, -⟩ := hstep
          exact hTag_no_stateTag_qAcc τ.1 (hTr_isHTrTag hτ)
            ((hSrc_tag hsrc).symm.trans haccst)
    · rcases Nat.eq_zero_or_pos nrun with hz | hpos2
      · rw [hz] at hrun
        obtain rfl : confHInit = cfin := hrun
        exact UPTag.noConfusion haccst
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos2)
        rw [hm] at hrun
        obtain ⟨d, hd, hstep⟩ := TMData.stepsIn_succ_iff.mp hrun
        obtain ⟨τ, hτ, -, -, hdst, -, -, -⟩ := hstep
        rcases hDst_acc_cases hdst haccst with hτ1 | ⟨dd, hτ1⟩
        · obtain ⟨c, x, y, hc, -, -, -⟩ := not_atMostOnePositive_iff.mp hhorn
          exact (hTr_at hτ _ hτ1).2 c hc
        · exact hhorn (hTr_at hτ _ hτ1).2.2.2
  · rintro ⟨hhorn, hsat⟩
    exact hornMachine_accepts_of hhorn hsat

end Run

end HornMachine

end DescriptiveComplexity
