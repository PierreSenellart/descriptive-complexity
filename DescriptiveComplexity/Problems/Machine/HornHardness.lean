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

The program half of `HORNSAT ≤ᶠᵒ[≤] DTMAccept`, stage 4 of the machine bridge:
the states, symbols and transitions of the deterministic machine computing the
unit-propagation closure of a CNF instance and verifying it, on the tape laid
out in `DescriptiveComplexity.Problems.Machine.HornTape`.

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
yes-instance of `DTMAccept` at all. The instance is read exactly as in stage 3
(`DescriptiveComplexity.SatCl`, `DescriptiveComplexity.SatPos`, …, imported from
`DescriptiveComplexity.Problems.Machine.Hardness` together with the clause-order
machinery), and the only two additions are the element order (rounds walk it)
and the Horn gate on the accept transition.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

noncomputable section HornMachine

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The elements of the machine -/

/-- The universe of the machine: tagged triples. -/
abbrev HV (A : Type) := HTag × (Fin 3 → A)

/-- A constant of the machine: a tag on the triple of least elements. -/
def cstH (t : HTag) : HV A := (t, fun _ => botA)

/-- A tag carrying one element. -/
def oneH (t : HTag) (a : A) : HV A := (t, ![a, botA, botA])

/-- A tag carrying two elements. -/
def twoH (t : HTag) (a b : A) : HV A := (t, ![a, b, botA])

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
  | .tInitChk => q = stHChk false (τ.2 0) (τ.2 1)
  | .tInitAcc => q = stHAcc
  | .tChk m f =>
      (q = stHChk true (τ.2 0) (τ.2 1) ∧ f = true ∧ (SatNeg (τ.2 1) (τ.2 2) → m = true)) ∨
        (q = stHChk false (τ.2 0) (τ.2 1) ∧
          (f = false ∨ (SatNeg (τ.2 1) (τ.2 2) ∧ m = false)))
  | .tChkEnd f => q = stHMark f (τ.2 0) (τ.2 1)
  | .tMark _ mrk => q = stHMark mrk (τ.2 0) (τ.2 1)
  | .tMarkEndNext _ => q = stHChk false (τ.2 0) (τ.2 2)
  | .tMarkEndRound _ =>
      q.1 = HTag.qChk false ∧ q.2 0 = τ.2 1 ∧ SatMinCl (q.2 1) ∧ ∀ a : A, q.2 2 ≤ a
  | .tMarkEndVer _ =>
      q.1 = HTag.qVer false true ∧ SatMinCl (q.2 0) ∧ (∀ a : A, q.2 1 ≤ a) ∧
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
def HAcc (q : HV A) : Prop := q.1 = HTag.qAcc

/-- Start states: the dispatch state alone. -/
def HStart (q : HV A) : Prop := q.1 = HTag.qInit ∧ IsMinTup3 q.2

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

There is no guess phase, so – unlike stage 3 – the whole table is functional:
the state and the symbol read pin the transition's tag up to promise-exclusive
alternatives, the tag pins the payload, and the branching destinations and
writes are separated by their first-order tests. This discharges the
`DescriptiveComplexity.TMData.Deterministic` promise of the constructed instance,
which is part of the correctness of the reduction. -/

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
theorem oneH_eq_oneH_iff {t t' : HTag} {a a' : A} :
    (oneH t a : HV A) = oneH t' a' ↔ t = t' ∧ a = a' := by
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, ?_⟩
    have := congrFun (congrArg Prod.snd h) 0
    simpa [oneH] using this
  · rintro ⟨rfl, rfl⟩; rfl

omit [Language.sat.Structure A] in
theorem twoH_eq_twoH_iff {t t' : HTag} {a a' b b' : A} :
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
def hStateTag : HTag → HTag
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
def hReadTag : HTag → HTag
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
def isHTrTag : HTag → Bool
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
def isInitChk : HTag → Bool | .tInitChk => true | _ => false

@[inherit_doc isInitChk] def isInitAcc : HTag → Bool | .tInitAcc => true | _ => false

@[inherit_doc isInitChk] def isMarkEndNext : HTag → Bool
  | .tMarkEndNext _ => true | _ => false

@[inherit_doc isInitChk] def isMarkEndRound : HTag → Bool
  | .tMarkEndRound _ => true | _ => false

@[inherit_doc isInitChk] def isMarkEndVer : HTag → Bool
  | .tMarkEndVer _ => true | _ => false

@[inherit_doc isInitChk] def isVerNext : HTag → Bool | .tVerNext _ => true | _ => false

@[inherit_doc isInitChk] def isVerAcc : HTag → Bool | .tVerAcc _ => true | _ => false

set_option maxRecDepth 8000 in
/-- **The state and the symbol determine the transition's tag**, up to the
promise-exclusive alternatives: the two dispatches, the three ends of a return
sweep, and the two ends of a verification sweep. A finite check over the
tags. -/
theorem hTag_cases : ∀ t t' : HTag, isHTrTag t → isHTrTag t' →
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
/-- The highest clause is unique. -/
theorem satMaxCl_unique {c c' : A} (h : SatMaxCl c) (h' : SatMaxCl c') : c = c' :=
  le_antisymm (h'.2 c h.1) (h.2 c' h'.1)

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
    (hτ : τ.1 = HTag.tInitChk) (hτ' : τ'.1 = HTag.tInitAcc) : False := by
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

theorem isInitChk_iff {t : HTag} : isInitChk t ↔ t = .tInitChk := by
  cases t <;> simp [isInitChk]

theorem isInitAcc_iff {t : HTag} : isInitAcc t ↔ t = .tInitAcc := by
  cases t <;> simp [isInitAcc]

theorem isMarkEndNext_iff {t : HTag} : isMarkEndNext t ↔ ∃ mrk, t = .tMarkEndNext mrk := by
  cases t <;> simp [isMarkEndNext]

theorem isMarkEndRound_iff {t : HTag} : isMarkEndRound t ↔ ∃ mrk, t = .tMarkEndRound mrk := by
  cases t <;> simp [isMarkEndRound]

theorem isMarkEndVer_iff {t : HTag} : isMarkEndVer t ↔ ∃ mrk, t = .tMarkEndVer mrk := by
  cases t <;> simp [isMarkEndVer]

theorem isVerNext_iff {t : HTag} : isVerNext t ↔ ∃ d, t = .tVerNext d := by
  cases t <;> simp [isVerNext]

theorem isVerAcc_iff {t : HTag} : isVerAcc t ↔ ∃ d, t = .tVerAcc d := by
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
        σ.1 = HTag.tMarkEndNext m →
        (σ'.1 = HTag.tMarkEndRound m' ∨ σ'.1 = HTag.tMarkEndVer m') → False := by
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
        σ.1 = HTag.tMarkEndRound m → σ'.1 = HTag.tMarkEndVer m' → False := by
      intro σ σ' m m' hσ hσ' hsσ hsσ' h h'
      have hq := hSrc_eq hsσ _ h
      have hq' := hSrc_eq hsσ' _ h'
      obtain ⟨-, hrr, -⟩ := twoH_eq_twoH_iff.mp (hq.symm.trans hq')
      exact succElt_maxElt_excl (hTr_at hσ _ h).1 (hTr_at hσ' _ h').1 hrr
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
    · obtain ⟨m, hm⟩ := isMarkEndNext_iff.mp h1
      obtain ⟨m', hm'⟩ := isMarkEndNext_iff.mp h2
      obtain ⟨he, -, -⟩ := twoH_eq_twoH_iff.mp ((hSrc_eq hs _ hm).symm.trans (hSrc_eq hs' _ hm'))
      exact hpay (by rw [hm, hm', HTag.qMark.inj he])
    · exact absurd (hend hτ hτ' hs hs' (isMarkEndNext_iff.mp h1).choose_spec
        (Or.inl (isMarkEndRound_iff.mp h2).choose_spec)) not_false
    · exact absurd (hend hτ hτ' hs hs' (isMarkEndNext_iff.mp h1).choose_spec
        (Or.inr (isMarkEndVer_iff.mp h2).choose_spec)) not_false
    · exact absurd (hend hτ' hτ hs' hs (isMarkEndNext_iff.mp h2).choose_spec
        (Or.inl (isMarkEndRound_iff.mp h1).choose_spec)) not_false
    · obtain ⟨m, hm⟩ := isMarkEndRound_iff.mp h1
      obtain ⟨m', hm'⟩ := isMarkEndRound_iff.mp h2
      obtain ⟨he, -, -⟩ := twoH_eq_twoH_iff.mp ((hSrc_eq hs _ hm).symm.trans (hSrc_eq hs' _ hm'))
      exact hpay (by rw [hm, hm', HTag.qMark.inj he])
    · exact absurd (hrv hτ hτ' hs hs' (isMarkEndRound_iff.mp h1).choose_spec
        (isMarkEndVer_iff.mp h2).choose_spec) not_false
    · exact absurd (hend hτ' hτ hs' hs (isMarkEndNext_iff.mp h2).choose_spec
        (Or.inr (isMarkEndVer_iff.mp h1).choose_spec)) not_false
    · exact absurd (hrv hτ' hτ hs' hs (isMarkEndRound_iff.mp h2).choose_spec
        (isMarkEndVer_iff.mp h1).choose_spec) not_false
    · obtain ⟨m, hm⟩ := isMarkEndVer_iff.mp h1
      obtain ⟨m', hm'⟩ := isMarkEndVer_iff.mp h2
      obtain ⟨he, -, -⟩ := twoH_eq_twoH_iff.mp ((hSrc_eq hs _ hm).symm.trans (hSrc_eq hs' _ hm'))
      exact hpay (by rw [hm, hm', HTag.qMark.inj he])
  · -- the two ends of a verification sweep
    have hva : ∀ {σ σ' : HV A} {d d' : Bool}, HTr σ → HTr σ' → HSrc σ q → HSrc σ' q →
        σ.1 = HTag.tVerNext d → σ'.1 = HTag.tVerAcc d' → False := by
      intro σ σ' d d' hσ hσ' hsσ hsσ' h h'
      have hq := hSrc_eq hsσ _ h
      have hq' := hSrc_eq hsσ' _ h'
      obtain ⟨-, hcc⟩ := oneH_eq_oneH_iff.mp (hq.symm.trans hq')
      exact hTr_next_max_excl (hTr_at hσ _ h).1 (hTr_at hσ' _ h').1 hcc
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · obtain ⟨d, hd⟩ := isVerNext_iff.mp h1
      obtain ⟨d', hd'⟩ := isVerNext_iff.mp h2
      obtain ⟨he, -⟩ := oneH_eq_oneH_iff.mp ((hSrc_eq hs _ hd).symm.trans (hSrc_eq hs' _ hd'))
      exact hpay (by rw [hd, hd', (HTag.qVer.inj he).2])
    · exact absurd (hva hτ hτ' hs hs' (isVerNext_iff.mp h1).choose_spec
        (isVerAcc_iff.mp h2).choose_spec) not_false
    · exact absurd (hva hτ' hτ hs' hs (isVerNext_iff.mp h2).choose_spec
        (isVerAcc_iff.mp h1).choose_spec) not_false
    · obtain ⟨d, hd⟩ := isVerAcc_iff.mp h1
      obtain ⟨d', hd'⟩ := isVerAcc_iff.mp h2
      obtain ⟨he, -⟩ := oneH_eq_oneH_iff.mp ((hSrc_eq hs _ hd).symm.trans (hSrc_eq hs' _ hd'))
      exact hpay (by rw [hd, hd', (HTag.qVer.inj he).2])

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

The dimension-3 mirror of stage 3's marker and cell lemmas: the left marker is
the lowest position, cells follow in the order of their elements, the right
marker closes the chain, and ranks are what the budget compares. -/

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
theorem hpStart_lt {t : HTag} (h : t ≠ HTag.pStart) : HTag.pStart < t := by
  revert h; revert t; decide

omit [Language.sat.Structure A] in
/-- There is only one left marker. -/
theorem eq_posHStart_of_posn {p : HV A} (hp : HPosn p) (h : p.1 = HTag.pStart) :
    p = posHStart := by
  obtain ⟨t, w⟩ := p
  cases h
  exact Prod.ext rfl (isMinTup3_unique hp isMinTup3_bot)

omit [Language.sat.Structure A] in
/-- There is only one right marker. -/
theorem eq_posHEnd_of_posn {p : HV A} (hp : HPosn p) (h : p.1 = HTag.pEnd) :
    p = posHEnd := by
  obtain ⟨t, w⟩ := p
  cases h
  exact Prod.ext rfl (isMinTup3_unique hp isMinTup3_bot)

omit [Language.sat.Structure A] in
/-- A cell is the cell of the element it carries. -/
theorem eq_posHCell_of_posn {p : HV A} (hp : HPosn p) (h : p.1 = HTag.pCell) :
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
  rcases eq_or_ne q.1 HTag.pStart with h | h
  · rw [eq_posHStart_of_posn hq h]
    exact hTagTupleLe_refl _
  · exact hTagTupleLe_of_tag_lt (hpStart_lt h)

omit [Language.sat.Structure A] in
theorem posHStart_le_posHCell (x : A) : tagTupleLe (posHStart : HV A) (posHCell x) :=
  hTagTupleLe_of_tag_lt (show HTag.pStart < HTag.pCell by decide)

omit [Language.sat.Structure A] in
theorem posHCell_le_posHEnd (x : A) : tagTupleLe (posHCell x : HV A) posHEnd :=
  hTagTupleLe_of_tag_lt (show HTag.pCell < HTag.pEnd by decide)

omit [Language.sat.Structure A] in
theorem posHStart_le_posHEnd : tagTupleLe (posHStart : HV A) posHEnd :=
  hTagTupleLe_of_tag_lt (show HTag.pStart < HTag.pEnd by decide)

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
theorem htag_le_pCell {t : HTag} (h : t ≤ HTag.pCell) :
    t = HTag.pStart ∨ t = HTag.pCell := by
  revert h; revert t; decide

/-- Only the three bracketing tags are at or below the right marker's. -/
theorem htag_le_pEnd {t : HTag} (h : t ≤ HTag.pEnd) :
    t = HTag.pStart ∨ t = HTag.pCell ∨ t = HTag.pEnd := by
  revert h; revert t; decide

/-- Only the two highest bracketing tags lie between a cell's and the right
marker's. -/
theorem htag_between {t : HTag} (h₁ : HTag.pCell ≤ t) (h₂ : t ≤ HTag.pEnd) :
    t = HTag.pCell ∨ t = HTag.pEnd := by
  revert h₁ h₂; revert t; decide

omit [Language.sat.Structure A] in
/-- The head's first move: the cell of the least element follows `⊢`. -/
theorem succPos_posHStart_posHCell :
    SuccPos tagTupleLe HPosn (posHStart : HV A) (posHCell botA) := by
  refine ⟨hPosn_posHStart, hPosn_posHCell _, posHStart_le_posHCell _, ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (show ¬(HTag.pStart = HTag.pCell) by decide)
  · intro r hr h1 h2
    rcases htag_le_pCell (hTagTupleLe_tag_le h2) with h | h
    · exact Or.inl (eq_posHStart_of_posn hr h)
    · refine Or.inr ?_
      have hcell := eq_posHCell_of_posn hr h
      have hle : r.2 0 ≤ botA := posHCell_le_iff.mp (hcell ▸ h2)
      rw [hcell, le_antisymm hle (botA_le _)]

omit [Language.sat.Structure A] in
/-- The head moves from cell to cell along the instance. -/
theorem succPos_posHCell_posHCell {x x' : A} (hsucc : SuccElt x x') :
    SuccPos tagTupleLe HPosn (posHCell x : HV A) (posHCell x') := by
  refine ⟨hPosn_posHCell _, hPosn_posHCell _, posHCell_le_iff.mpr hsucc.1.le, ?_, ?_⟩
  · intro h
    exact absurd (by simpa [oneH] using congrFun (congrArg Prod.snd h) 0 : x = x')
      (ne_of_lt hsucc.1)
  · intro r hr h1 h2
    have ht : r.1 = HTag.pCell :=
      le_antisymm (hTagTupleLe_tag_le h2) (hTagTupleLe_tag_le h1)
    have hcell := eq_posHCell_of_posn hr ht
    have hx : x ≤ r.2 0 := posHCell_le_iff.mp (hcell ▸ h1)
    have hx' : r.2 0 ≤ x' := posHCell_le_iff.mp (hcell ▸ h2)
    rcases eq_or_lt_of_le hx with heq | hlt
    · exact Or.inl (by rw [hcell, ← heq])
    · exact Or.inr (by rw [hcell, le_antisymm hx' (hsucc.2 _ hlt)])

omit [Language.sat.Structure A] in
/-- The head's last move of a sweep: `⊣` follows the last cell. -/
theorem succPos_posHCell_posHEnd :
    SuccPos tagTupleLe HPosn (posHCell (topA (A := A)) : HV A) posHEnd := by
  refine ⟨hPosn_posHCell _, hPosn_posHEnd, posHCell_le_posHEnd _, ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (show ¬(HTag.pCell = HTag.pEnd) by decide)
  · intro r hr h1 h2
    rcases htag_between (hTagTupleLe_tag_le h1) (hTagTupleLe_tag_le h2) with h | h
    · refine Or.inl ?_
      have hcell := eq_posHCell_of_posn hr h
      have hx : topA ≤ r.2 0 := posHCell_le_iff.mp (hcell ▸ h1)
      rw [hcell, le_antisymm (le_topA _) hx]
    · exact Or.inr (eq_posHEnd_of_posn hr h)

end Order

end HornMachine

end DescriptiveComplexity
