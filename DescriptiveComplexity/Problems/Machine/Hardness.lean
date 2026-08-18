/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Tape
import DescriptiveComplexity.Problems.Sat

/-!
# The machine of a CNF formula

The program half of `SAT ≤ᶠᵒ[≤] NTMAccept`: the states, symbols and transitions
of the machine `M_φ` built inside an ordered SAT instance, on the tape laid out
in `DescriptiveComplexity.Problems.Machine.Tape`.

## The program

```
  guess :  ⊢ →  at each cell (x,U) write (x,T) or (x,F), moving right  → ⊣
  check c: sweep back over the cells, accumulating
             flag := flag ∨ (posIn c x ∧ b) ∨ (negIn c x ∧ ¬b)
           at the far marker: if flag, take the next clause and turn round;
                              if not, no transition exists and the run dies
  accept:  when the clause just checked was the last one
```

Two things make this small. The check is an **first-order test on the source
structure** – `DescriptiveComplexity.SatLit` – evaluated by the formula that will define
the transition relation, so no clause-width bound and no occurrence machinery
are needed and the source can be plain SAT rather than 3SAT. And the sweeps
**alternate direction** instead of rewinding, so a clause costs one pass and
there are no rewind states; the markers are what tell the machine a pass has
ended.

The machine is nondeterministic in exactly one place, the choice of `(x,T)` or
`(x,F)` in the guess phase. That is a deliberate design decision, and it
is what will make the `⇒` half of correctness a corollary of uniqueness rather
than a second invariant induction.

## Semantics first

Everything here is a plain predicate on tagged tuples, as
`DescriptiveComplexity.SatPosn` and `DescriptiveComplexity.SatInp` are: the machine is
assembled as a `DescriptiveComplexity.TMData` and reasoned about directly. Only once
its correctness is proved does the first-order transcription happen, one
realization lemma per `relFormula`. A transition table type-checks whatever it
says, so it has to be validated by a proof, not by elaboration.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

noncomputable section Machine

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The instance, read -/

/-- Being a clause of the CNF instance. -/
def SatCl (c : A) : Prop := RelMap Language.satIsClause ![c]

/-- The variable `x` occurs positively in the clause `c`. -/
def SatPos (c x : A) : Prop := RelMap Language.satPosIn ![c, x]

/-- The variable `x` occurs negatively in the clause `c`. -/
def SatNeg (c x : A) : Prop := RelMap Language.satNegIn ![c, x]

/-- **The literal test**: the cell `x`, holding the truth value `v`, satisfies
the clause `c`. This is the first-order test on the source structure that the
transition relation performs; it is the whole of the check phase. -/
def SatLit (c x : A) (v : Bool) : Prop :=
  (SatPos c x ∧ v = true) ∨ (SatNeg c x ∧ v = false)

/-- `c` is the lowest clause. -/
def SatMinCl (c : A) : Prop := SatCl c ∧ ∀ e, SatCl e → c ≤ e

/-- `c` is the highest clause. -/
def SatMaxCl (c : A) : Prop := SatCl c ∧ ∀ e, SatCl e → e ≤ c

/-- `c'` is the clause immediately above `c`. -/
def SatNextCl (c c' : A) : Prop :=
  SatCl c ∧ SatCl c' ∧ c < c' ∧ ∀ e, SatCl e → c < e → c' ≤ e

/-! ### The elements of the machine -/

/-- The least element of the instance, to which every constant of the machine
is pinned. -/
def botA : A := (Finite.exists_min (id : A → A)).choose

omit [Language.sat.Structure A] in
theorem botA_le (a : A) : botA (A := A) ≤ a := (Finite.exists_min (id : A → A)).choose_spec a

omit [Language.sat.Structure A] in
theorem isMinTup_bot : IsMinTup (fun _ => botA (A := A)) := ⟨botA_le, botA_le⟩

/-- The universe of the machine: tagged pairs. -/
abbrev SatV (A : Type) := SatTag × (Fin 2 → A)

/-- A constant of the machine: a tag on the pair of least elements. -/
def cst (t : SatTag) : SatV A := (t, fun _ => botA)

/-- A tag carrying one element, pinned in the second coordinate. -/
def one (t : SatTag) (a : A) : SatV A := (t, ![a, botA])

/-! #### Symbols -/

/-- The left-marker symbol. -/
abbrev symStart : SatV A := cst .sStart

/-- The right-marker symbol. -/
abbrev symEnd : SatV A := cst .sEnd

/-- The blank symbol. -/
abbrev symBlank : SatV A := cst .sBlank

/-- The symbol of an unassigned cell. -/
abbrev symU (x : A) : SatV A := one .sU x

/-- The symbol of a cell assigned the truth value `v`. -/
abbrev symV (v : Bool) (x : A) : SatV A := one (if v then .sT else .sF) x

/-! #### Positions -/

/-- The left-marker cell. -/
abbrev posStart : SatV A := cst .pStart

/-- The cell of the element `x`. -/
abbrev posCell (x : A) : SatV A := one .pCell x

/-- The right-marker cell. -/
abbrev posEnd : SatV A := cst .pEnd

/-! #### States -/

/-- The guessing state. -/
abbrev stGuess : SatV A := cst .qGuess

/-- Checking the clause `c`, flag `f`, sweeping in direction `d`. -/
abbrev stChk (f d : Bool) (c : A) : SatV A := one (.qChk f d) c

/-- The accepting state. -/
abbrev stAcc : SatV A := cst .qAcc

/-! ### The transition table -/

/-- Which tagged tuples are transitions. The payload is pinned exactly as far
as the transition needs it, and the clause coordinates are required to be
clauses, so that no junk element is ever a transition. -/
def SatTr (τ : SatV A) : Prop :=
  match τ.1 with
  | .tGuessStart => IsMinTup τ.2
  | .tGuessVal _ => ∀ a : A, τ.2 1 ≤ a
  | .tGuessEndAcc => IsMinTup τ.2 ∧ ∀ e : A, ¬ SatCl e
  | .tGuessEndChk => (∀ a : A, τ.2 1 ≤ a) ∧ SatMinCl (τ.2 0)
  | .tChk _ _ _ => SatCl (τ.2 0)
  | .tTurnNext _ => SatNextCl (τ.2 0) (τ.2 1)
  | .tTurnAcc _ => (∀ a : A, τ.2 1 ≤ a) ∧ SatMaxCl (τ.2 0)
  | _ => False

/-- The state a transition applies in. -/
def SatSrc (τ q : SatV A) : Prop :=
  match τ.1 with
  | .tGuessStart => q = stGuess
  | .tGuessVal _ => q = stGuess
  | .tGuessEndAcc => q = stGuess
  | .tGuessEndChk => q = stGuess
  | .tChk _ f d => q = stChk f d (τ.2 0)
  | .tTurnNext d => q = stChk true d (τ.2 0)
  | .tTurnAcc d => q = stChk true d (τ.2 0)
  | _ => False

/-- The symbol a transition reads. -/
def SatRead (τ a : SatV A) : Prop :=
  match τ.1 with
  | .tGuessStart => a = symStart
  | .tGuessVal _ => a = symU (τ.2 0)
  | .tGuessEndAcc => a = symEnd
  | .tGuessEndChk => a = symEnd
  | .tChk v _ _ => a = symV v (τ.2 1)
  | .tTurnNext d => a = if d then symEnd else symStart
  | .tTurnAcc d => a = if d then symEnd else symStart
  | _ => False

/-- The state a transition moves to. The only place the instance is consulted
is the check clause, where the new flag depends on `DescriptiveComplexity.SatLit`. -/
def SatDst (τ q : SatV A) : Prop :=
  match τ.1 with
  | .tGuessStart => q = stGuess
  | .tGuessVal _ => q = stGuess
  | .tGuessEndAcc => q = stAcc
  | .tGuessEndChk => q = stChk false false (τ.2 0)
  | .tChk v f d =>
      (q = stChk true d (τ.2 0) ∧ (f = true ∨ SatLit (τ.2 0) (τ.2 1) v)) ∨
        (q = stChk false d (τ.2 0) ∧ f = false ∧ ¬ SatLit (τ.2 0) (τ.2 1) v)
  | .tTurnNext d => q = stChk false (!d) (τ.2 1)
  | .tTurnAcc _ => q = stAcc
  | _ => False

/-- The symbol a transition writes: everything but the guess phase leaves the
tape as it found it. -/
def SatWrite (τ a : SatV A) : Prop :=
  match τ.1 with
  | .tGuessStart => a = symStart
  | .tGuessVal v => a = symV v (τ.2 0)
  | .tGuessEndAcc => a = symEnd
  | .tGuessEndChk => a = symEnd
  | .tChk v _ _ => a = symV v (τ.2 1)
  | .tTurnNext d => a = if d then symEnd else symStart
  | .tTurnAcc d => a = if d then symEnd else symStart
  | _ => False

/-- Which transitions move the head right: the guess phase always does, a check
sweep goes in its own direction, and a turn – whether it takes the next clause
or accepts – reverses. A turn must reverse even when accepting: it fires *at* a
marker, and there is no position beyond one. -/
def SatRight (τ : SatV A) : Prop :=
  match τ.1 with
  | .tGuessStart => True
  | .tGuessVal _ => True
  | .tGuessEndAcc => False
  | .tGuessEndChk => False
  | .tChk _ _ d => d = true
  | .tTurnNext d => d = false
  | .tTurnAcc d => d = false
  | _ => False

/-- Accepting states: just `DescriptiveComplexity.stAcc`. -/
def SatAcc (q : SatV A) : Prop := q.1 = SatTag.qAcc

/-- Start states: just `DescriptiveComplexity.stGuess`. -/
def SatStart (q : SatV A) : Prop := q.1 = SatTag.qGuess ∧ IsMinTup q.2

/-- **The machine of a CNF instance.** -/
def satMachine (A : Type) [Language.sat.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] : TMData (SatV A) where
  Posn := SatPosn
  Le := tagTupleLe
  Tr := SatTr
  Start := SatStart
  Acc := SatAcc
  Blank := SatBlank
  Right := SatRight
  Src := SatSrc
  Read := SatRead
  Dst := SatDst
  Write := SatWrite
  Inp := SatInp

/-! ### The table is a table

Before any run is considered: each transition has exactly one destination and
symbol written, and the two places where two tags could otherwise both apply
are exclusive. A mistake in the table shows up here first, which is why these
come before the correctness proof. (Sources and symbols read need no
functionality lemma of their own: `DescriptiveComplexity.satTr_unique` pins the whole
transition from them.) -/

section Functional

omit [Language.sat.Structure A] in
theorem one_eq_one_iff {t t' : SatTag} {a a' : A} :
    (one t a : SatV A) = one t' a' ↔ t = t' ∧ a = a' := by
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, ?_⟩
    have := congrFun (congrArg Prod.snd h) 0
    simpa [one] using this
  · rintro ⟨rfl, rfl⟩; rfl

omit [Language.sat.Structure A] in
/-- A transition writes exactly one symbol. -/
theorem satWrite_functional {τ a a' : SatV A} (h : SatWrite τ a) (h' : SatWrite τ a') :
    a = a' := by
  unfold SatWrite at h h'
  cases hτ : τ.1 <;> rw [hτ] at h h' <;> simp only at h h' <;> exact h.trans h'.symm

/-- A transition moves to exactly one state. The only case with a choice is the
check clause, whose two branches are separated by the flag and by
`DescriptiveComplexity.SatLit`. -/
theorem satDst_functional {τ q q' : SatV A} (h : SatDst τ q) (h' : SatDst τ q') : q = q' := by
  unfold SatDst at h h'
  cases hτ : τ.1 <;> rw [hτ] at h h' <;> simp only at h h'
  case tChk v f d =>
    rcases h with ⟨hq, hcase⟩ | ⟨hq, hf, hlit⟩ <;> rcases h' with ⟨hq', hcase'⟩ | ⟨hq', hf', hlit'⟩
    · exact hq.trans hq'.symm
    · rcases hcase with hc | hc
      · exact absurd (hc.symm.trans hf') (by decide)
      · exact absurd hc hlit'
    · rcases hcase' with hc | hc
      · exact absurd (hc.symm.trans hf) (by decide)
      · exact absurd hc hlit
    · exact hq.trans hq'.symm
  all_goals exact h.trans h'.symm

omit [Finite A] [Nonempty A] in
/-- **The end of the guess phase is not ambiguous**: an instance either has a
clause to check or has none. -/
theorem satTr_guessEnd_excl {τ τ' : SatV A} (h : SatTr τ) (h' : SatTr τ')
    (hτ : τ.1 = SatTag.tGuessEndAcc) (hτ' : τ'.1 = SatTag.tGuessEndChk) : False := by
  unfold SatTr at h h'
  rw [hτ] at h
  rw [hτ'] at h'
  exact h.2 _ h'.2.1

omit [Finite A] [Nonempty A] in
/-- **A turn is not ambiguous**: the clause just checked either has a successor
or is the last one. -/
theorem satTr_turn_excl {τ τ' : SatV A} {d d' : Bool} (h : SatTr τ) (h' : SatTr τ')
    (hτ : τ.1 = SatTag.tTurnNext d) (hτ' : τ'.1 = SatTag.tTurnAcc d')
    (hc : τ.2 0 = τ'.2 0) : False := by
  unfold SatTr at h h'
  rw [hτ] at h
  rw [hτ'] at h'
  exact absurd (h'.2.2 _ h.2.1) (not_le.mpr (hc ▸ h.2.2.1))

/-- The tag of the state a transition applies in, as a function of its own tag.
Junk tags are sent to themselves; they are never transitions. -/
def stateTag : SatTag → SatTag
  | .tGuessStart => .qGuess
  | .tGuessVal _ => .qGuess
  | .tGuessEndAcc => .qGuess
  | .tGuessEndChk => .qGuess
  | .tChk _ f d => .qChk f d
  | .tTurnNext d => .qChk true d
  | .tTurnAcc d => .qChk true d
  | t => t

/-- The tag of the symbol a transition reads, as a function of its own tag. -/
def readTag : SatTag → SatTag
  | .tGuessStart => .sStart
  | .tGuessVal _ => .sU
  | .tGuessEndAcc => .sEnd
  | .tGuessEndChk => .sEnd
  | .tChk v _ _ => if v then .sT else .sF
  | .tTurnNext d => if d then .sEnd else .sStart
  | .tTurnAcc d => if d then .sEnd else .sStart
  | t => t

/-- **The state pins the transition's tag.** -/
theorem satSrc_tag {τ q : SatV A} (hτ : SatTr τ) (hs : SatSrc τ q) :
    q.1 = stateTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> dsimp only [SatTr, SatSrc] at hτ hs <;>
    first
      | exact False.elim hτ
      | (rw [hs]; rfl)

/-- **The symbol read pins the transition's tag.** -/
theorem satRead_tag {τ a : SatV A} (hτ : SatTr τ) (hr : SatRead τ a) :
    a.1 = readTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> dsimp only [SatTr, SatRead] at hτ hr <;>
    first
      | exact False.elim hτ
      | (rw [hr]; rfl)
      | (rename_i d; cases d <;> (rw [hr]; rfl))

/-- Being the tag of a transition. -/
def isTrTag : SatTag → Bool
  | .tGuessStart | .tGuessVal _ | .tGuessEndAcc | .tGuessEndChk
  | .tChk _ _ _ | .tTurnNext _ | .tTurnAcc _ => true
  | _ => false

/-- The tag of a guess-phase write. -/
def isGuessVal : SatTag → Bool
  | .tGuessVal _ => true
  | _ => false

/-- The tag ending the guess phase with no clause to check. -/
def isEndAcc : SatTag → Bool
  | .tGuessEndAcc => true
  | _ => false

/-- The tag ending the guess phase with a clause to check. -/
def isEndChk : SatTag → Bool
  | .tGuessEndChk => true
  | _ => false

/-- The tag turning to the next clause. -/
def isTurnNext : SatTag → Bool
  | .tTurnNext _ => true
  | _ => false

/-- The tag accepting after the last clause. -/
def isTurnAcc : SatTag → Bool
  | .tTurnAcc _ => true
  | _ => false

/-- **The state and the symbol determine the transition's tag, up to the three
known ambiguities**: the guess itself, the end of the guess phase, and a turn.
A finite check over the tags – no case analysis by hand. -/
theorem tag_cases : ∀ t t' : SatTag, isTrTag t → isTrTag t' →
    stateTag t = stateTag t' → readTag t = readTag t' →
    t = t' ∨ (isGuessVal t ∧ isGuessVal t') ∨
      (isEndAcc t ∧ isEndChk t') ∨ (isEndChk t ∧ isEndAcc t') ∨
      (isTurnNext t ∧ isTurnAcc t') ∨ (isTurnAcc t ∧ isTurnNext t') := by
  decide

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- Two elements agree when their tag and both coordinates do. -/
theorem satV_ext {τ τ' : SatV A} (ht : τ.1 = τ'.1) (h0 : τ.2 0 = τ'.2 0) (h1 : τ.2 1 = τ'.2 1) :
    τ = τ' := by
  refine Prod.ext ht (funext fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1

omit [Finite A] [Nonempty A] in
/-- Only transitions have transition tags. -/
theorem satTr_isTrTag {τ : SatV A} (hτ : SatTr τ) : isTrTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> first | exact False.elim hτ | rfl

theorem isGuessVal_iff {t : SatTag} : isGuessVal t ↔ ∃ v, t = .tGuessVal v := by
  cases t <;> simp [isGuessVal]

theorem isEndAcc_iff {t : SatTag} : isEndAcc t ↔ t = .tGuessEndAcc := by
  cases t <;> simp [isEndAcc]

theorem isEndChk_iff {t : SatTag} : isEndChk t ↔ t = .tGuessEndChk := by
  cases t <;> simp [isEndChk]

theorem isTurnNext_iff {t : SatTag} : isTurnNext t ↔ ∃ d, t = .tTurnNext d := by
  cases t <;> simp [isTurnNext]

theorem isTurnAcc_iff {t : SatTag} : isTurnAcc t ↔ ∃ d, t = .tTurnAcc d := by
  cases t <;> simp [isTurnAcc]

/-- Equal tags force equal payloads: the state and symbol pin one coordinate,
the promises in `DescriptiveComplexity.SatTr` pin the other. -/
theorem satTr_payload {τ τ' q a : SatV A} (hτ : SatTr τ) (hτ' : SatTr τ')
    (hs : SatSrc τ q) (hs' : SatSrc τ' q) (hr : SatRead τ a) (hr' : SatRead τ' a)
    (ht : τ.1 = τ'.1) : τ = τ' := by
  have hmin : ∀ u v : A, (∀ b : A, u ≤ b) → (∀ b : A, v ≤ b) → u = v :=
    fun u v hu hv => le_antisymm (hu v) (hv u)
  obtain ⟨t, w⟩ := τ
  obtain ⟨t', w'⟩ := τ'
  cases ht
  cases t <;> dsimp only [SatTr, SatSrc, SatRead] at hτ hτ' hs hs' hr hr' <;>
    first
      | exact False.elim hτ
      | exact Prod.ext rfl (isMinTup_unique hτ hτ')
      | exact Prod.ext rfl (isMinTup_unique hτ.1 hτ'.1)
      | exact satV_ext rfl (one_eq_one_iff.mp (hr.symm.trans hr')).2 (hmin _ _ hτ hτ')
      | exact satV_ext rfl (le_antisymm (hτ.2.2 _ hτ'.2.1) (hτ'.2.2 _ hτ.2.1))
          (hmin _ _ hτ.1 hτ'.1)
      | exact satV_ext rfl (one_eq_one_iff.mp (hs.symm.trans hs')).2
          (one_eq_one_iff.mp (hr.symm.trans hr')).2
      | exact satV_ext rfl (one_eq_one_iff.mp (hs.symm.trans hs')).2 (hmin _ _ hτ.1 hτ'.1)
      | (refine satV_ext rfl (one_eq_one_iff.mp (hs.symm.trans hs')).2 ?_
         have h0 := (one_eq_one_iff.mp (hs.symm.trans hs')).2
         exact le_antisymm (hτ.2.2.2 _ hτ'.2.1 (h0 ▸ hτ'.2.2.1))
           (hτ'.2.2.2 _ hτ.2.1 (h0 ▸ hτ.2.2.1)))

omit [Language.sat.Structure A] in
/-- Reading off `DescriptiveComplexity.SatSrc` at a guess-write tag. -/
theorem satSrc_guessVal {τ q : SatV A} {v : Bool} (h : τ.1 = .tGuessVal v)
    (hs : SatSrc τ q) : q = stGuess := by
  obtain ⟨t, w⟩ := τ; cases h; exact hs

omit [Language.sat.Structure A] in
/-- Reading off `DescriptiveComplexity.SatRead` at a guess-write tag. -/
theorem satRead_guessVal {τ a : SatV A} {v : Bool} (h : τ.1 = .tGuessVal v)
    (hr : SatRead τ a) : a = symU (τ.2 0) := by
  obtain ⟨t, w⟩ := τ; cases h; exact hr

omit [Language.sat.Structure A] in
/-- Reading off `DescriptiveComplexity.SatSrc` at a turn-to-next tag. -/
theorem satSrc_turnNext {τ q : SatV A} {d : Bool} (h : τ.1 = .tTurnNext d)
    (hs : SatSrc τ q) : q = stChk true d (τ.2 0) := by
  obtain ⟨t, w⟩ := τ; cases h; exact hs

omit [Language.sat.Structure A] in
/-- Reading off `DescriptiveComplexity.SatSrc` at a turn-to-accept tag. -/
theorem satSrc_turnAcc {τ q : SatV A} {d : Bool} (h : τ.1 = .tTurnAcc d)
    (hs : SatSrc τ q) : q = stChk true d (τ.2 0) := by
  obtain ⟨t, w⟩ := τ; cases h; exact hs

/-- **At most one transition applies**, away from the one nondeterministic
choice of the guess phase: the state and the symbol read pin the tag
(`DescriptiveComplexity.tag_cases`), the tag pins the payload
(`DescriptiveComplexity.satTr_payload`), and the three ambiguities are the guess itself
and the two exclusive branch points. -/
theorem satTr_unique {τ τ' q a : SatV A} (hτ : SatTr τ) (hτ' : SatTr τ')
    (hs : SatSrc τ q) (hs' : SatSrc τ' q) (hr : SatRead τ a) (hr' : SatRead τ' a)
    (hguess : ¬ (q = stGuess ∧ ∃ x : A, a = symU x)) : τ = τ' := by
  have hst : stateTag τ.1 = stateTag τ'.1 :=
    (satSrc_tag hτ hs).symm.trans (satSrc_tag hτ' hs')
  have hrd : readTag τ.1 = readTag τ'.1 :=
    (satRead_tag hτ hr).symm.trans (satRead_tag hτ' hr')
  rcases tag_cases τ.1 τ'.1 (satTr_isTrTag hτ) (satTr_isTrTag hτ') hst hrd with
    heq | ⟨hg, -⟩ | ⟨ha, hc⟩ | ⟨hc, ha⟩ | ⟨hn, hac⟩ | ⟨hac, hn⟩
  · exact satTr_payload hτ hτ' hs hs' hr hr' heq
  · obtain ⟨v, hv⟩ := isGuessVal_iff.mp hg
    exact absurd ⟨satSrc_guessVal hv hs, τ.2 0, satRead_guessVal hv hr⟩ hguess
  · exact (satTr_guessEnd_excl hτ hτ' (isEndAcc_iff.mp ha) (isEndChk_iff.mp hc)).elim
  · exact (satTr_guessEnd_excl hτ' hτ (isEndAcc_iff.mp ha) (isEndChk_iff.mp hc)).elim
  · obtain ⟨d, hd⟩ := isTurnNext_iff.mp hn
    obtain ⟨d', hd'⟩ := isTurnAcc_iff.mp hac
    exact (satTr_turn_excl hτ hτ' hd hd'
      (one_eq_one_iff.mp ((satSrc_turnNext hd hs).symm.trans (satSrc_turnAcc hd' hs'))).2).elim
  · obtain ⟨d, hd⟩ := isTurnAcc_iff.mp hac
    obtain ⟨d', hd'⟩ := isTurnNext_iff.mp hn
    exact (satTr_turn_excl hτ' hτ hd' hd
      (one_eq_one_iff.mp ((satSrc_turnNext hd' hs').symm.trans (satSrc_turnAcc hd hs))).2).elim

end Functional

/-! ### The positions of the tape, concretely -/

omit [Language.sat.Structure A] in
/-- The left marker is a position. -/
theorem satPosn_posStart : SatPosn (posStart : SatV A) := fun a => ⟨botA_le a, botA_le a⟩

omit [Language.sat.Structure A] in
/-- The cell of an element is a position. -/
theorem satPosn_posCell (x : A) : SatPosn (posCell x : SatV A) := fun a => botA_le a

omit [Language.sat.Structure A] in
/-- The right marker is a position. -/
theorem satPosn_posEnd : SatPosn (posEnd : SatV A) := fun a => ⟨botA_le a, botA_le a⟩

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
/-- The tape order is reflexive. -/
theorem tagTupleLe_refl (p : SatV A) : tagTupleLe p p := Or.inr ⟨rfl, Or.inl rfl⟩

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
/-- A tag strictly below another puts its tuples below all of theirs. -/
theorem tagTupleLe_of_tag_lt {p q : SatV A} (h : p.1 < q.1) : tagTupleLe p q := Or.inl h

/-- Every tag other than the left marker's is above it. -/
theorem pStart_lt {t : SatTag} (h : t ≠ SatTag.pStart) : SatTag.pStart < t := by
  revert h; revert t; decide

omit [Language.sat.Structure A] in
/-- There is only one left marker. -/
theorem eq_posStart_of_posn {p : SatV A} (hp : SatPosn p) (h : p.1 = SatTag.pStart) :
    p = posStart := by
  obtain ⟨t, w⟩ := p
  cases h
  refine Prod.ext rfl (funext fun i => ?_)
  fin_cases i
  · exact le_antisymm (hp botA).1 (botA_le _)
  · exact le_antisymm (hp botA).2 (botA_le _)

omit [Language.sat.Structure A] in
/-- **The left marker is the lowest position**: the head starts there. -/
theorem minPos_posStart : MinPos tagTupleLe SatPosn (posStart : SatV A) := by
  refine ⟨satPosn_posStart, fun q hq => ?_⟩
  rcases eq_or_ne q.1 SatTag.pStart with h | h
  · rw [eq_posStart_of_posn hq h]
    exact tagTupleLe_refl _
  · exact tagTupleLe_of_tag_lt (pStart_lt h)

omit [Language.sat.Structure A] in
/-- The left marker precedes every cell. -/
theorem posStart_le_posCell (x : A) : tagTupleLe (posStart : SatV A) (posCell x) :=
  tagTupleLe_of_tag_lt (show SatTag.pStart < SatTag.pCell by decide)

omit [Language.sat.Structure A] in
/-- Every cell precedes the right marker. -/
theorem posCell_le_posEnd (x : A) : tagTupleLe (posCell x : SatV A) posEnd :=
  tagTupleLe_of_tag_lt (show SatTag.pCell < SatTag.pEnd by decide)

omit [Language.sat.Structure A] in
/-- The left marker precedes the right marker. -/
theorem posStart_le_posEnd : tagTupleLe (posStart : SatV A) posEnd :=
  tagTupleLe_of_tag_lt (show SatTag.pStart < SatTag.pEnd by decide)

omit [Language.sat.Structure A] [Finite A] [Nonempty A] in
/-- The tape order refines the tag order. -/
theorem tagTupleLe_tag_le {p q : SatV A} (h : tagTupleLe p q) : p.1 ≤ q.1 := by
  rcases h with h | ⟨h, -⟩
  · exact le_of_lt h
  · exact le_of_eq h

omit [Language.sat.Structure A] in
/-- **Cells are ordered as their elements are.** The tape order between two
cells is the source order between the elements they belong to – which is what
makes a sweep over the cells a walk along the instance. -/
theorem posCell_le_iff {x y : A} : tagTupleLe (posCell x : SatV A) (posCell y) ↔ x ≤ y := by
  constructor
  · rintro (h | ⟨-, h | ⟨j, hlt, hj⟩⟩)
    · exact absurd h (lt_irrefl _)
    · exact le_of_eq (by simpa [one] using congrFun h 0)
    · fin_cases j
      · exact le_of_lt (by simpa [one] using hj)
      · exact le_of_eq (by simpa [one] using hlt 0 (by decide))
  · intro h
    refine Or.inr ⟨rfl, ?_⟩
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨0, fun i hi => absurd hi (by omega), by simpa [one] using hlt⟩

/-- Only the two lowest tags are at or below a cell's. -/
theorem tag_le_pCell {t : SatTag} (h : t ≤ SatTag.pCell) :
    t = SatTag.pStart ∨ t = SatTag.pCell := by
  revert h; revert t; decide

omit [Language.sat.Structure A] in
/-- A cell is the cell of the element it carries. -/
theorem eq_posCell_of_posn {p : SatV A} (hp : SatPosn p) (h : p.1 = SatTag.pCell) :
    p = posCell (p.2 0) := by
  obtain ⟨t, w⟩ := p
  cases h
  refine Prod.ext rfl (funext fun i => ?_)
  fin_cases i
  · simp [one]
  · exact le_antisymm (hp botA) (botA_le _)

omit [Language.sat.Structure A] in
/-- **The head's first move.** The cell of the least element follows the left
marker immediately: the guess sweep starts by stepping over `⊢`. -/
theorem succPos_posStart_posCell :
    SuccPos tagTupleLe SatPosn (posStart : SatV A) (posCell botA) := by
  refine ⟨satPosn_posStart, satPosn_posCell _, posStart_le_posCell _, ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (show ¬(SatTag.pStart = SatTag.pCell) by decide)
  · intro r hr h1 h2
    rcases tag_le_pCell (tagTupleLe_tag_le h2) with h | h
    · exact Or.inl (eq_posStart_of_posn hr h)
    · refine Or.inr ?_
      have hcell := eq_posCell_of_posn hr h
      have hle : r.2 0 ≤ botA := posCell_le_iff.mp (hcell ▸ h2)
      rw [hcell, le_antisymm hle (botA_le _)]

/-- The greatest element of the instance: the last cell of the tape. -/
def topA : A := (Finite.exists_max (id : A → A)).choose

omit [Language.sat.Structure A] in
theorem le_topA (a : A) : a ≤ topA (A := A) := (Finite.exists_max (id : A → A)).choose_spec a

/-- Only the two highest of the bracketing tags lie between a cell's and the
right marker's. -/
theorem tag_between {t : SatTag} (h₁ : SatTag.pCell ≤ t) (h₂ : t ≤ SatTag.pEnd) :
    t = SatTag.pCell ∨ t = SatTag.pEnd := by
  revert h₁ h₂; revert t; decide

omit [Language.sat.Structure A] in
/-- There is only one right marker. -/
theorem eq_posEnd_of_posn {p : SatV A} (hp : SatPosn p) (h : p.1 = SatTag.pEnd) :
    p = posEnd := by
  obtain ⟨t, w⟩ := p
  cases h
  refine Prod.ext rfl (funext fun i => ?_)
  fin_cases i
  · exact le_antisymm (hp botA).1 (botA_le _)
  · exact le_antisymm (hp botA).2 (botA_le _)

omit [Language.sat.Structure A] in
/-- **The head's last move of a sweep.** The right marker follows the cell of
the greatest element: this is where the guess sweep stops. -/
theorem succPos_posCell_posEnd :
    SuccPos tagTupleLe SatPosn (posCell (topA (A := A)) : SatV A) posEnd := by
  refine ⟨satPosn_posCell _, satPosn_posEnd, posCell_le_posEnd _, ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (show ¬(SatTag.pCell = SatTag.pEnd) by decide)
  · intro r hr h1 h2
    rcases tag_between (tagTupleLe_tag_le h1) (tagTupleLe_tag_le h2) with h | h
    · refine Or.inl ?_
      have hcell := eq_posCell_of_posn hr h
      have hx : topA ≤ r.2 0 := posCell_le_iff.mp (hcell ▸ h1)
      rw [hcell, le_antisymm (le_topA _) hx]
    · exact Or.inr (eq_posEnd_of_posn hr h)

/-- **The machine is deterministic away from the guess.** Once the transition
is pinned (`DescriptiveComplexity.satTr_unique`), the successor configuration is too: its
state by `satDst_functional`, the cell under the head by `satWrite_functional`,
every other cell by the frame condition, and the head itself by uniqueness of
the neighbor in the direction the transition names.

This is a deliberate design decision: with only the guess phase
branching, the `⇒` half of correctness becomes a corollary of uniqueness rather
than a second invariant induction. -/
theorem step_functional_off_guess {c c₁ c₂ : Config (SatV A)}
    (hguess : ¬ (c.state = stGuess ∧ ∃ x : A, c.tape c.head = symU x))
    (h₁ : (satMachine A).Step c c₁) (h₂ : (satMachine A).Step c c₂) : c₁ = c₂ := by
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := h₁
  obtain ⟨σ, hσ, hsrc', hread', hdst', hwrite', hframe', hmove'⟩ := h₂
  have hteq : τ = σ := satTr_unique hτ hσ hsrc hsrc' hread hread' hguess
  subst hteq
  refine Config.ext (satDst_functional hdst hdst') ?_ (funext fun p => ?_)
  · rcases hmove with ⟨hrt, hsp⟩ | ⟨hrt, hsp⟩ <;>
      rcases hmove' with ⟨hrt', hsp'⟩ | ⟨hrt', hsp'⟩
    · exact TMData.succPos_right_unique isLinOrd_tagTupleLe hsp hsp'
    · exact absurd hrt hrt'
    · exact absurd hrt' hrt
    · exact succPos_left_unique isLinOrd_tagTupleLe hsp hsp'
  · rcases eq_or_ne p c.head with rfl | hne
    · exact satWrite_functional hwrite hwrite'
    · rw [hframe p hne, hframe' p hne]

/-! ### The intended run: the guess phase -/

open Classical in
/-- The tape during the guess sweep, with the head at `p`: the markers hold
their own symbols, a cell strictly below the head has been assigned its value
under `ν`, a cell at or above the head is still unassigned, and every other
element reads blank.

A tuple carrying a cell's tag but a junk second coordinate is not a position,
and the machine never visits it – but the frame condition of a step quantifies
over it all the same, so its value must not move as the head advances. Hence
the guard `∀ a, q.2 1 ≤ a`: junk cells read unassigned forever, which is also
what `DescriptiveComplexity.SatInp` says they hold initially. -/
noncomputable def guessTape (ν : A → Bool) (p q : SatV A) : SatV A :=
  match q.1 with
  | .pStart => symStart
  | .pEnd => symEnd
  | .pCell =>
      if (∀ a : A, q.2 1 ≤ a) ∧ tagTupleLe q p ∧ q ≠ p then symV (ν (q.2 0)) (q.2 0)
      else symU (q.2 0)
  | _ => symBlank

/-- The configuration during the guess sweep, with the head at `p`. -/
noncomputable def confGuess (ν : A → Bool) (p : SatV A) : Config (SatV A) where
  state := stGuess
  head := p
  tape := guessTape ν p

omit [Language.sat.Structure A] in
/-- **The guess sweep only ever changes the cell under the head.** Every other
element reads the same before and after: markers and non-cells do not depend on
the head at all, junk cells are frozen, and a real cell is below the new head
exactly when it was below the old one – by the between-condition of
`DescriptiveComplexity.SuccPos` in one direction and transitivity in the other. -/
theorem guessTape_frame (ν : A → Bool) {p q r : SatV A}
    (hsucc : SuccPos tagTupleLe SatPosn p q) (hr : r ≠ p) :
    guessTape ν q r = guessTape ν p r := by
  classical
  obtain ⟨t, w⟩ := r
  cases t <;> simp only [guessTape]
  case pCell =>
    have hiff : ((∀ a : A, w 1 ≤ a) ∧ tagTupleLe ((SatTag.pCell, w) : SatV A) q ∧
          ((SatTag.pCell, w) : SatV A) ≠ q) ↔
        ((∀ a : A, w 1 ≤ a) ∧ tagTupleLe ((SatTag.pCell, w) : SatV A) p ∧
          ((SatTag.pCell, w) : SatV A) ≠ p) := by
      constructor
      · rintro ⟨hpos, hle, hne⟩
        refine ⟨hpos, ?_, hr⟩
        by_contra hcon
        rcases isLinOrd_tagTupleLe.2.2.2 p (SatTag.pCell, w) with h | h
        · rcases hsucc.2.2.2.2 (SatTag.pCell, w) hpos h hle with h' | h'
          · exact hr h'
          · exact hne h'
        · exact hcon h
      · rintro ⟨hpos, hle, -⟩
        refine ⟨hpos, isLinOrd_tagTupleLe.2.1 _ p q hle hsucc.2.2.1, ?_⟩
        rintro rfl
        exact hsucc.2.2.2.1 (isLinOrd_tagTupleLe.2.2.1 _ _ hsucc.2.2.1 hle)
    exact if_congr hiff rfl rfl

/-- **The guess sweep starts from an initial configuration**: at the left
marker no cell is below the head, so every cell still reads unassigned – which
is exactly the input `DescriptiveComplexity.SatInp` describes. -/
theorem isInit_confGuess (ν : A → Bool) :
    (satMachine A).IsInit (confGuess ν posStart) := by
  have hne : ∀ q : SatV A, q.1 = SatTag.pCell →
      ¬ ((∀ a : A, q.2 1 ≤ a) ∧ tagTupleLe q (posStart : SatV A) ∧ q ≠ posStart) := by
    rintro q hq ⟨-, hle, -⟩
    have h := tagTupleLe_tag_le hle
    rw [hq] at h
    exact absurd h (show ¬(SatTag.pCell ≤ SatTag.pStart) by decide)
  refine ⟨⟨rfl, isMinTup_bot⟩, minPos_posStart, fun q => ?_⟩
  change TMData.InitTape (satMachine A) q (guessTape ν posStart q)
  cases hq : q.1 <;> simp only [guessTape, hq] <;>
    first
      | exact Or.inl (Or.inl ⟨hq, rfl, isMinTup_bot⟩)
      | exact Or.inl (Or.inr (Or.inr ⟨hq, rfl, isMinTup_bot⟩))
      | (rw [if_neg (hne q hq)]
         exact Or.inl (Or.inr (Or.inl ⟨hq, rfl, rfl, fun b => botA_le b⟩)))
      | (refine Or.inr ⟨fun b hb => ?_, rfl, isMinTup_bot⟩
         rcases hb with ⟨h, -⟩ | ⟨h, -, -, -⟩ | ⟨h, -⟩ <;> rw [hq] at h <;> simp at h)

/-- Only the three bracketing tags are at or below the right marker's. -/
theorem tag_le_pEnd {t : SatTag} (h : t ≤ SatTag.pEnd) :
    t = SatTag.pStart ∨ t = SatTag.pCell ∨ t = SatTag.pEnd := by
  revert h; revert t; decide

/-- **One step of the guess sweep.** At the left marker the machine steps over
it; at a cell it writes the guessed value and moves on; past the right marker
the segment bound leaves nothing to prove. -/
theorem step_guess (ν : A → Bool) {p q : SatV A}
    (hsucc : SuccPos tagTupleLe SatPosn p q) (hb : tagTupleLe q posEnd) :
    (satMachine A).Step (confGuess ν p) (confGuess ν q) := by
  classical
  have hframe : ∀ r, r ≠ p → guessTape ν q r = guessTape ν p r :=
    fun r hr => guessTape_frame ν hsucc hr
  have hpe : p.1 ≤ SatTag.pEnd :=
    tagTupleLe_tag_le (isLinOrd_tagTupleLe.2.1 p q posEnd hsucc.2.2.1 hb)
  rcases tag_le_pEnd hpe with h | h | h
  · refine ⟨cst .tGuessStart, isMinTup_bot, rfl, ?_, rfl, ?_, hframe,
      Or.inl ⟨trivial, hsucc⟩⟩
    · change guessTape ν p p = symStart
      simp only [guessTape, h]
    · change guessTape ν q p = symStart
      simp only [guessTape, h]
  · have hpos : ∀ a : A, p.2 1 ≤ a := by
      have := hsucc.1
      rw [SatPosn, h] at this
      exact this
    refine ⟨one (.tGuessVal (ν (p.2 0))) (p.2 0), fun a => botA_le a, rfl, ?_, rfl, ?_, hframe,
      Or.inl ⟨trivial, hsucc⟩⟩
    · change guessTape ν p p = symU (p.2 0)
      simp only [guessTape, h]
      exact if_neg (fun hc => hc.2.2 rfl)
    · change guessTape ν q p = symV (ν (p.2 0)) (p.2 0)
      simp only [guessTape, h]
      exact if_pos ⟨hpos, hsucc.2.2.1, hsucc.2.2.2.1⟩
  · exact absurd (isLinOrd_tagTupleLe.2.2.1 p q hsucc.2.2.1
      ((eq_posEnd_of_posn hsucc.1 h) ▸ hb)) hsucc.2.2.2.1

/-- **The whole guess sweep.** From the left marker to the right one, the
machine writes a truth value in every cell, in as many steps as there are
positions strictly between the markers – plus the two markers themselves. -/
theorem steps_guess (ν : A → Bool) :
    (satMachine A).StepsIn
      (bitRank tagTupleLe SatPosn (posEnd : SatV A) -
        bitRank tagTupleLe SatPosn (posStart : SatV A))
      (confGuess ν posStart) (confGuess ν posEnd) :=
  TMData.stepsIn_of_segment isLinOrd_tagTupleLe satPosn_posStart
    (fun _ _ hsucc _ hb => step_guess ν hsucc hb) posEnd satPosn_posEnd
    (minPos_posStart.2 posEnd satPosn_posEnd) (tagTupleLe_refl _)

/-- **The turn out of the guess phase**, when there is a clause to check: the
machine reads the right marker, takes the lowest clause with an empty flag, and
turns round to sweep leftwards. -/
theorem step_turnChk (ν : A → Bool) {c₀ : A} (hc₀ : SatMinCl c₀) :
    (satMachine A).Step (confGuess ν posEnd)
      { state := stChk false false c₀, head := posCell topA, tape := guessTape ν posEnd } := by
  refine ⟨one .tGuessEndChk c₀, ⟨fun a => botA_le a, hc₀⟩, rfl, ?_, rfl, ?_,
    fun r _ => rfl, Or.inr ⟨id, succPos_posCell_posEnd⟩⟩
  · change guessTape ν posEnd posEnd = symEnd
    rfl
  · change guessTape ν posEnd posEnd = symEnd
    rfl

/-- **The turn out of the guess phase**, when the instance has no clause at
all: the formula is vacuously satisfiable and the machine accepts. Without this
tag the run would die and the reduction would be wrong on the empty CNF. -/
theorem step_turnAcc (ν : A → Bool) (hno : ∀ e : A, ¬ SatCl e) :
    (satMachine A).Step (confGuess ν posEnd)
      { state := stAcc, head := posCell topA, tape := guessTape ν posEnd } := by
  refine ⟨cst .tGuessEndAcc, ⟨isMinTup_bot, hno⟩, rfl, ?_, rfl, ?_,
    fun r _ => rfl, Or.inr ⟨id, succPos_posCell_posEnd⟩⟩
  · change guessTape ν posEnd posEnd = symEnd
    rfl
  · change guessTape ν posEnd posEnd = symEnd
    rfl

/-! ### The intended run: a check sweep -/

/-- The tape once the guess sweep has finished: every cell assigned. It does
not change again, so the frame condition of every later step is `rfl`. -/
noncomputable def doneTape (ν : A → Bool) : SatV A → SatV A := guessTape ν posEnd

open Classical in
/-- The flag of a leftward check sweep with the head at `p`: some cell already
visited – that is, strictly above `p` – satisfies the clause `c`. -/
noncomputable def chkFlagL (ν : A → Bool) (c : A) (p : SatV A) : Bool :=
  decide (∃ y : A, tagTupleLe p (posCell y) ∧ p ≠ posCell y ∧ SatLit c y (ν y))

/-- The configuration during a leftward check sweep of the clause `c`. -/
noncomputable def confChkL (ν : A → Bool) (c : A) (p : SatV A) : Config (SatV A) where
  state := stChk (chkFlagL ν c p) false c
  head := p
  tape := doneTape ν

/-- **A check sweep starts with an empty flag**: at the highest cell nothing has
been visited yet. -/
theorem chkFlagL_top (ν : A → Bool) (c : A) :
    chkFlagL ν c (posCell (topA (A := A))) = false := by
  classical
  simp only [chkFlagL, decide_eq_false_iff_not]
  rintro ⟨y, hle, hne, -⟩
  exact hne (congrArg _ (le_antisymm (le_topA y) (posCell_le_iff.mp hle))).symm

/-- **Stepping down adds exactly one literal to the flag.** Moving the head
from `q` to the position below it brings `q`'s own cell into view and nothing
else, because `DescriptiveComplexity.SuccPos` leaves no room between them. This is the
whole content of a check sweep. -/
theorem chkFlagL_succ (ν : A → Bool) (c : A) {p q : SatV A}
    (hsucc : SuccPos tagTupleLe SatPosn p q) (hq : q.1 = SatTag.pCell) :
    chkFlagL ν c p = true ↔
      (chkFlagL ν c q = true ∨ SatLit c (q.2 0) (ν (q.2 0))) := by
  classical
  have hqc : q = posCell (q.2 0) := eq_posCell_of_posn hsucc.2.1 hq
  simp only [chkFlagL, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hle, hne, hlit⟩
    by_cases hcase : tagTupleLe q (posCell y) ∧ q ≠ posCell y
    · exact Or.inl ⟨y, hcase.1, hcase.2, hlit⟩
    · refine Or.inr ?_
      have hyq : posCell y = q := by
        by_cases hle' : tagTupleLe q (posCell y)
        · exact (not_not.mp (by simpa [hle'] using hcase : ¬ q ≠ posCell y)).symm
        · rcases hsucc.2.2.2.2 (posCell y) (satPosn_posCell y) hle
            ((isLinOrd_tagTupleLe.2.2.2 (posCell y) q).resolve_right hle') with h | h
          · exact absurd h.symm hne
          · exact h
      have : y = q.2 0 := by
        have := congrArg (fun z : SatV A => z.2 0) (hyq.trans hqc)
        simpa [one] using this
      rwa [← this]
  · rintro (⟨y, hle, hne, hlit⟩ | hlit)
    · refine ⟨y, isLinOrd_tagTupleLe.2.1 p q _ hsucc.2.2.1 hle, ?_, hlit⟩
      rintro rfl
      exact hsucc.2.2.2.1 (isLinOrd_tagTupleLe.2.2.1 _ _ hsucc.2.2.1 hle)
    · exact ⟨q.2 0, hqc ▸ hsucc.2.2.1, hqc ▸ hsucc.2.2.2.1, hlit⟩

omit [Language.sat.Structure A] in
/-- After the guess sweep every real cell holds its assigned value. -/
theorem doneTape_cell (ν : A → Bool) {q : SatV A} (hq : q.1 = SatTag.pCell)
    (hpos : ∀ a : A, q.2 1 ≤ a) : doneTape ν q = symV (ν (q.2 0)) (q.2 0) := by
  classical
  simp only [doneTape, guessTape, hq]
  refine if_pos ⟨hpos, tagTupleLe_of_tag_lt ?_, ?_⟩
  · rw [hq]
    exact show SatTag.pCell < SatTag.pEnd by decide
  · intro h
    rw [h] at hq
    exact absurd hq (show ¬(SatTag.pEnd = SatTag.pCell) by decide)

/-- **One step of a leftward check sweep.** The machine reads the cell it is
on, folds that literal into the flag, and moves one place left. Which of the
two `DescriptiveComplexity.SatDst` branches applies is exactly
`DescriptiveComplexity.chkFlagL_succ`. -/
theorem step_chkL (ν : A → Bool) {c : A} (hc : SatCl c) {p q : SatV A}
    (hsucc : SuccPos tagTupleLe SatPosn p q) (hq : q.1 = SatTag.pCell) :
    (satMachine A).Step (confChkL ν c q) (confChkL ν c p) := by
  classical
  have hpos : ∀ a : A, q.2 1 ≤ a := by
    have := hsucc.2.1
    rw [SatPosn, hq] at this
    exact this
  have hread : doneTape ν q = symV (ν (q.2 0)) (q.2 0) := doneTape_cell ν hq hpos
  refine ⟨(SatTag.tChk (ν (q.2 0)) (chkFlagL ν c q) false, ![c, q.2 0]), hc, rfl, hread, ?_,
    hread, fun r _ => rfl, Or.inr ⟨Bool.false_ne_true, hsucc⟩⟩
  by_cases hflag : chkFlagL ν c p = true
  · refine Or.inl ⟨?_, ?_⟩
    · change stChk (chkFlagL ν c p) false c = stChk true false c
      rw [hflag]
    · exact (chkFlagL_succ ν c hsucc hq).mp hflag
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · change stChk (chkFlagL ν c p) false c = stChk false false c
      rw [Bool.not_eq_true] at hflag
      rw [hflag]
    · by_contra hcon
      exact hflag ((chkFlagL_succ ν c hsucc hq).mpr (Or.inl (by simpa using hcon)))
    · intro hlit
      exact hflag ((chkFlagL_succ ν c hsucc hq).mpr (Or.inr hlit))

/-- **A whole leftward check sweep.** From the highest cell down to the left
marker, the flag accumulating the literals of `c` satisfied along the way. -/
theorem steps_chkL (ν : A → Bool) {c : A} (hc : SatCl c) :
    (satMachine A).StepsIn
      (bitRank tagTupleLe SatPosn (posCell (topA (A := A))) -
        bitRank tagTupleLe SatPosn (posStart : SatV A))
      (confChkL ν c (posCell topA)) (confChkL ν c posStart) := by
  refine TMData.stepsIn_of_segment_down isLinOrd_tagTupleLe (satPosn_posCell _)
    (fun p q hsucc _ hub => step_chkL ν hc hsucc ?_) posStart satPosn_posStart
    (tagTupleLe_refl _) (posStart_le_posCell _)
  rcases tag_le_pCell (tagTupleLe_tag_le hub) with h | h
  · refine absurd (isLinOrd_tagTupleLe.2.2.1 p q hsucc.2.2.1 ?_) hsucc.2.2.2.1
    rw [eq_posStart_of_posn hsucc.2.1 h]
    exact minPos_posStart.2 p hsucc.1
  · exact h

open Classical in
/-- The flag of a *rightward* check sweep with the head at `p`: some cell
already visited – strictly below `p` – satisfies `c`. -/
noncomputable def chkFlagR (ν : A → Bool) (c : A) (p : SatV A) : Bool :=
  decide (∃ y : A, tagTupleLe (posCell y) p ∧ posCell y ≠ p ∧ SatLit c y (ν y))

/-- The configuration during a rightward check sweep of the clause `c`. -/
noncomputable def confChkR (ν : A → Bool) (c : A) (p : SatV A) : Config (SatV A) where
  state := stChk (chkFlagR ν c p) true c
  head := p
  tape := doneTape ν

/-- **A rightward sweep also starts with an empty flag**: nothing lies below
the lowest cell. -/
theorem chkFlagR_bot (ν : A → Bool) (c : A) :
    chkFlagR ν c (posCell (botA (A := A))) = false := by
  classical
  simp only [chkFlagR, decide_eq_false_iff_not]
  rintro ⟨y, hle, hne, -⟩
  exact hne (congrArg _ (le_antisymm (posCell_le_iff.mp hle) (botA_le y)))

omit [Language.sat.Structure A] in
/-- The left marker keeps its symbol throughout. -/
theorem doneTape_start (ν : A → Bool) : doneTape ν (posStart : SatV A) = symStart := rfl

/-- **The turn at the left marker**, when another clause follows: the flag is
set, so the machine takes the next clause, empties the flag and reverses to
sweep rightwards. -/
theorem step_turnNextL (ν : A → Bool) {c c' : A} (hnext : SatNextCl c c')
    (hflag : chkFlagL ν c (posStart : SatV A) = true) :
    (satMachine A).Step (confChkL ν c posStart) (confChkR ν c' (posCell botA)) := by
  refine ⟨(SatTag.tTurnNext false, ![c, c']), hnext, ?_, doneTape_start ν, ?_,
    doneTape_start ν, fun r _ => rfl, Or.inl ⟨rfl, succPos_posStart_posCell⟩⟩
  · change stChk (chkFlagL ν c posStart) false c = stChk true false c
    rw [hflag]
  · change stChk (chkFlagR ν c' (posCell botA)) true c' = stChk false true c'
    rw [chkFlagR_bot]

/-- **Stepping up adds exactly one literal to the flag** – the mirror of
`DescriptiveComplexity.chkFlagL_succ`. -/
theorem chkFlagR_succ (ν : A → Bool) (c : A) {p q : SatV A}
    (hsucc : SuccPos tagTupleLe SatPosn p q) (hp : p.1 = SatTag.pCell) :
    chkFlagR ν c q = true ↔ (chkFlagR ν c p = true ∨ SatLit c (p.2 0) (ν (p.2 0))) := by
  classical
  have hpc : p = posCell (p.2 0) := eq_posCell_of_posn hsucc.1 hp
  simp only [chkFlagR, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hle, hne, hlit⟩
    by_cases hcase : tagTupleLe (posCell y) p ∧ posCell y ≠ p
    · exact Or.inl ⟨y, hcase.1, hcase.2, hlit⟩
    · refine Or.inr ?_
      have hyp : posCell y = p := by
        by_cases hle' : tagTupleLe (posCell y) p
        · exact not_not.mp (by simpa [hle'] using hcase)
        · rcases hsucc.2.2.2.2 (posCell y) (satPosn_posCell y)
            ((isLinOrd_tagTupleLe.2.2.2 p (posCell y)).resolve_right hle') hle with h | h
          · exact h
          · exact absurd h hne
      have hy : y = p.2 0 := by
        have := congrArg (fun z : SatV A => z.2 0) (hyp.trans hpc)
        simpa [one] using this
      rwa [← hy]
  · rintro (⟨y, hle, hne, hlit⟩ | hlit)
    · refine ⟨y, isLinOrd_tagTupleLe.2.1 _ p q hle hsucc.2.2.1, ?_, hlit⟩
      rintro rfl
      exact hne (isLinOrd_tagTupleLe.2.2.1 _ _ hle hsucc.2.2.1)
    · exact ⟨p.2 0, hpc ▸ hsucc.2.2.1, hpc ▸ hsucc.2.2.2.1, hlit⟩

/-- **One step of a rightward check sweep** – the mirror of
`DescriptiveComplexity.step_chkL`. -/
theorem step_chkR (ν : A → Bool) {c : A} (hc : SatCl c) {p q : SatV A}
    (hsucc : SuccPos tagTupleLe SatPosn p q) (hp : p.1 = SatTag.pCell) :
    (satMachine A).Step (confChkR ν c p) (confChkR ν c q) := by
  classical
  have hpos : ∀ a : A, p.2 1 ≤ a := by
    have := hsucc.1
    rw [SatPosn, hp] at this
    exact this
  have hread : doneTape ν p = symV (ν (p.2 0)) (p.2 0) := doneTape_cell ν hp hpos
  refine ⟨(SatTag.tChk (ν (p.2 0)) (chkFlagR ν c p) true, ![c, p.2 0]), hc, rfl, hread, ?_,
    hread, fun r _ => rfl, Or.inl ⟨rfl, hsucc⟩⟩
  by_cases hflag : chkFlagR ν c q = true
  · refine Or.inl ⟨?_, ?_⟩
    · change stChk (chkFlagR ν c q) true c = stChk true true c
      rw [hflag]
    · exact (chkFlagR_succ ν c hsucc hp).mp hflag
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · change stChk (chkFlagR ν c q) true c = stChk false true c
      rw [Bool.not_eq_true] at hflag
      rw [hflag]
    · by_contra hcon
      exact hflag ((chkFlagR_succ ν c hsucc hp).mpr (Or.inl (by simpa using hcon)))
    · intro hlit
      exact hflag ((chkFlagR_succ ν c hsucc hp).mpr (Or.inr hlit))

omit [Language.sat.Structure A] in
/-- The right marker keeps its symbol throughout. -/
theorem doneTape_end (ν : A → Bool) : doneTape ν (posEnd : SatV A) = symEnd := rfl

/-- **A whole rightward check sweep** – the mirror of
`DescriptiveComplexity.steps_chkL`. -/
theorem steps_chkR (ν : A → Bool) {c : A} (hc : SatCl c) :
    (satMachine A).StepsIn
      (bitRank tagTupleLe SatPosn (posEnd : SatV A) -
        bitRank tagTupleLe SatPosn (posCell (botA (A := A))))
      (confChkR ν c (posCell botA)) (confChkR ν c posEnd) := by
  refine TMData.stepsIn_of_segment isLinOrd_tagTupleLe (satPosn_posCell _)
    (fun p q hsucc hlb hub => step_chkR ν hc hsucc ?_) posEnd satPosn_posEnd
    (posCell_le_posEnd _) (tagTupleLe_refl _)
  rcases tag_between (tagTupleLe_tag_le hlb)
      (tagTupleLe_tag_le (isLinOrd_tagTupleLe.2.1 p q posEnd hsucc.2.2.1 hub)) with h | h
  · exact h
  · exact absurd (isLinOrd_tagTupleLe.2.2.1 p q hsucc.2.2.1
      ((eq_posEnd_of_posn hsucc.1 h) ▸ hub)) hsucc.2.2.2.1

/-- **The turn at the right marker**, when another clause follows – the mirror
of `DescriptiveComplexity.step_turnNextL`. -/
theorem step_turnNextR (ν : A → Bool) {c c' : A} (hnext : SatNextCl c c')
    (hflag : chkFlagR ν c (posEnd : SatV A) = true) :
    (satMachine A).Step (confChkR ν c posEnd) (confChkL ν c' (posCell topA)) := by
  refine ⟨(SatTag.tTurnNext true, ![c, c']), hnext, ?_, doneTape_end ν, ?_,
    doneTape_end ν, fun r _ => rfl, Or.inr ⟨fun h => Bool.noConfusion h, succPos_posCell_posEnd⟩⟩
  · change stChk (chkFlagR ν c posEnd) true c = stChk true true c
    rw [hflag]
  · change stChk (chkFlagL ν c' (posCell topA)) false c' = stChk false false c'
    rw [chkFlagL_top]

/-- **Accepting at the left marker**: the flag is set and the clause just
checked was the last one. -/
theorem step_turnAccL (ν : A → Bool) {c : A} (hmax : SatMaxCl c)
    (hflag : chkFlagL ν c (posStart : SatV A) = true) :
    (satMachine A).Step (confChkL ν c posStart)
      { state := stAcc, head := posCell botA, tape := doneTape ν } := by
  refine ⟨one (.tTurnAcc false) c, ⟨fun a => botA_le a, hmax⟩, ?_, doneTape_start ν, rfl,
    doneTape_start ν, fun r _ => rfl, Or.inl ⟨rfl, succPos_posStart_posCell⟩⟩
  change stChk (chkFlagL ν c posStart) false c = stChk true false c
  rw [hflag]

/-- **Accepting at the right marker** – the mirror. -/
theorem step_turnAccR (ν : A → Bool) {c : A} (hmax : SatMaxCl c)
    (hflag : chkFlagR ν c (posEnd : SatV A) = true) :
    (satMachine A).Step (confChkR ν c posEnd)
      { state := stAcc, head := posCell topA, tape := doneTape ν } := by
  refine ⟨one (.tTurnAcc true) c, ⟨fun a => botA_le a, hmax⟩, ?_, doneTape_end ν, rfl,
    doneTape_end ν, fun r _ => rfl,
    Or.inr ⟨fun h => Bool.noConfusion h, succPos_posCell_posEnd⟩⟩
  change stChk (chkFlagR ν c posEnd) true c = stChk true true c
  rw [hflag]

/-- **A completed leftward sweep has seen every cell**: its flag says exactly
that some element satisfies the clause. -/
theorem chkFlagL_posStart (ν : A → Bool) (c : A) :
    chkFlagL ν c (posStart : SatV A) = true ↔ ∃ y : A, SatLit c y (ν y) := by
  classical
  simp only [chkFlagL, decide_eq_true_eq]
  constructor
  · rintro ⟨y, -, -, hlit⟩
    exact ⟨y, hlit⟩
  · rintro ⟨y, hlit⟩
    refine ⟨y, posStart_le_posCell y, ?_, hlit⟩
    intro h
    exact absurd (congrArg Prod.fst h) (show ¬(SatTag.pStart = SatTag.pCell) by decide)

/-- **A completed rightward sweep has seen every cell** – the same statement,
which is why the alternating directions never have to be reconciled inside the
induction over clauses. -/
theorem chkFlagR_posEnd (ν : A → Bool) (c : A) :
    chkFlagR ν c (posEnd : SatV A) = true ↔ ∃ y : A, SatLit c y (ν y) := by
  classical
  simp only [chkFlagR, decide_eq_true_eq]
  constructor
  · rintro ⟨y, -, -, hlit⟩
    exact ⟨y, hlit⟩
  · rintro ⟨y, hlit⟩
    refine ⟨y, posCell_le_posEnd y, ?_, hlit⟩
    intro h
    exact absurd (congrArg Prod.fst h) (show ¬(SatTag.pCell = SatTag.pEnd) by decide)

/-! ### One clause, checked end to end

Each of these is a sweep followed by its turn. They are the step and the base
case of the induction over clauses; the induction itself only has to choose
between them. Each carries its step count, bounded by the rank of the right
marker: that is the honest per-clause cost, roughly the size of the instance,
and what lets the whole run fit the budget of
`DescriptiveComplexity.TMData.Accepts`. -/

omit [Language.sat.Structure A] in
/-- The left marker has rank `0`: it is the lowest position. -/
theorem bitRank_posStart : bitRank tagTupleLe SatPosn (posStart : SatV A) = 0 :=
  bitRank_eq_zero_of_minPos isLinOrd_tagTupleLe minPos_posStart

omit [Language.sat.Structure A] in
/-- The right marker sits one step above the last cell. -/
theorem bitRank_posEnd_eq :
    bitRank tagTupleLe SatPosn (posEnd : SatV A) =
      bitRank tagTupleLe SatPosn (posCell (topA (A := A))) + 1 :=
  bitRank_succPos isLinOrd_tagTupleLe succPos_posCell_posEnd

omit [Language.sat.Structure A] in
/-- The first cell has rank `1`: it follows the left marker. -/
theorem bitRank_posCell_botA :
    bitRank tagTupleLe SatPosn (posCell (botA (A := A)) : SatV A) = 1 := by
  rw [bitRank_succPos isLinOrd_tagTupleLe succPos_posStart_posCell, bitRank_posStart]

/-- Checking `c` leftwards and moving on to the next clause. -/
theorem steps_clauseL (ν : A → Bool) {c c' : A} (hc : SatCl c) (hnext : SatNextCl c c')
    (hsat : ∃ y : A, SatLit c y (ν y)) :
    ∃ k ≤ bitRank tagTupleLe SatPosn (posEnd : SatV A),
      (satMachine A).StepsIn k (confChkL ν c (posCell topA)) (confChkR ν c' (posCell botA)) := by
  refine ⟨_, ?_,
    (steps_chkL ν hc).trans_step (step_turnNextL ν hnext ((chkFlagL_posStart ν c).mpr hsat))⟩
  have h1 := bitRank_posStart (A := A)
  have h2 := bitRank_posEnd_eq (A := A)
  omega

/-- Checking `c` rightwards and moving on to the next clause. -/
theorem steps_clauseR (ν : A → Bool) {c c' : A} (hc : SatCl c) (hnext : SatNextCl c c')
    (hsat : ∃ y : A, SatLit c y (ν y)) :
    ∃ k ≤ bitRank tagTupleLe SatPosn (posEnd : SatV A),
      (satMachine A).StepsIn k (confChkR ν c (posCell botA)) (confChkL ν c' (posCell topA)) := by
  refine ⟨_, ?_,
    (steps_chkR ν hc).trans_step (step_turnNextR ν hnext ((chkFlagR_posEnd ν c).mpr hsat))⟩
  have h1 := bitRank_posCell_botA (A := A)
  have h2 := bitRank_posEnd_eq (A := A)
  omega

/-- Checking the last clause leftwards, and accepting. -/
theorem steps_clauseAccL (ν : A → Bool) {c : A} (hc : SatCl c) (hmax : SatMaxCl c)
    (hsat : ∃ y : A, SatLit c y (ν y)) :
    ∃ k ≤ bitRank tagTupleLe SatPosn (posEnd : SatV A), ∃ cfin : Config (SatV A),
      (satMachine A).StepsIn k (confChkL ν c (posCell topA)) cfin ∧ SatAcc cfin.state := by
  refine ⟨_, ?_, _, (steps_chkL ν hc).trans_step
    (step_turnAccL ν hmax ((chkFlagL_posStart ν c).mpr hsat)), rfl⟩
  have h1 := bitRank_posStart (A := A)
  have h2 := bitRank_posEnd_eq (A := A)
  omega

/-- Checking the last clause rightwards, and accepting. -/
theorem steps_clauseAccR (ν : A → Bool) {c : A} (hc : SatCl c) (hmax : SatMaxCl c)
    (hsat : ∃ y : A, SatLit c y (ν y)) :
    ∃ k ≤ bitRank tagTupleLe SatPosn (posEnd : SatV A), ∃ cfin : Config (SatV A),
      (satMachine A).StepsIn k (confChkR ν c (posCell botA)) cfin ∧ SatAcc cfin.state := by
  refine ⟨_, ?_, _, (steps_chkR ν hc).trans_step
    (step_turnAccR ν hmax ((chkFlagR_posEnd ν c).mpr hsat)), rfl⟩
  have h1 := bitRank_posCell_botA (A := A)
  have h2 := bitRank_posEnd_eq (A := A)
  omega

omit [Language.sat.Structure A] in
/-- **A sweep is short.** Only the left marker and the cells lie below the
right marker, so a sweep of the tape takes about as many steps as the instance
has elements – not as many as the tape has positions, which is what makes the
run fit the budget. Proved by injecting into `Option A` rather than by counting.
-/
theorem bitRank_posEnd_le :
    bitRank tagTupleLe SatPosn (posEnd : SatV A) ≤ Nat.card A + 1 := by
  classical
  have hcell : ∀ r : SatV A, SatPosn r → tagTupleLe r posEnd → r ≠ posEnd →
      r.1 ≠ SatTag.pStart → r.1 = SatTag.pCell := by
    intro r hr hle hne hns
    rcases tag_le_pEnd (tagTupleLe_tag_le hle) with h | h | h
    · exact absurd h hns
    · exact h
    · exact absurd (eq_posEnd_of_posn hr h) hne
  refine le_trans (Set.ncard_le_ncard_of_injOn
    (fun r : SatV A => if r.1 = SatTag.pStart then none else some (r.2 0))
    (fun _ _ => Set.mem_univ _) ?_ (Set.toFinite _)) ?_
  · rintro r ⟨hr, hle, hne⟩ r' ⟨hr', hle', hne'⟩ heq
    by_cases hs : r.1 = SatTag.pStart <;> by_cases hs' : r'.1 = SatTag.pStart
    · rw [eq_posStart_of_posn hr hs, eq_posStart_of_posn hr' hs']
    · simp [hs, hs'] at heq
    · simp [hs, hs'] at heq
    · have h0 : r.2 0 = r'.2 0 := by simpa [hs, hs'] using heq
      rw [eq_posCell_of_posn hr (hcell r hr hle hne hs),
        eq_posCell_of_posn hr' (hcell r' hr' hle' hne' hs'), h0]
  · rw [Set.ncard_univ]
    have := Fintype.ofFinite A
    simp [Nat.card_eq_fintype_card]

omit [Nonempty A] in
/-- **Every clause but the last has a next one.** The clause the machine turns
to is the least one above the current one, which is what
`DescriptiveComplexity.SatNextCl` asserts. -/
theorem exists_satNextCl {c : A} (hc : SatCl c) (hnmax : ¬ SatMaxCl c) :
    ∃ c', SatNextCl c c' := by
  have hne : ∃ e : A, SatCl e ∧ c < e := by
    by_contra hcon
    push Not at hcon
    exact hnmax ⟨hc, hcon⟩
  obtain ⟨c', ⟨hc', hlt⟩, hmin⟩ :=
    exists_minPos (Le := (· ≤ ·)) (Posn := fun e : A => SatCl e ∧ c < e)
      ⟨le_refl, fun a b c => le_trans, fun a b => le_antisymm, le_total⟩ hne
  exact ⟨c', hc, hc', hlt, fun e he hce => hmin e ⟨he, hce⟩⟩

omit [Nonempty A] in
/-- Passing to the next clause removes exactly one clause from the ones still
to be checked. -/
theorem ncard_clauses_next {c c' : A} (hnext : SatNextCl c c') :
    {e : A | SatCl e ∧ c ≤ e}.ncard = {e : A | SatCl e ∧ c' ≤ e}.ncard + 1 := by
  obtain ⟨hc, hc', hlt, hmin⟩ := hnext
  have hset : {e : A | SatCl e ∧ c ≤ e} = insert c {e : A | SatCl e ∧ c' ≤ e} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨he, hce⟩
      rcases eq_or_lt_of_le hce with rfl | hlt'
      · exact Or.inl rfl
      · exact Or.inr ⟨he, hmin e he hlt'⟩
    · rintro (rfl | ⟨he, hce⟩)
      · exact ⟨hc, le_refl _⟩
      · exact ⟨he, le_trans hlt.le hce⟩
  rw [hset,
    Set.ncard_insert_of_notMem (fun hmem => absurd hmem.2 (not_le.mpr hlt)) (Set.toFinite _)]

/-- **The machine checks every remaining clause and accepts**, in at most one
sweep's worth of steps per clause. Induction along the clauses from `c`
upwards: if `c` is the last one the machine accepts at the marker it reaches,
and otherwise it turns to the next clause, reversing direction – which is why
the statement carries both orientations at once. -/
theorem accepts_from_chk (ν : A → Bool) (hsat : ∀ e : A, SatCl e → ∃ y : A, SatLit e y (ν y)) :
    ∀ c : A, SatCl c →
      (∃ (n : ℕ) (cfin : Config (SatV A)),
          n ≤ {e : A | SatCl e ∧ c ≤ e}.ncard * bitRank tagTupleLe SatPosn (posEnd : SatV A) ∧
          (satMachine A).StepsIn n (confChkL ν c (posCell topA)) cfin ∧ SatAcc cfin.state) ∧
        ∃ (n : ℕ) (cfin : Config (SatV A)),
          n ≤ {e : A | SatCl e ∧ c ≤ e}.ncard * bitRank tagTupleLe SatPosn (posEnd : SatV A) ∧
          (satMachine A).StepsIn n (confChkR ν c (posCell botA)) cfin ∧ SatAcc cfin.state := by
  intro c
  induction c using WellFoundedGT.induction with
  | ind c IH =>
    intro hc
    have hpos : 0 < {e : A | SatCl e ∧ c ≤ e}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨c, hc, le_refl c⟩
    by_cases hmax : SatMaxCl c
    · obtain ⟨kL, hkL, cfL, hL, haL⟩ := steps_clauseAccL ν hc hmax (hsat c hc)
      obtain ⟨kR, hkR, cfR, hR, haR⟩ := steps_clauseAccR ν hc hmax (hsat c hc)
      exact ⟨⟨kL, cfL, hkL.trans (Nat.le_mul_of_pos_left _ hpos), hL, haL⟩,
        ⟨kR, cfR, hkR.trans (Nat.le_mul_of_pos_left _ hpos), hR, haR⟩⟩
    · obtain ⟨c', hnext⟩ := exists_satNextCl hc hmax
      obtain ⟨⟨nL, cfL, hnL, hL, haL⟩, ⟨nR, cfR, hnR, hR, haR⟩⟩ := IH c' hnext.2.2.1 hnext.2.1
      obtain ⟨j, hj, hstepL⟩ := steps_clauseL ν hc hnext (hsat c hc)
      obtain ⟨j', hj', hstepR⟩ := steps_clauseR ν hc hnext (hsat c hc)
      have hcount : ∀ {a b : ℕ}, a ≤ bitRank tagTupleLe SatPosn (posEnd : SatV A) →
          b ≤ {e : A | SatCl e ∧ c' ≤ e}.ncard * bitRank tagTupleLe SatPosn (posEnd : SatV A) →
          a + b ≤
            {e : A | SatCl e ∧ c ≤ e}.ncard * bitRank tagTupleLe SatPosn (posEnd : SatV A) := by
        intro a b ha hb
        rw [ncard_clauses_next hnext, Nat.succ_mul]
        exact (Nat.add_le_add ha hb).trans (le_of_eq (Nat.add_comm _ _))
      exact ⟨⟨j + nR, cfR, hcount hj hnR, hstepL.trans hR, haR⟩,
        ⟨j' + nL, cfL, hcount hj' hnL, hstepR.trans hL, haL⟩⟩

/-- **The machine is well formed**, which is all of
`DescriptiveComplexity.TMData.WellFormed` – the order is linear, there is a position,
the input is functional and the blank is unique. Every conjunct was proved on
the tape layer, before any transition existed. -/
theorem satMachine_wellFormed : (satMachine A).WellFormed :=
  ⟨isLinOrd_tagTupleLe, exists_satPosn, fun _ _ _ ha hb => satInp_functional ha hb,
    exists_satBlank, fun _ _ ha hb => satBlank_unique ha hb⟩

/-! ### Correctness, the chaining half -/

/-- **A satisfying assignment makes the machine accept, within the budget.**
The run is the guess sweep, the turn into the lowest clause, and one sweep per
clause; its length is at most `(m + 1) · (n + 2)` steps for `n` elements and
`m` clauses, which `DescriptiveComplexity.sat_budget` puts strictly below the number
of filler positions alone. -/
theorem satMachine_accepts_of_sat (ν : A → Bool)
    (hsat : ∀ e : A, SatCl e → ∃ y : A, SatLit e y (ν y)) :
    (satMachine A).Accepts := by
  have hguess : (satMachine A).StepsIn (bitRank tagTupleLe SatPosn (posEnd : SatV A))
      (confGuess ν posStart) (confGuess ν posEnd) := by
    have h := steps_guess ν
    rwa [bitRank_posStart, Nat.sub_zero] at h
  have hRle : bitRank tagTupleLe SatPosn (posEnd : SatV A) ≤ Nat.card A + 1 :=
    bitRank_posEnd_le
  have hA : 1 ≤ Nat.card A := Nat.card_pos
  have hbudget := card_le_card_posn A
  by_cases hcl : ∃ e : A, SatCl e
  · obtain ⟨c₀, hc₀, hmin⟩ := exists_minPos (Le := (· ≤ · : A → A → Prop))
      (Posn := fun e : A => SatCl e)
      ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩ hcl
    have hmincl : SatMinCl c₀ := ⟨hc₀, hmin⟩
    obtain ⟨⟨n, cfin, hn, hrun, hacc⟩, -⟩ := accepts_from_chk ν hsat c₀ hc₀
    have hturn : (satMachine A).Step (confGuess ν posEnd) (confChkL ν c₀ (posCell topA)) := by
      have heq : confChkL ν c₀ (posCell (topA (A := A))) =
          { state := stChk false false c₀, head := posCell topA,
            tape := guessTape ν posEnd } := by
        refine Config.ext ?_ rfl rfl
        change stChk (chkFlagL ν c₀ (posCell topA)) false c₀ = stChk false false c₀
        rw [chkFlagL_top]
      rw [heq]
      exact step_turnChk ν hmincl
    have hchain := (hguess.trans_step hturn).trans hrun
    refine ⟨confGuess ν posStart, cfin,
      bitRank tagTupleLe SatPosn (posEnd : SatV A) + 1 + n, isInit_confGuess ν, ?_, hchain, hacc⟩
    have hm : {e : A | SatCl e ∧ c₀ ≤ e}.ncard ≤ Nat.card A := by
      have h := Set.ncard_le_ncard (Set.subset_univ {e : A | SatCl e ∧ c₀ ≤ e})
        (Set.toFinite _)
      rwa [Set.ncard_univ] at h
    have hs := sat_budget hA hm
    calc bitRank tagTupleLe SatPosn (posEnd : SatV A) + 1 + n
        ≤ ({e : A | SatCl e ∧ c₀ ≤ e}.ncard + 1) * (Nat.card A + 2) := by
          have h2 : {e : A | SatCl e ∧ c₀ ≤ e}.ncard *
                bitRank tagTupleLe SatPosn (posEnd : SatV A) ≤
              {e : A | SatCl e ∧ c₀ ≤ e}.ncard * (Nat.card A + 1) :=
            Nat.mul_le_mul_left _ hRle
          have h3 : ({e : A | SatCl e ∧ c₀ ≤ e}.ncard + 1) * (Nat.card A + 2) =
              {e : A | SatCl e ∧ c₀ ≤ e}.ncard * (Nat.card A + 1) +
                ({e : A | SatCl e ∧ c₀ ≤ e}.ncard + Nat.card A + 2) := by ring
          have h4 := hn.trans h2
          linarith
      _ < 8 * Nat.card A * Nat.card A := hs
      _ ≤ _ := hbudget
  · have hno : ∀ e : A, ¬ SatCl e := fun e he => hcl ⟨e, he⟩
    have hchain := hguess.trans_step (step_turnAcc ν hno)
    refine ⟨confGuess ν posStart, _, bitRank tagTupleLe SatPosn (posEnd : SatV A) + 1,
      isInit_confGuess ν, ?_, hchain, rfl⟩
    have hs := sat_budget (m := 0) hA (Nat.zero_le _)
    calc bitRank tagTupleLe SatPosn (posEnd : SatV A) + 1 ≤ Nat.card A + 2 := by omega
      _ = (0 + 1) * (Nat.card A + 2) := by ring
      _ < 8 * Nat.card A * Nat.card A := hs
      _ ≤ _ := hbudget

/-! ### Correctness, from an accepting run to an assignment

By design, the machine branches only at the guess, so
an accepting run *is* the intended run of the assignment it wrote, and the flag
conditions along it force every clause to be satisfied. The analysis is one
induction on the length of the run, with one case per tag of the head position.
At each non-guess configuration the transition that fired is identified through
its tag – a `decide` over the finite tag type – and the actual step is equated
with the intended one by `DescriptiveComplexity.step_functional_off_guess`; at a guess
configuration the transition itself says which value was written. -/

section Reverse

/-- In the guessing state over an unassigned cell, only a guess write can
fire. -/
theorem trTag_guess_sU : ∀ t : SatTag, isTrTag t → stateTag t = SatTag.qGuess →
    readTag t = SatTag.sU → ∃ v, t = SatTag.tGuessVal v := by decide

/-- In the guessing state over the right marker, only the two turns out of the
guess phase can fire. -/
theorem trTag_guess_sEnd : ∀ t : SatTag, isTrTag t → stateTag t = SatTag.qGuess →
    readTag t = SatTag.sEnd → t = SatTag.tGuessEndAcc ∨ t = SatTag.tGuessEndChk := by decide

/-- In a check state over the left marker, only a leftward turn can fire, and
only with the flag set. -/
theorem trTag_chk_sStart : ∀ (t : SatTag) (f d : Bool), isTrTag t →
    stateTag t = SatTag.qChk f d → readTag t = SatTag.sStart →
    f = true ∧ d = false ∧ (t = SatTag.tTurnNext false ∨ t = SatTag.tTurnAcc false) := by decide

/-- In a check state over the right marker, only a rightward turn can fire, and
only with the flag set. -/
theorem trTag_chk_sEnd : ∀ (t : SatTag) (f d : Bool), isTrTag t →
    stateTag t = SatTag.qChk f d → readTag t = SatTag.sEnd →
    f = true ∧ d = true ∧ (t = SatTag.tTurnNext true ∨ t = SatTag.tTurnAcc true) := by decide

/-- No transition reads the blank symbol: the head never leaves the bracketed
tape, so a run that somehow stood on a filler could not move. -/
theorem trTag_read_ne_sBlank : ∀ t : SatTag, isTrTag t → readTag t ≠ SatTag.sBlank := by decide

omit [Language.sat.Structure A] in
/-- Changing the assignment anywhere but strictly below the head leaves the
guess tape unchanged: only the cells already passed read it. -/
theorem guessTape_congr {ν ν' : A → Bool} {p : SatV A}
    (h : ∀ y : A, tagTupleLe (posCell y) p → posCell y ≠ p → ν y = ν' y) (r : SatV A) :
    guessTape ν p r = guessTape ν' p r := by
  classical
  obtain ⟨t, w⟩ := r
  cases t <;> simp only [guessTape]
  case pCell =>
    by_cases hcond : (∀ a : A, w 1 ≤ a) ∧ tagTupleLe ((SatTag.pCell, w) : SatV A) p ∧
        ((SatTag.pCell, w) : SatV A) ≠ p
    · rw [if_pos hcond, if_pos hcond]
      have hcw : ((SatTag.pCell, w) : SatV A) = posCell (w 0) := by
        refine satV_ext rfl ?_ ?_
        · simp [one]
        · exact le_antisymm (hcond.1 botA) (botA_le _)
      change symV (ν (w 0)) (w 0) = symV (ν' (w 0)) (w 0)
      rw [h (w 0) (hcw ▸ hcond.2.1) (hcw ▸ hcond.2.2)]
    · rw [if_neg hcond, if_neg hcond]

/-- **The initial configuration is unique**: the start state and the lowest
position are pinned, and the initial tape is functional, so any initial
configuration starts a guess run – of every assignment at once, no cell of the
guess tape at the left marker reading the assignment at all. -/
theorem isInit_eq_confGuess {c : Config (SatV A)} (h : (satMachine A).IsInit c) (ν : A → Bool) :
    c = confGuess ν posStart := by
  obtain ⟨hstart, hmin, htape⟩ := h
  refine Config.ext ?_ ?_ (funext fun p => ?_)
  · exact satV_ext hstart.1 (le_antisymm (hstart.2.1 botA) (botA_le _))
      (le_antisymm (hstart.2.2 botA) (botA_le _))
  · exact isLinOrd_tagTupleLe.2.2.1 c.head posStart
      (hmin.2 posStart satPosn_posStart) (minPos_posStart.2 c.head hmin.1)
  · have h1 := htape p
    have h2 : (satMachine A).InitTape p (guessTape ν posStart p) := (isInit_confGuess ν).2.2 p
    rcases h1 with ha | ⟨hna, ha⟩ <;> rcases h2 with hb | ⟨hnb, hb⟩
    · exact satInp_functional ha hb
    · exact absurd ha (hnb _)
    · exact absurd hb (hna _)
    · exact satBlank_unique ha hb

/-- **The check-phase analysis**, both directions at once: an accepting run
from a check configuration forces every clause from the current one upwards to
be satisfied. The only live positions are the cells – where the step is pinned
by determinism and the sweep continues – and the marker the sweep is headed to,
where the transition that fired says the flag was set, hence the clause
satisfied, and either names the next clause or certifies this one was last. -/
theorem sat_of_chk (k : ℕ) :
    (∀ (ν : A → Bool) (c : A) (p : SatV A) (cfin : Config (SatV A)), SatCl c → SatPosn p →
      (satMachine A).StepsIn k (confChkL ν c p) cfin → SatAcc cfin.state →
      ∀ e : A, SatCl e → c ≤ e → ∃ y : A, SatLit e y (ν y)) ∧
    (∀ (ν : A → Bool) (c : A) (p : SatV A) (cfin : Config (SatV A)), SatCl c → SatPosn p →
      (satMachine A).StepsIn k (confChkR ν c p) cfin → SatAcc cfin.state →
      ∀ e : A, SatCl e → c ≤ e → ∃ y : A, SatLit e y (ν y)) := by
  induction k with
  | zero =>
    constructor <;>
      · intro ν c p cfin hc hp hk hacc
        have heq : _ = cfin := hk
        rw [← heq] at hacc
        exact SatTag.noConfusion hacc
  | succ k ih =>
    obtain ⟨ihL, ihR⟩ := ih
    constructor
    · rintro ν c p cfin hc hp ⟨c₁, hstep, hrest⟩ hacc
      cases htag : p.1
      case pStart =>
        rw [show p = posStart from eq_posStart_of_posn hp htag] at hstep
        have hstep' := hstep
        obtain ⟨τ, hτ, hsrc, hread, -, -, -, -⟩ := hstep'
        obtain ⟨hflag, -, hcase⟩ := trTag_chk_sStart τ.1 (chkFlagL ν c posStart) false
          (satTr_isTrTag hτ) (satSrc_tag hτ hsrc).symm (satRead_tag hτ hread).symm
        have hcsat : ∃ y : A, SatLit c y (ν y) := (chkFlagL_posStart ν c).mp hflag
        rcases hcase with hτ₁ | hτ₁
        · have hc0 : c = τ.2 0 := (one_eq_one_iff.mp (satSrc_turnNext hτ₁ hsrc)).2
          have hnext' : SatNextCl (τ.2 0) (τ.2 1) := by
            have h : SatTr τ := hτ
            unfold SatTr at h
            rw [hτ₁] at h
            exact h
          rw [← hc0] at hnext'
          have hc₁ : c₁ = confChkR ν (τ.2 1) (posCell botA) :=
            step_functional_off_guess
              (fun hcon => SatTag.noConfusion (congrArg Prod.fst hcon.1)) hstep
              (step_turnNextL ν hnext' hflag)
          rw [hc₁] at hrest
          intro e he hce
          rcases eq_or_lt_of_le hce with rfl | hlt
          · exact hcsat
          · exact ihR ν (τ.2 1) (posCell botA) cfin hnext'.2.1 (satPosn_posCell _) hrest hacc
              e he (hnext'.2.2.2 e he hlt)
        · have hc0 : c = τ.2 0 := (one_eq_one_iff.mp (satSrc_turnAcc hτ₁ hsrc)).2
          have hmax' : SatMaxCl (τ.2 0) := by
            have h : SatTr τ := hτ
            unfold SatTr at h
            rw [hτ₁] at h
            exact h.2
          rw [← hc0] at hmax'
          intro e he hce
          rw [le_antisymm (hmax'.2 e he) hce]
          exact hcsat
      case pCell =>
        have hnmin : ¬ MinPos tagTupleLe SatPosn p := by
          intro hmin
          have hpp : p = posStart := isLinOrd_tagTupleLe.2.2.1 p posStart
            (hmin.2 posStart satPosn_posStart) (minPos_posStart.2 p hmin.1)
          rw [hpp] at htag
          exact SatTag.noConfusion htag
        obtain ⟨q, hqp⟩ := exists_predPos isLinOrd_tagTupleLe hp hnmin
        have hc₁ : c₁ = confChkL ν c q :=
          step_functional_off_guess
            (fun hcon => SatTag.noConfusion (congrArg Prod.fst hcon.1)) hstep
            (step_chkL ν hc hqp htag)
        rw [hc₁] at hrest
        exact ihL ν c q cfin hc hqp.1 hrest hacc
      case pEnd =>
        rw [show p = posEnd from eq_posEnd_of_posn hp htag] at hstep
        obtain ⟨τ, hτ, hsrc, hread, -, -, -, -⟩ := hstep
        obtain ⟨-, hd, -⟩ := trTag_chk_sEnd τ.1 (chkFlagL ν c posEnd) false
          (satTr_isTrTag hτ) (satSrc_tag hτ hsrc).symm (satRead_tag hτ hread).symm
        exact Bool.noConfusion hd
      case pFill _ =>
        obtain ⟨τ, hτ, -, hread, -, -, -, -⟩ := hstep
        have hbl : (confChkL ν c p).tape ((confChkL ν c p).head) = symBlank := by
          change doneTape ν p = symBlank
          simp only [doneTape, guessTape, htag]
        rw [hbl] at hread
        exact absurd (satRead_tag hτ hread).symm (trTag_read_ne_sBlank τ.1 (satTr_isTrTag hτ))
      all_goals (rw [SatPosn, htag] at hp; exact hp.elim)
    · rintro ν c p cfin hc hp ⟨c₁, hstep, hrest⟩ hacc
      cases htag : p.1
      case pEnd =>
        rw [show p = posEnd from eq_posEnd_of_posn hp htag] at hstep
        have hstep' := hstep
        obtain ⟨τ, hτ, hsrc, hread, -, -, -, -⟩ := hstep'
        obtain ⟨hflag, -, hcase⟩ := trTag_chk_sEnd τ.1 (chkFlagR ν c posEnd) true
          (satTr_isTrTag hτ) (satSrc_tag hτ hsrc).symm (satRead_tag hτ hread).symm
        have hcsat : ∃ y : A, SatLit c y (ν y) := (chkFlagR_posEnd ν c).mp hflag
        rcases hcase with hτ₁ | hτ₁
        · have hc0 : c = τ.2 0 := (one_eq_one_iff.mp (satSrc_turnNext hτ₁ hsrc)).2
          have hnext' : SatNextCl (τ.2 0) (τ.2 1) := by
            have h : SatTr τ := hτ
            unfold SatTr at h
            rw [hτ₁] at h
            exact h
          rw [← hc0] at hnext'
          have hc₁ : c₁ = confChkL ν (τ.2 1) (posCell topA) :=
            step_functional_off_guess
              (fun hcon => SatTag.noConfusion (congrArg Prod.fst hcon.1)) hstep
              (step_turnNextR ν hnext' hflag)
          rw [hc₁] at hrest
          intro e he hce
          rcases eq_or_lt_of_le hce with rfl | hlt
          · exact hcsat
          · exact ihL ν (τ.2 1) (posCell topA) cfin hnext'.2.1 (satPosn_posCell _) hrest hacc
              e he (hnext'.2.2.2 e he hlt)
        · have hc0 : c = τ.2 0 := (one_eq_one_iff.mp (satSrc_turnAcc hτ₁ hsrc)).2
          have hmax' : SatMaxCl (τ.2 0) := by
            have h : SatTr τ := hτ
            unfold SatTr at h
            rw [hτ₁] at h
            exact h.2
          rw [← hc0] at hmax'
          intro e he hce
          rw [le_antisymm (hmax'.2 e he) hce]
          exact hcsat
      case pCell =>
        have hnmax : ¬ MaxPos tagTupleLe SatPosn p := by
          intro hmax
          have hple : tagTupleLe p posEnd := by
            refine tagTupleLe_of_tag_lt ?_
            rw [htag]
            exact (show SatTag.pCell < SatTag.pEnd by decide)
          have hpe : p = posEnd :=
            isLinOrd_tagTupleLe.2.2.1 p posEnd hple (hmax.2 posEnd satPosn_posEnd)
          rw [hpe] at htag
          exact SatTag.noConfusion htag
        obtain ⟨q, hpq⟩ := TMData.exists_succPos' (M := satMachine A) isLinOrd_tagTupleLe hp hnmax
        have hc₁ : c₁ = confChkR ν c q :=
          step_functional_off_guess
            (fun hcon => SatTag.noConfusion (congrArg Prod.fst hcon.1)) hstep
            (step_chkR ν hc hpq htag)
        rw [hc₁] at hrest
        exact ihR ν c q cfin hc hpq.2.1 hrest hacc
      case pStart =>
        rw [show p = posStart from eq_posStart_of_posn hp htag] at hstep
        obtain ⟨τ, hτ, hsrc, hread, -, -, -, -⟩ := hstep
        obtain ⟨-, hd, -⟩ := trTag_chk_sStart τ.1 (chkFlagR ν c posStart) true
          (satTr_isTrTag hτ) (satSrc_tag hτ hsrc).symm (satRead_tag hτ hread).symm
        exact Bool.noConfusion hd
      case pFill _ =>
        obtain ⟨τ, hτ, -, hread, -, -, -, -⟩ := hstep
        have hbl : (confChkR ν c p).tape ((confChkR ν c p).head) = symBlank := by
          change doneTape ν p = symBlank
          simp only [doneTape, guessTape, htag]
        rw [hbl] at hread
        exact absurd (satRead_tag hτ hread).symm (trTag_read_ne_sBlank τ.1 (satTr_isTrTag hτ))
      all_goals (rw [SatPosn, htag] at hp; exact hp.elim)

/-- **The guess-phase analysis**: an accepting run from a guess configuration
yields a satisfying assignment. Walking the guess sweep, the assignment is
rebuilt one cell at a time from the values the run chose to write; at the right
marker the run either accepts – no clause exists – or enters the check phase,
where `DescriptiveComplexity.sat_of_chk` takes over. -/
theorem sat_of_guess : ∀ (k : ℕ) (ν : A → Bool) (p : SatV A) (cfin : Config (SatV A)),
    SatPosn p → tagTupleLe p posEnd →
    (satMachine A).StepsIn k (confGuess ν p) cfin → SatAcc cfin.state →
    ∃ ν' : A → Bool, ∀ e : A, SatCl e → ∃ y : A, SatLit e y (ν' y) := by
  intro k
  induction k with
  | zero =>
    intro ν p cfin hp hle hk hacc
    have heq : _ = cfin := hk
    rw [← heq] at hacc
    exact SatTag.noConfusion hacc
  | succ k ih =>
    rintro ν p cfin hp hle ⟨c₁, hstep, hrest⟩ hacc
    rcases tag_le_pEnd (tagTupleLe_tag_le hle) with htag | htag | htag
    · -- the left marker: step over it
      rw [show p = posStart from eq_posStart_of_posn hp htag] at hstep
      have hc₁ : c₁ = confGuess ν (posCell botA) :=
        step_functional_off_guess
          (fun hcon => SatTag.noConfusion (congrArg Prod.fst hcon.2.choose_spec)) hstep
          (step_guess ν succPos_posStart_posCell (posCell_le_posEnd botA))
      rw [hc₁] at hrest
      exact ih ν (posCell botA) cfin (satPosn_posCell _) (posCell_le_posEnd _) hrest hacc
    · -- a cell: the guess itself
      obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
      have hpos1 : ∀ a : A, p.2 1 ≤ a := by
        have h := hp
        rw [SatPosn, htag] at h
        exact h
      have hcell : (confGuess ν p).tape ((confGuess ν p).head) = symU (p.2 0) := by
        change guessTape ν p p = symU (p.2 0)
        simp only [guessTape, htag]
        exact if_neg (fun hcon => hcon.2.2 rfl)
      rw [hcell] at hread
      obtain ⟨v, hτ₁⟩ := trTag_guess_sU τ.1 (satTr_isTrTag hτ)
        (satSrc_tag hτ hsrc).symm (satRead_tag hτ hread).symm
      have hx : τ.2 0 = p.2 0 := (one_eq_one_iff.mp (satRead_guessVal hτ₁ hread)).2.symm
      have hst : c₁.state = stGuess := by
        have h : SatDst τ c₁.state := hdst
        unfold SatDst at h
        rw [hτ₁] at h
        exact h
      have hwr : c₁.tape p = symV v (p.2 0) := by
        have h : SatWrite τ (c₁.tape ((confGuess ν p).head)) := hwrite
        unfold SatWrite at h
        rw [hτ₁, hx] at h
        exact h
      have hsucc : SuccPos tagTupleLe SatPosn p c₁.head := by
        rcases hmove with ⟨-, hs⟩ | ⟨hr, -⟩
        · exact hs
        · refine absurd ?_ hr
          change SatRight τ
          unfold SatRight
          rw [hτ₁]
          trivial
      have hpc : p = posCell (p.2 0) := eq_posCell_of_posn hp htag
      have hc₁ : c₁ = confGuess (Function.update ν (p.2 0) v) c₁.head := by
        refine Config.ext hst rfl (funext fun r => ?_)
        rcases eq_or_ne r p with heq | hr
        · rw [heq, hwr]
          change _ = guessTape (Function.update ν (p.2 0) v) c₁.head p
          simp only [guessTape, htag]
          rw [if_pos ⟨hpos1, hsucc.2.2.1, hsucc.2.2.2.1⟩, Function.update_self]
        · rw [hframe r hr]
          change guessTape ν p r = guessTape (Function.update ν (p.2 0) v) c₁.head r
          rw [guessTape_frame (Function.update ν (p.2 0) v) hsucc hr]
          refine guessTape_congr (fun y hyle hyne => ?_) r
          refine (Function.update_of_ne (fun hy : y = p.2 0 => ?_) _ _).symm
          rw [hy] at hyne
          exact hyne hpc.symm
      rw [hc₁] at hrest
      have hqle : tagTupleLe c₁.head posEnd := by
        rcases isLinOrd_tagTupleLe.2.2.2 c₁.head posEnd with h | h
        · exact h
        · rcases hsucc.2.2.2.2 posEnd satPosn_posEnd hle h with h' | h'
          · exact SatTag.noConfusion ((congrArg Prod.fst h').trans htag)
          · rw [← h']
            exact isLinOrd_tagTupleLe.1 posEnd
      exact ih (Function.update ν (p.2 0) v) c₁.head cfin hsucc.2.1 hqle hrest hacc
    · -- the right marker: turn out of the guess phase
      rw [show p = posEnd from eq_posEnd_of_posn hp htag] at hstep
      have hstep' := hstep
      obtain ⟨τ, hτ, hsrc, hread, -, -, -, -⟩ := hstep'
      rcases trTag_guess_sEnd τ.1 (satTr_isTrTag hτ)
          (satSrc_tag hτ hsrc).symm (satRead_tag hτ hread).symm with hτ₁ | hτ₁
      · -- no clause at all: vacuously satisfiable
        have hno : ∀ e : A, ¬ SatCl e := by
          have h : SatTr τ := hτ
          unfold SatTr at h
          rw [hτ₁] at h
          exact h.2
        exact ⟨ν, fun e he => absurd he (hno e)⟩
      · -- start checking the lowest clause
        have htr : (∀ a : A, τ.2 1 ≤ a) ∧ SatMinCl (τ.2 0) := by
          have h : SatTr τ := hτ
          unfold SatTr at h
          rw [hτ₁] at h
          exact h
        have hint : (satMachine A).Step (confGuess ν posEnd)
            (confChkL ν (τ.2 0) (posCell topA)) := by
          have heq : confChkL ν (τ.2 0) (posCell (topA (A := A))) =
              { state := stChk false false (τ.2 0), head := posCell topA,
                tape := guessTape ν posEnd } := by
            refine Config.ext ?_ rfl rfl
            change stChk (chkFlagL ν (τ.2 0) (posCell topA)) false (τ.2 0) =
              stChk false false (τ.2 0)
            rw [chkFlagL_top]
          rw [heq]
          exact step_turnChk ν htr.2
        have hc₁ : c₁ = confChkL ν (τ.2 0) (posCell topA) :=
          step_functional_off_guess
            (fun hcon => SatTag.noConfusion (congrArg Prod.fst hcon.2.choose_spec)) hstep hint
        rw [hc₁] at hrest
        exact ⟨ν, fun e he => (sat_of_chk k).1 ν (τ.2 0) (posCell topA) cfin htr.2.1
          (satPosn_posCell _) hrest hacc e he (htr.2.2 e he)⟩

end Reverse

/-! ### The machine accepts exactly the satisfiable instances -/

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- Satisfiability with a `Bool`-valued assignment, the form the machine
manipulates. -/
theorem satisfiable_iff_exists_bool :
    Satisfiable A ↔ ∃ ν : A → Bool, ∀ e : A, SatCl e → ∃ y : A, SatLit e y (ν y) := by
  constructor
  · rintro ⟨ν, hν⟩
    classical
    refine ⟨fun a => decide (ν a), fun e he => ?_⟩
    obtain ⟨x, hx⟩ := hν e he
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨x, Or.inl ⟨hp, decide_eq_true hT⟩⟩
    · exact ⟨x, Or.inr ⟨hn, decide_eq_false hT⟩⟩
  · rintro ⟨ν, hν⟩
    refine ⟨fun a => ν a = true, fun c hc => ?_⟩
    obtain ⟨y, hy⟩ := hν c hc
    rcases hy with ⟨hp, hT⟩ | ⟨hn, hF⟩
    · exact ⟨y, Or.inl ⟨hp, hT⟩⟩
    · exact ⟨y, Or.inr ⟨hn, by simp [hF]⟩⟩

/-- **Correctness of the machine of a CNF formula**: it accepts – within the
budget – exactly the satisfiable instances. -/
theorem satMachine_accepts_iff_satisfiable : (satMachine A).Accepts ↔ Satisfiable A := by
  rw [satisfiable_iff_exists_bool]
  constructor
  · rintro ⟨c₀, cfin, n, hinit, -, hrun, hacc⟩
    rw [isInit_eq_confGuess hinit (fun _ => false)] at hrun
    exact sat_of_guess n (fun _ => false) posStart cfin satPosn_posStart
      posStart_le_posEnd hrun hacc
  · rintro ⟨ν, hν⟩
    exact satMachine_accepts_of_sat ν hν

end Machine

end DescriptiveComplexity
