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
`(x,F)` in the guess phase. That is design decision (d) of `MACHINE.md`, and it
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
sweep goes in its own direction, and a turn reverses. -/
def SatRight (τ : SatV A) : Prop :=
  match τ.1 with
  | .tGuessStart => True
  | .tGuessVal _ => True
  | .tGuessEndAcc => False
  | .tGuessEndChk => False
  | .tChk _ _ d => d = true
  | .tTurnNext d => d = false
  | .tTurnAcc _ => False
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

Before any run is considered: each transition has exactly one source, symbol
read, destination and symbol written, and the two places where two tags could
otherwise both apply are exclusive. A mistake in the table shows up here first,
which is why these come before the correctness proof. -/

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
theorem cst_eq_cst_iff {t t' : SatTag} : (cst t : SatV A) = cst t' ↔ t = t' :=
  ⟨congrArg Prod.fst, fun h => h ▸ rfl⟩

omit [Language.sat.Structure A] in
/-- A transition applies in exactly one state. -/
theorem satSrc_functional {τ q q' : SatV A} (h : SatSrc τ q) (h' : SatSrc τ q') : q = q' := by
  unfold SatSrc at h h'
  cases hτ : τ.1 <;> rw [hτ] at h h' <;> simp only at h h' <;> exact h.trans h'.symm

omit [Language.sat.Structure A] in
/-- A transition reads exactly one symbol. -/
theorem satRead_functional {τ a a' : SatV A} (h : SatRead τ a) (h' : SatRead τ a') : a = a' := by
  unfold SatRead at h h'
  cases hτ : τ.1 <;> rw [hτ] at h h' <;> simp only at h h' <;> exact h.trans h'.symm

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
/-- Every filler tuple is a position. -/
theorem satPosn_fill (i : Fin 4) (w : Fin 2 → A) : SatPosn ((SatTag.pFill i, w) : SatV A) :=
  trivial

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
/-- **The head moves from cell to cell along the instance.** -/
theorem succPos_posCell_posCell {x x' : A} (hlt : x < x')
    (hcov : ∀ y : A, x ≤ y → y ≤ x' → y = x ∨ y = x') :
    SuccPos tagTupleLe SatPosn (posCell x : SatV A) (posCell x') := by
  refine ⟨satPosn_posCell _, satPosn_posCell _, posCell_le_iff.mpr (le_of_lt hlt), ?_, ?_⟩
  · intro h
    exact absurd (by simpa [one] using congrFun (congrArg Prod.snd h) 0 : x = x') (ne_of_lt hlt)
  · intro r hr h1 h2
    have ht : r.1 = SatTag.pCell :=
      le_antisymm (tagTupleLe_tag_le h2) (tagTupleLe_tag_le h1)
    have hcell := eq_posCell_of_posn hr ht
    have hx : x ≤ r.2 0 := posCell_le_iff.mp (hcell ▸ h1)
    have hx' : r.2 0 ≤ x' := posCell_le_iff.mp (hcell ▸ h2)
    rcases hcov _ hx hx' with h | h
    · exact Or.inl (by rw [hcell, h])
    · exact Or.inr (by rw [hcell, h])

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
the neighbour in the direction the transition names.

This is design decision (d) of `MACHINE.md`: with only the guess phase
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

/-- **The machine is well formed**, which is all of
`DescriptiveComplexity.TMData.WellFormed` – the order is linear, there is a position,
the input is functional and the blank is unique. Every conjunct was proved on
the tape layer, before any transition existed. -/
theorem satMachine_wellFormed : (satMachine A).WellFormed :=
  ⟨isLinOrd_tagTupleLe, exists_satPosn, fun _ _ _ ha hb => satInp_functional ha hb,
    exists_satBlank, fun _ _ ha hb => satBlank_unique ha hb⟩

end Machine

end DescriptiveComplexity
