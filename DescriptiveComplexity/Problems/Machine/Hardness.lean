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

/-- **The machine is well formed**, which is all of
`DescriptiveComplexity.TMData.WellFormed` – the order is linear, there is a position,
the input is functional and the blank is unique. Every conjunct was proved on
the tape layer, before any transition existed. -/
theorem satMachine_wellFormed : (satMachine A).WellFormed :=
  ⟨isLinOrd_tagTupleLe, exists_satPosn, fun _ _ _ ha hb => satInp_functional ha hb,
    exists_satBlank, fun _ _ ha hb => satBlank_unique ha hb⟩

end Machine

end DescriptiveComplexity
