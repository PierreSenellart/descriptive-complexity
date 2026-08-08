/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameProgram
import DescriptiveComplexity.Exponential.GameTape

/-!
# The control of a machine playing a second-order game

The phases of the machine whose tape is
`DescriptiveComplexity.Exponential.GameTape`, and which player owns each. This
file fixes the control design; the transition table that realizes it is the
next step.

## The play, in one block

`r` is the region holding the current position of the game, `!r` the one
holding the candidate. A **universal split** is how a check is conjoined with a
continuation: a universal state whose successors are the branches, each of
which then has its own copy of the tape.

```
init        ∃-sweep into region 0 ; splitStart
splitStart  ∀ { verify start ; play }
play        ∃ { verify won                                    -- Wins.won
              ; splitEx                                       -- Wins.ex
              ; splitAll }                                    -- Wins.all
splitEx     ∀ { verify ¬univ ; ∃-sweep into !r ; splitMove }
splitMove   ∀ { verify move ; play at !r }
splitAll    ∀ { verify univ
              ; ∃-sweep into !r ; verify move                 -- a legal move exists
              ; ∀-sweep into !r ; allStep }
allStep     ∃ { verify ¬move ; play at !r }
```

Three conventions, all forced, and all the ones half A settled:

* **`play` is existential** and chooses which clause of
  `DescriptiveComplexity.SOGameSpec.Wins` it claims; a false claim loses
  because the corresponding check runs out of transitions.
* **the universal clause certifies a successor before it hands over**
  (`Wins.all` demands a legal move), which is the second branch of `splitAll`;
  the branches carry separate tapes, so the `∃`-guess and the `∀`-guess of the
  candidate never collide.
* **an illegal universal guess is discarded by the existential player**, who
  may refute `move` at `allStep` instead of continuing – no sentence over the
  base could filter it out before the guess.

`play` at `!r` **swaps the roles of the two regions** instead of copying one
over the other; a copy would be a quadratic walk with a nested induction.

## Checking a question

A check is `DescriptiveComplexity.QuestionData` run as a walk
(`DescriptiveComplexity.exists_questionData`): the prefix is played one
variable at a time, then the existential player claims the truth values of the
block atoms in one move, and the universal player either challenges one – a
walk to the cell it addresses – or lets the residual formula, which mentions no
block atom, guard the concluding transition.

```
pre q j     the player `pol q j` names writes the j-th variable ; pre q (j+1)
            at j = vars q: claim
claim q     ∃ picks the whole vector b of claims               ; check q b
check q b   ∀ { seek q b k  (k < natoms q) ; conc q b }
seek q b k  walk to the cell of the k-th atom; accept iff its bit is b k
conc q b    accept if the residual formula holds; no transition otherwise
```

## Two bookkeeping fields, and why

* **`par`**: `DescriptiveComplexity.TMData.Step` has no stay-put option, so a
  phase that does not touch the tape still moves the head; it bounces between
  the two left sentinels and `par` says which one it is on.
* **`cont`**: a sweep is one gadget used four times, so it carries what to do
  when it is over. It is followed by a `rewind`, a leftward walk that restores
  the head to the left sentinel, so that every check starts from the same end
  and the seek only ever walks one way.

## Why a structure rather than an inductive

`DescriptiveComplexity.MachPh` is a flat record, with fields that are junk in the
phases that do not use them. That is deliberate: `Finite` and `DecidableEq`
come from the product, the tag order of
`DescriptiveComplexity.machTagOrder` needs nothing else, and no injective
numbering of constructors has to be maintained. Unreachable field combinations
are harmless – no transition mentions them.
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### The pieces of a phase -/

/-- What a sweep does when it is over: the four places the control guesses an
assignment. -/
inductive SweepCont : Type
  /-- The initial sweep, which guesses the starting position of the game. -/
  | start
  /-- The existential player's move out of an existential position. -/
  | exMove
  /-- The existential player's certificate that the universal position it is
  about to hand over has a legal move at all. -/
  | certify
  /-- The universal player's move out of a universal position. -/
  | allMove
  deriving DecidableEq

instance : Fintype SweepCont :=
  ⟨{.start, .exMove, .certify, .allMove}, by intro x; cases x <;> simp⟩

/-- The kind of a phase: what the machine is doing. -/
inductive PhKind : Type
  /-- Walking right, writing a guessed assignment into one region. -/
  | sweep
  /-- Walking left, back to the left sentinel. -/
  | rewind
  /-- After the initial sweep: check the start condition, and play. -/
  | splitStart
  /-- A position of the game: the existential player picks a clause of `Wins`. -/
  | play
  /-- The existential clause: check that the position is existential, and move. -/
  | splitEx
  /-- The universal clause: check that the position is universal, certify a
  successor, and answer every candidate. -/
  | splitAll
  /-- After a candidate has been guessed: check the move, and play on. -/
  | splitMove
  /-- After the universal player's candidate: refute the move, or play on. -/
  | allStep
  /-- Playing the quantifier prefix of a question. -/
  | pre
  /-- Claiming the truth values of the block atoms of a question. -/
  | claim
  /-- Challenging one claim, or concluding. -/
  | check
  /-- Walking to the cell a challenged claim addresses. -/
  | seek
  /-- The residual formula decides. -/
  | conc
  /-- Accepting. -/
  | acc
  deriving DecidableEq

instance : Fintype PhKind :=
  ⟨{.sweep, .rewind, .splitStart, .play, .splitEx, .splitAll, .splitMove, .allStep,
      .pre, .claim, .check, .seek, .conc, .acc}, by intro x; cases x <;> simp⟩

/-! ### A phase -/

/-- **A phase of the control**: what the machine is doing, and the bookkeeping
it carries. Fields not used by a kind are junk – see the module docstring. -/
@[ext]
structure MachPh (V M : ℕ) : Type where
  /-- What the machine is doing. -/
  kind : PhKind
  /-- The question being checked. -/
  q : GameQuestion
  /-- The region holding the current position of the game. -/
  r : Bool
  /-- The region a sweep is writing into; at a seek, the claimed bit. -/
  tgt : Bool
  /-- The index of the prefix variable being played. -/
  j : Fin (V + 1)
  /-- The index of the block atom being challenged. -/
  k : Fin (M + 1)
  /-- The claimed truth values of the block atoms. -/
  claims : Fin M → Bool
  /-- What a sweep does when it is over. -/
  cont : SweepCont
  /-- Which of the two left sentinels the head is bouncing on. -/
  par : Bool

namespace MachPh

variable {V M : ℕ}

/-- A phase as a tuple, for the `Finite` instance. -/
def toProd (p : MachPh V M) :
    PhKind × GameQuestion × Bool × Bool × Fin (V + 1) × Fin (M + 1) ×
      (Fin M → Bool) × SweepCont × Bool :=
  (p.kind, p.q, p.r, p.tgt, p.j, p.k, p.claims, p.cont, p.par)

theorem toProd_injective : Function.Injective (toProd (V := V) (M := M)) := by
  intro a b h
  simp only [toProd, Prod.mk.injEq] at h
  exact MachPh.ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2

instance : Finite (MachPh V M) := Finite.of_injective _ toProd_injective

instance : Nonempty (MachPh V M) :=
  ⟨⟨.acc, .won, false, false, 0, 0, fun _ => false, .start, false⟩⟩

/-! ### What a phase owns and uses -/

/-- **The coordinates a phase uses**: the prefix has written the variables
below `j`, and a question that has reached its matrix has written them all.
Everything else carries no data, so the domain pins its whole tuple. -/
def arity (vars : GameQuestion → ℕ) (p : MachPh V M) : ℕ :=
  match p.kind with
  | .pre => min (p.j : ℕ) (vars p.q)
  | .claim | .check | .seek | .conc => vars p.q
  | _ => 0

/-- **Which phases belong to the universal player.** The splits are universal
because they conjoin a check with a continuation; `check` is universal because
it is the challenge; a prefix variable belongs to the player its polarity
names; a sweep belongs to the player guessing the assignment, which is the
universal one exactly for the universal player's own move. -/
def IsUniv (pol : GameQuestion → ℕ → Bool) (p : MachPh V M) : Bool :=
  match p.kind with
  | .splitStart | .splitEx | .splitAll | .splitMove | .check => true
  | .sweep => match p.cont with
      | .allMove => true
      | _ => false
  | .pre => !(pol p.q (p.j : ℕ))
  | _ => false

@[simp] theorem isUniv_play (pol : GameQuestion → ℕ → Bool) {p : MachPh V M} (h : p.kind = .play) :
    IsUniv pol p = false := by simp [IsUniv, h]

@[simp] theorem isUniv_check (pol : GameQuestion → ℕ → Bool) {p : MachPh V M}
    (h : p.kind = .check) : IsUniv pol p = true := by simp [IsUniv, h]

@[simp] theorem isUniv_claim (pol : GameQuestion → ℕ → Bool) {p : MachPh V M}
    (h : p.kind = .claim) : IsUniv pol p = false := by simp [IsUniv, h]

@[simp] theorem isUniv_acc (pol : GameQuestion → ℕ → Bool) {p : MachPh V M} (h : p.kind = .acc) :
    IsUniv pol p = false := by simp [IsUniv, h]

@[simp] theorem isUniv_conc (pol : GameQuestion → ℕ → Bool) {p : MachPh V M}
    (h : p.kind = .conc) : IsUniv pol p = false := by simp [IsUniv, h]

@[simp] theorem isUniv_allStep (pol : GameQuestion → ℕ → Bool) {p : MachPh V M}
    (h : p.kind = .allStep) : IsUniv pol p = false := by simp [IsUniv, h]

/-- **The four splits belong to the universal player**, which is what makes a
split a conjunction: each of its branches has to win. -/
theorem isUniv_split (pol : GameQuestion → ℕ → Bool) {p : MachPh V M}
    (h : p.kind = .splitStart ∨ p.kind = .splitEx ∨ p.kind = .splitAll ∨
      p.kind = .splitMove) : IsUniv pol p = true := by
  rcases h with h | h | h | h <;> simp [IsUniv, h]

@[simp] theorem isUniv_seek (pol : GameQuestion → ℕ → Bool) {p : MachPh V M}
    (h : p.kind = .seek) : IsUniv pol p = false := by simp [IsUniv, h]

@[simp] theorem isUniv_rewind (pol : GameQuestion → ℕ → Bool) {p : MachPh V M}
    (h : p.kind = .rewind) : IsUniv pol p = false := by simp [IsUniv, h]

/-- A sweep is universal exactly when it is the universal player's own move. -/
theorem isUniv_sweep (pol : GameQuestion → ℕ → Bool) {p : MachPh V M} (h : p.kind = .sweep) :
    IsUniv pol p = (p.cont == SweepCont.allMove) := by
  cases hc : p.cont <;> simp [IsUniv, h, hc]

/-- A prefix phase belongs to the player its polarity names. -/
theorem isUniv_pre (pol : GameQuestion → ℕ → Bool) {p : MachPh V M} (h : p.kind = .pre) :
    IsUniv pol p = !(pol p.q (p.j : ℕ)) := by simp [IsUniv, h]

end MachPh

/-! ### The phases, named -/

namespace MachPh

variable {V M : ℕ}

/-- The phase sweeping region `tgt` while the game sits in region `r`. -/
def sweepPh (r tgt : Bool) (cont : SweepCont) (par : Bool) : MachPh V M :=
  ⟨.sweep, .won, r, tgt, 0, 0, fun _ => false, cont, par⟩

/-- The phase walking back to the left sentinel after a sweep. -/
def rewindPh (r tgt : Bool) (cont : SweepCont) (par : Bool) : MachPh V M :=
  ⟨.rewind, .won, r, tgt, 0, 0, fun _ => false, cont, par⟩

/-- The split following the initial sweep. -/
def splitStartPh (r par : Bool) : MachPh V M :=
  ⟨.splitStart, .won, r, false, 0, 0, fun _ => false, .start, par⟩

/-- A position of the game, in region `r`. -/
def playPh (r par : Bool) : MachPh V M :=
  ⟨.play, .won, r, false, 0, 0, fun _ => false, .start, par⟩

/-- The existential clause of `Wins`. -/
def splitExPh (r par : Bool) : MachPh V M :=
  ⟨.splitEx, .won, r, false, 0, 0, fun _ => false, .start, par⟩

/-- The universal clause of `Wins`. -/
def splitAllPh (r par : Bool) : MachPh V M :=
  ⟨.splitAll, .won, r, false, 0, 0, fun _ => false, .start, par⟩

/-- Checking the move just guessed, then playing on. -/
def splitMovePh (r par : Bool) : MachPh V M :=
  ⟨.splitMove, .won, r, false, 0, 0, fun _ => false, .start, par⟩

/-- Refuting the move just guessed, or playing on. -/
def allStepPh (r par : Bool) : MachPh V M :=
  ⟨.allStep, .won, r, false, 0, 0, fun _ => false, .start, par⟩

/-- Playing the `j`-th variable of the prefix of `q`. -/
def prePh (q : GameQuestion) (r : Bool) (j : Fin (V + 1)) (par : Bool) : MachPh V M :=
  ⟨.pre, q, r, false, j, 0, fun _ => false, .start, par⟩

/-- Claiming the truth values of the block atoms of `q`. -/
def claimPh (q : GameQuestion) (r par : Bool) : MachPh V M :=
  ⟨.claim, q, r, false, 0, 0, fun _ => false, .start, par⟩

/-- The claims of `q` are `b`: challenge one, or conclude. -/
def checkPh (q : GameQuestion) (r : Bool) (b : Fin M → Bool) (par : Bool) : MachPh V M :=
  ⟨.check, q, r, false, 0, 0, b, .start, par⟩

/-- Walking to the cell the `k`-th atom of `q` addresses. -/
def seekPh (q : GameQuestion) (r : Bool) (b : Fin M → Bool) (k : Fin (M + 1))
    (par : Bool) : MachPh V M :=
  ⟨.seek, q, r, false, 0, k, b, .start, par⟩

/-- The residual formula of `q` under the claims `b` decides. -/
def concPh (q : GameQuestion) (r : Bool) (b : Fin M → Bool) (par : Bool) : MachPh V M :=
  ⟨.conc, q, r, false, 0, 0, b, .start, par⟩

/-- The accepting phase. -/
def accPh (par : Bool) : MachPh V M :=
  ⟨.acc, .won, false, false, 0, 0, fun _ => false, .start, par⟩

/-! ### The control graph -/

/-- **Where a tape-free step may go.** This is the block of the module
docstring, written out: the head is on a left sentinel throughout, so every
step here flips `par` and moves between the two.

The steps *out of* a walk – a sweep handing over to its rewind, a rewind
handing over to its continuation – are not here: they are tape steps, and
`DescriptiveComplexity.MachPh.rewindTarget` is where the second one lands. Nor
is the guard of `conc`, which is a condition on the source structure and enters
the transition table rather than the control graph. -/
def CtrlStep (vars natoms : GameQuestion → ℕ) (p p' : MachPh V M) : Prop :=
  match p.kind with
  | .splitStart => p' = prePh .start p.r 0 (!p.par) ∨ p' = playPh p.r (!p.par)
  | .play =>
      p' = prePh .won p.r 0 (!p.par) ∨ p' = splitExPh p.r (!p.par) ∨
        p' = splitAllPh p.r (!p.par)
  | .splitEx =>
      p' = prePh .notUniv p.r 0 (!p.par) ∨ p' = sweepPh p.r (!p.r) .exMove (!p.par)
  | .splitAll =>
      p' = prePh .univ p.r 0 (!p.par) ∨ p' = sweepPh p.r (!p.r) .certify (!p.par) ∨
        p' = sweepPh p.r (!p.r) .allMove (!p.par)
  | .splitMove => p' = prePh .move p.r 0 (!p.par) ∨ p' = playPh (!p.r) (!p.par)
  | .allStep => p' = prePh .notMove p.r 0 (!p.par) ∨ p' = playPh (!p.r) (!p.par)
  | .pre =>
      if (p.j : ℕ) < vars p.q then
        ∃ j' : Fin (V + 1), (j' : ℕ) = (p.j : ℕ) + 1 ∧ p' = prePh p.q p.r j' (!p.par)
      else p' = claimPh p.q p.r (!p.par)
  | .claim => ∃ b : Fin M → Bool, p' = checkPh p.q p.r b (!p.par)
  | .check =>
      (∃ k : Fin (M + 1), (k : ℕ) < natoms p.q ∧ p' = seekPh p.q p.r p.claims k (!p.par)) ∨
        p' = concPh p.q p.r p.claims (!p.par)
  | .conc => p' = accPh (!p.par)
  | .sweep | .rewind | .seek | .acc => False

/-- **Where a rewind hands over**: the four continuations of a sweep. The head
lands on the lowest position, so `par` is `false`. -/
def rewindTarget (p : MachPh V M) : MachPh V M :=
  match p.cont with
  | .start => splitStartPh p.r false
  | .exMove => splitMovePh p.r false
  | .certify => prePh .move p.r 0 false
  | .allMove => allStepPh p.r false

/-! ### The phases that carry no data -/

section Arity

variable (vars : GameQuestion → ℕ)

@[simp] theorem arity_sweepPh (r tgt : Bool) (cont : SweepCont) (par : Bool) :
    arity vars (sweepPh r tgt cont par : MachPh V M) = 0 := rfl

@[simp] theorem arity_rewindPh (r tgt : Bool) (cont : SweepCont) (par : Bool) :
    arity vars (rewindPh r tgt cont par : MachPh V M) = 0 := rfl

@[simp] theorem arity_accPh (par : Bool) : arity vars (accPh par : MachPh V M) = 0 := rfl

@[simp] theorem arity_playPh (r par : Bool) : arity vars (playPh r par : MachPh V M) = 0 := rfl

@[simp] theorem arity_splitStartPh (r par : Bool) :
    arity vars (splitStartPh r par : MachPh V M) = 0 := rfl

@[simp] theorem arity_splitExPh (r par : Bool) :
    arity vars (splitExPh r par : MachPh V M) = 0 := rfl

@[simp] theorem arity_splitAllPh (r par : Bool) :
    arity vars (splitAllPh r par : MachPh V M) = 0 := rfl

@[simp] theorem arity_splitMovePh (r par : Bool) :
    arity vars (splitMovePh r par : MachPh V M) = 0 := rfl

@[simp] theorem arity_allStepPh (r par : Bool) :
    arity vars (allStepPh r par : MachPh V M) = 0 := rfl

/-- **A prefix that has written nothing declares nothing**, so the phase a
question is entered at carries the constant valuation. -/
@[simp] theorem arity_prePh_zero (q : GameQuestion) (r par : Bool) :
    arity vars (prePh q r 0 par : MachPh V M) = 0 := by
  simp [arity, prePh]

/-- **A rewind hands over to a phase that carries no data**: the four
continuations of a sweep are all at the start of their own business, so the
state a rewind enters is the constant tuple. -/
@[simp] theorem arity_rewindTarget (p : MachPh V M) : arity vars (rewindTarget p) = 0 := by
  cases hc : p.cont <;>
    simp [rewindTarget, hc, arity, splitStartPh, splitMovePh, prePh, allStepPh]

/-- **And it hands over on the lowest position**, which is what its parity
records. -/
@[simp] theorem par_rewindTarget (p : MachPh V M) : (rewindTarget p).par = false := by
  cases hc : p.cont <;>
    simp [rewindTarget, hc, splitStartPh, splitMovePh, prePh, allStepPh]

/-- A seek declares the variables of its own question. -/
theorem arity_seekPh (q : GameQuestion) (r : Bool) (b : Fin M → Bool) (k : Fin (M + 1))
    (par : Bool) : arity vars (seekPh q r b k par : MachPh V M) = vars q := rfl

theorem arity_concPh (q : GameQuestion) (r : Bool) (b : Fin M → Bool) (par : Bool) :
    arity vars (concPh q r b par : MachPh V M) = vars q := rfl

/-- A prefix phase declares the variables it has already written. -/
theorem arity_prePh (q : GameQuestion) (r : Bool) (j : Fin (V + 1)) (par : Bool) :
    arity vars (prePh q r j par : MachPh V M) = min (j : ℕ) (vars q) := rfl

theorem arity_claimPh (q : GameQuestion) (r par : Bool) :
    arity vars (claimPh q r par : MachPh V M) = vars q := rfl

/-- A question that has reached its matrix declares its whole prefix. -/
theorem arity_of_matrix {p : MachPh V M}
    (h : p.kind = .claim ∨ p.kind = .check ∨ p.kind = .seek ∨ p.kind = .conc) :
    arity vars p = vars p.q := by
  rcases h with h | h | h | h <;> simp [arity, h]

/-- **No phase declares more coordinates than the machine's tuple has room
for**, as soon as the phase index bounds every question's prefix – which is
what `DescriptiveComplexity.GameProg` promises. -/
theorem arity_le_of_vars_le (hV : ∀ q, vars q ≤ V) (p : MachPh V M) : arity vars p ≤ V := by
  have h := hV p.q
  cases hk : p.kind <;> simp only [arity, hk] <;> omega

end Arity

/-! ### Sanity of the control graph -/

variable (vars natoms : GameQuestion → ℕ)

/-! The six phases of the game proper, each with its successors named. Stated
as equivalences, because the universal ones are read backwards. -/

theorem ctrlStep_splitStartPh (r par : Bool) (p' : MachPh V M) :
    CtrlStep vars natoms (splitStartPh r par) p' ↔
      (p' = prePh .start r 0 (!par) ∨ p' = playPh r (!par)) := Iff.rfl

theorem ctrlStep_playPh (r par : Bool) (p' : MachPh V M) :
    CtrlStep vars natoms (playPh r par) p' ↔
      (p' = prePh .won r 0 (!par) ∨ p' = splitExPh r (!par) ∨ p' = splitAllPh r (!par)) :=
  Iff.rfl

theorem ctrlStep_splitExPh (r par : Bool) (p' : MachPh V M) :
    CtrlStep vars natoms (splitExPh r par) p' ↔
      (p' = prePh .notUniv r 0 (!par) ∨ p' = sweepPh r (!r) .exMove (!par)) := Iff.rfl

theorem ctrlStep_splitAllPh (r par : Bool) (p' : MachPh V M) :
    CtrlStep vars natoms (splitAllPh r par) p' ↔
      (p' = prePh .univ r 0 (!par) ∨ p' = sweepPh r (!r) .certify (!par) ∨
        p' = sweepPh r (!r) .allMove (!par)) := Iff.rfl

theorem ctrlStep_splitMovePh (r par : Bool) (p' : MachPh V M) :
    CtrlStep vars natoms (splitMovePh r par) p' ↔
      (p' = prePh .move r 0 (!par) ∨ p' = playPh (!r) (!par)) := Iff.rfl

theorem ctrlStep_allStepPh (r par : Bool) (p' : MachPh V M) :
    CtrlStep vars natoms (allStepPh r par) p' ↔
      (p' = prePh .notMove r 0 (!par) ∨ p' = playPh (!r) (!par)) := Iff.rfl

/-- **A prefix phase with a variable left writes it**, moving to the next
index. Stated as an equivalence so that the backward reading has it too. -/
theorem ctrlStep_prePh (q : GameQuestion) (r : Bool) (j : Fin (V + 1)) (par : Bool)
    (h : (j : ℕ) < vars q) (p' : MachPh V M) :
    CtrlStep vars natoms (prePh q r j par) p' ↔
      ∃ j' : Fin (V + 1), (j' : ℕ) = (j : ℕ) + 1 ∧ p' = prePh q r j' (!par) := by
  simp [CtrlStep, prePh, h]

/-- **A prefix phase with no variable left hands over to the claim.** -/
theorem ctrlStep_prePh_last (q : GameQuestion) (r : Bool) (j : Fin (V + 1)) (par : Bool)
    (h : ¬ ((j : ℕ) < vars q)) (p' : MachPh V M) :
    CtrlStep vars natoms (prePh q r j par) p' ↔ p' = claimPh q r (!par) := by
  simp [CtrlStep, prePh, h]

theorem ctrlStep_acc (p p' : MachPh V M) (h : p.kind = .acc) :
    ¬ CtrlStep vars natoms p p' := by simp [CtrlStep, h]

theorem ctrlStep_sweep (p p' : MachPh V M) (h : p.kind = .sweep) :
    ¬ CtrlStep vars natoms p p' := by simp [CtrlStep, h]

theorem ctrlStep_seek (p p' : MachPh V M) (h : p.kind = .seek) :
    ¬ CtrlStep vars natoms p p' := by simp [CtrlStep, h]

/-- **A control step flips the parity**: the head really does bounce. -/
theorem par_of_ctrlStep {p p' : MachPh V M} (h : CtrlStep vars natoms p p') :
    p'.par = !p.par := by
  unfold CtrlStep at h
  rcases hk : p.kind <;> rw [hk] at h
  · exact h.elim
  · exact h.elim
  · rcases h with rfl | rfl <;> rfl
  · rcases h with rfl | rfl | rfl <;> rfl
  · rcases h with rfl | rfl <;> rfl
  · rcases h with rfl | rfl | rfl <;> rfl
  · rcases h with rfl | rfl <;> rfl
  · rcases h with rfl | rfl <;> rfl
  · by_cases hj : (p.j : ℕ) < vars p.q
    · rw [if_pos hj] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl
    · rw [if_neg hj] at h
      subst h
      rfl
  · obtain ⟨_, rfl⟩ := h; rfl
  · rcases h with ⟨_, _, rfl⟩ | rfl <;> rfl
  · exact h.elim
  · subst h; rfl
  · exact h.elim

end MachPh

end DescriptiveComplexity
