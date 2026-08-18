/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawOuter
import DescriptiveComplexity.Problems.Wide.DrawBuild

/-!
# The clocked program's outer layer

The EXPSPACE program's outer loop (`DescriptiveComplexity.Draw.OuterPh`) is an
iteration: startup, then a sweep, a convergence test and a copy-back, round after
round until the fixed point stops moving. A program on a clock cannot iterate –
a partial fixed point may run through doubly exponentially many stages – and it
cannot use the input channel's mark ladder either, since reaching it costs more
than the clock allows. What it does instead is four things once:

1. lay its own register file out, low on the tape, one cell per **block and
   tuple** (`DescriptiveComplexity.blkFile`: one per element is what a clock
   cannot pay for);
2. **guess** the certificate onto the same stretch, one write per address;
3. run the evaluation over the region, exactly the EXPSPACE program's;
4. accept.

This file is that outer layer, with the evaluation abstract – its phase type
`PE`, its site family and its boundary rules are parameters, as in
`DescriptiveComplexity.Draw.outerRule` – and with the two sweeps' *writes*
abstract too, because what a cell of the file holds is a fact about the layout
the caller chose and not about the shape of the loop. The runs the two sweeps
discharge against are `DescriptiveComplexity.Draw.Prog.reachesIn_buildFile` and
`DescriptiveComplexity.Draw.Prog.reachesIn_guessTracks`.

## Why the guess is a shape and not a guard

Every other site here separates in-shape: from the guard and the phase, the rule
that fired is recoverable, which is what the backward reading of a run needs. The
guessing site does not, and must not – its shapes are the certificate's values at
one cell, all of them firing under the same guard. That is the whole
nondeterminism of the program, and `nexSep` states the separation for every other
site, which is what `DescriptiveComplexity.TMData.UniqueFrom` asks for.

## Why the two sweeps stop on the control and not on the tape

Both sweeps run right along a stretch whose ends are addresses, and a rule sees
only the control and the cell under the head. The cell cannot say where the
stretch ends – the tape is blank there, and blank is what the cells ahead hold
too – so the stop test is a predicate on the control: the pointer has passed the
file's top. It is the caller's, along with the write and the pointer's advance,
bundled as `SweepSpec`.

## Why the block is in the phase and the tuple in the control

A register is named by a block and a tuple, and only the tuple is made of
elements: the control holds elements, so the tuple lives there, and the block –
finite, and one of finitely many – lives in the **phase**, which is where finite
data belongs. That is why `NexPh.buildP` and `NexPh.guessP` carry a `B`.

A destination phase is a *constant*, not a function of the control, so a sweep
whose pointer rolls over into the next block cannot decide that in the stepping
rule: the roll-over is its own rule, guarded by the pointer holding the last
tuple of its block (`SweepSpec.Roll`). The last register of the file is written
by a third – `Roll ∧ Done` – which moves right like the others and lands in
`NexPh.buildDoneP`, one cell past the file, where a fourth turns the machine
round. The last register has to be *written*, and the writes happen on the
right-moving steps, which is why the turn-around is a phase of its own and not
the exit guard of the sweep. The three guards at `NexPh.buildP` are pairwise
disjoint by construction, which is what `nexSep` reads off.

The exit into the next sweep **resets the pointer** (`SweepSpec.st0`): the sweep
that just finished left it at the file's last register, and the next one starts
at the first.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The phases -/

/-- **The phases of the clocked program**: the two opening sweeps with a walk
home after each, the evaluation, and the accepting phase. -/
inductive NexPh (B PE : Type) : Type
  /-- The initial phase: mark the home cell and set off. -/
  | start : NexPh B PE
  /-- Walking up to the file's base, writing nothing. Where it stops is the
  program's choice: a machine has no landmark but the cell it started on
 , and the file has to be laid *above* the data. -/
  | approachP : NexPh B PE
  /-- Laying the register file out, in the block the phase names. -/
  | buildP : B → NexPh B PE
  /-- The file is laid: standing one cell past its last register. -/
  | buildDoneP : NexPh B PE
  /-- Walking home after the file is laid out. -/
  | homeBuildP : NexPh B PE
  /-- Guessing the certificate onto the region, in the block the phase names. -/
  | guessP : B → NexPh B PE
  /-- The certificate is guessed: standing one cell past the last register. -/
  | guessDoneP : NexPh B PE
  /-- Walking home after the guess. -/
  | homeGuessP : NexPh B PE
  /-- The accepting phase: no rule leaves it. -/
  | acceptP : NexPh B PE
  /-- A phase of the evaluation. -/
  | evalP : PE → NexPh B PE

instance {B PE : Type} [Finite B] [Finite PE] : Finite (NexPh B PE) :=
  Finite.of_injective
    (fun p => match p with
      | .start => (Sum.inl (Sum.inl 0) : (Fin 7 ⊕ (B ⊕ B)) ⊕ PE)
      | .approachP => Sum.inl (Sum.inl 6)
      | .buildP b => Sum.inl (Sum.inr (Sum.inl b))
      | .buildDoneP => Sum.inl (Sum.inl 1)
      | .homeBuildP => Sum.inl (Sum.inl 2)
      | .guessP b => Sum.inl (Sum.inr (Sum.inr b))
      | .guessDoneP => Sum.inl (Sum.inl 3)
      | .homeGuessP => Sum.inl (Sum.inl 4)
      | .acceptP => Sum.inl (Sum.inl 5)
      | .evalP e => Sum.inr e)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-! ### The sites -/

/-- **The call sites of the clocked program**, plus the evaluation's. -/
inductive NexSite (SE : Type) : Type
  /-- The initial step. -/
  | start : NexSite SE
  /-- The walk up to the file's base: like the guess, it does not separate
  in-shape, its stop being a choice. -/
  | approach : NexSite SE
  /-- The file-laying sweep. -/
  | build : NexSite SE
  /-- The walk home after it. -/
  | homeBuild : NexSite SE
  /-- The guessing sweep: the one site that does not separate in-shape. -/
  | guess : NexSite SE
  /-- The walk home after it. -/
  | homeGuess : NexSite SE
  /-- The accepting phase's site: no rules. -/
  | accept : NexSite SE
  /-- An evaluation site. -/
  | eval : SE → NexSite SE

instance {SE : Type} [Finite SE] : Finite (NexSite SE) :=
  Finite.of_injective
    (fun i => match i with
      | .start => (Sum.inl 0 : Fin 7 ⊕ SE)
      | .approach => Sum.inl 6
      | .build => Sum.inl 1
      | .homeBuild => Sum.inl 2
      | .guess => Sum.inl 3
      | .homeGuess => Sum.inl 4
      | .accept => Sum.inl 5
      | .eval e => Sum.inr e)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule shape of each site of the clocked program**: the sweep's step and
its exit, the walks' kit rules and their exits, and the guess's values `G`. -/
def NexSh (SE B G : Type) (ShE : SE → Type) : NexSite SE → Type
  | .start => Unit
  | .approach => Unit ⊕ Unit
  | .build => B ⊕ B ⊕ B ⊕ Unit
  | .homeBuild => HomeKit.HomeRule ⊕ Unit
  | .guess => (B × G) ⊕ (B × G) ⊕ (B × G) ⊕ Unit ⊕ B
  | .homeGuess => HomeKit.HomeRule ⊕ Unit
  | .accept => Empty
  | .eval e => ShE e

instance {SE B G : Type} {ShE : SE → Type} [Finite B] [Finite G] [∀ e, Finite (ShE e)]
    (i : NexSite SE) : Finite (NexSh SE B G ShE i) := by
  cases i <;> unfold NexSh <;> infer_instance

/-! ### What a sweep writes -/

/-- **One right-running sweep, from the rules' side**: what it writes at the cell
under the head, where it leaves the pointer, and when it is over.

The three are the caller's because they are facts about the layout, not about the
shape of the loop: the file-laying sweep writes the background of the file it is
building, the guessing sweep writes one value of the certificate, and both stop
when the pointer has passed the stretch's top. -/
structure SweepSpec (A Q W B : Type) where
  /-- The tracks the cell under the head is left holding, in this block. -/
  wr : B → (Q → A) → (W → A) → W → A
  /-- The pointer the rule leaves in the control, within a block. -/
  st : B → (Q → A) → (W → A) → Q → A
  /-- The pointer at the file's **first** register: what the exit into the next
  sweep leaves, since the sweep just finished left it at the last. -/
  st0 : (Q → A) → (W → A) → Q → A
  /-- The pointer it leaves when the tuple rolls over into the next block. -/
  stRoll : B → (Q → A) → (W → A) → Q → A
  /-- The next block. -/
  nx : B → B
  /-- The pointer holds the last tuple of the block: the step rolls over. A
  destination phase is a constant, so the roll-over is its own rule and this
  is what tells the two apart. -/
  Roll : B → (Q → A) → Prop
  /-- The pointer holds the last tuple of the last block: the sweep is over. -/
  Done : B → (Q → A) → Prop

/-- **One right-running sweep that guesses**: the same three, with the write and
the pointer's advance depending on the value `G` guessed at the cell. All of them
fire under one guard, which is what makes the phase a guess. -/
structure GuessSpec (A Q W B G : Type) where
  /-- The tracks the cell under the head is left holding, at this value. -/
  wr : B → G → (Q → A) → (W → A) → W → A
  /-- The pointer the rule leaves in the control, at this value. -/
  st : B → G → (Q → A) → (W → A) → Q → A
  /-- The pointer it leaves when the tuple rolls over into the next block. -/
  stRoll : B → G → (Q → A) → (W → A) → Q → A
  /-- The next block. -/
  nx : B → B
  /-- The pointer holds the last tuple of the block. -/
  Roll : B → (Q → A) → Prop
  /-- The pointer holds the last tuple of the last block. -/
  Done : B → (Q → A) → Prop

/-- **The phases from the guess's walk home onward.** The program's only
nondeterminism is at `NexPh.guessP`, and no rule returns there: from the walk
home after the guess the machine is deterministic, which is the shape
`DescriptiveComplexity.TMData.UniqueFrom` wants. -/
def NexPh.PostGuess {B PE : Type} : NexPh B PE → Prop
  | .guessDoneP => True
  | .homeGuessP => True
  | .acceptP => True
  | .evalP _ => True
  | _ => False

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A Q B G PE SE : Type}
variable [DecidableEq dt.SlotIx]
variable (one : A) {ShE : SE → Type}

/-- **The rules of the clocked program's outer layer**: the initial step, the two
sweeps at their specifications with their exits, the two walks home at their
kits, and the evaluation's rules as the parameter `ruleE`. -/
noncomputable def nexRule (β : SweepSpec A Q dt.SlotIx B) (γ : GuessSpec A Q dt.SlotIx B G)
    (ruleE : ∀ e : SE, ShE e → Rule A Q dt.SlotIx (NexPh B PE)) (evalEntry : PE) (bot : B) :
    ∀ i : NexSite SE, NexSh SE B G ShE i → Rule A Q dt.SlotIx (NexPh B PE)
  | .start, _ =>
    -- The marker *and* the bottom mark, both at the cell the head starts on:
    -- the evaluation's walks read the second one (`hbotSt`), and no later rule
    -- writes it.
    { guard := fun _ _ => True
      srcPh := .start
      dstPh := .approachP
      dstSt := fun f _ => f
      wr := fun _ g => Function.update (Function.update g .wk one) .bot one
      moveRight := True }
  | .approach, Sum.inl _ =>
    { guard := fun _ _ => True
      srcPh := .approachP
      dstPh := .approachP
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .approach, Sum.inr _ =>
    -- Stop walking here and start laying the file: where the base falls is the
    -- program's choice, like the guess's stop.
    { guard := fun _ _ => True
      srcPh := .approachP
      dstPh := .buildP bot
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .build, Sum.inl b =>
    { guard := fun f _ => ¬β.Roll b f
      srcPh := .buildP b
      dstPh := .buildP b
      dstSt := β.st b
      wr := β.wr b
      moveRight := True }
  | .build, Sum.inr (Sum.inl b) =>
    { guard := fun f _ => β.Roll b f ∧ ¬β.Done b f
      srcPh := .buildP b
      dstPh := .buildP (β.nx b)
      dstSt := β.stRoll b
      wr := β.wr b
      moveRight := True }
  | .build, Sum.inr (Sum.inr (Sum.inl b)) =>
    { guard := fun f _ => β.Roll b f ∧ β.Done b f
      srcPh := .buildP b
      dstPh := .buildDoneP
      dstSt := β.stRoll b
      wr := β.wr b
      moveRight := True }
  | .build, Sum.inr (Sum.inr (Sum.inr _)) =>
    { guard := fun _ _ => True
      srcPh := .buildDoneP
      dstPh := .homeBuildP
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .homeBuild, Sum.inl ρ =>
    (HomeKit.mk (A := A) (Q := Q) .mir .wk .homeBuildP).rule one ρ
  | .homeBuild, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .homeBuildP
      dstPh := .guessP bot
      dstSt := β.st0
      wr := fun _ g => g
      moveRight := True }
  | .guess, Sum.inl ⟨b, x⟩ =>
    { guard := fun f _ => ¬γ.Roll b f
      srcPh := .guessP b
      dstPh := .guessP b
      dstSt := γ.st b x
      wr := γ.wr b x
      moveRight := True }
  | .guess, Sum.inr (Sum.inl ⟨b, x⟩) =>
    { guard := fun f _ => γ.Roll b f ∧ ¬γ.Done b f
      srcPh := .guessP b
      dstPh := .guessP (γ.nx b)
      dstSt := γ.stRoll b x
      wr := γ.wr b x
      moveRight := True }
  | .guess, Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)) =>
    { guard := fun f _ => γ.Roll b f ∧ γ.Done b f
      srcPh := .guessP b
      dstPh := .guessDoneP
      dstSt := γ.stRoll b x
      wr := γ.wr b x
      moveRight := True }
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) =>
    { guard := fun _ _ => True
      srcPh := .guessDoneP
      dstPh := .homeGuessP
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr b))) =>
    -- Stop guessing here: the sweep over the region carries no pointer, so where
    -- it stops is one more nondeterministic choice.
    { guard := fun _ _ => True
      srcPh := .guessP b
      dstPh := .homeGuessP
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .homeGuess, Sum.inl ρ =>
    (HomeKit.mk (A := A) (Q := Q) .mir .wk .homeGuessP).rule one ρ
  | .homeGuess, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .homeGuessP
      dstPh := .evalP evalEntry
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .accept, e => e.elim
  | .eval e, ρ => ruleE e ρ

/-- **The owner of each phase**: the site whose copy of a phase it is; the
evaluation's phases are owned through the parameter. -/
def nexOwner (ownE : PE → SE) : NexPh B PE → NexSite SE
  | .start => .start
  | .approachP => .approach
  | .buildP _ => .build
  | .buildDoneP => .build
  | .homeBuildP => .homeBuild
  | .guessP _ => .guess
  | .guessDoneP => .guess
  | .homeGuessP => .homeGuess
  | .acceptP => .accept
  | .evalP p => .eval (ownE p)

variable {dt one} {β : SweepSpec A Q dt.SlotIx B} {γ : GuessSpec A Q dt.SlotIx B G}
variable {ruleE : ∀ e : SE, ShE e → Rule A Q dt.SlotIx (NexPh B PE)} {evalEntry : PE}
variable {bot : B} {ownE : PE → SE}

/-- **Every rule fires from a phase its site owns**, given that the evaluation's
do. This is the `howner` field of the program's
`DescriptiveComplexity.Draw.Assembly`. -/
theorem nexOwner_nexRule
    (hownE : ∀ (e : SE) (ρ : ShE e), nexOwner ownE (ruleE e ρ).srcPh = NexSite.eval e) :
    ∀ (i : NexSite SE) (ρ : NexSh SE B G ShE i),
      nexOwner ownE (dt.nexRule one β γ ruleE evalEntry bot i ρ).srcPh = i := by
  intro i ρ
  match i, ρ with
  | .start, _ => rfl
  | .approach, Sum.inl _ => rfl
  | .approach, Sum.inr _ => rfl
  | .build, Sum.inl _ => rfl
  | .build, Sum.inr (Sum.inl _) => rfl
  | .build, Sum.inr (Sum.inr (Sum.inl _)) => rfl
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => rfl
  | .homeBuild, Sum.inl _ => rfl
  | .homeBuild, Sum.inr _ => rfl
  | .guess, Sum.inl _ => rfl
  | .guess, Sum.inr (Sum.inl _) => rfl
  | .guess, Sum.inr (Sum.inr (Sum.inl _)) => rfl
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => rfl
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => rfl
  | .homeGuess, Sum.inl _ => rfl
  | .homeGuess, Sum.inr _ => rfl
  | .accept, e => exact e.elim
  | .eval e, ρ => exact hownE e ρ

/-- **Every site but the guess separates in-shape.** The two sweeps' steps are
told from their exits by the stop test, the walks home by their kits, and the
accepting site has no rules at all; the guessing site is left out because its
shapes are the certificate's values, all firing under one guard, which is the
program's only nondeterminism. -/
theorem nexSep
    (hsepE : ∀ (e : SE) (ρ ρ' : ShE e) (f : Q → A) (g : dt.SlotIx → A),
      (ruleE e ρ).guard f g → (ruleE e ρ').guard f g →
      (ruleE e ρ).srcPh = (ruleE e ρ').srcPh → ρ = ρ') :
    ∀ (i : NexSite SE), i ≠ .guess → i ≠ .approach →
      ∀ (ρ ρ' : NexSh SE B G ShE i) (f : Q → A) (g : dt.SlotIx → A),
        (dt.nexRule one β γ ruleE evalEntry bot i ρ).guard f g →
        (dt.nexRule one β γ ruleE evalEntry bot i ρ').guard f g →
        (dt.nexRule one β γ ruleE evalEntry bot i ρ).srcPh =
          (dt.nexRule one β γ ruleE evalEntry bot i ρ').srcPh → ρ = ρ' := by
  intro i hne hnea ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .start, (), () => rfl
  | .approach, _, _ => exact absurd rfl hnea
  | .build, Sum.inl b, Sum.inl b' =>
    exact congrArg Sum.inl (NexPh.buildP.inj hph)
  | .build, Sum.inr (Sum.inl b), Sum.inr (Sum.inl b') =>
    exact congrArg (Sum.inr ∘ Sum.inl) (NexPh.buildP.inj hph)
  | .build, Sum.inr (Sum.inr (Sum.inl b)), Sum.inr (Sum.inr (Sum.inl b')) =>
    exact congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) (NexPh.buildP.inj hph)
  | .build, Sum.inr (Sum.inr (Sum.inr _)), Sum.inr (Sum.inr (Sum.inr _)) => rfl
  | .build, Sum.inr (Sum.inr (Sum.inr _)), Sum.inl _ => exact nomatch hph
  | .build, Sum.inr (Sum.inr (Sum.inr _)), Sum.inr (Sum.inl _) => exact nomatch hph
  | .build, Sum.inr (Sum.inr (Sum.inr _)), Sum.inr (Sum.inr (Sum.inl _)) =>
    exact nomatch hph
  | .build, Sum.inl _, Sum.inr (Sum.inr (Sum.inr _)) => exact nomatch hph
  | .build, Sum.inr (Sum.inl _), Sum.inr (Sum.inr (Sum.inr _)) => exact nomatch hph
  | .build, Sum.inr (Sum.inr (Sum.inl _)), Sum.inr (Sum.inr (Sum.inr _)) =>
    exact nomatch hph
  | .build, Sum.inl b, Sum.inr (Sum.inl b') =>
    exact absurd (NexPh.buildP.inj hph ▸ hg'.1) hg
  | .build, Sum.inl b, Sum.inr (Sum.inr (Sum.inl b')) =>
    exact absurd (NexPh.buildP.inj hph ▸ hg'.1) hg
  | .build, Sum.inr (Sum.inl b), Sum.inl b' =>
    exact absurd (NexPh.buildP.inj hph ▸ hg.1) hg'
  | .build, Sum.inr (Sum.inr (Sum.inl b)), Sum.inl b' =>
    exact absurd (NexPh.buildP.inj hph ▸ hg.1) hg'
  | .build, Sum.inr (Sum.inl b), Sum.inr (Sum.inr (Sum.inl b')) =>
    exact absurd (NexPh.buildP.inj hph ▸ hg'.2) hg.2
  | .build, Sum.inr (Sum.inr (Sum.inl b)), Sum.inr (Sum.inl b') =>
    exact absurd (NexPh.buildP.inj hph ▸ hg.2) hg'.2
  | .homeBuild, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (HomeKit.sep _ one σ σ' f g hg hg' hph)
  | .homeBuild, Sum.inr _, Sum.inr _ => rfl
  | .homeBuild, Sum.inl σ, Sum.inr _ =>
    exact absurd hg'.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg hp)
  | .homeBuild, Sum.inr _, Sum.inl σ =>
    exact absurd hg.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg' hp)
  | .guess, _, _ => exact absurd rfl hne
  | .homeGuess, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (HomeKit.sep _ one σ σ' f g hg hg' hph)
  | .homeGuess, Sum.inr _, Sum.inr _ => rfl
  | .homeGuess, Sum.inl σ, Sum.inr _ =>
    exact absurd hg'.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg hp)
  | .homeGuess, Sum.inr _, Sum.inl σ =>
    exact absurd hg.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg' hp)
  | .accept, e, _ => exact e.elim
  | .eval e, ρ, ρ' => exact hsepE e ρ ρ' f g hg hg' hph

/-- **No rule leaves the post-guess phases**, given that the evaluation's do not.
With `nexSep_postGuess` this is what says the clocked program guesses once and is
deterministic ever after. -/
theorem postGuess_nexRule
    (hclosedE : ∀ (e : SE) (ρ : ShE e), NexPh.PostGuess (ruleE e ρ).dstPh) :
    ∀ (i : NexSite SE) (ρ : NexSh SE B G ShE i),
      NexPh.PostGuess (dt.nexRule one β γ ruleE evalEntry bot i ρ).srcPh →
        NexPh.PostGuess (dt.nexRule one β γ ruleE evalEntry bot i ρ).dstPh := by
  intro i ρ h
  match i, ρ with
  | .start, _ => exact h.elim
  | .approach, Sum.inl _ => exact h.elim
  | .approach, Sum.inr _ => exact h.elim
  | .build, Sum.inl _ => exact h.elim
  | .build, Sum.inr (Sum.inl _) => exact h.elim
  | .build, Sum.inr (Sum.inr (Sum.inl _)) => exact h.elim
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact h.elim
  | .homeBuild, Sum.inl σ => cases σ; exact h.elim
  | .homeBuild, Sum.inr _ => exact h.elim
  | .guess, Sum.inl _ => exact h.elim
  | .guess, Sum.inr (Sum.inl _) => exact h.elim
  | .guess, Sum.inr (Sum.inr (Sum.inl _)) => exact trivial
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact trivial
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => exact h.elim
  | .homeGuess, Sum.inl σ => cases σ; exact trivial
  | .homeGuess, Sum.inr _ => exact trivial
  | .accept, e => exact e.elim
  | .eval e, ρ => exact hclosedE e ρ

/-- **The clocked program separates in-shape at every phase it can be in after
the guess.** The guessing site is excluded by its phase, not by hand: its rules
fire from `NexPh.guessP` alone, which `postGuess_nexRule` shows unreachable from
there on. -/
theorem nexSep_postGuess
    (hsepE : ∀ (e : SE) (ρ ρ' : ShE e) (f : Q → A) (g : dt.SlotIx → A),
      (ruleE e ρ).guard f g → (ruleE e ρ').guard f g →
      (ruleE e ρ).srcPh = (ruleE e ρ').srcPh → ρ = ρ') :
    ∀ (i : NexSite SE) (ρ ρ' : NexSh SE B G ShE i) (f : Q → A) (g : dt.SlotIx → A),
      NexPh.PostGuess (dt.nexRule one β γ ruleE evalEntry bot i ρ).srcPh →
      (dt.nexRule one β γ ruleE evalEntry bot i ρ).guard f g →
      (dt.nexRule one β γ ruleE evalEntry bot i ρ').guard f g →
      (dt.nexRule one β γ ruleE evalEntry bot i ρ).srcPh =
        (dt.nexRule one β γ ruleE evalEntry bot i ρ').srcPh → ρ = ρ' := by
  intro i ρ ρ' f g hpost hg hg' hph
  by_cases hc : i = NexSite.guess
  · subst hc
    match ρ, hpost with
    | Sum.inl _, h => exact h.elim
    | Sum.inr (Sum.inl _), h => exact h.elim
    | Sum.inr (Sum.inr (Sum.inl _)), h => exact h.elim
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))), h => exact h.elim
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), _ =>
      match ρ' with
      | Sum.inl _ => exact nomatch hph
      | Sum.inr (Sum.inl _) => exact nomatch hph
      | Sum.inr (Sum.inr (Sum.inl _)) => exact nomatch hph
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => rfl
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => exact nomatch hph
  · by_cases hca : i = NexSite.approach
    · subst hca
      match ρ, hpost with
      | Sum.inl _, h => exact h.elim
      | Sum.inr _, h => exact h.elim
    · exact nexSep hsepE i hc hca ρ ρ' f g hg hg' hph


/-! ### The rules, discharged

Each phase of the outer layer, in the form its run asks for: a rightward or a
leftward rule with its six attributes. The two walks home are `HomeKit`'s, so
their own rules are `hrules` specialized and need nothing here. -/

section Discharge

variable {L : Language.{0, 0}} {dt : Data L} {A R' Q B PE SE G : Type}
variable [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable {ShE : SE → Type}
variable {PR : Prog A R' (NexPh B PE) Q dt.SlotIx dt.KIx dt.dd}
variable {β : SweepSpec A Q dt.SlotIx B} {γ : GuessSpec A Q dt.SlotIx B G}
variable {ruleE : ∀ e : SE, ShE e → Rule A Q dt.SlotIx (NexPh B PE)} {evalEntry : PE}
variable {bot : B}
variable {rEmb : ∀ i : NexSite SE, NexSh SE B G ShE i → R'}
variable (hrules : ∀ (i : NexSite SE) (ρ : NexSh SE B G ShE i),
  PR.rules (rEmb i ρ) = dt.nexRule PR.one β γ ruleE evalEntry bot i ρ)

include hrules

/-- **The opening step**: mark the home cell – the working marker and the
bottom mark alike – and set off for the file's base. -/
theorem hasRight_start (f : Q → A) (g : dt.SlotIx → A) :
    PR.HasRight NexPh.start f g NexPh.approachP f
      (Function.update (Function.update g Slot.wk PR.one) Slot.bot PR.one) := by
  refine ⟨rEmb .start (), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .start ()] <;> first | rfl | trivial

/-- **A step of the approach walk**: move on, writing nothing. -/
theorem hasRight_approach (f : Q → A) (g : dt.SlotIx → A) :
    PR.HasRight NexPh.approachP f g NexPh.approachP f g := by
  refine ⟨rEmb .approach (Sum.inl ()), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .approach (Sum.inl ())] <;> first | rfl | trivial

/-- **The approach's exit**: stop walking and start laying the file here. -/
theorem hasRight_approachExit (f : Q → A) (g : dt.SlotIx → A) :
    PR.HasRight NexPh.approachP f g (NexPh.buildP bot) f g := by
  refine ⟨rEmb .approach (Sum.inr ()), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .approach (Sum.inr ())] <;> first | rfl | trivial

/-- **The file-laying sweep's step**: write the cell, advance the pointer, move
on. -/
theorem hasRight_build (b : B) (f : Q → A) (g : dt.SlotIx → A) (hg : ¬β.Roll b f) :
    PR.HasRight (NexPh.buildP b) f g (NexPh.buildP b) (β.st b f g) (β.wr b f g) := by
  refine ⟨rEmb .build (Sum.inl b), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .build (Sum.inl b)] <;> first | exact hg | rfl | trivial

/-- **The file-laying sweep's roll-over**: the last tuple of a block is written
and the pointer opens the next one. -/
theorem hasRight_buildRoll (b : B) (f : Q → A) (g : dt.SlotIx → A)
    (hroll : β.Roll b f) (hg : ¬β.Done b f) :
    PR.HasRight (NexPh.buildP b) f g (NexPh.buildP (β.nx b))
      (β.stRoll b f g) (β.wr b f g) := by
  refine ⟨rEmb .build (Sum.inr (Sum.inl b)), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .build (Sum.inr (Sum.inl b))] <;>
      first | exact ⟨hroll, hg⟩ | rfl | trivial

/-- **The file-laying sweep's exit**: the pointer is past the file's top, so turn
round. -/
theorem hasRight_buildLast (b : B) (f : Q → A) (g : dt.SlotIx → A)
    (hroll : β.Roll b f) (hg : β.Done b f) :
    PR.HasRight (NexPh.buildP b) f g NexPh.buildDoneP (β.stRoll b f g)
      (β.wr b f g) := by
  refine ⟨rEmb .build (Sum.inr (Sum.inr (Sum.inl b))), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .build (Sum.inr (Sum.inr (Sum.inl b)))] <;>
      first | exact ⟨hroll, hg⟩ | rfl | trivial

/-- **The file-laying sweep's turn-around**: one cell past the last register,
the file laid, the machine turns back. -/
theorem hasLeft_buildExit (f : Q → A) (g : dt.SlotIx → A) :
    PR.HasLeft NexPh.buildDoneP f g NexPh.homeBuildP f g := by
  refine ⟨rEmb .build (Sum.inr (Sum.inr (Sum.inr ()))), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .build (Sum.inr (Sum.inr (Sum.inr ())))] <;>
      first | trivial | rfl | exact id

/-- **The exit of the walk home after the file**: at the marker, start
guessing. -/
theorem hasRight_homeBuildExit (f : Q → A) (g : dt.SlotIx → A)
    (hg : dt.exitG PR.one g) :
    PR.HasRight NexPh.homeBuildP f g (NexPh.guessP bot) (β.st0 f g) g := by
  refine ⟨rEmb .homeBuild (Sum.inr ()), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .homeBuild (Sum.inr ())] <;> first | exact hg | rfl | trivial

/-- **The guessing sweep's step, at one value**: every value fires under the same
guard, which is the program's whole nondeterminism. -/
theorem hasRight_guess (b : B) (x : G) (f : Q → A) (g : dt.SlotIx → A)
    (hg : ¬γ.Roll b f) :
    PR.HasRight (NexPh.guessP b) f g (NexPh.guessP b) (γ.st b x f g)
      (γ.wr b x f g) := by
  refine ⟨rEmb .guess (Sum.inl ⟨b, x⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .guess (Sum.inl ⟨b, x⟩)] <;> first | exact hg | rfl | trivial

/-- **The guessing sweep's roll-over, at one value.** -/
theorem hasRight_guessRoll (b : B) (x : G) (f : Q → A) (g : dt.SlotIx → A)
    (hroll : γ.Roll b f) (hg : ¬γ.Done b f) :
    PR.HasRight (NexPh.guessP b) f g (NexPh.guessP (γ.nx b)) (γ.stRoll b x f g)
      (γ.wr b x f g) := by
  refine ⟨rEmb .guess (Sum.inr (Sum.inl ⟨b, x⟩)), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .guess (Sum.inr (Sum.inl ⟨b, x⟩))] <;>
      first | exact ⟨hroll, hg⟩ | rfl | trivial

/-- **The guessing sweep's exit.** -/
theorem hasRight_guessLast (b : B) (x : G) (f : Q → A) (g : dt.SlotIx → A)
    (hroll : γ.Roll b f) (hg : γ.Done b f) :
    PR.HasRight (NexPh.guessP b) f g NexPh.guessDoneP (γ.stRoll b x f g)
      (γ.wr b x f g) := by
  refine ⟨rEmb .guess (Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩))), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .guess (Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)))] <;>
      first | exact ⟨hroll, hg⟩ | rfl | trivial

/-- **The guessing sweep's turn-around.** -/
theorem hasLeft_guessExit (f : Q → A) (g : dt.SlotIx → A) :
    PR.HasLeft NexPh.guessDoneP f g NexPh.homeGuessP f g := by
  refine ⟨rEmb .guess (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))), ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
    rw [hrules .guess (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))] <;>
      first | trivial | rfl | exact id

/-- **The guessing sweep stops here**: the rule that ends a region-wide guess,
available at every address, so where the walk stops is one more nondeterministic
choice and nothing has to recognize the region's end. -/
theorem hasLeft_guessStop (b : B) (f : Q → A) (g : dt.SlotIx → A) :
    PR.HasLeft (NexPh.guessP b) f g NexPh.homeGuessP f g := by
  refine ⟨rEmb .guess (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))), ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
    rw [hrules .guess (Sum.inr (Sum.inr (Sum.inr (Sum.inr b))))] <;>
      first | trivial | rfl | exact id

/-- **The exit of the walk home after the guess**: at the marker, enter the
evaluation. -/
theorem hasRight_homeGuessExit (f : Q → A) (g : dt.SlotIx → A)
    (hg : dt.exitG PR.one g) :
    PR.HasRight NexPh.homeGuessP f g (NexPh.evalP evalEntry) f g := by
  refine ⟨rEmb .homeGuess (Sum.inr ()), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hrules .homeGuess (Sum.inr ())] <;> first | exact hg | rfl | trivial

end Discharge


end Data

end Draw

end DescriptiveComplexity
