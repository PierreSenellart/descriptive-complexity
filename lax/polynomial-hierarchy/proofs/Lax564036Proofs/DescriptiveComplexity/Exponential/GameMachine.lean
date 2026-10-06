/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Exponential.GameCtrl
import Lax564036Proofs.DescriptiveComplexity.MachinesAlt
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Walk
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax799700.Common
end Lax799700.Common

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMData)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd MinPos SuccPos TMData)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax799700.Common (bitRank)
end Lax564036Proofs.DescriptiveComplexity

/-!
# The machine of a second-order game

The alternating machine emitted by `SO-GAME ≤ʳᶠᵒ[≤] ATMAcceptSpace`, assembled
on the tape of `DescriptiveComplexity.Exponential.GameTape` with the phases of
`DescriptiveComplexity.Exponential.GameCtrl`.

## The shape of a transition

A transition is an *element* of the emitted universe, so it carries a tag and a
tuple. The tag is `DescriptiveComplexity.TrTag`: the phase it applies in, the
phase it moves to, the symbol it reads, the symbol it writes, and its
direction. The tuple carries, in one piece,

```
  coordinates 0 … V-1        the valuation of the question's variables
  coordinates V … V+a-1      the address of the cell the symbol sits in
```

which is what makes every relation of
`DescriptiveComplexity.TMData` first-order and uniform:

* `Src` and `Dst` read the valuation, each **up to the arity its own phase
  declares** – so a step of the prefix, whose destination declares one more
  variable than its source, writes exactly one coordinate, and the existential
  quantification over transitions *is* the quantification over the value
  written;
* `Read` and `Write` read the address, and a symbol shape together with an
  address is a point (`DescriptiveComplexity.symPt`).

Everything specific to the machine is therefore confined to one predicate, the
**rule** `DescriptiveComplexity.TrTag → (Fin dim → A) → Prop` saying which
tagged transitions are real. This file takes it as a parameter and proves what
does not depend on it: the two promises `ATMAcceptSpace` folds into its
yes-instances.

## The two promises are rule-independent

`DescriptiveComplexity.TMData.WellFormed` and
`DescriptiveComplexity.ATMData.BlocksSplit` are proved here once and for all
(`DescriptiveComplexity.gameMachine_wellFormed`,
`DescriptiveComplexity.gameMachine_blocksSplit`), because neither mentions the
transitions: the first is about the order, the positions, the input and the
blank – all fixed by the layout – and the second is about the marks, which are
`DescriptiveComplexity.MachPh.IsUniv` read off the phase.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-! ### Symbols, as a shape and an address -/

/-- **The shape of a symbol**: a sentinel's mark, or a cell's bit together with
the region and relation variable of the cell it sits in. The address itself is
carried by the transition's tuple, not by the shape. -/
inductive SymTag (B : Lax904597.SecondOrder.SOBlock) : Type
  /-- A sentinel's mark. -/
  | mark (b : Bool)
  /-- The bit `b` in a cell of region `r` holding the relation variable `i`. -/
  | val (b r : Bool) (i : B.ι)

namespace SymTag

variable {B : Lax904597.SecondOrder.SOBlock}

/-- The symbol shapes as a sum, for the `Finite` instance. -/
def equivSum : SymTag B ≃ Bool ⊕ (Bool × Bool × B.ι) where
  toFun
    | .mark b => .inl b
    | .val b r i => .inr (b, r, i)
  invFun
    | .inl b => .mark b
    | .inr (b, r, i) => .val b r i
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _, _⟩ <;> rfl

instance : Finite (SymTag B) := Finite.of_equiv _ equivSum.symm

end SymTag

/-! ### The dimension, and the two halves of a tuple -/

variable (B : Lax904597.SecondOrder.SOBlock) in
/-- The dimension of the emitted universe: room for the valuation of a
question's variables, and for the address of a cell. -/
noncomputable def gameDim (V : ℕ) : ℕ := V + blockArityBound B

section Address

variable {B : Lax904597.SecondOrder.SOBlock} {V : ℕ} {A : Type}

/-- The address half of a transition's tuple. -/
noncomputable def addrOf (w : Fin (gameDim B V) → A) : Fin (blockArityBound B) → A :=
  fun l => w ⟨V + (l : ℕ), by have := l.isLt; simp only [gameDim]; omega⟩

/-- The address a symbol shape reads, truncated to the arity of its relation
variable. -/
noncomputable def argsOf (i : B.ι) (ā : Fin (blockArityBound B) → A) : Fin (B.arity i) → A :=
  fun l => ā (Fin.castLE (arity_le_blockArityBound B i) l)

variable [LinearOrder A] (a₀ : A)

/-- **A symbol shape at an address is a point.** -/
noncomputable def gameSymPt {C : Type} (s : SymTag B) (ā : Fin (blockArityBound B) → A) :
    Pt B C (gameDim B V) A :=
  match s with
  | .mark b => markPt a₀ b
  | .val b r i => valPt a₀ b r i (argsOf i ā)

end Address

/-! ### The tags of the machine -/

/-- **The tag of a transition**: where it applies, where it goes, what it reads
and writes, and which way it moves. -/
structure TrTag (B : Lax904597.SecondOrder.SOBlock) (V M : ℕ) : Type where
  /-- The phase the transition applies in. -/
  src : MachPh V M
  /-- The phase it moves to. -/
  dst : MachPh V M
  /-- The symbol it reads. -/
  rd : SymTag B
  /-- The symbol it writes. -/
  wr : SymTag B
  /-- Whether it moves the head right. -/
  right : Bool

namespace TrTag

variable {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ}

/-- A transition tag as a tuple, for the `Finite` instance. -/
def toProd (t : TrTag B V M) : MachPh V M × MachPh V M × SymTag B × SymTag B × Bool :=
  (t.src, t.dst, t.rd, t.wr, t.right)

theorem toProd_injective : Function.Injective (toProd (B := B) (V := V) (M := M)) := by
  intro a b h
  simp only [toProd, Prod.mk.injEq] at h
  cases a; cases b
  simp_all

instance : Finite (TrTag B V M) := Finite.of_injective _ toProd_injective

end TrTag

/-- **The control's tags**: the phases, which are the states, and the rules,
which are the transitions. -/
abbrev GameCtrlTag (B : Lax904597.SecondOrder.SOBlock) (V M : ℕ) : Type := MachPh V M ⊕ TrTag B V M

/-- The coordinates a control tag uses: a phase declares its own, a transition
uses the whole tuple. -/
noncomputable def ctrlArity (vars : GameQuestion → ℕ) {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ} :
    GameCtrlTag B V M → ℕ :=
  Sum.elim (MachPh.arity vars) fun _ => gameDim B V

/-! ### The machine -/

section Machine

variable {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  (vars : GameQuestion → ℕ) (pol : GameQuestion → ℕ → Bool) (a₀ : A)

/-- A point of the emitted universe. -/
abbrev GamePt (B : Lax904597.SecondOrder.SOBlock) (V M : ℕ) (A : Type) : Type :=
  Pt B (GameCtrlTag B V M) (gameDim B V) A

/-- The point of a phase, at a given valuation. -/
noncomputable def phasePt (p : MachPh V M) (w : Fin (gameDim B V) → A) : GamePt B V M A :=
  (Sum.inr (Sum.inl p), w)

/-- A state belongs to the universal player exactly when its phase does. -/
noncomputable def isUnivPt (p : GamePt B V M A) : Prop :=
  match p.1 with
  | Sum.inr (Sum.inl ph) => MachPh.IsUniv pol ph = true
  | _ => False

variable (V M) in
/-- The state the machine starts in: the initial sweep, writing region `0`. -/
def startPh : MachPh V M := MachPh.sweepPh false false .start false

/-- **The machine of a second-order game**, with its rules as a parameter. -/
noncomputable def gameMachine (hdim : blockArityBound B ≤ gameDim B V)
    (rule : TrTag B V M → (Fin (gameDim B V) → A) → Prop) :
    Lax564036.AlternatingMachines.ATMData (GamePt B V M A) :=
  letI := machTagOrder (B := B) (C := GameCtrlTag B V M)
  { Posn p := machPosn p ∧ machDom (ctrlArity vars) p
    Le := tagTupleLe
    Tr p := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧ rule t p.2
    Start p := p = phasePt (startPh V M) fun _ => a₀
    Acc p := ∃ ph : MachPh V M, p.1 = Sum.inr (Sum.inl ph) ∧ ph.kind = .acc
    Blank p := p = markPt a₀ false
    Right p := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧ t.right = true
    Src p q := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧
      q.1 = Sum.inr (Sum.inl t.src) ∧ Canon (MachPh.arity vars t.src) q.2 ∧
        Agree (MachPh.arity vars t.src) p.2 q.2
    Read p x := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧ x = gameSymPt a₀ t.rd (addrOf p.2)
    Dst p q := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧
      q.1 = Sum.inr (Sum.inl t.dst) ∧ Canon (MachPh.arity vars t.dst) q.2 ∧
        Agree (MachPh.arity vars t.dst) p.2 q.2
    Write p x := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧ x = gameSymPt a₀ t.wr (addrOf p.2)
    Inp := machInp a₀ hdim
    Blk j p := (j = 1 ∧ isUnivPt pol p) ∨ (j = 0 ∧ ¬ isUnivPt pol p) }

/-! ### The two promises -/

variable {vars pol a₀}

/-! ### The two ends, and what a position is -/

/-! ### The rules -/

variable (vars natoms : GameQuestion → ℕ)

/-- **The rules of the machine**, all nine families.

Two of them are still parameters, and for the same reason the rules themselves
were one: they are the only places where the machine consults the *source
structure* rather than its own tape.

* `concOk` is the guard of a concluding transition – the residual formula of
  `DescriptiveComplexity.QuestionData`, which mentions no block atom and is
  therefore a first-order condition on the valuation;
* `isTarget` is the test a seek makes at a cell: is the symbol I am reading the
  one the challenged atom addresses, carrying the bit that was claimed? Both
  the address and the claim come from the phase and the tuple.

The control's own steps (family A) are `DescriptiveComplexity.MachPh.CtrlStep`,
which is `False` at every walk phase, so no family overlaps another except
where the design means it to: family C at a cell of the swept region, where the
two choices of the written bit are the guess. -/
def gameRule (concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop)
    (isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop)
    (t : TrTag B V M) (w : Fin (gameDim B V) → A) : Prop :=
  -- (A) a tape-free step of the control, bouncing on the left sentinels
  (t.rd = .mark false ∧ t.wr = .mark false ∧ t.right = !t.src.par ∧
      MachPh.CtrlStep vars natoms t.src t.dst ∧ (t.src.kind = .conc → concOk t.src w)) ∨
  -- (B) a sweep crossing the left sentinels
  (t.src.kind = .sweep ∧ t.dst = t.src ∧ t.rd = .mark false ∧ t.wr = .mark false ∧
      t.right = true) ∨
  -- (C) a sweep at a cell: guess in the swept region, copy back elsewhere
  (t.src.kind = .sweep ∧ t.dst = t.src ∧ t.right = true ∧
      ∃ (b b' rr : Bool) (i : B.ι), t.rd = .val b rr i ∧ t.wr = .val b' rr i ∧
        (rr = t.src.tgt ∨ b' = b)) ∨
  -- (D) a sweep at the right sentinel, handing over to its rewind
  (t.src.kind = .sweep ∧ t.dst = MachPh.rewindPh t.src.r t.src.tgt t.src.cont false ∧
      t.rd = .mark true ∧ t.wr = .mark true ∧ t.right = false) ∨
  -- (E) a rewind at a cell, which changes nothing
  (t.src.kind = .rewind ∧ t.dst = t.src ∧ t.rd = t.wr ∧ t.right = false ∧
      ∃ (b rr : Bool) (i : B.ι), t.rd = .val b rr i) ∨
  -- (F) a rewind at the left sentinel, handing over to its continuation
  (t.src.kind = .rewind ∧ t.dst = MachPh.rewindTarget t.src ∧
      t.rd = .mark false ∧ t.wr = .mark false ∧ t.right = false) ∨
  -- (G) a seek crossing the left sentinels
  (t.src.kind = .seek ∧ t.dst = t.src ∧ t.rd = .mark false ∧ t.wr = .mark false ∧
      t.right = true) ∨
  -- (H) a seek at a cell that is not the one it is looking for
  (t.src.kind = .seek ∧ t.dst = t.src ∧ t.rd = t.wr ∧ t.right = true ∧
      (∃ (b rr : Bool) (i : B.ι), t.rd = .val b rr i) ∧ ¬ isTarget t.src t.rd w) ∨
  -- (I) a seek at the cell it is looking for, carrying the bit that was claimed
  (t.src.kind = .seek ∧ t.dst = MachPh.accPh false ∧ t.rd = t.wr ∧ t.right = true ∧
      isTarget t.src t.rd w)

end Machine

/-! ### The machine of a specification -/

namespace GameProg

end GameProg

/-! ### Reading a step off its transition -/

section Step

end Step

/-! ### Building one step -/

section Build

end Build

/-! ### What a walk may do -/

section Cases

end Cases

/-! ### The two steps of a sweep -/

section Sweep

variable {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  {vars : GameQuestion → ℕ} {natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {r tgt : Bool} {cont : SweepCont} {par : Bool}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

end Sweep

/-! ### A walk along the positions

The induction the three walks run on, stated for an arbitrary machine: each
step moves the head to the neighboring position and preserves an invariant, so
the walk reaches the end of the tape. The measure is
`DescriptiveComplexity.bitRank`, which increases by one along
`DescriptiveComplexity.SuccPos`
(`DescriptiveComplexity.bitRank_succPos`) and is bounded by the number of
positions (`DescriptiveComplexity.bitRank_lt_card`), so nothing here depends on
*which* position follows which – the successor is whatever the step produces.
That is the payoff of §2.1a: a walk needs no address of its own. -/

section Walk

/-! ### What a walk has already passed

A walk's invariant has to say *what it has already rewritten*, and the only
handle on that is the order: the cells strictly below the head. The two facts
below are all it needs, and neither mentions the tape's layout – so the sweep's
invariant never has to compare two cells, and the order on cells
(`cellPt r i ā` against `cellPt r' i' ā'`) does not have to be characterized at
all. -/

section Below

end Below

end Walk

/-! ### The control's own step -/

section Ctrl

variable {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

end Ctrl

/-! ### The run of a sweep -/

section SweepRun

variable {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] [Finite A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {r tgt : Bool} {cont : SweepCont} {par : Bool}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

end SweepRun

/-! ### The run of a rewind

A rewind changes nothing – both its rules write back what they read – so its
invariant is about the *state*, not the tape. Unlike a sweep it does not end in
the phase it began: its last step, at the second left sentinel, both moves to
the lowest position and hands over to
`DescriptiveComplexity.MachPh.rewindTarget`. So the invariant it runs on is

```
(the tape is unchanged) ∧ (the head is not the right sentinel) ∧
  (the state is the rewind, or it is the target and the head is lowest)
```

and closing it needs the two order facts of the layout: the two left sentinels
are adjacent (`DescriptiveComplexity.succPos_leftPt`), so the handover really
does land on the lowest position; and a cell is never next to the first
sentinel (`DescriptiveComplexity.succPos_ne_leftPt`), so the walk cannot
reach the lowest position without reading the mark first. -/

section Rewind

variable {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] [Finite A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {r tgt : Bool} {cont : SweepCont} {par : Bool}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

end Rewind

/-! ### The run of a seek

A seek walks right, writing back everything it reads, and stops at the cell
whose symbol answers its test – the address *and* the claimed bit, which is why
a wrong claim is not a stop. It therefore either meets its cell and accepts, or
runs off the tape and, having no rule at the right sentinel, is stuck. Since a
seek is an existential phase, that is a loss: **asking an unprovable question
costs the player who asked.** -/

section Seek

variable {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] [Finite A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {ph : MachPh V M} {v : Fin (gameDim B V) → A}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

end Seek

end Lax564036Proofs.DescriptiveComplexity


