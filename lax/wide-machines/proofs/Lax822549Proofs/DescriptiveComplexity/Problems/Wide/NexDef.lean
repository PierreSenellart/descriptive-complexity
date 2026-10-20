/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawDefAsm
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawDefLoop
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawCtl
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawOrd
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexEval
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# The clocked program's rules are definable

A reduction has to *write its machine down*: the emitted table must be read off
the interpreted structure, which is what
`DescriptiveComplexity.Draw.Data.reads_progFrom` asks, and what it asks of the
rules is that each of them be first-order definable in the sense of
`DescriptiveComplexity.Draw.URulesDefinable`.

The clocked program shares its whole tower with the space-bounded one, so the
tower's definability (`DescriptiveComplexity.Draw.Data.uRulesDefinable_varRuleF`)
serves unchanged; what is new is the **spine**, whose checkpoints have two rules
instead of three, and the **outer layer**, whose sweeps are specifications
rather than kits. Both are here, and so are the program's own two
specifications: `uRulesDefinable_nexProg` is the whole clocked rule set, and
what a *reduction* still owes is its own `VarArgs`, the same obligation the
space-bounded one already meets.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### What the file's advance computes

The one thing a clocked program writes that is not a copy of a slot is its
sweep's **pointer**, and what it holds after a step is the next register's own
tuple. Below the last tuple of a block that is the tuple's lexicographic
successor, which is what the definability of the advance is read off. -/

section Advance

end Advance

namespace Data

variable {L : Language.{0, 0}} {dt : Data L} {Q : Type} [Fintype Q]

variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

/-! ### The clocked spine -/

omit [DecidableEq dt.SlotIx] in
/-- **The clocked evaluation's spine is definable**: one checkpoint per spine
position, with two rules each – the walk back to the marker, and the dispatch,
which goes into the position's machinery below the last checkpoint and out of
the evaluation at it. There is no third rule, the clocked evaluation running
once and leaving into whatever phase its caller names. -/
theorem uRulesDefinable_nexEvalRule {PM SM B : Type} {nv : ℕ} {ShM : SM → Type}
    {ruleM : ∀ (e : Env L) (s : SM), ShM s →
      Rule e.α Q dt.SlotIx (NexPh B (EvalPh nv PM))}
    {subEntry : Fin nv → PM} {exitPh : NexPh B (EvalPh nv PM)}
    (hM : URulesDefinable ruleM) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.nexEvalRule e.one (ruleM e) subEntry exitPh := by
  rintro (k | s) ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩
        (uGDefinable_trkOne (L := L) (Q := Q) (Slot.wk : dt.SlotIx)).not
        (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dsp =>
      by_cases hk : (k : ℕ) < nv
      · simp only [nexEvalRule, dif_pos hk]
        exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
          fun _ _ _ => rfl
      · simp only [nexEvalRule, dif_neg hk]
        exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
          fun _ _ _ => rfl
  · exact hM s ρ

omit [DecidableEq dt.SlotIx] in
/-- **The clocked evaluation's machineries are definable**: the same tower the
space-bounded program runs, one copy per spine position and the output's, at the
clocked program's own phases. -/
theorem uRulesDefinable_nexSmRule {B : Type}
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) (S := dt.SMF) (Sh := dt.SMSh) fun e =>
      dt.nexSmRule (B := B) e.zero e.one (args e) := by
  rintro (⟨j, s⟩ | s) ρ
  · exact uRulesDefinable_varRuleF
      (emb := fun p => (NexPh.evalP (.sub (Sum.inl ⟨j, p⟩)) :
        NexPh B (EvalPh dt.nv dt.PMF)))
      (exitPh := .evalP (.chk j.succ)) (h (dt.varAt j)) s ρ
  · exact uRulesDefinable_varRuleF
      (emb := fun p => (NexPh.evalP (.sub (Sum.inr p)) :
        NexPh B (EvalPh dt.nv dt.PMF)))
      (exitPh := .acceptP) (h none) s ρ

omit [DecidableEq dt.SlotIx] in
/-- **The clocked evaluation is definable**: its spine over those
machineries. -/
theorem uRulesDefinable_nexEvalRuleF {B : Type}
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) (S := dt.SEF) (Sh := dt.NexSESh) fun e =>
      dt.nexEvalRuleF (B := B) e.zero e.one (args e) :=
  uRulesDefinable_nexEvalRule (uRulesDefinable_nexSmRule h)

/-! ### The file-laying sweep's own definability

What `USweepSpecDef` asks of `DescriptiveComplexity.Draw.Data.buildSpec`, one
field at a time. The two tests are questions about the pointer's coordinates –
each is the greatest element, or the pointer is at the last register – and the
`st0` reset writes the least element into them. -/

section BuildSpec

end BuildSpec

/-! ### The outer layer

A clocked program's two sweeps are *specifications* rather than kits: what they
write at a cell, where they leave the pointer, and when they are over are the
caller's, so their definability is the caller's too. These are the two bundles,
and everything else in the outer layer – the opening step, the approach, the two
walks home and their exits, the guess's stop – is a constant rule with a guard
the toolkit already has. -/

/-- **What makes a file-laying sweep definable**: its write, its three pointers
and its two tests. The next block is a function of the phase alone, so nothing
is asked of it. -/
structure USweepSpecDef {B : Type} (β : ∀ e : Env L, SweepSpec e.α Q dt.SlotIx B) :
    Prop where
  /-- The tracks it leaves at the cell. -/
  wr : ∀ b : B, UTrDefinable fun e => (β e).wr b
  /-- The pointer it leaves within a block. -/
  st : ∀ b : B, UStDefinable fun e => (β e).st b
  /-- The pointer the exit resets to the file's first register. -/
  st0 : UStDefinable fun e => (β e).st0
  /-- The pointer it leaves at a roll-over. -/
  stRoll : ∀ b : B, UStDefinable fun e => (β e).stRoll b
  /-- The next block is chosen when the formula is built, not at the
  instance. -/
  nx : ∀ b : B, ∃ b' : B, ∀ e : Env L, (β e).nx b = b'
  /-- The roll-over test. -/
  roll : ∀ b : B, UGDefinable fun e f (_ : dt.SlotIx → e.α) => (β e).Roll b f
  /-- The stop test. -/
  done : ∀ b : B, UGDefinable fun e f (_ : dt.SlotIx → e.α) => (β e).Done b f

/-- **And what makes a guessing sweep definable**: the same, at each value it
may guess. -/
structure UGuessSpecDef {B G : Type}
    (γ : ∀ e : Env L, GuessSpec e.α Q dt.SlotIx B G) : Prop where
  /-- The tracks it leaves at the cell, at this value. -/
  wr : ∀ (b : B) (x : G), UTrDefinable fun e => (γ e).wr b x
  /-- The pointer it leaves, at this value. -/
  st : ∀ (b : B) (x : G), UStDefinable fun e => (γ e).st b x
  /-- The pointer it leaves at a roll-over. -/
  stRoll : ∀ (b : B) (x : G), UStDefinable fun e => (γ e).stRoll b x
  /-- The next block is chosen when the formula is built. -/
  nx : ∀ b : B, ∃ b' : B, ∀ e : Env L, (γ e).nx b = b'
  /-- The roll-over test. -/
  roll : ∀ b : B, UGDefinable fun e f (_ : dt.SlotIx → e.α) => (γ e).Roll b f
  /-- The stop test. -/
  done : ∀ b : B, UGDefinable fun e f (_ : dt.SlotIx → e.α) => (γ e).Done b f

omit [DecidableEq dt.SlotIx] in
/-- **The sweep that does nothing is definable**: every field is the identity or
a constant, and its two tests are `True` – which is what makes the phase a single
step. This is the specification a program that is *handed* its file puts where a
file-laying one puts `uSweepSpecDef_buildSpec`. -/
theorem uSweepSpecDef_nullSpec {B : Type} :
    USweepSpecDef (L := L) (Q := dt.CtlIx) (dt := dt)
      fun e => dt.nullSpec (A := e.α) B where
  wr _ := uTrDefinable_id
  st _ := uStDefinable_id
  st0 := uStDefinable_id
  stRoll _ := uStDefinable_id
  nx b := ⟨b, fun _ => rfl⟩
  roll _ := uGDefinable_true
  done _ := uGDefinable_true

omit [DecidableEq dt.SlotIx] in
/-- **What the guessing sweep writes is definable**: the stage tracks take the
guessed bit – a designated element, chosen when the formula is built, since the
value guessed is the rule's own shape – and every other slot keeps what it
held. -/
theorem uTrDefinable_guessWr (x : dt.d.B.ι → Bool) :
    UTrDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e _ g => dt.guessWr e.zero e.one x g := by
  intro sl
  match sl with
  | .old i =>
    exact uSlotDefinable_bitVal
      (uGDefinable_const (Q := dt.CtlIx) (W := dt.SlotIx) (x i = true))
  | .reg => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.reg
  | .regFirst => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.regFirst
  | .regLast => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.regLast
  | .blk c => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) (Slot.blk c)
  | .name j => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) (Slot.name j)
  | .pdd => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.pdd
  | .mir => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.mir
  | .tgt => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.tgt
  | .sav => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.sav
  | .val => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.val
  | .wk => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.wk
  | .bot => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.bot
  | .ltp => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.ltp
  | .new i => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) (Slot.new i)

omit [DecidableEq dt.SlotIx] in
/-- **The guessing sweep is definable**: it writes the guessed bit and moves no
pointer, so every field but the write is the identity or a constant. Its stop is
not a test at all – the sweep stops nondeterministically, which is why `Roll` is
always true and `Done` never. -/
theorem uGuessSpecDef_regionSpec :
    UGuessSpecDef (L := L) (Q := dt.CtlIx) (dt := dt)
      fun e => dt.regionSpec e.zero e.one where
  wr _ x := uTrDefinable_guessWr x
  st _ _ := uStDefinable_id (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  stRoll _ _ := uStDefinable_id (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  nx b := ⟨b, fun _ => rfl⟩
  roll _ := uGDefinable_true
  done _ := uGDefinable_false

/-- **The clocked program's outer layer is definable**: the opening step that
plants the two marks, the approach walk and its stop, the file-laying sweep at
its specification, the walk home and its turn, the guessing sweep at its own
specification and its stop, the second walk home, and the evaluation's rules as
the parameter. -/
theorem uRulesDefinable_nexRule {PE SE B G : Type} {ShE : SE → Type}
    {β : ∀ e : Env L, SweepSpec e.α Q dt.SlotIx B}
    {γ : ∀ e : Env L, GuessSpec e.α Q dt.SlotIx B G}
    {ruleE : ∀ (e : Env L) (s : SE), ShE s → Rule e.α Q dt.SlotIx (NexPh B PE)}
    {evalEntry : PE} {bot : B}
    (hβ : USweepSpecDef β) (hγ : UGuessSpecDef γ) (hE : URulesDefinable ruleE) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.nexRule e.one (β e) (γ e) (ruleE e) evalEntry bot := by
  rintro (- | - | - | - | - | - | - | s) ρ
  · exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      ((uTrDefinable_id.update Slot.wk uSlotDefinable_one).update Slot.bot
        uSlotDefinable_one)
  · match ρ with
    | Sum.inl _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl b =>
      exact ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial, (hβ.roll b).not, hβ.st b, hβ.wr b⟩
    | Sum.inr (Sum.inl b) =>
      obtain ⟨b', hb'⟩ := hβ.nx b
      exact ⟨⟨_, fun _ => rfl⟩, ⟨NexPh.buildP b', fun e => by
          change NexPh.buildP ((β e).nx b) = NexPh.buildP b'
          rw [hb']⟩,
        uRight_of_true fun _ => trivial, (hβ.roll b).and (hβ.done b).not,
        hβ.stRoll b, hβ.wr b⟩
    | Sum.inr (Sum.inr (Sum.inl b)) =>
      exact ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial, (hβ.roll b).and (hβ.done b),
        hβ.stRoll b, hβ.wr b⟩
    | Sum.inr (Sum.inr (Sum.inr _)) =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact HomeKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG hβ.st0
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl ⟨b, x⟩ =>
      exact ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial, (hγ.roll b).not, hγ.st b x, hγ.wr b x⟩
    | Sum.inr (Sum.inl ⟨b, x⟩) =>
      obtain ⟨b', hb'⟩ := hγ.nx b
      exact ⟨⟨_, fun _ => rfl⟩, ⟨NexPh.guessP b', fun e => by
          change NexPh.guessP ((γ e).nx b) = NexPh.guessP b'
          rw [hb']⟩,
        uRight_of_true fun _ => trivial, (hγ.roll b).and (hγ.done b).not,
        hγ.stRoll b x, hγ.wr b x⟩
    | Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)) =>
      exact ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial, (hγ.roll b).and (hγ.done b),
        hγ.stRoll b x, hγ.wr b x⟩
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact HomeKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · exact ρ.elim
  · exact hE s ρ

/-- **The clocked program's whole rule set is definable**: the outer layer
around the evaluation, at any two sweep specifications that are themselves
definable. -/
theorem uRulesDefinable_nexProgRule {B G : Type}
    {β : ∀ e : Env L, SweepSpec e.α Q dt.SlotIx B}
    {γ : ∀ e : Env L, GuessSpec e.α Q dt.SlotIx B G}
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    {bot : B}
    (hβ : USweepSpecDef β) (hγ : UGuessSpecDef γ)
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.nexRule e.one (β e) (γ e) (dt.nexEvalRuleF (B := B) e.zero e.one (args e))
        (.chk 0) bot :=
  uRulesDefinable_nexRule hβ hγ (uRulesDefinable_nexEvalRuleF h)

/-- **The rule set of a clocked program that is *handed* its file is definable,
and needs no coordinate map**: the sweep that would have laid the file is
`nullSpec`, whose definability is free, so nothing in the program asks for an
injective `Fin dd → CtlIx` – which is the map no wide machine's control can hold
(`DescriptiveComplexity.Draw.card_ctl_lt_card_univ`). This is the rule set a
reduction into `DescriptiveComplexity.WideRegAccept` emits. -/
theorem uRulesDefinable_nexProgHanded
    {args : ∀ (e : Env L) (v : dt.VarIx),
      dt.VarArgs (A := e.α) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := dt.CtlIx) fun e =>
      dt.nexRule e.one (dt.nullSpec (A := e.α) (Option dt.KIx))
        (dt.regionSpec e.zero e.one)
        (dt.nexEvalRuleF (B := Option dt.KIx) e.zero e.one (args e)) (.chk 0) bot :=
  uRulesDefinable_nexProgRule uSweepSpecDef_nullSpec uGuessSpecDef_regionSpec h

omit [DecidableEq dt.SlotIx] in
/-- **The clocked program's accepting predicate is definable**: the phase is
decided when the formula is built, and the bit it conjoins is the outermost
variable's verdict – the same field the space-bounded program accepts on. -/
theorem uGDefinable_nexAccept {B PE : Type}
    {args : ∀ (e : Env L) (v : dt.VarIx),
      dt.VarArgs (A := e.α) (Q := dt.CtlIx) v}
    (h : UVarArgsDef (Q := dt.CtlIx) none fun e => args e none)
    (p : NexPh B PE) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e f _ =>
      p = NexPh.acceptP ∧ (args e none).accBit f :=
  (uGDefinable_const (p = NexPh.acceptP)).and h.accBit

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


