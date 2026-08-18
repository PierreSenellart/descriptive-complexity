/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelProg
import DescriptiveComplexity.Problems.Wide.PadRules
import DescriptiveComplexity.Problems.Wide.RegChannelEntry

/-!
# The handed program, with room on its clock

`DescriptiveComplexity.Draw.DrawData.nexProgHanded` is the program a reduction
into `DescriptiveComplexity.WideRegAccept` emits, and its clock is `2 ^ |Tag|`
at its own rule names. The clock's one remaining obligation
(`clock_count_of_tags`) is that those names outnumber a constant of the kernel –
and a program may always have more of them, since a rule whose guard is `False`
changes nothing (`PadRules.lean`).

This file is that program: the same rules at the same sites, plus `n` sites
carrying a rule that never fires. Its record, its channel, its marks and its
phases are the originals – only the rule names are wider – so every constant the
clock is measured against is unchanged and the count goes up by `n`.
-/

namespace DescriptiveComplexity

namespace Draw

namespace DrawData

open FirstOrder

open Language Structure

section PadProg

variable {L : Language.{0, 0}} (dt : DrawData L) {A G : Type}
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable (zero one : A)

variable (G) in
/-- **The rule names of the padded program**: the clocked program's sites, and
`n` more carrying a rule that never fires. -/
abbrev NexRIxPad (n : ℕ) : Type :=
  DrawData.RTagOf (NexSite dt.SEF ⊕ Fin n)
    (padSh (NexSh dt.SEF (Option dt.KIx) G dt.NexSESh) n)

variable (G) in
/-- **The tags of the padded machine's universe**: the padded rule names, the
alphabet's, the phases and the argument blocks. -/
abbrev NexITagPad (n : ℕ) : Type :=
  dt.ITagOf (NexSite dt.SEF ⊕ Fin n)
    (padSh (NexSh dt.SEF (Option dt.KIx) G dt.NexSESh) n) dt.NexPF

omit [Fintype dt.SlotIx] [DecidableEq dt.SlotIx] [LinearOrder A] [Finite A]
  [Finite dt.KIx] [Nonempty A] in
/-- **What the padding buys, at this program's rule names**: one name per junk
site, and nothing else moves. -/
theorem card_nexRIxPad [Finite G] [Finite dt.KIx] [Finite dt.SEF]
    [∀ e : dt.SEF, Finite (dt.NexSESh e)] (n : ℕ) :
    Nat.card (dt.NexRIxPad (G := G) n) = Nat.card (dt.NexRIx (G := G)) + n :=
  card_rTagOf_pad (Sh := NexSh dt.SEF (Option dt.KIx) G dt.NexSESh) n

variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]

/-- **The handed program with `n` junk rule names**: the same program, its rule
names padded. -/
noncomputable def nexProgHandedPad (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
    (bot : Option dt.KIx) (n : ℕ)
    [LinearOrder (dt.NexRIxPad (G := G) n)] :
    Prog A (dt.NexRIxPad (G := G) n)
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      dt.CtlIx dt.SlotIx dt.KIx dt.dd where
  zero := zero
  one := one
  zero_ne_one := hzo
  payload_le := hpl
  rules r :=
    padRulesAt (dt := dt) (NexSh dt.SEF (Option dt.KIx) G dt.NexSESh)
      (fun i ρ => dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ
        (dt.nexEvalRuleF zero one args) (.chk 0) bot i ρ)
      NexPh.approachP n r.1 r.2
  startPh := .start
  startSt _ := zero
  accept := fun p f => p = .acceptP ∧ (args none).accBit f
  blank := fun _ => zero
  mark := regSlotMark zero one dt.dd0Le
  marked := fun x => (∃ k : dt.KIx, x.1 = DrawTag.arg k) ∨ IsTopNonArg x

variable {dt zero one}

variable [L.IsRelational] [L.Structure A] [Nonempty dt.KIx]

variable (dt) in
/-- **The padded program a clocked reduction emits**: `nexProgHanded` with `n`
junk rule names. -/
@[reducible] noncomputable def nexProgHandedPadAt (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) (bot : Option dt.KIx)
    (n : ℕ) [LinearOrder (dt.NexRIxPad (G := dt.d.B.ι → Bool) n)] :
    Prog A (dt.NexRIxPad (G := dt.d.B.ι → Bool) n)
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      dt.CtlIx dt.SlotIx dt.KIx dt.dd :=
  dt.nexProgHandedPad zero one hzo hpl (dt.regionSpec zero one)
    (fun w => dt.varArgsOf zero one w) bot n

/-! ### The interpretation, and that it reads the padded table -/

section Interp

variable {L : Language.{0, 0}} {dt : DrawData L}
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [Finite dt.KIx] [Nonempty dt.KIx]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable {args : ∀ (e : Env L) (v : dt.VarIx),
  dt.VarArgs (A := e.α) (Q := dt.CtlIx) v}

omit [Finite dt.KIx] [Nonempty dt.KIx] in
/-- **The padded program is the definability layer's**, at the padded rules. -/
theorem nexProgHandedPad_eq_progFrom (e : Env L)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (γ : GuessSpec e.α dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (arg : ∀ v : dt.VarIx, dt.VarArgs (A := e.α) (Q := dt.CtlIx) v)
    (bot : Option dt.KIx) (n : ℕ)
    [LinearOrder (dt.NexRIxPad (G := dt.d.B.ι → Bool) n)] :
    dt.nexProgHandedPad e.zero e.one e.hzo hpl γ arg bot n =
      dt.progFrom hpl e
        (padRulesAt (dt := dt)
          (NexSh dt.SEF (Option dt.KIx) (dt.d.B.ι → Bool) dt.NexSESh)
          (fun i ρ => dt.nexRule e.one (dt.nullSpec (Option dt.KIx)) γ
            (dt.nexEvalRuleF e.zero e.one arg) (.chk 0) bot i ρ)
          NexPh.approachP n)
        NexPh.start (fun p f => p = NexPh.acceptP ∧ (arg none).accBit f)
        (regFileMarkArg hpl) :=
  rfl

variable (dt) in
/-- **The padded machine, written down**: the interpretation whose universe is
tagged by the padded rule names – the clock's budget, widened by the junk sites
and by nothing else. -/
noncomputable def nexInterpHandedPad
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) (bot : Option dt.KIx)
    (n : ℕ)
    [LinearOrder (dt.NexRIxPad (G := dt.d.B.ι → Bool) n)] :
    FOInterpretation (L.sum Language.order) Language.wide
      (dt.ITagOf (NexSite dt.SEF ⊕ Fin n)
        (padSh (NexSh dt.SEF (Option dt.KIx) (dt.d.B.ι → Bool) dt.NexSESh) n)
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) dt.dd :=
  dt.drawInterp hpl
    (uRulesDefinable_padRules (uRulesDefinable_nexProgHanded (bot := bot) h)
      NexPh.approachP n)
    (uGDefinable_nexAccept (h none)) NexPh.start (regFileMarkArg hpl)

omit [Finite dt.KIx] [Nonempty dt.KIx] in
/-- **The interpreted structure reads the padded program's table**: the same
statement as at the unpadded program, at the wider rule names. -/
theorem reads_nexProgHandedPad
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v)
    (bot : Option dt.KIx) (n : ℕ) (e : Env L)
    [LinearOrder (dt.NexRIxPad (G := dt.d.B.ι → Bool) n)]
    [ws : Language.wide.Structure
      (Univ e.α (dt.NexRIxPad (G := dt.d.B.ι → Bool) n)
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
    (hws : ws = (dt.nexInterpHandedPad hpl h bot n).mapStructure e.α) :
    (dt.nexProgHandedPad e.zero e.one e.hzo hpl (dt.regionSpec e.zero e.one)
      (args e) bot n).table.Reads := by
  rw [nexProgHandedPad_eq_progFrom, ← padRules_eq_padRulesAt (dt := dt)
    (fun e => fun i ρ => dt.nexRule e.one (dt.nullSpec (Option dt.KIx))
      (dt.regionSpec e.zero e.one) (dt.nexEvalRuleF e.zero e.one (args e))
      (.chk 0) bot i ρ) NexPh.approachP n e]
  exact dt.reads_progFrom hpl
    (uRulesDefinable_padRules (uRulesDefinable_nexProgHanded (bot := bot) h)
      NexPh.approachP n)
    (uGDefinable_nexAccept (h none)) NexPh.start (regFileMarkArg hpl) e hws

/-! ### The padded program separates just as the program does -/

section Unique

variable {L : Language.{0, 0}} {dt : DrawData L} {A G : Type}
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable {zero one : A}

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] in
/-- **The padded program separates after its guess**: at the old rule names this
is `nexProgHanded_sep_rules`, and a junk name fires on nothing. -/
theorem nexProgHandedPad_sepOn (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} {n : ℕ}
    [LinearOrder (dt.NexRIxPad (G := G) n)]
    [LinearOrder (dt.NexRIx (G := G))] :
    (dt.nexProgHandedPad zero one hzo hpl γ args bot n).table.SepOn
      NexPh.PostGuess := by
  refine Prog.sepOn_of
    (PR := dt.nexProgHandedPad zero one hzo hpl γ args bot n) ?_
  rintro ⟨i, ρ⟩ ⟨i', ρ'⟩ f g hph0 hg hg' hph
  refine sep_padRulesAt (dt := dt) (Ph := NexPh.PostGuess)
    (fun i i' ρ ρ' f g hph0 hg hg' hph => ?_) i i' ρ ρ' f g hph0 hg hg' hph
  exact nexProgHanded_sep_rules (dt := dt) (zero := zero) (one := one)
    (G := G) hzo hpl (γ := γ) (args := args) (bot := bot)
    ⟨i, ρ⟩ ⟨i', ρ'⟩ f g hph0 hg hg' hph

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] in
/-- **No rule of the padded program fires from its accepting phase**: at an old
name that is `nexProgHanded_srcPh_ne_acceptP`, and a junk rule fires from the
start phase. -/
theorem nexProgHandedPad_srcPh_ne_acceptP (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} {n : ℕ}
    [LinearOrder (dt.NexRIxPad (G := G) n)] [LinearOrder (dt.NexRIx (G := G))]
    (r : dt.NexRIxPad (G := G) n) :
    ((dt.nexProgHandedPad zero one hzo hpl γ args bot n).table).srcPh r ≠
      NexPh.acceptP := by
  obtain ⟨i, ρ⟩ := r
  match i with
  | Sum.inl i =>
    exact nexProgHanded_srcPh_ne_acceptP (dt := dt) (zero := zero) (one := one)
      (G := G) hzo hpl (γ := γ) (args := args) (bot := bot) ⟨i, ρ⟩
  | Sum.inr k => exact fun hc => nomatch hc

variable {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
variable {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
variable {bot : Option dt.KIx}

/-! ### The marking's consequences, at any program with that channel -/

section Facts

variable {L : Language.{0, 0}} [L.IsRelational] {dt : DrawData L} {A R' : Type}
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx] [L.Structure A]
variable [LinearOrder A] [Finite A] [Nonempty A] [Nonempty dt.KIx] [Finite dt.KIx]
variable [LinearOrder R'] [Finite R']
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Language.wide.Structure (Univ A R'
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {zero : A}


/-! ### What a backward reading needs of the rules -/

variable (PR) in
/-- **The rules a program of this shape has**: at every rule name, either the
rule of a site of the clocked program, or a rule that never fires. That is all a
*backward* reading asks – it meets a rule by the name a step carries, not by the
site it was written at – and both the emitted program and the padded one answer
it, the second by its junk names. -/
def NexCovered {G : Type}
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
    (bot : Option dt.KIx) : Prop :=
  ∀ r : R', (∃ (i : NexSite dt.SEF) (ρ : NexSh dt.SEF (Option dt.KIx) G dt.NexSESh i),
      PR.rules r = dt.nexRule PR.one (dt.nullSpec (Option dt.KIx)) γ
        (dt.nexEvalRuleF PR.zero PR.one args) (.chk 0) bot i ρ) ∨
    ∃ p, PR.rules r = falseRule p ∧ p ≠ NexPh.start ∧ ¬NexPh.PostGuess p

omit [Nonempty dt.KIx] [L.IsRelational] [L.Structure A]
  [Nonempty A] [Finite A] [Finite dt.KIx] [LinearOrder R'] [Finite R']
  [Language.wide.Structure (Univ A R'
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **And so is the padded one**, its junk names carrying a rule that never
fires. -/
theorem nexCovered_nexProgHandedPad {G : Type} {one : A} (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) {n : ℕ}
    [LinearOrder (dt.NexRIxPad (G := G) n)]
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
    (bot : Option dt.KIx) :
    dt.NexCovered (dt.nexProgHandedPad zero one hzo hpl γ args bot n) γ args bot := by
  rintro ⟨i | k, ρ⟩
  · exact Or.inl ⟨i, ρ, rfl⟩
  · exact Or.inr ⟨NexPh.approachP, rfl, by rintro ⟨⟩, fun hc => hc⟩

omit [Nonempty dt.KIx] [L.IsRelational] [DecidableEq dt.SlotIx] [L.Structure A] in
/-- **What the marking, the order and the marker give the run**, at *any*
program whose channel writes for the argument elements and the one below them:
the seven facts the join asks about the channel and the file's ends. This is
This is the marking's seven consequences with the program abstracted, so that a
padded program
gets them by the same statement. -/
theorem regFacts_of_marked
    (hR : PR.table.Reads)
    (hmk : ∀ x : Univ A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd, PR.marked x ↔ ((∃ k, x.1 = DrawTag.arg k) ∨ IsTopNonArg x)) :
    (∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
        WMHasInp ((DrawTag.arg (toLex b), padTup (dt := dt) zero c) :
          Univ A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)) ∧
      (∀ z : Univ A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
        (∃ i : dt.KIx, z.1 = DrawTag.arg i) → WMHasInp z) ∧
      (∀ z w : Univ A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        dt.KIx dt.dd, WMLe z w → WMHasInp z → WMHasInp w) ∧
      ∃ botE : Univ A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        dt.KIx dt.dd,
        WMHasInp botE ∧
          (∀ z : Univ A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
            dt.KIx dt.dd, WMHasInp z → WMLe botE z) ∧
          (∀ i : dt.KIx, botE.1 ≠ DrawTag.arg i) := by
  refine ⟨fun b c => hasInp_blkElt hR hmk zero b c,
    fun z hz => hasInp_of_arg hR hmk hz,
    fun z w hzw hz => hasInp_up hR hmk hR.le z w hzw hz, ?_⟩
  obtain ⟨z, hz, hmin, hna⟩ := exists_regBotElt hR hmk hR.le
  exact ⟨z, hz, hmin, hna⟩

/-! ### What a reduction's program provides, in one record -/

variable (PR) in
/-- **The facts a clocked program of this shape provides**, collected: its rules
at the named sites, its channel's marks, its constants, its accepting predicate
and the separation its determinism is read off. Every layer of the run takes
this one hypothesis, and the two programs a reduction may emit – the plain one
and the padded one that buys the clock its room – provide it the same way, by
`rfl` at each field. -/
structure NexEmitted (bot : Option dt.KIx) where
  /-- The rule name of a site and a shape. -/
  site : ∀ i : NexSite dt.SEF,
    NexSh dt.SEF (Option dt.KIx) (dt.d.B.ι → Bool) dt.NexSESh i → R'
  /-- And the rule it names is the clocked one. -/
  rules_site : ∀ (i : NexSite dt.SEF)
      (ρ : NexSh dt.SEF (Option dt.KIx) (dt.d.B.ι → Bool) dt.NexSESh i),
    PR.rules (site i ρ) =
      dt.nexRule PR.one (dt.nullSpec (Option dt.KIx))
        (dt.regionSpec PR.zero PR.one)
        (dt.nexEvalRuleF PR.zero PR.one
          (fun w => dt.varArgsOf PR.zero PR.one w)) (.chk 0) bot i ρ
  /-- The rule name of a step of the walk home after the file is laid. -/
  homeBuild : HomeKit.HomeRule → R'
  /-- And it names that step. -/
  rules_homeBuild : ∀ ρ : HomeKit.HomeRule,
    PR.rules (homeBuild ρ) =
      (HomeKit.mk Slot.mir Slot.wk
        (NexPh.homeBuildP (B := Option dt.KIx)
          (PE := EvalPh dt.nv dt.PMF))).rule PR.one ρ
  /-- The rule name of a step of the walk home after the guess. -/
  homeGuess : HomeKit.HomeRule → R'
  /-- And it names that step. -/
  rules_homeGuess : ∀ ρ : HomeKit.HomeRule,
    PR.rules (homeGuess ρ) =
      (HomeKit.mk Slot.mir Slot.wk
        (NexPh.homeGuessP (B := Option dt.KIx)
          (PE := EvalPh dt.nv dt.PMF))).rule PR.one ρ
  /-- Every rule name carries a site's rule or one that never fires. -/
  covered : NexCovered PR (dt.regionSpec PR.zero PR.one)
    (fun w => dt.varArgsOf PR.zero PR.one w) bot
  /-- The mark the channel writes. -/
  mark : ∀ x, PR.mark x = regSlotMark PR.zero PR.one dt.dd0Le x
  /-- And who it writes for: the argument elements and the one below them. -/
  marked : ∀ x, PR.marked x ↔ ((∃ k, x.1 = DrawTag.arg k) ∨ IsTopNonArg x)
  /-- The tape is blank where the channel wrote nothing. -/
  blank : ∀ s, PR.blank s = PR.zero
  /-- The machine starts in the start phase … -/
  startPh : PR.startPh = NexPh.start
  /-- … with its control clear. -/
  startSt : PR.startSt = fun _ => PR.zero
  /-- It accepts in the accepting phase, at the output variable's bit. -/
  accept_iff : ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (f : dt.CtlIx → A),
    PR.accept p f ↔
      (p = NexPh.acceptP ∧ (dt.varArgsOf PR.zero PR.one (none : dt.VarIx)).accBit f)
  /-- Two rules firing on the same data after the guess are the same rule. -/
  sepOn : PR.table.SepOn NexPh.PostGuess
  /-- The post-guess phases are closed. -/
  dstPh_postGuess : ∀ r : R',
    NexPh.PostGuess (PR.table.srcPh r) → NexPh.PostGuess (PR.table.dstPh r)
  /-- And no rule fires from the accepting phase. -/
  srcPh_ne_acceptP : ∀ r : R', PR.table.srcPh r ≠ NexPh.acceptP

omit [Nonempty dt.KIx] in
/-- **The machine is deterministic after its guess**, at any program of this
shape: separation there, and the post-guess phases closed. -/
theorem NexEmitted.uniqueFrom {bot : Option dt.KIx} (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (cfg : Config (WPoint (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hcfg : ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      cfg.state = Sum.inr (stateElt PR.zero p f) → NexPh.PostGuess p) :
    (wideData (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).UniqueFrom cfg :=
  Table.uniqueFrom_of_sepOn hR hlin hE.sepOn hE.dstPh_postGuess hcfg

omit [Nonempty dt.KIx] [Finite dt.KIx] [Finite R']
  [Language.wide.Structure (Univ A R'
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **An accepting control is in the accepting phase.** -/
theorem NexEmitted.acceptPh {bot : Option dt.KIx} (hE : NexEmitted PR bot)
    (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (f : dt.CtlIx → A)
    (h : PR.accept p f) : p = NexPh.acceptP := ((hE.accept_iff p f).mp h).1

omit [Nonempty dt.KIx] [Finite dt.KIx] in
/-- **And so does the padded one**, its junk names never firing. -/
def nexEmitted_nexProgHandedPad {one : A} (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) {n : ℕ}
    [LinearOrder (dt.NexRIxPad (G := dt.d.B.ι → Bool) n)]
    [LinearOrder (dt.NexRIx (G := dt.d.B.ι → Bool))]
    (bot : Option dt.KIx) :
    NexEmitted (dt.nexProgHandedPad zero one hzo hpl (dt.regionSpec zero one)
      (fun w => dt.varArgsOf zero one w) bot n) bot where
  site i ρ := ⟨Sum.inl i, ρ⟩
  rules_site _ _ := rfl
  homeBuild ρ := ⟨Sum.inl .homeBuild, Sum.inl ρ⟩
  rules_homeBuild _ := rfl
  homeGuess ρ := ⟨Sum.inl .homeGuess, Sum.inl ρ⟩
  rules_homeGuess _ := rfl
  covered := nexCovered_nexProgHandedPad hzo hpl _ _ bot
  mark _ := rfl
  marked _ := Iff.rfl
  blank _ := rfl
  startPh := rfl
  startSt := rfl
  accept_iff _ _ := Iff.rfl
  sepOn := nexProgHandedPad_sepOn hzo hpl
  dstPh_postGuess r hsrc := by
    obtain ⟨i, ρ⟩ := r
    match i with
    | Sum.inl i =>
      exact postGuess_nexRule (dt := dt) (one := one)
        (β := dt.nullSpec (Option dt.KIx)) (γ := dt.regionSpec zero one)
        (ruleE := dt.nexEvalRuleF zero one (fun w => dt.varArgsOf zero one w))
        (evalEntry := .chk 0) (bot := bot)
        (nexEvalRuleF_postGuess _) i ρ hsrc
    | Sum.inr k => exact hsrc.elim
  srcPh_ne_acceptP := nexProgHandedPad_srcPh_ne_acceptP hzo hpl

/-! ### Determinism after the guess, at any program of this shape -/

omit [Nonempty dt.KIx] [L.IsRelational] [L.Structure A] [Nonempty A]
  [DecidableEq dt.SlotIx] [Finite A] [Finite dt.KIx] [Finite R'] in
/-- **The accepting phase is stuck**, at any program no rule fires from it. -/
theorem stuck_acceptP_of (hR : PR.table.Reads)
    (hne : ∀ r : R', PR.table.srcPh r ≠ NexPh.acceptP)
    {x : Config (WPoint (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    {f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A}
    (hx : x.state = Sum.inr (stateElt PR.zero NexPh.acceptP f)) :
    ∀ y, ¬(wideData (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step x y :=
  Table.stuck_of_srcPh hR (Ph := fun p => p = NexPh.acceptP)
    (fun _ => hne _) hx rfl

omit [Nonempty dt.KIx] [L.IsRelational] [L.Structure A] [Nonempty A]
  [DecidableEq dt.SlotIx] [Finite A] [Finite dt.KIx] [Finite R'] in
/-- **An accepting configuration is stuck**: it is in the accepting phase, and
no rule fires from there. -/
theorem stuck_of_acc_of (hR : PR.table.Reads)
    (hne : ∀ r : R', PR.table.srcPh r ≠ NexPh.acceptP)
    (haccPh : ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (f : dt.CtlIx → A), PR.accept p f → p = NexPh.acceptP)
    (e : Config (WPoint (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hacc : (wideData (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Acc e.state) :
    ∀ e', ¬(wideData (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step e e' := by
  classical
  rcases hst : e.state with s | q
  · rw [hst] at hacc; exact hacc.elim
  · rw [hst] at hacc
    have hIs : PR.table.IsAcc q := (hR.acc q).mp hacc
    obtain ⟨t, w⟩ := q
    match t with
    | .ctrl r => exact hIs.elim
    | .sym => exact hIs.elim
    | .arg i => exact hIs.elim
    | .phase p =>
      obtain ⟨hpad, hacc'⟩ := hIs
      have hph : p = NexPh.acceptP := haccPh _ _ hacc'
      subst hph
      refine stuck_acceptP_of hR hne
        (f := unpad PR.table.payload_le w) ?_
      rw [hst]
      exact congrArg Sum.inr (Prod.ext rfl (pad_unpad _ hpad).symm)

omit [Nonempty dt.KIx] [L.IsRelational] [L.Structure A] [Nonempty A]
  [DecidableEq dt.SlotIx] [Finite A] [Finite dt.KIx] [Finite R'] in
/-- **A configuration whose verdict is false accepts nothing below it**, at any
program that is deterministic after the guess: the run into the accepting phase
with the bit clear is a dead end that does not accept, and there is only one run.
What it reads of
it is uniqueness after the guess and the accepting phase's two facts. -/
theorem not_acc_of_verdict_false_of (hR : PR.table.Reads)
    (huniq : ∀ cfg : Config (WPoint (Univ A R'
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)),
      (∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
        cfg.state = Sum.inr (stateElt PR.zero p f) → NexPh.PostGuess p) →
      (wideData (Univ A R'
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).UniqueFrom cfg)
    (hne : ∀ r : R', PR.table.srcPh r ≠ NexPh.acceptP)
    (haccPh : ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (f : dt.CtlIx → A), PR.accept p f → p = NexPh.acceptP)
    {entry cT c : Config (WPoint (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (hentry : ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      entry.state = Sum.inr (stateElt PR.zero p f) → NexPh.PostGuess p)
    (hrun : Relation.ReflTransGen (wideData (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step entry cT)
    {fq : dt.CtlIx → A}
    (hstate : cT.state = Sum.inr (PR.stElt NexPh.acceptP fq))
    (hbit : ¬PR.accept NexPh.acceptP fq)
    (hreach : Relation.ReflTransGen (wideData (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step entry c)
    (hacc : (wideData (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Acc c.state) :
    False := by
  refine TMData.not_acc_of_reaches_dead_of_uniqueFrom (huniq entry hentry) hrun
    (stuck_acceptP_of hR hne hstate) (fun hc => ?_)
    (fun e he => stuck_of_acc_of hR hne haccPh e he) hreach hacc
  rw [hstate] at hc
  exact hbit (Prog.accept_of_isAcc (PR := PR) ((hR.acc _).mp hc))

/-! ### The opening, at any program with those rules -/

theorem reachesIn_openingReg (_hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {bot : Option dt.KIx}
    {rEmbS : ∀ i : NexSite dt.SEF,
      NexSh dt.SEF (Option dt.KIx) (dt.d.B.ι → Bool) dt.NexSESh i → R'}
    (hrulesS : ∀ (i : NexSite dt.SEF)
        (ρ : NexSh dt.SEF (Option dt.KIx) (dt.d.B.ι → Bool) dt.NexSESh i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one (dt.nullSpec (Option dt.KIx))
          (dt.regionSpec PR.zero PR.one)
          (dt.nexEvalRuleF PR.zero PR.one
            (fun w => dt.varArgsOf PR.zero PR.one w)) (.chk 0) bot i ρ)
    {rHomeB rHomeG : HomeKit.HomeRule → R'}
    (hrulesHB : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHomeB ρ) =
        (HomeKit.mk Slot.mir Slot.wk
          (NexPh.homeBuildP (B := Option dt.KIx)
            (PE := EvalPh dt.nv dt.PMF))).rule PR.one ρ)
    (hrulesHG : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHomeG ρ) =
        (HomeKit.mk Slot.mir Slot.wk
          (NexPh.homeGuessP (B := Option dt.KIx)
            (PE := EvalPh dt.nv dt.PMF))).rule PR.one ρ)
    (hmark : ∀ x, PR.mark x = regSlotMark PR.zero PR.one dt.dd0Le x)
    (hmk : ∀ x, PR.marked x ↔ ((∃ k, x.1 = DrawTag.arg k) ∨ IsTopNonArg x))
    (hblank : ∀ s, PR.blank s = PR.zero)
    (hstartPh : PR.startPh = NexPh.start) (hstartSt : PR.startSt = fun _ => PR.zero)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {v v₁ x y y' s₀ s₁ v' : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hvreg : ∀ z : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      ((∃ k, z.1 = DrawTag.arg k) ∨ IsTopNonArg z) → v ≠ wmRegSeg z)
    (hvi₁ : WMIncr WMLe v v₁) (hwalk : WMSetLe WMLe v₁ x) (hxy : WMIncr WMLe x y)
    (hyy' : WMIncr WMLe y y') (hyv : WMSetLe WMLe v y)
    (hvs₀ : WMIncr WMLe v s₀) (hle : WMSetLe WMLe s₀ s₁) (hne₁ : ∃ z, s₁ z)
    (hvv' : WMIncr WMLe v v')
    (hexB : dt.exitG PR.one (PR.passTracksAt
      (dt.regLaid hlin hord).cell Slot.mir
      (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le
        (dt.nexEntrySt v)) (fun _ => False) v))
    (σ : dt.d.B.ι →
      (Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) → Prop)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r s₁ → ¬σ i r)
    (hexG : dt.exitG PR.one (PR.passTracksAt
      (dt.regLaid hlin hord).cell Slot.mir
      (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le
        { dt.nexEntrySt v with old := σ }) (fun _ => False) v)) :
    (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      ((wideRank x - wideRank v₁) + (wideRank y - wideRank v) +
        ((wideRank s₁ - wideRank s₀) + (wideRank s₁ - wideRank v)) + 7)
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt),
        Sum.inl v,
        wideTape (PR.trackTapeAt
          (dt.regLaid hlin hord).cell Slot.mir
          PR.initBackReg (fun _ => False))
          (PR.syElt
            PR.blank)⟩
      ⟨Sum.inr (PR.stElt
          (NexPh.evalP (.chk 0)) (fun _ => PR.zero)),
        Sum.inl v',
        wideTape (PR.trackTapeAt
          (dt.regLaid hlin hord).cell Slot.mir
          (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le
            { dt.nexEntrySt v with old := σ }) (fun _ => False))
          (PR.syElt
            PR.blank)⟩ := by
  rw [hstartPh, hstartSt]
  have hbk : dt.startBack PR.initBackReg PR.one v =
      dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le
        (dt.nexEntrySt v) :=
    dt.startBack_initBackReg hlin hord hR hmark hmk hblank
      (fun z hz => hvreg z ((hmk z).mp hz))
  rw [← hbk] at hexB
  exact dt.reachesIn_openingHanded (F := dt.regLaid hlin hord)
    (PR := PR) (betaS := dt.nullSpec (Option dt.KIx))
    (ruleE := dt.nexEvalRuleF PR.zero PR.one
      (fun w => dt.varArgsOf PR.zero PR.one w))
    (evalEntry := .chk 0) (botS := bot)
    hR hlin (st := dt.nexEntrySt v) rfl hvi₁ hwalk hxy hyy' hyv hvs₀ hle hne₁ hvv'
    (bg := PR.initBackReg)
    (bg₀ := dt.startBack PR.initBackReg PR.one v)
    (fun _ hr => dt.startBack_frame hr)
    (dt.startBack_wr (dt.regLaid hlin hord).cell v) hbk
    (fun _ => PR.zero) trivial trivial rfl rfl hexB σ
    (fun i r hr => ⟨fun hc => absurd hc (hout i r hr), fun hc => hc.elim⟩) hexG
    (rEmbS := rEmbS) hrulesS (rHomeB := rHomeB) hrulesHB
    (rHomeG := rHomeG) hrulesHG


end Facts

end Unique

end Interp

end PadProg

end DrawData

end Draw

end DescriptiveComplexity
