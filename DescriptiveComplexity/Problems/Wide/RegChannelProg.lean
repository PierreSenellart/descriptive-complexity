/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelLaid
import DescriptiveComplexity.Problems.Wide.NexInterp
import DescriptiveComplexity.Problems.Wide.RegChannelInit
import DescriptiveComplexity.Problems.Wide.NexRun

/-!
# The clocked program of a reduction into the register channel

`DescriptiveComplexity.Draw.DrawData.nexProg` is the clocked program of a
reduction that *lays* its own file: it carries a coordinate map, and the sweep
that lays the file carries a pointer as wide as an address – which no wide
machine's control can hold (`DescriptiveComplexity.Problems.Wide.Limits`).

This file is the program of a reduction into
`DescriptiveComplexity.WideRegAccept`, which is *handed* its file. It is the
same program with two changes, and both remove something:

* the file-laying sweep is `nullSpec`, so there is no pointer and **no
  coordinate map** – the phase is two steps and writes nothing;
* the channel writes for the argument elements and for one element below them
  (`regFileMarkArg`), which is what puts the file inside the working region and
  directly above it – and the mark it writes is `regSlotMark`, whose `regFirst`
  slot names that element rather than the least of the universe.

Everything else – the guess, the walks home, the evaluation, the accepting
predicate – is `nexProg`'s own, so its definability, its separation and its runs
serve unchanged.

What is here is the program, the two legs of a clocked run packaged as a
yes-instance (`wideRegAccept_of_legs`, at an arbitrary program), and the
rule-level facts a determinism argument is built from: separation after the
guess and the accepting phase no rule fires from.
-/

namespace DescriptiveComplexity

namespace Draw

namespace DrawData

open FirstOrder

open Language Structure

section HandedProg

variable {L : Language.{0, 0}} (dt : DrawData L) {A G : Type}
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable (zero one : A)
variable [LinearOrder (dt.NexRIx (G := G))]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]

/-- **The clocked program of a reduction into the register channel**: the outer
layer at the sweep that lays nothing and the region-guessing one, over the
shared tower's evaluation, with the input written on the argument elements'
file. Its pointer starts clear – there is no file-laying pointer to set – and
its channel writes for the argument elements alone. -/
noncomputable def nexProgHanded (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
    (bot : Option dt.KIx) :
    Prog A (dt.NexRIx (G := G)) (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      dt.CtlIx dt.SlotIx dt.KIx dt.dd where
  zero := zero
  one := one
  zero_ne_one := hzo
  payload_le := hpl
  rules r :=
    dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ
      (dt.nexEvalRuleF zero one args) (.chk 0) bot r.1 r.2
  startPh := .start
  startSt _ := zero
  accept := fun p f => p = .acceptP ∧ (args none).accBit f
  blank := fun _ => zero
  mark := regSlotMark zero one dt.dd0Le
  marked := fun x => (∃ k : dt.KIx, x.1 = DrawTag.arg k) ∨ IsTopNonArg x

variable {dt zero one}

omit [Finite A] [Finite dt.KIx] [Nonempty A] in
/-- **The handed program's rules, at a rule name**: what every run lemma's rule
hypothesis is discharged by. -/
theorem nexProgHanded_rules (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} (i : NexSite dt.SEF)
    (ρ : NexSh dt.SEF (Option dt.KIx) G dt.NexSESh i) :
    (dt.nexProgHanded zero one hzo hpl γ args bot).rules ⟨i, ρ⟩ =
      dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ
        (dt.nexEvalRuleF zero one args) (.chk 0) bot i ρ :=
  rfl

end HandedProg


/-! ### The two legs, at any program that reads the same rules -/

section Legs

variable {L : Language.{0, 0}} {dt : DrawData L} {A R' : Type}
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable [LinearOrder R'] [Finite R']
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Language.wide.Structure (Univ A R'
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd}

omit [Nonempty A] in
/-- **A program accepts, from its opening and its evaluation** – stated of *any*
program whose channel writes nothing on the walked track, so that the padded
program and the program itself are two instances of one statement. It is
The two legs of a clocked run, at an arbitrary program: the
adjustment between them (`config_openingEnd_eq_evalStart`), the file the initial
tape is presented along (`trackTape_empty_congr`) and the clock. -/
theorem wideRegAccept_of_legs
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hmk : ∀ x : Univ A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd, PR.mark x Slot.mir = PR.zero)
    (hbl : PR.blank Slot.mir = PR.zero)
    {I : Type} {F : LaidFile dt A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) I}
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) I}
    (hmir : st.mir = fun _ => False)
    {evalEntry : EvalPh dt.nv dt.PMF} {f₁ : dt.CtlIx → A}
    {w : Univ A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd → Prop}
    {o e : ℕ}
    (hopen : (wideData (Univ A R'
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn o
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt F.cell Slot.mir PR.initBackReg (fun _ => False))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) f₁), Sum.inl w,
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False))
          (PR.syElt PR.blank)⟩)
    {cT : Config (WPoint (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (heval : (wideData (Univ A R'
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn e
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) f₁), Sum.inl w,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ cT)
    {a b k j m : ℕ}
    (hk : 1 ≤ k) (hkj : k + 1 < j) (hm : 0 < m)
    (hcard : (k + j) * m ≤ Nat.card (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (he : e ≤ a * b) (ha : a ≤ 2 ^ (k * m)) (hb : b ≤ 2 ^ (k * m))
    (hopenle : o + 1 ≤ 2 ^ ((k + 1) * m))
    {p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)} {fq : dt.CtlIx → A}
    (hstate : cT.state = Sum.inr (PR.stElt p fq))
    (hacc : PR.accept p fq) :
    WideRegAccept (Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) := by
  refine Prog.wideRegAccept_prog hR hlin (t₀ := Slot.mir) hmk hbl
    (n := o + e) ?_
    (lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _)
      (nexTotal_lt_two_pow' (o := o) (e := e) hk hkj hm he ha hb hopenle).le)
      (Nat.pow_le_pow_right (by omega) hcard)) hstate hacc
  rw [DrawData.trackTape_empty_congr (PR := PR)
    (cell := wmRegSeg) (cell' := F.cell) (rest := PR.initBackReg)]
  exact hopen.trans ((config_openingEnd_eq_evalStart hmir _ _ _) ▸ heval)

end Legs


/-! ### The handed program is deterministic after its guess

The three facts a *backward* reading needs, at the handed program: it separates
after the guess, so a run from a post-guess configuration is unique, and its
accepting phase is stuck. All three are `nexProg_sepOn`'s, `nexProg_uniqueFrom`'s
and `nexProg_stuck_acceptP`'s at the rule set that lays no file – the rules being
the same function of the rule name (`nexProgHanded_rules`), the sweep the only
thing that changed, and neither the sweep nor the channel entering any of the
three proofs. -/

section Unique

variable {L : Language.{0, 0}} {dt : DrawData L} {A G : Type}
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [LinearOrder (dt.NexRIx (G := G))] [Finite (dt.NexRIx (G := G))]
variable [Language.wide.Structure (Univ A (dt.NexRIx (G := G))
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {zero one : A}

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (dt.NexRIx (G := G))]
  [Language.wide.Structure (Univ A (dt.NexRIx (G := G))
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **The handed program separates after its guess**: two of its rules firing
in the same post-guess phase on the same data are the same rule. Across sites
that is the owner map (`nexOwner_nexRule`); within a site it is
`nexSep_postGuess`, and the guess site is where the two are allowed to differ –
which is why the phase restriction is there. -/
theorem nexProgHanded_sep_rules (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} :
    ∀ (r r' : dt.NexRIx (G := G)) (f : dt.CtlIx → A) (g : dt.SlotIx → A),
      NexPh.PostGuess ((dt.nexProgHanded zero one hzo hpl γ args bot).rules r).srcPh →
      ((dt.nexProgHanded zero one hzo hpl γ args bot).rules r).guard f g →
      ((dt.nexProgHanded zero one hzo hpl γ args bot).rules r').guard f g →
      ((dt.nexProgHanded zero one hzo hpl γ args bot).rules r).srcPh =
        ((dt.nexProgHanded zero one hzo hpl γ args bot).rules r').srcPh →
      r = r' := by
  rintro ⟨i, ρ⟩ ⟨i', ρ'⟩ f g hph0 hg hg' hph
  rw [nexProgHanded_rules (G := G) hzo hpl i ρ] at hph0 hg hph
  rw [nexProgHanded_rules (G := G) hzo hpl i' ρ'] at hg' hph
  have hown : i = i' := by
    have h₁ := nexOwner_nexRule (dt := dt) (one := one) (β := dt.nullSpec (Option dt.KIx)) (γ := γ)
      (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := .chk 0)
      (bot := bot) (ownE := dt.seOwn)
      (fun e ρ => by
        obtain ⟨p, hp, ho⟩ := nexEvalHosrcF (zero := zero) (one := one) args e ρ
        rw [hp]
        exact congrArg NexSite.eval ho) i ρ
    have h₂ := nexOwner_nexRule (dt := dt) (one := one) (β := dt.nullSpec (Option dt.KIx)) (γ := γ)
      (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := .chk 0)
      (bot := bot) (ownE := dt.seOwn)
      (fun e ρ => by
        obtain ⟨p, hp, ho⟩ := nexEvalHosrcF (zero := zero) (one := one) args e ρ
        rw [hp]
        exact congrArg NexSite.eval ho) i' ρ'
    rw [← h₁, ← h₂, hph]
  subst hown
  have hsep := nexSep_postGuess (dt := dt) (one := one) (β := dt.nullSpec (Option dt.KIx)) (γ := γ)
    (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := .chk 0) (bot := bot)
    (fun e ρ ρ' f g => nexEvalSepF hzo args e ρ ρ' f g) i ρ ρ' f g hph0 hg hg' hph
  exact congrArg (fun x => (⟨i, x⟩ : (i : NexSite dt.SEF) ×
    NexSh dt.SEF (Option dt.KIx) G dt.NexSESh i)) hsep

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (dt.NexRIx (G := G))] in
omit [Language.wide.Structure (Univ A (dt.NexRIx (G := G))
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **No rule of the handed program fires from its accepting phase**: the
accepting phase is owned by the accepting site (`nexOwner`), and that site has
no rules at all – its shape is `Empty`. -/
theorem nexProgHanded_srcPh_ne_acceptP (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} (r : dt.NexRIx (G := G)) :
    ((dt.nexProgHanded zero one hzo hpl γ args bot).table).srcPh r ≠
      NexPh.acceptP := by
  obtain ⟨i, ρ⟩ := r
  intro hsrc
  have hown := nexOwner_nexRule (dt := dt) (one := one) (β := dt.nullSpec (Option dt.KIx)) (γ := γ)
    (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := EvalPh.chk 0)
    (bot := bot) (ownE := dt.seOwn)
    (fun e ρ' => by
      obtain ⟨p, hp, hown⟩ := nexEvalHosrcF (B := Option dt.KIx) args e ρ'
      rw [hp]
      exact congrArg NexSite.eval hown) i ρ
  rw [show (dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ (dt.nexEvalRuleF zero one args)
      (EvalPh.chk 0) bot i ρ).srcPh =
    ((dt.nexProgHanded zero one hzo hpl γ args bot).table).srcPh ⟨i, ρ⟩ from rfl,
    hsrc] at hown
  have hi : NexSite.accept = i := hown
  subst hi
  exact ρ.elim

end Unique

end DrawData

end Draw

end DescriptiveComplexity
