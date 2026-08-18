/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexSpec
import DescriptiveComplexity.Problems.Wide.PfpProg
import DescriptiveComplexity.Problems.Wide.NexOuter
import DescriptiveComplexity.Problems.Wide.PfpRunEval

/-!
# The clocked evaluation's spine

The space-bounded spine (`DescriptiveComplexity.Pfp.PfpData.evalRule`) ends its
last checkpoint in one of two outer phases – the sweep's advance, or the
post-sweep reset – because it runs inside an iteration. A clocked program has
neither: its evaluation runs **once**, and its last checkpoint leaves into
whatever phase the caller names. So the spine's rules
are not the space-bounded ones at another embedding; they are two rules per
checkpoint instead of three, at the clocked program's own phases
(`DescriptiveComplexity.Pfp.NexPh`).

Everything else is shared: the sites are `DescriptiveComplexity.Pfp.EvalSite`,
the machineries' rules are the parameter, and the ownership and separation
proofs are the same case analysis with the dead third rule gone.

The run is `nexEval_reachesIn`, and it is the space-bounded spine's count with
the same shape: one machinery's width plus its dispatch and its walk back, once
per variable.

The file also assembles the **program**: the spine's rules at the *shared*
machineries – a clocked program's tower above the atom is the space-bounded one,
`PMF`, `SMF`, `SEF` and `varRuleF` and all – with
`nexEvalHosrcF`/`nexEvalSepF`, and `nexProg` – the outer layer's rules at the
two sweep specifications with the evaluation's as their parameter. That last is
built directly rather than through
`DescriptiveComplexity.Pfp.Assembly`, because a clocked program is *not*
deterministic: its guess site fires three rules on the same data, which is the
one piece of nondeterminism it has, and what does hold there is
`DescriptiveComplexity.Pfp.PfpData.nexSep_postGuess`.
-/

namespace DescriptiveComplexity

namespace Pfp

/-- **The rules of a clocked checkpoint**: the walk back to the marker, and the
one dispatch – into the variable's machinery below the last checkpoint, out of
the evaluation at it. -/
inductive NexEvalChkRule : Type
  /-- Walk left back to the marker. -/
  | stay : NexEvalChkRule
  /-- Dispatch: into the machinery, or out of the evaluation. -/
  | dsp : NexEvalChkRule
  deriving DecidableEq

instance : Finite NexEvalChkRule :=
  Finite.of_injective (fun p => match p with | .stay => (0 : Fin 2) | .dsp => 1)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule shape of each clocked evaluation site.** -/
def NexEvalSh (nv : ℕ) (SM : Type) (ShM : SM → Type) : EvalSite nv SM → Type
  | .chk _ => NexEvalChkRule
  | .sub s => ShM s

namespace PfpData

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} (dt : PfpData L) {A Q PM SM B : Type} {nv : ℕ}
variable (one : A) {ShM : SM → Type}

/-- **The rules of a clocked evaluation's spine**: per checkpoint the walk back
and the dispatch; the sub-machineries' rules are the parameter, and the exit at
the last checkpoint is the caller's phase. -/
noncomputable def nexEvalRule
    (ruleM : ∀ s : SM, ShM s → Rule A Q dt.SlotIx (NexPh B (EvalPh nv PM)))
    (subEntry : Fin nv → PM) (exitPh : NexPh B (EvalPh nv PM)) :
    ∀ i : EvalSite nv SM, NexEvalSh nv SM ShM i →
      Rule A Q dt.SlotIx (NexPh B (EvalPh nv PM))
  | .chk k, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := .evalP (.chk k)
      dstPh := .evalP (.chk k)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .chk k, .dsp =>
    if hk : (k : ℕ) < nv then
      { guard := fun _ g => dt.exitG one g
        srcPh := .evalP (.chk k)
        dstPh := .evalP (.sub (subEntry ⟨(k : ℕ), hk⟩))
        dstSt := fun f _ => f
        wr := fun _ g => g
        moveRight := True }
    else
      { guard := fun _ g => dt.exitG one g
        srcPh := .evalP (.chk k)
        dstPh := exitPh
        dstSt := fun f _ => f
        wr := fun _ g => g
        moveRight := True }
  | .sub s, ρ => ruleM s ρ

variable {ruleM : ∀ s : SM, ShM s → Rule A Q dt.SlotIx (NexPh B (EvalPh nv PM))}
variable {subEntry : Fin nv → PM} {ownM : PM → SM}
variable {exitPh : NexPh B (EvalPh nv PM)}

/-- **Every clocked spine rule fires from a phase its site owns**; the
sub-machineries' obligation is the parameter. -/
theorem nexEvalHosrc
    (hosrcM : ∀ (s : SM) (ρ : ShM s),
      ∃ p : PM, (ruleM s ρ).srcPh = .evalP (.sub p) ∧ ownM p = s) :
    ∀ (e : EvalSite nv SM) (ρ : NexEvalSh nv SM ShM e),
      ∃ p : EvalPh nv PM,
        (dt.nexEvalRule one ruleM subEntry exitPh e ρ).srcPh = .evalP p ∧
        evalOwn ownM p = e := by
  intro e ρ
  match e, ρ with
  | .chk k, .stay => exact ⟨.chk k, rfl, rfl⟩
  | .chk k, .dsp =>
    by_cases hk : (k : ℕ) < nv
    · exact ⟨.chk k, by simp [nexEvalRule, hk], rfl⟩
    · exact ⟨.chk k, by simp [nexEvalRule, hk], rfl⟩
  | .sub s, ρ =>
    obtain ⟨p, hp, ho⟩ := hosrcM s ρ
    exact ⟨.sub p, hp, congrArg EvalSite.sub ho⟩

/-- **The clocked spine separates in-shape**: per checkpoint, the walk's guard
is disjoint from the dispatch's, and there is no third rule to tell apart. -/
theorem nexEvalSep
    (hsepM : ∀ (s : SM) (ρ ρ' : ShM s) (f : Q → A) (g : dt.SlotIx → A),
      (ruleM s ρ).guard f g → (ruleM s ρ').guard f g →
      (ruleM s ρ).srcPh = (ruleM s ρ').srcPh → ρ = ρ') :
    ∀ (e : EvalSite nv SM) (ρ ρ' : NexEvalSh nv SM ShM e) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.nexEvalRule one ruleM subEntry exitPh e ρ).guard f g →
      (dt.nexEvalRule one ruleM subEntry exitPh e ρ').guard f g →
      (dt.nexEvalRule one ruleM subEntry exitPh e ρ).srcPh =
        (dt.nexEvalRule one ruleM subEntry exitPh e ρ').srcPh →
      ρ = ρ' := by
  intro e ρ ρ' f g hg hg' hph
  match e, ρ, ρ' with
  | .chk k, .stay, .stay => rfl
  | .chk k, .dsp, .dsp => rfl
  | .chk k, .stay, .dsp =>
    by_cases hk : (k : ℕ) < nv
    · simp only [nexEvalRule, dif_pos hk] at hg'
      simp only [nexEvalRule] at hg
      exact absurd hg'.1 hg
    · simp only [nexEvalRule, dif_neg hk] at hg'
      simp only [nexEvalRule] at hg
      exact absurd hg'.1 hg
  | .chk k, .dsp, .stay =>
    by_cases hk : (k : ℕ) < nv
    · simp only [nexEvalRule, dif_pos hk] at hg
      simp only [nexEvalRule] at hg'
      exact absurd hg.1 hg'
    · simp only [nexEvalRule, dif_neg hk] at hg
      simp only [nexEvalRule] at hg'
      exact absurd hg.1 hg'
  | .sub s, ρ, ρ' => exact hsepM s ρ ρ' f g hg hg' hph

/-- **A property of the spine's phases and its exit holds of every phase it can
move to**, given it holds of every phase a machinery can move to. -/
theorem nexEvalRule_dstIn {S : NexPh B (EvalPh nv PM) → Prop}
    (hemb : ∀ p : EvalPh nv PM, S (NexPh.evalP p)) (hexit : S exitPh)
    (hM : ∀ (s : SM) (ρ : ShM s), S (ruleM s ρ).dstPh)
    (e : EvalSite nv SM) (ρ : NexEvalSh nv SM ShM e) :
    S (dt.nexEvalRule one ruleM subEntry exitPh e ρ).dstPh := by
  match e, ρ with
  | .chk k, .stay => exact hemb _
  | .chk k, .dsp =>
    by_cases hk : (k : ℕ) < nv
    · rw [nexEvalRule, dif_pos hk]; exact hemb _
    · rw [nexEvalRule, dif_neg hk]; exact hexit
  | .sub s, ρ => exact hM s ρ

/-! ### The spine at the clocked machineries

The types of the spine, and its rules at the clocked variable machineries: what
`DescriptiveComplexity.Pfp.PfpData.nexRule` takes as its evaluation parameter.
The phases are `EvalPh` over the machineries', as in the space-bounded program;
only the machineries are the clocked ones and the exit is the accepting phase.
-/

section Spine

variable {L : Language.{0, 0}} (dt : PfpData L) {A Q B : Type}

/-- **The rule shape of the clocked evaluation's sites**: the spine's own, two
rules per checkpoint, over the machinery sites of the shared tower. -/
noncomputable def NexSESh : dt.SEF → Type :=
  NexEvalSh dt.nv dt.SMF dt.SMSh

variable (zero one : A) [Fintype Q] [Fintype dt.SlotIx]

/-- **The rules of the clocked evaluation's machineries**: one copy of the
clocked variable machinery per spine position – its exit the next checkpoint –
and the output's, whose exit is the accepting phase. -/
noncomputable def nexSmRule (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ s : dt.SMF, dt.SMSh s →
      Rule A Q dt.SlotIx (NexPh B (EvalPh dt.nv dt.PMF))
  | Sum.inl ⟨j, s⟩, ρ =>
    dt.varRuleF zero one (dt.varAt j) (args _)
      (fun p => .evalP (.sub (Sum.inl ⟨j, p⟩))) (.evalP (.chk j.succ)) s ρ
  | Sum.inr s, ρ =>
    dt.varRuleF zero one none (args none)
      (fun p => .evalP (.sub (Sum.inr p))) .acceptP s ρ

/-- **The rules of the clocked evaluation**: the spine over the machineries,
leaving at the last checkpoint into the **output's** machinery, whose own exit
is the accepting phase. The accepting predicate reads that machinery's verdict
bit, so the evaluation has to run it: a last checkpoint that went straight to
`acceptP` would leave the bit unwritten. -/
noncomputable def nexEvalRuleF (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ e : dt.SEF, dt.NexSESh e →
      Rule A Q dt.SlotIx (NexPh B (EvalPh dt.nv dt.PMF)) :=
  dt.nexEvalRule one (dt.nexSmRule (B := B) zero one args) dt.smEntry
    (.evalP (.sub dt.smEntryOut))

variable {dt zero one}

omit [Fintype Q] [Fintype dt.SlotIx] in
/-- **Every rule of the clocked evaluation's machineries fires from a phase its
site owns.** -/
theorem nexSmHosrc (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ (s : dt.SMF) (ρ : dt.SMSh s),
      ∃ p : dt.PMF,
        (dt.nexSmRule (B := B) zero one args s ρ).srcPh =
          NexPh.evalP (.sub p) ∧ dt.smOwn p = s := by
  intro s ρ
  match s, ρ with
  | Sum.inl ⟨j, s⟩, ρ =>
    obtain ⟨p, hp, ho⟩ :=
      varHosrcF zero one (dt.varAt j) (args _)
        (emb := fun p =>
          (NexPh.evalP (.sub (Sum.inl ⟨j, p⟩)) : NexPh B (EvalPh dt.nv dt.PMF)))
        (.evalP (.chk j.succ)) s ρ
    exact ⟨Sum.inl ⟨j, p⟩, hp, congrArg (fun x => (Sum.inl ⟨j, x⟩ : dt.SMF)) ho⟩
  | Sum.inr s, ρ =>
    obtain ⟨p, hp, ho⟩ :=
      varHosrcF zero one none (args none)
        (emb := fun p =>
          (NexPh.evalP (.sub (Sum.inr p)) : NexPh B (EvalPh dt.nv dt.PMF)))
        .acceptP s ρ
    exact ⟨Sum.inr p, hp, congrArg (fun x => (Sum.inr x : dt.SMF)) ho⟩

omit [Fintype Q] [Fintype dt.SlotIx] in
/-- **The clocked evaluation's machineries separate in-shape.** -/
theorem nexSmSep (hzo : zero ≠ one)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ (s : dt.SMF) (ρ ρ' : dt.SMSh s) (f : Q → A) (g : dt.SlotIx → A),
      (dt.nexSmRule (B := B) zero one args s ρ).guard f g →
      (dt.nexSmRule (B := B) zero one args s ρ').guard f g →
      (dt.nexSmRule (B := B) zero one args s ρ).srcPh =
        (dt.nexSmRule (B := B) zero one args s ρ').srcPh →
      ρ = ρ' := by
  intro s ρ ρ' f g hg hg' hph
  match s, ρ, ρ' with
  | Sum.inl ⟨j, s⟩, ρ, ρ' =>
    exact varSepF zero one hzo (dt.varAt j) (args _)
      (emb := fun p =>
        (NexPh.evalP (.sub (Sum.inl ⟨j, p⟩)) : NexPh B (EvalPh dt.nv dt.PMF)))
      (fun x y h => by
        have h1 := NexPh.evalP.inj h
        have h2 := EvalPh.sub.inj h1
        have h3 : (⟨j, x⟩ : (Σ j' : Fin dt.nv, dt.VarPhF (dt.varAt j'))) = ⟨j, y⟩ :=
          Sum.inl.inj h2
        exact sigma_mk_injective
          (β := fun j' : Fin dt.nv => dt.VarPhF (dt.varAt j')) h3)
      (.evalP (.chk j.succ)) s ρ ρ' f g hg hg' hph
  | Sum.inr s, ρ, ρ' =>
    exact varSepF zero one hzo none (args none)
      (emb := fun p =>
        (NexPh.evalP (.sub (Sum.inr p)) : NexPh B (EvalPh dt.nv dt.PMF)))
      (fun x y h => by
        have h1 := NexPh.evalP.inj h
        have h2 := EvalPh.sub.inj h1
        have h3 : (x : dt.VarPhF none) = y := Sum.inr.inj h2
        exact h3)
      .acceptP s ρ ρ' f g hg hg' hph

omit [Fintype Q] [Fintype dt.SlotIx] in
/-- **Every rule of the clocked evaluation fires from a phase its site
owns.** -/
theorem nexEvalHosrcF (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ (e : dt.SEF) (ρ : dt.NexSESh e),
      ∃ p : EvalPh dt.nv dt.PMF,
        (dt.nexEvalRuleF (B := B) zero one args e ρ).srcPh = .evalP p ∧
          dt.seOwn p = e :=
  dt.nexEvalHosrc one (nexSmHosrc args)

omit [Fintype Q] [Fintype dt.SlotIx] in
/-- **The clocked evaluation separates in-shape.** -/
theorem nexEvalSepF (hzo : zero ≠ one)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ (e : dt.SEF) (ρ ρ' : dt.NexSESh e) (f : Q → A) (g : dt.SlotIx → A),
      (dt.nexEvalRuleF (B := B) zero one args e ρ).guard f g →
      (dt.nexEvalRuleF (B := B) zero one args e ρ').guard f g →
      (dt.nexEvalRuleF (B := B) zero one args e ρ).srcPh =
        (dt.nexEvalRuleF (B := B) zero one args e ρ').srcPh →
      ρ = ρ' :=
  dt.nexEvalSep one (nexSmSep hzo args)

omit [Fintype dt.SlotIx] in
/-- **A property of the evaluation's phases and its accepting phase holds of
every phase a machinery can move to.** -/
theorem nexSmRule_dstIn {S : NexPh B (EvalPh dt.nv dt.PMF) → Prop}
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
    (hemb : ∀ p : EvalPh dt.nv dt.PMF, S (NexPh.evalP p)) (hacc : S NexPh.acceptP)
    (s : dt.SMF) (ρ : dt.SMSh s) :
    S (dt.nexSmRule (B := B) zero one args s ρ).dstPh := by
  match s, ρ with
  | Sum.inl ⟨j, s⟩, ρ =>
    exact dt.varRuleF_dstIn zero one (dt.varAt j) (args _)
      (emb := fun p => NexPh.evalP (.sub (Sum.inl ⟨j, p⟩)))
      (.evalP (.chk j.succ)) (fun p => hemb _) (hemb _) s ρ
  | Sum.inr s, ρ =>
    exact dt.varRuleF_dstIn zero one none (args none)
      (emb := fun p => NexPh.evalP (.sub (Sum.inr p))) .acceptP
      (fun p => hemb _) hacc s ρ

omit [Fintype dt.SlotIx] in
/-- **The clocked evaluation never leaves the post-guess phases**: every phase
its rules can move to is the evaluation's own or the accepting one, and
`NexPh.PostGuess` holds of both. This is the one fact
`DescriptiveComplexity.Pfp.PfpData.nexProg_uniqueFrom` takes from the
evaluation, and the tower discharges it layer by layer down to the trips. -/
theorem nexEvalRuleF_postGuess
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
    (e : dt.SEF) (ρ : dt.NexSESh e) :
    NexPh.PostGuess ((dt.nexEvalRuleF (B := B) zero one args) e ρ).dstPh :=
  nexEvalRule_dstIn (dt := dt) (one := one) (S := NexPh.PostGuess)
    (ruleM := dt.nexSmRule (B := B) zero one args)
    (subEntry := dt.smEntry) (exitPh := NexPh.evalP (.sub dt.smEntryOut))
    (fun _ => trivial) trivial
    (fun s ρ => nexSmRule_dstIn (B := B) (zero := zero) (one := one) args
      (fun _ => trivial) trivial s ρ) e ρ

end Spine

/-! ### The clocked program

The rule set assembled: the outer layer's rules at the two sweep
specifications, with the evaluation's as their parameter. Unlike the
space-bounded program this is *not* an
`DescriptiveComplexity.Pfp.Assembly` – the guess site fires three rules on the
same data, which is the program's one piece of nondeterminism – so the record
is built directly and the separation that does hold is
`DescriptiveComplexity.Pfp.PfpData.nexSep_postGuess`. -/

section Prog

variable {L : Language.{0, 0}} (dt : PfpData L) {A G : Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]

/-- **The rule names of the clocked program**: a site of its outer layer, or of
its evaluation, and one of that site's rules. -/
noncomputable abbrev NexRIx : Type :=
  (i : NexSite dt.SEF) ×
    NexSh dt.SEF (Option dt.KIx) G dt.NexSESh i

variable (zero one : A)
variable [LinearOrder (dt.NexRIx (G := G))]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]

/-- **The clocked program**: the outer layer's rules – the opening step, the
build sweep, the walk home, the guess sweep, the walk home – with the clocked
evaluation's as their parameter, and the reduction's constants. The accepting
phase is the outer layer's, and its verdict is read from the control exactly as
the space-bounded program's is. -/
noncomputable def nexProg (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (coord : Fin dt.dd → dt.CtlIx)
    (β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx))
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
    (bot : Option dt.KIx) :
    Prog A (dt.NexRIx (G := G)) (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      dt.CtlIx dt.SlotIx dt.KIx dt.dd where
  zero := zero
  one := one
  zero_ne_one := hzo
  payload_le := hpl
  rules := fun r =>
    dt.nexRule one β γ (dt.nexEvalRuleF zero one args) (.chk 0) bot r.1 r.2
  startPh := .start
  startSt := dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2
  accept := fun p f => p = .acceptP ∧ (args none).accBit f
  blank := fun _ => zero
  mark := fun _ _ => zero

variable {dt zero one}

omit [LinearOrder (dt.NexRIx (G := G))]
  [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] in
/-- **The clocked program's rules, at a rule name**: what every run lemma's
rule hypothesis is discharged by. -/
theorem nexProg_rules (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} (i : NexSite dt.SEF)
    (ρ : NexSh dt.SEF (Option dt.KIx) G dt.NexSESh i) :
    (dt.nexProg zero one hzo hpl coord β γ args bot).rules ⟨i, ρ⟩ =
      dt.nexRule one β γ (dt.nexEvalRuleF zero one args) (.chk 0) bot i ρ :=
  rfl

omit [LinearOrder (dt.NexRIx (G := G))]
  [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] in
/-- **The clocked program's evaluation rules**: at an evaluation site the
program's rule *is* the spine's, which is what discharges the rule hypothesis of
`DescriptiveComplexity.Pfp.PfpData.nexEval_reachesIn` at the assembled
program. -/
theorem nexProg_rules_eval (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} (e : dt.SEF) (ρ : dt.NexSESh e) :
    (dt.nexProg zero one hzo hpl coord β γ args bot).rules ⟨.eval e, ρ⟩ =
      dt.nexEvalRule one (dt.nexSmRule zero one args) dt.smEntry
        (NexPh.evalP (.sub dt.smEntryOut)) e ρ :=
  rfl

end Prog

section NexEvalRun

variable {L : Language.{0, 0}} {dt : PfpData L}
variable {A R Q PM SM B : Type} {nv : ℕ}
variable [Fintype Q] [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable [LinearOrder (NexPh B (EvalPh nv PM))]
variable [Language.wide.Structure
  (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (NexPh B (EvalPh nv PM))]
variable {ShM : SM → Type}
variable {PR : Prog A R (NexPh B (EvalPh nv PM)) Q dt.SlotIx dt.KIx dt.dd}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd) I ile)


variable {ruleM : ∀ s : SM, ShM s →
  Rule A Q dt.SlotIx (NexPh B (EvalPh nv PM))}
variable {subEntry : Fin nv → PM} {exitPh : NexPh B (EvalPh nv PM)}
variable {rEmb : ∀ i : EvalSite nv SM, NexEvalSh nv SM ShM i → R}
variable (hrules : ∀ (i : EvalSite nv SM) (ρ : NexEvalSh nv SM ShM i),
  PR.rules (rEmb i ρ) = dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ)

omit [LinearOrder A] [LinearOrder R] [LinearOrder (NexPh B (EvalPh nv PM))]
  [Language.wide.Structure (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (NexPh B (EvalPh nv PM))] in
include hrules in
/-- A spine rule with a true guard is a `HasRight` witness. -/
private theorem hasRight_of_rule {i : EvalSite nv SM} {ρ : NexEvalSh nv SM ShM i}
    {f f' : Q → A} {g g' : dt.SlotIx → A}
    {p p' : NexPh B (EvalPh nv PM)}
    (hg : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).guard f g)
    (hp : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).srcPh = p)
    (hp' : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).dstPh = p')
    (hf' : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).dstSt f g = f')
    (hg' : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).wr f g = g')
    (hmr : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).moveRight) :
    PR.HasRight p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'], by rw [hrules]; exact hmr⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder (NexPh B (EvalPh nv PM))]
  [Language.wide.Structure (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (NexPh B (EvalPh nv PM))] in
include hrules in
/-- A spine rule with a true guard is a `HasLeft` witness. -/
private theorem hasLeft_of_rule {i : EvalSite nv SM} {ρ : NexEvalSh nv SM ShM i}
    {f f' : Q → A} {g g' : dt.SlotIx → A}
    {p p' : NexPh B (EvalPh nv PM)}
    (hg : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).guard f g)
    (hp : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).srcPh = p)
    (hp' : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).dstPh = p')
    (hf' : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).dstSt f g = f')
    (hg' : (dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).wr f g = g')
    (hml : ¬(dt.nexEvalRule PR.one ruleM subEntry exitPh i ρ).moveRight) :
    PR.HasLeft p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'],
    fun hc => hml (by rw [hrules] at hc; exact hc)⟩

variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd
  (WMLe (A := Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)))
variable (hix : IsLinOrd ile)
variable {gbot : I}
variable (hbot : ∀ y, ile gbot y)
-- The program's working area lies below its file. Which addresses count as
-- working ones is the caller's to say – at the elementwise file it is «misses
-- the least element» (`wmSetLt_wmSeg_of_not_bot`) – so the predicate is a
-- parameter, and the one thing asked of it is that its addresses lie below
-- every register.
variable {WorkAddr : (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd → Prop) → Prop}
variable (hwork : ∀ {r : Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd → Prop}, WorkAddr r →
  ∀ u, WMSetLt WMLe r (RF.cell u))
variable {v v' : Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable {restOf : Fin (nv + 1) →
  (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
variable {mvOf : Fin (nv + 1) → I → Prop}
variable (hwkOf : ∀ k r, restOf k r Slot.wk = bitVal PR.zero PR.one (r = v))
variable (hrgOf : ∀ k r, restOf k r Slot.reg = bitVal PR.zero PR.one
  (∃ u : I, r = RF.cell u))
variable (fs : Fin (nv + 1) → Q → A)
-- The width of one variable's machinery: a clocked caller supplies it, a
-- space-bounded one takes the largest of the finitely many runs it has.
variable (w : ℕ)
variable (hVar : ∀ k : Fin nv,
  (wideData (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).ReachesIn w
    ⟨Sum.inr (PR.stElt (NexPh.evalP (.sub (subEntry k))) (fs k.castSucc)),
      Sum.inl v',
      wideTape (PR.trackTapeAt RF.cell Slot.val (restOf k.castSucc) (mvOf k.castSucc))
        (PR.syElt PR.blank)⟩
    ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk k.succ)) (fs k.succ)), Sum.inl v',
      wideTape (PR.trackTapeAt RF.cell Slot.val (restOf k.succ) (mvOf k.succ))
        (PR.syElt PR.blank)⟩)

include hrules hR hlin hix hbot hv hvi hwkOf hrgOf hVar in
/-- **The spine's run, on a clock**: from the checkpoint before the first
variable at the marker to the checkpoint after the last, one machinery run per
position, each with its dispatch and its walk back. -/
theorem nexEval_reachesIn :
    (wideData (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).ReachesIn
      ((w + 2) * nv)
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fs 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val (restOf 0) (mvOf 0))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk (Fin.last nv))) (fs (Fin.last nv))),
        Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val (restOf (Fin.last nv))
          (mvOf (Fin.last nv))) (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot RF hlin hix hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  suffices h : ∀ (k : ℕ) (hk : k ≤ nv),
      (wideData (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).ReachesIn
        ((w + 2) * (nv - k))
        ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk ⟨k, Nat.lt_succ_of_le hk⟩))
            (fs ⟨k, Nat.lt_succ_of_le hk⟩)), Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf ⟨k, Nat.lt_succ_of_le hk⟩)
            (mvOf ⟨k, Nat.lt_succ_of_le hk⟩)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk (Fin.last nv))) (fs (Fin.last nv))),
          Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf (Fin.last nv))
            (mvOf (Fin.last nv))) (PR.syElt PR.blank)⟩ by
    have h0 := h 0 (Nat.zero_le nv)
    rw [Nat.sub_zero] at h0
    exact h0
  intro k hk
  induction hd : nv - k generalizing k with
  | zero =>
    have hkn : k = nv := by omega
    subst hkn
    have hfk : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (k + 1)) = Fin.last k :=
      Fin.ext rfl
    rw [hfk, Nat.mul_zero]
    exact TMData.reachesIn_refl
  | succ n ih =>
    have hkl : k < nv := by omega
    set j : Fin nv := ⟨k, hkl⟩ with hj
    have hcast : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (nv + 1)) = j.castSucc :=
      Fin.ext rfl
    rw [hcast]
    -- the dispatch into variable `j`'s machinery
    have hdsp : (wideData
        (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk j.castSucc)) (fs j.castSucc)),
          Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf j.castSucc)
            (mvOf j.castSucc)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (NexPh.evalP (.sub (subEntry j))) (fs j.castSucc)),
          Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf j.castSucc)
            (mvOf j.castSucc)) (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      refine hasRight_of_rule hrules (i := .chk j.castSucc) (ρ := .dsp)
        ?_ ?_ ?_ ?_ ?_ ?_
      · rw [nexEvalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
        constructor
        · rw [Prog.passTracks_of_ne hne_wk_val, hwkOf]
          exact bitVal_pos rfl
        · rw [Prog.passTracks_of_ne hne_reg_val, hrgOf,
            bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
          exact PR.zero_ne_one
      · rw [nexEvalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
      · rw [nexEvalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
        rfl
      · rw [nexEvalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
      · rw [nexEvalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
      · rw [nexEvalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
        trivial
    -- the machinery's run, and the walk back at the next checkpoint
    have hback : (wideData
        (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk j.succ)) (fs j.succ)), Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf j.succ) (mvOf j.succ))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk j.succ)) (fs j.succ)), Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf j.succ) (mvOf j.succ))
            (PR.syElt PR.blank)⟩ := by
      have hwkv' : PR.passTracksAt RF.cell Slot.val (restOf j.succ) (mvOf j.succ) v'
          Slot.wk ≠ PR.one := by
        rw [Prog.passTracks_of_ne hne_wk_val, hwkOf,
          bitVal_neg (Ne.symm hvv')]
        exact PR.zero_ne_one
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      exact hasLeft_of_rule hrules (i := .chk j.succ) (ρ := .stay)
        hwkv' rfl rfl rfl rfl not_false
    have hsucc : j.succ = (⟨k + 1, Nat.lt_succ_of_le (by omega)⟩ :
        Fin (nv + 1)) := Fin.ext rfl
    refine TMData.ReachesIn.mono
      (show 1 + (w + (1 + (w + 2) * n)) ≤ (w + 2) * (n + 1) by
        rw [Nat.mul_succ]; omega) ?_
    refine (TMData.reachesIn_of_step hdsp).trans ?_
    refine (hVar j).trans ?_
    refine (TMData.reachesIn_of_step hback).trans ?_
    rw [hsucc]
    exact ih (k + 1) (by omega) (by omega)

omit hVar in
include hrules hR hlin hix hbot hv hvi hwkOf hrgOf in
/-- **The spine's run**, the budget forgotten: what a space-bounded caller
reads, its machineries' runs carrying no count. -/
theorem nexEval_run
    (hVarR : ∀ k : Fin nv,
      Relation.ReflTransGen
        (wideData (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (NexPh.evalP (.sub (subEntry k))) (fs k.castSucc)),
          Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf k.castSucc)
            (mvOf k.castSucc)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk k.succ)) (fs k.succ)), Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf k.succ) (mvOf k.succ))
            (PR.syElt PR.blank)⟩) :
    Relation.ReflTransGen
      (wideData (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fs 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val (restOf 0) (mvOf 0))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk (Fin.last nv))) (fs (Fin.last nv))),
        Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val (restOf (Fin.last nv))
          (mvOf (Fin.last nv))) (PR.syElt PR.blank)⟩ := by
  classical
  choose wOf hwOf using fun k : Fin nv =>
    TMData.exists_reachesIn_of_reflTransGen (hVarR k)
  exact (nexEval_reachesIn RF hrules hR hlin hix hbot hv hvi hwkOf hrgOf fs
    (Finset.univ.sup wOf)
    (fun k => (hwOf k).mono (Finset.le_sup (Finset.mem_univ k)))).reflTransGen

include hrules in
/-- **The evaluation's entry walk-back**: whatever dispatches into the spine
leaves the head one cell to the right of the marker, and a checkpoint's `stay`
rule walks it back. This is the step between the opening and
`DescriptiveComplexity.Pfp.PfpData.nexEval_reachesIn`. -/
theorem step_nexEvalBack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)))
    {v v' : Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v')
    {rest : (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd → Prop) →
      dt.SlotIx → A}
    {m : I → Prop} {f : Q → A} (k : Fin (nv + 1))
    (hwk : ∀ r, rest r Slot.wk = bitVal PR.zero PR.one (r = v)) :
    (wideData (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk k)) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk k)) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val rest m) (PR.syElt PR.blank)⟩ := by
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkv' : PR.passTracksAt RF.cell Slot.val rest m v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwk, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  exact hasLeft_of_rule hrules (i := .chk k) (ρ := .stay)
    hwkv' rfl rfl rfl rfl not_false

include hrules in
/-- **The evaluation's exit**: at the last checkpoint the spine leaves into the
phase the caller named, one cell to the right of the marker. This is the step
between `nexEval_reachesIn` and the accepting phase. -/
theorem step_nexEvalExit (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)))
    {v v' : Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v')
    {rest : (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd → Prop) →
      dt.SlotIx → A}
    {m : I → Prop} {f : Q → A}
    (hex : dt.exitG PR.one (PR.passTracksAt RF.cell Slot.val rest m v)) :
    (wideData (Univ A R (NexPh B (EvalPh nv PM)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk (Fin.last nv))) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val rest m) (PR.syElt PR.blank)⟩ := by
  refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
  refine hasRight_of_rule hrules (i := .chk (Fin.last nv)) (ρ := .dsp) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [nexEvalRule, dif_neg (by simp [Fin.last])]
    exact hex
  · rw [nexEvalRule, dif_neg (by simp [Fin.last])]
  · rw [nexEvalRule, dif_neg (by simp [Fin.last])]
  · rw [nexEvalRule, dif_neg (by simp [Fin.last])]
  · rw [nexEvalRule, dif_neg (by simp [Fin.last])]
  · rw [nexEvalRule, dif_neg (by simp [Fin.last])]
    trivial

end NexEvalRun

end PfpData

end Pfp

end DescriptiveComplexity
