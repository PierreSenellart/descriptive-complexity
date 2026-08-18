/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TrackWrites
import DescriptiveComplexity.Problems.Wide.RegChannelAccept

/-!
# Where a backward reading of an accepting run starts

A run that accepts ends in `NexPh.acceptP`, which is one of the phases the
program can never leave (`NexPh.PostGuess`). So somewhere along the run there is
a **first** configuration in a post-guess phase, and this file finds it and
recognises its tape.

Two facts do it. The phases before it are all the outer layer's, so the rules
fired up to that point keep the file, keep the addressed tracks and write bits
(`nexRule_keepsFile_of_ne_eval` and its two siblings) – which is exactly what
`DescriptiveComplexity.Pfp.ShapedAt` propagates along a run. And an accepting
configuration is in a post-guess phase, so the search has something to find.

What comes out is a configuration whose tape is an `ixBack` of *some* tape state
and whose phase is post-guess: the point where the machine's nondeterminism is
spent, the guess is written on the tape, and the rest of the run is the
evaluation's – deterministic, and read forward.
-/

namespace DescriptiveComplexity

/-! ### The first time a property holds -/

open Classical in
/-- **A property that holds at some time holds first at some time**, with
nothing before it. This is `Nat.find` in the form a run's reading wants: the
index, that it is no later than the one it was given, and that every earlier
index misses. -/
theorem exists_first_of {P : ℕ → Prop} {n : ℕ} (hn : P n) :
    ∃ m, m ≤ n ∧ P m ∧ ∀ i, i < m → ¬P i :=
  ⟨Nat.find ⟨n, hn⟩, Nat.find_le hn, Nat.find_spec ⟨n, hn⟩,
    fun _ hi => Nat.find_min ⟨n, hn⟩ hi⟩

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

section Entry

variable {L : Language.{0, 0}} {dt : PfpData L} {A I : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable {R' : Type} [LinearOrder R'] [Finite R']
variable [Language.wide.Structure (Univ A (R')
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd}

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (R')]
  [Language.wide.Structure (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] [LinearOrder A]
  [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] [LinearOrder R'] in
/-- **Every rule the machine can fire outside the post-guess phases keeps the
file, keeps the addressed tracks and writes bits.** The evaluation's rules fire
from an evaluation phase (`nexEvalHosrcF`), and those are post-guess – so a rule
whose source phase is not is one of the outer layer's, where the three facts are
`nexRule_keepsFile_of_ne_eval` and its siblings. -/
theorem nexProgHanded_facts_of_not_postGuess
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hcov : dt.NexCovered PR (dt.regionSpec PR.zero PR.one) args bot)
    (r : R')
    (hph : ¬NexPh.PostGuess (PR.rules r).srcPh) :
    Rule.KeepsFile dt (PR.rules r) ∧
      Rule.KeepsCellTracks dt (PR.rules r) ∧
      Rule.WritesBits dt PR.zero PR.one (PR.rules r) := by
  rcases hcov r with ⟨i, ρ, hr⟩ | ⟨p, hjunk⟩
  case inr => rw [hjunk.1]; exact falseRule_facts PR.zero PR.one p
  rw [hr] at hph ⊢
  -- the site is not the evaluation's: its rules fire from an evaluation phase
  have hi : ∀ e : dt.SEF, i ≠ NexSite.eval e := by
    rintro e rfl
    obtain ⟨p, hp, -⟩ := dt.nexEvalHosrcF (B := Option dt.KIx) (zero := PR.zero)
      (one := PR.one) args e ρ
    exact hph (by rw [show (dt.nexRule PR.one (dt.nullSpec (Option dt.KIx))
      (dt.regionSpec PR.zero PR.one) (dt.nexEvalRuleF PR.zero PR.one args)
      (EvalPh.chk 0) bot (NexSite.eval e) ρ).srcPh = _ from hp]; trivial)
  refine ⟨nexRule_keepsFile_of_ne_eval PR.one PR.zero _ (fun _ _ => rfl) _ _ _ i ρ hi,
    nexRule_keepsCellTracks_of_ne_eval PR.one PR.zero _ (fun _ _ => rfl) _ _ _ i ρ hi,
    nexRule_writesBits_of_ne_eval PR.one PR.zero _ (fun _ _ => rfl) _ _ _ i ρ hi⟩

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (R')] in
/-- **An accepting configuration is in a post-guess phase**, and its state is a
phase state: the accepting predicate names `NexPh.acceptP`, and an accepting
state is canonically padded, so it *is* `stateElt` of its own pointer. This is
what gives the search for the entry something to find. -/
theorem postGuess_of_acc
    (haccPh : ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (f : dt.CtlIx → A), PR.accept p f → p = NexPh.acceptP)
    (hR : PR.table.Reads)
    {c : Config (WPoint (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (hacc : (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Acc c.state) :
    ∃ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      c.state = Sum.inr (stateElt PR.zero p f) ∧ NexPh.PostGuess p := by
  rcases hst : c.state with s | q
  · rw [hst] at hacc; exact hacc.elim
  rw [hst] at hacc
  have hIs : PR.table.IsAcc q := (hR.acc q).mp hacc
  obtain ⟨t, w⟩ := q
  match t with
  | .ctrl r => exact hIs.elim
  | .sym => exact hIs.elim
  | .arg i => exact hIs.elim
  | .phase p =>
    obtain ⟨hpad, hacc'⟩ := hIs
    refine ⟨p, unpad PR.table.payload_le w, ?_, ?_⟩
    · exact congrArg Sum.inr (Prod.ext rfl (pad_unpad _ hpad).symm)
    · rw [haccPh _ _ hacc']
      trivial

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (R')]
  [Language.wide.Structure (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] [LinearOrder A]
  [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] [LinearOrder R'] in
/-- **No rule enters the start phase.** The machine is in it at time zero and
never again – which is what tells a reading that every step after the first
fires a rule that *keeps* the marker rather than writing it. -/
theorem nexProgHanded_dstPh_ne_start
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hcov : NexCovered PR (dt.regionSpec PR.zero PR.one) args bot)
    (r : R') :
    (PR.rules r).dstPh ≠ NexPh.start := by
  rcases hcov r with ⟨i, ρ, hr⟩ | ⟨p, hjunk⟩
  case inr => rw [hjunk.1]; exact hjunk.2.1
  rw [hr]
  match i, ρ with
  | .start, _ => exact fun hc => nomatch hc
  | .approach, Sum.inl _ => exact fun hc => nomatch hc
  | .approach, Sum.inr _ => exact fun hc => nomatch hc
  | .build, Sum.inl _ => exact fun hc => nomatch hc
  | .build, Sum.inr (Sum.inl _) => exact fun hc => nomatch hc
  | .build, Sum.inr (Sum.inr (Sum.inl _)) => exact fun hc => nomatch hc
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact fun hc => nomatch hc
  | .homeBuild, Sum.inl ρ' => cases ρ'; exact fun hc => nomatch hc
  | .homeBuild, Sum.inr _ => exact fun hc => nomatch hc
  | .guess, Sum.inl _ => exact fun hc => nomatch hc
  | .guess, Sum.inr (Sum.inl _) => exact fun hc => nomatch hc
  | .guess, Sum.inr (Sum.inr (Sum.inl _)) => exact fun hc => nomatch hc
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact fun hc => nomatch hc
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => exact fun hc => nomatch hc
  | .homeGuess, Sum.inl ρ' => cases ρ'; exact fun hc => nomatch hc
  | .homeGuess, Sum.inr _ => exact fun hc => nomatch hc
  | .accept, e => exact e.elim
  | .eval e, ρ' =>
    intro hc
    have h := dt.nexEvalRuleF_postGuess (B := Option dt.KIx) (zero := PR.zero)
      (one := PR.one) args e ρ'
    exact (hc ▸ h : NexPh.PostGuess (NexPh.start :
      NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)))

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (R')]
  [Language.wide.Structure (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] [LinearOrder A]
  [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] [LinearOrder R'] in
/-- **The start step writes the marker and the bottom mark**, and it is the only
rule that fires from the start phase. -/
theorem nexProgHanded_setsSlot_wk
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hcov : NexCovered PR (dt.regionSpec PR.zero PR.one) args bot)
    (r : R')
    (hph : (PR.rules r).srcPh = NexPh.start)
    (t : dt.SlotIx) (ht : t = Slot.wk ∨ t = Slot.bot) :
    Rule.SetsSlot dt PR.one t (PR.rules r) := by
  rcases hcov r with ⟨i, ρ, hr⟩ | ⟨p, hjunk⟩
  case inr => rw [hjunk.1] at hph; exact (hjunk.2.1 hph).elim
  rw [hr] at hph ⊢
  match i, ρ with
  | .start, ρ' =>
    exact nexRule_setsSlot_start PR.one _ _ (EvalPh.chk 0) bot ρ' t ht
  | .approach, Sum.inl _ => exact nomatch hph
  | .approach, Sum.inr _ => exact nomatch hph
  | .build, Sum.inl _ => exact nomatch hph
  | .build, Sum.inr (Sum.inl _) => exact nomatch hph
  | .build, Sum.inr (Sum.inr (Sum.inl _)) => exact nomatch hph
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact nomatch hph
  | .homeBuild, Sum.inl ρ' => cases ρ'; exact nomatch hph
  | .homeBuild, Sum.inr _ => exact nomatch hph
  | .guess, Sum.inl _ => exact nomatch hph
  | .guess, Sum.inr (Sum.inl _) => exact nomatch hph
  | .guess, Sum.inr (Sum.inr (Sum.inl _)) => exact nomatch hph
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact nomatch hph
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => exact nomatch hph
  | .homeGuess, Sum.inl ρ' => cases ρ'; exact nomatch hph
  | .homeGuess, Sum.inr _ => exact nomatch hph
  | .accept, e => exact e.elim
  | .eval e, ρ' =>
    obtain ⟨p, hp, -⟩ := dt.nexEvalHosrcF (B := Option dt.KIx) (zero := PR.zero)
      (one := PR.one) args e ρ'
    exact nomatch hp.symm.trans hph

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (R')]
  [Language.wide.Structure (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] [LinearOrder A]
  [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] [LinearOrder R'] in
/-- **Every other rule of the outer layer keeps the marker and the bottom
mark**: the evaluation's fire from a post-guess phase and the start step from the
start phase, so a rule whose source phase is neither leaves them where they
are. -/
theorem nexProgHanded_keepsSlot_wk
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hcov : NexCovered PR (dt.regionSpec PR.zero PR.one) args bot)
    (r : R')
    (hph : ¬NexPh.PostGuess (PR.rules r).srcPh)
    (hst : (PR.rules r).srcPh ≠ NexPh.start)
    (t : dt.SlotIx) (ht : t = Slot.wk ∨ t = Slot.bot) :
    Rule.KeepsSlot dt t (PR.rules r) := by
  rcases hcov r with ⟨i, ρ, hr⟩ | ⟨p, hjunk⟩
  case inr => rw [hjunk.1]; exact falseRule_keepsSlot t p
  rw [hr] at hph hst ⊢
  have hi : ∀ e : dt.SEF, i ≠ NexSite.eval e := by
    rintro e rfl
    obtain ⟨p, hp, -⟩ := dt.nexEvalHosrcF (B := Option dt.KIx) (zero := PR.zero)
      (one := PR.one) args e ρ
    exact hph (by rw [show (dt.nexRule PR.one (dt.nullSpec (Option dt.KIx))
      (dt.regionSpec PR.zero PR.one) (dt.nexEvalRuleF PR.zero PR.one args)
      (EvalPh.chk 0) bot (NexSite.eval e) ρ).srcPh = _ from hp]; trivial)
  have hstart : i ≠ NexSite.start := by
    rintro rfl
    exact hst rfl
  exact nexRule_keepsSlot_wk_bot PR.one PR.zero _ (fun _ _ => rfl) _ _ _ i ρ hi hstart
    t ht

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (R')]
  [Language.wide.Structure (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] [LinearOrder A]
  [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))] [LinearOrder R'] in
/-- **The one way into the post-guess phases is the guess's stop**, and it lands
in the walk home. The sweep over the region is never *done* – where it stops is
the program's choice, so `GuessSpec.Done` is `False` and the exit that would land
in `NexPh.guessDoneP` can never fire – so a rule that leaves the pre-guess phases
leaves them for `NexPh.homeGuessP`. That is the phase a backward reading finds at
its entry, and it is the one `reachesIn_homeGuessTail` runs from. -/
theorem nexProgHanded_dstPh_homeGuess
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hcov : NexCovered PR (dt.regionSpec PR.zero PR.one) args bot)
    (r : R')
    (f : dt.CtlIx → A) (gt : dt.SlotIx → A)
    (hg : (PR.rules r).guard f gt)
    (hsrc : ¬NexPh.PostGuess (PR.rules r).srcPh)
    (hdst : NexPh.PostGuess (PR.rules r).dstPh) :
    (PR.rules r).dstPh = NexPh.homeGuessP := by
  rcases hcov r with ⟨i, ρ, hr⟩ | ⟨p, hjunk⟩
  case inr => rw [hjunk.1] at hdst; exact (hjunk.2.2 hdst).elim
  rw [hr] at hg hsrc hdst ⊢
  match i, ρ with
  | .start, _ => exact hdst.elim
  | .approach, Sum.inl _ => exact hdst.elim
  | .approach, Sum.inr _ => exact hdst.elim
  | .build, Sum.inl _ => exact hdst.elim
  | .build, Sum.inr (Sum.inl _) => exact hdst.elim
  | .build, Sum.inr (Sum.inr (Sum.inl _)) => exact hdst.elim
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact hdst.elim
  | .homeBuild, Sum.inl ρ' => cases ρ'; exact hdst.elim
  | .homeBuild, Sum.inr _ => exact hdst.elim
  | .guess, Sum.inl _ => exact hdst.elim
  | .guess, Sum.inr (Sum.inl ⟨b, x⟩) => exact hdst.elim
  | .guess, Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)) => exact hg.2.elim
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact (hsrc trivial).elim
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr b))) => rfl
  | .homeGuess, Sum.inl ρ' => cases ρ'; exact (hsrc trivial).elim
  | .homeGuess, Sum.inr _ => exact (hsrc trivial).elim
  | .accept, e => exact e.elim
  | .eval e, ρ' =>
    obtain ⟨p, hp, -⟩ := dt.nexEvalHosrcF (B := Option dt.KIx) (zero := PR.zero)
      (one := PR.one) args e ρ'
    exact absurd (by rw [show (dt.nexRule PR.one (dt.nullSpec (Option dt.KIx))
      (dt.regionSpec PR.zero PR.one) (dt.nexEvalRuleF PR.zero PR.one args)
      (EvalPh.chk 0) bot (NexSite.eval e) ρ').srcPh = _ from hp]; trivial) hsrc

end Entry

section Shape

variable {L : Language.{0, 0}} {dt : PfpData L} {A I : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable {R' : Type} [LinearOrder R'] [Finite R']
variable [Language.wide.Structure (Univ A (R')
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd}

omit [Finite A] [Finite dt.KIx] [Nonempty A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (R')] in
/-- **The first post-guess configuration of a run, with its tape recognised.**
Every step before it fires a rule of the outer layer, and those keep the file –
so the shape the channel wrote at time zero is still there, and the tape is an
`ixBack` of a tape state (`exists_ixBack_of_shape`). The phase at that time is
one the machine never leaves, which is what
`DescriptiveComplexity.Pfp.PfpData.not_acc_of_verdict_false_of` asks of its entry.

This is where a backward reading starts: the guess is on the tape, the run from
here on is the evaluation's, and it is deterministic. -/
theorem exists_postGuess_shaped
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hcov : NexCovered PR (dt.regionSpec PR.zero PR.one) args bot)
    (haccPh : ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (f : dt.CtlIx → A), PR.accept p f → p = NexPh.acceptP)
    (hR : PR.table.Reads)
    {lay : Layout dt A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) I}
    {st₀ : TapeSt dt A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) I}
    (g : ℕ → Config (WPoint (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hhead : ∀ i, ∃ v, (g i).head = Sum.inl v)
    (h0 : ShapedAt PR lay st₀ (g 0))
    (n : ℕ)
    (hstep : ∀ i, i < n → (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
        (g i) (g (i + 1)))
    (hacc : (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Acc
        (g n).state) :
    ∃ m, m ≤ n ∧ ShapedAt PR lay st₀ (g m) ∧
      (∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
        (g m).state = Sum.inr (stateElt PR.zero p f) → NexPh.PostGuess p) ∧
      ∀ i, i < m → ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
        (g i).state = Sum.inr (stateElt PR.zero p f) → ¬NexPh.PostGuess p := by
  classical
  -- the accepting configuration is post-guess, so there is a first such time
  obtain ⟨p₀, f₀, hst₀, hpg₀⟩ := postGuess_of_acc haccPh hR hacc
  obtain ⟨m, hmn, hm, hlt⟩ := exists_first_of
    (P := fun i => ∃ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      (g i).state = Sum.inr (stateElt PR.zero p f) ∧ NexPh.PostGuess p)
    (n := n) ⟨p₀, f₀, hst₀, hpg₀⟩
  refine ⟨m, hmn, ?_, ?_, fun i hi p f hs hpg => hlt i hi ⟨p, f, hs, hpg⟩⟩
  · -- before the entry every phase is the outer layer's, so the shape survives
    refine shapedAt_of_seq hR
      (Ph := fun p => ¬NexPh.PostGuess p)
      (fun r hr => nexProgHanded_facts_of_not_postGuess hcov r hr)
      g hhead h0 m (fun i hi => hstep i (by omega))
      (fun i hi p f hs hpg => hlt i hi ⟨p, f, hs, hpg⟩)
  · rintro p f hs
    obtain ⟨p', f', hs', hpg'⟩ := hm
    rw [hs] at hs'
    have hp : PfpTag.phase (R := R')
        (K := dt.KIx) p = PfpTag.phase p' :=
      congrArg Prod.fst (Sum.inr.inj hs')
    rw [PfpTag.phase.inj hp]
    exact hpg'

end Shape

/-! ### The run from the entry, forward again -/

section Tail

variable {L : Language.{0, 0}} {dt : PfpData L} {A : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable [Nonempty dt.KIx] [L.IsRelational] [L.Structure A]
variable [LinearOrder (dt.X.Map A)]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable {R' : Type} [LinearOrder R'] [Finite R']
variable [Language.wide.Structure (Univ A (R')
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite (Univ A (R')
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd}

omit [Nonempty dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **From the entry to the evaluation, at the handed program**: the walk home
and the dispatch (`reachesIn_homeGuessTail`) with the program's rules discharged
(`nexProgHanded_rules`), over the file the channel hands it. The tape is
whatever the guess left – the lemma reads none of it but the marker – so this is
the step a *backward* reading takes from the configuration
`exists_postGuess_shaped` hands it. -/
theorem nexProgHanded_reachesIn_homeGuessTail
    {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {st : TapeSt dt A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (dt.RegIx (A := A) (R' := R')
        (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)))}
    {v y v' : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v)
    (hyv : WMSetLe WMLe v y) (hvv' : WMIncr WMLe v v')
    (f : dt.CtlIx → A)
    (hexG : dt.exitG PR.one (PR.passTracksAt
      (dt.regLaid hlin hord).cell Slot.mir
      (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
      (fun _ => False) v)) :
    (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      ((wideRank y - wideRank v) + 1)
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP f),
        Sum.inl y,
        wideTape (PR.trackTapeAt
          (dt.regLaid hlin hord).cell Slot.mir
          (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
          (fun _ => False))
          (PR.syElt
            PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) f),
        Sum.inl v',
        wideTape (PR.trackTapeAt
          (dt.regLaid hlin hord).cell Slot.mir
          (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
          (fun _ => False))
          (PR.syElt
            PR.blank)⟩ :=
  dt.reachesIn_homeGuessTail (F := dt.regLaid hlin hord) (PR := PR)
    (betaS := dt.nullSpec (Option dt.KIx))
    (ruleE := dt.nexEvalRuleF PR.zero PR.one (fun w => dt.varArgsOf PR.zero PR.one w))
    (evalEntry := .chk 0) (botS := bot) (st := st) (v := v) (y := y) (v' := v')
    hR hlin hwkS hyv hvv' f hexG
    (rEmbS := hE.site) hE.rules_site (rHomeG := hE.homeGuess) hE.rules_homeGuess

/-! ### The tape state the entry carries -/

omit [LinearOrder (dt.X.Map A)]
  [Finite (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **The entry's tape, read as a tape state.** The channel's tape is
recognisable (`tapeShape_initBackReg`), the reading survives to the first
post-guess time (`exists_postGuess_shaped`) and there the tape is an `ixBack`
(`exists_ixBack_of_shape`) whose mirror, target, saved mirror and valuation are
empty. The marker is the one write of the opening the reading has to *read*: the
start step sets it at the cell the head began on and no later rule touches it
(`track_set_of_seq`, `nexProgHanded_setsSlot_wk`, `nexProgHanded_keepsSlot_wk`),
so the state's working track marks that cell alone.

That is every hypothesis the evaluation's entry state is asked for except the
stage tracks, which are the guess's and are read off the same `ixBack`. -/
theorem exists_entry_state
    {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {v₀ : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hvreg : ∀ x : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      ((∃ k, x.1 = PfpTag.arg k) ∨ IsTopNonArg x) → v₀ ≠ wmRegSeg x)
    (g : ℕ → Config (WPoint (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hhead : ∀ i, ∃ v, (g i).head = Sum.inl v)
    (hhead0 : (g 0).head = Sum.inl v₀)
    (hstate0 : (g 0).state = Sum.inr (PR.stElt
      NexPh.start (fun _ => PR.zero)))
    (h0 : (g 0).tape = wideTape (PR.trackTapeAt
      (dt.regLaid hlin hord).cell Slot.mir
      PR.initBackReg (fun _ => False))
      (PR.syElt
        PR.blank))
    (n : ℕ)
    (hstep : ∀ i, i < n → (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
        (g i) (g (i + 1)))
    (hacc : (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Acc
        (g n).state) :
    ∃ m, m ≤ n ∧ ∃ st : TapeSt dt A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (dt.RegIx (A := A) (R' := R')
          (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))),
      (g m).tape = wideTape (PR.trackTapeAt
          (dt.regLaid hlin hord).cell Slot.mir
          (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
          (fun _ => False))
          (PR.syElt
            PR.blank) ∧
      st.wk = (fun r => r = v₀) ∧ st.mir = (fun _ => False) ∧
      st.tgt = (fun _ => False) ∧ st.sav = (fun _ => False) ∧
      st.val = (fun _ => False) ∧ st.bot = (fun r => r = v₀) ∧
      (∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
        (g m).state = Sum.inr (stateElt PR.zero p f) → NexPh.PostGuess p) ∧
      ∃ fm : dt.CtlIx → A, (g m).state = Sum.inr
        (PR.stElt NexPh.homeGuessP fm) := by
  classical
  -- the channel's tape, in the form a reading recognises
  have hmir₀ : ∀ r, PR.initBackReg r Slot.mir =
      PR.zero := fun r =>
    initBackReg_track_zero hlin hR hE.mark hE.blank r Slot.mir
      (fun hc => hc)
  have h0' : (g 0).tape = wideTape (fun r => PR.syElt
      (PR.initBackReg r))
      (PR.syElt
        PR.blank) := by
    rw [h0, show PR.trackTapeAt
      (dt.regLaid hlin hord).cell Slot.mir
      PR.initBackReg (fun _ => False) =
        fun r => PR.syElt
          (PR.passTracksAt
            (dt.regLaid hlin hord).cell Slot.mir
            PR.initBackReg (fun _ => False) r)
        from rfl,
      passTracksAt_of_mir_zero (dt := dt) (dt.regLaid hlin hord).cell _ hmir₀]
  have hshape0 : ShapedAt PR
      (dt.regLaid hlin hord).toLayout (dt.nexEntrySt v₀) (g 0) :=
    ⟨_, h0', tapeShape_initBackReg hlin hord hR hE.mark hE.marked
      hE.blank (fun x hx => hvreg x ((hE.marked x).mp hx))⟩
  -- the first post-guess time, and its shape
  obtain ⟨m, hmn, ⟨rest, htape, hshape⟩, hpg, hlt⟩ :=
    exists_postGuess_shaped hE.covered hE.acceptPh hR g hhead hshape0 n hstep hacc
  obtain ⟨st, hst, hmir, htgt, hsav, hval⟩ :=
    exists_ixBack_of_shape (dt := dt) (dt.regLaid hlin hord).toLayout
      PR.zero_ne_one rest
      (dt.nexEntrySt v₀) hshape.file hshape.cells hshape.bits
  -- the marker: written by the start step, kept by every later rule
  have hne_start : ∀ i, 0 < i → i ≤ n →
      ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      (g i).state = Sum.inr (stateElt PR.zero p f) → p ≠ NexPh.start := by
    intro i hi hin p f hs
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    obtain ⟨r, f', hr⟩ := step_state_dst hR (hstep j (by omega))
    rw [hs] at hr
    have hp : p = (PR.rules r).dstPh :=
      PfpTag.phase.inj (congrArg Prod.fst (Sum.inr.inj hr))
    rw [hp]
    exact nexProgHanded_dstPh_ne_start hE.covered r
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact absurd (hpg NexPh.start _ hstate0) (fun hc => hc)
    · exact hm
  have hset : ∀ t : dt.SlotIx, t = Slot.wk ∨ t = Slot.bot →
      (∀ r, rest r t = bitVal PR.zero PR.one (r = v₀)) := by
    intro t ht
    obtain ⟨rest', htape', hmark⟩ :=
      track_set_of_seq (PR := PR) hR
        (Ph₀ := fun p => p = NexPh.start)
        (Ph := fun p => ¬NexPh.PostGuess p ∧ p ≠ NexPh.start)
        (fun r hr => nexProgHanded_setsSlot_wk hE.covered r hr t ht)
        (fun r hr => nexProgHanded_keepsSlot_wk hE.covered r hr.1 hr.2 t ht)
        g hhead h0'
        (fun r => initBackReg_track_zero hlin hR hE.mark hE.blank r t
          (by rcases ht with rfl | rfl <;> exact fun hc => hc))
        hhead0 m hm0
        (fun i hi => hstep i (by omega))
        (fun p f hs => PfpTag.phase.inj
          (congrArg Prod.fst (Sum.inr.inj (hs.symm.trans hstate0))))
        (fun i hi₀ hi p f hs =>
          ⟨fun hc => hlt i hi p f hs hc, hne_start i hi₀ (by omega) p f hs⟩)
    have hrr : rest' = rest := rest_eq_of_tape (htape'.symm.trans htape)
    rw [hrr] at hmark
    exact hmark
  -- and the phase it lands in is the walk home: the guess's stop is the only
  -- rule that leaves the pre-guess phases
  have hhome : ∃ fm : dt.CtlIx → A, (g m).state = Sum.inr
      (PR.stElt NexPh.homeGuessP fm) := by
    obtain ⟨jm, rfl⟩ : ∃ jm, m = jm + 1 := ⟨m - 1, by omega⟩
    obtain ⟨r, fr, gr, hgr, hsr, hdr⟩ := step_rule hR (hstep jm (by omega))
    have hsrcne : ¬NexPh.PostGuess (PR.rules r).srcPh :=
      fun hc => hlt jm (by omega) _ _ hsr hc
    have hdstpg : NexPh.PostGuess
        (PR.rules r).dstPh := hpg _ _ hdr
    refine ⟨(PR.rules r).dstSt fr gr, ?_⟩
    rw [hdr, nexProgHanded_dstPh_homeGuess hE.covered r fr gr hgr hsrcne hdstpg]
    rfl
  refine ⟨m, hmn, st, ?_, ?_, hmir, htgt, hsav, hval, ?_, hpg, hhome⟩
  · rw [htape, hst, show PR.trackTapeAt
      (dt.regLaid hlin hord).cell Slot.mir
      (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
      (fun _ => False) =
        fun r => PR.syElt
          (PR.passTracksAt
            (dt.regLaid hlin hord).cell Slot.mir
            (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
            (fun _ => False) r)
        from rfl,
      passTracksAt_of_mir_zero (dt := dt) (dt.regLaid hlin hord).cell _
        (fun r => by rw [← hst]; exact hshape.cells r Slot.mir (Or.inl rfl))]
  · refine ixBack_wk_inv (dt := dt) (dt.regLaid hlin hord).toLayout PR.zero_ne_one st
      (fun r => ?_)
    rw [← hst]
    exact hset Slot.wk (Or.inl rfl) r
  · refine ixBack_bot_inv (dt := dt) (dt.regLaid hlin hord).toLayout PR.zero_ne_one st
      (fun r => ?_)
    rw [← hst]
    exact hset Slot.bot (Or.inr rfl) r

/-! ### No acceptance, from a false verdict at the entry -/

omit [LinearOrder (dt.X.Map A)] [Nonempty dt.KIx]
  [Finite (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **An entry whose verdict is false accepts nothing.** From the configuration a
backward reading finds – the walk home, at the tape state it recovered – the
machine's run is forced: the walk home and the dispatch
(`nexProgHanded_reachesIn_homeGuessTail`), then the evaluation, which ends in the
accepting phase with the bit the sentence's own value. If that bit is clear the
run is a dead end, and from a post-guess configuration the machine has only one
run (`not_acc_of_verdict_false_of`) – so nothing below the entry accepts.

This is the backward direction's last step: the reading supplies the entry, the
evaluation supplies the verdict, and the false verdict of a no-instance closes
it. -/
theorem not_acc_of_entry_verdict
    {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {st : TapeSt dt A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (dt.RegIx (A := A) (R' := R')
        (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)))}
    {v₀ y v' : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hwk : st.wk = fun r => r = v₀) (hmirS : st.mir = fun _ => False)
    (hyv : WMSetLe WMLe v₀ y) (hvv' : WMIncr WMLe v₀ v')
    (fm : dt.CtlIx → A)
    (hexG : dt.exitG PR.one (PR.passTracksAt
      (dt.regLaid hlin hord).cell Slot.mir
      (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
      (fun _ => False) v₀))
    {e : ℕ} {fq : dt.CtlIx → A}
    {cT : Config (WPoint (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (heval : (wideData (Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn e
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) fm),
        Sum.inl v',
        wideTape (PR.trackTapeAt
          (dt.regLaid hlin hord).cell Slot.val
          (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt
            PR.blank)⟩ cT)
    (hstateT : cT.state = Sum.inr
      (PR.stElt NexPh.acceptP fq))
    (hbit : ¬(dt.varArgsOf PR.zero PR.one none).accBit fq)
    {entry c : Config (WPoint (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (hentrySt : entry.state = Sum.inr
      (PR.stElt NexPh.homeGuessP fm))
    (hentryHd : entry.head = Sum.inl y)
    (hentryTp : entry.tape = wideTape (PR.trackTapeAt
      (dt.regLaid hlin hord).cell Slot.mir
      (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
      (fun _ => False))
      (PR.syElt
        PR.blank))
    (hreach : Relation.ReflTransGen (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step entry c)
    (hacc : (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Acc c.state) :
    False := by
  have hentry : entry = ⟨Sum.inr (PR.stElt
      NexPh.homeGuessP fm), Sum.inl y,
      wideTape (PR.trackTapeAt
        (dt.regLaid hlin hord).cell Slot.mir
        (dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le st)
        (fun _ => False))
        (PR.syElt
          PR.blank)⟩ :=
    Config.ext hentrySt hentryHd hentryTp
  -- the walk home and the dispatch, then the evaluation
  have htail := dt.nexProgHanded_reachesIn_homeGuessTail hE hR hlin hord
    (st := st) (v := v₀) (y := y) (v' := v') hwk hyv hvv' fm hexG
  have hjoin : Relation.ReflTransGen (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step entry cT := by
    rw [hentry]
    exact htail.reflTransGen.trans
      ((config_openingEnd_eq_evalStart (PR := PR)
        (F := dt.regLaid hlin hord) hmirS (NexPh.evalP (.chk 0)) fm v') ▸
        heval.reflTransGen)
  exact not_acc_of_verdict_false_of hR (hE.uniqueFrom hR hlin) hE.srcPh_ne_acceptP
    hE.acceptPh
    (entry := entry) (cT := cT) (c := c)
    (fun p f hs => by
      rw [hentrySt] at hs
      have hp : NexPh.homeGuessP = p :=
        PfpTag.phase.inj (congrArg Prod.fst (Sum.inr.inj hs))
      rw [← hp]
      trivial)
    hjoin hstateT (fun hc => hbit ((hE.accept_iff _ _).mp hc).2) hreach hacc

end Tail

end PfpData

end Pfp

end DescriptiveComplexity
