/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexBuild
import DescriptiveComplexity.Problems.Wide.NexGuess
import DescriptiveComplexity.Problems.Wide.NexDet
import DescriptiveComplexity.Problems.Wide.DrawInit
import DescriptiveComplexity.Problems.Wide.NexEval
import DescriptiveComplexity.Problems.Wide.DrawRegion

/-!
# The clocked program's whole run, and its clock

The two halves are counted separately – the opening and the evaluation
(`DescriptiveComplexity.Draw.DrawData.nexEval_reachesIn`) – and this file puts
them together and compares the sum with the clock.

The opening is `DescriptiveComplexity.Draw.DrawData.reachesIn_openingRegion`,
here: the approach walk up to the file's base, the file-laying sweep, and the
guess along the *region* below the file – one bit per address, which is what the
guessed relations are – for
`2·R + 2·base + (the guessed stretch out and back) + 4`, and `openingRegion_le`
bounds that
by the number of addresses.

Two things are worth naming. The **presentation bridge**: the opening is stated
with the tape walked along the mirror track and the evaluation along VAL, and
the two are the same tape whenever both marks are the background's own
(`DescriptiveComplexity.Draw.trackTape_of_back`), so the caller hands that
equality over rather than either run being restated. And the **arithmetic**:
the total is «opening + rounds × width», which is `mul_add_lt_two_pow`'s shape –
so what the clock asks is that the opening and each of the evaluation's two
factors fit the region, with one surplus block of slack for the additive term.
The opening is a bare number there
(`nexTotal_lt_two_pow`), so either shape of it is compared the same way.

The initial end is here as well, and it is three small facts.
`DescriptiveComplexity.Draw.Prog.trackTapeAt_initBack` says the all-blank tape is
the pass-layer presentation at *any* file – which a clocked program needs,
because its file does not exist at time zero – and
`DescriptiveComplexity.Draw.DrawData.startBack` with `startBack_frame` /
`startBack_wr` is the background the opening's first step leaves: the one it
started from with the marker planted, which is the frame condition and the write
that step asks for.

The forward direction lands here too (`nexProg_wideAccept`): an accepting run
of fewer than `2 ^ n` steps from the initial configuration is a yes-instance of
`DescriptiveComplexity.WideAccept`. Two of its hypotheses are `rfl` at the
assembled program, and that is the point of the program **declining the input
channel's marks**: with `mark` the blank, the tape is blank everywhere at time
zero and the channel's ruler is not there to be mistaken for a register
(`trackTape_blank_congr` for the presentations).

The backward direction's foundation is here as well: `nexProg_sepOn` – the
program separates at every post-guess phase, across sites by the owner map and
within a site by `nexSep_postGuess` – and `nexProg_uniqueFrom`, which is what a
reduction reads its certificate off an *arbitrary* accepting run with. The fact
it stands on – that the evaluation's rules never leave the post-guess phases –
is proved, not assumed:
`nexEvalRuleF_postGuess`, and under it a chain of «this machinery leaves only
into its own phases or its exit» lemmas, one per builder, down to the trips.
-/

namespace DescriptiveComplexity

namespace Draw

namespace DrawData

open FirstOrder

open Language Structure

section Total

variable {A : Type} {M : TMData A}

/-- **The clocked program's run, summed**: the opening, the evaluation and the
step that leaves it. Nothing here is about the program – the three legs are the
caller's – and what it records is the arithmetic: an opening of `o`, an
evaluation of `e`, and one step to accept. -/
theorem reachesIn_nexTotal {o e : ℕ} {c₀ c₁ c₂ c₃ : Config A}
    (hopen : M.ReachesIn o c₀ c₁) (heval : M.ReachesIn e c₁ c₂)
    (hexit : M.Step c₂ c₃) : M.ReachesIn (o + e + 1) c₀ c₃ :=
  (hopen.trans heval).tail hexit

end Total

section Bridge

variable {L : Language.{0, 0}} {dt : DrawData L} {A R' P' I : Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd}

/-- **Two presentations of one tape**: a run stated along a track whose digits
the background already carries is the same tape as one stated along another such
track, so a leg walking the mirror composes with a leg walking VAL without
either being restated. -/
theorem trackTape_ixBack_congr {F : LaidFile dt A R' P' I}
    {st : TapeSt dt A R' P' I} {t t' : dt.SlotIx} {m m' : I → Prop}
    (hm : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r t =
      bitVal PR.zero PR.one (bitAtOf F.cell m r))
    (hm' : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r t' =
      bitVal PR.zero PR.one (bitAtOf F.cell m' r)) :
    PR.trackTapeAt F.cell t
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m =
      PR.trackTapeAt F.cell t'
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m' :=
  (trackTape_of_back F.toIxFile hm).trans (trackTape_of_back F.toIxFile hm').symm

/-- **The mirror and VAL presentations agree**: the opening walks the mirror and
the evaluation walks VAL, and both marks are the state's own, so the two runs
compose on the nose. -/
theorem trackTape_ixBack_mir_val {F : LaidFile dt A R' P' I}
    {st : TapeSt dt A R' P' I} :
    PR.trackTapeAt F.cell Slot.mir
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir =
      PR.trackTapeAt F.cell Slot.val
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val :=
  trackTape_ixBack_congr (fun _ => rfl) (fun _ => rfl)

/-- **The opening leaves the tape the evaluation starts from**: the opening
walks the mirror at the empty mark, the evaluation walks VAL at the state's own,
and the state whose mirror is empty presents the same tape either way. This is
the one rewrite between `reachesIn_openingRegion` and
`DescriptiveComplexity.Draw.DrawData.nexIxEvalB_reachesIn`. -/
theorem trackTape_ixBack_mir_empty_val {F : LaidFile dt A R' P' I}
    {st : TapeSt dt A R' P' I} (hmir : st.mir = fun _ => False) :
    PR.trackTapeAt F.cell Slot.mir
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) =
      PR.trackTapeAt F.cell Slot.val
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val := by
  rw [← hmir]
  exact trackTape_ixBack_mir_val

/-- **The opening's last configuration is the evaluation's first**: same phase,
same head, and the same tape – the opening presents it along the mirror at the
empty mark, the evaluation along VAL at the state's own, and a state whose
mirror is empty presents both the same way. This is the junction of the two
legs: with it the whole run is `hopen.trans heval`, and
`DescriptiveComplexity.Draw.DrawData.nexProg_wideAccept_of_legs` does the clock. -/
theorem config_openingEnd_eq_evalStart {F : LaidFile dt A R' P' I}
    {st : TapeSt dt A R' P' I} (hmir : st.mir = fun _ => False)
    (p : P') (f : dt.CtlIx → A) (w : Univ A R' P' dt.KIx dt.dd → Prop) :
    (⟨Sum.inr (PR.stElt p f), Sum.inl w,
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False))
          (PR.syElt PR.blank)⟩ :
      Config (WPoint (Univ A R' P' dt.KIx dt.dd))) =
      ⟨Sum.inr (PR.stElt p f), Sum.inl w,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  rw [trackTape_ixBack_mir_empty_val hmir]

end Bridge

section Init

variable {L : Language.{0, 0}} {dt : DrawData L} {A R' P' I : Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
variable {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd}

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Finite dt.KIx] in
/-- **A blank tape is any presentation of the blank background**: a program that
declines the input channel's marks starts with every cell blank, and that tape
is what a run stated along *any* clear track begins from. This is the bridge
between the initial configuration
(`DescriptiveComplexity.Draw.Prog.wideAccept_prog` presents it along the
channel's file) and the opening's own presentation along the mirror. -/
theorem trackTape_blank_congr {I' : Type}
    {cell : I → (Univ A R' P' dt.KIx dt.dd → Prop)}
    {cell' : I' → (Univ A R' P' dt.KIx dt.dd → Prop)}
    {t t' : dt.SlotIx} {rest rest' : (Univ A R' P' dt.KIx dt.dd → Prop) →
      dt.SlotIx → A}
    (hrest : ∀ r, rest r = PR.blank) (hrest' : ∀ r, rest' r = PR.blank)
    (hb : PR.blank t = PR.zero) (hb' : PR.blank t' = PR.zero) :
    PR.trackTapeAt cell t rest (fun _ => False) =
      PR.trackTapeAt cell' t' rest' (fun _ => False) := by
  classical
  refine funext fun r => ?_
  change PR.syElt (fun s => if s = t
      then bitVal PR.zero PR.one (bitAtOf cell (fun _ => False) r) else rest r s) =
    PR.syElt (fun s => if s = t'
      then bitVal PR.zero PR.one (bitAtOf cell' (fun _ => False) r) else rest' r s)
  refine congrArg _ (funext fun s => ?_)
  have hnone : ∀ {J : Type} (c : J → (Univ A R' P' dt.KIx dt.dd → Prop)),
      bitVal PR.zero PR.one (bitAtOf c (fun _ => False) r) = PR.zero := by
    intro J c
    exact bitVal_neg (fun hc => hc.choose_spec.2)
  by_cases hs : s = t
  · subst hs
    rw [if_pos rfl, hnone]
    by_cases hs' : s = t'
    · rw [if_pos hs', hnone]
    · rw [if_neg hs', hrest', hb]
  · rw [if_neg hs, hrest]
    by_cases hs' : s = t'
    · rw [if_pos hs', hnone, hs', hb']
    · rw [if_neg hs', hrest']

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Finite dt.KIx] in
/-- **A tape walked along an empty track does not depend on which file presents
it**: the only cell-dependent part of the presentation is the bit at the walked
mark, and an empty mark has none. This is the bridge a program *handed* its file
needs, where `trackTape_blank_congr` is the one a program starting on a blank
tape needs: there the background is the blank, here it is the channel's own
marks, and neither is read by the presentation. -/
theorem trackTape_empty_congr {I' : Type}
    {cell : I → (Univ A R' P' dt.KIx dt.dd → Prop)}
    {cell' : I' → (Univ A R' P' dt.KIx dt.dd → Prop)}
    {t : dt.SlotIx} {rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A} :
    PR.trackTapeAt cell t rest (fun _ => False) =
      PR.trackTapeAt cell' t rest (fun _ => False) := by
  classical
  refine funext fun r => ?_
  change PR.syElt (fun s => if s = t
      then bitVal PR.zero PR.one (bitAtOf cell (fun _ => False) r) else rest r s) =
    PR.syElt (fun s => if s = t
      then bitVal PR.zero PR.one (bitAtOf cell' (fun _ => False) r) else rest r s)
  refine congrArg _ (funext fun s => ?_)
  have hnone : ∀ {J : Type} (c : J → (Univ A R' P' dt.KIx dt.dd → Prop)),
      bitVal PR.zero PR.one (bitAtOf c (fun _ => False) r) = PR.zero := by
    intro J c
    exact bitVal_neg (fun hc => hc.choose_spec.2)
  by_cases hs : s = t
  · subst hs
    rw [if_pos rfl, if_pos rfl, hnone, hnone]
  · rw [if_neg hs, if_neg hs]

end Init

/-! ### The opening, with the guess over the region -/

section Opening

variable {L : Language.{0, 0}} {dt : DrawData L} {A R' PE SE : Type}
variable {ShE : SE → Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [Nonempty A] [Finite A] [Finite R']
variable [Finite dt.KIx]
variable [LinearOrder (NexPh (Option dt.KIx) PE)]
variable [Finite (NexPh (Option dt.KIx) PE)]
variable [Language.wide.Structure
  (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {coord : Fin dt.dd → dt.CtlIx} {f₀ : dt.CtlIx → A}
variable {ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE)}
variable {evalEntry : PE}

/-- **The background the opening's first step leaves**: the one it started from,
with the marker planted at the address the head is on. A clocked program starts
on a blank tape, so this – with `DescriptiveComplexity.Draw.Prog.initBack` for the
background – is what its opening runs from. -/
noncomputable def startBack
    (bg : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A)
    (one : A) (v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A :=
  open Classical in
  fun r =>
    if r = v then Function.update (Function.update (bg r) Slot.wk one) Slot.bot one
    else bg r

omit [Fintype dt.CtlIx] [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R']
  [Nonempty A] [Finite A] [Finite R'] [Finite dt.KIx]
  [LinearOrder (NexPh (Option dt.KIx) PE)] [Finite (NexPh (Option dt.KIx) PE)]
  [Language.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **Planting the marker changes nothing elsewhere**: the frame condition of the
opening's first step. -/
theorem startBack_frame
    {bg : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {one : A} {v r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hr : r ≠ v) : dt.startBack bg one v r = bg r := by
  classical
  exact if_neg hr

omit [LinearOrder A] [LinearOrder R'] [Nonempty A] [Finite A] [Finite R']
  [Finite dt.KIx] [LinearOrder (NexPh (Option dt.KIx) PE)]
  [Finite (NexPh (Option dt.KIx) PE)]
  [Language.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **Planting the two marks is the write the opening's first step makes**: at
the address the head is on, the presentation with them is the presentation
without them, updated at the marker slot and at the bottom mark's. -/
theorem startBack_wr
    {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}
    {I : Type} (cell : I → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop))
    {bg : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    PR.passTracksAt cell Slot.mir (dt.startBack bg PR.one v) (fun _ => False) v =
      Function.update (Function.update
        (PR.passTracksAt cell Slot.mir bg (fun _ => False) v)
        Slot.wk PR.one) Slot.bot PR.one := by
  classical
  funext s
  have hbg : dt.startBack bg PR.one v v =
      Function.update (Function.update (bg v) Slot.wk PR.one) Slot.bot PR.one :=
    if_pos rfl
  by_cases hb : s = Slot.bot
  · subst hb
    rw [Function.update_self]
    change (if (Slot.bot : dt.SlotIx) = Slot.mir then _
      else dt.startBack bg PR.one v v Slot.bot) = PR.one
    rw [if_neg (by exact fun hc => nomatch hc), hbg, Function.update_self]
  · rw [Function.update_of_ne hb]
    by_cases hs : s = Slot.wk
    · subst hs
      rw [Function.update_self]
      change (if (Slot.wk : dt.SlotIx) = Slot.mir then _
        else dt.startBack bg PR.one v v Slot.wk) = PR.one
      rw [if_neg (by exact fun hc => nomatch hc), hbg,
        Function.update_of_ne (by exact fun hc => nomatch hc), Function.update_self]
    · rw [Function.update_of_ne hs]
      change (if s = (Slot.mir : dt.SlotIx) then _ else dt.startBack bg PR.one v v s) =
        if s = (Slot.mir : dt.SlotIx) then _ else bg v s
      by_cases hm : s = Slot.mir
      · rw [if_pos hm, if_pos hm]
      · rw [if_neg hm, if_neg hm, hbg, Function.update_of_ne hb,
          Function.update_of_ne hs]

/-! ### The state a clocked program starts in

Its first step plants the marker at the empty address and nothing else has been
written, so the state is clear but for the marker – and its background is the
blank tape everywhere off the file, which is what the opening's frame
hypotheses (`hbelow`, `habove`, `hwr`) ask of the caller. -/

variable (dt) in
/-- **The state a clocked program enters its opening in**: every register and
every track clear, the marker *and the bottom mark* at the address the head
stands on – the two the opening's first step writes, and the two the
evaluation's walks read. -/
noncomputable def nexEntrySt {I : Type}
    (v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    TapeSt dt A R' (NexPh (Option dt.KIx) PE) I where
  mir := fun _ => False
  tgt := fun _ => False
  sav := fun _ => False
  val := fun _ => False
  old := fun _ _ => False
  new := fun _ _ => False
  wk := fun r => r = v
  bot := fun r => r = v
  ltp := fun _ => False

omit [Fintype dt.CtlIx] [Fintype dt.SlotIx] [Nonempty A] [Finite A] [Finite R']
  [Finite dt.KIx] [LinearOrder (NexPh (Option dt.KIx) PE)]
  [Finite (NexPh (Option dt.KIx) PE)] [LinearOrder A] [LinearOrder R']
  [Language.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **Off the file, the entry state presents the blank tape with the marker
planted**: the equality the opening's `hbelow` and `habove` ask for, at the
initial background of a program whose channel marks are blank. -/
theorem ixBack_nexEntrySt {I : Type}
    {lay : Layout dt A R' (NexPh (Option dt.KIx) PE) I} {zero one : A}
    {v r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hr : ∀ u : I, r ≠ lay.cell u) :
    dt.ixBack lay zero one dt.dd0Le (dt.nexEntrySt v) r =
      dt.startBack (fun _ _ => zero) one v r := by
  classical
  by_cases hrv : r = v
  · subst hrv
    funext s
    rw [show dt.startBack (fun _ _ => zero) one r r =
      Function.update (Function.update (fun _ : dt.SlotIx => zero) Slot.wk one)
        Slot.bot one from if_pos rfl]
    have hno : ¬∃ u : I, r = lay.cell u := fun hc => hr hc.choose hc.choose_spec
    have hne : ∀ b : dt.SlotIx, b ≠ Slot.wk → b ≠ Slot.bot →
        Function.update (Function.update (fun _ : dt.SlotIx => zero) Slot.wk one)
          Slot.bot one b = zero :=
      fun b hb hb' => by
        rw [Function.update_of_ne hb', Function.update_of_ne hb]
    cases s with
    | reg => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact bitVal_neg hno
    | regFirst =>
      rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]
      exact bitVal_neg fun hc => hr hc.choose hc.choose_spec.1
    | regLast =>
      rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]
      exact bitVal_neg fun hc => hr hc.choose hc.choose_spec.1
    | blk b =>
      rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]
      exact bitVal_neg fun hc => hr hc.choose hc.choose_spec.1
    | name j => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact dif_neg hno
    | pdd =>
      rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]
      exact bitVal_neg fun hc => hr hc.choose hc.choose_spec.1
    | mir => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact bitVal_neg fun hc => hc.choose_spec.2
    | tgt => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact bitVal_neg fun hc => hc.choose_spec.2
    | sav => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact bitVal_neg fun hc => hc.choose_spec.2
    | val => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact bitVal_neg fun hc => hc.choose_spec.2
    | wk =>
      rw [Function.update_of_ne (by exact fun hc => nomatch hc), Function.update_self]
      exact bitVal_pos rfl
    | bot => rw [Function.update_self]; exact bitVal_pos rfl
    | ltp => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact bitVal_neg not_false
    | old i => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact bitVal_neg not_false
    | new i => rw [hne _ (by exact fun hc => nomatch hc)
        (by exact fun hc => nomatch hc)]; exact bitVal_neg not_false
  · rw [dt.startBack_frame hrv]
    exact dt.ixBack_of_not_reg hr hrv hrv not_false
      (fun _ => not_false) (fun _ => not_false)

/-- **The clocked program's opening**: the opening step, the **approach walk**
up to the file's base, the file-laying phase, the walk home with the turn into
the guess, the *region*-wide guess with its stop and its own walk home, and the
dispatch into the evaluation.

The file is laid **above** the program's data and the certificate is guessed
**below** it, which is what lets a stage atom seek to a dictionary entry: the
entry is a logical address and every logical address is below every register.
The approach is the price of that arrangement – the
base is not the marker's neighbour, so getting there is a walk and not a step –
and where it stops is the program's choice, a machine having no landmark but the
cell it started on. -/
theorem reachesIn_openingRegion (hcoord : Function.Injective coord)
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    (hmir : ∀ u, ¬st.mir u) (htgt : ∀ u, ¬st.tgt u) (hsav : ∀ u, ¬st.sav u)
    (hval : ∀ u, ¬st.val u)
    (hwk : ∀ v, ¬st.wk ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hbotR : ∀ v, ¬st.bot ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hltp : ∀ v, ¬st.ltp ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hold : ∀ i v, ¬st.old i ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hnew : ∀ i v, ¬st.new i ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    {v v' v₁ x s₀ top : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v) (hv0 : wideRank v = 0)
    (hle : WMSetLe WMLe v
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkTop A dt.KIx dt.dd)))
    -- The approach: one step off the marker, a walk, and the step that starts
    -- the file at the base the walk has reached.
    (hvi₁ : WMIncr WMLe v v₁) (hwalk : WMSetLe WMLe v₁ x)
    (hxb : WMIncr WMLe x
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)))
    -- The guess starts at the marker's neighbour, below the file.
    (hs₀ : WMIncr WMLe v s₀)
    (hvi' : WMIncr WMLe v v')
    {bg bg₀ : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) →
      dt.SlotIx → A}
    (hframe : ∀ r, r ≠ v → bg₀ r = bg r)
    (hwr : PR.passTracksAt (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
        bg₀ (fun _ => False) v =
      Function.update (Function.update (PR.passTracksAt
        (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir bg
        (fun _ => False) v) Slot.wk PR.one) Slot.bot PR.one)
    (hbelow : ∀ r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop,
      WMSetLt WMLe r
          ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)) →
      dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le st r = bg₀ r)
    (habove : ∀ r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop,
      ¬WMSetLt WMLe r (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) →
      dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le st r = bg₀ r)
    (σ : dt.d.B.ι →
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    (htop : WMSetLe WMLe s₀ top)
    (htopne : ∃ y, top y)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r top → (σ i r ↔ st.old i r))
    (hexB : dt.exitG PR.one (PR.passTracksAt
      (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
      (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le st) (fun _ => False) v))
    (hexG : dt.exitG PR.one (PR.passTracksAt
      (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
      (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le { st with old := σ }) (fun _ => False) v))
    {rEmb0 : ∀ i : NexSite SE,
      NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
    (hrules0 : ∀ (i : NexSite SE)
        (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
      PR.rules (rEmb0 i ρ) =
        dt.nexRule PR.one (dt.buildSpec PR.zero PR.one coord)
          (dt.regionSpec PR.zero PR.one) ruleE evalEntry
          (blkBot A dt.KIx dt.dd).1 i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (2 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 2 * base +
        ((wideRank top - wideRank s₀) + wideRank top) + 4)
      ⟨Sum.inr (PR.stElt NexPh.start
          (dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)),
        Sum.inl v,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir bg (fun _ => False)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry)
          (dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)),
        Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout
            PR.zero PR.one dt.dd0Le { st with old := σ }) (fun _ => False))
          (PR.syElt PR.blank)⟩ := by
  have hstart := dt.step_startBuild hR h hpos (le_of_lt hbase) hvi₁ hframe hwr
    (f := dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2) hrules0
  have hwalkR := dt.reachesIn_approachWalk hR h hpos (le_of_lt hbase) hwalk
    (m := fun _ => False) (rest := bg₀)
    (f := dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2) hrules0
  have henter := dt.step_approachEnter hR h hpos (le_of_lt hbase) hxb
    (m := fun _ => False) (rest := bg₀)
    (f := dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2) hrules0
  have hbuild := dt.reachesIn_buildPhase (f₀ := f₀) hcoord hR h hpos hbase hmir htgt
    hsav hval hwk hbotR hltp hold hnew hwkS hv0 hle hbelow habove hrules0
  have hmid := dt.step_homeBuildExit hR h hpos (le_of_lt hbase) hs₀ hexB hrules0
    (f := dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)
  rw [show (dt.buildSpec PR.zero PR.one coord).st0
        (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)
        (PR.passTracksAt (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
          (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero
            PR.one dt.dd0Le st) (fun _ => False) v) =
      dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2 from
    dt.ctlOf_ctlOf coord f₀ _ _] at hmid
  have hguess := reachesIn_guessRegionPhase (v := v)
    (F := dt.blkLaid h hpos (le_of_lt hbase)) (m := fun _ => False)
    (f₀ := dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2) hrules0 hR h σ
    (fun i => by intro hc; exact nomatch hc) (by intro hc; exact nomatch hc)
    (blkBot A dt.KIx dt.dd).1 hwkS htop
    (wmSetLt_of_wmIncr_le h hs₀ ((isLinOrd_wmSetLe h).1 _)) htopne
    (fun ρ => hrules0 .homeGuess (Sum.inl ρ)) hout
  have hexit := dt.step_homeGuessExit hR h hpos (le_of_lt hbase) hvi' hexG hrules0
    (f := dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)
  -- The approach costs the base: one step off the marker, the walk, and the
  -- step that lands on the first register.
  have hrb : wideRank ((dt.blkLaid h hpos (le_of_lt hbase)).cell
      (blkBot A dt.KIx dt.dd)) = base := by
    rw [dt.wideRank_blkLaid_cell h hpos (le_of_lt hbase) (blkBot A dt.KIx dt.dd),
      ixRank_of_bot (Wide.isLinOrd_blkLe dt.KIx A dt.dd)
        (blkLe_blkBot A dt.KIx dt.dd)]
    omega
  have hr₁ : wideRank v₁ = wideRank v + 1 := wideRank_incr h hvi₁
  have hrx : wideRank ((dt.blkLaid h hpos (le_of_lt hbase)).cell
      (blkBot A dt.KIx dt.dd)) = wideRank x + 1 := wideRank_incr h hxb
  have hrxle : wideRank v₁ ≤ wideRank x := wideRank_mono h hwalk
  exact ((((((TMData.reachesIn_of_step hstart).trans hwalkR).tail henter).trans
    hbuild).tail hmid).trans hguess).tail hexit |>.mono (by omega)


omit [Nonempty A] [Finite A] [Finite R'] [Finite dt.KIx]
  [Finite (NexPh (Option dt.KIx) PE)]
  [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The two exits of the walks home are free at the marker**: the guard they
fire under says the working marker is here and this cell is no register, and a
state that keeps its marker at an address off the file says both. So a program
that walks home to its own marker owes nothing for the turn. -/
theorem exitG_ixBack_of_wk {I : Type} {F : LaidFile dt A R' (NexPh (Option dt.KIx) PE) I}
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    {v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwk : st.wk v) (hne : ∀ u : I, v ≠ F.cell u)
    {t : dt.SlotIx} (htw : (Slot.wk : dt.SlotIx) ≠ t)
    (htr : (Slot.reg : dt.SlotIx) ≠ t) (m : I → Prop) :
    dt.exitG PR.one (PR.passTracksAt F.cell t
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m v) := by
  refine ⟨?_, ?_⟩
  · rw [Prog.passTracks_of_ne htw, ixBack_wk]
    exact bitVal_pos hwk
  · rw [Prog.passTracks_of_ne htr,
      show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v Slot.reg =
        bitVal PR.zero PR.one (∃ u : I, v = F.cell u) from rfl,
      bitVal_neg (fun hc => hne hc.choose hc.choose_spec)]
    exact PR.zero_ne_one

/-! ### What the guess writes

The stage tracks a clocked program guesses are an assignment's, **restricted to
the stretch the guess sweeps** – the file's first register up to the end marker.
Restricting them is what makes the opening's frame condition true (outside that
stretch the tracks are the entry state's, which is empty), and it costs the
dictionary nothing, since every entry the evaluation reads is inside the stretch
(a track marks no empty address, `nonempty_of_trackOf`). -/

section Guessed

variable {L : Language.{0, 0}} {dt : DrawData L} {A R' PE : Type}
variable [LinearOrder A] [L.Structure A]
variable [Language.wide.Structure
  (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]

variable (dt) in
/-- **The tracks the guess writes**: an assignment's, inside the swept
stretch. -/
def guessTracks (zero one : A) (σ : dt.d.B.Assignment (dt.X.Map A))
    (bot top : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    dt.d.B.ι → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop :=
  fun iv r => trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ r ∧
    WMSetLe WMLe bot r ∧ WMSetLt WMLe r top

/-- **Outside the swept stretch the guess writes nothing** — the opening's
`hout`, at tracks that are an assignment's inside it. -/
theorem not_guessTracks_out
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {zero one : A} {σ : dt.d.B.Assignment (dt.X.Map A)}
    {bot top r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hr : WMSetLt WMLe r bot ∨ ¬WMSetLt WMLe r top) (iv : dt.d.B.ι) :
    ¬dt.guessTracks zero one σ bot top iv r := by
  rintro ⟨-, hlo, hhi⟩
  rcases hr with hr | hr
  · exact ((wmSetLt_iff _ _).mp hr).2
      ((isLinOrd_wmSetLe h).2.2.1 r bot ((wmSetLt_iff _ _).mp hr).1 hlo)
  · exact hr hhi

omit [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **Inside it they are the assignment's** — the evaluation's `hdict`, at every
address of the stretch. -/
theorem guessTracks_iff
    {zero one : A} {σ : dt.d.B.Assignment (dt.X.Map A)}
    {bot top s : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hlo : WMSetLe WMLe bot s) (hhi : WMSetLt WMLe s top) (iv : dt.d.B.ι) :
    dt.guessTracks zero one σ bot top iv s ↔
      trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ s :=
  ⟨fun h => h.1, fun h => ⟨h, hlo, hhi⟩⟩

/-- **Below the guess's top the tracks are the assignment's, and nothing has to
be said about the bottom**: a track marks no empty address
(`nonempty_of_trackOf`), so an address it marks is at or above the marker's
neighbour by `wmSetLe_succ_bot_of_nonempty`, which is where the guess begins.
This is the `hdict` an evaluation asks for, and it asks of the *data* only what
`wmSetLt_ixStageTgt_logicalTop` already proves: that a dictionary address is
below the last logical one.

What it asks of the **reduction** is that every fixed-point variable have an
argument. A nullary one has the empty address for its entry, which is the
marker's own cell and below every stretch the machine writes; padding its
relation with a dummy argument costs nothing and is the intended reading. -/
theorem guessTracks_iff_of_lt
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {zero one : A} {σ : dt.d.B.Assignment (dt.X.Map A)}
    {s₀ top s : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hs₀ : WMIncr WMLe (fun _ => False) s₀)
    (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (hhi : WMSetLt WMLe s top) (iv : dt.d.B.ι) :
    dt.guessTracks zero one σ s₀ top iv s ↔
      trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ s :=
  ⟨fun hg => hg.1, fun hg =>
    ⟨hg, wmSetLe_succ_bot_of_nonempty h hs₀
      (nonempty_of_trackOf (dt.arOf_le_ko (some iv)) ⟨0, harity iv⟩ hg), hhi⟩⟩

/-- **The dictionary the evaluation reads, off a tape state**: the same reading
as `guessTracks_iff_of_lt`, at a state whose stage tracks are the guess's. Every
leg of the spine leaves them alone (`ixSpineStOfB_old`), so this is what the
evaluation's `hdict` is discharged by, at whatever program and whatever rule
names the reduction runs – nothing here mentions either. -/
theorem guessTracks_hdict_of_old {I : Type}
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {zero one : A} {σ : dt.d.B.Assignment (dt.X.Map A)}
    {s₀ top s : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    (hst : st.old = dt.guessTracks zero one σ s₀ top)
    (hs₀ : WMIncr WMLe (fun _ => False) s₀)
    (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (hhi : WMSetLt WMLe s top) (iv : dt.d.B.ι) :
    st.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ s := by
  rw [hst]
  exact dt.guessTracks_iff_of_lt h hs₀ harity hhi iv

omit [LinearOrder A] [L.Structure A] in
/-- **The guess's stretch is not empty**: the last logical address holds every
argument block, so it is at or above the marker's neighbour as soon as the
reduction has a block at all. This is the `htop` and the `htopne` the guessing
phase asks for, at the stretch the certificate lives on. -/
theorem wmSetLe_succ_bot_logicalTop [Nonempty A]
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {s₀ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hs₀ : WMIncr WMLe (fun _ => False) s₀) (i₀ : dt.KIx) :
    WMSetLe WMLe s₀ (logicalTop (R := R') (P := NexPh (Option dt.KIx) PE)
      (K := dt.KIx) (V := Fin dt.dd → A)) :=
  wmSetLe_succ_bot_of_nonempty h hs₀
    ⟨(DrawTag.arg i₀, fun _ => Classical.arbitrary A), i₀, rfl⟩

end Guessed

/-- **The clocked program's opening, from the state it starts in**: the same run
as `reachesIn_openingRegion` with every frame hypothesis discharged – the entry
state is clear but for the marker (`nexEntrySt`), its background off the file is
the blank tape (`ixBack_nexEntrySt`), and below the base and past the stretch
nothing is a register. What is left is what the *guess* decides: the stage
tracks `σ` it writes, empty outside the region, and the two exit guards. -/
theorem reachesIn_openingRegion_entry (hcoord : Function.Injective coord)
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {v v' v₁ x s₀ top : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hv0 : wideRank v = 0)
    (hle : WMSetLe WMLe v
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkTop A dt.KIx dt.dd)))
    (hvi₁ : WMIncr WMLe v v₁) (hwalk : WMSetLe WMLe v₁ x)
    (hxb : WMIncr WMLe x
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)))
    (hs₀ : WMIncr WMLe v s₀)
    (hvi' : WMIncr WMLe v v')
    (σ : dt.d.B.ι →
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    (htop : WMSetLe WMLe s₀ top)
    (htopne : ∃ y, top y)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r top → ¬σ i r)
    (hexB : dt.exitG PR.one (PR.passTracksAt
      (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
      (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le (dt.nexEntrySt v)) (fun _ => False) v))
    (hexG : dt.exitG PR.one (PR.passTracksAt
      (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
      (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le { dt.nexEntrySt v with old := σ }) (fun _ => False) v))
    {rEmb0 : ∀ i : NexSite SE,
      NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
    (hrules0 : ∀ (i : NexSite SE)
        (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
      PR.rules (rEmb0 i ρ) =
        dt.nexRule PR.one (dt.buildSpec PR.zero PR.one coord)
          (dt.regionSpec PR.zero PR.one) ruleE evalEntry
          (blkBot A dt.KIx dt.dd).1 i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (2 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 2 * base +
        ((wideRank top - wideRank s₀) + wideRank top) + 4)
      ⟨Sum.inr (PR.stElt NexPh.start
          (dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)),
        Sum.inl v,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (fun _ _ => PR.zero) (fun _ => False)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry)
          (dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)),
        Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout
            PR.zero PR.one dt.dd0Le { dt.nexEntrySt v with old := σ })
            (fun _ => False)) (PR.syElt PR.blank)⟩ := by
  have hnotcell : ∀ u : Wide.BlkIx dt.KIx A dt.dd,
      v ≠ (dt.blkLaid h hpos (le_of_lt hbase)).cell u := by
    intro u hc
    have := dt.wideRank_blkLaid_cell h hpos (le_of_lt hbase) u
    rw [← hc, hv0] at this
    omega
  exact dt.reachesIn_openingRegion (f₀ := f₀) hcoord hR h hpos hbase
    (st := dt.nexEntrySt v)
    (fun _ => not_false) (fun _ => not_false) (fun _ => not_false)
    (fun _ => not_false)
    (fun u hc => hnotcell u hc.symm)
    (fun u hc => hnotcell u hc.symm) (fun _ => not_false) (fun _ _ => not_false)
    (fun _ _ => not_false) rfl hv0 hle hvi₁ hwalk hxb hs₀ hvi'
    (bg := fun _ _ => PR.zero) (bg₀ := dt.startBack (fun _ _ => PR.zero) PR.one v)
    (fun _ hr => dt.startBack_frame hr)
    (dt.startBack_wr (dt.blkLaid h hpos (le_of_lt hbase)).cell v)
    (fun _ hr => dt.ixBack_nexEntrySt
      (dt.not_reg_blkLaid_of_lt h hpos (le_of_lt hbase) hr))
    (fun _ hr => dt.ixBack_nexEntrySt
      (dt.not_reg_blkLaid_of_not_lt_top h hpos (le_of_lt hbase) hbase hr))
    σ htop htopne
    (fun i r hr => ⟨fun hc => absurd hc (hout i r hr), fun hc => hc.elim⟩)
    hexB hexG hrules0


/-! ### The opening of a program that is handed its file

A program handed its file has nothing to lay: its file-laying phase is the two
steps of `nullSpec` and the rest of the opening is the same. So the whole
opening is stated here at an **arbitrary** file – the five steps of
`NexBuild`'s `AnyFile` section, the sweep that is over at once, the two walks
home and the guess, which was generic already. Nothing of the file is read but
its cells. -/

section Handed

variable {I : Type} {F : LaidFile dt A R' (NexPh (Option dt.KIx) PE) I}
variable {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
variable {botS : Option dt.KIx}

omit [Nonempty A] in
/-- **The whole opening of a program that is handed its file**: plant the two
marks, walk up, run the sweep that lays nothing, turn round, walk home, guess
the certificate over the stretch, walk home again, and step into the
evaluation. Its cost is the two walks up and back, the guess's stretch out and
back, and six single steps. -/
theorem reachesIn_openingHanded (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    {v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v)
    {v₁ x y y' s₀ s₁ v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi₁ : WMIncr WMLe v v₁) (hwalk : WMSetLe WMLe v₁ x) (hxy : WMIncr WMLe x y)
    (hyy' : WMIncr WMLe y y') (hyv : WMSetLe WMLe v y)
    (hvs₀ : WMIncr WMLe v s₀) (hle : WMSetLe WMLe s₀ s₁) (hne₁ : ∃ z, s₁ z)
    (hvv' : WMIncr WMLe v v')
    {bg bg₀ : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) →
      dt.SlotIx → A}
    (hframe : ∀ r, r ≠ v → bg₀ r = bg r)
    (hwr : PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False) v =
      Function.update (Function.update
        (PR.passTracksAt F.cell Slot.mir bg (fun _ => False) v) Slot.wk PR.one)
        Slot.bot PR.one)
    (hback : bg₀ = dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (f : dt.CtlIx → A)
    -- the sweep is over where it starts, and leaves nothing behind
    (hroll : betaS.Roll botS f) (hdone : betaS.Done botS f)
    (hstRoll : betaS.stRoll botS f (PR.passTracksAt F.cell Slot.mir bg₀
      (fun _ => False) y) = f)
    (hwrS : betaS.wr botS f (PR.passTracksAt F.cell Slot.mir bg₀
        (fun _ => False) y) =
      PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False) y)
    -- the two exits, and the certificate the guess writes
    (hexB : dt.exitG PR.one (PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False) v))
    (σ : dt.d.B.ι →
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r s₁ → (σ i r ↔ st.old i r))
    (hexG : dt.exitG PR.one (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ })
      (fun _ => False) v))
    {rEmbS : ∀ i : NexSite SE,
      NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
    (hrulesS : ∀ (i : NexSite SE)
        (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one betaS (dt.regionSpec PR.zero PR.one) ruleE evalEntry
          botS i ρ)
    {rHomeB rHomeG : HomeKit.HomeRule → R'}
    (hrulesHB : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHomeB ρ) =
        (HomeKit.mk Slot.mir Slot.wk
          (NexPh.homeBuildP (B := Option dt.KIx) (PE := PE))).rule PR.one ρ)
    (hrulesHG : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHomeG ρ) =
        (HomeKit.mk Slot.mir Slot.wk
          (NexPh.homeGuessP (B := Option dt.KIx) (PE := PE))).rule PR.one ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      ((wideRank x - wideRank v₁) + (wideRank y - wideRank v) +
        ((wideRank s₁ - wideRank s₀) + (wideRank s₁ - wideRank v)) + 7)
      ⟨Sum.inr (PR.stElt NexPh.start f), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.mir bg (fun _ => False))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) (betaS.st0 f
          (PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False) v))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ })
          (fun _ => False)) (PR.syElt PR.blank)⟩ := by
  classical
  subst hback
  have hstart := dt.step_startAny (PR := PR) (cell := F.cell) (m := fun _ => False)
    (f := f) hrulesS hR h hvi₁ hframe hwr
  have hwalkR := dt.reachesIn_approachAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f) hrulesS hR h hwalk
  have henter := dt.step_approachEnterAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f) hrulesS hR h hxy
  have hsweep := dt.step_sweepDone (PR := PR) (cell := F.cell) (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f)
    hrulesS hR h hyy' hroll hdone hstRoll hwrS
  have hturn := dt.step_doneBackAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f) hrulesS hR h hyy'
  have hhome := HomeKit.reachesIn
    (κ := HomeKit.mk Slot.mir Slot.wk
      (NexPh.homeBuildP (B := Option dt.KIx) (PE := PE)))
    (rEmb := rHomeB) F.toIxFile hrulesHB hR h (fun hc => nomatch hc)
    (m := fun _ => False) (fc := f)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (fun r => by
      change dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk = _
      rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkS])
    hyv
  have hmid := dt.step_homeBuildExitAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f)
    hrulesS hR h hvs₀ hexB
  have hguess := reachesIn_guessRegionPhase (F := F) (m := fun _ => False)
    (f₀ := betaS.st0 f (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) v))
    (st := st) hrulesS hR h σ (fun i => by intro hc; exact nomatch hc)
    (by intro hc; exact nomatch hc) botS hwkS hle
    (wmSetLt_of_wmIncr_le h hvs₀ ((isLinOrd_wmSetLe h).1 _)) hne₁ hrulesHG hout
  have hexit := dt.step_homeGuessExitAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ })
    (f := betaS.st0 f (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) v))
    hrulesS hR h hvv' hexG
  exact ((((((((TMData.reachesIn_of_step hstart).trans hwalkR).trans
    (TMData.reachesIn_of_step henter)).trans
    (TMData.reachesIn_of_step hsweep)).trans
    (TMData.reachesIn_of_step hturn)).trans hhome).trans
    (TMData.reachesIn_of_step hmid)).trans hguess).trans
    (TMData.reachesIn_of_step hexit) |>.mono (by omega)

omit [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The tail of the opening, from the walk home after the guess.** The whole
opening is a forward run, but a *backward* reading of an accepting run does not
get the opening: it gets the first configuration the machine cannot leave, which
is where the guess stopped and the walk home begins
(`DescriptiveComplexity.Draw.DrawData.exists_postGuess_shaped`). From there on the
run is forward again, and this is that piece: walk down to the marker from
wherever the guess stopped, and step into the evaluation.

Nothing of the guess is read here – the tracks are whatever the sweep left – so
the same lemma serves the forward opening's last two steps and the backward
reading's first. -/
theorem reachesIn_homeGuessTail (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    {v y v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v)
    (hyv : WMSetLe WMLe v y) (hvv' : WMIncr WMLe v v')
    (f : dt.CtlIx → A)
    (hexG : dt.exitG PR.one (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) v))
    {rEmbS : ∀ i : NexSite SE,
      NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
    (hrulesS : ∀ (i : NexSite SE)
        (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one betaS (dt.regionSpec PR.zero PR.one) ruleE evalEntry
          botS i ρ)
    {rHomeG : HomeKit.HomeRule → R'}
    (hrulesHG : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHomeG ρ) =
        (HomeKit.mk Slot.mir Slot.wk
          (NexPh.homeGuessP (B := Option dt.KIx) (PE := PE))).rule PR.one ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      ((wideRank y - wideRank v) + 1)
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP f), Sum.inl y,
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False))
          (PR.syElt PR.blank)⟩ := by
  have hhome := HomeKit.reachesIn
    (κ := HomeKit.mk Slot.mir Slot.wk
      (NexPh.homeGuessP (B := Option dt.KIx) (PE := PE)))
    (rEmb := rHomeG) F.toIxFile hrulesHG hR h (fun hc => nomatch hc)
    (m := fun _ => False) (fc := f)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (fun r => by
      change dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk = _
      rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkS])
    hyv
  have hexit := dt.step_homeGuessExitAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f)
    hrulesS hR h hvv' hexG
  exact (hhome.tail hexit).mono (by omega)

end Handed

end Opening

section Clock

/-- **The clock comparison**: an opening of `o` steps, an evaluation of at most
`a · b`, and the accepting step come to fewer than `2 ^ ((k + j) · m)` as soon as
each of `a`, `b` and `o + 1` is at most `2 ^ (k · m)` and `j` outruns `k` by two.
The opening is left abstract: the file-laying one and the region-guessing one
differ, and both are bounded by the number of addresses. -/
theorem nexTotal_lt_two_pow {k j m o e a b : ℕ} (hkj : k + 1 < j) (hm : 0 < m)
    (he : e ≤ a * b) (ha : a ≤ 2 ^ (k * m)) (hb : b ≤ 2 ^ (k * m))
    (hopen : o + 1 ≤ 2 ^ (k * m)) :
    o + e + 1 < 2 ^ ((k + j) * m) := by
  have hsum : o + e + 1 ≤ a * b + (o + 1) := by omega
  exact lt_of_le_of_lt hsum (mul_add_lt_two_pow hkj hm ha hb hopen)

/-- **The clock comparison, with the opening at twice the region**: the shape a
program that lays a file *and* guesses over the region actually meets – its
opening is two sweeps, not a fraction of one. One working block is enough
(`1 ≤ k`), and the rest is `mul_add_lt_two_pow'`. -/
theorem nexTotal_lt_two_pow' {k j m o e a b : ℕ} (hk : 1 ≤ k) (hkj : k + 1 < j)
    (hm : 0 < m) (he : e ≤ a * b) (ha : a ≤ 2 ^ (k * m)) (hb : b ≤ 2 ^ (k * m))
    (hopen : o + 1 ≤ 2 ^ ((k + 1) * m)) :
    o + e + 1 < 2 ^ ((k + j) * m) := by
  have hsum : o + e + 1 ≤ a * b + (o + 1) := by omega
  exact lt_of_le_of_lt hsum (mul_add_lt_two_pow' hk hkj hm ha hb hopen)

/-- **The opening fits the region a few times over**: the approach, the file's
own stretch and the guess all stay inside the region, so with each of the
program's numbers below the region's size `2 ^ (k · m)` and a block worth at
least eight addresses (`3 ≤ m`), the whole opening and the step that follows it
are below `2 ^ ((k + 1) · m)` – which is what
`DescriptiveComplexity.Draw.DrawData.nexTotal_lt_two_pow'` asks of it. The region
bound on a rank is `wideRank_lt_two_pow_supported`; the base is bounded the same
way, being an address of the region like any other. -/
theorem openingRegion_le_two_pow {A : Type} [Finite A] [Language.wide.Structure A]
    {R base k m : ℕ} {top bot : A → Prop} (hm : 3 ≤ m)
    (htop : wideRank top + 1 ≤ 2 ^ (k * m))
    (hbase : base + 1 ≤ 2 ^ (k * m))
    (hfile : 2 * R + 5 ≤ 2 ^ (k * m)) :
    2 * R + 2 * base + ((wideRank top - wideRank bot) + wideRank top) + 4 + 1 ≤
      2 ^ ((k + 1) * m) := by
  have hpow : 8 * 2 ^ (k * m) ≤ 2 ^ ((k + 1) * m) := by
    have hk : (k + 1) * m = k * m + m := by ring
    have h8 : (8 : ℕ) ≤ 2 ^ m := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [hk, pow_add]
    calc 8 * 2 ^ (k * m) = 2 ^ (k * m) * 8 := Nat.mul_comm _ _
      _ ≤ 2 ^ (k * m) * 2 ^ m := Nat.mul_le_mul_left _ h8
  -- `omega` drops a hypothesis carrying a power, so name the two of them first.
  generalize (2 : ℕ) ^ (k * m) = N at htop hbase hfile hpow
  generalize (2 : ℕ) ^ ((k + 1) * m) = P at hpow ⊢
  omega

/-- **The opening of a program whose region is the logical addresses**: the two
lemmas above composed, with the guess's top a *logical* address – every
non-argument block empty, which is what the region is
(`DescriptiveComplexity.Draw.wideRank_lt_two_pow_logical`). What is left to check
of an instantiation is one inequality in the program's own numbers: the file and
its base, below the region. -/
theorem openingLogical_le_two_pow {A R P K : Type} {dd : ℕ}
    [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
    [Finite A] [Finite R] [Finite P] [Finite K]
    [Language.wide.Structure (Univ A R P K dd)]
    {Rn base : ℕ} {top bot : Univ A R P K dd → Prop}
    (hord : ∀ x y : Univ A R P K dd, WMLe x y ↔ tagTupleLe x y)
    (hm : 3 ≤ Nat.card (Fin dd → A))
    (htop : ∀ τ : DrawTag R P K, (∀ i : K, τ ≠ DrawTag.arg i) →
      ∀ v : Fin dd → A, ¬top (τ, v))
    (hbase : base + 1 ≤ 2 ^ (Nat.card K * Nat.card (Fin dd → A)))
    (hfile : 2 * Rn + 5 ≤ 2 ^ (Nat.card K * Nat.card (Fin dd → A))) :
    2 * Rn + 2 * base + ((wideRank top - wideRank bot) + wideRank top) + 4 + 1 ≤
      2 ^ ((Nat.card K + 1) * Nat.card (Fin dd → A)) :=
  openingRegion_le_two_pow hm (wideRank_lt_two_pow_logical hord htop) hbase hfile

/-- **The region-guessing opening is bounded by the addresses**: its two sweeps
are each shorter than the number of addresses, so the whole of it is
`2 · R + base + 2 · N + 4` for `N` that number. This is the crude reading, above
the clock; `openingRegion_le_two_pow` is the one a clocked program can pay. -/
theorem openingRegion_le {A : Type} [Finite A]
    [Language.wide.Structure A]
    (R base : ℕ) (top bot : A → Prop) :
    2 * R + base + ((wideRank top - wideRank bot) + wideRank top) + 4 ≤
      2 * R + base + 2 * Nat.card {p : WPoint A // (wideData A).Posn p} + 4 := by
  have h₁ := wideRank_lt_card (A := A) top
  omega

end Clock
/-! ### The forward direction at the assembled program -/

section Accept

variable {L : Language.{0, 0}} {dt : DrawData L} {A G : Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable (dt) (zero one : A)
variable [LinearOrder (dt.NexRIx (G := G))] [Finite (dt.NexRIx (G := G))]
variable [Language.wide.Structure (Univ A (dt.NexRIx (G := G))
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]

variable {dt zero one}

omit [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [LinearOrder (dt.NexRIx (G := G))] [Finite (dt.NexRIx (G := G))] in
/-- **A clocked program starts on a blank tape**: it declines the input
channel's marks – its `mark` is the blank – so its initial background is the
constant blank, and the tape it starts on is the one its opening runs from
whatever file it means to lay. -/
theorem nexProg_initBack (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (coord : Fin dt.dd → dt.CtlIx)
    (β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx))
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
    (bot : Option dt.KIx) :
    (dt.nexProg zero one hzo hpl coord β γ args bot).initBack = fun _ _ => zero := by
  classical
  funext r s
  change (if _ : ∃ x : Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd, r = wmSeg x then
    (dt.nexProg zero one hzo hpl coord β γ args bot).mark _ s
    else (dt.nexProg zero one hzo hpl coord β γ args bot).blank s) = zero
  by_cases hr : ∃ x : Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd, r = wmSeg x
  · rw [dif_pos hr]
    rfl
  · rw [dif_neg hr]
    rfl

/-- **The clocked program's run makes its instance a yes-instance**: an
accepting run of fewer than `2 ^ n` steps from the initial configuration – the
head on the empty address, the tape blank because the program declines the
channel's marks – is what `DescriptiveComplexity.WideAccept` asks for.
Well-formedness comes free with the table and determinism is not asked for,
which is exactly what a program that guesses needs. -/
theorem nexProg_wideAccept (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hR : (dt.nexProg zero one hzo hpl coord β γ args bot).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {n : ℕ}
    {cfg : Config (WPoint (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (hreach : (wideData (Univ A (dt.NexRIx (G := G))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn n
      ⟨Sum.inr ((dt.nexProg zero one hzo hpl coord β γ args bot).stElt
          NexPh.start (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)),
        Sum.inl fun _ => False,
        wideTape ((dt.nexProg zero one hzo hpl coord β γ args bot).trackTapeAt
          wmSeg Slot.mir
          (dt.nexProg zero one hzo hpl coord β γ args bot).initBack
          fun _ => False)
          ((dt.nexProg zero one hzo hpl coord β γ args bot).syElt
            (dt.nexProg zero one hzo hpl coord β γ args bot).blank)⟩ cfg)
    (hlt : n < 2 ^ Nat.card (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    {fq : dt.CtlIx → A}
    (hstate : cfg.state = Sum.inr
      ((dt.nexProg zero one hzo hpl coord β γ args bot).stElt NexPh.acceptP fq))
    (hacc : (args none).accBit fq) :
    WideAccept (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) :=
  Prog.wideAccept_prog hR hlin (fun _ => trivial) (t₀ := Slot.mir) (fun _ => rfl) rfl
    hreach hlt hstate ⟨rfl, hacc⟩

/-- **The clocked program accepts, from its three legs**: the opening, the
evaluation and the step that leaves it, with the clock's arithmetic done once.
What the two strands above owe is exactly what this asks: an opening of `o`
steps with `o + 1` below `2 ^ ((k + 1) · m)` – two sweeps of the region, which
is what laying the file and guessing over it costs – an evaluation of at most
`a · b` with both factors below `2 ^ (k · m)`, and `k + 1 < j` with one working
block; then the whole run is below `2 ^ ((k + j) · m)`, hence below the number
of addresses (`DescriptiveComplexity.Draw.DrawData.nexTotal_lt_two_pow'`). -/
theorem nexProg_wideAccept_of_legs (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hR : (dt.nexProg zero one hzo hpl coord β γ args bot).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {o e a b k j m : ℕ}
    {c₁ c₂ c₃ : Config (WPoint (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (hopen : (wideData (Univ A (dt.NexRIx (G := G))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn o
      ⟨Sum.inr ((dt.nexProg zero one hzo hpl coord β γ args bot).stElt
          NexPh.start (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)),
        Sum.inl fun _ => False,
        wideTape ((dt.nexProg zero one hzo hpl coord β γ args bot).trackTapeAt
          wmSeg Slot.mir
          (dt.nexProg zero one hzo hpl coord β γ args bot).initBack
          fun _ => False)
          ((dt.nexProg zero one hzo hpl coord β γ args bot).syElt
            (dt.nexProg zero one hzo hpl coord β γ args bot).blank)⟩ c₁)
    (heval : (wideData (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn e c₁ c₂)
    (hexit : (wideData (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step c₂ c₃)
    (hk : 1 ≤ k) (hkj : k + 1 < j) (hm : 0 < m)
    (hcard : (k + j) * m ≤ Nat.card (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (he : e ≤ a * b) (ha : a ≤ 2 ^ (k * m)) (hb : b ≤ 2 ^ (k * m))
    (hopenle : o + 1 ≤ 2 ^ ((k + 1) * m))
    {fq : dt.CtlIx → A}
    (hstate : c₃.state = Sum.inr
      ((dt.nexProg zero one hzo hpl coord β γ args bot).stElt NexPh.acceptP fq))
    (hacc : (args none).accBit fq) :
    WideAccept (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) :=
  nexProg_wideAccept hzo hpl hR hlin
    (reachesIn_nexTotal hopen heval hexit)
    (lt_of_lt_of_le (nexTotal_lt_two_pow' hk hkj hm he ha hb hopenle)
      (Nat.pow_le_pow_right (by omega) hcard))
    hstate hacc

/-- **The clocked program accepts, from its opening and its evaluation**: the
two legs as they are actually proved – the opening from the state the program
starts in, presented along the mirror at the file it lays, and the evaluation
from the state the opening leaves, presented along VAL – with the two
adjustments between them done here. There are exactly two: the initial tape is
the blank one whatever track and whatever file it is presented along
(`trackTape_blank_congr` at `nexProg_initBack`), and the opening's last
configuration *is* the evaluation's first, because the state the opening leaves
has an empty mirror (`config_openingEnd_eq_evalStart`). The clock is
`nexTotal_lt_two_pow'`, one step of slack over the run since the evaluation
already ends in the accepting phase. -/
theorem nexProg_wideAccept_legs (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hR : (dt.nexProg zero one hzo hpl coord β γ args bot).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {I : Type}
    {F : LaidFile dt A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) I}
    {st : TapeSt dt A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) I}
    (hmir : st.mir = fun _ => False)
    {evalEntry : EvalPh dt.nv dt.PMF} {f₁ : dt.CtlIx → A}
    {w : Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    {o e : ℕ}
    (hopen : (wideData (Univ A (dt.NexRIx (G := G))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn o
      ⟨Sum.inr ((dt.nexProg zero one hzo hpl coord β γ args bot).stElt
          NexPh.start (dt.ctlOf coord (fun _ => zero) (blkBot A dt.KIx dt.dd).2)),
        Sum.inl fun _ => False,
        wideTape ((dt.nexProg zero one hzo hpl coord β γ args bot).trackTapeAt
          F.cell Slot.mir (fun _ _ => zero) (fun _ => False))
          ((dt.nexProg zero one hzo hpl coord β γ args bot).syElt
            (dt.nexProg zero one hzo hpl coord β γ args bot).blank)⟩
      ⟨Sum.inr ((dt.nexProg zero one hzo hpl coord β γ args bot).stElt
          (NexPh.evalP evalEntry) f₁),
        Sum.inl w,
        wideTape ((dt.nexProg zero one hzo hpl coord β γ args bot).trackTapeAt
          F.cell Slot.mir
          (dt.ixBack F.toLayout zero one dt.dd0Le st) (fun _ => False))
          ((dt.nexProg zero one hzo hpl coord β γ args bot).syElt
            (dt.nexProg zero one hzo hpl coord β γ args bot).blank)⟩)
    {cT : Config (WPoint (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (heval : (wideData (Univ A (dt.NexRIx (G := G))
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn e
      ⟨Sum.inr ((dt.nexProg zero one hzo hpl coord β γ args bot).stElt
          (NexPh.evalP evalEntry) f₁),
        Sum.inl w,
        wideTape ((dt.nexProg zero one hzo hpl coord β γ args bot).trackTapeAt
          F.cell Slot.val
          (dt.ixBack F.toLayout zero one dt.dd0Le st) st.val)
          ((dt.nexProg zero one hzo hpl coord β γ args bot).syElt
            (dt.nexProg zero one hzo hpl coord β γ args bot).blank)⟩ cT)
    {a b k j m : ℕ}
    (hk : 1 ≤ k) (hkj : k + 1 < j) (hm : 0 < m)
    (hcard : (k + j) * m ≤ Nat.card (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (he : e ≤ a * b) (ha : a ≤ 2 ^ (k * m)) (hb : b ≤ 2 ^ (k * m))
    (hopenle : o + 1 ≤ 2 ^ ((k + 1) * m))
    {fq : dt.CtlIx → A}
    (hstate : cT.state = Sum.inr
      ((dt.nexProg zero one hzo hpl coord β γ args bot).stElt NexPh.acceptP fq))
    (hacc : (args none).accBit fq) :
    WideAccept (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) := by
  have hstart := trackTape_blank_congr
    (PR := dt.nexProg zero one hzo hpl coord β γ args bot)
    (cell := wmSeg) (cell' := F.cell) (t := Slot.mir) (t' := Slot.mir)
    (rest := (dt.nexProg zero one hzo hpl coord β γ args bot).initBack)
    (rest' := fun _ _ => zero)
    (fun r => by
      rw [nexProg_initBack (G := G) hzo hpl coord β γ args bot]
      rfl)
    (fun _ => rfl) rfl rfl
  refine nexProg_wideAccept hzo hpl hR hlin (n := o + e) ?_
    (lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _)
      (nexTotal_lt_two_pow' (o := o) (e := e) hk hkj hm he ha hb hopenle).le)
      (Nat.pow_le_pow_right (by omega) hcard)) hstate hacc
  rw [hstart]
  exact hopen.trans ((config_openingEnd_eq_evalStart hmir _ _ _) ▸ heval)

end Accept
/-! ### Determinism after the guess -/

section Unique

variable {L : Language.{0, 0}} {dt : DrawData L} {A G : Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [Finite A] [Finite dt.KIx] [Nonempty A]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [LinearOrder (dt.NexRIx (G := G))] [Finite (dt.NexRIx (G := G))]
variable [Language.wide.Structure (Univ A (dt.NexRIx (G := G))
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {zero one : A}

omit [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [LinearOrder (dt.NexRIx (G := G))] [Finite (dt.NexRIx (G := G))]
  [Language.wide.Structure (Univ A (dt.NexRIx (G := G))
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **The clocked program separates after its guess**: two of its rules firing
in the same post-guess phase on the same data are the same rule. Across sites
that is the owner map (`nexOwner_nexRule`); within a site it is
`nexSep_postGuess`, and the guess site is where the two are allowed to differ –
which is why the phase restriction is there. -/
theorem nexProg_sepOn (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} :
    (dt.nexProg zero one hzo hpl coord β γ args bot).table.SepOn
      NexPh.PostGuess := by
  refine Prog.sepOn_of
    (PR := dt.nexProg zero one hzo hpl coord β γ args bot) ?_
  rintro ⟨i, ρ⟩ ⟨i', ρ'⟩ f g hph0 hg hg' hph
  rw [nexProg_rules (G := G) hzo hpl i ρ] at hph0 hg hph
  rw [nexProg_rules (G := G) hzo hpl i' ρ'] at hg' hph
  have hown : i = i' := by
    have h₁ := nexOwner_nexRule (dt := dt) (one := one) (β := β) (γ := γ)
      (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := .chk 0)
      (bot := bot) (ownE := dt.seOwn)
      (fun e ρ => by
        obtain ⟨p, hp, ho⟩ := nexEvalHosrcF (zero := zero) (one := one) args e ρ
        rw [hp]
        exact congrArg NexSite.eval ho) i ρ
    have h₂ := nexOwner_nexRule (dt := dt) (one := one) (β := β) (γ := γ)
      (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := .chk 0)
      (bot := bot) (ownE := dt.seOwn)
      (fun e ρ => by
        obtain ⟨p, hp, ho⟩ := nexEvalHosrcF (zero := zero) (one := one) args e ρ
        rw [hp]
        exact congrArg NexSite.eval ho) i' ρ'
    rw [← h₁, ← h₂, hph]
  subst hown
  have hsep := nexSep_postGuess (dt := dt) (one := one) (β := β) (γ := γ)
    (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := .chk 0) (bot := bot)
    (fun e ρ ρ' f g => nexEvalSepF hzo args e ρ ρ' f g) i ρ ρ' f g hph0 hg hg' hph
  exact congrArg (fun x => (⟨i, x⟩ : (i : NexSite dt.SEF) ×
    NexSh dt.SEF (Option dt.KIx) G dt.NexSESh i)) hsep

/-- **The clocked program is deterministic after its guess**: from any
configuration whose phase is post-guess, every reachable configuration has at
most one successor. This is what a reduction reads its certificate off an
*arbitrary* accepting run with – determinism where it is needed and
nondeterminism where the guess is, which is the whole of the polarity. -/
theorem nexProg_uniqueFrom (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hR : (dt.nexProg zero one hzo hpl coord β γ args bot).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {cfg : Config (WPoint (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    (hcfg : ∀ (p : NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      cfg.state = Sum.inr (stateElt zero p f) → NexPh.PostGuess p) :
    (wideData (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).UniqueFrom cfg :=
  Table.uniqueFrom_of_sepOn hR hlin (nexProg_sepOn hzo hpl)
    (fun r hsrc => by
      obtain ⟨i, ρ⟩ := r
      rw [show ((dt.nexProg zero one hzo hpl coord β γ args bot).table).dstPh
            ⟨i, ρ⟩ =
          (dt.nexRule one β γ (dt.nexEvalRuleF zero one args)
            (EvalPh.chk 0) bot i ρ).dstPh from rfl]
      exact postGuess_nexRule (dt := dt) (one := one) (β := β) (γ := γ)
        (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := .chk 0)
        (bot := bot) (nexEvalRuleF_postGuess args) i ρ hsrc)
    hcfg

omit [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [LinearOrder (dt.NexRIx (G := G))] [Finite (dt.NexRIx (G := G))]
  [Language.wide.Structure (Univ A (dt.NexRIx (G := G))
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **No rule of the clocked program fires from its accepting phase**: the
accepting phase is owned by the accepting site (`nexOwner`), and that site has
no rules at all – its shape is `Empty`. -/
theorem nexProg_srcPh_ne_acceptP (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx} (r : dt.NexRIx (G := G)) :
    ((dt.nexProg zero one hzo hpl coord β γ args bot).table).srcPh r ≠
      NexPh.acceptP := by
  obtain ⟨i, ρ⟩ := r
  intro hsrc
  have hown := nexOwner_nexRule (dt := dt) (one := one) (β := β) (γ := γ)
    (ruleE := dt.nexEvalRuleF zero one args) (evalEntry := EvalPh.chk 0)
    (bot := bot) (ownE := dt.seOwn)
    (fun e ρ' => by
      obtain ⟨p, hp, hown⟩ := nexEvalHosrcF (B := Option dt.KIx) args e ρ'
      rw [hp]
      exact congrArg NexSite.eval hown) i ρ
  rw [show (dt.nexRule one β γ (dt.nexEvalRuleF zero one args)
      (EvalPh.chk 0) bot i ρ).srcPh =
    ((dt.nexProg zero one hzo hpl coord β γ args bot).table).srcPh ⟨i, ρ⟩ from rfl,
    hsrc] at hown
  have hi : NexSite.accept = i := hown
  subst hi
  exact ρ.elim

omit [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (dt.NexRIx (G := G))] in
/-- **An accepting configuration of the clocked program is stuck**: no rule
fires from the accepting phase, so the run that reached it is the whole run.
This is what a backward reading needs of the *verdict*: an accepting run ends
where the evaluation's own run ends, and the two are the same run by
`nexProg_uniqueFrom`. -/
theorem nexProg_stuck_acceptP (hzo : zero ≠ one)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {coord : Fin dt.dd → dt.CtlIx}
    {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
    {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (hR : (dt.nexProg zero one hzo hpl coord β γ args bot).table.Reads)
    {x : Config (WPoint (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))}
    {f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A}
    (hx : x.state = Sum.inr (stateElt zero NexPh.acceptP f)) :
    ∀ y, ¬(wideData (Univ A (dt.NexRIx (G := G))
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step x y :=
  Table.stuck_of_srcPh hR (Ph := fun p => p = NexPh.acceptP)
    (fun r => nexProg_srcPh_ne_acceptP hzo hpl r) hx rfl

end Unique



end DrawData

end Draw

end DescriptiveComplexity
