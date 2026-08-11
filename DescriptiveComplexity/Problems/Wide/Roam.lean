/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Step

/-!
# Roaming: what a wide machine may do when it is not on a clock

`DescriptiveComplexity.WideAccept` counts its steps against the number of
addresses, so a program for it is **one monotone sweep** and nothing else – the
shape `DescriptiveComplexity.accepts_of_rightSweep` packages.
`DescriptiveComplexity.WideAcceptSpace` and
`DescriptiveComplexity.DWideAcceptSpace` drop the bound entirely: acceptance is
`Relation.ReflTransGen` of the step relation, with no count anywhere. So their
programs may **roam** – sweep up, sweep back down, and start again, as often as
they like.

That is a different, and much larger, programming model, and this file is its
interface. Three things, each stated so that a phase is described by a
single-step obligation and phases compose by `Relation.ReflTransGen.trans`:

| what | theorem |
|---|---|
| a phase sweeping up a stretch of addresses | `DescriptiveComplexity.reaches_of_wideUp` |
| a phase sweeping back down one | `DescriptiveComplexity.reaches_of_wideDown` |
| a phase running a whole subroutine per address | `DescriptiveComplexity.reaches_of_wideRounds` |
| a run that ends accepting | `DescriptiveComplexity.acceptsSpace_of_wideRoam` |

The third is the one an outer loop is written with, and the one a clock forbids:
each round may cost exponentially many steps and there are exponentially many
rounds.

On top of them sits the primitive a roaming program actually spends its time
on – the **scan**, `DescriptiveComplexity.reaches_scanRight` and
`DescriptiveComplexity.reaches_scanLeft`: hold the state, rewrite every symbol
by itself, and walk until the cell where the scanning transition is no longer
offered. A scan leaves the tape exactly as it found it, which is why its
statement mentions one tape and not two, and it is how a program that cannot
read the digits of its own address nevertheless finds its way back to a cell it
has marked.

A program does not know *which* cell will stop its scan, only that one will, so
the form it uses is `DescriptiveComplexity.reaches_scanRight_least` (and
`DescriptiveComplexity.reaches_scanLeft_greatest`): the machine arrives at the
first stopping cell and learns, on arrival, that nothing it passed was one. The
extremum is taken there, once, so no phase of a program has to name the address
a mark sits at.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Runs of unbounded length -/

namespace TMData

variable {A : Type} {M : TMData A}

/-- **A run of any length is a reachability**: the count `StepsIn` carries is
what a space-bounded machine does not have to produce, so every phase lemma
stated with a count is read through this. -/
theorem reflTransGen_of_stepsIn : ∀ {n : ℕ} {c d : Config A},
    M.StepsIn n c d → Relation.ReflTransGen M.Step c d := by
  intro n
  induction n with
  | zero => intro c d h; exact (show c = d from h) ▸ Relation.ReflTransGen.refl
  | succ n ih => rintro c d ⟨e, hstep, hrest⟩; exact Relation.ReflTransGen.head hstep (ih hrest)

end TMData

section Roam

variable {A : Type} [Language.wide.Structure A] [Finite A]

/-- A family of configurations indexed by the addresses, read on the whole
universe of the machine. Off the addresses the value is irrelevant – a phase
never looks – so it repeats the one at the empty address. -/
def wideLift (conf : (A → Prop) → Config (WPoint A)) : WPoint A → Config (WPoint A)
  | Sum.inl s => conf s
  | Sum.inr _ => conf fun _ => False

omit [Language.wide.Structure A] [Finite A] in
@[simp]
theorem wideLift_addr (conf : (A → Prop) → Config (WPoint A)) (s : A → Prop) :
    wideLift conf (Sum.inl s) = conf s :=
  rfl

/-! ### The two directions of a phase -/

/-- **A phase sweeping up.** Give the intended configuration at each address of
a stretch and one step between each address of it and its increment; the machine
then runs from the bottom of the stretch to the top.

This is `DescriptiveComplexity.stepsIn_of_wideSweep` with the count dropped and
the stretch bounded at both ends: a roaming program's phases stop where the next
one begins, and the transitions carrying them need not exist beyond. -/
theorem reaches_of_wideUp (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      (wideData A).Step (conf s) (conf t)) :
    Relation.ReflTransGen (wideData A).Step (conf s₀) (conf s₁) := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hrun := TMData.stepsIn_of_segment (M := wideData A) hlin (conf := wideLift conf)
    (p₀ := (Sum.inl s₀ : WPoint A)) (p₁ := (Sum.inl s₁ : WPoint A)) trivial
    (fun p q hsucc _ hub => ?_) (Sum.inl s₁) trivial hle (hlin.1 _)
  · exact TMData.reflTransGen_of_stepsIn hrun
  · obtain ⟨s, t, rfl, rfl, hi⟩ := step_ends_wide h hsucc
    exact hstep s t hi (by assumption) hub

/-- **A phase sweeping back down.** The mirror of
`DescriptiveComplexity.reaches_of_wideUp`: each address of the stretch carries a
step *from* its increment, and the machine runs from the top of the stretch to
the bottom. -/
theorem reaches_of_wideDown (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      (wideData A).Step (conf t) (conf s)) :
    Relation.ReflTransGen (wideData A).Step (conf s₁) (conf s₀) := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hrun := TMData.stepsIn_of_segment_down (M := wideData A) hlin (conf := wideLift conf)
    (p₀ := (Sum.inl s₀ : WPoint A)) (p₁ := (Sum.inl s₁ : WPoint A)) trivial
    (fun p q hsucc _ hub => ?_) (Sum.inl s₀) trivial (hlin.1 _) hle
  · exact TMData.reflTransGen_of_stepsIn hrun
  · obtain ⟨s, t, rfl, rfl, hi⟩ := step_ends_wide h hsucc
    exact hstep s t hi (by assumption) hub

/-! ### A phase that does work at every address

`DescriptiveComplexity.reaches_of_wideUp` asks for **one** step per address,
which is all a scan needs and all a machine on a clock can afford. A roaming
program's outer loops are not like that: at each address it runs a whole
subroutine – walk to the register file, increment the mirror, walk back – and
only then moves on. So the round, not the step, is the unit. -/

/-- **A phase that runs a subroutine at every address.** Give the intended
configuration at each address of a stretch and, between each address and its
increment, a *run* rather than a step; the machine then gets from the bottom of
the stretch to the top.

This is the shape of every outer loop of a space-bounded program – seeking an
address, sweeping a stage of a fixed-point iteration, comparing two tracks of the
tape – and it is available only because there is no clock: each round may cost
exponentially many steps and there are exponentially many rounds. -/
theorem reaches_of_wideRounds (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop}
    (hround : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      Relation.ReflTransGen (wideData A).Step (conf s) (conf t)) :
    ∀ s : A → Prop, WMSetLe WMLe s₀ s → WMSetLe WMLe s s₁ →
      Relation.ReflTransGen (wideData A).Step (conf s₀) (conf s) := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hset := isLinOrd_wmSetLe h
  have key : ∀ k : ℕ, ∀ s : A → Prop,
      bitRank (wideData A).Le (wideData A).Posn (Sum.inl s : WPoint A) = k →
      WMSetLe WMLe s₀ s → WMSetLe WMLe s s₁ →
      Relation.ReflTransGen (wideData A).Step (conf s₀) (conf s) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hrank hlb hub
      rcases eq_or_ne s₀ s with rfl | hne
      · exact Relation.ReflTransGen.refl
      · -- Above the bottom of the stretch, so not the empty address: it has a predecessor.
        have hlt : WMSetLt WMLe s₀ s := (wmSetLt_iff _ _).mpr ⟨hlb, hne⟩
        have hsome : ∃ x, s x := by
          by_contra hc
          exact hne (hset.2.2.1 s₀ s hlb (wmSetLe_of_empty h (fun x hx => hc ⟨x, hx⟩) s₀))
        obtain ⟨p, hp⟩ := exists_wmPred h hsome
        have hpl : WMSetLe WMLe s₀ p := (wmSetLt_iff_of_wmIncr h hp s₀).mp hlt
        have hpu : WMSetLe WMLe p s₁ := hset.2.1 p s s₁ (wmSetLe_of_wmIncr hp) hub
        have hb : bitRank (wideData A).Le (wideData A).Posn (Sum.inl s : WPoint A) =
            bitRank (wideData A).Le (wideData A).Posn (Sum.inl p : WPoint A) + 1 :=
          bitRank_succPos hlin ((succPos_wpLe_iff h p s).mpr hp)
        exact (ih _ (by omega) p rfl hpl hpu).trans (hround p s hp hpl hub)
  exact fun s hlb hub => key _ s rfl hlb hub

/-! ### The accumulator of a sweep

A sweep that is asking a question of every address – *do these two tracks agree
everywhere?* – carries one bit across exponentially many rounds, and since it
sweeps *upwards* that bit is a function of the **prefix**: of the addresses
strictly below the one it has reached. This is the address-scale twin of
`DescriptiveComplexity.accState`, which does the same for a walk of the register
file, and it is what the comparison sweep of a fixed-point program is written
with. -/

open Classical in
/-- **The state a sweep is in on arriving at an address**: the first state exactly
when the property holds at every address strictly below. -/
noncomputable def sweepState (P : (A → Prop) → Prop) (qy qn : A) (w : A → Prop) : A :=
  if ∀ r : A → Prop, WMSetLt WMLe r w → P r then qy else qn

open Classical in
/-- **The state a sweep is in on leaving an address**: the same with that address
taken into account. -/
noncomputable def sweepStateAfter (P : (A → Prop) → Prop) (qy qn : A) (w : A → Prop) : A :=
  if ∀ r : A → Prop, WMSetLe WMLe r w → P r then qy else qn

variable {P : (A → Prop) → Prop} {qy qn : A}

/-- **Leaving one address is arriving at the next**, which is what makes the two
definitions one accumulator. -/
theorem sweepStateAfter_succ (h : IsLinOrd (WMLe (A := A))) {w w' : A → Prop}
    (hi : WMIncr WMLe w w') : sweepStateAfter P qy qn w = sweepState P qy qn w' := by
  have hiff : (∀ r : A → Prop, WMSetLe WMLe r w → P r) ↔
      ∀ r : A → Prop, WMSetLt WMLe r w' → P r :=
    ⟨fun hall r hlt => hall r ((wmSetLt_iff_of_wmIncr h hi r).mp hlt),
      fun hall r hle => hall r ((wmSetLt_iff_of_wmIncr h hi r).mpr hle)⟩
  unfold sweepStateAfter sweepState
  by_cases hc : ∀ r : A → Prop, WMSetLt WMLe r w' → P r
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg fun hcon => hc (hiff.mp hcon), if_neg hc]

/-- **A sweep starts in the first state**: nothing lies below the empty
address. -/
theorem sweepState_bot (h : IsLinOrd (WMLe (A := A))) :
    sweepState P qy qn (fun _ => False) = qy := by
  refine if_pos fun r hlt => absurd ?_ ((wmSetLt_iff _ _).mp hlt).2
  exact (isLinOrd_wmSetLe h).2.2.1 r _ ((wmSetLt_iff _ _).mp hlt).1
    (wmSetLe_of_empty h (fun _ hc => hc) r)

omit [Finite A] in
/-- A sweep is in one of its two states, whatever it has seen. -/
theorem sweepState_cases (w : A → Prop) :
    sweepState P qy qn w = qy ∨ sweepState P qy qn w = qn := by
  unfold sweepState
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Finite A] in
/-- **A sweep that saw no failure ends in the first state.** -/
theorem sweepStateAfter_pos {w : A → Prop} (hall : ∀ r : A → Prop, WMSetLe WMLe r w → P r) :
    sweepStateAfter P qy qn w = qy :=
  if_pos hall

omit [Finite A] in
/-- **A sweep that saw a failure ends in the second state.** -/
theorem sweepStateAfter_neg {w r : A → Prop} (hle : WMSetLe WMLe r w) (hP : ¬P r) :
    sweepStateAfter P qy qn w = qn :=
  if_neg fun hall => hP (hall r hle)

/-! ### The scan -/

/-- An address whose increment is at or below a bound is strictly below it: the
side condition a rightward scan step needs. -/
private theorem wmSetLt_of_wmIncr_le (h : IsLinOrd (WMLe (A := A))) {r r' t : A → Prop}
    (hi : WMIncr WMLe r r') (hub : WMSetLe WMLe r' t) : WMSetLt WMLe r t := by
  have hlin := isLinOrd_wmSetLe h
  refine (wmSetLt_iff r t).mpr ⟨hlin.2.1 r r' t (wmSetLe_of_wmIncr hi) hub, fun hc => ?_⟩
  exact ne_of_wmIncr hi (hlin.2.2.1 r r' (wmSetLe_of_wmIncr hi) (hc ▸ hub))

/-- An address at or below one whose increment is taken is strictly below that
increment: the side condition a leftward scan step needs. -/
private theorem wmSetLt_of_le_wmIncr (h : IsLinOrd (WMLe (A := A))) {t r r' : A → Prop}
    (hlb : WMSetLe WMLe t r) (hi : WMIncr WMLe r r') : WMSetLt WMLe t r' := by
  have hlin := isLinOrd_wmSetLe h
  refine (wmSetLt_iff t r').mpr ⟨hlin.2.1 t r r' hlb (wmSetLe_of_wmIncr hi), fun hc => ?_⟩
  exact ne_of_wmIncr hi (hlin.2.2.1 r r' (wmSetLe_of_wmIncr hi) (hc ▸ hlb))

/-- **Scanning right.** In a fixed state, at every cell from `s` up to but not
including `t`, some transition of the instance rewrites the symbol by itself and
moves right; the machine then walks from `s` to `t`, leaving state and tape as it
found them.

This is how a program navigates: it cannot read the digits of the address it is
on, so it writes a marker in the cell it means to come back to and scans until
the scanning transition is withheld – at the marker, which is the only symbol the
hypothesis is not asked about. -/
theorem reaches_scanRight (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {s t : A → Prop} (hle : WMSetLe WMLe s t)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    Relation.ReflTransGen (wideData A).Step
      ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ :=
  reaches_of_wideUp (conf := fun r => ⟨Sum.inr q, Sum.inl r, tp⟩) h hle
    fun r r' hi hlb hub => by
      obtain ⟨τ, a, htr, hsrc, hread, hdst, hwrite, hright, hcur⟩ :=
        hstep r hlb (wmSetLt_of_wmIncr_le h hi hub)
      exact step_wide_right h hi htr hsrc hread hdst hwrite hright hcur hcur fun _ _ => rfl

/-- **Scanning left**, the same reading downwards: the transitions move left, and
the machine walks from `s` down to `t`. -/
theorem reaches_scanLeft (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {s t : A → Prop} (hle : WMSetLe WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ ¬WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    Relation.ReflTransGen (wideData A).Step
      ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ :=
  reaches_of_wideDown (conf := fun r => ⟨Sum.inr q, Sum.inl r, tp⟩) h hle
    fun r r' hi hlb hub => by
      obtain ⟨τ, a, htr, hsrc, hread, hdst, hwrite, hright, hcur⟩ :=
        hstep r' (wmSetLt_of_le_wmIncr h hlb hi) hub
      exact step_wide_left h hi htr hsrc hread hdst hwrite hright hcur hcur fun _ _ => rfl

/-! ### Scanning to the first cell that stops the scan

The form a program uses in practice: it does not know *which* cell will stop its
scan, only that some cell will, and it needs the arrival to come with the promise
that nothing before it stopped. -/

/-- **A rightward scan arrives at the first cell that stops it.** Given that some
cell at or above `s` stops the scan, and that every cell at or above `s` which
does not stop it offers the scanning transition, the machine reaches the *least*
stopping cell – and learns, on arrival, that no cell it passed was one.

The caller never constructs that cell: this is where the extremum is taken, once,
so a program's phases are stated about the marks they look for and not about the
addresses those marks sit at. -/
theorem reaches_scanRight_least (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {Stop : (A → Prop) → Prop} {s : A → Prop}
    (hex : ∃ t, Stop t ∧ WMSetLe WMLe s t)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s r →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe r t) → ¬Stop r →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe s t ∧
      (∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t → ¬Stop r) ∧
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ := by
  obtain ⟨t, ⟨hstop, hge⟩, hmin⟩ :=
    exists_least (isLinOrd_wmSetLe h) (P := fun t => Stop t ∧ WMSetLe WMLe s t) hex
  have hfirst : ∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t → ¬Stop r := fun r hlb hlt hc =>
    ((wmSetLt_iff r t).mp hlt).2 ((isLinOrd_wmSetLe h).2.2.1 r t
      ((wmSetLt_iff r t).mp hlt).1 (hmin r ⟨hc, hlb⟩))
  exact ⟨t, hstop, hge, hfirst,
    reaches_scanRight h hge fun r hlb hlt =>
      hstep r hlb ⟨t, hstop, ((wmSetLt_iff r t).mp hlt).1⟩ (hfirst r hlb hlt)⟩

/-- **A leftward scan arrives at the first cell that stops it**, the same reading
downwards: the *greatest* stopping cell at or below `s`. -/
theorem reaches_scanLeft_greatest (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {Stop : (A → Prop) → Prop} {s : A → Prop}
    (hex : ∃ t, Stop t ∧ WMSetLe WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe r s →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t r) → ¬Stop r →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ ¬WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t s ∧
      (∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s → ¬Stop r) ∧
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ := by
  obtain ⟨t, ⟨hstop, hle⟩, hmax⟩ :=
    exists_greatest (isLinOrd_wmSetLe h) (P := fun t => Stop t ∧ WMSetLe WMLe t s) hex
  have hfirst : ∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s → ¬Stop r := fun r hlt hub hc =>
    ((wmSetLt_iff t r).mp hlt).2 ((isLinOrd_wmSetLe h).2.2.1 t r
      ((wmSetLt_iff t r).mp hlt).1 (hmax r ⟨hc, hub⟩))
  exact ⟨t, hstop, hle, hfirst,
    reaches_scanLeft h hle fun r hlt hub =>
      hstep r hub ⟨t, hstop, ((wmSetLt_iff t r).mp hlt).1⟩ (hfirst r hlt hub)⟩

/-! ### A run that accepts -/

/-- **A roaming program accepts.** Start on the empty address in a start state
with a blank tape – the initial configuration a reduction that leaves `wmInp`
empty has (`DescriptiveComplexity.isInit_wide`) – reach any configuration by any
chain of phases, and end in an accepting state.

There is no clock and no count: this is the whole of
`DescriptiveComplexity.WideAcceptSpace` for a program, and the reason the
space-bounded halves of the wide catalog are the ones a *roaming* program can
reach. -/
theorem acceptsSpace_of_wideRoam (h : IsLinOrd (WMLe (A := A)))
    (hno : ∀ x y : A, ¬WMInp x y) {q₀ b : A} (hq : WMStart q₀) (hb : WMBlank b)
    {c : Config (WPoint A)}
    (hreach : Relation.ReflTransGen (wideData A).Step
      ⟨Sum.inr q₀, Sum.inl fun _ => False, fun _ => Sum.inr b⟩ c)
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : WMAcc qa) :
    (wideData A).AcceptsSpace := by
  refine ⟨⟨Sum.inr q₀, Sum.inl fun _ => False, fun _ => Sum.inr b⟩, c,
    isInit_wide h hno hq hb, hreach, ?_⟩
  change wpMark WMAcc c.state
  rw [hstate]
  exact hacc

end Roam

end DescriptiveComplexity
