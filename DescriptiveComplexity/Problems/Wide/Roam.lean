/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Step

/-!
# Roaming: what a wide machine may do between its phases

`DescriptiveComplexity.WideAcceptSpace` and
`DescriptiveComplexity.DWideAcceptSpace` put no bound on the length of a run:
acceptance is `Relation.ReflTransGen` of the step relation, with no count
anywhere. So their programs may **roam** – sweep up, sweep back down, and start
again, as often as they like. `DescriptiveComplexity.WideAccept` counts its steps
against the number of addresses, so its programs roam on a budget: as many phases
as they like, provided the lengths add up to less than the number of addresses.

That is a different, and much larger, programming model than a single sweep, and
this file is its interface. Every phase is stated **twice** – once with a budget
(`DescriptiveComplexity.TMData.ReachesIn`, which composes by adding) and once
without (`Relation.ReflTransGen`, its erasure) – so that the clocked and the
space-bounded programs share their phases and differ only in whether the sum is
taken:

* a phase sweeping up a stretch of addresses –
  `DescriptiveComplexity.reachesIn_of_wideUp`, erased as
  `DescriptiveComplexity.reaches_of_wideUp`;
* a phase sweeping back down one –
  `DescriptiveComplexity.reachesIn_of_wideDown`, erased as
  `DescriptiveComplexity.reaches_of_wideDown`;
* a phase running a whole subroutine per address –
  `DescriptiveComplexity.reachesIn_of_wideRounds`, erased as
  `DescriptiveComplexity.reaches_of_wideRounds`;
* a run that ends accepting – `DescriptiveComplexity.accepts_of_wideRoam`, erased
  as `DescriptiveComplexity.acceptsSpace_of_wideRoam`.

The third is the one an outer loop is written with, and the one whose two
readings differ most: the budgeted form charges a round `w` steps and the whole
phase the product of `w` with the number of addresses crossed, while the erased
form charges nothing, which is what lets a space-bounded program iterate a fixed
point through exponentially many stages.

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

section Roam

variable {A : Type} [Language.wide.Structure A] [Finite A]

/-! ### The rank of an address

Every phase below is stated twice: once with a budget
(`DescriptiveComplexity.TMData.ReachesIn`), which is what a clocked program needs,
and once without (`Relation.ReflTransGen`), which is the erasure a space-bounded
one uses. The budgets are all differences of *ranks*: the number of addresses
strictly below a given one, which is exactly the number of steps a machine
stepping once per increment spends reaching it from the empty address. -/

/-- **The rank of an address**: how many addresses lie strictly below it. -/
noncomputable def wideRank (s : A → Prop) : ℕ :=
  bitRank (wideData A).Le (wideData A).Posn (Sum.inl s : WPoint A)

/-- The empty address has rank zero: a program starts with nothing spent. -/
theorem wideRank_bot (h : IsLinOrd (WMLe (A := A))) : wideRank (fun _ : A => False) = 0 :=
  bitRank_eq_zero_of_minPos (isLinOrd_wpLe h) (minPos_wpLe h)

/-- Rank increases by one along an increment, which is what makes a difference of
ranks a step count. -/
theorem wideRank_incr (h : IsLinOrd (WMLe (A := A))) {s t : A → Prop} (hi : WMIncr WMLe s t) :
    wideRank t = wideRank s + 1 :=
  bitRank_succPos (isLinOrd_wpLe h) ((succPos_wpLe_iff h s t).mpr hi)

/-- Rank is monotone along the address order: a budget stated at one address
covers every address below it, which is how a phase whose stopping cell is
unknown is charged against a known ceiling. -/
theorem wideRank_mono (h : IsLinOrd (WMLe (A := A))) {s t : A → Prop} (hle : WMSetLe WMLe s t) :
    wideRank s ≤ wideRank t :=
  TMData.bitRank_le_of_le (M := wideData A) (isLinOrd_wpLe h) trivial hle

/-- **Rank is below the clock**: the machine's step bound counts the addresses,
so a program that sweeps the whole tape once is affordable and the arithmetic
never leaves `ℕ`. -/
theorem wideRank_lt_card (s : A → Prop) :
    wideRank s < Nat.card {p : WPoint A // (wideData A).Posn p} :=
  bitRank_lt_card (p := (Sum.inl s : WPoint A)) trivial

/-- **The addresses are the subsets of the instance.** -/
def wideAddrEquiv : {p : WPoint A // (wideData A).Posn p} ≃ (A → Prop) where
  toFun p :=
    match p with
    | ⟨Sum.inl s, _⟩ => s
    | ⟨Sum.inr _, h⟩ => False.elim h
  invFun s := ⟨Sum.inl s, trivial⟩
  left_inv := by
    rintro ⟨s | x, h⟩
    · rfl
    · exact False.elim h
  right_inv _ := rfl

/-- **The clock of a wide machine is `2 ^ n`.** The whole arithmetic of the
model: a reduction buys itself `2 ^ (|Tag| · nᵈ)` steps by choosing the tags and
the dimension of its interpretation, and nothing else it does changes the
figure. -/
theorem card_wideAddr :
    Nat.card {p : WPoint A // (wideData A).Posn p} = 2 ^ Nat.card A := by
  classical
  have := Fintype.ofFinite A
  rw [Nat.card_congr wideAddrEquiv]
  simp [Nat.card_eq_fintype_card]

/-! ### The size of a region

A clocked program keeps its data in the least significant blocks, so every
address it visits is empty above a fixed set of positions. Such a *region* is
much smaller than the tape, and the budget of every phase run inside it has to
be charged against the region and not against the number of addresses – a bound
by `card_wideAddr` is a bound by the clock itself, which proves nothing. The two
lemmas here are what charges it: the addresses supported on a set of positions
are that set's subsets, so an address supported there has rank below `2 ^` its
size. -/

omit [Language.wide.Structure A] in
/-- **The addresses supported on a set of positions are its subsets.** -/
theorem card_addr_supported (Q : A → Prop) :
    Nat.card {s : A → Prop // ∀ x, s x → Q x} = 2 ^ Nat.card {x : A // Q x} := by
  classical
  have := Fintype.ofFinite A
  have e : {s : A → Prop // ∀ x, s x → Q x} ≃ ({x : A // Q x} → Prop) :=
    { toFun := fun s x => s.1 x.1
      invFun := fun f => ⟨fun x => ∃ h : Q x, f ⟨x, h⟩, fun _ hx => hx.1⟩
      left_inv := by
        rintro ⟨t, ht⟩
        exact Subtype.ext (funext fun x =>
          propext ⟨fun hx => hx.2, fun hx => ⟨ht x hx, hx⟩⟩)
      right_inv := by
        intro f
        funext x
        refine propext ⟨fun hx => ?_, fun hx => ⟨x.2, ?_⟩⟩
        · have hxx : (⟨x.1, hx.1⟩ : {x : A // Q x}) = x := Subtype.ext rfl
          exact hxx ▸ hx.2
        · have hxx : (⟨x.1, x.2⟩ : {x : A // Q x}) = x := Subtype.ext rfl
          exact hxx ▸ hx }
  rw [Nat.card_congr e]
  simp [Nat.card_eq_fintype_card]

/-- **An address of a region has rank below the region's size**: if every
address at or below `s` is empty off `Q`, then fewer than `2 ^ #Q` addresses lie
below `s`, since they are distinct subsets of `Q` and `s` is one more. This is
the bound a clocked phase is charged against. -/
theorem wideRank_lt_two_pow_supported (h : IsLinOrd (WMLe (A := A))) {Q s : A → Prop}
    (hclosed : ∀ t : A → Prop, WMSetLe WMLe t s → ∀ x, t x → Q x) :
    wideRank s < 2 ^ Nat.card {x : A // Q x} := by
  classical
  -- The addresses strictly below `s`, and those supported on `Q`.
  have himg : {q : WPoint A | (wideData A).Posn q ∧ (wideData A).Le q (Sum.inl s) ∧
      q ≠ Sum.inl s} = Sum.inl '' {t : A → Prop | WMSetLe WMLe t s ∧ t ≠ s} := by
    ext q
    rcases q with t | x
    · exact ⟨fun hq => ⟨t, ⟨hq.2.1, fun hc => hq.2.2 (by rw [hc])⟩, rfl⟩,
        fun ⟨t', ht', he⟩ => by
          cases he
          exact ⟨trivial, ht'.1, fun hc => ht'.2 (Sum.inl_injective hc)⟩⟩
    · exact ⟨fun hq => hq.1.elim, fun ⟨_, _, he⟩ => nomatch he⟩
  have hlt : ({t : A → Prop | WMSetLe WMLe t s ∧ t ≠ s} : Set (A → Prop)).ncard <
      ({t : A → Prop | ∀ x, t x → Q x} : Set (A → Prop)).ncard := by
    refine Set.ncard_lt_ncard ⟨fun t ht => hclosed t ht.1, fun hsub => ?_⟩ (Set.toFinite _)
    exact (hsub (hclosed s ((isLinOrd_wmSetLe h).1 s))).2 rfl
  have hcard : ({t : A → Prop | ∀ x, t x → Q x} : Set (A → Prop)).ncard =
      2 ^ Nat.card {x : A // Q x} := by
    rw [← Nat.card_coe_set_eq]
    exact card_addr_supported Q
  rw [wideRank, bitRank, himg, Set.ncard_image_of_injective _ Sum.inl_injective]
  omega

omit [Language.wide.Structure A] [Finite A] in
/-- **The region's size, in the program's own numbers**: the positions outside a
set of blocks are one per surviving block and per tuple, so their number is
`k · m` – which is the shape the clock compares against
(`DescriptiveComplexity.Draw.Data.nexTotal_lt_two_pow'`). -/
theorem card_avoid_positions {T V : Type} [Finite T] [Finite V] (H : T → Prop) :
    Nat.card {p : T × V // ¬H p.1} = Nat.card {τ : T // ¬H τ} * Nat.card V := by
  classical
  have e : {p : T × V // ¬H p.1} ≃ {τ : T // ¬H τ} × V :=
    { toFun := fun p => (⟨p.1.1, p.2⟩, p.1.2)
      invFun := fun q => ⟨(q.1.1, q.2), q.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod]

/-- **The size of the working region**: at a universe drawn as blocks of
tuples, an address whose blocks in a downward-closed set `H` are empty has rank
below `2 ^` the number of positions outside `H`. That is the region a clocked
program works in – `DescriptiveComplexity.wmAvoids_of_wmSetLe` is why it is an
initial stretch – and this is what every phase run inside it is charged
against. -/
theorem wideRank_lt_two_pow_avoids {T V : Type} [Finite T] [Finite V]
    [Language.wide.Structure (T × V)] {LeT : T → T → Prop} {LeV : V → V → Prop}
    (hT : IsLinOrd LeT) (hV : IsLinOrd LeV)
    (hord : ∀ x y : T × V, WMLe x y ↔ lexRel LeT LeV x y)
    {H : T → Prop} (hdown : ∀ τ σ : T, LeT τ σ → H σ → H τ)
    {s : T × V → Prop} (hs : wmAvoids H s) :
    wideRank s < 2 ^ Nat.card {p : T × V // ¬H p.1} := by
  have hle : (WMLe : T × V → T × V → Prop) = lexRel LeT LeV :=
    funext fun x => funext fun y => propext (hord x y)
  refine wideRank_lt_two_pow_supported (by rw [hle]; exact isLinOrd_lexRel hT hV)
    fun t hts x hx hH => ?_
  rw [hle] at hts
  exact wmAvoids_of_wmSetLe hT hV hdown hts hs x.1 hH x.2 hx

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

This is `DescriptiveComplexity.stepsIn_of_wideSweep` with the count relaxed to a
budget and the stretch bounded at both ends: a roaming program's phases stop
where the next one begins, and the transitions carrying them need not exist
beyond. -/
theorem reachesIn_of_wideUp (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      (wideData A).Step (conf s) (conf t)) :
    (wideData A).ReachesIn (wideRank s₁ - wideRank s₀) (conf s₀) (conf s₁) := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hrun := TMData.stepsIn_of_segment (M := wideData A) hlin (conf := wideLift conf)
    (p₀ := (Sum.inl s₀ : WPoint A)) (p₁ := (Sum.inl s₁ : WPoint A)) trivial
    (fun p q hsucc _ hub => ?_) (Sum.inl s₁) trivial hle (hlin.1 _)
  · exact hrun.reachesIn
  · obtain ⟨s, t, rfl, rfl, hi⟩ := step_ends_wide h hsucc
    exact hstep s t hi (by assumption) hub

/-- **A phase sweeping up**, the budget forgotten. -/
theorem reaches_of_wideUp (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      (wideData A).Step (conf s) (conf t)) :
    Relation.ReflTransGen (wideData A).Step (conf s₀) (conf s₁) :=
  (reachesIn_of_wideUp h hle hstep).reflTransGen

/-- **A phase sweeping back down.** The mirror of
`DescriptiveComplexity.reachesIn_of_wideUp`: each address of the stretch carries a
step *from* its increment, and the machine runs from the top of the stretch to
the bottom, for the same price. -/
theorem reachesIn_of_wideDown (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      (wideData A).Step (conf t) (conf s)) :
    (wideData A).ReachesIn (wideRank s₁ - wideRank s₀) (conf s₁) (conf s₀) := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hrun := TMData.stepsIn_of_segment_down (M := wideData A) hlin (conf := wideLift conf)
    (p₀ := (Sum.inl s₀ : WPoint A)) (p₁ := (Sum.inl s₁ : WPoint A)) trivial
    (fun p q hsucc _ hub => ?_) (Sum.inl s₀) trivial (hlin.1 _) hle
  · exact hrun.reachesIn
  · obtain ⟨s, t, rfl, rfl, hi⟩ := step_ends_wide h hsucc
    exact hstep s t hi (by assumption) hub

/-- **A phase sweeping back down**, the budget forgotten. -/
theorem reaches_of_wideDown (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      (wideData A).Step (conf t) (conf s)) :
    Relation.ReflTransGen (wideData A).Step (conf s₁) (conf s₀) :=
  (reachesIn_of_wideDown h hle hstep).reflTransGen

/-! ### A phase that does work at every address

`DescriptiveComplexity.reaches_of_wideUp` asks for **one** step per address,
which is all a scan needs and all a machine on a clock can afford. A roaming
program's outer loops are not like that: at each address it runs a whole
subroutine – walk to the register file, increment the mirror, walk back – and
only then moves on. So the round, not the step, is the unit. -/

/-- **A phase that runs a subroutine at every address.** Give the intended
configuration at each address of a stretch and, between each address and its
increment, a *run* of at most `w` steps rather than a single step; the machine
then gets from the bottom of the stretch to the top, and pays `w` for each
address it crossed.

This is the shape of every outer loop of a wide program – seeking an address,
sweeping a stage of a fixed-point iteration, comparing two tracks of the tape –
and the product is what a clock reads: a program is affordable when the rounds it
runs, times the width of one, stays below the number of addresses. A space-bounded
program ignores the product (`DescriptiveComplexity.reaches_of_wideRounds`), which
is what lets it iterate a fixed point. -/
theorem reachesIn_of_wideRounds (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop} {w : ℕ}
    (hround : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      (wideData A).ReachesIn w (conf s) (conf t)) :
    ∀ s : A → Prop, WMSetLe WMLe s₀ s → WMSetLe WMLe s s₁ →
      (wideData A).ReachesIn ((wideRank s - wideRank s₀) * w) (conf s₀) (conf s) := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hset := isLinOrd_wmSetLe h
  have key : ∀ k : ℕ, ∀ s : A → Prop, wideRank s = k →
      WMSetLe WMLe s₀ s → WMSetLe WMLe s s₁ →
      (wideData A).ReachesIn ((wideRank s - wideRank s₀) * w) (conf s₀) (conf s) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hrank hlb hub
      rcases eq_or_ne s₀ s with rfl | hne
      · rw [Nat.sub_self, Nat.zero_mul]
        exact TMData.reachesIn_refl
      · -- Above the bottom of the stretch, so not the empty address: it has a predecessor.
        have hlt : WMSetLt WMLe s₀ s := (wmSetLt_iff _ _).mpr ⟨hlb, hne⟩
        have hsome : ∃ x, s x := by
          by_contra hc
          exact hne (hset.2.2.1 s₀ s hlb (wmSetLe_of_empty h (fun x hx => hc ⟨x, hx⟩) s₀))
        obtain ⟨p, hp⟩ := exists_wmPred h hsome
        have hpl : WMSetLe WMLe s₀ p := (wmSetLt_iff_of_wmIncr h hp s₀).mp hlt
        have hpu : WMSetLe WMLe p s₁ := hset.2.1 p s s₁ (wmSetLe_of_wmIncr hp) hub
        have hb : wideRank s = wideRank p + 1 := wideRank_incr h hp
        have hlow : wideRank s₀ ≤ wideRank p := wideRank_mono h hpl
        have heq : (wideRank s - wideRank s₀) * w =
            (wideRank p - wideRank s₀) * w + w := by
          rw [show wideRank s - wideRank s₀ = (wideRank p - wideRank s₀) + 1 by omega,
            Nat.succ_mul]
        rw [heq]
        exact (ih _ (by omega) p rfl hpl hpu).trans (hround p s hp hpl hub)
  exact fun s hlb hub => key _ s rfl hlb hub

/-- **A phase that runs a subroutine at every address**, the budget forgotten:
each round is a run of any length whatever, which is what only a space-bounded
program can afford. -/
theorem reaches_of_wideRounds (h : IsLinOrd (WMLe (A := A)))
    {conf : (A → Prop) → Config (WPoint A)} {s₀ s₁ : A → Prop}
    (hround : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s → WMSetLe WMLe t s₁ →
      Relation.ReflTransGen (wideData A).Step (conf s) (conf t)) :
    ∀ s : A → Prop, WMSetLe WMLe s₀ s → WMSetLe WMLe s s₁ →
      Relation.ReflTransGen (wideData A).Step (conf s₀) (conf s) := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hset := isLinOrd_wmSetLe h
  have key : ∀ k : ℕ, ∀ s : A → Prop, wideRank s = k →
      WMSetLe WMLe s₀ s → WMSetLe WMLe s s₁ →
      Relation.ReflTransGen (wideData A).Step (conf s₀) (conf s) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hrank hlb hub
      rcases eq_or_ne s₀ s with rfl | hne
      · exact Relation.ReflTransGen.refl
      · have hlt : WMSetLt WMLe s₀ s := (wmSetLt_iff _ _).mpr ⟨hlb, hne⟩
        have hsome : ∃ x, s x := by
          by_contra hc
          exact hne (hset.2.2.1 s₀ s hlb (wmSetLe_of_empty h (fun x hx => hc ⟨x, hx⟩) s₀))
        obtain ⟨p, hp⟩ := exists_wmPred h hsome
        have hpl : WMSetLe WMLe s₀ p := (wmSetLt_iff_of_wmIncr h hp s₀).mp hlt
        have hpu : WMSetLe WMLe p s₁ := hset.2.1 p s s₁ (wmSetLe_of_wmIncr hp) hub
        have hb : wideRank s = wideRank p + 1 := wideRank_incr h hp
        exact (ih _ (by omega) p rfl hpl hpu).trans (hround p s hp hpl hub)
  exact fun s hlb hub => key _ s rfl hlb hub

/-- **What a sweep leaves behind, address by address.** The semantic twin of
`DescriptiveComplexity.reaches_of_wideRounds`, at the same measure and the same
stretch: a property of the addresses that holds at the bottom and is carried
across each increment holds everywhere the sweep has been.

`reaches_of_wideRounds` says the machine *gets* to every address of the stretch;
this says what is *true* when it does – the two are used together, the run
theorem consuming the round's machine hypothesis and this one the round's tape
hypothesis. -/
theorem holds_of_wideRounds (h : IsLinOrd (WMLe (A := A)))
    {Q : (A → Prop) → Prop} {s₀ s₁ : A → Prop} (hbase : Q s₀)
    (hround : ∀ s t : A → Prop, WMIncr WMLe s t → WMSetLe WMLe s₀ s →
      WMSetLe WMLe t s₁ → Q s → Q t) :
    ∀ s : A → Prop, WMSetLe WMLe s₀ s → WMSetLe WMLe s s₁ → Q s := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hset := isLinOrd_wmSetLe h
  have key : ∀ k : ℕ, ∀ s : A → Prop,
      bitRank (wideData A).Le (wideData A).Posn (Sum.inl s : WPoint A) = k →
      WMSetLe WMLe s₀ s → WMSetLe WMLe s s₁ → Q s := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hrank hlb hub
      rcases eq_or_ne s₀ s with rfl | hne
      · exact hbase
      · -- above the bottom of the stretch, so not the empty address
        have hlt : WMSetLt WMLe s₀ s := (wmSetLt_iff _ _).mpr ⟨hlb, hne⟩
        have hsome : ∃ x, s x := by
          by_contra hc
          exact hne (hset.2.2.1 s₀ s hlb
            (wmSetLe_of_empty h (fun x hx => hc ⟨x, hx⟩) s₀))
        obtain ⟨p, hp⟩ := exists_wmPred h hsome
        have hpl : WMSetLe WMLe s₀ p := (wmSetLt_iff_of_wmIncr h hp s₀).mp hlt
        have hpu : WMSetLe WMLe p s₁ := hset.2.1 p s s₁ (wmSetLe_of_wmIncr hp) hub
        have hb : bitRank (wideData A).Le (wideData A).Posn (Sum.inl s : WPoint A) =
            bitRank (wideData A).Le (wideData A).Posn (Sum.inl p : WPoint A) + 1 :=
          bitRank_succPos hlin ((succPos_wpLe_iff h p s).mpr hp)
        exact hround p s hp hpl hub (ih _ (by omega) p rfl hpl hpu)
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
theorem wmSetLt_of_wmIncr_le (h : IsLinOrd (WMLe (A := A))) {r r' t : A → Prop}
    (hi : WMIncr WMLe r r') (hub : WMSetLe WMLe r' t) : WMSetLt WMLe r t := by
  have hlin := isLinOrd_wmSetLe h
  refine (wmSetLt_iff r t).mpr ⟨hlin.2.1 r r' t (wmSetLe_of_wmIncr hi) hub, fun hc => ?_⟩
  exact ne_of_wmIncr hi (hlin.2.2.1 r r' (wmSetLe_of_wmIncr hi) (hc ▸ hub))

/-- An address at or below one whose increment is taken is strictly below that
increment: the side condition a leftward scan step needs. -/
theorem wmSetLt_of_le_wmIncr (h : IsLinOrd (WMLe (A := A))) {t r r' : A → Prop}
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
theorem reachesIn_scanRight (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {s t : A → Prop} (hle : WMSetLe WMLe s t)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    (wideData A).ReachesIn (wideRank t - wideRank s)
      ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ :=
  reachesIn_of_wideUp (conf := fun r => ⟨Sum.inr q, Sum.inl r, tp⟩) h hle
    fun r r' hi hlb hub => by
      obtain ⟨τ, a, htr, hsrc, hread, hdst, hwrite, hright, hcur⟩ :=
        hstep r hlb (wmSetLt_of_wmIncr_le h hi hub)
      exact step_wide_right h hi htr hsrc hread hdst hwrite hright hcur hcur fun _ _ => rfl

/-- **Scanning right**, the budget forgotten. -/
theorem reaches_scanRight (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {s t : A → Prop} (hle : WMSetLe WMLe s t)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    Relation.ReflTransGen (wideData A).Step
      ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ :=
  (reachesIn_scanRight h hle hstep).reflTransGen

/-- **Scanning left**, the same reading downwards: the transitions move left, and
the machine walks from `s` down to `t`. -/
theorem reachesIn_scanLeft (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {s t : A → Prop} (hle : WMSetLe WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ ¬WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    (wideData A).ReachesIn (wideRank s - wideRank t)
      ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ :=
  reachesIn_of_wideDown (conf := fun r => ⟨Sum.inr q, Sum.inl r, tp⟩) h hle
    fun r r' hi hlb hub => by
      obtain ⟨τ, a, htr, hsrc, hread, hdst, hwrite, hright, hcur⟩ :=
        hstep r' (wmSetLt_of_le_wmIncr h hlb hi) hub
      exact step_wide_left h hi htr hsrc hread hdst hwrite hright hcur hcur fun _ _ => rfl

/-- **Scanning left**, the budget forgotten. -/
theorem reaches_scanLeft (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {s t : A → Prop} (hle : WMSetLe WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ ¬WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    Relation.ReflTransGen (wideData A).Step
      ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ :=
  (reachesIn_scanLeft h hle hstep).reflTransGen

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
addresses those marks sit at. The budget is stated at the cell reached, and a
caller that knows a ceiling for its marks charges the scan against that ceiling
by `DescriptiveComplexity.wideRank_mono` and
`DescriptiveComplexity.TMData.ReachesIn.mono`. -/
theorem reachesIn_scanRight_least (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {Stop : (A → Prop) → Prop} {s : A → Prop}
    (hex : ∃ t, Stop t ∧ WMSetLe WMLe s t)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s r →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe r t) → ¬Stop r →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe s t ∧
      (∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t → ¬Stop r) ∧
      (wideData A).ReachesIn (wideRank t - wideRank s)
        ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ := by
  obtain ⟨t, ⟨hstop, hge⟩, hmin⟩ :=
    exists_least (isLinOrd_wmSetLe h) (P := fun t => Stop t ∧ WMSetLe WMLe s t) hex
  have hfirst : ∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t → ¬Stop r := fun r hlb hlt hc =>
    ((wmSetLt_iff r t).mp hlt).2 ((isLinOrd_wmSetLe h).2.2.1 r t
      ((wmSetLt_iff r t).mp hlt).1 (hmin r ⟨hc, hlb⟩))
  exact ⟨t, hstop, hge, hfirst,
    reachesIn_scanRight h hge fun r hlb hlt =>
      hstep r hlb ⟨t, hstop, ((wmSetLt_iff r t).mp hlt).1⟩ (hfirst r hlb hlt)⟩

/-- **A rightward scan arrives at the first cell that stops it**, the budget
forgotten. -/
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
  obtain ⟨t, hstop, hge, hfirst, hrun⟩ := reachesIn_scanRight_least h hex hstep
  exact ⟨t, hstop, hge, hfirst, hrun.reflTransGen⟩

/-- **A leftward scan arrives at the first cell that stops it**, the same reading
downwards: the *greatest* stopping cell at or below `s`. -/
theorem reachesIn_scanLeft_greatest (h : IsLinOrd (WMLe (A := A))) {q : A}
    {tp : WPoint A → WPoint A} {Stop : (A → Prop) → Prop} {s : A → Prop}
    (hex : ∃ t, Stop t ∧ WMSetLe WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe r s →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t r) → ¬Stop r →
      ∃ τ a : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q ∧ WMWrite τ a ∧ ¬WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t s ∧
      (∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s → ¬Stop r) ∧
      (wideData A).ReachesIn (wideRank s - wideRank t)
        ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ := by
  obtain ⟨t, ⟨hstop, hle⟩, hmax⟩ :=
    exists_greatest (isLinOrd_wmSetLe h) (P := fun t => Stop t ∧ WMSetLe WMLe t s) hex
  have hfirst : ∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s → ¬Stop r := fun r hlt hub hc =>
    ((wmSetLt_iff t r).mp hlt).2 ((isLinOrd_wmSetLe h).2.2.1 t r
      ((wmSetLt_iff t r).mp hlt).1 (hmax r ⟨hc, hub⟩))
  exact ⟨t, hstop, hle, hfirst,
    reachesIn_scanLeft h hle fun r hlt hub =>
      hstep r hub ⟨t, hstop, ((wmSetLt_iff t r).mp hlt).1⟩ (hfirst r hlt hub)⟩

/-- **A leftward scan arrives at the first cell that stops it**, the budget
forgotten. -/
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
  obtain ⟨t, hstop, hle, hfirst, hrun⟩ := reachesIn_scanLeft_greatest h hex hstep
  exact ⟨t, hstop, hle, hfirst, hrun.reflTransGen⟩

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

/-- **A clocked program accepts.** The same run, with its budget kept and
compared once with the clock: `DescriptiveComplexity.WideAccept` allows strictly
fewer steps than there are addresses, so a program is affordable exactly when the
sum of its phases stays below that.

The budget is the only difference between this and
`DescriptiveComplexity.acceptsSpace_of_wideRoam`, and it is the whole difference
between the two halves of the wide catalog: a program that iterates a fixed point
has no bound to offer, and one that guesses a certificate and checks it in a
fixed number of passes has. -/
theorem accepts_of_wideRoam (h : IsLinOrd (WMLe (A := A)))
    (hno : ∀ x y : A, ¬WMInp x y) {q₀ b : A} (hq : WMStart q₀) (hb : WMBlank b)
    {n : ℕ} {c : Config (WPoint A)}
    (hreach : (wideData A).ReachesIn n
      ⟨Sum.inr q₀, Sum.inl fun _ => False, fun _ => Sum.inr b⟩ c)
    (hlt : n < Nat.card {p : WPoint A // (wideData A).Posn p})
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : WMAcc qa) :
    (wideData A).Accepts := by
  refine TMData.accepts_of_reachesIn (isInit_wide h hno hq hb) hreach hlt ?_
  change wpMark WMAcc c.state
  rw [hstate]
  exact hacc

/-- **A clocked program accepts**, with its budget compared against the count
rather than against the number of positions: the same statement as
`DescriptiveComplexity.accepts_of_wideRoam` in the form a program's arithmetic
actually produces, since what a reduction controls is `n` – the size of the
universe it draws – and not the subtype of positions. -/
theorem accepts_of_wideRoam_lt_two_pow (h : IsLinOrd (WMLe (A := A)))
    (hno : ∀ x y : A, ¬WMInp x y) {q₀ b : A} (hq : WMStart q₀) (hb : WMBlank b)
    {n : ℕ} {c : Config (WPoint A)}
    (hreach : (wideData A).ReachesIn n
      ⟨Sum.inr q₀, Sum.inl fun _ => False, fun _ => Sum.inr b⟩ c)
    (hlt : n < 2 ^ Nat.card A)
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : WMAcc qa) :
    (wideData A).Accepts :=
  accepts_of_wideRoam h hno hq hb hreach (by rw [card_wideAddr]; exact hlt) hstate hacc

end Roam

end DescriptiveComplexity
