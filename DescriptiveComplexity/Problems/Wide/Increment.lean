/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.WellFormed

/-!
# The address primitives of a wide machine

What a wide machine can do to its head, and nothing else: start it on the least
position, move it to a neighbour, recognize the last one. Every step of every
program a hardness reduction will write is one of these, so they are settled
first, at an arbitrary order relation and from finiteness alone.

The one thing to know about them is what an address's neighbour *is*. An address
is a subset read as a binary number whose **most** significant digit is the
`Le`-least element (`DescriptiveComplexity.WMSetLe` compares at the least element
where two addresses differ), so incrementing flips a run of trailing digits: the
greatest element `u` outside the address enters, and everything above `u` leaves.
`DescriptiveComplexity.WMIncr` says that relationally – with `u` existentially
quantified rather than chosen – so no choice function enters the statements and
the increment is first-order describable as it stands.

| primitive | what it is | theorem |
|---|---|---|
| the head's start | the empty address | `DescriptiveComplexity.minPos_wpLe` |
| the last cell | the whole universe | `DescriptiveComplexity.maxPos_wpLe` |
| one step | the binary increment | `DescriptiveComplexity.succPos_wpLe_iff` |

The last of these is the load-bearing one: `DescriptiveComplexity.TMData.Step`
moves the head by `DescriptiveComplexity.SuccPos`, an *order-theoretic* notion
(“no position strictly between”), while a program reasons with the increment. The
two agree, which is what lets a machine maintain a mirror of its own head
position by incrementing it – the invariant the whole hardness plan rests on,
since a head cannot read the digits of its address.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Extremal elements of a definable set -/

section Extremal

variable {α : Type} [Finite α] {Le : α → α → Prop}

/-- A nonempty set has a `Le`-least element. -/
theorem exists_least (h : IsLinOrd Le) {P : α → Prop} (hne : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → Le x y := by
  letI := h.toLinearOrder
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image {x : α | P x} id (Set.toFinite _) hne
  exact ⟨x, hx, fun y hy => hmin y hy⟩

/-- A nonempty set has a `Le`-greatest element. -/
theorem exists_greatest (h : IsLinOrd Le) {P : α → Prop} (hne : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → Le y x := by
  letI := h.toLinearOrder
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image {x : α | P x} id (Set.toFinite _) hne
  exact ⟨x, hx, fun y hy => hmax y hy⟩

end Extremal

/-! ### The strict order, and the strict comparison of addresses -/

section Strict

variable {α : Type}

/-- The strict part of an order relation, in the shape the address layer writes
it. -/
def WMLt (Le : α → α → Prop) (x y : α) : Prop := Le x y ∧ ¬Le y x

/-- **The strict comparison of two addresses**: at some element the first is out
of and the second in, they agree at every strictly smaller element. This is the
second disjunct of `DescriptiveComplexity.WMSetLe`, named. -/
def WMSetLt (Le : α → α → Prop) (s t : α → Prop) : Prop :=
  ∃ x, (∀ y, WMLt Le y x → (s y ↔ t y)) ∧ ¬s x ∧ t x

/-- Weak comparison of addresses is agreement or strict comparison, by
definition. -/
theorem wmSetLe_iff_wmSetLt (Le : α → α → Prop) (s t : α → Prop) :
    WMSetLe Le s t ↔ ((∀ x, s x ↔ t x) ∨ WMSetLt Le s t) :=
  Iff.rfl

/-- Two elements neither of which is strictly below the other are equal. -/
theorem eq_of_not_wmLt {Le : α → α → Prop} (h : IsLinOrd Le) {x y : α}
    (h1 : ¬WMLt Le x y) (h2 : ¬WMLt Le y x) : x = y := by
  rcases h.2.2.2 x y with hle | hle
  · exact h.2.2.1 x y hle (by
      by_contra hc
      exact h1 ⟨hle, hc⟩)
  · exact h.2.2.1 x y (by
      by_contra hc
      exact h2 ⟨hle, hc⟩) hle

end Strict

/-! ### The increment of an address -/

section Incr

variable {α : Type} {Le : α → α → Prop}

/-- **The binary increment of an address**: at the greatest element `u` the
address does not contain – so that it contains everything strictly above `u` –
the increment adds `u` and removes everything strictly above it. The carry
position is quantified, not chosen: nothing here needs a choice function, and the
relation is first-order in the two addresses. -/
def WMIncr (Le : α → α → Prop) (s t : α → Prop) : Prop :=
  ∃ u, ¬s u ∧ (∀ v, WMLt Le u v → s v) ∧
    ∀ v, t v ↔ (v = u ∨ (s v ∧ ¬WMLt Le u v))

/-- **The carry position of an increment is unique**: it is the greatest element
outside the address, and an address has only one such. -/
theorem wmIncr_carry_unique (h : IsLinOrd Le) {s : α → Prop} {u u' : α}
    (hu : ¬s u) (hau : ∀ v, WMLt Le u v → s v)
    (hu' : ¬s u') (hau' : ∀ v, WMLt Le u' v → s v) : u = u' :=
  eq_of_not_wmLt h (fun hc => hu' (hau u' hc)) (fun hc => hu (hau' u hc))

/-- **The increment is unique**, so a program stepping by it is deterministic. -/
theorem wmIncr_functional (h : IsLinOrd Le) {s t t' : α → Prop}
    (hi : WMIncr Le s t) (hi' : WMIncr Le s t') : t = t' := by
  obtain ⟨u, hu, hau, ht⟩ := hi
  obtain ⟨u', hu', hau', ht'⟩ := hi'
  obtain rfl : u = u' := wmIncr_carry_unique h hu hau hu' hau'
  exact funext fun v => propext ((ht v).trans (ht' v).symm)

/-- **The increment is above the address**: they differ at the carry position,
and agree at every element below it – that is, above it in significance. -/
theorem wmSetLe_of_wmIncr {s t : α → Prop} (hi : WMIncr Le s t) : WMSetLe Le s t := by
  obtain ⟨u, hu, -, ht⟩ := hi
  refine Or.inr ⟨u, fun y hy => ?_, hu, (ht u).mpr (Or.inl rfl)⟩
  have hyu : y ≠ u := by
    intro hc
    rw [hc] at hy
    exact hy.2 hy.1
  refine ((ht y).trans ?_).symm
  exact ⟨fun hc => (hc.resolve_left hyu).1, fun hc => Or.inr ⟨hc, fun hup => hy.2 hup.1⟩⟩

/-- The increment differs from the address, at the carry position. -/
theorem ne_of_wmIncr {s t : α → Prop} (hi : WMIncr Le s t) : s ≠ t := by
  obtain ⟨u, hu, -, ht⟩ := hi
  intro hst
  exact hu (hst ▸ (ht u).mpr (Or.inl rfl) : s u)

variable [Finite α]

/-- **Every address but the last has an increment.** -/
theorem exists_wmIncr (h : IsLinOrd Le) {s : α → Prop} (hne : ∃ x, ¬s x) :
    ∃ t, WMIncr Le s t := by
  obtain ⟨u, hu, hmax⟩ := exists_greatest h hne
  refine ⟨fun v => v = u ∨ (s v ∧ ¬(Le u v ∧ ¬Le v u)), u, hu, fun v hv => ?_, fun _ => Iff.rfl⟩
  by_contra hs
  exact hv.2 (hmax v hs)

/-- **Every address but the first has a predecessor.** The carry position of the
step *into* an address is the greatest element that address contains: everything
above it leaves, and it is what the increment put there. A program walking its
mirror downwards – which is what an increment does, the least significant digit
being the `Le`-greatest element – needs this end of the statement. -/
theorem exists_wmPred (h : IsLinOrd Le) {s : α → Prop} (hne : ∃ x, s x) :
    ∃ t, WMIncr Le t s := by
  obtain ⟨u, hu, hmax⟩ := exists_greatest h hne
  refine ⟨fun v => WMLt Le u v ∨ (s v ∧ v ≠ u), u, ?_, fun v hv => Or.inl hv, fun v => ?_⟩
  · exact fun hc => hc.elim (fun hlt => hlt.2 (h.1 u)) fun hs => hs.2 rfl
  · constructor
    · intro hs
      rcases eq_or_ne v u with rfl | hvu
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inr ⟨hs, hvu⟩, fun hlt => hlt.2 (hmax v hs)⟩
    · rintro (rfl | ⟨ht | ht, hnlt⟩)
      · exact hu
      · exact absurd ht hnlt
      · exact ht.1

omit [Finite α] in
/-- Strict comparison of addresses is weak comparison plus difference. -/
theorem wmSetLt_iff (s t : α → Prop) : WMSetLt Le s t ↔ (WMSetLe Le s t ∧ s ≠ t) := by
  constructor
  · rintro ⟨x, hb, hs, ht⟩
    exact ⟨Or.inr ⟨x, hb, hs, ht⟩, fun hc => hs (hc ▸ ht)⟩
  · rintro ⟨hle | hlt, hne⟩
    · exact absurd (funext fun z => propext (hle z)) hne
    · exact hlt

omit [Finite α] in
/-- **A set below an upward-closed address is contained in it**: at the element
where they first differ the smaller one says no, and everything above that
element is in the larger by closure — so nothing the smaller holds escapes.
This is what says a register enumerated up to a *region* (the address whose
elements are exactly a final segment's cells) never holds a cell outside it. -/
theorem subset_of_wmSetLe (h : IsLinOrd Le) {s t : α → Prop}
    (hup : ∀ x y, t x → WMLt Le x y → t y) (hle : WMSetLe Le s t)
    {x : α} (hx : s x) : t x := by
  rcases hle with hag | ⟨p, hagree, hnp, hp⟩
  · exact (hag x).mp hx
  by_contra hc
  rcases Classical.em (WMLt Le x p) with hlt | hnlt
  · exact hc ((hagree x hlt).mp hx)
  · exact hc (hup p x hp (by
      rcases Classical.em (WMLt Le p x) with hpx | hpx
      · exact hpx
      · exact absurd (eq_of_not_wmLt h hnlt hpx) (fun hxp => hc (hxp ▸ hp))))

/-- **An address holding nothing is below every address.** -/
theorem wmSetLe_of_empty (h : IsLinOrd Le) {s : α → Prop} (hs : ∀ x, ¬s x) (t : α → Prop) :
    WMSetLe Le s t := by
  rcases Classical.em (∃ x, t x) with hne | hno
  · obtain ⟨x, hx, hmin⟩ := exists_least h hne
    exact Or.inr ⟨x, fun y hy => iff_of_false (hs y) fun hc => hy.2 (hmin y hc), hs x, hx⟩
  · exact Or.inl fun z => iff_of_false (hs z) fun hc => hno ⟨z, hc⟩

/-- **A sub-address is below the address containing it.** The least element where
two addresses differ decides the comparison, and if one is contained in the other
that element is in the larger – so a program that only ever *clears* cells moves
its address down the tape, and one that only sets them moves it up. -/
theorem wmSetLe_of_subset (h : IsLinOrd Le) {s t : α → Prop} (hsub : ∀ x, s x → t x) :
    WMSetLe Le s t := by
  rcases Classical.em (∃ x, ¬(s x ↔ t x)) with hne | hno
  · obtain ⟨x, hx, hmin⟩ := exists_least h hne
    refine Or.inr ⟨x, fun y hy => not_not.mp fun hc => hy.2 (hmin y hc), fun hc => ?_, ?_⟩
    · exact hx (iff_of_true hc (hsub x hc))
    · by_contra hc
      exact hx (iff_of_false (fun hs => hc (hsub x hs)) hc)
  · exact Or.inl fun z => not_not.mp fun hc => hno ⟨z, hc⟩

/-- **An address holding everything is above every address.** -/
theorem wmSetLe_of_full (h : IsLinOrd Le) {t : α → Prop} (ht : ∀ x, t x) (s : α → Prop) :
    WMSetLe Le s t := by
  rcases Classical.em (∃ x, ¬s x) with hne | hno
  · obtain ⟨x, hx, hmin⟩ := exists_least h hne
    refine Or.inr ⟨x, fun y hy => iff_of_true ?_ (ht y), hx, ht x⟩
    by_contra hc
    exact hy.2 (hmin y hc)
  · exact Or.inl fun z => iff_of_true (not_not.mp fun hc => hno ⟨z, hc⟩) (ht z)

/-- **The strict part of the address order is the strict comparison of
addresses**: the fold of `DescriptiveComplexity.Problems.Wide.Fold` writes its
strict order as `DescriptiveComplexity.WMLt` of whatever relation it is given, and
at addresses that is `DescriptiveComplexity.WMSetLt`. -/
theorem wmLt_wmSetLe_iff (h : IsLinOrd Le) (s t : α → Prop) :
    WMLt (WMSetLe Le) s t ↔ WMSetLt Le s t := by
  have hlin := isLinOrd_wmSetLe h
  rw [wmSetLt_iff]
  constructor
  · rintro ⟨hle, hnot⟩
    refine ⟨hle, fun hc => hnot ?_⟩
    rw [hc]
    exact hlin.1 t
  · rintro ⟨hle, hne⟩
    exact ⟨hle, fun hc => hne (hlin.2.2.1 s t hle hc)⟩

/-- **Nothing lies strictly between an address and its increment**: an address
weakly between them agrees with one of the two. This is the half that makes the
increment an *immediate* successor, and the only place the linearity of the
address order is used. -/
theorem eq_of_between_wmIncr (h : IsLinOrd Le) {s t r : α → Prop} (hi : WMIncr Le s t)
    (h1 : WMSetLe Le s r) (h2 : WMSetLe Le r t) : r = s ∨ r = t := by
  have hlin := isLinOrd_wmSetLe h
  obtain ⟨u, hu, habove, ht⟩ := hi
  rcases h1 with hag | ⟨x, hbx, hsx, hrx⟩
  · exact Or.inl (funext fun z => propext (hag z).symm)
  -- The first difference between `s` and `r` is at or below the carry position,
  -- `s` containing everything above it.
  have hxu : ¬(Le u x ∧ ¬Le x u) := fun hc => hsx (habove x hc)
  rcases eq_or_ne x u with hxeq | hxne
  · -- It is *at* the carry position, so `r` agrees with `t` everywhere.
    rw [hxeq] at hbx hsx hrx
    refine Or.inr ?_
    have hrt : ∀ z, (Le z u ∧ ¬Le u z) → (r z ↔ t z) := by
      intro z hz
      have hzu : z ≠ u := by
        intro hc
        rw [hc] at hz
        exact hz.2 hz.1
      refine (hbx z hz).symm.trans ?_
      exact ((ht z).trans ⟨fun hc => (hc.resolve_left hzu).1,
        fun hc => Or.inr ⟨hc, fun hup => hz.2 hup.1⟩⟩).symm
    rcases h2 with hag | ⟨z, -, hrz, htz⟩
    · exact funext fun w => propext (hag w)
    · exfalso
      rcases h.2.2.2 z u with hzu | huz
      · rcases eq_or_ne z u with hzeq | hzne
        · rw [hzeq] at hrz
          exact hrz hrx
        · exact hrz ((hrt z ⟨hzu, fun hc => hzne (h.2.2.1 z u hzu hc)⟩).mpr htz)
      · rcases eq_or_ne z u with hzeq | hzne
        · rw [hzeq] at hrz
          exact hrz hrx
        · exact ((ht z).mp htz).elim hzne
            fun hc => hc.2 ⟨huz, fun hc' => hzne (h.2.2.1 z u hc' huz)⟩
  · -- It is strictly below it, which makes `t` smaller than `r`: impossible.
    exfalso
    have hnu : ¬Le u x := fun hc => hxu ⟨hc, fun hc' => hxne (h.2.2.1 x u hc' hc)⟩
    have hxlt : Le x u ∧ ¬Le u x := ⟨(h.2.2.2 x u).resolve_right hnu, hnu⟩
    have htx : ¬t x := fun hc => ((ht x).mp hc).elim hxne fun hc' => hsx hc'.1
    have htr : WMSetLe Le t r := by
      refine Or.inr ⟨x, fun y hy => ?_, htx, hrx⟩
      have hyu : Le y u ∧ ¬Le u y :=
        ⟨h.2.1 y x u hy.1 hxlt.1, fun hc => hy.2 (h.2.1 x u y hxlt.1 hc)⟩
      have hyne : y ≠ u := by
        intro hc
        rw [hc] at hyu
        exact hyu.2 hyu.1
      exact ((ht y).trans ⟨fun hc => (hc.resolve_left hyne).1,
        fun hc => Or.inr ⟨hc, fun hup => hyu.2 hup.1⟩⟩).trans (hbx y hy)
    refine htx ?_
    rw [hlin.2.2.1 t r htr h2]
    exact hrx

/-- **An address is below the increment of another exactly when it is at or below
that other**: the increment is the immediate successor, so `< t'` and `≤ t` are
the same. This is the hypothesis the fold of
`DescriptiveComplexity.Problems.Wide.Fold` asks about the successor, discharged for
addresses. -/
theorem wmSetLt_iff_of_wmIncr (h : IsLinOrd Le) {t t' : α → Prop} (hi : WMIncr Le t t')
    (s : α → Prop) : WMSetLt Le s t' ↔ WMSetLe Le s t := by
  have hlin := isLinOrd_wmSetLe h
  have htt' : WMSetLe Le t t' := wmSetLe_of_wmIncr hi
  have hne : t ≠ t' := ne_of_wmIncr hi
  constructor
  · intro hlt
    obtain ⟨hle, hst'⟩ := (wmSetLt_iff s t').mp hlt
    rcases hlin.2.2.2 s t with hc | hc
    · exact hc
    · rcases eq_of_between_wmIncr h hi hc hle with hst | hst
      · exact hst ▸ hlin.1 s
      · exact absurd hst hst'
  · intro hle
    refine (wmSetLt_iff s t').mpr ⟨hlin.2.1 s t t' hle htt', fun hc => ?_⟩
    exact hne (hlin.2.2.1 t t' htt' (hc ▸ hle))

/-- **The empty address's successor is at or below every nonempty address**: an
address strictly below it is at or below the empty one, hence empty. This is
what puts a program's data – every address it marks anything at – inside a
stretch that starts one step above the cell its head began on. -/
theorem wmSetLe_succ_bot_of_nonempty (h : IsLinOrd Le) {s₀ s : α → Prop}
    (hs₀ : WMIncr Le (fun _ => False) s₀) (hne : ∃ x, s x) : WMSetLe Le s₀ s := by
  have hlin := isLinOrd_wmSetLe h
  by_contra hc
  have hlt : WMSetLt Le s s₀ :=
    (wmSetLt_iff _ _).mpr ⟨(hlin.2.2.2 s s₀).resolve_right hc, fun hEq => hc (hEq ▸ hlin.1 s)⟩
  have hle : WMSetLe Le s (fun _ => False) := (wmSetLt_iff_of_wmIncr h hs₀ s).mp hlt
  obtain ⟨x, hx⟩ := hne
  have hEq : s = fun _ => False :=
    hlin.2.2.1 s (fun _ => False) hle (wmSetLe_of_empty h (fun _ => not_false) s)
  exact (hEq ▸ hx : (fun _ : α => False) x)

/-- **An increment cannot overshoot**: the successor of an address strictly below
another is still at or below it. A walk that stops at the first address a marker
sits on reads this at every round. -/
theorem wmSetLe_of_wmIncr_of_lt (h : IsLinOrd Le) {t t' s : α → Prop} (hi : WMIncr Le t t')
    (hlt : WMSetLt Le t s) : WMSetLe Le t' s := by
  have hlin := isLinOrd_wmSetLe h
  rcases hlin.2.2.2 t' s with hc | hc
  · exact hc
  · rcases eq_or_ne s t' with rfl | hne
    · exact hlin.1 _
    · exact absurd ((wmSetLt_iff_of_wmIncr h hi s).mp ((wmSetLt_iff s t').mpr ⟨hc, hne⟩))
        fun hst => ((wmSetLt_iff t s).mp hlt).2
          (hlin.2.2.1 t s ((wmSetLt_iff t s).mp hlt).1 hst)

/-! ### Every address is reached from the empty one by increments

The chain and its monotonicity, over an arbitrary linearly ordered index. The
universe of a wide machine is one such index and so is the index of a *file*,
which is what a program handed its file counts its rounds over. -/

section Chain

/-- The addresses strictly below a given one, as a measure to induct on. -/
private noncomputable def belowCount (Le : α → α → Prop) (s : α → Prop) : ℕ :=
  {t : α → Prop | WMSetLt Le t s}.ncard

private theorem belowCount_lt (h : IsLinOrd Le) {s t : α → Prop} (hi : WMIncr Le s t) :
    belowCount Le s < belowCount Le t := by
  classical
  have hlin := isLinOrd_wmSetLe h
  have hst : WMSetLt Le s t :=
    (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
  refine Set.ncard_lt_ncard ⟨fun r hr => ?_, fun hsub => ?_⟩ (Set.toFinite _)
  · refine (wmSetLt_iff _ _).mpr ⟨hlin.2.1 r s t ((wmSetLt_iff _ _).mp hr).1
      ((wmSetLt_iff _ _).mp hst).1, fun hEq => ?_⟩
    exact ((wmSetLt_iff _ _).mp hst).2
      (hlin.2.2.1 s t ((wmSetLt_iff _ _).mp hst).1 (hEq ▸ ((wmSetLt_iff _ _).mp hr).1))
  · exact ((wmSetLt_iff _ _).mp (hsub hst : WMSetLt Le s s)).2 rfl

/-- **Every address is reached from the empty one by increments**: a finite
chain, each step the binary increment, ending at the target. This is
`DescriptiveComplexity.Draw.exists_wmChain` over an arbitrary index. -/
theorem exists_wmChainOf (h : IsLinOrd Le) (target : α → Prop) :
    ∃ (n : ℕ) (mV : Fin (n + 1) → (α → Prop)),
      mV 0 = (fun _ => False) ∧ mV (Fin.last n) = target ∧
      ∀ k : Fin n, WMIncr Le (mV k.castSucc) (mV k.succ) := by
  classical
  suffices key : ∀ (k : ℕ) (s : α → Prop), belowCount Le s = k →
      ∃ (n : ℕ) (mV : Fin (n + 1) → (α → Prop)),
        mV 0 = (fun _ => False) ∧ mV (Fin.last n) = s ∧
        ∀ j : Fin n, WMIncr Le (mV j.castSucc) (mV j.succ) from
    key _ target rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hrank
    rcases Classical.em (∃ x, s x) with hne | hemp
    · obtain ⟨t, hi⟩ := exists_wmPred h hne
      obtain ⟨n, mV, h0, hlast, hchain⟩ :=
        ih (belowCount Le t) (hrank ▸ belowCount_lt h hi) t rfl
      refine ⟨n + 1, Fin.snoc mV s, ?_, ?_, ?_⟩
      · rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl,
          Fin.snoc_castSucc]
        exact h0
      · exact Fin.snoc_last _ _
      · intro j
        rcases Nat.lt_or_ge (j : ℕ) n with hj | hj
        · have e1 : (Fin.castSucc j : Fin (n + 2)) =
              Fin.castSucc (Fin.castSucc (⟨(j : ℕ), hj⟩ : Fin n)) := Fin.ext rfl
          have e2 : (Fin.succ j : Fin (n + 2)) =
              Fin.castSucc (Fin.succ (⟨(j : ℕ), hj⟩ : Fin n)) := Fin.ext rfl
          rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hchain _
        · have hjn : (j : ℕ) = n := by have := j.isLt; omega
          have e1 : (Fin.castSucc j : Fin (n + 2)) = (Fin.last n).castSucc :=
            Fin.ext hjn
          have e2 : (Fin.succ j : Fin (n + 2)) = Fin.last (n + 1) :=
            Fin.ext (by rw [Fin.val_succ, Fin.val_last, hjn])
          rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_last, hlast]
          exact hi
    · have hs : s = fun _ => False :=
        funext fun x => propext ⟨fun hx => hemp ⟨x, hx⟩, False.elim⟩
      exact ⟨0, fun _ => fun _ => False, rfl, hs.symm, fun j => j.elim0⟩

/-- **The chain is strictly increasing**: two positions compare as their
addresses do, by induction on the distance. -/
theorem wmChainOf_lt (h : IsLinOrd Le) {n : ℕ}
    {mV : Fin (n + 1) → (α → Prop)}
    (hchain : ∀ k : Fin n, WMIncr Le (mV k.castSucc) (mV k.succ))
    {a a' : Fin (n + 1)} (hlt : a < a') :
    WMSetLt Le (mV a) (mV a') := by
  have hset := isLinOrd_wmSetLe h
  have hstep : ∀ (d : ℕ) (b b' : Fin (n + 1)), (b' : ℕ) = (b : ℕ) + d + 1 →
      WMSetLt Le (mV b) (mV b') := by
    intro d
    induction d with
    | zero =>
      intro b b' hb
      have hbn : (b : ℕ) < n := by have := b'.isLt; omega
      have e1 : mV b = mV (Fin.castSucc (⟨(b : ℕ), hbn⟩ : Fin n)) :=
        congrArg mV (Fin.ext rfl)
      have e2 : mV b' = mV (Fin.succ (⟨(b : ℕ), hbn⟩ : Fin n)) :=
        congrArg mV (Fin.ext hb)
      rw [e1, e2]
      have hi := hchain ⟨(b : ℕ), hbn⟩
      exact (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
    | succ d ihd =>
      intro b b' hb
      have hmn : (b : ℕ) + d + 1 < n + 1 := by have := b'.isLt; omega
      set m : Fin (n + 1) := ⟨(b : ℕ) + d + 1, hmn⟩ with hm
      have hmval : (m : ℕ) = (b : ℕ) + d + 1 := rfl
      have hbm := ihd b m rfl
      have hmb' : WMSetLt Le (mV m) (mV b') := by
        have hmn' : (m : ℕ) < n := by have := b'.isLt; omega
        have e1 : mV m = mV (Fin.castSucc (⟨(m : ℕ), hmn'⟩ : Fin n)) :=
          congrArg mV (Fin.ext rfl)
        have e2 : mV b' = mV (Fin.succ (⟨(m : ℕ), hmn'⟩ : Fin n)) :=
          congrArg mV (Fin.ext (show (b' : ℕ) = (m : ℕ) + 1 by omega))
        rw [e1, e2]
        have hi := hchain ⟨(m : ℕ), hmn'⟩
        exact (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
      rw [wmSetLt_iff] at hbm hmb' ⊢
      refine ⟨hset.2.1 _ _ _ hbm.1 hmb'.1, fun hc => ?_⟩
      exact hmb'.2 (hset.2.2.1 _ _ hmb'.1 (hc ▸ hbm.1))
  exact hstep ((a' : ℕ) - (a : ℕ) - 1) a a' (by omega)

end Chain

end Incr

/-! ### The three primitives, on the universe of a wide machine -/

section Machine

variable {A : Type} [Language.wide.Structure A] [Finite A]

omit [Language.wide.Structure A] [Finite A] in
/-- Only addresses are positions, so both ends of a step are addresses. -/
theorem wpPosn_iff (p : WPoint A) : wpPosn p ↔ ∃ s, p = Sum.inl s := by
  match p with
  | Sum.inl s => exact iff_of_true trivial ⟨s, rfl⟩
  | Sum.inr x =>
    refine iff_of_false (fun h => h) ?_
    rintro ⟨s, hs⟩
    simp at hs

/-- **The head of a wide machine starts on the empty address.** -/
theorem minPos_wpLe (h : IsLinOrd (WMLe (A := A))) :
    MinPos wpLe wpPosn (Sum.inl fun _ => False : WPoint A) := by
  refine ⟨trivial, ?_⟩
  rintro (t | x) hq
  · exact wmSetLe_of_empty h (fun _ hc => hc) t
  · exact absurd hq (fun hc => hc)

/-- **The last cell of a wide machine is the full address.** -/
theorem maxPos_wpLe (h : IsLinOrd (WMLe (A := A))) :
    MaxPos wpLe wpPosn (Sum.inl fun _ => True : WPoint A) := by
  refine ⟨trivial, ?_⟩
  rintro (t | x) hq
  · exact wmSetLe_of_full h (fun _ => trivial) t
  · exact absurd hq (fun hc => hc)

/-- **A step of a wide machine is the binary increment of its address.** The
machine's own primitive is `DescriptiveComplexity.SuccPos`, which says only that
no position lies strictly between; this identifies it with the increment, which is
what a program can maintain. -/
theorem succPos_wpLe_iff (h : IsLinOrd (WMLe (A := A))) (s t : A → Prop) :
    SuccPos wpLe wpPosn (Sum.inl s : WPoint A) (Sum.inl t) ↔ WMIncr WMLe s t := by
  have hlin := isLinOrd_wmSetLe h
  constructor
  · rintro ⟨-, -, hle, hne, hbetw⟩
    -- The address is not the last one, so it has an increment; that increment is `t`.
    have hfull : ∃ x, ¬s x := by
      rcases Classical.em (∃ x, ¬s x) with hex | hno
      · exact hex
      · exfalso
        have hsu : ∀ x, s x := fun x => not_not.mp fun hc => hno ⟨x, hc⟩
        rcases hle with hag | ⟨x, -, hsx, -⟩
        · exact hne (congrArg Sum.inl (funext fun z => propext (hag z)))
        · exact hsx (hsu x)
    obtain ⟨t', hi⟩ := exists_wmIncr h hfull
    have h1 := wmSetLe_of_wmIncr hi
    have h2 : WMSetLe WMLe s t := hle
    rcases hlin.2.2.2 t t' with hc | hc
    · rcases eq_of_between_wmIncr h hi h2 hc with hts | hts
      · exact absurd (congrArg Sum.inl hts.symm) hne
      · rw [hts]
        exact hi
    · rcases hbetw (Sum.inl t') trivial h1 hc with hc' | hc'
      · exact absurd (Sum.inl_injective hc' : t' = s) fun he => ne_of_wmIncr hi he.symm
      · rw [← (Sum.inl_injective hc' : t' = t)]
        exact hi
  · intro hi
    refine ⟨trivial, trivial, wmSetLe_of_wmIncr hi, ?_, ?_⟩
    · exact fun hc => ne_of_wmIncr hi (Sum.inl_injective hc)
    · rintro (r | x) hr h1 h2
      · exact (eq_of_between_wmIncr h hi h1 h2).imp (congrArg Sum.inl) (congrArg Sum.inl)
      · exact absurd hr (fun hc => hc)

end Machine

end DescriptiveComplexity
