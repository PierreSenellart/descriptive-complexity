/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.MachinesAlt

/-!
# Alternating machines in bounded space

The fourth acceptance notion of `DescriptiveComplexity.TMData`, and the one
that reaches EXPTIME: an *alternating* machine whose tape is indexed by the
positions, with **no bound on the length of a play and no bound on the number
of alternations**. It stands to `DescriptiveComplexity.ATMData.AltAccepts`
exactly as `DescriptiveComplexity.TMData.AcceptsSpace` stands to
`DescriptiveComplexity.TMData.Accepts`: the step budget is dropped, the space
stays bounded by construction, and what changes is that a play no longer fits
inside the structure.

## Winning, as an inductive predicate

`DescriptiveComplexity.ATMData.AltAcc` recurses on a budget, which is what makes
it a Lean-level recursion rather than a fixed point. With the budget gone the
right presentation is the **least fixed point** of the game operator, and in
Lean that is an inductive predicate
(`DescriptiveComplexity.ATMData.AltWin`): an accepting state wins; an
existential configuration wins when *some* successor does; a universal one when
it has a successor and *every* successor wins. Looping therefore loses, which is
the standard convention and the one that agrees with the budgeted definition
(`DescriptiveComplexity.ATMData.altWin_iff_exists_altAcc`).

Being an inductive rather than a `∃ n` also makes the correspondence with the
AND/OR game of alternating reachability a matter of matching constructors, which
is what the EXPTIME membership proof consumes.

## Unbounded alternation, at no cost

`DescriptiveComplexity.ATMData.BlocksWellFormed` is what bounds the number of
alternations, by forbidding a transition from lowering the block index; it is
*not* imposed here. What is imposed instead is only that the marks partition the
states in two (`DescriptiveComplexity.ATMData.BlocksSplit`), so that block `0`
is the existential player and block `1` the universal one
(`DescriptiveComplexity.ATMData.isUniv_true_iff_blk_one`). No second machine
record is needed and no lemma of `DescriptiveComplexity.MachinesAlt` has to be
restated: the vocabulary is `FirstOrder.Language.turingAlt 2` unchanged.
-/

namespace DescriptiveComplexity

/-- A configuration is a state, a head position and a tape, and nothing else. -/
def Config.equivProd (A : Type) : Config A ≃ A × A × (A → A) where
  toFun c := (c.state, c.head, c.tape)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance Config.instFinite {A : Type} [Finite A] : Finite (Config A) :=
  Finite.of_equiv _ (Config.equivProd A).symm

namespace ATMData

variable {A : Type} (M : ATMData A)

/-! ### Winning the game on the configuration graph -/

/-- **Winning the alternating game**, with no bound on the length of a play: an
accepting state wins; an existential configuration wins when some successor
does; a universal one wins when it has a successor and every successor wins.

Being a least fixed point, this makes an infinite play a loss for the
existential player – the standard convention, and the one the budgeted
`DescriptiveComplexity.ATMData.AltAcc` already has. -/
inductive AltWin (start : Bool) : Config A → Prop
  /-- An accepting state wins outright. -/
  | acc {c : Config A} : M.Acc c.state → AltWin start c
  /-- An existential configuration wins when some successor does. -/
  | ex {c c' : Config A} : ¬M.IsUniv start c.state → M.Step c c' → AltWin start c' →
      AltWin start c
  /-- A universal configuration wins when it has a successor and every
  successor wins. -/
  | all {c : Config A} : M.IsUniv start c.state → (∃ c', M.Step c c') →
      (∀ c', M.Step c c' → AltWin start c') → AltWin start c

/-- **Acceptance in bounded space**: an initial configuration wins, the choice
of that configuration belonging to the player who moves first – exactly as in
`DescriptiveComplexity.ATMData.AltAccepts`, and for the same reason. -/
def AltAcceptsSpace (start : Bool) : Prop :=
  guardQ start (fun c₀ : Config A => M.IsInit c₀) (fun c₀ => M.AltWin start c₀)

/-! ### The budgeted definition, unbounded -/

variable {M}

/-- A budgeted win is a win. -/
theorem altWin_of_altAcc {start : Bool} :
    ∀ (n : ℕ) {c : Config A}, M.AltAcc start n c → M.AltWin start c := by
  intro n
  induction n with
  | zero => intro c h; exact .acc h
  | succ n ih =>
    intro c h
    rcases h with h | ⟨hu, hex, hall⟩ | ⟨hu, c', hstep, hacc⟩
    · exact .acc h
    · exact .all hu hex fun c' hc' => ih (hall c' hc')
    · exact .ex hu hstep (ih hacc)

/-- A win is a budgeted win, the budget being the depth of the winning
strategy. The universal case takes the greatest budget its successors need,
which is where the finiteness of the configuration space is used. -/
theorem exists_altAcc_of_altWin [Finite A] {start : Bool} {c : Config A}
    (h : M.AltWin start c) : ∃ n, M.AltAcc start n c := by
  classical
  induction h with
  | acc h => exact ⟨0, h⟩
  | ex hu _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr (Or.inr ⟨hu, _, ‹M.Step _ _›, hn⟩)⟩
  | @all c hu hex _ ih =>
    letI := Fintype.ofFinite (Config A)
    choose f hf using ih
    refine ⟨(Finset.univ.sup fun d => if h : M.Step c d then f d h else 0) + 1,
      Or.inr (Or.inl ⟨hu, hex, fun c' hc' => ?_⟩)⟩
    refine altAcc_mono ?_ (hf c' hc')
    have hle : (if h : M.Step c c' then f c' h else 0) ≤
        Finset.univ.sup fun d => if h : M.Step c d then f d h else 0 :=
      Finset.le_sup (f := fun d => if h : M.Step c d then f d h else 0) (Finset.mem_univ c')
    rw [dif_pos hc'] at hle
    exact hle

/-- **The two presentations agree**: winning is accepting within some budget.
Over a finite configuration space the budgeted recursion of
`DescriptiveComplexity.ATMData.AltAcc` computes the least fixed point, one
stage at a time. -/
theorem altWin_iff_exists_altAcc [Finite A] {start : Bool} {c : Config A} :
    M.AltWin start c ↔ ∃ n, M.AltAcc start n c :=
  ⟨exists_altAcc_of_altWin, fun ⟨_, h⟩ => altWin_of_altAcc _ h⟩

/-! ### With no universal state the model is the nondeterministic one -/

/-- **Without a universal state, winning is reaching an accepting state.** The
alternating model is a conservative extension of the space-bounded
nondeterministic one, exactly as
`DescriptiveComplexity.ATMData.altAcc_iff_stepsIn` says of the budgeted
model. -/
theorem altWin_iff_reach {start : Bool} (hex : ∀ q : A, ¬M.IsUniv start q) (c : Config A) :
    M.AltWin start c ↔ ∃ d, Relation.ReflTransGen M.Step c d ∧ M.Acc d.state := by
  constructor
  · intro hw
    induction hw with
    | @acc d ha => exact ⟨d, Relation.ReflTransGen.refl, ha⟩
    | @ex d d' _ hstep _ ih =>
      obtain ⟨e, hreach, hacc⟩ := ih
      exact ⟨e, Relation.ReflTransGen.head hstep hreach, hacc⟩
    | @all d hu _ _ _ => exact absurd hu (hex d.state)
  · rintro ⟨d, hreach, hacc⟩
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact .acc hacc
    | head hstep _ ih => exact .ex (hex _) hstep ih

/-- **Acceptance in bounded space, without a universal state, is acceptance in
bounded space of the underlying machine.** -/
theorem altAcceptsSpace_true_iff_acceptsSpace (hex : ∀ q : A, ¬M.IsUniv true q) :
    M.AltAcceptsSpace true ↔ M.toTMData.AcceptsSpace := by
  constructor
  · rintro ⟨c₀, hinit, hw⟩
    obtain ⟨d, hreach, hacc⟩ := (altWin_iff_reach hex c₀).mp hw
    exact ⟨c₀, d, hinit, hreach, hacc⟩
  · rintro ⟨c₀, d, hinit, hreach, hacc⟩
    exact ⟨c₀, hinit, (altWin_iff_reach hex c₀).mpr ⟨d, hreach, hacc⟩⟩

/-! ### Two blocks are a bipartition of the states -/

variable (M)

/-- **The marks split the states in two.** This is all the block discipline an
unbounded alternation needs: no state carries a mark above `1`, and every state
carries exactly one of the two. `DescriptiveComplexity.ATMData.BlocksWellFormed`
is deliberately *not* required – its ordering clause is what bounds the number
of alternations. -/
def BlocksSplit : Prop :=
  (∀ q, ∃ j, j < 2 ∧ M.Blk j q ∧ ∀ j', M.Blk j' q → j' = j)

variable {M}

/-- **Block `1` is the universal player.** With the marks split in two, the
polarity bookkeeping of `DescriptiveComplexity.blockPol` collapses to a single
mark, so the model reads as an ordinary alternating machine with an
existential and a universal set of states. -/
theorem isUniv_true_iff_blk_one (hsplit : M.BlocksSplit) (q : A) :
    M.IsUniv true q ↔ M.Blk 1 q := by
  constructor
  · rintro ⟨j, hj, hpol⟩
    obtain ⟨i, hi2, hi, huniq⟩ := hsplit q
    have hij : j = i := huniq j hj
    have hi1 : i = 1 := by
      have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with rfl | rfl
      · rw [hij] at hpol
        exact absurd hpol (by decide)
      · rfl
    rw [← hi1]
    exact hi
  · intro h
    exact ⟨1, h, by decide⟩

/-! ### Transport along an equivalence of universes -/

section Transport

variable {B : Type} {u : B ≃ A} {N : ATMData B}

/-- **Winning transports along an equivalence of universes.** Stated as an
implication rather than an equivalence, and proved without any finiteness: the
converse comes from the agreement in the other direction, which the
isomorphism-invariance of a decision problem has anyway. -/
theorem AltAgree.altWin_mp (h : AltAgree u N M) (start : Bool) :
    ∀ {c : Config B}, N.AltWin start c → M.AltWin start (c.map u) := by
  intro c hw
  induction hw with
  | acc ha => exact .acc ((h.base.acc _).mp ha)
  | @ex d d' hu hstep _ ih =>
    exact .ex (fun hc => hu ((h.isUniv start d.state).mpr hc)) (h.base.step.mp hstep) ih
  | @all d hu hex _ ih =>
    refine .all ((h.isUniv start d.state).mp hu) ?_ ?_
    · obtain ⟨e, he⟩ := hex
      exact ⟨e.map u, h.base.step.mp he⟩
    · intro e he
      obtain ⟨e₀, rfl⟩ := Config.map_surjective u e
      exact ih e₀ (h.base.step.mpr he)

/-- **Acceptance in bounded space transports along an equivalence.** -/
theorem AltAgree.altAcceptsSpace_mp (h : AltAgree u N M) (start : Bool) :
    N.AltAcceptsSpace start → M.AltAcceptsSpace start := by
  cases start with
  | true =>
    rintro ⟨c₀, hinit, hw⟩
    exact ⟨c₀.map u, h.base.isInit.mp hinit, h.altWin_mp true hw⟩
  | false =>
    rintro ⟨⟨c, hc⟩, hf⟩
    refine ⟨⟨c.map u, h.base.isInit.mp hc⟩, fun d hd => ?_⟩
    obtain ⟨d₀, rfl⟩ := Config.map_surjective u d
    exact h.altWin_mp false (hf d₀ (h.base.isInit.mpr hd))

/-- **The two-block split transports along an equivalence.** -/
theorem AltAgree.blocksSplit_mp (h : AltAgree u N M) : N.BlocksSplit → M.BlocksSplit := by
  intro hf q
  obtain ⟨j, hjk, hj, huq⟩ := hf (u.symm q)
  refine ⟨j, hjk, ?_, fun j' hj' => huq j' ?_⟩
  · rwa [h.blk j (u.symm q), Equiv.apply_symm_apply] at hj
  · rw [h.blk j' (u.symm q), Equiv.apply_symm_apply]
    exact hj'

variable [Finite A]

/-- Winning transports along an equivalence, as an equivalence. -/
theorem AltAgree.altWin (h : AltAgree u N M) (start : Bool) (c : Config B) :
    N.AltWin start c ↔ M.AltWin start (c.map u) := by
  haveI : Finite B := Finite.of_equiv A u.symm
  rw [altWin_iff_exists_altAcc, altWin_iff_exists_altAcc]
  exact exists_congr fun n => h.altAcc start n c

end Transport

end ATMData

end DescriptiveComplexity
