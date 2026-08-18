/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Machines

/-!
# Alternating Turing machines over a universe, without a vocabulary

The semantics half of the machine bridge for the polynomial hierarchy: what it
means for an *alternating* Turing machine, presented as relations on a
universe, to accept. As in `DescriptiveComplexity.Machines` no vocabulary
appears, so the reductions – which build machines rather than read them – can
reason about acceptance without unfolding any `RelMap`.

## The model

`DescriptiveComplexity.ATMData` is `DescriptiveComplexity.TMData` together with
one further family of marks, `Blk j q`: the state `q` belongs to the `j`-th
quantifier block. Two conventions fix the game the marks describe.

* **Which player owns a state.** Block `j` is existential when
  `DescriptiveComplexity.blockPol start j` is `true`, that is, when `j` is even
  and `start` is `true` or `j` is odd and `start` is `false`: the polarities
  alternate outwards-in from `start`, exactly as
  `DescriptiveComplexity.altQuant` alternates the quantifiers of a quantified
  Boolean formula. A state marked by a block of the other polarity is
  *universal* (`DescriptiveComplexity.ATMData.IsUniv`).
* **Blocks mark states, not times.** A variant marking the *time* – the phases
  of the run scheduled in advance – makes the round structure independent of
  the run, and is rejected for exactly that: it clocks the alternation, which
  is half of what the model is supposed to say.
* **A stuck universal state rejects.** A universal configuration accepts when
  every successor accepts *and there is one*
  (`DescriptiveComplexity.ATMData.AltAcc`). The other convention – vacuous
  universal quantification, so that a stuck universal configuration accepts –
  is equally standard, and this one is chosen because it makes “the machine
  stops without accepting” mean *reject* in every block, which is what a
  reduction needs: a checking phase that fails may then simply run out of
  transitions, whatever the polarity of the block it runs in.

With one block the model is the nondeterministic one: `AltAcc start n c`
unfolds to “some run of at most `n` steps from `c` reaches an accepting
state”, so `DescriptiveComplexity.ATMData.AltAccepts` at `k = 1` is
`DescriptiveComplexity.TMData.Accepts`.

## The alternation bound

Nothing above bounds the number of alternations; the bound is
`DescriptiveComplexity.ATMData.BlocksWellFormed`, folded into the yes-instances
of the decision problem exactly as linearity of the order is: every state
carries exactly one of the `k` marks, a transition raises the block index by
`0` or `1`, and a start state is in block `0`. All three are first-order for a
fixed `k` – the second because it is a condition on a single transition, which
is what makes “at most `k - 1` alternations” checkable by the kernel of a `Σₖ`
definition rather than by an inspection of runs. The last two together make a
run pass through the blocks in succession, starting at the first, which is what
lets it be read as `k` rounds of a game with the right player in each.

## Transport

`DescriptiveComplexity.ATMData.AltAgree` records that two alternating machines
over different universes correspond along an equivalence, and the lemmas below
transport acceptance along it – all the isomorphism-invariance proof of the
decision problem needs.
-/

namespace DescriptiveComplexity

/-- An alternating Turing machine presented as relations on a universe: a
machine in the sense of `DescriptiveComplexity.TMData`, together with marks
splitting its states into quantifier blocks. -/
structure ATMData (A : Type) extends TMData A where
  /-- `Blk j q`: the state `q` belongs to the `j`-th quantifier block. -/
  Blk : ℕ → A → Prop

/-- The polarity of the `j`-th quantifier block of a prefix starting with
polarity `start`: `true` for an existential block, `false` for a universal one.
The polarities alternate, so the parity of `j` decides. -/
def blockPol (start : Bool) (j : ℕ) : Bool :=
  if j % 2 = 0 then start else !start

@[simp]
theorem blockPol_zero (start : Bool) : blockPol start 0 = start := rfl

/-- The polarities of consecutive blocks are opposite. -/
theorem blockPol_succ (start : Bool) (j : ℕ) : blockPol start (j + 1) = !blockPol start j := by
  unfold blockPol
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have h1 : (j + 1) % 2 = 1 := by omega
    rw [h, h1]
    simp
  · have h1 : (j + 1) % 2 = 0 := by omega
    rw [h, h1]
    simp

/-- **Quantification with a polarity, guarded.** Existentially, the guard is
conjoined; universally it is assumed – and, in the same breath, required to be
satisfiable by *something*. That extra clause is the “a stuck universal state
rejects” convention of the module docstring, at the level of quantifiers: a
universal player with no legal move loses rather than winning vacuously. -/
def guardQ (pol : Bool) {α : Type} (C P : α → Prop) : Prop :=
  match pol with
  | true => ∃ a, C a ∧ P a
  | false => (∃ a, C a) ∧ ∀ a, C a → P a

theorem guardQ_true {α : Type} (C P : α → Prop) :
    guardQ true C P ↔ ∃ a, C a ∧ P a := Iff.rfl

theorem guardQ_false {α : Type} (C P : α → Prop) :
    guardQ false C P ↔ (∃ a, C a) ∧ ∀ a, C a → P a := Iff.rfl

/-- Guarded quantification only depends on its two predicates up to pointwise
equivalence. -/
theorem guardQ_congr (pol : Bool) {α : Type} {C C' P P' : α → Prop}
    (hC : ∀ a, C a ↔ C' a) (hP : ∀ a, C a → (P a ↔ P' a)) :
    guardQ pol C P ↔ guardQ pol C' P' := by
  cases pol
  · exact and_congr (exists_congr hC)
      ⟨fun h a ha => ((hP a ((hC a).mpr ha)).mp (h a ((hC a).mpr ha))),
        fun h a ha => (hP a ha).mpr (h a ((hC a).mp ha))⟩
  · exact exists_congr fun a => ⟨fun ⟨h1, h2⟩ => ⟨(hC a).mp h1, (hP a h1).mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨(hC a).mpr h1, (hP a ((hC a).mpr h1)).mpr h2⟩⟩

namespace ATMData

variable {A : Type} (M : ATMData A)

/-! ### The players -/

/-- The state `q` belongs to a block below `i`. -/
def BlkLt (i : ℕ) (q : A) : Prop := ∃ j, j < i ∧ M.Blk j q

/-- The state `q` is *universal*: it carries the mark of a block whose
polarity is universal, so the moves out of it belong to the universal
player. -/
def IsUniv (start : Bool) (q : A) : Prop := ∃ j, M.Blk j q ∧ blockPol start j = false

/-- No step is available from the configuration `c`: the machine stops there.
Whether that is an acceptance depends only on the state, never on the block –
see the module docstring. -/
def Stuck (c : Config A) : Prop := ∀ c', ¬ M.Step c c'

/-! ### Alternating acceptance -/

/-- **Alternating acceptance within a budget.** `M.AltAcc start n c` says the
configuration `c` accepts with `n` steps to spare: an accepting state accepts
outright, an existential configuration accepts when *some* successor does, and
a universal one when it has a successor and *every* successor accepts.

The budget recurses, so the definition is a Lean-level recursion rather than a
fixed point, and `DescriptiveComplexity.ATMData.AltAccepts` cashes it in at the
number of positions – the same unary bound as
`DescriptiveComplexity.TMData.Accepts`. -/
def AltAcc (start : Bool) : ℕ → Config A → Prop
  | 0, c => M.Acc c.state
  | n + 1, c => M.Acc c.state ∨
      (M.IsUniv start c.state ∧ (∃ c', M.Step c c') ∧
        ∀ c', M.Step c c' → AltAcc start n c') ∨
      (¬ M.IsUniv start c.state ∧ ∃ c', M.Step c c' ∧ AltAcc start n c')

/-- **Alternating acceptance**: an initial configuration accepts within as many
steps as there are positions – chosen by the player of block `0`, which is what
`DescriptiveComplexity.guardQ` at the polarity `start` says.

The residual freedom in the initial configuration (a machine may have several
start states, and its input may leave cells to the blank) belongs to the same
player as the first move, since it *is* the first move; at `start = true` this
is the `∃ c₀` of `DescriptiveComplexity.TMData.Accepts`, which the problem
therefore specializes to when every state lies in an existential block. -/
def AltAccepts (start : Bool) : Prop :=
  guardQ start (fun c₀ : Config A => M.IsInit c₀)
    (fun c₀ => M.AltAcc start (Nat.card {p : A // M.Posn p} - 1) c₀)

/-- **The block structure is well formed**, in the style of
`DescriptiveComplexity.TMData.WellFormed`: every state carries exactly one of
the `k` block marks, and every transition either stays in its block or moves to
the next one. The second clause is what bounds the number of alternations by
`k - 1`, and it is a condition on a *single* transition, hence first-order.

The blocks are entered *in order* – a transition may not skip one, and the run
starts in block `0` – so that the phases of a run are the blocks in succession.
Skipping would be harmless for the number of alternations but not for the
reading of the run as `k` rounds of a game: the round of a player would no
longer be the block whose moves it makes, and a run starting above block `0`
would hand the choice of its initial configuration to the wrong player.
Padding a machine that skips is a matter of inserting one state per skipped
block. -/
def BlocksWellFormed (k : ℕ) : Prop :=
  (∀ q, ∃ j, j < k ∧ M.Blk j q ∧ ∀ j', M.Blk j' q → j' = j) ∧
    (∀ τ q q' j j', M.Tr τ → M.Src τ q → M.Dst τ q' → M.Blk j q → M.Blk j' q' →
      j ≤ j' ∧ j' ≤ j + 1) ∧
    ∀ q, M.Start q → M.Blk 0 q

/-! ### Elementary properties -/

section Basic

variable {M}

/-- Being stuck is the negation of having a successor. -/
theorem stuck_iff_not_exists_step {c : Config A} : M.Stuck c ↔ ¬∃ c', M.Step c c' := by
  simp only [Stuck, not_exists]

/-- **Spare budget is never harmful**: one more step to spare cannot turn an
accepting configuration into a rejecting one. -/
theorem altAcc_succ {start : Bool} :
    ∀ (n : ℕ) {c : Config A}, M.AltAcc start n c → M.AltAcc start (n + 1) c := by
  intro n
  induction n with
  | zero => intro c h; exact Or.inl h
  | succ n ih =>
    intro c h
    rcases h with h | ⟨hu, hex, hall⟩ | ⟨hu, c', hstep, hacc⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hu, hex, fun c' hc' => ih (hall c' hc')⟩)
    · exact Or.inr (Or.inr ⟨hu, c', hstep, ih hacc⟩)

/-- **Acceptance is monotone in the budget.** -/
theorem altAcc_mono {start : Bool} :
    ∀ {m n : ℕ}, n ≤ m → ∀ {c : Config A}, M.AltAcc start n c → M.AltAcc start m c := by
  intro m
  induction m with
  | zero =>
    intro n hn c h
    rwa [Nat.le_zero.mp hn] at h
  | succ m ih =>
    intro n hn c h
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact altAcc_succ m (ih (Nat.lt_succ_iff.mp hlt) h)
    · rwa [Nat.le_antisymm hn hge] at h

/-- An accepting state accepts, whatever the budget. -/
theorem altAcc_of_acc {start : Bool} {n : ℕ} {c : Config A} (h : M.Acc c.state) :
    M.AltAcc start n c := by
  cases n with
  | zero => exact h
  | succ n => exact Or.inl h

/-- **With no universal state the model is the nondeterministic one**: the
recursion unfolds to “some run of at most `n` steps reaches an accepting
state”. This is what makes the one-block problem the machine problem of
`DescriptiveComplexity.Machines` again, and it is why the alternating model is
a conservative extension rather than a new one. -/
theorem altAcc_iff_stepsIn {start : Bool} (hex : ∀ q : A, ¬M.IsUniv start q) :
    ∀ (n : ℕ) (c : Config A),
      M.AltAcc start n c ↔ ∃ m, m ≤ n ∧ ∃ d, M.StepsIn m c d ∧ M.Acc d.state := by
  intro n
  induction n with
  | zero =>
    intro c
    constructor
    · intro h; exact ⟨0, Nat.le_refl 0, c, rfl, h⟩
    · rintro ⟨m, hm, d, hrun, hacc⟩
      rw [Nat.le_zero.mp hm] at hrun
      exact (show c = d from hrun) ▸ hacc
  | succ n ih =>
    intro c
    constructor
    · rintro (h | ⟨hu, -, -⟩ | ⟨-, c', hstep, hacc⟩)
      · exact ⟨0, Nat.zero_le _, c, rfl, h⟩
      · exact absurd hu (hex _)
      · obtain ⟨m, hm, d, hrun, hd⟩ := (ih c').mp hacc
        exact ⟨m + 1, by omega, d, ⟨c', hstep, hrun⟩, hd⟩
    · rintro ⟨m, hm, d, hrun, hacc⟩
      cases m with
      | zero => exact Or.inl ((show c = d from hrun) ▸ hacc)
      | succ m =>
        obtain ⟨c', hstep, hrest⟩ := hrun
        exact Or.inr (Or.inr ⟨hex _, c', hstep,
          (ih c').mpr ⟨m, by omega, d, hrest, hacc⟩⟩)

/-- **The one-block model accepts exactly when the underlying machine does.**
Stated at an existential outermost polarity, where the initial configuration is
chosen existentially, as `DescriptiveComplexity.TMData.Accepts` chooses it. -/
theorem altAccepts_true_iff_accepts [Finite A] (hex : ∀ q : A, ¬M.IsUniv true q)
    (hne : ∃ p, M.Posn p) : M.AltAccepts true ↔ M.Accepts := by
  have hpos : 0 < Nat.card {p : A // M.Posn p} := by
    obtain ⟨p, hp⟩ := hne
    have : Nonempty {p : A // M.Posn p} := ⟨⟨p, hp⟩⟩
    exact Nat.card_pos
  constructor
  · rintro ⟨c₀, hinit, hacc⟩
    obtain ⟨m, hm, d, hrun, hd⟩ := (altAcc_iff_stepsIn hex _ c₀).mp hacc
    exact ⟨c₀, d, m, hinit, by omega, hrun, hd⟩
  · rintro ⟨c₀, d, m, hinit, hm, hrun, hd⟩
    exact ⟨c₀, hinit, (altAcc_iff_stepsIn hex _ c₀).mpr ⟨m, by omega, d, hrun, hd⟩⟩

end Basic

/-! ### Transport along an equivalence of universes -/

section Transport

variable {B : Type} {M}

/-- Two alternating machines over different universes **agree** along an
equivalence when their underlying machines do and their block marks
correspond. -/
structure AltAgree (u : B ≃ A) (N : ATMData B) (M : ATMData A) : Prop where
  /-- The underlying machines agree. -/
  base : TMData.Agree u N.toTMData M.toTMData
  /-- The block marks correspond. -/
  blk : ∀ j b, N.Blk j b ↔ M.Blk j (u b)

variable {u : B ≃ A} {N : ATMData B}

/-- Universality of a state transports along an equivalence. -/
theorem AltAgree.isUniv (h : AltAgree u N M) (start : Bool) (b : B) :
    N.IsUniv start b ↔ M.IsUniv start (u b) :=
  exists_congr fun j => and_congr_left' (h.blk j b)

/-- Being stuck transports along an equivalence. -/
theorem AltAgree.stuck (h : AltAgree u N M) (c : Config B) :
    N.Stuck c ↔ M.Stuck (c.map u) := by
  constructor
  · intro hs d hd
    obtain ⟨d₀, rfl⟩ := Config.map_surjective u d
    exact hs d₀ (h.base.step.mpr hd)
  · intro hs d hd
    exact hs (d.map u) (h.base.step.mp hd)

/-- **Alternating acceptance within a budget transports along an
equivalence.** -/
theorem AltAgree.altAcc (h : AltAgree u N M) (start : Bool) :
    ∀ (n : ℕ) (c : Config B), N.AltAcc start n c ↔ M.AltAcc start n (c.map u) := by
  intro n
  induction n with
  | zero => intro c; exact h.base.acc _
  | succ n ih =>
    intro c
    have hex : (∃ c' : Config B, N.Step c c') ↔ ∃ d : Config A, M.Step (c.map u) d := by
      constructor
      · rintro ⟨c', hc'⟩
        exact ⟨c'.map u, h.base.step.mp hc'⟩
      · rintro ⟨d, hd⟩
        obtain ⟨d₀, rfl⟩ := Config.map_surjective u d
        exact ⟨d₀, h.base.step.mpr hd⟩
    have hall : (∀ c' : Config B, N.Step c c' → N.AltAcc start n c') ↔
        ∀ d : Config A, M.Step (c.map u) d → M.AltAcc start n d := by
      constructor
      · intro hf d hd
        obtain ⟨d₀, rfl⟩ := Config.map_surjective u d
        exact (ih d₀).mp (hf d₀ (h.base.step.mpr hd))
      · intro hf c' hc'
        exact (ih c').mpr (hf (c'.map u) (h.base.step.mp hc'))
    have hsome : (∃ c' : Config B, N.Step c c' ∧ N.AltAcc start n c') ↔
        ∃ d : Config A, M.Step (c.map u) d ∧ M.AltAcc start n d := by
      constructor
      · rintro ⟨c', hc', hacc⟩
        exact ⟨c'.map u, h.base.step.mp hc', (ih c').mp hacc⟩
      · rintro ⟨d, hd, hacc⟩
        obtain ⟨d₀, rfl⟩ := Config.map_surjective u d
        exact ⟨d₀, h.base.step.mpr hd, (ih d₀).mpr hacc⟩
    exact or_congr (h.base.acc _)
      (or_congr (and_congr (h.isUniv start _) (and_congr hex hall))
        (and_congr (not_congr (h.isUniv start _)) hsome))

/-- **Alternating acceptance transports along an equivalence.** -/
theorem AltAgree.altAccepts (h : AltAgree u N M) (start : Bool) :
    N.AltAccepts start ↔ M.AltAccepts start := by
  have hcard : Nat.card {b : B // N.Posn b} = Nat.card {a : A // M.Posn a} :=
    Nat.card_congr (u.subtypeEquiv fun b => h.base.posn b)
  have hinitex : (∃ c : Config B, N.IsInit c) ↔ ∃ c : Config A, M.IsInit c := by
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c.map u, h.base.isInit.mp hc⟩
    · rintro ⟨c, hc⟩
      obtain ⟨d, rfl⟩ := Config.map_surjective u c
      exact ⟨d, h.base.isInit.mpr hc⟩
  cases start with
  | true =>
    constructor
    · rintro ⟨c₀, hinit, hacc⟩
      exact ⟨c₀.map u, h.base.isInit.mp hinit, hcard ▸ (h.altAcc true _ c₀).mp hacc⟩
    · rintro ⟨c₀, hinit, hacc⟩
      obtain ⟨d₀, rfl⟩ := Config.map_surjective u c₀
      exact ⟨d₀, h.base.isInit.mpr hinit, (h.altAcc true _ d₀).mpr (hcard ▸ hacc)⟩
  | false =>
    refine and_congr hinitex ⟨fun hf c hc => ?_, fun hf c hc => ?_⟩
    · obtain ⟨d, rfl⟩ := Config.map_surjective u c
      exact hcard ▸ (h.altAcc false _ d).mp (hf d (h.base.isInit.mpr hc))
    · exact (h.altAcc false _ c).mpr (hcard ▸ hf _ (h.base.isInit.mp hc))

/-- **Well-formedness of the block structure transports along an
equivalence.** -/
theorem AltAgree.blocksWellFormed (h : AltAgree u N M) (k : ℕ) :
    N.BlocksWellFormed k ↔ M.BlocksWellFormed k := by
  have huniq : (∀ q : B, ∃ j, j < k ∧ N.Blk j q ∧ ∀ j', N.Blk j' q → j' = j) ↔
      ∀ q : A, ∃ j, j < k ∧ M.Blk j q ∧ ∀ j', M.Blk j' q → j' = j := by
    constructor
    · intro hf q
      obtain ⟨j, hjk, hj, huq⟩ := hf (u.symm q)
      refine ⟨j, hjk, ?_, fun j' hj' => huq j' ?_⟩
      · rwa [h.blk j (u.symm q), Equiv.apply_symm_apply] at hj
      · rw [h.blk j' (u.symm q), Equiv.apply_symm_apply]; exact hj'
    · intro hf q
      obtain ⟨j, hjk, hj, huq⟩ := hf (u q)
      exact ⟨j, hjk, (h.blk j q).mpr hj, fun j' hj' => huq j' ((h.blk j' q).mp hj')⟩
  have hstart : (∀ q, N.Start q → N.Blk 0 q) ↔ ∀ q, M.Start q → M.Blk 0 q := by
    constructor
    · intro hf q hq
      have := hf (u.symm q) ((h.base.start _).mpr (by rwa [Equiv.apply_symm_apply]))
      rwa [h.blk 0 (u.symm q), Equiv.apply_symm_apply] at this
    · intro hf q hq
      exact (h.blk 0 q).mpr (hf (u q) ((h.base.start q).mp hq))
  have hmono : (∀ τ q q' j j', N.Tr τ → N.Src τ q → N.Dst τ q' → N.Blk j q → N.Blk j' q' →
        j ≤ j' ∧ j' ≤ j + 1) ↔
      ∀ τ q q' j j', M.Tr τ → M.Src τ q → M.Dst τ q' → M.Blk j q → M.Blk j' q' →
        j ≤ j' ∧ j' ≤ j + 1 := by
    constructor
    · intro hf τ q q' j j' hτ hsrc hdst hj hj'
      refine hf (u.symm τ) (u.symm q) (u.symm q') j j'
        ((h.base.tr _).mpr (by rwa [Equiv.apply_symm_apply]))
        ((h.base.src _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
        ((h.base.dst _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
        ?_ ?_
      · rw [h.blk j (u.symm q), Equiv.apply_symm_apply]; exact hj
      · rw [h.blk j' (u.symm q'), Equiv.apply_symm_apply]; exact hj'
    · intro hf τ q q' j j' hτ hsrc hdst hj hj'
      exact hf (u τ) (u q) (u q') j j' ((h.base.tr _).mp hτ) ((h.base.src _ _).mp hsrc)
        ((h.base.dst _ _).mp hdst) ((h.blk j q).mp hj) ((h.blk j' q').mp hj')
  exact and_congr huniq (and_congr hmono hstart)

end Transport

end ATMData

end DescriptiveComplexity
