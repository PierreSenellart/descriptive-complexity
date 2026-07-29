/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.MachinesAlt

/-!
# One block at a time: collapsing the moves of a player into a single play

The mathematical content of the machine bridge for the polynomial hierarchy.
`DescriptiveComplexity.ATMData.AltAcc` recurses one *step* at a time, handing
each move to the owner of the current state's block; a `Σₖ` definition, and the
`k`-round game it describes, hands each player *all* of its moves at once. That
the two agree is the content of this file, and it is where the alternation
bound is spent: because a transition never decreases the block index and never
raises it by more than one
(`DescriptiveComplexity.ATMData.BlocksWellFormed`), the times at which a given
player moves form one contiguous stretch of the run – a **play of the block** –
and the whole stretch may be committed in a single quantifier.

## The two collapses

A play of block `i` from `c` (`DescriptiveComplexity.ATMData.BlockPlay`) is a
sequence of genuine steps whose configurations are, up to the last one, in
block `i` and not accepting: it stops exactly when the machine accepts or hands
over to block `i + 1`.

* **Existential** (`DescriptiveComplexity.ATMData.altAcc_iff_exists_play`): a
  configuration of an existential block accepts exactly when *some* play of the
  block ends accepting, or hands a configuration over to block `i + 1` which
  itself accepts with the remaining budget.
* **Universal** (`DescriptiveComplexity.ATMData.altAcc_iff_forall_play`): a
  configuration of a universal block accepts exactly when *every* play of the
  block is all right – it hands over only accepting configurations, and it can
  never stall inside the block, neither by getting stuck nor by exhausting the
  budget. The second clause is the “a stuck universal state rejects” convention
  of `DescriptiveComplexity.MachinesAlt` in the form the proofs use.

Both statements are equivalences, and both are proved by induction on the
budget with the *play* generalized, so no strategy tree is ever built.
-/

namespace DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : ATMData A} {k : ℕ}

/-! ### Reading the block structure -/

/-- **A state has only one block.** -/
theorem blk_unique (hbwf : M.BlocksWellFormed k) {q : A} {j j' : ℕ}
    (h : M.Blk j q) (h' : M.Blk j' q) : j = j' := by
  obtain ⟨j₀, -, -, huniq⟩ := hbwf.1 q
  exact (huniq j h).trans (huniq j' h').symm

/-- A state of an existential block belongs to the existential player. -/
theorem not_isUniv_of_blk (hbwf : M.BlocksWellFormed k) {start : Bool} {i : ℕ} {q : A}
    (h : M.Blk i q) (hpol : blockPol start i = true) : ¬M.IsUniv start q := by
  rintro ⟨j, hj, hpolj⟩
  rw [blk_unique hbwf hj h] at hpolj
  rw [hpol] at hpolj
  exact Bool.noConfusion hpolj

/-- A state of a universal block belongs to the universal player. -/
theorem isUniv_of_blk {start : Bool} {i : ℕ} {q : A} (h : M.Blk i q)
    (hpol : blockPol start i = false) : M.IsUniv start q :=
  ⟨i, h, hpol⟩

/-- **A step stays in its block or moves to the next one**: the alternation
bound, read on a single step. -/
theorem blk_step (hbwf : M.BlocksWellFormed k) {i : ℕ} {c d : Config A}
    (hstep : M.Step c d) (hi : M.Blk i c.state) :
    M.Blk i d.state ∨ M.Blk (i + 1) d.state := by
  obtain ⟨τ, hτ, hsrc, -, hdst, -, -, -⟩ := hstep
  obtain ⟨j, -, hj, -⟩ := hbwf.1 d.state
  obtain ⟨hle, hlt⟩ := hbwf.2.1 τ c.state d.state i j hτ hsrc hdst hi hj
  rcases Nat.lt_or_ge i j with h | h
  · exact Or.inr (by rwa [show i + 1 = j by omega])
  · exact Or.inl (by rwa [show i = j by omega])

/-! ### Plays of a block -/

variable (M) in
/-- **A play of block `i` from `c`**: `ℓ` genuine steps, whose configurations
before the last one are in block `i` and not accepting. A play therefore stops
as soon as the machine accepts or hands over to the next block, and its last
configuration is the one the next round of the game starts from. -/
def BlockPlay (i : ℕ) (c : Config A) (ℓ : ℕ) (f : ℕ → Config A) : Prop :=
  f 0 = c ∧ (∀ j, j < ℓ → M.Step (f j) (f (j + 1))) ∧
    ∀ j, j < ℓ → M.Blk i (f j).state ∧ ¬M.Acc (f j).state

variable (M) in
/-- **A play of an existential block ends well**: accepting, or handing an
accepting configuration over to block `i + 1`. -/
def PlayEnds (start : Bool) (i n ℓ : ℕ) (f : ℕ → Config A) : Prop :=
  M.Acc (f ℓ).state ∨ (M.Blk (i + 1) (f ℓ).state ∧ M.AltAcc start (n - ℓ) (f ℓ))

variable (M) in
/-- **A play of a universal block is all right**: what it hands over to block
`i + 1` accepts, and if it is still inside the block without having accepted
then it can – and must – go on, so the universal player can neither get stuck
nor run the budget out inside the block. -/
def UnivPlayOk (start : Bool) (i n ℓ : ℕ) (f : ℕ → Config A) : Prop :=
  (M.Blk (i + 1) (f ℓ).state → M.AltAcc start (n - ℓ) (f ℓ)) ∧
    (M.Blk i (f ℓ).state → M.Acc (f ℓ).state ∨ (ℓ < n ∧ ∃ d, M.Step (f ℓ) d))

/-! ### Prepending and shifting a play -/

/-- The play `f` with `c` prepended. -/
def consPlay (c : Config A) (f : ℕ → Config A) : ℕ → Config A
  | 0 => c
  | j + 1 => f j

@[simp] theorem consPlay_zero (c : Config A) (f : ℕ → Config A) : consPlay c f 0 = c := rfl

@[simp] theorem consPlay_succ (c : Config A) (f : ℕ → Config A) (j : ℕ) :
    consPlay c f (j + 1) = f j := rfl

/-- Prepending a step to a play of the same block. -/
theorem BlockPlay.cons {i : ℕ} {c d : Config A} {ℓ : ℕ} {f : ℕ → Config A}
    (h : M.BlockPlay i d ℓ f) (hstep : M.Step c d) (hblk : M.Blk i c.state)
    (hacc : ¬M.Acc c.state) : M.BlockPlay i c (ℓ + 1) (consPlay c f) := by
  obtain ⟨hf0, hfs, hfb⟩ := h
  refine ⟨rfl, fun j hj => ?_, fun j hj => ?_⟩
  · cases j with
    | zero => simpa [hf0] using hstep
    | succ j => exact hfs j (by omega)
  · cases j with
    | zero => exact ⟨hblk, hacc⟩
    | succ j => exact hfb j (by omega)

/-- The play `f` with its first configuration dropped. -/
theorem BlockPlay.tail {i : ℕ} {c : Config A} {ℓ : ℕ} {f : ℕ → Config A}
    (h : M.BlockPlay i c (ℓ + 1) f) : M.BlockPlay i (f 1) ℓ (fun j => f (j + 1)) :=
  ⟨rfl, fun j hj => h.2.1 (j + 1) (by omega), fun j hj => h.2.2 (j + 1) (by omega)⟩

/-! ### Running an existential play -/

/-- **A run of moves that all belong to the existential player accepts as soon
as its end does.** This is the “easy” half of both collapses: the budget is
spent one step at a time, and each step is a legitimate existential choice. -/
theorem altAcc_of_steps {start : Bool} :
    ∀ (ℓ n : ℕ) (f : ℕ → Config A), ℓ ≤ n →
      (∀ j, j < ℓ → M.Step (f j) (f (j + 1))) →
      (∀ j, j < ℓ → ¬M.IsUniv start (f j).state) →
      M.AltAcc start (n - ℓ) (f ℓ) → M.AltAcc start n (f 0) := by
  intro ℓ
  induction ℓ with
  | zero => intro n f _ _ _ h; simpa using h
  | succ ℓ ih =>
    intro n f hℓn hstep hex h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hrec : M.AltAcc start m (f 1) := by
      refine ih m (fun j => f (j + 1)) (by omega) (fun j hj => hstep (j + 1) (by omega))
        (fun j hj => hex (j + 1) (by omega)) ?_
      simpa [Nat.succ_sub_succ] using h
    exact Or.inr (Or.inr ⟨hex 0 (by omega), f 1, hstep 0 (by omega), hrec⟩)

/-! ### The existential collapse -/

/-- **The moves of an existential block collapse into one play.** -/
theorem altAcc_iff_exists_play (hbwf : M.BlocksWellFormed k) {start : Bool} {i : ℕ}
    {c : Config A} (hpol : blockPol start i = true) (hi : M.Blk i c.state) (n : ℕ) :
    M.AltAcc start n c ↔
      ∃ ℓ, ℓ ≤ n ∧ ∃ f, M.BlockPlay i c ℓ f ∧ M.PlayEnds start i n ℓ f := by
  constructor
  · induction n generalizing c with
    | zero =>
      intro h
      exact ⟨0, Nat.le_refl 0, fun _ => c, ⟨rfl, fun j hj => absurd hj (by omega),
        fun j hj => absurd hj (by omega)⟩, Or.inl h⟩
    | succ n ih =>
      intro h
      by_cases hacc : M.Acc c.state
      · exact ⟨0, Nat.zero_le _, fun _ => c, ⟨rfl, fun j hj => absurd hj (by omega),
          fun j hj => absurd hj (by omega)⟩, Or.inl hacc⟩
      rcases h with h | ⟨hu, -, -⟩ | ⟨-, d, hstep, hd⟩
      · exact absurd h hacc
      · exact absurd hu (not_isUniv_of_blk hbwf hi hpol)
      · rcases blk_step hbwf hstep hi with hdi | hdi
        · by_cases hdacc : M.Acc d.state
          · refine ⟨1, by omega, consPlay c (fun _ => d), ?_, Or.inl hdacc⟩
            exact BlockPlay.cons ⟨rfl, fun j hj => absurd hj (by omega),
              fun j hj => absurd hj (by omega)⟩ hstep hi hacc
          · obtain ⟨ℓ, hℓ, f, hplay, hends⟩ := ih hdi hd
            refine ⟨ℓ + 1, by omega, consPlay c f, hplay.cons hstep hi hacc, ?_⟩
            simpa [PlayEnds, consPlay, Nat.succ_sub_succ] using hends
        · refine ⟨1, by omega, consPlay c (fun _ => d), ?_, Or.inr ⟨hdi, ?_⟩⟩
          · exact BlockPlay.cons ⟨rfl, fun j hj => absurd hj (by omega),
              fun j hj => absurd hj (by omega)⟩ hstep hi hacc
          · simpa using hd
  · rintro ⟨ℓ, hℓ, f, hplay, hends⟩
    have hend : M.AltAcc start (n - ℓ) (f ℓ) := by
      rcases hends with h | ⟨-, h⟩
      · exact altAcc_of_acc h
      · exact h
    have := altAcc_of_steps ℓ n f hℓ hplay.2.1
      (fun j hj => not_isUniv_of_blk hbwf (hplay.2.2 j hj).1 hpol) hend
    rwa [hplay.1] at this

/-! ### The universal collapse -/

/-- Every play of a universal block starting from an accepting configuration
is all right, whatever the budget: the block is left at once. -/
private theorem univPlayOk_of_altAcc {start : Bool} {i : ℕ}
    (hpol : blockPol start i = false) :
    ∀ (ℓ n : ℕ) (c : Config A) (f : ℕ → Config A), ℓ ≤ n → M.AltAcc start n c →
      M.BlockPlay i c ℓ f → M.UnivPlayOk start i n ℓ f := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro n c f _ hacc hplay
    obtain ⟨hf0, -, -⟩ := hplay
    subst hf0
    refine ⟨fun _ => by simpa using hacc, fun hblk => ?_⟩
    by_cases hac : M.Acc (f 0).state
    · exact Or.inl hac
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      cases n with
      | zero => exact absurd hacc hac
      | succ m => exact ⟨m, rfl⟩
    rcases hacc with h | ⟨-, hex, -⟩ | ⟨hu, -⟩
    · exact absurd h hac
    · exact Or.inr ⟨by omega, hex⟩
    · exact absurd (isUniv_of_blk hblk hpol) hu
  | succ ℓ ih =>
    intro n c f hℓn hacc hplay
    obtain ⟨hblk0, hnacc0⟩ := hplay.2.2 0 (by omega)
    have hstep0 : M.Step (f 0) (f 1) := hplay.2.1 0 (by omega)
    rw [hplay.1] at hblk0 hnacc0
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      cases n with
      | zero => exact absurd (show M.Acc c.state from hacc) hnacc0
      | succ m => exact ⟨m, rfl⟩
    have hall : ∀ d, M.Step c d → M.AltAcc start m d := by
      rcases hacc with h | ⟨-, -, hall⟩ | ⟨hu, -⟩
      · exact absurd h hnacc0
      · exact hall
      · exact absurd (isUniv_of_blk hblk0 hpol) hu
    have hd : M.AltAcc start m (f 1) := hall (f 1) (by rwa [hplay.1] at hstep0)
    have := ih m (f 1) (fun j => f (j + 1)) (by omega) hd hplay.tail
    obtain ⟨h1, h2⟩ := this
    exact ⟨fun hb => by simpa [Nat.succ_sub_succ] using h1 hb,
      fun hb => by
        rcases h2 hb with h | ⟨hlt, hex⟩
        · exact Or.inl h
        · exact Or.inr ⟨by omega, hex⟩⟩

/-- **The moves of a universal block collapse into one play.** -/
theorem altAcc_iff_forall_play (hbwf : M.BlocksWellFormed k) {start : Bool} {i : ℕ}
    {c : Config A} (hpol : blockPol start i = false) (hi : M.Blk i c.state) (n : ℕ) :
    M.AltAcc start n c ↔
      ∀ ℓ, ℓ ≤ n → ∀ f, M.BlockPlay i c ℓ f → M.UnivPlayOk start i n ℓ f := by
  constructor
  · intro h ℓ hℓ f hplay
    exact univPlayOk_of_altAcc hpol ℓ n c f hℓ h hplay
  · induction n generalizing c with
    | zero =>
      intro h
      obtain ⟨-, h2⟩ := h 0 (Nat.le_refl 0) (fun _ => c) ⟨rfl, fun j hj => absurd hj (by omega),
        fun j hj => absurd hj (by omega)⟩
      rcases h2 hi with hac | ⟨hlt, -⟩
      · exact hac
      · exact absurd hlt (by omega)
    | succ n ih =>
      intro h
      by_cases hacc : M.Acc c.state
      · exact Or.inl hacc
      have hzero := h 0 (Nat.zero_le _) (fun _ => c) ⟨rfl, fun j hj => absurd hj (by omega),
        fun j hj => absurd hj (by omega)⟩
      obtain ⟨d, hstepd⟩ : ∃ d, M.Step c d := by
        rcases hzero.2 hi with hac | ⟨-, hex⟩
        · exact absurd hac hacc
        · exact hex
      refine Or.inr (Or.inl ⟨isUniv_of_blk hi hpol, ⟨d, hstepd⟩, fun e hstep => ?_⟩)
      rcases blk_step hbwf hstep hi with hei | hei
      · by_cases heacc : M.Acc e.state
        · exact altAcc_of_acc heacc
        refine ih hei fun ℓ hℓ f hplay => ?_
        have hcons : M.BlockPlay i c (ℓ + 1) (consPlay c f) := hplay.cons hstep hi hacc
        obtain ⟨h1, h2⟩ := h (ℓ + 1) (by omega) (consPlay c f) hcons
        refine ⟨fun hb => ?_, fun hb => ?_⟩
        · simpa [consPlay, Nat.succ_sub_succ] using h1 (by simpa [consPlay] using hb)
        · rcases h2 (by simpa [consPlay] using hb) with hac | ⟨hlt, hex⟩
          · exact Or.inl (by simpa [consPlay] using hac)
          · exact Or.inr ⟨by omega, by simpa [consPlay] using hex⟩
      · obtain ⟨h1, -⟩ := h 1 (by omega) (consPlay c (fun _ => e))
          (BlockPlay.cons ⟨rfl, fun j hj => absurd hj (by omega),
            fun j hj => absurd hj (by omega)⟩ hstep hi hacc)
        simpa [consPlay, Nat.succ_sub_succ] using h1 (by simpa [consPlay] using hei)

end ATMData

end DescriptiveComplexity
