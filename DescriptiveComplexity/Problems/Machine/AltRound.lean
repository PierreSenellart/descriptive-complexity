/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltSplice

/-!
# One round of the game, and what it leaves behind

The step of the induction that turns alternating acceptance into the `k`-round
game. Round `i` starts at the position `t`, in the configuration the previous
round handed over; whatever walk it plays describes a *play of block `i`*
(`DescriptiveComplexity.Problems.Machine.AltRank`), and
`DescriptiveComplexity.ATMData.game_iff_end` says that the rest of the game is
decided by how that play ends – which is exactly the shape
`DescriptiveComplexity.ATMData.PlayEnds` and
`DescriptiveComplexity.ATMData.UnivPlayOk` of the two collapse lemmas.

Two things end a play. Either it hands over to block `i + 1`, and then the rest
of the game is the game from round `i + 1`, by the induction hypothesis; or it
stops inside block `i`, and then – because acceptance is absorbing and a stuck
configuration cannot move – the walk stands still from there to the highest
position, every block is low, and
`DescriptiveComplexity.ATMData.gameFrom_of_blkLt` reduces the rest of the game
to whether that configuration accepts.
-/

namespace DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : ATMData A} {k : ℕ}

/-! ### Blocks along a sequence -/

omit [Finite A] in
/-- **The blocks along a play never decrease**: a play takes genuine steps, and
a step never lowers the block. -/
theorem le_blk_of_blockPlay (hbwf : M.BlocksWellFormed k) {i : ℕ} {c : Config A} {ℓ : ℕ}
    {f : ℕ → Config A} (hplay : M.BlockPlay i c ℓ f) (hc : M.Blk i c.state) :
    ∀ j, j ≤ ℓ → ∀ jj, M.Blk jj (f j).state → i ≤ jj := by
  intro j
  induction j with
  | zero =>
    intro _ jj hjj
    exact Nat.le_of_eq (blk_unique hbwf (hplay.1 ▸ hc) hjj)
  | succ j ih =>
    intro hj jj hjj
    obtain ⟨j₀, -, hj₀, -⟩ := hbwf.1 (f j).state
    refine Nat.le_trans (ih (by omega) j₀ hj₀) ?_
    rcases blk_step hbwf (hplay.2.1 j (by omega)) hj₀ with h | h
    · exact Nat.le_of_eq (blk_unique hbwf h hjj)
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j₀)
        (Nat.le_of_eq (blk_unique hbwf h hjj)))

omit [Finite A] in
/-- Both readings of the end of a play depend only on its last configuration. -/
theorem PlayEnds.congr {start : Bool} {i n ℓ : ℕ} {f g : ℕ → Config A} (h : f ℓ = g ℓ)
    (hf : M.PlayEnds start i n ℓ f) : M.PlayEnds start i n ℓ g := by
  unfold PlayEnds at hf ⊢
  rwa [← h]

omit [Finite A] in
/-- The universal reading likewise. -/
theorem UnivPlayOk.congr {start : Bool} {i n ℓ : ℕ} {f g : ℕ → Config A} (h : f ℓ = g ℓ)
    (hf : M.UnivPlayOk start i n ℓ f) : M.UnivPlayOk start i n ℓ g := by
  unfold UnivPlayOk at hf ⊢
  rwa [← h]

/-! ### Standing still -/

/-- **An absorbing configuration is never left.** Once a walk is accepting or
stuck at a position whose block it still answers for, its legality forces it to
stand still at every later position. -/
theorem constant_of_absorbing (hlin : IsLinOrd M.Le) {i : ℕ} {w : A → Config A}
    (hw : M.LegalBelow i w) {x : A} (hx : M.Posn x) (hb : M.BlkLt i (w x).state)
    (habs : M.Acc (w x).state ∨ M.Stuck (w x)) :
    ∀ y, M.Posn y → M.Le x y → w y = w x := by
  refine le_induction hlin hx (P := fun y => w y = w x) rfl ?_
  intro p q hpq _ hp
  rcases hw.2.2 p q hpq (by rw [hp]; exact hb) with ⟨hs, hnacc⟩ | ⟨heq, -⟩
  · rcases habs with hacc | hstuck
    · exact absurd (by rw [hp]; exact hacc) hnacc
    · exact absurd (by rw [← hp]; exact hs) (hstuck (w q))
  · rw [heq, hp]

/-! ### The rest of the game, read off the end of the play -/

section Round

variable (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le) {p₁ : A}
  (hmax : MaxPos M.Le M.Posn p₁)
include hbwf hlin hmax

omit hbwf in
/-- A position above `t` is the one the enumeration reaches at its rank. -/
theorem posSeq_eq_of_le {t s : A} (ht : M.Posn t) (hs : M.Posn s) (hle : M.Le t s) :
    s = M.posSeq t (bitRank M.Le M.Posn s - bitRank M.Le M.Posn t) := by
  have h1 : bitRank M.Le M.Posn t ≤ bitRank M.Le M.Posn s :=
    TMData.bitRank_le_of_le (M := M.toTMData) hlin ht hle
  have h2 : bitRank M.Le M.Posn s ≤ bitRank M.Le M.Posn p₁ :=
    TMData.bitRank_le_of_le (M := M.toTMData) hlin hs (hmax.2 s hs)
  obtain ⟨hp, hr⟩ := posSeq_spec hlin ht hmax
    (bitRank M.Le M.Posn s - bitRank M.Le M.Posn t) (by omega)
  exact bitRank_inj hlin hs hp (by omega)

/-- **What the rest of the game decides**: the game from round `i + 1` holds
exactly when the play of block `i` that round `i`'s walk describes ends well –
in either of the two readings the collapse lemmas use. -/
theorem game_iff_end (start : Bool) {i m : ℕ}
    (hIH : ∀ (v : A → Config A) (t' : A), M.LegalBelow (i + 1) v → M.Posn t' →
      M.Blk (i + 1) (v t').state →
      (∀ s, M.Posn s → M.Le s t' → s ≠ t' → M.BlkLt (i + 1) (v s).state) →
      (M.AltAcc start (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t') (v t') ↔
        M.gameFrom start (i + 1) m v))
    {t : A} (ht : M.Posn t) {w : A → Config A} (hw : M.LegalBelow (i + 1) w)
    (hwt : M.Blk i (w t).state)
    (hpastw : ∀ s, M.Posn s → M.Le s t → s ≠ t → M.BlkLt i (w s).state)
    {ℓ : ℕ} (hℓ : ℓ ≤ bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t)
    (hplay : M.BlockPlay i (w t) ℓ (fun j => w (M.posSeq t j)))
    (hstop : ℓ = bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t ∨
      ¬M.Blk i (w (M.posSeq t ℓ)).state ∨ M.Acc (w (M.posSeq t ℓ)).state ∨
      M.Stuck (w (M.posSeq t ℓ))) :
    (M.gameFrom start (i + 1) m w ↔
        M.PlayEnds start i (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t) ℓ
          (fun j => w (M.posSeq t j))) ∧
      (M.gameFrom start (i + 1) m w ↔
        M.UnivPlayOk start i (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t) ℓ
          (fun j => w (M.posSeq t j))) := by
  obtain ⟨ht', hr'⟩ := posSeq_spec hlin ht hmax ℓ hℓ
  set t' := M.posSeq t ℓ with hts
  have hrt : bitRank M.Le M.Posn t ≤ bitRank M.Le M.Posn p₁ :=
    TMData.bitRank_le_of_le (M := M.toTMData) hlin ht (hmax.2 t ht)
  have hbud : bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t' =
      (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t) - ℓ := by omega
  -- the handover configuration is in block `i` or `i + 1`
  have hblk' : M.Blk i (w t').state ∨ M.Blk (i + 1) (w t').state := by
    cases ℓ with
    | zero => exact Or.inl (by rw [hts]; exact hwt)
    | succ ℓ₀ =>
      exact blk_step hbwf (hplay.2.1 ℓ₀ (Nat.lt_succ_self ℓ₀))
        (hplay.2.2 ℓ₀ (Nat.lt_succ_self ℓ₀)).1
  -- everything strictly below the handover is in a block below `i + 1`
  have hpast' : ∀ s, M.Posn s → M.Le s t' → s ≠ t' → M.BlkLt (i + 1) (w s).state := by
    intro s hs hle hne
    have hsr : bitRank M.Le M.Posn s ≤ bitRank M.Le M.Posn t' :=
      TMData.bitRank_le_of_le (M := M.toTMData) hlin hs hle
    have hslt : bitRank M.Le M.Posn s < bitRank M.Le M.Posn t' :=
      Nat.lt_of_le_of_ne hsr fun hcon => hne (bitRank_inj hlin hs ht' hcon)
    rcases Nat.lt_trichotomy (bitRank M.Le M.Posn s) (bitRank M.Le M.Posn t) with h | h | h
    · obtain ⟨j, hj, hjb⟩ := hpastw s hs (le_of_bitRank_le hlin hs ht (by omega))
        (fun hcon => by rw [hcon] at h; exact absurd h (Nat.lt_irrefl _))
      exact ⟨j, by omega, hjb⟩
    · obtain rfl : s = t := bitRank_inj hlin hs ht h
      exact ⟨i, Nat.lt_succ_self i, hwt⟩
    · have hjlt : bitRank M.Le M.Posn s - bitRank M.Le M.Posn t < ℓ := by omega
      have : s = M.posSeq t (bitRank M.Le M.Posn s - bitRank M.Le M.Posn t) :=
        posSeq_eq_of_le hlin hmax ht hs (le_of_bitRank_le hlin ht hs (by omega))
      rw [this]
      exact ⟨i, Nat.lt_succ_self i, (hplay.2.2 _ hjlt).1⟩
  rcases hblk' with hb | hb
  · -- the play stopped inside its own block: the walk stands still to the end
    have hnotb : ¬M.Blk (i + 1) (w t').state := fun hcon => by
      have := blk_unique hbwf hb hcon
      omega
    have hconst : ∀ y, M.Posn y → M.Le t' y → w y = w t' := by
      rcases hstop with hs | hs | hs | hs
      · -- the play used the whole budget, so `t'` is the highest position
        have ht'p₁ : t' = p₁ := by rw [hts, hs]; exact posSeq_budget hlin ht hmax
        intro y hy hle
        have hyt : y = t' := hlin.2.2.1 y t' (by rw [ht'p₁]; exact hmax.2 y hy) hle
        rw [hyt]
      · exact absurd hb hs
      · exact constant_of_absorbing hlin hw ht' ⟨i, Nat.lt_succ_self i, hb⟩ (Or.inl hs)
      · exact constant_of_absorbing hlin hw ht' ⟨i, Nat.lt_succ_self i, hb⟩ (Or.inr hs)
    have hall : ∀ s, M.Posn s → M.BlkLt (i + 1) (w s).state := by
      intro s hs
      rcases hlin.2.2.2 s t' with hle | hle
      · rcases eq_or_ne s t' with rfl | hne
        · exact ⟨i, Nat.lt_succ_self i, hb⟩
        · exact hpast' s hs hle hne
      · rw [hconst s hs hle]
        exact ⟨i, Nat.lt_succ_self i, hb⟩
    have hgame : M.gameFrom start (i + 1) m w ↔ M.AccAt w :=
      gameFrom_of_blkLt start m (i + 1) w hw hall
    have hp₁ : w p₁ = w t' := hconst p₁ hmax.1 (hmax.2 t' ht')
    have hacc : M.AccAt w ↔ M.Acc (w t').state := by
      constructor
      · intro h
        rw [← hp₁]
        exact h p₁ hmax
      · intro h p hp
        rw [hconst p hp.1 (hp.2 t' ht')]
        exact h
    refine ⟨hgame.trans (hacc.trans ⟨fun h => Or.inl h, fun h => ?_⟩),
      hgame.trans (hacc.trans ⟨fun h => ⟨fun hcon => absurd hcon hnotb, fun _ => Or.inl h⟩,
        fun h => ?_⟩)⟩
    · rcases h with h | ⟨hcon, -⟩
      · exact h
      · exact absurd hcon hnotb
    · rcases h.2 hb with hcc | ⟨hlt, d, hd⟩
      · exact hcc
      · rcases hstop with hs | hs | hs | hs
        · omega
        · exact absurd hb hs
        · exact hs
        · exact absurd hd (hs d)
  · -- the play handed over: the induction hypothesis takes over
    have hnotb : ¬M.Blk i (w t').state := fun hcon => by
      have := blk_unique hbwf hcon hb
      omega
    have hrec : M.AltAcc start
        ((bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t) - ℓ) (w t') ↔
        M.gameFrom start (i + 1) m w := by
      rw [← hbud]
      exact hIH w t' hw ht' hb hpast'
    refine ⟨hrec.symm.trans ⟨fun h => Or.inr ⟨hb, h⟩, fun h => ?_⟩,
      hrec.symm.trans ⟨fun h => ⟨fun _ => h, fun hcon => absurd hcon hnotb⟩,
        fun h => h.1 hb⟩⟩
    rcases h with h | ⟨-, h⟩
    · exact altAcc_of_acc h
    · exact h

/-! ### One round, against an abstract admissibility condition

Both the induction step and its base – the first round, which has nothing to
inherit – are this one lemma, differing only in what makes a walk admissible.
`C` is that condition; the four hypotheses say it forces a walk to be legal
below `i + 1`, to start the round at `c`, to keep the past in low blocks, and
to be met by the walk `DescriptiveComplexity.ATMData.splice` builds out of any
play that ends the way a round may end. -/

/-- **One round of the game.** -/
theorem altAcc_iff_guardQ (start : Bool) {i m : ℕ}
    (hIH : ∀ (v : A → Config A) (t' : A), M.LegalBelow (i + 1) v → M.Posn t' →
      M.Blk (i + 1) (v t').state →
      (∀ s, M.Posn s → M.Le s t' → s ≠ t' → M.BlkLt (i + 1) (v s).state) →
      (M.AltAcc start (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t') (v t') ↔
        M.gameFrom start (i + 1) m v))
    {t : A} (ht : M.Posn t) {c : Config A} (hc : M.Blk i c.state)
    {C : (A → Config A) → Prop}
    (hC1 : ∀ w, C w → M.LegalBelow (i + 1) w)
    (hC2 : ∀ w, C w → w t = c)
    (hC3 : ∀ w, C w → ∀ s, M.Posn s → M.Le s t → s ≠ t → M.BlkLt i (w s).state)
    (hC4 : ∀ ℓ f, ℓ ≤ bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t →
      M.BlockPlay i c ℓ f →
      (ℓ < bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t →
        M.BlkLt (i + 1) (f ℓ).state → M.Acc (f ℓ).state ∨ M.Stuck (f ℓ)) →
      ∃ w, C w ∧ ∀ j, j ≤ ℓ → w (M.posSeq t j) = f j) :
    (M.AltAcc start (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t) c ↔
      guardQ (blockPol start i) C fun w => M.gameFrom start (i + 1) m w) := by
  classical
  set B := bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t with hB
  -- what an admissible walk decides, given a play of the block it describes
  have hat : ∀ w, C w → ∀ ℓ, ℓ ≤ B → M.BlockPlay i c ℓ (fun j => w (M.posSeq t j)) →
      (ℓ = B ∨ ¬M.Blk i (w (M.posSeq t ℓ)).state ∨ M.Acc (w (M.posSeq t ℓ)).state ∨
        M.Stuck (w (M.posSeq t ℓ))) →
      ((M.gameFrom start (i + 1) m w ↔ M.PlayEnds start i B ℓ (fun j => w (M.posSeq t j))) ∧
        (M.gameFrom start (i + 1) m w ↔
          M.UnivPlayOk start i B ℓ (fun j => w (M.posSeq t j)))) := by
    intro w hw ℓ hℓ hplay hstop
    have hwt : M.Blk i (w t).state := by rw [hC2 w hw]; exact hc
    have hplay' : M.BlockPlay i (w t) ℓ (fun j => w (M.posSeq t j)) := by
      rw [hC2 w hw]; exact hplay
    exact game_iff_end hbwf hlin hmax start hIH ht (hC1 w hw) hwt (hC3 w hw) hℓ hplay' hstop
  -- every admissible walk describes such a play
  have hread : ∀ w, C w → ∃ ℓ, ℓ ≤ B ∧ M.BlockPlay i c ℓ (fun j => w (M.posSeq t j)) ∧
      (ℓ = B ∨ ¬M.Blk i (w (M.posSeq t ℓ)).state ∨ M.Acc (w (M.posSeq t ℓ)).state ∨
        M.Stuck (w (M.posSeq t ℓ))) := by
    intro w hw
    obtain ⟨ℓ, hℓ, hplay, hstop⟩ := exists_play_of_legalBelow hlin (hC1 w hw) ht hmax (i := i)
    exact ⟨ℓ, hℓ, by rwa [hC2 w hw] at hplay, hstop⟩
  by_cases hpol : blockPol start i = true
  · rw [hpol, guardQ_true, altAcc_iff_exists_play hbwf hpol hc B]
    constructor
    · rintro ⟨ℓ, hℓ, f, hplay, hends⟩
      have hend : ℓ < B → M.BlkLt (i + 1) (f ℓ).state → M.Acc (f ℓ).state ∨ M.Stuck (f ℓ) := by
        intro _ hbl
        rcases hends with h | ⟨hb, -⟩
        · exact Or.inl h
        · exact absurd ((blkLt_iff hbwf hb).mp hbl) (by omega)
      obtain ⟨w, hCw, hagree⟩ := hC4 ℓ f hℓ hplay hend
      have hplayw : M.BlockPlay i c ℓ (fun j => w (M.posSeq t j)) :=
        BlockPlay.congr (fun j hj => (hagree j hj).symm) hplay
      have hstopw : ℓ = B ∨ ¬M.Blk i (w (M.posSeq t ℓ)).state ∨
          M.Acc (w (M.posSeq t ℓ)).state ∨ M.Stuck (w (M.posSeq t ℓ)) := by
        rw [hagree ℓ (Nat.le_refl ℓ)]
        rcases hends with h | ⟨hb, -⟩
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl fun hcon => absurd (blk_unique hbwf hcon hb) (by omega))
      exact ⟨w, hCw, ((hat w hCw ℓ hℓ hplayw hstopw).1).mpr
        (PlayEnds.congr (hagree ℓ (Nat.le_refl ℓ)).symm hends)⟩
    · rintro ⟨w, hCw, hg⟩
      obtain ⟨ℓ, hℓ, hplay, hstop⟩ := hread w hCw
      exact ⟨ℓ, hℓ, _, hplay, ((hat w hCw ℓ hℓ hplay hstop).1).mp hg⟩
  · have hfalse : blockPol start i = false := by
      cases h : blockPol start i
      · rfl
      · exact absurd h hpol
    rw [hfalse, guardQ_false, altAcc_iff_forall_play hbwf hfalse hc B]
    constructor
    · intro hall
      refine ⟨?_, fun w hCw => ?_⟩
      · -- the greedy continuation of `c` is a play, hence an admissible walk exists
        obtain ⟨ℓ, hℓ, hplay, hstop⟩ :=
          exists_play_of_seq (M := M) (i := i) (c := c) (g := M.greedy c) B rfl
            fun j _ _ hacc hstuck => by
              rcases greedy_step M c j with h | h
              · exact h.1
              · exact absurd h.2 (by rintro (h' | h') <;> [exact hacc h'; exact hstuck h'])
        have hend : ℓ < B → M.BlkLt (i + 1) (M.greedy c ℓ).state →
            M.Acc (M.greedy c ℓ).state ∨ M.Stuck (M.greedy c ℓ) := by
          intro hlt hbl
          rcases hstop with h | h | h | h
          · exact absurd h (by omega)
          · refine absurd ?_ h
            obtain ⟨jj, -, hjj, -⟩ := hbwf.1 (M.greedy c ℓ).state
            have h1 : jj < i + 1 := (blkLt_iff hbwf hjj).mp hbl
            have h2 : i ≤ jj := le_blk_of_blockPlay hbwf hplay hc ℓ (Nat.le_refl ℓ) jj hjj
            obtain rfl : jj = i := by omega
            exact hjj
          · exact Or.inl h
          · exact Or.inr h
        obtain ⟨w, hCw, -⟩ := hC4 ℓ (M.greedy c) hℓ hplay hend
        exact ⟨w, hCw⟩
      · obtain ⟨ℓ, hℓ, hplay, hstop⟩ := hread w hCw
        exact ((hat w hCw ℓ hℓ hplay hstop).2).mpr (hall ℓ hℓ _ hplay)
    · rintro ⟨-, hall⟩ ℓ hℓ f hplay
      by_cases hbad : ℓ < B ∧ M.Blk i (f ℓ).state ∧ ¬M.Acc (f ℓ).state ∧ ¬M.Stuck (f ℓ)
      · obtain ⟨hlt, hb, hnacc, hnst⟩ := hbad
        refine ⟨fun hcon => absurd (blk_unique hbwf hb hcon) (by omega),
          fun _ => Or.inr ⟨hlt, ?_⟩⟩
        by_contra hcon
        exact hnst fun d hd => hcon ⟨d, hd⟩
      · have hblow : ∀ jj, M.Blk jj (f ℓ).state → i ≤ jj :=
          le_blk_of_blockPlay hbwf hplay hc ℓ (Nat.le_refl ℓ)
        have hend : ℓ < B → M.BlkLt (i + 1) (f ℓ).state →
            M.Acc (f ℓ).state ∨ M.Stuck (f ℓ) := by
          intro hlt hbl
          obtain ⟨jj, -, hjj, -⟩ := hbwf.1 (f ℓ).state
          have h1 : jj < i + 1 := (blkLt_iff hbwf hjj).mp hbl
          have h2 : i ≤ jj := hblow jj hjj
          obtain rfl : jj = i := by omega
          by_contra hcon
          exact hbad ⟨hlt, hjj, fun h => hcon (Or.inl h), fun h => hcon (Or.inr h)⟩
        obtain ⟨w, hCw, hagree⟩ := hC4 ℓ f hℓ hplay hend
        have hplayw : M.BlockPlay i c ℓ (fun j => w (M.posSeq t j)) :=
          BlockPlay.congr (fun j hj => (hagree j hj).symm) hplay
        have hstopw : ℓ = B ∨ ¬M.Blk i (w (M.posSeq t ℓ)).state ∨
            M.Acc (w (M.posSeq t ℓ)).state ∨ M.Stuck (w (M.posSeq t ℓ)) := by
          rw [hagree ℓ (Nat.le_refl ℓ)]
          by_cases h1 : ℓ = B
          · exact Or.inl h1
          by_cases h2 : M.Blk i (f ℓ).state
          · by_cases h3 : M.Acc (f ℓ).state
            · exact Or.inr (Or.inr (Or.inl h3))
            · refine Or.inr (Or.inr (Or.inr ?_))
              by_contra h4
              exact hbad ⟨by omega, h2, h3, h4⟩
          · exact Or.inr (Or.inl h2)
        exact UnivPlayOk.congr (hagree ℓ (Nat.le_refl ℓ))
          (((hat w hCw ℓ hℓ hplayw hstopw).2).mp (hall w hCw))

/-! ### The induction over the rounds -/

/-- **The game from round `i` on decides acceptance at the entry into block
`i`.** The induction is on the number of rounds left; the base case is vacuous
because a state of block `k` does not exist, and the step is
`DescriptiveComplexity.ATMData.altAcc_iff_guardQ` with the agreement condition
of the round as its admissibility. -/
theorem gameFrom_iff (start : Bool) :
    ∀ (m i : ℕ), i + m = k → 0 < i → ∀ (prev : A → Config A) (t : A),
      M.LegalBelow i prev → M.Posn t → M.Blk i (prev t).state →
      (∀ s, M.Posn s → M.Le s t → s ≠ t → M.BlkLt i (prev s).state) →
      (M.AltAcc start (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t) (prev t) ↔
        M.gameFrom start i m prev) := by
  intro m
  induction m with
  | zero =>
    intro i hik _ prev t _ _ hti _
    exfalso
    obtain ⟨j, hjk, hj, -⟩ := hbwf.1 (prev t).state
    have := blk_unique hbwf hti hj
    omega
  | succ m ih =>
    intro i hik hi prev t hprev ht hti hpast
    -- the entry configuration is pinned: it is not the lowest position, since a
    -- start state is in block `0`
    have hnotmin : ¬MinPos M.Le M.Posn t := by
      intro hmin
      have h0 := hbwf.2.2 (prev t).state (hprev.1 t hmin).1
      have := blk_unique hbwf hti h0
      omega
    obtain ⟨s₀, hs₀⟩ := exists_predPos hlin ht hnotmin
    refine altAcc_iff_guardQ hbwf hlin hmax start
      (fun v t' => ih (i + 1) (by omega) (by omega) v t') ht hti
      (fun w hw => hw.1)
      (fun w hw => hw.2.2 s₀ t hs₀ (hpast s₀ hs₀.1 hs₀.2.2.1 hs₀.2.2.2.1))
      (fun w hw s hs hle hne => by
        rw [hw.2.1 s hs (hpast s hs hle hne)]
        exact hpast s hs hle hne)
      fun ℓ f hℓ hplay hend => ⟨M.splice prev t ℓ f,
        roundCond_splice hbwf hlin hprev ht hmax hti hpast hℓ hplay hend, fun j hj => ?_⟩
    rw [splice_posSeq hlin ht hmax hplay.1.symm (Nat.le_trans hj hℓ), Nat.min_eq_left hj]

/-! ### Acceptance is the game -/

/-- **Alternating acceptance is the `k`-round game.** The first round has
nothing to inherit, so it is the general round with the initial configuration
as its own choice – which is why
`DescriptiveComplexity.ATMData.AltAccepts` quantifies that configuration at the
polarity of block `0`. -/
theorem altAccepts_iff_altGame (start : Bool) {p₀ : A} (hmin : MinPos M.Le M.Posn p₀)
    (hk : 0 < k) : M.AltAccepts start ↔ M.AltGame start k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hcard : bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p₀ =
      Nat.card {p : A // M.Posn p} - 1 := by
    have h1 := bitRank_maxPos hmax
    have h2 : bitRank M.Le M.Posn p₀ = 0 := bitRank_eq_zero_of_minPos hlin hmin
    omega
  -- the first round, for a fixed initial configuration
  have hkey : ∀ c₀ : Config A, M.IsInit c₀ →
      (M.AltAcc start (Nat.card {p : A // M.Posn p} - 1) c₀ ↔
        guardQ start (fun w => M.LegalBelow 1 w ∧ w p₀ = c₀)
          fun w => M.gameFrom start 1 m w) := by
    intro c₀ hinit
    have hc : M.Blk 0 c₀.state := hbwf.2.2 c₀.state hinit.1
    have hbase : M.LegalBelow 0 (fun _ => c₀) := by
      refine ⟨fun p _ => hinit, fun p q _ j j' hj hj' => ?_, fun p q _ hb => ?_⟩
      · exact Nat.le_of_eq (blk_unique hbwf hj hj')
      · obtain ⟨j, hj, -⟩ := hb
        exact absurd hj (Nat.not_lt_zero _)
    have hpast : ∀ s, M.Posn s → M.Le s p₀ → s ≠ p₀ → M.BlkLt 0 ((fun _ => c₀) s).state :=
      fun s hs hle hne => absurd (hlin.2.2.1 s p₀ hle (hmin.2 s hs)) hne
    have hmain := altAcc_iff_guardQ hbwf hlin hmax start (i := 0) (m := m)
      (fun v t' => gameFrom_iff hbwf hlin hmax start m 1 (by omega) (by omega) v t') hmin.1 hc
      (C := fun w => M.LegalBelow 1 w ∧ w p₀ = c₀)
      (fun w hw => hw.1) (fun w hw => hw.2)
      (fun w hw s hs hle hne => absurd (hlin.2.2.1 s p₀ hle (hmin.2 s hs)) hne)
      (fun ℓ f hℓ hplay hend => ⟨M.splice (fun _ => c₀) p₀ ℓ f,
        ⟨(roundCond_splice hbwf hlin hbase hmin.1 hmax hc hpast hℓ hplay hend).1, ?_⟩,
        fun j hj => ?_⟩)
    · rw [blockPol_zero] at hmain
      rw [← hcard]
      exact hmain
    · have h0 := splice_posSeq (prev := fun _ => c₀) (ℓ := ℓ) (f := f) hlin hmin.1 hmax
        hplay.1.symm (Nat.zero_le _)
      rw [posSeq_zero] at h0
      rw [h0, Nat.zero_min, hplay.1]
    · rw [splice_posSeq (prev := fun _ => c₀) hlin hmin.1 hmax hplay.1.symm
        (Nat.le_trans hj hℓ), Nat.min_eq_left hj]
  change guardQ start (fun c₀ => M.IsInit c₀) _ ↔
    guardQ (blockPol start 0) (fun w => M.LegalBelow 1 w) _
  rw [blockPol_zero]
  cases start with
  | false =>
    constructor
    · rintro ⟨⟨c₀, hc₀⟩, hall⟩
      refine ⟨⟨M.greedyWalk c₀, (legalBelow_greedyWalk hbwf hlin hc₀ 1).1⟩, fun w hw => ?_⟩
      have hinit : M.IsInit (w p₀) := hw.1 p₀ hmin
      exact ((hkey (w p₀) hinit).mp (hall (w p₀) hinit)).2 w ⟨hw, rfl⟩
    · rintro ⟨⟨w₀, hw₀⟩, hall⟩
      refine ⟨⟨w₀ p₀, hw₀.1 p₀ hmin⟩, fun c₀ hc₀ => (hkey c₀ hc₀).mpr ⟨?_, fun w hw => ?_⟩⟩
      · obtain ⟨hleg, hval⟩ := legalBelow_greedyWalk hbwf hlin hc₀ 1
        exact ⟨M.greedyWalk c₀, hleg, hval p₀ hmin⟩
      · exact hall w hw.1
  | true =>
    constructor
    · rintro ⟨c₀, hc₀, hacc⟩
      obtain ⟨w, hw, hg⟩ := (hkey c₀ hc₀).mp hacc
      exact ⟨w, hw.1, hg⟩
    · rintro ⟨w, hw, hg⟩
      have hinit : M.IsInit (w p₀) := hw.1 p₀ hmin
      exact ⟨w p₀, hinit, (hkey (w p₀) hinit).mpr ⟨w, ⟨hw, rfl⟩, hg⟩⟩

end Round

end ATMData

end DescriptiveComplexity
