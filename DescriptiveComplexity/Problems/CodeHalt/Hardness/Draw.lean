/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CodeHalt.Hardness.Interp

/-!
# The drawn instance draws the intended code

The correctness of the drawing: the instance built by
`DescriptiveComplexity.codeProgInterp` is well formed
(`DescriptiveComplexity.codeWF_codeProg`) and its root draws

```
comp cP (pair (numeral card) (nest of the tables))
```

(`DescriptiveComplexity.decodesTo_rootPt`).

Everything is a walk of the input order, taken with the increasing enumeration
`DescriptiveComplexity.ordEnum` of the universe: the numeral chain and each
level of each table block are proved by the *same* downward induction, from the
tail of the chain – the shared `zero` element – back to its head.

The subtree of the fixed code `cP` is the one place the induction is on a code
rather than on the order: `DescriptiveComplexity.decodesTo_subPos` says that a
drawing whose marks and children follow `DescriptiveComplexity.subAt`,
`DescriptiveComplexity.sub1` and `DescriptiveComplexity.sub2` draws every
subterm at its position, by structural induction on the code.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Nat.Partrec (Code)

open CodeProgRed

/-! ### Drawing a fixed code -/

section SubPosDraw

variable {N : Type} [Language.code.Structure N]

/-- **A drawing of the syntax tree of a code**: every position carries the
mark of its subterm's constructor, and the child relations follow the
positions of the children. -/
structure Draws (c : Code) (F : SubPos c → N) : Prop where
  /-- Every position carries the mark of its subterm's constructor. -/
  mark : ∀ p, Mark (tagOf (subAt c p)) (F p)
  /-- The first-child relation follows the first child of a position. -/
  arg1 : ∀ p q, sub1 c p = some q → CArg1 (F p) (F q)
  /-- The second-child relation follows the second child of a position. -/
  arg2 : ∀ p q, sub2 c p = some q → CArg2 (F p) (F q)

/-- A drawing restricts to a drawing of a subterm, along an embedding of
positions that respects subterms and children. -/
theorem Draws.embed {c c' : Code} {F : SubPos c → N} (h : Draws c F)
    (e : SubPos c' → SubPos c) (hsub : ∀ q, subAt c (e q) = subAt c' q)
    (h1e : ∀ q, sub1 c (e q) = (sub1 c' q).map e)
    (h2e : ∀ q, sub2 c (e q) = (sub2 c' q).map e) : Draws c' (F ∘ e) where
  mark p := by rw [← hsub p]; exact h.mark (e p)
  arg1 p q hq := h.arg1 _ _ (by rw [h1e p, hq]; rfl)
  arg2 p q hq := h.arg2 _ _ (by rw [h2e p, hq]; rfl)

/-- **A drawing of a code draws every subterm at its position.** The
hypotheses are exactly what the defining formulas of the interpretation give
for the tags of `cP`; the induction is on the code. -/
theorem decodesTo_subPos : ∀ (c : Code) (F : SubPos c → N), Draws c F →
    ∀ p, DecodesTo (F p) (subAt c p) := by
  intro c
  induction c with
  | zero => intro F h p; exact h.mark p
  | succ => intro F h p; exact h.mark p
  | left => intro F h p; exact h.mark p
  | right => intro F h p; exact h.mark p
  | pair cf cg ihf ihg =>
    intro F h p
    have hf : Draws cf (F ∘ fun q => Sum.inr (Sum.inl q)) :=
      h.embed _ (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    have hg : Draws cg (F ∘ fun q => Sum.inr (Sum.inr q)) :=
      h.embed _ (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    have hrf : DecodesTo (F (Sum.inr (Sum.inl (codeRootPos cf)))) cf := by
      have := ihf _ hf (codeRootPos cf); rwa [subAt_codeRootPos] at this
    have hrg : DecodesTo (F (Sum.inr (Sum.inr (codeRootPos cg)))) cg := by
      have := ihg _ hg (codeRootPos cg); rwa [subAt_codeRootPos] at this
    match p with
    | Sum.inl _ =>
      exact ⟨h.mark (Sum.inl ()), _, _, h.arg1 _ _ rfl, h.arg2 _ _ rfl, hrf, hrg⟩
    | Sum.inr (Sum.inl q) => exact ihf _ hf q
    | Sum.inr (Sum.inr q) => exact ihg _ hg q
  | comp cf cg ihf ihg =>
    intro F h p
    have hf : Draws cf (F ∘ fun q => Sum.inr (Sum.inl q)) :=
      h.embed _ (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    have hg : Draws cg (F ∘ fun q => Sum.inr (Sum.inr q)) :=
      h.embed _ (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    have hrf : DecodesTo (F (Sum.inr (Sum.inl (codeRootPos cf)))) cf := by
      have := ihf _ hf (codeRootPos cf); rwa [subAt_codeRootPos] at this
    have hrg : DecodesTo (F (Sum.inr (Sum.inr (codeRootPos cg)))) cg := by
      have := ihg _ hg (codeRootPos cg); rwa [subAt_codeRootPos] at this
    match p with
    | Sum.inl _ =>
      exact ⟨h.mark (Sum.inl ()), _, _, h.arg1 _ _ rfl, h.arg2 _ _ rfl, hrf, hrg⟩
    | Sum.inr (Sum.inl q) => exact ihf _ hf q
    | Sum.inr (Sum.inr q) => exact ihg _ hg q
  | prec cf cg ihf ihg =>
    intro F h p
    have hf : Draws cf (F ∘ fun q => Sum.inr (Sum.inl q)) :=
      h.embed _ (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    have hg : Draws cg (F ∘ fun q => Sum.inr (Sum.inr q)) :=
      h.embed _ (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    have hrf : DecodesTo (F (Sum.inr (Sum.inl (codeRootPos cf)))) cf := by
      have := ihf _ hf (codeRootPos cf); rwa [subAt_codeRootPos] at this
    have hrg : DecodesTo (F (Sum.inr (Sum.inr (codeRootPos cg)))) cg := by
      have := ihg _ hg (codeRootPos cg); rwa [subAt_codeRootPos] at this
    match p with
    | Sum.inl _ =>
      exact ⟨h.mark (Sum.inl ()), _, _, h.arg1 _ _ rfl, h.arg2 _ _ rfl, hrf, hrg⟩
    | Sum.inr (Sum.inl q) => exact ihf _ hf q
    | Sum.inr (Sum.inr q) => exact ihg _ hg q
  | rfind' cf ihf =>
    intro F h p
    have hf : Draws cf (F ∘ fun q => Sum.inr q) :=
      h.embed _ (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    have hrf : DecodesTo (F (Sum.inr (codeRootPos cf))) cf := by
      have := ihf _ hf (codeRootPos cf); rwa [subAt_codeRootPos] at this
    match p with
    | Sum.inl _ => exact ⟨h.mark (Sum.inl ()), _, h.arg1 _ _ rfl, hrf⟩
    | Sum.inr q => exact ihf _ hf q

end SubPosDraw

/-! ### The increasing enumeration of a finite linear order -/

section Enum

variable (A : Type) [LinearOrder A] [Finite A]

/-- The increasing enumeration of a finite linear order. Every chain of the
drawing walks the order along it. -/
noncomputable def ordEnum : Fin (Nat.card A) ≃o A :=
  letI := Fintype.ofFinite A
  monoEquivOfFin A (Nat.card_eq_fintype_card (α := A)).symm

variable {A}

theorem isBot_ordEnum_zero (h : 0 < Nat.card A) : IsBot (ordEnum A ⟨0, h⟩) := fun a => by
  rw [← (ordEnum A).apply_symm_apply a, (ordEnum A).le_iff_le, Fin.le_def]
  change 0 ≤ ((ordEnum A).symm a : ℕ)
  omega

theorem isTop_ordEnum_last (h : 0 < Nat.card A) :
    IsTop (ordEnum A ⟨Nat.card A - 1, by omega⟩) := fun a => by
  rw [← (ordEnum A).apply_symm_apply a, (ordEnum A).le_iff_le, Fin.le_def]
  have h2 := ((ordEnum A).symm a).isLt
  change ((ordEnum A).symm a : ℕ) ≤ Nat.card A - 1
  omega

theorem ordEnum_lt_succ {k : ℕ} (h : k + 1 < Nat.card A) :
    ordEnum A ⟨k, by omega⟩ < ordEnum A ⟨k + 1, h⟩ := by
  rw [(ordEnum A).lt_iff_lt, Fin.lt_def]
  change k < k + 1
  omega

theorem ordEnum_covBy {k : ℕ} (h : k + 1 < Nat.card A) :
    ∀ a : A, ¬(ordEnum A ⟨k, by omega⟩ < a ∧ a < ordEnum A ⟨k + 1, h⟩) := by
  rintro a ⟨h1, h2⟩
  rw [← (ordEnum A).apply_symm_apply a, (ordEnum A).lt_iff_lt, Fin.lt_def] at h1 h2
  have e1 : k < ((ordEnum A).symm a : ℕ) := h1
  have e2 : ((ordEnum A).symm a : ℕ) < k + 1 := h2
  omega

end Enum

/-! ### Uniqueness of the elements the guards pin down -/

section Unique

variable {A : Type} [LinearOrder A]

theorem eq_of_isBot {a b : A} (ha : IsBot a) (hb : IsBot b) : a = b :=
  le_antisymm (ha b) (hb a)

theorem canon_ext {D m : ℕ} {u u' : Fin D → A} (h : Canon m u) (h' : Canon m u')
    (hag : ∀ j : Fin D, (j : ℕ) < m → u j = u' j) : u = u' := by
  funext j
  by_cases hj : (j : ℕ) < m
  · exact hag j hj
  · exact eq_of_isBot (h j (by omega)) (h' j (by omega))

theorem cov_unique {a b b' : A} (h1 : a < b) (h2 : ∀ c : A, ¬(a < c ∧ c < b))
    (h1' : a < b') (h2' : ∀ c : A, ¬(a < c ∧ c < b')) : b = b' := by
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · exact absurd ⟨h1, hlt⟩ (h2' b)
  · exact heq
  · exact absurd ⟨h1', hgt⟩ (h2 b')

theorem not_isTop_of_lt {a b : A} (h : a < b) : ¬IsTop a := fun ht => absurd (ht b) (not_le.mpr h)

theorem canon_mono {D m m' : ℕ} {u : Fin D → A} (h : Canon m u) (hm : m ≤ m') : Canon m' u :=
  fun j hj => h j (le_trans hm hj)

end Unique

/-! ### The elements of the drawing -/

section Draw

variable {L : Language.{0, 0}} (V : FinVocab L) (cP : Code)
  (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The least element of the input order. -/
noncomputable def botOrd : A := ordEnum A ⟨0, Nat.card_pos⟩

/-- The canonically padded tuple every unindexed element of the drawing
carries. -/
noncomputable def botTup : Fin (dimOf V) → A := fun _ => botOrd A

variable {V A}

theorem isBot_botA : IsBot (botOrd A) := isBot_ordEnum_zero _

omit [L.Structure A] in
theorem canon_botTup (m : ℕ) : Canon m (botTup V A) := fun _ _ => isBot_botA

theorem ordEnum_zero : ordEnum A ⟨0, Nat.card_pos⟩ = botOrd A := rfl

variable (V A)

open Classical in
/-- The element carrying the bit of a tuple: the shared `succ` element if the
symbol holds of it, the shared `zero` element if it does not. -/
noncomputable def bitPt (i : Fin V.numSyms) (u : Fin (dimOf V) → A) :
    (codeProgInterp V cP).Map A :=
  if bitOf V i u then progPt ProgTag.oneN (botTup V A) else progPt ProgTag.zeroN (botTup V A)

/-- The element standing at position `k` of the level-`l` chain of the block
of the symbol `i`, above the prefix `u`. -/
noncomputable def chainPt (i : Fin V.numSyms) (l : Fin (dimOf V))
    (u : Fin (dimOf V) → A) (k : ℕ) : (codeProgInterp V cP).Map A :=
  if h : k < Nat.card A then progPt (ProgTag.chainN i l) (setCo V (l : ℕ) (ordEnum A ⟨k, h⟩) u)
  else progPt ProgTag.zeroN (botTup V A)

/-- The element whose value is that of `DescriptiveComplexity.levelVal`: the
bit at the bottom, the head of the next chain above it. -/
noncomputable def levelPt (i : Fin V.numSyms) :
    ℕ → (Fin (dimOf V) → A) → (codeProgInterp V cP).Map A
  | 0, u => bitPt V cP A i u
  | m + 1, u =>
      chainPt V cP A i ⟨dimOf V - (m + 1), Nat.sub_lt (dimOf_pos V) (Nat.succ_pos m)⟩ u 0

/-- The element standing at position `k` of the numeral chain. -/
noncomputable def numPt (k : ℕ) : (codeProgInterp V cP).Map A :=
  if h : k < Nat.card A then progPt ProgTag.numN (setCo V 0 (ordEnum A ⟨k, h⟩) (botTup V A))
  else progPt ProgTag.zeroN (botTup V A)

/-- The element standing at the symbol `k` of the chain of blocks. -/
noncomputable def symPt (k : ℕ) : (codeProgInterp V cP).Map A :=
  if h : k < V.numSyms then progPt (ProgTag.symN ⟨k, h⟩) (botTup V A)
  else progPt ProgTag.zeroN (botTup V A)

variable {V cP A}

/-! ### The two shared leaves -/

theorem decodesTo_zeroPt :
    DecodesTo (progPt (ProgTag.zeroN : ProgTag V cP) (botTup V A)) Code.zero :=
  (mark_pt CodeTag.zero ProgTag.zeroN (botTup V A)).mpr ⟨canon_botTup 0, rfl⟩

theorem decodesTo_onePt :
    DecodesTo (progPt (ProgTag.oneN : ProgTag V cP) (botTup V A)) Code.succ :=
  (mark_pt CodeTag.succ ProgTag.oneN (botTup V A)).mpr ⟨canon_botTup 0, rfl⟩

/-! ### The chains of the blocks -/

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem canon_setCo {m : ℕ} {j : ℕ} (hj : j < m) (a : A) {u : Fin (dimOf V) → A}
    (h : Canon m u) : Canon m (setCo V j a u) := by
  intro j' hj'
  rw [setCo_apply_ne V (by omega) a u]
  exact h j' hj'

omit [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem setCo_at (l : Fin (dimOf V)) (a : A) (t : Fin (dimOf V) → A) :
    setCo V (l : ℕ) a t l = a := by rw [setCo, if_pos rfl]

omit [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem setCo_at_fz (a : A) (t : Fin (dimOf V) → A) : setCo V 0 a t (fz V) = a := by
  rw [setCo, if_pos (show ((fz V : Fin (dimOf V)) : ℕ) = 0 from rfl)]

omit [L.Structure A] in
theorem setCo_bot_at (l : Fin (dimOf V)) {u : Fin (dimOf V) → A} (h : IsBot (u l)) :
    setCo V (l : ℕ) (botOrd A) u = u := by
  rw [show botOrd A = u l from eq_of_isBot isBot_botA h]
  funext j
  by_cases hj : (j : ℕ) = (l : ℕ)
  · rw [setCo, if_pos hj]
    exact congrArg u (Fin.ext hj).symm
  · rw [setCo_apply_ne V hj]

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem okOn_chainN (i : Fin V.numSyms) (l : Fin (dimOf V)) (u : Fin (dimOf V) → A) :
    OkOn (ProgTag.chainN i l : ProgTag V cP) u ↔ Canon ((l : ℕ) + 1) u := Iff.rfl

open Classical in
theorem cArg1_chainPt (i : Fin V.numSyms) (l : Fin (dimOf V)) (m : ℕ)
    (hm : (l : ℕ) + m + 1 = dimOf V) {uk : Fin (dimOf V) → A}
    (hok : Canon ((l : ℕ) + 1) uk) :
    CArg1 (progPt (ProgTag.chainN i l) uk) (levelPt V cP A i m uk) := by
  match m with
  | 0 =>
    rw [levelPt, bitPt]
    by_cases hb : bitOf V i uk
    · rw [if_pos hb]
      exact (cArg1_pt _ _ _ _).mpr ⟨hok, canon_botTup _, by omega, hb⟩
    · rw [if_neg hb]
      exact (cArg1_pt _ _ _ _).mpr ⟨hok, canon_botTup _, by omega, hb⟩
  | m' + 1 =>
    rw [levelPt, chainPt, dif_pos (Nat.card_pos (α := A))]
    have hlt : dimOf V - (m' + 1) < dimOf V := Nat.sub_lt (dimOf_pos V) (Nat.succ_pos m')
    have hl'v : ((⟨dimOf V - (m' + 1), hlt⟩ : Fin (dimOf V)) : ℕ) = (l : ℕ) + 1 := by
      change dimOf V - (m' + 1) = (l : ℕ) + 1
      omega
    have hbot : IsBot (uk ⟨dimOf V - (m' + 1), hlt⟩) :=
      hok _ (by change (l : ℕ) + 1 ≤ dimOf V - (m' + 1); omega)
    rw [ordEnum_zero, setCo_bot_at _ hbot]
    exact (cArg1_pt _ _ _ _).mpr
      ⟨hok, (okOn_chainN _ _ _).mpr (canon_mono hok (by rw [hl'v]; omega)), ⟨rfl, hl'v⟩, rfl⟩

theorem cArg2_chainPt (i : Fin V.numSyms) (l : Fin (dimOf V)) {u : Fin (dimOf V) → A}
    (hu : Canon (l : ℕ) u) (k : ℕ) (hk : k < Nat.card A) :
    CArg2 (progPt (ProgTag.chainN i l) (setCo V (l : ℕ) (ordEnum A ⟨k, hk⟩) u))
      (chainPt V cP A i l u (k + 1)) := by
  have hok : Canon ((l : ℕ) + 1) (setCo V (l : ℕ) (ordEnum A ⟨k, hk⟩) u) :=
    canon_setCo (by omega) _ (canon_mono hu (by omega))
  by_cases hk1 : k + 1 < Nat.card A
  · rw [chainPt, dif_pos hk1]
    refine (cArg2_pt _ _ _ _).mpr ⟨hok,
      (okOn_chainN _ _ _).mpr (canon_setCo (by omega) _ (canon_mono hu (by omega))),
      ⟨rfl, rfl⟩, ?_, ?_⟩
    · rw [setCo_at, setCo_at]
      exact ⟨ordEnum_lt_succ hk1, ordEnum_covBy hk1⟩
    · intro j hj
      rw [setCo_apply_ne V (by omega) _ _, setCo_apply_ne V (by omega) _ _]
  · rw [chainPt, dif_neg hk1]
    refine (cArg2_pt _ _ _ _).mpr ⟨hok, canon_botTup _, ?_⟩
    change IsTop _
    rw [setCo_at, show (⟨k, hk⟩ : Fin (Nat.card A)) = ⟨Nat.card A - 1, by omega⟩ from
      Fin.ext (show k = Nat.card A - 1 from by omega)]
    exact isTop_ordEnum_last Nat.card_pos

open Classical in
/-- **Every level of a block is drawn**: the chain that walks the coordinate
`dimOf V - m` draws the nest of the values below it. The induction is on the
level, and inside it on the position along the chain, downwards from its
tail. -/
theorem decodesTo_levelPt : ∀ (m : ℕ), m ≤ dimOf V → ∀ (i : Fin V.numSyms)
    (u : Fin (dimOf V) → A), Canon (dimOf V - m) u →
    DecodesTo (levelPt V cP A i m u) (levelCode V (Nat.card A) (ordEnum A) i m u) := by
  intro m
  induction m with
  | zero =>
    intro _ i u _
    rw [levelPt, levelCode_zero, bitPt]
    by_cases hb : bitOf V i u
    · rw [if_pos hb, if_pos hb]; exact decodesTo_onePt
    · rw [if_neg hb, if_neg hb]; exact decodesTo_zeroPt
  | succ m ih =>
    intro hm i u hu
    have hlt : dimOf V - (m + 1) < dimOf V := Nat.sub_lt (dimOf_pos V) (Nat.succ_pos m)
    set l : Fin (dimOf V) := ⟨dimOf V - (m + 1), hlt⟩ with hl
    have hlv : (l : ℕ) = dimOf V - (m + 1) := rfl
    have hlm : (l : ℕ) + m + 1 = dimOf V := by rw [hlv]; omega
    have hu' : Canon (l : ℕ) u := by rw [hlv]; exact hu
    have key : ∀ j k : ℕ, k + j = Nat.card A →
        DecodesTo (chainPt V cP A i l u k)
          (codeNestFrom (fun d : Fin (Nat.card A) =>
            levelCode V (Nat.card A) (ordEnum A) i m
              (setCo V (l : ℕ) (ordEnum A d) u)) k) := by
      intro j
      induction j with
      | zero =>
        intro k hk
        have hkn : ¬k < Nat.card A := by omega
        rw [chainPt, dif_neg hkn, codeNestFrom_of_ge _ hkn]
        exact decodesTo_zeroPt
      | succ j ihj =>
        intro k hk
        have hkn : k < Nat.card A := by omega
        rw [chainPt, dif_pos hkn, codeNestFrom_of_lt _ hkn]
        have hokk : Canon ((l : ℕ) + 1) (setCo V (l : ℕ) (ordEnum A ⟨k, hkn⟩) u) :=
          canon_setCo (by omega) _ (canon_mono hu' (by omega))
        refine ⟨(mark_pt CodeTag.pair _ _).mpr ⟨hokk, rfl⟩,
          levelPt V cP A i m (setCo V (l : ℕ) (ordEnum A ⟨k, hkn⟩) u),
          chainPt V cP A i l u (k + 1), cArg1_chainPt i l m hlm hokk,
          cArg2_chainPt i l hu' k hkn, ?_, ihj (k + 1) (by omega)⟩
        exact ih (by omega) i _ (by rw [show dimOf V - m = (l : ℕ) + 1 from by omega]; exact hokk)
    have h0 := key (Nat.card A) 0 (by omega)
    rw [levelPt, levelCode_succ]
    exact h0

open Classical in
/-- The head of the chains of a block draws the block. -/
theorem decodesTo_blockPt (cP : Code) (i : Fin V.numSyms) :
    DecodesTo (progPt (ProgTag.chainN i ⟨0, dimOf_pos V⟩ : ProgTag V cP) (botTup V A))
      (blockCode V (Nat.card A) (ordEnum A) (botTup V A) i) := by
  obtain ⟨d, hd⟩ : ∃ d, dimOf V = d + 1 :=
    ⟨dimOf V - 1, by have := dimOf_pos V; omega⟩
  have h := decodesTo_levelPt (cP := cP) (d + 1) (by omega) i (botTup V A) (canon_botTup _)
  rw [levelPt, chainPt, dif_pos (Nat.card_pos (α := A))] at h
  rw [show (⟨dimOf V - (d + 1), Nat.sub_lt (dimOf_pos V) (Nat.succ_pos d)⟩ : Fin (dimOf V)) =
      ⟨0, dimOf_pos V⟩ from Fin.ext (by change dimOf V - (d + 1) = 0; omega),
    ordEnum_zero, setCo_bot_at _ isBot_botA, ← hd] at h
  rw [blockCode]
  exact h

/-! ### The chain of the blocks of the symbols -/

open Classical in
theorem decodesTo_symPt : ∀ (j k : ℕ), k + j = V.numSyms →
    DecodesTo (symPt V cP A k)
      (codeNestFrom (blockCode V (Nat.card A) (ordEnum A) (botTup V A)) k) := by
  intro j
  induction j with
  | zero =>
    intro k hk
    have hkn : ¬k < V.numSyms := by omega
    rw [symPt, dif_neg hkn, codeNestFrom_of_ge _ hkn]
    exact decodesTo_zeroPt
  | succ j ihj =>
    intro k hk
    have hkn : k < V.numSyms := by omega
    rw [symPt, dif_pos hkn, codeNestFrom_of_lt _ hkn]
    refine ⟨(mark_pt CodeTag.pair _ _).mpr ⟨canon_botTup _, rfl⟩,
      progPt (ProgTag.chainN ⟨k, hkn⟩ ⟨0, dimOf_pos V⟩) (botTup V A), symPt V cP A (k + 1), ?_, ?_,
      decodesTo_blockPt _ _, ihj (k + 1) (by omega)⟩
    · exact (cArg1_pt _ _ _ _).mpr ⟨canon_botTup _, canon_botTup _, ⟨rfl, rfl⟩, isBot_botA⟩
    · by_cases hk1 : k + 1 < V.numSyms
      · rw [symPt, dif_pos hk1]
        exact (cArg2_pt _ _ _ _).mpr ⟨canon_botTup _, canon_botTup _, rfl⟩
      · rw [symPt, dif_neg hk1]
        exact (cArg2_pt _ _ _ _).mpr
          ⟨canon_botTup _, canon_botTup _, by change k + 1 = V.numSyms; omega⟩

/-! ### The numeral chain -/

theorem decodesTo_numPt : ∀ (j k : ℕ), k + j = Nat.card A →
    DecodesTo (numPt V cP A k) (numCode (Nat.card A - k)) := by
  intro j
  induction j with
  | zero =>
    intro k hk
    have hkn : ¬k < Nat.card A := by omega
    rw [numPt, dif_neg hkn, show Nat.card A - k = 0 from by omega, numCode]
    exact decodesTo_zeroPt
  | succ j ihj =>
    intro k hk
    have hkn : k < Nat.card A := by omega
    rw [numPt, dif_pos hkn, show Nat.card A - k = Nat.card A - (k + 1) + 1 from by omega,
      numCode]
    have hok : Canon 1 (setCo V 0 (ordEnum A ⟨k, hkn⟩) (botTup V A)) :=
      canon_setCo (by omega) _ (canon_botTup _)
    refine ⟨(mark_pt CodeTag.comp _ _).mpr ⟨hok, rfl⟩, progPt ProgTag.oneN (botTup V A),
      numPt V cP A (k + 1), (cArg1_pt _ _ _ _).mpr ⟨hok, canon_botTup _, trivial⟩, ?_,
      decodesTo_onePt, ihj (k + 1) (by omega)⟩
    by_cases hk1 : k + 1 < Nat.card A
    · rw [numPt, dif_pos hk1]
      refine (cArg2_pt _ _ _ _).mpr
        ⟨hok, canon_setCo (show (0 : ℕ) < 1 from by omega) _ (canon_botTup _), ?_⟩
      change _ < _ ∧ _
      rw [setCo_at_fz, setCo_at_fz]
      exact ⟨ordEnum_lt_succ hk1, ordEnum_covBy hk1⟩
    · rw [numPt, dif_neg hk1]
      refine (cArg2_pt _ _ _ _).mpr ⟨hok, canon_botTup _, ?_⟩
      change IsTop _
      rw [setCo_at_fz, show (⟨k, hkn⟩ : Fin (Nat.card A)) = ⟨Nat.card A - 1, by omega⟩ from
        Fin.ext (show k = Nat.card A - 1 from by omega)]
      exact isTop_ordEnum_last Nat.card_pos
/-! ### The whole instance -/

open Classical in
/-- The element of the `pair` draws the numeral of the universe size beside
the nest of the tables. -/
theorem decodesTo_pairPt (cP : Code) :
    DecodesTo (progPt (ProgTag.pairN : ProgTag V cP) (botTup V A))
      (Code.pair (numCode (Nat.card A))
        (codeNestFrom (blockCode V (Nat.card A) (ordEnum A) (botTup V A)) 0)) := by
  refine ⟨(mark_pt CodeTag.pair _ _).mpr ⟨canon_botTup _, rfl⟩, numPt V cP A 0,
    symPt V cP A 0, ?_, ?_, ?_, decodesTo_symPt V.numSyms 0 (Nat.zero_add _)⟩
  · rw [numPt, dif_pos (Nat.card_pos (α := A))]
    refine (cArg1_pt _ _ _ _).mpr ⟨canon_botTup _,
      canon_setCo (show (0 : ℕ) < 1 from by omega) _ (canon_botTup _), ?_⟩
    change IsBot _
    rw [setCo_at_fz]
    exact isBot_ordEnum_zero _
  · by_cases hs : 0 < V.numSyms
    · rw [symPt, dif_pos hs]
      exact (cArg2_pt _ _ _ _).mpr ⟨canon_botTup _, canon_botTup _, rfl⟩
    · rw [symPt, dif_neg hs]
      exact (cArg2_pt _ _ _ _).mpr
        ⟨canon_botTup _, canon_botTup _, by change V.numSyms = 0; omega⟩
  · have h := decodesTo_numPt (V := V) (cP := cP) (A := A) (Nat.card A) 0 (Nat.zero_add _)
    rwa [Nat.sub_zero] at h

open Classical in
/-- **The root of the drawn instance draws the intended program**: the fixed
procedure `cP`, composed with the pair of the numeral of the universe size and
the nest of the tables. -/
theorem decodesTo_rootPt (cP : Code) :
    DecodesTo (progPt (ProgTag.root : ProgTag V cP) (botTup V A))
      (Code.comp cP (Code.pair (numCode (Nat.card A))
        (codeNestFrom (blockCode V (Nat.card A) (ordEnum A) (botTup V A)) 0))) := by
  have hdraws : Draws cP fun p =>
      (progPt (ProgTag.cp p) (botTup V A) : (codeProgInterp V cP).Map A) :=
    { mark := fun _ => (mark_pt _ _ _).mpr ⟨canon_botTup _, rfl⟩
      arg1 := fun _ _ hq => (cArg1_pt _ _ _ _).mpr ⟨canon_botTup _, canon_botTup _, hq⟩
      arg2 := fun _ _ hq => (cArg2_pt _ _ _ _).mpr ⟨canon_botTup _, canon_botTup _, hq⟩ }
  have hcp := decodesTo_subPos cP _ hdraws (codeRootPos cP)
  rw [subAt_codeRootPos] at hcp
  exact ⟨(mark_pt CodeTag.comp _ _).mpr ⟨canon_botTup _, rfl⟩,
    progPt (ProgTag.cp (codeRootPos cP)) (botTup V A), progPt ProgTag.pairN (botTup V A),
    (cArg1_pt _ _ _ _).mpr ⟨canon_botTup _, canon_botTup _, rfl⟩,
    (cArg2_pt _ _ _ _).mpr ⟨canon_botTup _, canon_botTup _, trivial⟩,
    hcp, decodesTo_pairPt cP⟩

/-! ### The drawing is well formed -/

omit [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem progPt_congr {t t' : ProgTag V cP} {u u' : Fin (dimOf V) → A} (h : t = t') (h2 : u = u') :
    (progPt t u : (codeProgInterp V cP).Map A) = progPt t' u' := by subst h; subst h2; rfl

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem canon0_ext {u u' : Fin (dimOf V) → A} (h : Canon 0 u) (h' : Canon 0 u') : u = u' :=
  canon_ext h h' (by omega)

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem canon_one_bot {u : Fin (dimOf V) → A} (h1 : Canon 1 u) (h0 : IsBot (u (fz V))) :
    Canon 0 u := by
  intro j _
  by_cases hj : (j : ℕ) = 0
  · rw [show j = fz V from Fin.ext hj]; exact h0
  · exact h1 j (by omega)

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem okOn_numN (u : Fin (dimOf V) → A) :
    OkOn (ProgTag.numN : ProgTag V cP) u ↔ Canon 1 u := Iff.rfl

omit [Finite A] [Nonempty A] in
/-- **The first child of an element is unique.** -/
theorem arg1_det {ta tb tb' : ProgTag V cP} {ua ub ub' : Fin (dimOf V) → A}
    (hob : OkOn tb ub) (hob' : OkOn tb' ub')
    (h : Arg1On ta tb ua ub) (h' : Arg1On ta tb' ua ub') :
    (progPt tb ub : (codeProgInterp V cP).Map A) = progPt tb' ub' := by
  cases ta
  case root =>
    cases tb <;> try exact h.elim
    cases tb' <;> try exact h'.elim
    exact progPt_congr (congrArg ProgTag.cp ((show _ = _ from h).trans (show _ = _ from h').symm))
      (canon0_ext hob hob')
  case cp p =>
    cases tb <;> try exact h.elim
    cases tb' <;> try exact h'.elim
    exact progPt_congr (congrArg ProgTag.cp (Option.some.inj (h.symm.trans h')))
      (canon0_ext hob hob')
  case pairN =>
    cases tb <;> try exact h.elim
    cases tb' <;> try exact h'.elim
    exact progPt_congr rfl
      (canon0_ext (canon_one_bot ((okOn_numN _).mp hob) h)
        (canon_one_bot ((okOn_numN _).mp hob') h'))
  case numN =>
    cases tb <;> try exact h.elim
    cases tb' <;> try exact h'.elim
    exact progPt_congr rfl (canon0_ext hob hob')
  case symN i =>
    cases tb <;> try exact h.elim
    rename_i i₁ l₁
    obtain ⟨⟨hi₁, hl₁⟩, hb₁⟩ := h
    cases tb' <;> try exact h'.elim
    rename_i i₂ l₂
    obtain ⟨⟨hi₂, hl₂⟩, hb₂⟩ := h'
    have hc₁ : Canon 1 ub := by simpa [hl₁] using (okOn_chainN _ _ _).mp hob
    have hc₂ : Canon 1 ub' := by simpa [hl₂] using (okOn_chainN _ _ _).mp hob'
    exact progPt_congr (by rw [← hi₁, ← hi₂, Fin.ext (hl₁.trans hl₂.symm)])
      (canon0_ext (canon_one_bot hc₁ hb₁) (canon_one_bot hc₂ hb₂))
  case chainN i l =>
    cases tb <;> try exact h.elim
    · rename_i i₁ l₁
      obtain ⟨⟨hi₁, hl₁⟩, hu₁⟩ := h
      cases tb' <;> try exact h'.elim
      · rename_i i₂ l₂
        obtain ⟨⟨hi₂, hl₂⟩, hu₂⟩ := h'
        exact progPt_congr (by rw [← hi₁, ← hi₂, Fin.ext (hl₁.trans hl₂.symm)])
          (hu₁.trans hu₂.symm)
      · obtain ⟨hd, -⟩ := h'
        exact absurd l₁.isLt (by omega)
      · obtain ⟨hd, -⟩ := h'
        exact absurd l₁.isLt (by omega)
    · obtain ⟨hd, hbit⟩ := h
      cases tb' <;> try exact h'.elim
      · rename_i i₂ l₂
        obtain ⟨⟨-, hl₂⟩, -⟩ := h'
        exact absurd l₂.isLt (by omega)
      · exact progPt_congr rfl (canon0_ext hob hob')
      · exact absurd hbit h'.2
    · obtain ⟨hd, hbit⟩ := h
      cases tb' <;> try exact h'.elim
      · rename_i i₂ l₂
        obtain ⟨⟨-, hl₂⟩, -⟩ := h'
        exact absurd l₂.isLt (by omega)
      · exact absurd h'.2 hbit
      · exact progPt_congr rfl (canon0_ext hob hob')
  case oneN => exact h.elim
  case zeroN => exact h.elim

omit [L.Structure A] [Finite A] [Nonempty A] in
/-- **The second child of an element is unique.** -/
theorem arg2_det {ta tb tb' : ProgTag V cP} {ua ub ub' : Fin (dimOf V) → A}
    (hob : OkOn tb ub) (hob' : OkOn tb' ub')
    (h : Arg2On ta tb ua ub) (h' : Arg2On ta tb' ua ub') :
    (progPt tb ub : (codeProgInterp V cP).Map A) = progPt tb' ub' := by
  cases ta
  case root =>
    cases tb <;> try exact h.elim
    cases tb' <;> try exact h'.elim
    exact progPt_congr rfl (canon0_ext hob hob')
  case cp p =>
    cases tb <;> try exact h.elim
    cases tb' <;> try exact h'.elim
    exact progPt_congr (congrArg ProgTag.cp (Option.some.inj (h.symm.trans h')))
      (canon0_ext hob hob')
  case pairN =>
    cases tb <;> try exact h.elim
    · rename_i i₁
      cases tb' <;> try exact h'.elim
      · exact progPt_congr (congrArg ProgTag.symN (Fin.ext ((show _ = _ from h).trans
          (show _ = _ from h').symm))) (canon0_ext hob hob')
      · exact absurd i₁.isLt (by have hz : V.numSyms = 0 := h'; omega)
    · cases tb' <;> try exact h'.elim
      · rename_i i₂
        exact absurd i₂.isLt (by have hz : V.numSyms = 0 := h; omega)
      · exact progPt_congr rfl (canon0_ext hob hob')
  case numN =>
    cases tb <;> try exact h.elim
    · cases tb' <;> try exact h'.elim
      · refine progPt_congr rfl (canon_ext ((okOn_numN _).mp hob) ((okOn_numN _).mp hob')
          fun j hj => ?_)
        rw [show j = fz V from Fin.ext (show (j : ℕ) = 0 from by omega)]
        exact cov_unique h.1 h.2 h'.1 h'.2
      · exact absurd h' (not_isTop_of_lt h.1)
    · cases tb' <;> try exact h'.elim
      · exact absurd h (not_isTop_of_lt h'.1)
      · exact progPt_congr rfl (canon0_ext hob hob')
  case symN i =>
    cases tb <;> try exact h.elim
    · rename_i i₁
      cases tb' <;> try exact h'.elim
      · exact progPt_congr (congrArg ProgTag.symN (Fin.ext ((show _ = _ from h).trans
          (show _ = _ from h').symm))) (canon0_ext hob hob')
      · exact absurd i₁.isLt (by
          have h1 : (i₁ : ℕ) = (i : ℕ) + 1 := h
          have h2 : (i : ℕ) + 1 = V.numSyms := h'
          omega)
    · cases tb' <;> try exact h'.elim
      · rename_i i₂
        exact absurd i₂.isLt (by
          have h1 : (i₂ : ℕ) = (i : ℕ) + 1 := h'
          have h2 : (i : ℕ) + 1 = V.numSyms := h
          omega)
      · exact progPt_congr rfl (canon0_ext hob hob')
  case chainN i l =>
    cases tb <;> try exact h.elim
    · rename_i i₁ l₁
      obtain ⟨⟨hi₁, hl₁⟩, hcov₁, hag₁⟩ := h
      subst hl₁
      cases tb' <;> try exact h'.elim
      · rename_i i₂ l₂
        obtain ⟨⟨hi₂, hl₂⟩, hcov₂, hag₂⟩ := h'
        subst hl₂
        refine progPt_congr (by rw [← hi₁, ← hi₂]) (canon_ext ((okOn_chainN _ _ _).mp hob)
          ((okOn_chainN _ _ _).mp hob') fun j hj => ?_)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
        · rw [hag₁ j hj', hag₂ j hj']
        · rw [show j = l from Fin.ext hj']
          exact cov_unique hcov₁.1 hcov₁.2 hcov₂.1 hcov₂.2
      · exact absurd h' (not_isTop_of_lt hcov₁.1)
    · cases tb' <;> try exact h'.elim
      · rename_i i₂ l₂
        exact absurd h (not_isTop_of_lt h'.2.1.1)
      · exact progPt_congr rfl (canon0_ext hob hob')
  case oneN => exact h.elim
  case zeroN => exact h.elim

variable (V cP A)

omit [Finite A] [Nonempty A] in
/-- **The drawn instance is well formed**: at most one constructor mark per
element and functional child relations, which is what makes what an element
draws unique. -/
theorem codeWF_codeProg : CodeWF ((codeProgInterp V cP).Map A) where
  exclusive a t t' h1 h2 := by
    obtain ⟨tg, u, rfl⟩ := exists_progPt a
    exact ((mark_pt t tg u).mp h1).2.symm.trans ((mark_pt t' tg u).mp h2).2
  arg1_fun a b b' h1 h2 := by
    obtain ⟨ta, ua, rfl⟩ := exists_progPt a
    obtain ⟨tb, ub, rfl⟩ := exists_progPt b
    obtain ⟨tb', ub', rfl⟩ := exists_progPt b'
    obtain ⟨-, hob, hab⟩ := (cArg1_pt _ _ _ _).mp h1
    obtain ⟨-, hob', hab'⟩ := (cArg1_pt _ _ _ _).mp h2
    exact arg1_det hob hob' hab hab'
  arg2_fun a b b' h1 h2 := by
    obtain ⟨ta, ua, rfl⟩ := exists_progPt a
    obtain ⟨tb, ub, rfl⟩ := exists_progPt b
    obtain ⟨tb', ub', rfl⟩ := exists_progPt b'
    obtain ⟨-, hob, hab⟩ := (cArg2_pt _ _ _ _).mp h1
    obtain ⟨-, hob', hab'⟩ := (cArg2_pt _ _ _ _).mp h2
    exact arg2_det hob hob' hab hab'

end Draw

end DescriptiveComplexity
