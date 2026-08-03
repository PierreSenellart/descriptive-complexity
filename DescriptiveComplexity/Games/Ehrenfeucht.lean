/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.EquivK

/-!
# Ehrenfeucht–Fraïssé games on finite structures

The graded back-and-forth refinement between *two* structures
([Ehrenfeucht 1961][ehrenfeucht1961application];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 2), and the one lemma the
whole inexpressibility toolkit rests on: surviving `n` rounds implies agreeing
on every sentence of quantifier rank at most `n`
(`DescriptiveComplexity.realize_efStage`), so a property distinguishing two
structures the duplicator can play forever is not first-order.

A position (`DescriptiveComplexity.PartialIso`) is a pair of tuples of equal
length, one on each side, satisfying the same equalities between coordinates
and the same base relations at every selection of coordinates – agreement on
the atomic type (`DescriptiveComplexity.atomicAgreeOn`) read across two
structures. A round appends one element, chosen on either side by the spoiler
and answered on the other by the duplicator, and
`DescriptiveComplexity.efStage L n` is the set of positions from which the
duplicator survives `n` of them.

The stages are *not* an instance of the abstract pebble refinement
(`DescriptiveComplexity.Invariant.Pebble`), although the two chains look
alike: there the two tuples live in the same structure and a round *replaces*
one of `k` fixed pebbles, here they live in two different structures – the
spoiler's move is a quantifier over one of them, the duplicator's answer a
quantifier over the other – and a round *appends* a coordinate, so a position
is not a point of a fixed relation but of a family indexed by the number of
rounds already played. What the two do share is the measure they are graded
by, `DescriptiveComplexity.qdepth`, and the shape of the proof: the atomic
case is settled by the position, the quantifier case by one round of the game.
The vocabulary is relational, as everywhere in this library, so that atomic
formulas read coordinates rather than terms
(`DescriptiveComplexity.exists_eq_var_of_isRelational`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]

/-! ### Positions -/

/-- A **legal position** of the Ehrenfeucht–Fraïssé game: two tuples of equal
length, one on each side, satisfying the same equalities between their
coordinates and the same base relations at every selection of coordinates.
Equivalently, matching coordinate to coordinate is a partial isomorphism.

This is `DescriptiveComplexity.atomicAgreeOn` read across two structures, and
over the *whole* vocabulary: unlike the `≡ᵏ` layer, which must restrict to the
symbols a definition mentions to stay definable, a game plays against one
sentence at a time and nothing here has to be defined by a formula. -/
def PartialIso (L : Language.{0, 0}) {M N : Type} [L.Structure M] [L.Structure N] {j : ℕ}
    (a : Fin j → M) (b : Fin j → N) : Prop :=
  (∀ i i' : Fin j, a i = a i' ↔ b i = b i') ∧
    ∀ (l : ℕ) (R : L.Relations l) (g : Fin l → Fin j),
      ((RelMap R fun p => a (g p)) ↔ RelMap R fun p => b (g p))

/-- A legal position read from the other side is legal. -/
theorem PartialIso.symm {j : ℕ} {a : Fin j → M} {b : Fin j → N}
    (h : PartialIso L a b) : PartialIso L b a :=
  ⟨fun i i' => (h.1 i i').symm, fun l R g => (h.2 l R g).symm⟩

/-! ### The refinement chain -/

/-- **The stages of the Ehrenfeucht–Fraïssé refinement**: `efStage L n a b`
says that from the position `(a, b)` the duplicator survives `n` further
rounds – the position is legal, and whichever element the spoiler appends on
either side, the duplicator can append one on the other and survive `n - 1`
more rounds.

The chain descends (`DescriptiveComplexity.efStage_le`), so the stage index is
a *budget*: a position surviving `n` rounds survives fewer. -/
def efStage (L : Language.{0, 0}) {M N : Type} [L.Structure M] [L.Structure N] :
    ℕ → ∀ {j : ℕ}, (Fin j → M) → (Fin j → N) → Prop
  | 0, _, a, b => PartialIso L a b
  | n + 1, _, a, b =>
      PartialIso L a b ∧
        (∀ c : M, ∃ d : N, efStage L n (Fin.snoc a c) (Fin.snoc b d)) ∧
        (∀ d : N, ∃ c : M, efStage L n (Fin.snoc a c) (Fin.snoc b d))

variable {n j : ℕ} {a : Fin j → M} {b : Fin j → N}

/-- A position from which the duplicator survives any number of rounds is
legal. -/
theorem efStage.partialIso : ∀ {n : ℕ}, efStage L n a b → PartialIso L a b
  | 0, h => h
  | _ + 1, h => h.1

/-- **The spoiler moves on the left**: from a position surviving `n + 1`
rounds, an element appended on the left is answered on the right. -/
theorem efStage.forth (h : efStage L (n + 1) a b) (c : M) :
    ∃ d : N, efStage L n (Fin.snoc a c) (Fin.snoc b d) :=
  h.2.1 c

/-- **The spoiler moves on the right**: from a position surviving `n + 1`
rounds, an element appended on the right is answered on the left. -/
theorem efStage.back (h : efStage L (n + 1) a b) (d : N) :
    ∃ c : M, efStage L n (Fin.snoc a c) (Fin.snoc b d) :=
  h.2.2 d

/-- The refinement chain descends: surviving one more round is a stronger
requirement. -/
theorem efStage_succ_le : ∀ (n : ℕ) {j : ℕ} {a : Fin j → M} {b : Fin j → N},
    efStage L (n + 1) a b → efStage L n a b
  | 0, _, _, _, h => h.1
  | n + 1, _, _, _, h =>
      ⟨h.1, fun c => (h.forth c).imp fun _ hd => efStage_succ_le n hd,
        fun d => (h.back d).imp fun _ hc => efStage_succ_le n hc⟩

/-- The refinement chain descends, monotonically. -/
theorem efStage_le {m : ℕ} (hmn : m ≤ n) (h : efStage L n a b) : efStage L m a b := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact ih (Nat.lt_succ_iff.mp hlt) (efStage_succ_le n h)
    · exact heq ▸ h

/-- Positions surviving `n` rounds, read from the other side. -/
theorem efStage.symm : ∀ {n : ℕ} {j : ℕ} {a : Fin j → M} {b : Fin j → N},
    efStage L n a b → efStage L n b a := by
  intro n
  induction n with
  | zero => intro _ _ _ h; exact PartialIso.symm h
  | succ n ih =>
    intro _ _ _ h
    exact ⟨PartialIso.symm h.1, fun d => (h.back d).imp fun _ hc => ih hc,
      fun c => (h.forth c).imp fun _ hd => ih hd⟩

/-! ### `n`-round equivalence of structures -/

/-- **`n`-round equivalence**: the duplicator survives `n` rounds of the
Ehrenfeucht–Fraïssé game on `M` and `N` played from the empty position. -/
def EFEquiv (L : Language.{0, 0}) (M N : Type) [L.Structure M] [L.Structure N] (n : ℕ) : Prop :=
  efStage L n (default : Fin 0 → M) (default : Fin 0 → N)

/-- `n`-round equivalence is symmetric. -/
theorem EFEquiv.symm (h : EFEquiv L M N n) : EFEquiv L N M n :=
  efStage.symm h

/-- `n`-round equivalence is antitone in the number of rounds. -/
theorem EFEquiv.mono {m : ℕ} (hmn : m ≤ n) (h : EFEquiv L M N n) : EFEquiv L M N m :=
  efStage_le hmn h

/-! ### The methodology lemma -/

section Relational

variable [L.IsRelational]

/-- **The Ehrenfeucht–Fraïssé method.** A formula whose quantifier rank fits
in the duplicator's remaining budget cannot separate the two sides of a
position: each quantifier spends one round of the game, and atomic formulas
are decided by the position itself.

The free-variable context is empty (`Empty`): the tuples of the position play
the role of the free variables, exactly as the bound variables of Mathlib's
`FirstOrder.Language.BoundedFormula` are read off the valuation tuple. -/
theorem realize_efStage : ∀ {j : ℕ} (φ : L.BoundedFormula Empty j) {n : ℕ}, qdepth φ ≤ n →
    ∀ {a : Fin j → M} {b : Fin j → N}, efStage L n a b →
      (φ.Realize default a ↔ φ.Realize default b) := by
  intro j φ
  induction φ with
  | falsum =>
    intro _ _ _ _ _
    exact Iff.rfl
  | @equal n t₁ t₂ =>
    intro _ _ a b h
    obtain ⟨x₁, rfl⟩ := exists_eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := exists_eq_var_of_isRelational t₂
    rcases x₁ with e | i₁
    · exact e.elim
    rcases x₂ with e | i₂
    · exact e.elim
    exact h.partialIso.1 i₁ i₂
  | @rel n l R ts =>
    intro _ _ a b h
    have hts : ∀ p, ∃ i : Fin n, ts p = Term.var (Sum.inr i) := by
      intro p
      obtain ⟨x, hx⟩ := exists_eq_var_of_isRelational (ts p)
      rcases x with e | i
      · exact e.elim
      · exact ⟨i, hx⟩
    choose g hg using hts
    have hsub : ts = fun p => Term.var (Sum.inr (g p)) := funext hg
    subst hsub
    exact h.partialIso.2 l R g
  | @imp n f₁ f₂ ih₁ ih₂ =>
    intro m hm a b h
    simp only [qdepth] at hm
    exact imp_congr (ih₁ (le_trans (le_max_left _ _) hm) h)
      (ih₂ (le_trans (le_max_right _ _) hm) h)
  | @all n ψ ih =>
    intro m hm a b h
    simp only [qdepth] at hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hψ : qdepth ψ ≤ m := by omega
    rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
    constructor
    · intro hall d
      obtain ⟨c, hc⟩ := h.back d
      exact (ih hψ hc).mp (hall c)
    · intro hall c
      obtain ⟨d, hd⟩ := h.forth c
      exact (ih hψ hd).mpr (hall d)

/-- **The methodology lemma**: `n`-round equivalent structures satisfy the
same sentences of quantifier rank at most `n`. Everything the inexpressibility
toolkit proves is a contrapositive of this. -/
theorem realize_sentence_of_efEquiv (h : EFEquiv L M N n) (φ : L.Sentence)
    (hφ : qdepth φ ≤ n) : M ⊨ φ ↔ N ⊨ φ :=
  realize_efStage φ hφ h

end Relational

end DescriptiveComplexity
