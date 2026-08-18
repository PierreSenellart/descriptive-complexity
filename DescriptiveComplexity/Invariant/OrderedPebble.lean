/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.Pebble

/-!
# The canonical order on `≡ᵏ`-classes, as an inflationary refinement

The `k`-pebble refinement (`DescriptiveComplexity.Invariant.Pebble`) splits
classes round by round; this file runs the *ordered* version of the same
refinement: a strict order `DescriptiveComplexity.ordStage` on `k`-tuples
that grows round by round – tuples split apart become comparable, and stay
comparable for ever after. The initial data is a *coloring* `c₀` of the
tuples in a linear order (over a structure: the atomic type, read as a tuple
of bits); one round (`DescriptiveComplexity.ordRefine`) keeps the current
order and, inside one incomparability class, compares first the colors, then
the *move sets* – at the first pebble where they differ, the sets of current
classes reachable by moving that pebble, compared through their least
separating class (`DescriptiveComplexity.SetLess`).

The point of the construction, and the reason it is phrased as a growing
chain, is twofold:

* **its incomparability is exactly the pebble refinement**, stage by stage
  (the third component of `DescriptiveComplexity.ordStage_invariant`) and at
  the limit `DescriptiveComplexity.OrdK`, whose incomparability is `≡ᵏ`
  (`DescriptiveComplexity.incompRel_ordK_eq`); the limit is asymmetric and
  transitive (`DescriptiveComplexity.ordK_asymm`,
  `DescriptiveComplexity.ordK_trans`), and total across classes
  (`DescriptiveComplexity.ordK_or_of_not_equivK`) by the very definition of
  incomparability – a **canonical linear order on the `≡ᵏ`-classes**;
* **the chain is inflationary**, so it is computed by an inflationary
  fixed-point induction – one more relation variable alongside any other –
  and its canonicity (invariance under isomorphisms) is inherited from the
  transport of inflationary stages rather than proved by hand.

Everything is stated over a bare type and an abstract coloring, with no
vocabulary in sight, exactly as in `DescriptiveComplexity.Invariant.Pebble`;
the instantiation at the atomic coloring of a structure, and the first-order
definition of one round, live with the invariant structure.
-/

namespace DescriptiveComplexity

variable {A : Type} {k : ℕ} {β : Type*} [LinearOrder β]

/-! ### Incomparability, move sets, and set comparison -/

/-- Incomparability in a relation on `k`-tuples: the current classes. -/
def IncompRel (O : PebbleRel A k) : PebbleRel A k :=
  fun u v => ¬O u v ∧ ¬O v u

theorem IncompRel.symm {O : PebbleRel A k} {u v : Fin k → A}
    (h : IncompRel O u v) : IncompRel O v u :=
  ⟨h.2, h.1⟩

/-- The class of `x` belongs to the move set of `u` at pebble `j`: some move
of pebble `j` from `u` lands in the class of `x`. -/
def InMoves (O : PebbleRel A k) (j : Fin k) (u x : Fin k → A) : Prop :=
  ∃ a, IncompRel O (Function.update u j a) x

/-- The move sets of `u` and `v` at pebble `j` coincide. -/
def MovesEq (O : PebbleRel A k) (j : Fin k) (u v : Fin k → A) : Prop :=
  ∀ x, InMoves O j u x ↔ InMoves O j v x

/-- The class of `x` separates the move sets of `u` and `v` at pebble `j`. -/
def MovesDiff (O : PebbleRel A k) (j : Fin k) (u v x : Fin k → A) : Prop :=
  ¬(InMoves O j u x ↔ InMoves O j v x)

theorem MovesDiff.symm {O : PebbleRel A k} {j : Fin k} {u v x : Fin k → A}
    (h : MovesDiff O j u v x) : MovesDiff O j v u x :=
  fun hiff => h hiff.symm

/-- Comparison of move sets at pebble `j`: a class in the move set of `u` but
not of `v` is minimal among the separating classes. -/
def SetLess (O : PebbleRel A k) (j : Fin k) (u v : Fin k → A) : Prop :=
  ∃ x, InMoves O j u x ∧ ¬InMoves O j v x ∧ ∀ y, MovesDiff O j u v y → ¬O y x

/-- Lexicographic comparison of the move sets over the pebbles: equal before
some pebble, less at it. -/
def MovesLess (O : PebbleRel A k) (u v : Fin k → A) : Prop :=
  ∃ j, (∀ j' < j, MovesEq O j' u v) ∧ SetLess O j u v

/-! ### One round of the ordered refinement, and the chain -/

variable (c₀ : (Fin k → A) → β)

/-- Agreement on the coloring: the initial relation of the refinement. -/
def colorAgree : PebbleRel A k :=
  fun u v => c₀ u = c₀ v

omit [LinearOrder β] in
theorem colorAgree_equivalence : Equivalence (colorAgree c₀) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-- One round of the ordered refinement: keep the current order; inside one
incomparability class, compare the colors, then the move sets. -/
def ordRefine (O : PebbleRel A k) : PebbleRel A k :=
  fun u v => O u v ∨ (IncompRel O u v ∧
    (c₀ u < c₀ v ∨ (c₀ u = c₀ v ∧ MovesLess O u v)))

/-- The ordered refinement chain, from the empty order. -/
def ordStage : ℕ → PebbleRel A k
  | 0 => fun _ _ => False
  | n + 1 => ordRefine c₀ (ordStage n)

/-- **The canonical order**: the union of the ordered refinement chain. Its
incomparability is `≡ᵏ` (`DescriptiveComplexity.incompRel_ordK_eq`), and it
is transitive and asymmetric, so it is a linear order on the
`≡ᵏ`-classes. -/
def OrdK : PebbleRel A k :=
  fun u v => ∃ n, ordStage c₀ n u v

/-- The chain grows: one round only ever adds pairs. -/
theorem ordStage_le_succ (n : ℕ) {u v : Fin k → A} (h : ordStage c₀ n u v) :
    ordStage c₀ (n + 1) u v :=
  Or.inl h

/-- The chain grows, monotonically. -/
theorem ordStage_le_of_le {m n : ℕ} (hmn : m ≤ n) {u v : Fin k → A}
    (h : ordStage c₀ m u v) : ordStage c₀ n u v := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact ordStage_le_succ c₀ n (ih (Nat.lt_succ_iff.mp hlt))
    · rwa [heq] at h

/-! ### Structural lemmas

Each lemma of this section holds for any relation with the listed fragments
of the stage invariant – asymmetry, transitivity, transitivity of
incomparability – which the master induction
(`DescriptiveComplexity.ordStage_invariant`) establishes stage by stage. -/

section Structural

variable {O : PebbleRel A k}
variable (hasymm : ∀ u v : Fin k → A, O u v → ¬O v u)
variable (htrans : ∀ u v w : Fin k → A, O u v → O v w → O u w)
variable (hinc : ∀ u v w : Fin k → A,
  IncompRel O u v → IncompRel O v w → IncompRel O u w)

include htrans hinc in
/-- Comparability is a congruence for incomparability, on the right. -/
theorem IncompRel.congr_left {u v w : Fin k → A} (h : O u v)
    (hvw : IncompRel O v w) : O u w := by
  by_contra huw
  rcases Classical.em (O w u) with hwu | hwu
  · exact hvw.2 (htrans w u v hwu h)
  · exact (hinc u w v ⟨huw, hwu⟩ hvw.symm).1 h

include htrans hinc in
/-- Comparability is a congruence for incomparability, on the left. -/
theorem IncompRel.congr_right {u v w : Fin k → A} (huv : IncompRel O u v)
    (h : O v w) : O u w := by
  by_contra huw
  rcases Classical.em (O w u) with hwu | hwu
  · exact huv.2 (htrans v w u h hwu)
  · exact (hinc v u w huv.symm ⟨huw, hwu⟩).1 h

include hinc in
/-- Membership in a move set only depends on the class of the target. -/
theorem InMoves.congr {j : Fin k} {u x y : Fin k → A}
    (h : InMoves O j u x) (hxy : IncompRel O x y) : InMoves O j u y := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, hinc _ _ _ ha hxy⟩

include hasymm htrans in
/-- If the move sets differ, one compares below the other: the least
separating class lands on one of the two sides. -/
theorem setLess_or [Finite A] {j : Fin k} {u v : Fin k → A}
    (h : ¬MovesEq O j u v) : SetLess O j u v ∨ SetLess O j v u := by
  classical
  have hwf : WellFounded O := by
    let : IsTrans (Fin k → A) O := ⟨htrans⟩
    let : Std.Irrefl O := ⟨fun a ha => hasymm a a ha ha⟩
    exact Finite.wellFounded_of_trans_of_irrefl O
  have hne : {y : Fin k → A | MovesDiff O j u v y}.Nonempty := not_forall.mp h
  obtain ⟨m, hm, hmin⟩ := hwf.has_min _ hne
  rcases Classical.em (InMoves O j u m) with hu | hu
  · have hv : ¬InMoves O j v m := fun hv => hm (iff_of_true hu hv)
    exact Or.inl ⟨m, hu, hv, fun y hy => hmin y hy⟩
  · have hv : InMoves O j v m := by
      by_contra hv
      exact hm (iff_of_false hu hv)
    exact Or.inr ⟨m, hv, hu, fun y hy => hmin y hy.symm⟩

include hinc in
/-- Set comparison is asymmetric: the two candidate least separating classes
would be incomparable, hence equal as classes, hence on the same side. -/
theorem setLess_asymm {j : Fin k} {u v : Fin k → A} (h : SetLess O j u v) :
    ¬SetLess O j v u := by
  rintro ⟨y, hyv, hyu, hymin⟩
  obtain ⟨x, hxu, hxv, hxmin⟩ := h
  have hdx : MovesDiff O j u v x := fun hiff => hxv (hiff.mp hxu)
  have hdy : MovesDiff O j u v y := fun hiff => hyu (hiff.mpr hyv)
  have hxy : IncompRel O x y := ⟨hymin x hdx.symm, hxmin y hdy⟩
  exact hyu (InMoves.congr hinc hxu hxy)

/-- A separating class for `u, w` separates `u, v` or `v, w`. -/
private theorem movesDiff_trans {O : PebbleRel A k} {j : Fin k}
    {u w z : Fin k → A} (v : Fin k → A) (h : MovesDiff O j u w z) :
    MovesDiff O j u v z ∨ MovesDiff O j v w z := by
  rcases Classical.em (InMoves O j u z ↔ InMoves O j v z) with huv | huv
  · exact Or.inr fun hvw => h (huv.trans hvw)
  · exact Or.inl huv

/-- Set comparison is invariant under move-set equality on the right. -/
theorem SetLess.congr_right {O : PebbleRel A k} {j : Fin k} {u v w : Fin k → A}
    (h : SetLess O j u v) (hvw : MovesEq O j v w) : SetLess O j u w := by
  obtain ⟨x, hxu, hxv, hxmin⟩ := h
  refine ⟨x, hxu, fun hxw => hxv ((hvw x).mpr hxw), fun y hy => hxmin y ?_⟩
  exact fun hiff => hy (hiff.trans (hvw y))

/-- Set comparison is invariant under move-set equality on the left. -/
theorem SetLess.congr_left {O : PebbleRel A k} {j : Fin k} {u v w : Fin k → A}
    (huv : MovesEq O j u v) (h : SetLess O j v w) : SetLess O j u w := by
  obtain ⟨x, hxv, hxw, hxmin⟩ := h
  refine ⟨x, (huv x).mpr hxv, hxw, fun y hy => hxmin y ?_⟩
  exact fun hiff => hy ((huv y).trans hiff)

include htrans hinc in
/-- Set comparison is transitive: compare the two least separating classes,
and reuse the smaller one. -/
theorem setLess_trans {j : Fin k} {u v w : Fin k → A}
    (h₁ : SetLess O j u v) (h₂ : SetLess O j v w) : SetLess O j u w := by
  obtain ⟨a, hau, hav, hamin⟩ := h₁
  obtain ⟨b, hbv, hbw, hbmin⟩ := h₂
  rcases Classical.em (O a b) with hab | hab
  · -- `a` stays the least separating class of `u, w`
    refine ⟨a, hau, fun haw => ?_, fun z hz => ?_⟩
    · exact hbmin a (fun hiff => hav (hiff.mpr haw)) hab
    · rcases movesDiff_trans v hz with hz' | hz'
      · exact hamin z hz'
      · exact fun hza => hbmin z hz' (htrans z a b hza hab)
  · rcases Classical.em (O b a) with hba | hba
    · -- `b` takes over as the least separating class of `u, w`
      refine ⟨b, ?_, hbw, fun z hz => ?_⟩
      · by_contra hbu
        exact hamin b (fun hiff => hbu (hiff.mpr hbv)) hba
      · rcases movesDiff_trans v hz with hz' | hz'
        · exact fun hzb => hamin z hz' (htrans z b a hzb hba)
        · exact hbmin z hz'
    · -- incomparable candidates are the same class: contradiction at `v`
      exact absurd (InMoves.congr hinc hbv ⟨hba, hab⟩) hav

/-- Move-set equality contradicts set comparison at the same pebble. -/
theorem SetLess.not_movesEq {O : PebbleRel A k} {j : Fin k} {u v : Fin k → A}
    (h : SetLess O j u v) (heq : MovesEq O j u v) : False := by
  obtain ⟨x, hxu, hxv, -⟩ := h
  exact hxv ((heq x).mp hxu)

include hinc in
/-- Lexicographic move-set comparison is asymmetric. -/
theorem movesLess_asymm {u v : Fin k → A} (h : MovesLess O u v) :
    ¬MovesLess O v u := by
  rintro ⟨j₂, hpre₂, hless₂⟩
  obtain ⟨j₁, hpre₁, hless₁⟩ := h
  rcases lt_trichotomy j₁ j₂ with hlt | heq | hlt
  · exact hless₁.not_movesEq fun x => (hpre₂ j₁ hlt x).symm
  · subst heq
    exact setLess_asymm hinc hless₁ hless₂
  · exact hless₂.not_movesEq fun x => (hpre₁ j₂ hlt x).symm

include htrans hinc in
/-- Lexicographic move-set comparison is transitive. -/
theorem movesLess_trans {u v w : Fin k → A} (h₁ : MovesLess O u v)
    (h₂ : MovesLess O v w) : MovesLess O u w := by
  obtain ⟨j₁, hpre₁, hless₁⟩ := h₁
  obtain ⟨j₂, hpre₂, hless₂⟩ := h₂
  rcases lt_trichotomy j₁ j₂ with hlt | heq | hlt
  · refine ⟨j₁, fun j' hj' x => ?_, hless₁.congr_right (hpre₂ j₁ hlt)⟩
    exact (hpre₁ j' hj' x).trans (hpre₂ j' (hj'.trans hlt) x)
  · subst heq
    refine ⟨j₁, fun j' hj' x => (hpre₁ j' hj' x).trans (hpre₂ j' hj' x), ?_⟩
    exact setLess_trans htrans hinc hless₁ hless₂
  · refine ⟨j₂, fun j' hj' x => ?_, SetLess.congr_left (hpre₁ j₂ hlt) hless₂⟩
    exact (hpre₁ j' (hj'.trans hlt) x).trans (hpre₂ j' hj' x)

include hasymm htrans in
/-- If the move sets differ at some pebble, the tuples compare one way or the
other lexicographically: cut at the first differing pebble. -/
theorem movesLess_or [Finite A] {u v : Fin k → A} (h : ¬∀ j, MovesEq O j u v) :
    MovesLess O u v ∨ MovesLess O v u := by
  classical
  have hne : {j : Fin k | ¬MovesEq O j u v}.Nonempty := not_forall.mp h
  obtain ⟨j₀, hj₀, hmin⟩ := (wellFounded_lt (α := Fin k)).has_min _ hne
  have hpre : ∀ j' < j₀, MovesEq O j' u v := by
    intro j' hj'
    by_contra hbad
    exact hmin j' hbad hj'
  rcases setLess_or hasymm htrans hj₀ with hless | hless
  · exact Or.inl ⟨j₀, hpre, hless⟩
  · exact Or.inr ⟨j₀, fun j' hj' x => (hpre j' hj' x).symm, hless⟩

end Structural

/-! ### The stage invariant -/

section Invariant

variable [Finite A]

/-- **The stage invariant of the ordered refinement**: every stage is
asymmetric and transitive, and its incomparability is the corresponding
pebble stage relative to color agreement. One simultaneous induction
establishes all three. -/
theorem ordStage_invariant (n : ℕ) :
    (∀ u v : Fin k → A, ordStage c₀ n u v → ¬ordStage c₀ n v u) ∧
    (∀ u v w : Fin k → A, ordStage c₀ n u v → ordStage c₀ n v w →
      ordStage c₀ n u w) ∧
    IncompRel (ordStage c₀ n) = pebbleStage (colorAgree c₀) n := by
  induction n with
  | zero =>
    refine ⟨fun u v h => h.elim, fun u v w h => h.elim, ?_⟩
    funext u v
    exact propext (iff_of_true ⟨not_false, not_false⟩ trivial)
  | succ n ih =>
    obtain ⟨ha, ht, hI⟩ := ih
    have hPeq : Equivalence (pebbleStage (colorAgree c₀) n) :=
      pebbleStage_equivalence (colorAgree_equivalence c₀) n
    have hinc : ∀ u v w : Fin k → A, IncompRel (ordStage c₀ n) u v →
        IncompRel (ordStage c₀ n) v w → IncompRel (ordStage c₀ n) u w := by
      intro u v w huv hvw
      rw [hI] at huv hvw ⊢
      exact hPeq.trans huv hvw
    have hIrefl : ∀ u : Fin k → A, IncompRel (ordStage c₀ n) u u := by
      intro u
      rw [hI]
      exact hPeq.refl u
    refine ⟨?_, ?_, ?_⟩
    · -- asymmetry
      rintro u v (huv | ⟨hiuv, hduv⟩) (hvu | ⟨hivu, hdvu⟩)
      · exact ha u v huv hvu
      · exact hivu.2 huv
      · exact hiuv.2 hvu
      · rcases hduv with hlt | ⟨heq, hml⟩ <;> rcases hdvu with hlt' | ⟨heq', hml'⟩
        · exact lt_asymm hlt hlt'
        · exact ne_of_gt hlt heq'
        · exact ne_of_gt hlt' heq
        · exact movesLess_asymm hinc hml hml'
    · -- transitivity
      rintro u v w (huv | ⟨hiuv, hduv⟩) (hvw | ⟨hivw, hdvw⟩)
      · exact Or.inl (ht u v w huv hvw)
      · exact Or.inl (IncompRel.congr_left ht hinc huv hivw)
      · exact Or.inl (IncompRel.congr_right ht hinc hiuv hvw)
      · refine Or.inr ⟨hinc u v w hiuv hivw, ?_⟩
        rcases hduv with hlt | ⟨heq, hml⟩ <;> rcases hdvw with hlt' | ⟨heq', hml'⟩
        · exact Or.inl (hlt.trans hlt')
        · exact Or.inl (lt_of_lt_of_le hlt (le_of_eq heq'))
        · exact Or.inl (lt_of_le_of_lt (le_of_eq heq) hlt')
        · exact Or.inr ⟨heq.trans heq', movesLess_trans ht hinc hml hml'⟩
    · -- incomparability is the next pebble stage
      funext u v
      refine propext ?_
      have hpeel : IncompRel (ordStage c₀ (n + 1)) u v ↔
          (IncompRel (ordStage c₀ n) u v ∧
            ¬(c₀ u < c₀ v ∨ (c₀ u = c₀ v ∧ MovesLess (ordStage c₀ n) u v)) ∧
            ¬(c₀ v < c₀ u ∨ (c₀ v = c₀ u ∧ MovesLess (ordStage c₀ n) v u))) := by
        constructor
        · rintro ⟨h1, h2⟩
          have hn1 : ¬ordStage c₀ n u v := fun h => h1 (Or.inl h)
          have hn2 : ¬ordStage c₀ n v u := fun h => h2 (Or.inl h)
          exact ⟨⟨hn1, hn2⟩, fun hd => h1 (Or.inr ⟨⟨hn1, hn2⟩, hd⟩),
            fun hd => h2 (Or.inr ⟨⟨hn2, hn1⟩, hd⟩)⟩
        · rintro ⟨hi, hd1, hd2⟩
          constructor
          · rintro (h | ⟨-, hd⟩)
            · exact hi.1 h
            · exact hd1 hd
          · rintro (h | ⟨-, hd⟩)
            · exact hi.2 h
            · exact hd2 hd
      rw [hpeel]
      change _ ↔ pebbleRefine (colorAgree c₀) (pebbleStage (colorAgree c₀) n) u v
      constructor
      · rintro ⟨hi, hd1, hd2⟩
        have hd1' : ¬(c₀ u < c₀ v) ∧
            (c₀ u = c₀ v → ¬MovesLess (ordStage c₀ n) u v) :=
          ⟨fun hlt => hd1 (Or.inl hlt), fun heq hml => hd1 (Or.inr ⟨heq, hml⟩)⟩
        have hd2' : ¬(c₀ v < c₀ u) ∧
            (c₀ v = c₀ u → ¬MovesLess (ordStage c₀ n) v u) :=
          ⟨fun hlt => hd2 (Or.inl hlt), fun heq hml => hd2 (Or.inr ⟨heq, hml⟩)⟩
        have heq : c₀ u = c₀ v := le_antisymm (not_lt.mp hd2'.1) (not_lt.mp hd1'.1)
        have hmeq : ∀ j, MovesEq (ordStage c₀ n) j u v := by
          by_contra hne
          rcases movesLess_or ha ht hne with hml | hml
          · exact hd1'.2 heq hml
          · exact hd2'.2 heq.symm hml
        refine ⟨heq, fun i => ⟨fun c => ?_, fun d => ?_⟩⟩
        · have hx : InMoves (ordStage c₀ n) i u (Function.update u i c) :=
            ⟨c, hIrefl _⟩
          obtain ⟨d, hd⟩ := (hmeq i (Function.update u i c)).mp hx
          refine ⟨d, ?_⟩
          rw [← hI]
          exact hd.symm
        · have hx : InMoves (ordStage c₀ n) i v (Function.update v i d) :=
            ⟨d, hIrefl _⟩
          obtain ⟨c, hc⟩ := (hmeq i (Function.update v i d)).mpr hx
          refine ⟨c, ?_⟩
          rw [← hI]
          exact hc
      · rintro ⟨heq, hbf⟩
        have hi : IncompRel (ordStage c₀ n) u v := by
          rw [hI]
          exact pebbleStage_succ_le (colorAgree c₀) n u v ⟨heq, hbf⟩
        have hmeq : ∀ j, MovesEq (ordStage c₀ n) j u v := by
          intro j x
          constructor
          · rintro ⟨a, ha'⟩
            obtain ⟨b, hb⟩ := (hbf j).1 a
            have hb' : IncompRel (ordStage c₀ n) (Function.update u j a)
                (Function.update v j b) := by rw [hI]; exact hb
            exact ⟨b, hinc _ _ _ hb'.symm ha'⟩
          · rintro ⟨b, hb'⟩
            obtain ⟨a, ha'⟩ := (hbf j).2 b
            have ha'' : IncompRel (ordStage c₀ n) (Function.update u j a)
                (Function.update v j b) := by rw [hI]; exact ha'
            exact ⟨a, hinc _ _ _ ha'' hb'⟩
        refine ⟨hi, ?_, ?_⟩
        · rintro (hlt | ⟨-, hml⟩)
          · exact ne_of_lt hlt heq
          · obtain ⟨j, -, hless⟩ := hml
            exact hless.not_movesEq (hmeq j)
        · rintro (hlt | ⟨-, hml⟩)
          · exact ne_of_lt hlt heq.symm
          · obtain ⟨j, -, hless⟩ := hml
            exact hless.not_movesEq fun x => (hmeq j x).symm

/-! ### The limit -/

/-- The canonical order is asymmetric. -/
theorem ordK_asymm {u v : Fin k → A} (h : OrdK c₀ u v) : ¬OrdK c₀ v u := by
  obtain ⟨n, hn⟩ := h
  rintro ⟨m, hm⟩
  exact (ordStage_invariant c₀ (max n m)).1 u v
    (ordStage_le_of_le c₀ (le_max_left n m) hn)
    (ordStage_le_of_le c₀ (le_max_right n m) hm)

/-- The canonical order is transitive. -/
theorem ordK_trans {u v w : Fin k → A} (h₁ : OrdK c₀ u v) (h₂ : OrdK c₀ v w) :
    OrdK c₀ u w := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨max n m, (ordStage_invariant c₀ (max n m)).2.1 u v w
    (ordStage_le_of_le c₀ (le_max_left n m) hn)
    (ordStage_le_of_le c₀ (le_max_right n m) hm)⟩

/-- **Incomparability in the canonical order is `≡ᵏ`**: the limit linearly
orders the `≡ᵏ`-classes. -/
theorem incompRel_ordK_eq :
    IncompRel (OrdK c₀) = EquivK (colorAgree c₀) := by
  funext u v
  refine propext ⟨fun h n => ?_, fun h => ?_⟩
  · rw [← (ordStage_invariant c₀ n).2.2]
    exact ⟨fun hn => h.1 ⟨n, hn⟩, fun hn => h.2 ⟨n, hn⟩⟩
  · constructor
    · rintro ⟨n, hn⟩
      have := h n
      rw [← (ordStage_invariant c₀ n).2.2] at this
      exact this.1 hn
    · rintro ⟨n, hn⟩
      have := h n
      rw [← (ordStage_invariant c₀ n).2.2] at this
      exact this.2 hn

/-- Inequivalent tuples are comparable in the canonical order. -/
theorem ordK_or_of_not_equivK {u v : Fin k → A}
    (h : ¬EquivK (colorAgree c₀) u v) : OrdK c₀ u v ∨ OrdK c₀ v u := by
  by_contra hc
  have hi : IncompRel (OrdK c₀) u v :=
    ⟨fun h1 => hc (Or.inl h1), fun h2 => hc (Or.inr h2)⟩
  rw [incompRel_ordK_eq] at hi
  exact h hi

/-- Incomparability in the canonical order is transitive. -/
theorem incompRel_ordK_trans {u v w : Fin k → A}
    (h₁ : IncompRel (OrdK c₀) u v) (h₂ : IncompRel (OrdK c₀) v w) :
    IncompRel (OrdK c₀) u w := by
  rw [incompRel_ordK_eq] at h₁ h₂ ⊢
  exact (equivK_equivalence (colorAgree_equivalence c₀)).trans h₁ h₂

/-- The canonical order is a congruence for `≡ᵏ` on the right. -/
theorem OrdK.congr_left {u v w : Fin k → A} (h : OrdK c₀ u v)
    (hvw : EquivK (colorAgree c₀) v w) : OrdK c₀ u w := by
  have hvw' : IncompRel (OrdK c₀) v w := by
    rw [incompRel_ordK_eq]
    exact hvw
  exact IncompRel.congr_left (O := OrdK c₀)
    (fun a b c h1 h2 => ordK_trans c₀ h1 h2)
    (fun a b c h1 h2 => incompRel_ordK_trans c₀ h1 h2) h hvw'

/-- The canonical order is a congruence for `≡ᵏ` on the left. -/
theorem OrdK.congr_right {u v w : Fin k → A} (huv : EquivK (colorAgree c₀) u v)
    (h : OrdK c₀ v w) : OrdK c₀ u w := by
  have huv' : IncompRel (OrdK c₀) u v := by
    rw [incompRel_ordK_eq]
    exact huv
  exact IncompRel.congr_right (O := OrdK c₀)
    (fun a b c h1 h2 => ordK_trans c₀ h1 h2)
    (fun a b c h1 h2 => incompRel_ordK_trans c₀ h1 h2) huv' h

end Invariant

end DescriptiveComplexity
