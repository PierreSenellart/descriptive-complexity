/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Iterate
import Mathlib.Data.Fintype.Pi

/-!
# The `k`-pebble refinement, over an abstract initial relation

The combinatorial core of `k`-variable equivalence `≡ᵏ`
([Abiteboul–Vianu 1991][abiteboul1991generic];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 3), with no logic in sight:
positions are `k`-tuples over a bare type `A`, an *initial relation* `E₀`
stands in for «same atomic type», and one round of the `k`-pebble game refines
a relation `E` to `DescriptiveComplexity.pebbleRefine E₀ E` – the pairs that
are in `E₀` and survive one exchange of a pebble
(`DescriptiveComplexity.PebbleBackForth`).

`DescriptiveComplexity.EquivK E₀` is the limit of the descending refinement
chain `DescriptiveComplexity.pebbleStage`, that is, the *greatest* fixed point
of the refinement:

* the chain plateaus within the number of pairs of tuples
  (`DescriptiveComplexity.pebbleStage_eq_stage_card`, the antitone half of
  `DescriptiveComplexity.exists_succ_eq_of_antitone_subset`), so on a finite
  type the limit is a stage and is itself a fixed point
  (`DescriptiveComplexity.equivK_iff`, the interface characterization);
* any relation below `E₀` that survives its own back-and-forth condition is
  below the limit (`DescriptiveComplexity.le_equivK`, the coinduction
  principle), which is what «greatest» means and how anything is ever proved
  `≡ᵏ`-equivalent;
* the limit is an equivalence relation whenever `E₀` is
  (`DescriptiveComplexity.equivK_equivalence`);
* refining the initial relation by anything the limit already refines does not
  change the limit (`DescriptiveComplexity.equivK_inf_eq`) – read with `E₀'`
  the agreement on a `≡ᵏ`-invariant relation, this is the *expansion* lemma:
  `≡ᵏ` is unchanged when the structure is expanded by an `≡ᵏ`-invariant
  relation. It is the lemma that carries the `≡ᵏ`-invariance of fixed-point
  logics, each stage of an induction being such an expansion.

Keeping `E₀` abstract keeps the vocabulary out: the instantiation at «same
atomic type over a structure» – necessarily over the *finitely many* symbols a
definition actually mentions – is where the logic enters, and lives with the
invariance results for the fixed-point logics, not here. The same skeleton
with rounds in place of pebbles is the Ehrenfeucht–Fraïssé refinement, a
second consumer this file is stated to serve.
-/

namespace DescriptiveComplexity

/-! ### Relations on `k`-tuples -/

/-- A relation between `k`-tuples over `A`: the positions of the `k`-pebble
game. -/
abbrev PebbleRel (A : Type) (k : ℕ) : Type :=
  (Fin k → A) → (Fin k → A) → Prop

variable {A : Type} {k : ℕ}

/-- Pointwise implication of relations on `k`-tuples, spelled out (the
lattice order, kept explicit per the conventions of this library). -/
def PebbleRel.Le (E E' : PebbleRel A k) : Prop :=
  ∀ a b : Fin k → A, E a b → E' a b

/-! ### One round of the game -/

/-- The back-and-forth condition of the `k`-pebble game relative to a
relation `E`: whichever pebble the spoiler moves, on whichever side, the
duplicator can move the same pebble on the other side and stay in `E`. -/
def PebbleBackForth (E : PebbleRel A k) : PebbleRel A k :=
  fun a b => ∀ i : Fin k,
    (∀ c : A, ∃ d : A, E (Function.update a i c) (Function.update b i d)) ∧
    (∀ d : A, ∃ c : A, E (Function.update a i c) (Function.update b i d))

/-- One round of refinement: agree initially, and survive one exchange of a
pebble relative to `E`. -/
def pebbleRefine (E₀ E : PebbleRel A k) : PebbleRel A k :=
  fun a b => E₀ a b ∧ PebbleBackForth E a b

/-- The back-and-forth condition is monotone in the relation it is relative
to. -/
theorem pebbleBackForth_mono {E E' : PebbleRel A k} (h : E.Le E') :
    (PebbleBackForth E).Le (PebbleBackForth E') := by
  intro a b hab i
  refine ⟨fun c => ?_, fun d => ?_⟩
  · obtain ⟨d, hd⟩ := (hab i).1 c
    exact ⟨d, h _ _ hd⟩
  · obtain ⟨c, hc⟩ := (hab i).2 d
    exact ⟨c, h _ _ hc⟩

/-- One round of refinement is monotone in the refined relation. -/
theorem pebbleRefine_mono (E₀ : PebbleRel A k) {E E' : PebbleRel A k} (h : E.Le E') :
    (pebbleRefine E₀ E).Le (pebbleRefine E₀ E') :=
  fun a b hab => ⟨hab.1, pebbleBackForth_mono h a b hab.2⟩

/-! ### The refinement chain and its limit -/

/-- The descending refinement chain, from the all-relation: what one round
cannot yet tell apart, twice refined, thrice refined, … -/
def pebbleStage (E₀ : PebbleRel A k) : ℕ → PebbleRel A k
  | 0 => fun _ _ => True
  | n + 1 => pebbleRefine E₀ (pebbleStage E₀ n)

/-- **`k`-equivalence relative to an initial relation**: the limit of the
refinement chain – equivalently (`DescriptiveComplexity.equivK_iff`,
`DescriptiveComplexity.le_equivK`) the greatest fixed point of one round of
refinement. -/
def EquivK (E₀ : PebbleRel A k) : PebbleRel A k :=
  fun a b => ∀ n, pebbleStage E₀ n a b

variable {E₀ : PebbleRel A k}

/-- The refinement chain descends. -/
theorem pebbleStage_succ_le (E₀ : PebbleRel A k) (n : ℕ) :
    (pebbleStage E₀ (n + 1)).Le (pebbleStage E₀ n) := by
  induction n with
  | zero => exact fun a b _ => trivial
  | succ n ih => exact pebbleRefine_mono E₀ ih

/-- The refinement chain descends, monotonically. -/
theorem pebbleStage_le_of_le (E₀ : PebbleRel A k) {m n : ℕ} (hmn : m ≤ n) :
    (pebbleStage E₀ n).Le (pebbleStage E₀ m) := by
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]; exact fun _ _ h => h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact fun a b h => ih (Nat.lt_succ_iff.mp hlt) a b (pebbleStage_succ_le E₀ n a b h)
    · rw [heq]; exact fun _ _ h => h

/-- The limit is below every stage. -/
theorem EquivK.stage {a b : Fin k → A} (h : EquivK E₀ a b) (n : ℕ) :
    pebbleStage E₀ n a b :=
  h n

/-- The limit is below the initial relation. -/
theorem EquivK.initial {a b : Fin k → A} (h : EquivK E₀ a b) : E₀ a b :=
  (h 1).1

/-! ### Coinduction: the limit is the greatest post-fixed point -/

/-- **The coinduction principle**: a relation below its own refinement is
below the limit. This is how tuples are ever proved `≡ᵏ`-equivalent – exhibit
a back-and-forth system containing the pair. -/
theorem le_equivK {E : PebbleRel A k} (h : E.Le (pebbleRefine E₀ E)) :
    E.Le (EquivK E₀) := by
  intro a b hab n
  induction n generalizing a b with
  | zero => trivial
  | succ n ih => exact pebbleRefine_mono E₀ ih a b (h a b hab)

/-! ### Stabilization on a finite type -/

section Finite

variable [Finite A]

/-- The refinement chain plateaus within the number of pairs of `k`-tuples:
consecutive stages agree from there on. -/
theorem exists_pebbleStage_succ_eq (E₀ : PebbleRel A k) :
    ∃ N ≤ Nat.card ((Fin k → A) × (Fin k → A)),
      pebbleStage E₀ (N + 1) = pebbleStage E₀ N := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_antitone_subset
    (c := fun n => {p : (Fin k → A) × (Fin k → A) | pebbleStage E₀ n p.1 p.2})
    (fun n p hp => pebbleStage_succ_le E₀ n p.1 p.2 hp)
  refine ⟨N, hN, ?_⟩
  funext a b
  exact propext ⟨fun h => (Set.ext_iff.mp heq (a, b)).mp h,
    fun h => (Set.ext_iff.mp heq (a, b)).mpr h⟩

omit [Finite A] in
private theorem pebbleStage_eq_of_succ_eq {N : ℕ}
    (hN : pebbleStage E₀ (N + 1) = pebbleStage E₀ N) {n : ℕ} (hn : N ≤ n) :
    pebbleStage E₀ n = pebbleStage E₀ N := by
  induction n with
  | zero => rw [Nat.le_zero.mp hn]
  | succ n ih =>
    rcases Nat.lt_or_ge N (n + 1) with h | h
    · have : pebbleStage E₀ n = pebbleStage E₀ N := ih (by omega)
      calc pebbleStage E₀ (n + 1) = pebbleRefine E₀ (pebbleStage E₀ n) := rfl
        _ = pebbleRefine E₀ (pebbleStage E₀ N) := by rw [this]
        _ = pebbleStage E₀ N := hN
    · rw [le_antisymm hn h]

/-- On a finite type, the limit is the stage at the number of pairs of
`k`-tuples. -/
theorem equivK_eq_stage_card (E₀ : PebbleRel A k) :
    EquivK E₀ = pebbleStage E₀ (Nat.card ((Fin k → A) × (Fin k → A))) := by
  obtain ⟨N, hle, hN⟩ := exists_pebbleStage_succ_eq E₀
  funext a b
  refine propext ⟨fun h => h _, fun h n => ?_⟩
  rcases Nat.le_total n (Nat.card ((Fin k → A) × (Fin k → A))) with hn | hn
  · exact pebbleStage_le_of_le E₀ hn a b h
  · rw [pebbleStage_eq_of_succ_eq hN (hle.trans hn),
      ← pebbleStage_eq_of_succ_eq hN hle]
    exact h

/-- **On a finite type the limit is a fixed point of the refinement** – the
greatest one, by `DescriptiveComplexity.le_equivK`. -/
theorem pebbleRefine_equivK (E₀ : PebbleRel A k) :
    pebbleRefine E₀ (EquivK E₀) = EquivK E₀ := by
  obtain ⟨N, hle, hN⟩ := exists_pebbleStage_succ_eq E₀
  have hlim : EquivK E₀ = pebbleStage E₀ N := by
    funext a b
    refine propext ⟨fun h => h N, fun h n => ?_⟩
    rcases Nat.le_total n N with hn | hn
    · exact pebbleStage_le_of_le E₀ hn a b h
    · rw [pebbleStage_eq_of_succ_eq hN hn]; exact h
  rw [hlim]
  exact hN

/-- **The interface characterization of `≡ᵏ` on a finite type**: initial
agreement together with the back-and-forth condition relative to `≡ᵏ`
itself. Consumers should use this, never the stages. -/
theorem equivK_iff (E₀ : PebbleRel A k) (a b : Fin k → A) :
    EquivK E₀ a b ↔ E₀ a b ∧ PebbleBackForth (EquivK E₀) a b := by
  conv_lhs => rw [← pebbleRefine_equivK E₀]
  exact Iff.rfl

/-- **The game move**: from an equivalent pair, moving a pebble on the left
can be answered on the right. -/
theorem EquivK.update {a b : Fin k → A} (h : EquivK E₀ a b) (i : Fin k) (c : A) :
    ∃ d : A, EquivK E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK_iff E₀ a b).mp h).2 i).1 c

/-- The game move, from the right. -/
theorem EquivK.update_right {a b : Fin k → A} (h : EquivK E₀ a b) (i : Fin k) (d : A) :
    ∃ c : A, EquivK E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK_iff E₀ a b).mp h).2 i).2 d

end Finite

/-! ### Equivalence -/

section Equivalence

/-- The back-and-forth condition preserves reflexivity. -/
theorem pebbleBackForth_refl {E : PebbleRel A k} (h : ∀ a, E a a) (a : Fin k → A) :
    PebbleBackForth E a a :=
  fun _ => ⟨fun c => ⟨c, h _⟩, fun d => ⟨d, h _⟩⟩

/-- The back-and-forth condition preserves symmetry. -/
theorem pebbleBackForth_symm {E : PebbleRel A k} (h : ∀ a b, E a b → E b a)
    {a b : Fin k → A} (hab : PebbleBackForth E a b) : PebbleBackForth E b a := by
  intro i
  refine ⟨fun c => ?_, fun d => ?_⟩
  · obtain ⟨d, hd⟩ := (hab i).2 c
    exact ⟨d, h _ _ hd⟩
  · obtain ⟨c, hc⟩ := (hab i).1 d
    exact ⟨c, h _ _ hc⟩

/-- The back-and-forth condition preserves transitivity. -/
theorem pebbleBackForth_trans {E : PebbleRel A k} (h : ∀ a b c, E a b → E b c → E a c)
    {a b c : Fin k → A} (hab : PebbleBackForth E a b) (hbc : PebbleBackForth E b c) :
    PebbleBackForth E a c := by
  intro i
  refine ⟨fun x => ?_, fun z => ?_⟩
  · obtain ⟨y, hy⟩ := (hab i).1 x
    obtain ⟨z, hz⟩ := (hbc i).1 y
    exact ⟨z, h _ _ _ hy hz⟩
  · obtain ⟨y, hy⟩ := (hbc i).2 z
    obtain ⟨x, hx⟩ := (hab i).2 y
    exact ⟨x, h _ _ _ hx hy⟩

/-- Every stage of the refinement chain of an equivalence is an
equivalence. -/
theorem pebbleStage_equivalence (hE₀ : Equivalence E₀) (n : ℕ) :
    Equivalence (pebbleStage E₀ n) := by
  induction n with
  | zero => exact ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  | succ n ih =>
    exact ⟨fun a => ⟨hE₀.refl a, pebbleBackForth_refl (fun x => ih.refl x) a⟩,
      fun hab => ⟨hE₀.symm hab.1, pebbleBackForth_symm (fun _ _ h => ih.symm h) hab.2⟩,
      fun hab hbc => ⟨hE₀.trans hab.1 hbc.1,
        pebbleBackForth_trans (E := pebbleStage E₀ n)
          (fun _ _ _ h h' => ih.trans h h') hab.2 hbc.2⟩⟩

/-- **`≡ᵏ` is an equivalence** whenever the initial relation is one. -/
theorem equivK_equivalence (hE₀ : Equivalence E₀) : Equivalence (EquivK E₀) :=
  ⟨fun a n => (pebbleStage_equivalence hE₀ n).refl a,
    fun h n => (pebbleStage_equivalence hE₀ n).symm (h n),
    fun hab hbc n => (pebbleStage_equivalence hE₀ n).trans (hab n) (hbc n)⟩

end Equivalence

/-! ### Monotonicity and the expansion lemma -/

/-- The stages are monotone in the initial relation. -/
theorem pebbleStage_mono {E₀ E₀' : PebbleRel A k} (h : E₀'.Le E₀) (n : ℕ) :
    (pebbleStage E₀' n).Le (pebbleStage E₀ n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    exact fun a b hab => ⟨h a b hab.1, pebbleBackForth_mono ih a b hab.2⟩

/-- `≡ᵏ` is monotone in the initial relation. -/
theorem equivK_mono {E₀ E₀' : PebbleRel A k} (h : E₀'.Le E₀) :
    (EquivK E₀').Le (EquivK E₀) :=
  fun a b hab n => pebbleStage_mono h n a b (hab n)

/-- **The expansion lemma**: refining the initial relation by anything `≡ᵏ`
already refines does not change `≡ᵏ`. Read with `E₀'` the conjunction of `E₀`
and agreement on an `≡ᵏ`-invariant relation, this says `≡ᵏ` is unchanged when
the structure is expanded by an `≡ᵏ`-invariant relation – the lemma that
carries the `≡ᵏ`-invariance of the fixed-point logics, stage by stage. -/
theorem equivK_inf_eq [Finite A] {E₀ E₀' : PebbleRel A k} (hle : E₀'.Le E₀)
    (hinv : (EquivK E₀).Le E₀') : EquivK E₀' = EquivK E₀ := by
  funext a b
  refine propext ⟨fun h => equivK_mono hle a b h, fun h => ?_⟩
  refine le_equivK (E₀ := E₀') (E := EquivK E₀) (fun a b hab => ?_) a b h
  exact ⟨hinv a b hab, ((equivK_iff E₀ a b).mp hab).2⟩

end DescriptiveComplexity
