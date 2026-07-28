/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation

/-!
# Savitch's recursive doubling

The combinatorial half of Savitch's theorem ([Savitch 1970][savitch1970relationships]),
stated for an arbitrary relation and independent of any logic: reachability in a
graph whose vertices are only known *up to a classifying map* into a finite type.

The setting is a relation `R` on a type `St` of *presentations*, together with a
map `cls : St → T` into a finite type of *classes*, such that `R` only depends on
its endpoints through their classes (`DescriptiveComplexity.SavInv`). That extra
generality is what the reduction of SUCCINCT-REACH to QSAT needs: a state of a
succinctly described transition system is a predicate on the whole universe, but
the clauses only read it on the state variables, so the honest vertex set is the
(finite) quotient.

Three notions of bounded reachability live here:

* `DescriptiveComplexity.SavStep`: one move – a step of `R`, or standing still
  inside a class;
* `DescriptiveComplexity.SavLe n`: at most `n` moves, the linear staging;
* `DescriptiveComplexity.SavPow k`: Savitch's staging, `ψ_{k+1}(X, Y) = ∃Z,
  ψ_k(X, Z) ∧ ψ_k(Z, Y)`, which unfolds into a formula of *depth* `k` rather
  than length `2 ^ k`.

The two stagings agree, `DescriptiveComplexity.savPow_iff_savLe` : `SavPow k =
SavLe (2 ^ k)`, and the pigeonhole `DescriptiveComplexity.savLe_card` says that
`SavLe` saturates at `Nat.card T` moves – a walk that revisits a class can be
shortened. Together they give the statement a reduction uses,
`DescriptiveComplexity.savPow_of_reflTransGen`: as soon as `2 ^ k` classes are
enough, `SavPow k` *is* reachability.
-/

namespace DescriptiveComplexity

variable {St T : Type}

/-! ### Moves, and the two stagings -/

/-- One move of the walk: a step of `R`, or standing still inside a class. The
reflexive part is `cls`-equality rather than equality because a class, not a
presentation, is what the walk really visits. -/
def SavStep (cls : St → T) (R : St → St → Prop) (X Y : St) : Prop :=
  cls X = cls Y ∨ R X Y

/-- Reachability in **at most `n` moves**: the linear staging. -/
def SavLe (cls : St → T) (R : St → St → Prop) : ℕ → St → St → Prop
  | 0 => fun X Y => cls X = cls Y
  | n + 1 => fun X Y => ∃ Z, SavLe cls R n X Z ∧ SavStep cls R Z Y

/-- **Savitch's staging**: `SavPow k` is “reachable through a midpoint, twice at
level `k - 1`”, which is reachability in at most `2 ^ k` moves
(`DescriptiveComplexity.savPow_iff_savLe`) written with `k` nested midpoints. -/
def SavPow (cls : St → T) (R : St → St → Prop) : ℕ → St → St → Prop
  | 0 => SavStep cls R
  | k + 1 => fun X Y => ∃ Z, SavPow cls R k X Z ∧ SavPow cls R k Z Y

/-- The walk only depends on its endpoints through their classes: the hypothesis
that makes the classes, rather than the presentations, the vertices. -/
def SavInv (cls : St → T) (R : St → St → Prop) : Prop :=
  ∀ X X' Y Y' : St, cls X = cls X' → cls Y = cls Y' → R X Y → R X' Y'

/-! ### Class-invariance of the stagings -/

section Congr

variable {cls : St → T} {R : St → St → Prop}

theorem savStep_congr (h : SavInv cls R) {X X' Y Y' : St} (hX : cls X = cls X')
    (hY : cls Y = cls Y') (hs : SavStep cls R X Y) : SavStep cls R X' Y' := by
  rcases hs with he | hr
  · exact Or.inl (hX ▸ hY ▸ he)
  · exact Or.inr (h X X' Y Y' hX hY hr)

theorem savLe_congr (h : SavInv cls R) :
    ∀ (n : ℕ) {X X' Y Y' : St}, cls X = cls X' → cls Y = cls Y' →
      SavLe cls R n X Y → SavLe cls R n X' Y' := by
  intro n
  induction n with
  | zero => exact fun hX hY he => hX.symm.trans (he.trans hY)
  | succ n ih =>
    rintro X X' Y Y' hX hY ⟨Z, hZ, hs⟩
    exact ⟨Z, ih hX rfl hZ, savStep_congr h rfl hY hs⟩

theorem savPow_congr (h : SavInv cls R) :
    ∀ (k : ℕ) {X X' Y Y' : St}, cls X = cls X' → cls Y = cls Y' →
      SavPow cls R k X Y → SavPow cls R k X' Y' := by
  intro k
  induction k with
  | zero => exact fun hX hY hs => savStep_congr h hX hY hs
  | succ k ih =>
    rintro X X' Y Y' hX hY ⟨Z, h1, h2⟩
    exact ⟨Z, ih hX rfl h1, ih rfl hY h2⟩

end Congr

/-! ### The linear staging -/

section Linear

variable {cls : St → T} {R : St → St → Prop}

theorem savLe_succ {n : ℕ} {X Y : St} (hs : SavLe cls R n X Y) : SavLe cls R (n + 1) X Y :=
  ⟨Y, hs, Or.inl rfl⟩

theorem savLe_of_le {m n : ℕ} (hmn : m ≤ n) {X Y : St} (hs : SavLe cls R m X Y) :
    SavLe cls R n X Y := by
  induction n with
  | zero => exact Nat.le_zero.mp hmn ▸ hs
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact savLe_succ (ih (Nat.lt_succ_iff.mp hlt))
    · exact heq ▸ hs

theorem savLe_of_savStep {X Y : St} (hs : SavStep cls R X Y) : SavLe cls R 1 X Y :=
  ⟨X, rfl, hs⟩

/-- **The linear staging composes**: walking `a + b` moves is walking `a` and
then `b`. -/
theorem savLe_add (h : SavInv cls R) :
    ∀ (a b : ℕ) {X Y : St},
      SavLe cls R (a + b) X Y ↔ ∃ Z, SavLe cls R a X Z ∧ SavLe cls R b Z Y := by
  intro a b
  induction b with
  | zero =>
    intro X Y
    exact ⟨fun hs => ⟨Y, hs, rfl⟩, fun ⟨Z, hZ, he⟩ => savLe_congr h a rfl he hZ⟩
  | succ b ih =>
    intro X Y
    constructor
    · rintro ⟨W, hW, hs⟩
      obtain ⟨Z, hZ, hZW⟩ := (ih (X := X) (Y := W)).mp hW
      exact ⟨Z, hZ, W, hZW, hs⟩
    · rintro ⟨Z, hZ, W, hW, hs⟩
      exact ⟨W, (ih (X := X) (Y := W)).mpr ⟨Z, hZ, hW⟩, hs⟩

end Linear

/-! ### The two stagings agree -/

section Pow

variable {cls : St → T} {R : St → St → Prop}

/-- **Savitch's staging is the linear one at `2 ^ k`**: `k` nested midpoints
describe a walk of exponentially many moves. -/
theorem savPow_iff_savLe (h : SavInv cls R) :
    ∀ (k : ℕ) {X Y : St}, SavPow cls R k X Y ↔ SavLe cls R (2 ^ k) X Y := by
  intro k
  induction k with
  | zero =>
    intro X Y
    refine ⟨fun hs => savLe_of_savStep hs, ?_⟩
    rintro ⟨Z, he, hs⟩
    exact savStep_congr h he.symm rfl hs
  | succ k ih =>
    intro X Y
    rw [pow_succ, Nat.mul_two, savLe_add h]
    exact exists_congr fun Z => and_congr ih ih

end Pow

/-! ### Reachability, and the pigeonhole -/

section Reach

variable {cls : St → T} {R : St → St → Prop}

theorem exists_savLe_of_reflTransGen {X Y : St} (hr : Relation.ReflTransGen R X Y) :
    ∃ n : ℕ, SavLe cls R n X Y := by
  induction hr with
  | refl => exact ⟨0, rfl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, c, hn, Or.inr hcd⟩

/-- A bounded walk is a genuine walk, up to the class of its endpoint. -/
theorem reflTransGen_of_savLe (h : SavInv cls R) :
    ∀ (n : ℕ) {X Y : St}, SavLe cls R n X Y →
      ∃ Y' : St, cls Y' = cls Y ∧ Relation.ReflTransGen R X Y' := by
  intro n
  induction n with
  | zero => exact fun {X Y} he => ⟨X, he, Relation.ReflTransGen.refl⟩
  | succ n ih =>
    rintro X Y ⟨Z, hZ, hs⟩
    obtain ⟨Z', hZ', hr⟩ := ih hZ
    rcases hs with he | hstep
    · exact ⟨Z', hZ'.trans he, hr⟩
    · exact ⟨Y, rfl, hr.tail (h Z Z' Y Y hZ'.symm rfl hstep)⟩

/-- **The pigeonhole**: a walk saturates after as many moves as there are
classes. The set of classes reached in at most `n` moves grows with `n`, and as
soon as it stops growing it stops growing for good, so it is stable by the time
`n` reaches `Nat.card T`. -/
theorem savLe_card [Finite T] (h : SavInv cls R) (X : St) :
    ∀ (n : ℕ) {Y : St}, SavLe cls R n X Y → SavLe cls R (Nat.card T) X Y := by
  classical
  set N := Nat.card T with hN
  set Rch : ℕ → Set T := fun n => {t : T | ∃ Y : St, cls Y = t ∧ SavLe cls R n X Y} with hRchdef
  have hmem : ∀ (n : ℕ) (Y : St), SavLe cls R n X Y → cls Y ∈ Rch n := fun n Y hY => ⟨Y, rfl, hY⟩
  have hmono : ∀ m n : ℕ, m ≤ n → Rch m ⊆ Rch n := by
    rintro m n hmn t ⟨Y, hY, hs⟩
    exact ⟨Y, hY, savLe_of_le hmn hs⟩
  -- once the reachable classes stop growing, they never grow again
  have hstep : ∀ n : ℕ, Rch (n + 1) ⊆ Rch n → Rch (n + 2) ⊆ Rch (n + 1) := by
    rintro n hsub t ⟨Y, hY, Z, hZ, hs⟩
    obtain ⟨Z', hZ', hZ'le⟩ := hsub (hmem (n + 1) Z hZ)
    exact ⟨Y, hY, Z', hZ'le, savStep_congr h hZ'.symm rfl hs⟩
  have hstab : ∀ n : ℕ, Rch (n + 1) ⊆ Rch n → ∀ j : ℕ, Rch (n + j) ⊆ Rch n := by
    intro n hsub
    have hone : ∀ j : ℕ, Rch (n + j + 1) ⊆ Rch (n + j) := by
      intro j
      induction j with
      | zero => exact hsub
      | succ j ih => exact hstep (n + j) ih
    intro j
    induction j with
    | zero => exact fun _ ht => ht
    | succ j ih => exact fun t ht => ih (hone j ht)
  -- some `n ≤ N` is already stable, else `N + 1` distinct classes appear
  have hfind : ∃ n : ℕ, n ≤ N ∧ Rch (n + 1) ⊆ Rch n := by
    by_contra hcon
    have hpick : ∀ i : Fin (N + 1), ∃ t : T, t ∈ Rch ((i : ℕ) + 1) ∧ t ∉ Rch (i : ℕ) := by
      intro i
      refine Set.not_subset.mp fun hsub => hcon ⟨(i : ℕ), Nat.lt_succ_iff.mp i.isLt, hsub⟩
    choose f hf hf' using hpick
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hne' : (i : ℕ) ≠ (j : ℕ) := fun he => hne (Fin.ext he)
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · exact hf' j (hij ▸ hmono ((i : ℕ) + 1) (j : ℕ) hlt (hf i))
      · exact hf' i (hij ▸ hmono ((j : ℕ) + 1) (i : ℕ) hlt (hf j))
    have hcard := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, ← hN] at hcard
    omega
  obtain ⟨n₀, hn₀N, hn₀⟩ := hfind
  intro n Y hY
  have hsub : Rch n ⊆ Rch N := by
    rcases Nat.le_total n n₀ with hle | hle
    · exact fun t ht => hmono n₀ N hn₀N (hmono n n₀ hle ht)
    · refine fun t ht => hmono n₀ N hn₀N (hstab n₀ hn₀ (n - n₀) ?_)
      rwa [Nat.add_sub_cancel' hle]
  obtain ⟨Y', hY', hle⟩ := hsub (hmem n Y hY)
  exact savLe_congr h N rfl hY' hle

/-- **Savitch's staging computes reachability**, as soon as it is deep enough
for the number of classes. -/
theorem savPow_of_reflTransGen [Finite T] (h : SavInv cls R) {k : ℕ} (hk : Nat.card T ≤ 2 ^ k)
    {X Y : St} (hr : Relation.ReflTransGen R X Y) : SavPow cls R k X Y := by
  obtain ⟨n, hn⟩ := exists_savLe_of_reflTransGen (cls := cls) hr
  exact (savPow_iff_savLe h k).mpr (savLe_of_le hk (savLe_card h X n hn))

end Reach

end DescriptiveComplexity
