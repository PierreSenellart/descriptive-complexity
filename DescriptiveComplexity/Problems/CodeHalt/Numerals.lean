/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel

/-!
# The numeral segment of a certificate

An `∃SO[new]` certificate for `DescriptiveComplexity.CODEHALT` carries numbers
as *invented values*: a finite set with a guessed linear order on it, read as
the initial segment `0, 1, …, N` of `ℕ`. This file is that reading.

`DescriptiveComplexity.CodeHalt.numOf` is the number a value stands for – the
count of values below it, i.e. `DescriptiveComplexity.bitRank` at the trivial
set of positions. `DescriptiveComplexity.CodeHalt.IsZ` and
`DescriptiveComplexity.CodeHalt.IsS` are “is the least value” and “is covered
by”, spelled out so that a first-order kernel can state them verbatim, and the
two `iff` lemmas say they mean `0` and `+ 1`. That is the whole bridge: from
there on a certificate is a statement about natural numbers.

The last two lemmas run the bridge the other way, on `Fin (N + 1)` with its own
order, which is the segment a certificate is *built* on.
-/

namespace DescriptiveComplexity

namespace CodeHalt

/-! ### The number a value stands for -/

section Segment

variable {D : Type} {Le : D → D → Prop}

/-- **The number a value of the numeral segment stands for**: how many values
lie strictly below it. -/
noncomputable def numOf (Le : D → D → Prop) (d : D) : ℕ :=
  bitRank Le (fun _ => True) d

/-- `d` is the least value of the segment, i.e. the numeral `0`. -/
def IsZ (Le : D → D → Prop) (d : D) : Prop := ∀ e, Le d e

/-- `d'` is the value just above `d`, i.e. its numeral is one more. -/
def IsS (Le : D → D → Prop) (d d' : D) : Prop :=
  Le d d' ∧ d ≠ d' ∧ ∀ e, Le d e → Le e d' → e = d ∨ e = d'

variable [Finite D] (hlin : IsLinOrd Le)
include hlin

theorem numOf_lt {x y : D} (hle : Le x y) (hne : x ≠ y) : numOf Le x < numOf Le y :=
  bitRank_lt hlin trivial hle hne

theorem le_of_numOf_lt {x y : D} (h : numOf Le x < numOf Le y) : Le x y ∧ x ≠ y := by
  have hne : x ≠ y := fun hxy => absurd h (by rw [hxy]; omega)
  refine ⟨?_, hne⟩
  rcases hlin.2.2.2 x y with hxy | hyx
  · exact hxy
  · exact absurd (numOf_lt hlin hyx fun h' => hne h'.symm) (by omega)

theorem numOf_injective {x y : D} (h : numOf Le x = numOf Le y) : x = y := by
  by_contra hne
  rcases hlin.2.2.2 x y with hxy | hyx
  · exact absurd (numOf_lt hlin hxy hne) (by omega)
  · exact absurd (numOf_lt hlin hyx fun h' => hne h'.symm) (by omega)

theorem le_iff_numOf_le {x y : D} : Le x y ↔ numOf Le x ≤ numOf Le y := by
  constructor
  · intro hxy
    rcases eq_or_ne x y with rfl | hne
    · exact le_rfl
    · exact (numOf_lt hlin hxy hne).le
  · intro h
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · exact (numOf_injective hlin heq) ▸ hlin.1 x
    · exact (le_of_numOf_lt hlin hlt).1

theorem isZ_iff {d : D} : IsZ Le d ↔ numOf Le d = 0 := by
  constructor
  · intro h
    have hset : {q : D | (fun _ => True) q ∧ Le q d ∧ q ≠ d} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, true_and, not_and, not_not]
      exact fun hq => hlin.2.2.1 q d hq (h q)
    rw [numOf, bitRank, hset, Set.ncard_empty]
  · intro h e
    by_contra hde
    have hed : Le e d := (hlin.2.2.2 d e).resolve_left hde
    have hne : e ≠ d := fun hh => hde (hh ▸ hlin.1 e)
    exact absurd (numOf_lt hlin hed hne) (by omega)

theorem isS_iff {d d' : D} : IsS Le d d' ↔ numOf Le d' = numOf Le d + 1 := by
  constructor
  · rintro ⟨hle, hne, hbtw⟩
    have hset : {q : D | (fun _ => True) q ∧ Le q d' ∧ q ≠ d'} =
        insert d {q : D | (fun _ => True) q ∧ Le q d ∧ q ≠ d} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, true_and]
      constructor
      · rintro ⟨hqd', hqne⟩
        rcases hlin.2.2.2 d q with hdq | hqd
        · exact Or.inl ((hbtw q hdq hqd').resolve_right hqne)
        · rcases eq_or_ne q d with rfl | hqdne
          · exact Or.inl rfl
          · exact Or.inr ⟨hqd, hqdne⟩
      · rintro (rfl | ⟨hqd, hqdne⟩)
        · exact ⟨hle, hne⟩
        · refine ⟨hlin.2.1 q d d' hqd hle, ?_⟩
          rintro rfl
          exact hne (hlin.2.2.1 d q hle hqd)
    have hnot : d ∉ {q : D | (fun _ => True) q ∧ Le q d ∧ q ≠ d} := fun hh => hh.2.2 rfl
    rw [numOf, numOf, bitRank, bitRank, hset, Set.ncard_insert_of_notMem hnot (Set.toFinite _)]
  · intro h
    obtain ⟨hle, hne⟩ := le_of_numOf_lt hlin (show numOf Le d < numOf Le d' by omega)
    refine ⟨hle, hne, fun e hde hed' => ?_⟩
    have h1 : numOf Le d ≤ numOf Le e := (le_iff_numOf_le hlin).mp hde
    have h2 : numOf Le e ≤ numOf Le d' := (le_iff_numOf_le hlin).mp hed'
    rcases (by omega : numOf Le e = numOf Le d ∨ numOf Le e = numOf Le d') with he | he
    · exact Or.inl (numOf_injective hlin he)
    · exact Or.inr (numOf_injective hlin he)

omit [Finite D] hlin in
theorem isZ_iff_minPos {d : D} : IsZ Le d ↔ MinPos Le (fun _ => True) d :=
  ⟨fun h => ⟨trivial, fun q _ => h q⟩, fun h q => h.2 q trivial⟩

omit [Finite D] hlin in
theorem isS_iff_succPos {d d' : D} : IsS Le d d' ↔ SuccPos Le (fun _ => True) d d' :=
  ⟨fun h => ⟨trivial, trivial, h.1, h.2.1, fun r _ => h.2.2 r⟩,
    fun h => ⟨h.2.2.1, h.2.2.2.1, fun r => h.2.2.2.2 r trivial⟩⟩

/-- **Every number below a reached one is reached**: the values of the segment
are an initial segment of `ℕ`. This is what lets a bounded universal over the
segment be read as a bounded universal over `ℕ`. -/
theorem exists_numOf :
    ∀ (Y : ℕ) (y : D), numOf Le y = Y → ∀ w, w ≤ Y → ∃ x : D, numOf Le x = w := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | _ Y ih =>
    rintro y rfl w hw
    rcases Nat.eq_or_lt_of_le hw with heq | hlt
    · exact ⟨y, heq.symm⟩
    · have hne0 : numOf Le y ≠ 0 := by omega
      have hmin : ¬MinPos Le (fun _ => True) y := fun hm =>
        hne0 ((isZ_iff hlin).mp (isZ_iff_minPos.mpr hm))
      obtain ⟨y', hy'⟩ := exists_predPos hlin (Posn := fun _ => True) trivial hmin
      have hsy : numOf Le y = numOf Le y' + 1 := (isS_iff hlin).mp (isS_iff_succPos.mpr hy')
      exact ih (numOf Le y') (by omega) y' rfl w (by omega)

end Segment

/-! ### The segment a certificate is built on -/

section Fin

variable {N : ℕ}

theorem isZ_fin {i : Fin (N + 1)} : IsZ (· ≤ ·) i ↔ (i : ℕ) = 0 := by
  constructor
  · intro h
    simpa [Fin.le_def] using (h 0 : i ≤ 0)
  · intro h j
    show i ≤ j
    rw [Fin.le_def]
    omega

theorem isS_fin {i j : Fin (N + 1)} : IsS (· ≤ ·) i j ↔ (j : ℕ) = (i : ℕ) + 1 := by
  constructor
  · rintro ⟨hle, hne, hbtw⟩
    have hle' : (i : ℕ) ≤ (j : ℕ) := by rwa [← Fin.le_def]
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
    by_contra hcon
    have hb : ((i : ℕ) + 1) < N + 1 := by omega
    set p : Fin (N + 1) := ⟨(i : ℕ) + 1, hb⟩ with hpdef
    have hp : (p : ℕ) = (i : ℕ) + 1 := rfl
    have h1 : i ≤ p := by rw [Fin.le_def, hp]; omega
    have h2 : p ≤ j := by rw [Fin.le_def, hp]; omega
    rcases hbtw _ h1 h2 with h | h <;>
      · have := congrArg Fin.val h
        rw [hp] at this
        omega
  · intro h
    refine ⟨show i ≤ j by rw [Fin.le_def]; omega, fun hc => by rw [hc] at h; omega,
      fun e hie hej => ?_⟩
    have hie' : (i : ℕ) ≤ (e : ℕ) := by rwa [← Fin.le_def]
    have hej' : (e : ℕ) ≤ (j : ℕ) := by rwa [← Fin.le_def]
    rcases (by omega : (e : ℕ) = (i : ℕ) ∨ (e : ℕ) = (j : ℕ)) with he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext he)

end Fin

end CodeHalt

end DescriptiveComplexity
