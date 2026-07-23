/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.JobSequencing.Schedule
import DescriptiveComplexity.Problems.NaeThreeSat
import DescriptiveComplexity.OccurrenceSlack
import DescriptiveComplexity.OrderedComposition
import DescriptiveComplexity.Numbers.Digits
import DescriptiveComplexity.Padding

/-!
# Job sequencing is NP-hard

Karp derives SEQUENCING from Partition: one job per number, every deadline and
the bound both `Σ / 2`. That reduction does **not** transfer here, because a
first-order interpretation has to *write* the deadline and the bound in
binary, and half of a total is an iterated sum – the same obstruction that
ruled out Karp's padding for Partition, one step further along.

The way out is to make the gadget's own total a number it can write. By
`DescriptiveComplexity.hasGoodSchedule_iff_exists_half`, with a common deadline
`D`, penalties equal to execution times, jobs weighing `2 D` in total and the
bound equal to `D`, a good schedule is exactly a set of jobs weighing `D`:
Partition's condition. So it is enough to build a balanced-split gadget
**all of whose digit blocks total an even number**, and then to let `D` be the
digit-wise half – which is first-order, one bit per block, while `Σ = 2 D`
holds by `DescriptiveComplexity.digitNum_mul_left`.

## The gadget

One digit block per variable and one per clause, in base `2 ^ (3 |A|)`, and
one job per literal and per slack occurrence
(`DescriptiveComplexity.SatOcc.Mid`), as in the reduction to Partition:

* the block of a variable totals `2`, so a balanced split takes exactly one of
  its two literals: it *is* an assignment;
* the block of a clause of width `w` totals `w + (w − 2) = 2 (w − 1)`, so a
  balanced split takes between `1` and `w − 1` true literals: exactly
  not-all-equal satisfaction.

Every block total is `2 (w − 1)`, hence `D` has digit `w − 1` there. That is a
*single bit per block* only when `w − 1` is a power of two, so – unlike
Partition, which never had to write the number to reach – the width has to be
bounded: the source is NAE-**3**SAT, and `w − 1 ∈ {1, 2}` is the bit at the
base of the block, or the one just above it.

Positions are pairs of a block and an index inside it, as in the reduction to
Partition, but the key ordering them (`DescriptiveComplexity.JSRed.leKF`) puts
the index **last**: the positions of a block are then consecutive, so the bit
just above a block's base is worth exactly twice it
(`DescriptiveComplexity.JSRed.bitRank_jPos`), which is what lets the deadline
carry the digit `2`.

## The degenerate instances

The width bound of NAE-3SAT is folded into its yes-instances, and a clause of
width at most one is not-all-equal unsatisfiable, so both kinds of degeneracy
(`DescriptiveComplexity.JSRed.Deg`: a wide clause, or a short one) mark a
no-instance of the source. The gadget gates the deadline and the bound on
their absence: a degenerate input is sent to an instance of deadline `0` and
bound `0`, which no schedule can meet, every literal job having a positive
execution time.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace JSRed

open Language Structure SatOcc

/-! ### The degenerate inputs

Two first-order tests carve out the instances the gadget refuses to encode: a
clause with four distinct occurrences – `DescriptiveComplexity.Wide`, the negation
of the width bound of 3SAT – and a clause with at most one, which is
not-all-equal unsatisfiable. A clause has two occurrences exactly when one of
them is not the first one (`DescriptiveComplexity.SatOcc.Chained`), which is how
the second test avoids counting. -/

section Degenerate

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- A *short* clause: one with at most one occurrence, that is, one none of
whose occurrences is preceded by another. -/
def Short (c : A) : Prop := IsCl c ∧ ∀ x s, ¬Chained c x s

variable (A) in
/-- A *degenerate* input: one with a wide clause or a short one. Both mark a
no-instance of NAE-3SAT, and the gadget sends them to an instance no schedule
can serve. -/
def Deg : Prop := ThreeSatToSat.Wide A ∨ ∃ c : A, Short c

/-- A short clause is not-all-equal unsatisfiable: its true and its false
literal would be one and the same occurrence. -/
theorem not_naeProper_of_short {c : A} (hc : Short c) (ν : A → Prop) : ¬NAEProper ν := by
  intro hν
  obtain ⟨⟨x, s, hx, hxT⟩, ⟨y, t, hy, hyT⟩⟩ := naeProper_occ hν c hc.1
  rcases occLt_trichotomy x s y t with hlt | ⟨rfl, rfl⟩ | hlt
  · exact hc.2 y t ⟨hy, fun hmin => hmin.2 x s hx hlt⟩
  · exact hyT hxT
  · exact hc.2 x s ⟨hx, fun hmin => hmin.2 y t hy hlt⟩

/-- **A clause has at most one slack occurrence under the width bound**: its
first occurrence, its last one and two distinct slack ones would be four. -/
theorem midSet_subsingleton [Finite A] (hwidth : WidthAtMostThree A) {c x y : A} {s t : Bool}
    (hx : Mid c x s) (hy : Mid c y t) : x = y ∧ s = t := by
  by_contra hne
  obtain ⟨m, ms, hmin⟩ := exists_minOcc ⟨x, s, hx.occIn⟩
  obtain ⟨M, Ms, hmax⟩ := exists_maxOcc ⟨x, s, hx.occIn⟩
  obtain ⟨i, j, hij, hxx, hss⟩ :=
    hwidth c ![m, x, y, M] ![ms, s, t, Ms] (by
      intro i
      fin_cases i
      exacts [hmin.1, hx.occIn, hy.occIn, hmax.1])
  have d12 : ¬(m = x ∧ ms = s) := by
    rintro ⟨rfl, rfl⟩
    exact hx.1.2 hmin
  have d13 : ¬(m = y ∧ ms = t) := by
    rintro ⟨rfl, rfl⟩
    exact hy.1.2 hmin
  have d14 : ¬(m = M ∧ ms = Ms) := by
    rintro ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := eq_of_minOcc_of_maxOcc hmin hmax hx.occIn
    exact hx.1.2 hmin
  have d23 : ¬(x = y ∧ s = t) := hne
  have d24 : ¬(x = M ∧ s = Ms) := by
    rintro ⟨rfl, rfl⟩
    exact hx.2 hmax
  have d34 : ¬(y = M ∧ t = Ms) := by
    rintro ⟨rfl, rfl⟩
    exact hy.2 hmax
  fin_cases i <;> fin_cases j <;> simp_all

/-- A clause of a non-degenerate input has an occurrence which is not the
first one, hence at least two occurrences. -/
theorem exists_chained_of_not_deg (hd : ¬Deg A) {c : A} (hc : IsCl c) :
    ∃ x s, Chained c x s := by
  by_contra h
  exact hd (Or.inr ⟨c, hc, fun x s hx => h ⟨x, s, hx⟩⟩)

end Degenerate

/-! ### The tags -/

/-- Tags of the reduction. The jobs are those of the literals and of the slack
occurrences; the positions carry a *block* – a variable block (`false`) or a
clause block (`true`) – and an index inside it, of which `Fin 3` are enough to
keep the base above every digit and to leave room for the deadline's bit. -/
inductive JTag : Type
  /-- The job of the literal `(x, s)`; its tuple is `(x, ⊥)`. -/
  | lit (s : Bool)
  /-- The job of the slack occurrence `(x, s)` of `c`; its tuple is `(c, x)`. -/
  | slk (s : Bool)
  /-- The `f`-th position of the block `(k, e)`; its tuple is `(e, y)`. -/
  | pos (k : Bool) (f : Fin 3)
  deriving DecidableEq

instance : Fintype JTag where
  elems :=
    {.lit false, .lit true, .slk false, .slk true,
      .pos false 0, .pos false 1, .pos false 2, .pos true 0, .pos true 1, .pos true 2}
  complete := by
    intro t
    cases t with
    | lit s => cases s <;> decide
    | slk s => cases s <;> decide
    | pos k f => cases k <;> fin_cases f <;> decide

instance : Nonempty JTag := ⟨JTag.lit true⟩

/-- The rank of a tag: the jobs first, then the positions of the variable
blocks, then those of the clause blocks. It is the leading component of the
key, so it separates jobs from positions and variable blocks from clause
blocks. -/
def tagRk : JTag → ℕ
  | .lit false => 0
  | .lit true => 1
  | .slk false => 2
  | .slk true => 3
  | .pos false _ => 4
  | .pos true _ => 5

/-- The rank of a tag inside a block: the index of a position, and `0` for the
jobs, which no block holds. Unlike the reduction to Partition, this is the
*last* component of the key, so that consecutive indices are consecutive
positions and the deadline can carry the digit `2`. -/
def subRk : JTag → ℕ
  | .pos _ f => (f : ℕ)
  | _ => 0

/-- The two ranks together determine the tag. -/
theorem tag_ext {t t' : JTag} (h₁ : tagRk t = tagRk t') (h₂ : subRk t = subRk t') : t = t' := by
  revert h₁ h₂
  revert t t'
  decide

/-! ### The interpretation -/

section Formulas

variable {α : Type}

/-- A minimum of the order, as a formula over the ordered expansion of the
vocabulary of CNF instances. -/
noncomputable def minF (x : α) : satOrd.Formula α := botF (L := Language.sat) x

@[simp]
theorem realize_minF {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : α → A} {x : α} :
    (minF x).Realize v ↔ IsBot (v x) :=
  realize_botF

/-- `c` has an occurrence which is not its first one, as a formula. -/
noncomputable def hasChainedF (c : α) : satOrd.Formula α :=
  (chainedF false (.inl c) (.inr ()) ⊔ chainedF true (.inl c) (.inr ())).iExs Unit

@[simp]
theorem realize_hasChainedF {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : α → A}
    {c : α} : (hasChainedF c).Realize v ↔ ∃ x s, Chained (v c) x s := by
  simp only [hasChainedF, Formula.realize_iExs, Formula.realize_sup, realize_chainedF,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, h | h⟩
    exacts [⟨i (), false, h⟩, ⟨i (), true, h⟩]
  · rintro ⟨x, s, h⟩
    cases s
    exacts [⟨fun _ => x, Or.inl h⟩, ⟨fun _ => x, Or.inr h⟩]

/-- `c` has a slack occurrence, as a formula: the width-three test, a clause
of a non-degenerate input having width two or three. -/
noncomputable def hasMidF (c : α) : satOrd.Formula α :=
  (midF false (.inl c) (.inr ()) ⊔ midF true (.inl c) (.inr ())).iExs Unit

@[simp]
theorem realize_hasMidF {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : α → A}
    {c : α} : (hasMidF c).Realize v ↔ ∃ x s, Mid (v c) x s := by
  simp only [hasMidF, Formula.realize_iExs, Formula.realize_sup, realize_midF,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, h | h⟩
    exacts [⟨i (), false, h⟩, ⟨i (), true, h⟩]
  · rintro ⟨x, s, h⟩
    cases s
    exacts [⟨fun _ => x, Or.inl h⟩, ⟨fun _ => x, Or.inr h⟩]

/-- `c` is a short clause, as a formula. -/
noncomputable def shortF (c : α) : satOrd.Formula α := clF c ⊓ ∼(hasChainedF c)

@[simp]
theorem realize_shortF {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : α → A}
    {c : α} : (shortF c).Realize v ↔ Short (v c) := by
  simp only [shortF, Formula.realize_inf, Formula.realize_not, realize_clF, realize_hasChainedF,
    Short]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x s hx => h2 ⟨x, s, hx⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨x, s, hx⟩ => h2 x s hx⟩

/-- The input is degenerate, as a (closed) formula. -/
noncomputable def degF : satOrd.Formula α :=
  ThreeSatToSat.wideOrdF ⊔ (shortF (Sum.inr ())).iExs Unit

@[simp]
theorem realize_degF {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : α → A} :
    (degF (α := α)).Realize v ↔ Deg A := by
  simp only [degF, Formula.realize_sup, Formula.realize_iExs, realize_shortF, Sum.elim_inr, Deg,
    ThreeSatToSat.realize_wideOrdF]
  exact or_congr Iff.rfl ⟨fun ⟨i, h⟩ => ⟨i (), h⟩, fun ⟨c, h⟩ => ⟨fun _ => c, h⟩⟩

/-- Defining formula for the jobs: one per literal and one per slack
occurrence. -/
noncomputable def jobF : JTag → satOrd.Formula (Fin 1 × Fin 2)
  | .lit _ => minF (0, 1)
  | .slk s => midF s (0, 0) (0, 1)
  | .pos _ _ => ⊥

/-- Defining formula for the bit positions: every tagged pair is one. -/
def posnF : JTag → satOrd.Formula (Fin 1 × Fin 2)
  | .pos _ _ => ⊤
  | _ => ⊥

/-- Defining formula for the bits of the execution times – and of the
penalties, which equal them. Only the lowest position of a block – index `0`,
second coordinate a minimum – ever carries a bit. -/
noncomputable def bitF : JTag → JTag → satOrd.Formula (Fin 2 × Fin 2)
  | .lit s, .pos k f =>
    if f = 0 then
      minF (0, 1) ⊓ minF (1, 1) ⊓ (if k then occF s (1, 0) (0, 0) else eqF (1, 0) (0, 0))
    else ⊥
  | .slk s, .pos k f =>
    if f = 0 ∧ k = true then
      midF s (0, 0) (0, 1) ⊓ minF (1, 1) ⊓ eqF (1, 0) (0, 0)
    else ⊥
  | _, _ => ⊥

/-- Defining formula for the bits of the common deadline, over the tuple of a
position: the digit `1` – the bit at the base of the block – in every variable
block and in the block of a clause of width two, and the digit `2` – the bit
one position up – in the block of a clause of width three. A degenerate input
gets the deadline `0`. -/
noncomputable def dbitF (k : Bool) (f : Fin 3) (e y : α) : satOrd.Formula α :=
  if k = false ∧ f = 0 then minF y ⊓ ∼degF
  else if k = true ∧ f = 0 then minF y ⊓ clF e ⊓ ∼(hasMidF e) ⊓ ∼degF
  else if k = true ∧ f = 1 then minF y ⊓ clF e ⊓ hasMidF e ⊓ ∼degF
  else ⊥

/-- Defining formula for the bits of the deadline of a job: the job condition,
and the deadline's bit pattern, the same for every job. -/
noncomputable def dlineF : JTag → JTag → satOrd.Formula (Fin 2 × Fin 2)
  | .lit _, .pos k f => minF (0, 1) ⊓ dbitF k f (1, 0) (1, 1)
  | .slk s, .pos k f => midF s (0, 0) (0, 1) ⊓ dbitF k f (1, 0) (1, 1)
  | _, _ => ⊥

/-- Defining formula for the bits of the penalty bound: the deadline again. -/
noncomputable def bndF : JTag → satOrd.Formula (Fin 1 × Fin 2)
  | .pos k f => dbitF k f (0, 0) (0, 1)
  | _ => ⊥

/-- Defining formula for the order: the key `(tag rank, first coordinate,
second coordinate, index in the block)`, read lexicographically. The index
comes *last*, so that the positions of a block are consecutive. -/
def leKF (t t' : JTag) : satOrd.Formula (Fin 2 × Fin 2) :=
  if tagRk t < tagRk t' then ⊤
  else if tagRk t' < tagRk t then ⊥
  else
    SatOcc.ltF (0, 0) (1, 0) ⊔
      (SatOcc.eqF (0, 0) (1, 0) ⊓
        (SatOcc.ltF (0, 1) (1, 1) ⊔
          (SatOcc.eqF (0, 1) (1, 1) ⊓ (if subRk t' < subRk t then ⊥ else ⊤))))

/-- The interpretation of a job-sequencing instance in a CNF structure: one
job per literal and per slack occurrence, one block of `3 |A|` positions per
variable and per clause, every deadline and the bound the digit-wise half of
the total execution time. -/
noncomputable def jInterp : FOInterpretation satOrd Language.jobSeq JTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .job => fun t => jobF (t 0)
    | _, .posn => fun t => posnF (t 0)
    | _, .time => fun t => bitF (t 0) (t 1)
    | _, .dline => fun t => dlineF (t 0) (t 1)
    | _, .pen => fun t => bitF (t 0) (t 1)
    | _, .bnd => fun t => bndF (t 0)
    | _, .le => fun t => leKF (t 0) (t 1)

end Formulas

/-! ### The points of the interpreted structure -/

section Points

variable {A : Type}

/-- The point of tag `t` over the pair `w`. -/
def jPt (t : JTag) (w : Fin 2 → A) : jInterp.Map A := (t, w)

theorem jPt_surj (q : jInterp.Map A) : ∃ t w, q = jPt t w := ⟨q.1, q.2, rfl⟩

theorem jPt_eq_iff {t t' : JTag} {w w' : Fin 2 → A} :
    jPt t w = jPt t' w' ↔ t = t' ∧ w = w' := by
  constructor
  · intro h
    exact ⟨congrArg (fun q : jInterp.Map A => q.1) h,
      congrArg (fun q : jInterp.Map A => q.2) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem jPt_snd (t : JTag) (w : Fin 2 → A) (j : Fin 2) : (jPt t w).2 j = w j := rfl

/-- Two `2`-tuples with the same coordinates are equal. -/
theorem tuple₂_ext {w w' : Fin 2 → A} (h0 : w 0 = w' 0) (h1 : w 1 = w' 1) : w = w' := by
  funext j
  fin_cases j
  · exact h0
  · exact h1

/-- The job of the literal `(x, s)`. -/
def jLit (a₀ : A) (s : Bool) (x : A) : jInterp.Map A := jPt (.lit s) ![x, a₀]

/-- The job of the slack occurrence `(x, s)` of the clause `c`. -/
def jSlk (s : Bool) (c x : A) : jInterp.Map A := jPt (.slk s) ![c, x]

/-- The `f`-th position of the block `b`. -/
def jPos (f : Fin 3) (b : Bool × A) (y : A) : jInterp.Map A := jPt (.pos b.1 f) ![b.2, y]

/-- The lowest position of the block `b`. -/
def jLow (a₀ : A) (b : Bool × A) : jInterp.Map A := jPos 0 b a₀

theorem jPos_eq (f : Fin 3) (k : Bool) (e y : A) : jPos f (k, e) y = jPt (.pos k f) ![e, y] := rfl

theorem jLit_injective (a₀ : A) : Function.Injective fun p : A × Bool => jLit a₀ p.2 p.1 := by
  rintro ⟨x, s⟩ ⟨x', s'⟩ h
  obtain ⟨ht, hw⟩ := jPt_eq_iff.mp h
  refine Prod.ext ?_ ?_
  · simpa using congrArg (fun u : Fin 2 → A => u 0) hw
  · cases s <;> cases s' <;> simp_all

theorem jSlk_injective (c : A) : Function.Injective fun p : A × Bool => jSlk p.2 c p.1 := by
  rintro ⟨x, s⟩ ⟨x', s'⟩ h
  obtain ⟨ht, hw⟩ := jPt_eq_iff.mp h
  refine Prod.ext ?_ ?_
  · simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  · cases s <;> cases s' <;> simp_all

theorem jPos_injective : Function.Injective fun u : (Bool × A) × Fin 3 × A =>
    jPos u.2.1 u.1 u.2.2 := by
  rintro ⟨⟨k, e⟩, f, y⟩ ⟨⟨k', e'⟩, f', y'⟩ h
  obtain ⟨ht, hw⟩ := jPt_eq_iff.mp h
  have h0 : e = e' := by simpa using congrArg (fun u : Fin 2 → A => u 0) hw
  have h1 : y = y' := by simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  have hk : k = k' ∧ f = f' := by
    refine ⟨?_, ?_⟩ <;> · injection ht
  obtain ⟨hk₁, hk₂⟩ := hk
  subst h0; subst h1; subst hk₁; subst hk₂
  rfl

theorem jLow_injective (a₀ : A) : Function.Injective (jLow a₀ (A := A)) := by
  rintro ⟨k, e⟩ ⟨k', e'⟩ h
  obtain ⟨ht, hw⟩ := jPt_eq_iff.mp h
  have h0 : e = e' := by simpa using congrArg (fun u : Fin 2 → A => u 0) hw
  have hk : k = k' := by injection ht
  exact Prod.ext hk h0

theorem jLit_ne_jSlk (a₀ : A) (s s' : Bool) (x c y : A) : jLit a₀ s x ≠ jSlk s' c y := by
  intro h
  rw [jLit, jSlk] at h
  exact absurd (jPt_eq_iff.mp h).1 (by simp)

theorem jLit_eq_iff {a₀ : A} {s s' : Bool} {x x' : A} :
    jLit a₀ s x = jLit a₀ s' x' ↔ s = s' ∧ x = x' := by
  rw [jLit, jLit, jPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    exact ⟨by simpa using ht, by simpa using congrArg (fun u : Fin 2 → A => u 0) hw⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem jSlk_eq_iff {s s' : Bool} {c c' x x' : A} :
    jSlk s c x = jSlk s' c' x' ↔ s = s' ∧ c = c' ∧ x = x' := by
  rw [jSlk, jSlk, jPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    exact ⟨by simpa using ht, by simpa using congrArg (fun u : Fin 2 → A => u 0) hw,
      by simpa using congrArg (fun u : Fin 2 → A => u 1) hw⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end Points

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

@[simp]
theorem jsJob_lit (s : Bool) (w : Fin 2 → A) :
    JSJob (jPt (.lit s) w) ↔ IsBot (w 1) := by
  rw [JSJob, jPt, FOInterpretation.relMap_map]
  simp [jInterp, jobF]

@[simp]
theorem jsJob_slk (s : Bool) (w : Fin 2 → A) :
    JSJob (jPt (.slk s) w) ↔ Mid (w 0) (w 1) s := by
  rw [JSJob, jPt, FOInterpretation.relMap_map]
  simp [jInterp, jobF]

@[simp]
theorem jsJob_pos (k : Bool) (f : Fin 3) (w : Fin 2 → A) : ¬JSJob (jPt (.pos k f) w) := by
  rw [JSJob, jPt, FOInterpretation.relMap_map]
  simp [jInterp, jobF]

@[simp]
theorem jsPosn_pos (k : Bool) (f : Fin 3) (w : Fin 2 → A) : JSPosn (jPt (.pos k f) w) := by
  rw [JSPosn, jPt, FOInterpretation.relMap_map]
  simp [jInterp, posnF]

@[simp]
theorem jsPosn_lit (s : Bool) (w : Fin 2 → A) : ¬JSPosn (jPt (.lit s) w) := by
  rw [JSPosn, jPt, FOInterpretation.relMap_map]
  simp [jInterp, posnF]

@[simp]
theorem jsPosn_slk (s : Bool) (w : Fin 2 → A) : ¬JSPosn (jPt (.slk s) w) := by
  rw [JSPosn, jPt, FOInterpretation.relMap_map]
  simp [jInterp, posnF]

/-- The penalty of a job is its execution time: the two are defined by the
same formula. -/
theorem jsPen_iff_jsTime (i q : jInterp.Map A) : JSPen i q ↔ JSTime i q := by
  obtain ⟨t, w, rfl⟩ := jPt_surj i
  obtain ⟨t', w', rfl⟩ := jPt_surj q
  rw [JSPen, JSTime, jPt, jPt, FOInterpretation.relMap_map, FOInterpretation.relMap_map]
  exact Iff.rfl

/-- The key of a point: tag rank, first coordinate, second coordinate, index
in the block. -/
def jKey (q : jInterp.Map A) : ℕ × A × A × ℕ :=
  (tagRk q.1, q.2 0, q.2 1, subRk q.1)

/-- The order of the interpreted structure, read lexicographically on the
keys. -/
def keyLe : ℕ × A × A × ℕ → ℕ × A × A × ℕ → Prop :=
  lexRel (· ≤ ·) (lexRel (· ≤ ·) (lexRel (· ≤ ·) (· ≤ ·)))

theorem jsLe_iff (t t' : JTag) (w w' : Fin 2 → A) :
    JSLe (jPt t w) (jPt t' w') ↔ keyLe (jKey (jPt t w)) (jKey (jPt t' w')) := by
  rw [JSLe, jPt, jPt, FOInterpretation.relMap_map]
  simp only [jInterp, leKF, keyLe, jKey, lexRel]
  split_ifs with h₁ h₂ h₃
  · simp only [Formula.realize_top, true_iff]
    exact Or.inl ⟨h₁.le, ne_of_lt h₁⟩
  · simp only [Formula.realize_bot, false_iff, not_or]
    exact ⟨fun h => absurd h.1 (Nat.not_le.mpr h₂), fun h => absurd h.1 (ne_of_gt h₂)⟩
  · have hrk : tagRk t = tagRk t' := Nat.le_antisymm (Nat.not_lt.mp h₂) (Nat.not_lt.mp h₁)
    simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_bot, and_false,
      or_false, SatOcc.realize_ltF, realize_eqF]
    constructor
    · rintro (h | ⟨he, h⟩)
      · exact Or.inr ⟨hrk, Or.inl ⟨h.le, ne_of_lt h⟩⟩
      · exact Or.inr ⟨hrk, Or.inr ⟨he, Or.inl ⟨h.le, ne_of_lt h⟩⟩⟩
    · rintro (⟨-, hne⟩ | ⟨-, h | ⟨he, h | ⟨-, hsub⟩⟩⟩)
      · exact absurd hrk hne
      · exact Or.inl (lt_of_le_of_ne h.1 h.2)
      · exact Or.inr ⟨he, lt_of_le_of_ne h.1 h.2⟩
      · exact absurd hsub (Nat.not_le.mpr h₃)
  · have hrk : tagRk t = tagRk t' := Nat.le_antisymm (Nat.not_lt.mp h₂) (Nat.not_lt.mp h₁)
    have hsub : subRk t ≤ subRk t' := Nat.not_lt.mp h₃
    simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_top, and_true,
      SatOcc.realize_ltF, realize_eqF]
    constructor
    · rintro (h | ⟨he, h | he'⟩)
      · exact Or.inr ⟨hrk, Or.inl ⟨h.le, ne_of_lt h⟩⟩
      · exact Or.inr ⟨hrk, Or.inr ⟨he, Or.inl ⟨h.le, ne_of_lt h⟩⟩⟩
      · exact Or.inr ⟨hrk, Or.inr ⟨he, Or.inr ⟨he', hsub⟩⟩⟩
    · rintro (⟨-, hne⟩ | ⟨-, h | ⟨he, h | ⟨he', -⟩⟩⟩)
      · exact absurd hrk hne
      · exact Or.inl (lt_of_le_of_ne h.1 h.2)
      · exact Or.inr ⟨he, Or.inl (lt_of_le_of_ne h.1 h.2)⟩
      · exact Or.inr ⟨he, Or.inr he'⟩

omit [Language.sat.Structure A] [LinearOrder A] in
theorem jKey_injective : Function.Injective (jKey (A := A)) := by
  intro q q' h
  obtain ⟨t, w, rfl⟩ := jPt_surj q
  obtain ⟨t', w', rfl⟩ := jPt_surj q'
  have h₁ : tagRk t = tagRk t' := congrArg (fun u : ℕ × A × A × ℕ => u.1) h
  have h₂ : subRk t = subRk t' := congrArg (fun u : ℕ × A × A × ℕ => u.2.2.2) h
  have h₃ : w 0 = w' 0 := congrArg (fun u : ℕ × A × A × ℕ => u.2.1) h
  have h₄ : w 1 = w' 1 := congrArg (fun u : ℕ × A × A × ℕ => u.2.2.1) h
  exact jPt_eq_iff.mpr ⟨tag_ext h₁ h₂, tuple₂_ext h₃ h₄⟩

/-- The interpreted order is a linear order: the lexicographic order of the
keys, which are pairwise distinct. -/
theorem isLinOrd_jsLe : IsLinOrd (JSLe (A := jInterp.Map A)) := by
  refine isLinOrd_of_key (isLinOrd_lexRel isLinOrd_le
    (isLinOrd_lexRel isLinOrd_le (isLinOrd_lexRel isLinOrd_le isLinOrd_le)))
    jKey jKey_injective fun q q' => ?_
  obtain ⟨t, w, rfl⟩ := jPt_surj q
  obtain ⟨t', w', rfl⟩ := jPt_surj q'
  exact jsLe_iff t t' w w'

end Characterizations

/-! ### The blocks -/

section Blocks

variable {A : Type} [LinearOrder A]

/-- The order of the blocks: the variable blocks first, then the clause
blocks, each group in the order of the input. -/
def blkLe : Bool × A → Bool × A → Prop := lexRel (· ≤ ·) (· ≤ ·)

theorem isLinOrd_blkLe : IsLinOrd (blkLe (A := A)) := isLinOrd_lexRel isLinOrd_le isLinOrd_le

/-- Being strictly below a block. -/
theorem blkLt_iff {k k' : Bool} {x e : A} :
    (blkLe (k, x) (k', e) ∧ (k, x) ≠ (k', e)) ↔
      (k = k' ∧ x < e) ∨ (k = false ∧ k' = true) := by
  cases k <;> cases k' <;> simp [blkLe, lexRel, lt_iff_le_and_ne]

/-- The rank of a block: how many blocks lie strictly below it. -/
noncomputable def blkRank (b : Bool × A) : ℕ := bitRank (blkLe (A := A)) (fun _ => True) b

end Blocks

/-! ### The bits, and the positions of a block -/

section Bits

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

theorem jsTime_lit_pos (s : Bool) (w : Fin 2 → A) (k : Bool) (f : Fin 3) (w' : Fin 2 → A) :
    JSTime (jPt (.lit s) w) (jPt (.pos k f) w') ↔
      f = 0 ∧ IsBot (w 1) ∧ IsBot (w' 1) ∧ (if k then OccIn (w' 0) (w 0) s else w' 0 = w 0) := by
  rw [JSTime, jPt, jPt, FOInterpretation.relMap_map]
  by_cases hf : f = 0
  · subst hf
    cases k <;> simp [jInterp, bitF, and_assoc]
  · simp [jInterp, bitF, hf]

theorem jsTime_slk_pos (s : Bool) (w : Fin 2 → A) (k : Bool) (f : Fin 3) (w' : Fin 2 → A) :
    JSTime (jPt (.slk s) w) (jPt (.pos k f) w') ↔
      f = 0 ∧ k = true ∧ Mid (w 0) (w 1) s ∧ IsBot (w' 1) ∧ w' 0 = w 0 := by
  rw [JSTime, jPt, jPt, FOInterpretation.relMap_map]
  by_cases hf : f = 0 ∧ k = true
  · obtain ⟨rfl, rfl⟩ := hf
    simp [jInterp, bitF, and_assoc]
  · simp [jInterp, bitF, hf]
    tauto

@[simp]
theorem jsTime_pos_left (k : Bool) (f : Fin 3) (w : Fin 2 → A) (q : jInterp.Map A) :
    ¬JSTime (jPt (.pos k f) w) q := by
  obtain ⟨t', w', rfl⟩ := jPt_surj q
  rw [JSTime, jPt, jPt, FOInterpretation.relMap_map]
  cases t' <;> simp [jInterp, bitF]

@[simp]
theorem jsTime_job_right (t : JTag) (w : Fin 2 → A) (s : Bool) (w' : Fin 2 → A) :
    ¬JSTime (jPt t w) (jPt (.lit s) w') ∧ ¬JSTime (jPt t w) (jPt (.slk s) w') := by
  refine ⟨?_, ?_⟩ <;>
    · rw [JSTime, jPt, jPt, FOInterpretation.relMap_map]
      cases t <;> simp [jInterp, bitF]

/-- Only the lowest position of a block ever carries a bit of an execution
time. -/
theorem eq_jLow_of_time {a₀ : A} (ha₀ : IsBot a₀) {i q : jInterp.Map A} (h : JSTime i q)
    (hq : JSPosn q) : ∃ b, q = jLow a₀ b := by
  obtain ⟨t, w, rfl⟩ := jPt_surj i
  obtain ⟨t', w', rfl⟩ := jPt_surj q
  have hlow : ∀ (k : Bool) (f : Fin 3), f = 0 → IsBot (w' 1) →
      ∃ b : Bool × A, jPt (.pos k f) w' = jLow a₀ b := by
    rintro k f rfl hb
    refine ⟨(k, w' 0), ?_⟩
    rw [jLow, jPos]
    exact congrArg (jPt (JTag.pos k 0))
      (tuple₂_ext (by simp) (by simp [(ha₀ (w' 1)).antisymm (hb a₀)]))
  cases t' with
  | lit s => exact absurd hq (jsPosn_lit s w')
  | slk s => exact absurd hq (jsPosn_slk s w')
  | pos k f =>
    cases t with
    | lit s =>
      obtain ⟨hf, -, hb, -⟩ := (jsTime_lit_pos s w k f w').mp h
      exact hlow k f hf hb
    | slk s =>
      obtain ⟨hf, -, -, hb, -⟩ := (jsTime_slk_pos s w k f w').mp h
      exact hlow k f hf hb
    | pos k' f' => exact absurd h (jsTime_pos_left k' f' w _)

/-- The bit of a literal job in a block. -/
theorem jsTime_jLit_jLow {a₀ : A} (ha₀ : IsBot a₀) (s : Bool) (x : A) (b : Bool × A) :
    JSTime (jLit a₀ s x) (jLow a₀ b) ↔ (if b.1 then OccIn b.2 x s else b.2 = x) := by
  rw [jLit, jLow, jPos, jsTime_lit_pos]
  simp [ha₀]

/-- The bit of a slack job in a block. -/
theorem jsTime_jSlk_jLow {a₀ : A} (ha₀ : IsBot a₀) (s : Bool) (c x : A) (b : Bool × A) :
    JSTime (jSlk s c x) (jLow a₀ b) ↔ b.1 = true ∧ b.2 = c ∧ Mid c x s := by
  rw [jSlk, jLow, jPos, jsTime_slk_pos]
  simp [ha₀]
  tauto

end Bits

/-! ### The place values -/

section Places

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

omit [Language.sat.Structure A] [LinearOrder A] in
private theorem key_pos (k : Bool) (f : Fin 3) (w : Fin 2 → A) :
    jKey (jPt (.pos k f) w) = (if k then 5 else 4, w 0, w 1, (f : ℕ)) := by
  cases k <;> rfl

theorem jsLe_pos_pos (k k' : Bool) (f f' : Fin 3) (w w' : Fin 2 → A) :
    JSLe (jPt (.pos k f) w) (jPt (.pos k' f') w') ↔
      (k = false ∧ k' = true) ∨
        (k = k' ∧ (w 0 < w' 0 ∨
          (w 0 = w' 0 ∧ (w 1 < w' 1 ∨ (w 1 = w' 1 ∧ (f : ℕ) ≤ (f' : ℕ)))))) := by
  rw [jsLe_iff, key_pos, key_pos]
  cases k <;> cases k' <;>
    simp [keyLe, lexRel, lt_iff_le_and_ne]

variable [Finite A]

omit [Language.sat.Structure A] in
/-- How many indices of a block lie below a given one. -/
private theorem ncard_fin_lt (f : Fin 3) :
    ({f' : Fin 3 | (f' : ℕ) < (f : ℕ)} : Set (Fin 3)).ncard = (f : ℕ) := by
  fin_cases f
  · have : {f' : Fin 3 | (f' : ℕ) < (0 : ℕ)} = (∅ : Set (Fin 3)) := by
      ext f'
      simp
    rw [this, Set.ncard_empty]
  · have : {f' : Fin 3 | (f' : ℕ) < (1 : ℕ)} = ({0} : Set (Fin 3)) := by
      ext f'
      fin_cases f' <;> simp
    rw [this, Set.ncard_singleton]
  · have : {f' : Fin 3 | (f' : ℕ) < (2 : ℕ)} = ({0, 1} : Set (Fin 3)) := by
      ext f'
      fin_cases f' <;> simp
    rw [this, Set.ncard_pair (by decide)]

/-- **The block structure**: the rank of the `f`-th position of a block is
`3 |A|` times the rank of the block, plus `f`, so its place value is
`(2 ^ (3 |A|)) ^ rank · 2 ^ f` – one digit of base `2 ^ (3 |A|)` per block,
whose bits are the positions of that block, in order. -/
theorem bitRank_jPos {a₀ : A} (ha₀ : IsBot a₀) (f : Fin 3) (k : Bool) (e : A) :
    bitRank (JSLe (A := jInterp.Map A)) JSPosn (jPos f (k, e) a₀) =
      3 * Nat.card A * blkRank (k, e) + (f : ℕ) := by
  classical
  have hset : {q : jInterp.Map A | JSPosn q ∧ JSLe q (jPos f (k, e) a₀) ∧
      q ≠ jPos f (k, e) a₀} =
      ((fun u : (Bool × A) × Fin 3 × A => jPos u.2.1 u.1 u.2.2) ''
          ({b' : Bool × A | blkLe b' (k, e) ∧ b' ≠ (k, e)} ×ˢ Set.univ)) ∪
        ((fun f' : Fin 3 => jPos f' (k, e) a₀) '' {f' : Fin 3 | (f' : ℕ) < (f : ℕ)}) := by
    ext q
    obtain ⟨t, w, rfl⟩ := jPt_surj q
    constructor
    · rintro ⟨hp, hle, hne⟩
      cases t with
      | lit s => exact absurd hp (jsPosn_lit s w)
      | slk s => exact absurd hp (jsPosn_slk s w)
      | pos k' f' =>
        rw [jPos_eq, jsLe_pos_pos] at hle
        by_cases hb : blkLe (k', w 0) (k, e) ∧ (k', w 0) ≠ (k, e)
        · exact Or.inl ⟨((k', w 0), f', w 1), ⟨hb, Set.mem_univ _⟩,
            (congrArg (jPt (JTag.pos k' f')) (tuple₂_ext (by simp) (by simp))).symm⟩
        · -- inside the block of `(k, e)`: only a lower index lies below
          have hkk : k' = k := by
            rcases hle with ⟨h₁, h₂⟩ | ⟨h, -⟩
            · exact absurd (blkLt_iff.mpr (Or.inr ⟨h₁, h₂⟩)) hb
            · exact h
          subst hkk
          have hrest : w 0 = e ∧ (w 1 < a₀ ∨ (w 1 = a₀ ∧ (f' : ℕ) ≤ (f : ℕ))) := by
            rcases hle with ⟨h₁, h₂⟩ | ⟨-, h⟩
            · exact absurd (blkLt_iff.mpr (Or.inr ⟨h₁, h₂⟩)) hb
            · rcases h with h | ⟨he, h⟩
              · exact absurd (blkLt_iff.mpr (Or.inl ⟨rfl, h⟩)) hb
              · exact ⟨he, h⟩
          obtain ⟨hwe, hrest⟩ := hrest
          have hy : w 1 = a₀ := by
            rcases hrest with h | ⟨h, -⟩
            · exact absurd h (not_lt.mpr (ha₀ (w 1)))
            · exact h
          have hf : (f' : ℕ) ≤ (f : ℕ) := by
            rcases hrest with h | ⟨-, h⟩
            · exact absurd h (not_lt.mpr (ha₀ (w 1)))
            · exact h
          have hpt : jPt (JTag.pos k' f') w = jPos f' (k', e) a₀ := by
            rw [jPos_eq]
            exact congrArg (jPt (JTag.pos k' f')) (tuple₂_ext (by simpa using hwe)
              (by simpa using hy))
          have hlt : (f' : ℕ) < (f : ℕ) := by
            rcases Nat.lt_or_ge (f' : ℕ) (f : ℕ) with h | h
            · exact h
            · exfalso
              have hfeq : f' = f := Fin.ext (Nat.le_antisymm hf h)
              exact hne (by rw [hpt, hfeq])
          exact Or.inr ⟨f', hlt, hpt.symm⟩
    · rintro (⟨⟨⟨k', x⟩, f', y⟩, ⟨hb, -⟩, hq⟩ | ⟨f', hlt, hq⟩)
      · obtain ⟨ht, hw⟩ := jPt_eq_iff.mp hq.symm
        subst ht
        subst hw
        rcases blkLt_iff.mp hb with hb' | hb'
        · refine ⟨jsPosn_pos _ _ _, ?_, ?_⟩
          · rw [jPos_eq, jsLe_pos_pos]
            exact Or.inr ⟨hb'.1, Or.inl (by simpa using hb'.2)⟩
          · intro hcon
            rw [jPos_eq] at hcon
            obtain ⟨-, hw⟩ := jPt_eq_iff.mp hcon
            exact absurd (by simpa using congrArg (fun u : Fin 2 → A => u 0) hw)
              (ne_of_lt hb'.2)
        · refine ⟨jsPosn_pos _ _ _, ?_, ?_⟩
          · rw [jPos_eq, jsLe_pos_pos]
            exact Or.inl ⟨hb'.1, hb'.2⟩
          · intro hcon
            rw [jPos_eq] at hcon
            obtain ⟨ht, -⟩ := jPt_eq_iff.mp hcon
            have hkk : k' = k := by injection ht
            rw [hb'.1, hb'.2] at hkk
            exact absurd hkk (by decide)
      · obtain ⟨ht, hw⟩ := jPt_eq_iff.mp hq.symm
        subst ht
        subst hw
        refine ⟨jsPosn_pos _ _ _, ?_, ?_⟩
        · rw [jPos_eq, jsLe_pos_pos]
          exact Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, le_of_lt hlt⟩⟩⟩
        · intro hcon
          rw [jPos_eq] at hcon
          obtain ⟨ht, -⟩ := jPt_eq_iff.mp hcon
          have hfeq : f' = f := by injection ht
          exact absurd (congrArg (fun g : Fin 3 => (g : ℕ)) hfeq) (ne_of_lt hlt)
  have hdisj : Disjoint
      ((fun u : (Bool × A) × Fin 3 × A => jPos u.2.1 u.1 u.2.2) ''
          ({b' : Bool × A | blkLe b' (k, e) ∧ b' ≠ (k, e)} ×ˢ Set.univ))
      ((fun f' : Fin 3 => jPos f' (k, e) a₀) '' {f' : Fin 3 | (f' : ℕ) < (f : ℕ)}) := by
    rw [Set.disjoint_left]
    rintro q ⟨⟨⟨k', x⟩, f', y⟩, ⟨hb, -⟩, rfl⟩ ⟨f'', -, hq⟩
    simp only [jPos_eq] at hq
    obtain ⟨ht, hw⟩ := jPt_eq_iff.mp hq
    have hk : k = k' := by injection ht
    have hx : e = x := by simpa using congrArg (fun u : Fin 2 → A => u 0) hw
    exact hb.2 (Prod.ext hk.symm hx.symm)
  have hinj : Set.InjOn (fun f' : Fin 3 => jPos f' (k, e) a₀)
      {f' : Fin 3 | (f' : ℕ) < (f : ℕ)} := by
    intro f₁ _ f₂ _ h
    simp only [jPos_eq] at h
    obtain ⟨ht, -⟩ := jPt_eq_iff.mp h
    injection ht
  have hcard : Nat.card (Fin 3 × A) = 3 * Nat.card A := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hset' : {q : Bool × A | (fun _ => True) q ∧ blkLe q (k, e) ∧ q ≠ (k, e)} =
      {b' : Bool × A | blkLe b' (k, e) ∧ b' ≠ (k, e)} := by
    ext q
    simp
  rw [bitRank, hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    jPos_injective.injOn.ncard_image, hinj.ncard_image, Set.ncard_prod, Set.ncard_univ,
    ncard_fin_lt, blkRank, bitRank, hset', hcard, Nat.mul_comm]

end Places

/-! ### Execution times, as base-`2 ^ (3 |A|)` numbers -/

section Numbers

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- The base: one digit per block, `3 |A|` bits wide, which is above every
digit the gadget writes, so digits never carry into the next block. -/
noncomputable def jbase (A : Type) [Finite A] : ℕ := 2 ^ (3 * Nat.card A)

omit [Language.sat.Structure A] [LinearOrder A] in
theorem jbase_pos : 0 < jbase A := by
  rw [jbase]
  positivity

open Classical in
/-- **A number written by one bit per block**, the bit of a block sitting at
the height `g b` inside it, is the base-`2 ^ (3 |A|)` number with digit
`2 ^ g b` there. -/
theorem binNum_eq_digit {a₀ : A} (ha₀ : IsBot a₀) {p : jInterp.Map A → Prop}
    {sub : Bool × A → Prop} {g : Bool × A → Fin 3}
    (hp : ∀ q : jInterp.Map A, (JSPosn q ∧ p q) ↔ ∃ b, sub b ∧ q = jPos (g b) b a₀) :
    binNum (JSLe (A := jInterp.Map A)) JSPosn p =
      digitNum (blkLe (A := A)) (fun _ => True) (jbase A)
        (fun b => if sub b then 2 ^ (g b : ℕ) else 0) := by
  classical
  have hinj : Set.InjOn (fun b : Bool × A => jPos (g b) b a₀) {b | sub b} := by
    intro b _ b' _ h
    obtain ⟨ht, hw⟩ := jPt_eq_iff.mp h
    have h0 : b.2 = b'.2 := by simpa using congrArg (fun u : Fin 2 → A => u 0) hw
    have h1 : b.1 = b'.1 := by injection ht
    exact Prod.ext h1 h0
  have hset : {q : jInterp.Map A | JSPosn q ∧ p q} =
      (fun b : Bool × A => jPos (g b) b a₀) '' {b | sub b} := by
    ext q
    rw [Set.mem_setOf_eq, hp q]
    exact ⟨fun ⟨b, hb, hq⟩ => ⟨b, hb, hq.symm⟩, fun ⟨b, hb, hq⟩ => ⟨b, hb, hq.symm⟩⟩
  rw [binNum, hset, finsum_mem_image hinj]
  refine (finsum_mem_congr rfl fun b _ => ?_).trans
    (finsum_coeff_eq_digitNum (fun b => 2 ^ (g b : ℕ)) fun _ _ => trivial)
  rw [bitRank_jPos ha₀, jbase, pow_add, pow_mul, blkRank, Nat.mul_comm]

open Classical in
/-- **Every execution time is read digit by digit**: the digit of a block is
`1` when the job carries a bit at its lowest position, and `0` otherwise. -/
theorem jsTimeVal_eq {a₀ : A} (ha₀ : IsBot a₀) (i : jInterp.Map A) :
    JSTimeVal i = digitNum (blkLe (A := A)) (fun _ => True) (jbase A)
      (fun b => if JSTime i (jLow a₀ b) then 1 else 0) := by
  classical
  refine (binNum_eq_digit (sub := fun b => JSTime i (jLow a₀ b)) (g := fun _ => 0) ha₀
    fun q => ?_).trans (digitNum_congr_on ?_)
  · constructor
    · rintro ⟨hq, hbit⟩
      obtain ⟨b, rfl⟩ := eq_jLow_of_time ha₀ hbit hq
      exact ⟨b, hbit, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨jsPosn_pos _ _ _, hb⟩
  · intro b _
    by_cases hb : JSTime i (jLow a₀ b) <;> simp [hb]

open Classical in
/-- **The total execution time of a set of jobs**, read digit by digit: the
digit of a block is the number of selected jobs carrying a bit there. -/
theorem sum_times_eq {a₀ : A} (ha₀ : IsBot a₀) (S : jInterp.Map A → Prop) :
    (∑ᶠ i ∈ {i | S i}, JSTimeVal i) =
      digitNum (blkLe (A := A)) (fun _ => True) (jbase A)
        (fun b => ({i : jInterp.Map A | S i ∧ JSTime i (jLow a₀ b)} : Set _).ncard) := by
  classical
  haveI : Finite (jInterp.Map A) := jInterp.map_finite A
  have h₁ : (∑ᶠ i ∈ {i | S i}, JSTimeVal i) =
      ∑ᶠ i ∈ {i | S i}, digitNum (blkLe (A := A)) (fun _ => True) (jbase A)
        (fun b => if JSTime i (jLow a₀ b) then 1 else 0) :=
    finsum_mem_congr rfl fun i _ => jsTimeVal_eq ha₀ i
  rw [h₁, digitNum_finsum]
  refine digitNum_congr_on fun b _ => ?_
  refine (finsum_mem_ite_one (ι := jInterp.Map A) _ _).trans ?_
  exact congrArg Set.ncard (by ext i; simp)

end Numbers

/-! ### Counting the jobs of a block -/

section Counting

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- The number of selected jobs carrying a bit in a block: the digit that
block contributes to the total execution time of the selection. -/
noncomputable def cnt (a₀ : A) (S : jInterp.Map A → Prop) (b : Bool × A) : ℕ :=
  ({i : jInterp.Map A | S i ∧ JSTime i (jLow a₀ b)} : Set _).ncard

theorem sum_times_eq_cnt {a₀ : A} (ha₀ : IsBot a₀) (S : jInterp.Map A → Prop) :
    (∑ᶠ i ∈ {i | S i}, JSTimeVal i) =
      digitNum (blkLe (A := A)) (fun _ => True) (jbase A) (cnt a₀ S) :=
  sum_times_eq ha₀ S

/-- A selection and the jobs it leaves out split every digit. -/
theorem cnt_add_cnt (a₀ : A) {S : jInterp.Map A → Prop} (hS : ∀ i, S i → JSJob i)
    (b : Bool × A) :
    cnt a₀ S b + cnt a₀ (fun i => JSJob i ∧ ¬S i) b = cnt a₀ JSJob b := by
  haveI : Finite (jInterp.Map A) := jInterp.map_finite A
  rw [cnt, cnt, cnt, ← Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _)]
  · congr 1
    ext i
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hi, hb⟩ | ⟨⟨hi, -⟩, hb⟩)
      · exact ⟨hS i hi, hb⟩
      · exact ⟨hi, hb⟩
    · rintro ⟨hi, hb⟩
      by_cases h : S i
      · exact Or.inl ⟨h, hb⟩
      · exact Or.inr ⟨⟨hi, h⟩, hb⟩
  · rw [Set.disjoint_left]
    rintro i ⟨hi, -⟩ ⟨⟨-, hn⟩, -⟩
    exact hn hi

/-! #### Which jobs carry a bit in a block -/

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem jLow_eq (a₀ : A) (k : Bool) (e : A) : jLow a₀ (k, e) = jPt (.pos k 0) ![e, a₀] := rfl

omit [Finite A] in
/-- The jobs carrying a bit in a variable block are the two literals of that
variable. -/
theorem time_jLow_var {a₀ : A} (ha₀ : IsBot a₀) (x : A) (i : jInterp.Map A) :
    JSTime i (jLow a₀ (false, x)) ↔ ∃ s, i = jLit a₀ s x := by
  have hbot : ∀ y : A, IsBot y → y = a₀ := fun y hy => le_antisymm (hy a₀) (ha₀ y)
  obtain ⟨t, w, rfl⟩ := jPt_surj i
  rw [jLow_eq]
  cases t with
  | lit s =>
    rw [jsTime_lit_pos]
    constructor
    · rintro ⟨-, hb, -, he⟩
      have hx : x = w 0 := by simpa using he
      refine ⟨s, ?_⟩
      rw [jLit, hx]
      exact congrArg (jPt (JTag.lit s)) (tuple₂_ext (by simp) (by simp [hbot (w 1) hb]))
    · rintro ⟨s', hs⟩
      rw [jLit] at hs
      obtain ⟨ht, hw⟩ := jPt_eq_iff.mp hs
      cases ht
      subst hw
      exact ⟨rfl, by simpa using ha₀, by simpa using ha₀, by simp⟩
  | slk s =>
    rw [jsTime_slk_pos]
    constructor
    · rintro ⟨-, hk, -⟩
      exact absurd hk (by simp)
    · rintro ⟨s', hs⟩
      exact absurd (jPt_eq_iff.mp hs).1 (by simp)
  | pos k f =>
    constructor
    · intro h
      exact absurd h (jsTime_pos_left k f w _)
    · rintro ⟨s', hs⟩
      exact absurd (jPt_eq_iff.mp hs).1 (by simp)

omit [Finite A] in
/-- The jobs carrying a bit in a clause block are the literals occurring in
the clause and its slack jobs. -/
theorem time_jLow_cls {a₀ : A} (ha₀ : IsBot a₀) (c : A) (i : jInterp.Map A) :
    JSTime i (jLow a₀ (true, c)) ↔
      (∃ p : A × Bool, OccIn c p.1 p.2 ∧ i = jLit a₀ p.2 p.1) ∨
        (∃ p : A × Bool, Mid c p.1 p.2 ∧ i = jSlk p.2 c p.1) := by
  have hbot : ∀ y : A, IsBot y → y = a₀ := fun y hy => le_antisymm (hy a₀) (ha₀ y)
  obtain ⟨t, w, rfl⟩ := jPt_surj i
  rw [jLow_eq]
  cases t with
  | lit s =>
    rw [jsTime_lit_pos]
    constructor
    · rintro ⟨-, hb, -, hocc⟩
      refine Or.inl ⟨(w 0, s), by simpa using hocc, ?_⟩
      rw [jLit]
      exact congrArg (jPt (JTag.lit s)) (tuple₂_ext (by simp) (by simp [hbot (w 1) hb]))
    · rintro (⟨⟨y, r⟩, hocc, hs⟩ | ⟨⟨y, r⟩, -, hs⟩)
      · rw [jLit] at hs
        obtain ⟨ht, hw⟩ := jPt_eq_iff.mp hs
        cases ht
        subst hw
        exact ⟨rfl, by simpa using ha₀, by simpa using ha₀, by simpa using hocc⟩
      · exact absurd (jPt_eq_iff.mp hs).1 (by simp)
  | slk s =>
    rw [jsTime_slk_pos]
    constructor
    · rintro ⟨-, -, hmid, -, hc⟩
      have hc' : c = w 0 := by simpa using hc
      refine Or.inr ⟨(w 1, s), ?_, ?_⟩
      · rw [hc']
        exact hmid
      · rw [jSlk]
        exact congrArg (jPt (JTag.slk s)) (tuple₂_ext (by simp [hc']) (by simp))
    · rintro (⟨⟨y, r⟩, -, hs⟩ | ⟨⟨y, r⟩, hmid, hs⟩)
      · exact absurd (jPt_eq_iff.mp hs).1 (by simp)
      · rw [jSlk] at hs
        obtain ⟨ht, hw⟩ := jPt_eq_iff.mp hs
        cases ht
        subst hw
        exact ⟨rfl, rfl, by simpa using hmid, by simpa using ha₀, by simp⟩
  | pos k f =>
    constructor
    · intro h
      exact absurd h (jsTime_pos_left k f w _)
    · rintro (⟨⟨y, r⟩, -, hs⟩ | ⟨⟨y, r⟩, -, hs⟩) <;>
        exact absurd (jPt_eq_iff.mp hs).1 (by simp)

/-! #### The digits, block by block -/

omit [Finite A] in
/-- The digit of a variable block counts the selected literals of that
variable. -/
theorem cnt_var {a₀ : A} (ha₀ : IsBot a₀) (S : jInterp.Map A → Prop) (x : A) :
    cnt a₀ S (false, x) = ({s : Bool | S (jLit a₀ s x)} : Set Bool).ncard := by
  have hinj : Set.InjOn (fun s : Bool => jLit a₀ s x) {s | S (jLit a₀ s x)} := by
    intro s _ s' _ h
    have ht := congrArg (fun q : jInterp.Map A => q.1) h
    simpa [jLit, jPt] using ht
  have hset : {i : jInterp.Map A | S i ∧ JSTime i (jLow a₀ (false, x))} =
      (fun s : Bool => jLit a₀ s x) '' {s | S (jLit a₀ s x)} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hi, hb⟩
      obtain ⟨s, rfl⟩ := (time_jLow_var ha₀ x i).mp hb
      exact ⟨s, hi, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, (time_jLow_var ha₀ x _).mpr ⟨s, rfl⟩⟩
  rw [cnt, hset, hinj.ncard_image]

open Classical in
/-- The digit of a clause block counts the selected literals occurring in the
clause and its selected slack jobs. -/
theorem cnt_cls {a₀ : A} (ha₀ : IsBot a₀) (S : jInterp.Map A → Prop) (c : A) :
    cnt a₀ S (true, c) =
      ({p ∈ OccSet c | S (jLit a₀ p.2 p.1)} : Set (A × Bool)).ncard +
        ({p ∈ MidSet c | S (jSlk p.2 c p.1)} : Set (A × Bool)).ncard := by
  classical
  haveI : Finite (jInterp.Map A) := jInterp.map_finite A
  have hset : {i : jInterp.Map A | S i ∧ JSTime i (jLow a₀ (true, c))} =
      ((fun p : A × Bool => jLit a₀ p.2 p.1) '' {p ∈ OccSet c | S (jLit a₀ p.2 p.1)}) ∪
        ((fun p : A × Bool => jSlk p.2 c p.1) '' {p ∈ MidSet c | S (jSlk p.2 c p.1)}) := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hi, hb⟩
      rcases (time_jLow_cls ha₀ c i).mp hb with ⟨p, hocc, rfl⟩ | ⟨p, hmid, rfl⟩
      · exact Or.inl ⟨p, ⟨hocc, hi⟩, rfl⟩
      · exact Or.inr ⟨p, ⟨hmid, hi⟩, rfl⟩
    · rintro (⟨p, ⟨hocc, hs⟩, rfl⟩ | ⟨p, ⟨hmid, hs⟩, rfl⟩)
      · exact ⟨hs, (time_jLow_cls ha₀ c _).mpr (Or.inl ⟨p, hocc, rfl⟩)⟩
      · exact ⟨hs, (time_jLow_cls ha₀ c _).mpr (Or.inr ⟨p, hmid, rfl⟩)⟩
  have hd : Disjoint
      ((fun p : A × Bool => jLit a₀ p.2 p.1) '' {p ∈ OccSet c | S (jLit a₀ p.2 p.1)})
      ((fun p : A × Bool => jSlk p.2 c p.1) '' {p ∈ MidSet c | S (jSlk p.2 c p.1)}) := by
    rw [Set.disjoint_left]
    rintro i ⟨p, -, rfl⟩ ⟨q, -, hq⟩
    exact absurd hq.symm (jLit_ne_jSlk a₀ p.2 q.2 p.1 c q.1)
  rw [cnt, hset, Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _),
    (jLit_injective a₀).injOn.ncard_image, (jSlk_injective c).injOn.ncard_image]

omit [Finite A] in
/-- Every variable block totals two: a balanced split takes exactly one of the
two literals of the variable. -/
theorem cnt_job_var {a₀ : A} (ha₀ : IsBot a₀) (x : A) : cnt a₀ JSJob (false, x) = 2 := by
  rw [cnt_var ha₀]
  have hset : {s : Bool | JSJob (jLit a₀ s x)} = Set.univ := by
    ext s
    simp [jLit, ha₀]
  rw [hset, Set.ncard_univ]
  simp

/-- A clause block totals its occurrences plus its slack occurrences. -/
theorem cnt_job_cls {a₀ : A} (ha₀ : IsBot a₀) (c : A) :
    cnt a₀ JSJob (true, c) = (OccSet c).ncard + (MidSet c).ncard := by
  have h₁ : {p ∈ OccSet c | JSJob (jLit a₀ p.2 p.1)} = OccSet c := by
    ext p
    simp [jLit, ha₀]
  have h₂ : {p ∈ MidSet c | JSJob (jSlk p.2 c p.1)} = MidSet c := by
    ext p
    simp [jSlk, MidSet]
  rw [cnt_cls ha₀, h₁, h₂]

end Counting

/-! ### The digits stay below the base -/

section Bound

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

omit [Language.sat.Structure A] [LinearOrder A] in
theorem ncard_le_two_card (X : Set (A × Bool)) : X.ncard ≤ 2 * Nat.card A := by
  have h1 : X.ncard ≤ (Set.univ : Set (A × Bool)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ X) (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have hb : Nat.card (A × Bool) = Nat.card A * 2 := by
    rw [Nat.card_prod]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  omega

/-- A selection weighs at most as much as all the jobs, digit by digit. -/
theorem cnt_le (a₀ : A) {S : jInterp.Map A → Prop} (hS : ∀ i, S i → JSJob i) (b : Bool × A) :
    cnt a₀ S b ≤ cnt a₀ JSJob b := by
  haveI : Finite (jInterp.Map A) := jInterp.map_finite A
  exact Set.ncard_le_ncard (fun i hi => ⟨hS i hi.1, hi.2⟩) (Set.toFinite _)

variable [Nonempty A]

/-- **No carry**: every digit the gadget writes stays below the base, `3 |A|`
bits being more than the `4 |A|` jobs a block can hold. -/
theorem cnt_job_lt_jbase {a₀ : A} (ha₀ : IsBot a₀) (b : Bool × A) :
    cnt a₀ JSJob b < jbase A := by
  classical
  have hn : 1 ≤ Nat.card A := Nat.card_pos
  have hkey : 4 * Nat.card A + 1 < jbase A := by
    have h1 : Nat.card A + 1 ≤ 2 ^ Nat.card A := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ (Nat.card A + 2) ≤ 2 ^ (3 * Nat.card A) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 : ℕ) ^ (Nat.card A + 2) = 2 ^ Nat.card A * 4 := by
      rw [pow_add]
      norm_num
    rw [jbase]
    omega
  obtain ⟨k, e⟩ := b
  cases k with
  | false =>
    rw [cnt_job_var ha₀]
    omega
  | true =>
    rw [cnt_job_cls ha₀]
    have h1 := ncard_le_two_card (OccSet e)
    have h2 := ncard_le_two_card (MidSet e)
    omega

end Bound

/-! ### The deadline, and the bound

Both are the *digit-wise half* of the total execution time: one bit per
block, at its base when the digit is `1` – a variable block, or the block of a
clause of width two – and one position up when it is `2` – the block of a
clause of width three. -/

section Deadline

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

open Classical in
/-- The digit the deadline writes in a block: `1` in every variable block, and
in a clause block the width minus one. A degenerate input gets the deadline
`0`. -/
noncomputable def dd (b : Bool × A) : ℕ :=
  if Deg A then 0
  else if b.1 = false then 1
  else if IsCl b.2 then (if ∃ x s, Mid b.2 x s then 2 else 1)
  else 0

/-- The value of the deadline: the digit-wise half. -/
noncomputable def dval (A : Type) [Language.sat.Structure A] [LinearOrder A] [Finite A] : ℕ :=
  digitNum (blkLe (A := A)) (fun _ => True) (jbase A) dd

omit [Finite A] in
theorem dd_deg (hdeg : Deg A) (b : Bool × A) : dd b = 0 := by
  rw [dd, if_pos hdeg]

omit [Finite A] in
theorem dd_var (hdeg : ¬Deg A) (x : A) : dd ((false, x) : Bool × A) = 1 := by
  rw [dd, if_neg hdeg, if_pos rfl]

open Classical in
omit [Finite A] in
theorem dd_cls (hdeg : ¬Deg A) {c : A} (hc : IsCl c) :
    dd ((true, c) : Bool × A) = if ∃ x s, Mid c x s then 2 else 1 := by
  rw [dd, if_neg hdeg, if_neg (by simp), if_pos hc]

omit [Finite A] in
theorem dd_not_cls (c : A) (hc : ¬IsCl c) : dd ((true, c) : Bool × A) = 0 := by
  rw [dd]
  by_cases h : Deg A
  · rw [if_pos h]
  · rw [if_neg h, if_neg (by simp), if_neg hc]

omit [Finite A] in
theorem dd_le_two (b : Bool × A) : dd b ≤ 2 := by
  classical
  rw [dd]
  split_ifs <;> omega

theorem dd_lt_jbase [Nonempty A] (b : Bool × A) : dd b < jbase A := by
  have h1 := dd_le_two b
  have hn : 1 ≤ Nat.card A := Nat.card_pos
  have h2 : (2 : ℕ) ^ 2 ≤ 2 ^ (3 * Nat.card A) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [jbase]
  norm_num at h2
  omega

/-- Where the deadline writes its bit in a block: at the base, unless the
block totals four. -/
noncomputable def dht (b : Bool × A) : Fin 3 := if dd b = 2 then 1 else 0

omit [Finite A] in
theorem dbit_pos {a₀ : A} (ha₀ : IsBot a₀) (k : Bool) (f : Fin 3) (w : Fin 2 → A) :
    (∃ b : Bool × A, dd b ≠ 0 ∧ jPt (.pos k f) w = jPos (dht b) b a₀) ↔
      (IsBot (w 1) ∧ dd (k, w 0) ≠ 0 ∧ dht (k, w 0) = f) := by
  constructor
  · rintro ⟨⟨k', e⟩, hne, hq⟩
    rw [jPos] at hq
    obtain ⟨ht, hw⟩ := jPt_eq_iff.mp hq
    have hk : k = k' := by injection ht
    have hf : f = dht (k', e) := by injection ht
    have h0 : w 0 = e := by simpa using congrArg (fun u : Fin 2 → A => u 0) hw
    have h1 : w 1 = a₀ := by simpa using congrArg (fun u : Fin 2 → A => u 1) hw
    subst hk
    subst h0
    exact ⟨by rw [h1]; exact ha₀, hne, hf.symm⟩
  · rintro ⟨hb, hne, hf⟩
    refine ⟨(k, w 0), hne, ?_⟩
    rw [jPos, hf]
    exact congrArg (jPt (JTag.pos k f))
      (tuple₂_ext (by simp) (by simp [(ha₀ (w 1)).antisymm (hb a₀)]))

omit [Finite A] in
/-- What the deadline's bit pattern says, formula-free. -/
theorem realize_dbitF {α : Type} {v : α → A} (k : Bool) (f : Fin 3) (e y : α) :
    (dbitF k f e y).Realize v ↔
      IsBot (v y) ∧
        ((k = false ∧ f = 0) ∨ (k = true ∧ f = 0 ∧ IsCl (v e) ∧ ¬∃ x s, Mid (v e) x s) ∨
          (k = true ∧ f = 1 ∧ IsCl (v e) ∧ ∃ x s, Mid (v e) x s)) ∧ ¬Deg A := by
  rw [dbitF]
  split_ifs with h1 h2 h3 <;> simp_all [and_assoc]

omit [Finite A] in
theorem jsBnd_pos (k : Bool) (f : Fin 3) (w : Fin 2 → A) :
    JSBnd (jPt (.pos k f) w) ↔ IsBot (w 1) ∧ dd (k, w 0) ≠ 0 ∧ dht (k, w 0) = f := by
  classical
  rw [JSBnd, jPt, FOInterpretation.relMap_map]
  by_cases hdeg : Deg A
  · rw [dht, dd_deg hdeg]
    cases k <;> fin_cases f <;> simp [jInterp, bndF, dbitF, hdeg]
  · cases k with
    | false =>
      rw [dht, dd_var hdeg]
      fin_cases f <;> simp [jInterp, bndF, dbitF, hdeg]
    | true =>
      by_cases hc : IsCl (w 0)
      · by_cases hm : ∃ x s, Mid (w 0) x s
        · have hm' : ∃ x, Mid (w 0) x false ∨ Mid (w 0) x true := by
            obtain ⟨x, s, h⟩ := hm
            cases s
            exacts [⟨x, Or.inl h⟩, ⟨x, Or.inr h⟩]
          rw [dht, dd_cls hdeg hc, if_pos hm]
          fin_cases f <;> simp [jInterp, bndF, dbitF, hdeg, hc, hm']
        · have hm' : ∀ x : A, ¬Mid (w 0) x false ∧ ¬Mid (w 0) x true := fun x =>
            ⟨fun h => hm ⟨x, false, h⟩, fun h => hm ⟨x, true, h⟩⟩
          rw [dht, dd_cls hdeg hc, if_neg hm]
          fin_cases f <;> simp [jInterp, bndF, dbitF, hdeg, hc, hm']
      · rw [dht, dd_not_cls _ hc]
        fin_cases f <;> simp [jInterp, bndF, dbitF, hdeg, hc]

omit [Finite A] in
@[simp]
theorem jsBnd_lit (s : Bool) (w : Fin 2 → A) : ¬JSBnd (jPt (.lit s) w) := by
  rw [JSBnd, jPt, FOInterpretation.relMap_map]
  simp [jInterp, bndF]

omit [Finite A] in
@[simp]
theorem jsBnd_slk (s : Bool) (w : Fin 2 → A) : ¬JSBnd (jPt (.slk s) w) := by
  rw [JSBnd, jPt, FOInterpretation.relMap_map]
  simp [jInterp, bndF]

/-- **The bound is the digit-wise half**: it carries one bit per block, at the
height its digit asks for. -/
theorem jsBound_eq {a₀ : A} (ha₀ : IsBot a₀) : JSBound (jInterp.Map A) = dval A := by
  classical
  rw [JSBound, dval]
  refine (binNum_eq_digit (sub := fun b => dd b ≠ 0) (g := dht) ha₀ fun q => ?_).trans
    (digitNum_congr_on fun b _ => ?_)
  · obtain ⟨t, w, rfl⟩ := jPt_surj q
    cases t with
    | lit s =>
      simp only [jsPosn_lit, false_and, false_iff]
      rintro ⟨b, -, hq⟩
      rw [jPos] at hq
      exact absurd (jPt_eq_iff.mp hq).1 (by simp)
    | slk s =>
      simp only [jsPosn_slk, false_and, false_iff]
      rintro ⟨b, -, hq⟩
      rw [jPos] at hq
      exact absurd (jPt_eq_iff.mp hq).1 (by simp)
    | pos k f =>
      refine Iff.trans ?_ (dbit_pos ha₀ k f w).symm
      exact (and_iff_right (jsPosn_pos k f w)).trans (jsBnd_pos k f w)
  · have h2 := dd_le_two b
    rw [dht]
    by_cases h0 : dd b = 0
    · simp [h0]
    · by_cases h1 : dd b = 2
      · simp [h1]
      · have h3 : dd b = 1 := by omega
        simp [h3]

omit [Finite A] in
/-- The deadline of a job is the bound: the two are defined by the same bit
pattern. -/
theorem jsDline_iff (i q : jInterp.Map A) : JSDline i q ↔ JSJob i ∧ JSBnd q := by
  obtain ⟨t, w, rfl⟩ := jPt_surj i
  obtain ⟨t', w', rfl⟩ := jPt_surj q
  rw [JSDline, JSJob, JSBnd, jPt, jPt, FOInterpretation.relMap_map,
    FOInterpretation.relMap_map, FOInterpretation.relMap_map]
  cases t <;> cases t' <;> simp [jInterp, dlineF, jobF, bndF, realize_dbitF]

omit [Finite A] in
theorem jsDlineVal_eq {j : jInterp.Map A} (hj : JSJob j) :
    JSDlineVal j = JSBound (jInterp.Map A) := by
  rw [JSDlineVal, JSBound]
  exact binNum_congr fun p =>
    ⟨fun h => ((jsDline_iff j p).mp h).2, fun h => (jsDline_iff j p).mpr ⟨hj, h⟩⟩

omit [Finite A] in
theorem jsPenVal_eq {j : jInterp.Map A} : JSPenVal j = JSTimeVal j :=
  binNum_congr fun p => jsPen_iff_jsTime j p

end Deadline

/-! ### Every block totals twice the deadline's digit -/

section Half

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- A clause of a non-degenerate input has at least two occurrences. -/
theorem two_le_ncard_occSet (hd : ¬Deg A) {c : A} (hc : IsCl c) : 2 ≤ (OccSet c).ncard := by
  obtain ⟨x, s, hch⟩ := exists_chained_of_not_deg hd hc
  have hex : ∃ y t, OccIn c y t ∧ occLt y t x s := by
    by_contra h
    exact hch.2 ⟨hch.1, fun y t hy hlt => h ⟨y, t, hy, hlt⟩⟩
  obtain ⟨y, t, hy, hlt⟩ := hex
  have hne : ((y, t) : A × Bool) ≠ (x, s) := by
    rintro h
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact occLt_irrefl y t hlt
  have hsub : ({(y, t), (x, s)} : Set (A × Bool)) ⊆ OccSet c := by
    rintro ⟨v, r⟩ hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hv
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hy, hch.1]
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair hne] at hcard

/-- Under the width bound a clause has at most one slack occurrence. -/
theorem ncard_midSet_le_one (hwidth : WidthAtMostThree A) (c : A) : (MidSet c).ncard ≤ 1 := by
  rw [Set.ncard_le_one (Set.toFinite _)]
  intro p hp q hq
  obtain ⟨h1, h2⟩ := midSet_subsingleton hwidth hp hq
  exact Prod.ext h1 h2

/-- **The deadline is the digit-wise half**: every block totals twice the
digit the deadline writes there – `2` in a variable block, `2 (w − 1)` in the
block of a clause of width `w ∈ {2, 3}`. -/
theorem two_mul_dd {a₀ : A} (ha₀ : IsBot a₀) (hd : ¬Deg A) (hwidth : WidthAtMostThree A)
    (b : Bool × A) : 2 * dd b = cnt a₀ JSJob b := by
  classical
  obtain ⟨k, c⟩ := b
  cases k with
  | false => rw [cnt_job_var ha₀, dd_var hd]
  | true =>
    rw [cnt_job_cls ha₀]
    by_cases hc : IsCl c
    · have h2 := two_le_ncard_occSet hd hc
      have hmid := card_midSet_add_two h2
      have hle := ncard_midSet_le_one hwidth c
      rw [dd_cls hd hc]
      by_cases hm : ∃ x s, Mid c x s
      · rw [if_pos hm]
        have hpos : 0 < (MidSet c).ncard := by
          obtain ⟨x, s, h⟩ := hm
          exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨(x, s), h⟩
        omega
      · rw [if_neg hm]
        have hzero : (MidSet c).ncard = 0 := by
          rw [Set.ncard_eq_zero (Set.toFinite _)]
          ext p
          simp only [Set.mem_empty_iff_false, iff_false]
          exact fun hp => hm ⟨p.1, p.2, hp⟩
        omega
    · rw [dd_not_cls _ hc]
      have ho : OccSet c = ∅ := by
        ext p
        simp only [OccSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hc h.1
      have hm : MidSet c = ∅ := Set.subset_empty_iff.mp (ho ▸ midSet_subset)
      rw [ho, hm, Set.ncard_empty]

variable [Nonempty A]

omit [Language.sat.Structure A] [Nonempty A] in
/-- A number written by digits below the base is zero only if all its digits
are. -/
theorem digits_eq_zero {c : Bool × A → ℕ} (hc : ∀ b, c b < jbase A)
    (h : digitNum (blkLe (A := A)) (fun _ => True) (jbase A) c = 0) (b : Bool × A) : c b = 0 := by
  have hz : digitNum (blkLe (A := A)) (fun _ => True) (jbase A) (fun _ => 0) = 0 := by
    rw [digitNum]
    simp
  exact digitNum_inj (Le := blkLe (A := A)) isLinOrd_blkLe jbase_pos
    ({b : Bool × A | True} : Set _).ncard (fun _ => True) rfl _ _ hc (fun _ => jbase_pos)
    (h.trans hz.symm) b trivial

/-- **A selection weighs the deadline exactly when it takes half of every
digit**, the digits of both staying below the base. -/
theorem sum_eq_dval_iff {a₀ : A} (ha₀ : IsBot a₀) {S : jInterp.Map A → Prop}
    (hS : ∀ i, S i → JSJob i) :
    ((∑ᶠ i ∈ {i | S i}, JSTimeVal i) = dval A) ↔ ∀ b, cnt a₀ S b = dd b := by
  rw [sum_times_eq_cnt ha₀, dval]
  constructor
  · intro heq b
    exact digitNum_inj (Le := blkLe (A := A)) isLinOrd_blkLe jbase_pos
      ({b : Bool × A | True} : Set _).ncard (fun _ => True) rfl _ _
      (fun b' => lt_of_le_of_lt (cnt_le a₀ hS b') (cnt_job_lt_jbase ha₀ b'))
      (fun b' => dd_lt_jbase b') heq b trivial
  · intro h
    exact digitNum_congr_on fun b _ => h b

end Half

/-! ### The selection made by an assignment -/

section Correctness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- The jobs a not-all-equal assignment selects: those of the true literals,
and the slack jobs chosen by `M`. -/
def splitSet (a₀ : A) (ν : A → Prop) (M : A → Set (A × Bool)) : jInterp.Map A → Prop := fun i =>
  (∃ p : A × Bool, LitTrue ν p.1 p.2 ∧ i = jLit a₀ p.2 p.1) ∨
    (∃ (c : A) (p : A × Bool), p ∈ M c ∧ i = jSlk p.2 c p.1)

variable {a₀ : A} {ν : A → Prop} {M : A → Set (A × Bool)}

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem splitSet_jLit (s : Bool) (x : A) : splitSet a₀ ν M (jLit a₀ s x) ↔ LitTrue ν x s := by
  constructor
  · rintro (⟨p, hT, hp⟩ | ⟨c, p, -, hp⟩)
    · obtain ⟨h₁, h₂⟩ := jLit_eq_iff.mp hp
      rw [h₁, h₂]
      exact hT
    · exact absurd hp (jLit_ne_jSlk a₀ s p.2 x c p.1)
  · intro h
    exact Or.inl ⟨(x, s), h, rfl⟩

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem splitSet_jSlk (s : Bool) (c x : A) :
    splitSet a₀ ν M (jSlk s c x) ↔ (x, s) ∈ M c := by
  constructor
  · rintro (⟨p, -, hp⟩ | ⟨c', p, hp, hq⟩)
    · exact absurd hp.symm (jLit_ne_jSlk a₀ p.2 s p.1 c x)
    · obtain ⟨h₁, h₂, h₃⟩ := jSlk_eq_iff.mp hq
      subst h₂
      have hp' : ((x, s) : A × Bool) = p := Prod.ext h₃ h₁
      rw [hp']
      exact hp
  · intro h
    exact Or.inr ⟨c, (x, s), h, rfl⟩

/-- The true occurrences of a clause under an assignment. -/
def TrueSet (ν : A → Prop) (c : A) : Set (A × Bool) := {p ∈ OccSet c | LitTrue ν p.1 p.2}

end Correctness

/-! ### Correctness of the reduction -/

section Correct

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

private theorem ncard_bool_eq_one {P : Bool → Prop} (h : ({s | P s} : Set Bool).ncard = 1) :
    P false ↔ ¬P true := by
  classical
  by_cases h2 : P true <;> by_cases h3 : P false
  · exfalso
    have hset : {s : Bool | P s} = Set.univ := by
      ext s
      cases s <;> simp [h2, h3]
    rw [hset, Set.ncard_univ] at h
    simp [Nat.card_eq_fintype_card] at h
  · simp [h2, h3]
  · simp [h2, h3]
  · exfalso
    have hset : {s : Bool | P s} = ∅ := by
      ext s
      cases s <;> simp [h2, h3]
    rw [hset, Set.ncard_empty] at h
    exact absurd h (by norm_num)

omit [Finite A] [Nonempty A] in
/-- **A balanced split is an assignment**: the two literals of a variable
split its block, so exactly one of them is selected. -/
theorem litTrue_iff_sel {a₀ : A} (ha₀ : IsBot a₀) {S : jInterp.Map A → Prop}
    (hbal : ∀ b, 2 * cnt a₀ S b = cnt a₀ JSJob b) (x : A) (s : Bool) :
    S (jLit a₀ s x) ↔ LitTrue (fun y => S (jLit a₀ true y)) x s := by
  have h := hbal (false, x)
  rw [cnt_var ha₀, cnt_job_var ha₀] at h
  have h1 : ({s : Bool | S (jLit a₀ s x)} : Set Bool).ncard = 1 := by omega
  cases s with
  | true => exact Iff.rfl
  | false =>
    change S (jLit a₀ false x) ↔ ¬S (jLit a₀ true x)
    exact ncard_bool_eq_one h1

omit [Nonempty A] in
/-- **A balanced split satisfies every clause, not all equal**: if no
occurrence of a clause were selected, its slack – strictly fewer jobs than it
has occurrences – would have to make up for all of them. -/
theorem exists_occ_selected {a₀ : A} (ha₀ : IsBot a₀) (hd : ¬Deg A) {S T : jInterp.Map A → Prop}
    (hcompl : ∀ i, JSJob i → (S i ↔ ¬T i))
    (hbal : ∀ b, cnt a₀ S b = cnt a₀ T b) {c : A} (hc : IsCl c) :
    ∃ p : A × Bool, p ∈ OccSet c ∧ S (jLit a₀ p.2 p.1) := by
  classical
  by_contra hcon
  push Not at hcon
  have hlitem : ∀ p : A × Bool, JSJob (jLit a₀ p.2 p.1) := by
    intro p
    rw [jLit]
    exact (jsJob_lit _ _).mpr (by simpa using ha₀)
  have hlitS : {p ∈ OccSet c | S (jLit a₀ p.2 p.1)} = ∅ := by
    ext p
    simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hp => hcon p hp
  have hlitT : {p ∈ OccSet c | T (jLit a₀ p.2 p.1)} = OccSet c := by
    ext p
    simp only [Set.mem_sep_iff, and_iff_left_iff_imp]
    intro hp
    by_contra hnT
    exact hcon p hp ((hcompl _ (hlitem p)).mpr hnT)
  have hbc := hbal (true, c)
  rw [cnt_cls ha₀, cnt_cls ha₀, hlitS, hlitT, Set.ncard_empty] at hbc
  have hne : (OccSet c).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    have := two_le_ncard_occSet hd hc
    omega
  have hle : ({p ∈ MidSet c | S (jSlk p.2 c p.1)} : Set (A × Bool)).ncard ≤
      (MidSet c).ncard := Set.ncard_le_ncard (fun p hp => hp.1) (Set.toFinite _)
  have hlt := card_midSet_lt hne
  omega

/-- **Correctness of the reduction**: a CNF structure is a yes-instance of
NAE-3SAT iff the interpreted job-sequencing instance has a good schedule. -/
theorem naeThreeSatisfiable_iff_hasGoodSchedule (A : Type) [Language.sat.Structure A]
    [LinearOrder A] [Finite A] [Nonempty A] :
    NAEThreeSatisfiable A ↔ HasGoodSchedule (jInterp.Map A) := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  haveI : Finite (jInterp.Map A) := jInterp.map_finite A
  haveI : LinearOrder (jInterp.Map A) := finiteLinearOrder _
  have hpt : ∀ j : jInterp.Map A, JSJob j → JSPenVal j = JSTimeVal j := fun j _ => jsPenVal_eq
  by_cases hdeg : Deg A
  · -- a degenerate input: no assignment, and no schedule either
    have hdl : ∀ j : jInterp.Map A, JSJob j → JSDlineVal j = 0 := by
      intro j hj
      rw [jsDlineVal_eq hj, jsBound_eq ha₀, dval]
      have hz : dd (A := A) = fun _ => 0 := funext fun b => dd_deg hdeg b
      rw [hz, digitNum]
      simp
    refine iff_of_false ?_ ?_
    · rintro ⟨hw, ν, hν⟩
      rcases hdeg with hwide | ⟨c, hshort⟩
      · exact (ThreeSatToSat.wide_iff_not_widthAtMostThree A).mp hwide hw
      · exact not_naeProper_of_short hshort ν hν
    · intro hgood
      have hbnd : JSBound (jInterp.Map A) = 0 := by
        rw [jsBound_eq ha₀, dval]
        have hz : dd (A := A) = fun _ => 0 := funext fun b => dd_deg hdeg b
        rw [hz, digitNum]
        simp
      rw [hasGoodSchedule_iff_exists_subset isLinOrd_jsLe hdl hpt, hbnd] at hgood
      obtain ⟨S, hSj, hS1, hS2⟩ := hgood
      have e1 := Nat.le_zero.mp hS1
      have e2 := Nat.le_zero.mp hS2
      rw [sum_times_eq_cnt ha₀] at e1 e2
      obtain ⟨x⟩ := ‹Nonempty A›
      have d1 := digits_eq_zero
        (fun b => lt_of_le_of_lt (cnt_le a₀ hSj b) (cnt_job_lt_jbase ha₀ b)) e1 (false, x)
      have d2 := digits_eq_zero
        (fun b => lt_of_le_of_lt (cnt_le a₀ (fun i hi => hi.1) b) (cnt_job_lt_jbase ha₀ b)) e2
        (false, x)
      have hb := cnt_add_cnt a₀ hSj (false, x)
      rw [cnt_job_var ha₀, d1, d2] at hb
      omega
  · -- a proper input: the gadget is a balanced-split instance
    have hwide : ¬ThreeSatToSat.Wide A := fun h => hdeg (Or.inl h)
    have hwidth : WidthAtMostThree A := by
      by_contra h
      exact hwide ((ThreeSatToSat.wide_iff_not_widthAtMostThree A).mpr h)
    rw [NAEThreeSatisfiable, and_iff_right hwidth]
    have hdl : ∀ j : jInterp.Map A, JSJob j → JSDlineVal j = dval A := fun j hj => by
      rw [jsDlineVal_eq hj, jsBound_eq ha₀]
    have htot : (∑ᶠ j ∈ {j : jInterp.Map A | JSJob j}, JSTimeVal j) = 2 * dval A := by
      rw [sum_times_eq_cnt ha₀, dval, ← digitNum_mul_left]
      exact digitNum_congr_on fun b _ => (two_mul_dd ha₀ hdeg hwidth b).symm
    rw [hasGoodSchedule_iff_exists_half isLinOrd_jsLe hdl hpt htot (jsBound_eq ha₀)]
    constructor
    · rintro ⟨ν, hν⟩
      -- a clause has a true occurrence, and at least one more occurrence
      have hocc : ∀ c : A, IsCl c →
          1 ≤ (TrueSet ν c).ncard ∧ (TrueSet ν c).ncard < (OccSet c).ncard := by
        intro c hc
        obtain ⟨⟨x, s, hx, hxT⟩, ⟨y, t, hy, hyT⟩⟩ := naeProper_occ hν c hc
        have h1 : 0 < (TrueSet ν c).ncard :=
          (Set.ncard_pos (Set.toFinite _)).mpr ⟨(x, s), hx, hxT⟩
        refine ⟨by omega, ?_⟩
        refine Set.ncard_lt_ncard ⟨fun p hp => hp.1, fun hsub => ?_⟩ (Set.toFinite _)
        exact hyT (hsub (show ((y, t) : A × Bool) ∈ OccSet c from hy)).2
      have hOccEmpty : ∀ c : A, ¬IsCl c → OccSet c = ∅ := by
        intro c hc
        ext p
        simp only [OccSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hc h.1
      -- enough slack to balance every clause block
      have hsub : ∀ c : A,
          ((OccSet c).ncard - 1 - (TrueSet ν c).ncard) ≤ (MidSet c).ncard := by
        intro c
        by_cases hc : IsCl c
        · obtain ⟨h1, h2⟩ := hocc c hc
          have h3 := card_midSet_add_two (two_le_ncard_occSet hdeg hc)
          omega
        · rw [hOccEmpty c hc, Set.ncard_empty]
          omega
      choose M hMsub hMcard using fun c : A => Set.exists_subset_card_eq (hsub c)
      have hjobs : ∀ i, splitSet a₀ ν M i → JSJob i := by
        rintro i (⟨p, -, rfl⟩ | ⟨c, p, hp, rfl⟩)
        · rw [jLit]
          exact (jsJob_lit _ _).mpr (by simpa using ha₀)
        · rw [jSlk]
          exact (jsJob_slk _ _).mpr (by simpa [MidSet] using hMsub c hp)
      refine ⟨splitSet a₀ ν M, hjobs, ?_⟩
      rw [sum_eq_dval_iff ha₀ hjobs]
      rintro ⟨k, e⟩
      cases k with
      | false =>
        rw [cnt_var ha₀, dd_var hdeg]
        have hset : {s : Bool | splitSet a₀ ν M (jLit a₀ s e)} = {s | LitTrue ν e s} := by
          ext s
          rw [Set.mem_setOf_eq, Set.mem_setOf_eq, splitSet_jLit]
        rw [hset]
        by_cases hv : ν e
        · have : {s : Bool | LitTrue ν e s} = {true} := by
            ext s
            cases s <;> simp [LitTrue, hv]
          rw [this, Set.ncard_singleton]
        · have : {s : Bool | LitTrue ν e s} = {false} := by
            ext s
            cases s <;> simp [LitTrue, hv]
          rw [this, Set.ncard_singleton]
      | true =>
        rw [cnt_cls ha₀]
        have hlit : {p ∈ OccSet e | splitSet a₀ ν M (jLit a₀ p.2 p.1)} = TrueSet ν e := by
          ext p
          rw [Set.mem_sep_iff, splitSet_jLit]
          exact Iff.rfl
        have hslk : {p ∈ MidSet e | splitSet a₀ ν M (jSlk p.2 e p.1)} = M e := by
          ext p
          rw [Set.mem_sep_iff, splitSet_jSlk]
          constructor
          · rintro ⟨-, h⟩
            simpa using h
          · intro h
            exact ⟨hMsub e h, by simpa using h⟩
        rw [hlit, hslk, hMcard e]
        by_cases hc : IsCl e
        · obtain ⟨h1, h2⟩ := hocc e hc
          have h3 := card_midSet_add_two (two_le_ncard_occSet hdeg hc)
          have h4 := ncard_midSet_le_one hwidth e
          rw [dd_cls hdeg hc]
          by_cases hm : ∃ x s, Mid e x s
          · rw [if_pos hm]
            have hpos : 0 < (MidSet e).ncard := by
              obtain ⟨x, s, h⟩ := hm
              exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨(x, s), h⟩
            omega
          · rw [if_neg hm]
            have hzero : (MidSet e).ncard = 0 := by
              rw [Set.ncard_eq_zero (Set.toFinite _)]
              ext p
              simp only [Set.mem_empty_iff_false, iff_false]
              exact fun hp => hm ⟨p.1, p.2, hp⟩
            omega
        · have ho := hOccEmpty e hc
          have hTe : TrueSet ν e = ∅ :=
            Set.subset_empty_iff.mp (ho ▸ (fun p hp => hp.1 : TrueSet ν e ⊆ OccSet e))
          rw [dd_not_cls _ hc, hTe, ho]
          simp
    · rintro ⟨S, hSj, hsum⟩
      have hdig := (sum_eq_dval_iff ha₀ hSj).mp hsum
      have hbal : ∀ b, 2 * cnt a₀ S b = cnt a₀ JSJob b := fun b => by
        rw [hdig b]
        exact two_mul_dd ha₀ hdeg hwidth b
      have hcompl : ∀ i, JSJob i → (S i ↔ ¬(JSJob i ∧ ¬S i)) := by
        intro i hi
        constructor
        · rintro h ⟨-, hn⟩
          exact hn h
        · intro h
          by_contra hn
          exact h ⟨hi, hn⟩
      have hbal' : ∀ b, cnt a₀ S b = cnt a₀ (fun i => JSJob i ∧ ¬S i) b := by
        intro b
        have h1 := cnt_add_cnt a₀ hSj b
        have h2 := hbal b
        omega
      refine ⟨fun y => S (jLit a₀ true y), naeProper_of_occ fun c hc => ?_⟩
      obtain ⟨p, hp, hpS⟩ := exists_occ_selected ha₀ hdeg hcompl hbal' hc
      obtain ⟨q, hq, hqT⟩ := exists_occ_selected ha₀ hdeg
        (fun i hi => ⟨fun h hn => h.2 hn, fun h => ⟨hi, h⟩⟩) (fun b => (hbal' b).symm) hc
      exact ⟨⟨p.1, p.2, hp, (litTrue_iff_sel ha₀ hbal p.1 p.2).mp hpS⟩,
        ⟨q.1, q.2, hq, fun hT => hqT.2 ((litTrue_iff_sel ha₀ hbal q.1 q.2).mpr hT)⟩⟩

end Correct

end JSRed

open JSRed in
/-- **NAE-3SAT ordered-FO-reduces to job sequencing**: one job per literal and
one per slack occurrence, one digit block of `3 |A|` bit positions per variable
and per clause, and a common deadline – the bound as well – equal to the
digit-wise half of the total execution time. A variable block totals `2` and
the block of a clause of width `w` totals `2 (w − 1)`, so a schedule whose
late jobs stay within the bound is a balanced split of the blocks, that is, a
not-all-equal satisfying assignment. -/
noncomputable def nae3Sat_ordered_fo_reduction_jobSequencing : NAE3SAT ≤ᶠᵒ[≤] JobSequencing where
  Tag := JTag
  dim := 2
  toInterpretation := jInterp
  correct A _ _ _ _ := naeThreeSatisfiable_iff_hasGoodSchedule A

end DescriptiveComplexity
