/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CircuitNumber.Defs
import DescriptiveComplexity.Counting.Relativized

/-!
# The number written by a circuit ignores isolated elements

A circuit with elements added that are no gate, wired to nothing, not
outputs and compared with nothing writes the same number
(`DescriptiveComplexity.circuitNumber_of_embedding`). So a *relativized*
reduction to `DescriptiveComplexity.CircuitNumber`, whose target universe is a
definable set of tagged tuples, is a reduction with the whole set of tagged
tuples as universe: guard every relation by the domain formulas of its
arguments (`DescriptiveComplexity.RelFOInterpretation.guard`), and the tuples
outside the domain are such isolated elements
(`DescriptiveComplexity.RelOrderedParsimoniousReduction.unrelCircuitNumber`).

This is what closes FP under relativized parsimonious reductions
(`DescriptiveComplexity.mem_FP_of_relOrderedParsimonious`, in
`DescriptiveComplexity.Problems.CircuitNumber`): the class has a complete
problem that tolerates junk.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Isolated elements -/

section Embedding

variable {X Y : Type} [Language.numCircuit.Structure X] [Language.numCircuit.Structure Y]

open Classical in
/-- **Isolated elements do not change the number written.** If `X` embeds in
`Y` with the same relations, and every relation of `Y` holds only of elements
of `X`, the two circuits write the same number. -/
theorem circuitNumber_of_embedding (φ : X → Y) (hφ : Function.Injective φ)
    (hrel : ∀ {n : ℕ} (R : Language.numCircuit.Relations n) (xs : Fin n → X),
      RelMap R (fun i => φ (xs i)) ↔ RelMap R xs)
    (hrange : ∀ {n : ℕ} (R : Language.numCircuit.Relations n) (ys : Fin n → Y),
      RelMap R ys → ∀ i, ys i ∈ Set.range φ) :
    circuitNumber Y = circuitNumber X := by
  have h1 : ∀ (R : Language.numCircuit.Relations 1) (x : X),
      RelMap R ![φ x] ↔ RelMap R ![x] := fun R x =>
    (iff_of_eq (congrArg _ (funext fun i => by fin_cases i; rfl))).trans (hrel R (![x]))
  have h2 : ∀ (R : Language.numCircuit.Relations 2) (x x' : X),
      RelMap R ![φ x, φ x'] ↔ RelMap R ![x, x'] := fun R x x' =>
    (iff_of_eq (congrArg _ (funext fun i => by fin_cases i <;> rfl))).trans
      (hrel R (![x, x']))
  have r1 : ∀ (R : Language.numCircuit.Relations 1) (y : Y), RelMap R ![y] → ∃ x, φ x = y :=
    fun R y h => hrange R ![y] h 0
  have r2 : ∀ (R : Language.numCircuit.Relations 2) (y y' : Y), RelMap R ![y, y'] →
      ∃ x, φ x = y' := fun R y y' h => hrange R ![y, y'] h 1
  -- the gates evaluate alike
  have hup : ∀ {b : Bool} {x : X}, GateVal b x → GateVal b (φ x) := by
    intro b x h
    induction h with
    | constTrue hg => exact .constTrue ((h1 ncIsTrue _).mpr hg)
    | constFalse hg => exact .constFalse ((h1 ncIsFalse _).mpr hg)
    | andTrue hg hl hr _ _ ihl ihr =>
      exact .andTrue ((h1 ncIsAnd _).mpr hg) ((h2 ncLeft _ _).mpr hl)
        ((h2 ncRight _ _).mpr hr) ihl ihr
    | andFalseLeft hg hl _ ihl =>
      exact .andFalseLeft ((h1 ncIsAnd _).mpr hg) ((h2 ncLeft _ _).mpr hl) ihl
    | andFalseRight hg hr _ ihr =>
      exact .andFalseRight ((h1 ncIsAnd _).mpr hg) ((h2 ncRight _ _).mpr hr) ihr
    | orTrueLeft hg hl _ ihl =>
      exact .orTrueLeft ((h1 ncIsOr _).mpr hg) ((h2 ncLeft _ _).mpr hl) ihl
    | orTrueRight hg hr _ ihr =>
      exact .orTrueRight ((h1 ncIsOr _).mpr hg) ((h2 ncRight _ _).mpr hr) ihr
    | orFalse hg hl hr _ _ ihl ihr =>
      exact .orFalse ((h1 ncIsOr _).mpr hg) ((h2 ncLeft _ _).mpr hl)
        ((h2 ncRight _ _).mpr hr) ihl ihr
    | notTrue hg hi _ ihi =>
      exact .notTrue ((h1 ncIsNot _).mpr hg) ((h2 ncLeft _ _).mpr hi) ihi
    | notFalse hg hi _ ihi =>
      exact .notFalse ((h1 ncIsNot _).mpr hg) ((h2 ncLeft _ _).mpr hi) ihi
  have hdown : ∀ {b : Bool} {y : Y}, GateVal b y → ∀ x : X, φ x = y → GateVal b x := by
    intro b y h
    induction h with
    | constTrue hg =>
      rintro x rfl
      exact .constTrue ((h1 ncIsTrue _).mp hg)
    | constFalse hg =>
      rintro x rfl
      exact .constFalse ((h1 ncIsFalse _).mp hg)
    | andTrue hg hl hr _ _ ihl ihr =>
      rintro x rfl
      obtain ⟨l, rfl⟩ := r2 ncLeft _ _ hl
      obtain ⟨r, rfl⟩ := r2 ncRight _ _ hr
      exact .andTrue ((h1 ncIsAnd _).mp hg) ((h2 ncLeft _ _).mp hl) ((h2 ncRight _ _).mp hr)
        (ihl l rfl) (ihr r rfl)
    | andFalseLeft hg hl _ ihl =>
      rintro x rfl
      obtain ⟨l, rfl⟩ := r2 ncLeft _ _ hl
      exact .andFalseLeft ((h1 ncIsAnd _).mp hg) ((h2 ncLeft _ _).mp hl) (ihl l rfl)
    | andFalseRight hg hr _ ihr =>
      rintro x rfl
      obtain ⟨r, rfl⟩ := r2 ncRight _ _ hr
      exact .andFalseRight ((h1 ncIsAnd _).mp hg) ((h2 ncRight _ _).mp hr) (ihr r rfl)
    | orTrueLeft hg hl _ ihl =>
      rintro x rfl
      obtain ⟨l, rfl⟩ := r2 ncLeft _ _ hl
      exact .orTrueLeft ((h1 ncIsOr _).mp hg) ((h2 ncLeft _ _).mp hl) (ihl l rfl)
    | orTrueRight hg hr _ ihr =>
      rintro x rfl
      obtain ⟨r, rfl⟩ := r2 ncRight _ _ hr
      exact .orTrueRight ((h1 ncIsOr _).mp hg) ((h2 ncRight _ _).mp hr) (ihr r rfl)
    | orFalse hg hl hr _ _ ihl ihr =>
      rintro x rfl
      obtain ⟨l, rfl⟩ := r2 ncLeft _ _ hl
      obtain ⟨r, rfl⟩ := r2 ncRight _ _ hr
      exact .orFalse ((h1 ncIsOr _).mp hg) ((h2 ncLeft _ _).mp hl) ((h2 ncRight _ _).mp hr)
        (ihl l rfl) (ihr r rfl)
    | notTrue hg hi _ ihi =>
      rintro x rfl
      obtain ⟨i, rfl⟩ := r2 ncLeft _ _ hi
      exact .notTrue ((h1 ncIsNot _).mp hg) ((h2 ncLeft _ _).mp hi) (ihi i rfl)
    | notFalse hg hi _ ihi =>
      rintro x rfl
      obtain ⟨i, rfl⟩ := r2 ncLeft _ _ hi
      exact .notFalse ((h1 ncIsNot _).mp hg) ((h2 ncLeft _ _).mp hi) (ihi i rfl)
  have hbit : ∀ x : X, OutBit (φ x) ↔ OutBit x := fun x =>
    and_congr (h1 ncOut x) ⟨fun h => hdown h x rfl, hup⟩
  have hlow : ∀ x x' : X, LowerOut (φ x) (φ x') ↔ LowerOut x x' := fun x x' =>
    and_congr (h1 ncOut x') (and_congr hφ.ne_iff (h2 ncBelow x' x))
  have hrank : ∀ x : X, outRank (φ x) = outRank x := by
    intro x
    rw [outRank, outRank]
    symm
    refine Nat.card_eq_of_bijective (fun x' => ⟨φ x'.1, (hlow x x'.1).mpr x'.2⟩) ⟨?_, ?_⟩
    · intro a b h
      exact Subtype.ext (hφ (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x', rfl⟩ := r1 ncOut y hy.1
      exact ⟨⟨x', (hlow x x').mp hy⟩, rfl⟩
  have hsupp : ∀ y ∈ Function.support (fun y : Y => if OutBit y then 2 ^ outRank y else 0),
      y ∈ Set.univ ↔ y ∈ Set.range φ := by
    intro y hy
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    have hb : OutBit y := by
      by_contra h
      exact hy (ite_eq_right h)
    exact r1 ncOut y hb.1
  have hord : OutOrder Y ↔ OutOrder X := by
    have hb : ∀ y, RelMap ncOut ![y] → ∃ x, φ x = y := r1 ncOut
    constructor
    · rintro ⟨hr, ht, ha, hl⟩
      refine ⟨fun p hp => (h2 _ _ _).mp (hr _ ((h1 _ _).mpr hp)),
        fun p q r hp hq hr' hpq hqr => (h2 _ _ _).mp (ht _ _ _ ((h1 _ _).mpr hp) ((h1 _ _).mpr hq)
          ((h1 _ _).mpr hr') ((h2 _ _ _).mpr hpq) ((h2 _ _ _).mpr hqr)),
        fun p q hp hq hpq hqp => hφ (ha _ _ ((h1 _ _).mpr hp) ((h1 _ _).mpr hq)
          ((h2 _ _ _).mpr hpq) ((h2 _ _ _).mpr hqp)),
        fun p q hp hq => (hl _ _ ((h1 _ _).mpr hp) ((h1 _ _).mpr hq)).imp (h2 _ _ _).mp
          (h2 _ _ _).mp⟩
    · rintro ⟨hr, ht, ha, hl⟩
      refine ⟨fun p hp => ?_, fun p q r hp hq hr' hpq hqr => ?_, fun p q hp hq hpq hqp => ?_,
        fun p q hp hq => ?_⟩
      · obtain ⟨p, rfl⟩ := hb p hp
        exact (h2 _ _ _).mpr (hr p ((h1 _ _).mp hp))
      · obtain ⟨p, rfl⟩ := hb p hp
        obtain ⟨q, rfl⟩ := hb q hq
        obtain ⟨r, rfl⟩ := hb r hr'
        exact (h2 _ _ _).mpr (ht p q r ((h1 _ _).mp hp) ((h1 _ _).mp hq) ((h1 _ _).mp hr')
          ((h2 _ _ _).mp hpq) ((h2 _ _ _).mp hqr))
      · obtain ⟨p, rfl⟩ := hb p hp
        obtain ⟨q, rfl⟩ := hb q hq
        exact congrArg φ (ha p q ((h1 _ _).mp hp) ((h1 _ _).mp hq) ((h2 _ _ _).mp hpq)
          ((h2 _ _ _).mp hqp))
      · obtain ⟨p, rfl⟩ := hb p hp
        obtain ⟨q, rfl⟩ := hb q hq
        exact (hl p q ((h1 _ _).mp hp) ((h1 _ _).mp hq)).imp (h2 _ _ _).mpr (h2 _ _ _).mpr
  have hsum : (∑ᶠ y : Y, if OutBit y then 2 ^ outRank y else 0) =
      ∑ᶠ x : X, if OutBit x then 2 ^ outRank x else 0 := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ _ hsupp, finsum_mem_range hφ]
    refine finsum_congr fun x => ?_
    rw [hrank x, if_congr (hbit x) rfl rfl]
  rw [circuitNumber, circuitNumber, hsum]
  exact if_congr hord rfl rfl

end Embedding

/-! ### Guarding an interpretation by its domain -/

section Guard

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} {dim : ℕ}

/-- **The guarded interpretation**: the whole set of tagged tuples as universe,
every relation holding only of tuples in the domain. -/
noncomputable def RelFOInterpretation.guard (J : RelFOInterpretation L L' Tag dim) :
    FOInterpretation L L' Tag dim where
  relFormula {n} R := fun t =>
    J.relFormula R t ⊓
      Formula.iInf fun i : Fin n => Formula.relabel (fun j => (i, j)) (J.domFormula (t i))

theorem RelFOInterpretation.relMap_guard (J : RelFOInterpretation L L' Tag dim) {A : Type}
    [L.Structure A] {n : ℕ} (R : L'.Relations n) (ys : Fin n → J.guard.Map A) :
    RelMap R ys ↔ (J.relFormula R fun i => (ys i).1).Realize (fun p => (ys p.1).2 p.2) ∧
      ∀ i, (J.domFormula (ys i).1).Realize (ys i).2 := by
  rw [FOInterpretation.relMap_map]
  refine Formula.realize_inf.trans (and_congr Iff.rfl ?_)
  refine (BoundedFormula.realize_iInf (v := fun p : Fin n × Fin dim => (ys p.1).2 p.2)).trans ?_
  exact forall_congr' fun i => Formula.realize_relabel

end Guard

/-! ### A relativized reduction to the number written by a circuit -/

section Unrel

variable {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L}

/-- **A relativized reduction to the number written by a circuit is a
reduction**: the tuples outside the domain are isolated elements. -/
noncomputable def RelOrderedParsimoniousReduction.unrelCircuitNumber
    (f : C ≤ʳᵖ[≤] CircuitNumber) : C ≤ᵖ[≤] CircuitNumber where
  Tag := f.Tag
  tagFinite := f.tagFinite
  tagNonempty := by
    let : L.Structure PUnit := ⟨fun {_} g => isEmptyElim g, fun {_} _ _ => False⟩
    obtain ⟨t, -⟩ := f.dom_nonempty PUnit
    exact ⟨t⟩
  dim := f.dim
  toInterpretation := f.toRelInterpretation.guard
  correct := fun A _ _ _ _ => by
    refine (f.correct A).trans (Eq.symm ?_)
    refine circuitNumber_of_embedding
      (X := f.toRelInterpretation.MapRel A) (Y := f.toRelInterpretation.guard.Map A)
      Subtype.val Subtype.val_injective (fun R xs => ?_) (fun R ys h i => ?_)
    · exact (f.toRelInterpretation.relMap_guard R _).trans (and_iff_left fun i => (xs i).2)
    · exact ⟨⟨ys i, ((f.toRelInterpretation.relMap_guard R ys).mp h).2 i⟩, rfl⟩

end Unrel

end DescriptiveComplexity
