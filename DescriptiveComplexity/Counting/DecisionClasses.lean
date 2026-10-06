/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Class
import DescriptiveComplexity.Counting.KernelPair

/-!
# Decision classes defined by counting

The classes of decision problems whose answer is a property of the number of
witnesses of an existential second-order sentence – classically, of the
number of accepting runs of a nondeterministic polynomial-time machine:

* **⊕P** (`DescriptiveComplexity.ParityP`, [Papadimitriou, Zachos
  1982][papadimitriou1982two], [Goldschlager, Parberry 1986][goldschlager1986parallel]):
  the number is odd;
* **Mod_k P** (`DescriptiveComplexity.ModP k`, [Cai, Hemachandra
  1990][cai1990complexity]): the number is not a multiple of `k`;
* **PP** (`DescriptiveComplexity.PP`, [Gill 1977][gill1977computational]): one
  number exceeds another – classically, more runs accept than reject;
* **C₌P** (`DescriptiveComplexity.CeqP`, [Wagner 1986][wagner1986complexity]):
  the two numbers are equal;
* **UP** (`DescriptiveComplexity.UP`, [Valiant 1976][valiant1976relative]): the
  number is at most one, and the answer is whether it is one.

Each is `DescriptiveComplexity.countClass S R` for a side condition `S` and a
relation `R` on two numbers: a problem is in the class when, on nonempty
finite ordered structures, `S` holds of the two witness counts and the answer
is `R` of them (`DescriptiveComplexity.CountDefinable`). The witness counts
are those of `DescriptiveComplexity.SharpPDefinable`, read over the ordered
expansion; the two-number form is the characterization of these classes by
`GapP` functions, differences of two `#P` functions
([Fenner, Fortnow, Kurtz 1994][fenner1994gap]), which needs no integer-valued
problem.

Closure under first-order reductions is the pullback of the two kernels
through the interpretation, as for `#P`
(`DescriptiveComplexity.CountDefinable.of_orderedReduction`); hardness is
cofinal, as for every class of the library. A problem of the class is given
by two counting problems of `#P` (`DescriptiveComplexity.mem_countClass_of_sharpP`),
which is how memberships are proved.

Inclusions: `UP ⊆ NP`, `UP ⊆ ⊕P`, `NP ⊆ PP`, `coNP ⊆ PP`; `⊕P` and `PP` are
closed under complement, by adding one witness to a kernel
(`DescriptiveComplexity.pairKernel` with the kernel `⊤` over the block without
variables). Whether `C₌P` is closed under complement is open. The complete
problems are in `DescriptiveComplexity.Problems.Sat.CountingDecision`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Problems defined by a relation between two witness counts -/

section Definable

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A decision problem is **defined by the relation `R` between two witness
counts under the side condition `S`** if, on nonempty finite ordered
structures, the two counts satisfy `S` and the problem holds exactly when
they satisfy `R`. -/
def CountDefinable (S R : ℕ → ℕ → Prop) (P : DecisionProblem L) : Prop :=
  ∃ (B : SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence)
    (B' : SOBlock) (φ' : ((L.sum Language.order).sum B'.lang).Sentence),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      S (witnessCount B φ A) (witnessCount B' φ' A) ∧
        (P A ↔ R (witnessCount B φ A) (witnessCount B' φ' A))

variable {S R : ℕ → ℕ → Prop}

theorem CountDefinable.congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) (hP : CountDefinable S R P) :
    CountDefinable S R Q := by
  obtain ⟨B, φ, B', φ', hφ⟩ := hP
  exact ⟨B, φ, B', φ', fun A _ _ _ _ => ⟨(hφ A).1, (h A).symm.trans (hφ A).2⟩⟩

variable {L' : Language.{0, 0}} [L'.IsRelational] {P : DecisionProblem L}
  {Q : DecisionProblem L'}

/-- **Closure under ordered first-order reductions**: both kernels are pulled
back through the interpretation, extended with the lexicographic order. -/
theorem CountDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : CountDefinable S R Q) :
    CountDefinable S R P := by
  obtain ⟨B, φ, B', φ', hφ⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨B.pull f.Tag f.dim, (f.toInterpretation.ordExtend.extendSO B).pullSentence φ,
    B'.pull f.Tag f.dim, (f.toInterpretation.ordExtend.extendSO B').pullSentence φ', ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have : Finite (f.toInterpretation.Map A) := f.toInterpretation.map_finite A
  have : Nonempty (f.toInterpretation.Map A) := f.toInterpretation.map_nonempty A
  have h1 := witnessCount_map f.toInterpretation.ordExtend B φ A
  have h2 := witnessCount_map f.toInterpretation.ordExtend B' φ' A
  rw [witnessCount_iso B φ (f.toInterpretation.ordExtendLEquiv A)] at h1
  rw [witnessCount_iso B' φ' (f.toInterpretation.ordExtendLEquiv A)] at h2
  rw [← h1, ← h2, f.correct A]
  exact hφ (f.toInterpretation.Map A)

/-- Closure under first-order reductions. -/
theorem CountDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : CountDefinable S R Q) :
    CountDefinable S R P :=
  h.of_orderedReduction f.toOrdered

end Definable

/-! ### The classes -/

/-- **The class of the problems defined by the relation `R` between two
witness counts under the side condition `S`**, with cofinal hardness. -/
noncomputable def countClass (S R : ℕ → ℕ → Prop) : ComplexityClass :=
  ComplexityClass.ofMem (CountDefinable S R)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => ⟨fun hP => hP.congr h, fun hQ => hQ.congr fun A _ _ => (h A).symm⟩)

/-- **⊕P**: the number of witnesses is odd. -/
noncomputable def ParityP : ComplexityClass :=
  countClass (fun _ _ => True) fun c _ => Odd c

/-- **Mod_k P**: the number of witnesses is not a multiple of `k`. -/
noncomputable def ModP (k : ℕ) : ComplexityClass :=
  countClass (fun _ _ => True) fun c _ => ¬ k ∣ c

/-- **PP**: the first number of witnesses exceeds the second – classically,
more runs accept than reject. -/
noncomputable def PP : ComplexityClass :=
  countClass (fun _ _ => True) fun c d => d < c

/-- **C₌P**: the two numbers of witnesses are equal. -/
noncomputable def CeqP : ComplexityClass :=
  countClass (fun _ _ => True) fun c d => c = d

/-- **UP**: at most one witness, and the answer is whether there is one.
No complete problem is known for it, and the question does not relativize
([Hartmanis, Hemachandra 1988][hartmanis1988complexity]); the class is here
for its inclusions. -/
noncomputable def UP : ComplexityClass :=
  countClass (fun c _ => c ≤ 1) fun c _ => c = 1

section Mem

variable {L : Language.{0, 0}} [L.IsRelational] {S R : ℕ → ℕ → Prop}

theorem mem_countClass_iff (P : DecisionProblem L) :
    P ∈ countClass S R ↔ CountDefinable S R P :=
  Iff.rfl

/-- **A problem of the class, from two counting problems of `#P`.** -/
theorem mem_countClass_of_sharpP {C D : CountingProblem L} (hC : C ∈ SharpP) (hD : D ∈ SharpP)
    {P : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      S (C A) (D A) ∧ (P A ↔ R (C A) (D A))) :
    P ∈ countClass S R := by
  obtain ⟨B, φ, hφ⟩ := (mem_sharpP_iff C).mp hC
  obtain ⟨B', φ', hφ'⟩ := (mem_sharpP_iff D).mp hD
  exact ⟨B, φ, B', φ', fun A _ _ _ _ => by rw [← hφ A, ← hφ' A]; exact h A⟩

/-- Hardness for the class is the usual notion: every member reduces to the
problem. -/
theorem hard_countClass_iff (P : DecisionProblem L) :
    (countClass S R).Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        CountDefinable S R Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

end Mem

/-! ### Inclusions needing no arithmetic on the kernels -/

section Inclusions

/-- The side condition and the relation may be weakened. -/
theorem countClass_subset {S R S' R' : ℕ → ℕ → Prop} (hS : ∀ c d, S c d → S' c d)
    (hR : ∀ c d, S c d → (R c d ↔ R' c d)) : countClass S R ⊆ countClass S' R' := by
  rintro L _ P ⟨B, φ, B', φ', hφ⟩
  exact ⟨B, φ, B', φ', fun A _ _ _ _ =>
    ⟨hS _ _ (hφ A).1, (hφ A).2.trans (hR _ _ (hφ A).1)⟩⟩

/-- `UP ⊆ ⊕P`: at most one witness, and one is an odd number of them. -/
theorem UP_subset_parityP : UP ⊆ ParityP :=
  countClass_subset (fun _ _ _ => trivial) fun c _ hc => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> simp

/-- `UP ⊆ NP`: a problem with at most one witness is a problem with a
witness, and the order the kernel reads is re-quantified. -/
theorem UP_subset_NP : UP ⊆ NP := by
  rintro L _ P ⟨B, φ, B', φ', hφ⟩
  refine sigmaSODefinable_of_orderPull (k := 0) [B] rfl φ ?_
  intro A _ _ _
  constructor
  · intro hP
    refine ⟨finiteLinearOrder A, ?_⟩
    let := finiteLinearOrder A
    have h1 := ((hφ A).2.mp hP)
    exact (witnessCount_pos_iff B φ A).mp (by omega)
  · rintro ⟨lo, hlo⟩
    let := lo
    have hpos := (witnessCount_pos_iff B φ A).mpr hlo
    have hle := (hφ A).1
    exact (hφ A).2.mpr (by omega)

/-- `NP ⊆ PP`: a problem with a witness has more witnesses than the kernel
`⊥` has, namely none. -/
theorem NP_subset_PP : NP ⊆ PP := by
  intro L _ P hP
  obtain ⟨C, hC, hCP⟩ := (mem_NP_iff_exists_sharpP_support P).mp hP
  refine mem_countClass_of_sharpP hC (ofKernel_mem_sharpP SOBlock.trivial ⊥) fun A _ _ _ => ?_
  refine ⟨trivial, (hCP A).symm.trans ?_⟩
  rw [CountingProblem.support_iff, CountingProblem.ofKernel_apply]
  have : witnessCount (L := L) SOBlock.trivial ⊥ A = 0 := by
    rw [witnessCount, Nat.card_eq_zero]
    exact Or.inl ⟨fun ⟨_, h⟩ => h⟩
  rw [this]

/-- **Swapping the two counts.** -/
theorem countClass_swap_subset (S R : ℕ → ℕ → Prop) :
    countClass S R ⊆ countClass (fun c d => S d c) fun c d => R d c := by
  rintro L _ P ⟨B, φ, B', φ', hφ⟩
  exact ⟨B', φ', B, φ, fun A _ _ _ _ => hφ A⟩

/-- **Adding one to the first count**: the first kernel is paired with the
kernel `⊤` over the block without variables. -/
theorem countClass_succ_subset (S R : ℕ → ℕ → Prop) :
    countClass S R ⊆ countClass (fun c d => ∃ c', c = c' + 1 ∧ S c' d) fun c d =>
      ∃ c', c = c' + 1 ∧ R c' d := by
  rintro L _ P ⟨B, φ, B', φ', hφ⟩
  refine ⟨pairBlock B SOBlock.trivial, pairKernel B SOBlock.trivial φ ⊤, B', φ',
    fun A _ _ _ _ => ?_⟩
  rw [witnessCount_pairKernel, witnessCount_trivial_top]
  exact ⟨⟨_, rfl, (hφ A).1⟩, (hφ A).2.trans
    ⟨fun h => ⟨_, rfl, h⟩, fun ⟨c', hc, h⟩ => by rwa [Nat.add_right_cancel_iff.mp hc]⟩⟩

/-- The complement of a problem of the class of `R` is in the class of
`¬R`. -/
theorem compl_mem_countClass {L : Language.{0, 0}} [L.IsRelational] {S R : ℕ → ℕ → Prop}
    {P : DecisionProblem L} (h : P ∈ countClass S R) :
    Pᶜ ∈ countClass S fun c d => ¬R c d := by
  obtain ⟨B, φ, B', φ', hφ⟩ := h
  exact ⟨B, φ, B', φ', fun A _ _ _ _ => ⟨(hφ A).1, not_congr (hφ A).2⟩⟩

/-- **`⊕P` is closed under complement**: a number is even exactly when its
successor is odd. -/
theorem compl_mem_parityP {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : P ∈ ParityP) : Pᶜ ∈ ParityP := by
  have := countClass_succ_subset _ _ (compl_mem_countClass h)
  refine countClass_subset (fun _ _ _ => trivial) (fun c d _ => ?_) this
  constructor
  · rintro ⟨c', rfl, hc⟩
    exact Nat.odd_add_one.mpr hc
  · intro hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by
      obtain ⟨m, rfl⟩ := hc
      rfl⟩
    exact ⟨c', rfl, Nat.odd_add_one.mp hc⟩

/-- **`PP` is closed under complement**: `¬ (d < c)` is `c < d + 1`, with the
counts swapped. -/
theorem compl_mem_PP {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : P ∈ PP) : Pᶜ ∈ PP := by
  have := countClass_succ_subset _ _ (countClass_swap_subset _ _ (compl_mem_countClass h))
  refine countClass_subset (fun _ _ _ => trivial) (fun c d _ => ?_) this
  constructor
  · rintro ⟨c', rfl, hc⟩
    exact Nat.lt_succ_of_le (not_lt.mp hc)
  · intro hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    exact ⟨c', rfl, not_lt.mpr (Nat.le_of_lt_succ hc)⟩

/-- `coNP ⊆ PP`. -/
theorem coNP_subset_PP : coNP ⊆ PP := by
  intro L _ P hP
  rw [← DecisionProblem.compl_compl P]
  exact compl_mem_PP (NP_subset_PP ((mem_piP_iff 1 P).mp hP))

end Inclusions

end DescriptiveComplexity
