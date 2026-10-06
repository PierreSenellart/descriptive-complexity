/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat.CountingHardness
import DescriptiveComplexity.Problems.Machine.CountingHardness
import DescriptiveComplexity.Counting.DecisionClasses

/-!
# ⊕SAT and Mod_k-SAT: complete problems for the classes defined by one count

For a property `R` of a number, `DescriptiveComplexity.CountingProblem.decide R C`
is the decision problem “`R` holds of the count of `C`”, and
`DescriptiveComplexity.countClass₁ R` the class of the problems defined by `R`
of one witness count: `⊕P` for `Odd`, `Mod_k P` for “not a multiple of `k`”.

* **The decision version of `#SAT` is complete for every such class**
  (`DescriptiveComplexity.decide_sharpSat_countClass₁_complete`): membership is
  that `#SAT` is in `#P`, and hardness is the parsimonious Tseitin
  interpretation of `DescriptiveComplexity.Problems.Sat.CountingHardness`, which
  carries a witness count to a model count exactly and so carries any
  property of it.
* **It transfers along parsimonious reductions**
  (`DescriptiveComplexity.countClass₁_complete_of_sharpP_parsimoniousComplete`):
  the decision version of every parsimoniously `#P`-complete problem is
  complete for every such class. So `⊕SAT`, `⊕3SAT`, `⊕Clique`, …, and the
  parity of the number of accepting runs of a machine, are `⊕P`-complete;
  likewise for `Mod_k P`.
* **The machine characterization**
  (`DescriptiveComplexity.mem_parityP_iff_le_parity_sharpNtmAccept`): a problem
  is in `⊕P` exactly when it reduces to the parity of the number of accepting
  runs of a nondeterministic polynomial-time machine, through the counting
  machine bridge of `DescriptiveComplexity.Problems.Machine.CountingHardness`.

The classical statements are [Papadimitriou, Zachos 1982][papadimitriou1982two]
for `⊕SAT` and [Valiant 1979][valiant1979complexity] for the transfer: a
parsimonious reduction preserves every property of the count.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The decision version of a counting problem -/

section Decide

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The decision version of a counting problem** by a property `R` of
numbers: does the count satisfy `R`? -/
def CountingProblem.decide (R : ℕ → Prop) (C : CountingProblem L) : DecisionProblem L where
  Holds := fun A inst => R (@CountingProblem.Count L _ C A inst)
  iso_invariant := fun e => by rw [C.iso_invariant e]

theorem CountingProblem.decide_iff (R : ℕ → Prop) (C : CountingProblem L) (A : Type)
    [L.Structure A] : C.decide R A ↔ R (C A) :=
  Iff.rfl

/-- The class of the problems defined by the property `R` of one witness
count. -/
noncomputable abbrev countClass₁ (R : ℕ → Prop) : ComplexityClass :=
  countClass (fun _ _ => True) fun c _ => R c

theorem parityP_eq : ParityP = countClass₁ Odd := rfl

theorem modP_eq (k : ℕ) : ModP k = countClass₁ fun c => ¬ k ∣ c := rfl

/-- The decision version of a problem of `#P` is in the class of its
property. -/
theorem decide_mem_countClass₁ (R : ℕ → Prop) {C : CountingProblem L} (hC : C ∈ SharpP) :
    C.decide R ∈ countClass₁ R :=
  mem_countClass_of_sharpP hC hC fun _ _ _ _ => ⟨trivial, Iff.rfl⟩

variable {L' : Language.{0, 0}} [L'.IsRelational]

/-- A relativized parsimonious reduction is a relativized first-order
reduction between the decision versions by any property: equal counts share
every property. -/
def RelOrderedParsimoniousReduction.decide (R : ℕ → Prop) {C : CountingProblem L}
    {D : CountingProblem L'} (f : C ≤ʳᵖ[≤] D) : C.decide R ≤ʳᶠᵒ[≤] D.decide R :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toRelInterpretation
    dom_nonempty := f.dom_nonempty
    correct := fun A _ _ _ _ => by
      rw [CountingProblem.decide_iff, CountingProblem.decide_iff, f.correct A] }

/-- An ordered parsimonious reduction is an ordered first-order reduction
between the decision versions by any property. -/
def OrderedParsimoniousReduction.decide (R : ℕ → Prop) {C : CountingProblem L}
    {D : CountingProblem L'} (f : C ≤ᵖ[≤] D) : C.decide R ≤ᶠᵒ[≤] D.decide R :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => by
      rw [CountingProblem.decide_iff, CountingProblem.decide_iff, f.correct A] }

end Decide

/-! ### The decision versions of `#SAT` -/

section Sat

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Every problem defined by a property of one witness count reduces to the
decision version of `#SAT` by that property**: the parsimonious Tseitin
interpretation. -/
noncomputable def CountDefinable.orderedReduction_decide_sharpSat (R : ℕ → Prop)
    {P : DecisionProblem L} (B : SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ R (witnessCount B φ A)) : P ≤ᶠᵒ[≤] SharpSAT.decide R where
  Tag := SharpTseitinTag B φ
  dim := tseitinDim B φ
  toInterpretation := (sharpTseitinInterp B φ).liftSource (orderCollapse L)
  correct A _ _ _ _ := by
    rw [h A, CountingProblem.decide_iff,
      SharpSAT.iso_invariant ((sharpTseitinInterp B φ).liftSourceLEquiv (orderCollapse L) A),
      sharpSat_sharpTseitin B φ A]

/-- The decision version of `#SAT` by `R` is hard for the class of `R`. -/
theorem decide_sharpSat_countClass₁_hard (R : ℕ → Prop) :
    (countClass₁ R).Hard (SharpSAT.decide R) := by
  rw [hard_countClass_iff]
  rintro L'' _ Q ⟨B, φ, B', φ', hφ⟩
  exact ⟨(CountDefinable.orderedReduction_decide_sharpSat R B φ fun A _ _ _ _ => (hφ A).2).toRel⟩

/-- **The decision version of `#SAT` by `R` is complete for the class of
`R`.** -/
theorem decide_sharpSat_countClass₁_complete (R : ℕ → Prop) :
    (countClass₁ R).Complete (SharpSAT.decide R) :=
  ⟨decide_mem_countClass₁ R sharpSat_mem_sharpP, decide_sharpSat_countClass₁_hard R⟩

/-- **Completeness transfers along parsimonious completeness**: the decision
version by `R` of every parsimoniously `#P`-complete problem is complete for
the class of `R`. -/
theorem countClass₁_complete_of_sharpP_parsimoniousComplete (R : ℕ → Prop)
    {C : CountingProblem L} (hC : SharpP.ParsimoniousComplete C) :
    (countClass₁ R).Complete (C.decide R) :=
  ⟨decide_mem_countClass₁ R hC.mem,
    (countClass₁ R).hard_of_relOrderedReduction
      (((parsimoniousHard_sharpP_iff C).mp hC.parsimoniousHard SharpSAT
        sharpSat_mem_sharpP).some.decide R)
      (decide_sharpSat_countClass₁_hard R)⟩

end Sat

/-- **The machine characterization of the class of `R`**: a problem is in it
exactly when it reduces to the decision version by `R` of the number of
accepting runs of a nondeterministic machine. -/
theorem mem_countClass₁_iff_le_decide_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational]
    (R : ℕ → Prop) (P : DecisionProblem L) :
    P ∈ countClass₁ R ↔ Nonempty (P ≤ᶠᵒ[≤] SharpNTMAccept.decide R) := by
  constructor
  · rintro ⟨B, φ, B', φ', hφ⟩
    exact ⟨(CountDefinable.orderedReduction_decide_sharpSat R B φ fun A _ _ _ _ => (hφ A).2).trans
      (SatTM.sharpSat_ordered_parsimonious_sharpNtmAccept.decide R)⟩
  · rintro ⟨f⟩
    exact (countClass₁ R).mem_of_orderedReduction f
      (decide_mem_countClass₁ R sharpNtmAccept_mem_sharpP)

/-! ### ⊕SAT and Mod_k-SAT -/

/-- **⊕SAT**: the number of models of a CNF formula is odd. -/
noncomputable def ParitySAT : DecisionProblem Language.sat :=
  SharpSAT.decide Odd

/-- **Mod_k-SAT**: the number of models of a CNF formula is not a multiple of
`k`. -/
noncomputable def ModSAT (k : ℕ) : DecisionProblem Language.sat :=
  SharpSAT.decide fun c => ¬ k ∣ c

/-- **⊕SAT is `⊕P`-complete.** -/
theorem paritySat_parityP_complete : ParityP.Complete ParitySAT :=
  decide_sharpSat_countClass₁_complete Odd

/-- **Mod_k-SAT is `Mod_k P`-complete.** -/
theorem modSat_modP_complete (k : ℕ) : (ModP k).Complete (ModSAT k) :=
  decide_sharpSat_countClass₁_complete _

/-- The parity of every parsimoniously `#P`-complete problem is
`⊕P`-complete. -/
theorem parityP_complete_of_sharpP_parsimoniousComplete {L : Language.{0, 0}} [L.IsRelational]
    {C : CountingProblem L} (hC : SharpP.ParsimoniousComplete C) :
    ParityP.Complete (C.decide Odd) :=
  countClass₁_complete_of_sharpP_parsimoniousComplete Odd hC

/-- **The machine characterization of `⊕P`**: a problem is in `⊕P` exactly
when it reduces to the parity of the number of accepting runs of a
nondeterministic polynomial-time machine. -/
theorem mem_parityP_iff_le_parity_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) : P ∈ ParityP ↔ Nonempty (P ≤ᶠᵒ[≤] SharpNTMAccept.decide Odd) :=
  mem_countClass₁_iff_le_decide_sharpNtmAccept Odd P

/-- **The machine characterization of `Mod_k P`**. -/
theorem mem_modP_iff_le_mod_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational] (k : ℕ)
    (P : DecisionProblem L) :
    P ∈ ModP k ↔ Nonempty (P ≤ᶠᵒ[≤] SharpNTMAccept.decide fun c => ¬ k ∣ c) :=
  mem_countClass₁_iff_le_decide_sharpNtmAccept _ P

/-- The residue of every parsimoniously `#P`-complete problem is
`Mod_k P`-complete. -/
theorem modP_complete_of_sharpP_parsimoniousComplete {L : Language.{0, 0}} [L.IsRelational]
    (k : ℕ) {C : CountingProblem L} (hC : SharpP.ParsimoniousComplete C) :
    (ModP k).Complete (C.decide fun c => ¬ k ∣ c) :=
  countClass₁_complete_of_sharpP_parsimoniousComplete _ hC

end DescriptiveComplexity
