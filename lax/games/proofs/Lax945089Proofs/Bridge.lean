import Lax485149.LClosure
import Lax485149.FirstOrderInTransitiveClosure
import Lax485149.NLIsTransitiveClosure
import Lax535992.NLSubsetPTIME
import Lax895169.ACZeroFinite
import Lax945089.EvenInvariance
import Lax945089.EhrenfeuchtMethodology
import Lax945089.GamesOnSets
import Lax945089.GamesOnLinearOrders
import Lax945089.PebbleInvariance
import Lax945089.NoDefinableOrder
import Lax945089.EvenNotFirstOrder
import Lax945089.FirstOrderBelowTransitiveClosure
import Lax945089.FirstOrderBelowACZero
import Lax945089.OrderFreeInductionMissesPTIME
import Lax945089.ParityInLogSpace
import Lax945089.ReductionsBelowLogSpace
import Lax945089Proofs.DescriptiveComplexity.FirstOrderDefinable
import Lax945089Proofs.DescriptiveComplexity.FixedPointInflationary
import Lax945089Proofs.DescriptiveComplexity.Games.Bare
import Lax945089Proofs.DescriptiveComplexity.Games.Ehrenfeucht
import Lax945089Proofs.DescriptiveComplexity.Games.LinearOrder
import Lax945089Proofs.DescriptiveComplexity.Invariant.Bare
import Lax945089Proofs.DescriptiveComplexity.Invariant.TwoInvariance
import Lax945089Proofs.DescriptiveComplexity.Invariant.TwoPebble
import Lax945089Proofs.DescriptiveComplexity.Invariant.TwoStages
import Lax945089Proofs.DescriptiveComplexity.Problems.Even
import Lax945089Proofs.DescriptiveComplexity.Problems.Parity
import Lax945089Proofs.DescriptiveComplexity.TransitiveClosureReductionStrict

/-!
# The inexpressibility statements, from the library's theorems

The games and the logics are restated by the concepts, so the game-theoretic
claims are the library's theorems of the same name. EVEN and PARITY are
bundled in the concepts from their defining properties; statements about them
are transported along the agreement with the library's problems, and the
separations are assembled from this submission's own statements about EVEN,
together with statements of the submissions on logarithmic space, polynomial
time and AC⁰.
-/

namespace Lax945089Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes
open Lax485149.Problems Lax485149.FirstOrderDefinability Lax485149.TransitiveClosure
open Lax485149.DeterministicTransitiveClosure Lax485149.ClassNL Lax485149.ClassL
open Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax134656.PartialFixedPoint Lax895169.ArithmeticLogic
open Lax945089.OrderFreeFirstOrder Lax945089.EhrenfeuchtGames Lax945089.PebbleGames
open Lax945089.Even Lax945089.Parity
open Lax945089.TransitiveClosureReductions

/-- For an invariant property, the problem it gives holds exactly where the
property does. -/
theorem ofPred_iff {L : Language.{0, 0}} [L.IsRelational] {P : ∀ (A : Type) [L.Structure A], Prop}
    (hP : ∀ {A B : Type} [L.Structure A] [L.Structure B], (A ≃[L] B) → (P A ↔ P B))
    (V : Type) [L.Structure V] : DecisionProblem.ofPred P V ↔ P V := by
  constructor
  · rintro ⟨B, i, f, h⟩
    exact (hP f).mp h
  · intro h
    exact ⟨V, inferInstance, Language.Equiv.refl _ _, h⟩

/-- A first-order reduction transported along agreements of its two ends. -/
def FOReduction.congr {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P P' : DecisionProblem L} {Q Q' : DecisionProblem L'}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (hQ : ∀ (A : Type) [L'.Structure A], Q A ↔ Q' A)
    (f : FOReduction P Q) : FOReduction P' Q' :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => ((hP A).symm.trans (f.correct A)).trans (hQ _) }

/-- An ordered first-order reduction transported along agreements of its two
ends. -/
def OrderedFOReduction.congr {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P P' : DecisionProblem L} {Q Q' : DecisionProblem L'}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (hQ : ∀ (A : Type) [L'.Structure A], Q A ↔ Q' A)
    (f : OrderedFOReduction P Q) : OrderedFOReduction P' Q' :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => ((hP A).symm.trans (f.correct A)).trans (hQ _) }

/-- An FO(DTC) reduction transported along an agreement of its source. -/
def DTCReduction.congrSource {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P P' : DecisionProblem L} {Q : DecisionProblem L'}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (f : DTCReduction P Q) : DTCReduction P' Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    fam := f.fam
    toRel := f.toRel
    map_nonempty := f.map_nonempty
    correct := fun A _ _ _ _ => (hP A).symm.trans (f.correct A) }

/--
---
conclusion: Lax945089.EvenInvariance.even_iff
---
The property is invariant, as the library proves when it bundles the problem.
-/
theorem even_iff (A : Type) [Language.empty.Structure A] : EVEN A ↔ Even (Nat.card A) :=
  ofPred_iff (P := fun A _ => Even (Nat.card A)) (fun e =>
    (DescriptiveComplexity.EVEN).iso_invariant e) A

/-- The library's EVEN and the concept's have the same instances. -/
theorem even_agree (A : Type)
    [Language.empty.Structure A] : DescriptiveComplexity.EVEN A ↔ EVEN A :=
  (even_iff A).symm

/--
---
conclusion: Lax945089.EvenInvariance.parity_iff
---
The property is invariant, as the library proves when it bundles the problem.
-/
theorem parity_iff (A : Type) [markedSet.Structure A] :
    PARITY A ↔ Even (Marked A).ncard :=
  ofPred_iff (P := fun A _ => Even (Marked A).ncard)
    (fun e => (DescriptiveComplexity.PARITY).iso_invariant e) A

/-- The library's PARITY and the concept's have the same instances. -/
theorem parity_agree (A : Type) [markedSet.Structure A] :
    DescriptiveComplexity.PARITY A ↔ PARITY A :=
  (parity_iff A).symm

/--
---
conclusion: Lax945089.EhrenfeuchtMethodology.realize_sentence_of_efEquiv
---
The library's induction on the sentence, one round per quantifier.
-/
theorem realize_sentence_of_efEquiv {L : Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N]
    {n : ℕ} [L.IsRelational] (h : EFEquiv L M N n) (φ : L.Sentence) (hφ : qdepth φ ≤ n) :
    M ⊨ φ ↔ N ⊨ φ :=
  DescriptiveComplexity.realize_sentence_of_efEquiv h φ hφ

/--
---
conclusion: Lax945089.GamesOnSets.efEquiv_bare
---
The library's strategy on bare sets.
-/
theorem efEquiv_bare {M N : Type} [Language.empty.Structure M] [Language.empty.Structure N]
    [Finite M]
    [Finite N] (n : ℕ) (hM : n ≤ Nat.card M) (hN : n ≤ Nat.card N) : EFEquiv Language.empty M N n :=
  DescriptiveComplexity.efEquiv_bare n hM hN

/--
---
conclusion: Lax945089.GamesOnSets.exists_card_bound_of_foDefinableFree
---
The library's theorem, the method applied to the defining sentence.
-/
theorem exists_card_bound_of_foDefinableFree {P : DecisionProblem Language.empty}
    (h : FODefinableFree P) :
    ∃ N : ℕ, ∀ (A B : Type) [Language.empty.Structure A] [Language.empty.Structure B] [Finite A]
    [Finite B]
      [Nonempty A] [Nonempty B], N ≤ Nat.card A → N ≤ Nat.card B → (P A ↔ P B) :=
  DescriptiveComplexity.exists_card_bound_of_foDefinableFree h

/--
---
conclusion: Lax945089.GamesOnLinearOrders.efEquiv_linearOrder
---
The library's strategy, by truncated distances.
-/
theorem efEquiv_linearOrder {A B : Type} [Language.empty.Structure A] [Language.empty.Structure B]
    [LinearOrder A]
    [LinearOrder B] [Finite A] [Finite B] (n : ℕ) (hA : 2 ^ n ≤ Nat.card A)
    (hB : 2 ^ n ≤ Nat.card B) : EFEquiv (Language.empty.sum Language.order) A B n :=
  DescriptiveComplexity.efEquiv_linearOrder n hA hB

/--
---
conclusion: Lax945089.PebbleInvariance.realize_equivK₂
---
The library's invariance lemma, by induction on the formula.
-/
theorem realize_equivK₂ {L : Language.{0, 0}} {M N : Type} {k : ℕ} [L.IsRelational] [L.Structure M]
    [L.Structure N] [Finite M] [Finite N] {S : Set ((n : ℕ) × L.Relations n)} {α : Type}
    [Fintype α] {n : ℕ} (φ : L.BoundedFormula α n) (g : α → Fin k) (h : Fin n → Fin k)
    (hh : Function.Injective h) (hgh : ∀ (i : α) (j : Fin n), g i ≠ h j)
    (hk : (Finset.image g Finset.univ ∪ Finset.image h Finset.univ).card + qdepth φ ≤ k)
    (hS : RelsIn S φ) (v : Fin k → M) (w : Fin k → N)
    (hvw : EquivK₂ (atomicAgreeOn₂ S M N k) v w) :
    (φ.Realize (fun i => v (g i)) fun j => v (h j)) ↔
      φ.Realize (fun i => w (g i)) fun j => w (h j) :=
  DescriptiveComplexity.realize_equivK₂ φ g h hh hgh hk hS v w hvw

/--
---
conclusion: Lax945089.PebbleInvariance.equivK₂_bare
---
The library's strategy on bare sets.
-/
theorem equivK₂_bare {M N : Type} {k : ℕ} [Language.empty.Structure M] [Language.empty.Structure N]
    [Finite M] [Finite N] {S : Set ((n : ℕ) × Language.empty.Relations n)} (hM : k ≤ Nat.card M)
    (hN : k ≤ Nat.card N) {v : Fin k → M} {w : Fin k → N}
    (h : ∀ (p q : Fin k), v p = v q ↔ w p = w q) : EquivK₂ (atomicAgreeOn₂ S M N k) v w :=
  DescriptiveComplexity.equivK₂_bare hM hN h

/--
---
conclusion: Lax945089.PebbleInvariance.ifpHolds_equivK₂
---
The library's transfer of the stages of the induction, one by one.
-/
theorem ifpHolds_equivK₂ {L : Language.{0, 0}} {M N : Type} {k : ℕ}
    {S : Set ((n : ℕ) × L.Relations n)} [L.Structure M] [L.Structure N] [L.IsRelational]
    [Finite M] [Finite N] (d : StepDef L) (hb : StepDef.VarBound d k)
    (hu : StepDef.UsesRels d S) (ho : qdepth d.out ≤ k) {v : Fin k → M} {w : Fin k → N}
    (hvw : EquivK₂ (atomicAgreeOn₂ S M N k) v w) : d.IFPHolds M ↔ d.IFPHolds N :=
  DescriptiveComplexity.StepDef.ifpHolds_equivK₂ d hb hu ho hvw

/--
---
conclusion: Lax945089.NoDefinableOrder.not_isLinearOrder_inflLimit
---
The library's theorem, by invariance of the limit under a transposition.
-/
theorem not_isLinearOrder_inflLimit {k : ℕ} (d : StepDef Language.empty) {i : d.B.ι}
    (hb : StepDef.VarBound d k) (harity : d.B.arity i = 2) (A : Type) [Language.empty.Structure A]
    [Finite A] (hk : k ≤ Nat.card A) :
    ¬IsLinearOrder A fun x y => d.inflLimit A i fun p => ![x, y] (Fin.cast harity p) :=
  DescriptiveComplexity.not_isLinearOrder_inflLimit d hb harity A hk

/--
---
conclusion: Lax945089.EvenNotFirstOrder.foDefinableFree_foDefinable
---
The library's reading of a sentence over the ordered expansion.
-/
theorem foDefinableFree_foDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : FODefinableFree P) : FODefinable P :=
  DescriptiveComplexity.FODefinableFree.foDefinable h

/--
---
conclusion: Lax945089.EvenNotFirstOrder.even_not_foDefinableFree
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem even_not_foDefinableFree : ¬FODefinableFree EVEN :=
  fun h => DescriptiveComplexity.even_not_foDefinableFree
    ((DescriptiveComplexity.foDefinableFree_congr fun A _ _ => even_agree A).mpr h)

/--
---
conclusion: Lax945089.EvenNotFirstOrder.even_not_foDefinable
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem even_not_foDefinable : ¬FODefinable EVEN :=
  fun h => DescriptiveComplexity.even_not_foDefinable
    ((DescriptiveComplexity.foDefinable_congr fun A _ _ => even_agree A).mpr h)

/--
---
conclusion: Lax945089.FirstOrderBelowTransitiveClosure.even_dtcDefinable
---
The library's walk along the order, transported to the concept's problem.
-/
theorem even_dtcDefinable : DTCDefinable EVEN :=
  (Lax485149.LClosure.LOGSPACE_mem_congr_finite fun A _ _ => even_agree A).mp
    DescriptiveComplexity.even_dtcDefinable

/--
---
conclusion: Lax945089.FirstOrderBelowTransitiveClosure.even_tcDefinable
---
A deterministic walk is a walk, a statement of the submission on logarithmic
space.
-/
theorem even_tcDefinable : TCDefinable EVEN :=
  Lax485149.FirstOrderInTransitiveClosure.dtcDefinable_tcDefinable
    Lax945089.FirstOrderBelowTransitiveClosure.even_dtcDefinable

/--
---
conclusion: Lax945089.FirstOrderBelowTransitiveClosure.even_mem_NL
---
FO(TC) definability is membership in NL, a statement of the submission on
logarithmic space.
-/
theorem even_mem_NL : NL.Mem EVEN :=
  (Lax485149.NLIsTransitiveClosure.tcDefinable_iff_mem_NL EVEN).mp
    Lax945089.FirstOrderBelowTransitiveClosure.even_tcDefinable

/--
---
conclusion: Lax945089.FirstOrderBelowTransitiveClosure.even_mem_PTIME
---
NL is contained in PTIME, a statement of the submission on polynomial time.
-/
theorem even_mem_PTIME : PTIME.Mem EVEN :=
  Lax535992.NLSubsetPTIME.NL_subset_PTIME EVEN
    Lax945089.FirstOrderBelowTransitiveClosure.even_mem_NL

/--
---
conclusion: Lax945089.FirstOrderBelowTransitiveClosure.exists_tcDefinable_not_foDefinable
---
EVEN, by this submission's statements.
-/
theorem exists_tcDefinable_not_foDefinable :
    ∃ P : DecisionProblem Language.empty, TCDefinable P ∧ ¬FODefinable P :=
  ⟨EVEN, Lax945089.FirstOrderBelowTransitiveClosure.even_tcDefinable,
    Lax945089.EvenNotFirstOrder.even_not_foDefinable⟩

/--
---
conclusion: Lax945089.FirstOrderBelowACZero.even_ac0Definable
---
The library's sentence on the rank of the greatest element, transported to
the concept's problem.
-/
theorem even_ac0Definable : AC0Definable EVEN :=
  (Lax895169.ACZeroFinite.ac0Definable_congr_finite fun A _ _ => even_agree A).mp
    DescriptiveComplexity.even_ac0Definable

/--
---
conclusion: Lax945089.FirstOrderBelowACZero.exists_ac0Definable_not_foDefinable
---
EVEN, by this submission's statements.
-/
theorem exists_ac0Definable_not_foDefinable :
    ∃ P : DecisionProblem Language.empty, AC0Definable P ∧ ¬FODefinable P :=
  ⟨EVEN, Lax945089.FirstOrderBelowACZero.even_ac0Definable,
    Lax945089.EvenNotFirstOrder.even_not_foDefinable⟩

/--
---
conclusion: Lax945089.OrderFreeInductionMissesPTIME.even_not_ifpDefinableFree
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem even_not_ifpDefinableFree : ¬IFPDefinableFree EVEN :=
  fun h => DescriptiveComplexity.even_not_ifpDefinableFree
    ((DescriptiveComplexity.ifpDefinableFree_congr fun A _ _ => even_agree A).mpr h)

/--
---
conclusion: Lax945089.OrderFreeInductionMissesPTIME.exists_mem_PTIME_not_ifpDefinableFree
---
EVEN, by this submission's statements.
-/
theorem exists_mem_PTIME_not_ifpDefinableFree :
    ∃ P : DecisionProblem Language.empty, PTIME.Mem P ∧ ¬IFPDefinableFree P :=
  ⟨EVEN, Lax945089.FirstOrderBelowTransitiveClosure.even_mem_PTIME,
    Lax945089.OrderFreeInductionMissesPTIME.even_not_ifpDefinableFree⟩

/--
---
conclusion: Lax945089.ParityInLogSpace.parity_mem_LOGSPACE
---
The library's deterministic walk, transported to the concept's problem.
-/
theorem parity_mem_LOGSPACE : LOGSPACE.Mem PARITY :=
  (Lax485149.LClosure.LOGSPACE_mem_congr_finite fun A _ _ => parity_agree A).mp
    DescriptiveComplexity.parity_mem_LOGSPACE

/--
---
conclusion: Lax945089.ParityInLogSpace.even_fo_reduction_parity
---
The library's reduction marking every element, transported to the concept's
problems.
-/
theorem even_fo_reduction_parity : Nonempty (FOReduction EVEN PARITY) :=
  ⟨FOReduction.congr even_agree parity_agree DescriptiveComplexity.even_fo_reduction_parity⟩

/--
---
conclusion: Lax945089.ParityInLogSpace.parity_not_foDefinable
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem parity_not_foDefinable : ¬FODefinable PARITY :=
  fun h => DescriptiveComplexity.parity_not_foDefinable
    ((DescriptiveComplexity.foDefinable_congr fun A _ _ => parity_agree A).mpr h)

/--
---
conclusion: Lax945089.ReductionsBelowLogSpace.exists_dtcReduction_not_orderedReduction
---
The library's theorem, the reductions transported to the concept's problem
along the agreement.
-/
theorem exists_dtcReduction_not_orderedReduction :
    ∃ (L : Language.{0, 0}) (_ : L.IsRelational) (Q : DecisionProblem L),
      Nonempty (DTCReduction EVEN Q) ∧ IsEmpty (OrderedFOReduction EVEN Q) :=
  let ⟨L, inst, Q, ⟨f⟩, hne⟩ := DescriptiveComplexity.exists_dtcReduction_not_orderedReduction
  ⟨L, inst, Q, ⟨DTCReduction.congrSource even_agree f⟩,
    ⟨fun g => hne.false
      (OrderedFOReduction.congr (fun A _ => (even_agree A).symm) (fun _ _ => Iff.rfl) g)⟩⟩

end Lax945089Proofs.Bridge
