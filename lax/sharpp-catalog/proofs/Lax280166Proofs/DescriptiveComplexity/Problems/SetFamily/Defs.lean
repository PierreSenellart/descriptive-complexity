/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Vocabulary
import Lax280166Proofs.DescriptiveComplexity.Interpretation
import Lax280166Proofs.DescriptiveComplexity.Numbers.Unary
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies

namespace Lax280166Proofs.DescriptiveComplexity.CoversOn
end Lax280166Proofs.DescriptiveComplexity.CoversOn

namespace Lax280166Proofs.DescriptiveComplexity.ExactlyCoversOn
end Lax280166Proofs.DescriptiveComplexity.ExactlyCoversOn

namespace Lax280166Proofs.DescriptiveComplexity.HitsOn
end Lax280166Proofs.DescriptiveComplexity.HitsOn

namespace Lax280166Proofs.DescriptiveComplexity.PacksOn
end Lax280166Proofs.DescriptiveComplexity.PacksOn

namespace Lax280166Proofs.DescriptiveComplexity.SplitsOn
end Lax280166Proofs.DescriptiveComplexity.SplitsOn

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (ExactCoverBy)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.SetFamily (CoversOn ExactlyCoversOn HasExactCover HasLargeSetPacking HasSetSplitting HasSmallHittingSet HasSmallSetCover HitsOn PacksOn SSElem SSFam SSMarked SSMem SplitsOn)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem ssElem ssFam ssMarked ssMem)
end FirstOrder.Language

/-!
# Set Cover, Hitting Set and Set Packing: definitions

The three classical problems on set systems ([Karp 1972][karp1972reducibility]),
as decision problems on `FirstOrder.Language.setSystem`-structures: a universe
carrying two unary marks separating the ground *elements* from the *sets* of a
family, a binary incidence relation between them, and a third unary mark
carrying the numeric threshold `k` in the *unary representation* of
`DescriptiveComplexity.Numbers.Unary` (the threshold is the cardinality
`Set.ncard` of the marked set, order-free and isomorphism-invariant for free).

* `DescriptiveComplexity.SetCover`: some subfamily of at most `k` sets covers every
  element;
* `DescriptiveComplexity.HittingSet`: some set of at most `k` elements meets every
  set of the family;
* `DescriptiveComplexity.SetPacking`: some subfamily of at least `k` pairwise
  disjoint sets exists.

They are the set-system counterparts of the clique family
(`DescriptiveComplexity.Problems.CliqueFamily`), and are organized the same way: the
semantics is carried by generic properties of predicates on a type –
`DescriptiveComplexity.CoversOn`, its transpose `DescriptiveComplexity.HitsOn` (elements
and sets exchanged, incidence read backwards) and `DescriptiveComplexity.PacksOn` –
which the isomorphism-invariance proofs and the reductions share. Set Cover
and Hitting Set being literally one property read in two directions is what
makes them inter-reducible by a single interpretation
(`DescriptiveComplexity.Problems.SetFamily.Reductions`), just as complementation
relates Clique and Independent Set.

Two conventions worth stating once:

* Nothing forces an element of the universe to be an element or a set, or
  forbids it to be both: elements outside both marks are junk that no
  condition mentions, which is what lets a first-order interpretation build a
  set system inside a tagged power of its input universe without a
  definable-subset mechanism. Junk *marked* elements would change the
  threshold, so interpretations remain responsible for the mark they define.
* Disjointness in `DescriptiveComplexity.PacksOn` is required of the ground
  elements only. This is not cosmetic: the interpretation of
  `DescriptiveComplexity.Problems.SetFamily.FromGraphs` produces junk tuples incident
  to two sets each, and those must not count as witnesses of an intersection.

As with the clique family, cardinality thresholds are only meaningful on
finite structures, so finiteness of the universe is part of the yes-instances;
by `DescriptiveComplexity.ComplexityClass.mem_congr_finite` this does not affect
any complexity-theoretic statement.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic covering property

The property underlying both problems, for arbitrary unary predicates `Ep`
(ground elements), `Fp` (sets of the family) and `Kp` (marks), and an
arbitrary binary predicate `Mp` (incidence) on a type. -/

section Generic

variable {A : Type}

/-- Exactness of a given subfamily in the “exactly one” form: covering plus
disjointness is one covering set per element. -/
theorem exactCoverBy_iff_unique (Ep Fp : A → Prop) (Mp : A → A → Prop) (G : A → Prop) :
    Lax280166.CountingSetFamilies.ExactCoverBy Ep Fp Mp G ↔ (∀ s, G s → Fp s) ∧ ∀ x, Ep x → ∃! s, G s ∧ Mp x s := by
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hcov, hdisj⟩ x hx
    obtain ⟨s, hs, hms⟩ := hcov x hx
    refine ⟨s, ⟨hs, hms⟩, fun s' hs' => ?_⟩
    by_contra hne
    exact hdisj s' s hs'.1 hs hne x hx ⟨hs'.2, hms⟩
  · intro h
    refine ⟨fun x hx => ?_, fun s s' hs hs' hne x hx => ?_⟩
    · obtain ⟨s, hs, -⟩ := h x hx
      exact ⟨s, hs⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨s₀, -, huniq⟩ := h x hx
      exact hne ((huniq s ⟨hs, h1⟩).trans (huniq s' ⟨hs', h2⟩).symm)

/-! #### The threshold as an injection

On a finite universe, comparing the decoded numbers is comparing sizes, so the
threshold condition can equivalently be read as the existence of an injection.
This is the form the second-order definitions guess. -/

section Embedding

end Embedding

variable {B : Type}

/-- `CoversOn` transports along an equivalence commuting with the four
predicates. -/
theorem CoversOn.of_equiv (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : Lax799700.SetFamily.CoversOn EB FB MB KB) : Lax799700.SetFamily.CoversOn EA FA MA KA := by
  obtain ⟨G, hGF, hcov, hcard⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun x hx => ?_, ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · obtain ⟨s, hs, hms⟩ := hcov (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
    refine ⟨u s, by simpa using hs, ?_⟩
    have := (hM (u.symm x) s).mp hms
    simpa using this
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u G]
    exact hcard

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.SetFamily.CoversOn

export Lax280166Proofs.DescriptiveComplexity.CoversOn (of_equiv)

end Lax799700.SetFamily.CoversOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

private theorem symm_hUn {PB : B → Prop} {PA : A → Prop} (u : B ≃ A)
    (hP : ∀ b, PB b ↔ PA (u b)) (a : A) : PA a ↔ PB (u.symm a) := by
  rw [hP]
  simp

private theorem symm_hBin {MB : B → B → Prop} {MA : A → A → Prop} (u : B ≃ A)
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (a a' : A) :
    MA a a' ↔ MB (u.symm a) (u.symm a') := by
  rw [hM]
  simp

/-- `CoversOn` transports along an equivalence, iff version. -/
theorem CoversOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    Lax799700.SetFamily.CoversOn EB FB MB KB ↔ Lax799700.SetFamily.CoversOn EA FA MA KA :=
  ⟨CoversOn.of_equiv u hE hF hM hK,
    CoversOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)
      (symm_hUn u hK)⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.SetFamily.CoversOn

export Lax280166Proofs.DescriptiveComplexity.CoversOn (equiv_iff)

end Lax799700.SetFamily.CoversOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `HitsOn` transports along an equivalence, iff version. -/
theorem HitsOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    Lax799700.SetFamily.HitsOn EB FB MB KB ↔ Lax799700.SetFamily.HitsOn EA FA MA KA :=
  CoversOn.equiv_iff u hF hE (fun b b' => hM b' b) hK

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.SetFamily.HitsOn

export Lax280166Proofs.DescriptiveComplexity.HitsOn (equiv_iff)

end Lax799700.SetFamily.HitsOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `PacksOn` transports along an equivalence commuting with the four
predicates. -/
theorem PacksOn.of_equiv (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : Lax799700.SetFamily.PacksOn EB FB MB KB) : Lax799700.SetFamily.PacksOn EA FA MA KA := by
  obtain ⟨G, hGF, hdisj, hcard⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun s s' hs hs' hne x hx => ?_, ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · rintro ⟨h1, h2⟩
    exact hdisj (u.symm s) (u.symm s') hs hs' (fun h => hne (u.symm.injective h))
      (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
      ⟨(hM (u.symm x) (u.symm s)).mpr (by simpa using h1),
        (hM (u.symm x) (u.symm s')).mpr (by simpa using h2)⟩
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u G]
    exact hcard

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.SetFamily.PacksOn

export Lax280166Proofs.DescriptiveComplexity.PacksOn (of_equiv)

end Lax799700.SetFamily.PacksOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `ExactlyCoversOn` transports along an equivalence commuting with the three
predicates. -/
theorem ExactlyCoversOn.of_equiv (u : B ≃ A) {EB FB : B → Prop} {MB : B → B → Prop}
    {EA FA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (h : Lax799700.SetFamily.ExactlyCoversOn EB FB MB) :
    Lax799700.SetFamily.ExactlyCoversOn EA FA MA := by
  obtain ⟨G, hGF, hcov, hdisj⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun x hx => ?_,
    fun s s' hs hs' hne x hx => ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · obtain ⟨s, hs, hms⟩ := hcov (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
    refine ⟨u s, by simpa using hs, ?_⟩
    have := (hM (u.symm x) s).mp hms
    simpa using this
  · rintro ⟨h1, h2⟩
    exact hdisj (u.symm s) (u.symm s') hs hs' (fun h => hne (u.symm.injective h))
      (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
      ⟨(hM (u.symm x) (u.symm s)).mpr (by simpa using h1),
        (hM (u.symm x) (u.symm s')).mpr (by simpa using h2)⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.SetFamily.ExactlyCoversOn

export Lax280166Proofs.DescriptiveComplexity.ExactlyCoversOn (of_equiv)

end Lax799700.SetFamily.ExactlyCoversOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `ExactlyCoversOn` transports along an equivalence, iff version. -/
theorem ExactlyCoversOn.equiv_iff (u : B ≃ A) {EB FB : B → Prop} {MB : B → B → Prop}
    {EA FA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) :
    Lax799700.SetFamily.ExactlyCoversOn EB FB MB ↔ Lax799700.SetFamily.ExactlyCoversOn EA FA MA :=
  ⟨ExactlyCoversOn.of_equiv u hE hF hM,
    ExactlyCoversOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.SetFamily.ExactlyCoversOn

export Lax280166Proofs.DescriptiveComplexity.ExactlyCoversOn (equiv_iff)

end Lax799700.SetFamily.ExactlyCoversOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `PacksOn` transports along an equivalence, iff version. -/
theorem PacksOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    Lax799700.SetFamily.PacksOn EB FB MB KB ↔ Lax799700.SetFamily.PacksOn EA FA MA KA :=
  ⟨PacksOn.of_equiv u hE hF hM hK,
    PacksOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)
      (symm_hUn u hK)⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.SetFamily.PacksOn

export Lax280166Proofs.DescriptiveComplexity.PacksOn (equiv_iff)

end Lax799700.SetFamily.PacksOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

end Generic

/-! ### The two problems -/

section Problems

section Shorthands

variable {A : Type} [Lax799700.SetFamily.setSystem.Structure A]

end Shorthands

variable (A : Type) [Lax799700.SetFamily.setSystem.Structure A]

end Problems

/-! ### Isomorphism-invariance and the bundled problems -/

section Iso

variable {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B]

private theorem ssElem_map (e : A ≃[Lax799700.SetFamily.setSystem] B) (a : A) :
    Lax799700.SetFamily.SSElem a ↔ Lax799700.SetFamily.SSElem (e a) :=
  relMap_equiv₁ e Lax799700.SetFamily.ssElem a

private theorem ssFam_map (e : A ≃[Lax799700.SetFamily.setSystem] B) (a : A) :
    Lax799700.SetFamily.SSFam a ↔ Lax799700.SetFamily.SSFam (e a) :=
  relMap_equiv₁ e Lax799700.SetFamily.ssFam a

private theorem ssMem_map (e : A ≃[Lax799700.SetFamily.setSystem] B) (a b : A) :
    Lax799700.SetFamily.SSMem a b ↔ Lax799700.SetFamily.SSMem (e a) (e b) :=
  relMap_equiv₂ e Lax799700.SetFamily.ssMem a b

private theorem ssMarked_map (e : A ≃[Lax799700.SetFamily.setSystem] B) (a : A) :
    Lax799700.SetFamily.SSMarked a ↔ Lax799700.SetFamily.SSMarked (e a) :=
  relMap_equiv₁ e Lax799700.SetFamily.ssMarked a

/-- The set-cover threshold property is isomorphism-invariant. -/
theorem hasSmallSetCover_iso (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    Lax799700.SetFamily.HasSmallSetCover A ↔ Lax799700.SetFamily.HasSmallSetCover B :=
  and_congr e.toEquiv.finite_iff
    (CoversOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))

/-- The hitting-set threshold property is isomorphism-invariant. -/
theorem hasSmallHittingSet_iso (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    Lax799700.SetFamily.HasSmallHittingSet A ↔ Lax799700.SetFamily.HasSmallHittingSet B :=
  and_congr e.toEquiv.finite_iff
    (HitsOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))

/-- The set-packing threshold property is isomorphism-invariant. -/
theorem hasLargeSetPacking_iso (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    Lax799700.SetFamily.HasLargeSetPacking A ↔ Lax799700.SetFamily.HasLargeSetPacking B :=
  and_congr e.toEquiv.finite_iff
    (PacksOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))

/-- The exact-cover property is isomorphism-invariant. -/
theorem hasExactCover_iso (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    Lax799700.SetFamily.HasExactCover A ↔ Lax799700.SetFamily.HasExactCover B :=
  ExactlyCoversOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)

end Iso

/-- SET COVER, as a problem on set systems: is there a subfamily covering
every ground element, at most as large as the marked set? -/
def SetCover : Lax904597.Problems.DecisionProblem Lax799700.SetFamily.setSystem where
  Holds := fun A inst => @Lax799700.SetFamily.HasSmallSetCover A inst
  iso_invariant := fun e => hasSmallSetCover_iso e

/-- HITTING SET, as a problem on set systems: is there a set of ground
elements meeting every set of the family, at most as large as the marked
set? -/
def HittingSet : Lax904597.Problems.DecisionProblem Lax799700.SetFamily.setSystem where
  Holds := fun A inst => @Lax799700.SetFamily.HasSmallHittingSet A inst
  iso_invariant := fun e => hasSmallHittingSet_iso e

/-- SET PACKING, as a problem on set systems: is there a pairwise disjoint
subfamily at least as large as the marked set? -/
def SetPacking : Lax904597.Problems.DecisionProblem Lax799700.SetFamily.setSystem where
  Holds := fun A inst => @Lax799700.SetFamily.HasLargeSetPacking A inst
  iso_invariant := fun e => hasLargeSetPacking_iso e

/-- EXACT COVER, as a problem on set systems: is there a subfamily covering
every ground element exactly once? The marked set plays no role – exactness
replaces the threshold. -/
def ExactCover : Lax904597.Problems.DecisionProblem Lax799700.SetFamily.setSystem where
  Holds := fun A inst => @Lax799700.SetFamily.HasExactCover A inst
  iso_invariant := fun e => hasExactCover_iso e

end Lax280166Proofs.DescriptiveComplexity


