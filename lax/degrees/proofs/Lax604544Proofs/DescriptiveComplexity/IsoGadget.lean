/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.Interpretation
import Mathlib.ModelTheory.Graph
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax604544.RelationIsomorphism
end Lax604544.RelationIsomorphism

namespace Lax604544Proofs.DescriptiveComplexity.RelIsoOn
end Lax604544Proofs.DescriptiveComplexity.RelIsoOn

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.RelationIsomorphism (RelIsoOn)
end Lax604544Proofs.DescriptiveComplexity

/-!
# The two marked sides of an isomorphism problem, as structures

Every problem of the GI degree says “the two marked sides of the instance are
isomorphic”, and every reduction between two such problems runs one gadget on
the pattern side and the same gadget on the host side. The reductions built so
far (`DescriptiveComplexity.Problems.DagIso`) pay for that shape twice: each
characterization lemma is stated once for the pattern side and once, verbatim,
for the host side.

This file is the first half of the cure. It reads a marked binary relation
inside a structure as a `FirstOrder.Language.graph`-structure in its own right
(`DescriptiveComplexity.sideStructure`), and shows that the semantic condition
these problems use – `DescriptiveComplexity.RelIsoOn`, a bijection of the two
marked sets preserving the relation in both directions – is exactly an
isomorphism of those two structures
(`DescriptiveComplexity.relIsoOn_iff_nonempty_sideEquiv`).

The point is what it makes statable: a gadget can then be given on *single*
graphs, where the pattern/host distinction does not exist, and its correctness
asked for in the form “`F G ≅ F H` implies `G ≅ H`” – one statement instead of
two mirrored families. The forward implication is free, an interpretation being
functorial (`DescriptiveComplexity.FOInterpretation.mapLEquiv`).

Nothing here is specific to a vocabulary: the side is given by a unary
predicate and a binary one, so the same lemmas serve
`FirstOrder.Language.twoGraphs` (`patV`/`patE`) and
`FirstOrder.Language.twoDags` (`patV`/`patArc`), whose extra relations the
isomorphism ignores.
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### A marked relation as a graph -/

section Side

end Side

/-! ### The generic property -/

section Generic

variable {A : Type}

variable {B : Type}

/-- `RelIsoOn` transports along an equivalence commuting with the four
predicates. -/
theorem RelIsoOn.of_equiv (u : B ≃ A) {PVB HVB : B → Prop} {PEB HEB : B → B → Prop}
    {PVA HVA : A → Prop} {PEA HEA : A → A → Prop}
    (hPV : ∀ b, PVB b ↔ PVA (u b)) (hHV : ∀ b, HVB b ↔ HVA (u b))
    (hPE : ∀ b b', PEB b b' ↔ PEA (u b) (u b'))
    (hHE : ∀ b b', HEB b b' ↔ HEA (u b) (u b'))
    (h : Lax604544.RelationIsomorphism.RelIsoOn PVB HVB PEB HEB) : Lax604544.RelationIsomorphism.RelIsoOn PVA HVA PEA HEA := by
  obtain ⟨f, hmaps, hinj, hsurj, hedge⟩ := h
  refine ⟨fun a => u (f (u.symm a)), fun x hx => ?_, fun x y hx hy hxy => ?_,
    fun y hy => ?_, fun x y hx hy => ?_⟩
  · exact (hHV (f (u.symm x))).mp (hmaps _ ((hPV (u.symm x)).mpr (by simpa using hx)))
  · have hux : u.symm x = u.symm y :=
      hinj _ _ ((hPV _).mpr (by simpa using hx)) ((hPV _).mpr (by simpa using hy))
        (u.injective hxy)
    simpa using congrArg u hux
  · obtain ⟨b, hb, hfb⟩ := hsurj (u.symm y) ((hHV (u.symm y)).mpr (by simpa using hy))
    exact ⟨u b, (hPV b).mp hb, by simp [hfb]⟩
  · have h := hedge (u.symm x) (u.symm y) ((hPV _).mpr (by simpa using hx))
      ((hPV _).mpr (by simpa using hy))
    rw [hPE, hHE] at h
    simpa using h

end Generic

end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544.RelationIsomorphism.RelIsoOn

export Lax604544Proofs.DescriptiveComplexity.RelIsoOn (of_equiv)

end Lax604544.RelationIsomorphism.RelIsoOn

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `RelIsoOn` transports along an equivalence, iff version. -/
theorem RelIsoOn.equiv_iff (u : B ≃ A) {PVB HVB : B → Prop} {PEB HEB : B → B → Prop}
    {PVA HVA : A → Prop} {PEA HEA : A → A → Prop}
    (hPV : ∀ b, PVB b ↔ PVA (u b)) (hHV : ∀ b, HVB b ↔ HVA (u b))
    (hPE : ∀ b b', PEB b b' ↔ PEA (u b) (u b'))
    (hHE : ∀ b b', HEB b b' ↔ HEA (u b) (u b')) :
    Lax604544.RelationIsomorphism.RelIsoOn PVB HVB PEB HEB ↔ Lax604544.RelationIsomorphism.RelIsoOn PVA HVA PEA HEA :=
  ⟨RelIsoOn.of_equiv u hPV hHV hPE hHE,
    RelIsoOn.of_equiv u.symm (fun a => by rw [hPV]; simp) (fun a => by rw [hHV]; simp)
      (fun a a' => by rw [hPE]; simp) fun a a' => by rw [hHE]; simp⟩

end Generic

end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544.RelationIsomorphism.RelIsoOn

export Lax604544Proofs.DescriptiveComplexity.RelIsoOn (equiv_iff)

end Lax604544.RelationIsomorphism.RelIsoOn

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- **The property is isomorphism of the two marked graphs**: a map of the
universe as in `DescriptiveComplexity.RelIsoOn` is the same thing as an
equivalence of the marked subsets carrying one adjacency relation to the
other. -/
theorem relIsoOn_iff_equiv (PV HV : A → Prop) (PE HE : A → A → Prop) :
    Lax604544.RelationIsomorphism.RelIsoOn PV HV PE HE ↔
      ∃ e : {x : A // PV x} ≃ {y : A // HV y},
        ∀ x y : {x : A // PV x}, PE x.1 y.1 ↔ HE (e x).1 (e y).1 := by
  classical
  constructor
  · rintro ⟨f, hmaps, hinj, hsurj, hedge⟩
    have hbij : Function.Bijective fun x : {x : A // PV x} => (⟨f x.1, hmaps x.1 x.2⟩ :
        {y : A // HV y}) := by
      constructor
      · exact fun x y hxy => Subtype.ext (hinj x.1 y.1 x.2 y.2 (congrArg Subtype.val hxy))
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx, hfx⟩ := hsurj y hy
        exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
    exact ⟨Equiv.ofBijective _ hbij, fun x y => hedge x.1 y.1 x.2 y.2⟩
  · rintro ⟨e, hedge⟩
    refine ⟨fun x => if h : PV x then (e ⟨x, h⟩).1 else x, fun x hx => ?_,
      fun x y hx hy hxy => ?_, fun y hy => ?_, fun x y hx hy => ?_⟩
    · change HV (if h : PV x then (e ⟨x, h⟩).1 else x)
      rw [dif_pos hx]
      exact (e ⟨x, hx⟩).2
    · have hxy' : (if h : PV x then (e ⟨x, h⟩).1 else x) =
          if h : PV y then (e ⟨y, h⟩).1 else y := hxy
      rw [dif_pos hx, dif_pos hy] at hxy'
      exact congrArg Subtype.val (e.injective (Subtype.ext hxy'))
    · obtain ⟨z, hz⟩ : ∃ z : {x : A // PV x}, e z = ⟨y, hy⟩ :=
        ⟨e.symm ⟨y, hy⟩, e.apply_symm_apply _⟩
      refine ⟨z.1, z.2, ?_⟩
      change (if h : PV z.1 then (e ⟨z.1, h⟩).1 else z.1) = y
      rw [dif_pos z.2, Subtype.coe_eta, hz]
    · change PE x y ↔ HE (if h : PV x then (e ⟨x, h⟩).1 else x)
        (if h : PV y then (e ⟨y, h⟩).1 else y)
      rw [dif_pos hx, dif_pos hy]
      exact hedge ⟨x, hx⟩ ⟨y, hy⟩

end Generic

/-! ### The two sides as structures -/

section Sides

end Sides

end Lax604544Proofs.DescriptiveComplexity


