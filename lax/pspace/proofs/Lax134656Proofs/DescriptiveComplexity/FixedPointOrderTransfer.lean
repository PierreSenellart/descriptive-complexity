/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.FixedPointPartial
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity.DecisionProblem
end Lax134656Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax134656Proofs.DescriptiveComplexity.IFPDefinableFree
end Lax134656Proofs.DescriptiveComplexity.IFPDefinableFree

namespace Lax134656Proofs.DescriptiveComplexity.PFPDefinableFree
end Lax134656Proofs.DescriptiveComplexity.PFPDefinableFree

namespace Lax134656Proofs.DescriptiveComplexity.StepDef
end Lax134656Proofs.DescriptiveComplexity.StepDef

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax134656Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (IFPDefinableFree PFPDefinable PFPDefinableFree)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable StepDef)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (PFPHolds partStage)
end Lax535992.InflationaryFixedPoint.StepDef

/-!
# Order relativization: moving the order between the instance and the vocabulary

The ordered fixed-point definability notions
(`DescriptiveComplexity.IFPDefinable`, `DescriptiveComplexity.PFPDefinable`)
quantify over every linear order on the universe of an `L`-structure; the
order-free notions over the *ordered expansion* `L.sum Language.order` instead
see the order as one more relation of the instance. This file proves the two
readings interchangeable, the bookkeeping the unordered Abiteboul–Vianu
theorem (`DescriptiveComplexity.AbiteboulVianu`) threads its right-to-left
direction through:

* `DescriptiveComplexity.DecisionProblem.withOrder` – the problem «the order
  symbol is a linear order, and `P` holds on the `L`-reduct», over
  `L.sum Language.order`;
* `DescriptiveComplexity.ifpDefinable_iff_ifpDefinableFree_withOrder` and
  `DescriptiveComplexity.pfpDefinable_iff_pfpDefinableFree_withOrder` – `P` is
  FO(≤, IFP) (resp. FO(≤, PFP)) definable exactly when `P.withOrder` is
  *order-free* FO(IFP) (resp. FO(PFP)) definable.

Left to right, the induction is reused as is and its output is guarded by the
first-order sentence «the order symbol is a linear order»
(`DescriptiveComplexity.leLinearS`, via
`DescriptiveComplexity.StepDef.guardOut`); on an instance whose order symbol
does satisfy the guard, the promoted order
(`DescriptiveComplexity.LeLinearOn.linearOrder`) rebuilds the ordered
instance, identical to the given one through the identity isomorphism
(`DescriptiveComplexity.relMapIffEquiv`). Right to left is immediate: an
ordered `L`-structure *is* an instance of the expansion whose order symbol is
a linear order (`DescriptiveComplexity.sumOrderStructure`).
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Identity isomorphisms between structures with the same relations -/

/-- Two structures over a relational vocabulary interpreting every relation
symbol equivalently are isomorphic through the identity map. -/
def relMapIffEquiv [L.IsRelational] {A : Type} (inst inst' : L.Structure A)
    (h : ∀ {n : ℕ} (r : L.Relations n) (x : Fin n → A),
      @RelMap L A inst n r x ↔ @RelMap L A inst' n r x) :
    @Language.Equiv L A A inst inst' :=
  @Language.Equiv.mk L A A inst inst' (Equiv.refl A)
    (fun {_} f _ => isEmptyElim f) (fun {_} r x => (h r x).symm)

/-- An isomorphism over an expanded vocabulary is an isomorphism of the
reducts. -/
def reductSumInlEquiv {L' : Language.{0, 0}} {A B : Type}
    [instA : (L.sum L').Structure A] [instB : (L.sum L').Structure B]
    (e : A ≃[L.sum L'] B) :
    @Language.Equiv L A B ((LHom.sumInl : L →ᴸ L.sum L').reduct A)
      ((LHom.sumInl : L →ᴸ L.sum L').reduct B) :=
  @Language.Equiv.mk L A B ((LHom.sumInl : L →ᴸ L.sum L').reduct A)
    ((LHom.sumInl : L →ᴸ L.sum L').reduct B) e.toEquiv
    (fun {_} f x => e.map_fun' (Sum.inl f) x)
    (fun {_} r x => e.map_rel' (Sum.inl r) x)

/-! ### «The order symbol is a linear order» -/

section LeLinear

variable (L)

/-- The interpretation of the order symbol of the ordered expansion is a
linear order: reflexive, transitive, antisymmetric and total. This is the
guard under which a structure over `L.sum Language.order` is an ordered
`L`-structure. -/
def LeLinearOn (A : Type) [(L.sum Language.order).Structure A] : Prop :=
  Std.Refl (fun x y : A =>
    RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y]) ∧
  IsTrans A (fun x y : A =>
    RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y]) ∧
  Std.Antisymm (fun x y : A =>
    RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y]) ∧
  Std.Total (fun x y : A =>
    RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y])

/-- The guard sentence «the order symbol is a linear order», over the ordered
expansion. -/
def leLinearS : (L.sum Language.order).Sentence :=
  (leSymb : (L.sum Language.order).Relations 2).reflexive ⊓
    ((leSymb : (L.sum Language.order).Relations 2).transitive ⊓
      ((leSymb : (L.sum Language.order).Relations 2).antisymmetric ⊓
        (leSymb : (L.sum Language.order).Relations 2).total))

/-- Realization of the guard sentence: the order symbol is a linear order. -/
theorem realize_leLinearS (A : Type) [(L.sum Language.order).Structure A] :
    A ⊨ leLinearS L ↔ LeLinearOn L A := by
  have hsplit : A ⊨ leLinearS L ↔
      (A ⊨ (leSymb : (L.sum Language.order).Relations 2).reflexive ∧
        (A ⊨ (leSymb : (L.sum Language.order).Relations 2).transitive ∧
          (A ⊨ (leSymb : (L.sum Language.order).Relations 2).antisymmetric ∧
            A ⊨ (leSymb : (L.sum Language.order).Relations 2).total))) :=
    Formula.realize_inf.trans (and_congr Iff.rfl
      (Formula.realize_inf.trans (and_congr Iff.rfl Formula.realize_inf)))
  rw [hsplit, Relations.realize_reflexive, Relations.realize_transitive,
    Relations.realize_antisymmetric, Relations.realize_total]
  exact Iff.rfl

variable {L}

/-- Promoting a linear order symbol to a linear order on the universe
(decidability by choice). -/
@[instance_reducible]
noncomputable def LeLinearOn.linearOrder {A : Type}
    [(L.sum Language.order).Structure A] (h : LeLinearOn L A) : LinearOrder A where
  le x y := RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y]
  le_refl := h.1.refl
  le_trans := h.2.1.trans
  le_antisymm := h.2.2.1.antisymm
  le_total := h.2.2.2.total
  toDecidableLE := fun _ _ => Classical.propDecidable _

/-- The guard transports along an isomorphism over the ordered expansion. -/
theorem LeLinearOn.equiv {A B : Type} [(L.sum Language.order).Structure A]
    [(L.sum Language.order).Structure B] (e : A ≃[L.sum Language.order] B)
    (h : LeLinearOn L A) : LeLinearOn L B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hrel : ∀ a a' : A,
      RelMap (leSymb : (L.sum Language.order).Relations 2) ![a, a'] ↔
        RelMap (leSymb : (L.sum Language.order).Relations 2) ![e a, e a'] :=
    fun a a' => relMap_equiv₂ e leSymb a a'
  have hsurj : Function.Surjective e := EquivLike.surjective e
  refine ⟨⟨fun b => ?_⟩, ⟨fun b b' b'' hbb' hb'b'' => ?_⟩,
    ⟨fun b b' hbb' hb'b => ?_⟩, ⟨fun b b' => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hsurj b
    exact (hrel a a).mp (h1.refl a)
  · obtain ⟨a, rfl⟩ := hsurj b
    obtain ⟨a', rfl⟩ := hsurj b'
    obtain ⟨a'', rfl⟩ := hsurj b''
    exact (hrel a a'').mp
      (h2.trans a a' a'' ((hrel a a').mpr hbb') ((hrel a' a'').mpr hb'b''))
  · obtain ⟨a, rfl⟩ := hsurj b
    obtain ⟨a', rfl⟩ := hsurj b'
    exact congrArg _ (h3.antisymm a a' ((hrel a a').mpr hbb') ((hrel a' a).mpr hb'b))
  · obtain ⟨a, rfl⟩ := hsurj b
    obtain ⟨a', rfl⟩ := hsurj b'
    rcases h4.total a a' with hc | hc
    · exact Or.inl ((hrel a a').mp hc)
    · exact Or.inr ((hrel a' a).mp hc)

end LeLinear

/-! ### The problem, moved to the ordered expansion -/

section WithOrder

variable [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L)

private theorem withOrder_iso_invariant {A B : Type}
    [instA : (L.sum Language.order).Structure A]
    [instB : (L.sum Language.order).Structure B] (e : A ≃[L.sum Language.order] B) :
    (LeLinearOn L A ∧
        (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A; P A)) ↔
      (LeLinearOn L B ∧
        (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct B; P B)) :=
  and_congr ⟨fun h => h.equiv e, fun h => h.equiv e.symm⟩
    (@Lax904597.Problems.DecisionProblem.iso_invariant L _ P A B
      ((LHom.sumInl : L →ᴸ L.sum Language.order).reduct A)
      ((LHom.sumInl : L →ᴸ L.sum Language.order).reduct B) (reductSumInlEquiv e))

/-- «The order symbol is a linear order, and `P` holds on the `L`-reduct»:
the problem `P`, moved to the ordered expansion of its vocabulary with the
order now part of the instance. The order-relativized problem through which
definability quantified over all linear orders
(`DescriptiveComplexity.IFPDefinable`, `DescriptiveComplexity.PFPDefinable`)
is compared with order-free definability over the expansion. -/
def DecisionProblem.withOrder : Lax904597.Problems.DecisionProblem (L.sum Language.order) where
  Holds A _ := LeLinearOn L A ∧
    (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A; P A)
  iso_invariant e := withOrder_iso_invariant P e

end WithOrder

end Lax134656Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax134656Proofs.DescriptiveComplexity.DecisionProblem (withOrder)

end Lax904597.Problems.DecisionProblem

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section WithOrder

variable [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L)

end WithOrder

/-! ### Guarding the output of an induction -/

namespace StepDef

variable {L' : Language.{0, 0}} (d : Lax535992.InflationaryFixedPoint.StepDef L') (χ : L'.Sentence)

/-- Guard the output of a simultaneous induction by a sentence over the base
vocabulary: same block, same step formulas, the output conjoined with the
guard. -/
def guardOut : Lax535992.InflationaryFixedPoint.StepDef L' where
  B := d.B
  step := d.step
  out := LHom.sumInl.onSentence χ ⊓ d.out

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (guardOut)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable {L' : Language.{0, 0}} (d : Lax535992.InflationaryFixedPoint.StepDef L') (χ : L'.Sentence)

variable {A : Type} [L'.Structure A]

theorem realize_guardOut_out (ρ : d.B.Assignment A) :
    (@Sentence.Realize _ A (d.B.structure₁ (L := L') ρ) (d.guardOut χ).out) ↔
      (A ⊨ χ ∧ @Sentence.Realize _ A (d.B.structure₁ (L := L') ρ) d.out) := by
  let := d.B.structure₁ (L := L') ρ
  refine Formula.realize_inf.trans (and_congr ?_ Iff.rfl)
  exact (LHom.sumInl : L' →ᴸ L'.sum d.B.lang).realize_onSentence (M := A) χ

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (realize_guardOut_out)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable {L' : Language.{0, 0}} (d : Lax535992.InflationaryFixedPoint.StepDef L') (χ : L'.Sentence)

variable {A : Type} [L'.Structure A]

variable (A) in
/-- The inflationary value of the guarded induction: the guard holds and the
original value does. -/
theorem ifpHolds_guardOut : (d.guardOut χ).IFPHolds A ↔ (A ⊨ χ ∧ d.IFPHolds A) :=
  realize_guardOut_out d χ (d.inflLimit A)

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (ifpHolds_guardOut)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable {L' : Language.{0, 0}} (d : Lax535992.InflationaryFixedPoint.StepDef L') (χ : L'.Sentence)

variable {A : Type} [L'.Structure A]

variable (A) in
/-- The partial value of the guarded induction: the guard holds and the
original value does. -/
theorem pfpHolds_guardOut : (d.guardOut χ).PFPHolds A ↔ (A ⊨ χ ∧ d.PFPHolds A) := by
  constructor
  · rintro ⟨n, hfix, hout⟩
    obtain ⟨hχ, hout'⟩ := (realize_guardOut_out d χ (d.partStage A n)).mp hout
    exact ⟨hχ, n, hfix, hout'⟩
  · rintro ⟨hχ, n, hfix, hout⟩
    exact ⟨n, hfix, (realize_guardOut_out d χ (d.partStage A n)).mpr ⟨hχ, hout⟩⟩

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (pfpHolds_guardOut)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable {L' : Language.{0, 0}} (d : Lax535992.InflationaryFixedPoint.StepDef L') (χ : L'.Sentence)

variable {A : Type} [L'.Structure A]

end StepDef

/-! ### The transfer -/

section Transfer

variable [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L)

private theorem vecEta₂ {A : Type} (x : Fin 2 → A) : ![x 0, x 1] = x := by
  funext j
  fin_cases j <;> simp

/-- The ordered instance rebuilt from a structure over the expansion whose
order symbol is a linear order is the given instance, through the identity
isomorphism. -/
private noncomputable def rebuildEquiv {A : Type}
    [inst : (L.sum Language.order).Structure A]
    (h : LeLinearOn L A) :
    @Language.Equiv (L.sum Language.order) A A
      (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A
       letI := h.linearOrder
       Lax904597.Interpretations.sumOrderStructure L A) inst :=
  letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A
  letI := h.linearOrder
  relMapIffEquiv (Lax904597.Interpretations.sumOrderStructure L A) inst fun {n} r x => by
    cases r with
    | inl s => exact Iff.rfl
    | inr s =>
      cases s with
      | le =>
        exact iff_of_eq
          (congrArg (@RelMap (L.sum Language.order) A inst 2 (Sum.inr orderRel.le))
            (vecEta₂ x))

/-- **Order relativization, inflationary case**: `P` is FO(≤, IFP) definable
exactly when its ordered relativization
(`DescriptiveComplexity.DecisionProblem.withOrder`) is *order-free* FO(IFP)
definable. -/
theorem ifpDefinable_iff_ifpDefinableFree_withOrder :
    Lax535992.InflationaryFixedPoint.IFPDefinable P ↔ Lax134656.PartialFixedPoint.IFPDefinableFree P.withOrder := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d.guardOut (leLinearS L), ?_⟩
    intro A inst _ _
    rw [d.ifpHolds_guardOut (leLinearS L) A, realize_leLinearS L A]
    refine and_congr_right fun h => ?_
    let := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A
    let := h.linearOrder
    exact (hd A).trans
      (@StepDef.ifpHolds_equiv (L.sum Language.order) d A A (Lax904597.Interpretations.sumOrderStructure L A)
        inst (rebuildEquiv h))
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro A instL lo _ _
    refine Iff.trans ?_ (hd A)
    have hlin : LeLinearOn L A :=
      ⟨⟨fun a => le_refl a⟩, ⟨fun a b c hab hbc => le_trans hab hbc⟩,
        ⟨fun a b hab hba => le_antisymm hab hba⟩, ⟨fun a b => le_total a b⟩⟩
    have hP : (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A; P A) ↔ P A :=
      @Lax904597.Problems.DecisionProblem.iso_invariant L _ P A A
        ((LHom.sumInl : L →ᴸ L.sum Language.order).reduct A) instL
        (relMapIffEquiv _ instL fun r x => Iff.rfl)
    exact ⟨fun hp => ⟨hlin, hP.mpr hp⟩, fun hw => hP.mp hw.2⟩

/-- **Order relativization, partial case**: `P` is FO(≤, PFP) definable
exactly when its ordered relativization
(`DescriptiveComplexity.DecisionProblem.withOrder`) is *order-free* FO(PFP)
definable. -/
theorem pfpDefinable_iff_pfpDefinableFree_withOrder :
    Lax134656.PartialFixedPoint.PFPDefinable P ↔ Lax134656.PartialFixedPoint.PFPDefinableFree P.withOrder := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d.guardOut (leLinearS L), ?_⟩
    intro A inst _ _
    rw [d.pfpHolds_guardOut (leLinearS L) A, realize_leLinearS L A]
    refine and_congr_right fun h => ?_
    let := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A
    let := h.linearOrder
    exact (hd A).trans
      (@StepDef.pfpHolds_equiv (L.sum Language.order) d A A (Lax904597.Interpretations.sumOrderStructure L A)
        inst (rebuildEquiv h))
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro A instL lo _ _
    refine Iff.trans ?_ (hd A)
    have hlin : LeLinearOn L A :=
      ⟨⟨fun a => le_refl a⟩, ⟨fun a b c hab hbc => le_trans hab hbc⟩,
        ⟨fun a b hab hba => le_antisymm hab hba⟩, ⟨fun a b => le_total a b⟩⟩
    have hP : (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A; P A) ↔ P A :=
      @Lax904597.Problems.DecisionProblem.iso_invariant L _ P A A
        ((LHom.sumInl : L →ᴸ L.sum Language.order).reduct A) instL
        (relMapIffEquiv _ instL fun r x => Iff.rfl)
    exact ⟨fun hp => ⟨hlin, hP.mpr hp⟩, fun hw => hP.mp hw.2⟩

end Transfer

/-! ### Order-free definability implies ordered definability -/

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

/-- A simultaneous induction over the base vocabulary, read over the ordered
expansion: the formulas ignore the order symbol. -/
noncomputable def liftOrder : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order) where
  B := d.B
  step := fun i =>
    (LHom.sumMap (LHom.sumInl (L' := Language.order))
      (LHom.id d.B.lang)).onFormula (d.step i)
  out :=
    (LHom.sumMap (LHom.sumInl (L' := Language.order))
      (LHom.id d.B.lang)).onSentence d.out

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (liftOrder)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_liftOrder {α : Type} (ρ : d.B.Assignment A)
    (φ : (L.sum d.B.lang).Formula α) (v : α → A) :
    (@Formula.Realize _ A
      (@Lax535992.InflationaryFixedPoint.SOBlock.structure₁ (L.sum Language.order) d.B A
        (Lax904597.Interpretations.sumOrderStructure L A) ρ) _
      ((LHom.sumMap (LHom.sumInl (L' := Language.order))
        (LHom.id d.B.lang)).onFormula φ) v) ↔
      @Formula.Realize _ A (d.B.structure₁ (L := L) ρ) _ φ v := by
  let := d.B.structure₁ (L := L) ρ
  let := @Lax535992.InflationaryFixedPoint.SOBlock.structure₁ (L.sum Language.order) d.B A
    (Lax904597.Interpretations.sumOrderStructure L A) ρ
  exact LHom.realize_onFormula
    (φ := LHom.sumMap (LHom.sumInl (L' := Language.order)) (LHom.id d.B.lang)) φ

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (realize_liftOrder)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem next_liftOrder (ρ : d.B.Assignment A) :
    @Lax535992.InflationaryFixedPoint.StepDef.next (L.sum Language.order) d.liftOrder A (Lax904597.Interpretations.sumOrderStructure L A) ρ =
      d.next ρ := by
  funext i x
  exact propext (d.realize_liftOrder ρ (d.step i) x)

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (next_liftOrder)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem inflStage_liftOrder (n : ℕ) :
    @Lax535992.InflationaryFixedPoint.StepDef.inflStage (L.sum Language.order) d.liftOrder A
        (Lax904597.Interpretations.sumOrderStructure L A) n = d.inflStage A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i x
    rw [@StepDef.inflStage_succ (L.sum Language.order) d.liftOrder A
      (Lax904597.Interpretations.sumOrderStructure L A) n, d.inflStage_succ, ih]
    refine propext (or_congr Iff.rfl ?_)
    exact iff_of_eq (congrFun (congrFun (d.next_liftOrder (d.inflStage A n)) i) x)

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (inflStage_liftOrder)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem partStage_liftOrder (n : ℕ) :
    @Lax134656.PartialFixedPoint.StepDef.partStage (L.sum Language.order) d.liftOrder A
        (Lax904597.Interpretations.sumOrderStructure L A) n = d.partStage A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [@StepDef.partStage_succ (L.sum Language.order) d.liftOrder A
      (Lax904597.Interpretations.sumOrderStructure L A) n, d.partStage_succ, ih]
    exact d.next_liftOrder (d.partStage A n)

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (partStage_liftOrder)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The inflationary value of the lifted induction is the original one. -/
theorem ifpHolds_liftOrder :
    (@Lax535992.InflationaryFixedPoint.StepDef.IFPHolds (L.sum Language.order) d.liftOrder A
        (Lax904597.Interpretations.sumOrderStructure L A)) ↔ d.IFPHolds A := by
  have hlim : @Lax535992.InflationaryFixedPoint.StepDef.inflLimit (L.sum Language.order) d.liftOrder A
      (Lax904597.Interpretations.sumOrderStructure L A) = d.inflLimit A := by
    funext i x
    exact propext (exists_congr fun n => iff_of_eq
      (congrFun (congrFun (d.inflStage_liftOrder n) i) x))
  rw [Lax535992.InflationaryFixedPoint.StepDef.IFPHolds, Lax535992.InflationaryFixedPoint.StepDef.IFPHolds, hlim]
  exact d.realize_liftOrder (d.inflLimit A) d.out default

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (ifpHolds_liftOrder)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The partial value of the lifted induction is the original one. -/
theorem pfpHolds_liftOrder :
    (@Lax134656.PartialFixedPoint.StepDef.PFPHolds (L.sum Language.order) d.liftOrder A
        (Lax904597.Interpretations.sumOrderStructure L A)) ↔ d.PFPHolds A := by
  refine exists_congr fun n => ?_
  rw [d.partStage_liftOrder n]
  exact and_congr
    ⟨fun h => (d.next_liftOrder (d.partStage A n)).symm.trans h,
      fun h => (d.next_liftOrder (d.partStage A n)).trans h⟩
    (d.realize_liftOrder (d.partStage A n) d.out default)

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (pfpHolds_liftOrder)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

variable {A : Type} [L.Structure A] [LinearOrder A]

end StepDef

/-- **Order-free FO(IFP) definability implies ordered definability**: the
induction ignores the order. -/
theorem IFPDefinableFree.ifpDefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax134656.PartialFixedPoint.IFPDefinableFree P) : Lax535992.InflationaryFixedPoint.IFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.liftOrder, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (d.ifpHolds_liftOrder).symm

end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656.PartialFixedPoint.IFPDefinableFree

export Lax134656Proofs.DescriptiveComplexity.IFPDefinableFree (ifpDefinable)

end Lax134656.PartialFixedPoint.IFPDefinableFree

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- **Order-free FO(PFP) definability implies ordered definability**: the
induction ignores the order. -/
theorem PFPDefinableFree.pfpDefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax134656.PartialFixedPoint.PFPDefinableFree P) : Lax134656.PartialFixedPoint.PFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.liftOrder, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (d.pfpHolds_liftOrder).symm

end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656.PartialFixedPoint.PFPDefinableFree

export Lax134656Proofs.DescriptiveComplexity.PFPDefinableFree (pfpDefinable)

end Lax134656.PartialFixedPoint.PFPDefinableFree

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

end Lax134656Proofs.DescriptiveComplexity


