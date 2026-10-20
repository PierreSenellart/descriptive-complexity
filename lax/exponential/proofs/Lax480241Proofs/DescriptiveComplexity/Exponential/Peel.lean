/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Matrix
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign)
end Lax904597.SecondOrder.SOBlock

/-!
# Peeling a quantifier into a block

The semantic core of the translation lemma. Two facts, both independent of any
syntax.

**A guarded block is a point.** A second-order quantifier ranges over *all*
assignments of `DescriptiveComplexity.ExpExpansion.pointBlock`; the quantifier
being translated ranges over the *points* of the expanded universe, which are
the assignments the point guard admits. The two match up
(`DescriptiveComplexity.ExpExpansion.exists_point_iff`,
`DescriptiveComplexity.ExpExpansion.forall_point_iff`): a guarded block *is* a
point, existentially with the guard as a conjunct and universally with the guard
as a hypothesis, which is the usual shape of relativized quantification.

**A guard can be pulled through the rest of the prefix.** The guard of round `i`
sits at nesting depth `i` in the kernel, so peeling round `i` first has to move
it out past the quantifiers that remain
(`DescriptiveComplexity.altBlockQuant_and_const`,
`DescriptiveComplexity.altBlockQuant_const_imp`). Both directions need the block
assignments to be inhabited, which they are –
`DescriptiveComplexity.SOBlock.botAssign` – and the existential case of the
implication needs excluded middle, as relativized quantification always does.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Moving a constant through the prefix -/

section Const

variable {B : Lax904597.SecondOrder.SOBlock} {A : Type}

/-- A conjunct not depending on the rounds moves out of the prefix. -/
theorem altBlockQuant_and_const (g : Prop) :
    ∀ (k : ℕ) (P : (Fin k → B.Assignment A) → Prop) (pol : Bool),
      altBlockQuant A B k (fun ρs => g ∧ P ρs) pol ↔ g ∧ altBlockQuant A B k P pol := by
  intro k
  induction k with
  | zero => intro P pol; exact Iff.rfl
  | succ k ih =>
    intro P pol
    cases pol with
    | true =>
      constructor
      · rintro ⟨ρ, h⟩
        obtain ⟨hg, h'⟩ := (ih _ false).mp h
        exact ⟨hg, ρ, h'⟩
      · rintro ⟨hg, ρ, h⟩
        exact ⟨ρ, (ih _ false).mpr ⟨hg, h⟩⟩
    | false =>
      constructor
      · intro h
        exact ⟨((ih _ true).mp (h (B.botAssign A))).1,
          fun ρ => ((ih _ true).mp (h ρ)).2⟩
      · rintro ⟨hg, h⟩ ρ
        exact (ih _ true).mpr ⟨hg, h ρ⟩

/-- A hypothesis not depending on the rounds moves out of the prefix. The
existential case is where excluded middle enters: with the hypothesis false, any
round will do, and there is one. -/
theorem altBlockQuant_const_imp (g : Prop) :
    ∀ (k : ℕ) (P : (Fin k → B.Assignment A) → Prop) (pol : Bool),
      altBlockQuant A B k (fun ρs => g → P ρs) pol ↔ (g → altBlockQuant A B k P pol) := by
  classical
  intro k
  induction k with
  | zero => intro P pol; exact Iff.rfl
  | succ k ih =>
    intro P pol
    cases pol with
    | true =>
      constructor
      · rintro ⟨ρ, h⟩ hg
        exact ⟨ρ, (ih _ false).mp h hg⟩
      · intro h
        by_cases hg : g
        · obtain ⟨ρ, hρ⟩ := h hg
          exact ⟨ρ, (ih _ false).mpr fun _ => hρ⟩
        · exact ⟨B.botAssign A, (ih _ false).mpr fun hg' => absurd hg' hg⟩
    | false =>
      constructor
      · intro h hg ρ
        exact (ih _ true).mp (h ρ) hg
      · intro h ρ
        exact (ih _ true).mpr fun hg => h hg ρ

end Const

/-! ### A guarded block is a point -/

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The block assignment carrying a point. -/
def pointAssign (p : X.Map A) : X.pointBlock.Assignment A :=
  SOBlock.tagAssign p.1.1 p.1.2

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pointAssign)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

@[simp]
theorem roundAssign_apply [Finite A] [Nonempty A] (pts : Fin m → X.Map A) (i : Fin m) :
    roundAssign pts i = pointAssign (pts i) :=
  rfl

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundAssign_apply)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The condition the point guard expresses, semantically. -/
def IsPointAssign (σ : X.pointBlock.Assignment A) : Prop :=
  ∃ (t : X.Tag) (ρ : X.B.Assignment A), σ = SOBlock.tagAssign t ρ ∧ Lax480241.Expansions.ExpExpansion.DomHolds (X := X) (t, ρ)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (IsPointAssign)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem isPointAssign_pointAssign (p : X.Map A) : IsPointAssign (pointAssign p) :=
  ⟨p.1.1, p.1.2, rfl, p.2⟩

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (isPointAssign_pointAssign)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **A guarded block is a point, existentially.** -/
theorem exists_point_iff (P : X.pointBlock.Assignment A → Prop) :
    (∃ σ : X.pointBlock.Assignment A, IsPointAssign (X := X) σ ∧ P σ) ↔
      ∃ p : X.Map A, P (pointAssign p) := by
  constructor
  · rintro ⟨σ, ⟨t, ρ, rfl, hd⟩, hP⟩
    exact ⟨Lax480241.Expansions.ExpExpansion.pt t ρ hd, hP⟩
  · rintro ⟨p, hP⟩
    exact ⟨pointAssign p, isPointAssign_pointAssign p, hP⟩

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (exists_point_iff)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **A guarded block is a point, universally.** -/
theorem forall_point_iff (P : X.pointBlock.Assignment A → Prop) :
    (∀ σ : X.pointBlock.Assignment A, IsPointAssign (X := X) σ → P σ) ↔
      ∀ p : X.Map A, P (pointAssign p) := by
  constructor
  · intro h p
    exact h _ (isPointAssign_pointAssign p)
  · rintro h σ ⟨t, ρ, rfl, hd⟩
    exact h (Lax480241.Expansions.ExpExpansion.pt t ρ hd)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (forall_point_iff)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

/-! ### The peel steps

Peeling the outermost quantifier of the prefix: the guard of the leading round
moves out past the rounds that remain
(`DescriptiveComplexity.altBlockQuant_and_const`,
`DescriptiveComplexity.altBlockQuant_const_imp`), and what is left of it turns
the round into a point (`exists_point_iff`, `forall_point_iff`). -/

/-- **Peeling an existential quantifier.** -/
theorem altBlockQuant_peel_ex {k : ℕ}
    (R : X.pointBlock.Assignment A → (Fin k → X.pointBlock.Assignment A) → Prop) :
    altBlockQuant A X.pointBlock (k + 1)
        (fun ρs => IsPointAssign (X := X) (ρs 0) ∧ R (ρs 0) (Fin.tail ρs)) true ↔
      ∃ p : X.Map A, altBlockQuant A X.pointBlock k (R (pointAssign p)) false := by
  change (∃ ρ, altBlockQuant A X.pointBlock k
    (fun ρs => IsPointAssign (X := X) ρ ∧ R ρ ρs) false) ↔ _
  refine Iff.trans (exists_congr fun ρ => altBlockQuant_and_const _ k (R ρ) false) ?_
  exact exists_point_iff fun σ => altBlockQuant A X.pointBlock k (R σ) false

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (altBlockQuant_peel_ex)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **Peeling a universal quantifier.** -/
theorem altBlockQuant_peel_all {k : ℕ}
    (R : X.pointBlock.Assignment A → (Fin k → X.pointBlock.Assignment A) → Prop) :
    altBlockQuant A X.pointBlock (k + 1)
        (fun ρs => IsPointAssign (X := X) (ρs 0) → R (ρs 0) (Fin.tail ρs)) false ↔
      ∀ p : X.Map A, altBlockQuant A X.pointBlock k (R (pointAssign p)) true := by
  change (∀ ρ, altBlockQuant A X.pointBlock k
    (fun ρs => IsPointAssign (X := X) ρ → R ρ ρs) true) ↔ _
  refine Iff.trans (forall_congr' fun ρ => altBlockQuant_const_imp _ k (R ρ) true) ?_
  exact forall_point_iff fun σ => altBlockQuant A X.pointBlock k (R σ) true

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (altBlockQuant_peel_all)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {m : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


