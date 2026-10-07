/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.TilingExp
import Lax822549Proofs.DescriptiveComplexity.Problems.Tiling.CorridorMem
import Lax822549Proofs.DescriptiveComplexity.Exponential.Classes
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549.WideTilings
end Lax822549.WideTilings

namespace Lax904597.Problems
end Lax904597.Problems

namespace FirstOrder.Language
export Lax822549.WideTilings (wtile)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WPoint)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideTilings (wideTileData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The wide corridor: a strip as wide as the addresses

`DescriptiveComplexity.CORRIDOR` with one exponent added in the semantics of the
problem, exactly as `DescriptiveComplexity.WideTiling` adds one to
`DescriptiveComplexity.TILING`: the columns are the **subsets** of the instance,
while the tiles stay an ordinary part of it, and the rows are numbers.

So an instance of size `n` asks whether a corridor of width `2ⁿ` can be tiled
upward until an accepting tile appears – the classical second complete problem
of EXPSPACE beside a machine. The tile system it reads off an instance is the
same `DescriptiveComplexity.wideTileData` as the square's, so the two problems
differ only in the question asked, and the membership is again a composition:
the corridor of the exponential expansion, `CORRIDOR` being in PSPACE.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Problem

/-- **The two halves transport**, in either direction. -/
theorem wideCorridor_map {A B : Type} [Lax822549.WideTilings.wtile.Structure A] [Lax822549.WideTilings.wtile.Structure B]
    (e : A ≃[Lax822549.WideTilings.wtile] B)
    (h : (Lax822549.WideTilings.wideTileData A).WellFormed ∧ (Lax822549.WideTilings.wideTileData A).CorridorTileable) :
    (Lax822549.WideTilings.wideTileData B).WellFormed ∧ (Lax822549.WideTilings.wideTileData B).CorridorTileable :=
  ⟨TileData.wellFormed_map _ (wtPointEquiv e) _ (wtPosn_map e) (wtLe_point_map e) h.1,
    TileData.corridorTileable_map _ (wtPointEquiv e) _ (wtPosn_map e) (wtLe_point_map e)
      (wtTile_point_map e) (wtAcc_point_map e) (wtHoriz_point_map e)
      (wtVert_point_map e) (wtFirst_point_map e) (wtBase_point_map e)
      (wtStart_point_map e) (wtEdgeL_point_map e) (wtEdgeR_point_map e) h.2⟩

/-- **Tiling a wide corridor.** Can the strip whose width is the *subsets* of
the instance be tiled upward, from the bottom row the description allows until
an accepting tile appears? -/
def WideCorridor : Lax904597.Problems.DecisionProblem Lax822549.WideTilings.wtile where
  Holds := fun A _ => (Lax822549.WideTilings.wideTileData A).WellFormed ∧ (Lax822549.WideTilings.wideTileData A).CorridorTileable
  iso_invariant := fun {_ _} _ _ e => ⟨wideCorridor_map e, wideCorridor_map e.symm⟩

end Problem

/-! ### The membership -/

section Membership

open WideTile

/-- **A wide corridor is an ordinary corridor of the expansion.** The tile
system is the one `DescriptiveComplexity.WideTile.wtileAgree` matches field by
field; only the question differs. -/
theorem wideCorridor_iff_expansion (A : Type) [Lax822549.WideTilings.wtile.Structure A] [LinearOrder A] :
    letI := wtileStructure A
    (WideCorridor A ↔ CORRIDOR (wtileExp.Map A)) := by
  let := wtileStructure A
  obtain ⟨hposn, hle, htile, hacc, hhoriz, hvert, hfirst, hbase, hstart, hel, her⟩ :=
    wtileAgree (A := A)
  constructor
  · exact fun h => ⟨TileData.wellFormed_map _ wtileEquiv _ hposn hle h.1,
      TileData.corridorTileable_map _ wtileEquiv _ hposn hle htile hacc hhoriz hvert hfirst
        hbase hstart hel her h.2⟩
  · -- and back, along the inverse bijection
    have hback : ∀ {P : Lax822549.WideMachines.WPoint A → Prop} {Q : wtileExp.Map A → Prop},
        (∀ p, P p ↔ Q (wtileEquiv p)) → ∀ p, Q p ↔ P (wtileEquiv.symm p) := by
      intro P Q h p
      have h' := h (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h'
      exact h'.symm
    have hback₂ : ∀ {P : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A → Prop} {Q : wtileExp.Map A → wtileExp.Map A → Prop},
        (∀ p q, P p q ↔ Q (wtileEquiv p) (wtileEquiv q)) →
        ∀ p q, Q p q ↔ P (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro P Q h p q
      have h' := h (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
      exact h'.symm
    exact fun h => ⟨TileData.wellFormed_map _ wtileEquiv.symm _ (hback hposn) (hback₂ hle) h.1,
      TileData.corridorTileable_map _ wtileEquiv.symm _ (hback hposn) (hback₂ hle)
        (hback htile) (hback hacc) (hback₂ hhoriz) (hback₂ hvert) (hback₂ hfirst)
        (hback hbase) (hback hstart) (hback hel) (hback her) h.2⟩

/-- **The wide corridor is in EXPSPACE**, which is `PSPACE.exp`: the expansion
turns it into `DescriptiveComplexity.CORRIDOR`, and that problem is in PSPACE.
This is the second natural member the class has, beside the wide machine. -/
theorem wideCorridor_mem_EXPSPACE : WideCorridor ∈ EXPSPACE := by
  let hinst : ∀ (A : Type) [Lax822549.WideTilings.wtile.Structure A] [LinearOrder A],
      Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Structure (wtileExp.Map A) := fun A => wtileStructure A
  rw [EXPSPACE_eq_PSPACE_exp]
  refine ⟨wtileExp, CORRIDOR, corridor_mem_PSPACE, ?_⟩
  intro A _ _ _ _
  exact wideCorridor_iff_expansion A

end Membership

end Lax822549Proofs.DescriptiveComplexity


