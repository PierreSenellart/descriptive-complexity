/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.QsatProgram
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

namespace Lax134656.Qsat
end Lax134656.Qsat

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (MinPos)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.Qsat (IsQVar QPrec QsatWf)
end Lax480241Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax134656.Qsat (qsat)
end FirstOrder.Language

/-!
# The geometry of the QBF machine's tape

Where the cells sit: which tagged tuples are positions, which is the lowest and
which the highest, and what the immediate neighbor of each one is. Everything
the run needs to know about *movement*, proved once, before any transition is
taken.

The content is that the tape

```
  ⊢   v₁ v₂ … vₙ   ⊣
```

is exactly the position order `DescriptiveComplexity.QsatTM.QLe`: the left marker
is `DescriptiveComplexity.MinPos`, the right marker is `DescriptiveComplexity.MaxPos`,
and `DescriptiveComplexity.SuccPos` steps from the left marker to the outermost
variable, from a variable to the next one the prefix binds, and from the
innermost variable to the right marker. The degenerate instance – no quantified
variable at all – is the case where the two markers are neighbors.

All of it needs the instance to be well formed, since that is exactly when the
prefix order is a linear order on the variables and `QLe` is a linear order at
all (`DescriptiveComplexity.QsatTM.isLinOrd_qLe`).
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QsatTM

/-! ### The three position tags, compared -/

private theorem tag_lt_sc : qTagIdx QTag.pStart < qTagIdx QTag.pCell := by decide

private theorem tag_lt_se : qTagIdx QTag.pStart < qTagIdx QTag.pEnd := by decide

private theorem tag_lt_ce : qTagIdx QTag.pCell < qTagIdx QTag.pEnd := by decide

private theorem tag_nlt_cs : ¬qTagIdx QTag.pCell < qTagIdx QTag.pStart := by decide

private theorem tag_nlt_ec : ¬qTagIdx QTag.pEnd < qTagIdx QTag.pCell := by decide

private theorem tag_nlt_es : ¬qTagIdx QTag.pEnd < qTagIdx QTag.pStart := by decide

private theorem tag_ne_cs : QTag.pCell ≠ QTag.pStart := by decide

private theorem tag_ne_ec : QTag.pEnd ≠ QTag.pCell := by decide

private theorem tag_ne_es : QTag.pEnd ≠ QTag.pStart := by decide

noncomputable section Geometry

variable {A : Type} [Lax134656.Qsat.qsat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### Walking the quantifier prefix -/

/-! ### The positions -/

omit [Lax134656.Qsat.qsat.Structure A] in
/-- A tuple pinned at both coordinates is the tuple of least elements. -/
theorem eq_qBot_tup {w : Fin 2 → A} (h : IsMinTup w) : w = fun _ => qBot :=
  isMinTup_unique h isMinTup_qBot

theorem qPosn_posStart : QPosn (posStart : QV A) := isMinTup_qBot

theorem qPosn_posEnd : QPosn (posEnd : QV A) := isMinTup_qBot

theorem qPosn_posCell {x : A} (hx : Lax134656.Qsat.IsQVar x) : QPosn (posCell x : QV A) :=
  ⟨hx, fun a => qBot_le a⟩

/-- **The positions of the tape, listed**: the two markers and one cell per
quantified variable. -/
theorem qPosn_iff (p : QV A) :
    QPosn p ↔ (p = posStart ∨ (∃ x : A, Lax134656.Qsat.IsQVar x ∧ p = posCell x) ∨ p = posEnd) := by
  constructor
  · intro h
    obtain ⟨t, w⟩ := p
    cases t <;> dsimp only [QPosn] at h
    case pStart => exact Or.inl (Prod.ext rfl (eq_qBot_tup h))
    case pCell =>
      refine Or.inr (Or.inl ⟨w 0, h.1, Prod.ext rfl (funext fun i => ?_)⟩)
      fin_cases i
      · rfl
      · exact le_antisymm (h.2 _) (qBot_le _)
    case pEnd => exact Or.inr (Or.inr (Prod.ext rfl (eq_qBot_tup h)))
  · rintro (rfl | ⟨x, hx, rfl⟩ | rfl)
    · exact qPosn_posStart
    · exact qPosn_posCell hx
    · exact qPosn_posEnd

/-! ### Comparing positions -/

/-- Between two cells the tape order is the prefix order. -/
theorem qLe_posCell_iff (hwf : Lax134656.Qsat.QsatWf A) {x y : A} :
    QLe (posCell x : QV A) (posCell y) ↔ PLe x y := by
  have hrefl := (isLinOrd_pLe A hwf).1
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact absurd h (Nat.lt_irrefl _)
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · have hxy : x = y := h
        exact hxy ▸ hrefl x
  · intro h
    refine Or.inr ⟨rfl, ?_⟩
    rcases eq_or_ne x y with rfl | hne
    · exact Or.inr ⟨rfl, hrefl _⟩
    · exact Or.inl ⟨h, hne⟩

omit [Finite A] [Nonempty A] in
/-- A tag strictly lower in the index order is lower on the tape. -/
theorem qLe_of_tagIdx_lt {p q : QV A} (h : qTagIdx p.1 < qTagIdx q.1) : QLe p q := Or.inl h

omit [Finite A] [Nonempty A] in
/-- The tape order is reflexive on a well-formed instance. -/
theorem qLe_refl (hwf : Lax134656.Qsat.QsatWf A) (p : QV A) : QLe p p := (isLinOrd_qLe A hwf).1 p

theorem qLe_start_cell (x : A) : QLe (posStart : QV A) (posCell x) :=
  qLe_of_tagIdx_lt tag_lt_sc

theorem qLe_start_end : QLe (posStart : QV A) posEnd := qLe_of_tagIdx_lt tag_lt_se

theorem qLe_cell_end (x : A) : QLe (posCell x : QV A) posEnd :=
  qLe_of_tagIdx_lt tag_lt_ce

theorem not_qLe_cell_start (x : A) : ¬QLe (posCell x : QV A) posStart := by
  rintro (h | ⟨h, -⟩)
  · exact tag_nlt_cs h
  · exact tag_ne_cs h

theorem not_qLe_end_cell (x : A) : ¬QLe (posEnd : QV A) (posCell x) := by
  rintro (h | ⟨h, -⟩)
  · exact tag_nlt_ec h
  · exact tag_ne_ec h

theorem not_qLe_end_start : ¬QLe (posEnd : QV A) posStart := by
  rintro (h | ⟨h, -⟩)
  · exact tag_nlt_es h
  · exact tag_ne_es h

/-! ### The ends of the tape -/

/-- **The left marker is the lowest position.** -/
theorem minPos_posStart (hwf : Lax134656.Qsat.QsatWf A) : Lax904597.Machines.MinPos (QLe (A := A)) QPosn posStart := by
  refine ⟨qPosn_posStart, fun q hq => ?_⟩
  rcases (qPosn_iff q).mp hq with rfl | ⟨x, -, rfl⟩ | rfl
  · exact qLe_refl hwf _
  · exact qLe_start_cell x
  · exact qLe_start_end

/-- **The right marker is the highest position.** -/
theorem maxPos_posEnd (hwf : Lax134656.Qsat.QsatWf A) : MaxPos (QLe (A := A)) QPosn posEnd := by
  refine ⟨qPosn_posEnd, fun q hq => ?_⟩
  rcases (qPosn_iff q).mp hq with rfl | ⟨x, -, rfl⟩ | rfl
  · exact qLe_start_end
  · exact qLe_cell_end x
  · exact qLe_refl hwf _

/-! ### Neighbors -/

end Geometry

end QsatTM

end Lax480241Proofs.DescriptiveComplexity


