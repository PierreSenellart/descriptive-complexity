/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegFile
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

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMLe WPoint wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# A register file on a stretch of consecutive addresses

The register file the input channel marks (`DescriptiveComplexity.wmSegFile`) is
free, but it is a geometric ruler: the cell of the `j`-th element sits at address
`2 ^ m − 2 ^ (m − j − 1)`, so the file lies entirely in the **top half** of the
tape and reaching its upper registers costs almost the whole tape. A machine with
no clock does not care. A machine whose clock counts the addresses can walk that
file once and never again.

This file builds the other one:

> **the registers are `n` consecutive addresses**, the register of the `j`-th
> element being the address of rank `base + j`.

Everything a walk asks for follows at once, since
`DescriptiveComplexity.RegFile` asks only for strict monotonicity: ranks are
monotone, so the cells are (`DescriptiveComplexity.segFile`). What indexes the
registers plays no part in that, so the construction is made at an arbitrary
ordered index (`DescriptiveComplexity.ixSegFile`) and the elementwise file is
its diagonal – which is what a program too tightly clocked to afford one
register per element will build its own file with. What the geometry
buys is the *cost*: consecutive registers are consecutive addresses
(`DescriptiveComplexity.segFile_gap`), so a move of the walk is one step and a
pass over the whole file costs `n`, against the whole tape for the ruler.

**Where the stretch sits is the caller's choice, and it is not a free one.** The
subroutines written for the input channel's file assume it lies *above* the
addresses the program computes with, since that is where the ruler is
(`DescriptiveComplexity.Problems.Wide.Marks`): a scan looking for a register
scans upwards, and the bound it is given is a register. A program that builds its
own file and wants those subroutines unchanged puts it above its data as well; one
that wants it out of the way takes `base = 1`, `DescriptiveComplexity.lowFile`,
whose registers are the first `n` nonempty addresses and which therefore lies
below everything (`DescriptiveComplexity.wideRank_lowCell_le`).

There is nothing to arrange for the addresses to exist: the cell of an element
uses no marked symbol, so a program with this file **writes** its own names into
those cells – one per cell, as it walks the bottom of the tape in its first `n`
steps – and the two ends are recognized like any other register. The one fact
that has to be proved is that there is room, and there is, with room to spare:
there are `2 ^ n` addresses for `n` elements
(`DescriptiveComplexity.card_wideAddr`, the clock of the model read as a count).
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section LowFile

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [Finite A]

/-! ### Comparing addresses by rank -/

/-- **An address is below another exactly when its rank is smaller.** The rank
determines the address, so a family of addresses is strictly monotone as soon as
its ranks are. -/
theorem wideRank_lt_iff (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) (s t : A → Prop) :
    wideRank s < wideRank t ↔ WMSetLt Lax822549.WideMachines.WMLe s t := by
  have hlin := isLinOrd_wmSetLe h
  constructor
  · intro hlt
    rcases hlin.2.2.2 s t with hst | hts
    · exact (wmSetLt_iff s t).mpr ⟨hst, fun hc => absurd (hc ▸ hlt) (Nat.lt_irrefl _)⟩
    · exact absurd (wideRank_mono h hts) (by omega)
  · intro hlt
    exact bitRank_lt (isLinOrd_wpLe h) (p := (Sum.inl s : Lax822549.WideMachines.WPoint A)) trivial
      ((wmSetLt_iff s t).mp hlt).1
      fun hc => ((wmSetLt_iff s t).mp hlt).2 (Sum.inl_injective hc)

/-! ### There is room at the bottom -/

/-! ### The addresses from the bottom, one by one -/

/-! ### The file, and where it sits

Which stretch of the tape the registers occupy is the **caller's** choice, and it
is not a free one. The file the input channel marks lies *above* every address a
program computes with (`DescriptiveComplexity.Problems.Wide.Marks`), and the
subroutines written for it are stated that way – a scan looking for a register
scans upwards, and the bound it is given is a register. A program that builds its
own file and wants those subroutines unchanged must therefore put it **above its
data** as well, which here means high in its working region; one that wants the
file out of the way puts it at the bottom. Both are the same construction at a
different base. -/

/-! ### The file, at an arbitrary index -/

section IxSeg

end IxSeg

/-! ### The file at the bottom

The base-`1` case: the registers are the first `n` nonempty addresses, so the
machine builds the file in its first `n` steps and everything above it is free. -/

/-! ### Which addresses the registers are

A program does not merely need its file to exist: the phase that **builds** it
walks the bottom of the tape writing one name per cell, so it needs to know that
the cells it passes are exactly the registers, and which element each belongs
to. Both are read off the ranks. -/

/-- **An address is determined by its rank**, ranks being a strictly monotone map
of a linear order. -/
theorem wideRank_injective (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) :
    Function.Injective (wideRank (A := A)) := by
  intro s t he
  rcases eq_or_ne s t with rfl | hne
  · rfl
  · rcases (isLinOrd_wmSetLe h).2.2.2 s t with hle | hle
    · exact absurd ((wideRank_lt_iff h s t).mpr ((wmSetLt_iff s t).mpr ⟨hle, hne⟩))
        (by omega)
    · refine absurd ((wideRank_lt_iff h t s).mpr ((wmSetLt_iff t s).mpr
        ⟨hle, fun hc => hne hc.symm⟩)) (by omega)

/-! ### What a file's stretch costs

A sweep of the stretch costs the difference of the two ranks, and these are what
that difference is: the stretch is exactly as long as the file has registers,
and the last register sits one short of its end. Every budget of the opening
phases is one of these two numbers. -/

end LowFile

end Lax822549Proofs.DescriptiveComplexity


