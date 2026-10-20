/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawData
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawTripKits
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawIncrKit
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawSweepKit
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawAdvKit
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawSeekKit
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

/-!
# The call sites' kits, at the concrete slots

The kit instantiations of the EXPSPACE program: each call site of the program
is one of the kit shapes of the layer, at the slot
inventory of `DescriptiveComplexity.Problems.Wide.DrawSlots`. This file fixes
the slots and guards; the phase embeddings stay parameters (each call site
gets its own copy of the shape's phases in the program's phase sum), and so
does the control location a name guard compares against (the `Ctl` sizing is
fixed with the site enumeration, not here).

The register-file service slots are the same for every kit – `reg` the
register mark, `regLast` the file-top mark (the greatest element's cell *is*
the file's top), `wk` the working-cell marker – and the guards are exactly
the slot conditions the kits' separation lemmas were built around.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A Q P : Type}

/-! ### Slot distinctness

The facts every discharge asks about the service slots, provable once: the
walked registers, the register mark, the file-top mark and the marker are
pairwise distinct constructors. -/

theorem mir_ne_reg : (Slot.mir : dt.SlotIx) ≠ .reg := fun h => nomatch h

theorem tgt_ne_reg : (Slot.tgt : dt.SlotIx) ≠ .reg := fun h => nomatch h

theorem regLast_ne_mir : (Slot.regLast : dt.SlotIx) ≠ .mir := fun h => nomatch h

theorem regLast_ne_tgt : (Slot.regLast : dt.SlotIx) ≠ .tgt := fun h => nomatch h

theorem wk_ne_mir : (Slot.wk : dt.SlotIx) ≠ .mir := fun h => nomatch h

theorem wk_ne_tgt : (Slot.wk : dt.SlotIx) ≠ .tgt := fun h => nomatch h

theorem tgt_ne_mir : (Slot.tgt : dt.SlotIx) ≠ .mir := fun h => nomatch h

theorem ltp_ne_mir : (Slot.ltp : dt.SlotIx) ≠ .mir := fun h => nomatch h

theorem bot_ne_mir : (Slot.bot : dt.SlotIx) ≠ .mir := fun h => nomatch h

/-! ### The plain sweeps: COMPARE and COPY -/

/-- **COMPARE's kit**: one question per cell of the logical interval – every
stage track agrees with its next. -/
def compareKit (one : A) (emb : SweepPh → P) : FlagSweepKit A Q dt.SlotIx P where
  t := .mir
  ltp := .ltp
  TestG := fun g => ∀ i : dt.d.B.ι, (g (.old i) = one ↔ g (.new i) = one)
  emb := emb

/-- **COPY's kit**: every stage track takes its next's digit, the next stage
riding along for the following round. -/
def copyKit (ph : P) : WriteSweepKit A Q dt.SlotIx P where
  t := .mir
  ltp := .ltp
  wrG := fun g s => match s with
    | .old i => g (.new i)
    | s' => g s'
  ph := ph

/-! ### The register-file trips -/

/-- **The random access**: MIRROR sought to TARGET, marker in tow. -/
def seekKit (emb : SeekPh → P) : SeekKit A Q dt.SlotIx P where
  t := .mir
  tg := .tgt
  rg := .reg
  rl := .regLast
  wk := .wk
  emb := emb

/-- **One round of the outer sweep**: the working cell advances one address,
MIRROR incremented in tow. -/
def advKit (emb : AdvPh → P) : AdvKit A Q dt.SlotIx P :=
  ⟨.mir, .reg, .regLast, .wk, emb⟩

/-- Clearing the MIRROR register, at a random access's reset. -/
def clearMirKit (emb : TrackPh → P) : ClearKit A Q dt.SlotIx P :=
  ⟨.mir, .reg, .regLast, .wk, emb⟩

/-- **TARGET := the logical top**: the pattern write of startup – the digit
set exactly at the argument-tagged cells, read off the one-hot marks. -/
def tgtTopKit (one : A) (emb : TrackPh → P) : MapKit A Q dt.SlotIx P where
  t := .tgt
  rg := .reg
  rl := .regLast
  wk := .wk
  Fb := fun g => ∃ b : Fin dt.ko ⊕ Fin dt.ki, g (.blk (some b)) = one
  emb := emb

/-! ### The navigation-by-name trips -/

/-- **The name guard, at computed coordinates**: this cell is the canonically
padded cell of the element whose block is `b` and whose first `dd0`
coordinates are the ones the control *computes* through `cf`. The trips of
the coordinate loops read the control's slots directly
(`DescriptiveComplexity.Draw.Data.nameG`); the leaf reads of the element
loops compute an encoded tuple from them
(`DescriptiveComplexity.Problems.Wide.DrawName`), and both are this guard. -/
def nameGF (one : A) (b : Fin dt.ko ⊕ Fin dt.ki) (cf : (Q → A) → Fin dt.dd0 → A) :
    (Q → A) → (dt.SlotIx → A) → Prop :=
  fun fc g => g (.blk (some b)) = one ∧ g .pdd = one ∧
    ∀ j : Fin dt.dd0, g (.name j) = cf fc j

/-- **The name guard**: this cell is the canonically padded cell of the
element whose block is `b` and whose first `dd0` coordinates the control
holds at `coord`. -/
def nameG (one : A) (b : Fin dt.ko ⊕ Fin dt.ki) (coord : Fin dt.dd0 → Q) :
    (Q → A) → (dt.SlotIx → A) → Prop :=
  dt.nameGF one b fun fc j => fc (coord j)

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


