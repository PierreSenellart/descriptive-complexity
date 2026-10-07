/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.PointGuard
import Lax480241Proofs.DescriptiveComplexity.SecondOrderReplicate
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

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (replicate replicateAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Placing an expansion's sentences into a quantifier prefix

The translation lemma quantifies `m` points of the expanded universe, one per
quantifier of the sentence being translated. Its kernel then has to *talk about*
those points – and everything it can say about them is already written, in
`DescriptiveComplexity.ExpExpansion.relSentence`,
`DescriptiveComplexity.ExpExpansion.ordSentence` and
`DescriptiveComplexity.SOBlock.eqAssignF`. All three are sentences over the
ordered base expanded by `DescriptiveComplexity.SOBlock.replicate n` – `n`
copies of the expansion's block, one per argument.

What this file supplies is the **renaming** that reads such a sentence inside
the quantifier prefix: copy `j` of `X.B` is to be read as the `X.B`-part of
round `sel j`.

The prefix itself is *not* built here and needs nothing new.
`DescriptiveComplexity.SecondOrderReplicate` already collapses `m` copies of one
block into a single merged block (`DescriptiveComplexity.repMerged`), names each
round's variables (`DescriptiveComplexity.repSym`) and identifies the
alternating quantification over the merged assignment with one assignment per
round (`DescriptiveComplexity.sorealize_repBlocks`). So the kernel is a sentence
over *one* merged block, and the renaming below is a
`DescriptiveComplexity.SOBlock.homLHom` between two blocks – no bespoke
`m`-block expansion is needed anywhere.

The one fact with content is
`DescriptiveComplexity.ExpExpansion.homAssign_roundIx`: transporting a merged
assignment back along the renaming gives the replicated assignment of the
selected rounds, with their tag bits dropped. It is `relMap_repSym` read as a
statement about assignments rather than about `RelMap`.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-- The block one quantified point of the expanded universe is guessed in: the
expansion's block, extended by its tag bits. -/
abbrev pointBlock : Lax904597.SecondOrder.SOBlock := X.B.withTag X.Tag

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pointBlock)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

/-! ### The renaming -/

/-- Copy `j` of the expansion's block, read as the `X.B`-part of round
`sel j`. -/
def roundIx (X : Lax480241.Expansions.ExpExpansion L) : (X.B.replicate n).ι → (repMerged X.pointBlock m).ι :=
  fun p => (repSym X.pointBlock (Sum.inr p.2)
    (rfl : X.pointBlock.arity (Sum.inr p.2) = X.B.arity p.2) m (sel p.1)).1

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundIx)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

theorem roundIx_arity (X : Lax480241.Expansions.ExpExpansion L) :
    ∀ p, (repMerged X.pointBlock m).arity (roundIx sel X p) = (X.B.replicate n).arity p :=
  fun p => (repSym X.pointBlock (Sum.inr p.2)
    (rfl : X.pointBlock.arity (Sum.inr p.2) = X.B.arity p.2) m (sel p.1)).2

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundIx_arity)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

/-- The vocabulary map reading a sentence over `n` copies of the expansion's
block inside the quantifier prefix, copy `j` at round `sel j`. -/
def roundLHom (X : Lax480241.Expansions.ExpExpansion L) :
    ((L.sum Language.order).sum (X.B.replicate n).lang) →ᴸ
      ((L.sum Language.order).sum (repMerged X.pointBlock m).lang) :=
  LHom.sumMap (LHom.id (L.sum Language.order))
    (SOBlock.homLHom (roundIx sel X) (roundIx_arity sel X))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundLHom)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

/-! ### Correctness -/

variable {A : Type} [L.Structure A] [LinearOrder A]

omit [L.Structure A] [LinearOrder A] in
/-- **Transporting the prefix's assignment back along the renaming** gives the
`n` selected rounds, with their tag bits dropped. This is
`DescriptiveComplexity.relMap_repSym` read as a statement about assignments. -/
theorem homAssign_roundIx (X : Lax480241.Expansions.ExpExpansion L)
    (ρs : Fin m → X.pointBlock.Assignment A) :
    SOBlock.homAssign (roundIx sel X) (roundIx_arity sel X)
        (repBlockAssign X.pointBlock A m ρs) =
      X.B.replicateAssign fun j => SOBlock.dropTag (ρs (sel j)) := by
  funext p y
  obtain ⟨j, x⟩ := p
  exact propext (relMap_repSym X.pointBlock (Sum.inr x)
    (rfl : X.pointBlock.arity (Sum.inr x) = X.B.arity x) m ρs (sel j) y)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (homAssign_roundIx)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **The renaming is correct**: a sentence over `n` copies of the expansion's
block, read inside the prefix, says of the selected rounds what it said of the
copies. -/
theorem realize_roundLHom (X : Lax480241.Expansions.ExpExpansion L) (ρs : Fin m → X.pointBlock.Assignment A)
    (φ : ((L.sum Language.order).sum (X.B.replicate n).lang).Sentence) :
    (@Sentence.Realize _ A
        ((repMerged X.pointBlock m).structure₁ (L := L.sum Language.order)
          (repBlockAssign X.pointBlock A m ρs))
        ((roundLHom sel X).onSentence φ) ↔
      @Sentence.Realize _ A
        ((X.B.replicate n).structure₁ (L := L.sum Language.order)
          (X.B.replicateAssign fun j => SOBlock.dropTag (ρs (sel j)))) φ) := by
  have h := SOBlock.realize_homSentence (L := L.sum Language.order)
    (roundIx sel X) (roundIx_arity sel X) (repBlockAssign X.pointBlock A m ρs) φ
  rwa [homAssign_roundIx sel X ρs] at h

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_roundLHom)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-! ### Reading one whole round

The selection above places a sentence about `n` *arguments* of the expansion's
block. A sentence about a whole guessed point – its tag bits included, so
`DescriptiveComplexity.SOBlock.tagBitF` and
`DescriptiveComplexity.ExpExpansion.pointGuardF` – needs the same renaming at
`X.pointBlock` rather than at `X.B`. It is the same construction with `sel`
replaced by a single round. -/

variable (i : Fin m)

/-- Round `i`'s block, as an index map into the prefix. -/
def roundOneIx (X : Lax480241.Expansions.ExpExpansion L) : X.pointBlock.ι → (repMerged X.pointBlock m).ι :=
  fun x => (repSym X.pointBlock x rfl m i).1

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundOneIx)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

variable {A : Type} [L.Structure A] [LinearOrder A]

variable (i : Fin m)

theorem roundOneIx_arity (X : Lax480241.Expansions.ExpExpansion L) :
    ∀ x, (repMerged X.pointBlock m).arity (roundOneIx i X x) = X.pointBlock.arity x :=
  fun x => (repSym X.pointBlock x rfl m i).2

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundOneIx_arity)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

variable {A : Type} [L.Structure A] [LinearOrder A]

variable (i : Fin m)

/-- The vocabulary map reading a sentence about one guessed point at round
`i`. -/
def roundOneLHom (X : Lax480241.Expansions.ExpExpansion L) :
    ((L.sum Language.order).sum X.pointBlock.lang) →ᴸ
      ((L.sum Language.order).sum (repMerged X.pointBlock m).lang) :=
  LHom.sumMap (LHom.id (L.sum Language.order))
    (SOBlock.homLHom (roundOneIx i X) (roundOneIx_arity i X))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (roundOneLHom)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

variable {A : Type} [L.Structure A] [LinearOrder A]

variable (i : Fin m)

omit [L.Structure A] [LinearOrder A] in
theorem homAssign_roundOneIx (X : Lax480241.Expansions.ExpExpansion L)
    (ρs : Fin m → X.pointBlock.Assignment A) :
    SOBlock.homAssign (roundOneIx i X) (roundOneIx_arity i X)
        (repBlockAssign X.pointBlock A m ρs) = ρs i := by
  funext x y
  exact propext (relMap_repSym X.pointBlock x rfl m ρs i y)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (homAssign_roundOneIx)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

variable {A : Type} [L.Structure A] [LinearOrder A]

variable (i : Fin m)

/-- **Reading one round is reading its own assignment.** -/
theorem realize_roundOneLHom (X : Lax480241.Expansions.ExpExpansion L) (ρs : Fin m → X.pointBlock.Assignment A)
    (φ : ((L.sum Language.order).sum X.pointBlock.lang).Sentence) :
    (@Sentence.Realize _ A
        ((repMerged X.pointBlock m).structure₁ (L := L.sum Language.order)
          (repBlockAssign X.pointBlock A m ρs))
        ((roundOneLHom i X).onSentence φ) ↔
      @Sentence.Realize _ A
        (X.pointBlock.structure₁ (L := L.sum Language.order) (ρs i)) φ) := by
  have h := SOBlock.realize_homSentence (L := L.sum Language.order)
    (roundOneIx i X) (roundOneIx_arity i X) (repBlockAssign X.pointBlock A m ρs) φ
  rwa [homAssign_roundOneIx i X ρs] at h

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_roundOneLHom)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {m n : ℕ} (sel : Fin n → Fin m)

variable {A : Type} [L.Structure A] [LinearOrder A]

variable (i : Fin m)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


