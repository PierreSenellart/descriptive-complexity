/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawRepAtoms
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawData
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawPad
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

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (replicate replicateAssign)
end Lax904597.SecondOrder.SOBlock

/-!
# What an expansion atom's element loop computes

An atom `r(p₁,…,p_k)` of a step matrix is a relation of the *expanded*
structure, so it holds exactly when the expansion's defining sentence
`X.relSentence r τ̄` – at the argument points' tags – holds of the base
structure with one copy of the block per argument, interpreted by the
points' assignments (`DescriptiveComplexity.ExpExpansion.relMap_map`). The
machine evaluates that sentence by an **element loop**: its prefix is
enumerated in the control's loop-variable slots, and per tuple its matrix is
a Boolean function of atoms which are either *guards* – equalities, base
relations, order on control-held elements, all evaluated by the transition
table – or *read leaves*, one bit of one argument point's assignment
(`DescriptiveComplexity.Problems.Wide.DrawRepAtoms`).

This file is the semantic anchor of that loop, the control-scale twin of
`DescriptiveComplexity.Problems.Wide.DrawLeaf`:
`DescriptiveComplexity.Draw.Data.relMap_iff_altQuantFrom_expLeaf` says the
expanded relation **is** the prefix of
`DescriptiveComplexity.Draw.Data.expLeaf` played from level `0`, and the
`_pad` variant says the same of the loop the machine actually runs, which
enumerates *every* loop-variable slot – the levels past the sentence's own
prefix being read by nobody
(`DescriptiveComplexity.Draw.altQuantFrom_pad`).
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} [L.IsRelational] (dt : Data L) {A : Type}

variable [L.Structure A] [LinearOrder A] [Nonempty A]

/-! ### The leaf of the loop -/

/-- **What one round of an expansion atom's element loop is worth**: the
Boolean value of the defining sentence's matrix at the control's tuple, its
replicated-block atoms read off the argument points' assignments – one named
bit each – and its base atoms decided by the guards. -/
noncomputable def expLeaf {k : ℕ} (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag)
    (ρs : Fin k → dt.X.B.Assignment A) (u : Fin (dt.relPk e τ).n → A) : Prop :=
  qfValue (dt.relPk e τ).mat fun a =>
    (blkAtom? a).elim False (BlkAtom.holds (dt.X.B.replicateAssign ρs) u)

/-! ### The join -/

/-- **The element loop computes the expanded relation.** An atom of the
expansion holds of a tuple of points exactly when the prefix of the leaf
predicate, played from level `0`, does – whatever the loop's slots held when
it began, since level `0` reads no valuation. -/
theorem relMap_iff_altQuantFrom_expLeaf {k : ℕ} (e : dt.X.E.Relations k)
    (p : Fin k → dt.X.Map A)
    (v : Fin (dt.relPk e fun ℓ => (p ℓ).1.1).n → A) :
    RelMap (M := dt.X.Map A) e p ↔
      altQuantFrom (dt.relPk e fun ℓ => (p ℓ).1.1).pol
        (dt.expLeaf e (fun ℓ => (p ℓ).1.1) fun ℓ => (p ℓ).1.2) 0 v := by
  let inst := (dt.X.B.replicate k).structure₁ (L := L.sum Language.order)
    (dt.X.B.replicateAssign fun ℓ => (p ℓ).1.2)
  have hspec := (dt.relPk e fun ℓ => (p ℓ).1.1).spec A v default fun i => i.elim0
  have hrel : (((dt.X.relSentence e fun ℓ => (p ℓ).1.1).relabel
        (Empty.elim : Empty → Fin 0)).Realize (default : Fin 0 → A)) ↔
      @Sentence.Realize _ A inst (dt.X.relSentence e fun ℓ => (p ℓ).1.1) := by
    rw [Formula.realize_relabel]
    exact Iff.rfl
  have hmat : (fun w : Fin (dt.relPk e fun ℓ => (p ℓ).1.1).n → A =>
        @BoundedFormula.Realize _ A inst _ _ (dt.relPk e fun ℓ => (p ℓ).1.1).mat default w) =
      dt.expLeaf e (fun ℓ => (p ℓ).1.1) fun ℓ => (p ℓ).1.2 :=
    funext fun w => propext
      (realize_iff_qfValue_blkHolds (dt.relPk e fun ℓ => (p ℓ).1.1).isQF _ w)
  rw [ExpExpansion.relMap_map, ← hrel, hspec, hmat]

/-- **The loop the machine runs**, over every loop-variable slot: the levels
past the sentence's own prefix are read by nobody, so playing them changes
nothing. -/
theorem relMap_iff_altQuantFrom_expLeaf_pad {k : ℕ} (e : dt.X.E.Relations k)
    (p : Fin k → dt.X.Map A) {N : ℕ}
    (hn : (dt.relPk e fun ℓ => (p ℓ).1.1).n ≤ N) (t : Fin N → A) :
    RelMap (M := dt.X.Map A) e p ↔
      altQuantFrom (dt.relPk e fun ℓ => (p ℓ).1.1).pol
        (fun w : Fin N → A =>
          dt.expLeaf e (fun ℓ => (p ℓ).1.1) (fun ℓ => (p ℓ).1.2)
            fun j => w (Fin.castLE hn j)) 0 t := by
  rw [altQuantFrom_pad (P := dt.expLeaf e (fun ℓ => (p ℓ).1.1) fun ℓ => (p ℓ).1.2)
    hn (Nat.zero_le _) t]
  exact dt.relMap_iff_altQuantFrom_expLeaf e p _

/-! ### The domain gate's sub-evaluation

The gate of a block value asks, after the shape checks, that the decoded
assignment satisfy its tag's **domain sentence** – a sentence over the base
vocabulary expanded by the block itself, not by a replicated one. The
classifier being stated at an arbitrary block, it is the same element loop
with one copy instead of `k`. -/

/-- **What one round of a domain gate's element loop is worth.** -/
noncomputable def domLeaf (t : dt.X.Tag) (ρ : dt.X.B.Assignment A)
    (u : Fin (dt.domPk t).n → A) : Prop :=
  qfValue (dt.domPk t).mat fun a => (blkAtom? a).elim False (BlkAtom.holds ρ u)

/-- **The domain gate's loop computes the domain condition**: a tagged
assignment is a point of the expanded universe exactly when the prefix of
its leaf predicate, played from level `0`, holds. -/
theorem domHolds_iff_altQuantFrom_domLeaf (t : dt.X.Tag)
    (ρ : dt.X.B.Assignment A) (v : Fin (dt.domPk t).n → A) :
    Lax480241.Expansions.ExpExpansion.DomHolds (X := dt.X) (t, ρ) ↔
      altQuantFrom (dt.domPk t).pol (dt.domLeaf t ρ) 0 v := by
  let inst := dt.X.B.structure₁ (L := L.sum Language.order) ρ
  have hspec := (dt.domPk t).spec A v default fun i => i.elim0
  have hrel : ((((dt.X.dom t).relabel (Empty.elim : Empty → Fin 0)).Realize
        (default : Fin 0 → A))) ↔ @Sentence.Realize _ A inst (dt.X.dom t) := by
    rw [Formula.realize_relabel]
    exact Iff.rfl
  have hmat : (fun w : Fin (dt.domPk t).n → A =>
        @BoundedFormula.Realize _ A inst _ _ (dt.domPk t).mat default w) =
      dt.domLeaf t ρ :=
    funext fun w => propext (realize_iff_qfValue_blkHolds (dt.domPk t).isQF _ w)
  rw [Lax480241.Expansions.ExpExpansion.DomHolds, ← hrel, hspec, hmat]

/-- The same over every loop-variable slot, which is what the machine's loop
enumerates. -/
theorem domHolds_iff_altQuantFrom_domLeaf_pad (t : dt.X.Tag)
    (ρ : dt.X.B.Assignment A) {N : ℕ} (hn : (dt.domPk t).n ≤ N) (u : Fin N → A) :
    Lax480241.Expansions.ExpExpansion.DomHolds (X := dt.X) (t, ρ) ↔
      altQuantFrom (dt.domPk t).pol
        (fun w : Fin N → A => dt.domLeaf t ρ fun j => w (Fin.castLE hn j)) 0 u := by
  rw [altQuantFrom_pad (P := dt.domLeaf t ρ) hn (Nat.zero_le _) u]
  exact dt.domHolds_iff_altQuantFrom_domLeaf t ρ _

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


