/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.SecondOrderBlockHom
import Lax822549Proofs.DescriptiveComplexity.SecondOrderTransitiveClosurePull
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

namespace Lax822549Proofs.DescriptiveComplexity.SOBlock
end Lax822549Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (replicate replicateAssign)
end Lax904597.SecondOrder.SOBlock

/-!
# Independent copies of a second-order block

An exponential expansion (`DescriptiveComplexity.ExpExpansion`) defines an
`n`-ary relation on its universe – the assignments of a block `B` – by a
first-order sentence that must read `n` assignments at once. The vocabulary it
is written over is therefore `n` independent copies of `B.lang`, packaged here
as a single block `DescriptiveComplexity.SOBlock.replicate`:

* its relation variables are pairs `(k, i)` of a copy index and a variable of
  `B`, with the arity of `i`;
* `DescriptiveComplexity.SOBlock.replicateAssign` assembles one assignment per
  copy into an assignment of the replicated block – exactly, since the
  index type is a plain product;
* `DescriptiveComplexity.SOBlock.replicateSym` names the symbol of copy `k`,
  read back by `DescriptiveComplexity.SOBlock.relMap_replicateSym`.

This is a *product* presentation of a quantifier prefix, as opposed to the
iterated-merge presentation of `DescriptiveComplexity.repMerged`
(`DescriptiveComplexity.SecondOrderReplicate`), which is built by recursion on
`k` and whose index type is a nest of sums. The product presentation is what
this development needs, for one reason: replication **commutes with the
pullback of a block through an interpretation** definitionally
(`DescriptiveComplexity.SOBlock.homAssign_replicatePullHom`), because both
sides re-associate the same `Σ`-type over a product. Pulling an expansion back
through an interpretation is exactly that re-association, so the commutation is
the lemma `DescriptiveComplexity.Exponential.Pull` rests on, and is proved by
`rfl`.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

/-! ### The replicated block -/

@[simp]
theorem replicate_arity (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) (p : Fin n × B.ι) :
    (B.replicate n).arity p = B.arity p.2 :=
  rfl

end SOBlock

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (replicate_arity)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

/-- The relation symbol of the `k`-th copy corresponding to a symbol of the
block's own vocabulary. -/
def replicateSym (B : Lax904597.SecondOrder.SOBlock) {n m : ℕ} (k : Fin n) (r : B.lang.Relations m) :
    (B.replicate n).lang.Relations m :=
  ⟨(k, r.1), r.2⟩

end SOBlock

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (replicateSym)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

/-! ### Replication commutes with the pullback through an interpretation

`DescriptiveComplexity.SOBlock.pull` turns an `a`-ary variable on the
interpreted universe `Tag × A^d` into one `(a · d)`-ary variable on `A` per
tuple of tags. Applied to the replicated block it produces variables indexed by
`Σ (k, i), Fin (B.arity i) → Tag`; replicating the pulled block produces
variables indexed by `Fin n × Σ i, Fin (B.arity i) → Tag`. These are the same
data re-associated, with equal arities, so the induced block morphism is an
arity-preserving bijection and the transported assignments agree by `rfl`. -/

variable (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T] (d n : ℕ)

/-- The re-association of indices identifying the pullback of a replicated
block with the replication of the pulled block. -/
def replicatePullHom : ((B.replicate n).pull T d).ι → ((B.pull T d).replicate n).ι :=
  fun p => (p.1.1, ⟨p.1.2, p.2⟩)

end SOBlock

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (replicatePullHom)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T] (d n : ℕ)

theorem replicatePullHom_arity :
    ∀ i, ((B.pull T d).replicate n).arity (B.replicatePullHom T d n i) =
      ((B.replicate n).pull T d).arity i :=
  fun _ => rfl

end SOBlock

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (replicatePullHom_arity)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T] (d n : ℕ)

/-- The vocabulary morphism reading a sentence over the pullback of the
replicated block inside the replication of the pulled block. -/
def replicatePullLHom : ((B.replicate n).pull T d).lang →ᴸ ((B.pull T d).replicate n).lang :=
  homLHom (B.replicatePullHom T d n) (B.replicatePullHom_arity T d n)

end SOBlock

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (replicatePullLHom)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T] (d n : ℕ)

end SOBlock

end Lax822549Proofs.DescriptiveComplexity


