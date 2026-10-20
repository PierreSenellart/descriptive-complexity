/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.SharpP
import Lax366625Proofs.DescriptiveComplexity.SecondOrderMerge
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax366625Proofs.DescriptiveComplexity.SOBlock
end Lax366625Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

/-!
# The sum of two witness counts, as one witness count

Two kernels over two blocks are combined into one kernel over one block with
a **selector**, a relation variable of arity zero (`DescriptiveComplexity.boolBlock`):
when the selector holds, the first kernel must hold of the first block and the
second block must be empty; otherwise the second kernel must hold of the
second block and the first block must be empty
(`DescriptiveComplexity.pairKernel`). The witnesses of the pair kernel are,
bijectively, the witnesses of one kernel or the other
(`DescriptiveComplexity.pairWitnessEquiv`), so

* its witness count is the sum of the two (`DescriptiveComplexity.witnessCount_pairKernel`),
* and the selector reads the two summands back
  (`DescriptiveComplexity.card_pairWitness_sel`,
  `DescriptiveComplexity.card_pairWitness_not_sel`).

The first is what adding a constant to a witness count takes – the second
kernel being `⊤` over the block without variables, with exactly one witness
(`DescriptiveComplexity.witnessCount_trivial_top`) – and so what the closure
under complement of `⊕P` and `PP` rests on. The second is what the
completeness of a problem comparing two counts rests on: a single formula,
whose models are told apart by the value of the selector's variable.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The selector block and the lifting of kernels -/

/-- The block with one relation variable of arity zero: a Boolean. -/
@[reducible]
def boolBlock : Lax904597.SecondOrder.SOBlock where
  ι := Unit
  arity := fun _ => 0

/-- The Boolean an assignment of the selector block holds. -/
def boolSel {A : Type} (ζ : boolBlock.Assignment A) : Prop :=
  ζ () finZeroElim

theorem boolSel_iff {A : Type} (ζ : boolBlock.Assignment A) (x : Fin 0 → A) :
    boolSel ζ ↔ ζ () x :=
  iff_of_eq (congrArg (ζ ()) (Subsingleton.elim _ _))

/-- Assignments of a merged block are pairs of assignments. -/
def SOBlock.consAssignEquiv (B M : Lax904597.SecondOrder.SOBlock) (A : Type) :
    (SOBlock.cons B M).Assignment A ≃ B.Assignment A × M.Assignment A where
  toFun ρ := (fun i => ρ (Sum.inl i), fun j => ρ (Sum.inr j))
  invFun p := consAssign p.1 p.2
  left_inv ρ := consAssign_split ρ
  right_inv _ := rfl

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax366625Proofs.DescriptiveComplexity.SOBlock (consAssignEquiv)

end Lax904597.SecondOrder.SOBlock

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- “Every relation variable of the block is empty.” -/
noncomputable def emptyBlockS (B : Lax904597.SecondOrder.SOBlock) : (L.sum B.lang).Sentence :=
  Formula.iInf fun i : B.ι => Formula.iAlls (Fin (B.arity i))
    (∼(Relations.formula (Sum.inr ⟨i, rfl⟩ : (L.sum B.lang).Relations (B.arity i))
      fun j => Term.var (Sum.inr j)))

section Realize

variable {A : Type} [L.Structure A]

theorem realize_emptyBlockS (B : Lax904597.SecondOrder.SOBlock) (ρ : B.Assignment A) :
    (@Sentence.Realize _ A (@sumStructure L _ A _ (B.structure ρ)) (emptyBlockS B)) ↔
      ∀ (i : B.ι) (x : Fin (B.arity i) → A), ¬ρ i x := by
  let := B.structure ρ
  rw [emptyBlockS, Sentence.Realize]
  simp only [Formula.realize_iInf, Formula.realize_iAlls, Formula.realize_not]
  refine forall_congr' fun i => forall_congr' fun x => not_congr (iff_of_eq ?_)
  change ρ i (fun j => x (Fin.cast rfl j)) = ρ i x
  rfl

end Realize

/-! ### The pair kernel -/

section Witnesses

end Witnesses

end Lax366625Proofs.DescriptiveComplexity


