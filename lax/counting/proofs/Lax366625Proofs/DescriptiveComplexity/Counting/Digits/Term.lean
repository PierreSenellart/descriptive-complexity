/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.ProdSweep
import Lax366625Proofs.DescriptiveComplexity.Counting.Quantitative
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

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (QTerm)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax366625Proofs.DescriptiveComplexity

/-!
# The digits of a quantitative term

`DescriptiveComplexity.Digits.dig_term`: the binary digits of the value of a
term of quantitative first-order logic, read over the structure expanded by the
limit of an induction `e₀`, can be added to any tower above `e₀`. By induction
on the term, each construct being one closure property:

* a formula, counting `1` or `0`: one first-order stratum, the formula being
  read in the tower through the embedding of `e₀`;
* a constant: iterated addition of ones;
* `+` and `·`: `DescriptiveComplexity.Digits.Dig.add`,
  `DescriptiveComplexity.Digits.Dig.mul`;
* `Σx̄` and `Πx̄`: `DescriptiveComplexity.Digits.Dig.sum`,
  `DescriptiveComplexity.Digits.Dig.prod`, the bound variables becoming
  parameters.

The digits are those of the value modulo `2 ^ (n ^ ℓ)`, for any `ℓ`; no bound
on the value is needed here.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Digits

variable {K : Language.{0, 0}} (e₀ : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order))

/-- The value of a term, as a family of numbers: its free variables are read
off the parameters through `f`. -/
noncomputable def termFam {α : Type} (t : Lax366625.QuantitativeLogic.QTerm ((K.sum Language.order).sum e₀.B.lang) α)
    {a : ℕ} (f : α → Fin a) : Fam K a :=
  fun A _ _ w => @Lax366625.QuantitativeLogic.QTerm.eval _ A (ctxStr e₀ A) α t fun y => w (f y)

variable {e₀}

/-- The family constantly equal to a number. -/
theorem Dig.const {ℓ a : ℕ} (s : ℕ) : Dig e₀ ℓ (fun _ _ _ _ => s : Fam K a) := by
  induction s with
  | zero => exact Dig.zero a
  | succ s ih => exact Dig.add ih (Dig.one a)

/-- **The digits of the value of a term can be added to any tower.** -/
theorem dig_term (ℓ : ℕ) {α : Type} (t : Lax366625.QuantitativeLogic.QTerm ((K.sum Language.order).sum e₀.B.lang) α) :
    ∀ {a : ℕ} (f : α → Fin a), Dig e₀ ℓ (termFam e₀ t f) := by
  induction t with
  | ind φ =>
    intro a f e x
    refine exists_ext_of_num e
      (Formula.relabel (fun y => Sum.inl (f y))
          ((LHom.sumMap (LHom.id (K.sum Language.order))
            (SOBlock.homLHom x.emb x.arity_emb)).onFormula φ) ⊓
        LHom.sumInl.onFormula (minTupF Sum.inr)) _ (fun A _ _ _ _ w p => ?_)
    have hφ := SOBlock.realize_homFormula (L := K.sum Language.order) x.emb x.arity_emb
      (e.inflLimit A) φ (fun y => w (f y))
    rw [x.limit A] at hφ
    let := e.B.structure (e.inflLimit A)
    classical
    refine Formula.realize_inf.trans (Iff.trans (and_congr (Formula.realize_relabel.trans hφ)
      ((LHom.realize_onFormula
        (LHom.sumInl : K.sum Language.order →ᴸ (K.sum Language.order).sum e.B.lang) _).trans
        ((realize_minTupF (L := K) (v := Sum.elim w p) Sum.inr).trans
          ((tup_isBot_iff (t := p)).symm.trans (tupBits_one p).symm)))) ?_)
    exact (bitsOf_ite _ 1 (toLex p)).symm
  | const s =>
    intro a f
    exact Dig.const s
  | add s t hs ht =>
    intro a f
    exact Dig.add (hs f) (ht f)
  | mul s t hs ht =>
    intro a f
    exact Dig.mul (hs f) (ht f)
  | sum n t ht =>
    intro a f
    refine Dig.congr (fun A _ _ w => ?_)
      (Dig.sum (m := n) (ht (Sum.elim (fun y => Fin.castAdd n (f y)) (Fin.natAdd a))))
    refine finsum_congr fun u => ?_
    refine congrArg (@Lax366625.QuantitativeLogic.QTerm.eval _ A (ctxStr e₀ A) _ t) (funext fun y => ?_)
    rcases y with y | y <;> simp
  | prod n t ht =>
    intro a f
    refine Dig.congr (fun A _ _ w => ?_)
      (Dig.prod (m := n) (Dig.one a)
        (ht (Sum.elim (fun y => Fin.castAdd n (f y)) (Fin.natAdd a))))
    rw [one_mul]
    refine finprod_congr fun u => ?_
    refine congrArg (@Lax366625.QuantitativeLogic.QTerm.eval _ A (ctxStr e₀ A) _ t) (funext fun y => ?_)
    rcases y with y | y <;> simp

end Digits

end Lax366625Proofs.DescriptiveComplexity


