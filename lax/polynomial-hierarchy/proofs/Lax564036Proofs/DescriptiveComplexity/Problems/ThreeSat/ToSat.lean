/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Problems.ThreeSat.Defs
import Lax564036Proofs.DescriptiveComplexity.OccurrenceFormulas
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

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax799700.ThreeSat
end Lax799700.ThreeSat

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax799700.ThreeSat (ThreeSatisfiable WidthAtMostThree)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax564036Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl NegIn OccIn PosIn)
end Lax564036Proofs.DescriptiveComplexity.SatOcc

/-!
# 3SAT FO-reduces to SAT

This file constructs a first-order reduction from 3SAT to SAT,
`DescriptiveComplexity.threeSat_fo_reduction_sat : ThreeSAT ≤ᶠᵒ SAT`, over the identity
of vocabularies. The point of the reduction is the width bound: a 3SAT
instance is a SAT instance *plus* the promise that every clause has at most
three literals, and the promise is checked by a closed first-order sentence.

The interpretation (`DescriptiveComplexity.ThreeSatToSat.threeSatToSat`) is
identity-like – one tag, dimension one – with all relation formulas gated on
the sentence `DescriptiveComplexity.ThreeSatToSat.wideS` (“some clause has at least four
distinct literal occurrences”):

* if the input is not wide, the output is a copy of the input, so the output
  is satisfiable iff the input is (and the width promise holds);
* if the input is wide, every element of the output becomes an empty clause,
  so the output is unsatisfiable, matching the violated promise.

The order is not needed: this is an order-free FO reduction (though not a
quantifier-free one, since `wideS` quantifies over clauses and occurrences).
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

namespace ThreeSatToSat

open Language Structure SatOcc

/-! ### Order-free formulas over the vocabulary of CNF instances -/

section Builders

variable {α : Type}

/-- `c` is a clause, as a formula. -/
def clF (c : α) : Lax904597.Sat.sat.Formula α :=
  Relations.formula₁ Lax904597.Sat.satIsClause (Term.var c)

/-- `x` occurs positively in `c`, as a formula. -/
def posF (c x : α) : Lax904597.Sat.sat.Formula α :=
  Relations.formula₂ Lax904597.Sat.satPosIn (Term.var c) (Term.var x)

/-- `x` occurs negatively in `c`, as a formula. -/
def negF (c x : α) : Lax904597.Sat.sat.Formula α :=
  Relations.formula₂ Lax904597.Sat.satNegIn (Term.var c) (Term.var x)

/-- `x = y`, as a formula. -/
def eqF (x y : α) : Lax904597.Sat.sat.Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- The literal `(x, s)` occurs in the clause `c`, as a formula. -/
def occF (s : Bool) (c x : α) : Lax904597.Sat.sat.Formula α :=
  clF c ⊓ if s then posF c x else negF c x

end Builders

/-- Some clause has at least four distinct literal occurrences, as a sentence:
the clause is variable `0` and the four occurrence variables are `1`, …, `4`;
the disjunction ranges over the sign vectors, and distinctness is only
required between occurrences carrying the same sign. -/
noncomputable def wideS : Lax904597.Sat.sat.Sentence :=
  (Formula.iSup fun s : Fin 4 → Bool =>
      (Formula.iInf fun i : Fin 4 =>
        occF (s i) (Sum.inr 0) (Sum.inr i.succ)) ⊓
      Formula.iInf fun p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2 ∧ s p.1 = s p.2} =>
        ∼(eqF (Sum.inr (p.1.1.succ : Fin 5)) (Sum.inr p.1.2.succ))).iExs (Fin 5)

section Semantics

variable {A : Type} [Lax904597.Sat.sat.Structure A] {α : Type} {v : α → A}

@[simp]
theorem realize_clF {c : α} : (clF c).Realize v ↔ Lax799700.Common.SatOcc.IsCl (v c) := by
  rw [clF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_posF {c x : α} : (posF c x).Realize v ↔ Lax799700.Common.SatOcc.PosIn (v c) (v x) := by
  rw [posF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_negF {c x : α} : (negF c x).Realize v ↔ Lax799700.Common.SatOcc.NegIn (v c) (v x) := by
  rw [negF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]

@[simp]
theorem realize_occF {s : Bool} {c x : α} :
    (occF s c x).Realize v ↔ Lax799700.Common.SatOcc.OccIn (v c) (v x) s := by
  cases s <;> simp [occF, Lax799700.Common.SatOcc.OccIn]

variable (A)

/-- Some clause has at least four distinct literal occurrences. This is the
negation of the width bound of 3SAT (`wide_iff_not_widthAtMostThree`). -/
def Wide : Prop :=
  ∃ (c : A) (x : Fin 4 → A) (s : Fin 4 → Bool),
    (∀ i, Lax799700.Common.SatOcc.OccIn c (x i) (s i)) ∧ ∀ i j, i ≠ j → s i = s j → x i ≠ x j

theorem wide_iff_not_widthAtMostThree : Wide A ↔ ¬Lax799700.ThreeSat.WidthAtMostThree A := by
  constructor
  · rintro ⟨c, x, s, hocc, hdist⟩ h
    obtain ⟨i, j, hij, hx, hs⟩ := h c x s hocc
    exact hdist i j hij hs hx
  · intro h
    rw [Lax799700.ThreeSat.WidthAtMostThree] at h
    push Not at h
    obtain ⟨c, x, s, hocc, hdist⟩ := h
    exact ⟨c, x, s, hocc, fun i j hij hs hx => hdist i j hij hx hs⟩

/-- Realization of the formula `wideS` (under any assignment of its – absent –
free variables). -/
@[simp]
theorem realize_wideS {w : Empty → A} : Formula.Realize wideS w ↔ Wide A := by
  simp only [wideS, Formula.realize_iExs, Formula.realize_iSup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_not, realize_occF, realize_eqF, Sum.elim_inr]
  constructor
  · rintro ⟨e, s, hocc, hdist⟩
    exact ⟨e 0, fun i => e i.succ, s, hocc, fun i j hij hs => hdist ⟨(i, j), hij, hs⟩⟩
  · rintro ⟨c, x, s, hocc, hdist⟩
    refine ⟨Fin.cases c x, s, fun i => ?_, fun p => ?_⟩
    · simpa using hocc i
    · simpa using hdist p.1.1 p.1.2 p.2.1 p.2.2

/-! ### The same check over the ordered expansion

The reductions that build gadgets over `SatOcc.satOrd` (Max Cut, 1-in-SAT)
gate themselves on the width check too, and need it as a formula of the
ordered vocabulary. -/

section Ordered

end Ordered

end Semantics

/-! ### The interpretation -/

section Characterizations

end Characterizations

/-! ### Correctness -/

end ThreeSatToSat

end Lax564036Proofs.DescriptiveComplexity


