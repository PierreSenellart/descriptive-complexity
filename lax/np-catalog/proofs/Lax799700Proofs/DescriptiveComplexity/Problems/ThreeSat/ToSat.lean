/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeSat.Defs
import Lax799700Proofs.DescriptiveComplexity.OccurrenceFormulas
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

/-!
# 3SAT FO-reduces to SAT

This file constructs a first-order reduction from 3SAT to SAT,
`Lax799700Proofs.DescriptiveComplexity.threeSat_fo_reduction_sat : ThreeSAT ≤ᶠᵒ SAT`, over the identity
of vocabularies. The point of the reduction is the width bound: a 3SAT
instance is a SAT instance *plus* the promise that every clause has at most
three literals, and the promise is checked by a closed first-order sentence.

The interpretation (`Lax799700Proofs.DescriptiveComplexity.ThreeSatToSat.threeSatToSat`) is
identity-like – one tag, dimension one – with all relation formulas gated on
the sentence `Lax799700Proofs.DescriptiveComplexity.ThreeSatToSat.wideS` (“some clause has at least four
distinct literal occurrences”):

* if the input is not wide, the output is a copy of the input, so the output
  is satisfiable iff the input is (and the width promise holds);
* if the input is wide, every element of the output becomes an empty clause,
  so the output is unsatisfiable, matching the violated promise.

The order is not needed: this is an order-free FO reduction (though not a
quantifier-free one, since `wideS` quantifies over clauses and occurrences).
-/

namespace Lax799700Proofs.DescriptiveComplexity

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

variable {α : Type}

/-- Some clause has at least four distinct literal occurrences, as a formula
over the ordered expansion: `wideS` read there. -/
noncomputable def wideOrdF : SatOcc.satOrd.Formula α :=
  (Formula.iSup fun s : Fin 4 → Bool =>
      (Formula.iInf fun i : Fin 4 => SatOcc.occF (s i) (Sum.inr 0) (Sum.inr i.succ)) ⊓
      Formula.iInf fun p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2 ∧ s p.1 = s p.2} =>
        ∼(SatOcc.eqF (Sum.inr (p.1.1.succ : Fin 5)) (Sum.inr p.1.2.succ))).iExs (Fin 5)

@[simp]
theorem realize_wideOrdF {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]
    {v : α → A} : (wideOrdF (α := α)).Realize v ↔ Wide A := by
  simp only [wideOrdF, Formula.realize_iExs, Formula.realize_iSup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_not, SatOcc.realize_occF, SatOcc.realize_eqF,
    Sum.elim_inr]
  constructor
  · rintro ⟨e, s, hocc, hdist⟩
    exact ⟨e 0, fun i => e i.succ, s, hocc, fun i j hij hs => hdist ⟨(i, j), hij, hs⟩⟩
  · rintro ⟨c, x, s, hocc, hdist⟩
    refine ⟨Fin.cases c x, s, fun i => ?_, fun p => ?_⟩
    · simpa using hocc i
    · simpa using hdist p.1.1 p.1.2 p.2.1 p.2.2

end Ordered

end Semantics

/-! ### The interpretation -/

/-- The identity-like interpretation of SAT instances in 3SAT instances,
gated on the width check: a faithful copy if no clause is wide, an
unsatisfiable structure made of empty clauses otherwise. -/
noncomputable def threeSatToSat : Lax904597.Interpretations.FOInterpretation Lax904597.Sat.sat Lax904597.Sat.sat Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun _ => clF (0, 0) ⊔ wideS.relabel Empty.elim
    | _, .posIn => fun _ => posF (0, 0) (1, 0) ⊓ ∼(wideS.relabel Empty.elim)
    | _, .negIn => fun _ => negF (0, 0) (1, 0) ⊓ ∼(wideS.relabel Empty.elim)

section Characterizations

variable {A : Type} [Lax904597.Sat.sat.Structure A]

@[simp]
theorem isClause_iff (w : Fin 1 → A) :
    RelMap (M := threeSatToSat.Map A) Lax904597.Sat.satIsClause ![((), w)] ↔ Lax799700.Common.SatOcc.IsCl (w 0) ∨ Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [threeSatToSat]

@[simp]
theorem posIn_iff (wc wx : Fin 1 → A) :
    RelMap (M := threeSatToSat.Map A) Lax904597.Sat.satPosIn ![((), wc), ((), wx)] ↔
      Lax799700.Common.SatOcc.PosIn (wc 0) (wx 0) ∧ ¬Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [threeSatToSat]

@[simp]
theorem negIn_iff (wc wx : Fin 1 → A) :
    RelMap (M := threeSatToSat.Map A) Lax904597.Sat.satNegIn ![((), wc), ((), wx)] ↔
      Lax799700.Common.SatOcc.NegIn (wc 0) (wx 0) ∧ ¬Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [threeSatToSat]

end Characterizations

/-! ### Correctness -/

/-- Correctness of the reduction: a CNF structure is a yes-instance of 3SAT
iff the interpreted CNF structure is satisfiable. -/
theorem threeSatisfiable_iff_satisfiable (A : Type) [Lax904597.Sat.sat.Structure A] :
    Lax799700.ThreeSat.ThreeSatisfiable A ↔ Lax904597.Sat.Satisfiable (threeSatToSat.Map A) := by
  by_cases hw : Wide A
  · -- wide input: both sides fail
    refine iff_of_false
      (fun h => (wide_iff_not_widthAtMostThree A).mp hw h.1) ?_
    rintro ⟨ν, hν⟩
    have hw' := hw
    obtain ⟨c, -, -, -, -⟩ := hw'
    obtain ⟨⟨⟨⟩, wx⟩, hx⟩ := hν ((), fun _ => c) ((isClause_iff _).mpr (Or.inr hw))
    rcases hx with ⟨hpos, -⟩ | ⟨hneg, -⟩
    · exact ((posIn_iff _ _).mp hpos).2 hw
    · exact ((negIn_iff _ _).mp hneg).2 hw
  · -- non-wide input: faithful copy
    have hwidth : Lax799700.ThreeSat.WidthAtMostThree A := by
      by_contra h
      exact hw ((wide_iff_not_widthAtMostThree A).mpr h)
    rw [Lax799700.ThreeSat.ThreeSatisfiable, and_iff_right hwidth]
    constructor
    · rintro ⟨ν, hν⟩
      refine ⟨fun p => ν (p.2 0), ?_⟩
      rintro ⟨⟨⟩, w⟩ hcl
      rcases (isClause_iff w).mp hcl with hcl' | hcl'
      · obtain ⟨z, hz⟩ := hν (w 0) hcl'
        rcases hz with ⟨hp, hT⟩ | ⟨hn, hT⟩
        · exact ⟨((), fun _ => z), Or.inl ⟨(posIn_iff _ _).mpr ⟨hp, hw⟩, hT⟩⟩
        · exact ⟨((), fun _ => z), Or.inr ⟨(negIn_iff _ _).mpr ⟨hn, hw⟩, hT⟩⟩
      · exact absurd hcl' hw
    · rintro ⟨ν, hν⟩
      refine ⟨fun a => ν ((), fun _ => a), ?_⟩
      intro c hc
      obtain ⟨⟨⟨⟩, wz⟩, hz⟩ := hν ((), fun _ => c) ((isClause_iff _).mpr (Or.inl hc))
      -- transport along `(fun _ => wz 0) = wz`, at raw product type
      have hsub : ∀ (g : Unit × (Fin 1 → A) → Prop) (w : Fin 1 → A),
          g ((), w) ↔ g ((), fun _ => w 0) := fun g w => by
        have hw : (fun _ => w 0) = w := funext fun i => congrArg w (Subsingleton.elim 0 i)
        rw [hw]
      rcases hz with ⟨hp, hT⟩ | ⟨hn, hT⟩
      · exact ⟨wz 0, Or.inl ⟨((posIn_iff _ _).mp hp).1, (hsub ν wz).mp hT⟩⟩
      · exact ⟨wz 0, Or.inr ⟨((negIn_iff _ _).mp hn).1, fun h => hT ((hsub ν wz).mpr h)⟩⟩

end ThreeSatToSat

open ThreeSatToSat in
/-- **3SAT FO-reduces to SAT.** The identity-like interpretation
`ThreeSatToSat.threeSatToSat`, gated on the first-order width check, maps a
CNF structure to a satisfiable CNF instance iff it is a yes-instance of
3SAT. -/
noncomputable def threeSat_fo_reduction_sat : ThreeSAT ≤ᶠᵒ Lax904597.Sat.SAT where
  Tag := Unit
  dim := 1
  toInterpretation := threeSatToSat
  correct A _ _ _ := threeSatisfiable_iff_satisfiable A

end Lax799700Proofs.DescriptiveComplexity


