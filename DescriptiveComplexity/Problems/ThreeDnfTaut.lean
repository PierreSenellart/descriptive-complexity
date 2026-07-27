/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Taut
import DescriptiveComplexity.Problems.ThreeSat.ToSat
import DescriptiveComplexity.Problems.ThreeSat.FromSat

/-!
# 3-DNF-TAUT is coNP-complete

3-DNF-TAUT is the width-three restriction of TAUT: a
`FirstOrder.Language.sat`-structure, read *disjunctively*, is a yes-instance
(`DescriptiveComplexity.ThreeDnfTautology`) when every term has at most three literal
occurrences – the very same promise `DescriptiveComplexity.WidthAtMostThree` as 3SAT –
*and* every truth assignment satisfies all the literals of some term.

## Why the width-three variant is not free

Plain TAUT is coNP-complete by *complementing* the Cook–Levin discharge
(`DescriptiveComplexity.taut_hard_of_piSODefinable`): the sign swap
`DescriptiveComplexity.swapSignInterp` turns `SATᶜ` into TAUT. The same sign swap turns
`3SATᶜ` into "not a width-three tautology", which is *not* 3-DNF-TAUT: 3SAT
folds its width bound into the yes-instances
(`ThreeSatisfiable = WidthAtMostThree ∧ Satisfiable`), so `3SATᶜ` is the
*disjunction* `¬WidthAtMostThree ∨ ¬Satisfiable` and the sign swap does not
transfer. What the discharge needs is the promise that the reduction feeding
it only ever outputs width-three instances – an invariant of the *image*,
which the `≤ᶠᵒ` interface of a reduction hides.

The invariant is available where it is proved, so this file routes the
discharge through the problem that carries it, namely width-three
unsatisfiability (`DescriptiveComplexity.ThreeUnsatisfiable`, bundled as
`DescriptiveComplexity.ThreeUNSAT`), the CNF-side reading of the same yes-instances:

* `DescriptiveComplexity.sat_compl_ordered_fo_reduction_threeUnsat`: 3SAT's
  clause-splitting interpretation `DescriptiveComplexity.SatToThreeSat.satToThreeSat`,
  applied unchanged, reduces `SATᶜ` to 3-UNSAT – its correctness is
  `DescriptiveComplexity.SatToThreeSat.satisfiable_iff_map` negated, *conjoined with the
  width promise* `DescriptiveComplexity.SatToThreeSat.widthAtMostThree_map`, which is
  exactly the invariant the naive route loses;
* `DescriptiveComplexity.threeUnsat_fo_reduction_threeDnfTaut`: the sign swap then
  carries 3-UNSAT to 3-DNF-TAUT, by De Morgan
  (`DescriptiveComplexity.tautology_map_iff_not_satisfiable`) on the satisfiability
  half and by `DescriptiveComplexity.widthAtMostThree_swapSign` on the promise – the
  swap is a bijection on *signed* occurrences, so the width bound is
  insensitive to it.

Membership is the gated sign swap
`DescriptiveComplexity.ThreeDnfTautToSat.gatedSwap`: TAUT's swap with every relation
formula conjoined with the first-order width check of
`DescriptiveComplexity.ThreeSatToSat.wideS`, so that a wide input is mapped to a
structure with no clauses at all – trivially satisfiable, matching the
violated promise – and a narrow one to its plain sign swap.

Both problems are coNP-complete (`DescriptiveComplexity.ThreeDnfTAUT_coNP_complete`,
`DescriptiveComplexity.ThreeUNSAT_coNP_complete`), with no second-order argument of
their own.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

/-! ### The two problems -/

section Problems

variable (A : Type) [Language.sat.Structure A]

/-- A `Language.sat`-structure, read as a formula in disjunctive normal form,
is a yes-instance of 3-DNF-TAUT if every term has at most three literal
occurrences and every truth assignment satisfies all the literals of some
term. -/
def ThreeDnfTautology : Prop :=
  WidthAtMostThree A ∧ Tautology A

/-- A `Language.sat`-structure, read as a formula in conjunctive normal form,
is a yes-instance of 3-UNSAT if every clause has at most three literal
occurrences and no truth assignment satisfies the formula. This is the
CNF-side reading of `DescriptiveComplexity.ThreeDnfTautology`; it is *not* the
complement of 3SAT, which also holds of wide instances. -/
def ThreeUnsatisfiable : Prop :=
  WidthAtMostThree A ∧ ¬Satisfiable A

end Problems

section Iso

variable {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]

/-- Being a width-three tautology is isomorphism-invariant. -/
theorem threeDnfTautology_iso (e : A ≃[Language.sat] B) :
    ThreeDnfTautology A ↔ ThreeDnfTautology B :=
  and_congr (widthAtMostThree_iso e) (tautology_iso e)

/-- Width-three unsatisfiability is isomorphism-invariant. -/
theorem threeUnsatisfiable_iso (e : A ≃[Language.sat] B) :
    ThreeUnsatisfiable A ↔ ThreeUnsatisfiable B :=
  and_congr (widthAtMostThree_iso e) (not_congr (satisfiable_iso e))

end Iso

/-- 3-DNF-TAUT, as a problem on `Language.sat`-structures read disjunctively:
TAUT with 3SAT's width bound folded into the yes-instances. -/
def ThreeDnfTAUT : DecisionProblem Language.sat where
  Holds := fun A inst => @ThreeDnfTautology A inst
  iso_invariant := fun e => threeDnfTautology_iso e

/-- 3-UNSAT, as a problem on `Language.sat`-structures: unsatisfiability with
3SAT's width bound folded into the yes-instances. -/
def ThreeUNSAT : DecisionProblem Language.sat where
  Holds := fun A inst => @ThreeUnsatisfiable A inst
  iso_invariant := fun e => threeUnsatisfiable_iso e

/-! ### The width bound survives the sign swap -/

section SwapWidth

variable {A : Type} [Language.sat.Structure A]

/-- The occurrences of the sign swap are the occurrences of the input, with
the opposite sign. -/
theorem swapSign_occIn (p q : swapSignInterp.Map A) (s : Bool) :
    OccIn p q s ↔ OccIn (p.2 0) (q.2 0) (!s) := by
  obtain ⟨⟨⟩, wp⟩ := p
  obtain ⟨⟨⟩, wq⟩ := q
  cases s <;> simp [OccIn, IsCl, PosIn, NegIn]

/-- The width bound is insensitive to the sign swap: it counts *signed*
occurrences, and the swap is a bijection on them. -/
theorem widthAtMostThree_swapSign :
    WidthAtMostThree (swapSignInterp.Map A) ↔ WidthAtMostThree A := by
  constructor
  · intro h c x s hocc
    obtain ⟨i, j, hij, hx, hs⟩ :=
      h ((), fun _ => c) (fun i => ((), fun _ => x i)) (fun i => !(s i))
        fun i => (swapSign_occIn _ _ _).mpr (by simpa using hocc i)
    refine ⟨i, j, hij, ?_, Bool.not_inj hs⟩
    have := congrArg (fun p : swapSignInterp.Map A => p.2 0) hx
    simpa using this
  · intro h p x s hocc
    obtain ⟨i, j, hij, hx, hs⟩ :=
      h (p.2 0) (fun i => (x i).2 0) (fun i => !(s i))
        fun i => (swapSign_occIn _ _ _).mp (hocc i)
    refine ⟨i, j, hij, ?_, Bool.not_inj hs⟩
    exact Prod.ext_iff.mpr ⟨Subsingleton.elim _ _,
      funext fun k => by rw [Subsingleton.elim k 0]; exact hx⟩

end SwapWidth

/-! ### The two reductions

The width promise is established where the clause-splitting interpretation is
applied, and carried along the sign swap; no invariant has to be recovered
from a reduction after the fact. -/

section Reductions

open SatToThreeSat

/-- Correctness of the hardness reduction: an ordered CNF structure is
unsatisfiable iff its width-three split is a yes-instance of 3-UNSAT. The
width half is the promise `SatToThreeSat.widthAtMostThree_map`. -/
theorem not_satisfiable_iff_threeUnsatisfiable (A : Type) [Language.sat.Structure A]
    [LinearOrder A] [Finite A] :
    ¬Satisfiable A ↔ ThreeUnsatisfiable (satToThreeSat.Map A) := by
  rw [ThreeUnsatisfiable, and_iff_right widthAtMostThree_map]
  exact not_congr satisfiable_iff_map

/-- **The complement of SAT ordered-FO-reduces to 3-UNSAT.** 3SAT's
clause-splitting interpretation `SatToThreeSat.satToThreeSat`, applied
unchanged: it preserves satisfiability, and its output always meets the width
bound. -/
noncomputable def sat_compl_ordered_fo_reduction_threeUnsat : SATᶜ ≤ᶠᵒ[≤] ThreeUNSAT where
  Tag := SplitTag
  dim := 2
  toInterpretation := satToThreeSat
  correct A _ _ _ _ := not_satisfiable_iff_threeUnsatisfiable A

/-- Correctness of the sign swap between the two readings: a width-three CNF
structure is unsatisfiable iff its sign swap is a width-three DNF
tautology. -/
theorem threeUnsatisfiable_iff_threeDnfTautology_map (A : Type) [Language.sat.Structure A] :
    ThreeUnsatisfiable A ↔ ThreeDnfTautology (swapSignInterp.Map A) :=
  and_congr widthAtMostThree_swapSign.symm (tautology_map_iff_not_satisfiable A).symm

/-- **3-UNSAT FO-reduces to 3-DNF-TAUT**, by TAUT's sign swap
`swapSignInterp`: De Morgan on the satisfiability half, and the width bound is
insensitive to the swap. -/
def threeUnsat_fo_reduction_threeDnfTaut : ThreeUNSAT ≤ᶠᵒ ThreeDnfTAUT where
  Tag := Unit
  dim := 1
  toInterpretation := swapSignInterp
  correct A _ _ := threeUnsatisfiable_iff_threeDnfTautology_map A

end Reductions

/-! ### Membership: the gated sign swap -/

namespace ThreeDnfTautToSat

open ThreeSatToSat

/-- The sign-swapping interpretation of TAUT, gated on the width check: a
plain sign swap if no term is wide, a structure with no clauses at all
otherwise. Reading the output as a CNF formula, a wide input becomes
trivially satisfiable, which is what the complement of 3-DNF-TAUT
requires. -/
noncomputable def gatedSwap : FOInterpretation Language.sat Language.sat Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun _ => clF (0, 0) ⊓ ∼(wideS.relabel Empty.elim)
    | _, .posIn => fun _ => negF (0, 0) (1, 0) ⊓ ∼(wideS.relabel Empty.elim)
    | _, .negIn => fun _ => posF (0, 0) (1, 0) ⊓ ∼(wideS.relabel Empty.elim)

section Characterizations

variable {A : Type} [Language.sat.Structure A]

@[simp]
theorem isClause_iff (w : Fin 1 → A) :
    RelMap (M := gatedSwap.Map A) satIsClause ![((), w)] ↔ IsCl (w 0) ∧ ¬Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [gatedSwap]

@[simp]
theorem posIn_iff (wc wx : Fin 1 → A) :
    RelMap (M := gatedSwap.Map A) satPosIn ![((), wc), ((), wx)] ↔
      NegIn (wc 0) (wx 0) ∧ ¬Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [gatedSwap]

@[simp]
theorem negIn_iff (wc wx : Fin 1 → A) :
    RelMap (M := gatedSwap.Map A) satNegIn ![((), wc), ((), wx)] ↔
      PosIn (wc 0) (wx 0) ∧ ¬Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [gatedSwap]

end Characterizations

/-- Correctness of the membership reduction: a DNF structure fails to be a
width-three tautology exactly when its gated sign swap is satisfiable. A wide
input has no clause in its image, hence a satisfiable one; a narrow input is
sign-swapped faithfully, and De Morgan applies. -/
theorem not_threeDnfTautology_iff_satisfiable (A : Type) [Language.sat.Structure A] :
    ¬ThreeDnfTautology A ↔ Satisfiable (gatedSwap.Map A) := by
  by_cases hw : Wide A
  · -- wide input: the promise fails, and the image has no clause at all
    refine iff_of_true (fun h => (wide_iff_not_widthAtMostThree A).mp hw h.1)
      ⟨fun _ => True, ?_⟩
    rintro ⟨⟨⟩, w⟩ hcl
    exact absurd ((isClause_iff w).mp hcl).2 (not_not_intro hw)
  · -- narrow input: the plain sign swap, and De Morgan
    have hwidth : WidthAtMostThree A := by
      by_contra h
      exact hw ((wide_iff_not_widthAtMostThree A).mpr h)
    have hde : Tautology A ↔ ¬Satisfiable (gatedSwap.Map A) :=
      tautology_iff_not_satisfiable (gatedSwap.mapEquivSelf A).symm
        (fun c => ((isClause_iff (A := A) fun _ => c).trans (and_iff_left hw)).symm)
        (fun c x => ((negIn_iff (A := A) (fun _ => c) fun _ => x).trans (and_iff_left hw)).symm)
        fun c x => ((posIn_iff (A := A) (fun _ => c) fun _ => x).trans (and_iff_left hw)).symm
    have hred : ThreeDnfTautology A ↔ Tautology A := and_iff_right hwidth
    exact (not_congr (hred.trans hde)).trans not_not

end ThreeDnfTautToSat

open ThreeDnfTautToSat in
/-- **The complement of 3-DNF-TAUT FO-reduces to SAT.** The gated sign swap
`ThreeDnfTautToSat.gatedSwap` maps a DNF structure to a satisfiable CNF
instance iff it is not a width-three tautology. -/
noncomputable def threeDnfTaut_compl_fo_reduction_sat : ThreeDnfTAUTᶜ ≤ᶠᵒ SAT where
  Tag := Unit
  dim := 1
  toInterpretation := gatedSwap
  correct A _ _ := not_threeDnfTautology_iff_satisfiable A

/-! ### coNP-completeness -/

/-- **3-DNF-TAUT is in coNP**: its complement FO-reduces to SAT, hence is in
NP. -/
theorem threeDnfTaut_mem_coNP : ThreeDnfTAUT ∈ coNP :=
  (mem_piP_iff 1 ThreeDnfTAUT).mpr
    (NP.mem_of_foReduction threeDnfTaut_compl_fo_reduction_sat sat_mem_NP)

/-- **3-UNSAT is in coNP**: it FO-reduces to 3-DNF-TAUT, which is in coNP. -/
theorem threeUnsat_mem_coNP : ThreeUNSAT ∈ coNP :=
  coNP.mem_of_foReduction threeUnsat_fo_reduction_threeDnfTaut threeDnfTaut_mem_coNP

/-- **coNP-hardness of 3-UNSAT**, by complementing the Cook–Levin discharge
and splitting clauses: a `Π₁`-definable problem has a `Σ₁`-definable
complement, which reduces to SAT; complementing that reduction lands in
`SATᶜ`, which the clause-splitting interpretation carries to 3-UNSAT, width
promise included. -/
theorem threeUnsat_hard_of_piSODefinable :
    ∀ {L : Language.{0, 0}} (Q : DecisionProblem L),
      PiSODefinable 1 Q → Nonempty (Q ≤ᶠᵒ[≤] ThreeUNSAT) := by
  intro L Q hQ
  obtain ⟨g⟩ := sat_hard_of_sigmaSODefinable Qᶜ ((piSODefinable_iff_compl 1 Q).mp hQ)
  exact ⟨(g.compl.congrSource fun A _ _ => not_not).trans
    sat_compl_ordered_fo_reduction_threeUnsat⟩

/-- **coNP-hardness of 3-DNF-TAUT**: the hardness of 3-UNSAT, followed by the
sign swap. -/
theorem threeDnfTaut_hard_of_piSODefinable :
    ∀ {L : Language.{0, 0}} (Q : DecisionProblem L),
      PiSODefinable 1 Q → Nonempty (Q ≤ᶠᵒ[≤] ThreeDnfTAUT) := by
  intro L Q hQ
  exact (threeUnsat_hard_of_piSODefinable Q hQ).map fun f =>
    f.trans_fo threeUnsat_fo_reduction_threeDnfTaut

/-- **3-UNSAT is coNP-complete.** -/
theorem ThreeUNSAT_coNP_complete : coNP.Complete ThreeUNSAT :=
  ⟨threeUnsat_mem_coNP,
    (hard_piP_succ_iff 0 ThreeUNSAT).mpr fun Q hQ =>
      (threeUnsat_hard_of_piSODefinable Q hQ).map OrderedFOReduction.toRel⟩

/-- **3-DNF-TAUT is coNP-complete.** Membership is the gated sign swap; the
hardness discharge is the Cook–Levin theorem read through the complement,
routed through 3-UNSAT so that the width promise of the clause-splitting
reduction is available where it is needed. -/
theorem ThreeDnfTAUT_coNP_complete : coNP.Complete ThreeDnfTAUT :=
  ⟨threeDnfTaut_mem_coNP,
    (hard_piP_succ_iff 0 ThreeDnfTAUT).mpr fun Q hQ =>
      (threeDnfTaut_hard_of_piSODefinable Q hQ).map OrderedFOReduction.toRel⟩

/-- 3-DNF-TAUT is coNP-hard. -/
theorem threeDnfTaut_coNP_hard : coNP.Hard ThreeDnfTAUT :=
  ThreeDnfTAUT_coNP_complete.hard

/-- 3-UNSAT is coNP-hard. -/
theorem threeUnsat_coNP_hard : coNP.Hard ThreeUNSAT :=
  ThreeUNSAT_coNP_complete.hard

end DescriptiveComplexity
