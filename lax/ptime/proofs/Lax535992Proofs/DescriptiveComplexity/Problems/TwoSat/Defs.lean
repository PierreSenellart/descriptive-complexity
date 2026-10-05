/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax535992Proofs.DescriptiveComplexity.OccurrenceFormulas
import Lax535992Proofs.DescriptiveComplexity.Problems.Sat
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149.TwoSat
end Lax485149.TwoSat

namespace Lax485149.TwoSat.SatOcc
end Lax485149.TwoSat.SatOcc

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Sat (Satisfiable)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax485149.TwoSat (TwoSatisfiable WidthAtMostTwo)
end Lax535992Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax535992Proofs.DescriptiveComplexity.SatOcc
export Lax485149.TwoSat.SatOcc (OccIn)
end Lax535992Proofs.DescriptiveComplexity.SatOcc

/-!
# 2SAT: definition

The problem 2SAT, over the same vocabulary `FirstOrder.Language.sat` as SAT and
3SAT: a CNF structure is a yes-instance iff every clause has at most two
literal occurrences (`DescriptiveComplexity.WidthAtMostTwo`) *and* the CNF is
satisfiable (`DescriptiveComplexity.TwoSatisfiable`, bundled as
`DescriptiveComplexity.TwoSAT`).

As for 3SAT, folding the width bound into the yes-instances rather than into
the vocabulary is what keeps 2SAT a decision problem on arbitrary
`Language.sat`-structures, and the bound “at most two” is expressed without
counting: among any three literal occurrences of a clause, two coincide.

Two facts about the bound are needed by the Krom program of
`DescriptiveComplexity.Problems.TwoSat.Membership`, and both are here: the bound is
first-order expressible over the ordered expansion
(`DescriptiveComplexity.wideTwoOrdF`, its violation), and a clause of a width-two
structure has *two signed occurrences covering all of them*
(`DescriptiveComplexity.exists_covering_pair`), the shape a 2-clause can talk about.
-/

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

section TwoSat

variable (A : Type) [Lax904597.Sat.sat.Structure A]

/-- Some clause has at least three distinct literal occurrences: the negation
of the width bound (`DescriptiveComplexity.wideTwo_iff_not_widthAtMostTwo`). -/
def WideTwo : Prop :=
  ∃ (c : A) (x : Fin 3 → A) (s : Fin 3 → Bool),
    (∀ i, Lax485149.TwoSat.SatOcc.OccIn c (x i) (s i)) ∧ ∀ i j, i ≠ j → s i = s j → x i ≠ x j

end TwoSat

section Basic

variable {A : Type} [Lax904597.Sat.sat.Structure A]

theorem wideTwo_iff_not_widthAtMostTwo : WideTwo A ↔ ¬Lax485149.TwoSat.WidthAtMostTwo A := by
  constructor
  · rintro ⟨c, x, s, hocc, hdist⟩ h
    obtain ⟨i, j, hij, hx, hs⟩ := h c x s hocc
    exact hdist i j hij hs hx
  · intro h
    rw [Lax485149.TwoSat.WidthAtMostTwo] at h
    push Not at h
    obtain ⟨c, x, s, hocc, hdist⟩ := h
    exact ⟨c, x, s, hocc, fun i j hij hs hx => hdist i j hij hx hs⟩

/-- **Two occurrences cover a clause of a width-two structure**: if the clause
`c` has an occurrence at all, there are two signed occurrences of `c` such that
every occurrence of `c` is one of them. This is what lets a *single* 2-clause
speak for the whole clause. -/
theorem exists_covering_pair (h : Lax485149.TwoSat.WidthAtMostTwo A) {c x : A} {s : Bool}
    (hocc : Lax485149.TwoSat.SatOcc.OccIn c x s) :
    ∃ (y : A) (u : Bool), Lax485149.TwoSat.SatOcc.OccIn c y u ∧
      ∀ z t, Lax485149.TwoSat.SatOcc.OccIn c z t → (z = x ∧ t = s) ∨ (z = y ∧ t = u) := by
  classical
  by_cases hall : ∀ z t, Lax485149.TwoSat.SatOcc.OccIn c z t → z = x ∧ t = s
  · exact ⟨x, s, hocc, fun z t hz => Or.inl (hall z t hz)⟩
  · -- a second occurrence exists; with width two there is no third
    obtain ⟨y, hy⟩ := not_forall.mp hall
    obtain ⟨u, hu⟩ := not_forall.mp hy
    obtain ⟨hyocc, hyne⟩ := Classical.not_imp.mp hu
    refine ⟨y, u, hyocc, fun z t hz => ?_⟩
    by_contra hz'
    rw [not_or] at hz'
    obtain ⟨h1, h2⟩ := hz'
    -- the three occurrences `(x, s)`, `(y, u)`, `(z, t)` are pairwise distinct
    have hthree : ∀ i, Lax485149.TwoSat.SatOcc.OccIn c (![x, y, z] i) (![s, u, t] i) := by
      intro i
      fin_cases i
      · exact hocc
      · exact hyocc
      · exact hz
    obtain ⟨i, j, hij, heq, hseq⟩ := h c ![x, y, z] ![s, u, t] hthree
    fin_cases i <;> fin_cases j <;> simp_all

end Basic

section Iso

variable {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]

private theorem occIn_map (e : A ≃[Lax904597.Sat.sat] B) {c x : A} {s : Bool}
    (h : Lax485149.TwoSat.SatOcc.OccIn c x s) : Lax485149.TwoSat.SatOcc.OccIn (e c) (e x) s := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨(relMap_equiv₁ e Lax904597.Sat.satIsClause c).mp hc, ?_⟩
  cases s with
  | false => exact (relMap_equiv₂ e Lax904597.Sat.satNegIn c x).mp hs
  | true => exact (relMap_equiv₂ e Lax904597.Sat.satPosIn c x).mp hs

private theorem widthAtMostTwo_of_iso (e : A ≃[Lax904597.Sat.sat] B) (h : Lax485149.TwoSat.WidthAtMostTwo A) :
    Lax485149.TwoSat.WidthAtMostTwo B := by
  intro c x s hocc
  obtain ⟨i, j, hij, hx, hs⟩ :=
    h (e.symm c) (fun i => e.symm (x i)) s fun i => occIn_map e.symm (hocc i)
  refine ⟨i, j, hij, ?_, hs⟩
  have := congrArg e hx
  simpa using this

/-- The width-two bound is isomorphism-invariant. -/
theorem widthAtMostTwo_iso (e : A ≃[Lax904597.Sat.sat] B) :
    Lax485149.TwoSat.WidthAtMostTwo A ↔ Lax485149.TwoSat.WidthAtMostTwo B :=
  ⟨widthAtMostTwo_of_iso e, widthAtMostTwo_of_iso e.symm⟩

/-- 2-satisfiability is isomorphism-invariant. -/
theorem twoSatisfiable_iso (e : A ≃[Lax904597.Sat.sat] B) :
    Lax485149.TwoSat.TwoSatisfiable A ↔ Lax485149.TwoSat.TwoSatisfiable B :=
  and_congr (widthAtMostTwo_iso e) (satisfiable_iso e)

end Iso

/-- 2SAT, as a problem on `Language.sat`-structures: the same vocabulary as
SAT, with the width-two bound folded into the yes-instances. -/
def TwoSAT : Lax904597.Problems.DecisionProblem Lax904597.Sat.sat where
  Holds := fun A inst => @Lax485149.TwoSat.TwoSatisfiable A inst
  iso_invariant := fun e => twoSatisfiable_iso e

/-! ### The width bound as a formula

The Krom program defining 2SAT enforces the width bound by a *guard*: guards
are first-order over the input vocabulary, so the bound costs nothing beyond
one goal clause. The formula is the width-two analogue of
`DescriptiveComplexity.ThreeSatToSat.wideOrdF`. -/

section Formula

variable {α : Type}

/-- Some clause has at least three distinct literal occurrences, as a formula
over the ordered expansion: the clause is variable `0` and the three occurrence
variables are `1`, `2`, `3`; the disjunction ranges over the sign vectors, and
distinctness is only required between occurrences carrying the same sign. -/
noncomputable def wideTwoOrdF : satOrd.Formula α :=
  (Formula.iSup fun s : Fin 3 → Bool =>
      (Formula.iInf fun i : Fin 3 => occF (s i) (Sum.inr 0) (Sum.inr i.succ)) ⊓
      Formula.iInf fun p : {p : Fin 3 × Fin 3 // p.1 ≠ p.2 ∧ s p.1 = s p.2} =>
        ∼(eqF (Sum.inr (p.1.1.succ : Fin 4)) (Sum.inr p.1.2.succ))).iExs (Fin 4)

@[simp]
theorem realize_wideTwoOrdF {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]
    {v : α → A} : (wideTwoOrdF (α := α)).Realize v ↔ WideTwo A := by
  simp only [wideTwoOrdF, Formula.realize_iExs, Formula.realize_iSup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_not, realize_occF, realize_eqF, Sum.elim_inr]
  constructor
  · rintro ⟨e, s, hocc, hdist⟩
    exact ⟨e 0, fun i => e i.succ, s, hocc, fun i j hij hs => hdist ⟨(i, j), hij, hs⟩⟩
  · rintro ⟨c, x, s, hocc, hdist⟩
    refine ⟨Fin.cases c x, s, fun i => ?_, fun p => ?_⟩
    · simpa using hocc i
    · simpa using hdist p.1.1 p.1.2 p.2.1 p.2.2

end Formula

end Lax535992Proofs.DescriptiveComplexity


