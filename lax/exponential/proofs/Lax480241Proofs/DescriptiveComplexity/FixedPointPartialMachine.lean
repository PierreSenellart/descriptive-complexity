/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.FixedPointStepRel
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.SpaceHard
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

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (Config MinPos SuccPos TMAcc TMDst TMLe TMPosn TMRead TMRight TMSrc TMStart TMTr TMWrite tmData)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (PFPDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign)
end Lax904597.SecondOrder.SOBlock

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing)
end FirstOrder.Language

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (PFPHolds partStage)
end Lax535992.InflationaryFixedPoint.StepDef

/-!
# PSPACE is contained in FO(≤, PFP)

The hard half of the capture theorem FO(≤, PFP) = PSPACE, by iterating the
PSPACE-complete deterministic machine problem: a partial fixed-point
definition `DescriptiveComplexity.SpaceTM.mPfp` whose block holds one machine
configuration – the block of the SO(TC) membership proof of
`DescriptiveComplexity.Problems.Machine.Space` – and whose step formulas
advance it:

* from the empty assignment (recognized by its empty state mark, which no
  configuration has), one step *loads the initial configuration* – start
  state, head on the lowest position, initial tape;
* from a configuration that can move – some applicable transition with a
  destination, a written symbol and a neighboring position to move to
  (`DescriptiveComplexity.SpaceTM.GoOn`) – and is not yet accepting, one step
  is **the** machine step, determinism making the step formulas functional;
* from an accepting or stuck configuration, the step *stutters*, so that a
  halting run is exactly a converging iteration.

A machine that loops forever diverges the iteration, and under the
convergence-requiring semantics of `DescriptiveComplexity.FixedPointPartial`
that alone makes the definition false – no divergence detection, no counter.
The output sentence checks well-formedness and determinism (conditions on the
instance only) and reads acceptance off the stable configuration
(`DescriptiveComplexity.dtmAcceptSpace_pfpDefinable`).

Whence the capture: every PSPACE problem reduces to the machine problem by a
*relativized* ordered reduction
(`DescriptiveComplexity.le_dtmAcceptSpace_of_mem_PSPACE`), and FO(≤, PFP)
definability crosses such reductions
(`DescriptiveComplexity.PFPDefinable.of_relOrderedReduction`), so
`DescriptiveComplexity.pfpDefinable_of_mem_PSPACE` and, with the converse
inclusion of `DescriptiveComplexity.FixedPointPartialSpace`, the capture
theorem `DescriptiveComplexity.pfpDefinable_iff_mem_PSPACE`.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

namespace SpaceTM

/-! ### Formula builders

In the parameterized style of `DescriptiveComplexity.Problems.Machine.Space`:
each builder takes the relation symbols it reads, so realization lemmas are
stated over `RelMap` and specialize to any expansion. -/

section Shapes

variable {L' : Language.{0, 0}} {M : Type} [L'.Structure M] {γ : Type}

/-- Some element carries both marks. -/
noncomputable def markMeetF (s r : L'.Relations 1) : L'.Formula γ :=
  (Relations.formula₁ s (Term.var (Sum.inr 0)) ⊓
    Relations.formula₁ r (Term.var (Sum.inr 0))).iExs (Fin 1)

/-- The binary relation holds of `x` and some element. -/
noncomputable def someArgF (r : L'.Relations 2) (x : γ) : L'.Formula γ :=
  (Relations.formula₂ r (Term.var (Sum.inl x)) (Term.var (Sum.inr 0))).iExs (Fin 1)

/-- `τ` is an applicable transition: a transition whose source is the
marked state and whose read symbol is the one held by the marked cell. -/
noncomputable def applF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (τ : γ) : L'.Formula γ :=
  Relations.formula₁ tr (Term.var τ) ⊓ (markArgF src s τ ⊓ cellArgF rd h t τ)

/-- The head can move from the marked cell to `p'`, in the direction the
transition names. -/
noncomputable def moveToF (right : L'.Relations 1) (le : L'.Relations 2)
    (posn h : L'.Relations 1) (τ p' : γ) : L'.Formula γ :=
  ((Relations.formula₁ h (Term.var (Sum.inr 0))) ⊓
    ((Relations.formula₁ right (Term.var (Sum.inl τ)) ⊓
        succPosF le posn (Sum.inr 0) (Sum.inl p')) ⊔
      (∼(Relations.formula₁ right (Term.var (Sum.inl τ))) ⊓
        succPosF le posn (Sum.inl p') (Sum.inr 0)))).iExs (Fin 1)

/-- The machine takes a step: no accepting mark, and some applicable
transition with a destination, a written symbol, and a position to move
to. -/
noncomputable def goF (tr : L'.Relations 1) (src rd dst wr : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (acc right : L'.Relations 1)
    (le : L'.Relations 2) (posn : L'.Relations 1) : L'.Formula γ :=
  ∼(markMeetF s acc) ⊓
    ((applF tr src rd s h t (Sum.inr 0) ⊓
        (someArgF dst (Sum.inr 0) ⊓
          (someArgF wr (Sum.inr 0) ⊓
            moveToF right le posn h (Sum.inr 0) (Sum.inr 1)))).iExs (Fin 2))

/-- The cell initially holds this symbol: its input symbol, or the blank when
no input is given for it. -/
noncomputable def initTapeAtF (inp : L'.Relations 2) (blank : L'.Relations 1)
    (x y : γ) : L'.Formula γ :=
  Relations.formula₂ inp (Term.var x) (Term.var y) ⊔
    (Formula.iAlls (Fin 1)
        (∼(Relations.formula₂ inp (Term.var (Sum.inl x)) (Term.var (Sum.inr 0))) :
          L'.Formula (γ ⊕ Fin 1)) ⊓
      Relations.formula₁ blank (Term.var y))

/-- `x` is the lowest position. -/
noncomputable def minPosAtF (le : L'.Relations 2) (posn : L'.Relations 1)
    (x : γ) : L'.Formula γ :=
  Relations.formula₁ posn (Term.var x) ⊓
    ((Relations.formula₁ posn (Term.var (Sum.inr 0))).imp
      (Relations.formula₂ le (Term.var (Sum.inl x)) (Term.var (Sum.inr 0)))).iAlls (Fin 1)

variable {v : γ → M}

@[simp]
theorem realize_markMeetF (s r : L'.Relations 1) :
    (markMeetF (γ := γ) s r).Realize v ↔ ∃ q : M, RelMap s ![q] ∧ RelMap r ![q] := by
  rw [markMeetF]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁,
    Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩

@[simp]
theorem realize_someArgF (r : L'.Relations 2) (x : γ) :
    (someArgF r x).Realize v ↔ ∃ b : M, RelMap r ![v x, b] := by
  rw [someArgF]
  simp only [Formula.realize_iExs, Formula.realize_rel₂, Term.realize_var, Sum.elim_inl,
    Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩

@[simp]
theorem realize_applF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (τ : γ) :
    (applF tr src rd s h t τ).Realize v ↔
      (RelMap tr ![v τ] ∧
        ((∀ q : M, RelMap s ![q] → RelMap src ![v τ, q]) ∧
          ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] →
            RelMap rd ![v τ, a])) := by
  rw [applF]
  simp only [Formula.realize_inf, Formula.realize_rel₁, realize_markArgF,
    realize_cellArgF, Term.realize_var]

@[simp]
theorem realize_moveToF (right : L'.Relations 1) (le : L'.Relations 2)
    (posn h : L'.Relations 1) (τ p' : γ) :
    (moveToF right le posn h τ p').Realize v ↔
      ∃ p : M, RelMap h ![p] ∧
        ((RelMap right ![v τ] ∧
            Lax904597.Machines.SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) p
              (v p')) ∨
          (¬RelMap right ![v τ] ∧
            Lax904597.Machines.SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a])
              (v p') p)) := by
  rw [moveToF]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_not, Formula.realize_rel₁, realize_succPosF, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩

@[simp]
theorem realize_goF (tr : L'.Relations 1) (src rd dst wr : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (acc right : L'.Relations 1)
    (le : L'.Relations 2) (posn : L'.Relations 1) :
    (goF (γ := γ) tr src rd dst wr s h t acc right le posn).Realize v ↔
      ((¬∃ q : M, RelMap s ![q] ∧ RelMap acc ![q]) ∧
        ∃ τ p' : M,
          ((RelMap tr ![τ] ∧
              ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
                ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
            ((∃ b : M, RelMap dst ![τ, b]) ∧
              ((∃ b : M, RelMap wr ![τ, b]) ∧
                ∃ p : M, RelMap h ![p] ∧
                  ((RelMap right ![τ] ∧
                      Lax904597.Machines.SuccPos (fun a b => RelMap le ![a, b])
                        (fun a => RelMap posn ![a]) p p') ∨
                    (¬RelMap right ![τ] ∧
                      Lax904597.Machines.SuccPos (fun a b => RelMap le ![a, b])
                        (fun a => RelMap posn ![a]) p' p)))))) := by
  rw [goF]
  simp only [Formula.realize_inf, Formula.realize_not, realize_markMeetF,
    Formula.realize_iExs, realize_applF, realize_someArgF, realize_moveToF, Sum.elim_inr]
  refine and_congr Iff.rfl
    ⟨fun ⟨i, hi⟩ => ⟨i 0, i 1, hi⟩, fun ⟨τ, p', hp⟩ => ⟨![τ, p'], hp⟩⟩

@[simp]
theorem realize_initTapeAtF (inp : L'.Relations 2) (blank : L'.Relations 1)
    (x y : γ) :
    (initTapeAtF inp blank x y).Realize v ↔
      (RelMap inp ![v x, v y] ∨
        ((∀ b : M, ¬RelMap inp ![v x, b]) ∧
          RelMap blank ![v y])) := by
  rw [initTapeAtF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_not, Formula.realize_rel₂, Formula.realize_rel₁, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr]
  exact or_congr Iff.rfl (and_congr
    ⟨fun hh b => hh fun _ => b, fun hh i => hh (i 0)⟩ Iff.rfl)

@[simp]
theorem realize_minPosAtF (le : L'.Relations 2) (posn : L'.Relations 1)
    (x : γ) :
    (minPosAtF le posn x).Realize v ↔
      Lax904597.Machines.MinPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) (v x) := by
  rw [minPosAtF, Lax904597.Machines.MinPos]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inl,
    Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun hh q => hh fun _ => q, fun hh i => hh (i 0)⟩

/-- The transition applies, with a destination, a written symbol, and this
new symbol written in the marked cell. -/
noncomputable def writeNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t wr : L'.Relations 2) (y : γ) : L'.Formula γ :=
  (applF tr src rd s h t (Sum.inr 0) ⊓
    Relations.formula₂ wr (Term.var (Sum.inr 0)) (Term.var (Sum.inl y))).iExs (Fin 1)

/-- The transition applies and moves to this new state. -/
noncomputable def dstNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t dst : L'.Relations 2) (y : γ) : L'.Formula γ :=
  (applF tr src rd s h t (Sum.inr 0) ⊓
    Relations.formula₂ dst (Term.var (Sum.inr 0)) (Term.var (Sum.inl y))).iExs (Fin 1)

/-- The transition applies and moves the head to this new position. -/
noncomputable def headNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (right : L'.Relations 1)
    (le : L'.Relations 2) (posn : L'.Relations 1) (y : γ) : L'.Formula γ :=
  (applF tr src rd s h t (Sum.inr 0) ⊓
    moveToF right le posn h (Sum.inr 0) (Sum.inl y)).iExs (Fin 1)

variable {v : γ → M}

@[simp]
theorem realize_writeNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t wr : L'.Relations 2) (y : γ) :
    (writeNewF tr src rd s h t wr y).Realize v ↔
      ∃ τ : M, (RelMap tr ![τ] ∧
          ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
            ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
        RelMap wr ![τ, v y] := by
  rw [writeNewF]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_applF,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

@[simp]
theorem realize_dstNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t dst : L'.Relations 2) (y : γ) :
    (dstNewF tr src rd s h t dst y).Realize v ↔
      ∃ τ : M, (RelMap tr ![τ] ∧
          ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
            ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
        RelMap dst ![τ, v y] := by
  rw [dstNewF]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_applF,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

@[simp]
theorem realize_headNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (right : L'.Relations 1)
    (le : L'.Relations 2) (posn : L'.Relations 1) (y : γ) :
    (headNewF tr src rd s h t right le posn y).Realize v ↔
      ∃ τ : M, (RelMap tr ![τ] ∧
          ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
            ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
        ∃ p : M, RelMap h ![p] ∧
          ((RelMap right ![τ] ∧
              Lax904597.Machines.SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) p
                (v y)) ∨
            (¬RelMap right ![τ] ∧
              Lax904597.Machines.SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a])
                (v y) p)) := by
  rw [headNewF]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_applF, realize_moveToF,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

end Shapes

/-! ### The iterated definition and its semantics -/

section Machine

variable {A : Type} [Lax904597.Machines.turing.Structure A]

/-- The state mark is empty: how the iteration recognizes the not-yet-started
assignment, which no configuration resembles. -/
def StateEmptyOn (ρ : mBlock.Assignment A) : Prop := ¬∃ q : A, mState ρ q

/-- The transition applies in the marked state, reading the marked cell. -/
def ApplOn (ρ : mBlock.Assignment A) (τ : A) : Prop :=
  Lax904597.Machines.TMTr τ ∧ ((∀ q : A, mState ρ q → Lax904597.Machines.TMSrc τ q) ∧
    ∀ p a : A, mHead ρ p → mTape ρ p a → Lax904597.Machines.TMRead τ a)

/-- The machine takes a step from this assignment: no accepting mark, and
some applicable transition with a destination, a written symbol and a
position to move to. -/
def GoOn (ρ : mBlock.Assignment A) : Prop :=
  (¬∃ q : A, mState ρ q ∧ Lax904597.Machines.TMAcc q) ∧
    ∃ τ p' : A, ApplOn ρ τ ∧
      ((∃ b : A, Lax904597.Machines.TMDst τ b) ∧ ((∃ b : A, Lax904597.Machines.TMWrite τ b) ∧
        ∃ p : A, mHead ρ p ∧ ((Lax904597.Machines.TMRight τ ∧ Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p p') ∨
          (¬Lax904597.Machines.TMRight τ ∧ Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p' p))))

variable (A) in
/-- The initial assignment: start states, lowest positions, the initial
tape. On a well-formed deterministic instance with a start state this is a
configuration – the initial one. -/
def mInitAssign : mBlock.Assignment A
  | none => fun x => (Lax904597.Machines.tmData A).InitTape (x 0) (x 1)
  | some false => fun x => Lax904597.Machines.TMStart (x 0)
  | some true => fun x => Lax904597.Machines.MinPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn (x 0)

/-- One application of the step formulas, semantically: load the initial
configuration from the empty assignment, take the machine step when one is
available and the state is not accepting, stutter otherwise. -/
def mNextAssign (ρ : mBlock.Assignment A) : mBlock.Assignment A
  | none => fun x =>
      (StateEmptyOn ρ ∧ (Lax904597.Machines.tmData A).InitTape (x 0) (x 1)) ∨
        (¬StateEmptyOn ρ ∧
          ((¬GoOn ρ ∧ mTape ρ (x 0) (x 1)) ∨
            (GoOn ρ ∧ ((¬mHead ρ (x 0) ∧ mTape ρ (x 0) (x 1)) ∨
              (mHead ρ (x 0) ∧ ∃ τ : A, ApplOn ρ τ ∧ Lax904597.Machines.TMWrite τ (x 1))))))
  | some false => fun x =>
      (StateEmptyOn ρ ∧ Lax904597.Machines.TMStart (x 0)) ∨
        (¬StateEmptyOn ρ ∧
          ((¬GoOn ρ ∧ mState ρ (x 0)) ∨
            (GoOn ρ ∧ ∃ τ : A, ApplOn ρ τ ∧ Lax904597.Machines.TMDst τ (x 0))))
  | some true => fun x =>
      (StateEmptyOn ρ ∧ Lax904597.Machines.MinPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn (x 0)) ∨
        (¬StateEmptyOn ρ ∧
          ((¬GoOn ρ ∧ mHead ρ (x 0)) ∨
            (GoOn ρ ∧ ∃ τ : A, ApplOn ρ τ ∧ ∃ p : A, mHead ρ p ∧
              ((Lax904597.Machines.TMRight τ ∧ Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p (x 0)) ∨
                (¬Lax904597.Machines.TMRight τ ∧ Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn (x 0) p)))))

end Machine

/-! ### The step formulas -/

section Formulas

/-- The empty-state test, as a formula. -/
noncomputable def emptyF {γ : Type} : mLang₁.Formula γ := ∼(someF mS₁)

/-- The step condition, at the machine's symbols. -/
noncomputable def mGoF {γ : Type} : mLang₁.Formula γ :=
  goF (mIn₁ Lax904597.Machines.tmTr) (mIn₁ Lax904597.Machines.tmSrc) (mIn₁ Lax904597.Machines.tmRead) (mIn₁ Lax904597.Machines.tmDst) (mIn₁ Lax904597.Machines.tmWrite) mS₁ mH₁ mT₁
    (mIn₁ Lax904597.Machines.tmAcc) (mIn₁ Lax904597.Machines.tmRight) (mIn₁ Lax904597.Machines.tmLe) (mIn₁ Lax904597.Machines.tmPosn)

/-- The step formula of the tape variable. -/
noncomputable def stepTapeF : mLang₁.Formula (Fin 2) :=
  (emptyF ⊓ initTapeAtF (mIn₁ Lax904597.Machines.tmInp) (mIn₁ Lax904597.Machines.tmBlank) 0 1) ⊔
    (∼emptyF ⊓
      ((∼mGoF ⊓ Relations.formula₂ mT₁ (Term.var 0) (Term.var 1)) ⊔
        (mGoF ⊓ ((∼(Relations.formula₁ mH₁ (Term.var 0)) ⊓
            Relations.formula₂ mT₁ (Term.var 0) (Term.var 1)) ⊔
          (Relations.formula₁ mH₁ (Term.var 0) ⊓
            writeNewF (mIn₁ Lax904597.Machines.tmTr) (mIn₁ Lax904597.Machines.tmSrc) (mIn₁ Lax904597.Machines.tmRead) mS₁ mH₁ mT₁
              (mIn₁ Lax904597.Machines.tmWrite) 1)))))

/-- The step formula of the state variable. -/
noncomputable def stepStateF : mLang₁.Formula (Fin 1) :=
  (emptyF ⊓ Relations.formula₁ (mIn₁ Lax904597.Machines.tmStart) (Term.var 0)) ⊔
    (∼emptyF ⊓
      ((∼mGoF ⊓ Relations.formula₁ mS₁ (Term.var 0)) ⊔
        (mGoF ⊓ dstNewF (mIn₁ Lax904597.Machines.tmTr) (mIn₁ Lax904597.Machines.tmSrc) (mIn₁ Lax904597.Machines.tmRead) mS₁ mH₁ mT₁
          (mIn₁ Lax904597.Machines.tmDst) 0)))

/-- The step formula of the head variable. -/
noncomputable def stepHeadF : mLang₁.Formula (Fin 1) :=
  (emptyF ⊓ minPosAtF (mIn₁ Lax904597.Machines.tmLe) (mIn₁ Lax904597.Machines.tmPosn) 0) ⊔
    (∼emptyF ⊓
      ((∼mGoF ⊓ Relations.formula₁ mH₁ (Term.var 0)) ⊔
        (mGoF ⊓ headNewF (mIn₁ Lax904597.Machines.tmTr) (mIn₁ Lax904597.Machines.tmSrc) (mIn₁ Lax904597.Machines.tmRead) mS₁ mH₁ mT₁
          (mIn₁ Lax904597.Machines.tmRight) (mIn₁ Lax904597.Machines.tmLe) (mIn₁ Lax904597.Machines.tmPosn) 0)))

/-- **The machine iteration**: one configuration in the block, one machine
step per stage, stuttering on halting configurations; the output checks the
instance and reads acceptance off the stable configuration. -/
noncomputable def mPfp : Lax535992.InflationaryFixedPoint.StepDef mBase where
  B := mBlock
  step := fun i => match i with
    | none => stepTapeF
    | some false => stepStateF
    | some true => stepHeadF
  out := wfF (mIn₁ Lax904597.Machines.tmLe) (mIn₁ Lax904597.Machines.tmInp) (mIn₁ Lax904597.Machines.tmPosn) (mIn₁ Lax904597.Machines.tmBlank) ⊓
    (detF (mIn₁ Lax904597.Machines.tmTr) (mIn₁ Lax904597.Machines.tmStart) (mIn₁ Lax904597.Machines.tmSrc) (mIn₁ Lax904597.Machines.tmRead) (mIn₁ Lax904597.Machines.tmDst)
        (mIn₁ Lax904597.Machines.tmWrite) ⊓
      markMeetF mS₁ (mIn₁ Lax904597.Machines.tmAcc))

end Formulas

/-! ### The step formulas mean the semantic step -/

section Master

variable {A : Type} [Lax904597.Machines.turing.Structure A] [LinearOrder A]

theorem realize_emptyF (ρ : mBlock.Assignment A) {γ : Type} (v : γ → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ (emptyF (γ := γ)) v) ↔
      StateEmptyOn ρ := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [emptyF, Formula.realize_not, realize_someF]
  exact Iff.rfl

theorem realize_mGoF (ρ : mBlock.Assignment A) {γ : Type} (v : γ → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ (mGoF (γ := γ)) v) ↔
      GoOn ρ := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [mGoF, realize_goF]
  exact Iff.rfl

theorem realize_stepTapeF (ρ : mBlock.Assignment A) (x : Fin 2 → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ stepTapeF x) ↔
      mNextAssign ρ none x := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [stepTapeF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_emptyF, realize_mGoF, realize_initTapeAtF, realize_writeNewF,
    Formula.realize_rel₂, Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

theorem realize_stepStateF (ρ : mBlock.Assignment A) (x : Fin 1 → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ stepStateF x) ↔
      mNextAssign ρ (some false) x := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [stepStateF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_emptyF, realize_mGoF, realize_dstNewF, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

theorem realize_stepHeadF (ρ : mBlock.Assignment A) (x : Fin 1 → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ stepHeadF x) ↔
      mNextAssign ρ (some true) x := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [stepHeadF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_emptyF, realize_mGoF, realize_minPosAtF, realize_headNewF,
    Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- **One application of the step formulas is the semantic step.** -/
theorem next_mPfp (ρ : mBlock.Assignment A) : mPfp.next ρ = mNextAssign ρ := by
  funext i x
  match i with
  | none => exact propext (realize_stepTapeF ρ x)
  | some false => exact propext (realize_stepStateF ρ x)
  | some true => exact propext (realize_stepHeadF ρ x)

end Master

/-! ### The iteration follows the run -/

section Run

variable {A : Type} [Lax904597.Machines.turing.Structure A] [LinearOrder A]

omit [Lax904597.Machines.turing.Structure A] [LinearOrder A] in
theorem not_stateEmptyOn_cfgAssign (c : Lax904597.Machines.Config A) : ¬StateEmptyOn (cfgAssign c) :=
  fun h => h ⟨c.state, rfl⟩

omit [Lax904597.Machines.turing.Structure A] [LinearOrder A] in
theorem stateEmptyOn_botAssign : StateEmptyOn (mBlock.botAssign A) :=
  fun ⟨_, h⟩ => h

omit [LinearOrder A] in
/-- From an empty state mark, one step loads the initial assignment. -/
theorem mNextAssign_of_stateEmpty {ρ : mBlock.Assignment A} (h : StateEmptyOn ρ) :
    mNextAssign ρ = mInitAssign A := by
  funext i x
  match i with
  | none =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inl ⟨h, hh⟩⟩
    rcases hh with ⟨-, h2⟩ | ⟨hn, -⟩
    · exact h2
    · exact absurd h hn
  | some false =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inl ⟨h, hh⟩⟩
    rcases hh with ⟨-, h2⟩ | ⟨hn, -⟩
    · exact h2
    · exact absurd h hn
  | some true =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inl ⟨h, hh⟩⟩
    rcases hh with ⟨-, h2⟩ | ⟨hn, -⟩
    · exact h2
    · exact absurd h hn

omit [LinearOrder A] in
/-- On a configuration from which the machine takes no step, the iteration
stutters. -/
theorem mNextAssign_cfgAssign_of_not_goOn {c : Lax904597.Machines.Config A} (hng : ¬GoOn (cfgAssign c)) :
    mNextAssign (cfgAssign c) = cfgAssign c := by
  have hne := not_stateEmptyOn_cfgAssign c
  funext i x
  match i with
  | none =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inr ⟨hne, Or.inl ⟨hng, hh⟩⟩⟩
    rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨-, ht⟩ | ⟨hg, -⟩⟩
    · exact absurd hSE hne
    · exact ht
    · exact absurd hg hng
  | some false =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inr ⟨hne, Or.inl ⟨hng, hh⟩⟩⟩
    rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨-, ht⟩ | ⟨hg, -⟩⟩
    · exact absurd hSE hne
    · exact ht
    · exact absurd hg hng
  | some true =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inr ⟨hne, Or.inl ⟨hng, hh⟩⟩⟩
    rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨-, ht⟩ | ⟨hg, -⟩⟩
    · exact absurd hSE hne
    · exact ht
    · exact absurd hg hng

omit [LinearOrder A] in
/-- On an accepting configuration, the iteration stutters. -/
theorem mNextAssign_cfgAssign_of_acc {c : Lax904597.Machines.Config A} (hacc : (Lax904597.Machines.tmData A).Acc c.state) :
    mNextAssign (cfgAssign c) = cfgAssign c :=
  mNextAssign_cfgAssign_of_not_goOn fun hgo => hgo.1 ⟨c.state, rfl, hacc⟩

/-- A configuration from which the step condition fires can take a machine
step. -/
theorem step_of_goOn {c : Lax904597.Machines.Config A} (hgo : GoOn (cfgAssign c)) :
    ∃ d, (Lax904597.Machines.tmData A).Step c d := by
  classical
  obtain ⟨-, τ, p', ⟨htr, hsrcs, hreads⟩, ⟨q₀, hq₀⟩, ⟨a₀, ha₀⟩, p, hp, hmv⟩ := hgo
  rw [show p = c.head from hp] at hmv
  refine ⟨⟨q₀, p', fun r => if r = c.head then a₀ else c.tape r⟩, τ, htr,
    hsrcs c.state rfl, hreads c.head (c.tape c.head) rfl rfl, hq₀, ?_, ?_, hmv⟩
  · change Lax904597.Machines.TMWrite τ (if c.head = c.head then a₀ else c.tape c.head)
    rw [if_pos rfl]
    exact ha₀
  · intro r hr
    change (if r = c.head then a₀ else c.tape r) = c.tape r
    rw [if_neg hr]

omit [LinearOrder A] in
/-- On a non-accepting configuration that steps, the iteration takes **the**
machine step. -/
theorem mNextAssign_cfgAssign_of_step (hwf : (Lax904597.Machines.tmData A).WellFormed)
    (hdet : (Lax904597.Machines.tmData A).Deterministic) {c d : Lax904597.Machines.Config A}
    (hnacc : ¬(Lax904597.Machines.tmData A).Acc c.state) (hstep : (Lax904597.Machines.tmData A).Step c d) :
    mNextAssign (cfgAssign c) = cfgAssign d := by
  obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  have happl : ApplOn (cfgAssign c) τ :=
    ⟨htr, fun q hq => (show q = c.state from hq) ▸ hsrc, fun p a hp ha => by
      rw [show p = c.head from hp] at ha
      have ha' : c.tape c.head = a := ha
      exact ha' ▸ hread⟩
  have hgo : GoOn (cfgAssign c) :=
    ⟨fun ⟨q, hq, hacc⟩ => hnacc (hq ▸ hacc), τ, d.head, happl,
      ⟨d.state, hdst⟩, ⟨d.tape c.head, hwrite⟩, c.head, rfl, hmove⟩
  have hne := not_stateEmptyOn_cfgAssign c
  have happl_uniq : ∀ τ' : A, ApplOn (cfgAssign c) τ' → τ' = τ := by
    rintro τ' ⟨htr', hsrcs', hreads'⟩
    exact hdet.2.1 τ' τ c.state (c.tape c.head) htr' htr (hsrcs' c.state rfl) hsrc
      (hreads' c.head (c.tape c.head) rfl rfl) hread
  funext i x
  match i with
  | none =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨hng, -⟩ | ⟨-, ⟨hnh, ht⟩ | ⟨hh, τ', happl', hw⟩⟩⟩
      · exact absurd hSE hne
      · exact absurd hgo hng
      · change d.tape (x 0) = x 1
        rw [hframe (x 0) (fun hcon => hnh hcon)]
        exact ht
      · have heq := happl_uniq τ' happl'
        subst heq
        change d.tape (x 0) = x 1
        rw [show (x 0) = c.head from hh]
        exact hdet.2.2.2 τ' _ _ hwrite hw
    · rcases eq_or_ne (x 0) c.head with hx | hx
      · refine Or.inr ⟨hne, Or.inr ⟨hgo, Or.inr ⟨hx, τ, happl, ?_⟩⟩⟩
        rw [← (show d.tape (x 0) = x 1 from hh), hx]
        exact hwrite
      · refine Or.inr ⟨hne, Or.inr ⟨hgo, Or.inl ⟨hx, ?_⟩⟩⟩
        change c.tape (x 0) = x 1
        rw [← hframe (x 0) hx]
        exact hh
  | some false =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨hng, -⟩ | ⟨-, τ', happl', hd'⟩⟩
      · exact absurd hSE hne
      · exact absurd hgo hng
      · have heq := happl_uniq τ' happl'
        subst heq
        exact hdet.2.2.1 τ' _ _ hd' hdst
    · exact Or.inr ⟨hne, Or.inr ⟨hgo, τ, happl,
        (show (x 0) = d.state from hh) ▸ hdst⟩⟩
  | some true =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨hng, -⟩ | ⟨-, τ', happl', p, hp, hmv'⟩⟩
      · exact absurd hSE hne
      · exact absurd hgo hng
      · have heq := happl_uniq τ' happl'
        subst heq
        rw [show p = c.head from hp] at hmv'
        change (x 0) = d.head
        rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩ <;> rcases hmv' with ⟨hr', hs'⟩ | ⟨hr', hs'⟩
        · exact (TMData.succPos_right_unique hwf.1 hs' hs :)
        · exact absurd hr hr'
        · exact absurd hr' hr
        · exact (succPos_left_unique hwf.1 hs' hs :)
    · refine Or.inr ⟨hne, Or.inr ⟨hgo, τ, happl, c.head, rfl, ?_⟩⟩
      rw [show (x 0) = d.head from hh]
      exact hmove

omit [LinearOrder A] in
/-- The initial assignment of a well-formed deterministic instance with an
initial configuration is that configuration. -/
theorem mInitAssign_eq_cfgAssign (hwf : (Lax904597.Machines.tmData A).WellFormed)
    (hdet : (Lax904597.Machines.tmData A).Deterministic) {c₀ : Lax904597.Machines.Config A}
    (hinit : (Lax904597.Machines.tmData A).IsInit c₀) : mInitAssign A = cfgAssign c₀ := by
  funext i x
  match i with
  | none =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · exact TMData.initTape_functional hwf (hinit.2.2 (x 0))
        (show (Lax904597.Machines.tmData A).InitTape (x 0) (x 1) from hh)
    · change (Lax904597.Machines.tmData A).InitTape (x 0) (x 1)
      rw [← (show c₀.tape (x 0) = x 1 from hh)]
      exact hinit.2.2 (x 0)
  | some false =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · exact hdet.1 _ _ hh hinit.1
    · exact show Lax904597.Machines.TMStart (x 0) from (show (x 0) = c₀.state from hh) ▸ hinit.1
  | some true =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · exact hwf.1.2.2.1 _ _ (hh.2 c₀.head hinit.2.1.1) (hinit.2.1.2 (x 0) hh.1)
    · exact show Lax904597.Machines.MinPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn (x 0) from
        (show (x 0) = c₀.head from hh) ▸ hinit.2.1

/-- The first stage of the iteration is the initial assignment. -/
theorem partStage_one : mPfp.partStage A 1 = mInitAssign A :=
  (mPfp.partStage_succ 0).trans ((next_mPfp _).trans
    (mNextAssign_of_stateEmpty stateEmptyOn_botAssign))

/-- **The stages follow the run**: as long as no accepting configuration has
been reached, stage `n + 1` is the `n`-th configuration of the run. -/
theorem partStage_run (hwf : (Lax904597.Machines.tmData A).WellFormed) (hdet : (Lax904597.Machines.tmData A).Deterministic)
    {c₀ : Lax904597.Machines.Config A} (hinit : (Lax904597.Machines.tmData A).IsInit c₀) :
    ∀ n c, (Lax904597.Machines.tmData A).StepsIn n c₀ c →
      (∀ k, k < n → ∀ e, (Lax904597.Machines.tmData A).StepsIn k c₀ e → ¬(Lax904597.Machines.tmData A).Acc e.state) →
      mPfp.partStage A (n + 1) = cfgAssign c := by
  intro n
  induction n with
  | zero =>
    intro c hsteps _
    rw [← (show c₀ = c from hsteps)]
    exact partStage_one.trans (mInitAssign_eq_cfgAssign hwf hdet hinit)
  | succ n ih =>
    intro c hsteps hnoacc
    obtain ⟨d, hd, hstep⟩ := TMData.stepsIn_succ_iff.mp hsteps
    have hstage := ih d hd fun k hk => hnoacc k (by omega)
    rw [mPfp.partStage_succ, hstage, next_mPfp]
    exact mNextAssign_cfgAssign_of_step hwf hdet (hnoacc n (by omega) d hd) hstep

omit [LinearOrder A] in
/-- The run reaches a configuration in some number of steps. -/
theorem stepsIn_of_reflTransGen {c d : Lax904597.Machines.Config A}
    (h : Relation.ReflTransGen (Lax904597.Machines.tmData A).Step c d) :
    ∃ n, (Lax904597.Machines.tmData A).StepsIn n c d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, hn.trans_step hstep⟩

/-- The semantics of the output sentence. -/
theorem realize_mOut (ρ : mBlock.Assignment A) :
    (@Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ) mPfp.out) ↔
      ((Lax904597.Machines.tmData A).WellFormed ∧ ((Lax904597.Machines.tmData A).Deterministic ∧
        ∃ q : A, mState ρ q ∧ Lax904597.Machines.TMAcc q)) := by
  let := mBlock.structure₁ (L := mBase) ρ
  simp only [mPfp, Sentence.Realize, Formula.realize_inf, realize_wfF, realize_detF,
    realize_markMeetF, relMap_mIn₁, relMap_mS₁]
  exact Iff.rfl

/-- **A well-formed deterministic accepting instance makes the iteration
converge with an accepting output**: run to the first accepting configuration
and stutter there. -/
theorem pfpHolds_mPfp_of_acceptsSpace (hwf : (Lax904597.Machines.tmData A).WellFormed)
    (hdet : (Lax904597.Machines.tmData A).Deterministic) (hacc : (Lax904597.Machines.tmData A).AcceptsSpace) :
    mPfp.PFPHolds A := by
  obtain ⟨c₀, c, hinit, hreach, haccst⟩ := hacc
  have hex : ∃ n, ∃ cA : Lax904597.Machines.Config A,
      (Lax904597.Machines.tmData A).StepsIn n c₀ cA ∧ (Lax904597.Machines.tmData A).Acc cA.state := by
    obtain ⟨n, hn⟩ := stepsIn_of_reflTransGen hreach
    exact ⟨n, c, hn, haccst⟩
  have hmem : sInf {n | ∃ cA, (Lax904597.Machines.tmData A).StepsIn n c₀ cA ∧ (Lax904597.Machines.tmData A).Acc cA.state} ∈
      {n | ∃ cA, (Lax904597.Machines.tmData A).StepsIn n c₀ cA ∧ (Lax904597.Machines.tmData A).Acc cA.state} :=
    Nat.sInf_mem hex
  obtain ⟨cA, hsteps, haccA⟩ := hmem
  have hnoacc : ∀ k, k < sInf {n | ∃ cA, (Lax904597.Machines.tmData A).StepsIn n c₀ cA ∧
      (Lax904597.Machines.tmData A).Acc cA.state} → ∀ e, (Lax904597.Machines.tmData A).StepsIn k c₀ e →
      ¬(Lax904597.Machines.tmData A).Acc e.state := by
    intro k hk e hst hacce
    have hmem : k ∈ {n | ∃ cA, (Lax904597.Machines.tmData A).StepsIn n c₀ cA ∧ (Lax904597.Machines.tmData A).Acc cA.state} :=
      ⟨e, hst, hacce⟩
    exact absurd (Nat.sInf_le hmem) (by omega)
  have hstage := partStage_run hwf hdet hinit _ cA hsteps hnoacc
  refine ⟨sInf {n | ∃ cA, (Lax904597.Machines.tmData A).StepsIn n c₀ cA ∧ (Lax904597.Machines.tmData A).Acc cA.state} + 1,
    ?_, ?_⟩
  · have h : mPfp.next (mPfp.partStage A (sInf {n | ∃ cA, (Lax904597.Machines.tmData A).StepsIn n c₀ cA ∧
        (Lax904597.Machines.tmData A).Acc cA.state} + 1)) = mPfp.partStage A (sInf {n | ∃ cA,
        (Lax904597.Machines.tmData A).StepsIn n c₀ cA ∧ (Lax904597.Machines.tmData A).Acc cA.state} + 1) := by
      rw [hstage, next_mPfp]
      exact mNextAssign_cfgAssign_of_acc haccA
    exact h
  · rw [hstage]
    exact (realize_mOut (cfgAssign cA)).mpr ⟨hwf, hdet, cA.state, rfl, haccA⟩

/-- **A converging accepting iteration means the instance is well-formed,
deterministic and accepting**: the stages only ever hold the empty
assignment, the initial assignment, or a configuration of the run. -/
theorem acceptsSpace_of_pfpHolds_mPfp [Finite A] (h : mPfp.PFPHolds A) :
    ((Lax904597.Machines.tmData A).WellFormed ∧ ((Lax904597.Machines.tmData A).Deterministic ∧
      (Lax904597.Machines.tmData A).AcceptsSpace)) := by
  obtain ⟨n, -, hout⟩ := h
  obtain ⟨hwf, hdet, q, hq, hqacc⟩ := (realize_mOut _).mp hout
  by_cases hstart : ∃ q₀ : A, Lax904597.Machines.TMStart q₀
  · obtain ⟨q₀, hq₀⟩ := hstart
    obtain ⟨c₀, hinit, -⟩ := TMData.exists_isInit hwf hq₀
    have hinv : ∀ m, mPfp.partStage A m = mBlock.botAssign A ∨
        ∃ k c, (Lax904597.Machines.tmData A).StepsIn k c₀ c ∧ mPfp.partStage A m = cfgAssign c := by
      intro m
      induction m with
      | zero => exact Or.inl rfl
      | succ m ihm =>
        rcases ihm with hm | ⟨k, c, hkc, hm⟩ <;> rw [mPfp.partStage_succ, hm, next_mPfp]
        · exact Or.inr ⟨0, c₀, rfl, (mNextAssign_of_stateEmpty
            stateEmptyOn_botAssign).trans (mInitAssign_eq_cfgAssign hwf hdet hinit)⟩
        · by_cases hgo : GoOn (cfgAssign c)
          · obtain ⟨d, hd⟩ := step_of_goOn hgo
            refine Or.inr ⟨k + 1, d, hkc.trans_step hd, ?_⟩
            exact mNextAssign_cfgAssign_of_step hwf hdet
              (fun hacc => hgo.1 ⟨c.state, rfl, hacc⟩) hd
          · exact Or.inr ⟨k, c, hkc, mNextAssign_cfgAssign_of_not_goOn hgo⟩
    rcases hinv n with hn | ⟨k, c, hkc, hn⟩
    · rw [hn] at hq
      exact hq.elim
    · rw [hn] at hq
      exact ⟨hwf, hdet, c₀, c, hinit, TMData.reflTransGen_of_stepsIn hkc,
        (show q = c.state from hq) ▸ hqacc⟩
  · have hstages : ∀ m, mPfp.partStage A m = mBlock.botAssign A ∨
        mPfp.partStage A m = mInitAssign A := by
      intro m
      induction m with
      | zero => exact Or.inl rfl
      | succ m ihm =>
        rcases ihm with hm | hm <;> rw [mPfp.partStage_succ, hm, next_mPfp]
        · exact Or.inr (mNextAssign_of_stateEmpty stateEmptyOn_botAssign)
        · exact Or.inr (mNextAssign_of_stateEmpty fun ⟨q', hq'⟩ => hstart ⟨q', hq'⟩)
    rcases hstages n with hn | hn <;> rw [hn] at hq
    · exact hq.elim
    · exact absurd ⟨q, hq⟩ hstart

end Run

end SpaceTM

open SpaceTM

/-! ### The capture theorem -/

/-- **The deterministic space-bounded machine problem is FO(≤, PFP)
definable**: iterate the machine, stuttering on halting configurations. -/
theorem dtmAcceptSpace_pfpDefinable : Lax134656.PartialFixedPoint.PFPDefinable DTMAcceptSpace := by
  refine ⟨mPfp, ?_⟩
  intro A _ _ _ _
  constructor
  · rintro ⟨hwf, hdet, hacc⟩
    exact pfpHolds_mPfp_of_acceptsSpace hwf hdet hacc
  · intro h
    exact acceptsSpace_of_pfpHolds_mPfp h

/-- **PSPACE is contained in FO(≤, PFP)**: reduce to the machine problem and
pull the iteration back through the relativized reduction. -/
theorem pfpDefinable_of_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : P ∈ PSPACE) : Lax134656.PartialFixedPoint.PFPDefinable P := by
  obtain ⟨f⟩ := le_dtmAcceptSpace_of_mem_PSPACE P h
  exact PFPDefinable.of_relOrderedReduction f dtmAcceptSpace_pfpDefinable

/-- **The capture theorem FO(≤, PFP) = PSPACE** ([Abiteboul–Vianu
1989][abiteboul1989fixpoint]; [Ebbinghaus–Flum 1995][ebbinghaus1995finite],
ch. 7): a problem is FO(≤, PFP) definable exactly when it is in PSPACE. -/
theorem pfpDefinable_iff_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) :
    Lax134656.PartialFixedPoint.PFPDefinable P ↔ P ∈ PSPACE :=
  ⟨mem_PSPACE_of_pfpDefinable, pfpDefinable_of_mem_PSPACE⟩

end Lax480241Proofs.DescriptiveComplexity


