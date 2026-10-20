import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Logic.Equiv.Prod
import Lax366625.CountingSat
import Lax904597.Sat
import Lax485149.Problems
import Lax366625.CountingProblems
import Lax175070.CountDefinability

/-!
---
title: Satisfiability decided by counting models
type: definition
---
⊕SAT asks whether a CNF instance of the NP core has an odd number of models,
and Mod$_k$-SAT whether that number is not a multiple of $k$.

An instance with a selected variable is a CNF instance together with a mark
on its variables. #SelSAT$_b$ counts the models in which every selected
variable has the value $b$. SelMajSAT asks whether the selected variable is
true in more models than it is false, and SelEqSAT whether it is true in
exactly as many models as it is false.
-/

namespace Lax175070.SelectedSat

open Lax366625.CountingSat Lax904597.Sat

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive selMarkRel : ℕ → Type where
/-- `sel x`: the variable `x` is selected. -/
  | sel : selMarkRel 1
  deriving DecidableEq

/-- The symbol selecting a variable. -/
def selMark : FirstOrder.Language :=
  ⟨fun _ => Empty, selMarkRel⟩

instance instIsRelationalSelMark : FirstOrder.Language.IsRelational selMark := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `sel x`: the variable `x` is selected. -/
abbrev smSel : selMark.Relations 1 :=
  .sel

/-- The relational language of CNF formulas with a selected variable. -/
abbrev satSel : Language.{0, 0} := sat.sum selMark

open FirstOrder

open Language Structure

/-- “Is selected”, in the vocabulary of CNF formulas with a selected
variable. -/
abbrev ssSel : satSel.Relations 1 := Sum.inr smSel

/-- A CNF formula with a selected variable is a CNF formula. -/
instance satSelStructure (A : Type) [satSel.Structure A] :
    sat.Structure A :=
  (LHom.sumInl : sat →ᴸ satSel).reduct A

section Counts

variable (A : Type) [satSel.Structure A]

/-- A model of the formula in which every selected variable has the value
`b`. -/
def SelModel (b : Bool) (ν : A → Prop) : Prop :=
  SatModel A ν ∧ ∀ x : A, RelMap ssSel ![x] → (ν x ↔ b = true)

end Counts

open Lax904597.Problems Lax485149.Problems Lax366625.CountingProblems Lax175070.CountDefinability

/-- **⊕SAT**: the number of models of a CNF formula is odd. -/
noncomputable def ParitySAT : DecisionProblem sat :=
  decide Odd SharpSAT

/-- **Mod_k-SAT**: the number of models of a CNF formula is not a multiple of
`k`. -/
noncomputable def ModSAT (k : ℕ) : DecisionProblem sat :=
  decide (fun c => ¬ k ∣ c) SharpSAT

/-- **#SelSAT**: the number of models in which every selected variable has the
value `b`. -/
noncomputable def SharpSelSAT (b : Bool) : CountingProblem satSel :=
  CountingProblem.ofFun fun A _ => Nat.card {ν : A → Prop // SelModel A b ν}

/-- **SelMajSAT**: the selected variable is true in more models than it is
false. -/
noncomputable def SelMajSAT : DecisionProblem satSel :=
  DecisionProblem.ofPred fun A _ => SharpSelSAT false A < SharpSelSAT true A

/-- **SelEqSAT**: the selected variable is true in exactly as many models as it
is false. -/
noncomputable def SelEqSAT : DecisionProblem satSel :=
  DecisionProblem.ofPred fun A _ => SharpSelSAT true A = SharpSelSAT false A

end Lax175070.SelectedSat
