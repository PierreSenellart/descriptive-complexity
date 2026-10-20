/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Walk
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax564036Proofs.DescriptiveComplexity.SecondOrder
import Lax564036Proofs.DescriptiveComplexity.Hierarchy
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

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Machines (MinPos SuccPos TMAcc TMBlank TMDst TMInp TMLe TMPosn TMRead TMRight TMSrc TMStart TMTr TMWrite tmData)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing)
end FirstOrder.Language

/-!
# Machine acceptance is existential second-order definable

The membership half of the machine bridge: `NTMAccept` is `Σ₁`-definable, hence
in NP. This is Fagin's tableau argument, and – unlike the certificate of a
weighted problem – it needs no arithmetic at all: one existential block guesses
the run, and a first-order kernel checks it clause by clause.

## What is guessed

Three relation variables, indexed by the *positions*, which are simultaneously
the tape cells and the time steps:

* `Q t q` – at time `t` the machine is in state `q`;
* `H t p` – at time `t` the head is on the cell `p`;
* `T t p a` – at time `t` the cell `p` holds the symbol `a`.

That the guess is a run is exactly `DescriptiveComplexity.TMData.RelWalk`, and
`DescriptiveComplexity.TMData.exists_relWalk_iff_exists_walk` together with
`DescriptiveComplexity.TMData.accepts_iff_exists_walk` is what connects it back to
acceptance. So this file is a transcription: every clause below mirrors one
field of `RelWalk` or one conjunct of `DescriptiveComplexity.TMData.WellFormed`, and each
has its own realization lemma. Nothing here does mathematics; the mathematics is
in `DescriptiveComplexity.Problems.Machine.Walk`.

## The clauses

Seventeen of them, conjoined into `DescriptiveComplexity.tqKernel`: four saying the
order is linear, four more for the remaining promises of `WellFormed`, six for
the functionality of the guess, then the initial clause, the step clause and
the accepting clause. The step clause is the largest formula in the library –
an existential over a transition element with seven conjuncts, against a
stutter alternative – and is kept manageable by parameterizing its body
(`DescriptiveComplexity.tqStepBodyF`) over the three variables it reads, so that no
`Sum` nesting goes deeper than two levels.

## The order predicates

`MinPos`, `MaxPos` and `SuccPos` are relativized to the positions, so they are
not the ordered-structure guards of `DescriptiveComplexity.OrderWalk` but formulas over
the instance's own `le` and `posn` symbols, defined here as
`DescriptiveComplexity.tqMinPosF` and friends.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

/-! ### The block -/

/-- The relation variables of the certificate: the state, the head and the tape
of the configuration at each time. -/
inductive TMIdx : Type
  /-- The state at a time. -/
  | state
  /-- The head cell at a time. -/
  | head
  /-- The tape contents at a time. -/
  | tape
  deriving DecidableEq

instance : Fintype TMIdx where
  elems := {TMIdx.state, TMIdx.head, TMIdx.tape}
  complete := fun i => by cases i <;> decide

/-- The single existential block: the run, guessed as a state, a head position
and a tape contents for each time. -/
def tmGuessBlock : Lax904597.SecondOrder.SOBlock where
  ι := TMIdx
  arity := fun i => match i with
    | .state => 2
    | .head => 2
    | .tape => 3

/-- The symbol of the state relation variable. -/
def tqStateRel : tmGuessBlock.lang.Relations 2 := ⟨.state, rfl⟩

/-- The symbol of the head relation variable. -/
def tqHeadRel : tmGuessBlock.lang.Relations 2 := ⟨.head, rfl⟩

/-- The symbol of the tape relation variable. -/
def tqTapeRel : tmGuessBlock.lang.Relations 3 := ⟨.tape, rfl⟩

/-- The vocabulary of the kernel: machine instances together with the guessed
run. -/
abbrev tqSOLang : Language := Lax904597.Machines.turing.sum tmGuessBlock.lang

/-- The position symbol in the kernel's vocabulary. -/
abbrev tqPosnSym : tqSOLang.Relations 1 := Sum.inl Lax904597.Machines.tmPosn

/-- The transition symbol in the kernel's vocabulary. -/
abbrev tqTrSym : tqSOLang.Relations 1 := Sum.inl Lax904597.Machines.tmTr

/-- The start-state symbol in the kernel's vocabulary. -/
abbrev tqStartSym : tqSOLang.Relations 1 := Sum.inl Lax904597.Machines.tmStart

/-- The accepting-state symbol in the kernel's vocabulary. -/
abbrev tqAccSym : tqSOLang.Relations 1 := Sum.inl Lax904597.Machines.tmAcc

/-- The blank symbol in the kernel's vocabulary. -/
abbrev tqBlankSym : tqSOLang.Relations 1 := Sum.inl Lax904597.Machines.tmBlank

/-- The move-right symbol in the kernel's vocabulary. -/
abbrev tqRightSym : tqSOLang.Relations 1 := Sum.inl Lax904597.Machines.tmRight

/-- The order symbol in the kernel's vocabulary. -/
abbrev tqLeSym : tqSOLang.Relations 2 := Sum.inl Lax904597.Machines.tmLe

/-- The transition-source symbol in the kernel's vocabulary. -/
abbrev tqSrcSym : tqSOLang.Relations 2 := Sum.inl Lax904597.Machines.tmSrc

/-- The transition-read symbol in the kernel's vocabulary. -/
abbrev tqReadSym : tqSOLang.Relations 2 := Sum.inl Lax904597.Machines.tmRead

/-- The transition-destination symbol in the kernel's vocabulary. -/
abbrev tqDstSym : tqSOLang.Relations 2 := Sum.inl Lax904597.Machines.tmDst

/-- The transition-write symbol in the kernel's vocabulary. -/
abbrev tqWriteSym : tqSOLang.Relations 2 := Sum.inl Lax904597.Machines.tmWrite

/-- The input symbol in the kernel's vocabulary. -/
abbrev tqInpSym : tqSOLang.Relations 2 := Sum.inl Lax904597.Machines.tmInp

/-- The guessed-state symbol in the kernel's vocabulary. -/
abbrev tqStateSym : tqSOLang.Relations 2 := Sum.inr tqStateRel

/-- The guessed-head symbol in the kernel's vocabulary. -/
abbrev tqHeadSym : tqSOLang.Relations 2 := Sum.inr tqHeadRel

/-- The guessed-tape symbol in the kernel's vocabulary. -/
abbrev tqTapeSym : tqSOLang.Relations 3 := Sum.inr tqTapeRel

/-! ### Formula builders -/

section Builders

variable {α : Type}

/-- `x` is a position, as a formula. -/
def tqPosnF (x : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₁ tqPosnSym (FirstOrder.Language.Term.var x)

/-- `x` is a transition, as a formula. -/
def tqTrF (x : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₁ tqTrSym (FirstOrder.Language.Term.var x)

/-- `x` is a start state, as a formula. -/
def tqStartF (x : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₁ tqStartSym (FirstOrder.Language.Term.var x)

/-- `x` is an accepting state, as a formula. -/
def tqAccF (x : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₁ tqAccSym (FirstOrder.Language.Term.var x)

/-- `x` is the blank symbol, as a formula. -/
def tqBlankF (x : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₁ tqBlankSym (FirstOrder.Language.Term.var x)

/-- `x` moves the head right, as a formula. -/
def tqRightF (x : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₁ tqRightSym (FirstOrder.Language.Term.var x)

/-- `x ≤ y`, as a formula. -/
def tqLeF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₂ tqLeSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- `x = y`, as a formula. -/
def tqEqF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The transition `x` applies in the state `y`, as a formula. -/
def tqSrcF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₂ tqSrcSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The transition `x` reads the symbol `y`, as a formula. -/
def tqReadF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₂ tqReadSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The transition `x` moves to the state `y`, as a formula. -/
def tqDstF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₂ tqDstSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The transition `x` writes the symbol `y`, as a formula. -/
def tqWriteF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₂ tqWriteSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The cell `x` initially holds `y`, as a formula. -/
def tqInpF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₂ tqInpSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The state at time `x` is `y`, as a formula. -/
def tqStateF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₂ tqStateSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The head at time `x` is on `y`, as a formula. -/
def tqHeadF (x y : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula₂ tqHeadSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- At time `x` the cell `y` holds `z`, as a formula. -/
def tqTapeF (x y z : α) : tqSOLang.Formula α := FirstOrder.Language.Relations.formula tqTapeSym
                                                    ![FirstOrder.Language.Term.var x, FirstOrder.Language.Term.var y, FirstOrder.Language.Term.var z]

/-- `x` is the lowest position, as a formula. -/
noncomputable def tqMinPosF (x : α) : tqSOLang.Formula α :=
  tqPosnF x ⊓ FirstOrder.Language.Formula.iAlls (Fin 1) ((tqPosnF (Sum.inr 0)).imp (tqLeF (Sum.inl x) (Sum.inr 0)))

/-- `x` is the highest position, as a formula. -/
noncomputable def tqMaxPosF (x : α) : tqSOLang.Formula α :=
  tqPosnF x ⊓ FirstOrder.Language.Formula.iAlls (Fin 1) ((tqPosnF (Sum.inr 0)).imp (tqLeF (Sum.inr 0) (Sum.inl x)))

/-- `y` is the position immediately above `x`, as a formula. -/
noncomputable def tqSuccPosF (x y : α) : tqSOLang.Formula α :=
  tqPosnF x ⊓
      (tqPosnF y ⊓
        (tqLeF x y ⊓
          (FirstOrder.Language.BoundedFormula.not (tqEqF x y) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 1)
              ((tqPosnF (Sum.inr 0) ⊓ (tqLeF (Sum.inl x) (Sum.inr 0) ⊓ tqLeF (Sum.inr 0) (Sum.inl y))).imp
                (tqEqF (Sum.inr 0) (Sum.inl x) ⊔ tqEqF (Sum.inr 0) (Sum.inl y))))))

/-- The head moves from its cell at `t` to its cell at `t'`, in the direction
`dir`. -/
noncomputable def tqMoveF (t t' : α) (dir : Bool) : tqSOLang.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((tqHeadF (Sum.inl t) (Sum.inr 0) ⊓ tqHeadF (Sum.inl t') (Sum.inr 1)).imp
        (if dir then tqSuccPosF (Sum.inr 0) (Sum.inr 1) else tqSuccPosF (Sum.inr 1) (Sum.inr 0)))

/-- **The step body**: the transition `τ` takes the configuration at `t` to the
one at `t'`. Its seven conjuncts are those of `DescriptiveComplexity.TMData.RelStep`. -/
noncomputable def tqStepBodyF (t t' τ : α) : tqSOLang.Formula α :=
  tqTrF τ ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 1) ((tqStateF (Sum.inl t) (Sum.inr 0)).imp (tqSrcF (Sum.inl τ) (Sum.inr 0))) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 2)
            ((tqHeadF (Sum.inl t) (Sum.inr 0) ⊓ tqTapeF (Sum.inl t) (Sum.inr 0) (Sum.inr 1)).imp
              (tqReadF (Sum.inl τ) (Sum.inr 1))) ⊓
          (FirstOrder.Language.Formula.iAlls (Fin 1)
              ((tqStateF (Sum.inl t') (Sum.inr 0)).imp (tqDstF (Sum.inl τ) (Sum.inr 0))) ⊓
            (FirstOrder.Language.Formula.iAlls (Fin 2)
                ((tqHeadF (Sum.inl t) (Sum.inr 0) ⊓ tqTapeF (Sum.inl t') (Sum.inr 0) (Sum.inr 1)).imp
                  (tqWriteF (Sum.inl τ) (Sum.inr 1))) ⊓
              (FirstOrder.Language.Formula.iAlls (Fin 2)
                  ((FirstOrder.Language.BoundedFormula.not (tqHeadF (Sum.inl t) (Sum.inr 0))).imp
                    ((tqTapeF (Sum.inl t) (Sum.inr 0) (Sum.inr 1)).iff (tqTapeF (Sum.inl t') (Sum.inr 0) (Sum.inr 1)))) ⊓
                (tqRightF τ ⊓ (tqMoveF t t' true) ⊔
                  FirstOrder.Language.BoundedFormula.not (tqRightF τ) ⊓ (tqMoveF t t' false)))))))

/-- **The stutter body**: an accepting configuration repeated. -/
noncomputable def tqStutterBodyF (t t' : α) : tqSOLang.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1) ((tqStateF (Sum.inl t) (Sum.inr 0)).imp (tqAccF (Sum.inr 0))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 1)
          ((tqStateF (Sum.inl t') (Sum.inr 0)).iff (tqStateF (Sum.inl t) (Sum.inr 0))) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 1)
            ((tqHeadF (Sum.inl t') (Sum.inr 0)).iff (tqHeadF (Sum.inl t) (Sum.inr 0))) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 2)
            ((tqTapeF (Sum.inl t') (Sum.inr 0) (Sum.inr 1)).iff (tqTapeF (Sum.inl t) (Sum.inr 0) (Sum.inr 1)))))

/-- The cell `x` may initially hold `y`: the input where it is defined, the
blank elsewhere. -/
noncomputable def tqInitTapeF (x y : α) : tqSOLang.Formula α :=
  tqInpF x y ⊔
      FirstOrder.Language.Formula.iAlls (Fin 1) (FirstOrder.Language.BoundedFormula.not (tqInpF (Sum.inl x) (Sum.inr 0))) ⊓
        tqBlankF y

end Builders

/-! ### Realization of the builders -/

section Realize

variable {A : Type} [Lax904597.Machines.turing.Structure A] (ρ : tmGuessBlock.Assignment A)

/-- The structure the kernel is read in: the instance expanded by the guess. -/
local notation "SOStruc" => @sumStructure Lax904597.Machines.turing tmGuessBlock.lang A _
  (tmGuessBlock.structure ρ)

variable {α : Type} (v : α → A)

@[simp] theorem realize_tqPosnF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqPosnF x) v) ↔ Lax904597.Machines.TMPosn (v x) := by
  let := tmGuessBlock.structure ρ
  simp [tqPosnF, Lax904597.Machines.TMPosn, Language.relMap_sumInl]

@[simp] theorem realize_tqTrF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqTrF x) v) ↔ Lax904597.Machines.TMTr (v x) := by
  let := tmGuessBlock.structure ρ
  simp [tqTrF, Lax904597.Machines.TMTr, Language.relMap_sumInl]

@[simp] theorem realize_tqStartF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqStartF x) v) ↔ Lax904597.Machines.TMStart (v x) := by
  let := tmGuessBlock.structure ρ
  simp [tqStartF, Lax904597.Machines.TMStart, Language.relMap_sumInl]

@[simp] theorem realize_tqAccF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqAccF x) v) ↔ Lax904597.Machines.TMAcc (v x) := by
  let := tmGuessBlock.structure ρ
  simp [tqAccF, Lax904597.Machines.TMAcc, Language.relMap_sumInl]

@[simp] theorem realize_tqBlankF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqBlankF x) v) ↔ Lax904597.Machines.TMBlank (v x) := by
  let := tmGuessBlock.structure ρ
  simp [tqBlankF, Lax904597.Machines.TMBlank, Language.relMap_sumInl]

@[simp] theorem realize_tqRightF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqRightF x) v) ↔ Lax904597.Machines.TMRight (v x) := by
  let := tmGuessBlock.structure ρ
  simp [tqRightF, Lax904597.Machines.TMRight, Language.relMap_sumInl]

@[simp] theorem realize_tqLeF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqLeF x y) v) ↔ Lax904597.Machines.TMLe (v x) (v y) := by
  let := tmGuessBlock.structure ρ
  simp [tqLeF, Lax904597.Machines.TMLe, Language.relMap_sumInl]

@[simp] theorem realize_tqEqF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqEqF x y) v) ↔ v x = v y := by
  let := tmGuessBlock.structure ρ
  simp [tqEqF]

@[simp] theorem realize_tqSrcF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqSrcF x y) v) ↔ Lax904597.Machines.TMSrc (v x) (v y) := by
  let := tmGuessBlock.structure ρ
  simp [tqSrcF, Lax904597.Machines.TMSrc, Language.relMap_sumInl]

@[simp] theorem realize_tqReadF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqReadF x y) v) ↔ Lax904597.Machines.TMRead (v x) (v y) := by
  let := tmGuessBlock.structure ρ
  simp [tqReadF, Lax904597.Machines.TMRead, Language.relMap_sumInl]

@[simp] theorem realize_tqDstF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqDstF x y) v) ↔ Lax904597.Machines.TMDst (v x) (v y) := by
  let := tmGuessBlock.structure ρ
  simp [tqDstF, Lax904597.Machines.TMDst, Language.relMap_sumInl]

@[simp] theorem realize_tqWriteF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqWriteF x y) v) ↔ Lax904597.Machines.TMWrite (v x) (v y) := by
  let := tmGuessBlock.structure ρ
  simp [tqWriteF, Lax904597.Machines.TMWrite, Language.relMap_sumInl]

@[simp] theorem realize_tqInpF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqInpF x y) v) ↔ Lax904597.Machines.TMInp (v x) (v y) := by
  let := tmGuessBlock.structure ρ
  simp [tqInpF, Lax904597.Machines.TMInp, Language.relMap_sumInl]

@[simp] theorem realize_tqStateF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqStateF x y) v) ↔ ρ .state ![v x, v y] := by
  let := tmGuessBlock.structure ρ
  simp only [tqStateF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_tqHeadF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqHeadF x y) v) ↔ ρ .head ![v x, v y] := by
  let := tmGuessBlock.structure ρ
  simp only [tqHeadF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_tqTapeF (x y z : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqTapeF x y z) v) ↔
      ρ .tape ![v x, v y, v z] := by
  let := tmGuessBlock.structure ρ
  simp only [tqTapeF, Formula.realize_rel, Language.relMap_sumInr]
  exact iff_of_eq (congrArg (ρ TMIdx.tape) (funext fun i => by fin_cases i <;> rfl))

@[simp] theorem realize_tqMinPosF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqMinPosF x) v) ↔
      Lax904597.Machines.MinPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn (v x) := by
  let := tmGuessBlock.structure ρ
  simp only [tqMinPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_tqPosnF, realize_tqLeF, Sum.elim_inl, Sum.elim_inr, Lax904597.Machines.MinPos]
  exact and_congr Iff.rfl ⟨fun h a => h (fun _ => a), fun h i => h (i 0)⟩

@[simp] theorem realize_tqMaxPosF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqMaxPosF x) v) ↔
      MaxPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn (v x) := by
  let := tmGuessBlock.structure ρ
  simp only [tqMaxPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_tqPosnF, realize_tqLeF, Sum.elim_inl, Sum.elim_inr, MaxPos]
  exact and_congr Iff.rfl ⟨fun h a => h (fun _ => a), fun h i => h (i 0)⟩

@[simp] theorem realize_tqSuccPosF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqSuccPosF x y) v) ↔
      Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn (v x) (v y) := by
  let := tmGuessBlock.structure ρ
  simp only [tqSuccPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_sup, realize_tqPosnF, realize_tqLeF, realize_tqEqF,
    Sum.elim_inl, Sum.elim_inr, Lax904597.Machines.SuccPos, ne_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  exact ⟨fun h a ha h₁ h₂ => h (fun _ => a) ⟨ha, h₁, h₂⟩,
    fun h i hi => h (i 0) hi.1 hi.2.1 hi.2.2⟩

@[simp] theorem realize_tqInitTapeF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqInitTapeF x y) v) ↔
      Lax904597.Machines.TMInp (v x) (v y) ∨ ((∀ b, ¬ Lax904597.Machines.TMInp (v x) b) ∧ Lax904597.Machines.TMBlank (v y)) := by
  let := tmGuessBlock.structure ρ
  simp only [tqInitTapeF, Formula.realize_sup, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_not, realize_tqInpF, realize_tqBlankF, Sum.elim_inl, Sum.elim_inr]
  exact or_congr Iff.rfl (and_congr ⟨fun h b => h fun _ => b, fun h i => h (i 0)⟩ Iff.rfl)

@[simp] theorem realize_tqMoveF (t t' : α) (dir : Bool) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqMoveF t t' dir) v) ↔
      ∀ p p', ρ .head ![v t, p] → ρ .head ![v t', p'] →
        (if dir then Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p p' else Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p' p) := by
  let := tmGuessBlock.structure ρ
  cases dir <;>
    simp only [tqMoveF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      realize_tqHeadF, realize_tqSuccPosF, Sum.elim_inl, Sum.elim_inr, if_true, if_false,
      Bool.false_eq_true] <;>
    exact ⟨fun h p p' h₁ h₂ => h ![p, p'] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

theorem realize_tqStepBodyF (t t' τ : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqStepBodyF t t' τ) v) ↔
      Lax904597.Machines.TMTr (v τ) ∧ (∀ q, ρ .state ![v t, q] → Lax904597.Machines.TMSrc (v τ) q) ∧
        (∀ p a, ρ .head ![v t, p] → ρ .tape ![v t, p, a] → Lax904597.Machines.TMRead (v τ) a) ∧
        (∀ q, ρ .state ![v t', q] → Lax904597.Machines.TMDst (v τ) q) ∧
        (∀ p a, ρ .head ![v t, p] → ρ .tape ![v t', p, a] → Lax904597.Machines.TMWrite (v τ) a) ∧
        (∀ p a, ¬ ρ .head ![v t, p] → (ρ .tape ![v t, p, a] ↔ ρ .tape ![v t', p, a])) ∧
        ((Lax904597.Machines.TMRight (v τ) ∧ ∀ p p', ρ .head ![v t, p] → ρ .head ![v t', p'] →
            Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p p') ∨
          (¬ Lax904597.Machines.TMRight (v τ) ∧ ∀ p p', ρ .head ![v t, p] → ρ .head ![v t', p'] →
            Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p' p)) := by
  let := tmGuessBlock.structure ρ
  simp only [tqStepBodyF, Formula.realize_inf, Formula.realize_sup, Formula.realize_imp,
    Formula.realize_not, Formula.realize_iff, Formula.realize_iAlls, realize_tqTrF,
    realize_tqStateF, realize_tqSrcF, realize_tqHeadF, realize_tqTapeF, realize_tqReadF,
    realize_tqDstF, realize_tqWriteF, realize_tqRightF, realize_tqMoveF, Sum.elim_inl,
    Sum.elim_inr, if_true, if_false, Bool.false_eq_true]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_
    (and_congr ?_ Iff.rfl)))))
  · exact ⟨fun h q hq => h (fun _ => q) hq, fun h i hi => h (i 0) hi⟩
  · exact ⟨fun h p a h₁ h₂ => h ![p, a] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩
  · exact ⟨fun h q hq => h (fun _ => q) hq, fun h i hi => h (i 0) hi⟩
  · exact ⟨fun h p a h₁ h₂ => h ![p, a] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩
  · exact ⟨fun h p a hp => h ![p, a] hp, fun h i hi => h (i 0) (i 1) hi⟩

theorem realize_tqStutterBodyF (t t' : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqStutterBodyF t t') v) ↔
      (∀ q, ρ .state ![v t, q] → Lax904597.Machines.TMAcc q) ∧
        (∀ q, ρ .state ![v t', q] ↔ ρ .state ![v t, q]) ∧
        (∀ p, ρ .head ![v t', p] ↔ ρ .head ![v t, p]) ∧
        ∀ p a, ρ .tape ![v t', p, a] ↔ ρ .tape ![v t, p, a] := by
  let := tmGuessBlock.structure ρ
  simp only [tqStutterBodyF, Formula.realize_inf, Formula.realize_imp, Formula.realize_iff,
    Formula.realize_iAlls, realize_tqStateF, realize_tqAccF, realize_tqHeadF, realize_tqTapeF,
    Sum.elim_inl, Sum.elim_inr]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun h q hq => h (fun _ => q) hq, fun h i hi => h (i 0) hi⟩
  · exact ⟨fun h q => h fun _ => q, fun h i => h (i 0)⟩
  · exact ⟨fun h p => h fun _ => p, fun h i => h (i 0)⟩
  · exact ⟨fun h p a => h ![p, a], fun h i => h (i 0) (i 1)⟩

end Realize

/-! ### The clauses of the kernel

Each mirrors one field of `DescriptiveComplexity.TMData.RelWalk`. -/

section Clauses

/-- There is a state at each time. -/
noncomputable def tqStateExClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.Formula.iExs (Fin 1) (tqStateF (Sum.inl (Sum.inr 0)) (Sum.inr 0)))

/-- There is only one state at each time. -/
noncomputable def tqStateUniqClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((tqStateF (Sum.inr 0) (Sum.inr 1) ⊓ tqStateF (Sum.inr 0) (Sum.inr 2)).imp (tqEqF (Sum.inr 1) (Sum.inr 2)))

/-- The head is somewhere at each time. -/
noncomputable def tqHeadExClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.Formula.iExs (Fin 1) (tqHeadF (Sum.inl (Sum.inr 0)) (Sum.inr 0)))

/-- The head is in only one place at each time. -/
noncomputable def tqHeadUniqClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((tqHeadF (Sum.inr 0) (Sum.inr 1) ⊓ tqHeadF (Sum.inr 0) (Sum.inr 2)).imp (tqEqF (Sum.inr 1) (Sum.inr 2)))

/-- Every cell holds a symbol at each time. -/
noncomputable def tqTapeExClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      (FirstOrder.Language.Formula.iExs (Fin 1) (tqTapeF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1)) (Sum.inr 0)))

/-- Every cell holds only one symbol at each time. -/
noncomputable def tqTapeUniqClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
      ((tqTapeF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ tqTapeF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3)).imp
        (tqEqF (Sum.inr 2) (Sum.inr 3)))

/-- Consecutive times are related by a step or by an accepting stutter. -/
noncomputable def tqStepClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((tqSuccPosF (Sum.inr 0) (Sum.inr 1)).imp
        (FirstOrder.Language.Formula.iExs (Fin 1) (tqStepBodyF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1)) (Sum.inr 0)) ⊔
          tqStutterBodyF (Sum.inr 0) (Sum.inr 1)))

/-- At the lowest time the configuration is initial. -/
noncomputable def tqInitClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((tqMinPosF (Sum.inr 0)).imp
        (FirstOrder.Language.Formula.iAlls (Fin 1)
            ((tqStateF (Sum.inl (Sum.inr 0)) (Sum.inr 0)).imp (tqStartF (Sum.inr 0))) ⊓
          (FirstOrder.Language.Formula.iAlls (Fin 1)
              ((tqHeadF (Sum.inl (Sum.inr 0)) (Sum.inr 0)).imp (tqMinPosF (Sum.inr 0))) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 2)
              ((tqTapeF (Sum.inl (Sum.inr 0)) (Sum.inr 0) (Sum.inr 1)).imp (tqInitTapeF (Sum.inr 0) (Sum.inr 1))))))

/-- The order is reflexive. -/
noncomputable def tqReflClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (tqLeF (Sum.inr 0) (Sum.inr 0))

/-- The order is transitive. -/
noncomputable def tqTransClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((tqLeF (Sum.inr 0) (Sum.inr 1) ⊓ tqLeF (Sum.inr 1) (Sum.inr 2)).imp (tqLeF (Sum.inr 0) (Sum.inr 2)))

/-- The order is antisymmetric. -/
noncomputable def tqAntisymClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((tqLeF (Sum.inr 0) (Sum.inr 1) ⊓ tqLeF (Sum.inr 1) (Sum.inr 0)).imp (tqEqF (Sum.inr 0) (Sum.inr 1)))

/-- The order is total. -/
noncomputable def tqTotalClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2) (tqLeF (Sum.inr 0) (Sum.inr 1) ⊔ tqLeF (Sum.inr 1) (Sum.inr 0))

/-- There is a position. -/
noncomputable def tqPosnExClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 1) (tqPosnF (Sum.inr 0))

/-- The input is functional. -/
noncomputable def tqInpFunClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((tqInpF (Sum.inr 0) (Sum.inr 1) ⊓ tqInpF (Sum.inr 0) (Sum.inr 2)).imp (tqEqF (Sum.inr 1) (Sum.inr 2)))

/-- There is a blank symbol. -/
noncomputable def tqBlankExClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 1) (tqBlankF (Sum.inr 0))

/-- There is only one blank symbol. -/
noncomputable def tqBlankUniqClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((tqBlankF (Sum.inr 0) ⊓ tqBlankF (Sum.inr 1)).imp (tqEqF (Sum.inr 0) (Sum.inr 1)))

/-- At the highest time the state is accepting. -/
noncomputable def tqAccClause : tqSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((tqMaxPosF (Sum.inr 0) ⊓ tqStateF (Sum.inr 0) (Sum.inr 1)).imp (tqAccF (Sum.inr 1)))

/-- **The kernel**: well-formedness of the instance, then that the guess is a
run – the six functionality clauses, the initial clause, the step clause and
the accepting clause. -/
noncomputable def tqKernel : tqSOLang.Sentence :=
  tqReflClause ⊓ (tqTransClause ⊓ (tqAntisymClause ⊓ (tqTotalClause ⊓
    (tqPosnExClause ⊓ (tqInpFunClause ⊓ (tqBlankExClause ⊓ (tqBlankUniqClause ⊓
      (tqStateExClause ⊓ (tqStateUniqClause ⊓ (tqHeadExClause ⊓ (tqHeadUniqClause ⊓
        (tqTapeExClause ⊓ (tqTapeUniqClause ⊓ (tqInitClause ⊓
          (tqStepClause ⊓ tqAccClause)))))))))))))))

end Clauses

section RealizeClauses

variable {A : Type} [Lax904597.Machines.turing.Structure A] (ρ : tmGuessBlock.Assignment A)

local notation "SOStruc" => @sumStructure Lax904597.Machines.turing tmGuessBlock.lang A _
  (tmGuessBlock.structure ρ)

theorem realize_tqStateExClause :
    (@Sentence.Realize tqSOLang A SOStruc tqStateExClause) ↔
      ∀ t, ∃ q, ρ .state ![t, q] := by
  simp only [tqStateExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_tqStateF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h t
    obtain ⟨i, hi⟩ := h fun _ => t
    exact ⟨i 0, by simpa using hi⟩
  · intro h i
    obtain ⟨q, hq⟩ := h (i 0)
    exact ⟨fun _ => q, by simpa using hq⟩

theorem realize_tqStateUniqClause :
    (@Sentence.Realize tqSOLang A SOStruc tqStateUniqClause) ↔
      ∀ t q q', ρ .state ![t, q] → ρ .state ![t, q'] → q = q' := by
  simp only [tqStateUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqStateF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h t q q' h₁ h₂ => h ![t, q, q'] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

theorem realize_tqHeadExClause :
    (@Sentence.Realize tqSOLang A SOStruc tqHeadExClause) ↔
      ∀ t, ∃ p, ρ .head ![t, p] := by
  simp only [tqHeadExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_tqHeadF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h t
    obtain ⟨i, hi⟩ := h fun _ => t
    exact ⟨i 0, by simpa using hi⟩
  · intro h i
    obtain ⟨q, hq⟩ := h (i 0)
    exact ⟨fun _ => q, by simpa using hq⟩

theorem realize_tqHeadUniqClause :
    (@Sentence.Realize tqSOLang A SOStruc tqHeadUniqClause) ↔
      ∀ t p p', ρ .head ![t, p] → ρ .head ![t, p'] → p = p' := by
  simp only [tqHeadUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqHeadF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h t p p' h₁ h₂ => h ![t, p, p'] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

theorem realize_tqTapeExClause :
    (@Sentence.Realize tqSOLang A SOStruc tqTapeExClause) ↔
      ∀ t p, ∃ a, ρ .tape ![t, p, a] := by
  simp only [tqTapeExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_tqTapeF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h t p
    obtain ⟨i, hi⟩ := h ![t, p]
    exact ⟨i 0, by simpa using hi⟩
  · intro h i
    obtain ⟨a, ha⟩ := h (i 0) (i 1)
    exact ⟨fun _ => a, by simpa using ha⟩

theorem realize_tqTapeUniqClause :
    (@Sentence.Realize tqSOLang A SOStruc tqTapeUniqClause) ↔
      ∀ t p a a', ρ .tape ![t, p, a] → ρ .tape ![t, p, a'] → a = a' := by
  simp only [tqTapeUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqTapeF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h t p a a' h₁ h₂ => h ![t, p, a, a'] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) (i 3) hi.1 hi.2⟩

theorem realize_tqAccClause :
    (@Sentence.Realize tqSOLang A SOStruc tqAccClause) ↔
      ∀ t, MaxPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn t → ∀ q, ρ .state ![t, q] → Lax904597.Machines.TMAcc q := by
  simp only [tqAccClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqMaxPosF, realize_tqStateF, realize_tqAccF, Sum.elim_inr]
  exact ⟨fun h t ht q hq => h ![t, q] ⟨ht, hq⟩,
    fun h i hi => h (i 0) hi.1 (i 1) hi.2⟩

theorem realize_tqInitClause :
    (@Sentence.Realize tqSOLang A SOStruc tqInitClause) ↔
      ∀ t, Lax904597.Machines.MinPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn t →
        (∀ q, ρ .state ![t, q] → Lax904597.Machines.TMStart q) ∧
          (∀ p, ρ .head ![t, p] → Lax904597.Machines.MinPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p) ∧
            ∀ p a, ρ .tape ![t, p, a] → Lax904597.Machines.TMInp p a ∨ ((∀ b, ¬ Lax904597.Machines.TMInp p b) ∧ Lax904597.Machines.TMBlank a) := by
  simp only [tqInitClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqMinPosF, realize_tqStateF, realize_tqStartF,
    realize_tqHeadF, realize_tqTapeF, realize_tqInitTapeF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h t ht
    obtain ⟨h1, h2, h3⟩ := h (fun _ => t) ht
    exact ⟨fun q hq => h1 (fun _ => q) hq, fun p hp => h2 (fun _ => p) hp,
      fun p a hpa => h3 ![p, a] (by simpa using hpa)⟩
  · intro h i hi
    obtain ⟨h1, h2, h3⟩ := h (i 0) hi
    exact ⟨fun j hj => h1 (j 0) hj, fun j hj => h2 (j 0) hj, fun j hj => h3 (j 0) (j 1) hj⟩

theorem realize_tqReflClause :
    (@Sentence.Realize tqSOLang A SOStruc tqReflClause) ↔ ∀ a : A, Lax904597.Machines.TMLe a a := by
  simp only [tqReflClause, Sentence.Realize, Formula.realize_iAlls, realize_tqLeF, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

theorem realize_tqTransClause :
    (@Sentence.Realize tqSOLang A SOStruc tqTransClause) ↔
      ∀ a b c : A, Lax904597.Machines.TMLe a b → Lax904597.Machines.TMLe b c → Lax904597.Machines.TMLe a c := by
  simp only [tqTransClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqLeF, Sum.elim_inr]
  exact ⟨fun h a b c h₁ h₂ => h ![a, b, c] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

theorem realize_tqAntisymClause :
    (@Sentence.Realize tqSOLang A SOStruc tqAntisymClause) ↔
      ∀ a b : A, Lax904597.Machines.TMLe a b → Lax904597.Machines.TMLe b a → a = b := by
  simp only [tqAntisymClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqLeF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h a b h₁ h₂ => h ![a, b] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

theorem realize_tqTotalClause :
    (@Sentence.Realize tqSOLang A SOStruc tqTotalClause) ↔
      ∀ a b : A, Lax904597.Machines.TMLe a b ∨ Lax904597.Machines.TMLe b a := by
  simp only [tqTotalClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_sup,
    realize_tqLeF, Sum.elim_inr]
  exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩

theorem realize_tqPosnExClause :
    (@Sentence.Realize tqSOLang A SOStruc tqPosnExClause) ↔ ∃ p : A, Lax904597.Machines.TMPosn p := by
  simp only [tqPosnExClause, Sentence.Realize, Formula.realize_iExs, realize_tqPosnF,
    Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩

theorem realize_tqInpFunClause :
    (@Sentence.Realize tqSOLang A SOStruc tqInpFunClause) ↔
      ∀ p a b : A, Lax904597.Machines.TMInp p a → Lax904597.Machines.TMInp p b → a = b := by
  simp only [tqInpFunClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqInpF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h p a b h₁ h₂ => h ![p, a, b] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

theorem realize_tqBlankExClause :
    (@Sentence.Realize tqSOLang A SOStruc tqBlankExClause) ↔ ∃ b : A, Lax904597.Machines.TMBlank b := by
  simp only [tqBlankExClause, Sentence.Realize, Formula.realize_iExs, realize_tqBlankF,
    Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩

theorem realize_tqBlankUniqClause :
    (@Sentence.Realize tqSOLang A SOStruc tqBlankUniqClause) ↔
      ∀ a b : A, Lax904597.Machines.TMBlank a → Lax904597.Machines.TMBlank b → a = b := by
  simp only [tqBlankUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqBlankF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h a b h₁ h₂ => h ![a, b] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

theorem realize_tqStepClause :
    (@Sentence.Realize tqSOLang A SOStruc tqStepClause) ↔
      ∀ t t', Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn t t' →
        (∃ τ, Lax904597.Machines.TMTr τ ∧ (∀ q, ρ .state ![t, q] → Lax904597.Machines.TMSrc τ q) ∧
            (∀ p a, ρ .head ![t, p] → ρ .tape ![t, p, a] → Lax904597.Machines.TMRead τ a) ∧
            (∀ q, ρ .state ![t', q] → Lax904597.Machines.TMDst τ q) ∧
            (∀ p a, ρ .head ![t, p] → ρ .tape ![t', p, a] → Lax904597.Machines.TMWrite τ a) ∧
            (∀ p a, ¬ ρ .head ![t, p] → (ρ .tape ![t, p, a] ↔ ρ .tape ![t', p, a])) ∧
            ((Lax904597.Machines.TMRight τ ∧ ∀ p p', ρ .head ![t, p] → ρ .head ![t', p'] →
                Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p p') ∨
              (¬ Lax904597.Machines.TMRight τ ∧ ∀ p p', ρ .head ![t, p] → ρ .head ![t', p'] →
                Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p' p))) ∨
          ((∀ q, ρ .state ![t, q] → Lax904597.Machines.TMAcc q) ∧
            (∀ q, ρ .state ![t', q] ↔ ρ .state ![t, q]) ∧
            (∀ p, ρ .head ![t', p] ↔ ρ .head ![t, p]) ∧
            ∀ p a, ρ .tape ![t', p, a] ↔ ρ .tape ![t, p, a]) := by
  simp only [tqStepClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_iExs, realize_tqSuccPosF, realize_tqStepBodyF,
    realize_tqStutterBodyF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h t t' hs
    rcases h ![t, t'] (by simpa using hs) with ⟨i, hi⟩ | hstut
    · exact Or.inl ⟨i 0, by simpa using hi⟩
    · exact Or.inr (by simpa using hstut)
  · intro h i hi
    rcases h (i 0) (i 1) hi with ⟨τ, hτ⟩ | hstut
    · exact Or.inl ⟨fun _ => τ, hτ⟩
    · exact Or.inr hstut

private theorem realize_inf_sentence (φ ψ : tqSOLang.Sentence) :
    (@Sentence.Realize tqSOLang A SOStruc (φ ⊓ ψ)) ↔
      (@Sentence.Realize tqSOLang A SOStruc φ) ∧ (@Sentence.Realize tqSOLang A SOStruc ψ) := by
  let := tmGuessBlock.structure ρ
  exact Formula.realize_inf

/-- **The kernel says exactly what it should**: the instance is well formed and
the guessed relations are a run. -/
theorem realize_tqKernel :
    (@Sentence.Realize tqSOLang A SOStruc tqKernel) ↔
      (Lax904597.Machines.tmData A).WellFormed ∧
        (Lax904597.Machines.tmData A).RelWalk (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
          (fun t p a => ρ .tape ![t, p, a]) := by
  simp only [tqKernel, realize_inf_sentence, realize_tqReflClause, realize_tqTransClause,
    realize_tqAntisymClause, realize_tqTotalClause, realize_tqPosnExClause,
    realize_tqInpFunClause, realize_tqBlankExClause, realize_tqBlankUniqClause,
    realize_tqStateExClause, realize_tqStateUniqClause, realize_tqHeadExClause,
    realize_tqHeadUniqClause, realize_tqTapeExClause, realize_tqTapeUniqClause,
    realize_tqInitClause, realize_tqStepClause, realize_tqAccClause]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
    exact ⟨⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16, h17⟩⟩
  · rintro ⟨⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩, hw⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, hw.qex, hw.quniq, hw.hex, hw.huniq, hw.tex,
      hw.tuniq, hw.init, hw.step, hw.acc⟩

end RealizeClauses

/-! ### The definability theorems -/

/-- **Machine acceptance is `Σ₁`-definable**: one existential block guesses the
run – the state, the head cell and the tape contents at each time – and the
first-order kernel checks that it is one. -/
theorem ntmAccept_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 NTMAccept := by
  refine ⟨[tmGuessBlock], rfl, tqKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨hwf, hacc⟩
    obtain ⟨Q, H, T, hrel⟩ := TMData.exists_relWalk_iff_exists_walk.mpr
      ((TMData.accepts_iff_exists_walk hwf).mp hacc)
    refine ⟨fun i => match i with
      | .state => fun w : Fin 2 → A => Q (w 0) (w 1)
      | .head => fun w : Fin 2 → A => H (w 0) (w 1)
      | .tape => fun w : Fin 3 → A => T (w 0) (w 1) (w 2), ?_⟩
    exact (realize_tqKernel _).mpr ⟨hwf, hrel⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hwf, hrel⟩ := (realize_tqKernel ρ).mp hρ
    exact ⟨hwf, (TMData.accepts_iff_exists_walk hwf).mpr
      (TMData.exists_relWalk_iff_exists_walk.mp ⟨_, _, _, hrel⟩)⟩

/-- **Machine acceptance is in NP.** -/
theorem ntmAccept_mem_NP : NTMAccept ∈ NP := ntmAccept_sigmaSODefinable

end Lax564036Proofs.DescriptiveComplexity


