/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.QsatGeom
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

namespace Lax134656.Qsat
end Lax134656.Qsat

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax134656.Qsat (qsat)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config SuccPos)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.Qsat (IsQVar QsatWf)
end Lax822549Proofs.DescriptiveComplexity

/-!
# One step of the QBF machine

The transition table of `DescriptiveComplexity.Problems.Machine.QsatProgram` says
which tuples *are* transitions; this file says what they *do*. There is one
lemma per line of the program, each of the shape

> in this state, at this cell, reading this symbol, the machine steps to that
> state, that cell, and that tape

with the movement supplied as a `DescriptiveComplexity.SuccPos` hypothesis, so that
the boundary cases – the outermost variable, the innermost one, the degenerate
instance with no variable at all – are handled by passing a different lemma of
`DescriptiveComplexity.Problems.Machine.QsatGeom` rather than by duplicating each
line of the program.

The tape after a step is never built here either: it is an arbitrary `σ'`
required to hold the written symbol at the head and to agree with `σ`
everywhere else, which is exactly what `DescriptiveComplexity.TMData.Step` asks
and what the run induction will supply.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QsatTM

noncomputable section Steps

variable {A : Type} [Lax134656.Qsat.qsat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable {σ σ' : QV A → QV A} {p' : QV A}

/-- The marker a sweep in direction `d` ends at, as a position. -/
abbrev markerPos (d : Bool) : QV A := if d then posEnd else posStart

/-! ### Descending -/

/-- **Descent, over the left marker.** -/
theorem step_descStart (hσ : σ posStart = symStart)
    (hnext : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn posStart p') :
    (qsatMachine A).Step ⟨stDesc, posStart, σ⟩ ⟨stDesc, p', σ⟩ :=
  ⟨qCst .tDescStart, isMinTup_qBot, rfl, hσ, rfl, hσ, fun _ _ => rfl,
    Or.inl ⟨trivial, hnext⟩⟩

/-- **Descent, at a variable's cell**: reset it and move on. -/
theorem step_descCell {x : A} (hx : Lax134656.Qsat.IsQVar x) {b f : Bool}
    (hσ : σ (posCell x) = symV b f x) (hw : σ' (posCell x) = symV false false x)
    (hfr : ∀ r, r ≠ posCell x → σ' r = σ r)
    (hnext : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn (posCell x) p') :
    (qsatMachine A).Step ⟨stDesc, posCell x, σ⟩ ⟨stDesc, p', σ'⟩ :=
  ⟨qOne (.tDescCell b f) x, ⟨hx, fun a => qBot_le a⟩, rfl, hσ, rfl, hw, hfr,
    Or.inl ⟨trivial, hnext⟩⟩

/-- **Descent over, with an empty matrix**: it is true, so start returning. -/
theorem step_descEndTrue (hno : ∀ e : A, ¬QCl e) (hσ : σ posEnd = symEnd)
    (hprev : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn p' posEnd) :
    (qsatMachine A).Step ⟨stDesc, posEnd, σ⟩ ⟨stProc true, p', σ⟩ :=
  ⟨qCst .tDescEndTrue, ⟨isMinTup_qBot, hno⟩, rfl, hσ, rfl, hσ, fun _ _ => rfl,
    Or.inr ⟨not_false, hprev⟩⟩

/-- **Descent over**: start evaluating the matrix at its lowest clause. -/
theorem step_descEndEval {c : A} (hc : QMinCl c) (hσ : σ posEnd = symEnd)
    (hprev : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn p' posEnd) :
    (qsatMachine A).Step ⟨stDesc, posEnd, σ⟩ ⟨stEval false false c, p', σ⟩ :=
  ⟨qOne .tDescEndEval c, ⟨hc, fun a => qBot_le a⟩, rfl, hσ, rfl, hσ, fun _ _ => rfl,
    Or.inr ⟨not_false, hprev⟩⟩

/-! ### Evaluating the matrix -/

/-- The movement of an evaluation sweep, in its own direction. -/
def SweepMove (d : Bool) (p q : QV A) : Prop :=
  (d = true ∧ Lax904597.Machines.SuccPos (QLe (A := A)) QPosn p q) ∨ (d = false ∧ Lax904597.Machines.SuccPos (QLe (A := A)) QPosn q p)

/-- **A sweep step that sets the flag**: either it was already set, or the
literal at this cell satisfies the clause. -/
theorem step_eval_true {c x : A} (hc : QCl c) (hx : Lax134656.Qsat.IsQVar x) {b f fl d : Bool}
    (hlit : fl = true ∨ QLit c x b) (hσ : σ (posCell x) = symV b f x)
    (hmove : SweepMove d (posCell x) p') :
    (qsatMachine A).Step ⟨stEval fl d c, posCell x, σ⟩ ⟨stEval true d c, p', σ⟩ := by
  refine ⟨(.tEval b f fl d, ![c, x]), ⟨hc, hx⟩, rfl, hσ, Or.inl ⟨rfl, hlit⟩, hσ,
    fun _ _ => rfl, ?_⟩
  rcases hmove with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · exact Or.inl ⟨hd, hs⟩
  · refine Or.inr ⟨?_, hs⟩
    first
      | exact fun h => Bool.noConfusion h
      | (subst hd; exact fun h => Bool.noConfusion h)

/-- **A sweep step that leaves the flag down**: it was down and the literal at
this cell does not satisfy the clause. -/
theorem step_eval_false {c x : A} (hc : QCl c) (hx : Lax134656.Qsat.IsQVar x) {b f d : Bool}
    (hlit : ¬QLit c x b) (hσ : σ (posCell x) = symV b f x)
    (hmove : SweepMove d (posCell x) p') :
    (qsatMachine A).Step ⟨stEval false d c, posCell x, σ⟩ ⟨stEval false d c, p', σ⟩ := by
  refine ⟨(.tEval b f false d, ![c, x]), ⟨hc, hx⟩, rfl, hσ, Or.inr ⟨rfl, rfl, hlit⟩, hσ,
    fun _ _ => rfl, ?_⟩
  rcases hmove with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · exact Or.inl ⟨hd, hs⟩
  · refine Or.inr ⟨?_, hs⟩
    first
      | exact fun h => Bool.noConfusion h
      | (subst hd; exact fun h => Bool.noConfusion h)

/-- The movement of a turn, against the direction just swept. -/
def TurnMove (d : Bool) (p q : QV A) : Prop :=
  (d = false ∧ Lax904597.Machines.SuccPos (QLe (A := A)) QPosn p q) ∨ (d = true ∧ Lax904597.Machines.SuccPos (QLe (A := A)) QPosn q p)

/-- **Turn**: the clause is satisfied and another one follows. -/
theorem step_turnNext {c c₂ : A} (hcc : QNextCl c c₂) {d : Bool}
    (hσ : σ (markerPos d) = markerSym d) (hmove : TurnMove d (markerPos (A := A) d) p') :
    (qsatMachine A).Step ⟨stEval true d c, markerPos d, σ⟩ ⟨stEval false (!d) c₂, p', σ⟩ := by
  refine ⟨(.tTurnNext d, ![c, c₂]), hcc, rfl, hσ, rfl, hσ, fun _ _ => rfl, ?_⟩
  rcases hmove with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · exact Or.inl ⟨hd, hs⟩
  · refine Or.inr ⟨?_, hs⟩
    first
      | exact fun h => Bool.noConfusion h
      | (subst hd; exact fun h => Bool.noConfusion h)

/-- **Turn**: the clause is satisfied and it was the last one, so the matrix is
true. -/
theorem step_turnLast {c : A} (hc : QMaxCl c) {d : Bool}
    (hσ : σ (markerPos d) = markerSym d) (hmove : TurnMove d (markerPos (A := A) d) p') :
    (qsatMachine A).Step ⟨stEval true d c, markerPos d, σ⟩ ⟨stToEnd true, p', σ⟩ := by
  refine ⟨qOne (.tTurnLast d) c, ⟨hc, fun a => qBot_le a⟩, rfl, hσ, rfl, hσ,
    fun _ _ => rfl, ?_⟩
  rcases hmove with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · exact Or.inl ⟨hd, hs⟩
  · refine Or.inr ⟨?_, hs⟩
    first
      | exact fun h => Bool.noConfusion h
      | (subst hd; exact fun h => Bool.noConfusion h)

/-- **Turn**: the clause is not satisfied, so the matrix is false. -/
theorem step_turnFalse {c : A} (hc : QCl c) {d : Bool}
    (hσ : σ (markerPos d) = markerSym d) (hmove : TurnMove d (markerPos (A := A) d) p') :
    (qsatMachine A).Step ⟨stEval false d c, markerPos d, σ⟩ ⟨stToEnd false, p', σ⟩ := by
  refine ⟨qOne (.tTurnFalse d) c, ⟨hc, fun a => qBot_le a⟩, rfl, hσ, rfl, hσ,
    fun _ _ => rfl, ?_⟩
  rcases hmove with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · exact Or.inl ⟨hd, hs⟩
  · refine Or.inr ⟨?_, hs⟩
    first
      | exact fun h => Bool.noConfusion h
      | (subst hd; exact fun h => Bool.noConfusion h)

/-! ### Carrying the value to the right marker -/

/-- **Carry**, over a variable's cell. -/
theorem step_toEndCell {x : A} (hx : Lax134656.Qsat.IsQVar x) {v b f : Bool}
    (hσ : σ (posCell x) = symV b f x)
    (hnext : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn (posCell x) p') :
    (qsatMachine A).Step ⟨stToEnd v, posCell x, σ⟩ ⟨stToEnd v, p', σ⟩ :=
  ⟨qOne (.tToEndCell v b f) x, ⟨hx, fun a => qBot_le a⟩, rfl, hσ, rfl, hσ, fun _ _ => rfl,
    Or.inl ⟨trivial, hnext⟩⟩

/-- **Carry**, over the left marker. -/
theorem step_toEndStart {v : Bool} (hσ : σ posStart = symStart)
    (hnext : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn posStart p') :
    (qsatMachine A).Step ⟨stToEnd v, posStart, σ⟩ ⟨stToEnd v, p', σ⟩ :=
  ⟨qCst (.tToEndStart v), isMinTup_qBot, rfl, hσ, rfl, hσ, fun _ _ => rfl,
    Or.inl ⟨trivial, hnext⟩⟩

/-- **Carry over**: the right marker is reached, so turn round and return. -/
theorem step_toEndTurn {v : Bool} (hσ : σ posEnd = symEnd)
    (hprev : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn p' posEnd) :
    (qsatMachine A).Step ⟨stToEnd v, posEnd, σ⟩ ⟨stProc v, p', σ⟩ :=
  ⟨qCst (.tToEndTurn v), isMinTup_qBot, rfl, hσ, rfl, hσ, fun _ _ => rfl,
    Or.inr ⟨not_false, hprev⟩⟩

/-! ### Returning through the prefix -/

/-- **Return, past a decided level**: the quantifier settles it, or both its
values have already been tried. -/
theorem step_procSkip {x : A} (hx : Lax134656.Qsat.IsQVar x) {v b f : Bool}
    (hdec : QShort v x ∨ f = true) (hσ : σ (posCell x) = symV b f x)
    (hprev : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn p' (posCell x)) :
    (qsatMachine A).Step ⟨stProc v, posCell x, σ⟩ ⟨stProc v, p', σ⟩ :=
  ⟨qOne (.tProcSkip v b f) x, ⟨hx, fun a => qBot_le a, hdec⟩, rfl, hσ, rfl, hσ,
    fun _ _ => rfl, Or.inr ⟨not_false, hprev⟩⟩

/-- **Return, at an undecided level**: try the second value and descend
again. -/
theorem step_procSwitch {x : A} (hx : Lax134656.Qsat.IsQVar x) {v b : Bool}
    (hdec : ¬QShort v x) (hσ : σ (posCell x) = symV b false x)
    (hw : σ' (posCell x) = symV true true x) (hfr : ∀ r, r ≠ posCell x → σ' r = σ r)
    (hnext : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn (posCell x) p') :
    (qsatMachine A).Step ⟨stProc v, posCell x, σ⟩ ⟨stDesc, p', σ'⟩ :=
  ⟨qOne (.tProcSwitch v b false) x, ⟨hx, fun a => qBot_le a, hdec, rfl⟩, rfl, hσ, rfl, hw,
    hfr, Or.inl ⟨trivial, hnext⟩⟩

/-- **Return over**: the prefix is exhausted and the value is true, so
accept. -/
theorem step_procAcc (hσ : σ posStart = symStart)
    (hnext : Lax904597.Machines.SuccPos (QLe (A := A)) QPosn posStart p') :
    (qsatMachine A).Step ⟨stProc true, posStart, σ⟩ ⟨stAcc, p', σ⟩ :=
  ⟨qCst .tProcAcc, isMinTup_qBot, rfl, hσ, rfl, hσ, fun _ _ => rfl,
    Or.inl ⟨trivial, hnext⟩⟩

/-! ### The initial configuration

Where the machine starts: descending, at the left marker, on the tape the
instance prescribes. Every cell of the tape carries a symbol – the markers
their own, a variable's cell the value `false` with the flag down – so the
blank is never read, and it is only there because
`DescriptiveComplexity.TMData.InitTape` needs a default for the tuples that are
not cells at all. -/

/-- **The tape the machine starts on.** It depends on the tag and on the first
coordinate alone, which is what makes it agree with
`DescriptiveComplexity.QsatTM.QInp` at *every* tuple, junk included. -/
def initTape (p : QV A) : QV A :=
  match p.1 with
  | .pStart => symStart
  | .pCell => symV false false (p.2 0)
  | .pEnd => symEnd
  | _ => qCst .sBlank

omit [Lax134656.Qsat.qsat.Structure A] [Finite A] [Nonempty A] in
/-- Away from the three position tags the instance prescribes nothing. -/
theorem not_qInp_of_junk {p : QV A} (h : p.1 ≠ QTag.pStart) (h' : p.1 ≠ QTag.pCell)
    (h'' : p.1 ≠ QTag.pEnd) : ∀ a : QV A, ¬QInp p a := by
  rintro a (⟨hp, -, -⟩ | ⟨hp, -, -, -⟩ | ⟨hp, -, -⟩)
  · exact h hp
  · exact h' hp
  · exact h'' hp

/-- **The starting tape is the initial tape of the instance.** -/
theorem initTape_spec (p : QV A) : (qsatMachine A).InitTape p (initTape p) := by
  obtain ⟨t, w⟩ := p
  cases t
  case pStart => exact Or.inl (Or.inl ⟨rfl, rfl, isMinTup_qBot⟩)
  case pCell =>
    exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl, rfl, fun b => qBot_le b⟩))
  case pEnd => exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, isMinTup_qBot⟩))
  all_goals
    exact Or.inr ⟨not_qInp_of_junk (fun h => QTag.noConfusion h)
      (fun h => QTag.noConfusion h) (fun h => QTag.noConfusion h), rfl, isMinTup_qBot⟩

/-- **The machine starts descending at the left marker.** -/
theorem isInit_start (hwf : Lax134656.Qsat.QsatWf A) :
    (qsatMachine A).IsInit ⟨stDesc, posStart, initTape⟩ :=
  ⟨⟨rfl, isMinTup_qBot⟩, minPos_posStart hwf, initTape_spec⟩

/-! ### Where the machine stops

The two dead ends, both of them facts about the table alone: nothing follows an
accepting configuration, and nothing follows a `false` returned past the
outermost quantifier. They are exactly the side conditions of
`DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead`, which is what turns
one exhibited run into non-acceptance for a no-instance. -/

/-- No transition applies in the accepting state. -/
theorem qStateTag_ne_acc : ∀ t : QTag, qIsTrTag t → qStateTag t ≠ QTag.qAcc := by decide

/-- No transition applies to a `false` at the left marker: the two `return`
transitions read a variable's cell, and the accepting one needs a `true`. -/
theorem qStateTag_procFalse : ∀ t : QTag, qIsTrTag t → qStateTag t = QTag.qProc false →
    qReadTag t ≠ QTag.sStart := by decide

/-- **The accepting state is a sink.** -/
theorem not_step_of_acc {c c' : Lax904597.Machines.Config (QV A)} (hacc : (qsatMachine A).Acc c.state) :
    ¬(qsatMachine A).Step c c' := by
  rintro ⟨τ, htr, hsrc, -⟩
  exact qStateTag_ne_acc τ.1 (qTr_isTrTag htr) ((qSrc_tag htr hsrc).symm.trans hacc.2)

/-- **A `false` returned past the outermost quantifier is a dead end.** -/
theorem not_step_procFalse {σ : QV A → QV A} (hσ : σ posStart = symStart)
    {c' : Lax904597.Machines.Config (QV A)} : ¬(qsatMachine A).Step ⟨stProc false, posStart, σ⟩ c' := by
  rintro ⟨τ, htr, hsrc, hread, -⟩
  refine qStateTag_procFalse τ.1 (qTr_isTrTag htr) (qSrc_tag htr hsrc).symm ?_
  have hr : QRead τ (symStart : QV A) := hσ ▸ (hread : QRead τ (σ posStart))
  exact (qRead_tag htr hr).symm

/-- **The accepting configuration is accepting**, on a well-formed instance:
the guard on `DescriptiveComplexity.QsatTM.QAcc` is discharged. -/
theorem acc_stAcc (hwf : Lax134656.Qsat.QsatWf A) : (qsatMachine A).Acc (stAcc : QV A) := ⟨hwf, rfl⟩

/-- **A `false` at the left marker is not accepting.** -/
theorem not_acc_stProcFalse : ¬(qsatMachine A).Acc (stProc false : QV A) := by
  rintro ⟨-, h⟩
  exact QTag.noConfusion h

end Steps

end QsatTM

end Lax822549Proofs.DescriptiveComplexity


