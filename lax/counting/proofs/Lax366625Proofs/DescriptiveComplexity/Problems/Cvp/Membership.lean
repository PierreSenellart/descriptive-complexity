/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.Cvp.Defs
import Lax366625Proofs.DescriptiveComplexity.FixedPointHorn
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

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.CircuitValue
end Lax535992.CircuitValue

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives LFPDef LFPDefinable lfpAssign)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.CircuitValue (CircuitAccepts GateVal)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax535992.CircuitValue (circIsAnd circIsFalse circIsNot circIsOr circIsTrue circLeft circOut circRight circuit)
end FirstOrder.Language

/-!
# CVP is in polynomial time

Membership is written in FO(LFP) and not in the Horn fragment, and the choice
is the point of the file: the semantics of `DescriptiveComplexity.CVP` *is* a
least fixed point (`DescriptiveComplexity.GateVal`), so the rule system
`DescriptiveComplexity.Cvp.cvpRules` is the ten gate rules transcribed, one per line
of the inductive definition, and the output sentence is the one first-order
statement the Horn fragment could not make head-on: “some output gate is in the
true rail”. A Horn program accepts when its least model satisfies its *goal*
clauses, i.e., when something is **not** derived, so the same definition in the
fragment would have to be written on the false rail and would need the circuit
to be well-formed for the two rails to be complementary. Reading the value at
an unrestricted first-order output formula avoids the detour, and
`DescriptiveComplexity.lfpDefinable_iff_mem_PTIME` – Immerman–Vardi – turns it
back into membership in the class.

The `≡` between the rule system's least model and the inductive semantics is
proved in both directions in the usual way: the inductive predicate is closed
under the rules (`DescriptiveComplexity.Cvp.derives_of_gateVal`), and it is a
prefixpoint, so it contains the least one
(`DescriptiveComplexity.Cvp.gateVal_of_derives`, by
`DescriptiveComplexity.lfpAssign_least_of_closed`).
-/

namespace Lax366625Proofs.DescriptiveComplexity

namespace Cvp

open FirstOrder

open Language Structure

/-! ### The block, the vocabulary of the rules, and their guards -/

/-- The two rails of the induction: one unary relation variable per truth
value, `true` carrying the gates that evaluate to `1`. Indexing the block by
`Bool` rather than by `Fin 2` is what lets `ρ true` and `ρ false` elaborate;
the block is reducible so that a numeral elaborates at `Fin (arity i)`. -/
@[reducible] def valBlock : Lax904597.SecondOrder.SOBlock where
  ι := Bool
  arity := fun _ => 1

/-- The vocabulary the rules are written over: circuits, expanded by the order
that every FO(LFP) definition may use (this one does not). -/
abbrev cvLang : Language := Lax535992.CircuitValue.circuit.sum Language.order

/-- “Is a constant `1` input”, in the rules' vocabulary. -/
abbrev gIsTrue : cvLang.Relations 1 := Sum.inl Lax535992.CircuitValue.circIsTrue

/-- “Is a constant `0` input”, in the rules' vocabulary. -/
abbrev gIsFalse : cvLang.Relations 1 := Sum.inl Lax535992.CircuitValue.circIsFalse

/-- “Is a conjunction gate”, in the rules' vocabulary. -/
abbrev gIsAnd : cvLang.Relations 1 := Sum.inl Lax535992.CircuitValue.circIsAnd

/-- “Is a disjunction gate”, in the rules' vocabulary. -/
abbrev gIsOr : cvLang.Relations 1 := Sum.inl Lax535992.CircuitValue.circIsOr

/-- “Is a negation gate”, in the rules' vocabulary. -/
abbrev gIsNot : cvLang.Relations 1 := Sum.inl Lax535992.CircuitValue.circIsNot

/-- “Takes as first argument”, in the rules' vocabulary. -/
abbrev gLeft : cvLang.Relations 2 := Sum.inl Lax535992.CircuitValue.circLeft

/-- “Takes as second argument”, in the rules' vocabulary. -/
abbrev gRight : cvLang.Relations 2 := Sum.inl Lax535992.CircuitValue.circRight

/-- The rules quantify over three variables: the gate and its two arguments. -/
abbrev nvars : ℕ := 3

/-- A gate-kind guard on one of the three variables. -/
noncomputable def kindF (r : cvLang.Relations 1) (i : Fin nvars) :
    cvLang.Formula (Fin nvars) :=
  Relations.formula₁ r (Term.var i)

/-- A wire guard between two of the three variables. -/
noncomputable def wireF (r : cvLang.Relations 2) (i j : Fin nvars) :
    cvLang.Formula (Fin nvars) :=
  Relations.formula₂ r (Term.var i) (Term.var j)

/-- The atom “variable `i` is in the rail `b`”. -/
def rail (b : Bool) (i : Fin nvars) : Lax485149.SecondOrderAtoms.SOAtom valBlock nvars :=
  ⟨b, fun _ => i⟩

/-! ### The rules

One rule per constructor of `DescriptiveComplexity.GateVal`, with the gate as
variable `0` and its two arguments as variables `1` and `2`. -/

/-- The ten gate rules, read off the inductive semantics. -/
noncomputable def cvpRules : List (Lax535992.HornFragment.HornClause cvLang valBlock nvars) :=
  [ ⟨kindF gIsTrue 0, [], some (rail true 0)⟩,
    ⟨kindF gIsFalse 0, [], some (rail false 0)⟩,
    ⟨kindF gIsAnd 0 ⊓ wireF gLeft 0 1 ⊓ wireF gRight 0 2,
      [rail true 1, rail true 2], some (rail true 0)⟩,
    ⟨kindF gIsAnd 0 ⊓ wireF gLeft 0 1, [rail false 1], some (rail false 0)⟩,
    ⟨kindF gIsAnd 0 ⊓ wireF gRight 0 2, [rail false 2], some (rail false 0)⟩,
    ⟨kindF gIsOr 0 ⊓ wireF gLeft 0 1, [rail true 1], some (rail true 0)⟩,
    ⟨kindF gIsOr 0 ⊓ wireF gRight 0 2, [rail true 2], some (rail true 0)⟩,
    ⟨kindF gIsOr 0 ⊓ wireF gLeft 0 1 ⊓ wireF gRight 0 2,
      [rail false 1, rail false 2], some (rail false 0)⟩,
    ⟨kindF gIsNot 0 ⊓ wireF gLeft 0 1, [rail false 1], some (rail true 0)⟩,
    ⟨kindF gIsNot 0 ⊓ wireF gLeft 0 1, [rail true 1], some (rail false 0)⟩ ]

/-! ### The output sentence: some output gate is in the true rail -/

/-! ### The least model of the rules is the inductive semantics -/

section Model

variable {A : Type} [Lax535992.CircuitValue.circuit.Structure A] [LinearOrder A]

/-- Realization of a kind guard, down to the circuit structure. -/
theorem realize_kindF (r : cvLang.Relations 1) (i : Fin nvars)
    (v : Fin nvars → A) :
    (kindF r i).Realize v ↔ RelMap r ![v i] := by
  rw [kindF, Formula.realize_rel₁]
  rfl

/-- Realization of a wire guard, down to the circuit structure. -/
theorem realize_wireF (r : cvLang.Relations 2) (i j : Fin nvars)
    (v : Fin nvars → A) :
    (wireF r i j).Realize v ↔ RelMap r ![v i, v j] := by
  rw [wireF, Formula.realize_rel₂]
  rfl

/-- The assignment cut out by the inductive semantics: a gate is in the rail
`b` when it derives the value `b`. -/
abbrev gateAssign : valBlock.Assignment A := fun b x => Lax535992.CircuitValue.GateVal b (x 0)

omit [LinearOrder A] in
/-- A rail atom holds of the inductive semantics exactly when the variable it
names derives the value it names. -/
theorem gateAssign_rail (b : Bool) (i : Fin nvars) (v : Fin nvars → A) :
    (rail b i).Holds (gateAssign (A := A)) v ↔ Lax535992.CircuitValue.GateVal b (v i) :=
  Iff.rfl

/-- **The inductive semantics is closed under the rules**, one case per gate
rule. -/
theorem gateAssign_closed :
    ∀ c ∈ cvpRules, ∀ a : Lax485149.SecondOrderAtoms.SOAtom valBlock nvars, c.head = some a →
      ∀ v : Fin nvars → A, c.guard.Realize v →
        (∀ b ∈ c.body, b.Holds (gateAssign (A := A)) v) → a.Holds gateAssign v := by
  intro c hc a ha v hg hb
  -- Unfold the membership in the ten-element list, then discharge each rule.
  simp only [cvpRules, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Option.some.injEq] at ha
      subst ha
      simp only [Formula.realize_inf, realize_kindF, realize_wireF] at hg
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      simp only [gateAssign_rail] at hb ⊢
      first
        | exact .constTrue hg
        | exact .constFalse hg
        | exact .andTrue hg.1.1 hg.1.2 hg.2 hb.1 hb.2
        | exact .andFalseLeft hg.1 hg.2 hb
        | exact .andFalseRight hg.1 hg.2 hb
        | exact .orTrueLeft hg.1 hg.2 hb
        | exact .orTrueRight hg.1 hg.2 hb
        | exact .orFalse hg.1.1 hg.1.2 hg.2 hb.1 hb.2
        | exact .notTrue hg.1 hg.2 hb
        | exact .notFalse hg.1 hg.2 hb

/-- Everything the rules derive has its value derivable by the gate rules: the
least fixed point is contained in the inductive semantics. -/
theorem gateVal_of_derives {b : Bool} {x : Fin 1 → A}
    (h : Lax535992.LeastFixedPoint.Derives cvpRules (⟨b, x⟩ : Σ i : valBlock.ι, Fin (valBlock.arity i) → A)) :
    Lax535992.CircuitValue.GateVal b (x 0) :=
  lfpAssign_least_of_closed (ρ := gateAssign) gateAssign_closed h

/-- Conversely, every derivable value is derived by the rules. The tuple is
written `fun _ => g` throughout, which is the shape
`DescriptiveComplexity.Derives.rule` produces for a unary head. -/
theorem derives_of_gateVal {b : Bool} {g : A} (h : Lax535992.CircuitValue.GateVal b g) :
    Lax535992.LeastFixedPoint.Derives cvpRules (⟨b, fun _ => g⟩ : Σ i : valBlock.ι, Fin (valBlock.arity i) → A) := by
  -- Each case names its clause literally: the membership witness alone would
  -- leave the clause a metavariable, since nothing else determines it.
  induction h with
  | @constTrue g hg =>
    refine .rule (c := ⟨kindF gIsTrue 0, [], some (rail true 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, g, g]) ?_ (by simp)
    exact (realize_kindF _ _ _).mpr hg
  | @constFalse g hg =>
    refine .rule (c := ⟨kindF gIsFalse 0, [], some (rail false 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, g, g]) ?_ (by simp)
    exact (realize_kindF _ _ _).mpr hg
  | @andTrue g l r hgg hl hr _ _ ihl ihr =>
    refine .rule (c := ⟨kindF gIsAnd 0 ⊓ wireF gLeft 0 1 ⊓ wireF gRight 0 2,
        [rail true 1, rail true 2], some (rail true 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, l, r]) ?_ ?_
    · simp only [Formula.realize_inf, realize_kindF, realize_wireF]
      exact ⟨⟨hgg, hl⟩, hr⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ihl
      · exact ihr
  | @andFalseLeft g l hgg hl _ ihl =>
    refine .rule (c := ⟨kindF gIsAnd 0 ⊓ wireF gLeft 0 1, [rail false 1], some (rail false 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, l, l]) ?_ ?_
    · simp only [Formula.realize_inf, realize_kindF, realize_wireF]
      exact ⟨hgg, hl⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exact ihl
  | @andFalseRight g r hgg hr _ ihr =>
    refine .rule (c := ⟨kindF gIsAnd 0 ⊓ wireF gRight 0 2, [rail false 2], some (rail false 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, r, r]) ?_ ?_
    · simp only [Formula.realize_inf, realize_kindF, realize_wireF]
      exact ⟨hgg, hr⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exact ihr
  | @orTrueLeft g l hgg hl _ ihl =>
    refine .rule (c := ⟨kindF gIsOr 0 ⊓ wireF gLeft 0 1, [rail true 1], some (rail true 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, l, l]) ?_ ?_
    · simp only [Formula.realize_inf, realize_kindF, realize_wireF]
      exact ⟨hgg, hl⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exact ihl
  | @orTrueRight g r hgg hr _ ihr =>
    refine .rule (c := ⟨kindF gIsOr 0 ⊓ wireF gRight 0 2, [rail true 2], some (rail true 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, r, r]) ?_ ?_
    · simp only [Formula.realize_inf, realize_kindF, realize_wireF]
      exact ⟨hgg, hr⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exact ihr
  | @orFalse g l r hgg hl hr _ _ ihl ihr =>
    refine .rule (c := ⟨kindF gIsOr 0 ⊓ wireF gLeft 0 1 ⊓ wireF gRight 0 2,
        [rail false 1, rail false 2], some (rail false 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, l, r]) ?_ ?_
    · simp only [Formula.realize_inf, realize_kindF, realize_wireF]
      exact ⟨⟨hgg, hl⟩, hr⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ihl
      · exact ihr
  | @notTrue g i hgg hi _ ihi =>
    refine .rule (c := ⟨kindF gIsNot 0 ⊓ wireF gLeft 0 1, [rail false 1], some (rail true 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, i, i]) ?_ ?_
    · simp only [Formula.realize_inf, realize_kindF, realize_wireF]
      exact ⟨hgg, hi⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exact ihi
  | @notFalse g i hgg hi _ ihi =>
    refine .rule (c := ⟨kindF gIsNot 0 ⊓ wireF gLeft 0 1, [rail true 1], some (rail false 0)⟩)
      (by simp [cvpRules]) rfl (v := ![g, i, i]) ?_ ?_
    · simp only [Formula.realize_inf, realize_kindF, realize_wireF]
      exact ⟨hgg, hi⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exact ihi

/-- **The least model of the rules is the inductive semantics.** -/
theorem lfpAssign_iff {b : Bool} {x : Fin 1 → A} :
    Lax535992.LeastFixedPoint.lfpAssign (A := A) cvpRules b x ↔ Lax535992.CircuitValue.GateVal b (x 0) := by
  refine ⟨gateVal_of_derives, fun h => ?_⟩
  have hx : (fun _ : Fin 1 => x 0) = x := funext fun j => congrArg x (Fin.eq_zero j).symm
  exact hx ▸ derives_of_gateVal h

/-! ### The value of the definition -/

end Model

/-! ### Definability and membership -/

end Cvp

end Lax366625Proofs.DescriptiveComplexity


