/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax366625Proofs.DescriptiveComplexity.ClauseDischarge
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.Defs
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

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.HornSat
end Lax535992.HornSat

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Sat (Satisfiable)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause HornProgram SigmaSOHornDefinable)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornSat (AtMostOnePositive HornSatisfiable)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# Hardness of HORN-SAT: the Horn discharge

Every SO-Horn definable problem admits an ordered first-order reduction to
HORN-SAT (`DescriptiveComplexity.hornSat_hard_of_sigmaSOHornDefinable`): the
machine-free P-hardness statement, one level below the Cook–Levin discharge of
`DescriptiveComplexity.Problems.Sat.Hardness` and in the same style.

It is *simpler* than Cook–Levin, and this is the whole point of the Horn
fragment. The Tseitin translation of an arbitrary first-order kernel has to
name every subformula by an auxiliary *gate* variable, and the gate clauses it
emits are not Horn. Here nothing has to be named: a Horn program
(`DescriptiveComplexity.HornProgram`) is already a conjunction of clauses, its
first-order guards mention the input vocabulary only – so they are *evaluated*
in the input structure rather than encoded – and each clause instance
translates to one propositional clause with at most one positive literal.

Given a block `B`, a number `k` of universally quantified first-order variables
and a program `prog`, the reduction interprets, inside an ordered input
structure `A`:

* propositional variables: one per relation variable `i` of `B` and per
  `B.arity i`-tuple over `A`, canonically padded
  (`DescriptiveComplexity.Padding`) to the common dimension
  `DescriptiveComplexity.clauseDim`;
* clauses: one per clause `c` of the program and per `k`-tuple over `A`
  *satisfying the guard of `c`* – the guard is an input-vocabulary formula, so
  “the guard holds” is literally what the defining formula of `satIsClause`
  says;
* literals: the head atom of `c` occurs positively and its body atoms occur
  negatively, at the canonically padded tuples of their arguments.

A clause of the program with no head (a goal clause) yields a purely negative
propositional clause, and one with a head yields exactly one positive literal:
the interpreted structure is always Horn
(`DescriptiveComplexity.horn_atMostOnePositive`), which is what makes the reduction land
in HORN-SAT rather than merely in SAT.

The correctness proof (`DescriptiveComplexity.horn_satisfiable_iff`) reads in both
directions through the canonical padding: an assignment `ρ` of the block gives
the truth value `ρ i (pref x)` of the propositional variable `(i, x)`, and
conversely a satisfying truth assignment `ν` gives the assignment
`ρ i ā := ν (i, pad ā)`.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Discharge

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-! ### Tags and clause access

The dimension, the tags and the two generic defining formulas are shared with
the Krom discharge; they live in `DescriptiveComplexity.ClauseDischarge`. -/

/-- The tags of the Horn interpretation: the generic clausal tags at the
program's number of clauses. -/
abbrev HornTag (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) : Type :=
  ClauseTag prog.length B

/-- The `c`-th clause of the program. -/
abbrev clauseAt (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) (c : Fin prog.length) :
    Lax535992.HornFragment.HornClause (L.sum Language.order) B k :=
  prog[(c : ℕ)]'c.isLt

/-! ### The defining formulas -/

section Formulas

variable {γ : Type}

open Classical in
/-- The defining formula of a positive occurrence: the head atom of the
clause, when it is an atom of the relation variable `i`. -/
noncomputable def headOccF (c : Lax535992.HornFragment.HornClause (L.sum Language.order) B k) (i : B.ι)
    (u x : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  c.head.elim ⊥ fun a => if a.idx = i then atomOccF a u x else ⊥

open Classical in
/-- The defining formula of a negative occurrence: any body atom of the
clause that is an atom of the relation variable `i`. -/
noncomputable def bodyOccF (c : Lax535992.HornFragment.HornClause (L.sum Language.order) B k) (i : B.ι)
    (u x : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  listSup (c.body.map fun a => if a.idx = i then atomOccF a u x else ⊥)

/-! #### Realization of the defining formulas -/

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

theorem realize_headOccF {c : Lax535992.HornFragment.HornClause (L.sum Language.order) B k} {i : B.ι}
    {u x : Fin (clauseDim B k) → γ} :
    (headOccF c i u x).Realize v ↔
      ∃ a ∈ c.head, a.idx = i ∧
        PadTup (atomIdx a) (fun j => v (u j)) fun j => v (x j) := by
  classical
  rw [headOccF]
  cases hh : c.head with
  | none =>
    rw [Option.elim_none]
    refine iff_of_false id ?_
    rintro ⟨a, ha, -⟩
    simp at ha
  | some a =>
    rw [Option.elim_some]
    by_cases hi : a.idx = i
    · rw [if_pos hi, realize_atomOccF]
      refine ⟨fun h => ⟨a, rfl, hi, h⟩, ?_⟩
      rintro ⟨a', ha', -, h⟩
      have hae := Option.mem_def.mp ha'
      rw [Option.some.injEq] at hae
      subst hae
      exact h
    · rw [if_neg hi]
      refine iff_of_false id ?_
      rintro ⟨a', ha', hi', -⟩
      have hae := Option.mem_def.mp ha'
      rw [Option.some.injEq] at hae
      subst hae
      exact hi hi'

theorem realize_bodyOccF {c : Lax535992.HornFragment.HornClause (L.sum Language.order) B k} {i : B.ι}
    {u x : Fin (clauseDim B k) → γ} :
    (bodyOccF c i u x).Realize v ↔
      ∃ a ∈ c.body, a.idx = i ∧
        PadTup (atomIdx a) (fun j => v (u j)) fun j => v (x j) := by
  classical
  rw [bodyOccF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψmem, hψ⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hψmem
    by_cases hi : a.idx = i
    · rw [if_pos hi, realize_atomOccF] at hψ
      exact ⟨a, ha, hi, hψ⟩
    · rw [if_neg hi] at hψ
      exact hψ.elim
  · rintro ⟨a, ha, hi, hpad⟩
    refine ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [if_pos hi, realize_atomOccF]
    exact hpad

end Formulas

/-- The Horn interpretation: the CNF instance of the propositional translation
of the program, defined inside the ordered input structure. -/
noncomputable def hornInterp (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) :
    Lax904597.Interpretations.FOInterpretation (L.sum Language.order) Lax904597.Sat.sat (HornTag prog) (clauseDim B k) where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
        match t 0 with
        | Sum.inl (Sum.inl c) =>
            guardF (clauseAt prog c).guard (fun j => ((0 : Fin 1), j)) ⊓
              canonF k fun j => ((0 : Fin 1), j)
        | _ => ⊥
    | _, .posIn => fun t =>
        match t 0, t 1 with
        | Sum.inl (Sum.inl c), Sum.inl (Sum.inr i) =>
            headOccF (clauseAt prog c) i (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
        | _, _ => ⊥
    | _, .negIn => fun t =>
        match t 0, t 1 with
        | Sum.inl (Sum.inl c), Sum.inl (Sum.inr i) =>
            bodyOccF (clauseAt prog c) i (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
        | _, _ => ⊥

/-! ### Characterization of the interpreted relations

Every statement below is the corresponding realization lemma read through
`DescriptiveComplexity.FOInterpretation.relMap_map`; the tag combinations that are not
listed have `⊥` as defining formula, so the corresponding relation is empty. -/

section Characterizations

variable {A : Type} [L.Structure A] [LinearOrder A]

variable {prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k}

/-- **The clause elements**: one per clause of the program and per canonically
padded tuple satisfying that clause's guard. -/
theorem horn_isClause_cl (c : Fin prog.length) (w : Fin (clauseDim B k) → A) :
    RelMap (M := (hornInterp prog).Map A) Lax904597.Sat.satIsClause ![(clTag c, w)] ↔
      (clauseAt prog c).guard.Realize (fun j => w (Fin.castLE le_clauseDim j)) ∧ Canon k w := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_inf.trans (and_congr realize_guardF realize_canonF)

/-- Elements carrying a variable tag are not clauses. -/
theorem horn_not_isClause_var (i : B.ι) (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (hornInterp prog).Map A) Lax904597.Sat.satIsClause ![(varTag i, w)] :=
  id

/-- Elements carrying the junk tag are not clauses. -/
theorem horn_not_isClause_junk (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (hornInterp prog).Map A) Lax904597.Sat.satIsClause
      ![((Sum.inr () : HornTag prog), w)] :=
  id

/-- **The positive literals**: the head atom of the clause, at the canonically
padded tuple of its arguments. -/
theorem horn_posIn_cl_var (c : Fin prog.length) (i : B.ι)
    (u x : Fin (clauseDim B k) → A) :
    RelMap (M := (hornInterp prog).Map A) Lax904597.Sat.satPosIn ![(clTag c, u), (varTag i, x)] ↔
      ∃ a ∈ (clauseAt prog c).head, a.idx = i ∧ PadTup (atomIdx a) u x := by
  rw [FOInterpretation.relMap_map]
  exact realize_headOccF

/-- **The negative literals**: any body atom of the clause, at the canonically
padded tuple of its arguments. -/
theorem horn_negIn_cl_var (c : Fin prog.length) (i : B.ι)
    (u x : Fin (clauseDim B k) → A) :
    RelMap (M := (hornInterp prog).Map A) Lax904597.Sat.satNegIn ![(clTag c, u), (varTag i, x)] ↔
      ∃ a ∈ (clauseAt prog c).body, a.idx = i ∧ PadTup (atomIdx a) u x := by
  rw [FOInterpretation.relMap_map]
  exact realize_bodyOccF

end Characterizations

/-! ### The interpreted structure is Horn, and correct -/

section Correctness

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k)

/-- **The interpretation always lands in HORN-SAT**: a clause of the program
has at most one head atom, and canonical padding makes the element encoding it
unique, so every interpreted clause has at most one positive literal. -/
theorem horn_atMostOnePositive : Lax535992.HornSat.AtMostOnePositive ((hornInterp prog).Map A) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rintro ⟨tc, u⟩ ⟨tx, x⟩ ⟨ty, y⟩ hc hx hy
  rcases tc with (c | i) | ⟨⟩
  · rcases tx with (c' | i') | ⟨⟩ <;> try exact hx.elim
    rcases ty with (c'' | i'') | ⟨⟩ <;> try exact hy.elim
    obtain ⟨a, ha, hai, hpx⟩ := (horn_posIn_cl_var c i' u x).mp hx
    obtain ⟨a', ha', hai', hpy⟩ := (horn_posIn_cl_var c i'' u y).mp hy
    have hae : (clauseAt prog c).head = some a := Option.mem_def.mp ha
    have hae' : (clauseAt prog c).head = some a' := Option.mem_def.mp ha'
    rw [hae, Option.some.injEq] at hae'
    subst hae'
    subst hai
    subst hai'
    rw [eq_pad_of_padTup ha₀ hpx, eq_pad_of_padTup ha₀ hpy]
  · exact absurd hc (horn_not_isClause_var i u)
  · exact absurd hc (horn_not_isClause_junk u)

end Correctness

end Discharge

end Lax366625Proofs.DescriptiveComplexity


