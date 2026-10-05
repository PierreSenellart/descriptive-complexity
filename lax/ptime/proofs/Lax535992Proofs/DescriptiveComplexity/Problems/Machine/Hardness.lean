/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import Lax535992Proofs.DescriptiveComplexity.OrderedComposition
import Lax535992Proofs.DescriptiveComplexity.Problems.Machine.Program
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

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Sat (Satisfiable)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Machines (Config MinPos SuccPos TMData)
end Lax535992Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# The machine of a CNF formula

The program half of `SAT ≤ᶠᵒ[≤] NTMAccept`: the states, symbols and transitions
of the machine `M_φ` built inside an ordered SAT instance, on the tape laid out
in `DescriptiveComplexity.Problems.Machine.Tape`.

## The program

```
  guess :  ⊢ →  at each cell (x,U) write (x,T) or (x,F), moving right  → ⊣
  check c: sweep back over the cells, accumulating
             flag := flag ∨ (posIn c x ∧ b) ∨ (negIn c x ∧ ¬b)
           at the far marker: if flag, take the next clause and turn round;
                              if not, no transition exists and the run dies
  accept:  when the clause just checked was the last one
```

Two things make this small. The check is an **first-order test on the source
structure** – `DescriptiveComplexity.SatLit` – evaluated by the formula that will define
the transition relation, so no clause-width bound and no occurrence machinery
are needed and the source can be plain SAT rather than 3SAT. And the sweeps
**alternate direction** instead of rewinding, so a clause costs one pass and
there are no rewind states; the markers are what tell the machine a pass has
ended.

The machine is nondeterministic in exactly one place, the choice of `(x,T)` or
`(x,F)` in the guess phase. That is a deliberate design decision, and it
is what will make the `⇒` half of correctness a corollary of uniqueness rather
than a second invariant induction.

## Semantics first

Everything here is a plain predicate on tagged tuples, as
`DescriptiveComplexity.SatPosn` and `DescriptiveComplexity.SatInp` are: the machine is
assembled as a `DescriptiveComplexity.TMData` and reasoned about directly. Only once
its correctness is proved does the first-order transcription happen, one
realization lemma per `relFormula`. A transition table type-checks whatever it
says, so it has to be validated by a proof, not by elaboration.
-/

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

noncomputable section Machine

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The instance, read -/

/-- Being a clause of the CNF instance. -/
def SatCl (c : A) : Prop := RelMap Lax904597.Sat.satIsClause ![c]

/-- The variable `x` occurs positively in the clause `c`. -/
def SatPos (c x : A) : Prop := RelMap Lax904597.Sat.satPosIn ![c, x]

/-- The variable `x` occurs negatively in the clause `c`. -/
def SatNeg (c x : A) : Prop := RelMap Lax904597.Sat.satNegIn ![c, x]

/-- `c` is the lowest clause. -/
def SatMinCl (c : A) : Prop := SatCl c ∧ ∀ e, SatCl e → c ≤ e

/-- `c` is the highest clause. -/
def SatMaxCl (c : A) : Prop := SatCl c ∧ ∀ e, SatCl e → e ≤ c

/-- `c'` is the clause immediately above `c`. -/
def SatNextCl (c c' : A) : Prop :=
  SatCl c ∧ SatCl c' ∧ c < c' ∧ ∀ e, SatCl e → c < e → c' ≤ e

/-! ### The elements of the machine -/

/-- The least element of the instance, to which every constant of the machine
is pinned. -/
def botA : A := (Finite.exists_min (id : A → A)).choose

omit [Lax904597.Sat.sat.Structure A] in
theorem botA_le (a : A) : botA (A := A) ≤ a := (Finite.exists_min (id : A → A)).choose_spec a

/-! #### Symbols -/

/-! #### Positions -/

/-! #### States -/

/-! ### The transition table -/

/-! ### The table is a table

Before any run is considered: each transition has exactly one destination and
symbol written, and the two places where two tags could otherwise both apply
are exclusive. A mistake in the table shows up here first, which is why these
come before the correctness proof. (Sources and symbols read need no
functionality lemma of their own: `DescriptiveComplexity.satTr_unique` pins the whole
transition from them.) -/

section Functional

end Functional

/-! ### The positions of the tape, concretely -/

/-- The greatest element of the instance: the last cell of the tape. -/
def topA : A := (Finite.exists_max (id : A → A)).choose

omit [Lax904597.Sat.sat.Structure A] in
theorem le_topA (a : A) : a ≤ topA (A := A) := (Finite.exists_max (id : A → A)).choose_spec a

/-! ### The intended run: the guess phase -/

/-! ### The intended run: a check sweep -/

/-! ### One clause, checked end to end

Each of these is a sweep followed by its turn. They are the step and the base
case of the induction over clauses; the induction itself only has to choose
between them. Each carries its step count, bounded by the rank of the right
marker: that is the honest per-clause cost, roughly the size of the instance,
and what lets the whole run fit the budget of
`DescriptiveComplexity.TMData.Accepts`. -/

omit [Nonempty A] in
/-- **Every clause but the last has a next one.** The clause the machine turns
to is the least one above the current one, which is what
`DescriptiveComplexity.SatNextCl` asserts. -/
theorem exists_satNextCl {c : A} (hc : SatCl c) (hnmax : ¬ SatMaxCl c) :
    ∃ c', SatNextCl c c' := by
  have hne : ∃ e : A, SatCl e ∧ c < e := by
    by_contra hcon
    push Not at hcon
    exact hnmax ⟨hc, hcon⟩
  obtain ⟨c', ⟨hc', hlt⟩, hmin⟩ :=
    exists_minPos (Le := (· ≤ ·)) (Posn := fun e : A => SatCl e ∧ c < e)
      ⟨le_refl, fun a b c => le_trans, fun a b => le_antisymm, le_total⟩ hne
  exact ⟨c', hc, hc', hlt, fun e he hce => hmin e ⟨he, hce⟩⟩

omit [Nonempty A] in
/-- Passing to the next clause removes exactly one clause from the ones still
to be checked. -/
theorem ncard_clauses_next {c c' : A} (hnext : SatNextCl c c') :
    {e : A | SatCl e ∧ c ≤ e}.ncard = {e : A | SatCl e ∧ c' ≤ e}.ncard + 1 := by
  obtain ⟨hc, hc', hlt, hmin⟩ := hnext
  have hset : {e : A | SatCl e ∧ c ≤ e} = insert c {e : A | SatCl e ∧ c' ≤ e} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨he, hce⟩
      rcases eq_or_lt_of_le hce with rfl | hlt'
      · exact Or.inl rfl
      · exact Or.inr ⟨he, hmin e he hlt'⟩
    · rintro (rfl | ⟨he, hce⟩)
      · exact ⟨hc, le_refl _⟩
      · exact ⟨he, le_trans hlt.le hce⟩
  rw [hset,
    Set.ncard_insert_of_notMem (fun hmem => absurd hmem.2 (not_le.mpr hlt)) (Set.toFinite _)]

/-! ### Correctness, the chaining half -/

/-! ### Correctness, from an accepting run to an assignment

By design, the machine branches only at the guess, so
an accepting run *is* the intended run of the assignment it wrote, and the flag
conditions along it force every clause to be satisfied. The analysis is one
induction on the length of the run, with one case per tag of the head position.
At each non-guess configuration the transition that fired is identified through
its tag – a `decide` over the finite tag type – and the actual step is equated
with the intended one by `DescriptiveComplexity.step_functional_off_guess`; at a guess
configuration the transition itself says which value was written. -/

section Reverse

end Reverse

/-! ### The machine accepts exactly the satisfiable instances -/

end Machine

end Lax535992Proofs.DescriptiveComplexity


