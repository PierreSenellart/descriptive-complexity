/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax485149Proofs.DescriptiveComplexity.Problems.Sat
import Mathlib.Data.Set.Finite.Lemmas
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149.TwoSat.SatOcc
end Lax485149.TwoSat.SatOcc

namespace Lax485149Proofs.DescriptiveComplexity.SatOcc.OccIn
end Lax485149Proofs.DescriptiveComplexity.SatOcc.OccIn

namespace Lax904597.Sat
end Lax904597.Sat

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax485149Proofs.DescriptiveComplexity.SatOcc
export Lax485149.TwoSat.SatOcc (IsCl NegIn OccIn PosIn)
end Lax485149Proofs.DescriptiveComplexity.SatOcc

/-!
# Literal occurrences of a CNF structure, ordered

Semantic layer shared by the reductions *from* SAT (to 3-colorability, to
3SAT…): literal *occurrences* of a `Language.sat`-structure, their traversal
along a linear order of the universe, and the truth of literals and of prefix
disjunctions under an assignment.

An occurrence of a clause `c` is a pair `(x, s)` with `x` an element and
`s : Bool` a sign, such that `x` occurs in `c` with sign `s` (`OccIn`).
Occurrences are ordered lexicographically (variable first, then sign,
`false < true`): `occLt`. On a finite universe every clause with at least one
occurrence has a first (`MinOcc`) and last (`MaxOcc`) occurrence, and every
occurrence that is not first has an immediate predecessor (`SuccOcc`,
`exists_succOcc`), which is unique in both directions. These are the facts
needed to thread a gadget chain (an OR-gadget chain for 3-colorability, a
clause-splitting chain for 3SAT) along the occurrences of each clause.

For chain-correctness arguments, `LitTrue` states that a literal is true under
an assignment, and `PrefixOr`/`PrefixOrStrict` state that some occurrence of a
clause up to (resp. strictly before) a given position is true; the lemmas
relating them to `MinOcc`/`MaxOcc`/`SuccOcc` implement the usual invariant of
chain constructions.

Everything in this file is first-order definable over
`Language.sat.sum Language.order`; the corresponding formulas and their
realization lemmas are in `DescriptiveComplexity.OccurrenceFormulas`.
-/

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [Lax904597.Sat.sat.Structure A]

@[simp] theorem occIn_true {c x : A} : Lax485149.TwoSat.SatOcc.OccIn c x true ↔ Lax485149.TwoSat.SatOcc.IsCl c ∧ Lax485149.TwoSat.SatOcc.PosIn c x := Iff.rfl

@[simp] theorem occIn_false {c x : A} : Lax485149.TwoSat.SatOcc.OccIn c x false ↔ Lax485149.TwoSat.SatOcc.IsCl c ∧ Lax485149.TwoSat.SatOcc.NegIn c x := Iff.rfl

theorem OccIn.isCl {c x : A} {s : Bool} (h : Lax485149.TwoSat.SatOcc.OccIn c x s) : Lax485149.TwoSat.SatOcc.IsCl c := h.1

end SatOcc

end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149.TwoSat.SatOcc.OccIn

export Lax485149Proofs.DescriptiveComplexity.SatOcc.OccIn (isCl)

end Lax485149.TwoSat.SatOcc.OccIn

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [Lax904597.Sat.sat.Structure A]

/-- `c` is a clause with no literal: an unsatisfiable clause. -/
def EmptyCl (c : A) : Prop := Lax485149.TwoSat.SatOcc.IsCl c ∧ ∀ x s, ¬Lax485149.TwoSat.SatOcc.OccIn c x s

/-- The literal `(x, s)` is true under the assignment `ν`. -/
def LitTrue (ν : A → Prop) (x : A) (s : Bool) : Prop := if s then ν x else ¬ν x

/-- Bridge from the `Satisfiable` form of clause satisfaction to the
occurrence form. -/
theorem satClauses_occ {ν : A → Prop}
    (hν : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] →
      ∃ x : A, (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ν x) ∨ (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ν x)) :
    ∀ c : A, Lax485149.TwoSat.SatOcc.IsCl c → ∃ x s, Lax485149.TwoSat.SatOcc.OccIn c x s ∧ LitTrue ν x s := by
  intro c hc
  obtain ⟨x, hx⟩ := hν c hc
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · exact ⟨x, true, ⟨hc, hp⟩, hT⟩
  · exact ⟨x, false, ⟨hc, hn⟩, hT⟩

section Order

variable [LinearOrder A]

/-! ### Truth of prefix disjunctions -/

variable [Finite A]

end Order

end SatOcc

end Lax485149Proofs.DescriptiveComplexity


