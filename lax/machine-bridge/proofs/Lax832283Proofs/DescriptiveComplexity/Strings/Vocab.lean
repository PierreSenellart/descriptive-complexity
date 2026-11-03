/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.SetTheory.Cardinal.NatCard
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
import Lax751879.FixedPointSemantics
import Lax751879.FixedPointSyntax
import Lax751879.LeastFixedPoints
import Lax751879.OrderedStructures
import Lax751879.PolynomialTime
import Lax751879.StructureEncoding
import Lax832283.StringProblems
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax988886.ExistentialSecondOrder
import Lax988886.FiniteStructures
import Lax988886.NondeterministicPolynomialTime

namespace Lax832283.StringProblems
end Lax832283.StringProblems

namespace Lax832283Proofs.DescriptiveComplexity.Strings.FinVocab
end Lax832283Proofs.DescriptiveComplexity.Strings.FinVocab

namespace Lax832283Proofs.DescriptiveComplexity.Strings
export Lax832283.StringProblems (FinVocab)
end Lax832283Proofs.DescriptiveComplexity.Strings

/-!
# Finite vocabularies as lists of arities

The string side of the library's bridge to machine classes numbers the relation
symbols of a structure, so that a structure can be written down as a bit string:
the tables of its relations, one symbol after the other. A
`DescriptiveComplexity.Strings.FinVocab` is such a numbering of the symbols of a
relational language. It is data: the encoding of a structure depends on it, as it
must, while what is proved about the encoded language does not.

`DescriptiveComplexity.Strings.FinVocab.ofEquiv` builds one from an enumeration of
the symbols, and `DescriptiveComplexity.Strings.FinVocab.ofFinite` from the mere
finiteness of the set of symbols.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder

namespace FinVocab

variable {L : Language.{0, 0}}

variable (V : Lax832283.StringProblems.FinVocab L)

/-- The number of a symbol has the arity of that symbol. -/
theorem arity_toSym {n : ℕ} (R : L.Relations n) : V.σ.get (V.toSym R) = n := by
  rw [← V.arity_sym, Lax832283.StringProblems.FinVocab.toSym, Equiv.apply_symm_apply]

end FinVocab

end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283.StringProblems.FinVocab

export Lax832283Proofs.DescriptiveComplexity.Strings.FinVocab (arity_toSym)

end Lax832283.StringProblems.FinVocab

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder

namespace FinVocab

variable {L : Language.{0, 0}}

variable (V : Lax832283.StringProblems.FinVocab L)

/-- The symbol of a given number, at the arity the list records. -/
def ofSym (i : Fin V.σ.length) : L.Relations (V.σ.get i) :=
  V.arity_sym i ▸ (V.sym i).2

end FinVocab

end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283.StringProblems.FinVocab

export Lax832283Proofs.DescriptiveComplexity.Strings.FinVocab (ofSym)

end Lax832283.StringProblems.FinVocab

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder

namespace FinVocab

variable {L : Language.{0, 0}}

variable (V : Lax832283.StringProblems.FinVocab L)

theorem toSym_ofSym (i : Fin V.σ.length) : V.toSym (V.ofSym i) = i := by
  have key : ∀ (n : ℕ) (h : (V.sym i).1 = n), V.toSym (h ▸ (V.sym i).2) = i := by
    rintro _ rfl
    exact V.sym.symm_apply_apply i
  exact key _ _

end FinVocab

end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283.StringProblems.FinVocab

export Lax832283Proofs.DescriptiveComplexity.Strings.FinVocab (toSym_ofSym)

end Lax832283.StringProblems.FinVocab

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder

namespace FinVocab

variable {L : Language.{0, 0}}

variable (V : Lax832283.StringProblems.FinVocab L)

/-- The symbol of the number of a symbol is that symbol. -/
theorem ofSym_toSym {n : ℕ} (R : L.Relations n) :
    V.arity_toSym R ▸ V.ofSym (V.toSym R) = R := by
  have key : ∀ (s : Σ n, L.Relations n) (hs : s = ⟨n, R⟩) (m : ℕ) (h₁ : s.1 = m) (h₂ : m = n),
      h₂ ▸ h₁ ▸ s.2 = R := by
    rintro _ rfl _ rfl _; rfl
  exact key _ (V.sym.apply_symm_apply _) _ _ _

end FinVocab

end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283.StringProblems.FinVocab

export Lax832283Proofs.DescriptiveComplexity.Strings.FinVocab (ofSym_toSym)

end Lax832283.StringProblems.FinVocab

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder

namespace FinVocab

variable {L : Language.{0, 0}}

variable (V : Lax832283.StringProblems.FinVocab L)

end FinVocab

end Lax832283Proofs.DescriptiveComplexity.Strings


