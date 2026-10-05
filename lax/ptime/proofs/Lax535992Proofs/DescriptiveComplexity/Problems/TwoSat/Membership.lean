/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax535992Proofs.DescriptiveComplexity.LogSpace
import Lax535992Proofs.DescriptiveComplexity.Problems.TwoSat.Defs
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

namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax485149.TwoSat
end Lax485149.TwoSat

namespace Lax485149.TwoSat.SatOcc
end Lax485149.TwoSat.SatOcc

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax535992Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax485149.KromFragment (KromClause KromLit KromProgram SigmaSOKromDefinable)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax485149.TwoSat (WidthAtMostTwo)
end Lax535992Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace Lax535992Proofs.DescriptiveComplexity.SatOcc
export Lax485149.TwoSat.SatOcc (IsCl OccIn)
end Lax535992Proofs.DescriptiveComplexity.SatOcc

/-!
# 2SAT is SO-Krom definable, hence in NL

The membership half of the completeness of 2SAT for `DescriptiveComplexity.NL`: a Krom
program (`DescriptiveComplexity.TwoSatKrom.twoSatProgram`) whose satisfying assignments
are exactly the satisfying truth assignments of a width-two CNF structure, so
`DescriptiveComplexity.twoSat_mem_NL`.

The program is the natural one, and it shows what the guards of the Krom
fragment buy. Guess the truth assignment as the single unary relation variable
of `DescriptiveComplexity.satAssignBlock`, universally quantify three first-order
variables `c, x, y`, and emit:

* for each pair of signs `(s, u)`, the clause whose guard says “`c` is a clause,
  `(x, s)` and `(y, u)` are occurrences of `c`, and *every* occurrence of `c` is
  one of these two”, with the 2-clause `ℓ(x, s) ∨ ℓ(y, u)` as its body. A clause
  with a single occurrence is covered by instantiating `y := x`, `u := s`, which
  emits `ℓ(x, s) ∨ ℓ(x, s)`: no separate unit clause is needed;
* the goal clause guarded by “`c` is an empty clause” – an empty clause makes
  the CNF unsatisfiable;
* the goal clause guarded by “some clause has three distinct occurrences”
  (`DescriptiveComplexity.wideTwoOrdF`) – this is how the *width promise* of 2SAT is
  enforced from inside the fragment: guards are first-order over the input, so a
  promise costs one goal clause and no second-order machinery.

Correctness rests on `DescriptiveComplexity.exists_covering_pair`: under the width
bound, a clause with an occurrence has two signed occurrences covering all of
them, which is exactly the shape a single 2-clause can speak about.
-/

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

namespace TwoSatKrom

/-! ### The atoms and the guards -/

/-- The covering condition, as a formula over the ordered expansion: every
occurrence of the clause `0` is the occurrence `(1, s)` or the occurrence
`(2, u)`. -/
noncomputable def coverF (s u : Bool) : satOrd.Formula (Fin 3) :=
  (Formula.iInf fun t : Bool =>
    (occF t (Sum.inl 0) (Sum.inr 0)).imp
      ((if t = s then eqF (Sum.inr 0) (Sum.inl 1) else ⊥) ⊔
        if t = u then eqF (Sum.inr 0) (Sum.inl 2) else ⊥)).iAlls (Fin 1)

/-- The guard of the two-literal clause of the program: `0` is a clause whose
occurrences are exactly `(1, s)` and `(2, u)`. -/
noncomputable def pairGuard (s u : Bool) : satOrd.Formula (Fin 3) :=
  clF 0 ⊓ occF s 0 1 ⊓ occF u 0 2 ⊓ coverF s u

/-! ### Realization of the guards -/

section Realize

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A] {v : Fin 3 → A}

theorem realize_coverF {s u : Bool} :
    (coverF s u).Realize v ↔
      ∀ z t, Lax485149.TwoSat.SatOcc.OccIn (v 0) z t → (z = v 1 ∧ t = s) ∨ (z = v 2 ∧ t = u) := by
  simp only [coverF, Formula.realize_iAlls, Formula.realize_iInf, Formula.realize_imp,
    Formula.realize_sup, realize_occF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h z t hz
    rcases h (fun _ => z) t hz with h' | h'
    · left
      cases s <;> cases t <;> simp_all
    · right
      cases u <;> cases t <;> simp_all
  · intro h i t hi
    rcases h (i 0) t hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      subst h2
      simpa using h1
    · right
      subst h2
      simpa using h1

theorem realize_pairGuard {s u : Bool} :
    (pairGuard s u).Realize v ↔
      Lax485149.TwoSat.SatOcc.IsCl (v 0) ∧ Lax485149.TwoSat.SatOcc.OccIn (v 0) (v 1) s ∧ Lax485149.TwoSat.SatOcc.OccIn (v 0) (v 2) u ∧
        ∀ z t, Lax485149.TwoSat.SatOcc.OccIn (v 0) z t → (z = v 1 ∧ t = s) ∨ (z = v 2 ∧ t = u) := by
  simp only [pairGuard, Formula.realize_inf, realize_clF, realize_occF, realize_coverF]
  tauto

end Realize

/-! ### The program -/

/-! ### Assignments on both sides -/

section Assignments

end Assignments

/-! ### The program holds of a satisfying truth assignment -/

section Soundness

end Soundness

end TwoSatKrom

/-! ### 2SAT is SO-Krom definable -/

end Lax535992Proofs.DescriptiveComplexity


