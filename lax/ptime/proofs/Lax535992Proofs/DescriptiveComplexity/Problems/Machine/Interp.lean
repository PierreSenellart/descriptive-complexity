/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax535992Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax535992Proofs.DescriptiveComplexity.Problems.Machine.Hardness
import Lax535992Proofs.DescriptiveComplexity.OccurrenceFormulas
import Lax535992Proofs.DescriptiveComplexity.OrderWalk
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

namespace Lax485149.TwoSat.SatOcc
end Lax485149.TwoSat.SatOcc

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Machines (TMAcc TMBlank TMDst TMInp TMLe TMPosn TMRead TMRight TMSrc TMStart TMTr TMWrite tmData)
end Lax535992Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Machines (turing)
end FirstOrder.Language

namespace Lax535992Proofs.DescriptiveComplexity.SatOcc
export Lax485149.TwoSat.SatOcc (NegIn PosIn)
end Lax535992Proofs.DescriptiveComplexity.SatOcc

/-!
# The transcription: `SAT ≤ᶠᵒ[≤] NTMAccept`

The first-order half of the reduction. The machine of a CNF formula was built
*semantically* in `DescriptiveComplexity.Problems.Machine.Hardness` – plain predicates
on tagged tuples, with its correctness `DescriptiveComplexity.satMachine_accepts_iff_satisfiable`
proved there. This file writes the defining formulas of an interpretation of
`Language.turing` in ordered CNF instances, shows each formula realizes exactly
the corresponding predicate of the machine, and bundles the result as the
ordered first-order reduction `DescriptiveComplexity.SatTM.sat_ordered_fo_reduction_ntmAccept`.

## Method

Everything is arranged so that no `simp` call ever faces a tag `match`:

* the binary symbols' formulas are written through two **shape helpers** –
  `cstF s` (“the second argument is the constant element pinned to the minima”)
  and `oneF s x` (“the second argument carries the tag `s` and the payload held
  by the variable `x`”) – matching the two shapes `DescriptiveComplexity.cst` and
  `DescriptiveComplexity.one` every state, symbol and transition of the machine has;
  each has one realization lemma, so each defining formula needs a `match` on
  its **first** tag only;
* realization lemmas take the valuation abstractly, with the values of the
  needed variables as equation hypotheses; at the call sites these are
  discharged by `rfl`, since the interpreted valuation reduces definitionally
  on concrete tags.

The transfer to `DescriptiveComplexity.NTMAccept` is then a fieldwise
`DescriptiveComplexity.TMData.Agree` along the identity equivalence: the machine the
interpreted structure describes agrees with `DescriptiveComplexity.satMachine`, so
acceptance and well-formedness transport, and correctness is inherited from the
semantic layer.
-/

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

namespace SatTM

open Language Structure SatOcc

/-! ### Formulas for the clause order -/

section Builders

variable {α : Type}

/-- `c` is the lowest clause, as a formula. -/
noncomputable def minClF (c : α) : satOrd.Formula α :=
  clF c ⊓ Formula.iAlls Unit (clF (Sum.inr ()) ⟹ SatOcc.leF (Sum.inl c) (Sum.inr ()))

/-- `c` is the highest clause, as a formula. -/
noncomputable def maxClF (c : α) : satOrd.Formula α :=
  clF c ⊓ Formula.iAlls Unit (clF (Sum.inr ()) ⟹ SatOcc.leF (Sum.inr ()) (Sum.inl c))

/-- `c'` is the clause immediately above `c`, as a formula. -/
noncomputable def nextClF (c c' : α) : satOrd.Formula α :=
  clF c ⊓ clF c' ⊓ SatOcc.ltF c c' ⊓
    Formula.iAlls Unit ((clF (Sum.inr ()) ⊓ SatOcc.ltF (Sum.inl c) (Sum.inr ())) ⟹
      SatOcc.leF (Sum.inl c') (Sum.inr ()))

/-- There is no clause at all, as a formula. -/
noncomputable def noClF : satOrd.Formula α :=
  Formula.iAlls Unit (∼(clF (Sum.inr () : α ⊕ Unit)))

end Builders

section BuilderRealize

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

theorem realize_minClF {x : α} {c : A} (h : v x = c) :
    (minClF x).Realize v ↔ SatMinCl c := by
  simp only [minClF, Formula.realize_inf, realize_clF, Formula.realize_iAlls,
    Formula.realize_imp, SatOcc.realize_leF, Sum.elim_inl, Sum.elim_inr, h, SatMinCl]
  exact and_congr Iff.rfl ⟨fun hh e he => hh (fun _ => e) he, fun hh i hi => hh (i ()) hi⟩

theorem realize_maxClF {x : α} {c : A} (h : v x = c) :
    (maxClF x).Realize v ↔ SatMaxCl c := by
  simp only [maxClF, Formula.realize_inf, realize_clF, Formula.realize_iAlls,
    Formula.realize_imp, SatOcc.realize_leF, Sum.elim_inl, Sum.elim_inr, h, SatMaxCl]
  exact and_congr Iff.rfl ⟨fun hh e he => hh (fun _ => e) he, fun hh i hi => hh (i ()) hi⟩

theorem realize_nextClF {x y : α} {c c' : A} (hx : v x = c) (hy : v y = c') :
    (nextClF x y).Realize v ↔ SatNextCl c c' := by
  simp only [nextClF, Formula.realize_inf, realize_clF, SatOcc.realize_ltF,
    Formula.realize_iAlls, Formula.realize_imp, SatOcc.realize_leF, Sum.elim_inl,
    Sum.elim_inr, hx, hy, SatNextCl]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun e he hce => h4 (fun _ => e) ⟨he, hce⟩⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, fun i hi => h4 (i ()) hi.1 hi.2⟩

theorem realize_noClF : (noClF (α := α)).Realize v ↔ ∀ e : A, ¬ SatCl e := by
  simp only [noClF, Formula.realize_iAlls, Formula.realize_not, realize_clF, Sum.elim_inr]
  exact ⟨fun h e => h fun _ => e, fun h i => h (i ())⟩

end BuilderRealize

/-! ### The two shapes of the machine's elements, as formulas -/

section Shapes

end Shapes

/-! ### The defining formulas -/

/-! ### The realization lemmas

One per symbol of `Language.turing`, each saying its defining formula defines
the corresponding predicate of `DescriptiveComplexity.satMachine`. The universe of the
interpreted structure is definitionally `DescriptiveComplexity.SatV A`;
`DescriptiveComplexity.SatTM.satMapEquiv` names the identity equivalence, along which
the machines will be shown to agree. -/

section Characterize

/-! ### The machines agree, and the reduction -/

end Characterize

end SatTM

end Lax535992Proofs.DescriptiveComplexity


