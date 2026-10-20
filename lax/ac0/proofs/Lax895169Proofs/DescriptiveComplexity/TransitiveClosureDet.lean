/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.TransitiveClosure
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

namespace Lax485149.DeterministicTransitiveClosure
end Lax485149.DeterministicTransitiveClosure

namespace Lax485149.DeterministicTransitiveClosure.TCSpec
end Lax485149.DeterministicTransitiveClosure.TCSpec

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax895169Proofs.DescriptiveComplexity.DTCDefinable
end Lax895169Proofs.DescriptiveComplexity.DTCDefinable

namespace Lax895169Proofs.DescriptiveComplexity.TCSpec
end Lax895169Proofs.DescriptiveComplexity.TCSpec

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCDefinable TCSpec)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.DeterministicTransitiveClosure (DTCDefinable)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec
export Lax485149.DeterministicTransitiveClosure.TCSpec (det detStep detVar)
end Lax485149.TransitiveClosure.TCSpec

/-!
# FO(DTC): first-order logic with deterministic transitive closure

The logic that captures *deterministic* logarithmic space on ordered
structures ([Immerman 1987][immerman1987languages]): first-order logic with a
transitive-closure operator that may only follow a step when it is the *only*
step available. `DescriptiveComplexity.LOGSPACE` is defined by it, exactly as
`DescriptiveComplexity.NL` is defined by the Krom fragment and
`DescriptiveComplexity.PTIME` by the Horn one.

## Determinism as a formula, not as a side condition

There are two ways to say “the walk is deterministic”. One is to carry a
proof: a specification together with the hypothesis that its `Step` relation is
functional on every structure. That is the wrong choice here – the hypothesis is
not first-order data, and it would have to be re-established after every
pullback, at which point closure under reductions stops being a syntactic
argument.

The other is Immerman's own: keep an arbitrary
`DescriptiveComplexity.TCSpec` and read its transition formula through its
*determinization*

```
detStep(x̄, ȳ)  :=  step(x̄, ȳ)  ∧  ∀ z̄. step(x̄, z̄) → z̄ = ȳ
```

which is again first-order. Every specification then denotes a legitimate
deterministic walk (`DescriptiveComplexity.TCSpec.det_functional`), nothing has to be
preserved, and nothing is lost: on a specification whose steps are already
functional the determinization is equivalent to it
(`DescriptiveComplexity.TCSpec.det_step_of_functional`).

The one wrinkle the textbook formula does not show is **modes**. A node of a
`DescriptiveComplexity.TCSpec` is a mode together with a tuple
(`DescriptiveComplexity.TCSpec.Node`), so “the only step available” has to quantify
over successor *nodes*, not successor tuples: the uniqueness clause is a finite
conjunction over the modes, in which the mode comparison is resolved at
formula-construction time (`⊥` for a mode other than the intended target, so
that a step into it refutes the guard). This is the same static/dynamic split
as the tag comparisons of `DescriptiveComplexity.lexLeF`.

## What is here

`DescriptiveComplexity.TCSpec.det` and its semantics
(`DescriptiveComplexity.TCSpec.det_step_iff`: a determinized step is a step with no
competitor), the resulting definability notion
`DescriptiveComplexity.DTCDefinable`, and the inclusion at the level of definability,
`DescriptiveComplexity.DTCDefinable.tcDefinable` – the future `L ⊆ NL`, a one-liner
because a determinized specification *is* a specification.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

/-! ### Determinizing the transition formula -/

section Det

variable (spec : Lax485149.TransitiveClosure.TCSpec L)

@[simp]
theorem det_mode : spec.det.Mode = spec.Mode := rfl

end Det

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (det_mode)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section Det

variable (spec : Lax485149.TransitiveClosure.TCSpec L)

@[simp]
theorem det_k : spec.det.k = spec.k := rfl

end Det

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (det_k)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section Det

variable (spec : Lax485149.TransitiveClosure.TCSpec L)

end Det

/-! ### Semantics of the determinization -/

section DetSemantics

variable (spec : Lax485149.TransitiveClosure.TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_detStep (m n : spec.Mode) (x y : Fin spec.k → A) :
    (spec.detStep m n).Realize (Sum.elim x y) ↔
      (spec.step m n).Realize (Sum.elim x y) ∧
        ∀ (m' : spec.Mode) (z : Fin spec.k → A),
          (spec.step m m').Realize (Sum.elim x z) → m' = n ∧ z = y := by
  classical
  rw [Lax485149.DeterministicTransitiveClosure.TCSpec.detStep, Formula.realize_inf, Formula.realize_iInf]
  refine and_congr Iff.rfl ⟨fun h m' z hz => ?_, fun h m' => ?_⟩
  · have hm := (Formula.realize_iAlls).mp (h m') z
    rw [Formula.realize_imp, Formula.realize_relabel] at hm
    have hrel : (Sum.elim (Sum.elim x y) z) ∘ spec.detVar = Sum.elim x z := by
      funext i
      rcases i with i | i <;> rfl
    rw [hrel] at hm
    have hc := hm hz
    by_cases hmn : m' = n
    · refine ⟨hmn, ?_⟩
      rw [if_pos hmn, Formula.realize_iInf] at hc
      funext i
      have := hc i
      rw [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
      exact this
    · rw [if_neg hmn, Formula.realize_bot] at hc
      exact hc.elim
  · refine Formula.realize_iAlls.mpr fun z => ?_
    rw [Formula.realize_imp, Formula.realize_relabel]
    have hrel : (Sum.elim (Sum.elim x y) z) ∘ spec.detVar = Sum.elim x z := by
      funext i
      rcases i with i | i <;> rfl
    rw [hrel]
    intro hz
    obtain ⟨hmn, hzy⟩ := h m' z hz
    rw [if_pos hmn, Formula.realize_iInf]
    intro i
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact congrFun hzy i

end DetSemantics

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (realize_detStep)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section DetSemantics

variable (spec : Lax485149.TransitiveClosure.TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

/-- **A determinized step is a step with no competitor**: the node `b` is
reached from `a` in the deterministic walk exactly when it is reached in the
original one and is the only node so reached. -/
theorem det_step_iff (a b : spec.Node A) :
    spec.det.Step a b ↔ spec.Step a b ∧ ∀ c : spec.Node A, spec.Step a c → c = b := by
  change (spec.detStep a.1 b.1).Realize (Sum.elim a.2 b.2) ↔ _
  rw [realize_detStep]
  refine and_congr Iff.rfl ⟨fun h c hc => ?_, fun h m' z hz => ?_⟩
  · obtain ⟨hm, hz⟩ := h c.1 c.2 hc
    exact Prod.ext_iff.mpr ⟨hm, hz⟩
  · have := h (m', z) hz
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

end DetSemantics

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (det_step_iff)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section DetSemantics

variable (spec : Lax485149.TransitiveClosure.TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

/-- The source nodes of the deterministic reading are those of the original. -/
@[simp]
theorem det_isSrc (a : spec.Node A) : spec.det.IsSrc a ↔ spec.IsSrc a := Iff.rfl

end DetSemantics

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (det_isSrc)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section DetSemantics

variable (spec : Lax485149.TransitiveClosure.TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

/-- The accepting nodes of the deterministic reading are those of the
original. -/
@[simp]
theorem det_isTgt (a : spec.Node A) : spec.det.IsTgt a ↔ spec.IsTgt a := Iff.rfl

end DetSemantics

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (det_isTgt)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section DetSemantics

variable (spec : Lax485149.TransitiveClosure.TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

end DetSemantics

/-! ### Functional specifications -/

section Functional

variable (spec : Lax485149.TransitiveClosure.TCSpec L) (A : Type) [L.Structure A] [LinearOrder A]

/-- A specification is *functional* on a structure when every node has at most
one successor: the walk it describes is deterministic outright. -/
def Functional : Prop :=
  ∀ a b c : spec.Node A, spec.Step a b → spec.Step a c → b = c

end Functional

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (Functional)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section Functional

variable (spec : Lax485149.TransitiveClosure.TCSpec L) (A : Type) [L.Structure A] [LinearOrder A]

variable {spec A}

/-- **The deterministic reading is functional**, whatever the specification it
comes from: this is what makes determinization the right packaging, there
being nothing left to assume. -/
theorem det_functional : spec.det.Functional A := by
  intro a b c hb hc
  obtain ⟨-, hu⟩ := (spec.det_step_iff a b).mp hb
  exact (hu c ((spec.det_step_iff a c).mp hc).1).symm

end Functional

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (det_functional)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section Functional

variable (spec : Lax485149.TransitiveClosure.TCSpec L) (A : Type) [L.Structure A] [LinearOrder A]

variable {spec A}

/-- **Determinizing a functional specification changes nothing**: no step had
a competitor to begin with. -/
theorem det_step_of_functional (h : spec.Functional A) (a b : spec.Node A) :
    spec.det.Step a b ↔ spec.Step a b := by
  rw [spec.det_step_iff a b]
  exact ⟨And.left, fun hab => ⟨hab, fun c hc => h a c b hc hab⟩⟩

end Functional

end TCSpec

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax895169Proofs.DescriptiveComplexity.TCSpec (det_step_of_functional)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCSpec

section Functional

variable (spec : Lax485149.TransitiveClosure.TCSpec L) (A : Type) [L.Structure A] [LinearOrder A]

variable {spec A}

end Functional

end TCSpec

/-! ### FO(DTC) definability -/

/-- FO(DTC) definability only depends on the finite instances of a problem. -/
theorem dtcDefinable_congr [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax485149.DeterministicTransitiveClosure.DTCDefinable P ↔ Lax485149.DeterministicTransitiveClosure.DTCDefinable Q := by
  constructor <;> rintro ⟨spec, hspec⟩ <;> refine ⟨spec, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hspec A)
  · exact (h A).trans (hspec A)

/-- **FO(DTC) ⊆ FO(TC)**, the definability-level `L ⊆ NL`: a determinized
specification is a specification like any other. -/
theorem DTCDefinable.tcDefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L} (h : Lax485149.DeterministicTransitiveClosure.DTCDefinable P) :
    Lax485149.TransitiveClosure.TCDefinable P := by
  obtain ⟨spec, hspec⟩ := h
  exact ⟨spec.det, hspec⟩

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.DeterministicTransitiveClosure.DTCDefinable

export Lax895169Proofs.DescriptiveComplexity.DTCDefinable (tcDefinable)

end Lax485149.DeterministicTransitiveClosure.DTCDefinable

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

end Lax895169Proofs.DescriptiveComplexity


