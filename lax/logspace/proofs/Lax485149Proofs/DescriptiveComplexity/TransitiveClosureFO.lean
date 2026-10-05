/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax485149Proofs.DescriptiveComplexity.FirstOrderDefinable
import Lax485149Proofs.DescriptiveComplexity.TransitiveClosureDet
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

namespace Lax485149.DeterministicTransitiveClosure
end Lax485149.DeterministicTransitiveClosure

namespace Lax485149.DeterministicTransitiveClosure.TCSpec
end Lax485149.DeterministicTransitiveClosure.TCSpec

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax485149Proofs.DescriptiveComplexity.FODefinable
end Lax485149Proofs.DescriptiveComplexity.FODefinable

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax485149Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCDefinable TCSpec)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax485149.DeterministicTransitiveClosure (DTCDefinable)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax485149.FirstOrderDefinability (FODefinable)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec
export Lax485149.DeterministicTransitiveClosure.TCSpec (det)
end Lax485149.TransitiveClosure.TCSpec

/-!
# First-order logic sits inside FO(TC), and inside FO(DTC)

The trivial half of `FO ⊆ FO(TC)`, needed to state the strict inclusion that
`DescriptiveComplexity.Problems.Even` proves: a sentence is the walk that
takes no step at all – arity `0`, one mode, no transition, the sentence as the
condition on starting nodes and nothing to check at the end. Reachability is
then reflexivity, and acceptance is the sentence.

The same walk is *deterministic*, and for the cheapest of reasons: a walk with
no step has no step with a competitor either, so nothing in the argument reads
the transition formula and the proof of
`DescriptiveComplexity.accepts_det_sentenceSpec_iff` is the proof of
`DescriptiveComplexity.accepts_sentenceSpec_iff` again. That gives
`FO(≤) ⊆ FO(DTC)` (`DescriptiveComplexity.FODefinable.dtcDefinable`), hence
`FO(≤) ⊆ L` through `DescriptiveComplexity.mem_LOGSPACE_iff` – the end of the
chain `FO(≤) ⊊ AC⁰ ⊆ L ⊆ NL` that would otherwise be left implicit, since the
strict half of it (`DescriptiveComplexity.exists_ac0Definable_not_foDefinable`)
says nothing about where FO(≤) itself sits.

The converse fails, unconditionally: `EVEN` is a walk and is not a sentence
(`DescriptiveComplexity.exists_tcDefinable_not_foDefinable`).
-/

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The walk that takes no step: the sentence decides the starting node, and
the node it starts at is already accepting. -/
noncomputable def sentenceSpec (φ : (L.sum Language.order).Sentence) : Lax485149.TransitiveClosure.TCSpec L where
  Mode := Unit
  k := 0
  step _ _ := ⊥
  src _ := φ.relabel Empty.elim
  tgt _ := ⊤

omit [L.IsRelational] in
/-- A node of the walk is a starting node exactly when the sentence holds: the
tuple is empty, so there is nothing for the relabeling to carry. -/
theorem isSrc_sentenceSpec_iff (φ : (L.sum Language.order).Sentence) {A : Type}
    [L.Structure A] [LinearOrder A] (u : (sentenceSpec φ).Node A) :
    (sentenceSpec φ).IsSrc u ↔ A ⊨ φ := by
  change (Formula.relabel Empty.elim φ).Realize u.2 ↔ _
  rw [Formula.realize_relabel]
  have hv : (u.2 ∘ Empty.elim) = (default : Empty → A) := funext fun e => e.elim
  rw [hv]
  exact Iff.rfl

omit [L.IsRelational] in
/-- The *deterministic* reading of the same walk accepts on the same instances.
The proof does not mention the transition formula at all – neither direction
takes a step – which is precisely why determinization costs nothing here. -/
theorem accepts_det_sentenceSpec_iff (φ : (L.sum Language.order).Sentence) (A : Type)
    [L.Structure A] [LinearOrder A] [Nonempty A] :
    (sentenceSpec φ).det.Accepts A ↔ A ⊨ φ := by
  constructor
  · rintro ⟨u, -, hu, -, -⟩
    exact (isSrc_sentenceSpec_iff φ u).mp hu
  · intro h
    refine ⟨((), fun _ => Classical.arbitrary A), ((), fun _ => Classical.arbitrary A),
      (isSrc_sentenceSpec_iff φ _).mpr h, ?_, Relation.ReflTransGen.refl⟩
    exact Formula.realize_top.mpr trivial

/-- **A first-order definable problem is FO(DTC) definable**, hence in
`DescriptiveComplexity.LOGSPACE` by `DescriptiveComplexity.mem_LOGSPACE_iff`:
the walk that takes no step is deterministic for want of any step to compete. -/
theorem FODefinable.dtcDefinable {P : Lax904597.Problems.DecisionProblem L} (h : Lax485149.FirstOrderDefinability.FODefinable P) :
    Lax485149.DeterministicTransitiveClosure.DTCDefinable P := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨sentenceSpec φ, fun A _ _ _ _ => (hφ A).trans (accepts_det_sentenceSpec_iff φ A).symm⟩

end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149.FirstOrderDefinability.FODefinable

export Lax485149Proofs.DescriptiveComplexity.FODefinable (dtcDefinable)

end Lax485149.FirstOrderDefinability.FODefinable

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

end Lax485149Proofs.DescriptiveComplexity


