/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Composition
import Lax799700Proofs.DescriptiveComplexity.Ordered
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Composition of ordered first-order reductions

Transitivity of `P ≤ᶠᵒ[≤] Q` (`Lax799700Proofs.DescriptiveComplexity.OrderedFOReduction.trans`), and the
mixed variants with plain FO reductions.

The obstacle to composing two ordered reductions with the plain composition
of `Lax799700Proofs.DescriptiveComplexity.Composition` is that the outer reduction's formulas mention
the *order of the intermediate structure*, which is not part of the inner
interpretation's output. The fix is classical: the interpreted universe
`Tag × A^dim` carries a linear order that is first-order definable from the
order of `A` – the lexicographic order comparing tags first (by an arbitrary
fixed linear order on the finite tag type; tag comparisons are static, i.e.,
resolved at formula-construction time), then the tuple coordinates in order.

Concretely:

* `Lax799700Proofs.DescriptiveComplexity.tagTupleLe` is the lexicographic order on `Tag × (Fin d → A)`,
  bundled as `Lax799700Proofs.DescriptiveComplexity.tagTupleOrder : LinearOrder (Tag × (Fin d → A))`
  (via Mathlib's `Prod.Lex` and `Pi.Lex`);
* `Lax799700Proofs.DescriptiveComplexity.lexLeF` is the corresponding first-order formula over the
  ordered expansion, with realization lemma `Lax799700Proofs.DescriptiveComplexity.realize_lexLeF`;
* `Lax799700Proofs.DescriptiveComplexity.FOInterpretation.ordExtend` extends an interpretation with
  target `L₂` to one with target `L₂.sum Language.order`, interpreting the
  order symbol by `lexLeF`; the interpreted structure is isomorphic to the
  original one equipped with the lexicographic order
  (`Lax799700Proofs.DescriptiveComplexity.FOInterpretation.ordExtendLEquiv`);
* `Lax799700Proofs.DescriptiveComplexity.OrderedFOReduction.trans` composes the outer interpretation
  with the extended inner one, using `FOInterpretation.comp`;
* `Lax799700Proofs.DescriptiveComplexity.FOReduction.toOrdered` upgrades a plain FO reduction to an
  ordered one (lifting its formulas along `LHom.sumInl`), giving the mixed
  transitivity variants `Lax799700Proofs.DescriptiveComplexity.OrderedFOReduction.trans_fo` and
  `Lax799700Proofs.DescriptiveComplexity.FOReduction.trans_ordered`, and `Trans` instances for all
  combinations.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### A linear order on any finite type -/

/-- An arbitrary linear order on a finite type, obtained by pulling back the
order of `Fin n` along an arbitrary enumeration. Used to order tags. -/
@[instance_reducible]
noncomputable def finiteLinearOrder (T : Type) [Finite T] : LinearOrder T :=
  letI := Fintype.ofFinite T
  LinearOrder.lift' (Fintype.equivFin T) (Fintype.equivFin T).injective

/-! ### The lexicographic order on tagged tuples -/

section LexOrder

variable {Tag : Type} [LinearOrder Tag] {d : ℕ} {A : Type} [LinearOrder A]

end LexOrder

/-! ### First-order formulas for the lexicographic order -/

section LexFormulas

variable {L : Language.{0, 0}}

variable {A : Type} [L.Structure A] [LinearOrder A] {α : Type} {v : α → A}

end LexFormulas

/-! ### Extending an interpretation with the lexicographic order -/

section OrdExtend

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational]

variable {T : Type} [LinearOrder T] {d : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation (L₁.sum Language.order) L₂ T d)

variable (A : Type) [L₁.Structure A] [LinearOrder A]

end OrdExtend

/-! ### Transitivity -/

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂} {R : Lax904597.Problems.DecisionProblem L₃}

end Trans

end Lax799700Proofs.DescriptiveComplexity


