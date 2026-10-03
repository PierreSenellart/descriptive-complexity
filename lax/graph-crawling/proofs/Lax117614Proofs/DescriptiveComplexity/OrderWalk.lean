/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Lax117614Proofs.DescriptiveComplexity.Ordered
import Lax117614.CrawlInstances
import Lax117614.GraphCrawlingProblem
import Lax117614.WebsiteGraphs
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
# Walking a finite linear order, first-order

Shared machinery for constructions that traverse a finite linear order – or the
lexicographic order on tuples – one step at a time, with each step described by
a first-order guard over the ordered expansion `L.sum Language.order`.

Two clients, one technique. The SO-Horn definition of HORN-SAT
(`Lax117614Proofs.DescriptiveComplexity.Problems.HornSat.Definability`) assembles the unbounded body of
an input clause by walking the order of its elements; the translation of
FO(LFP) into SO-Horn (`Lax117614Proofs.DescriptiveComplexity.FixedPointHorn`) walks the lexicographic
order of *stage* and *valuation* tuples to derive the complement of a fixed
point. Both need the same three ingredients, provided here:

* **guards**: formulas `Lax117614Proofs.DescriptiveComplexity.minF`, `Lax117614Proofs.DescriptiveComplexity.maxF`,
  `Lax117614Proofs.DescriptiveComplexity.succF` – being minimal, maximal, the immediate successor – and
  their tuple analogues `Lax117614Proofs.DescriptiveComplexity.minTupF`, `Lax117614Proofs.DescriptiveComplexity.maxTupF`,
  `Lax117614Proofs.DescriptiveComplexity.succTupF` for the lexicographic order, with realization lemmas
  phrased purely in terms of the order of the structure;
* **induction**: `Lax117614Proofs.DescriptiveComplexity.order_induction`, walking any finite linear order
  from its minimum along immediate successors – applied not only to the
  universe of a structure but to lexicographic tuple orders over it;
* **the bridge to `Lex`**: the coordinatewise conditions realized by the tuple
  guards characterize bottom, top and covering
  (`Lax117614Proofs.DescriptiveComplexity.tupSucc_iff_covBy`…) in `Lex (Fin D → A)`, and
  `Lax117614Proofs.DescriptiveComplexity.prodLex_covBy_iff`/`Lax117614Proofs.DescriptiveComplexity.finCovBy_iff` do the same for
  the lexicographic product heading a static index; so a walk described by
  guards is a walk along covers of a bona fide finite linear order.

Finally `Lax117614Proofs.DescriptiveComplexity.orank` – the rank of an element of a finite linear order,
the number of its strict predecessors – converts that walk into arithmetic:
rank `0` at the bottom (`Lax117614Proofs.DescriptiveComplexity.orank_eq_zero`), `+1` along a cover
(`Lax117614Proofs.DescriptiveComplexity.orank_covBy`), `Nat.card - 1` at the top
(`Lax117614Proofs.DescriptiveComplexity.orank_isTop`). This is how a fixed-point stage indexed by a
tuple is matched with the `ℕ`-indexed stages of
`Lax117614Proofs.DescriptiveComplexity.derivesIn`.
-/

namespace Lax117614Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Order guards -/

section Guards

variable {L : Language.{0, 0}} {α : Type}

/-- `x ≤ y`, as a formula over the ordered expansion. -/
noncomputable def leF (x y : α) : (L.sum Language.order).Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- The variable `x` holds a minimum. -/
noncomputable def minF (x : α) : (L.sum Language.order).Formula α :=
  (leF (Sum.inl x) (Sum.inr 0)).iAlls (Fin 1)

variable {A : Type} [L.Structure A] [LinearOrder A] {v : α → A}

@[simp]
theorem realize_leF (x y : α) : (leF (L := L) x y).Realize v ↔ v x ≤ v y := by
  rw [leF, Formula.realize_rel₂, relMap_leSymb]
  exact Iff.rfl

@[simp]
theorem realize_minF (x : α) : (minF (L := L) x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [minF]
  simp only [Formula.realize_iAlls, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

end Guards

/-! ### Immediate predecessors, and induction along a finite linear order -/

section Pred

variable {A : Type} [LinearOrder A] [Finite A]

end Pred

/-! ### The lexicographic successor of a tuple, coordinatewise -/

section TupSucc

variable {D : ℕ} {A : Type} [LinearOrder A]

end TupSucc

/-! ### Tuple guards, for the lexicographic order -/

section TupGuards

variable {D : ℕ} {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

end TupGuards

/-! ### The bridge to `Lex`: bottom, top and covering, coordinatewise

The tuple guards above speak coordinatewise; the walk they describe is along
the finite linear order `Lex (Fin D → A)`. These lemmas identify the two
languages. (`Lex` is a type synonym, so `Finite` and `Nonempty` instances are
provided for it here.) -/

section LexBridge

instance {α : Type*} [Finite α] : Finite (Lex α) := Finite.of_equiv α toLex

instance {α : Type*} [Nonempty α] : Nonempty (Lex α) := Nonempty.map toLex ‹_›

variable {D : ℕ} {A : Type} [LinearOrder A]

/-! #### The lexicographic product with a static head -/

variable {J B : Type} [LinearOrder J] [LinearOrder B]

end LexBridge

/-! ### Deciding the lexicographic order of two tuples

`Lax117614Proofs.DescriptiveComplexity.succTupF` *walks* the lexicographic order; the two
guards below *decide* it, which is what a reduction defining the order of its
image has to do. They are stated at arbitrary selectors `sel`, `sel'` into a
shared variable type, rather than at the fixed layout `Fin 2 × Fin D` of
`Lax117614Proofs.DescriptiveComplexity.lexTupleLeF`, because their consumers compare tuples
sitting at arbitrary positions among the free variables. -/

section LexDecide

variable {D : ℕ} {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

end LexDecide

/-! ### Reaching an element from below a cover -/

section CovByCases

variable {α : Type*} [LinearOrder α]

end CovByCases

/-! ### The rank of an element of a finite linear order -/

section Rank

variable {A : Type} [LinearOrder A]

variable [Finite A]

end Rank

end Lax117614Proofs.DescriptiveComplexity


