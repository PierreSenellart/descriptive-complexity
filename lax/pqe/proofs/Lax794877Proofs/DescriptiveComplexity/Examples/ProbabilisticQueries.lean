/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax794877Proofs.DescriptiveComplexity.Counting.UnitWeights
import Lax794877Proofs.DescriptiveComplexity.Counting
import Lax794877Proofs.DescriptiveComplexity.Decoding
import Lax794877Proofs.DescriptiveComplexity.Encoding
import Lax794877Proofs.DescriptiveComplexity.Numbers.BinEnum
import Lax794877Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingBipartite
import Lax794877Proofs.DescriptiveComplexity.Counting.WeightedTerms
import Lax794877Proofs.DescriptiveComplexity.Counting.FP
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax794877.ExampleDatabase
end Lax794877.ExampleDatabase

namespace Lax794877.PossibleWorlds
end Lax794877.PossibleWorlds

namespace Lax794877.Queries
end Lax794877.Queries

namespace Lax794877.WeightedWorlds
end Lax794877.WeightedWorlds

namespace Lax794877Proofs.DescriptiveComplexity.FactStatus
end Lax794877Proofs.DescriptiveComplexity.FactStatus

namespace Lax794877Proofs.DescriptiveComplexity.ProbDb
end Lax794877Proofs.DescriptiveComplexity.ProbDb

namespace Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches
end Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches

namespace Lax799700.Common
end Lax799700.Common

namespace Lax859101.CountingBipartite
end Lax859101.CountingBipartite

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.PossibleWorlds (IsWorld worldBlock worldStructure)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.WeightedWorlds (Fact IsOpen WLe WeightedRel absWeight bitsOf presWeight weightedLang worldProb)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.Queries (h0 instFiniteSigmaNatRelationsRst rs)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.ExampleDatabase (FactStatus HoldsH0 ProbDb World instDecidableHoldsH0)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.Common (binNum)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (QTerm)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax859101.CountingBipartite (BGEdge BGLeft Pp2dnfModel)
end Lax794877Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax794877.Queries (rst rstR rstS rstT)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax859101.CountingBipartite (bgEdge bgLeft bipGraph)
end FirstOrder.Language

/-!
# Worked example: query evaluation over probabilistic databases

This file is a *tutorial*, read top to bottom like
`DescriptiveComplexity.Examples.ConjunctiveQueries`, and the first one about a
**counting** problem. The domain is probabilistic databases: a database whose
facts are present independently, each with its own probability, and the
problem of computing the probability that a fixed Boolean query holds
(*probabilistic query evaluation*). Its data complexity is `#P`-hard already
for the conjunctive query

`h₀ = ∃ x y, R(x) ∧ S(x, y) ∧ T(y)`

([Dalvi and Suciu 2012][dalvi2012dichotomy], Proposition 5.2), which is the
first result formalized here; the second is that on the same instances the
query

`∃ x y, R(x) ∧ S(x, y)`

is *easy*: the numerator of its probability is in FP, the polynomial-time
functions. The two queries are the smallest pair on the two sides of the
dichotomy of that paper, the second being hierarchical and the first not; the
dichotomy itself is not formalized, and nothing here is generic in the query.

## The model

A fact is *certain*, or it is *uncertain* and present with some probability,
independently of the others. The file works in two stages.

* **Uniform probability.** Steps 1 to 6 take every uncertain fact to be
  present with probability `1/2`. A probability is then a count: with `k`
  uncertain facts there are `2 ^ k` equally likely possible worlds
  (`DescriptiveComplexity.card_isWorld`), and the probability of a query is
  the number of worlds in which it holds, divided by `2 ^ k`. This is all the
  hardness of `h₀` needs.
* **Probabilities in the instance.** Step 7 gives each uncertain fact its own
  probability `a / (a + c)`, as two natural weights written in binary
  (`DescriptiveComplexity.Counting.WeightedWorlds`). The probability of a
  query is then a ratio of two numbers,
  `WeightedWorlds φ / WeightedWorlds ⊤`
  (`DescriptiveComplexity.funcProb_holdsEvent_eq_ratio`), both of them in `#P`
  for *every* first-order query
  (`DescriptiveComplexity.weightedWorlds_mem_sharpP`). The uniform case is the
  case where all weights are `1`, so the hardness of `h₀` carries over to the
  numerator.

## The steps

1. **Vocabulary.** The schema `FirstOrder.Language.rst` of the query; an
   instance is a structure over two copies of it, certain facts and uncertain
   ones. This step, and the next two, are generic in the schema and are
   library helpers, in `DescriptiveComplexity.Counting.PossibleWorlds`.
2. **Semantics.** A possible world keeps the certain facts and some of the
   uncertain ones (`DescriptiveComplexity.IsWorld`), and
   `DescriptiveComplexity.PossibleWorlds φ` counts the worlds satisfying `φ`.
3. **Membership.** A world is one relation per symbol of the schema, so the
   problem counts the witnesses of a first-order kernel: it is in `#P` for
   *every* first-order query (`DescriptiveComplexity.possibleWorlds_mem_sharpP`).
   Nothing is specific to `h₀` up to here.
4. **The query**, `DescriptiveComplexity.h0`, and what it says of a world
   (`DescriptiveComplexity.realize_h0`).
5. **Hardness.** From #PP2DNF (`DescriptiveComplexity.SharpPP2DNF`), the models
   of `⋁ (x ∧ y)` over the edges of a bipartite graph. The instance has the
   edges as certain `S`-facts, the left vertices as uncertain `R`-facts and the
   right vertices as uncertain `T`-facts
   (`DescriptiveComplexity.h0Interp`); a world is then a set of vertices, and
   `h₀` holds in it exactly when some edge has both ends chosen
   (`DescriptiveComplexity.possibleWorlds_h0_eq`). The reduction is
   parsimonious, one-dimensional and quantifier-free.
6. **The theorem**: counting the worlds of `h₀` is one-call `#P`-complete
   (`DescriptiveComplexity.possibleWorlds_h0_sharpP_oneCallComplete`).
7. **Probabilities in the instance**: the numerator of the probability of
   `h₀` is one-call `#P`-complete
   (`DescriptiveComplexity.weightedWorlds_h0_sharpP_oneCallComplete`), by the
   ordered parsimonious reduction from the uniform case
   (`DescriptiveComplexity.possibleWorlds_ordered_parsimonious_weightedWorlds`).
8. **A concrete database.** `DescriptiveComplexity.ProbDb` is a probabilistic
   database in plain terms: `n` constants and, for each possible fact, whether
   it is absent, certain, or uncertain with two weights. Its weighted count
   `DescriptiveComplexity.ProbDb.count` and its total weight
   `DescriptiveComplexity.ProbDb.total` are *computed* (the `#guard`s at the
   end run them). `DescriptiveComplexity.probDbEncoding` encodes a database as
   a weighted instance, with the size bounds of
   `DescriptiveComplexity.Encoding` discharged, and it is faithful
   (`DescriptiveComplexity.probDbEncoding_countFaithful`,
   `DescriptiveComplexity.probDbEncoding_countFaithful_total`): the abstract
   counting problems return, on the encoded instance, the two numbers computed
   from the database. So the probability of `h₀` over a database is
   `count / total` (`DescriptiveComplexity.probDb_worldProb_eq`).

## What kind of hardness

#PP2DNF is itself complete under one-call reductions only, so the statement
is one-call completeness, not plain completeness: every problem of `#P` is
answered by one question about the probability of `h₀`, followed by
arithmetic. A formula of this kind always has a world in which it holds as
soon as the graph has an edge, so no parsimonious reduction from #SAT can
exist unless `P = NP`. Whether the problem is complete under subtractive
reductions is not known here.

9. **The decoder.** `DescriptiveComplexity.probDbDecode` reads a database
   back from any presented weighted instance whose position order is linear,
   by a computation (it runs, too), and the database has the weighted count of
   the instance (`DescriptiveComplexity.probDbDecoding`, a
   `DescriptiveComplexity.CountDecoding`). So the hardness of the abstract
   problem is hardness on instances that are databases.

## The easy query

Steps 10 to 15 are the second result, on the same weighted instances.

10. **The query**, `DescriptiveComplexity.rs`.
11. **The weights.** Every fact is a Boolean variable with a weight of
    presence and a weight of absence
    (`DescriptiveComplexity.Counting.WeightedFacts`); the facts of the schema
    are the `R`-facts, the `S`-facts and the `T`-facts
    (`DescriptiveComplexity.factEquiv`).
12. **Failing is a product.** The query fails in a world when no `x` has both
    `R(x)` and some `S(x, y)`. Given which `R`-facts are present, this
    constrains each `S`-fact separately; summing over the `R`-facts then
    factorizes too. The weight of the worlds in which the query fails is
    `∏x. F(x)`, times the total weight of the `T`-facts
    (`DescriptiveComplexity.SafeQ.weightedCount_fail`), `F(x)` being the
    weight of failing at `x`.
13. **Succeeding, without a subtraction.** The weight of the worlds in which
    the query holds is the total weight minus that product. A quantitative
    term has no subtraction; the *first success* identity
    (`DescriptiveComplexity.prod_add_eq_prod_add_sum`) removes it, by sorting
    the worlds by the first `x` at which the query succeeds – and, inside the
    weight of succeeding at `x`, by the first `y`
    (`DescriptiveComplexity.SafeQ.weightedWorlds_rs_eq`).
14. **The term.** The closed form is a term of quantitative first-order logic
    over the instance, its leaves being the weights, read in binary
    (`DescriptiveComplexity.SafeQ.rsT`). The order it sorts by is the order of
    the definition, on which the value does not depend.
15. **The theorem**: `DescriptiveComplexity.weightedWorlds_rs_mem_FP`.

Steps 12 and 13 use the library's lemmas on independent Boolean variables
(`DescriptiveComplexity.Counting.Independence`), and step 14 its helpers for
writing terms (`DescriptiveComplexity.Counting.QuantitativeBinders`,
`DescriptiveComplexity.Counting.WeightedTerms`).

## The concrete step, and what it relies on

The two other tutorials open with the concrete instances; here they come last
(steps 8 and 9), the hardness result needing none of it. The encoder and the
decoder are two corollaries of one theorem: an instance that *matches* a
database (`DescriptiveComplexity.ProbDb.Matches`) has its counts
(`DescriptiveComplexity.ProbDb.Matches.count_eq`). The step is short because
its two generic ingredients are library lemmas: the binary digits written by
an encoder decode to the number they came from
(`DescriptiveComplexity.binNum_fin_of_testBit`, in
`DescriptiveComplexity.Numbers.BinEnum`), and faithfulness for a counting
problem is `DescriptiveComplexity.Encoding.CountFaithful`. What remains is
specific to the database format: reading a status off each fact
(`DescriptiveComplexity.factWeight_of_status`) and matching the abstract
worlds and facts with the three tables of a concrete world
(`DescriptiveComplexity.worldEquiv`, `DescriptiveComplexity.factEquiv`).

One restriction of the format is deliberate: the weights are written on `n`
bits, `n` being the number of constants, since the constants double as bit
positions. A database with longer weights is padded with unused constants.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ## Steps 1 and 4: the schema, and the query -/

theorem realize_h0 {B : Type} (ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment B) :
    @Sentence.Realize Lax794877.Queries.rst B (Lax794877.PossibleWorlds.worldStructure ρ) Lax794877.Queries.h0 ↔
      ∃ a b : B, ρ ⟨1, Lax794877.Queries.rstR⟩ ![a] ∧ ρ ⟨2, Lax794877.Queries.rstS⟩ ![a, b] ∧ ρ ⟨1, Lax794877.Queries.rstT⟩ ![b] := by
  let := Lax794877.PossibleWorlds.worldStructure ρ
  rw [Lax794877.Queries.h0]
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr]
  constructor
  · rintro ⟨v, h⟩
    exact ⟨v 0, v 1, h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨![a, b], h⟩

/-! ## Step 5: hardness, from #PP2DNF -/

section Semantic

variable {A B : Type} [Lax859101.CountingBipartite.bipGraph.Structure A] [(Lax794877.Queries.rst.sum Lax794877.Queries.rst).Structure B]

/-- **The worlds of a bipartite graph.** Let the instance `B` hold a bipartite
graph `A` this way: `S` is certain and is the set of edges from the left side
to the right side, `R` is uncertain and is the left side, `T` is uncertain and
is the right side. Then the worlds satisfying `h₀` are as many as the models
of the partitioned positive 2-DNF formula of the graph: a world is a set of
left vertices and a set of right vertices, and `h₀` says that some edge has
both its ends chosen. -/
theorem possibleWorlds_h0_eq (e : A ≃ B)
    (hcR : ∀ x : Fin 1 → B, ¬RelMap (L := Lax794877.Queries.rst.sum Lax794877.Queries.rst) (Sum.inl Lax794877.Queries.rstR) x)
    (hcT : ∀ x : Fin 1 → B, ¬RelMap (L := Lax794877.Queries.rst.sum Lax794877.Queries.rst) (Sum.inl Lax794877.Queries.rstT) x)
    (hcS : ∀ x : Fin 2 → B, RelMap (L := Lax794877.Queries.rst.sum Lax794877.Queries.rst) (Sum.inl Lax794877.Queries.rstS) x ↔
      Lax859101.CountingBipartite.BGLeft (e.symm (x 0)) ∧ ¬Lax859101.CountingBipartite.BGLeft (e.symm (x 1)) ∧ Lax859101.CountingBipartite.BGEdge (e.symm (x 0)) (e.symm (x 1)))
    (huR : ∀ x : Fin 1 → B, RelMap (L := Lax794877.Queries.rst.sum Lax794877.Queries.rst) (Sum.inr Lax794877.Queries.rstR) x ↔
      Lax859101.CountingBipartite.BGLeft (e.symm (x 0)))
    (huT : ∀ x : Fin 1 → B, RelMap (L := Lax794877.Queries.rst.sum Lax794877.Queries.rst) (Sum.inr Lax794877.Queries.rstT) x ↔
      ¬Lax859101.CountingBipartite.BGLeft (e.symm (x 0)))
    (huS : ∀ x : Fin 2 → B, ¬RelMap (L := Lax794877.Queries.rst.sum Lax794877.Queries.rst) (Sum.inr Lax794877.Queries.rstS) x) :
    PossibleWorlds Lax794877.Queries.h0 B = SharpPP2DNF A := by
  rw [possibleWorlds_apply, sharpPP2DNF_apply]
  symm
  -- The world of a set of vertices.
  let F : (A → Prop) → (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment B := fun S p =>
    match p with
    | ⟨_, .r⟩ => fun x : Fin 1 → B => S (e.symm (x 0)) ∧ Lax859101.CountingBipartite.BGLeft (e.symm (x 0))
    | ⟨_, .s⟩ => fun x : Fin 2 → B =>
      RelMap (L := Lax794877.Queries.rst.sum Lax794877.Queries.rst) (Sum.inl Lax794877.Queries.rstS) x
    | ⟨_, .t⟩ => fun x : Fin 1 → B => S (e.symm (x 0)) ∧ ¬Lax859101.CountingBipartite.BGLeft (e.symm (x 0))
  have hFr : ∀ S a, F S ⟨1, Lax794877.Queries.rstR⟩ ![e a] ↔ S a ∧ Lax859101.CountingBipartite.BGLeft a := fun S a => by
    change S (e.symm (e a)) ∧ Lax859101.CountingBipartite.BGLeft (e.symm (e a)) ↔ _
    rw [e.symm_apply_apply]
  have hFt : ∀ S a, F S ⟨1, Lax794877.Queries.rstT⟩ ![e a] ↔ S a ∧ ¬Lax859101.CountingBipartite.BGLeft a := fun S a => by
    change S (e.symm (e a)) ∧ ¬Lax859101.CountingBipartite.BGLeft (e.symm (e a)) ↔ _
    rw [e.symm_apply_apply]
  have hx1 : ∀ x : Fin 1 → B, ![e (e.symm (x 0))] = x := fun x =>
    funext fun j => by rw [Subsingleton.elim j 0]; simp
  have hworld : ∀ S, Lax794877.PossibleWorlds.IsWorld (F S) := by
    rintro S ⟨n, R⟩ x
    cases R
    · exact ⟨fun h => (hcR x h).elim, fun h => Or.inr ((huR x).mpr h.2)⟩
    · exact ⟨id, Or.inl⟩
    · exact ⟨fun h => (hcT x h).elim, fun h => Or.inr ((huT x).mpr h.2)⟩
  have hquery : ∀ S, @Sentence.Realize Lax794877.Queries.rst B (Lax794877.PossibleWorlds.worldStructure (F S)) Lax794877.Queries.h0 ↔
      Lax859101.CountingBipartite.Pp2dnfModel A S := by
    intro S
    rw [realize_h0]
    constructor
    · rintro ⟨a, b, ⟨hSa, hla⟩, hs, hSb, hlb⟩
      exact ⟨e.symm a, e.symm b, hSa, hSb, hla, hlb, ((hcS _).mp hs).2.2⟩
    · rintro ⟨x, y, hx, hy, hl, hr, he⟩
      refine ⟨e x, e y, (hFr S x).mpr ⟨hx, hl⟩, (hcS _).mpr ?_, (hFt S y).mpr ⟨hy, hr⟩⟩
      simpa using And.intro hl (And.intro hr he)
  refine Nat.card_congr (Equiv.ofBijective
    (fun S : {S : A → Prop // Lax859101.CountingBipartite.Pp2dnfModel A S} =>
      (⟨F S.1, hworld S.1, (hquery S.1).mpr S.2⟩ :
        {ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment B //
          Lax794877.PossibleWorlds.IsWorld ρ ∧ @Sentence.Realize Lax794877.Queries.rst B (Lax794877.PossibleWorlds.worldStructure ρ) Lax794877.Queries.h0})) ⟨?_, ?_⟩)
  · rintro ⟨S, _⟩ ⟨S', _⟩ h
    have hF : F S = F S' := congrArg Subtype.val h
    refine Subtype.ext (funext fun a => propext ?_)
    have h1 : S a ∧ Lax859101.CountingBipartite.BGLeft a ↔ S' a ∧ Lax859101.CountingBipartite.BGLeft a :=
      (hFr S a).symm.trans ((iff_of_eq (congrFun (congrFun hF ⟨1, Lax794877.Queries.rstR⟩) ![e a])).trans
        (hFr S' a))
    have h2 : S a ∧ ¬Lax859101.CountingBipartite.BGLeft a ↔ S' a ∧ ¬Lax859101.CountingBipartite.BGLeft a :=
      (hFt S a).symm.trans ((iff_of_eq (congrFun (congrFun hF ⟨1, Lax794877.Queries.rstT⟩) ![e a])).trans
        (hFt S' a))
    by_cases hl : Lax859101.CountingBipartite.BGLeft a
    · exact ⟨fun h => (h1.mp ⟨h, hl⟩).1, fun h => (h1.mpr ⟨h, hl⟩).1⟩
    · exact ⟨fun h => (h2.mp ⟨h, hl⟩).1, fun h => (h2.mpr ⟨h, hl⟩).1⟩
  · rintro ⟨ρ, hw, hq⟩
    have hF : F (fun a => ρ ⟨1, Lax794877.Queries.rstR⟩ ![e a] ∨ ρ ⟨1, Lax794877.Queries.rstT⟩ ![e a]) = ρ := by
      funext ⟨n, R⟩ x
      cases R
      · have hR := congrArg (ρ ⟨1, Lax794877.Queries.rstR⟩) (hx1 x)
        have hT := congrArg (ρ ⟨1, Lax794877.Queries.rstT⟩) (hx1 x)
        refine propext ⟨?_, fun h => ?_⟩
        · rintro ⟨hS | hS, hl⟩
          · exact hR.mp hS
          · exact absurd hl ((huT x).mp (((hw ⟨1, Lax794877.Queries.rstT⟩ x).2 (hT.mp hS)).resolve_left (hcT x)))
        · exact ⟨Or.inl (hR.mpr h),
            (huR x).mp (((hw ⟨1, Lax794877.Queries.rstR⟩ x).2 h).resolve_left (hcR x))⟩
      · exact propext ⟨(hw ⟨2, Lax794877.Queries.rstS⟩ x).1, fun h => ((hw ⟨2, Lax794877.Queries.rstS⟩ x).2 h).resolve_right (huS x)⟩
      · have hR := congrArg (ρ ⟨1, Lax794877.Queries.rstR⟩) (hx1 x)
        have hT := congrArg (ρ ⟨1, Lax794877.Queries.rstT⟩) (hx1 x)
        refine propext ⟨?_, fun h => ?_⟩
        · rintro ⟨hS | hS, hl⟩
          · exact absurd ((huR x).mp (((hw ⟨1, Lax794877.Queries.rstR⟩ x).2 (hR.mp hS)).resolve_left (hcR x))) hl
          · exact hT.mp hS
        · exact ⟨Or.inr (hT.mpr h),
            (huT x).mp (((hw ⟨1, Lax794877.Queries.rstT⟩ x).2 h).resolve_left (hcT x))⟩
    exact ⟨⟨fun a => ρ ⟨1, Lax794877.Queries.rstR⟩ ![e a] ∨ ρ ⟨1, Lax794877.Queries.rstT⟩ ![e a],
      (hquery _).mp (hF.symm ▸ hq)⟩, Subtype.ext hF⟩

end Semantic

/-- The instance of a bipartite graph: the edges from left to right are the
certain `S`-facts, the left vertices the uncertain `R`-facts, and the right
vertices the uncertain `T`-facts. One-dimensional, single-tagged and
quantifier-free. -/
noncomputable def h0Interp :
    Lax904597.Interpretations.FOInterpretation Lax859101.CountingBipartite.bipGraph (Lax794877.Queries.rst.sum Lax794877.Queries.rst) Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl .r => fun _ => ⊥
    | _, Sum.inl .s => fun _ => FirstOrder.Language.Relations.formula₁ Lax859101.CountingBipartite.bgLeft (FirstOrder.Language.Term.var (0, 0)) ⊓
                                    (FirstOrder.Language.BoundedFormula.not
                                        (FirstOrder.Language.Relations.formula₁ Lax859101.CountingBipartite.bgLeft (FirstOrder.Language.Term.var (1, 0))) ⊓
                                      FirstOrder.Language.Relations.formula₂ Lax859101.CountingBipartite.bgEdge (FirstOrder.Language.Term.var (0, 0))
                                        (FirstOrder.Language.Term.var (1, 0)))
    | _, Sum.inl .t => fun _ => ⊥
    | _, Sum.inr .r => fun _ => FirstOrder.Language.Relations.formula₁ Lax859101.CountingBipartite.bgLeft (FirstOrder.Language.Term.var (0, 0))
    | _, Sum.inr .s => fun _ => ⊥
    | _, Sum.inr .t => fun _ => FirstOrder.Language.BoundedFormula.not
                                    (FirstOrder.Language.Relations.formula₁ Lax859101.CountingBipartite.bgLeft (FirstOrder.Language.Term.var (0, 0)))

/-- **#PP2DNF reduces parsimoniously to counting the worlds of `h₀`**
([Dalvi and Suciu 2012][dalvi2012dichotomy], Proposition 5.2). -/
noncomputable def sharpPP2DNF_parsimonious_possibleWorlds_h0 :
    SharpPP2DNF ≤ᵖ PossibleWorlds Lax794877.Queries.h0 where
  Tag := Unit
  dim := 1
  toInterpretation := h0Interp
  correct := fun A _ _ _ => by
    refine (possibleWorlds_h0_eq (B := h0Interp.Map A) (h0Interp.mapEquivSelf A).symm
      (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_)).symm
    · exact fun h => (FOInterpretation.relMap_map ..).mp h
    · exact fun h => (FOInterpretation.relMap_map ..).mp h
    · refine (FOInterpretation.relMap_map ..).trans ?_
      change _ ↔ RelMap Lax859101.CountingBipartite.bgLeft ![(x 0).2 0] ∧ ¬RelMap Lax859101.CountingBipartite.bgLeft ![(x 1).2 0] ∧
        RelMap Lax859101.CountingBipartite.bgEdge ![(x 0).2 0, (x 1).2 0]
      simp [h0Interp, Formula.realize_rel₁, Formula.realize_rel₂]
    · refine (FOInterpretation.relMap_map ..).trans ?_
      change _ ↔ RelMap Lax859101.CountingBipartite.bgLeft ![(x 0).2 0]
      simp [h0Interp, Formula.realize_rel₁]
    · refine (FOInterpretation.relMap_map ..).trans ?_
      change _ ↔ ¬RelMap Lax859101.CountingBipartite.bgLeft ![(x 0).2 0]
      simp [h0Interp, Formula.realize_rel₁]
    · exact fun h => (FOInterpretation.relMap_map ..).mp h

/-! ## Step 6: the theorems -/

/-- **Counting the worlds of `h₀` is one-call `#P`-hard.** -/
theorem possibleWorlds_h0_sharpP_oneCallHard : SharpP.OneCallHard (PossibleWorlds Lax794877.Queries.h0) :=
  CountingClass.OneCallHard.of_parsimonious sharpPP2DNF_parsimonious_possibleWorlds_h0
    sharpPP2DNF_sharpP_oneCallHard

/-- **Counting the worlds of `h₀` is one-call `#P`-complete**: it is in `#P`,
like the count of the worlds of any first-order query, and every problem of
`#P` reduces to it with one call. -/
theorem possibleWorlds_h0_sharpP_oneCallComplete :
    SharpP.OneCallComplete (PossibleWorlds Lax794877.Queries.h0) :=
  .of_mem (possibleWorlds_mem_sharpP Lax794877.Queries.h0) possibleWorlds_h0_sharpP_oneCallHard

/-! ## Step 7: probabilities in the instance -/

/-- **The weighted worlds of `h₀` are one-call `#P`-hard to count**, already
when every weight is `1`, i.e., at uniform probability `1/2`. -/
theorem weightedWorlds_h0_sharpP_oneCallHard : SharpP.OneCallHard (WeightedWorlds Lax794877.Queries.h0) :=
  CountingClass.OneCallHard.of_orderedParsimonious
    (possibleWorlds_ordered_parsimonious_weightedWorlds Lax794877.Queries.h0)
    possibleWorlds_h0_sharpP_oneCallHard

/-- **The numerator of the probability of `h₀` is one-call `#P`-complete**:
counting the weighted worlds of `h₀` is in `#P`, like those of any
first-order query, and every problem of `#P` reduces to it with one call. -/
theorem weightedWorlds_h0_sharpP_oneCallComplete :
    SharpP.OneCallComplete (WeightedWorlds Lax794877.Queries.h0) :=
  .of_mem (weightedWorlds_mem_sharpP Lax794877.Queries.h0) weightedWorlds_h0_sharpP_oneCallHard

/-! ## Step 8: a concrete database, and its encoding -/

namespace FactStatus

end FactStatus

/-- **The encoding of a probabilistic database** as a weighted instance: the
universe is the set of constants, which serve as bit positions too, in their
own order, and the bits of a weight are its binary digits. -/
def probDbEncoding : Encoding (Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) Lax794877.ExampleDatabase.ProbDb where
  size := fun i => i.n
  Univ := fun i => Fin i.n
  deceq := fun _ => inferInstance
  fintype := fun _ => inferInstance
  relBool := fun i {n} R =>
    match n, R with
    | _, .cert .r => fun x => (i.r (x 0)).isCert
    | _, .cert .s => fun x => (i.s (x 0) (x 1)).isCert
    | _, .cert .t => fun x => (i.t (x 0)).isCert
    | _, .unc .r => fun x => (i.r (x 0)).isUnc
    | _, .unc .s => fun x => (i.s (x 0) (x 1)).isUnc
    | _, .unc .t => fun x => (i.t (x 0)).isUnc
    | _, .pres .r => fun x => (i.r (x 0)).presW.testBit (x 1).1
    | _, .pres .s => fun x => (i.s (x 0) (x 1)).presW.testBit (x 2).1
    | _, .pres .t => fun x => (i.t (x 0)).presW.testBit (x 1).1
    | _, .abs .r => fun x => (i.r (x 0)).absW.testBit (x 1).1
    | _, .abs .s => fun x => (i.s (x 0) (x 1)).absW.testBit (x 2).1
    | _, .abs .t => fun x => (i.t (x 0)).absW.testBit (x 1).1
    | _, .le => fun x => decide (x 0 ≤ x 1)
  card_le := Encoding.linear_bound (c := 1) fun i => by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  le_card := Encoding.linear_bound (c := 1) fun i => by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega

/-! ### The concrete semantics

Everything here is computed: a world is three Boolean tables, and the weighted
count of the query can be evaluated on a small database. -/

namespace FactStatus

end FactStatus

namespace ProbDb

variable (i : Lax794877.ExampleDatabase.ProbDb)

end ProbDb

/-! ### Faithfulness -/

section Faithful

variable {n : ℕ}

theorem vec1_eta {α : Type} (x : Fin 1 → α) : ![x 0] = x :=
  funext fun j => by rw [Subsingleton.elim j 0]; rfl

theorem vec2_eta {α : Type} (x : Fin 2 → α) : ![x 0, x 1] = x :=
  funext fun j => by fin_cases j <;> rfl

open Classical in
/-- The concrete world of a family of relations. -/
noncomputable def worldTables (ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin n)) : Lax794877.ExampleDatabase.World n :=
  (fun x => decide (ρ ⟨1, Lax794877.Queries.rstR⟩ ![x]), fun x y => decide (ρ ⟨2, Lax794877.Queries.rstS⟩ ![x, y]),
    fun y => decide (ρ ⟨1, Lax794877.Queries.rstT⟩ ![y]))

/-- The family of relations of a concrete world. -/
def tableRels (W : Lax794877.ExampleDatabase.World n) : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin n) := fun p =>
  match p with
  | ⟨_, .r⟩ => fun x : Fin 1 → Fin n => W.1 (x 0) = true
  | ⟨_, .s⟩ => fun x : Fin 2 → Fin n => W.2.1 (x 0) (x 1) = true
  | ⟨_, .t⟩ => fun x : Fin 1 → Fin n => W.2.2 (x 0) = true

open Classical in
/-- Families of relations over the schema are concrete worlds. -/
noncomputable def worldEquiv (n : ℕ) : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin n) ≃ Lax794877.ExampleDatabase.World n where
  toFun := worldTables
  invFun := tableRels
  left_inv ρ := by
    funext ⟨k, R⟩ x
    cases R
    · exact propext (decide_eq_true_iff.trans (iff_of_eq (congrArg (ρ ⟨1, Lax794877.Queries.rstR⟩) (vec1_eta x))))
    · exact propext (decide_eq_true_iff.trans (iff_of_eq (congrArg (ρ ⟨2, Lax794877.Queries.rstS⟩) (vec2_eta x))))
    · exact propext (decide_eq_true_iff.trans (iff_of_eq (congrArg (ρ ⟨1, Lax794877.Queries.rstT⟩) (vec1_eta x))))
  right_inv W := by
    refine Prod.ext (funext fun x => ?_) (Prod.ext (funext fun x => funext fun y => ?_)
      (funext fun y => ?_))
    · cases h : W.1 x
      · exact decide_eq_false fun h' : W.1 x = true => by rw [h] at h'; exact Bool.noConfusion h'
      · exact decide_eq_true (show W.1 x = true from h)
    · cases h : W.2.1 x y
      · exact decide_eq_false fun h' : W.2.1 x y = true => by
          rw [h] at h'; exact Bool.noConfusion h'
      · exact decide_eq_true (show W.2.1 x y = true from h)
    · cases h : W.2.2 y
      · exact decide_eq_false fun h' : W.2.2 y = true => by
          rw [h] at h'; exact Bool.noConfusion h'
      · exact decide_eq_true (show W.2.2 y = true from h)

/-- The facts over the schema: an `R`-fact, an `S`-fact or a `T`-fact. -/
def factEquiv (A : Type) : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A ≃ A ⊕ (A × A) ⊕ A where
  toFun q :=
    match q with
    | ⟨⟨_, .r⟩, x⟩ => .inl (x 0)
    | ⟨⟨_, .s⟩, x⟩ => .inr (.inl (x 0, x 1))
    | ⟨⟨_, .t⟩, x⟩ => .inr (.inr (x 0))
  invFun z :=
    match z with
    | .inl a => ⟨⟨1, Lax794877.Queries.rstR⟩, ![a]⟩
    | .inr (.inl p) => ⟨⟨2, Lax794877.Queries.rstS⟩, ![p.1, p.2]⟩
    | .inr (.inr b) => ⟨⟨1, Lax794877.Queries.rstT⟩, ![b]⟩
  left_inv := by
    rintro ⟨⟨k, R⟩, x⟩
    cases R
    · exact congrArg (Sigma.mk (⟨1, Lax794877.Queries.rstR⟩ : Σ n, Lax794877.Queries.rst.Relations n)) (vec1_eta x)
    · exact congrArg (Sigma.mk (⟨2, Lax794877.Queries.rstS⟩ : Σ n, Lax794877.Queries.rst.Relations n)) (vec2_eta x)
    · exact congrArg (Sigma.mk (⟨1, Lax794877.Queries.rstT⟩ : Σ n, Lax794877.Queries.rst.Relations n)) (vec1_eta x)
  right_inv := by
    rintro (a | p | b) <;> rfl

/-- What a world may do with a fact, in terms of its status. -/
theorem FactStatus.admits_decide_iff (st : Lax794877.ExampleDatabase.FactStatus) (P : Prop) [Decidable P] :
    st.admits (decide P) = true ↔
      (st.isCert = true → P) ∧ (P → st.isCert = true ∨ st.isUnc = true) := by
  cases st <;> simp [Lax794877.ExampleDatabase.FactStatus.admits, Lax794877.ExampleDatabase.FactStatus.isCert, Lax794877.ExampleDatabase.FactStatus.isUnc]

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.FactStatus

export Lax794877Proofs.DescriptiveComplexity.FactStatus (admits_decide_iff)

end Lax794877.ExampleDatabase.FactStatus

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

/-- The status of a fact, by cases: an uncertain fact is not certain. -/
theorem FactStatus.isUnc_and_not_isCert (st : Lax794877.ExampleDatabase.FactStatus) :
    st.isUnc = true ∧ ¬st.isCert = true ↔ st.isUnc = true := by
  cases st <;> simp [Lax794877.ExampleDatabase.FactStatus.isUnc, Lax794877.ExampleDatabase.FactStatus.isCert]

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.FactStatus

export Lax794877Proofs.DescriptiveComplexity.FactStatus (isUnc_and_not_isCert)

end Lax794877.ExampleDatabase.FactStatus

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

/-- **A weighted instance says of a fact what a status says**: the fact is
certain exactly when the status is, it is open exactly when the status is
uncertain, and then its two weights, read in binary on the order of the
instance, are those of the status. -/
structure StatusAt [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin n)] (st : Lax794877.ExampleDatabase.FactStatus)
    (q : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst (Fin n)) : Prop where
  /-- The fact is certain exactly when its status is. -/
  cert : RelMap (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) (Lax794877.WeightedWorlds.WeightedRel.cert q.1.2) q.2 ↔
    st.isCert = true
  /-- The fact is open exactly when its status is uncertain. -/
  isOpen : Lax794877.WeightedWorlds.IsOpen q ↔ st.isUnc = true
  /-- The weight of presence of an uncertain fact. -/
  pres : st.isUnc = true → Lax799700.Common.binNum (Lax794877.WeightedWorlds.WLe Lax794877.Queries.rst (Fin n)) (fun _ => True)
    (Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.pres q.1.2) q.2) = st.presW
  /-- The weight of absence of an uncertain fact. -/
  abs : st.isUnc = true → Lax799700.Common.binNum (Lax794877.WeightedWorlds.WLe Lax794877.Queries.rst (Fin n)) (fun _ => True)
    (Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.abs q.1.2) q.2) = st.absW

section StatusAt

variable [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin n)] {st : Lax794877.ExampleDatabase.FactStatus}
  {q : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst (Fin n)}

open Classical in
/-- The weight the abstract problem reads at a fact is the weight of its
status. -/
theorem StatusAt.factWeight_eq (h : StatusAt st q)
    (ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin n)) :
    factWeight ρ q = st.weight (decide (ρ q.1 q.2)) := by
  cases st with
  | absent =>
    have ho : ¬Lax794877.WeightedWorlds.IsOpen q := fun hq => Bool.noConfusion (h.isOpen.mp hq)
    simp only [factWeight, ho, ↓reduceIte]
    rfl
  | certain =>
    have ho : ¬Lax794877.WeightedWorlds.IsOpen q := fun hq => Bool.noConfusion (h.isOpen.mp hq)
    simp only [factWeight, ho, ↓reduceIte]
    rfl
  | uncertain a c =>
    have ho : Lax794877.WeightedWorlds.IsOpen q := h.isOpen.mpr rfl
    by_cases hρ : ρ q.1 q.2
    · simp only [factWeight, ho, hρ, ↓reduceIte, decide_true, Lax794877.ExampleDatabase.FactStatus.weight]
      exact h.pres rfl
    · simp only [factWeight, ho, hρ, ↓reduceIte, decide_false, Lax794877.ExampleDatabase.FactStatus.weight,
        Bool.false_eq_true]
      exact h.abs rfl

/-- What a possible world may do with a fact is what its status admits. -/
theorem StatusAt.admits_iff (h : StatusAt st q) (P : Prop) [Decidable P] :
    st.admits (decide P) = true ↔
      (RelMap (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) (Lax794877.WeightedWorlds.WeightedRel.cert q.1.2) q.2 → P) ∧
        (P → RelMap (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) (Lax794877.WeightedWorlds.WeightedRel.cert q.1.2) q.2 ∨
          RelMap (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) (Lax794877.WeightedWorlds.WeightedRel.unc q.1.2) q.2) := by
  rw [FactStatus.admits_decide_iff, ← h.cert]
  refine and_congr Iff.rfl (imp_congr Iff.rfl ⟨fun h' => h'.imp id fun hu => (h.isOpen.mpr hu).1,
    fun h' => ?_⟩)
  by_cases hc : RelMap (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) (Lax794877.WeightedWorlds.WeightedRel.cert q.1.2) q.2
  · exact Or.inl hc
  · exact Or.inr (h.isOpen.mp ⟨h'.resolve_left hc, hc⟩)

end StatusAt

/-- **A weighted instance over the constants of a database matches it**: its
position order is linear, and it says of every fact what the database says. -/
structure ProbDb.Matches (i : Lax794877.ExampleDatabase.ProbDb) [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)] :
    Prop where
  /-- The positions are linearly ordered. -/
  lin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe Lax794877.Queries.rst (Fin i.n))
  /-- The `R`-facts. -/
  r : ∀ x, StatusAt (i.r x) ⟨⟨1, Lax794877.Queries.rstR⟩, ![x]⟩
  /-- The `S`-facts. -/
  s : ∀ x y, StatusAt (i.s x y) ⟨⟨2, Lax794877.Queries.rstS⟩, ![x, y]⟩
  /-- The `T`-facts. -/
  t : ∀ y, StatusAt (i.t y) ⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb

export Lax794877Proofs.DescriptiveComplexity.ProbDb (Matches)

end Lax794877.ExampleDatabase.ProbDb

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb.Matches

export Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches (lin r s t)

end Lax794877.ExampleDatabase.ProbDb.Matches

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

section Matches

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

/-- The status the database gives a fact. -/
def ProbDb.statusAt (i : Lax794877.ExampleDatabase.ProbDb) (z : Fin i.n ⊕ (Fin i.n × Fin i.n) ⊕ Fin i.n) : Lax794877.ExampleDatabase.FactStatus :=
  match z with
  | .inl a => i.r a
  | .inr (.inl p) => i.s p.1 p.2
  | .inr (.inr b) => i.t b

end Matches

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb

export Lax794877Proofs.DescriptiveComplexity.ProbDb (statusAt)

end Lax794877.ExampleDatabase.ProbDb

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

section Matches

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

theorem ProbDb.Matches.statusAt (hm : i.Matches)
    (z : Fin i.n ⊕ (Fin i.n × Fin i.n) ⊕ Fin i.n) :
    StatusAt (i.statusAt z) ((factEquiv (Fin i.n)).symm z) := by
  rcases z with a | p | b
  · exact hm.r a
  · exact hm.s p.1 p.2
  · exact hm.t b

end Matches

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb.Matches

export Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches (statusAt)

end Lax794877.ExampleDatabase.ProbDb.Matches

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

section Matches

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

open Classical in
/-- The product of the weights of the facts, in a family of relations, is the
weight of its concrete world. -/
theorem ProbDb.Matches.finprod_factWeight (hm : i.Matches)
    (ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin i.n)) :
    ∏ᶠ q : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst (Fin i.n), factWeight ρ q = i.weight (worldTables ρ) := by
  let := Fintype.ofEquiv _ (factEquiv (Fin i.n)).symm
  rw [finprod_eq_prod_of_fintype,
    ← Fintype.prod_equiv (factEquiv (Fin i.n)).symm
      (fun z => factWeight ρ ((factEquiv (Fin i.n)).symm z)) _ (fun _ => rfl),
    Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [(hm.statusAt _).factWeight_eq ρ]
  rfl

end Matches

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb.Matches

export Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches (finprod_factWeight)

end Lax794877.ExampleDatabase.ProbDb.Matches

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

section Matches

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

open Classical in
/-- The possible worlds of the instance are the possible worlds of the
database. -/
theorem ProbDb.Matches.isWeightedWorld_iff (hm : i.Matches)
    (ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin i.n)) :
    IsWeightedWorld ρ ↔ i.Valid (worldTables ρ) := by
  constructor
  · intro h
    exact ⟨fun x => ((hm.r x).admits_iff _).mpr (h ⟨⟨1, Lax794877.Queries.rstR⟩, ![x]⟩),
      fun x y => ((hm.s x y).admits_iff _).mpr (h ⟨⟨2, Lax794877.Queries.rstS⟩, ![x, y]⟩),
      fun y => ((hm.t y).admits_iff _).mpr (h ⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩)⟩
  · rintro ⟨hr, hs, ht⟩ q
    obtain ⟨z, rfl⟩ := (factEquiv (Fin i.n)).symm.surjective q
    rcases z with a | p | b
    · exact ((hm.r a).admits_iff _).mp (hr a)
    · exact ((hm.s p.1 p.2).admits_iff _).mp (hs p.1 p.2)
    · exact ((hm.t b).admits_iff _).mp (ht b)

end Matches

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb.Matches

export Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches (isWeightedWorld_iff)

end Lax794877.ExampleDatabase.ProbDb.Matches

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

section Matches

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

end Matches

open Classical in
/-- The query holds in a family of relations exactly when it holds in its
concrete world. -/
theorem realize_h0_iff_holdsH0 (ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin n)) :
    @Sentence.Realize Lax794877.Queries.rst (Fin n) (Lax794877.PossibleWorlds.worldStructure ρ) Lax794877.Queries.h0 ↔ Lax794877.ExampleDatabase.HoldsH0 (worldTables ρ) :=
  (realize_h0 ρ).trans
    ⟨fun ⟨a, b, h1, h2, h3⟩ => ⟨a, b, decide_eq_true h1, decide_eq_true h2, decide_eq_true h3⟩,
      fun ⟨a, b, h1, h2, h3⟩ =>
        ⟨a, b, of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3⟩⟩

section Counts

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

/-- **On an instance matching a database, the abstract count of the weighted
worlds of `h₀` is the weighted count computed from the database.** The
encoder's faithfulness and the decoder's soundness are both this. -/
theorem ProbDb.Matches.count_eq (hm : i.Matches) : i.count = WeightedWorlds Lax794877.Queries.h0 (Fin i.n) := by
  let := Fintype.ofFinite {ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin i.n) //
    IsWeightedWorld ρ ∧ @Sentence.Realize Lax794877.Queries.rst (Fin i.n) (Lax794877.PossibleWorlds.worldStructure ρ) Lax794877.Queries.h0}
  rw [weightedWorlds_eq_weightSum hm.lin, finsum_eq_sum_of_fintype, Lax794877.ExampleDatabase.ProbDb.count,
    ← Finset.sum_filter,
    Finset.sum_subtype (p := fun W : Lax794877.ExampleDatabase.World i.n => i.Valid W ∧ Lax794877.ExampleDatabase.HoldsH0 W)
      (Finset.univ.filter fun W : Lax794877.ExampleDatabase.World i.n => i.Valid W ∧ Lax794877.ExampleDatabase.HoldsH0 W) (by simp)]
  exact (Fintype.sum_equiv ((worldEquiv i.n).subtypeEquiv fun ρ =>
    and_congr (hm.isWeightedWorld_iff ρ) (realize_h0_iff_holdsH0 ρ)) _ _
    fun ρ => hm.finprod_factWeight ρ.1).symm

end Counts

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb.Matches

export Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches (count_eq)

end Lax794877.ExampleDatabase.ProbDb.Matches

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

section Counts

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

/-- On an instance matching a database, the abstract count of all the weighted
worlds is the total weight computed from the database. -/
theorem ProbDb.Matches.total_eq (hm : i.Matches) :
    i.total = WeightedWorlds (⊤ : Lax794877.Queries.rst.Sentence) (Fin i.n) := by
  let := Fintype.ofFinite {ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment (Fin i.n) //
    IsWeightedWorld ρ ∧ @Sentence.Realize Lax794877.Queries.rst (Fin i.n) (Lax794877.PossibleWorlds.worldStructure ρ) ⊤}
  rw [weightedWorlds_eq_weightSum hm.lin, finsum_eq_sum_of_fintype, Lax794877.ExampleDatabase.ProbDb.total,
    ← Finset.sum_filter,
    Finset.sum_subtype (p := fun W : Lax794877.ExampleDatabase.World i.n => i.Valid W)
      (Finset.univ.filter fun W : Lax794877.ExampleDatabase.World i.n => i.Valid W) (by simp)]
  exact (Fintype.sum_equiv ((worldEquiv i.n).subtypeEquiv fun ρ =>
    ⟨fun h => (hm.isWeightedWorld_iff ρ).mp h.1, fun h =>
      ⟨(hm.isWeightedWorld_iff ρ).mpr h, by
        let := Lax794877.PossibleWorlds.worldStructure ρ
        exact Formula.realize_top.mpr trivial⟩⟩) _ _
    fun ρ => hm.finprod_factWeight ρ.1).symm

end Counts

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb.Matches

export Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches (total_eq)

end Lax794877.ExampleDatabase.ProbDb.Matches

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

section Counts

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

/-- On an instance matching a database, the probability of `h₀` is the ratio
of the two numbers computed from the database. -/
theorem ProbDb.Matches.worldProb_eq (hm : i.Matches)
    (hpos : ∀ x : {q : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst (Fin i.n) // Lax794877.WeightedWorlds.IsOpen q},
      0 < Lax794877.WeightedWorlds.presWeight x + Lax794877.WeightedWorlds.absWeight x) :
    Lax794877.WeightedWorlds.worldProb Lax794877.Queries.h0 hpos = (i.count : ℚ) / (i.total : ℚ) := by
  rw [worldProb_eq_ratio hm.lin, ← hm.count_eq, ← hm.total_eq]

end Counts

end Faithful

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.ExampleDatabase.ProbDb.Matches

export Lax794877Proofs.DescriptiveComplexity.ProbDb.Matches (worldProb_eq)

end Lax794877.ExampleDatabase.ProbDb.Matches

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Faithful

variable {n : ℕ}

section Counts

variable {i : Lax794877.ExampleDatabase.ProbDb} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n)]

end Counts

/-! ### The encoding is faithful -/

/-- The encoded structure of a database, on its constants. -/
@[instance_reducible]
def probDbStructure (i : Lax794877.ExampleDatabase.ProbDb) : (Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure (Fin i.n) :=
  probDbEncoding.str i

/-- The order of the positions of an encoded database is the order of its
constants. -/
theorem probDb_wle (i : Lax794877.ExampleDatabase.ProbDb) (a b : Fin i.n) :
    @Lax794877.WeightedWorlds.WLe Lax794877.Queries.rst (Fin i.n) (probDbStructure i) a b ↔ a ≤ b :=
  decide_eq_true_iff

/-- The encoded structure of a database matches it: the binary digits the
encoder writes decode to the weights
(`DescriptiveComplexity.binNum_fin_of_testBit`). -/
theorem probDb_matches (i : Lax794877.ExampleDatabase.ProbDb) : @ProbDb.Matches i (probDbStructure i) :=
  letI := probDbStructure i
  { lin := ⟨fun a => (probDb_wle i a a).mpr le_rfl,
      fun a b c h1 h2 => (probDb_wle i a c).mpr
        (le_trans ((probDb_wle i a b).mp h1) ((probDb_wle i b c).mp h2)),
      fun a b h1 h2 => le_antisymm ((probDb_wle i a b).mp h1) ((probDb_wle i b a).mp h2),
      fun a b => (le_total a b).imp (probDb_wle i a b).mpr (probDb_wle i b a).mpr⟩
    r := fun x => ⟨Iff.rfl, (i.r x).isUnc_and_not_isCert,
      fun _ => binNum_fin_of_testBit (probDb_wle i) _ (i.fits_r x).1 _ fun _ => Iff.rfl,
      fun _ => binNum_fin_of_testBit (probDb_wle i) _ (i.fits_r x).2 _ fun _ => Iff.rfl⟩
    s := fun x y => ⟨Iff.rfl, (i.s x y).isUnc_and_not_isCert,
      fun _ => binNum_fin_of_testBit (probDb_wle i) _ (i.fits_s x y).1 _ fun _ => Iff.rfl,
      fun _ => binNum_fin_of_testBit (probDb_wle i) _ (i.fits_s x y).2 _ fun _ => Iff.rfl⟩
    t := fun y => ⟨Iff.rfl, (i.t y).isUnc_and_not_isCert,
      fun _ => binNum_fin_of_testBit (probDb_wle i) _ (i.fits_t y).1 _ fun _ => Iff.rfl,
      fun _ => binNum_fin_of_testBit (probDb_wle i) _ (i.fits_t y).2 _ fun _ => Iff.rfl⟩ }

/-- **The probability of `h₀` over a database is the ratio of the two numbers
computed from it.** The uncertain facts of the database being present
independently, each with probability its weight of presence over the sum of
its weights, the probability that the query holds is `count / total`. -/
theorem probDb_worldProb_eq (i : Lax794877.ExampleDatabase.ProbDb)
    (hpos : ∀ x : {q : @Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst (Fin i.n) // @Lax794877.WeightedWorlds.IsOpen _ _ (probDbStructure i) q},
      0 < @Lax794877.WeightedWorlds.presWeight _ _ (probDbStructure i) x + @Lax794877.WeightedWorlds.absWeight _ _ (probDbStructure i) x) :
    @Lax794877.WeightedWorlds.worldProb _ _ _ _ (probDbStructure i) _ Lax794877.Queries.h0 hpos = (i.count : ℚ) / (i.total : ℚ) :=
  @ProbDb.Matches.worldProb_eq i (probDbStructure i) (probDb_matches i) hpos

end Faithful

/-! ## Step 9: the decoder

The converse of the encoding: from a concretely presented weighted instance
back to a database, by a computation. The presented order has to be linear –
otherwise the instance carries no number – and that is the only
well-formedness condition. A fact that is both certain and uncertain is read
as certain, which is what the semantics does with it. -/

section Decoder

end Decoder

/-! ### A database, computed

Two constants. `R(0)` is uncertain with probability `1/2`, `S(0, 1)` is
certain, `T(1)` is uncertain with probability `1/4`. The query holds in the
one world keeping both uncertain facts, of weight `1 · 1`, out of a total
weight `(1 + 1) · (1 + 3) = 8`: its probability is `1/8`. -/

/-! The decoder runs too, and gets the two numbers back from the encoded
instance. -/

/-! ## Step 10: the easy query -/

theorem realize_rs {B : Type} (ρ : (Lax794877.PossibleWorlds.worldBlock Lax794877.Queries.rst).Assignment B) :
    @Sentence.Realize Lax794877.Queries.rst B (Lax794877.PossibleWorlds.worldStructure ρ) Lax794877.Queries.rs ↔
      ∃ a b : B, ρ ⟨1, Lax794877.Queries.rstR⟩ ![a] ∧ ρ ⟨2, Lax794877.Queries.rstS⟩ ![a, b] := by
  let := Lax794877.PossibleWorlds.worldStructure ρ
  rw [Lax794877.Queries.rs]
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr]
  constructor
  · rintro ⟨v, h⟩
    exact ⟨v 0, v 1, h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨![a, b], h⟩

namespace SafeQ

/-! ## Step 11: the weights -/

section Weights

variable (A : Type) [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure A]

/-- The weight of presence of the fact `R(x)`. -/
noncomputable def aR (x : A) : ℕ := fullPresWeight (⟨⟨1, Lax794877.Queries.rstR⟩, ![x]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A)

/-- The weight of absence of the fact `R(x)`. -/
noncomputable def cR (x : A) : ℕ := fullAbsWeight (⟨⟨1, Lax794877.Queries.rstR⟩, ![x]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A)

/-- The weight of presence of the fact `S(x, y)`. -/
noncomputable def aS (x y : A) : ℕ :=
  fullPresWeight (⟨⟨2, Lax794877.Queries.rstS⟩, ![x, y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A)

/-- The weight of absence of the fact `S(x, y)`. -/
noncomputable def cS (x y : A) : ℕ :=
  fullAbsWeight (⟨⟨2, Lax794877.Queries.rstS⟩, ![x, y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A)

/-- The total weight of the fact `T(y)`, which the query does not read. -/
noncomputable def tT (y : A) : ℕ :=
  fullPresWeight (⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A) +
    fullAbsWeight (⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A)

variable [Fintype A]

/-- **The weight of failing at `x`**: `R(x)` is present and no `S(x, y)` is,
or `R(x)` is absent. -/
noncomputable def failW (x : A) : ℕ :=
  aR A x * ∏ y, cS A x y + cR A x * ∏ y, (aS A x y + cS A x y)

variable [LinearOrder A]

/-- **The weight of succeeding at `x`**: `R(x)` is present, and the `S(x, y)`
are sorted by the first `y` that is present. -/
noncomputable def succW (x : A) : ℕ :=
  aR A x * ∑ y, (∏ y' ∈ Finset.univ.filter (· < y), cS A x y') * aS A x y *
    ∏ y' ∈ Finset.univ.filter (y < ·), (aS A x y' + cS A x y')

end Weights

/-! ## Step 12: failing is a product -/

section Count

variable {A : Type} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure A]

/-- The facts, as variables: the `R`-facts, the `S`-facts and the `T`-facts. -/
abbrev Var (A : Type) : Type := A ⊕ (A × A) ⊕ A

theorem pres_comp :
    (fun z : Var A => fullPresWeight ((factEquiv A).symm z)) =
      Sum.elim (aR A) (Sum.elim (fun p => aS A p.1 p.2)
        fun y => fullPresWeight (⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A)) := by
  funext z
  rcases z with x | p | y <;> rfl

theorem abs_comp :
    (fun z : Var A => fullAbsWeight ((factEquiv A).symm z)) =
      Sum.elim (cR A) (Sum.elim (fun p => cS A p.1 p.2)
        fun y => fullAbsWeight (⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A)) := by
  funext z
  rcases z with x | p | y <;> rfl

variable [Fintype A] [LinearOrder A]

/-- What failing asks of each `S`-fact and `T`-fact, given the `R`-facts: an
`S`-fact at an `x` whose `R`-fact is present must be absent. -/
def okS (vR : A → Bool) : (A × A) ⊕ A → Bool → Bool
  | Sum.inl p, b => !(vR p.1 && b)
  | Sum.inr _, _ => true

/-- “The query holds”, on a valuation of the facts. -/
def holdsRs (v : Var A → Bool) : Bool :=
  decide (∃ x y : A, v (.inl x) = true ∧ v (.inr (.inl (x, y))) = true)

/-- **The count of the weighted worlds of the query**, as a weighted count
over the valuations of the facts. -/
theorem weightedWorlds_rs_eq_weightedCount (hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe Lax794877.Queries.rst A)) :
    WeightedWorlds Lax794877.Queries.rs A =
      weightedCount (fun z : Var A => fullPresWeight ((factEquiv A).symm z))
        (fun z => fullAbsWeight ((factEquiv A).symm z)) holdsRs := by
  have : Finite A := Finite.of_fintype A
  let : DecidableEq (Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A) := Classical.decEq _
  rw [weightedWorlds_eq_weightedCount_facts hlin,
    weightedCount_equiv _ _ (factEquiv A).symm]
  refine congrArg _ (funext fun v => ?_)
  rw [holdsRs]
  refine decide_eq_decide.mpr ((realize_rs _).trans ?_)
  have hR : ∀ x : A, (factEquiv A).symm.symm (⟨⟨1, Lax794877.Queries.rstR⟩, ![x]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A) =
      .inl x := fun x => rfl
  have hS : ∀ x y : A, (factEquiv A).symm.symm (⟨⟨2, Lax794877.Queries.rstS⟩, ![x, y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A) =
      .inr (.inl (x, y)) := fun x y => rfl
  simp only [factWorld, hR, hS]

/-- **Failing is a product**: the weight of the worlds in which the query
fails is the product, over `x`, of the weight of failing at `x`, times the
total weight of the `T`-facts. -/
theorem weightedCount_fail :
    weightedCount (fun z : Var A => fullPresWeight ((factEquiv A).symm z))
        (fun z => fullAbsWeight ((factEquiv A).symm z)) (fun v => !holdsRs v) =
      (∏ y, tT A y) * ∏ x, failW A x := by
  rw [pres_comp, abs_comp, weightedCount_sum_type]
  -- given the `R`-facts, the event constrains each other fact separately
  have hev : ∀ vR : A → Bool, (fun vST : (A × A) ⊕ A → Bool => !holdsRs (Sum.elim vR vST)) =
      fun vST => decide (∀ z, okS vR z (vST z) = true) := by
    intro vR
    funext vST
    rw [holdsRs, ← decide_not]
    refine decide_eq_decide.mpr ⟨fun h z => ?_, fun h ⟨x, y, hx, hy⟩ => ?_⟩
    · rcases z with ⟨x, y⟩ | y
      · cases hx : vR x
        · simp [okS, hx]
        · cases hy : vST (Sum.inl (x, y))
          · simp [okS]
          · exact absurd ⟨x, y, hx, hy⟩ h
      · rfl
    · have hx' : vR x = true := hx
      have hy' : vST (Sum.inl (x, y)) = true := hy
      have := h (Sum.inl (x, y))
      simp [okS, hx', hy'] at this
  have hinner : ∀ vR : A → Bool,
      weightedCount (Sum.elim (fun p : A × A => aS A p.1 p.2)
          fun y => fullPresWeight (⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A))
        (Sum.elim (fun p : A × A => cS A p.1 p.2)
          fun y => fullAbsWeight (⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A))
        (fun vST => !holdsRs (Sum.elim vR vST)) =
      (∏ x, ∏ y, if vR x then cS A x y else aS A x y + cS A x y) * ∏ y, tT A y := by
    intro vR
    rw [hev vR]
    have hfa := weightedCount_forall
      (Sum.elim (fun p : A × A => aS A p.1 p.2)
        fun y => fullPresWeight (⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A))
      (Sum.elim (fun p : A × A => cS A p.1 p.2)
        fun y => fullAbsWeight (⟨⟨1, Lax794877.Queries.rstT⟩, ![y]⟩ : Lax794877.WeightedWorlds.Fact Lax794877.Queries.rst A))
      (okS vR)
    refine hfa.trans ?_
    rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun y _ => ?_)
      (Finset.prod_congr rfl fun y _ => ?_)
    · cases hx : vR x <;> simp [okS, hx]
    · simp [okS, tT]
  -- summing over the `R`-facts factorizes too
  have hsum := weightedCount_true (fun x : A => aR A x * ∏ y, cS A x y)
    (fun x : A => cR A x * ∏ y, (aS A x y + cS A x y))
  simp only [weightedCount, valWeight, ite_true] at hsum
  rw [Finset.sum_congr rfl fun vR _ => congrArg (valWeight (aR A) (cR A) vR * ·) (hinner vR)]
  have hterm : ∀ vR : A → Bool, valWeight (aR A) (cR A) vR *
      ((∏ x, ∏ y, if vR x then cS A x y else aS A x y + cS A x y) * ∏ y, tT A y) =
      (∏ y, tT A y) * ∏ x, (if vR x then aR A x * ∏ y, cS A x y
        else cR A x * ∏ y, (aS A x y + cS A x y)) := by
    intro vR
    rw [valWeight, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    refine congrArg _ (Finset.prod_congr rfl fun x _ => ?_)
    cases vR x <;> simp
  rw [Finset.sum_congr rfl fun vR _ => hterm vR, ← Finset.mul_sum, hsum]
  rfl

/-! ## Step 13: succeeding, without a subtraction -/

/-- Failing or succeeding at `x` is the total weight of the facts about
`x`: the first success identity, over `y`. -/
theorem failW_add_succW (x : A) :
    failW A x + succW A x = (aR A x + cR A x) * ∏ y, (aS A x y + cS A x y) := by
  have h := prod_add_eq_prod_add_sum (fun y => cS A x y) (fun y => aS A x y)
  have h' : ∏ y, (aS A x y + cS A x y) = ∏ y, (cS A x y + aS A x y) :=
    Finset.prod_congr rfl fun y _ => add_comm _ _
  have h'' : ∀ y, ∏ y' ∈ Finset.univ.filter (y < ·), (aS A x y' + cS A x y') =
      ∏ y' ∈ Finset.univ.filter (y < ·), (cS A x y' + aS A x y') := fun y =>
    Finset.prod_congr rfl fun y' _ => add_comm _ _
  rw [failW, succW, h', Finset.sum_congr rfl fun y _ => congrArg _ (h'' y), h]
  ring

/-- **The count of the weighted worlds of the query, in closed form**: the
worlds in which the query holds, sorted by the first `x` at which it
succeeds. -/
theorem weightedWorlds_rs_eq (hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe Lax794877.Queries.rst A)) :
    WeightedWorlds Lax794877.Queries.rs A = (∏ y, tT A y) *
      ∑ x, (∏ x' ∈ Finset.univ.filter (· < x), failW A x') * succW A x *
        ∏ x' ∈ Finset.univ.filter (x < ·), (failW A x' + succW A x') := by
  have htot : (∏ z : Var A, (fullPresWeight ((factEquiv A).symm z) +
      fullAbsWeight ((factEquiv A).symm z))) =
      (∏ y, tT A y) * ∏ x, (failW A x + succW A x) := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_prod_type,
      Finset.prod_congr rfl fun x _ => failW_add_succW x, Finset.prod_mul_distrib]
    change (∏ x, (aR A x + cR A x)) * ((∏ x, ∏ y, (aS A x y + cS A x y)) * ∏ y, tT A y) = _
    ring
  have hadd := weightedCount_add_not
    (fun z : Var A => fullPresWeight ((factEquiv A).symm z))
    (fun z => fullAbsWeight ((factEquiv A).symm z)) holdsRs
  rw [← weightedWorlds_rs_eq_weightedCount hlin, weightedCount_fail, htot,
    prod_add_eq_prod_add_sum (failW A) (succW A), mul_add] at hadd
  rw [add_comm] at hadd
  exact Nat.add_left_cancel hadd

end Count

/-! ## Step 14: the term -/

section Term

variable {δ : Type}

/-- The weight of presence of `R(x)`, as a term. -/
noncomputable def aRT (x : δ) : Lax366625.QuantitativeLogic.QTerm (wOrd Lax794877.Queries.rst) δ := fullPresT Lax794877.Queries.rstR ![x]

/-- The weight of absence of `R(x)`, as a term. -/
noncomputable def cRT (x : δ) : Lax366625.QuantitativeLogic.QTerm (wOrd Lax794877.Queries.rst) δ := fullAbsT Lax794877.Queries.rstR ![x]

/-- The weight of presence of `S(x, y)`, as a term. -/
noncomputable def aST (x y : δ) : Lax366625.QuantitativeLogic.QTerm (wOrd Lax794877.Queries.rst) δ := fullPresT Lax794877.Queries.rstS ![x, y]

/-- The weight of absence of `S(x, y)`, as a term. -/
noncomputable def cST (x y : δ) : Lax366625.QuantitativeLogic.QTerm (wOrd Lax794877.Queries.rst) δ := fullAbsT Lax794877.Queries.rstS ![x, y]

/-- The total weight of `T(y)`, as a term. -/
noncomputable def tTT (y : δ) : Lax366625.QuantitativeLogic.QTerm (wOrd Lax794877.Queries.rst) δ :=
  .add (fullPresT Lax794877.Queries.rstT ![y]) (fullAbsT Lax794877.Queries.rstT ![y])

/-- The weight of failing at `x`, as a term. -/
noncomputable def failT (x : δ) : Lax366625.QuantitativeLogic.QTerm (wOrd Lax794877.Queries.rst) δ :=
  .add (.mul (aRT x) (QTerm.prodOver fun up y => cST (up x) y))
    (.mul (cRT x) (QTerm.prodOver fun up y => .add (aST (up x) y) (cST (up x) y)))

/-- The weight of succeeding at `x`, as a term: a sum over the first `y`. -/
noncomputable def succT (x : δ) : Lax366625.QuantitativeLogic.QTerm (wOrd Lax794877.Queries.rst) δ :=
  .mul (aRT x) (QTerm.sumOver fun up y =>
    .mul (.mul
      (QTerm.prodOver fun up' y' =>
        QTerm.cond (ltF (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) y' (up' y))
          (cST (up' (up x)) y') (.const 1))
      (aST (up x) y))
      (QTerm.prodOver fun up' y' =>
        QTerm.cond (ltF (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) (up' y) y')
          (.add (aST (up' (up x)) y') (cST (up' (up x)) y')) (.const 1)))

/-- **The term computing the weighted count of the query**: the total weight
of the `T`-facts, times the sum, over the first `x` at which the query
succeeds, of the weight of failing before, succeeding at `x`, and doing
anything after; all of it `0` unless the positions are linearly ordered. -/
noncomputable def rsT : Lax366625.QuantitativeLogic.QTerm (wOrd Lax794877.Queries.rst) Empty :=
  .mul linGuardT (.mul (QTerm.prodOver fun _ y => tTT y)
    (QTerm.sumOver fun _ x =>
      .mul (.mul
        (QTerm.prodOver fun up x' =>
          QTerm.cond (ltF (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) x' (up x)) (failT x') (.const 1))
        (succT x))
        (QTerm.prodOver fun up x' =>
          QTerm.cond (ltF (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst) (up x) x')
            (.add (failT x') (succT x')) (.const 1))))

theorem comp_vec1 {A : Type} (v : δ → A) (x : δ) : (fun m => v (![x] m)) = ![v x] :=
  funext fun m => by fin_cases m; rfl

theorem comp_vec2 {A : Type} (v : δ → A) (x y : δ) :
    (fun m => v (![x, y] m)) = ![v x, v y] :=
  funext fun m => by fin_cases m <;> rfl

variable {A : Type} [(Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst).Structure A] [LinearOrder A]

section Leaves

variable [Finite A]

theorem eval_aRT (x : δ) (v : δ → A) : (aRT x).eval v = aR A (v x) := by
  rw [aRT, eval_fullPresT, comp_vec1, aR]

theorem eval_cRT (x : δ) (v : δ → A) : (cRT x).eval v = cR A (v x) := by
  rw [cRT, eval_fullAbsT, comp_vec1, cR]

theorem eval_aST (x y : δ) (v : δ → A) : (aST x y).eval v = aS A (v x) (v y) := by
  rw [aST, eval_fullPresT, comp_vec2, aS]

theorem eval_cST (x y : δ) (v : δ → A) : (cST x y).eval v = cS A (v x) (v y) := by
  rw [cST, eval_fullAbsT, comp_vec2, cS]

theorem eval_tTT (y : δ) (v : δ → A) : (tTT y).eval v = tT A (v y) := by
  rw [tTT, QTerm.eval_add, eval_fullPresT, eval_fullAbsT, comp_vec1, tT]

end Leaves

variable [Fintype A]

theorem eval_failT (x : δ) (v : δ → A) : (failT x).eval v = failW A (v x) := by
  rw [failT, QTerm.eval_add, QTerm.eval_mul, QTerm.eval_mul, QTerm.eval_prodOver,
    QTerm.eval_prodOver, eval_aRT, eval_cRT, finprod_eq_prod_of_fintype,
    finprod_eq_prod_of_fintype, failW]
  refine congrArg₂ (· + ·) (congrArg _ (Finset.prod_congr rfl fun y _ => ?_))
    (congrArg _ (Finset.prod_congr rfl fun y _ => ?_))
  · exact eval_cST _ _ _
  · rw [QTerm.eval_add, eval_aST, eval_cST]
    rfl

open Classical in
theorem eval_succT (x : δ) (v : δ → A) : (succT x).eval v = succW A (v x) := by
  rw [succT, QTerm.eval_mul, eval_aRT, QTerm.eval_sumOver, finsum_eq_sum_of_fintype, succW]
  refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
  rw [QTerm.eval_mul, QTerm.eval_mul, QTerm.eval_prodOver, QTerm.eval_prodOver, eval_aST,
    finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Finset.prod_filter,
    Finset.prod_filter]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (Finset.prod_congr rfl fun y' _ => ?_) rfl)
    (Finset.prod_congr rfl fun y' _ => ?_)
  · rw [QTerm.eval_cond, eval_cST]
    exact if_congr (realize_ltF _ _) rfl rfl
  · rw [QTerm.eval_cond, QTerm.eval_add, eval_aST, eval_cST]
    exact if_congr (realize_ltF _ _) rfl rfl

omit [Fintype A] in
open Classical in
/-- **The term computes the weighted count of the query.** -/
theorem rsT_value [Finite A] : WeightedWorlds Lax794877.Queries.rs A = rsT.value A := by
  let := Fintype.ofFinite A
  rw [Lax366625.QuantitativeLogic.QTerm.value, rsT, QTerm.eval_mul, eval_linGuardT]
  by_cases hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe Lax794877.Queries.rst A)
  · rw [if_pos hlin, one_mul, weightedWorlds_rs_eq hlin, QTerm.eval_mul, QTerm.eval_prodOver,
      QTerm.eval_sumOver, finprod_eq_prod_of_fintype, finsum_eq_sum_of_fintype]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun y _ =>
        (eval_tTT (A := A) (Sum.inr 0) (Sum.elim default fun _ => y)).symm)
      (Finset.sum_congr rfl fun x _ => ?_)
    rw [QTerm.eval_mul, QTerm.eval_mul, QTerm.eval_prodOver, QTerm.eval_prodOver, eval_succT,
      finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Finset.prod_filter,
      Finset.prod_filter]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (Finset.prod_congr rfl fun x' _ => ?_) rfl)
      (Finset.prod_congr rfl fun x' _ => ?_)
    · rw [QTerm.eval_cond, eval_failT]
      exact if_congr (realize_ltF (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst)
        (v := Sum.elim (Sum.elim (default : Empty → A) fun _ => x) fun _ => x') (Sum.inr 0)
        (Sum.inl (Sum.inr 0))).symm rfl rfl
    · rw [QTerm.eval_cond, QTerm.eval_add, eval_failT, eval_succT]
      exact if_congr (realize_ltF (L := Lax794877.WeightedWorlds.weightedLang Lax794877.Queries.rst)
        (v := Sum.elim (Sum.elim (default : Empty → A) fun _ => x) fun _ => x')
        (Sum.inl (Sum.inr 0)) (Sum.inr 0)).symm rfl rfl
  · rw [if_neg hlin, zero_mul]
    exact weightedWorlds_of_not_isLinOrd Lax794877.Queries.rs A hlin

end Term

end SafeQ

/-! ## Step 15: the theorem -/

/-- **The weighted count of `∃ x y, R(x) ∧ S(x, y)` is in FP**: the numerator
of the probability of this query over a probabilistic database is computed in
polynomial time, where that of `∃ x y, R(x) ∧ S(x, y) ∧ T(y)` is `#P`-hard
(`DescriptiveComplexity.weightedWorlds_h0_sharpP_oneCallComplete`). -/
theorem weightedWorlds_rs_mem_FP : WeightedWorlds Lax794877.Queries.rs ∈ FP :=
  fpDefinable_of_qfo SafeQ.rsT fun _ _ _ _ _ => SafeQ.rsT_value

end Lax794877Proofs.DescriptiveComplexity


