/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Tactic.FinCases
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Counting.PossibleWorlds
import DescriptiveComplexity.Problems.CliqueFamily.CountingBipartite

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
result formalized here.

## The model

We restrict the probabilities to `1` and `1/2`: a fact is *certain*, or it is
*uncertain* and present with probability `1/2`. This is all the hardness proof
of `h₀` uses, and it turns a probability into a count: with `k` uncertain
facts there are `2 ^ k` equally likely possible worlds
(`DescriptiveComplexity.card_isWorld`), so the probability of a query is the
number of worlds in which it holds, divided by `2 ^ k`. Probabilities in the
instance, which the harder queries of the dichotomy need, are out of scope.

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

## What kind of hardness

#PP2DNF is itself complete under one-call reductions only, so the statement
is one-call completeness, not plain completeness: every problem of `#P` is
answered by one question about the probability of `h₀`, followed by
arithmetic. A formula of this kind always has a world in which it holds as
soon as the graph has an edge, so no parsimonious reduction from #SAT can
exist unless `P = NP`. Whether the problem is complete under subtractive
reductions is not known here.

Unlike the two other tutorials, this one does not start from a concrete
presentation of instances with its encoding: the instance is the pair of
structures directly.
-/

namespace FirstOrder

namespace Language

/-- The schema of the example: two unary relations and a binary one. -/
fo_language rst with rst where
  /-- `r a`. -/
  r : 1
  /-- `s a b`. -/
  s : 2
  /-- `t b`. -/
  t : 1

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ## Steps 1 and 4: the schema, and the query -/

instance : Finite (Σ n, Language.rst.Relations n) :=
  Finite.of_surjective
    (fun i : Fin 3 => match i with
      | 0 => (⟨1, rstR⟩ : Σ n, Language.rst.Relations n)
      | 1 => ⟨2, rstS⟩
      | 2 => ⟨1, rstT⟩)
    (by
      rintro ⟨n, R⟩
      cases R
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)

/-- The query `h₀ = ∃ x y, R(x) ∧ S(x, y) ∧ T(y)`. -/
noncomputable def h0 : Language.rst.Sentence :=
  fo% ∃ x y, rstR(x) ∧ rstS(x, y) ∧ rstT(y)

theorem realize_h0 {B : Type} (ρ : (worldBlock Language.rst).Assignment B) :
    @Sentence.Realize Language.rst B (worldStructure ρ) h0 ↔
      ∃ a b : B, ρ ⟨1, rstR⟩ ![a] ∧ ρ ⟨2, rstS⟩ ![a, b] ∧ ρ ⟨1, rstT⟩ ![b] := by
  let := worldStructure ρ
  rw [h0]
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr]
  constructor
  · rintro ⟨v, h⟩
    exact ⟨v 0, v 1, h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨![a, b], h⟩

/-! ## Step 5: hardness, from #PP2DNF -/

section Semantic

variable {A B : Type} [Language.bipGraph.Structure A] [(Language.rst.sum Language.rst).Structure B]

/-- **The worlds of a bipartite graph.** Let the instance `B` hold a bipartite
graph `A` this way: `S` is certain and is the set of edges from the left side
to the right side, `R` is uncertain and is the left side, `T` is uncertain and
is the right side. Then the worlds satisfying `h₀` are as many as the models
of the partitioned positive 2-DNF formula of the graph: a world is a set of
left vertices and a set of right vertices, and `h₀` says that some edge has
both its ends chosen. -/
theorem possibleWorlds_h0_eq (e : A ≃ B)
    (hcR : ∀ x : Fin 1 → B, ¬RelMap (L := Language.rst.sum Language.rst) (Sum.inl rstR) x)
    (hcT : ∀ x : Fin 1 → B, ¬RelMap (L := Language.rst.sum Language.rst) (Sum.inl rstT) x)
    (hcS : ∀ x : Fin 2 → B, RelMap (L := Language.rst.sum Language.rst) (Sum.inl rstS) x ↔
      BGLeft (e.symm (x 0)) ∧ ¬BGLeft (e.symm (x 1)) ∧ BGEdge (e.symm (x 0)) (e.symm (x 1)))
    (huR : ∀ x : Fin 1 → B, RelMap (L := Language.rst.sum Language.rst) (Sum.inr rstR) x ↔
      BGLeft (e.symm (x 0)))
    (huT : ∀ x : Fin 1 → B, RelMap (L := Language.rst.sum Language.rst) (Sum.inr rstT) x ↔
      ¬BGLeft (e.symm (x 0)))
    (huS : ∀ x : Fin 2 → B, ¬RelMap (L := Language.rst.sum Language.rst) (Sum.inr rstS) x) :
    PossibleWorlds h0 B = SharpPP2DNF A := by
  rw [possibleWorlds_apply, sharpPP2DNF_apply]
  symm
  -- The world of a set of vertices.
  let F : (A → Prop) → (worldBlock Language.rst).Assignment B := fun S p =>
    match p with
    | ⟨_, .r⟩ => fun x : Fin 1 → B => S (e.symm (x 0)) ∧ BGLeft (e.symm (x 0))
    | ⟨_, .s⟩ => fun x : Fin 2 → B =>
      RelMap (L := Language.rst.sum Language.rst) (Sum.inl rstS) x
    | ⟨_, .t⟩ => fun x : Fin 1 → B => S (e.symm (x 0)) ∧ ¬BGLeft (e.symm (x 0))
  have hFr : ∀ S a, F S ⟨1, rstR⟩ ![e a] ↔ S a ∧ BGLeft a := fun S a => by
    change S (e.symm (e a)) ∧ BGLeft (e.symm (e a)) ↔ _
    rw [e.symm_apply_apply]
  have hFt : ∀ S a, F S ⟨1, rstT⟩ ![e a] ↔ S a ∧ ¬BGLeft a := fun S a => by
    change S (e.symm (e a)) ∧ ¬BGLeft (e.symm (e a)) ↔ _
    rw [e.symm_apply_apply]
  have hx1 : ∀ x : Fin 1 → B, ![e (e.symm (x 0))] = x := fun x =>
    funext fun j => by rw [Subsingleton.elim j 0]; simp
  have hworld : ∀ S, IsWorld (F S) := by
    rintro S ⟨n, R⟩ x
    cases R
    · exact ⟨fun h => (hcR x h).elim, fun h => Or.inr ((huR x).mpr h.2)⟩
    · exact ⟨id, Or.inl⟩
    · exact ⟨fun h => (hcT x h).elim, fun h => Or.inr ((huT x).mpr h.2)⟩
  have hquery : ∀ S, @Sentence.Realize Language.rst B (worldStructure (F S)) h0 ↔
      Pp2dnfModel A S := by
    intro S
    rw [realize_h0]
    constructor
    · rintro ⟨a, b, ⟨hSa, hla⟩, hs, hSb, hlb⟩
      exact ⟨e.symm a, e.symm b, hSa, hSb, hla, hlb, ((hcS _).mp hs).2.2⟩
    · rintro ⟨x, y, hx, hy, hl, hr, he⟩
      refine ⟨e x, e y, (hFr S x).mpr ⟨hx, hl⟩, (hcS _).mpr ?_, (hFt S y).mpr ⟨hy, hr⟩⟩
      simpa using And.intro hl (And.intro hr he)
  refine Nat.card_congr (Equiv.ofBijective
    (fun S : {S : A → Prop // Pp2dnfModel A S} =>
      (⟨F S.1, hworld S.1, (hquery S.1).mpr S.2⟩ :
        {ρ : (worldBlock Language.rst).Assignment B //
          IsWorld ρ ∧ @Sentence.Realize Language.rst B (worldStructure ρ) h0})) ⟨?_, ?_⟩)
  · rintro ⟨S, _⟩ ⟨S', _⟩ h
    have hF : F S = F S' := congrArg Subtype.val h
    refine Subtype.ext (funext fun a => propext ?_)
    have h1 : S a ∧ BGLeft a ↔ S' a ∧ BGLeft a :=
      (hFr S a).symm.trans ((iff_of_eq (congrFun (congrFun hF ⟨1, rstR⟩) ![e a])).trans
        (hFr S' a))
    have h2 : S a ∧ ¬BGLeft a ↔ S' a ∧ ¬BGLeft a :=
      (hFt S a).symm.trans ((iff_of_eq (congrFun (congrFun hF ⟨1, rstT⟩) ![e a])).trans
        (hFt S' a))
    by_cases hl : BGLeft a
    · exact ⟨fun h => (h1.mp ⟨h, hl⟩).1, fun h => (h1.mpr ⟨h, hl⟩).1⟩
    · exact ⟨fun h => (h2.mp ⟨h, hl⟩).1, fun h => (h2.mpr ⟨h, hl⟩).1⟩
  · rintro ⟨ρ, hw, hq⟩
    have hF : F (fun a => ρ ⟨1, rstR⟩ ![e a] ∨ ρ ⟨1, rstT⟩ ![e a]) = ρ := by
      funext ⟨n, R⟩ x
      cases R
      · have hR := congrArg (ρ ⟨1, rstR⟩) (hx1 x)
        have hT := congrArg (ρ ⟨1, rstT⟩) (hx1 x)
        refine propext ⟨?_, fun h => ?_⟩
        · rintro ⟨hS | hS, hl⟩
          · exact hR.mp hS
          · exact absurd hl ((huT x).mp (((hw ⟨1, rstT⟩ x).2 (hT.mp hS)).resolve_left (hcT x)))
        · exact ⟨Or.inl (hR.mpr h),
            (huR x).mp (((hw ⟨1, rstR⟩ x).2 h).resolve_left (hcR x))⟩
      · exact propext ⟨(hw ⟨2, rstS⟩ x).1, fun h => ((hw ⟨2, rstS⟩ x).2 h).resolve_right (huS x)⟩
      · have hR := congrArg (ρ ⟨1, rstR⟩) (hx1 x)
        have hT := congrArg (ρ ⟨1, rstT⟩) (hx1 x)
        refine propext ⟨?_, fun h => ?_⟩
        · rintro ⟨hS | hS, hl⟩
          · exact absurd ((huR x).mp (((hw ⟨1, rstR⟩ x).2 (hR.mp hS)).resolve_left (hcR x))) hl
          · exact hT.mp hS
        · exact ⟨Or.inr (hT.mpr h),
            (huT x).mp (((hw ⟨1, rstT⟩ x).2 h).resolve_left (hcT x))⟩
    exact ⟨⟨fun a => ρ ⟨1, rstR⟩ ![e a] ∨ ρ ⟨1, rstT⟩ ![e a],
      (hquery _).mp (hF.symm ▸ hq)⟩, Subtype.ext hF⟩

end Semantic

/-- The instance of a bipartite graph: the edges from left to right are the
certain `S`-facts, the left vertices the uncertain `R`-facts, and the right
vertices the uncertain `T`-facts. One-dimensional, single-tagged and
quantifier-free. -/
noncomputable def h0Interp :
    FOInterpretation Language.bipGraph (Language.rst.sum Language.rst) Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl .r => fun _ => ⊥
    | _, Sum.inl .s => fun _ => fo%⟨x, y⟩ bgLeft(x) ∧ ¬ bgLeft(y) ∧ bgEdge(x, y)
    | _, Sum.inl .t => fun _ => ⊥
    | _, Sum.inr .r => fun _ => fo%⟨x⟩ bgLeft(x)
    | _, Sum.inr .s => fun _ => ⊥
    | _, Sum.inr .t => fun _ => fo%⟨x⟩ ¬ bgLeft(x)

/-- **#PP2DNF reduces parsimoniously to counting the worlds of `h₀`**
([Dalvi and Suciu 2012][dalvi2012dichotomy], Proposition 5.2). -/
noncomputable def sharpPP2DNF_parsimonious_possibleWorlds_h0 :
    SharpPP2DNF ≤ᵖ PossibleWorlds h0 where
  Tag := Unit
  dim := 1
  toInterpretation := h0Interp
  correct := fun A _ _ _ => by
    refine (possibleWorlds_h0_eq (B := h0Interp.Map A) (h0Interp.mapEquivSelf A).symm
      (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_)).symm
    · exact fun h => (FOInterpretation.relMap_map ..).mp h
    · exact fun h => (FOInterpretation.relMap_map ..).mp h
    · refine (FOInterpretation.relMap_map ..).trans ?_
      change _ ↔ RelMap bgLeft ![(x 0).2 0] ∧ ¬RelMap bgLeft ![(x 1).2 0] ∧
        RelMap bgEdge ![(x 0).2 0, (x 1).2 0]
      simp [h0Interp, Formula.realize_rel₁, Formula.realize_rel₂]
    · refine (FOInterpretation.relMap_map ..).trans ?_
      change _ ↔ RelMap bgLeft ![(x 0).2 0]
      simp [h0Interp, Formula.realize_rel₁]
    · refine (FOInterpretation.relMap_map ..).trans ?_
      change _ ↔ ¬RelMap bgLeft ![(x 0).2 0]
      simp [h0Interp, Formula.realize_rel₁]
    · exact fun h => (FOInterpretation.relMap_map ..).mp h

/-! ## Step 6: the theorems -/

/-- **Counting the worlds of `h₀` is one-call `#P`-hard.** -/
theorem possibleWorlds_h0_sharpP_oneCallHard : SharpP.OneCallHard (PossibleWorlds h0) :=
  CountingClass.OneCallHard.of_parsimonious sharpPP2DNF_parsimonious_possibleWorlds_h0
    sharpPP2DNF_sharpP_oneCallHard

/-- **Counting the worlds of `h₀` is one-call `#P`-complete**: it is in `#P`,
like the count of the worlds of any first-order query, and every problem of
`#P` reduces to it with one call. -/
theorem possibleWorlds_h0_sharpP_oneCallComplete :
    SharpP.OneCallComplete (PossibleWorlds h0) :=
  .of_mem (possibleWorlds_mem_sharpP h0) possibleWorlds_h0_sharpP_oneCallHard

end DescriptiveComplexity
