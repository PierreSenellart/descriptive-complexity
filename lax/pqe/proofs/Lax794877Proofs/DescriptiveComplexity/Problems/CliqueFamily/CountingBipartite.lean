/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingAll
import Lax794877Proofs.DescriptiveComplexity.Problems.CliqueFamily.Stretch
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax859101.CountingBipartite
end Lax859101.CountingBipartite

namespace Lax859101.OneCallReductions
end Lax859101.OneCallReductions

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax859101.OneCallReductions (PolyTerm)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax859101.CountingBipartite (BGEdge BGLeft BipIndep Pp2dnfModel)
end Lax794877Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax859101.CountingBipartite (bgEdge bgLeft bipGraph)
end FirstOrder.Language

/-!
# #BIS and #PP2DNF: counting the independent sets of a bipartite graph

A *bipartite graph* is given with its bipartition
(`FirstOrder.Language.bipGraph`): a unary relation marks the left side, the
right side is the rest, and only the edges from a left vertex to a right vertex
are read. `DescriptiveComplexity.SharpBIS` is the number of its independent
sets, the sets with no edge from a left member to a right member.

Like the count of all the independent sets of a graph, it is one-call
`#P`-complete and not parsimoniously
(`DescriptiveComplexity.sharpBIS_sharpP_oneCallComplete`). Hardness is from that
problem, by stretching (`DescriptiveComplexity.stretchInterp`): every edge is
replaced by `2n` paths of length two through new middle vertices, which form
the left side. An independent set of the result is any set `S` of vertices and
any set of middles of the edges with no endpoint in `S`, so the oracle answers
`∑ S, (2 ^ (2n)) ^ e(S)`, and the remainder modulo `2 ^ (2n)` counts the sets
with `e(S) = 0`, the complements of the independent sets
(`DescriptiveComplexity.card_stretchIndep_mod`).

`DescriptiveComplexity.SharpPP2DNF` is the same data read as a formula: one
variable per vertex and one term `x ∧ y` per edge, a *partitioned positive
2-DNF*. Its models are the sets of vertices that are not independent, so
`#BIS + #PP2DNF = 2 ^ n` (`DescriptiveComplexity.sharpBIS_add_sharpPP2DNF`) and
it is one-call `#P`-complete as well
(`DescriptiveComplexity.sharpPP2DNF_sharpP_oneCallComplete`).

In the literature these are the two *partitioned positive* problems. The
independent sets of a bipartite graph are the complements of its vertex
covers, i.e., of the models of `⋀ (x ∨ y)` over its edges, so #BIS is
#PP2CNF, whose `#P`-hardness is due to
[Provan and Ball 1983][provan1983complexity]; #PP2DNF is its dual. This is
the form in which [Dalvi and Suciu 2012][dalvi2012dichotomy] (Theorem 5.1
there, and Proposition 5.2 for the query `R(x), S(x, y), T(y)`) use it. The
hardness proved here is by a different route, with one oracle call, and is
not taken from those papers.

The interpretation is three-dimensional and relativized: the vertices are the
diagonal triples of one tag, and each of two other tags carries the triples
`(u, v, i)` with `u – v` an edge.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [Lax859101.CountingBipartite.bipGraph.Structure A]

end Shorthands

/-! ### The problem -/

section Kernel

open Lax904597.SecondOrder.SOBlock

/-- The vocabulary of the kernel: bipartite graphs with one unary relation
variable. -/
abbrev bisSOLang : Language := Lax859101.CountingBipartite.bipGraph.sum satAssignBlock.lang

/-- The left-side symbol, in the kernel vocabulary. -/
abbrev kbLeftSym : bisSOLang.Relations 1 := Sum.inl Lax859101.CountingBipartite.bgLeft

/-- The edge symbol, in the kernel vocabulary. -/
abbrev kbEdgeSym : bisSOLang.Relations 2 := Sum.inl Lax859101.CountingBipartite.bgEdge

/-- The guessed set, in the kernel vocabulary. -/
abbrev kbSetSym : bisSOLang.Relations 1 := Sum.inr satNuSym

/-- The first-order kernel: no edge from a left member to a right member. -/
noncomputable def bisKernel : bisSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₁ kbSetSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        ((FirstOrder.Language.Relations.formula₁ kbSetSym (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          ((FirstOrder.Language.Relations.formula₁ kbLeftSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
            ((FirstOrder.Language.BoundedFormula.not
                  (FirstOrder.Language.Relations.formula₁ kbLeftSym (FirstOrder.Language.Term.var (Sum.inr 1)))).imp
              (FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₂ kbEdgeSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1))))))))

theorem realize_bisKernel {A : Type} [Lax859101.CountingBipartite.bipGraph.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize bisSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) bisKernel) ↔
      Lax859101.CountingBipartite.BipIndep A ((satAssignEquiv A).symm ρ) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := bisSOLang) (M := A) kbSetSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [bisKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, Language.relMap_sumInl, hsub]
  constructor
  · intro h x y hx hy hl hr
    exact h ![x, y] hx hy hl hr
  · intro h w hx hy hl hr
    exact h (w 0) (w 1) hx hy hl hr

end Kernel

/-- The number of independent sets of a bipartite graph is the number of
witnesses of the kernel. -/
theorem card_bipIndep_eq_witnessCount (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    Nat.card {S : A → Prop // Lax859101.CountingBipartite.BipIndep A S} = Lax366625.WitnessCounting.witnessCount satAssignBlock bisKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun S => by
    rw [realize_bisKernel, Equiv.symm_apply_apply])

/-- **#BIS**: the number of independent sets of a bipartite graph. -/
noncomputable def SharpBIS : Lax366625.CountingProblems.CountingProblem Lax859101.CountingBipartite.bipGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @Lax859101.CountingBipartite.BipIndep A inst S}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_bipIndep_eq_witnessCount A, card_bipIndep_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock bisKernel e

theorem sharpBIS_apply (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    SharpBIS A = Nat.card {S : A → Prop // Lax859101.CountingBipartite.BipIndep A S} :=
  rfl

/-! ### The stretched graph -/

/-- Domain of the middle vertices: the triples whose first two coordinates are
the ends of an edge. -/
noncomputable def stretchMidDom : (Language.graph.sum Language.order).Formula (Fin 3) :=
  (∼((Term.var 0).equal (Term.var 1))) ⊓
    LHom.sumInl.onFormula (Language.adj.formula₂ (Term.var 0) (Term.var 1))

/-- The stretched graph, drawn in triples: the tag `none` carries the vertices,
on the diagonal, and each tag `some b` the middle vertices `(u, v, i)` of the
edge `u – v`, adjacent to `u` and to `v`. The middle vertices are the left
side. -/
noncomputable def stretchInterp :
    Lax904597.Relativized.RelFOInterpretation (Language.graph.sum Language.order) Lax859101.CountingBipartite.bipGraph (Option Bool) 3 where
  relFormula {n} R :=
    match n, R with
    | _, .left => fun t =>
      match t 0 with
      | none => ⊥
      | some _ => ⊤
    | _, .edge => fun t =>
      match t 0, t 1 with
      | some _, none => FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (1, 0)) (FirstOrder.Language.Term.var (0, 0)) ⊔
                            FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (1, 0)) (FirstOrder.Language.Term.var (0, 1))
      | _, _ => ⊥
  domFormula := fun t =>
    match t with
    | none => (Term.var 0).equal (Term.var 1) ⊓ (Term.var 1).equal (Term.var 2)
    | some _ => stretchMidDom

section Stretch

variable {A : Type} [Language.graph.Structure A] [LinearOrder A]

theorem realize_stretchMidDom (w : Fin 3 → A) :
    stretchMidDom.Realize w ↔ w 0 ≠ w 1 ∧ RelMap Language.adj ![w 0, w 1] := by
  simp [stretchMidDom, LHom.realize_onFormula, Formula.realize_rel₂]

/-- The points of the stretched graph: a vertex, or a middle vertex of an
edge. -/
noncomputable def stretchEquiv : stretchInterp.MapRel A ≃
    A ⊕ EdgePair (fun a b : A => RelMap Language.adj ![a, b]) × (Bool × A) where
  toFun x :=
    match x with
    | ⟨(none, w), _⟩ => .inl (w 0)
    | ⟨(some b, w), hw⟩ => .inr (⟨(w 0, w 1), (realize_stretchMidDom w).mp hw⟩, (b, w 2))
  invFun y :=
    match y with
    | .inl a => ⟨(none, ![a, a, a]), by simp [stretchInterp]⟩
    | .inr q => ⟨(some q.2.1, ![q.1.1.1, q.1.1.2, q.2.2]),
        (realize_stretchMidDom _).mpr q.1.2⟩
  left_inv := by
    rintro ⟨⟨t, w⟩, hw⟩
    cases t with
    | none =>
      have h : w 0 = w 1 ∧ w 1 = w 2 := by simpa [stretchInterp] using hw
      refine Subtype.ext (Prod.ext rfl (funext fun j => ?_))
      fin_cases j
      · rfl
      · exact h.1
      · exact h.1.trans h.2
    | some b =>
      refine Subtype.ext (Prod.ext rfl (funext fun j => ?_))
      fin_cases j <;> rfl
  right_inv := by
    rintro (a | q) <;> rfl

theorem stretch_left (x : stretchInterp.MapRel A) :
    Lax859101.CountingBipartite.BGLeft x ↔ (stretchEquiv x).isRight = true := by
  rw [Lax859101.CountingBipartite.BGLeft, RelFOInterpretation.relMap_mapRel]
  obtain ⟨⟨t, w⟩, hw⟩ := x
  cases t with
  | none =>
    change _ ↔ false = true
    simp [stretchInterp]
  | some b =>
    change _ ↔ true = true
    simp [stretchInterp]

theorem stretch_edge (x y : stretchInterp.MapRel A) :
    Lax859101.CountingBipartite.BGEdge x y ↔ stretchEdge (fun a b : A => RelMap Language.adj ![a, b])
      (stretchEquiv x) (stretchEquiv y) := by
  rw [Lax859101.CountingBipartite.BGEdge, RelFOInterpretation.relMap_mapRel]
  obtain ⟨⟨t, w⟩, hw⟩ := x
  obtain ⟨⟨t', w'⟩, hw'⟩ := y
  cases t with
  | none =>
    change _ ↔ False
    cases t' <;> simp [stretchInterp]
  | some b =>
    cases t' with
    | none =>
      change _ ↔ (w' 0 = w 0 ∨ w' 0 = w 1)
      simp [stretchInterp]
    | some b' =>
      change _ ↔ False
      simp [stretchInterp]

/-- The independent sets of the interpreted bipartite graph are those of the
stretched graph. -/
theorem sharpBIS_stretch :
    SharpBIS (stretchInterp.MapRel A) =
      Nat.card {T : A ⊕ EdgePair (fun a b : A => RelMap Language.adj ![a, b]) × (Bool × A) →
        Prop // StretchIndep (fun a b : A => RelMap Language.adj ![a, b]) T} :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr stretchEquiv (Equiv.refl Prop))
    fun S => stretchIndep_equiv_iff stretchEquiv stretch_left stretch_edge S)

end Stretch

/-! ### The reduction -/

/-- **Counting the independent sets of a graph reduces to #BIS with one
call**: the number of independent sets of the stretched graph, modulo
`2 ^ (2n)`, is the number of independent sets of the graph. -/
noncomputable def sharpAllIndependentSets_oneCall_sharpBIS :
    SharpAllIndependentSets ≤ᶜ[≤] SharpBIS where
  Tag := Option Bool
  dim := 3
  toRelInterpretation := stretchInterp
  dom_nonempty := fun A _ _ _ _ =>
    ⟨none, fun _ => Classical.arbitrary A, by simp [stretchInterp]⟩
  post := .mod .oracle (.pow2 (.mul (.num 2) .univ))
  correct := fun A _ _ _ _ => by
    change SharpAllIndependentSets A =
      SharpBIS (stretchInterp.MapRel A) %
        2 ^ (2 * (PolyTerm.univ : Lax859101.OneCallReductions.PolyTerm Language.graph).eval A)
    have hpos : 0 < Nat.card A := Nat.card_pos
    have hW : Nat.card (Bool × A) = 2 * Nat.card A := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [PolyTerm.eval_univ, sharpBIS_stretch, ← hW,
      card_stretchIndep_mod _ (by rw [hW]; omega), sharpAllIndependentSets_apply]

/-- **#BIS is one-call `#P`-hard.** -/
theorem sharpBIS_sharpP_oneCallHard : SharpP.OneCallHard SharpBIS :=
  CountingClass.OneCallHard.of_oneCall sharpAllIndependentSets_oneCall_sharpBIS
    sharpAllIndependentSets_sharpP_oneCallHard

/-! ### #PP2DNF -/

/-- The models of the formula are the sets of vertices that are not
independent. -/
theorem pp2dnfModel_iff_not_bipIndep (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A]
    (S : A → Prop) : Lax859101.CountingBipartite.Pp2dnfModel A S ↔ ¬Lax859101.CountingBipartite.BipIndep A S := by
  constructor
  · rintro ⟨x, y, hx, hy, hl, hr, he⟩ h
    exact h x y hx hy hl hr he
  · intro h
    by_contra hno
    exact h fun x y hx hy hl hr he => hno ⟨x, y, hx, hy, hl, hr, he⟩

/-- The number of models of the formula is the number of witnesses of the
negated kernel of #BIS. -/
theorem card_pp2dnfModel_eq_witnessCount (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    Nat.card {S : A → Prop // Lax859101.CountingBipartite.Pp2dnfModel A S} = Lax366625.WitnessCounting.witnessCount satAssignBlock (∼bisKernel) A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun S => by
    let := satAssignBlock.structure (satAssignEquiv A S)
    rw [Sentence.Realize, Formula.realize_not, ← Sentence.Realize, realize_bisKernel,
      Equiv.symm_apply_apply]
    exact pp2dnfModel_iff_not_bipIndep A S)

/-- **#PP2DNF**: the number of satisfying assignments of a partitioned
positive 2-DNF formula, presented as its bipartite graph. -/
noncomputable def SharpPP2DNF : Lax366625.CountingProblems.CountingProblem Lax859101.CountingBipartite.bipGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @Lax859101.CountingBipartite.Pp2dnfModel A inst S}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_pp2dnfModel_eq_witnessCount A, card_pp2dnfModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock (∼bisKernel) e

theorem sharpPP2DNF_apply (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    SharpPP2DNF A = Nat.card {S : A → Prop // Lax859101.CountingBipartite.Pp2dnfModel A S} :=
  rfl

/-- **Independent sets and models share out the sets of vertices**:
`#BIS + #PP2DNF = 2 ^ n`. -/
theorem sharpBIS_add_sharpPP2DNF (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] [Finite A] :
    SharpBIS A + SharpPP2DNF A = 2 ^ Nat.card A := by
  have h1 : SharpPP2DNF A = Nat.card {S : A → Prop // ¬Lax859101.CountingBipartite.BipIndep A S} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun S => pp2dnfModel_iff_not_bipIndep A S)
  have h2 := card_not_add_card (V := A → Prop) (Lax859101.CountingBipartite.BipIndep A)
  have h3 : Nat.card (A → Prop) = 2 ^ Nat.card A := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_prop]
  rw [h1, sharpBIS_apply, ← h3, ← h2]
  exact Nat.add_comm _ _

/-- **#BIS reduces to #PP2DNF with one call**, on the same instance:
`#BIS = 2 ^ n - #PP2DNF`. -/
noncomputable def sharpBIS_oneCall_sharpPP2DNF : SharpBIS ≤ᶜ[≤] SharpPP2DNF :=
  (ParsimoniousReduction.refl SharpPP2DNF).toOneCall.ofPost (.sub (.pow2 .univ) .oracle)
    fun A _ _ _ _ => by
      change SharpBIS A =
        2 ^ (PolyTerm.univ : Lax859101.OneCallReductions.PolyTerm Lax859101.CountingBipartite.bipGraph).eval A - SharpPP2DNF A
      rw [PolyTerm.eval_univ, ← sharpBIS_add_sharpPP2DNF A]
      exact (Nat.add_sub_cancel_right ..).symm

/-- **#PP2DNF is one-call `#P`-hard.** -/
theorem sharpPP2DNF_sharpP_oneCallHard : SharpP.OneCallHard SharpPP2DNF :=
  CountingClass.OneCallHard.of_oneCall sharpBIS_oneCall_sharpPP2DNF sharpBIS_sharpP_oneCallHard

end Lax794877Proofs.DescriptiveComplexity


