/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingReductions
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.Pendant
import Lax859101Proofs.DescriptiveComplexity.Counting.Reduction
import Mathlib.ModelTheory.Graph
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

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax859101.CountingAllSets
end Lax859101.CountingAllSets

namespace Lax859101.OneCallReductions
end Lax859101.OneCallReductions

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax859101Proofs.DescriptiveComplexity
export Lax859101.OneCallReductions (PolyTerm)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax859101.CountingAllSets (IndepSet)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (MGAdj MGMarked)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

/-!
# Counting all the independent sets of a graph

`DescriptiveComplexity.SharpAllIndependentSets` is the number of independent
sets of a graph, of every size, on the plain vocabulary of graphs. A graph
always has one, the empty set, so the problem is not parsimoniously `#P`-hard
unless `P = NP`; it is one-call `#P`-complete
(`DescriptiveComplexity.sharpAllIndependentSets_sharpP_oneCallComplete`).

Hardness is from `DescriptiveComplexity.SharpIndependentSet`, which counts the
independent sets of exactly the threshold size and is parsimoniously complete.
The reduction (`DescriptiveComplexity.pendInterp`) attaches `n` pendant leaves
to each of the `n` vertices; an independent set of the result is an independent
set `S` of the graph and any set of leaves of the vertices outside `S`, so the
answer of the oracle is `∑ S, (2 ^ n) ^ (n - |S|)`, and the number of
independent sets of size `k` is its digit of rank `n - k` in base `2 ^ n`
(`DescriptiveComplexity.card_indepSet_pend_digit`, in
`DescriptiveComplexity.Problems.CliqueFamily.Pendant`). The post-processing
term is that digit, `oracle / 2 ^ (n * (n - k)) % 2 ^ n`: the number `n - k` is
the number of unmarked elements, a definable cardinality. This is the first
reduction of the library to use a quotient and a remainder.

The interpretation is two-dimensional and relativized: the vertices are the
diagonal pairs of one tag, the leaves all the pairs of the other.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Kernel

open Lax904597.SecondOrder.SOBlock

/-- The vocabulary of the kernel: graphs with one unary relation variable. -/
abbrev indepSOLang : Language := Language.graph.sum satAssignBlock.lang

/-- The adjacency symbol, in the kernel vocabulary. -/
abbrev kisAdjSym : indepSOLang.Relations 2 := Sum.inl Language.adj

/-- The guessed set, in the kernel vocabulary. -/
abbrev kisSetSym : indepSOLang.Relations 1 := Sum.inr satNuSym

/-- The first-order kernel: no two distinct elements of the set are adjacent. -/
noncomputable def indepKernel : indepSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₁ kisSetSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        ((FirstOrder.Language.Relations.formula₁ kisSetSym (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          ((FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1)))).imp
            (FirstOrder.Language.BoundedFormula.not
              (FirstOrder.Language.Relations.formula₂ kisAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1)))))))

theorem realize_indepKernel {A : Type} [Language.graph.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize indepSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) indepKernel) ↔
      Lax859101.CountingAllSets.IndepSet (fun x y : A => RelMap Language.adj ![x, y]) ((satAssignEquiv A).symm ρ) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := indepSOLang) (M := A) kisSetSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [indepKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_equal,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr,
    Language.relMap_sumInl, hsub]
  constructor
  · intro h x y hx hy hxy
    exact h ![x, y] hx hy hxy
  · intro h w hx hy hxy
    exact h (w 0) (w 1) hx hy hxy

end Kernel

/-- The number of independent sets of a graph is the number of witnesses of
the kernel. -/
theorem card_indepSet_eq_witnessCount (A : Type) [Language.graph.Structure A] :
    Nat.card {S : A → Prop // Lax859101.CountingAllSets.IndepSet (fun x y : A => RelMap Language.adj ![x, y]) S} =
      Lax366625.WitnessCounting.witnessCount satAssignBlock indepKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun S => by
    rw [realize_indepKernel, Equiv.symm_apply_apply])

/-- **#Independent Sets, of all sizes**: the number of independent sets of a
graph. -/
noncomputable def SharpAllIndependentSets : Lax366625.CountingProblems.CountingProblem Language.graph where
  Count := fun A inst =>
    Nat.card {S : A → Prop // Lax859101.CountingAllSets.IndepSet (fun x y : A => @RelMap _ A inst _ Language.adj ![x, y]) S}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_indepSet_eq_witnessCount A, card_indepSet_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock indepKernel e

theorem sharpAllIndependentSets_apply (A : Type) [Language.graph.Structure A] :
    SharpAllIndependentSets A =
      Nat.card {S : A → Prop // Lax859101.CountingAllSets.IndepSet (fun x y : A => RelMap Language.adj ![x, y]) S} :=
  rfl

/-- **Counting all the independent sets is in `#P`.** -/
theorem sharpAllIndependentSets_mem_sharpP : SharpAllIndependentSets ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_indepSet_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock indepKernel)

/-! ### The graph with pendant leaves -/

/-- The graph with pendant leaves, drawn in pairs: the tag `false` carries the
vertices, on the diagonal, and the tag `true` the leaves, the leaf `(a, i)`
being adjacent to the vertex `a` alone. -/
noncomputable def pendInterp :
    Lax904597.Relativized.RelFOInterpretation (Lax799700.CliqueFamily.markedGraph.sum Language.order) Language.graph Bool 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t =>
      match t 0, t 1 with
      | false, false => LHom.sumInl.onFormula (FirstOrder.Language.Relations.formula₂ Lax799700.CliqueFamily.mgAdj (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0)))
      | false, true => FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
      | true, false => FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
      | true, true => ⊥
  domFormula := fun t =>
    match t with
    | false => (Term.var 0).equal (Term.var 1)
    | true => ⊤

section Pend

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [LinearOrder A]

/-- The points of the graph with leaves: a vertex or a leaf. -/
noncomputable def pendEquiv : pendInterp.MapRel A ≃ A ⊕ A × A where
  toFun x :=
    match x.1.1 with
    | false => .inl (x.1.2 0)
    | true => .inr (x.1.2 0, x.1.2 1)
  invFun y :=
    match y with
    | .inl a => ⟨(false, ![a, a]), by simp [pendInterp]⟩
    | .inr p => ⟨(true, ![p.1, p.2]), by simp [pendInterp]⟩
  left_inv := by
    rintro ⟨⟨t, w⟩, hw⟩
    cases t
    · have h : w 0 = w 1 := by simpa [pendInterp] using hw
      refine Subtype.ext (Prod.ext rfl (funext fun j => ?_))
      fin_cases j
      · rfl
      · exact h
    · refine Subtype.ext (Prod.ext rfl (funext fun j => ?_))
      fin_cases j <;> rfl
  right_inv := by
    rintro (a | p) <;> rfl

/-- Adjacency in the interpreted graph is adjacency of the graph with pendant
leaves. -/
theorem pend_adj (x y : pendInterp.MapRel A) :
    RelMap Language.adj ![x, y] ↔
      pendAdj (fun a b : A => Lax799700.CliqueFamily.MGAdj a b) (pendEquiv x) (pendEquiv y) := by
  rw [RelFOInterpretation.relMap_mapRel]
  obtain ⟨⟨t, w⟩, hw⟩ := x
  obtain ⟨⟨t', w'⟩, hw'⟩ := y
  cases t <;> cases t'
  · change _ ↔ Lax799700.CliqueFamily.MGAdj (w 0) (w' 0)
    simp [pendInterp, LHom.realize_onFormula, Formula.realize_rel₂, Lax799700.CliqueFamily.MGAdj]
  · change _ ↔ w 0 = w' 0
    simp [pendInterp]
  · change _ ↔ w 0 = w' 0
    simp [pendInterp]
  · change _ ↔ False
    simp [pendInterp]

/-- “`x` is not marked.” -/
noncomputable def mgUnmarkedAt {α : Type} (x : α) : Lax799700.CliqueFamily.markedGraph.Formula α :=
  FirstOrder.Language.BoundedFormula.not
      (FirstOrder.Language.Relations.formula₁ Lax799700.CliqueFamily.mgMarked (FirstOrder.Language.Term.var x))

/-- The number of unmarked elements, as a polynomial term. -/
noncomputable def unmarkedCount : Lax859101.OneCallReductions.PolyTerm Lax799700.CliqueFamily.markedGraph :=
  .count (LHom.sumInl.onFormula (mgUnmarkedAt (0 : Fin 1)))

theorem eval_unmarkedCount : unmarkedCount.eval A = Nat.card {v : A // ¬Lax799700.CliqueFamily.MGMarked v} := by
  rw [unmarkedCount, PolyTerm.eval_count_one]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  rw [LHom.realize_onFormula, mgUnmarkedAt]
  simp [Formula.realize_rel₁, Lax799700.CliqueFamily.MGMarked]

/-- The independent sets of the interpreted graph are those of the graph with
pendant leaves. -/
theorem sharpAllIndependentSets_pend :
    SharpAllIndependentSets (pendInterp.MapRel A) =
      Nat.card {T : A ⊕ A × A → Prop // Lax859101.CountingAllSets.IndepSet (pendAdj fun a b : A => Lax799700.CliqueFamily.MGAdj a b) T} :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr pendEquiv (Equiv.refl Prop))
    fun S => indepSet_equiv_iff pendEquiv pend_adj S)

end Pend

/-! ### The reduction -/

/-- **#Independent Set reduces to counting all the independent sets, with one
call**: in the graph with `n` pendant leaves at each of its `n` vertices, the
independent sets of size `k` of the graph are counted by the digit of rank
`n - k` of the number of independent sets, in base `2 ^ n`. -/
noncomputable def sharpIndependentSet_oneCall_sharpAllIndependentSets :
    SharpIndependentSet ≤ᶜ[≤] SharpAllIndependentSets where
  Tag := Bool
  dim := 2
  toRelInterpretation := pendInterp
  dom_nonempty := fun A _ _ _ _ =>
    ⟨true, fun _ => Classical.arbitrary A, Formula.realize_top.mpr trivial⟩
  post := .mod (.div .oracle (.pow2 (.mul .univ unmarkedCount))) (.pow2 .univ)
  correct := fun A _ _ _ _ => by
    change SharpIndependentSet A =
      SharpAllIndependentSets (pendInterp.MapRel A) /
        2 ^ ((PolyTerm.univ : Lax859101.OneCallReductions.PolyTerm Lax799700.CliqueFamily.markedGraph).eval A * unmarkedCount.eval A) %
          2 ^ (PolyTerm.univ : Lax859101.OneCallReductions.PolyTerm Lax799700.CliqueFamily.markedGraph).eval A
    rw [PolyTerm.eval_univ, eval_unmarkedCount, sharpAllIndependentSets_pend,
      card_indepSet_pend_digit, sharpIndependentSet_apply]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun S =>
      ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩)

/-- **Counting all the independent sets is one-call `#P`-hard.** -/
theorem sharpAllIndependentSets_sharpP_oneCallHard : SharpP.OneCallHard SharpAllIndependentSets :=
  CountingClass.OneCallHard.of_oneCall sharpIndependentSet_oneCall_sharpAllIndependentSets
    (oneCallHard_sharpP_of_parsimoniousHard sharpIndependentSet_sharpP_parsimoniousHard)

/-- **Counting all the independent sets of a graph is one-call
`#P`-complete.** -/
theorem sharpAllIndependentSets_sharpP_oneCallComplete :
    SharpP.OneCallComplete SharpAllIndependentSets :=
  .of_mem sharpAllIndependentSets_mem_sharpP sharpAllIndependentSets_sharpP_oneCallHard

end Lax859101Proofs.DescriptiveComplexity


