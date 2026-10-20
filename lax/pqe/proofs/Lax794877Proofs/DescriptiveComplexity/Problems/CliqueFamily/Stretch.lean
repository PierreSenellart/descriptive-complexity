/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Problems.CliqueFamily.Pendant
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

namespace Lax859101.CountingAllSets
end Lax859101.CountingAllSets

namespace Lax794877Proofs.DescriptiveComplexity
export Lax859101.CountingAllSets (IndepSet)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Stretched edges: the independent sets of a graph, read off a bipartite one

The combinatorial core of the reduction from counting the independent sets of
a graph to counting those of a bipartite graph. Replace every edge `u – v` by
`t` paths `u – w – v` through new *middle* vertices: the result is bipartite,
the vertices on one side and the middles on the other. An independent set of
it is any set `S` of vertices together with any set of middles of the edges
having no endpoint in `S` (`DescriptiveComplexity.bisIndep_stretch_iff`), so
there are

`∑ S, (2 ^ t) ^ e(S)`

of them, `e(S)` being the number of edges with no endpoint in `S`. When
`2 ^ t` exceeds the number `2 ^ n` of sets of vertices, the remainder modulo
`2 ^ t` is the number of sets `S` with `e(S) = 0`, i.e., whose complement is
independent (`DescriptiveComplexity.card_bisIndep_stretch_mod`).
-/

namespace Lax794877Proofs.DescriptiveComplexity

variable {V W : Type}

/-- The edges of a graph, as ordered pairs of distinct adjacent vertices. -/
abbrev EdgePair (Adj : V → V → Prop) : Type := {p : V × V // p.1 ≠ p.2 ∧ Adj p.1 p.2}

/-- Independence in the stretched graph: no chosen middle vertex has a chosen
endpoint. -/
def StretchIndep (Adj : V → V → Prop) (T : V ⊕ EdgePair Adj × W → Prop) : Prop :=
  ∀ (q : EdgePair Adj × W) (a : V), T (.inr q) → T (.inl a) → ¬(a = q.1.1.1 ∨ a = q.1.1.2)

/-- An independent set of the stretched graph is a set of vertices, and middle
vertices of edges with no endpoint in it. -/
theorem stretchIndep_iff (Adj : V → V → Prop) (T : V ⊕ EdgePair Adj × W → Prop) :
    StretchIndep Adj T ↔
      ∀ q : EdgePair Adj × W, T (.inr q) → ¬T (.inl q.1.1.1) ∧ ¬T (.inl q.1.1.2) := by
  constructor
  · intro h q hq
    exact ⟨fun ha => h q _ hq ha (Or.inl rfl), fun ha => h q _ hq ha (Or.inr rfl)⟩
  · rintro h q a hq ha (rfl | rfl)
    · exact (h q hq).1 ha
    · exact (h q hq).2 ha

/-- The edges of the stretched graph, from a middle vertex to an endpoint. -/
def stretchEdge (Adj : V → V → Prop) :
    V ⊕ EdgePair Adj × W → V ⊕ EdgePair Adj × W → Prop
  | .inr q, .inl a => a = q.1.1.1 ∨ a = q.1.1.2
  | _, _ => False

/-- Independence in a bipartite graph presented as the stretched graph, the
middle vertices being its left side. -/
theorem stretchIndep_equiv_iff {T : Type} {Adj : V → V → Prop}
    (E : T ≃ V ⊕ EdgePair Adj × W) {Left : T → Prop} {Edge : T → T → Prop}
    (hleft : ∀ x, Left x ↔ (E x).isRight = true)
    (hedge : ∀ x y, Edge x y ↔ stretchEdge Adj (E x) (E y)) (S : T → Prop) :
    (∀ x y, S x → S y → Left x → ¬Left y → ¬Edge x y) ↔
      StretchIndep Adj fun z => S (E.symm z) := by
  constructor
  · intro h q a hq ha hor
    refine h (E.symm (.inr q)) (E.symm (.inl a)) hq ha ((hleft _).mpr (by simp))
      (fun hl => ?_) ((hedge _ _).mpr ?_)
    · have := (hleft _).mp hl
      simp at this
    · rw [E.apply_symm_apply, E.apply_symm_apply]
      exact hor
  · intro h x y hx hy _ _ he
    have he' := (hedge x y).mp he
    have hx' : S (E.symm (E x)) := by simpa using hx
    have hy' : S (E.symm (E y)) := by simpa using hy
    generalize E x = ex at he' hx'
    generalize E y = ey at he' hy'
    rcases ex with a | q
    · exact he'
    · rcases ey with b | r
      · exact h q b hx' hy' he'
      · exact he'

/-- **The independent sets of a graph, as a remainder.** In the graph whose
edges are stretched through `|W|` middle vertices each, `W` having more
elements than the graph has vertices, the number of independent sets modulo
`2 ^ |W|` is the number of independent sets of the graph. -/
theorem card_stretchIndep_mod [Finite V] [Finite W] (Adj : V → V → Prop)
    (hW : Nat.card V < Nat.card W) :
    Nat.card {T : V ⊕ EdgePair Adj × W → Prop // StretchIndep Adj T} % 2 ^ Nat.card W =
      Nat.card {U : V → Prop // Lax859101.CountingAllSets.IndepSet Adj U} := by
  classical
  let := Fintype.ofFinite (V → Prop)
  have hcount : Nat.card {T : V ⊕ EdgePair Adj × W → Prop // StretchIndep Adj T} =
      ∑ S : V → Prop, (2 ^ Nat.card W) ^
        Nat.card {p : EdgePair Adj // ¬S p.1.1 ∧ ¬S p.1.2} := by
    have e1 : {T : V ⊕ EdgePair Adj × W → Prop // StretchIndep Adj T} ≃
        {q : (V → Prop) × (EdgePair Adj × W → Prop) //
          ∀ p, q.2 p → ¬q.1 p.1.1.1 ∧ ¬q.1 p.1.1.2} :=
      Equiv.subtypeEquiv (Equiv.sumArrowEquivProdArrow V (EdgePair Adj × W) Prop)
        fun T => stretchIndep_iff Adj T
    have e2 : {q : (V → Prop) × (EdgePair Adj × W → Prop) //
          ∀ p, q.2 p → ¬q.1 p.1.1.1 ∧ ¬q.1 p.1.1.2} ≃
        Σ S : V → Prop, {F : EdgePair Adj × W → Prop //
          ∀ p, F p → ¬S p.1.1.1 ∧ ¬S p.1.1.2} :=
      { toFun := fun q => ⟨q.1.1, ⟨q.1.2, q.2⟩⟩
        invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr (e1.trans e2), Nat.card_sigma]
    refine Finset.sum_congr rfl fun S _ => ?_
    have e3 : {p : EdgePair Adj × W // ¬S p.1.1.1 ∧ ¬S p.1.1.2} ≃
        W × {p : EdgePair Adj // ¬S p.1.1 ∧ ¬S p.1.2} :=
      { toFun := fun p => (p.1.2, ⟨p.1.1, p.2⟩)
        invFun := fun x => ⟨(x.2.1, x.1), x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [card_subsets_eq_two_pow fun p : EdgePair Adj × W => ¬S p.1.1.1 ∧ ¬S p.1.1.2,
      Nat.card_congr e3, Nat.card_prod, pow_mul]
  have hbound : ∀ q, (Finset.univ.filter fun S : V → Prop =>
      Nat.card {p : EdgePair Adj // ¬S p.1.1 ∧ ¬S p.1.2} = q).card < 2 ^ Nat.card W := by
    intro q
    have hpow : Fintype.card (V → Prop) = 2 ^ Nat.card V := by
      rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_eq_fintype_card,
        Fintype.card_prop]
    calc _ ≤ Fintype.card (V → Prop) := Finset.card_le_univ _
      _ = 2 ^ Nat.card V := hpow
      _ < 2 ^ Nat.card W := Nat.pow_lt_pow_right (by norm_num) hW
  have h := sum_pow_div_mod (fun S : V → Prop =>
    Nat.card {p : EdgePair Adj // ¬S p.1.1 ∧ ¬S p.1.2}) (Nat.pow_pos (by norm_num)) hbound 0
  rw [pow_zero, Nat.div_one] at h
  rw [hcount, h, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hiff : ∀ S : V → Prop, Nat.card {p : EdgePair Adj // ¬S p.1.1 ∧ ¬S p.1.2} = 0 ↔
      Lax859101.CountingAllSets.IndepSet Adj fun v => ¬S v := by
    intro S
    rw [Nat.card_eq_zero, or_iff_left (not_infinite_iff_finite.mpr inferInstance)]
    constructor
    · intro hE x y hx hy hxy hadj
      exact hE.false ⟨⟨(x, y), hxy, hadj⟩, hx, hy⟩
    · intro hI
      exact ⟨fun p => hI p.1.1.1 p.1.1.2 p.2.1 p.2.2 p.1.2.1 p.1.2.2⟩
  exact Nat.card_congr
    { toFun := fun S => ⟨fun v => ¬S.1 v, (hiff S.1).mp S.2⟩
      invFun := fun U => ⟨fun v => ¬U.1 v, (hiff fun v => ¬U.1 v).mpr fun x y hx hy =>
        U.2 x y (not_not.mp hx) (not_not.mp hy)⟩
      left_inv := fun S => Subtype.ext (funext fun v => propext not_not)
      right_inv := fun U => Subtype.ext (funext fun v => propext not_not) }

end Lax794877Proofs.DescriptiveComplexity


