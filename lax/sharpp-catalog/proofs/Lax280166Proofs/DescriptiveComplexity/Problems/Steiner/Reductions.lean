/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Problems.Steiner.Defs
import Lax280166Proofs.DescriptiveComplexity.OrderWalk
import Mathlib.Data.Fintype.Lattice
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

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.Steiner
end Lax799700.Steiner

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (HasSmallVertexCover MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Steiner (ConnectedOn HasSmallEdgeSteinerTree HasSmallSteinerTree Link STAdj STMarked STTerminal)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.Steiner (stAdj stMarked stTerminal steinerGraph)
end FirstOrder.Language

/-!
# Vertex Cover reduces to Steiner Tree

The classical reduction, read in the tagged framework
(`DescriptiveComplexity.steinerInterp`, tag `Fin 3`, dimension 2): a marked graph
becomes the bipartite incidence structure of its edges, plus a root joined to
every vertex.

* tag `0` on the diagonal carries the **vertices** of the input;
* tag `1` on adjacent off-diagonal pairs carries the **edges**, which are the
  terminals;
* tag `2` on the diagonal of the minimum carries the **root**, also a
  terminal;
* everything else is junk: isolated, non-terminal, unmarked, and therefore
  never in a chosen set.

A connected set containing all terminals must join every edge-terminal to the
root, and an edge's only neighbors are its two endpoints, so the vertices it
uses form a vertex cover; conversely a vertex cover joins every edge to the
root through one of its endpoints. Since vertices are the only non-terminals,
the budget counts exactly the cover, and the marked diagonal transports the
threshold unchanged.

The root is a *single* fresh element, so – as for the fresh variable of
`DescriptiveComplexity.Problems.NaeSat` – this is an **ordered** reduction: an
interpretation adds elements only by tags, and a tag contributes a whole copy
of the universe, so the root has to be picked out inside its copy as the
minimum (`DescriptiveComplexity.minF`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-- The adjacency symbol over the ordered expansion of marked graphs. -/
abbrev sAdjSym : (Lax799700.CliqueFamily.markedGraph.sum Language.order).Relations 2 := Sum.inl Lax799700.CliqueFamily.mgAdj

/-- The mark symbol over the ordered expansion of marked graphs. -/
abbrev sMarkedSym : (Lax799700.CliqueFamily.markedGraph.sum Language.order).Relations 1 := Sum.inl Lax799700.CliqueFamily.mgMarked

/-- “The pair is an edge of the input”, as a formula on the coordinates of the
`i`-th argument. -/
private noncomputable def isEdgeF {n : ℕ} (i : Fin n) :
    (Lax799700.CliqueFamily.markedGraph.sum Language.order).Formula (Fin n × Fin 2) :=
  Relations.formula₂ sAdjSym (Term.var (i, 0)) (Term.var (i, 1)) ⊓
    ∼(Term.equal (Term.var (i, 0)) (Term.var (i, 1)))

/-- “The pair is diagonal”, as a formula on the coordinates of the `i`-th
argument. -/
private noncomputable def isDiagF {n : ℕ} (i : Fin n) :
    (Lax799700.CliqueFamily.markedGraph.sum Language.order).Formula (Fin n × Fin 2) :=
  Term.equal (Term.var (i, 0)) (Term.var (i, 1))

/-- The three sorts of point of the interpreted structure. Tags built from
constructors, rather than `Fin 3`, so that the tag match inside the defining
formulas reduces definitionally in the characterization proofs. -/
inductive SteinerTag
  /-- A vertex of the input graph, carried by the diagonal. -/
  | vertex
  /-- An edge of the input graph, carried by an adjacent off-diagonal pair. -/
  | edge
  /-- The root, carried by the diagonal of the minimum. -/
  | root
  deriving DecidableEq

instance : Fintype SteinerTag := ⟨{.vertex, .edge, .root}, fun t => by cases t <;> decide⟩

instance : Inhabited SteinerTag := ⟨.vertex⟩

/-- The interpretation of Vertex Cover into Steiner Tree. -/
noncomputable def steinerInterp :
    Lax904597.Interpretations.FOInterpretation (Lax799700.CliqueFamily.markedGraph.sum Language.order) Lax799700.Steiner.steinerGraph
      SteinerTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t =>
        match t 0, t 1 with
        | .vertex, .edge =>
            (isDiagF 0) ⊓ (isEdgeF 1) ⊓
                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0)) ⊔
                  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 1)))
        | .root, .vertex => isDiagF 0 ⊓ minF (0, 0) ⊓ isDiagF 1
        | _, _ => ⊥
    | _, .terminal => fun t =>
        match t 0 with
        | .edge => isEdgeF 0
        | .root => isDiagF 0 ⊓ minF (0, 0)
        | _ => ⊥
    | _, .marked => fun t =>
        match t 0 with
        | .vertex => (isDiagF 0) ⊓ FirstOrder.Language.Relations.formula₁ sMarkedSym (FirstOrder.Language.Term.var (0, 0))
        | _ => ⊥

section Points

variable {A : Type}

/-- The point carrying the vertex `v`. -/
def vPt (v : A) : steinerInterp.Map A := (.vertex, ![v, v])

/-- The point carrying the (oriented) edge `(u, v)`. -/
def ePt (u v : A) : steinerInterp.Map A := (.edge, ![u, v])

/-- The point carrying the root, at the minimum `m`. -/
def rPt (m : A) : steinerInterp.Map A := (.root, ![m, m])

theorem vPt_injective : Function.Injective (vPt (A := A)) :=
  fun _ _ h => congrArg (fun p : SteinerTag × (Fin 2 → A) => p.2 0) h

end Points

section Characterizations

end Characterizations

/-! #### Shapes

The three master characterizations, from which the point-level lemmas above
and the case analyses of the correctness proof follow. -/

section Shapes

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [LinearOrder A]

theorem steiner_adj_iff (t t' : SteinerTag) (w w' : Fin 2 → A) :
    Lax799700.Steiner.STAdj (A := steinerInterp.Map A) (t, w) (t', w') ↔
      (t = .vertex ∧ t' = .edge ∧ w 0 = w 1 ∧ (Lax799700.CliqueFamily.MGAdj (w' 0) (w' 1) ∧ w' 0 ≠ w' 1) ∧
        (w 0 = w' 0 ∨ w 0 = w' 1)) ∨
      (t = .root ∧ t' = .vertex ∧ w 0 = w 1 ∧ (∀ a : A, w 0 ≤ a) ∧ w' 0 = w' 1) := by
  change RelMap (M := steinerInterp.Map A) Lax799700.Steiner.stAdj ![(t, w), (t', w')] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> cases t' <;>
    simp [steinerInterp, isDiagF, isEdgeF, Lax799700.CliqueFamily.MGAdj, realize_minF, Formula.realize_rel₂, and_assoc]

theorem steiner_terminal_iff (t : SteinerTag) (w : Fin 2 → A) :
    Lax799700.Steiner.STTerminal (A := steinerInterp.Map A) (t, w) ↔
      (t = .edge ∧ Lax799700.CliqueFamily.MGAdj (w 0) (w 1) ∧ w 0 ≠ w 1) ∨
      (t = .root ∧ w 0 = w 1 ∧ ∀ a : A, w 0 ≤ a) := by
  change RelMap (M := steinerInterp.Map A) Lax799700.Steiner.stTerminal ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;>
    simp [steinerInterp, isDiagF, isEdgeF, Lax799700.CliqueFamily.MGAdj, realize_minF, Formula.realize_rel₂]

theorem steiner_marked_iff (t : SteinerTag) (w : Fin 2 → A) :
    Lax799700.Steiner.STMarked (A := steinerInterp.Map A) (t, w) ↔ t = .vertex ∧ w 0 = w 1 ∧ Lax799700.CliqueFamily.MGMarked (w 0) := by
  change RelMap (M := steinerInterp.Map A) Lax799700.Steiner.stMarked ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;>
    simp [steinerInterp, isDiagF, Lax799700.CliqueFamily.MGMarked, Formula.realize_rel₁]

@[simp]
theorem steiner_adj_ve (v u w : A) :
    Lax799700.Steiner.STAdj (vPt v) (ePt u w) ↔ (Lax799700.CliqueFamily.MGAdj u w ∧ u ≠ w) ∧ (v = u ∨ v = w) := by
  simpa [vPt, ePt] using steiner_adj_iff (A := A) .vertex .edge ![v, v] ![u, w]

@[simp]
theorem steiner_adj_rv (m v : A) : Lax799700.Steiner.STAdj (rPt m) (vPt v) ↔ ∀ a : A, m ≤ a := by
  simpa [rPt, vPt] using steiner_adj_iff (A := A) .root .vertex ![m, m] ![v, v]

@[simp]
theorem steiner_terminal_e (u v : A) : Lax799700.Steiner.STTerminal (ePt u v) ↔ Lax799700.CliqueFamily.MGAdj u v ∧ u ≠ v := by
  simpa [ePt] using steiner_terminal_iff (A := A) .edge ![u, v]

@[simp]
theorem steiner_terminal_r (m : A) : Lax799700.Steiner.STTerminal (rPt m) ↔ ∀ a : A, m ≤ a := by
  simpa [rPt] using steiner_terminal_iff (A := A) .root ![m, m]

@[simp]
theorem steiner_terminal_v (v : A) : ¬Lax799700.Steiner.STTerminal (vPt v) := by
  simpa [vPt] using steiner_terminal_iff (A := A) .vertex ![v, v]

@[simp]
theorem steiner_marked_v (v : A) : Lax799700.Steiner.STMarked (vPt v) ↔ Lax799700.CliqueFamily.MGMarked v := by
  simpa [vPt] using steiner_marked_iff (A := A) .vertex ![v, v]

/-- A marked point of the interpreted structure is a vertex point. -/
theorem steiner_marked_shape {p : steinerInterp.Map A} (h : Lax799700.Steiner.STMarked p) : ∃ v, p = vPt v := by
  rcases p with ⟨t, w⟩
  obtain ⟨rfl, hdiag, -⟩ := (steiner_marked_iff t w).mp h
  exact ⟨w 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [vPt, hdiag]⟩⟩

/-- A terminal of the interpreted structure is an edge point or the root. -/
theorem steiner_terminal_shape {p : steinerInterp.Map A} (h : Lax799700.Steiner.STTerminal p) :
    (∃ u v, p = ePt u v ∧ Lax799700.CliqueFamily.MGAdj u v ∧ u ≠ v) ∨ ∃ r, p = rPt r ∧ ∀ a : A, r ≤ a := by
  rcases p with ⟨t, w⟩
  rcases (steiner_terminal_iff t w).mp h with ⟨rfl, hadj, hne⟩ | ⟨rfl, hdiag, hmin⟩
  · refine Or.inl ⟨w 0, w 1, ?_, hadj, hne⟩
    exact Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [ePt]⟩
  · refine Or.inr ⟨w 0, ?_, hmin⟩
    exact Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [rPt, hdiag]⟩

/-- The neighbors of an edge point are the points of its two endpoints. -/
theorem steiner_link_ePt {S : steinerInterp.Map A → Prop} {u v : A}
    {q : steinerInterp.Map A} (h : Lax799700.Steiner.Link Lax799700.Steiner.STAdj S (ePt u v) q) :
    (q = vPt u ∨ q = vPt v) ∧ S q := by
  refine ⟨?_, h.2.1⟩
  rcases q with ⟨t', w'⟩
  rcases h.2.2 with hadj | hadj
  · rcases (steiner_adj_iff .edge t' ![u, v] w').mp hadj with ⟨h0, -⟩ | ⟨h0, -⟩ <;>
      exact absurd h0 (by decide)
  · rcases (steiner_adj_iff t' .edge w' ![u, v]).mp hadj with
      ⟨rfl, -, hdiag, -, hinc⟩ | ⟨-, h1, -⟩
    · have hq : ((SteinerTag.vertex, w') : steinerInterp.Map A) = vPt (w' 0) :=
        Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [vPt, hdiag]⟩
      rcases hinc with hu | hv
      · exact Or.inl (hq.trans (congrArg vPt (by simpa using hu)))
      · exact Or.inr (hq.trans (congrArg vPt (by simpa using hv)))
    · exact absurd h1 (by decide)

end Shapes

/-! #### Counting on the vertex points -/

section Counting

variable {A : Type}

/-- A predicate holding only of vertex points encodes the same number as its
restriction to the vertices. -/
theorem ncard_vPt_eq (P : A → Prop) (Q : steinerInterp.Map A → Prop)
    (hshape : ∀ p, Q p → ∃ v, p = vPt v) (hP : ∀ v : A, Q (vPt v) ↔ P v) :
    {p | Q p}.ncard = {v | P v}.ncard := by
  have hset : {p | Q p} = vPt '' {v | P v} := by
    ext p
    constructor
    · intro hq
      obtain ⟨v, rfl⟩ := hshape p hq
      exact ⟨v, (hP v).mp hq, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hP v).mpr hv
  rw [hset, Set.ncard_image_of_injective _ vPt_injective]

end Counting

/-! #### The two halves of the correspondence, set by set -/

section Halves

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [LinearOrder A]

/-- The terminals together with the points of a vertex cover are connected:
every edge reaches the root through a covering endpoint. -/
theorem steiner_connectedOn_of_cover {m : A} (hm : ∀ a : A, m ≤ a) {C : A → Prop}
    (hcov : ∀ x y, x ≠ y → Lax799700.CliqueFamily.MGAdj x y → C x ∨ C y) :
    Lax799700.Steiner.ConnectedOn Lax799700.Steiner.STAdj fun p : steinerInterp.Map A => Lax799700.Steiner.STTerminal p ∨ ∃ v, C v ∧ p = vPt v := by
  have hroot : Lax799700.Steiner.STTerminal (rPt m (A := A)) := (steiner_terminal_r m).mpr hm
  have hlinkroot : ∀ v : A, C v →
      Lax799700.Steiner.Link Lax799700.Steiner.STAdj (fun p => Lax799700.Steiner.STTerminal p ∨ ∃ v, C v ∧ p = vPt v) (vPt v) (rPt m) := by
    intro v hv
    exact ⟨Or.inr ⟨v, hv, rfl⟩, Or.inl hroot,
      Or.inr ((steiner_adj_rv m v).mpr hm)⟩
  have hreach : ∀ p, (Lax799700.Steiner.STTerminal p ∨ ∃ v, C v ∧ p = vPt v) →
      Relation.ReflTransGen
        (Lax799700.Steiner.Link Lax799700.Steiner.STAdj fun p => Lax799700.Steiner.STTerminal p ∨ ∃ v, C v ∧ p = vPt v) p (rPt m) := by
    rintro p (hp | ⟨v, hv, rfl⟩)
    · rcases steiner_terminal_shape hp with ⟨u, v, rfl, hadj, hne⟩ | ⟨r, rfl, hminr⟩
      · -- an edge terminal: step to a covering endpoint, then to the root
        have hC := hcov u v hne hadj
        rcases hC with hu | hv
        · exact Relation.ReflTransGen.head
            (link_symm ⟨Or.inr ⟨u, hu, rfl⟩, Or.inl hp,
              Or.inl ((steiner_adj_ve u u v).mpr ⟨⟨hadj, hne⟩, Or.inl rfl⟩)⟩)
            (Relation.ReflTransGen.single (hlinkroot u hu))
        · exact Relation.ReflTransGen.head
            (link_symm ⟨Or.inr ⟨v, hv, rfl⟩, Or.inl hp,
              Or.inl ((steiner_adj_ve v u v).mpr ⟨⟨hadj, hne⟩, Or.inr rfl⟩)⟩)
            (Relation.ReflTransGen.single (hlinkroot v hv))
      · have : r = m := le_antisymm (hminr m) (hm r)
        subst this
        exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (hlinkroot v hv)
  intro x y hx hy
  exact (hreach x hx).trans
    (reflTransGen_symm (fun _ _ hab => link_symm hab) (hreach y hy))

/-- The vertices of a connected set containing the terminals cover every edge:
the path from an edge terminal to the root starts at an endpoint. -/
theorem steiner_cover_of_connected {m : A} (hm : ∀ a : A, m ≤ a)
    {S : steinerInterp.Map A → Prop} (hterms : ∀ p, Lax799700.Steiner.STTerminal p → S p)
    (hconn : Lax799700.Steiner.ConnectedOn Lax799700.Steiner.STAdj S) (x y : A) (hxy : x ≠ y) (hadj : Lax799700.CliqueFamily.MGAdj x y) :
    S (vPt x) ∨ S (vPt y) := by
  have hroot : Lax799700.Steiner.STTerminal (rPt m (A := A)) := (steiner_terminal_r m).mpr hm
  have hex : S (ePt x y) := hterms _ ((steiner_terminal_e x y).mpr ⟨hadj, hxy⟩)
  have hrt : S (rPt m) := hterms _ hroot
  have hpath := hconn (ePt x y) (rPt m) hex hrt
  rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨q, hlink, -⟩
  · have htag : SteinerTag.edge = SteinerTag.root :=
      congrArg (fun p : SteinerTag × (Fin 2 → A) => p.1) heq
    exact absurd htag (by decide)
  · obtain ⟨hq, hqS⟩ := steiner_link_ePt hlink
    rcases hq with rfl | rfl
    · exact Or.inl hqS
    · exact Or.inr hqS

end Halves

/-! #### Correctness -/

section Correctness

end Correctness

/-! ### The edge-weighted variant

The same construction, with one clause changed: the marked set must now count
`k` *plus one unit per edge point*, since a Steiner tree of the incidence
structure spends one edge joining each edge point to an endpoint before it can
spend anything on the cover. Marking the edge points themselves is exactly
that budget, and it needs no arithmetic in the formulas. -/

section EdgePoints

end EdgePoints

section EdgeShapes

end EdgeShapes

/-! #### Correctness of the edge-weighted reduction -/

section EdgeCorrectness

end EdgeCorrectness

section CoverPick

end CoverPick

section EdgeCorrectness'

end EdgeCorrectness'

end Lax280166Proofs.DescriptiveComplexity


