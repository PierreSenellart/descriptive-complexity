/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Vocabulary
import Lax480241Proofs.DescriptiveComplexity.Problems.HornSat.Hardness
import Lax480241Proofs.DescriptiveComplexity.FixedPoint
import Lax480241Proofs.DescriptiveComplexity.FixedPointHorn
import Lax480241Proofs.DescriptiveComplexity.LogSpace
import Lax480241Proofs.DescriptiveComplexity.Complexity
import Lax480241Proofs.DescriptiveComplexity.Ordered
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax480241Proofs.Foreign.FirstOrder.Language
end Lax480241Proofs.Foreign.FirstOrder.Language

namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax485149.Reachability
end Lax485149.Reachability

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax485149.KromFragment (KromClause KromLit KromProgram SigmaSOKromDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCDefinable TCSpec)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax485149.Reachability (Reachable SGEdge SGSource SGTarget)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause HornProgram SigmaSOHornDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (LFPDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax485149.Reachability (sgEdge sgSource sgTarget stGraph)
end FirstOrder.Language

/-!
# Reachability, and the Horn fragment at work

The problem REACH – is some marked target reachable from some marked source in
a directed graph? – and its complement UNREACH, over the vocabulary
`FirstOrder.Language.stGraph` of graphs with marked sources and targets.

The point of this file is UNREACH: it is the worked instance of the SO-Horn
fragment of `DescriptiveComplexity.SecondOrderHorn`. Its Horn program guesses a binary
relation `T` and forces it, by two rules, to contain the transitive closure of
the edge relation, then rules out with a goal clause the case of a marked
target lying in `T` (or being itself a marked source):

```
             edge(x, y) → T(x, y)
  T(x, y) ∧  edge(y, z) → T(x, z)
  T(x, y) ∧ source(x) ∧ target(y) → ⊥
            source(x) ∧ target(x) → ⊥
```

Such a program is satisfiable exactly when its *least* model – here the
transitive closure – already satisfies the goal clauses, which is why the
existential second-order quantifier in front of a Horn kernel expresses a
polynomial-time property rather than a nondeterministic guess. That is the
content of `DescriptiveComplexity.unreach_sigmaSOHornDefinable`, and with the Horn
discharge it gives `DescriptiveComplexity.unreach_le_hornSat`: UNREACH first-order
reduces to HORN-SAT.

Note that it is the *complement* that the fragment defines: goal clauses can
only rule models out. This is the usual state of affairs for SO-Horn, and
harmless, both problems being in polynomial time.

The same file also places UNREACH one level lower, in
`DescriptiveComplexity.NL`: the Krom fragment defines it by a *two-literal*
program guessing the set `U` of vertices from which a marked target is
reachable,

```
              target(x) → U(x)
  edge(x, y)            → ¬U(y) ∨ U(x)
              source(x) → ¬U(x)
```

and the same asymmetry appears one level down, for the same reason. A clausal
fragment states closure and rejection, so it defines UNREACH head-on
(`DescriptiveComplexity.unreach_mem_NL`) while REACH would need the guessed set to be
*contained* in the true reachable set – a minimality condition no clause can
impose. At the Horn level the way out was the equivalence with FO(LFP), a full
logic closed under negation; at the Krom level the corresponding statement is
`NL = coNL`, i.e., Immerman–Szelepcsényi, and it is what carries
`DescriptiveComplexity.unreach_mem_NL` over to `REACH ∈ NL`
(`DescriptiveComplexity.reach_mem_NL`, in
`DescriptiveComplexity.ImmermanSzelepcsenyi`).
-/

namespace FirstOrder

namespace Language

open Lax480241Proofs.Foreign.FirstOrder.Language in
/-- The edge symbol in the ordered expansion. -/
abbrev _root_.Lax480241Proofs.Foreign.FirstOrder.Language.sgEdgeO : (Lax485149.Reachability.stGraph.sum Language.order).Relations 2 := Sum.inl Lax485149.Reachability.sgEdge

export Lax480241Proofs.Foreign.FirstOrder.Language (sgEdgeO)

open Lax480241Proofs.Foreign.FirstOrder.Language in
/-- The marked-source symbol in the ordered expansion. -/
abbrev _root_.Lax480241Proofs.Foreign.FirstOrder.Language.sgSourceO : (Lax485149.Reachability.stGraph.sum Language.order).Relations 1 := Sum.inl Lax485149.Reachability.sgSource

export Lax480241Proofs.Foreign.FirstOrder.Language (sgSourceO)

open Lax480241Proofs.Foreign.FirstOrder.Language in
/-- The marked-target symbol in the ordered expansion. -/
abbrev _root_.Lax480241Proofs.Foreign.FirstOrder.Language.sgTargetO : (Lax485149.Reachability.stGraph.sum Language.order).Relations 1 := Sum.inl Lax485149.Reachability.sgTarget

export Lax480241Proofs.Foreign.FirstOrder.Language (sgTargetO)

end Language

end FirstOrder

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Defs

variable {A : Type} [Lax485149.Reachability.stGraph.Structure A]

end Defs

section Iso

variable {A B : Type} [Lax485149.Reachability.stGraph.Structure A] [Lax485149.Reachability.stGraph.Structure B]

private theorem sgEdge_map (e : A ≃[Lax485149.Reachability.stGraph] B) (a b : A) :
    Lax485149.Reachability.SGEdge a b ↔ Lax485149.Reachability.SGEdge (e a) (e b) :=
  relMap_equiv₂ e Lax485149.Reachability.sgEdge a b

private theorem reflTransGen_map (e : A ≃[Lax485149.Reachability.stGraph] B) {a b : A}
    (h : Relation.ReflTransGen Lax485149.Reachability.SGEdge a b) :
    Relation.ReflTransGen Lax485149.Reachability.SGEdge (e a) (e b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ((sgEdge_map e _ _).mp hbc)

private theorem reachable_of_iso (e : A ≃[Lax485149.Reachability.stGraph] B) (h : Lax485149.Reachability.Reachable A) :
    Lax485149.Reachability.Reachable B := by
  obtain ⟨s, t, hs, ht, hpath⟩ := h
  exact ⟨e s, e t, (relMap_equiv₁ e Lax485149.Reachability.sgSource s).mp hs,
    (relMap_equiv₁ e Lax485149.Reachability.sgTarget t).mp ht, reflTransGen_map e hpath⟩

/-- Reachability is isomorphism-invariant. -/
theorem reachable_iso (e : A ≃[Lax485149.Reachability.stGraph] B) : Lax485149.Reachability.Reachable A ↔ Lax485149.Reachability.Reachable B :=
  ⟨reachable_of_iso e, reachable_of_iso e.symm⟩

end Iso

/-- REACH, as a problem on graphs with marked sources and targets. -/
def REACH : Lax904597.Problems.DecisionProblem Lax485149.Reachability.stGraph where
  Holds := fun A inst => @Lax485149.Reachability.Reachable A inst
  iso_invariant := fun e => reachable_iso e

/-- UNREACH, the complement of REACH: no marked target is reachable from a
marked source. -/
def UNREACH : Lax904597.Problems.DecisionProblem Lax485149.Reachability.stGraph := REACHᶜ

/-! ### The Horn program -/

/-- The block of the SO-Horn definition of UNREACH: one binary relation
variable, forced to contain the transitive closure of the edge relation. -/
def reachBlock : Lax904597.SecondOrder.SOBlock where
  ι := Unit
  arity := fun _ => 2

/-- The atom `T (xᵢ, xⱼ)` of the guessed relation. -/
def tAtom (i j : Fin 3) : Lax485149.SecondOrderAtoms.SOAtom reachBlock 3 :=
  ⟨(), ![i, j]⟩

/-- The guard `edge (xᵢ, xⱼ)`. Guards live over the ordered expansion of the
vocabulary, as `DescriptiveComplexity.SigmaSOHornDefinable` requires; this program
happens not to need the order. -/
noncomputable def edgeG (i j : Fin 3) :
    (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₂ Lax480241Proofs.Foreign.FirstOrder.Language.sgEdgeO (Term.var i) (Term.var j)

/-- The guard `source xᵢ`. -/
noncomputable def sourceG (i : Fin 3) :
    (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₁ Lax480241Proofs.Foreign.FirstOrder.Language.sgSourceO (Term.var i)

/-- The guard `target xᵢ`. -/
noncomputable def targetG (i : Fin 3) :
    (Lax485149.Reachability.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₁ Lax480241Proofs.Foreign.FirstOrder.Language.sgTargetO (Term.var i)

/-- Base rule: an edge is in `T`. -/
noncomputable def reachC1 :
    Lax535992.HornFragment.HornClause (Lax485149.Reachability.stGraph.sum Language.order) reachBlock 3 :=
  { guard := edgeG 0 1, body := [], head := some (tAtom 0 1) }

/-- Inductive rule: `T` is closed under appending an edge. -/
noncomputable def reachC2 :
    Lax535992.HornFragment.HornClause (Lax485149.Reachability.stGraph.sum Language.order) reachBlock 3 :=
  { guard := edgeG 1 2, body := [tAtom 0 1], head := some (tAtom 0 2) }

/-- Goal clause: no marked target is in `T` from a marked source. -/
noncomputable def reachC3 :
    Lax535992.HornFragment.HornClause (Lax485149.Reachability.stGraph.sum Language.order) reachBlock 3 :=
  { guard := sourceG 0 ⊓ targetG 1, body := [tAtom 0 1], head := none }

/-- Goal clause: no vertex is both a marked source and a marked target (the
empty path). -/
noncomputable def reachC4 :
    Lax535992.HornFragment.HornClause (Lax485149.Reachability.stGraph.sum Language.order) reachBlock 3 :=
  { guard := sourceG 0 ⊓ targetG 0, body := [], head := none }

/-- The Horn program defining UNREACH: two rules generating the transitive
closure of the edge relation into `T`, and two goal clauses forbidding a marked
target to be reached from a marked source. -/
noncomputable def reachProgram :
    Lax535992.HornFragment.HornProgram (Lax485149.Reachability.stGraph.sum Language.order) reachBlock 3 :=
  [reachC1, reachC2, reachC3, reachC4]

/-! ### Correctness of the program -/

section Program

variable {A : Type} [Lax485149.Reachability.stGraph.Structure A] [LinearOrder A]

/-- The relation guessed by an assignment of the block. -/
def TRel (ρ : reachBlock.Assignment A) (x y : A) : Prop := ρ () ![x, y]

omit [Lax485149.Reachability.stGraph.Structure A] [LinearOrder A] in
private theorem tAtom_holds (ρ : reachBlock.Assignment A) (v : Fin 3 → A) (i j : Fin 3) :
    (tAtom i j).Holds ρ v ↔ TRel ρ (v i) (v j) := by
  refine iff_of_eq (congrArg (ρ ()) (funext fun l => ?_))
  fin_cases l <;> rfl

private theorem realize_edgeG (v : Fin 3 → A) (i j : Fin 3) :
    (edgeG i j).Realize v ↔ Lax485149.Reachability.SGEdge (v i) (v j) := by
  rw [edgeG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

private theorem realize_sourceG (v : Fin 3 → A) (i : Fin 3) :
    (sourceG i).Realize v ↔ Lax485149.Reachability.SGSource (v i) := by
  rw [sourceG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

private theorem realize_targetG (v : Fin 3 → A) (i : Fin 3) :
    (targetG i).Realize v ↔ Lax485149.Reachability.SGTarget (v i) := by
  rw [targetG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

private theorem realize_srcTgtG (v : Fin 3 → A) (i j : Fin 3) :
    (sourceG i ⊓ targetG j).Realize v ↔ Lax485149.Reachability.SGSource (v i) ∧ Lax485149.Reachability.SGTarget (v j) := by
  rw [Formula.realize_inf, realize_sourceG, realize_targetG]

/-- What it means for an assignment to satisfy the program: the guessed
relation contains the transitive closure of the edge relation, and meets no
source-target pair. -/
theorem reachProgram_holds_iff (ρ : reachBlock.Assignment A) :
    reachProgram.Holds ρ ↔
      ((∀ x y : A, Lax485149.Reachability.SGEdge x y → TRel ρ x y) ∧
        (∀ x y z : A, TRel ρ x y → Lax485149.Reachability.SGEdge y z → TRel ρ x z)) ∧
      ((∀ x y : A, TRel ρ x y → Lax485149.Reachability.SGSource x → Lax485149.Reachability.SGTarget y → False) ∧
        ∀ x : A, Lax485149.Reachability.SGSource x → Lax485149.Reachability.SGTarget x → False) := by
  constructor
  · intro h
    refine ⟨⟨fun x y hxy => ?_, fun x y z hxy hyz => ?_⟩, fun x y hxy hx hy => ?_,
      fun x hx hy => ?_⟩
    · have hcl := h ![x, y, x] reachC1 (by simp [reachProgram])
      exact (tAtom_holds ρ _ 0 1).mp
        (hcl ⟨(realize_edgeG _ 0 1).mpr hxy, by simp [reachC1]⟩)
    · have hcl := h ![x, y, z] reachC2 (by simp [reachProgram])
      refine (tAtom_holds ρ _ 0 2).mp (hcl ⟨(realize_edgeG _ 1 2).mpr hyz, ?_⟩)
      intro a ha
      simp only [reachC2, List.mem_singleton] at ha
      subst ha
      exact (tAtom_holds ρ _ 0 1).mpr hxy
    · have hcl := h ![x, y, x] reachC3 (by simp [reachProgram])
      refine hcl ⟨(realize_srcTgtG _ 0 1).mpr ⟨hx, hy⟩, ?_⟩
      intro a ha
      simp only [reachC3, List.mem_singleton] at ha
      subst ha
      exact (tAtom_holds ρ _ 0 1).mpr hxy
    · have hcl := h ![x, x, x] reachC4 (by simp [reachProgram])
      exact hcl ⟨(realize_srcTgtG _ 0 0).mpr ⟨hx, hy⟩, by simp [reachC4]⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩ v c hc
    simp only [reachProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · rintro ⟨hg, -⟩
      exact (tAtom_holds ρ _ 0 1).mpr (h1 _ _ ((realize_edgeG _ 0 1).mp hg))
    · rintro ⟨hg, hb⟩
      refine (tAtom_holds ρ _ 0 2).mpr (h2 _ _ _ ?_ ((realize_edgeG _ 1 2).mp hg))
      exact (tAtom_holds ρ _ 0 1).mp (hb _ (by simp [reachC2]))
    · rintro ⟨hg, hb⟩
      obtain ⟨hs, ht⟩ := (realize_srcTgtG _ 0 1).mp hg
      exact h3 _ _ ((tAtom_holds ρ _ 0 1).mp (hb _ (by simp [reachC3]))) hs ht
    · rintro ⟨hg, -⟩
      obtain ⟨hs, ht⟩ := (realize_srcTgtG _ 0 0).mp hg
      exact h4 _ hs ht

/-- The transitive closure of the edge relation, as an assignment of the
block: the least model of the two rules of the program. -/
def transClosureAssign : reachBlock.Assignment A :=
  fun _ w => Relation.TransGen Lax485149.Reachability.SGEdge (w ⟨0, Nat.zero_lt_two⟩) (w ⟨1, Nat.one_lt_two⟩)

omit [LinearOrder A] in
@[simp]
theorem tRel_transClosureAssign (x y : A) :
    TRel (transClosureAssign (A := A)) x y ↔ Relation.TransGen Lax485149.Reachability.SGEdge x y :=
  Iff.rfl

omit [LinearOrder A] in
/-- Any model of the two rules of the program contains the transitive closure
of the edge relation. -/
theorem transGen_tRel {ρ : reachBlock.Assignment A}
    (h1 : ∀ x y : A, Lax485149.Reachability.SGEdge x y → TRel ρ x y)
    (h2 : ∀ x y z : A, TRel ρ x y → Lax485149.Reachability.SGEdge y z → TRel ρ x z) {a b : A}
    (h : Relation.TransGen Lax485149.Reachability.SGEdge a b) : TRel ρ a b := by
  induction h with
  | single hab => exact h1 _ _ hab
  | tail _ hbc ih => exact h2 _ _ _ ih hbc

end Program

/-! ### UNREACH is SO-Horn definable -/

/-- **UNREACH is SO-Horn definable**: the guessed relation is forced to
contain the transitive closure of the edge relation, and the goal clauses
forbid it to link a marked source to a marked target. The witness in the
nontrivial direction *is* the transitive closure – the least model of the two
rules. -/
theorem unreach_sigmaSOHornDefinable : Lax535992.HornFragment.SigmaSOHornDefinable UNREACH := by
  refine ⟨reachBlock, 3, reachProgram, ?_⟩
  intro A _ _ _ _
  constructor
  · intro h
    refine ⟨transClosureAssign, (reachProgram_holds_iff _).mpr
      ⟨⟨fun x y hxy => Relation.TransGen.single hxy,
        fun x y z hxy hyz => Relation.TransGen.tail hxy hyz⟩, fun x y hxy hx hy => ?_,
        fun x hx hy => ?_⟩⟩
    · exact h ⟨x, y, hx, hy, hxy.to_reflTransGen⟩
    · exact h ⟨x, x, hx, hy, Relation.ReflTransGen.refl⟩
  · rintro ⟨ρ, hρ⟩ ⟨s, t, hs, ht, hpath⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (reachProgram_holds_iff ρ).mp hρ
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hpath with rfl | htg
    · exact h4 _ hs ht
    · exact h3 _ _ (transGen_tRel h1 h2 htg) hs ht

/-- **REACH is in PTIME** after all: what the fragment cannot say head-on it
can say through the equivalence with FO(LFP)
(`DescriptiveComplexity.SigmaSOHornDefinable.compl`). -/
theorem reach_mem_PTIME : REACH ∈ PTIME := by
  have h := unreach_sigmaSOHornDefinable.compl
  rwa [UNREACH, DecisionProblem.compl_compl] at h

/-! ### UNREACH is SO-Krom definable, hence in NL

The Krom fragment needs no transitive closure: it guesses the set of vertices
from which a marked target is reachable, closes it under *predecessors* – a
two-literal implication – and forbids a marked source to belong to it. -/

section KromProgram

end KromProgram

/-! ### REACH is FO(TC) definable

The canonical example of `DescriptiveComplexity.TCDefinable`, and the one the logic is
shaped after: REACH *is* a transitive closure, at arity one, of the edge
relation between the marked sources and the marked targets. Note the contrast
with the two clausal fragments above, which define the *complement* head-on:
here it is reachability itself that is stated, which is why closing FO(TC)
under complement (Immerman–Szelepcsényi) is what `REACH ∈ NL` waits on. -/

section TCProgram

end TCProgram

end Lax480241Proofs.DescriptiveComplexity


