/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameSO
import DescriptiveComplexity.Exponential.Peel
import DescriptiveComplexity.Problems.Game

/-!
# The nodes of an interpreted AND/OR graph, as states of a game

The road from `DescriptiveComplexity.EXPTIME` to `SO-GAME` reads a `PTIME` inner
problem as the **AND/OR graph an interpretation draws on the expanded
universe**, and plays that graph. A node of the graph is a
tagged tuple of points, so a node is a *state* of a second-order game — that
correspondence is what this file builds.

Two things are settled here.

**The interpretation may be taken non-relativized.** `GAME` is PTIME-hard under
ordinary ordered reductions (`DescriptiveComplexity.game_hard_ordered`): the
composite of the Horn discharge with the unit-propagation game is a plain
`≤ᶠᵒ[≤]`, and `DescriptiveComplexity.game_PTIME_hard` only widens it to `≤ʳᶠᵒ[≤]`
at the very end. That matters here: a *definable domain* would have to be
checked by a formula over the expansion, i.e. by a whole sub-game, whereas a
non-relativized interpretation leaves the nodes guarded by nothing but “each
slot is a point”.

**A node is a guarded assignment.** The state block is
`DescriptiveComplexity.ExpExpansion.nodeBlock`: the `d` rounds of
`DescriptiveComplexity.repMerged`, each holding one point of the expanded
universe (`DescriptiveComplexity.ExpExpansion.pointBlock`), extended by tag bits
for the interpretation's tag. `DescriptiveComplexity.ExpExpansion.nodeGuardF`
says exactly that a guessed state is such a tuple
(`DescriptiveComplexity.ExpExpansion.realize_nodeGuardF`), so quantifying over
nodes of the graph is quantifying over guarded states
(`DescriptiveComplexity.ExpExpansion.exists_node_iff`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### GAME is PTIME-hard under ordinary ordered reductions -/

/-- **`GAME` is PTIME-hard without a definable domain**: the reduction of
`DescriptiveComplexity.game_PTIME_hard` is an ordinary ordered one, and only
becomes relativized when `DescriptiveComplexity.ComplexityClass.Hard` asks for
it. Playing the graph an interpretation draws needs this form, since a definable
domain would itself have to be decided by a sub-game. -/
theorem game_hard_ordered {L : Language.{0, 0}} [L.IsRelational] (Q : DecisionProblem L)
    (hQ : SigmaSOHornDefinable Q) : Nonempty (Q ≤ᶠᵒ[≤] GAME) := by
  obtain ⟨f⟩ := hornSat_hard_of_sigmaSOHornDefinable Qᶜ hQ.compl
  exact ⟨(f.compl.congrSource fun A _ _ => not_not).trans
    hornSatCompl_ordered_fo_reduction_game⟩

/-! ### Splitting a merged round assignment -/

/-- **Every assignment of the merged rounds is one assignment per round.** -/
theorem repBlockAssign_split (B : SOBlock) (A : Type) :
    ∀ (k : ℕ) (ν : (repMerged B k).Assignment A),
      ∃ ρs : Fin k → B.Assignment A, ν = repBlockAssign B A k ρs := by
  intro k
  induction k with
  | zero =>
    intro ν
    refine ⟨fun i => i.elim0, ?_⟩
    funext i
    exact i.elim
  | succ k ih =>
    intro ν
    obtain ⟨ρs, hρs⟩ := ih fun i => ν (Sum.inr i)
    refine ⟨Fin.cons (fun i => ν (Sum.inl i)) ρs, ?_⟩
    have hs : (fun i : Fin k =>
        (Fin.cons (fun i => ν (Sum.inl i)) ρs : Fin (k + 1) → B.Assignment A) i.succ) = ρs :=
      funext fun i => Fin.cons_succ _ _ i
    have hcons : repBlockAssign B A (k + 1) (Fin.cons (fun i => ν (Sum.inl i)) ρs) =
        consAssign (fun i => ν (Sum.inl i)) (repBlockAssign B A k ρs) := by
      rw [repBlockAssign, hs]
      rfl
    rw [hcons, ← hρs]
    exact (consAssign_split ν).symm

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : ExpExpansion L) (T : Type) [Finite T] (d : ℕ)

/-! ### The block a node is guessed in -/

/-- **The block of a node** of an AND/OR graph interpreted over the expansion:
`d` rounds, each holding a point, and tag bits naming the interpretation's
tag. -/
abbrev nodeBlock : SOBlock := (repMerged X.pointBlock d).withTag T

variable {X T d} {A : Type} [L.Structure A] [LinearOrder A]

/-- The state carrying a node: its tag in the tag bits, its points in the
rounds. -/
def nodeAssign (n : T × (Fin d → X.Map A)) : (nodeBlock X T d).Assignment A :=
  SOBlock.tagAssign n.1 (repBlockAssign X.pointBlock A d fun i => pointAssign (n.2 i))

variable (X T d)

/-- **The guard saying a guessed state is a node**: its tag bits name a tag and
each of its rounds is a point. -/
noncomputable def nodeGuardF : ((L.sum Language.order).sum (nodeBlock X T d).lang).Sentence :=
  SOBlock.tagGuardF (repMerged X.pointBlock d) T ⊓
    listInf ((List.finRange d).map fun i =>
      (withTagLHom L (repMerged X.pointBlock d) T).onSentence
        ((roundOneLHom i X).onSentence X.pointGuardF))

variable {X T d}

/-- **The guard is exactly “this is a node”.** -/
theorem realize_nodeGuardF (σ : (nodeBlock X T d).Assignment A) :
    (@Sentence.Realize _ A
        ((nodeBlock X T d).structure₁ (L := L.sum Language.order) σ) (nodeGuardF X T d) ↔
      ∃ n : T × (Fin d → X.Map A), σ = nodeAssign n) := by
  letI := (nodeBlock X T d).structure₁ (L := L.sum Language.order) σ
  rw [nodeGuardF, Sentence.Realize, Formula.realize_inf, realize_listInf]
  constructor
  · rintro ⟨hguard, hrounds⟩
    obtain ⟨t, ν, rfl⟩ := (SOBlock.realize_tagGuardF (L := L.sum Language.order) σ).mp hguard
    obtain ⟨ρs, rfl⟩ := repBlockAssign_split X.pointBlock A d ν
    have hpt : ∀ i : Fin d, IsPointAssign (X := X) (ρs i) := by
      intro i
      have h : @Sentence.Realize _ A
          ((nodeBlock X T d).structure₁ (L := L.sum Language.order)
            (SOBlock.tagAssign t (repBlockAssign X.pointBlock A d ρs)))
          ((withTagLHom L (repMerged X.pointBlock d) T).onSentence
            ((roundOneLHom i X).onSentence X.pointGuardF)) :=
        hrounds _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
      refine (realize_pointGuardF (ρs i)).mp ?_
      refine (realize_roundOneLHom i X ρs X.pointGuardF).mp ?_
      exact (realize_withTagLHom _ _).mp h
    refine ⟨(t, fun i => ?_), ?_⟩
    · exact pt (Classical.choose (hpt i)) (Classical.choose (Classical.choose_spec (hpt i)))
        (Classical.choose_spec (Classical.choose_spec (hpt i))).2
    · refine congrArg (SOBlock.tagAssign t) (congrArg (repBlockAssign X.pointBlock A d) ?_)
      funext i
      exact (Classical.choose_spec (Classical.choose_spec (hpt i))).1
  · rintro ⟨⟨t, pts⟩, rfl⟩
    refine ⟨(SOBlock.realize_tagGuardF (L := L.sum Language.order) _).mpr ⟨t, _, rfl⟩,
      fun ψ hψ => ?_⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    refine (realize_withTagLHom _ _).mpr ?_
    refine (realize_roundOneLHom i X (fun j => pointAssign (pts j)) X.pointGuardF).mpr ?_
    exact (realize_pointGuardF _).mpr (isPointAssign_pointAssign (pts i))

/-- **Quantifying over nodes is quantifying over guarded states.** -/
theorem exists_node_iff (P : (nodeBlock X T d).Assignment A → Prop) :
    ((∃ σ : (nodeBlock X T d).Assignment A,
        (@Sentence.Realize _ A
          ((nodeBlock X T d).structure₁ (L := L.sum Language.order) σ) (nodeGuardF X T d)) ∧
        P σ) ↔
      ∃ n : T × (Fin d → X.Map A), P (nodeAssign n)) := by
  constructor
  · rintro ⟨σ, hg, hP⟩
    obtain ⟨n, rfl⟩ := (realize_nodeGuardF σ).mp hg
    exact ⟨n, hP⟩
  · rintro ⟨n, hP⟩
    exact ⟨nodeAssign n, (realize_nodeGuardF _).mpr ⟨n, rfl⟩, hP⟩

end ExpExpansion

end DescriptiveComplexity
