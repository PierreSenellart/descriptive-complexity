/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Steiner.Counting
import DescriptiveComplexity.Problems.CliqueFamily.CountingReductions

/-!
# #Steiner Tree is parsimoniously `#P`-complete

`DescriptiveComplexity.sharpSteinerTree_sharpP_parsimoniousComplete`, by the reduction
from Vertex Cover of `DescriptiveComplexity.Problems.Steiner.Reductions`, which is
parsimonious as it stands
(`DescriptiveComplexity.sharpVertexCover_ordered_parsimonious_sharpSteinerTree`).

In the incidence structure of a graph the terminals are the edges and the
root, and the only other points with a neighbour are the vertices
(`DescriptiveComplexity.steiner_nonterminal_shape`). So a connected set containing the
terminals is the terminals together with a set of vertices, which covers every
edge, and any cover will do: the Steiner sets using a given number of
non-terminals are the vertex covers of that size, bijectively. A superset of a
solution is a solution on both sides here, and the two paddings are the same
vertices.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Shape

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]

/-- A point of the incidence structure with a neighbour is a terminal or a
vertex. -/
theorem steiner_nonterminal_shape {p q : steinerInterp.Map A}
    (h : STAdj p q ∨ STAdj q p) (hp : ¬STTerminal p) : ∃ v, p = vPt v := by
  rcases p with ⟨t, w⟩
  rcases q with ⟨t', w'⟩
  rcases h with h | h
  · rcases (steiner_adj_iff t t' w w').mp h with ⟨rfl, -, hdiag, -, -⟩ | ⟨rfl, -, hdiag, hmin, -⟩
    · exact ⟨w 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [vPt, hdiag]⟩⟩
    · exact absurd ((steiner_terminal_iff .root w).mpr (Or.inr ⟨rfl, hdiag, hmin⟩)) hp
  · rcases (steiner_adj_iff t' t w' w).mp h with ⟨-, rfl, -, hedge, -⟩ | ⟨-, rfl, -, -, hdiag⟩
    · exact absurd ((steiner_terminal_iff .edge w).mpr (Or.inl ⟨rfl, hedge.1, hedge.2⟩)) hp
    · exact ⟨w 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [vPt, hdiag]⟩⟩

/-- The non-terminals of a connected set containing the terminals are
vertices. -/
theorem steiner_mem_shape {m : A} (hm : ∀ a : A, m ≤ a) {S : steinerInterp.Map A → Prop}
    (hterms : ∀ p, STTerminal p → S p) (hconn : ConnectedOn STAdj S)
    {p : steinerInterp.Map A} (hp : S p) (hnt : ¬STTerminal p) : ∃ v, p = vPt v := by
  have hroot : STTerminal (rPt m (A := A)) := (steiner_terminal_r m).mpr hm
  rcases Relation.ReflTransGen.cases_head (hconn p (rPt m) hp (hterms _ hroot)) with
    heq | ⟨q, hlink, -⟩
  · exact absurd (heq ▸ hroot) hnt
  · exact steiner_nonterminal_shape hlink.2.2 hnt

variable (A) [Finite A] [Nonempty A]

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpSteinerTree_map :
    SharpSteinerTree (steinerInterp.Map A) = SharpVertexCover A := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  have hM : Finite (steinerInterp.Map A) := steinerInterp.map_finite A
  have hmarked : {p : steinerInterp.Map A | STMarked p}.ncard = {v : A | MGMarked v}.ncard :=
    ncard_vPt_eq MGMarked _ (fun _ hp => steiner_marked_shape hp) fun v => steiner_marked_v v
  have hto : ∀ C : A → Prop, CoverOfSize A C →
      SteinerOfSize (steinerInterp.Map A) fun p => STTerminal p ∨ ∃ v, C v ∧ p = vPt v := by
    intro C hC
    refine ⟨hM, fun x hx => Or.inl hx, steiner_connectedOn_of_cover hm hC.2.1, ?_⟩
    -- the non-terminals of the set of a cover are the cover
    have hne : {p : steinerInterp.Map A |
        (STTerminal p ∨ ∃ v, C v ∧ p = vPt v) ∧ ¬STTerminal p}.ncard
          = {v : A | C v}.ncard := by
      refine ncard_vPt_eq C _ (fun p hp => ?_) fun v => ?_
      · rcases hp.1 with h | ⟨v, -, rfl⟩
        · exact absurd h hp.2
        · exact ⟨v, rfl⟩
      · exact ⟨fun h => by
          rcases h.1 with h' | ⟨v', hv', hvv⟩
          · exact absurd h' (steiner_terminal_v v)
          · exact vPt_injective hvv.symm ▸ hv',
        fun h => ⟨Or.inr ⟨v, h, rfl⟩, steiner_terminal_v v⟩⟩
    exact hne.trans (hC.2.2.trans hmarked.symm)
  have hfrom : ∀ S : steinerInterp.Map A → Prop, SteinerOfSize (steinerInterp.Map A) S →
      CoverOfSize A fun v => S (vPt v) := by
    intro S hS
    refine ⟨‹Finite A›, steiner_cover_of_connected hm hS.2.1 hS.2.2.1, ?_⟩
    -- the vertices of a Steiner set are its non-terminals
    have hne : {p : steinerInterp.Map A | S p ∧ ¬STTerminal p}.ncard =
        {v : A | S (vPt v)}.ncard :=
      ncard_vPt_eq (fun v => S (vPt v)) _
        (fun p hp => steiner_mem_shape hm hS.2.1 hS.2.2.1 hp.1 hp.2)
        fun v => ⟨fun h => h.1, fun h => ⟨h, steiner_terminal_v v⟩⟩
    exact hne.symm.trans (hS.2.2.2.trans hmarked)
  rw [sharpSteinerTree_apply, sharpVertexCover_apply]
  exact (Nat.card_congr
    { toFun := fun C => ⟨fun p => STTerminal p ∨ ∃ v, C.1 v ∧ p = vPt v, hto C.1 C.2⟩
      invFun := fun S => ⟨fun v => S.1 (vPt v), hfrom S.1 S.2⟩
      left_inv := fun C => Subtype.ext (funext fun v => propext
        ⟨fun h => by
          rcases h with h | ⟨v', hv', hvv⟩
          · exact absurd h (steiner_terminal_v v)
          · exact vPt_injective hvv.symm ▸ hv', fun h => Or.inr ⟨v, h, rfl⟩⟩)
      right_inv := fun S => Subtype.ext (funext fun p => propext
        ⟨fun h => by
          rcases h with h | ⟨v, hv, rfl⟩
          exacts [S.2.2.1 p h, hv], fun h => by
          by_cases ht : STTerminal p
          · exact Or.inl ht
          · obtain ⟨v, rfl⟩ := steiner_mem_shape hm S.2.2.1 S.2.2.2.1 h ht
            exact Or.inr ⟨v, h, rfl⟩⟩) }).symm

end Shape

/-- **#Vertex Cover reduces parsimoniously to #Steiner Tree**, by the incidence
structure of the graph with a root. -/
noncomputable def sharpVertexCover_ordered_parsimonious_sharpSteinerTree :
    SharpVertexCover ≤ᵖ[≤] SharpSteinerTree where
  Tag := SteinerTag
  dim := 2
  toInterpretation := steinerInterp
  correct A _ _ _ _ := (sharpSteinerTree_map A).symm

/-- #Steiner Tree is parsimoniously `#P`-hard. -/
theorem sharpSteinerTree_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpSteinerTree :=
  SharpP.parsimoniousHard_of_orderedParsimonious
    sharpVertexCover_ordered_parsimonious_sharpSteinerTree
    sharpVertexCover_sharpP_parsimoniousHard

/-- **#Steiner Tree is parsimoniously `#P`-complete**, counting the Steiner sets
using exactly the threshold number of non-terminals. -/
theorem sharpSteinerTree_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpSteinerTree :=
  ⟨sharpSteinerTree_mem_sharpP, sharpSteinerTree_sharpP_parsimoniousHard⟩

end DescriptiveComplexity
