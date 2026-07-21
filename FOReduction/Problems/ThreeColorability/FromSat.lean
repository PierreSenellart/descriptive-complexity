/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.Problems.ThreeColorability.SatGadget
import FOReduction.Problems.ThreeColorability.Defs
import FOReduction.OccurrenceFormulas

/-!
# SAT reduces to 3-colorability by an ordered FO reduction

The reverse direction of `FOReduction.ThreeColToSat`: the gadget graph of
`FOReduction.SatGadget` is first-order definable over the *ordered* expansion
`Language.sat.sum Language.order` of the language of CNF instances, giving an
ordered first-order reduction from SAT to 3-colorability —
`FirstOrder.sat_ordered_fo_reduction_threeCol : OrderedFOReduction SAT ThreeCol`.

The order is genuinely needed: the OR-gadget chain of a clause is threaded
along the order of its literal occurrences ("first occurrence", "immediate
predecessor" and "last occurrence" are FO(≤)-definable, but not FO-definable).
This is the standard situation in descriptive complexity, where reductions
operate on ordered finite structures.

The file assembles the edge formulas `edgeF` mirroring `SatToCol.Core` from
the shared occurrence formula builders of `FOReduction.OccurrenceFormulas`
(`occF`, `minOccF`, `succOccF`, …), and packages everything into the
interpretation `SatToCol.satToCol` and the final reduction.
-/

namespace FirstOrder

namespace SatToCol

open Language Structure SatOcc

/-! ### The edge formulas and the interpretation -/

/-- One direction of the edge formulas of the gadget graph, mirroring
`SatToCol.Core`: the free variable `(i, j)` is the `j`-th component of the
`i`-th vertex. -/
noncomputable def edgeF : SatTag → SatTag → satOrd.Formula (Fin 2 × Fin 2)
  | .palT, .palF => ⊤
  | .palF, .palB => ⊤
  | .palB, .palT => ⊤
  | .lit s, .lit t =>
      if t = !s then eqF (0, 0) (0, 1) ⊓ eqF (1, 0) (1, 1) ⊓ eqF (0, 0) (1, 0) else ⊥
  | .lit _, .palB => eqF (0, 0) (0, 1)
  | .lit s, .palF => eqF (0, 0) (0, 1) ⊓ unitLitF s (0, 0)
  | .gv s, .lit t =>
      if t = s then eqF (1, 0) (1, 1) ⊓ eqF (1, 0) (0, 1) ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | .gu s, .lit t =>
      eqF (1, 0) (1, 1) ⊓ chainedF s (0, 0) (0, 1) ⊓ minOccF t (0, 0) (1, 0) ⊓
        succOccF t s (0, 0) (1, 0) (0, 1)
  | .gu s, .gv t =>
      if t = s then eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1) ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | .gu s, .go t =>
      (if t = s then eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1) ⊓ chainedF s (0, 0) (0, 1) else ⊥) ⊔
        (eqF (0, 0) (1, 0) ⊓ chainedF s (0, 0) (0, 1) ⊓ chainedF t (1, 0) (1, 1) ⊓
          succOccF t s (0, 0) (1, 1) (0, 1))
  | .gv s, .go t =>
      if t = s then eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1) ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | .go s, .palF => chainedF s (0, 0) (0, 1) ⊓ maxOccF s (0, 0) (0, 1)
  | .go s, .palB => chainedF s (0, 0) (0, 1)
  | .spoil, .palT => eqF (0, 0) (0, 1) ⊓ emptyClF (0, 0)
  | .spoil, .palF => eqF (0, 0) (0, 1) ⊓ emptyClF (0, 0)
  | .spoil, .palB => eqF (0, 0) (0, 1) ⊓ emptyClF (0, 0)
  | _, _ => ⊥

/-- Variable swap exchanging the two vertex positions. -/
def swapVar : Fin 2 × Fin 2 → Fin 2 × Fin 2 := fun p => (![1, 0] p.1, p.2)

/-- The interpretation producing, from an ordered CNF structure, its
3-colorability gadget graph. -/
noncomputable def satToCol : FOInterpretation satOrd Language.graph SatTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t => edgeF (t 0) (t 1) ⊔ (edgeF (t 1) (t 0)).relabel swapVar

section Characterization

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

theorem realize_edgeF {t₁ t₂ : SatTag} {v : Fin 2 × Fin 2 → A} :
    (edgeF t₁ t₂).Realize v ↔
      Core t₁ (v (0, 0)) (v (0, 1)) t₂ (v (1, 0)) (v (1, 1)) := by
  cases t₁ <;> cases t₂
  case lit.lit s t =>
    rcases eq_or_ne t (!s) with rfl | h
    · simp [edgeF, Core, and_assoc]
    · simp [edgeF, Core, h]
  case gv.lit s t =>
    rcases eq_or_ne t s with rfl | h
    · simp [edgeF, Core, and_assoc]
    · simp [edgeF, Core, h]
  case gu.gv s t =>
    rcases eq_or_ne t s with rfl | h
    · simp [edgeF, Core, and_assoc]
    · simp [edgeF, Core, h]
  case gu.go s t =>
    rcases eq_or_ne t s with rfl | h
    · simp [edgeF, Core, and_assoc]
    · simp [edgeF, Core, h, and_assoc]
  case gv.go s t =>
    rcases eq_or_ne t s with rfl | h
    · simp [edgeF, Core, and_assoc]
    · simp [edgeF, Core, h]
  all_goals simp [edgeF, Core, and_assoc]

/-- Characterization of the interpreted adjacency relation: it is the
symmetrization of `Core`. -/
theorem relMap_adj_iff {t₁ t₂ : SatTag} {w₁ w₂ : Fin 2 → A} :
    RelMap (M := satToCol.Map A) adj ![(t₁, w₁), (t₂, w₂)] ↔
      Core t₁ (w₁ 0) (w₁ 1) t₂ (w₂ 0) (w₂ 1) ∨
        Core t₂ (w₂ 0) (w₂ 1) t₁ (w₁ 0) (w₁ 1) := by
  rw [FOInterpretation.relMap_map]
  simp only [satToCol, Formula.realize_sup, Formula.realize_relabel]
  rw [realize_edgeF, realize_edgeF]
  simp [swapVar]

end Characterization

/-! ### Main theorem -/

variable (A : Type) [Language.sat.Structure A] [LinearOrder A]

/-- Correctness of the reduction: an ordered CNF structure is satisfiable iff
its interpreted gadget graph is 3-colorable. -/
theorem satisfiable_iff_threeColorable [Finite A] :
    Satisfiable A ↔ ThreeColorable (satToCol.Map A) := by
  rw [satisfiable_iff_gadColoring A]
  unfold ThreeColorable
  constructor
  · rintro ⟨col, hcol⟩
    refine ⟨fun p => col p.1 (p.2 0) (p.2 1), ?_⟩
    rintro ⟨t₁, w₁⟩ ⟨t₂, w₂⟩ hadj
    rw [relMap_adj_iff] at hadj
    rcases hadj with h | h
    · exact hcol _ _ _ _ _ _ h
    · exact fun heq => hcol _ _ _ _ _ _ h heq.symm
  · rintro ⟨col, hcol⟩
    refine ⟨fun t a b => col (t, ![a, b]), fun t₁ a₁ b₁ t₂ a₂ b₂ h => ?_⟩
    refine hcol (t₁, ![a₁, b₁]) (t₂, ![a₂, b₂]) ?_
    rw [relMap_adj_iff]
    left
    simpa using h

end SatToCol

open SatToCol in
/-- **SAT FO-reduces to 3-colorability on ordered structures.** The reverse
`fo_reduction` theorem: the first-order interpretation `SatToCol.satToCol`,
over the ordered expansion of the language of CNF instances, maps a finite
CNF structure to a 3-colorable graph iff it is satisfiable. Together with
`threeCol_fo_reduction_sat`, SAT and 3-colorability are FO-interreducible. -/
noncomputable def sat_ordered_fo_reduction_threeCol : SAT ≤ᶠᵒ[≤] ThreeCol where
  Tag := SatTag
  dim := 2
  toInterpretation := satToCol
  correct A _ _ _ := satisfiable_iff_threeColorable A

end FirstOrder
