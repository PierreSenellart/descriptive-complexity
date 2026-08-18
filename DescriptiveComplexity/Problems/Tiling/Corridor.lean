/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Tiling.Defs

/-!
# Tiling a corridor: the same tiles, one dimension unbounded

The corridor is `DescriptiveComplexity.TILING` with the square replaced by a
strip ([Fürer 1983][furer1983domino] for the two complexities the pair
carries): the columns are still the positions of the instance, but the rows are
*numbers*, and the question is whether the description can be continued upward
until an accepting tile appears.

Nothing about tiles changes – the vocabulary, the two compatibilities, the
bottom row, the edge marks and the accepting mark are
`DescriptiveComplexity.TileData` as before – so a tile system is read off an
instance exactly once and asked two different questions. What changes is the
resource: a square of the instance's own side is a polynomial object and the
tiling of it sits in NP, while a corridor is a *walk* whose states are the rows,
so it sits in PSPACE and, read over an exponential expansion, in EXPSPACE.

## Why the height is a number and the width is not

A row is an assignment of tiles to positions – an object of the same size as the
instance – and the corridor asks for a sequence of them, one above the other. A
walk of that shape is exactly what `DescriptiveComplexity.SOTCSpec` describes,
which is why the height is a plain `ℕ` here and not a coordinate of the
instance: nothing in the problem bounds it.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TileData

variable {A : Type} (T : TileData A)

/-- **A tiling of the corridor up to a given height**: every cell of the strip
carries a tile, the bottom row is one the description allows, the two edge
columns carry tiles allowed there, neighbors in a row and rows one above the
other are compatible, and the top row carries an accepting tile.

The height is where a corridor differs from
`DescriptiveComplexity.TileData.IsTiling`: nothing in the instance bounds it,
and the tiles above the accepting row are not asked about at all. -/
def IsCorridor (h : ℕ) (τ : ℕ → A → A) : Prop :=
  (∀ k x, k ≤ h → T.Posn x → T.Tile (τ k x)) ∧
    (∀ x, T.Posn x →
      ((MinPos T.Le T.Posn x → T.Start (τ 0 x)) ∧
        (¬MinPos T.Le T.Posn x → T.FirstTile x (τ 0 x)))) ∧
    (∀ k x, k ≤ h → MinPos T.Le T.Posn x → T.EdgeL (τ k x)) ∧
    (∀ k x, k ≤ h → MaxPos T.Le T.Posn x → T.EdgeR (τ k x)) ∧
    (∀ k x x', k ≤ h → SuccPos T.Le T.Posn x x' → T.Horiz (τ k x) (τ k x')) ∧
    (∀ k x, k < h → T.Posn x → T.Vert (τ k x) (τ (k + 1) x)) ∧
    ∃ x, T.Posn x ∧ T.Acc (τ h x)

/-- **The corridor can be tiled**: some assignment of tiles to its cells is a
tiling of it, of some height. -/
def CorridorTileable : Prop := ∃ (h : ℕ) (τ : ℕ → A → A), T.IsCorridor h τ

/-! ### Transport along a bijection -/

section Transport

variable {B : Type} (u : A ≃ B) (S : TileData B)
variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))
variable (htile : ∀ a, T.Tile a ↔ S.Tile (u a)) (hacc : ∀ a, T.Acc a ↔ S.Acc (u a))
variable (hhoriz : ∀ a a', T.Horiz a a' ↔ S.Horiz (u a) (u a'))
variable (hvert : ∀ a a', T.Vert a a' ↔ S.Vert (u a) (u a'))
variable (hfirst : ∀ a a', T.First a a' ↔ S.First (u a) (u a'))
variable (hbase : ∀ a, T.Base a ↔ S.Base (u a))
variable (hstart : ∀ a, T.Start a ↔ S.Start (u a))
variable (hedgeL : ∀ a, T.EdgeL a ↔ S.EdgeL (u a)) (hedgeR : ∀ a, T.EdgeR a ↔ S.EdgeR (u a))

include hposn hle htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR

/-- **A bijection matching the two systems carries a corridor across.** -/
theorem isCorridor_map {h : ℕ} {τ : ℕ → A → A} (hcor : T.IsCorridor h τ) :
    S.IsCorridor h fun k x => u (τ k (u.symm x)) := by
  obtain ⟨htiles, hfst, hel, her, hhor, hver, x, hx, hax⟩ := hcor
  have hpt : ∀ p : B, ∃ a, p = u a := fun p => ⟨u.symm p, (u.apply_symm_apply p).symm⟩
  refine ⟨fun k p hk hp => ?_, fun p hp => ?_, fun k p hk hp => ?_, fun k p hk hp => ?_,
    fun k p p' hk hp => ?_, fun k p hk hp => ?_, u x, (hposn x).mp hx, ?_⟩
  · obtain ⟨a, rfl⟩ := hpt p
    simp only [u.symm_apply_apply]
    exact (htile _).mp (htiles k a hk ((hposn a).mpr hp))
  · obtain ⟨a, rfl⟩ := hpt p
    simp only [u.symm_apply_apply]
    obtain ⟨hst, hfr⟩ := hfst a ((hposn a).mpr hp)
    refine ⟨fun hmin => (hstart _).mp (hst ((minPos_map T u S hposn hle a).mpr hmin)), ?_⟩
    intro hmin
    rcases hfr (fun hc => hmin ((minPos_map T u S hposn hle a).mp hc)) with hf | ⟨hno, hb⟩
    · exact Or.inl ((hfirst _ _).mp hf)
    · refine Or.inr ⟨fun v hv => ?_, (hbase _).mp hb⟩
      obtain ⟨c, rfl⟩ := hpt v
      exact hno c ((hfirst a c).mpr hv)
  · obtain ⟨a, rfl⟩ := hpt p
    simp only [u.symm_apply_apply]
    exact (hedgeL _).mp (hel k a hk ((minPos_map T u S hposn hle a).mpr hp))
  · obtain ⟨a, rfl⟩ := hpt p
    simp only [u.symm_apply_apply]
    exact (hedgeR _).mp (her k a hk ((maxPos_map T u S hposn hle a).mpr hp))
  · obtain ⟨a, rfl⟩ := hpt p
    obtain ⟨a', rfl⟩ := hpt p'
    simp only [u.symm_apply_apply]
    exact (hhoriz _ _).mp (hhor k a a' hk ((succPos_map T u S hposn hle a a').mpr hp))
  · obtain ⟨a, rfl⟩ := hpt p
    simp only [u.symm_apply_apply]
    exact (hvert _ _).mp (hver k a hk ((hposn a).mpr hp))
  · simp only [u.symm_apply_apply]
    exact (hacc _).mp hax

/-- **And with it, the corridor's tileability.** -/
theorem corridorTileable_map (h : T.CorridorTileable) : S.CorridorTileable :=
  ⟨h.choose, _, isCorridor_map T u S hposn hle htile hacc hhoriz hvert hfirst hbase hstart
    hedgeL hedgeR h.choose_spec.choose_spec⟩

end Transport

end TileData

/-! ### The problem -/

section Problem

variable {A B : Type} [Language.tiling.Structure A] [Language.tiling.Structure B]

/-- **An isomorphism carries a corridor across.** -/
theorem isCorridor_map (e : A ≃[Language.tiling] B) {h : ℕ} {τ : ℕ → A → A}
    (hcor : (tileData A).IsCorridor h τ) :
    (tileData B).IsCorridor h fun k u => e (τ k (e.symm u)) :=
  TileData.isCorridor_map _ e.toEquiv _ (tlPosn_map e) (tlLe_map e) (tlTile_map e)
    (tlAcc_map e) (tlHoriz_map e) (tlVert_map e) (tlFirst_map e) (tlBase_map e)
    (tlStart_map e) (tlEdgeL_map e) (tlEdgeR_map e) hcor

/-- **Tileability of the corridor is an isomorphism invariant.** -/
theorem corridorTileable_congr (e : A ≃[Language.tiling] B) :
    (tileData A).CorridorTileable ↔ (tileData B).CorridorTileable :=
  ⟨fun ⟨_, _, h⟩ => ⟨_, _, isCorridor_map e h⟩, fun ⟨_, _, h⟩ => ⟨_, _, isCorridor_map e.symm h⟩⟩

/-- **Tiling a corridor.** Can the strip whose width is the positions of the
instance be tiled upward, from the bottom row the description allows until an
accepting tile appears? The well-formedness promises are folded into the
yes-instances, exactly as for `DescriptiveComplexity.TILING`. -/
def CORRIDOR : DecisionProblem Language.tiling where
  Holds := fun A _ => (tileData A).WellFormed ∧ (tileData A).CorridorTileable
  iso_invariant := fun {_ _} _ _ e =>
    and_congr (wellFormed_congr e) (corridorTileable_congr e)

end Problem

end DescriptiveComplexity
