/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Tiling
import Lax822549Proofs.DescriptiveComplexity.Problems.Tiling.Membership
import Lax822549Proofs.DescriptiveComplexity.Exponential.Classes
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549.WideTilings
end Lax822549.WideTilings

namespace FirstOrder.Language
export Lax822549.WideTilings (wtAcc wtBase wtDig wtEdgeL wtEdgeR wtFirst wtHoriz wtLe wtStart wtTile wtVert wtile)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WPoint wpAttr wpMark)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideTilings (wideTileData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# The wide tiling as an exponential expansion

What makes `DescriptiveComplexity.WideTiling` a *member* of NEXPTIME, and
nothing about resources: the address expansion
(`DescriptiveComplexity.AddrExp.addrExp`) at the vocabulary of ordinary tile
systems. Read on an instance `A`, it produces exactly the tile system whose
positions are the addresses of `A` – so a wide tiling *is* an ordinary tiling,
one exponential up, and membership is the composition `TILING ∘ expansion`,
exactly as `DescriptiveComplexity.wideAccept_mem_NEXPTIME` is `NTMAccept ∘
expansion`.

Each of the symbols is a static choice on the two tags followed by one of
the address expansion's five sentences: a mark of the instance for the tiles and
the accepting ones, a binary attribute for the two compatibilities, the
binary-number order for the order, and the initial-segment reading for the
bottom row.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace WideTile

/-! ### The defining sentences, at the tags -/

/-- The ordered vocabulary of wide tile-system instances. -/
abbrev wtOrd : Language.{0, 0} := AddrExp.aeOrd Lax822549.WideTilings.wtile

/-- The base vocabulary expanded by one copy of the block. -/
abbrev wtile1 : Language.{0, 0} := AddrExp.aeLang1 Lax822549.WideTilings.wtile

/-- The base vocabulary expanded by two copies of the block. -/
abbrev wtile2 : Language.{0, 0} := AddrExp.aeLang2 Lax822549.WideTilings.wtile

open AddrExp

/-- Being a position: an address of digits is one, a tile is not. -/
noncomputable def posnT : WTag → wtile1.Sentence
  | .addr => subsetS Lax822549.WideTilings.wtDig
  | .ctrl => ⊥

/-- A mark of the instance, at a tag: only the elements carry it. -/
noncomputable def markT (r : Lax822549.WideTilings.wtile.Relations 1) : WTag → wtile1.Sentence
  | .addr => ⊥
  | .ctrl => markS r

/-- A binary attribute of the instance, at a pair of tags. -/
noncomputable def binT (r : Lax822549.WideTilings.wtile.Relations 2) : WTag → WTag → wtile2.Sentence
  | .ctrl, .ctrl => binS r
  | _, _ => ⊥

/-- The order of the tiling, at a pair of tags: the addresses come first, in the
binary-number order, then the tiles in the instance's order. -/
noncomputable def leT : WTag → WTag → wtile2.Sentence
  | .addr, .addr => addrLeS Lax822549.WideTilings.wtLe
  | .addr, .ctrl => ⊤
  | .ctrl, .addr => ⊥
  | .ctrl, .ctrl => binS Lax822549.WideTilings.wtLe

/-- The bottom row, at a pair of tags: the cell of an element may carry a
tile. -/
noncomputable def firstT : WTag → WTag → wtile2.Sentence
  | .addr, .ctrl => regS Lax822549.WideTilings.wtLe Lax822549.WideTilings.wtFirst
  | _, _ => ⊥

/-- **The expansion of a wide tile-system instance**: the address expansion at
the vocabulary of ordinary tile systems. -/
noncomputable def wtileExp : Lax480241.Expansions.ExpExpansion Lax822549.WideTilings.wtile :=
  AddrExp.addrExp Lax822549.WideTilings.wtile Lax822549Proofs.Foreign.FirstOrder.Language.tiling fun {n} r τ =>
    match n, r with
    | _, .posn => onS1 (posnT (τ 0))
    | _, .tile => onS1 (markT Lax822549.WideTilings.wtTile (τ 0))
    | _, .tacc => onS1 (markT Lax822549.WideTilings.wtAcc (τ 0))
    | _, .tle => onS2 (leT (τ 0) (τ 1))
    | _, .horiz => onS2 (binT Lax822549.WideTilings.wtHoriz (τ 0) (τ 1))
    | _, .vert => onS2 (binT Lax822549.WideTilings.wtVert (τ 0) (τ 1))
    | _, .first => onS2 (firstT (τ 0) (τ 1))
    | _, .base => onS1 (markT Lax822549.WideTilings.wtBase (τ 0))
    | _, .tstart => onS1 (markT Lax822549.WideTilings.wtStart (τ 0))
    | _, .ledge => onS1 (markT Lax822549.WideTilings.wtEdgeL (τ 0))
    | _, .redge => onS1 (markT Lax822549.WideTilings.wtEdgeR (τ 0))

section Structure

variable (A : Type) [Lax822549.WideTilings.wtile.Structure A] [LinearOrder A]

/-- The expanded structure, at the vocabulary of tile systems – equal to the
expansion's own by definition, but not syntactically, so instance search has to
be handed it. -/
@[instance_reducible]
noncomputable def wtileStructure : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Structure (wtileExp.Map A) :=
  AddrExp.addrStructure (L := Lax822549.WideTilings.wtile) A

variable {A}

/-- **The universe of the wide tiling sits inside the expansion.** -/
noncomputable def wtileEmbed : Lax822549.WideMachines.WPoint A → wtileExp.Map A := AddrExp.addrEmbed

/-- **The points of the expansion are the universe of the wide tiling.** -/
noncomputable def wtileEquiv : Lax822549.WideMachines.WPoint A ≃ wtileExp.Map A := AddrExp.addrEquiv

@[simp]
theorem wtileEquiv_apply (p : Lax822549.WideMachines.WPoint A) : wtileEquiv p = wtileEmbed p := rfl

/-- Reading a unary symbol of the expanded vocabulary at one point. -/
theorem realize_one (rt : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1) (φ : WTag → wtile1.Sentence)
    (h : ∀ τ : Fin 1 → wtileExp.Tag, wtileExp.relSentence rt τ = onS1 (φ (τ 0)))
    (x : wtileExp.Map A) :
    letI := wtileStructure A
    (RelMap rt ![x] ↔
      @Sentence.Realize wtile1 A (AddrExp.addrBlock.structure₁ (L := wtOrd) x.1.2)
        (φ x.1.1)) :=
  AddrExp.realize_one rt φ h x

/-- Reading a binary symbol of the expanded vocabulary at two points. -/
theorem realize_two (rt : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 2) (φ : WTag → WTag → wtile2.Sentence)
    (h : ∀ τ : Fin 2 → wtileExp.Tag, wtileExp.relSentence rt τ = onS2 (φ (τ 0) (τ 1)))
    (x y : wtileExp.Map A) :
    letI := wtileStructure A
    (RelMap rt ![x, y] ↔
      @Sentence.Realize wtile2 A
        (AddrExp.addrBlock.structure₂ (L := wtOrd) x.1.2 y.1.2) (φ x.1.1 y.1.1)) :=
  AddrExp.realize_two rt φ h x y

end Structure

/-! ### The seven symbols -/

section Symbols

variable {A : Type} [Lax822549.WideTilings.wtile.Structure A] [LinearOrder A]

/-- **The positions of the expanded tiling are the addresses.** -/
theorem relMap_posn (p : Lax822549.WideMachines.WPoint A) :
    letI := wtileStructure A
    (RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlPosn ![wtileEmbed p] ↔ (Lax822549.WideTilings.wideTileData A).Posn p) := by
  let := wtileStructure A
  rw [realize_one Lax822549Proofs.Foreign.FirstOrder.Language.tlPosn posnT (fun _ => rfl) (wtileEmbed p)]
  match p with
  | Sum.inl s => exact realize_subsetS Lax822549.WideTilings.wtDig _
  | Sum.inr x => exact iff_of_false (not_realize_botS _) (fun h => h)

/-- **A mark of the expanded tiling is the corresponding mark of the
instance**, carried by the tiles alone. -/
theorem relMap_mark (rt : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1) (r : Lax822549.WideTilings.wtile.Relations 1)
    (h : ∀ τ : Fin 1 → wtileExp.Tag, wtileExp.relSentence rt τ = onS1 (markT r (τ 0)))
    (p : Lax822549.WideMachines.WPoint A) :
    letI := wtileStructure A
    (RelMap rt ![wtileEmbed p] ↔ Lax822549.WideMachines.wpMark (fun x => RelMap r ![x]) p) := by
  let := wtileStructure A
  rw [realize_one rt (markT r) h (wtileEmbed p)]
  match p with
  | Sum.inl s => exact iff_of_false (not_realize_botS _) (fun h => h)
  | Sum.inr x =>
    refine (realize_markS r _).trans ?_
    exact ⟨fun ⟨z, hz, hr⟩ => hz ▸ hr, fun hr => ⟨x, rfl, hr⟩⟩

/-- **A compatibility of the expanded tiling is the corresponding relation of
the instance**, holding of tiles alone. -/
theorem relMap_attr (rt : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 2) (r : Lax822549.WideTilings.wtile.Relations 2)
    (h : ∀ τ : Fin 2 → wtileExp.Tag, wtileExp.relSentence rt τ = onS2 (binT r (τ 0) (τ 1)))
    (p q : Lax822549.WideMachines.WPoint A) :
    letI := wtileStructure A
    (RelMap rt ![wtileEmbed p, wtileEmbed q] ↔ Lax822549.WideMachines.wpAttr (fun x y => RelMap r ![x, y]) p q) := by
  let := wtileStructure A
  rw [realize_two rt (binT r) h (wtileEmbed p) (wtileEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y =>
    refine (realize_binS r _ _).trans ?_
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => ha ▸ hb ▸ hr, fun hr => ⟨x, y, rfl, rfl, hr⟩⟩

/-- **The order of the expanded tiling**: addresses in the binary-number order
the instance's own order induces, then the tiles in that order. -/
theorem relMap_le (p q : Lax822549.WideMachines.WPoint A) :
    letI := wtileStructure A
    (RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlLe ![wtileEmbed p, wtileEmbed q] ↔ (Lax822549.WideTilings.wideTileData A).Le p q) := by
  let := wtileStructure A
  rw [realize_two Lax822549Proofs.Foreign.FirstOrder.Language.tlLe leT (fun _ => rfl) (wtileEmbed p) (wtileEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact realize_addrLeS Lax822549.WideTilings.wtLe _ _
  | Sum.inl s, Sum.inr y => exact iff_of_true (realize_topS₂ _ _) trivial
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y =>
    refine (realize_binS Lax822549.WideTilings.wtLe _ _).trans ?_
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => ha ▸ hb ▸ hr, fun hr => ⟨x, y, rfl, rfl, hr⟩⟩

/-- **The bottom row of the expanded tiling**: the address cutting the initial
segment of an element may carry that element's tiles. -/
theorem relMap_first (p q : Lax822549.WideMachines.WPoint A) :
    letI := wtileStructure A
    (RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlFirst ![wtileEmbed p, wtileEmbed q] ↔ (Lax822549.WideTilings.wideTileData A).First p q) := by
  let := wtileStructure A
  rw [realize_two Lax822549Proofs.Foreign.FirstOrder.Language.tlFirst firstT (fun _ => rfl) (wtileEmbed p) (wtileEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y =>
    refine (realize_regS Lax822549.WideTilings.wtLe Lax822549.WideTilings.wtFirst _ _).trans ?_
    exact ⟨fun ⟨a, b, hd, hb, hr⟩ => ⟨a, hd, hb ▸ hr⟩, fun ⟨a, hd, hr⟩ => ⟨a, y, hd, rfl, hr⟩⟩
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)

end Symbols

/-! ### The two tile systems agree -/

section Agree

variable {A : Type} [Lax822549.WideTilings.wtile.Structure A] [LinearOrder A]

/-- **The expanded tile system is the wide one**, field by field, along the
bijection between the universes. -/
theorem wtileAgree :
    letI := wtileStructure A
    (∀ p : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).Posn p ↔ (tileData (wtileExp.Map A)).Posn (wtileEquiv p)) ∧
      (∀ p q : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).Le p q ↔
        (tileData (wtileExp.Map A)).Le (wtileEquiv p) (wtileEquiv q)) ∧
      (∀ p : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).Tile p ↔
        (tileData (wtileExp.Map A)).Tile (wtileEquiv p)) ∧
      (∀ p : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).Acc p ↔
        (tileData (wtileExp.Map A)).Acc (wtileEquiv p)) ∧
      (∀ p q : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).Horiz p q ↔
        (tileData (wtileExp.Map A)).Horiz (wtileEquiv p) (wtileEquiv q)) ∧
      (∀ p q : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).Vert p q ↔
        (tileData (wtileExp.Map A)).Vert (wtileEquiv p) (wtileEquiv q)) ∧
      (∀ p q : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).First p q ↔
        (tileData (wtileExp.Map A)).First (wtileEquiv p) (wtileEquiv q)) ∧
      (∀ p : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).Base p ↔
        (tileData (wtileExp.Map A)).Base (wtileEquiv p)) ∧
      (∀ p : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).Start p ↔
        (tileData (wtileExp.Map A)).Start (wtileEquiv p)) ∧
      (∀ p : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).EdgeL p ↔
        (tileData (wtileExp.Map A)).EdgeL (wtileEquiv p)) ∧
      ∀ p : Lax822549.WideMachines.WPoint A, (Lax822549.WideTilings.wideTileData A).EdgeR p ↔
        (tileData (wtileExp.Map A)).EdgeR (wtileEquiv p) := by
  let := wtileStructure A
  exact ⟨fun p => (relMap_posn p).symm, fun p q => (relMap_le p q).symm,
    fun p => (relMap_mark Lax822549Proofs.Foreign.FirstOrder.Language.tlTile Lax822549.WideTilings.wtTile (fun _ => rfl) p).symm,
    fun p => (relMap_mark Lax822549Proofs.Foreign.FirstOrder.Language.tlAcc Lax822549.WideTilings.wtAcc (fun _ => rfl) p).symm,
    fun p q => (relMap_attr Lax822549Proofs.Foreign.FirstOrder.Language.tlHoriz Lax822549.WideTilings.wtHoriz (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr Lax822549Proofs.Foreign.FirstOrder.Language.tlVert Lax822549.WideTilings.wtVert (fun _ => rfl) p q).symm,
    fun p q => (relMap_first p q).symm,
    fun p => (relMap_mark Lax822549Proofs.Foreign.FirstOrder.Language.tlBase Lax822549.WideTilings.wtBase (fun _ => rfl) p).symm,
    fun p => (relMap_mark Lax822549Proofs.Foreign.FirstOrder.Language.tlStart Lax822549.WideTilings.wtStart (fun _ => rfl) p).symm,
    fun p => (relMap_mark Lax822549Proofs.Foreign.FirstOrder.Language.tlEdgeL Lax822549.WideTilings.wtEdgeL (fun _ => rfl) p).symm,
    fun p => (relMap_mark Lax822549Proofs.Foreign.FirstOrder.Language.tlEdgeR Lax822549.WideTilings.wtEdgeR (fun _ => rfl) p).symm⟩

/-- **A wide tiling is an ordinary tiling of the expansion.** -/
theorem wideTiling_iff_expansion (A : Type) [Lax822549.WideTilings.wtile.Structure A] [LinearOrder A] :
    letI := wtileStructure A
    (WideTiling A ↔ TILING (wtileExp.Map A)) := by
  let := wtileStructure A
  obtain ⟨hposn, hle, htile, hacc, hhoriz, hvert, hfirst, hbase, hstart, hel, her⟩ :=
    wtileAgree (A := A)
  constructor
  · exact fun h => ⟨TileData.wellFormed_map _ wtileEquiv _ hposn hle h.1,
      TileData.tileable_map _ wtileEquiv _ hposn hle htile hacc hhoriz hvert hfirst
        hbase hstart hel her h.2⟩
  · -- and back, along the inverse bijection
    have hposn' : ∀ p, (tileData (wtileExp.Map A)).Posn p ↔
        (Lax822549.WideTilings.wideTileData A).Posn (wtileEquiv.symm p) := by
      intro p
      have h := hposn (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hle' : ∀ p q, (tileData (wtileExp.Map A)).Le p q ↔
        (Lax822549.WideTilings.wideTileData A).Le (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro p q
      have h := hle (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    have htile' : ∀ p, (tileData (wtileExp.Map A)).Tile p ↔
        (Lax822549.WideTilings.wideTileData A).Tile (wtileEquiv.symm p) := by
      intro p
      have h := htile (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hacc' : ∀ p, (tileData (wtileExp.Map A)).Acc p ↔
        (Lax822549.WideTilings.wideTileData A).Acc (wtileEquiv.symm p) := by
      intro p
      have h := hacc (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hhoriz' : ∀ p q, (tileData (wtileExp.Map A)).Horiz p q ↔
        (Lax822549.WideTilings.wideTileData A).Horiz (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro p q
      have h := hhoriz (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    have hvert' : ∀ p q, (tileData (wtileExp.Map A)).Vert p q ↔
        (Lax822549.WideTilings.wideTileData A).Vert (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro p q
      have h := hvert (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    have hfirst' : ∀ p q, (tileData (wtileExp.Map A)).First p q ↔
        (Lax822549.WideTilings.wideTileData A).First (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro p q
      have h := hfirst (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    have hbase' : ∀ p, (tileData (wtileExp.Map A)).Base p ↔
        (Lax822549.WideTilings.wideTileData A).Base (wtileEquiv.symm p) := by
      intro p
      have h := hbase (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hstart' : ∀ p, (tileData (wtileExp.Map A)).Start p ↔
        (Lax822549.WideTilings.wideTileData A).Start (wtileEquiv.symm p) := by
      intro p
      have h := hstart (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hel' : ∀ p, (tileData (wtileExp.Map A)).EdgeL p ↔
        (Lax822549.WideTilings.wideTileData A).EdgeL (wtileEquiv.symm p) := by
      intro p
      have h := hel (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have her' : ∀ p, (tileData (wtileExp.Map A)).EdgeR p ↔
        (Lax822549.WideTilings.wideTileData A).EdgeR (wtileEquiv.symm p) := by
      intro p
      have h := her (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    exact fun h => ⟨TileData.wellFormed_map _ wtileEquiv.symm _ hposn' hle' h.1,
      TileData.tileable_map _ wtileEquiv.symm _ hposn' hle' htile' hacc' hhoriz' hvert'
        hfirst' hbase' hstart' hel' her' h.2⟩

end Agree

end WideTile

/-! ### The membership -/

/-- **The wide tiling is in NEXPTIME**, which is `NP.exp`: the expansion turns it
into `DescriptiveComplexity.TILING`, and that problem is in NP. This is the
second natural member the class has, beside the wide machine. -/
theorem wideTiling_mem_NEXPTIME : WideTiling ∈ NEXPTIME := by
  let hinst : ∀ (A : Type) [Lax822549.WideTilings.wtile.Structure A] [LinearOrder A],
      Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Structure (WideTile.wtileExp.Map A) := fun A => WideTile.wtileStructure A
  refine ⟨WideTile.wtileExp, TILING, tiling_mem_NP, ?_⟩
  intro A _ _ _ _
  exact WideTile.wideTiling_iff_expansion A

end Lax822549Proofs.DescriptiveComplexity


