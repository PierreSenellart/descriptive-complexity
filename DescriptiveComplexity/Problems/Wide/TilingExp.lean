/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Tiling
import DescriptiveComplexity.Problems.Tiling.Membership
import DescriptiveComplexity.Exponential.Classes

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace WideTile

/-! ### The defining sentences, at the tags -/

/-- The ordered vocabulary of wide tile-system instances. -/
abbrev wtOrd : Language.{0, 0} := AddrExp.aeOrd Language.wtile

/-- The base vocabulary expanded by one copy of the block. -/
abbrev wtile1 : Language.{0, 0} := AddrExp.aeLang1 Language.wtile

/-- The base vocabulary expanded by two copies of the block. -/
abbrev wtile2 : Language.{0, 0} := AddrExp.aeLang2 Language.wtile

open AddrExp

/-- Being a position: an address of digits is one, a tile is not. -/
noncomputable def posnT : WTag → wtile1.Sentence
  | .addr => subsetS wtDig
  | .ctrl => ⊥

/-- A mark of the instance, at a tag: only the elements carry it. -/
noncomputable def markT (r : Language.wtile.Relations 1) : WTag → wtile1.Sentence
  | .addr => ⊥
  | .ctrl => markS r

/-- A binary attribute of the instance, at a pair of tags. -/
noncomputable def binT (r : Language.wtile.Relations 2) : WTag → WTag → wtile2.Sentence
  | .ctrl, .ctrl => binS r
  | _, _ => ⊥

/-- The order of the tiling, at a pair of tags: the addresses come first, in the
binary-number order, then the tiles in the instance's order. -/
noncomputable def leT : WTag → WTag → wtile2.Sentence
  | .addr, .addr => addrLeS wtLe
  | .addr, .ctrl => ⊤
  | .ctrl, .addr => ⊥
  | .ctrl, .ctrl => binS wtLe

/-- The bottom row, at a pair of tags: the cell of an element may carry a
tile. -/
noncomputable def firstT : WTag → WTag → wtile2.Sentence
  | .addr, .ctrl => regS wtLe wtFirst
  | _, _ => ⊥

/-- **The expansion of a wide tile-system instance**: the address expansion at
the vocabulary of ordinary tile systems. -/
noncomputable def wtileExp : ExpExpansion Language.wtile :=
  AddrExp.addrExp Language.wtile Language.tiling fun {n} r τ =>
    match n, r with
    | _, .posn => onS1 (posnT (τ 0))
    | _, .tile => onS1 (markT wtTile (τ 0))
    | _, .tacc => onS1 (markT wtAcc (τ 0))
    | _, .tle => onS2 (leT (τ 0) (τ 1))
    | _, .horiz => onS2 (binT wtHoriz (τ 0) (τ 1))
    | _, .vert => onS2 (binT wtVert (τ 0) (τ 1))
    | _, .first => onS2 (firstT (τ 0) (τ 1))
    | _, .base => onS1 (markT wtBase (τ 0))
    | _, .tstart => onS1 (markT wtStart (τ 0))
    | _, .ledge => onS1 (markT wtEdgeL (τ 0))
    | _, .redge => onS1 (markT wtEdgeR (τ 0))

section Structure

variable (A : Type) [Language.wtile.Structure A] [LinearOrder A]

/-- The expanded structure, at the vocabulary of tile systems – equal to the
expansion's own by definition, but not syntactically, so instance search has to
be handed it. -/
@[instance_reducible]
noncomputable def wtileStructure : Language.tiling.Structure (wtileExp.Map A) :=
  AddrExp.addrStructure (L := Language.wtile) A

variable {A}

/-- **The universe of the wide tiling sits inside the expansion.** -/
noncomputable def wtileEmbed : WPoint A → wtileExp.Map A := AddrExp.addrEmbed

/-- **The points of the expansion are the universe of the wide tiling.** -/
noncomputable def wtileEquiv : WPoint A ≃ wtileExp.Map A := AddrExp.addrEquiv

@[simp]
theorem wtileEquiv_apply (p : WPoint A) : wtileEquiv p = wtileEmbed p := rfl

/-- Reading a unary symbol of the expanded vocabulary at one point. -/
theorem realize_one (rt : Language.tiling.Relations 1) (φ : WTag → wtile1.Sentence)
    (h : ∀ τ : Fin 1 → wtileExp.Tag, wtileExp.relSentence rt τ = onS1 (φ (τ 0)))
    (x : wtileExp.Map A) :
    letI := wtileStructure A
    (RelMap rt ![x] ↔
      @Sentence.Realize wtile1 A (AddrExp.addrBlock.structure₁ (L := wtOrd) x.1.2)
        (φ x.1.1)) :=
  AddrExp.realize_one rt φ h x

/-- Reading a binary symbol of the expanded vocabulary at two points. -/
theorem realize_two (rt : Language.tiling.Relations 2) (φ : WTag → WTag → wtile2.Sentence)
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

variable {A : Type} [Language.wtile.Structure A] [LinearOrder A]

/-- **The positions of the expanded tiling are the addresses.** -/
theorem relMap_posn (p : WPoint A) :
    letI := wtileStructure A
    (RelMap tlPosn ![wtileEmbed p] ↔ (wideTileData A).Posn p) := by
  let := wtileStructure A
  rw [realize_one tlPosn posnT (fun _ => rfl) (wtileEmbed p)]
  match p with
  | Sum.inl s => exact realize_subsetS wtDig _
  | Sum.inr x => exact iff_of_false (not_realize_botS _) (fun h => h)

/-- **A mark of the expanded tiling is the corresponding mark of the
instance**, carried by the tiles alone. -/
theorem relMap_mark (rt : Language.tiling.Relations 1) (r : Language.wtile.Relations 1)
    (h : ∀ τ : Fin 1 → wtileExp.Tag, wtileExp.relSentence rt τ = onS1 (markT r (τ 0)))
    (p : WPoint A) :
    letI := wtileStructure A
    (RelMap rt ![wtileEmbed p] ↔ wpMark (fun x => RelMap r ![x]) p) := by
  let := wtileStructure A
  rw [realize_one rt (markT r) h (wtileEmbed p)]
  match p with
  | Sum.inl s => exact iff_of_false (not_realize_botS _) (fun h => h)
  | Sum.inr x =>
    refine (realize_markS r _).trans ?_
    exact ⟨fun ⟨z, hz, hr⟩ => hz ▸ hr, fun hr => ⟨x, rfl, hr⟩⟩

/-- **A compatibility of the expanded tiling is the corresponding relation of
the instance**, holding of tiles alone. -/
theorem relMap_attr (rt : Language.tiling.Relations 2) (r : Language.wtile.Relations 2)
    (h : ∀ τ : Fin 2 → wtileExp.Tag, wtileExp.relSentence rt τ = onS2 (binT r (τ 0) (τ 1)))
    (p q : WPoint A) :
    letI := wtileStructure A
    (RelMap rt ![wtileEmbed p, wtileEmbed q] ↔ wpAttr (fun x y => RelMap r ![x, y]) p q) := by
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
theorem relMap_le (p q : WPoint A) :
    letI := wtileStructure A
    (RelMap tlLe ![wtileEmbed p, wtileEmbed q] ↔ (wideTileData A).Le p q) := by
  let := wtileStructure A
  rw [realize_two tlLe leT (fun _ => rfl) (wtileEmbed p) (wtileEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact realize_addrLeS wtLe _ _
  | Sum.inl s, Sum.inr y => exact iff_of_true (realize_topS₂ _ _) trivial
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y =>
    refine (realize_binS wtLe _ _).trans ?_
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => ha ▸ hb ▸ hr, fun hr => ⟨x, y, rfl, rfl, hr⟩⟩

/-- **The bottom row of the expanded tiling**: the address cutting the initial
segment of an element may carry that element's tiles. -/
theorem relMap_first (p q : WPoint A) :
    letI := wtileStructure A
    (RelMap tlFirst ![wtileEmbed p, wtileEmbed q] ↔ (wideTileData A).First p q) := by
  let := wtileStructure A
  rw [realize_two tlFirst firstT (fun _ => rfl) (wtileEmbed p) (wtileEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y =>
    refine (realize_regS wtLe wtFirst _ _).trans ?_
    exact ⟨fun ⟨a, b, hd, hb, hr⟩ => ⟨a, hd, hb ▸ hr⟩, fun ⟨a, hd, hr⟩ => ⟨a, y, hd, rfl, hr⟩⟩
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)

end Symbols

/-! ### The two tile systems agree -/

section Agree

variable {A : Type} [Language.wtile.Structure A] [LinearOrder A]

/-- **The expanded tile system is the wide one**, field by field, along the
bijection between the universes. -/
theorem wtileAgree :
    letI := wtileStructure A
    (∀ p : WPoint A, (wideTileData A).Posn p ↔ (tileData (wtileExp.Map A)).Posn (wtileEquiv p)) ∧
      (∀ p q : WPoint A, (wideTileData A).Le p q ↔
        (tileData (wtileExp.Map A)).Le (wtileEquiv p) (wtileEquiv q)) ∧
      (∀ p : WPoint A, (wideTileData A).Tile p ↔
        (tileData (wtileExp.Map A)).Tile (wtileEquiv p)) ∧
      (∀ p : WPoint A, (wideTileData A).Acc p ↔
        (tileData (wtileExp.Map A)).Acc (wtileEquiv p)) ∧
      (∀ p q : WPoint A, (wideTileData A).Horiz p q ↔
        (tileData (wtileExp.Map A)).Horiz (wtileEquiv p) (wtileEquiv q)) ∧
      (∀ p q : WPoint A, (wideTileData A).Vert p q ↔
        (tileData (wtileExp.Map A)).Vert (wtileEquiv p) (wtileEquiv q)) ∧
      (∀ p q : WPoint A, (wideTileData A).First p q ↔
        (tileData (wtileExp.Map A)).First (wtileEquiv p) (wtileEquiv q)) ∧
      (∀ p : WPoint A, (wideTileData A).Base p ↔
        (tileData (wtileExp.Map A)).Base (wtileEquiv p)) ∧
      (∀ p : WPoint A, (wideTileData A).Start p ↔
        (tileData (wtileExp.Map A)).Start (wtileEquiv p)) ∧
      (∀ p : WPoint A, (wideTileData A).EdgeL p ↔
        (tileData (wtileExp.Map A)).EdgeL (wtileEquiv p)) ∧
      ∀ p : WPoint A, (wideTileData A).EdgeR p ↔
        (tileData (wtileExp.Map A)).EdgeR (wtileEquiv p) := by
  let := wtileStructure A
  exact ⟨fun p => (relMap_posn p).symm, fun p q => (relMap_le p q).symm,
    fun p => (relMap_mark tlTile wtTile (fun _ => rfl) p).symm,
    fun p => (relMap_mark tlAcc wtAcc (fun _ => rfl) p).symm,
    fun p q => (relMap_attr tlHoriz wtHoriz (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr tlVert wtVert (fun _ => rfl) p q).symm,
    fun p q => (relMap_first p q).symm,
    fun p => (relMap_mark tlBase wtBase (fun _ => rfl) p).symm,
    fun p => (relMap_mark tlStart wtStart (fun _ => rfl) p).symm,
    fun p => (relMap_mark tlEdgeL wtEdgeL (fun _ => rfl) p).symm,
    fun p => (relMap_mark tlEdgeR wtEdgeR (fun _ => rfl) p).symm⟩

/-- **A wide tiling is an ordinary tiling of the expansion.** -/
theorem wideTiling_iff_expansion (A : Type) [Language.wtile.Structure A] [LinearOrder A] :
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
        (wideTileData A).Posn (wtileEquiv.symm p) := by
      intro p
      have h := hposn (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hle' : ∀ p q, (tileData (wtileExp.Map A)).Le p q ↔
        (wideTileData A).Le (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro p q
      have h := hle (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    have htile' : ∀ p, (tileData (wtileExp.Map A)).Tile p ↔
        (wideTileData A).Tile (wtileEquiv.symm p) := by
      intro p
      have h := htile (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hacc' : ∀ p, (tileData (wtileExp.Map A)).Acc p ↔
        (wideTileData A).Acc (wtileEquiv.symm p) := by
      intro p
      have h := hacc (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hhoriz' : ∀ p q, (tileData (wtileExp.Map A)).Horiz p q ↔
        (wideTileData A).Horiz (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro p q
      have h := hhoriz (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    have hvert' : ∀ p q, (tileData (wtileExp.Map A)).Vert p q ↔
        (wideTileData A).Vert (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro p q
      have h := hvert (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    have hfirst' : ∀ p q, (tileData (wtileExp.Map A)).First p q ↔
        (wideTileData A).First (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro p q
      have h := hfirst (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    have hbase' : ∀ p, (tileData (wtileExp.Map A)).Base p ↔
        (wideTileData A).Base (wtileEquiv.symm p) := by
      intro p
      have h := hbase (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hstart' : ∀ p, (tileData (wtileExp.Map A)).Start p ↔
        (wideTileData A).Start (wtileEquiv.symm p) := by
      intro p
      have h := hstart (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hel' : ∀ p, (tileData (wtileExp.Map A)).EdgeL p ↔
        (wideTileData A).EdgeL (wtileEquiv.symm p) := by
      intro p
      have h := hel (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have her' : ∀ p, (tileData (wtileExp.Map A)).EdgeR p ↔
        (wideTileData A).EdgeR (wtileEquiv.symm p) := by
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
  let hinst : ∀ (A : Type) [Language.wtile.Structure A] [LinearOrder A],
      Language.tiling.Structure (WideTile.wtileExp.Map A) := fun A => WideTile.wtileStructure A
  refine ⟨WideTile.wtileExp, TILING, tiling_mem_NP, ?_⟩
  intro A _ _ _ _
  exact WideTile.wideTiling_iff_expansion A

end DescriptiveComplexity
