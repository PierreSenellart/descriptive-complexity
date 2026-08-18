/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingHard.Tiles
import DescriptiveComplexity.OrderedComposition

/-!
# The tile system a machine is drawn as, and its grid

The instance the hardness reduction emits, read semantically: a
`FirstOrder.Language.wtile`-structure on the tagged triples
`DescriptiveComplexity.TilePt`, with the tiles of
`DescriptiveComplexity.Problems.Wide.TilingHard.Tiles` and an order whose
**digits come last**.

That last point is what makes the grid the right size. A coordinate of
`DescriptiveComplexity.WideTiling` is an address holding digits alone, so the
square is indexed by the subsets of the diagonal – one per subset of the
machine's own instance, which is exactly one per tape address and one per time
step. The other points of the emitted universe are tiles, and they are ordered
*below* every digit, so they never enter a coordinate and never disturb the
binary-number order the coordinates are compared by: two coordinates differ at a
digit, and there the emitted order is the machine's own.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

/-! ### The order on the emitted universe -/

section Order

variable {A : Type} [LinearOrder A] [Language.wide.Structure A]

/-- A linear order on the tags, to order the points that are not digits. -/
noncomputable instance : LinearOrder TileTag := finiteLinearOrder _

/-- **The order the emitted instance carries**: the points that are not digits
first, in the lexicographic order of their tag and their triple, then the digits
in the machine's own order. -/
def tpLe (p q : TilePt A) : Prop :=
  (TPDig p ∧ TPDig q ∧ WMLe (p.2 0) (q.2 0)) ∨
    (¬TPDig p ∧ TPDig q) ∨
    (¬TPDig p ∧ ¬TPDig q ∧ tagTupleLe p q)

omit [Language.wide.Structure A] in
/-- **The lexicographic order on the emitted universe is linear** – Mathlib's,
read through `DescriptiveComplexity.tagTupleLe_iff_le`. -/
theorem isLinOrd_tagTuple :
    IsLinOrd (tagTupleLe (Tag := TileTag) (d := 3) (A := A)) := by
  have heq : (tagTupleLe (Tag := TileTag) (d := 3) (A := A)) =
      (tagTupleOrder : LinearOrder (TileTag × (Fin 3 → A))).le := by
    funext p q
    exact propext (tagTupleLe_iff_le p q)
  rw [heq]
  exact ⟨fun a => @le_refl _ (tagTupleOrder (Tag := TileTag) (d := 3) (A := A)).toPreorder a,
    fun a b c => @le_trans _ (tagTupleOrder (Tag := TileTag) (d := 3) (A := A)).toPreorder a b c,
    fun a b => @le_antisymm _
      (tagTupleOrder (Tag := TileTag) (d := 3) (A := A)).toPartialOrder a b,
    fun a b => @le_total _ (tagTupleOrder (Tag := TileTag) (d := 3) (A := A)) a b⟩

omit [LinearOrder A] [Language.wide.Structure A] in
/-- A digit is determined by the element it is the digit of. -/
theorem eq_of_tpDig {p q : TilePt A} (hp : TPDig p) (hq : TPDig q)
    (h : p.2 0 = q.2 0) : p = q := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have h1 : p.2 1 = q.2 1 := by rw [← hp2, ← hq2]; exact h
  have h2 : p.2 2 = q.2 2 := by rw [← hp3, ← hq3]; exact h1
  refine Prod.ext (hp1.trans hq1.symm) (funext fun i => ?_)
  fin_cases i <;> assumption

/-- **The emitted order is linear**, given that the machine's is: the digits
carry the machine's order, and everything else the lexicographic one. -/
theorem isLinOrd_tpLe (h : IsLinOrd (WMLe (A := A))) : IsLinOrd (tpLe (A := A)) := by
  obtain ⟨hrefl, htrans, hanti, htot⟩ := h
  obtain ⟨lrefl, ltrans, lanti, ltot⟩ := isLinOrd_tagTuple (A := A)
  refine ⟨fun p => ?_, fun p q r hpq hqr => ?_, fun p q hpq hqp => ?_, fun p q => ?_⟩
  · by_cases hd : TPDig p
    · exact Or.inl ⟨hd, hd, hrefl _⟩
    · exact Or.inr (Or.inr ⟨hd, hd, lrefl p⟩)
  · rcases hpq with ⟨hp, hq, hle⟩ | ⟨hp, hq⟩ | ⟨hp, hq, hlex⟩
    · rcases hqr with ⟨_, hr, hle'⟩ | ⟨hq', _⟩ | ⟨hq', _⟩
      · exact Or.inl ⟨hp, hr, htrans _ _ _ hle hle'⟩
      · exact absurd hq hq'
      · exact absurd hq hq'
    · rcases hqr with ⟨_, hr, _⟩ | ⟨hq', _⟩ | ⟨hq', _⟩
      · exact Or.inr (Or.inl ⟨hp, hr⟩)
      · exact absurd hq hq'
      · exact absurd hq hq'
    · rcases hqr with ⟨hq', _, _⟩ | ⟨_, hr⟩ | ⟨_, hr, hlex'⟩
      · exact absurd hq' hq
      · exact Or.inr (Or.inl ⟨hp, hr⟩)
      · exact Or.inr (Or.inr ⟨hp, hr, ltrans _ _ _ hlex hlex'⟩)
  · rcases hpq with ⟨hp, hq, hle⟩ | ⟨hp, hq⟩ | ⟨hp, hq, hlex⟩
    · rcases hqp with ⟨_, _, hle'⟩ | ⟨hq', _⟩ | ⟨hq', _⟩
      · exact eq_of_tpDig hp hq (hanti _ _ hle hle')
      · exact absurd hq hq'
      · exact absurd hq hq'
    · rcases hqp with ⟨-, hp', -⟩ | ⟨hq', -⟩ | ⟨hq', -, -⟩
      · exact absurd hp' hp
      · exact absurd hq hq'
      · exact absurd hq hq'
    · rcases hqp with ⟨hq', _, _⟩ | ⟨_, hp'⟩ | ⟨_, _, hlex'⟩
      · exact absurd hq' hq
      · exact absurd hp' hp
      · exact lanti _ _ hlex hlex'
  · by_cases hp : TPDig p
    · by_cases hq : TPDig q
      · rcases htot (p.2 0) (q.2 0) with hle | hle
        · exact Or.inl (Or.inl ⟨hp, hq, hle⟩)
        · exact Or.inr (Or.inl ⟨hq, hp, hle⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hq, hp⟩))
    · by_cases hq : TPDig q
      · exact Or.inl (Or.inr (Or.inl ⟨hp, hq⟩))
      · rcases ltot p q with hlex | hlex
        · exact Or.inl (Or.inr (Or.inr ⟨hp, hq, hlex⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hq, hp, hlex⟩))

/-- Between two digits the emitted order is the machine's. -/
theorem tpLe_dig (x y : A) : tpLe (tpDig (A := A) x) (tpDig (A := A) y) ↔ WMLe x y :=
  ⟨fun h => by
      rcases h with ⟨-, -, hle⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
      · exact hle
      · exact absurd (tpDig_isDig x) hp
      · exact absurd (tpDig_isDig x) hp,
    fun h => Or.inl ⟨tpDig_isDig x, tpDig_isDig y, h⟩⟩

end Order

/-! ### The structure the reduction emits -/

section Structure

variable {A : Type} [LinearOrder A] [Language.wide.Structure A]

/-- **The tile system a wide machine is drawn as**: the tiles of
`DescriptiveComplexity.Problems.Wide.TilingHard.Tiles` on the tagged triples,
with the digits last in the order. This is the instance the hardness reductions
emit, read semantically – the formulas that write it down come later, and are
checked against exactly this.

The **bottom row is a parameter**, because it is the one thing the two machines
this drawing serves describe differently: the clocked machine's tape is a
register file and the space-bounded machine's the ruler of all the segments.
Everything else – the tiles, the two compatibilities, the edges and the corner –
is the same drawing. -/
@[instance_reducible]
noncomputable def tileStrOf (F : TilePt A → TilePt A → Prop) :
    Language.wtile.Structure (TilePt A) where
  funMap {_} f _ := isEmptyElim f
  RelMap {n} r :=
    match n, r with
    | _, .wle => fun v => tpLe (v 0) (v 1)
    | _, .dig => fun v => TPDig (v 0)
    | _, .tile => fun v => TPTile (v 0)
    | _, .tacc => fun v => TPAcc (v 0)
    | _, .horiz => fun v => TPHoriz (v 0) (v 1)
    | _, .vert => fun v => TPVert (v 0) (v 1)
    | _, .first => fun v => F (v 0) (v 1)
    | _, .base => fun v => TPBase (v 0)
    | _, .tstart => fun v => TPStart (v 0)
    | _, .ledge => fun v => TPEdgeL (v 0)
    | _, .redge => fun v => TPEdgeR (v 0)

variable (A) in
/-- **The drawing of the clocked machine**: the tile system above with the
register file for its bottom row. -/
@[instance_reducible]
noncomputable def tileStr : Language.wtile.Structure (TilePt A) := tileStrOf TPFirst

variable (A) in
/-- **The drawing of the space-bounded machine**: the same tile system with the
ruler of all the segments for its bottom row. -/
@[instance_reducible]
noncomputable def tileStrR : Language.wtile.Structure (TilePt A) := tileStrOf TPFirstR

@[simp]
theorem wtLe_tileStrOf (F : TilePt A → TilePt A → Prop) (p q : TilePt A) :
    letI := tileStrOf F
    (WTLe p q ↔ tpLe p q) := Iff.rfl

@[simp]
theorem wtLe_tileStr (p q : TilePt A) :
    letI := tileStr A
    (WTLe p q ↔ tpLe p q) := Iff.rfl

@[simp]
theorem wtDig_tileStr (p : TilePt A) :
    letI := tileStr A
    (WTDig p ↔ TPDig p) := Iff.rfl

@[simp]
theorem wtTile_tileStr (p : TilePt A) :
    letI := tileStr A
    (WTTile p ↔ TPTile p) := Iff.rfl

@[simp]
theorem wtAcc_tileStr (p : TilePt A) :
    letI := tileStr A
    (WTAcc p ↔ TPAcc p) := Iff.rfl

@[simp]
theorem wtHoriz_tileStr (p q : TilePt A) :
    letI := tileStr A
    (WTHoriz p q ↔ TPHoriz p q) := Iff.rfl

@[simp]
theorem wtVert_tileStr (p q : TilePt A) :
    letI := tileStr A
    (WTVert p q ↔ TPVert p q) := Iff.rfl

@[simp]
theorem wtFirst_tileStr (p q : TilePt A) :
    letI := tileStr A
    (WTFirst p q ↔ TPFirst p q) := Iff.rfl

@[simp]
theorem wtFirst_tileStrR (p q : TilePt A) :
    letI := tileStrR A
    (WTFirst p q ↔ TPFirstR p q) := Iff.rfl

@[simp]
theorem wtBase_tileStr (p : TilePt A) :
    letI := tileStr A
    (WTBase p ↔ TPBase p) := Iff.rfl

@[simp]
theorem wtStart_tileStr (p : TilePt A) :
    letI := tileStr A
    (WTStart p ↔ TPStart p) := Iff.rfl

@[simp]
theorem wtEdgeL_tileStr (p : TilePt A) :
    letI := tileStr A
    (WTEdgeL p ↔ TPEdgeL p) := Iff.rfl

@[simp]
theorem wtEdgeR_tileStr (p : TilePt A) :
    letI := tileStr A
    (WTEdgeR p ↔ TPEdgeR p) := Iff.rfl

end Structure

end TilingHard

end DescriptiveComplexity
