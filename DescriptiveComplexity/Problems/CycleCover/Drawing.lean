/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CycleCover.Formulas
import DescriptiveComplexity.Problems.CycleCover.Defs
import DescriptiveComplexity.Counting.Post
import DescriptiveComplexity.Numbers.DigitExtract

/-!
# The drawing of the reduction of #1-in-SAT to #Cycle Cover

`DescriptiveComplexity.SatCover.drawInterp` draws, over the ordered expansion
of a CNF formula, the ladder expansion of the base graph with Valiant's
gadgets attached: its universe is in bijection with the nodes and the rungs
of the ladder graph (`DescriptiveComplexity.SatCover.drawEquiv`), its arcs
are the ladder edges (`DescriptiveComplexity.SatCover.drawArc_iff`), plus one
isolated node with a self-loop so that the universe is never empty.

The number of cycle covers of the drawn digraph is then the permanent of the
ladder expansion, and the number of exactly-one models is read off it by a
remainder modulo `2 ^ L + 1`, `L` the number of levels, and a quotient by `4`
to the number of occurrences, both definable cardinalities
(`DescriptiveComplexity.sharpOneInSat_oneCall_sharpCycleCover`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc Finset

namespace SatCover

/-! ### The two definable cardinalities -/

/-- The occurrences, as a relativized interpretation into the empty
vocabulary. -/
noncomputable def occInterp : RelFOInterpretation satOrd Language.empty OccTag 2 where
  relFormula := fun R => isEmptyElim R
  domFormula := fun t => occDomF t.1 t.2 0 1

section Cards

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The universe of the interpretation of the occurrences is the occurrences. -/
noncomputable def occInterpEquiv : occInterp.MapRel A ≃ Occ A where
  toFun p := occOf p.1.1.1 p.1.1.2 (p.1.2 0) (p.1.2 1) (realize_occDomF.mp p.2)
  invFun o := ⟨(occTag o, ![(occPair o).1, (occPair o).2]), by
    have h := occDom_occTag o
    exact realize_occDomF.mpr (by simpa using h)⟩
  left_inv := by
    rintro ⟨⟨⟨d, s⟩, w⟩, hw⟩
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact occTag_occOf d s (w 0) (w 1) _
    · funext j
      change ![(occPair (occOf d s (w 0) (w 1) _)).1, (occPair (occOf d s (w 0) (w 1) _)).2] j =
        w j
      rw [occPair_occOf]
      fin_cases j <;> rfl
  right_inv o := by
    change occOf (occTag o).1 (occTag o).2 _ _ _ = o
    exact occOf_occTag o

theorem card_occInterp : Nat.card (occInterp.MapRel A) = Nat.card (Occ A) :=
  Nat.card_congr occInterpEquiv

/-- The level of an occurrence and an index. -/
noncomputable def levelOfPos (q : Occ A × Fin 3) : Level A :=
  mkLevel (LevelTag.pos (occTag q.1) q.2) (occPair q.1).1 (occPair q.1).2 (occDom_occTag q.1)

theorem levelOfPos_injective : Function.Injective (levelOfPos (A := A)) := by
  rintro ⟨o, k⟩ ⟨o', k'⟩ h
  have h1 := congrArg (fun ℓ : Level A => ℓ.1.1) h
  have h2 := congrArg (fun ℓ : Level A => ℓ.1.2) h
  change LevelTag.pos (occTag o) k = LevelTag.pos (occTag o') k' at h1
  change ![(occPair o).1, (occPair o).2] = ![(occPair o').1, (occPair o').2] at h2
  obtain ⟨ht, hk⟩ := Prod.mk.inj (Option.some.inj h1)
  have hp : occPair o = occPair o' :=
    Prod.ext (congrFun h2 0) (congrFun h2 1)
  rw [← occOf_occTag o, ← occOf_occTag o']
  exact Prod.ext (by simp only [ht, hp]) hk

/-- There are at least three levels per occurrence. -/
theorem three_mul_card_occ_le [Finite A] :
    3 * Nat.card (Occ A) ≤ Nat.card (Level A) := by
  have := Nat.card_le_card_of_injective _ (levelOfPos_injective (A := A))
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, mul_comm] at this

end Cards

/-! ### The drawing -/

/-- The tags of the drawing: the nodes and the rungs of the ladder graph, and
one extra node. -/
abbrev FullTag : Type := DrawTag ⊕ Unit

/-- Coordinates `2` to `5` pinned to coordinate `0`. -/
noncomputable def pinF : satOrd.Formula (Fin 6) :=
  eqF 2 0 ⊓ (eqF 3 0 ⊓ (eqF 4 0 ⊓ eqF 5 0))

/-- The domain of each tag: the nodes, pinned; the rungs, a node, a node, a
level and an index below the width; the extra node, all coordinates the
least element. -/
noncomputable def drawDomF : FullTag → satOrd.Formula (Fin 6)
  | Sum.inl (Sum.inl t) => vDomF t 0 1 ⊓ pinF
  | Sum.inl (Sum.inr (t, t', l, j)) =>
      vDomF t 0 1 ⊓ (vDomF t' 2 3 ⊓ (levelDomF l 4 5 ⊓ widthF t t' l j 0 1 2 3 4 5))
  | Sum.inr () => isMinF 0 ⊓ (eqF 1 0 ⊓ pinF)

/-- The arcs: the ladder edges, and the self-loop of the extra node. -/
noncomputable def drawArcF : FullTag → FullTag → satOrd.Formula (Fin 2 × Fin 6)
  | Sum.inl (Sum.inl t), Sum.inl (Sum.inr (t', _, l, _)) =>
      if t = t' then eqF (0, 0) (1, 0) ⊓ (eqF (0, 1) (1, 1) ⊓ levelMinF l (1, 4) (1, 5)) else ⊥
  | Sum.inl (Sum.inr (t, t', l, j)), Sum.inl (Sum.inr (ta, tb, l', j')) =>
      (if (t, t', l, j) = (ta, tb, l', j') then Formula.iInf fun i : Fin 6 => eqF (0, i) (1, i)
        else ⊥) ⊔
      (if t = ta ∧ t' = tb then
        eqF (0, 0) (1, 0) ⊓ (eqF (0, 1) (1, 1) ⊓ (eqF (0, 2) (1, 2) ⊓ (eqF (0, 3) (1, 3) ⊓
          levelCovF l l' (0, 4) (0, 5) (1, 4) (1, 5))))
      else ⊥)
  | Sum.inl (Sum.inr (_, t', l, _)), Sum.inl (Sum.inl tb) =>
      if t' = tb then eqF (0, 2) (1, 0) ⊓ (eqF (0, 3) (1, 1) ⊓ levelMaxF l (0, 4) (0, 5)) else ⊥
  | Sum.inr (), Sum.inr () => ⊤
  | _, _ => ⊥

/-- **The drawing**: the ladder expansion of the attached graph, with an extra
node. -/
noncomputable def drawInterp : RelFOInterpretation satOrd Language.digraph FullTag 6 where
  relFormula {n} R :=
    match n, R with
    | _, .arc => fun t => drawArcF (t 0) (t 1)
  domFormula := drawDomF

section Draw

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

theorem realize_pinF {w : Fin 6 → A} :
    pinF.Realize w ↔ w 2 = w 0 ∧ w 3 = w 0 ∧ w 4 = w 0 ∧ w 5 = w 0 := by
  simp only [pinF, Formula.realize_inf, realize_eqF]

theorem realize_drawDomF_base {t : VTag} {w : Fin 6 → A} :
    (drawDomF (Sum.inl (Sum.inl t))).Realize w ↔
      VDom t (w 0) (w 1) ∧ (w 2 = w 0 ∧ w 3 = w 0 ∧ w 4 = w 0 ∧ w 5 = w 0) := by
  simp only [drawDomF, Formula.realize_inf, realize_vDomF, realize_pinF]

theorem realize_drawDomF_extra {w : Fin 6 → A} :
    (drawDomF (Sum.inr ())).Realize w ↔
      (∀ y, w 0 ≤ y) ∧ w 1 = w 0 ∧ (w 2 = w 0 ∧ w 3 = w 0 ∧ w 4 = w 0 ∧ w 5 = w 0) := by
  simp only [drawDomF, Formula.realize_inf, realize_isMinF, realize_eqF, realize_pinF]

variable [Fintype A] [Nonempty A]

/-- The rungs of the ladder graph. -/
abbrev RungA (A : Type) [Language.sat.Structure A] [LinearOrder A] [Fintype A] [Nonempty A] :
    Type :=
  Rung 3 (widths (Λ := Level A) (attachedM (A := A)))

/-- A pair is a rung: two nodes, a level, and the index below the width. -/
def RungDom (t t' : VTag) (l : LevelTag) (j : Fin 3) (w : Fin 6 → A) : Prop :=
  VDom t (w 0) (w 1) ∧ VDom t' (w 2) (w 3) ∧ LevelDom l (w 4) (w 5) ∧
    ∀ (h : VDom t (w 0) (w 1)) (h' : VDom t' (w 2) (w 3)) (h'' : LevelDom l (w 4) (w 5)),
      j.val < widths (Λ := Level A) attachedM (vOf t (w 0) (w 1) h) (vOf t' (w 2) (w 3) h')
        (mkLevel l (w 4) (w 5) h'')

theorem realize_drawDomF_rung {t t' : VTag} {l : LevelTag} {j : Fin 3} {w : Fin 6 → A} :
    (drawDomF (Sum.inl (Sum.inr (t, t', l, j)))).Realize w ↔ RungDom t t' l j w := by
  simp only [drawDomF, Formula.realize_inf, realize_vDomF, realize_levelDomF, RungDom]
  constructor
  · rintro ⟨h, h', h'', hw⟩
    exact ⟨h, h', h'', fun _ _ _ => (realize_widthF h h' h'').mp hw⟩
  · rintro ⟨h, h', h'', hw⟩
    exact ⟨h, h', h'', (realize_widthF h h' h'').mpr (hw h h' h'')⟩

/-- The pair of a node, pinned into a `6`-tuple. -/
def pin (p : A × A) : Fin 6 → A :=
  ![p.1, p.2, p.1, p.1, p.1, p.1]

/-- The tuple of a rung. -/
noncomputable def rungTuple (q : RungA A) : Fin 6 → A :=
  ![(vPair q.src).1, (vPair q.src).2, (vPair q.tgt).1, (vPair q.tgt).2, q.lvl.1.2 0, q.lvl.1.2 1]

/-- The least element. -/
noncomputable def least : A := univ.min' univ_nonempty

/-- **The universe of the drawing**: the nodes and the rungs of the ladder
graph, and the extra node. -/
noncomputable def drawEquiv : drawInterp.MapRel A ≃ (V A ⊕ RungA A) ⊕ Unit where
  toFun p :=
    match p with
    | ⟨(Sum.inl (Sum.inl t), w), hw⟩ =>
        Sum.inl (Sum.inl (vOf t (w 0) (w 1) (realize_drawDomF_base.mp hw).1))
    | ⟨(Sum.inl (Sum.inr (t, t', l, j)), w), hw⟩ =>
        have h := realize_drawDomF_rung.mp hw
        Sum.inl (Sum.inr ⟨(vOf t (w 0) (w 1) h.1, vOf t' (w 2) (w 3) h.2.1,
          mkLevel l (w 4) (w 5) h.2.2.1, j), h.2.2.2 h.1 h.2.1 h.2.2.1⟩)
    | ⟨(Sum.inr (), _), _⟩ => Sum.inr ()
  invFun y :=
    match y with
    | Sum.inl (Sum.inl n) => ⟨(Sum.inl (Sum.inl (vTag n)), pin (vPair n)), by
        change (drawDomF (Sum.inl (Sum.inl (vTag n)))).Realize (pin (vPair n))
        rw [realize_drawDomF_base]
        exact ⟨vDom_vTag n, rfl, rfl, rfl, rfl⟩⟩
    | Sum.inl (Sum.inr q) => ⟨(Sum.inl (Sum.inr (vTag q.src, vTag q.tgt, q.lvl.1.1, q.idx)),
        rungTuple q), by
        change (drawDomF (Sum.inl (Sum.inr (vTag q.src, vTag q.tgt, q.lvl.1.1, q.idx)))).Realize
          (rungTuple q)
        rw [realize_drawDomF_rung]
        refine ⟨vDom_vTag q.src, vDom_vTag q.tgt, levelDom_of q.lvl, fun h h' h'' => ?_⟩
        change q.idx.val < widths attachedM (vOf (vTag q.src) (vPair q.src).1
          (vPair q.src).2 h) (vOf (vTag q.tgt) (vPair q.tgt).1 (vPair q.tgt).2 h')
          (mkLevel q.lvl.1.1 (q.lvl.1.2 0) (q.lvl.1.2 1) h'')
        rw [vOf_vTag, vOf_vTag, mkLevel_eq]
        exact q.2⟩
    | Sum.inr () => ⟨(Sum.inr (), fun _ => least), by
        change (drawDomF (Sum.inr ())).Realize fun _ => least
        rw [realize_drawDomF_extra]
        exact ⟨fun y => min'_le _ _ (mem_univ y), rfl, rfl, rfl, rfl, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨(t | ⟨t, t', l, j⟩) | ⟨⟩, w⟩, hw⟩
    · obtain ⟨-, h2, h3, h4, h5⟩ := realize_drawDomF_base.mp hw
      refine Subtype.ext (Prod.ext ?_ (funext fun i => ?_))
      · change Sum.inl (Sum.inl (vTag (vOf t (w 0) (w 1) _))) = Sum.inl (Sum.inl t)
        rw [vTag_vOf]
      change pin (vPair (vOf t (w 0) (w 1) _)) i = w i
      rw [vPair_vOf]
      fin_cases i
      · rfl
      · rfl
      · exact h2.symm
      · exact h3.symm
      · exact h4.symm
      · exact h5.symm
    · have h := realize_drawDomF_rung.mp hw
      refine Subtype.ext (Prod.ext ?_ (funext fun i => ?_))
      · change Sum.inl (Sum.inr (vTag (vOf t (w 0) (w 1) h.1), vTag (vOf t' (w 2) (w 3) h.2.1),
          (mkLevel l (w 4) (w 5) h.2.2.1).1.1, j)) = _
        rw [vTag_vOf, vTag_vOf]
        rfl
      · change rungTuple ⟨(vOf t (w 0) (w 1) h.1, vOf t' (w 2) (w 3) h.2.1,
          mkLevel l (w 4) (w 5) h.2.2.1, j), h.2.2.2 h.1 h.2.1 h.2.2.1⟩ i = w i
        simp only [rungTuple, Rung.src, Rung.tgt, Rung.lvl, vPair_vOf, mkLevel]
        fin_cases i <;> rfl
    · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := realize_drawDomF_extra.mp hw
      have hl : w 0 = least := le_antisymm (h0 _) (min'_le _ _ (mem_univ _))
      refine Subtype.ext (Prod.ext rfl (funext fun i => ?_))
      change least = w i
      fin_cases i
      · exact hl.symm
      · exact (h1.trans hl).symm
      · exact (h2.trans hl).symm
      · exact (h3.trans hl).symm
      · exact (h4.trans hl).symm
      · exact (h5.trans hl).symm
  right_inv := by
    rintro ((n | q) | ⟨⟩)
    · change Sum.inl (Sum.inl (vOf (vTag n) (vPair n).1 (vPair n).2 _)) = _
      rw [vOf_vTag]
    · refine congrArg (fun q => Sum.inl (Sum.inr q)) (Rung.ext ?_ ?_ ?_ rfl)
      · exact vOf_vTag q.src
      · exact vOf_vTag q.tgt
      · exact mkLevel_eq q.lvl
    · rfl

/-! ### The arcs -/

omit [LinearOrder A] [Fintype A] [Nonempty A] in
/-- A node of the attached graph is determined by its tag and its pair. -/
theorem vOf_eq_iff {t t' : VTag} {c x c' x' : A} (h : VDom t c x) (h' : VDom t' c' x') :
    vOf t c x h = vOf t' c' x' h' ↔ t = t' ∧ (c, x) = (c', x') := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · rw [← vTag_vOf t c x h, he, vTag_vOf]
    · rw [← vPair_vOf t c x h, he, vPair_vOf]
  · rintro ⟨rfl, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    rfl

omit [Fintype A] [Nonempty A] in
/-- A level is determined by its tag and its pair. -/
theorem mkLevel_eq_iff {t t' : LevelTag} {c x c' x' : A} (h : LevelDom t c x)
    (h' : LevelDom t' c' x') :
    mkLevel t c x h = mkLevel t' c' x' h' ↔ t = t' ∧ (c, x) = (c', x') := by
  constructor
  · intro he
    have h1 := congrArg (fun ℓ : Level A => ℓ.1.1) he
    have h2 := congrArg (fun ℓ : Level A => ℓ.1.2) he
    exact ⟨h1, Prod.ext (congrFun h2 0) (congrFun h2 1)⟩
  · rintro ⟨rfl, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    rfl

omit [LinearOrder A] [Fintype A] [Nonempty A] in
/-- A node of the attached graph is determined by its tag and its pair. -/
theorem v_eq_iff (n n' : V A) : n = n' ↔ vTag n = vTag n' ∧ vPair n = vPair n' := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← vOf_vTag n, ← vOf_vTag n']
    exact (vOf_eq_iff _ _).mpr ⟨h1, h2⟩

/-- The edge relation of the drawing, read on the nodes and the rungs. -/
def DrawEdge (y y' : (V A ⊕ RungA A) ⊕ Unit) : Prop :=
  match y, y' with
  | Sum.inl a, Sum.inl b => LadderEdge 3 (widths attachedM) a b
  | Sum.inr (), Sum.inr () => True
  | _, _ => False

theorem drawEquiv_symm_node (n : V A) :
    (drawEquiv.symm (Sum.inl (Sum.inl n)) : drawInterp.MapRel A).1 =
      (Sum.inl (Sum.inl (vTag n)), pin (vPair n)) :=
  rfl

theorem drawEquiv_symm_rung (q : RungA A) :
    (drawEquiv.symm (Sum.inl (Sum.inr q)) : drawInterp.MapRel A).1 =
      (Sum.inl (Sum.inr (vTag q.src, vTag q.tgt, q.lvl.1.1, q.idx)), rungTuple q) :=
  rfl

/-- **The arcs of the drawing are the edges of the ladder graph**, and the
self-loop of the extra node. -/
theorem drawArc_iff (y y' : (V A ⊕ RungA A) ⊕ Unit) :
    DGArc (drawEquiv.symm y) (drawEquiv.symm y') ↔ DrawEdge y y' := by
  rw [DGArc, RelFOInterpretation.relMap_mapRel]
  rcases y with (n | q) | ⟨⟩ <;> rcases y' with (n' | q') | ⟨⟩
  · change (drawArcF (Sum.inl (Sum.inl (vTag n))) (Sum.inl (Sum.inl (vTag n')))).Realize _ ↔ _
    exact iff_of_false (by simp [drawArcF]) (ladderEdge_inl_inl _ _)
  · -- node to rung
    set v : Fin 2 × Fin 6 → A := fun pr =>
      ((![drawEquiv.symm (Sum.inl (Sum.inl n)), drawEquiv.symm (Sum.inl (Sum.inr q'))] :
        Fin 2 → drawInterp.MapRel A) pr.1).1.2 pr.2 with hv
    change (drawArcF (Sum.inl (Sum.inl (vTag n)))
      (Sum.inl (Sum.inr (vTag q'.src, vTag q'.tgt, q'.lvl.1.1, q'.idx)))).Realize v ↔
      LadderEdge 3 (widths attachedM) (Sum.inl n) (Sum.inr q')
    rw [ladderEdge_inl_inr]
    simp only [drawArcF]
    split_ifs with ht
    · rw [Formula.realize_inf, Formula.realize_inf, realize_eqF, realize_eqF,
        realize_levelMinF (v := v) (c := (1, 4)) (x := (1, 5)) (levelDom_of q'.lvl)]
      change (vPair n).1 = (vPair q'.src).1 ∧ (vPair n).2 = (vPair q'.src).2 ∧
        mkLevel q'.lvl.1.1 (q'.lvl.1.2 0) (q'.lvl.1.2 1) (levelDom_of q'.lvl) = ⊥ ↔
        q'.src = n ∧ q'.lvl = ⊥
      rw [mkLevel_eq]
      rw [v_eq_iff, ← ht]
      simp only [true_and]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨Prod.ext h1.symm h2.symm, h3⟩,
        fun ⟨h12, h3⟩ => ⟨(congrArg Prod.fst h12).symm, (congrArg Prod.snd h12).symm, h3⟩⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      intro he
      exact absurd (congrArg vTag he).symm ht
  · change (drawArcF (Sum.inl (Sum.inl (vTag n))) (Sum.inr ())).Realize _ ↔ _
    exact iff_of_false (by simp [drawArcF]) (by simp [DrawEdge])
  · -- rung to node
    set v : Fin 2 × Fin 6 → A := fun pr =>
      ((![drawEquiv.symm (Sum.inl (Sum.inr q)), drawEquiv.symm (Sum.inl (Sum.inl n'))] :
        Fin 2 → drawInterp.MapRel A) pr.1).1.2 pr.2 with hv
    change (drawArcF (Sum.inl (Sum.inr (vTag q.src, vTag q.tgt, q.lvl.1.1, q.idx)))
      (Sum.inl (Sum.inl (vTag n')))).Realize v ↔
      LadderEdge 3 (widths attachedM) (Sum.inr q) (Sum.inl n')
    rw [ladderEdge_inr_inl]
    simp only [drawArcF]
    split_ifs with ht
    · rw [Formula.realize_inf, Formula.realize_inf, realize_eqF, realize_eqF,
        realize_levelMaxF (v := v) (c := (0, 4)) (x := (0, 5)) (levelDom_of q.lvl)]
      change (vPair q.tgt).1 = (vPair n').1 ∧ (vPair q.tgt).2 = (vPair n').2 ∧
        mkLevel q.lvl.1.1 (q.lvl.1.2 0) (q.lvl.1.2 1) (levelDom_of q.lvl) = ⊤ ↔
        q.tgt = n' ∧ q.lvl = ⊤
      rw [mkLevel_eq]
      rw [v_eq_iff, ht]
      simp only [true_and]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨Prod.ext h1 h2, h3⟩,
        fun ⟨h12, h3⟩ => ⟨congrArg Prod.fst h12, congrArg Prod.snd h12, h3⟩⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      intro he
      exact absurd (congrArg vTag he) ht
  · -- rung to rung
    set v : Fin 2 × Fin 6 → A := fun pr =>
      ((![drawEquiv.symm (Sum.inl (Sum.inr q)), drawEquiv.symm (Sum.inl (Sum.inr q'))] :
        Fin 2 → drawInterp.MapRel A) pr.1).1.2 pr.2 with hv
    change (drawArcF (Sum.inl (Sum.inr (vTag q.src, vTag q.tgt, q.lvl.1.1, q.idx)))
      (Sum.inl (Sum.inr (vTag q'.src, vTag q'.tgt, q'.lvl.1.1, q'.idx)))).Realize v ↔
      LadderEdge 3 (widths attachedM) (Sum.inr q) (Sum.inr q')
    rw [ladderEdge_inr_inr]
    simp only [drawArcF, Formula.realize_sup]
    rw [realize_ite_bot, realize_ite_bot, Formula.realize_iInf]
    simp only [realize_eqF, Formula.realize_inf]
    rw [realize_levelCovF (v := v) (c := (0, 4)) (x := (0, 5)) (c' := (1, 4)) (x' := (1, 5))
      (levelDom_of q.lvl) (levelDom_of q'.lvl)]
    change ((vTag q.src, vTag q.tgt, q.lvl.1.1, q.idx) =
        (vTag q'.src, vTag q'.tgt, q'.lvl.1.1, q'.idx) ∧ ∀ i, rungTuple q i = rungTuple q' i) ∨
      ((vTag q.src = vTag q'.src ∧ vTag q.tgt = vTag q'.tgt) ∧
        (vPair q.src).1 = (vPair q'.src).1 ∧ (vPair q.src).2 = (vPair q'.src).2 ∧
        (vPair q.tgt).1 = (vPair q'.tgt).1 ∧ (vPair q.tgt).2 = (vPair q'.tgt).2 ∧
        mkLevel q.lvl.1.1 (q.lvl.1.2 0) (q.lvl.1.2 1) (levelDom_of q.lvl) ⋖
          mkLevel q'.lvl.1.1 (q'.lvl.1.2 0) (q'.lvl.1.2 1) (levelDom_of q'.lvl)) ↔ _
    rw [mkLevel_eq, mkLevel_eq]
    constructor
    · rintro (⟨htags, hw⟩ | ⟨⟨hs, ht⟩, h0, h1, h2, h3, hc⟩)
      · left
        obtain ⟨hs, ht, hl, hj⟩ := Prod.mk.inj htags |>.imp_right (Prod.mk.inj · |>.imp_right
          Prod.mk.inj)
        refine Rung.ext ((v_eq_iff _ _).mpr ⟨hs, Prod.ext (hw 0) (hw 1)⟩)
          ((v_eq_iff _ _).mpr ⟨ht, Prod.ext (hw 2) (hw 3)⟩) ?_ hj
        exact Subtype.ext (Prod.ext hl (funext fun i => by
          fin_cases i
          · exact hw 4
          · exact hw 5))
      · right
        exact ⟨(v_eq_iff _ _).mpr ⟨hs, Prod.ext h0 h1⟩, (v_eq_iff _ _).mpr ⟨ht, Prod.ext h2 h3⟩, hc⟩
    · rintro (rfl | ⟨hs, ht, hc⟩)
      · left
        exact ⟨rfl, fun _ => rfl⟩
      · right
        exact ⟨⟨congrArg vTag hs, congrArg vTag ht⟩, congrArg (fun n => (vPair n).1) hs,
          congrArg (fun n => (vPair n).2) hs, congrArg (fun n => (vPair n).1) ht,
          congrArg (fun n => (vPair n).2) ht, hc⟩
  · change (drawArcF (Sum.inl (Sum.inr (vTag q.src, vTag q.tgt, q.lvl.1.1, q.idx)))
      (Sum.inr ())).Realize _ ↔ _
    exact iff_of_false (by simp [drawArcF]) (by simp [DrawEdge])
  · change (drawArcF (Sum.inr ()) (Sum.inl (Sum.inl (vTag n')))).Realize _ ↔ _
    exact iff_of_false (by simp [drawArcF]) (by simp [DrawEdge])
  · change (drawArcF (Sum.inr ()) (Sum.inl (Sum.inr (vTag q'.src, vTag q'.tgt, q'.lvl.1.1,
      q'.idx)))).Realize _ ↔ _
    exact iff_of_false (by simp [drawArcF]) (by simp [DrawEdge])
  · change (drawArcF (Sum.inr ()) (Sum.inr ())).Realize _ ↔ _
    exact iff_of_true (by simp [drawArcF]) trivial

end Draw

end SatCover

end DescriptiveComplexity
