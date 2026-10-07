/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ThreeColorability.CountGadget
import DescriptiveComplexity.Problems.ThreeColorability.Counting
import DescriptiveComplexity.Problems.Sat.CountingHardness
import DescriptiveComplexity.OccurrenceFormulas
import DescriptiveComplexity.OccurrencePrefix
import DescriptiveComplexity.Counting.Reduction

/-!
# #3-Colorability is one-call `#P`-complete

The gadget graph of `DescriptiveComplexity.Problems.ThreeColorability.CountGadget`,
drawn over the ordered expansion of a CNF formula
(`DescriptiveComplexity.SatToColCount.drawInterp`): its universe is the set of
vertices of the gadget graph (`DescriptiveComplexity.SatToColCount.drawEquiv`),
its edges those of the gadget graph read in both directions. The number of
proper 3-colorings is `6 · 8 ^ g` times the number of models, `g` the number of
non-first occurrences, a definable cardinality: one division recovers #SAT
(`DescriptiveComplexity.sharpSat_oneCall_sharpThreeCol`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

namespace SatToColCount

/-! ### Tags -/

/-- The tags of the drawing. -/
inductive CTag : Type
  /-- A palette vertex, at the pair of least elements. -/
  | pal (p : Pal)
  /-- The literal of sign `s` of a variable `x`, at `(x, x)`. -/
  | lit (s : Bool)
  /-- The Boolean vertex of polarity `b` of the gate of the occurrence of sign
  `s` of `x` in `c`, at `(c, x)`. -/
  | gate (s b : Bool)
  /-- The spoiler of an empty clause `c`, at `(c, c)`. -/
  | spoil
  /-- The vertex `r` of the triangle `j` of the gate of the occurrence of sign
  `s` of `x` in `c`, at `(c, x)`. -/
  | tri (s : Bool) (j r : Fin 3)
  deriving DecidableEq

/-- The tags, as a sum type. -/
def CTag.code : CTag → Pal ⊕ Bool ⊕ (Bool × Bool) ⊕ Unit ⊕ (Bool × Fin 3 × Fin 3)
  | .pal p => Sum.inl p
  | .lit s => Sum.inr (Sum.inl s)
  | .gate s b => Sum.inr (Sum.inr (Sum.inl (s, b)))
  | .spoil => Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))
  | .tri s j r => Sum.inr (Sum.inr (Sum.inr (Sum.inr (s, j, r))))

theorem CTag.code_injective : Function.Injective CTag.code := by
  intro t t' h
  cases t <;> cases t' <;> simp_all [CTag.code]

instance : Finite CTag := Finite.of_injective _ CTag.code_injective

/-! ### Points -/

section Points

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The pair `(c, x)` is a point of tag `t`. -/
def CDom : CTag → A → A → Prop
  | .pal _, c, x => (∀ y, c ≤ y) ∧ x = c
  | .lit _, c, x => x = c ∧ SatOccurs A c
  | .gate s _, c, x => Chained c x s
  | .spoil, c, x => x = c ∧ EmptyCl c
  | .tri s _ _, c, x => Chained c x s

/-- The vertex of the gadget graph a point denotes. -/
def vOf : (t : CTag) → (c x : A) → CDom t c x → V A
  | .pal p, _, _, _ => Sum.inl (Sum.inl p)
  | .lit s, c, _, h => Sum.inl (bvV (Sum.inl ⟨c, h.2⟩, s))
  | .gate s b, c, x, h => Sum.inl (bvV (Sum.inr ⟨(c, x, s), h⟩, b))
  | .spoil, c, _, h => Sum.inl (spV ⟨c, h.2⟩)
  | .tri s j r, c, x, h => Sum.inr (⟨(c, x, s), h⟩, j, r)

/-- The tag of a vertex. -/
def vTag : V A → CTag
  | Sum.inl (Sum.inl p) => .pal p
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl _, s))) => .lit s
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr g, b))) => .gate g.1.2.2 b
  | Sum.inl (Sum.inr (Sum.inr _)) => .spoil
  | Sum.inr (g, j, r) => .tri g.1.2.2 j r

theorem vTag_vOf (t : CTag) (c x : A) (h : CDom t c x) : vTag (vOf t c x h) = t := by
  cases t <;> rfl

variable [Fintype A] [Nonempty A]

/-- The least element. -/
noncomputable def least : A := Finset.univ.min' Finset.univ_nonempty

omit [Language.sat.Structure A] in
theorem least_le (a : A) : least ≤ a := Finset.min'_le _ _ (Finset.mem_univ a)

/-- The pair a vertex is drawn as. -/
noncomputable def vPair : V A → A × A
  | Sum.inl (Sum.inl _) => (least, least)
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl x, _))) => (x.1, x.1)
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr g, _))) => (g.1.1, g.1.2.1)
  | Sum.inl (Sum.inr (Sum.inr c)) => (c.1, c.1)
  | Sum.inr (g, _, _) => (g.1.1, g.1.2.1)

theorem cDom_vTag (n : V A) : CDom (vTag n) (vPair n).1 (vPair n).2 := by
  rcases n with (p | (⟨x | g, s⟩ | c)) | ⟨g, j, r⟩
  · exact ⟨least_le, rfl⟩
  · exact ⟨rfl, x.2⟩
  · exact g.2
  · exact ⟨rfl, c.2⟩
  · exact g.2

theorem vOf_vTag (n : V A) : vOf (vTag n) (vPair n).1 (vPair n).2 (cDom_vTag n) = n := by
  rcases n with (p | (⟨x | g, s⟩ | c)) | ⟨g, j, r⟩ <;> rfl

theorem vPair_vOf (t : CTag) (c x : A) (h : CDom t c x) : vPair (vOf t c x h) = (c, x) := by
  cases t with
  | pal p =>
    have hc : least = c := le_antisymm (least_le c) (h.1 _)
    change (least, least) = (c, x)
    rw [h.2, hc]
  | lit s => exact Prod.ext rfl h.1.symm
  | gate s b => rfl
  | spoil => exact Prod.ext rfl h.1.symm
  | tri s j r => rfl

end Points

/-! ### The formulas -/

section Formulas

variable {α : Type}

/-- `x` is a variable of the formula. -/
noncomputable def occursF (x : α) : satOrd.Formula α :=
  fo%[x] ∃ c, clF⟨c⟩ ∧ (posF⟨c, x⟩ ∨ negF⟨c, x⟩)

/-- `c` is the least element. -/
noncomputable def isMinF (c : α) : satOrd.Formula α :=
  fo%[c] ∀ y, leF⟨c, y⟩

/-- The domain of each tag. -/
noncomputable def domF : CTag → satOrd.Formula (Fin 2)
  | .pal _ => isMinF 0 ⊓ eqF 1 0
  | .lit _ => eqF 1 0 ⊓ occursF 0
  | .gate s _ => chainedF s 0 1
  | .spoil => eqF 1 0 ⊓ emptyClF 0
  | .tri s _ _ => chainedF s 0 1

/-- What a triangle vertex is attached to. -/
inductive OKind : Type
  /-- The gate output. -/
  | z
  /-- The negated predecessor. -/
  | negP
  /-- The negated literal. -/
  | negL
  /-- The palette `F`. -/
  | palF

/-- What the vertex `r` of the triangle `j` of a gate is attached to. -/
def outerKind : Fin 3 → Fin 3 → OKind :=
  ![![.z, .negP, .negL], ![.negP, .z, .palF], ![.negL, .z, .palF] ]

/-- The point of tag `t'` at `(1, ·)` is what a triangle vertex of the gate
of sign `s` at `(0, ·)` is attached to, of kind `k`. -/
noncomputable def outerF (s : Bool) : OKind → CTag → satOrd.Formula (Fin 2 × Fin 2)
  | .z, .gate s' b' => if s' = s ∧ b' = true then eqF (1, 0) (0, 0) ⊓ eqF (1, 1) (0, 1) else ⊥
  | .negP, .lit u => succOccF (!u) s (0, 0) (1, 0) (0, 1) ⊓ minOccF (!u) (0, 0) (1, 0)
  | .negP, .gate t b' => if b' = false then eqF (1, 0) (0, 0) ⊓ succOccF t s (0, 0) (1, 1) (0, 1)
      else ⊥
  | .negL, .lit u => if u = !s then eqF (1, 0) (0, 1) else ⊥
  | .palF, .pal .F => ⊤
  | _, _ => ⊥

/-- **The edges, in one direction**, between the point of tag `t` at `(0, ·)`
and the point of tag `t'` at `(1, ·)`. -/
noncomputable def dirF : CTag → CTag → satOrd.Formula (Fin 2 × Fin 2)
  | .pal p, .pal q => if p = q then ⊥ else ⊤
  | .lit s, .lit s' => if s' = !s then eqF (0, 0) (1, 0) else ⊥
  | .gate s b, .gate s' b' =>
      if s = s' ∧ b' = !b then eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1) else ⊥
  | .lit _, .pal .B => ⊤
  | .gate _ _, .pal .B => ⊤
  | .lit t, .pal .F => unitLitF t (0, 0)
  | .gate s b, .pal .F => if b then maxOccF s (0, 0) (0, 1) else ⊥
  | .spoil, .pal _ => ⊤
  | .tri s j r, .tri s' j' r' =>
      if s = s' ∧ j = j' ∧ r ≠ r' then eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1) else ⊥
  | .tri s j r, t' => outerF s (outerKind j r) t'
  | _, _ => ⊥

end Formulas

/-! ### Realization -/

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

theorem realize_occursF {x : α} : (occursF x).Realize v ↔ SatOccurs A (v x) := by
  simp only [occursF, Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup, realize_clF,
    realize_posF, realize_negF, Sum.elim_inl, Sum.elim_inr, SatOccurs, IsCl, PosIn, NegIn]
  exact ⟨fun ⟨c, h⟩ => ⟨c 0, h⟩, fun ⟨c, h⟩ => ⟨fun _ => c, h⟩⟩

theorem realize_isMinF {c : α} : (isMinF c).Realize v ↔ ∀ y, v c ≤ y := by
  simp only [isMinF, Formula.realize_iAlls, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h y => h fun _ => y, fun h y => h (y 0)⟩

theorem realize_domF (t : CTag) (w : Fin 2 → A) : (domF t).Realize w ↔ CDom t (w 0) (w 1) := by
  cases t <;>
    simp [domF, CDom, realize_isMinF, realize_eqF, realize_occursF, realize_chainedF,
      realize_emptyClF, Chained]

variable [Finite A]

/-- The negated predecessor of a gate is a literal exactly when the
predecessor is the first occurrence. -/
theorem negPred_eq_lit (g : Gate A) {y : A} (hy : SatOccurs A y) (u : Bool) :
    negPred g = bvV (Sum.inl ⟨y, hy⟩, u) ↔
      SuccOcc g.1.1 y (!u) g.1.2.1 g.1.2.2 ∧ MinOcc g.1.1 y (!u) := by
  have hs := pred_spec g
  unfold negPred
  by_cases hm : MinOcc g.1.1 (pred g).1 (pred g).2
  · rw [prefixBv_of_min hs.1 hm]
    simp only [bvV, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      rw [Bool.not_not]
      exact ⟨hs, hm⟩
    · rintro ⟨hsu, -⟩
      obtain ⟨h1, h2⟩ := succOcc_left_unique hs hsu
      exact ⟨h1, by rw [h2, Bool.not_not]⟩
  · rw [prefixBv_of_chained (⟨hs.1, hm⟩ : Chained _ _ _)]
    simp only [bvV, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, false_and,
      false_iff, not_and]
    intro hsu hmin
    obtain ⟨h1, h2⟩ := succOcc_left_unique hs hsu
    exact hm (h1 ▸ h2 ▸ hmin)

/-- The negated predecessor of a gate is the negated output of another gate
exactly when the predecessor is that gate's occurrence. -/
theorem negPred_eq_gate (g : Gate A) {c y : A} {t : Bool} (h : Chained c y t) (b : Bool) :
    negPred g = bvV (Sum.inr ⟨(c, y, t), h⟩, b) ↔
      b = false ∧ c = g.1.1 ∧ SuccOcc g.1.1 y t g.1.2.1 g.1.2.2 := by
  have hs := pred_spec g
  unfold negPred
  by_cases hm : MinOcc g.1.1 (pred g).1 (pred g).2
  · rw [prefixBv_of_min hs.1 hm]
    simp only [bvV, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, false_and,
      false_iff, not_and]
    rintro - rfl hsu
    obtain ⟨h1, h2⟩ := succOcc_left_unique hs hsu
    exact h.2 (h1 ▸ h2 ▸ hm)
  · rw [prefixBv_of_chained (⟨hs.1, hm⟩ : Chained _ _ _)]
    simp only [bvV, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, Bool.not_true]
    constructor
    · rintro ⟨hg, h4⟩
      have hv := congrArg Subtype.val hg
      simp only [Prod.mk.injEq] at hv
      obtain ⟨h1, h2, h3⟩ := hv
      refine ⟨h4.symm, h1.symm, ?_⟩
      rw [← h2, ← h3]
      exact hs
    · rintro ⟨rfl, rfl, hsu⟩
      obtain ⟨h1, h2⟩ := succOcc_left_unique hs hsu
      refine ⟨Subtype.ext ?_, rfl⟩
      simp only [h1, h2]

omit [Finite A] in
theorem prefixBv_eq_lit {c x : A} {s : Bool} (h : OccIn c x s) {y : A} (hy : SatOccurs A y)
    (t : Bool) : prefixBv h = (Sum.inl ⟨y, hy⟩, t) ↔ MinOcc c x s ∧ x = y ∧ s = t := by
  by_cases hm : MinOcc c x s
  · rw [prefixBv_of_min h hm]
    simp only [Prod.mk.injEq, Sum.inl.injEq, Subtype.mk.injEq, hm, true_and]
  · rw [prefixBv_of_chained (⟨h, hm⟩ : Chained c x s)]
    simp [hm]

omit [Finite A] in
theorem prefixBv_eq_gate {c x : A} {s : Bool} (h : OccIn c x s) {c' x' : A} {s' : Bool}
    (h' : Chained c' x' s') (b : Bool) :
    prefixBv h = (Sum.inr ⟨(c', x', s'), h'⟩, b) ↔ ¬MinOcc c x s ∧ (c, x, s) = (c', x', s') ∧
      b = true := by
  by_cases hm : MinOcc c x s
  · rw [prefixBv_of_min h hm]
    simp [hm]
  · rw [prefixBv_of_chained (⟨h, hm⟩ : Chained c x s)]
    simp only [Prod.mk.injEq, Sum.inr.injEq, Subtype.ext_iff, hm, not_false_eq_true,
      true_and]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩

/-- The core vertex of a kind of attachment. -/
noncomputable def kindV (g : Gate A) : OKind → Core A
  | .z => zV g
  | .negP => negPred g
  | .negL => negLit g
  | .palF => palV .F

theorem outer_kind (g : Gate A) (j r : Fin 3) : outer g j r = kindV g (outerKind j r) := by
  fin_cases j <;> fin_cases r <;> rfl

/-- **The attachment formulas define the attachments of the triangles.** -/
theorem realize_outerF (s : Bool) {v : Fin 2 × Fin 2 → A} (k : OKind) (t' : CTag)
    (h : Chained (v (0, 0)) (v (0, 1)) s) (h' : CDom t' (v (1, 0)) (v (1, 1))) :
    (outerF s k t').Realize v ↔
      vOf t' _ _ h' = Sum.inl (kindV ⟨(v (0, 0), v (0, 1), s), h⟩ k) := by
  cases k <;> rcases t' with q | u | ⟨u, b'⟩ | _ | ⟨u, j', r'⟩
  -- the gate output
  · simp [outerF, vOf, kindV, zV]
  · simp [outerF, vOf, kindV, zV]
  · simp only [outerF, vOf, kindV, zV, bvV, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      Subtype.ext_iff]
    split_ifs with hub
    · rw [Formula.realize_inf, realize_eqF, realize_eqF]
      exact ⟨fun he => ⟨⟨he.1, he.2, hub.1⟩, hub.2⟩, fun he => ⟨he.1.1, he.1.2.1⟩⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      exact fun he hb => hub ⟨he.2.2, hb⟩
  · simp [outerF, vOf, kindV, zV]
  · simp [outerF, vOf, kindV, zV]
  -- the negated predecessor
  · simp [outerF, vOf, kindV, negPred]
  · change _ ↔ Sum.inl (bvV (Sum.inl ⟨v (1, 0), h'.2⟩, u)) = Sum.inl (negPred _)
    rw [Sum.inl.injEq, eq_comm, negPred_eq_lit]
    simp only [outerF, Formula.realize_inf, realize_succOccF, realize_minOccF]
  · change _ ↔ Sum.inl (bvV (Sum.inr ⟨(v (1, 0), v (1, 1), u), h'⟩, b')) = Sum.inl (negPred _)
    rw [Sum.inl.injEq, eq_comm]
    refine Iff.trans ?_ (negPred_eq_gate _ (h' : Chained _ _ _) b').symm
    simp only [outerF]
    split_ifs with hb
    · rw [Formula.realize_inf, realize_eqF, realize_succOccF]
      exact ⟨fun he => ⟨hb, he.1, he.2⟩, fun he => ⟨he.2.1, he.2.2⟩⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      exact fun h1 => absurd h1 hb
  · simp [outerF, vOf, kindV, negPred]
  · simp [outerF, vOf]
  -- the negated literal
  · simp [outerF, vOf, kindV, negLit]
  · simp only [outerF, vOf, kindV, negLit, bvV, Sum.inl.injEq, Sum.inr.injEq,
      Subtype.mk.injEq, Prod.mk.injEq]
    split_ifs with hu
    · rw [realize_eqF]
      exact ⟨fun he => ⟨he, hu⟩, fun he => he.1⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      exact fun _ h2 => hu h2
  · simp [outerF, vOf, kindV, negLit]
  · simp [outerF, vOf, kindV, negLit]
  · simp [outerF, vOf]
  -- the palette `F`
  · cases q <;> simp [outerF, vOf, kindV]
  · simp [outerF, vOf, kindV]
  · simp [outerF, vOf, kindV]
  · simp [outerF, vOf, kindV]
  · simp [outerF, vOf]

/-- **The edge formulas define the edges of the gadget graph.** -/
theorem realize_dirF (t t' : CTag) {v : Fin 2 × Fin 2 → A} (h : CDom t (v (0, 0)) (v (0, 1)))
    (h' : CDom t' (v (1, 0)) (v (1, 1))) :
    (dirF t t').Realize v ↔ E (vOf t _ _ h) (vOf t' _ _ h') := by
  rcases t with p | s | ⟨s, b⟩ | _ | ⟨s, j, r⟩ <;>
    rcases t' with q | u | ⟨u, b'⟩ | _ | ⟨u, j', r'⟩
  all_goals try (simp [dirF, vOf, E, CoreE, outerF]; done)
  · -- palette, palette
    cases p <;> cases q <;> simp [dirF, vOf, E, CoreE]
  · -- literal, palette
    cases q
    · simp [dirF, vOf, E, CoreE]
    · change (unitLitF s (0, 0)).Realize v ↔ ∃ (c x : A) (t : Bool) (hm : MaxOcc c x t), _
      rw [realize_unitLitF]
      constructor
      · rintro ⟨c, hmin, hmax⟩
        exact ⟨c, _, _, hmax, ((prefixBv_eq_lit hmax.1 _ _).mpr ⟨hmin, rfl, rfl⟩).symm⟩
      · rintro ⟨c, x, t, hmax, he⟩
        obtain ⟨hmin, rfl, rfl⟩ := (prefixBv_eq_lit hmax.1 _ _).mp he.symm
        exact ⟨c, hmin, hmax⟩
    · simp [dirF, vOf, E, CoreE]
  · -- literal, literal
    simp only [dirF, vOf, E, CoreE, bvV, Sum.inl.injEq, Subtype.mk.injEq]
    split_ifs with hu
    · rw [realize_eqF]
      exact ⟨fun he => ⟨he, hu⟩, fun he => he.1⟩
    · simp [hu]
  · -- gate, palette
    cases q
    · simp [dirF, vOf, E, CoreE]
    · change (if b then maxOccF s (0, 0) (0, 1) else ⊥).Realize v ↔
        ∃ (c x : A) (t : Bool) (hm : MaxOcc c x t), _
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, Formula.realize_bot, false_iff, not_exists]
        intro c x t hm he
        exact Bool.false_ne_true ((prefixBv_eq_gate hm.1 h false).mp he.symm).2.2
      · rw [ite_eq_left rfl, realize_maxOccF]
        constructor
        · intro hm
          exact ⟨_, _, _, hm, ((prefixBv_eq_gate hm.1 h true).mpr ⟨h.2, rfl, rfl⟩).symm⟩
        · rintro ⟨c, x, t, hm, he⟩
          obtain ⟨-, he', -⟩ := (prefixBv_eq_gate hm.1 h true).mp he.symm
          simp only [Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl, rfl⟩ := he'
          exact hm
    · simp [dirF, vOf, E, CoreE]
  · -- gate, gate
    simp only [dirF, vOf, E, CoreE, bvV, Sum.inr.injEq, Subtype.ext_iff, Prod.mk.injEq]
    split_ifs with hsb
    · rw [Formula.realize_inf, realize_eqF, realize_eqF]
      exact ⟨fun he => ⟨⟨he.1, he.2, hsb.1⟩, hsb.2⟩, fun he => ⟨he.1.1, he.1.2.1⟩⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      exact fun h1 h2 => hsb ⟨h1.2.2, h2⟩
  · -- triangle, palette
    exact (realize_outerF s _ (.pal q) h h').trans (by
      change Sum.inl _ = Sum.inl _ ↔ _ = outer _ j r
      rw [Sum.inl.injEq, outer_kind, eq_comm])
  · -- triangle, literal
    exact (realize_outerF s _ (.lit u) h h').trans (by
      change Sum.inl _ = Sum.inl _ ↔ _ = outer _ j r
      rw [Sum.inl.injEq, outer_kind, eq_comm])
  · -- triangle, gate
    exact (realize_outerF s _ (.gate u b') h h').trans (by
      change Sum.inl _ = Sum.inl _ ↔ _ = outer _ j r
      rw [Sum.inl.injEq, outer_kind, eq_comm])
  · -- triangle, spoil
    exact (realize_outerF s _ .spoil h h').trans (by
      change Sum.inl _ = Sum.inl _ ↔ _ = outer _ j r
      rw [Sum.inl.injEq, outer_kind, eq_comm])
  · -- triangle, triangle
    simp only [dirF, vOf, E, Subtype.ext_iff, Prod.mk.injEq]
    split_ifs with hsjr
    · rw [Formula.realize_inf, realize_eqF, realize_eqF]
      exact ⟨fun he => ⟨⟨he.1, he.2, hsjr.1⟩, hsjr.2.1, hsjr.2.2⟩,
        fun he => ⟨he.1.1, he.1.2.1⟩⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      exact fun h1 h2 h3 => hsjr ⟨h1.2.2, h2, h3⟩

end Realize

/-! ### The drawing -/

/-- Exchanging the two points of an edge formula. -/
def swapPt (p : Fin 2 × Fin 2) : Fin 2 × Fin 2 := (Fin.rev p.1, p.2)

/-- **The drawing of the gadget graph**: the edges in both directions. -/
noncomputable def drawInterp : RelFOInterpretation satOrd Language.graph CTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t => dirF (t 0) (t 1) ⊔ (dirF (t 1) (t 0)).relabel swapPt
  domFormula := domF

section Draw

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Fintype A] [Nonempty A]

/-- **The universe of the drawing is the set of vertices of the gadget
graph.** -/
noncomputable def drawEquiv : drawInterp.MapRel A ≃ V A where
  toFun p := vOf p.1.1 (p.1.2 0) (p.1.2 1) ((realize_domF _ _).mp p.2)
  invFun n := ⟨(vTag n, ![(vPair n).1, (vPair n).2]), (realize_domF _ _).mpr (cDom_vTag n)⟩
  left_inv := by
    rintro ⟨⟨t, w⟩, hw⟩
    have hd : CDom t (w 0) (w 1) := (realize_domF _ _).mp hw
    refine Subtype.ext (Prod.ext (vTag_vOf t _ _ hd) (funext fun i => ?_))
    have hp := vPair_vOf t _ _ hd
    fin_cases i
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  right_inv n := vOf_vTag n

/-- **The edges of the drawing are those of the gadget graph**, in either
direction. -/
theorem adj_drawEquiv_symm (u w : V A) :
    RelMap adj ![drawEquiv.symm u, drawEquiv.symm w] ↔ E u w ∨ E w u := by
  rw [RelFOInterpretation.relMap_mapRel]
  change (dirF (vTag u) (vTag w) ⊔ (dirF (vTag w) (vTag u)).relabel swapPt).Realize _ ↔ _
  rw [Formula.realize_sup, Formula.realize_relabel]
  have e1 : (dirF (vTag u) (vTag w)).Realize
        (fun p => (![drawEquiv.symm u, drawEquiv.symm w] p.1).1.2 p.2) ↔
      E (vOf (vTag u) (vPair u).1 (vPair u).2 (cDom_vTag u))
        (vOf (vTag w) (vPair w).1 (vPair w).2 (cDom_vTag w)) :=
    realize_dirF (vTag u) (vTag w) (cDom_vTag u) (cDom_vTag w)
  have e2 : (dirF (vTag w) (vTag u)).Realize
        ((fun p => (![drawEquiv.symm u, drawEquiv.symm w] p.1).1.2 p.2) ∘ swapPt) ↔
      E (vOf (vTag w) (vPair w).1 (vPair w).2 (cDom_vTag w))
        (vOf (vTag u) (vPair u).1 (vPair u).2 (cDom_vTag u)) :=
    realize_dirF (vTag w) (vTag u) (cDom_vTag w) (cDom_vTag u)
  rw [vOf_vTag, vOf_vTag] at e1 e2
  exact or_congr e1 e2

omit [Fintype A] in
/-- **The number of proper 3-colorings of the drawing** is that of the gadget
graph. -/
theorem sharpThreeCol_draw [Finite A] :
    SharpThreeCol (drawInterp.MapRel A) = Nat.card {χ : V A → Fin 3 // Proper χ} := by
  have := Fintype.ofFinite A
  rw [sharpThreeCol_apply]
  refine Nat.card_congr
    { toFun := fun χ => ⟨χ.1 ∘ drawEquiv.symm, fun u w huw =>
        χ.2 _ _ ((adj_drawEquiv_symm u w).mpr (Or.inl huw))⟩
      invFun := fun χ => ⟨χ.1 ∘ drawEquiv, fun x y hxy => by
        have hxy' : RelMap adj ![drawEquiv.symm (drawEquiv x), drawEquiv.symm (drawEquiv y)] := by
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          exact hxy
        rcases (adj_drawEquiv_symm _ _).mp hxy' with h | h
        · exact χ.2 _ _ h
        · exact fun he => χ.2 _ _ h he.symm⟩
      left_inv := fun χ => Subtype.ext (funext fun x => by simp)
      right_inv := fun χ => Subtype.ext (funext fun u => by simp) }

end Draw

/-! ### The reduction -/

/-- The number of gates, as a polynomial term: the non-first occurrences of
either sign. -/
noncomputable def gateCount : PolyTerm Language.sat :=
  .add (.count (chainedF false (0 : Fin 2) 1)) (.count (chainedF true (0 : Fin 2) 1))

/-- The gates of one sign. -/
def gateSignEquiv (A : Type) [Language.sat.Structure A] [LinearOrder A] (s : Bool) :
    {w : Fin 2 → A // (chainedF s (0 : Fin 2) 1).Realize w} ≃
      {o : A × A // Chained o.1 o.2 s} where
  toFun w := ⟨(w.1 0, w.1 1), realize_chainedF.mp w.2⟩
  invFun o := ⟨![o.1.1, o.1.2], realize_chainedF.mpr o.2⟩
  left_inv w := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
  right_inv _ := rfl

/-- The gates, by sign. -/
def gateEquiv (A : Type) [Language.sat.Structure A] [LinearOrder A] :
    {o : A × A // Chained o.1 o.2 false} ⊕ {o : A × A // Chained o.1 o.2 true} ≃ Gate A where
  toFun := Sum.elim (fun o => ⟨(o.1.1, o.1.2, false), o.2⟩) fun o => ⟨(o.1.1, o.1.2, true), o.2⟩
  invFun g := if h : g.1.2.2 = true then Sum.inr ⟨(g.1.1, g.1.2.1), h ▸ g.2⟩
    else Sum.inl ⟨(g.1.1, g.1.2.1), (Bool.of_not_eq_true h) ▸ g.2⟩
  left_inv := by
    rintro (o | o) <;> rfl
  right_inv := by
    rintro ⟨⟨c, x, s⟩, h⟩
    cases s <;> rfl

theorem eval_gateCount (A : Type) [Language.sat.Structure A] [LinearOrder A] [Finite A] :
    gateCount.eval A = Nat.card (Gate A) := by
  rw [gateCount, PolyTerm.eval, PolyTerm.eval_count, PolyTerm.eval_count,
    Nat.card_congr (gateSignEquiv A false), Nat.card_congr (gateSignEquiv A true),
    ← Nat.card_sum, Nat.card_congr (gateEquiv A)]

end SatToColCount

open SatToColCount in
/-- **#SAT reduces to #3-Colorability with one call**: the count of the
drawing is divided by `6 · 8 ^ g`, `g` the number of non-first
occurrences. -/
noncomputable def sharpSat_oneCall_sharpThreeCol : SharpSAT ≤ᶜ[≤] SharpThreeCol where
  Tag := CTag
  dim := 2
  toRelInterpretation := drawInterp
  dom_nonempty := fun A _ _ _ _ => by
    let := Fintype.ofFinite A
    have hd : CDom (A := A) (.pal .T) least least := ⟨least_le, rfl⟩
    exact ⟨.pal .T, ![least, least], (realize_domF (.pal .T) ![least, least]).mpr hd⟩
  post := .div .oracle (.mul (.poly (.num 6)) (.pow2 (.mul (.num 3) gateCount)))
  correct := fun A _ _ _ _ => by
    change SharpSAT A = SharpThreeCol (drawInterp.MapRel A) / (6 * 2 ^ (3 * gateCount.eval A))
    rw [sharpThreeCol_draw, card_proper, eval_gateCount, pow_mul, sharpSat_apply]
    norm_num

/-- **#3-Colorability is one-call `#P`-complete.**
Registered in the Lax archive as
[`Lax859101.ColoringComplete.sharpThreeCol_sharpP_oneCallComplete`](https://laxarchive.org/lax-859101/Lax859101.ColoringComplete.html#s-Lax859101.ColoringComplete.sharpThreeCol_sharpP_oneCallComplete). -/
theorem sharpThreeCol_sharpP_oneCallComplete : SharpP.OneCallComplete SharpThreeCol :=
  .of_mem sharpThreeCol_mem_sharpP (CountingClass.OneCallHard.of_oneCall
    sharpSat_oneCall_sharpThreeCol
    (oneCallHard_sharpP_of_parsimoniousHard sharpSat_sharpP_parsimoniousHard))

end DescriptiveComplexity
