/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MaxCut.Interp

/-!
# NAE-3SAT ordered-FO-reduces to Max Cut

Correctness of the gadget of `DescriptiveComplexity.Problems.MaxCut.Interp`. The whole
argument runs through one map, `DescriptiveComplexity.MaxCutRed.cutMap`, which charges
every edge of the cut to a threshold unit:

* a cut variable edge is charged to the mark of its element;
* a cut occurrence edge is charged to the mark of its occurrence;
* a cut clause edge `{u, v}` of a clause `c` is charged to whichever of `u`,
  `v` is not the last occurrence of `c` – the tie, when neither is, broken
  towards the side the last occurrence lies on.

The map is *injective on the cut* (`DescriptiveComplexity.MaxCutRed.cutMap_injOn`), and
this is exactly where the width bound is used: two cut clause edges with the
same charge would give four distinct occurrences of one clause, two on each
side of the cut. Injectivity gives `cut ≤ threshold` for every `S`.

Conversely, given a not-all-equal assignment, the side that puts a literal
vertex with its literal and an occurrence vertex with the *negation* of its
literal makes the map hit *every* mark
(`DescriptiveComplexity.MaxCutRed.marked_subset_image`), so `threshold ≤ cut`.

Both halves together say that a cut reaches the threshold iff it is
“perfect”: every variable edge cut (which reads off an assignment), every
occurrence edge cut (which ties the occurrence vertices to it), and every
clause gadget non-monochromatic (which is not-all-equal satisfaction). The
penalty marks of clauses with at most one occurrence are never charged, which
is what rules those clauses out – as it must, since such a clause is never
not-all-equal satisfiable.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace MaxCutRed

open Language Structure SatOcc MaxCutInterp

/-! ### Occurrence bookkeeping -/

section Occurrences

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The last occurrence of a clause is unique. -/
theorem maxOcc_unique {c x y : A} {s t : Bool} (h₁ : MaxOcc c x s) (h₂ : MaxOcc c y t) :
    x = y ∧ s = t := by
  rcases occLt_trichotomy x s y t with hlt | heq | hlt
  · exact absurd hlt (h₁.2 y t h₂.occIn)
  · exact heq
  · exact absurd hlt (h₂.2 x s h₁.occIn)

open Classical in
/-- The occurrence vertex of the last occurrence of `c` (a penalty vertex if
`c` has no occurrence at all). -/
noncomputable def maxVert (c : A) : mcInterp.Map A :=
  if h : ∃ p : A × Bool, MaxOcc c p.1 p.2 then occPt h.choose.2 c h.choose.1 else penPt c

theorem maxVert_eq {c x : A} {s : Bool} (h : MaxOcc c x s) : maxVert c = occPt s c x := by
  have hex : ∃ p : A × Bool, MaxOcc c p.1 p.2 := ⟨(x, s), h⟩
  rw [maxVert, dif_pos hex]
  obtain ⟨hx, hs⟩ := maxOcc_unique hex.choose_spec h
  rw [hx, hs]

omit [LinearOrder A] in
/-- No clause has four distinct occurrence vertices: the width bound, read on
the gadget. -/
theorem no_four_occPt (hwidth : WidthAtMostThree A) {c : A} {v₁ v₂ v₃ v₄ : mcInterp.Map A}
    (h₁ : ∃ x s, OccIn c x s ∧ v₁ = occPt s c x)
    (h₂ : ∃ x s, OccIn c x s ∧ v₂ = occPt s c x)
    (h₃ : ∃ x s, OccIn c x s ∧ v₃ = occPt s c x)
    (h₄ : ∃ x s, OccIn c x s ∧ v₄ = occPt s c x)
    (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₁₄ : v₁ ≠ v₄)
    (h₂₃ : v₂ ≠ v₃) (h₂₄ : v₂ ≠ v₄) (h₃₄ : v₃ ≠ v₄) : False := by
  obtain ⟨x₁, s₁, ho₁, he₁⟩ := h₁
  obtain ⟨x₂, s₂, ho₂, he₂⟩ := h₂
  obtain ⟨x₃, s₃, ho₃, he₃⟩ := h₃
  obtain ⟨x₄, s₄, ho₄, he₄⟩ := h₄
  obtain ⟨i, j, hij, hx, hs⟩ :=
    hwidth c ![x₁, x₂, x₃, x₄] ![s₁, s₂, s₃, s₄] (by intro i; fin_cases i <;> assumption)
  subst he₁
  subst he₂
  subst he₃
  subst he₄
  fin_cases i <;> fin_cases j <;>
    simp_all [occPt_eq_iff]

variable [Finite A]

/-- A clause has at most one occurrence exactly when none of its occurrences
is a non-first one – the first-order form the marks use. -/
theorem atMostOne_iff_noChained {c : A} :
    (∀ x s y t, OccIn c x s → OccIn c y t → x = y ∧ s = t) ↔ ∀ x s, ¬Chained c x s := by
  constructor
  · intro h x s hch
    obtain ⟨y, t, hmin⟩ := exists_minOcc ⟨x, s, hch.occIn⟩
    obtain ⟨rfl, rfl⟩ := h x s y t hch.occIn hmin.occIn
    exact hch.2 hmin
  · intro h x s y t hx hy
    have hxmin : MinOcc c x s := by
      by_contra hm
      exact h x s ⟨hx, hm⟩
    have hymin : MinOcc c y t := by
      by_contra hm
      exact h y t ⟨hy, hm⟩
    rcases occLt_trichotomy x s y t with hlt | heq | hlt
    · exact absurd hlt (hymin.2 x s hx)
    · exact heq
    · exact absurd hlt (hxmin.2 y t hy)

/-- The vertex of the last occurrence, as an occurrence vertex. -/
theorem exists_maxVert {c x : A} {s : Bool} (h : OccIn c x s) :
    ∃ y t, MaxOcc c y t ∧ maxVert c = occPt t c y := by
  obtain ⟨y, t, hmax⟩ := exists_maxOcc ⟨x, s, h⟩
  exact ⟨y, t, hmax, maxVert_eq hmax⟩

end Occurrences

/-! ### Charging a cut edge to a threshold unit -/

section CutMap

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The cut of the gadget graph determined by `S`, as a set of pairs. -/
def cutSet (S : mcInterp.Map A → Prop) : Set (mcInterp.Map A × mcInterp.Map A) :=
  {p | CutRel MAGAdj S p.1 p.2}

/-- The threshold, as a set of pairs. -/
def markSet : Set (mcInterp.Map A × mcInterp.Map A) := {p | MAGMarked p.1 p.2}

@[simp]
theorem mem_cutSet {S : mcInterp.Map A → Prop} {p : mcInterp.Map A × mcInterp.Map A} :
    p ∈ cutSet S ↔ MAGAdj p.1 p.2 ∧ S p.1 ∧ ¬S p.2 := Iff.rfl

@[simp]
theorem mem_markSet {p : mcInterp.Map A × mcInterp.Map A} :
    p ∈ markSet ↔ MAGMarked p.1 p.2 := Iff.rfl

open Classical in
/-- The endpoint of a clause edge that the threshold unit is charged to. -/
noncomputable def pick (S : mcInterp.Map A → Prop) (u v m : mcInterp.Map A) :
    mcInterp.Map A :=
  if S m then (if u = m then v else u) else (if v = m then u else v)

omit [Language.sat.Structure A] [LinearOrder A] in
theorem pick_cases {S : mcInterp.Map A → Prop} {u v m : mcInterp.Map A} (huv : u ≠ v) :
    (pick S u v m = u ∨ pick S u v m = v) ∧ pick S u v m ≠ m := by
  rw [pick]
  split_ifs with hm hu hv
  · exact ⟨Or.inr rfl, fun h => huv (hu.trans h.symm)⟩
  · exact ⟨Or.inl rfl, hu⟩
  · exact ⟨Or.inl rfl, fun h => huv (h.trans hv.symm)⟩
  · exact ⟨Or.inr rfl, hv⟩

omit [Language.sat.Structure A] [LinearOrder A] in
theorem pick_left {S : mcInterp.Map A → Prop} {u v m : mcInterp.Map A} (hm : S m)
    (h : u ≠ m) : pick S u v m = u := by
  rw [pick, if_pos hm, if_neg h]

omit [Language.sat.Structure A] [LinearOrder A] in
theorem pick_right {S : mcInterp.Map A → Prop} {u v m : mcInterp.Map A} (hm : ¬S m)
    (h : v ≠ m) : pick S u v m = v := by
  rw [pick, if_neg hm, if_neg h]

omit [Language.sat.Structure A] [LinearOrder A] in
theorem pick_of_left_eq {S : mcInterp.Map A → Prop} {v m : mcInterp.Map A} (hm : S m) :
    pick S m v m = v := by
  rw [pick, if_pos hm, if_pos rfl]

omit [Language.sat.Structure A] [LinearOrder A] in
theorem pick_of_right_eq {S : mcInterp.Map A → Prop} {u m : mcInterp.Map A} (hm : ¬S m) :
    pick S u m m = u := by
  rw [pick, if_neg hm, if_pos rfl]

variable [Finite A]

open Classical in
/-- The charge map: every edge of the cut is charged to a threshold unit. -/
noncomputable def cutMap (S : mcInterp.Map A → Prop)
    (p : mcInterp.Map A × mcInterp.Map A) : mcInterp.Map A × mcInterp.Map A :=
  match p.1.1, p.2.1 with
  | .lit _, .lit _ => (litPt true (p.1.2 0), litPt false (p.1.2 0))
  | .occ s, .lit _ => (p.1, litPt s (p.1.2 1))
  | .lit _, .occ t => (p.2, litPt t (p.2.2 1))
  | .occ _, .occ _ => (pick S p.1 p.2 (maxVert (p.1.2 0)), maxVert (p.1.2 0))
  | _, _ => p

omit [Finite A] in
@[simp]
theorem cutMap_lit_lit (S : mcInterp.Map A → Prop) (s t : Bool) (x y : A) :
    cutMap S (litPt s x, litPt t y) = (litPt true x, litPt false x) := by
  simp [cutMap, litPt]

omit [Finite A] in
@[simp]
theorem cutMap_occ_lit (S : mcInterp.Map A → Prop) (s t : Bool) (c x y : A) :
    cutMap S (occPt s c x, litPt t y) = (occPt s c x, litPt s x) := by
  simp [cutMap, litPt, occPt]

omit [Finite A] in
@[simp]
theorem cutMap_lit_occ (S : mcInterp.Map A → Prop) (s t : Bool) (c x y : A) :
    cutMap S (litPt s x, occPt t c y) = (occPt t c y, litPt t y) := by
  simp [cutMap, litPt, occPt]

omit [Finite A] in
@[simp]
theorem cutMap_occ_occ (S : mcInterp.Map A → Prop) (s t : Bool) (c d x y : A) :
    cutMap S (occPt s c x, occPt t d y) =
      (pick S (occPt s c x) (occPt t d y) (maxVert c), maxVert c) := by
  simp [cutMap, occPt]

/-- **Every edge of the cut, with its charge in explicit form.** -/
theorem cut_charge {S : mcInterp.Map A → Prop} {p : mcInterp.Map A × mcInterp.Map A}
    (hp : p ∈ cutSet S) :
    (∃ x : A, cutMap S p = (litPt true x, litPt false x) ∧
        (p = (litPt true x, litPt false x) ∨ p = (litPt false x, litPt true x))) ∨
      (∃ (s : Bool) (c x : A), OccIn c x s ∧ cutMap S p = (occPt s c x, litPt s x) ∧
        (p = (occPt s c x, litPt s x) ∨ p = (litPt s x, occPt s c x))) ∨
      ∃ (s t u : Bool) (c x y z : A), OccIn c x s ∧ OccIn c y t ∧ MaxOcc c z u ∧
        ¬(x = y ∧ s = t) ∧ p = (occPt s c x, occPt t c y) ∧
        cutMap S p = (pick S (occPt s c x) (occPt t c y) (occPt u c z), occPt u c z) := by
  obtain ⟨hadj, -, -⟩ := hp
  obtain ⟨-, hshape⟩ := adj_cases hadj
  rcases hshape with ⟨s, x, h1, h2⟩ | ⟨s, c, x, hocc, h1, h2⟩ | ⟨s, c, x, hocc, h1, h2⟩ |
    ⟨s, t, c, x, y, hx, hy, hne, h1, h2⟩
  · have hpe : p = (litPt s x, litPt (!s) x) := Prod.ext h1 h2
    refine Or.inl ⟨x, by rw [hpe, cutMap_lit_lit], ?_⟩
    cases s
    · exact Or.inr hpe
    · exact Or.inl hpe
  · have hpe : p = (occPt s c x, litPt s x) := Prod.ext h1 h2
    exact Or.inr (Or.inl ⟨s, c, x, hocc, by rw [hpe, cutMap_occ_lit], Or.inl hpe⟩)
  · have hpe : p = (litPt s x, occPt s c x) := Prod.ext h1 h2
    exact Or.inr (Or.inl ⟨s, c, x, hocc, by rw [hpe, cutMap_lit_occ], Or.inr hpe⟩)
  · obtain ⟨z, u, hmz, hmv⟩ := exists_maxVert hx
    have hpe : p = (occPt s c x, occPt t c y) := Prod.ext h1 h2
    refine Or.inr (Or.inr ⟨s, t, u, c, x, y, z, hx, hy, hmz, hne, hpe, ?_⟩)
    rw [hpe, cutMap_occ_occ, hmv]

/-- The charge map sends the cut into the threshold. -/
theorem cutMap_mapsTo (S : mcInterp.Map A → Prop) :
    Set.MapsTo (cutMap S) (cutSet S) (markSet (A := A)) := by
  intro p hp
  rcases cut_charge hp with ⟨x, hcp, -⟩ | ⟨s, c, x, hocc, hcp, -⟩ |
    ⟨s, t, u, c, x, y, z, hx, hy, hmz, hne, hpe, hcp⟩
  · rw [mem_markSet, hcp]
    exact marked_lit x
  · rw [mem_markSet, hcp]
    exact marked_occ_lit hocc
  · have huv : occPt s c x ≠ occPt t c y := fun h => hne (by
      obtain ⟨hs, -, hx'⟩ := occPt_eq_iff.mp h
      exact ⟨hx', hs⟩)
    rw [mem_markSet, hcp]
    obtain ⟨hcase, hne'⟩ := pick_cases (S := S) (m := occPt u c z) huv
    rcases hcase with h | h <;> rw [h]
    · refine marked_tri hx hmz fun hcontra => hne' ?_
      rw [h, occPt_eq_iff.mpr ⟨hcontra.2, rfl, hcontra.1⟩]
    · refine marked_tri hy hmz fun hcontra => hne' ?_
      rw [h, occPt_eq_iff.mpr ⟨hcontra.2, rfl, hcontra.1⟩]

/-- **The charge map is injective on the cut.** This is where the width bound
is used: two clause edges with the same charge would exhibit four distinct
occurrences of one clause. -/
theorem cutMap_injOn (hwidth : WidthAtMostThree A) (S : mcInterp.Map A → Prop) :
    Set.InjOn (cutMap S) (cutSet S) := by
  intro p hp q hq heq
  rcases cut_charge hp with ⟨x, hcp, hpp⟩ | ⟨s, c, x, hocc, hcp, hpp⟩ |
      ⟨s, t, u, c, x, y, z, hx, hy, hmz, hne, hpe, hcp⟩ <;>
    rcases cut_charge hq with ⟨x', hcq, hqq⟩ | ⟨s', c', x', hocc', hcq, hqq⟩ |
      ⟨s', t', u', c', x', y', z', hx', hy', hmz', hne', hqe, hcq⟩ <;>
    rw [hcp, hcq] at heq
  · -- two variable edges
    obtain ⟨-, rfl⟩ := litPt_eq_iff.mp (congrArg Prod.fst heq)
    rcases hpp with rfl | rfl <;> rcases hqq with rfl | rfl
    · rfl
    · exact absurd hq.2.1 hp.2.2
    · exact absurd hp.2.1 hq.2.2
    · rfl
  · exact absurd (congrArg Prod.fst heq) (by simp)
  · exact absurd (congrArg Prod.snd heq) (by simp)
  · exact absurd (congrArg Prod.fst heq) (by simp)
  · -- two occurrence edges
    obtain ⟨rfl, rfl, rfl⟩ := occPt_eq_iff.mp (congrArg Prod.fst heq)
    rcases hpp with rfl | rfl <;> rcases hqq with rfl | rfl
    · rfl
    · exact absurd hq.2.1 hp.2.2
    · exact absurd hp.2.1 hq.2.2
    · rfl
  · exact absurd (congrArg Prod.snd heq) (by simp)
  · exact absurd (congrArg Prod.snd heq) (by simp)
  · exact absurd (congrArg Prod.snd heq) (by simp)
  · -- two clause edges: the width bound
    obtain ⟨rfl, rfl, rfl⟩ := occPt_eq_iff.mp (congrArg Prod.snd heq)
    have hpick := congrArg Prod.fst heq
    subst hpe
    subst hqe
    obtain ⟨-, hin, hout⟩ := hp
    obtain ⟨-, hin', hout'⟩ := hq
    simp only at hin hout hin' hout'
    by_cases hm : S (occPt u c z)
    · simp only [pick] at hpick
      rw [if_pos hm, if_pos hm] at hpick
      by_cases h₁ : occPt s c x = occPt u c z
      · rw [if_pos h₁] at hpick
        by_cases h₂ : occPt s' c x' = occPt u c z
        · rw [if_pos h₂] at hpick
          rw [Prod.mk.injEq]
          exact ⟨h₁.trans h₂.symm, hpick⟩
        · rw [if_neg h₂] at hpick
          exact absurd (hpick ▸ hin') hout
      · rw [if_neg h₁] at hpick
        by_cases h₂ : occPt s' c x' = occPt u c z
        · rw [if_pos h₂] at hpick
          exact absurd (hpick ▸ hin) hout'
        · rw [if_neg h₂] at hpick
          by_cases hb : occPt t c y = occPt t' c y'
          · rw [Prod.mk.injEq]
            exact ⟨hpick, hb⟩
          · exact (no_four_occPt hwidth ⟨x, s, hx, rfl⟩ ⟨z, u, hmz.occIn, rfl⟩
              ⟨y, t, hy, rfl⟩ ⟨y', t', hy', rfl⟩ h₁
              (fun hc => hout (hc ▸ hin)) (fun hc => hout' (hc ▸ hin))
              (fun hc => hout (hc ▸ hm)) (fun hc => hout' (hc ▸ hm)) hb).elim
    · simp only [pick] at hpick
      rw [if_neg hm, if_neg hm] at hpick
      by_cases h₁ : occPt t c y = occPt u c z
      · rw [if_pos h₁] at hpick
        by_cases h₂ : occPt t' c y' = occPt u c z
        · rw [if_pos h₂] at hpick
          rw [Prod.mk.injEq]
          exact ⟨hpick, h₁.trans h₂.symm⟩
        · rw [if_neg h₂] at hpick
          exact absurd (hpick ▸ hin) hout'
      · rw [if_neg h₁] at hpick
        by_cases h₂ : occPt t' c y' = occPt u c z
        · rw [if_pos h₂] at hpick
          exact absurd (hpick ▸ hin') hout
        · rw [if_neg h₂] at hpick
          by_cases ha : occPt s c x = occPt s' c x'
          · rw [Prod.mk.injEq]
            exact ⟨ha, hpick⟩
          · exact (no_four_occPt hwidth ⟨y, t, hy, rfl⟩ ⟨z, u, hmz.occIn, rfl⟩
              ⟨x, s, hx, rfl⟩ ⟨x', s', hx', rfl⟩ h₁
              (fun hc => hout (hc ▸ hin)) (fun hc => hout (hc ▸ hin'))
              (fun hc => hm (hc ▸ hin)) (fun hc => hm (hc ▸ hin')) ha).elim

end CutMap

/-! ### The side of the cut given by an assignment -/

section Forward

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- The side of the cut determined by an assignment: a literal vertex takes
the value of its literal, an occurrence vertex the negation of its literal,
and the penalty vertices are outside. -/
def cutSide (ν : A → Prop) (p : mcInterp.Map A) : Prop :=
  match p.1 with
  | .lit s => LitTrue ν (p.2 0) s
  | .occ s => ¬LitTrue ν (p.2 1) s
  | .pen => False

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
@[simp]
theorem cutSide_lit (ν : A → Prop) (s : Bool) (x : A) :
    cutSide ν (litPt s x) ↔ LitTrue ν x s := by
  simp [cutSide, litPt]

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
@[simp]
theorem cutSide_occ (ν : A → Prop) (s : Bool) (c x : A) :
    cutSide ν (occPt s c x) ↔ ¬LitTrue ν x s := by
  simp [cutSide, occPt]

/-- Given a not-all-equal assignment, the charge map hits *every* threshold
unit, so the cut is at least as large as the threshold. -/
theorem marked_subset_image (hw : ¬ThreeSatToSat.Wide A) {ν : A → Prop} (hν : NAEProper ν) :
    markSet (A := A) ⊆ cutMap (cutSide ν) '' cutSet (cutSide ν) := by
  rintro ⟨p, q⟩ hmk
  rcases marked_cases hmk with ⟨x, rfl, rfl⟩ | ⟨s, c, x, hocc, rfl, rfl⟩ |
    ⟨s, t, c, x, y, hx, hmax, hne, rfl, rfl⟩ | ⟨c, hcl, hch, rfl, rfl⟩
  · -- the mark of an element: its variable edge is cut
    by_cases hv : ν x
    · exact ⟨(litPt true x, litPt false x),
        ⟨adj_lit_lit hw (by simp) x, by simp [LitTrue, hv], by simp [LitTrue, hv]⟩, by simp⟩
    · exact ⟨(litPt false x, litPt true x),
        ⟨adj_lit_lit hw (by simp) x, by simp [LitTrue, hv], by simp [LitTrue, hv]⟩, by simp⟩
  · -- the mark of an occurrence: its edge is cut
    by_cases hv : LitTrue ν x s
    · exact ⟨(litPt s x, occPt s c x),
        ⟨adj_lit_occ hw hocc, by simpa using hv, by simpa using hv⟩, by simp⟩
    · exact ⟨(occPt s c x, litPt s x),
        ⟨adj_occ_lit hw hocc, by simpa using hv, by simpa using hv⟩, by simp⟩
  · -- the mark of a non-maximal occurrence: some clause edge is charged to it
    have hmv : maxVert c = occPt t c y := maxVert_eq hmax
    have hvert : occPt s c x ≠ occPt t c y := fun h => hne (by
      obtain ⟨hs, -, hx'⟩ := occPt_eq_iff.mp h
      exact ⟨hx', hs⟩)
    by_cases hsame : LitTrue ν x s ↔ LitTrue ν y t
    · -- the two agree: some other occurrence of `c` disagrees with both
      obtain ⟨⟨z₁, u₁, ho₁, hT₁⟩, ⟨z₂, u₂, ho₂, hF₂⟩⟩ := naeProper_occ hν c hx.isCl
      obtain ⟨z, u, hz, hzne⟩ : ∃ z u, OccIn c z u ∧ ¬(LitTrue ν z u ↔ LitTrue ν y t) := by
        by_cases hb : LitTrue ν y t
        · exact ⟨z₂, u₂, ho₂, fun h => hF₂ (h.mpr hb)⟩
        · exact ⟨z₁, u₁, ho₁, fun h => hb (h.mp hT₁)⟩
      have hzx : ¬(z = x ∧ u = s) := by
        rintro ⟨rfl, rfl⟩
        exact hzne hsame
      have hzy : occPt u c z ≠ occPt t c y := fun h => by
        obtain ⟨rfl, -, rfl⟩ := occPt_eq_iff.mp h
        exact hzne Iff.rfl
      have hzx' : occPt u c z ≠ occPt s c x := fun h => hzx (by
        obtain ⟨hs, -, hx'⟩ := occPt_eq_iff.mp h
        exact ⟨hx', hs⟩)
      by_cases hval : LitTrue ν y t
      · -- the last occurrence is true, so its vertex is outside
        refine ⟨(occPt u c z, occPt s c x), ⟨adj_occ_occ hw hz hx hzx, ?_, ?_⟩, ?_⟩
        · simpa using fun h => hzne (iff_of_true h hval)
        · simpa using hsame.mpr hval
        · rw [cutMap_occ_occ, hmv, pick_right (by simpa using hval) hvert]
      · refine ⟨(occPt s c x, occPt u c z), ⟨adj_occ_occ hw hx hz (fun h =>
          hzx ⟨h.1.symm, h.2.symm⟩), ?_, ?_⟩, ?_⟩
        · simpa using fun h => hval (hsame.mp h)
        · simp only [cutSide_occ, not_not]
          by_contra hc
          exact hzne (iff_of_false hc hval)
        · rw [cutMap_occ_occ, hmv, pick_left (by simpa using hval) hvert]
    · -- the two already disagree: the edge to the last occurrence is cut
      by_cases hval : LitTrue ν y t
      · -- the marked occurrence is false, so its vertex is inside
        refine ⟨(occPt s c x, occPt t c y), ⟨adj_occ_occ hw hx hmax.occIn hne, ?_, ?_⟩, ?_⟩
        · simp only [cutSide_occ]
          by_contra hc
          exact hsame (iff_of_true hc hval)
        · simpa using hval
        · rw [cutMap_occ_occ, hmv, pick_of_right_eq (by simpa using hval)]
      · refine ⟨(occPt t c y, occPt s c x),
          ⟨adj_occ_occ hw hmax.occIn hx (fun h => hne ⟨h.1.symm, h.2.symm⟩), ?_, ?_⟩, ?_⟩
        · simpa using hval
        · simp only [cutSide_occ, not_not]
          by_contra hc
          exact hsame (iff_of_false hc hval)
        · rw [cutMap_occ_occ, hmv, pick_of_left_eq (by simpa using hval)]
  · -- a clause with at most one occurrence is never not-all-equal satisfiable
    exfalso
    obtain ⟨⟨z₁, u₁, ho₁, hT₁⟩, ⟨z₂, u₂, ho₂, hF₂⟩⟩ := naeProper_occ hν c hcl
    have hne : ¬(z₁ = z₂ ∧ u₁ = u₂) := by
      rintro ⟨rfl, rfl⟩
      exact hF₂ hT₁
    exact hne (atMostOne_iff_noChained.mpr hch z₁ u₁ z₂ u₂ ho₁ ho₂)

end Forward

/-! ### Correctness -/

section Correctness

variable (A : Type) [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- Correctness of the reduction: a CNF structure is a yes-instance of
NAE-3SAT iff its gadget graph has a cut at least as large as its marked
relation. -/
theorem naeThreeSatisfiable_iff_hasLargeCut :
    NAEThreeSatisfiable A ↔ HasLargeCut (mcInterp.Map A) := by
  haveI : Finite (mcInterp.Map A) := mcInterp.map_finite A
  by_cases hw : ThreeSatToSat.Wide A
  · -- a wide input has no edge at all, but a nonempty threshold
    refine iff_of_false
      (fun h => (ThreeSatToSat.wide_iff_not_widthAtMostThree A).mp hw h.1) ?_
    rintro ⟨-, S, hcard⟩
    obtain ⟨c, x, s, hocc, -⟩ := id hw
    have hempty : {p : mcInterp.Map A × mcInterp.Map A |
        CutRel MAGAdj S p.1 p.2} = ∅ := by
      ext ⟨p, q⟩
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => (adj_cases h.1).1 hw
    have hmk : (0 : ℕ) < {p : mcInterp.Map A × mcInterp.Map A | MAGMarked p.1 p.2}.ncard := by
      rw [Set.ncard_pos (Set.toFinite _)]
      exact ⟨(occPt (s 0) c (x 0), litPt (s 0) (x 0)), marked_occ_lit (hocc 0)⟩
    rw [hempty, Set.ncard_empty] at hcard
    omega
  · -- the interesting case
    have hwidth : WidthAtMostThree A := by
      by_contra h
      exact hw ((ThreeSatToSat.wide_iff_not_widthAtMostThree A).mpr h)
    rw [NAEThreeSatisfiable, and_iff_right hwidth, HasLargeCut, and_iff_right ‹Finite _›]
    constructor
    · -- a not-all-equal assignment gives a cut reaching the threshold
      rintro ⟨ν, hν⟩
      refine ⟨cutSide ν, ?_⟩
      calc (markSet (A := A)).ncard
          ≤ (cutMap (cutSide ν) '' cutSet (cutSide ν)).ncard :=
            Set.ncard_le_ncard (marked_subset_image hw hν) (Set.toFinite _)
        _ ≤ (cutSet (cutSide ν)).ncard := Set.ncard_image_le (Set.toFinite _)
    · -- a cut reaching the threshold is perfect, and reads off an assignment
      rintro ⟨S, hcard⟩
      have himg : cutMap S '' cutSet S = markSet (A := A) := by
        refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr (cutMap_mapsTo S)) ?_
          (Set.toFinite _)
        rw [(cutMap_injOn hwidth S).ncard_image]
        exact hcard
      have hhit : ∀ p q : mcInterp.Map A, MAGMarked p q →
          ∃ r ∈ cutSet S, cutMap S r = (p, q) := fun p q h => himg.symm.subset h
      -- every variable edge is cut, which reads off the assignment
      have hvar : ∀ (x : A) (r : Bool),
          S (litPt r x) ↔ LitTrue (fun a => S (litPt true a)) x r := by
        intro x r
        obtain ⟨p, hp, hcp⟩ := hhit _ _ (marked_lit x)
        rcases cut_charge hp with ⟨x', hc, hpp⟩ | ⟨s', c', x', -, hc, -⟩ |
          ⟨s', t', u', c', x', y', z', -, -, -, -, -, hc⟩
        · rw [hc] at hcp
          obtain ⟨-, rfl⟩ := litPt_eq_iff.mp (congrArg Prod.fst hcp)
          rcases hpp with rfl | rfl <;> obtain ⟨-, hin, hout⟩ := hp <;> cases r
          · exact iff_of_false hout (not_not_intro hin)
          · exact Iff.rfl
          · exact iff_of_true hin hout
          · exact Iff.rfl
        · rw [hc] at hcp
          exact absurd (congrArg Prod.fst hcp) (by simp)
        · rw [hc] at hcp
          exact absurd (congrArg Prod.snd hcp) (by simp)
      -- occurrence vertices carry the negation of their literal
      have hoccval : ∀ (d w : A) (r : Bool), OccIn d w r →
          (S (occPt r d w) ↔ ¬S (litPt r w)) := by
        intro d w r hocc
        obtain ⟨p, hp, hcp⟩ := hhit _ _ (marked_occ_lit hocc)
        rcases cut_charge hp with ⟨x', hc, -⟩ | ⟨s', c', x', -, hc, hpp⟩ |
          ⟨s', t', u', c', x', y', z', -, -, -, -, -, hc⟩
        · rw [hc] at hcp
          exact absurd (congrArg Prod.fst hcp) (by simp)
        · rw [hc] at hcp
          obtain ⟨rfl, rfl, rfl⟩ := occPt_eq_iff.mp (congrArg Prod.fst hcp)
          rcases hpp with rfl | rfl <;> obtain ⟨-, hin, hout⟩ := hp
          · exact iff_of_true hin hout
          · exact iff_of_false hout (not_not_intro hin)
        · rw [hc] at hcp
          exact absurd (congrArg Prod.snd hcp) (by simp)
      refine ⟨fun a => S (litPt true a), naeProper_of_occ fun c hcl => ?_⟩
      -- the clause has at least two occurrences
      have hchained : ∃ x r, Chained c x r := by
        by_contra hno
        push Not at hno
        obtain ⟨p, hp, hcp⟩ := hhit _ _ (marked_pen hcl fun x r => hno x r)
        rcases cut_charge hp with ⟨x', hc, -⟩ | ⟨s', c', x', -, hc, -⟩ |
          ⟨s', t', u', c', x', y', z', -, -, -, -, -, hc⟩ <;> rw [hc] at hcp
        · exact absurd (congrArg Prod.fst hcp) (by simp)
        · exact absurd (congrArg Prod.fst hcp) (by simp)
        · exact absurd (congrArg Prod.snd hcp) (by simp)
      obtain ⟨x, r, hch⟩ := hchained
      obtain ⟨y, t, hmax⟩ := exists_maxOcc ⟨x, r, hch.occIn⟩
      obtain ⟨z, u, hz, hzne⟩ : ∃ z u, OccIn c z u ∧ ¬(z = y ∧ u = t) := by
        rcases Classical.em (x = y ∧ r = t) with ⟨rfl, rfl⟩ | h
        · obtain ⟨w, r', hsucc⟩ := exists_succOcc hch
          exact ⟨w, r', hsucc.1, fun hc => occLt_irrefl x r (by
            rw [hc.1, hc.2] at hsucc
            exact hsucc.2.2.1)⟩
        · exact ⟨x, r, hch.occIn, h⟩
      obtain ⟨p, hp, hcp⟩ := hhit _ _ (marked_tri hz hmax hzne)
      -- that charge comes from a clause edge, whose endpoints disagree
      rcases cut_charge hp with ⟨x', hc, -⟩ | ⟨s', c', x', -, hc, -⟩ |
        ⟨s', t', u', c', x', y', z', hx', hy', -, -, hpe, hc⟩ <;> rw [hc] at hcp
      · exact absurd (congrArg Prod.fst hcp) (by simp)
      · exact absurd (congrArg Prod.snd hcp) (by simp)
      · obtain ⟨-, hcc, -⟩ := occPt_eq_iff.mp (congrArg Prod.snd hcp)
        rw [hpe] at hp
        have hin : S (occPt s' c' x') := hp.2.1
        have hout : ¬S (occPt t' c' y') := hp.2.2
        rw [hcc] at hx' hy' hin hout
        refine ⟨⟨y', t', hy', ?_⟩, ⟨x', s', hx', ?_⟩⟩
        · have hy : S (litPt t' y') := by
            by_contra hcon
            exact hout ((hoccval c y' t' hy').mpr hcon)
          exact (hvar y' t').mp hy
        · have hx : ¬S (litPt s' x') := (hoccval c x' s' hx').mp hin
          exact fun hcon => hx ((hvar x' s').mpr hcon)

end Correctness

/-- **NAE-3SAT ordered-FO-reduces to Max Cut**: the gadget graph, whose cut
reaches the threshold exactly when the clauses are not-all-equal satisfiable. -/
noncomputable def nae3Sat_ordered_fo_reduction_maxCut : NAE3SAT ≤ᶠᵒ[≤] MaxCut where
  Tag := MCTag
  dim := 2
  toInterpretation := mcInterp
  correct A _ _ _ _ := naeThreeSatisfiable_iff_hasLargeCut A

end MaxCutRed

end DescriptiveComplexity
