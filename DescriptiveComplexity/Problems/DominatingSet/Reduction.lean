/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.DominatingSet.Defs
import DescriptiveComplexity.Problems.SetFamily

/-!
# Set Cover FO-reduces to Dominating Set

The classical reduction – ground elements and sets become vertices, the sets
form a clique, and a set is joined to its elements – with the two degenerate
cases that make it delicate handled by *gates* rather than by a canonical
extra vertex. The reduction is therefore order-free, which the roadmap did not
expect.

The two gates, both first-order:

* `DescriptiveComplexity.DomRed.Uncoverable`, “some ground element belongs to no set”:
  the input is then a no-instance, and the output is made edgeless with an
  empty threshold, hence a no-instance too;
* `DescriptiveComplexity.DomRed.NoElem`, “there is no ground element at all”: the input
  is then a yes-instance (the empty cover works), and the output is made
  edgeless with *everything* marked, hence a yes-instance too.

Outside those two cases every cover is nonempty – it has to cover something –
which is exactly what the domination argument needs: a nonempty set of
set-vertices dominates the whole clique, and with it every junk vertex, since
the junk is made adjacent to all set-vertices. Junk cannot be ignored here:
domination constrains *every* element of the universe, unlike the covering and
packing conditions of the set family.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace DomRed

open Language Structure

/-! ### Formula builders over the vocabulary of set systems -/

section Builders

variable {α : Type}

/-- `x` is a ground element, as a formula. -/
def elemF (x : α) : Language.setSystem.Formula α := Relations.formula₁ ssElem (Term.var x)

/-- `f` is a set of the family, as a formula. -/
def famF (f : α) : Language.setSystem.Formula α := Relations.formula₁ ssFam (Term.var f)

/-- `x` belongs to `f`, as a formula. -/
def memF (x f : α) : Language.setSystem.Formula α :=
  Relations.formula₂ ssMem (Term.var x) (Term.var f)

/-- `x` is marked, as a formula. -/
def markF (x : α) : Language.setSystem.Formula α :=
  Relations.formula₁ ssMarked (Term.var x)

/-- `x = y`, as a formula. -/
def eqF (x y : α) : Language.setSystem.Formula α := Term.equal (Term.var x) (Term.var y)

/-- Some ground element belongs to no set, as a formula. -/
noncomputable def uncoverableF : Language.setSystem.Formula α :=
  (elemF (Sum.inr ()) ⊓
    Formula.iAlls Unit
      (∼(famF (Sum.inr ()) ⊓ memF (Sum.inl (Sum.inr ())) (Sum.inr ())))).iExs Unit

/-- There is no ground element at all, as a formula. -/
noncomputable def noElemF : Language.setSystem.Formula α :=
  Formula.iAlls Unit (∼(elemF (Sum.inr ())))

/-- The gate: either degenerate case. -/
noncomputable def gateF : Language.setSystem.Formula α := uncoverableF ⊔ noElemF

end Builders

section Semantics

variable {A : Type} [Language.setSystem.Structure A] {α : Type} {v : α → A}

@[simp]
theorem realize_elemF {x : α} : (elemF x).Realize v ↔ SSElem (v x) := by
  rw [elemF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_famF {f : α} : (famF f).Realize v ↔ SSFam (v f) := by
  rw [famF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_memF {x f : α} : (memF x f).Realize v ↔ SSMem (v x) (v f) := by
  rw [memF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_markF {x : α} : (markF x).Realize v ↔ SSMarked (v x) := by
  rw [markF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp] theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]

variable (A)

/-- Some ground element belongs to no set: the input is then a no-instance. -/
def Uncoverable : Prop := ∃ x : A, SSElem x ∧ ∀ f : A, ¬(SSFam f ∧ SSMem x f)

/-- There is no ground element at all: the empty cover then works. -/
def NoElem : Prop := ∀ x : A, ¬SSElem x

variable {A}

@[simp]
theorem realize_uncoverableF : (uncoverableF (α := α)).Realize v ↔ Uncoverable A := by
  simp only [uncoverableF, Formula.realize_iExs, Formula.realize_iAlls, Formula.realize_inf,
    Formula.realize_not, realize_elemF, realize_famF, realize_memF, Sum.elim_inl,
    Sum.elim_inr, Uncoverable]
  constructor
  · rintro ⟨x, hx, hno⟩
    exact ⟨x (), hx, fun f hf => hno (fun _ => f) hf⟩
  · rintro ⟨x, hx, hno⟩
    exact ⟨fun _ => x, hx, fun f hf => hno (f ()) hf⟩

@[simp]
theorem realize_noElemF : (noElemF (α := α)).Realize v ↔ NoElem A := by
  simp only [noElemF, Formula.realize_iAlls, Formula.realize_not, realize_elemF,
    Sum.elim_inr, NoElem]
  exact ⟨fun h x => h (fun _ => x), fun h i => h (i ())⟩

@[simp]
theorem realize_gateF : (gateF (α := α)).Realize v ↔ Uncoverable A ∨ NoElem A := by
  simp [gateF]

end Semantics

/-! ### The interpretation -/

/-- Tags of the reduction: the vertex of a ground element and the vertex of a
set. -/
inductive DSTag : Type
  /-- The vertex of a ground element. -/
  | elt
  /-- The vertex of a set of the family. -/
  | set
  deriving DecidableEq

instance : Fintype DSTag where
  elems := {DSTag.elt, DSTag.set}
  complete := by
    intro t
    cases t <;> decide

instance : Nonempty DSTag := ⟨DSTag.set⟩

/-- Defining formula for adjacency, before the gate: the sets form a clique,
and a set is joined to its elements – and to every junk vertex. -/
noncomputable def adjF : DSTag → DSTag → Language.setSystem.Formula (Fin 2 × Fin 1)
  | .set, .set => ∼(eqF (0, 0) (1, 0))
  | .set, .elt => (famF (0, 0) ⊓ elemF (1, 0) ⊓ memF (1, 0) (0, 0)) ⊔ ∼(elemF (1, 0))
  | .elt, .set => (famF (1, 0) ⊓ elemF (0, 0) ⊓ memF (0, 0) (1, 0)) ⊔ ∼(elemF (0, 0))
  | .elt, .elt => ⊥

/-- The interpretation of Dominating Set instances in set systems. -/
noncomputable def dsInterp :
    FOInterpretation Language.setSystem Language.markedGraph DSTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t => adjF (t 0) (t 1) ⊓ ∼gateF
    | _, .marked => fun t =>
        (if t 0 = DSTag.set then markF (0, 0) else ⊥) ⊓ ∼gateF ⊔ noElemF

/-! ### The points -/

section Points

variable {A : Type}

/-- The vertex of tag `t` over the element `x`. -/
def dsPt (t : DSTag) (x : A) : dsInterp.Map A := (t, fun _ => x)

theorem dsPt_eq_iff {t t' : DSTag} {x x' : A} : dsPt t x = dsPt t' x' ↔ t = t' ∧ x = x' := by
  constructor
  · intro h
    exact ⟨by simpa [dsPt] using congrArg (fun p : dsInterp.Map A => p.1) h,
      by simpa [dsPt] using congrArg (fun p : dsInterp.Map A => p.2 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem dsPt_injective (t : DSTag) : Function.Injective (dsPt t (A := A)) :=
  fun _ _ h => (dsPt_eq_iff.mp h).2

theorem dsPt_surj (q : dsInterp.Map A) : ∃ t x, q = dsPt t x :=
  ⟨q.1, q.2 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg q.2 (Subsingleton.elim i 0)⟩⟩

end Points

/-! ### Characterization of the two relations -/

section Characterizations

variable {A : Type} [Language.setSystem.Structure A]

theorem mgAdj_pt (t₁ t₂ : DSTag) (x y : A) :
    MGAdj (dsPt t₁ x) (dsPt t₂ y) ↔
      ¬(Uncoverable A ∨ NoElem A) ∧
        ((t₁ = .set ∧ t₂ = .set ∧ x ≠ y) ∨
          (t₁ = .set ∧ t₂ = .elt ∧ ((SSFam x ∧ SSElem y ∧ SSMem y x) ∨ ¬SSElem y)) ∨
          (t₁ = .elt ∧ t₂ = .set ∧ ((SSFam y ∧ SSElem x ∧ SSMem x y) ∨ ¬SSElem x))) := by
  rw [MGAdj, dsPt, dsPt, FOInterpretation.relMap_map]
  cases t₁ <;> cases t₂ <;>
    simp [dsInterp, adjF, realize_gateF] <;> tauto

theorem mgMarked_pt (t : DSTag) (x : A) :
    MGMarked (dsPt t x) ↔
      (t = .set ∧ SSMarked x ∧ ¬(Uncoverable A ∨ NoElem A)) ∨ NoElem A := by
  rw [MGMarked, dsPt, FOInterpretation.relMap_map]
  cases t <;> simp [dsInterp, realize_gateF]

end Characterizations

/-! ### Correctness -/

section Correctness

variable {A : Type} [Language.setSystem.Structure A]

omit [Language.setSystem.Structure A] in
private theorem ncard_pt_eq (t : DSTag) (P : A → Prop) (Q : dsInterp.Map A → Prop)
    (hshape : ∀ p, Q p → ∃ v, p = dsPt t v) (hP : ∀ v : A, Q (dsPt t v) ↔ P v) :
    {p | Q p}.ncard = {v | P v}.ncard := by
  have hset : {p | Q p} = dsPt t '' {v | P v} := by
    ext p
    constructor
    · intro hq
      obtain ⟨v, rfl⟩ := hshape p hq
      exact ⟨v, (hP v).mp hq, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hP v).mpr hv
  rw [hset, Set.ncard_image_of_injective _ (dsPt_injective t)]

omit [Language.setSystem.Structure A] in
/-- Finiteness transfers back along the vertices of the sets. -/
private theorem finite_of_map (h : Finite (dsInterp.Map A)) : Finite A :=
  Finite.of_injective _ (dsPt_injective (A := A) .set)

variable (A)

/-- Correctness of the reduction: a set system has a small cover iff its
incidence graph has a small dominating set. -/
theorem hasSmallSetCover_iff_hasSmallDominatingSet :
    HasSmallSetCover A ↔ HasSmallDominatingSet (dsInterp.Map A) := by
  by_cases hno : NoElem A
  · -- no ground element at all: the empty cover works, and everything is marked
    constructor
    · rintro ⟨hfin, -⟩
      haveI := hfin
      haveI : Finite (dsInterp.Map A) := dsInterp.map_finite A
      refine ⟨inferInstance, fun _ => True, fun v => Or.inl trivial,
        Set.ncard_le_ncard (fun v _ => ?_) (Set.toFinite _)⟩
      obtain ⟨t, x, rfl⟩ := dsPt_surj v
      exact (mgMarked_pt t x).mpr (Or.inr hno)
    · rintro ⟨hfin, -⟩
      haveI := finite_of_map hfin
      exact ⟨inferInstance, fun _ => False, fun s hs => hs.elim,
        fun x hx => absurd hx (hno x), by simp⟩
  · by_cases hunc : Uncoverable A
    · -- an element in no set: no cover, and the output has no edge and no mark
      refine iff_of_false ?_ ?_
      · rintro ⟨-, G, hGfam, hcov, -⟩
        obtain ⟨x, hx, hx'⟩ := hunc
        obtain ⟨s, hs, hms⟩ := hcov x hx
        exact hx' s ⟨hGfam s hs, hms⟩
      · rintro ⟨hfin, D, hdom, hcard⟩
        haveI := hfin
        have hall : ∀ v : dsInterp.Map A, D v := by
          intro v
          refine (hdom v).resolve_right ?_
          rintro ⟨u, -, hadj⟩
          obtain ⟨t, x, rfl⟩ := dsPt_surj u
          obtain ⟨t', y, rfl⟩ := dsPt_surj v
          exact ((mgAdj_pt t t' x y).mp hadj).1 (Or.inl hunc)
        have hmk : {v : dsInterp.Map A | MGMarked v} = ∅ := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          obtain ⟨t, x, rfl⟩ := dsPt_surj v
          intro h
          rcases (mgMarked_pt t x).mp h with ⟨-, -, hg⟩ | hg
          · exact hg (Or.inl hunc)
          · obtain ⟨z, hz, -⟩ := hunc
            exact hg z hz
        obtain ⟨z, hz, -⟩ := hunc
        have hpos : (0 : ℕ) < {v : dsInterp.Map A | D v}.ncard := by
          rw [Set.ncard_pos (Set.toFinite _)]
          exact ⟨dsPt .set z, hall _⟩
        rw [hmk, Set.ncard_empty] at hcard
        omega
    · -- the interesting case
      obtain ⟨x₀, hx₀⟩ : ∃ x : A, SSElem x := by
        by_contra h
        exact hno fun x hx => h ⟨x, hx⟩
      have hgate : ¬(Uncoverable A ∨ NoElem A) := by
        rintro (h | h)
        exacts [hunc h, hno h]
      have hmkcard : {v : dsInterp.Map A | MGMarked v}.ncard = {x : A | SSMarked x}.ncard := by
        refine ncard_pt_eq .set _ _ (fun p hp => ?_) fun x => ?_
        · obtain ⟨t, y, rfl⟩ := dsPt_surj p
          rcases (mgMarked_pt t y).mp hp with ⟨rfl, -, -⟩ | h
          · exact ⟨y, rfl⟩
          · exact absurd h hno
        · rw [mgMarked_pt]
          exact ⟨fun h => h.elim (fun h' => h'.2.1) fun h' => absurd h' hno,
            fun h => Or.inl ⟨rfl, h, hgate⟩⟩
      constructor
      · -- a cover dominates: its set-vertices reach every vertex
        rintro ⟨hfin, G, hGfam, hcov, hcard⟩
        haveI := hfin
        haveI : Finite (dsInterp.Map A) := dsInterp.map_finite A
        obtain ⟨s₀, hs₀, -⟩ := hcov x₀ hx₀
        refine ⟨inferInstance, fun v => ∃ s, G s ∧ v = dsPt .set s, fun v => ?_, ?_⟩
        · obtain ⟨t, y, rfl⟩ := dsPt_surj v
          cases t with
          | set =>
            by_cases hy : G y
            · exact Or.inl ⟨y, hy, rfl⟩
            · exact Or.inr ⟨dsPt .set s₀, ⟨s₀, hs₀, rfl⟩, (mgAdj_pt _ _ _ _).mpr
                ⟨hgate, Or.inl ⟨rfl, rfl, fun h => hy (h ▸ hs₀)⟩⟩⟩
          | elt =>
            by_cases hy : SSElem y
            · obtain ⟨s, hs, hms⟩ := hcov y hy
              exact Or.inr ⟨dsPt .set s, ⟨s, hs, rfl⟩, (mgAdj_pt _ _ _ _).mpr
                ⟨hgate, Or.inr (Or.inl ⟨rfl, rfl, Or.inl ⟨hGfam s hs, hy, hms⟩⟩)⟩⟩
            · exact Or.inr ⟨dsPt .set s₀, ⟨s₀, hs₀, rfl⟩, (mgAdj_pt _ _ _ _).mpr
                ⟨hgate, Or.inr (Or.inl ⟨rfl, rfl, Or.inr hy⟩)⟩⟩
        · rw [hmkcard, ncard_pt_eq .set G _ (fun p hp => ?_) fun x => ?_]
          · exact hcard
          · obtain ⟨s, -, rfl⟩ := hp
            exact ⟨s, rfl⟩
          · exact ⟨fun ⟨s, hs, he⟩ => (dsPt_eq_iff.mp he).2 ▸ hs, fun h => ⟨x, h, rfl⟩⟩
      · -- a dominating set covers: replace each vertex by a set
        rintro ⟨hfin, D, hdom, hcard⟩
        haveI := hfin
        haveI := finite_of_map hfin
        classical
        have hcov : ∀ a : A, SSElem a → ∃ s, SSFam s ∧ SSMem a s := by
          intro a ha
          by_contra h
          exact hunc ⟨a, ha, fun f hf => h ⟨f, hf⟩⟩
        set cov : A → A := fun a =>
          if h : ∃ s, SSFam s ∧ SSMem a s then h.choose else a with hcovdef
        have hcovspec : ∀ a, SSElem a → SSFam (cov a) ∧ SSMem a (cov a) := by
          intro a ha
          have hex := hcov a ha
          rw [hcovdef]
          simp only [dif_pos hex]
          exact hex.choose_spec
        set g : dsInterp.Map A → A := fun v =>
          match v.1 with
          | .set => v.2 0
          | .elt => cov (v.2 0) with hgdef
        have hgset : ∀ s : A, g (dsPt .set s) = s := fun s => rfl
        have hgelt : ∀ a : A, g (dsPt .elt a) = cov a := fun a => rfl
        refine ⟨inferInstance, fun s => SSFam s ∧ ∃ v, D v ∧ g v = s, fun s hs => hs.1,
          fun a ha => ?_, ?_⟩
        · rcases hdom (dsPt .elt a) with h | ⟨u, hu, hadj⟩
          · exact ⟨cov a, ⟨(hcovspec a ha).1, dsPt .elt a, h, hgelt a⟩, (hcovspec a ha).2⟩
          · obtain ⟨t, y, rfl⟩ := dsPt_surj u
            obtain ⟨-, hshape⟩ := (mgAdj_pt t .elt y a).mp hadj
            rcases hshape with ⟨-, hc, -⟩ | ⟨rfl, -, hmem⟩ | ⟨-, hc, -⟩
            · exact absurd hc (by simp)
            · rcases hmem with ⟨hf, -, hm⟩ | hne
              · exact ⟨y, ⟨hf, dsPt .set y, hu, hgset y⟩, hm⟩
              · exact absurd ha hne
            · exact absurd hc (by simp)
        · calc {s : A | SSFam s ∧ ∃ v, D v ∧ g v = s}.ncard
              ≤ (g '' {v | D v}).ncard :=
                Set.ncard_le_ncard (fun s hs => by
                  obtain ⟨-, v, hv, hgv⟩ := hs
                  exact ⟨v, hv, hgv⟩) (Set.toFinite _)
            _ ≤ {v : dsInterp.Map A | D v}.ncard := Set.ncard_image_le (Set.toFinite _)
            _ ≤ {v : dsInterp.Map A | MGMarked v}.ncard := hcard
            _ = {x : A | SSMarked x}.ncard := hmkcard

end Correctness

/-- **Set Cover FO-reduces to Dominating Set**: elements and sets become
vertices, the sets form a clique, and each set is joined to its elements – and
to the junk, which domination cannot ignore. -/
noncomputable def setCover_fo_reduction_dominatingSet : SetCover ≤ᶠᵒ DominatingSet where
  Tag := DSTag
  dim := 1
  toInterpretation := dsInterp
  correct A _ _ := hasSmallSetCover_iff_hasSmallDominatingSet A

end DomRed

end DescriptiveComplexity
