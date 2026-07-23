/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily.Defs
import DescriptiveComplexity.Problems.CliqueFamily.Defs

/-!
# Hardness of the set family: graphs as incidence systems

One interpretation, read twice. `DescriptiveComplexity.edgeIncidenceInterp` maps a
marked graph to the incidence system of its edges: the ground elements are the
(oriented) edges, the sets are the vertices, and a vertex-set contains the
edges it is an endpoint of. It has tag `Unit` and dimension 2, and splits the
pairs of vertices in three: an *off-diagonal adjacent* pair is the ground
element for that edge, a *diagonal* pair `(v, v)` is the vertex-set of `v`,
and any other pair is junk that no relation of the output mentions. The
threshold is transported to the marked diagonal, so the interpreted marked set
is in bijection with the input one and encodes the same number.

Under this reading,

* a set of vertices meets every edge iff the family of its vertex-sets covers
  every ground element, giving
  `DescriptiveComplexity.vertexCover_fo_reduction_setCover`;
* two distinct vertices are non-adjacent iff their vertex-sets are disjoint
  (`DescriptiveComplexity.exists_elem_mem_both_iff`), giving
  `DescriptiveComplexity.indSet_fo_reduction_setPacking`.

Each edge gives *two* ground elements, one per orientation, and this is
harmless: the two carry the same constraint in both readings. The cardinality
bookkeeping – the interpreted family and marked set are diagonal, hence in
bijection with their vertex counterparts – is `DescriptiveComplexity.ncard_diag_eq`
below, the unary representation's counting step for both reductions.

The vertex-sets are named (`DescriptiveComplexity.diagPt`) and characterized by an
iff lemma (`DescriptiveComplexity.eq_diagPt_iff`) rather than handled by
projections. The reason is that `FOInterpretation.Map` is a non-reducible
definition: a statement phrased over the raw `Tag × (Fin d → A)` is ill-typed
at the transparency `rw`/`simp` match at, even though `exact` accepts it, and
destructuring an element of the interpreted universe inside a set-builder
membership goal produces exactly such a statement. Keeping every hypothesis in
the shape `∀ p, Q p → ∃ v, p = diagPt v` avoids the issue outright.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### The interpretation -/

/-- The edge-incidence interpretation of a marked graph as a set system: the
ground elements are the (oriented) edges, the sets are the vertices, sitting
on the diagonal, and a vertex-set contains the edges it is an endpoint of.
The threshold moves to the marked diagonal, encoding the same number. -/
def edgeIncidenceInterp :
    FOInterpretation Language.markedGraph Language.setSystem Unit 2 where
  relFormula {n} R :=
    match n, R with
    | _, .elem => fun _ =>
        mgAdj.formula₂ (Term.var (0, 0)) (Term.var (0, 1)) ⊓
          ∼(Term.equal (Term.var (0, 0)) (Term.var (0, 1)))
    | _, .fam => fun _ => Term.equal (Term.var (0, 0)) (Term.var (0, 1))
    | _, .mem => fun _ =>
        Term.equal (Term.var (1, 0)) (Term.var (1, 1)) ⊓
          (Term.equal (Term.var (1, 0)) (Term.var (0, 0)) ⊔
            Term.equal (Term.var (1, 0)) (Term.var (0, 1)))
    | _, .marked => fun _ =>
        Term.equal (Term.var (0, 0)) (Term.var (0, 1)) ⊓
          mgMarked.formula₁ (Term.var (0, 0))

/-- The edge-incidence interpretation is quantifier-free. -/
theorem edgeIncidenceInterp_isQuantifierFree : edgeIncidenceInterp.IsQuantifierFree := by
  intro n R t
  cases R with
  | elem => exact (IsAtomic.rel _ _).isQF.inf ((IsAtomic.equal _ _).isQF.imp isQF_bot)
  | fam => exact (IsAtomic.equal _ _).isQF
  | mem =>
    exact (IsAtomic.equal _ _).isQF.inf ((IsAtomic.equal _ _).isQF.sup (IsAtomic.equal _ _).isQF)
  | marked => exact (IsAtomic.equal _ _).isQF.inf (IsAtomic.rel _ _).isQF

section EdgeIncidenceCharacterizations

variable {A : Type} [Language.markedGraph.Structure A]

@[simp]
theorem edgeIncidence_elem (w : Fin 2 → A) :
    RelMap (M := edgeIncidenceInterp.Map A) ssElem ![((), w)] ↔
      RelMap mgAdj ![w 0, w 1] ∧ w 0 ≠ w 1 := by
  rw [FOInterpretation.relMap_map]
  simp [edgeIncidenceInterp, Formula.realize_rel₂]

@[simp]
theorem edgeIncidence_fam (w : Fin 2 → A) :
    RelMap (M := edgeIncidenceInterp.Map A) ssFam ![((), w)] ↔ w 0 = w 1 := by
  rw [FOInterpretation.relMap_map]
  simp [edgeIncidenceInterp]

@[simp]
theorem edgeIncidence_mem (w₁ w₂ : Fin 2 → A) :
    RelMap (M := edgeIncidenceInterp.Map A) ssMem ![((), w₁), ((), w₂)] ↔
      w₂ 0 = w₂ 1 ∧ (w₂ 0 = w₁ 0 ∨ w₂ 0 = w₁ 1) := by
  rw [FOInterpretation.relMap_map]
  simp [edgeIncidenceInterp]

@[simp]
theorem edgeIncidence_marked (w : Fin 2 → A) :
    RelMap (M := edgeIncidenceInterp.Map A) ssMarked ![((), w)] ↔
      w 0 = w 1 ∧ RelMap mgMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [edgeIncidenceInterp, Formula.realize_rel₁]

end EdgeIncidenceCharacterizations

/-! ### The counting step

Both the interpreted family and the interpreted marked set live on the
diagonal, which is in bijection with the vertex set; so the numbers they
encode are the numbers encoded by their vertex counterparts. -/

section Counting

variable {A : Type}

/-- A vertex, as a set of the interpreted set system: the diagonal pair. -/
def diagPt (v : A) : edgeIncidenceInterp.Map A := ((), ![v, v])

/-- A tagged pair is the vertex-set of `v` exactly when both its coordinates
are `v`. Stating the diagonal condition this way, rather than by projections,
is what keeps the proofs about the interpreted structure free of
destructuring (see the module docstring above). -/
theorem eq_diagPt_iff (t : Unit) (w : Fin 2 → A) (v : A) :
    ((t, w) : edgeIncidenceInterp.Map A) = diagPt v ↔ w 0 = v ∧ w 1 = v := by
  constructor
  · intro h
    have hw : w = ![v, v] := congrArg (fun p : Unit × (Fin 2 → A) => p.2) h
    exact ⟨by rw [hw]; simp, by rw [hw]; simp⟩
  · rintro ⟨h0, h1⟩
    cases t
    refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
    funext i
    fin_cases i <;> simp [diagPt, h0, h1]

/-- Distinct vertices give distinct vertex-sets. -/
theorem diagPt_injective : Function.Injective (diagPt (A := A)) := by
  intro v v' h
  simpa using ((eq_diagPt_iff () ![v, v] v').mp h).1

/-- A predicate that only holds of diagonal pairs encodes the same number as
its restriction to the diagonal, read as a predicate on vertices. -/
theorem ncard_diag_eq (P : A → Prop) (Q : edgeIncidenceInterp.Map A → Prop)
    (hdiag : ∀ p, Q p → ∃ v, p = diagPt v) (hP : ∀ v : A, Q (diagPt v) ↔ P v) :
    {p | Q p}.ncard = {v | P v}.ncard := by
  have hset : {p | Q p} = diagPt '' {v | P v} := by
    ext p
    constructor
    · intro hq
      obtain ⟨v, rfl⟩ := hdiag p hq
      exact ⟨v, (hP v).mp hq, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hP v).mpr hv
  rw [hset, Set.ncard_image_of_injective _ diagPt_injective]

/-- The subfamily of vertex-sets attached to a set of vertices: the diagonal
pairs of its members. Shared by the reductions of Vertex Cover to Set Cover
and of Independent Set to Set Packing, which both send a set of vertices to
the family of its vertex-sets. -/
def vertexFamily (C : A → Prop) : edgeIncidenceInterp.Map A → Prop :=
  fun p => ∃ v, C v ∧ p = diagPt v

/-- The family of vertex-sets of a set of vertices encodes the same number as
the set itself. -/
theorem ncard_vertexFamily (C : A → Prop) :
    {p | vertexFamily C p}.ncard = {v | C v}.ncard :=
  ncard_diag_eq C (vertexFamily C) (fun _ h => ⟨h.choose, h.choose_spec.2⟩)
    fun v => ⟨fun ⟨_, hv', heq⟩ => diagPt_injective heq ▸ hv', fun hv => ⟨v, hv, rfl⟩⟩

end Counting

section EdgeIncidenceCorrectness

variable (A : Type) [Language.markedGraph.Structure A]

/-- The interpreted marked set lives on the diagonal. -/
theorem marked_diag :
    ∀ p : edgeIncidenceInterp.Map A, SSMarked p → ∃ v, p = diagPt v := by
  rintro ⟨⟨⟩, w⟩ hw
  exact ⟨w 0, (eq_diagPt_iff () w (w 0)).mpr ⟨rfl, ((edgeIncidence_marked w).mp hw).1.symm⟩⟩

/-- The interpreted marked set encodes the same number as the input one. -/
theorem ncard_marked :
    {p : edgeIncidenceInterp.Map A | SSMarked p}.ncard = {v : A | MGMarked v}.ncard :=
  ncard_diag_eq (A := A) MGMarked (fun p => SSMarked p) (marked_diag A)
    fun v => (edgeIncidence_marked (A := A) ![v, v]).trans (by simp [MGMarked])

/-- Correctness of the edge-incidence interpretation: a graph has a vertex
cover at most as large as its marked set iff the associated set system has a
cover at most as large as its marked set. -/
theorem hasSmallVertexCover_iff_setCover_map :
    HasSmallVertexCover A ↔ HasSmallSetCover (edgeIncidenceInterp.Map A) := by
  constructor
  · rintro ⟨hfin, C, hcov, hcard⟩
    haveI := hfin
    refine ⟨edgeIncidenceInterp.map_finite A, vertexFamily C, ?_, ?_, ?_⟩
    · rintro s ⟨v, -, rfl⟩
      exact (edgeIncidence_fam ![v, v]).mpr (by simp)
    · rintro ⟨⟨⟩, w⟩ hx
      obtain ⟨hadj, hne⟩ := (edgeIncidence_elem w).mp hx
      rcases hcov (w 0) (w 1) hne hadj with h0 | h1
      · exact ⟨diagPt (w 0), ⟨w 0, h0, rfl⟩,
          (edgeIncidence_mem w ![w 0, w 0]).mpr ⟨by simp, Or.inl (by simp)⟩⟩
      · exact ⟨diagPt (w 1), ⟨w 1, h1, rfl⟩,
          (edgeIncidence_mem w ![w 1, w 1]).mpr ⟨by simp, Or.inr (by simp)⟩⟩
    · exact (ncard_vertexFamily C).trans_le (hcard.trans (ncard_marked A).ge)
  · rintro ⟨hfin, G, hGfam, hcov, hcard⟩
    haveI := hfin
    have hA : Finite A := Finite.of_injective _ (diagPt_injective (A := A))
    haveI := hA
    have hdiag : ∀ p : edgeIncidenceInterp.Map A, G p → ∃ v, p = diagPt v := by
      rintro ⟨⟨⟩, w⟩ hw
      exact ⟨w 0, (eq_diagPt_iff () w (w 0)).mpr
        ⟨rfl, ((edgeIncidence_fam w).mp (hGfam _ hw)).symm⟩⟩
    refine ⟨hA, fun v => G (diagPt v), ?_, ?_⟩
    · intro x y hxy hadj
      obtain ⟨s, hsG, hsMem⟩ := hcov ((), ![x, y])
        ((edgeIncidence_elem ![x, y]).mpr ⟨hadj, hxy⟩)
      obtain ⟨v, rfl⟩ := hdiag s hsG
      obtain ⟨-, hend⟩ := (edgeIncidence_mem ![x, y] ![v, v]).mp hsMem
      rcases hend with h | h
      · exact Or.inl (by simpa [show v = x by simpa using h] using hsG)
      · exact Or.inr (by simpa [show v = y by simpa using h] using hsG)
    · refine le_trans (le_of_eq ?_) (hcard.trans (ncard_marked A).le)
      exact (ncard_diag_eq _ G hdiag fun _ => Iff.rfl).symm

end EdgeIncidenceCorrectness

/-- **Vertex Cover FO-reduces to Set Cover**: the edges are the ground
elements, the vertices the sets that cover them. -/
def vertexCover_fo_reduction_setCover : VertexCover ≤ᶠᵒ SetCover where
  Tag := Unit
  dim := 2
  toInterpretation := edgeIncidenceInterp
  correct A _ _ := hasSmallVertexCover_iff_setCover_map A

/-! ### Independent Set reduces to Set Packing

The same interpretation, read again: a set of vertices is independent exactly
when the family of their vertex-sets is pairwise disjoint. -/

section Correctness

variable {A : Type} [Language.markedGraph.Structure A]

/-- Two distinct vertices have intersecting sets of incident edges exactly
when they are adjacent (in either direction). This is the whole content of
the reduction; note that only *ground elements*, i.e. genuine edges, count as
witnesses of an intersection. -/
theorem exists_elem_mem_both_iff {u v : A} (huv : u ≠ v) :
    (∃ x : edgeIncidenceInterp.Map A, SSElem x ∧ SSMem x (diagPt u) ∧ SSMem x (diagPt v)) ↔
      MGAdj u v ∨ MGAdj v u := by
  constructor
  · rintro ⟨⟨⟨⟩, w⟩, hx, hmu, hmv⟩
    obtain ⟨hadj, hne⟩ := (edgeIncidence_elem w).mp hx
    obtain ⟨-, hu⟩ := (edgeIncidence_mem w ![u, u]).mp hmu
    obtain ⟨-, hv⟩ := (edgeIncidence_mem w ![v, v]).mp hmv
    simp only [Matrix.cons_val_zero] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact absurd (hu.trans hv.symm) huv
    · exact Or.inl (by rw [hu, hv]; exact hadj)
    · exact Or.inr (by rw [hu, hv]; exact hadj)
    · exact absurd (hu.trans hv.symm) huv
  · intro h
    rcases h with h | h
    · exact ⟨((), ![u, v]), (edgeIncidence_elem ![u, v]).mpr ⟨h, huv⟩,
        (edgeIncidence_mem ![u, v] ![u, u]).mpr ⟨rfl, Or.inl rfl⟩,
        (edgeIncidence_mem ![u, v] ![v, v]).mpr ⟨rfl, Or.inr rfl⟩⟩
    · exact ⟨((), ![v, u]), (edgeIncidence_elem ![v, u]).mpr ⟨h, huv.symm⟩,
        (edgeIncidence_mem ![v, u] ![u, u]).mpr ⟨rfl, Or.inr rfl⟩,
        (edgeIncidence_mem ![v, u] ![v, v]).mpr ⟨rfl, Or.inl rfl⟩⟩

/-- Correctness of the edge-incidence interpretation as a reduction of
Independent Set: a graph has an independent set at least as large as its
marked set iff the associated set system has a packing at least as large as
its marked set. -/
theorem hasLargeIndependentSet_iff_setPacking_map (A : Type)
    [Language.markedGraph.Structure A] :
    HasLargeIndependentSet A ↔ HasLargeSetPacking (edgeIncidenceInterp.Map A) := by
  constructor
  · rintro ⟨hfin, S, hS, hcard⟩
    haveI := hfin
    refine ⟨edgeIncidenceInterp.map_finite A, vertexFamily S, ?_, ?_, ?_⟩
    · rintro s ⟨v, -, rfl⟩
      exact (edgeIncidence_fam ![v, v]).mpr (by simp)
    · rintro s s' ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ hne x hx ⟨hmu, hmv⟩
      have huv : u ≠ v := fun h => hne (by rw [h])
      rcases (exists_elem_mem_both_iff huv).mp ⟨x, hx, hmu, hmv⟩ with h | h
      · exact hS u v hu hv huv h
      · exact hS v u hv hu huv.symm h
    · exact ((ncard_marked A).trans_le hcard).trans (ncard_vertexFamily S).ge
  · rintro ⟨hfin, G, hGfam, hdisj, hcard⟩
    haveI := hfin
    have hA : Finite A := Finite.of_injective _ (diagPt_injective (A := A))
    haveI := hA
    have hdiag : ∀ p : edgeIncidenceInterp.Map A, G p → ∃ v, p = diagPt v := by
      rintro ⟨⟨⟩, w⟩ hw
      exact ⟨w 0, (eq_diagPt_iff () w (w 0)).mpr
        ⟨rfl, ((edgeIncidence_fam w).mp (hGfam _ hw)).symm⟩⟩
    refine ⟨hA, fun v => G (diagPt v), fun u v hu hv huv hadj => ?_, ?_⟩
    · obtain ⟨x, hx, hmu, hmv⟩ := (exists_elem_mem_both_iff huv).mpr (Or.inl hadj)
      exact hdisj _ _ hu hv (fun h => huv (diagPt_injective h)) x hx ⟨hmu, hmv⟩
    · refine le_trans ((ncard_marked A).symm.trans_le hcard) (le_of_eq ?_)
      exact ncard_diag_eq _ G hdiag fun _ => Iff.rfl

end Correctness

/-- **Independent Set FO-reduces to Set Packing**: the vertices become the
sets of edges they are incident to, and independence becomes disjointness. -/
def indSet_fo_reduction_setPacking : IndependentSet ≤ᶠᵒ SetPacking where
  Tag := Unit
  dim := 2
  toInterpretation := edgeIncidenceInterp
  correct A _ _ := hasLargeIndependentSet_iff_setPacking_map A
end DescriptiveComplexity
