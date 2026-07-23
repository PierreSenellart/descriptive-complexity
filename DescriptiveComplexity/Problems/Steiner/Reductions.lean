/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Steiner.Defs
import DescriptiveComplexity.OrderWalk
import Mathlib.Data.Fintype.Lattice

/-!
# Vertex Cover reduces to Steiner Tree

The classical reduction, read in the tagged framework
(`DescriptiveComplexity.steinerInterp`, tag `Fin 3`, dimension 2): a marked graph
becomes the bipartite incidence structure of its edges, plus a root joined to
every vertex.

* tag `0` on the diagonal carries the **vertices** of the input;
* tag `1` on adjacent off-diagonal pairs carries the **edges**, which are the
  terminals;
* tag `2` on the diagonal of the minimum carries the **root**, also a
  terminal;
* everything else is junk: isolated, non-terminal, unmarked, and therefore
  never in a chosen set.

A connected set containing all terminals must join every edge-terminal to the
root, and an edge's only neighbours are its two endpoints, so the vertices it
uses form a vertex cover; conversely a vertex cover joins every edge to the
root through one of its endpoints. Since vertices are the only non-terminals,
the budget counts exactly the cover, and the marked diagonal transports the
threshold unchanged.

The root is a *single* fresh element, so – as for the fresh variable of
`DescriptiveComplexity.Problems.NaeSat` – this is an **ordered** reduction: an
interpretation adds elements only by tags, and a tag contributes a whole copy
of the universe, so the root has to be picked out inside its copy as the
minimum (`DescriptiveComplexity.minF`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-- The adjacency symbol over the ordered expansion of marked graphs. -/
abbrev sAdjSym : (Language.markedGraph.sum Language.order).Relations 2 := Sum.inl mgAdj

/-- The mark symbol over the ordered expansion of marked graphs. -/
abbrev sMarkedSym : (Language.markedGraph.sum Language.order).Relations 1 := Sum.inl mgMarked

/-- “The pair is an edge of the input”, as a formula on the coordinates of the
`i`-th argument. -/
private noncomputable def isEdgeF {n : ℕ} (i : Fin n) :
    (Language.markedGraph.sum Language.order).Formula (Fin n × Fin 2) :=
  Relations.formula₂ sAdjSym (Term.var (i, 0)) (Term.var (i, 1)) ⊓
    ∼(Term.equal (Term.var (i, 0)) (Term.var (i, 1)))

/-- “The pair is diagonal”, as a formula on the coordinates of the `i`-th
argument. -/
private noncomputable def isDiagF {n : ℕ} (i : Fin n) :
    (Language.markedGraph.sum Language.order).Formula (Fin n × Fin 2) :=
  Term.equal (Term.var (i, 0)) (Term.var (i, 1))

/-- The three sorts of point of the interpreted structure. Tags built from
constructors, rather than `Fin 3`, so that the tag match inside the defining
formulas reduces definitionally in the characterization proofs. -/
inductive SteinerTag
  /-- A vertex of the input graph, carried by the diagonal. -/
  | vertex
  /-- An edge of the input graph, carried by an adjacent off-diagonal pair. -/
  | edge
  /-- The root, carried by the diagonal of the minimum. -/
  | root
  deriving DecidableEq

instance : Fintype SteinerTag := ⟨{.vertex, .edge, .root}, fun t => by cases t <;> decide⟩

instance : Inhabited SteinerTag := ⟨.vertex⟩

/-- The interpretation of Vertex Cover into Steiner Tree. -/
noncomputable def steinerInterp :
    FOInterpretation (Language.markedGraph.sum Language.order) Language.steinerGraph
      SteinerTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t =>
        match t 0, t 1 with
        | .vertex, .edge =>
            isDiagF 0 ⊓ isEdgeF 1 ⊓
              (Term.equal (Term.var (0, 0)) (Term.var (1, 0)) ⊔
                Term.equal (Term.var (0, 0)) (Term.var (1, 1)))
        | .root, .vertex => isDiagF 0 ⊓ minF (0, 0) ⊓ isDiagF 1
        | _, _ => ⊥
    | _, .terminal => fun t =>
        match t 0 with
        | .edge => isEdgeF 0
        | .root => isDiagF 0 ⊓ minF (0, 0)
        | _ => ⊥
    | _, .marked => fun t =>
        match t 0 with
        | .vertex => isDiagF 0 ⊓ Relations.formula₁ sMarkedSym (Term.var (0, 0))
        | _ => ⊥

section Points

variable {A : Type}

/-- The point carrying the vertex `v`. -/
def vPt (v : A) : steinerInterp.Map A := (.vertex, ![v, v])

/-- The point carrying the (oriented) edge `(u, v)`. -/
def ePt (u v : A) : steinerInterp.Map A := (.edge, ![u, v])

/-- The point carrying the root, at the minimum `m`. -/
def rPt (m : A) : steinerInterp.Map A := (.root, ![m, m])

theorem vPt_injective : Function.Injective (vPt (A := A)) :=
  fun _ _ h => congrArg (fun p : SteinerTag × (Fin 2 → A) => p.2 0) h

end Points

section Characterizations

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]

end Characterizations

/-! #### Shapes

The three master characterizations, from which the point-level lemmas above
and the case analyses of the correctness proof follow. -/

section Shapes

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]

theorem steiner_adj_iff (t t' : SteinerTag) (w w' : Fin 2 → A) :
    STAdj (A := steinerInterp.Map A) (t, w) (t', w') ↔
      (t = .vertex ∧ t' = .edge ∧ w 0 = w 1 ∧ (MGAdj (w' 0) (w' 1) ∧ w' 0 ≠ w' 1) ∧
        (w 0 = w' 0 ∨ w 0 = w' 1)) ∨
      (t = .root ∧ t' = .vertex ∧ w 0 = w 1 ∧ (∀ a : A, w 0 ≤ a) ∧ w' 0 = w' 1) := by
  change RelMap (M := steinerInterp.Map A) stAdj ![(t, w), (t', w')] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> cases t' <;>
    simp [steinerInterp, isDiagF, isEdgeF, MGAdj, realize_minF, Formula.realize_rel₂, and_assoc]

theorem steiner_terminal_iff (t : SteinerTag) (w : Fin 2 → A) :
    STTerminal (A := steinerInterp.Map A) (t, w) ↔
      (t = .edge ∧ MGAdj (w 0) (w 1) ∧ w 0 ≠ w 1) ∨
      (t = .root ∧ w 0 = w 1 ∧ ∀ a : A, w 0 ≤ a) := by
  change RelMap (M := steinerInterp.Map A) stTerminal ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;>
    simp [steinerInterp, isDiagF, isEdgeF, MGAdj, realize_minF, Formula.realize_rel₂]

theorem steiner_marked_iff (t : SteinerTag) (w : Fin 2 → A) :
    STMarked (A := steinerInterp.Map A) (t, w) ↔ t = .vertex ∧ w 0 = w 1 ∧ MGMarked (w 0) := by
  change RelMap (M := steinerInterp.Map A) stMarked ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;>
    simp [steinerInterp, isDiagF, MGMarked, Formula.realize_rel₁]

@[simp]
theorem steiner_adj_ve (v u w : A) :
    STAdj (vPt v) (ePt u w) ↔ (MGAdj u w ∧ u ≠ w) ∧ (v = u ∨ v = w) := by
  simpa [vPt, ePt] using steiner_adj_iff (A := A) .vertex .edge ![v, v] ![u, w]

@[simp]
theorem steiner_adj_rv (m v : A) : STAdj (rPt m) (vPt v) ↔ ∀ a : A, m ≤ a := by
  simpa [rPt, vPt] using steiner_adj_iff (A := A) .root .vertex ![m, m] ![v, v]

@[simp]
theorem steiner_terminal_e (u v : A) : STTerminal (ePt u v) ↔ MGAdj u v ∧ u ≠ v := by
  simpa [ePt] using steiner_terminal_iff (A := A) .edge ![u, v]

@[simp]
theorem steiner_terminal_r (m : A) : STTerminal (rPt m) ↔ ∀ a : A, m ≤ a := by
  simpa [rPt] using steiner_terminal_iff (A := A) .root ![m, m]

@[simp]
theorem steiner_terminal_v (v : A) : ¬STTerminal (vPt v) := by
  simpa [vPt] using steiner_terminal_iff (A := A) .vertex ![v, v]

@[simp]
theorem steiner_marked_v (v : A) : STMarked (vPt v) ↔ MGMarked v := by
  simpa [vPt] using steiner_marked_iff (A := A) .vertex ![v, v]

/-- A marked point of the interpreted structure is a vertex point. -/
theorem steiner_marked_shape {p : steinerInterp.Map A} (h : STMarked p) : ∃ v, p = vPt v := by
  rcases p with ⟨t, w⟩
  obtain ⟨rfl, hdiag, -⟩ := (steiner_marked_iff t w).mp h
  exact ⟨w 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [vPt, hdiag]⟩⟩

/-- A terminal of the interpreted structure is an edge point or the root. -/
theorem steiner_terminal_shape {p : steinerInterp.Map A} (h : STTerminal p) :
    (∃ u v, p = ePt u v ∧ MGAdj u v ∧ u ≠ v) ∨ ∃ r, p = rPt r ∧ ∀ a : A, r ≤ a := by
  rcases p with ⟨t, w⟩
  rcases (steiner_terminal_iff t w).mp h with ⟨rfl, hadj, hne⟩ | ⟨rfl, hdiag, hmin⟩
  · refine Or.inl ⟨w 0, w 1, ?_, hadj, hne⟩
    exact Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [ePt]⟩
  · refine Or.inr ⟨w 0, ?_, hmin⟩
    exact Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [rPt, hdiag]⟩

/-- The neighbours of an edge point are the points of its two endpoints. -/
theorem steiner_link_ePt {S : steinerInterp.Map A → Prop} {u v : A}
    {q : steinerInterp.Map A} (h : Link STAdj S (ePt u v) q) :
    (q = vPt u ∨ q = vPt v) ∧ S q := by
  refine ⟨?_, h.2.1⟩
  rcases q with ⟨t', w'⟩
  rcases h.2.2 with hadj | hadj
  · rcases (steiner_adj_iff .edge t' ![u, v] w').mp hadj with ⟨h0, -⟩ | ⟨h0, -⟩ <;>
      exact absurd h0 (by decide)
  · rcases (steiner_adj_iff t' .edge w' ![u, v]).mp hadj with
      ⟨rfl, -, hdiag, -, hinc⟩ | ⟨-, h1, -⟩
    · have hq : ((SteinerTag.vertex, w') : steinerInterp.Map A) = vPt (w' 0) :=
        Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [vPt, hdiag]⟩
      rcases hinc with hu | hv
      · exact Or.inl (hq.trans (congrArg vPt (by simpa using hu)))
      · exact Or.inr (hq.trans (congrArg vPt (by simpa using hv)))
    · exact absurd h1 (by decide)

end Shapes

/-! #### Counting on the vertex points -/

section Counting

variable {A : Type}

/-- A predicate holding only of vertex points encodes the same number as its
restriction to the vertices. -/
theorem ncard_vPt_eq (P : A → Prop) (Q : steinerInterp.Map A → Prop)
    (hshape : ∀ p, Q p → ∃ v, p = vPt v) (hP : ∀ v : A, Q (vPt v) ↔ P v) :
    {p | Q p}.ncard = {v | P v}.ncard := by
  have hset : {p | Q p} = vPt '' {v | P v} := by
    ext p
    constructor
    · intro hq
      obtain ⟨v, rfl⟩ := hshape p hq
      exact ⟨v, (hP v).mp hq, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hP v).mpr hv
  rw [hset, Set.ncard_image_of_injective _ vPt_injective]

end Counting

/-! #### Correctness -/

section Correctness

variable (A : Type) [Language.markedGraph.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- Correctness of the interpretation: a graph has a vertex cover at most as
large as its marked set iff the associated incidence structure has a Steiner
tree of the same budget. -/
theorem hasSmallVertexCover_iff_steiner_map :
    HasSmallVertexCover A ↔ HasSmallSteinerTree (steinerInterp.Map A) := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  haveI : Finite (steinerInterp.Map A) := steinerInterp.map_finite A
  have hmarked : {p : steinerInterp.Map A | STMarked p}.ncard = {v : A | MGMarked v}.ncard :=
    ncard_vPt_eq MGMarked _ (fun _ hp => steiner_marked_shape hp) fun v => steiner_marked_v v
  have hroot : STTerminal (rPt m (A := A)) := (steiner_terminal_r m).mpr hm
  constructor
  · rintro ⟨hfin, C, hcov, hcard⟩
    haveI := hfin
    refine ⟨inferInstance,
      fun p => STTerminal p ∨ ∃ v, C v ∧ p = vPt v, fun x hx => Or.inl hx, ?_, ?_⟩
    · -- connectivity: every member reaches the root
      have hlinkroot : ∀ v : A, C v →
          Link STAdj (fun p => STTerminal p ∨ ∃ v, C v ∧ p = vPt v) (vPt v) (rPt m) := by
        intro v hv
        exact ⟨Or.inr ⟨v, hv, rfl⟩, Or.inl hroot,
          Or.inr ((steiner_adj_rv m v).mpr hm)⟩
      have hreach : ∀ p, (STTerminal p ∨ ∃ v, C v ∧ p = vPt v) →
          Relation.ReflTransGen
            (Link STAdj fun p => STTerminal p ∨ ∃ v, C v ∧ p = vPt v) p (rPt m) := by
        rintro p (hp | ⟨v, hv, rfl⟩)
        · rcases steiner_terminal_shape hp with ⟨u, v, rfl, hadj, hne⟩ | ⟨r, rfl, hminr⟩
          · -- an edge terminal: step to a covering endpoint, then to the root
            have hC := hcov u v hne hadj
            rcases hC with hu | hv
            · exact Relation.ReflTransGen.head
                (link_symm ⟨Or.inr ⟨u, hu, rfl⟩, Or.inl hp,
                  Or.inl ((steiner_adj_ve u u v).mpr ⟨⟨hadj, hne⟩, Or.inl rfl⟩)⟩)
                (Relation.ReflTransGen.single (hlinkroot u hu))
            · exact Relation.ReflTransGen.head
                (link_symm ⟨Or.inr ⟨v, hv, rfl⟩, Or.inl hp,
                  Or.inl ((steiner_adj_ve v u v).mpr ⟨⟨hadj, hne⟩, Or.inr rfl⟩)⟩)
                (Relation.ReflTransGen.single (hlinkroot v hv))
          · have : r = m := le_antisymm (hminr m) (hm r)
            subst this
            exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single (hlinkroot v hv)
      intro x y hx hy
      exact (hreach x hx).trans
        (reflTransGen_symm (fun _ _ hab => link_symm hab) (hreach y hy))
    · -- counting: the non-terminals of the chosen set are the cover
      have hne : {p : steinerInterp.Map A |
          (STTerminal p ∨ ∃ v, C v ∧ p = vPt v) ∧ ¬STTerminal p}.ncard
            = {v : A | C v}.ncard := by
        refine ncard_vPt_eq C _ (fun p hp => ?_) fun v => ?_
        · rcases hp.1 with h | ⟨v, -, rfl⟩
          · exact absurd h hp.2
          · exact ⟨v, rfl⟩
        · exact ⟨fun h => by
            rcases h.1 with h' | ⟨v', hv', hvv⟩
            · exact absurd h' (steiner_terminal_v v)
            · exact vPt_injective hvv.symm ▸ hv',
          fun h => ⟨Or.inr ⟨v, h, rfl⟩, steiner_terminal_v v⟩⟩
      rw [hne, hmarked]
      exact hcard
  · rintro ⟨hfin, S, hterms, hconn, hcard⟩
    have hA : Finite A := Finite.of_injective _ (vPt_injective (A := A))
    haveI := hA
    refine ⟨hA, fun v => S (vPt v), fun x y hxy hadj => ?_, ?_⟩
    · -- the path from the edge terminal to the root starts at an endpoint
      have hex : S (ePt x y) := hterms _ ((steiner_terminal_e x y).mpr ⟨hadj, hxy⟩)
      have hrt : S (rPt m) := hterms _ hroot
      have hpath := hconn (ePt x y) (rPt m) hex hrt
      rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨q, hlink, -⟩
      · have htag : SteinerTag.edge = SteinerTag.root :=
          congrArg (fun p : SteinerTag × (Fin 2 → A) => p.1) heq
        exact absurd htag (by decide)
      · obtain ⟨hq, hqS⟩ := steiner_link_ePt hlink
        rcases hq with rfl | rfl
        · exact Or.inl hqS
        · exact Or.inr hqS
    · -- the cover injects into the non-terminals of the chosen set
      have hsub : vPt '' {v : A | S (vPt v)} ⊆
          {p : steinerInterp.Map A | S p ∧ ¬STTerminal p} := by
        rintro p ⟨v, hv, rfl⟩
        exact ⟨hv, steiner_terminal_v v⟩
      calc {v : A | S (vPt v)}.ncard
          = (vPt '' {v : A | S (vPt v)}).ncard :=
            (Set.ncard_image_of_injective _ vPt_injective).symm
        _ ≤ {p : steinerInterp.Map A | S p ∧ ¬STTerminal p}.ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {p : steinerInterp.Map A | STMarked p}.ncard := hcard
        _ = {v : A | MGMarked v}.ncard := hmarked

end Correctness

/-- **Vertex Cover ordered-FO-reduces to Steiner Tree**: the edges become the
terminals, the vertices the available Steiner points, and the minimum of a
spare copy the root joining them all. -/
noncomputable def vertexCover_ordered_fo_reduction_steinerTree :
    VertexCover ≤ᶠᵒ[≤] SteinerTree where
  Tag := SteinerTag
  dim := 2
  toInterpretation := steinerInterp
  correct A _ _ _ _ := hasSmallVertexCover_iff_steiner_map A

end DescriptiveComplexity
