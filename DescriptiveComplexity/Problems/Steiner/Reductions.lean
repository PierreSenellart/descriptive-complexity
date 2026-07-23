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

/-! ### The edge-weighted variant

The same construction, with one clause changed: the marked set must now count
`k` *plus one unit per edge point*, since a Steiner tree of the incidence
structure spends one edge joining each edge point to an endpoint before it can
spend anything on the cover. Marking the edge points themselves is exactly
that budget, and it needs no arithmetic in the formulas. -/

/-- The interpretation of Vertex Cover into the edge-weighted Steiner Tree:
as `DescriptiveComplexity.steinerInterp`, but the marked set also contains every edge
point. -/
noncomputable def steinerEdgeInterp :
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
        | .edge => isEdgeF 0
        | _ => ⊥

section EdgePoints

variable {A : Type}

/-- The vertex point of the edge-weighted interpretation. -/
def veePt (v : A) : steinerEdgeInterp.Map A := (.vertex, ![v, v])

/-- The edge point of the edge-weighted interpretation. -/
def eeePt (u v : A) : steinerEdgeInterp.Map A := (.edge, ![u, v])

/-- The root point of the edge-weighted interpretation. -/
def reePt (m : A) : steinerEdgeInterp.Map A := (.root, ![m, m])

theorem veePt_injective : Function.Injective (veePt (A := A)) :=
  fun _ _ h => congrArg (fun p : SteinerTag × (Fin 2 → A) => p.2 0) h

end EdgePoints

section EdgeShapes

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]

theorem steinerE_adj_iff (t t' : SteinerTag) (w w' : Fin 2 → A) :
    STAdj (A := steinerEdgeInterp.Map A) (t, w) (t', w') ↔
      (t = .vertex ∧ t' = .edge ∧ w 0 = w 1 ∧ (MGAdj (w' 0) (w' 1) ∧ w' 0 ≠ w' 1) ∧
        (w 0 = w' 0 ∨ w 0 = w' 1)) ∨
      (t = .root ∧ t' = .vertex ∧ w 0 = w 1 ∧ (∀ a : A, w 0 ≤ a) ∧ w' 0 = w' 1) := by
  change RelMap (M := steinerEdgeInterp.Map A) stAdj ![(t, w), (t', w')] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> cases t' <;>
    simp [steinerEdgeInterp, isDiagF, isEdgeF, MGAdj, realize_minF, Formula.realize_rel₂,
      and_assoc]

theorem steinerE_terminal_iff (t : SteinerTag) (w : Fin 2 → A) :
    STTerminal (A := steinerEdgeInterp.Map A) (t, w) ↔
      (t = .edge ∧ MGAdj (w 0) (w 1) ∧ w 0 ≠ w 1) ∨
      (t = .root ∧ w 0 = w 1 ∧ ∀ a : A, w 0 ≤ a) := by
  change RelMap (M := steinerEdgeInterp.Map A) stTerminal ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;>
    simp [steinerEdgeInterp, isDiagF, isEdgeF, MGAdj, realize_minF, Formula.realize_rel₂]

theorem steinerE_marked_iff (t : SteinerTag) (w : Fin 2 → A) :
    STMarked (A := steinerEdgeInterp.Map A) (t, w) ↔
      (t = .vertex ∧ w 0 = w 1 ∧ MGMarked (w 0)) ∨
      (t = .edge ∧ MGAdj (w 0) (w 1) ∧ w 0 ≠ w 1) := by
  change RelMap (M := steinerEdgeInterp.Map A) stMarked ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;>
    simp [steinerEdgeInterp, isDiagF, isEdgeF, MGMarked, MGAdj, Formula.realize_rel₁,
      Formula.realize_rel₂]

@[simp]
theorem steinerE_adj_ve (v u w : A) :
    STAdj (veePt v) (eeePt u w) ↔ (MGAdj u w ∧ u ≠ w) ∧ (v = u ∨ v = w) := by
  simpa [veePt, eeePt] using steinerE_adj_iff (A := A) .vertex .edge ![v, v] ![u, w]

@[simp]
theorem steinerE_adj_rv (m v : A) : STAdj (reePt m) (veePt v) ↔ ∀ a : A, m ≤ a := by
  simpa [reePt, veePt] using steinerE_adj_iff (A := A) .root .vertex ![m, m] ![v, v]

@[simp]
theorem steinerE_terminal_e (u v : A) : STTerminal (eeePt u v) ↔ MGAdj u v ∧ u ≠ v := by
  simpa [eeePt] using steinerE_terminal_iff (A := A) .edge ![u, v]

@[simp]
theorem steinerE_terminal_r (m : A) : STTerminal (reePt m) ↔ ∀ a : A, m ≤ a := by
  simpa [reePt] using steinerE_terminal_iff (A := A) .root ![m, m]

@[simp]
theorem steinerE_terminal_v (v : A) : ¬STTerminal (veePt v) := by
  simpa [veePt] using steinerE_terminal_iff (A := A) .vertex ![v, v]

@[simp]
theorem steinerE_marked_v (v : A) : STMarked (veePt v) ↔ MGMarked v := by
  simpa [veePt] using steinerE_marked_iff (A := A) .vertex ![v, v]

@[simp]
theorem steinerE_marked_e (u v : A) : STMarked (eeePt u v) ↔ MGAdj u v ∧ u ≠ v := by
  simpa [eeePt] using steinerE_marked_iff (A := A) .edge ![u, v]

/-- The neighbours of an edge point are the points of its two endpoints. -/
theorem steinerE_link_ePt {S : steinerEdgeInterp.Map A → Prop} {u v : A}
    {q : steinerEdgeInterp.Map A} (h : Link STAdj S (eeePt u v) q) :
    (q = veePt u ∨ q = veePt v) ∧ S q := by
  refine ⟨?_, h.2.1⟩
  rcases q with ⟨t', w'⟩
  rcases h.2.2 with hadj | hadj
  · rcases (steinerE_adj_iff .edge t' ![u, v] w').mp hadj with ⟨h0, -⟩ | ⟨h0, -⟩ <;>
      exact absurd h0 (by decide)
  · rcases (steinerE_adj_iff t' .edge w' ![u, v]).mp hadj with
      ⟨rfl, -, hdiag, -, hinc⟩ | ⟨-, h1, -⟩
    · have hq : ((SteinerTag.vertex, w') : steinerEdgeInterp.Map A) = veePt (w' 0) :=
        Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [veePt, hdiag]⟩
      rcases hinc with hu | hv
      · exact Or.inl (hq.trans (congrArg veePt (by simpa using hu)))
      · exact Or.inr (hq.trans (congrArg veePt (by simpa using hv)))
    · exact absurd h1 (by decide)

end EdgeShapes

/-! #### Correctness of the edge-weighted reduction -/

section EdgeCorrectness

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]

/-- The edge points of the interpreted structure: what the marked set pays for
before any cover. -/
def EdgePtSet (A : Type) [Language.markedGraph.Structure A] [LinearOrder A] :
    Set (steinerEdgeInterp.Map A) :=
  {p | ∃ u v, (MGAdj u v ∧ u ≠ v) ∧ p = eeePt u v}

theorem steinerE_terminal_shape {p : steinerEdgeInterp.Map A} (h : STTerminal p) :
    p ∈ EdgePtSet A ∨ ∃ r, p = reePt r ∧ ∀ a : A, r ≤ a := by
  rcases p with ⟨t, w⟩
  rcases (steinerE_terminal_iff t w).mp h with ⟨rfl, hadj, hne⟩ | ⟨rfl, hdiag, hmin⟩
  · exact Or.inl ⟨w 0, w 1, ⟨hadj, hne⟩,
      Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [eeePt]⟩⟩
  · exact Or.inr ⟨w 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => by
      fin_cases i <;> simp [reePt, hdiag]⟩, hmin⟩

theorem steinerE_marked_shape {p : steinerEdgeInterp.Map A} (h : STMarked p) :
    (∃ v, p = veePt v ∧ MGMarked v) ∨ p ∈ EdgePtSet A := by
  rcases p with ⟨t, w⟩
  rcases (steinerE_marked_iff t w).mp h with ⟨rfl, hdiag, hm⟩ | ⟨rfl, hadj, hne⟩
  · exact Or.inl ⟨w 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => by
      fin_cases i <;> simp [veePt, hdiag]⟩, hm⟩
  · exact Or.inr ⟨w 0, w 1, ⟨hadj, hne⟩,
      Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> simp [eeePt]⟩⟩

/-- The marked set of the interpreted structure is one unit per edge point,
plus the marked vertices. -/
theorem ncard_marked_edge [Finite A] :
    {p : steinerEdgeInterp.Map A | STMarked p}.ncard
      = {v : A | MGMarked v}.ncard + (EdgePtSet A).ncard := by
  haveI : Finite (steinerEdgeInterp.Map A) := steinerEdgeInterp.map_finite A
  have hdisj : Disjoint (veePt '' {v : A | MGMarked v}) (EdgePtSet A) := by
    rw [Set.disjoint_left]
    rintro p ⟨v, -, rfl⟩ ⟨u, w, -, hp⟩
    have htag : SteinerTag.vertex = SteinerTag.edge :=
      congrArg (fun q : SteinerTag × (Fin 2 → A) => q.1) hp
    exact absurd htag (by decide)
  have hset : {p : steinerEdgeInterp.Map A | STMarked p}
      = veePt '' {v : A | MGMarked v} ∪ EdgePtSet A := by
    ext p
    constructor
    · intro hp
      rcases steinerE_marked_shape hp with ⟨v, rfl, hv⟩ | he
      · exact Or.inl ⟨v, hv, rfl⟩
      · exact Or.inr he
    · rintro (⟨v, hv, rfl⟩ | ⟨u, w, hedge, rfl⟩)
      · exact (steinerE_marked_v v).mpr hv
      · exact (steinerE_marked_e u w).mpr hedge
  rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ veePt_injective]

end EdgeCorrectness

section CoverPick

variable {A : Type}

open Classical in
/-- The endpoint through which an edge is attached to the cover. -/
private noncomputable def coverPick (C : A → Prop) (u v : A) : A := if C u then u else v

private theorem coverPick_mem (C : A → Prop) {u v : A} (h : C u ∨ C v) :
    C (coverPick C u v) := by
  classical
  rw [coverPick]
  split
  · assumption
  · exact h.resolve_left ‹¬C u›

private theorem coverPick_eq (C : A → Prop) (u v : A) :
    coverPick C u v = u ∨ coverPick C u v = v := by
  classical
  rw [coverPick]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end CoverPick

section EdgeCorrectness'

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]

/-- Correctness of the edge-weighted interpretation: a graph has a vertex
cover at most as large as its marked set iff the associated incidence
structure has an edge-weighted Steiner tree within the enlarged budget. -/
theorem hasSmallVertexCover_iff_edgeSteiner_map (A : Type)
    [Language.markedGraph.Structure A] [LinearOrder A] [Finite A] [Nonempty A] :
    HasSmallVertexCover A ↔ HasSmallEdgeSteinerTree (steinerEdgeInterp.Map A) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  haveI : Finite (steinerEdgeInterp.Map A) := steinerEdgeInterp.map_finite A
  have hroot : STTerminal (reePt m (A := A)) := (steinerE_terminal_r m).mpr hm
  have hedgeS : ∀ p ∈ EdgePtSet A, STTerminal p := by
    rintro p ⟨u, w, hedge, rfl⟩
    exact (steinerE_terminal_e u w).mpr hedge
  have hedge_ne_root : ∀ p ∈ EdgePtSet A, p ≠ reePt m := by
    rintro p ⟨u, w, -, rfl⟩ h
    have htag : SteinerTag.edge = SteinerTag.root :=
      congrArg (fun q : SteinerTag × (Fin 2 → A) => q.1) h
    exact absurd htag (by decide)
  constructor
  · rintro ⟨hfin, C, hcov, hcard⟩
    haveI := hfin
    set Tset : steinerEdgeInterp.Map A → steinerEdgeInterp.Map A → Prop :=
      fun p q => (∃ v, C v ∧ p = reePt m ∧ q = veePt v) ∨
        (q ∈ EdgePtSet A ∧ p = veePt (coverPick C (q.2 0) (q.2 1))) with hTdef
    set Sset : steinerEdgeInterp.Map A → Prop :=
      fun p => STTerminal p ∨ ∃ v, C v ∧ p = veePt v with hSdef
    refine ⟨inferInstance, Tset, Sset, ?_, fun x hx => Or.inl hx, ?_, ?_⟩
    · -- the chosen pairs are edges of the interpreted graph
      rintro a b (⟨v, hv, rfl, rfl⟩ | ⟨⟨u, w, hedge, rfl⟩, rfl⟩)
      · exact (steinerE_adj_rv m v).mpr hm
      · exact (steinerE_adj_ve _ u w).mpr ⟨hedge, by
          simpa [eeePt] using coverPick_eq C u w⟩
    · -- connectivity, through the root
      have hlinkroot : ∀ v : A, C v → Link Tset Sset (veePt v) (reePt m) :=
        fun v hv => ⟨Or.inr ⟨v, hv, rfl⟩, Or.inl hroot, Or.inr (Or.inl ⟨v, hv, rfl, rfl⟩)⟩
      have hreach : ∀ p, Sset p → Relation.ReflTransGen (Link Tset Sset) p (reePt m) := by
        rintro p (hp | ⟨v, hv, rfl⟩)
        · rcases steinerE_terminal_shape hp with ⟨u, w, hedge, rfl⟩ | ⟨r, rfl, hminr⟩
          · have hpick : C (coverPick C u w) := coverPick_mem C (hcov u w hedge.2 hedge.1)
            refine Relation.ReflTransGen.head ?_
              (Relation.ReflTransGen.single (hlinkroot _ hpick))
            exact ⟨Or.inl hp, Or.inr ⟨_, hpick, rfl⟩,
              Or.inr (Or.inr ⟨⟨u, w, hedge, rfl⟩, by simp [eeePt]⟩)⟩
          · have hrm : r = m := le_antisymm (hminr m) (hm r)
            subst hrm
            exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single (hlinkroot v hv)
      intro x y hx hy
      exact (hreach x hx).trans
        (reflTransGen_symm (fun _ _ hab => link_symm hab) (hreach y hy))
    · -- the budget: the chosen pairs are one per cover vertex and one per edge point
      have hdisj : Disjoint ((fun v : A => (reePt m (A := A), veePt v)) '' {v : A | C v})
          ((fun q : steinerEdgeInterp.Map A =>
            (veePt (coverPick C (q.2 0) (q.2 1)), q)) '' EdgePtSet A) := by
        rw [Set.disjoint_left]
        rintro ⟨p, q⟩ ⟨v, -, hv⟩ ⟨e, -, he⟩
        have h1 : p = reePt m := (Prod.ext_iff.mp hv.symm).1
        have h2 : p = veePt (coverPick C (e.2 0) (e.2 1)) := (Prod.ext_iff.mp he.symm).1
        have htag : SteinerTag.root = SteinerTag.vertex :=
          congrArg (fun r : SteinerTag × (Fin 2 → A) => r.1) (h1.symm.trans h2)
        exact absurd htag (by decide)
      have hTset : {p : steinerEdgeInterp.Map A × steinerEdgeInterp.Map A |
            (∃ v, C v ∧ p.1 = reePt m ∧ p.2 = veePt v) ∨
              (p.2 ∈ EdgePtSet A ∧ p.1 = veePt (coverPick C (p.2.2 0) (p.2.2 1)))}
          = ((fun v : A => (reePt m (A := A), veePt v)) '' {v : A | C v}) ∪
            ((fun q : steinerEdgeInterp.Map A =>
              (veePt (coverPick C (q.2 0) (q.2 1)), q)) '' EdgePtSet A) := by
        ext ⟨p, q⟩
        constructor
        · rintro (⟨v, hv, hp, hq⟩ | ⟨hq, hp⟩)
          · exact Or.inl ⟨v, hv, Prod.ext hp.symm hq.symm⟩
          · exact Or.inr ⟨q, hq, Prod.ext hp.symm rfl⟩
        · rintro (⟨v, hv, hpq⟩ | ⟨e, he, hpq⟩)
          · exact Or.inl ⟨v, hv, (Prod.ext_iff.mp hpq.symm).1, (Prod.ext_iff.mp hpq.symm).2⟩
          · refine Or.inr ⟨(Prod.ext_iff.mp hpq.symm).2 ▸ he, ?_⟩
            rw [(Prod.ext_iff.mp hpq.symm).1, (Prod.ext_iff.mp hpq.symm).2]
      have hinj₁ : Function.Injective fun v : A => (reePt m (A := A), veePt v) :=
        fun _ _ h => veePt_injective (Prod.ext_iff.mp h).2
      have hinj₂ : Function.Injective fun q : steinerEdgeInterp.Map A =>
          (veePt (coverPick C (q.2 0) (q.2 1)), q) := fun _ _ h => (Prod.ext_iff.mp h).2
      rw [hTset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
        Set.ncard_image_of_injective _ hinj₁, Set.ncard_image_of_injective _ hinj₂,
        ncard_marked_edge]
      omega
  · rintro ⟨hfin, T, S, hsub, hterms, hconn, hcard⟩
    have hA : Finite A := Finite.of_injective _ (veePt_injective (A := A))
    haveI := hA
    have hlinkmono : ∀ p q, Link T S p q → Link STAdj S p q :=
      fun _ _ h => ⟨h.1, h.2.1, h.2.2.imp (hsub _ _) (hsub _ _)⟩
    refine ⟨hA, fun v => S (veePt v), fun x y hxy hadj => ?_, ?_⟩
    · -- the first step out of an edge terminal lands on one of its endpoints
      have hex : S (eeePt x y) := hterms _ ((steinerE_terminal_e x y).mpr ⟨hadj, hxy⟩)
      have hrt : S (reePt m) := hterms _ hroot
      rcases Relation.ReflTransGen.cases_head (hconn (eeePt x y) (reePt m) hex hrt) with
        heq | ⟨q, hlink, -⟩
      · have htag : SteinerTag.edge = SteinerTag.root :=
          congrArg (fun r : SteinerTag × (Fin 2 → A) => r.1) heq
        exact absurd htag (by decide)
      · obtain ⟨hq, hqS⟩ := steinerE_link_ePt (hlinkmono _ _ hlink)
        rcases hq with rfl | rfl
        · exact Or.inl hqS
        · exact Or.inr hqS
    · -- the budget: edge points and cover vertices are disjoint members of the tree
      have hrt : S (reePt m) := hterms _ hroot
      have hdisj : Disjoint (EdgePtSet A) (veePt '' {v : A | S (veePt v)}) := by
        rw [Set.disjoint_left]
        rintro p ⟨u, w, -, rfl⟩ ⟨v, -, hv⟩
        have htag : SteinerTag.vertex = SteinerTag.edge :=
          congrArg (fun r : SteinerTag × (Fin 2 → A) => r.1) hv
        exact absurd htag (by decide)
      have hsubset : EdgePtSet A ∪ veePt '' {v : A | S (veePt v)} ⊆
          {x : steinerEdgeInterp.Map A | S x ∧ x ≠ reePt m} := by
        rintro p (hp | ⟨v, hv, rfl⟩)
        · exact ⟨hterms _ (hedgeS p hp), hedge_ne_root p hp⟩
        · refine ⟨hv, fun h => ?_⟩
          have htag : SteinerTag.vertex = SteinerTag.root :=
            congrArg (fun r : SteinerTag × (Fin 2 → A) => r.1) h
          exact absurd htag (by decide)
      have hsum : (EdgePtSet A).ncard + {v : A | S (veePt v)}.ncard
          ≤ {x : steinerEdgeInterp.Map A | S x ∧ x ≠ reePt m}.ncard := by
        rw [← Set.ncard_image_of_injective {v : A | S (veePt v)} veePt_injective,
          ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
        exact Set.ncard_le_ncard hsubset (Set.toFinite _)
      have hconncard := ncard_le_ncard_of_connected hrt hconn
      rw [ncard_marked_edge] at hcard
      change {v : A | S (veePt v)}.ncard ≤ {x : A | MGMarked x}.ncard
      omega

end EdgeCorrectness'

/-- **Vertex Cover ordered-FO-reduces to the edge-weighted Steiner Tree**:
Karp's original reading of the problem, with the budget enlarged by one unit
per edge point – the price of attaching each terminal to the tree. -/
noncomputable def vertexCover_ordered_fo_reduction_edgeSteinerTree :
    VertexCover ≤ᶠᵒ[≤] EdgeSteinerTree where
  Tag := SteinerTag
  dim := 2
  toInterpretation := steinerEdgeInterp
  correct A _ _ _ _ := hasSmallVertexCover_iff_edgeSteiner_map A

end DescriptiveComplexity
