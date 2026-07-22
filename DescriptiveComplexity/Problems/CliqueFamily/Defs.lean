/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import DescriptiveComplexity.Interpretation

/-!
# Clique, Independent Set and Vertex Cover: definitions

The three classical threshold problems on graphs, as decision problems on
*marked graphs*: `FirstOrder.Language.markedGraph`-structures, carrying a
binary adjacency relation and a unary mark. The marked set plays the role of
the numeric threshold `k` of the textbook problems – its *cardinality* is the
threshold – so that no number encoding is needed:

* `DescriptiveComplexity.Clique`: some clique is at least as large as the marked set;
* `DescriptiveComplexity.IndependentSet`: some independent set is at least as large as
  the marked set;
* `DescriptiveComplexity.VertexCover`: some vertex cover is at most as large as the
  marked set.

Cardinality comparisons are phrased as existence of injections (type
embeddings), which makes isomorphism-invariance compositional. Since
cardinality thresholds are only meaningful on finite structures, finiteness
of the universe is part of the yes-instances; by
`ComplexityClass.mem_congr_finite` this does not affect any
complexity-theoretic statement.

Self-loops are ignored (all three properties are about the underlying
loopless graph), and adjacency is required in both directions on ordered
pairs, so the problems agree with their standard versions on (structures
encoding) simple graphs.

The three predicates are instances of generic properties `DescriptiveComplexity.CliqueOn`
/ `IndepOn` / `CoverOn` of a binary and a unary predicate on a type; the
generic form is shared by the isomorphism-invariance proofs and by the
reductions of `DescriptiveComplexity.Problems.CliqueFamily.Reductions`.
-/

/- The language of marked graphs lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of marked graphs. -/
inductive markedGraphRel : ℕ → Type
  /-- `adj a b`: there is an edge from `a` to `b`. -/
  | adj : markedGraphRel 2
  /-- `marked a`: the element `a` belongs to the marked set. -/
  | marked : markedGraphRel 1
  deriving DecidableEq

/-- The relational language of marked graphs: a graph together with a marked
subset of its vertices, whose cardinality serves as threshold. -/
protected def markedGraph : Language :=
  ⟨fun _ => Empty, markedGraphRel⟩
  deriving IsRelational

/-- The adjacency symbol of marked graphs. -/
abbrev mgAdj : Language.markedGraph.Relations 2 := .adj

/-- The mark symbol of marked graphs. -/
abbrev mgMarked : Language.markedGraph.Relations 1 := .marked

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Generic threshold properties

The properties underlying the three problems, for an arbitrary binary
predicate `Adjp` (adjacency) and unary predicate `Kp` (marks) on a type. -/

section Generic

variable {A : Type}

/-- Some set that is pairwise `Adjp`-related (off the diagonal) admits an
injection from the `Kp`-marked elements: “some clique is at least as large as
the marked set”. -/
def CliqueOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ S : A → Prop, (∀ x y, S x → S y → x ≠ y → Adjp x y) ∧
    Nonempty ({x // Kp x} ↪ {x // S x})

/-- Some set that is pairwise non-`Adjp`-related (off the diagonal) admits an
injection from the `Kp`-marked elements: “some independent set is at least as
large as the marked set”. -/
def IndepOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  CliqueOn (fun x y => ¬Adjp x y) Kp

/-- Some set meeting every (off-diagonal) `Adjp`-edge injects into the
`Kp`-marked elements: “some vertex cover is at most as large as the marked
set”. -/
def CoverOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ C : A → Prop, (∀ x y, x ≠ y → Adjp x y → C x ∨ C y) ∧
    Nonempty ({x // C x} ↪ {x // Kp x})

variable {B : Type}

/-- `CliqueOn` transports along an equivalence commuting with the two
predicates. -/
theorem CliqueOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : CliqueOn AdjB KB) : CliqueOn AdjA KA := by
  obtain ⟨S, hS, ⟨e⟩⟩ := h
  refine ⟨fun a => S (u.symm a), fun x y hx hy hxy => ?_, ⟨?_⟩⟩
  · have h' := (hadj (u.symm x) (u.symm y)).mp
      (hS _ _ hx hy fun h => hxy (u.symm.injective h))
    simpa using h'
  · refine (Equiv.subtypeEquiv u.symm fun a => ?_).toEmbedding.trans
      (e.trans (Equiv.subtypeEquiv u fun b => ?_).toEmbedding)
    · simp [hK]
    · simp

/-- `IndepOn` transports along an equivalence commuting with the two
predicates. -/
theorem IndepOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : IndepOn AdjB KB) : IndepOn AdjA KA :=
  CliqueOn.of_equiv u (fun b b' => not_congr (hadj b b')) hK h

/-- `CoverOn` transports along an equivalence commuting with the two
predicates. -/
theorem CoverOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : CoverOn AdjB KB) : CoverOn AdjA KA := by
  obtain ⟨C, hC, ⟨e⟩⟩ := h
  refine ⟨fun a => C (u.symm a), fun x y hxy hadjA => ?_, ⟨?_⟩⟩
  · exact hC (u.symm x) (u.symm y) (fun h => hxy (u.symm.injective h))
      ((hadj (u.symm x) (u.symm y)).mpr (by simpa using hadjA))
  · refine (Equiv.subtypeEquiv u.symm fun a => Iff.rfl).toEmbedding.trans
      (e.trans (Equiv.subtypeEquiv u fun b => hK b).toEmbedding)

private theorem symm_hadj {AdjB : B → B → Prop} {AdjA : A → A → Prop} (u : B ≃ A)
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (a a' : A) :
    AdjA a a' ↔ AdjB (u.symm a) (u.symm a') := by
  rw [hadj]
  simp

private theorem symm_hK {KB : B → Prop} {KA : A → Prop} (u : B ≃ A)
    (hK : ∀ b, KB b ↔ KA (u b)) (a : A) : KA a ↔ KB (u.symm a) := by
  rw [hK]
  simp

/-- `CliqueOn` transports along an equivalence, iff version. -/
theorem CliqueOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    CliqueOn AdjB KB ↔ CliqueOn AdjA KA :=
  ⟨CliqueOn.of_equiv u hadj hK,
    CliqueOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩

/-- `IndepOn` transports along an equivalence, iff version. -/
theorem IndepOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    IndepOn AdjB KB ↔ IndepOn AdjA KA :=
  ⟨IndepOn.of_equiv u hadj hK,
    IndepOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩

/-- `CoverOn` transports along an equivalence, iff version. -/
theorem CoverOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    CoverOn AdjB KB ↔ CoverOn AdjA KA :=
  ⟨CoverOn.of_equiv u hadj hK,
    CoverOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩

/-- `CliqueOn` only depends on the off-diagonal part of the adjacency
predicate and on the extension of the mark predicate. -/
theorem cliqueOn_congr {P Q : A → A → Prop} {K K' : A → Prop}
    (hPQ : ∀ x y, x ≠ y → (P x y ↔ Q x y)) (hK : ∀ x, K x ↔ K' x) :
    CliqueOn P K ↔ CliqueOn Q K' := by
  have h : ∀ {P Q : A → A → Prop} {K K' : A → Prop},
      (∀ x y, x ≠ y → (P x y ↔ Q x y)) → (∀ x, K x ↔ K' x) →
      CliqueOn P K → CliqueOn Q K' := by
    rintro P Q K K' hPQ hK ⟨S, hS, ⟨e⟩⟩
    exact ⟨S, fun x y hx hy hxy => (hPQ x y hxy).mp (hS x y hx hy hxy),
      ⟨(Equiv.subtypeEquivRight hK).symm.toEmbedding.trans e⟩⟩
  exact ⟨h hPQ hK, h (fun x y hxy => (hPQ x y hxy).symm) fun x => (hK x).symm⟩

/-- `IndepOn` only depends on the off-diagonal part of the adjacency
predicate and on the extension of the mark predicate. -/
theorem indepOn_congr {P Q : A → A → Prop} {K K' : A → Prop}
    (hPQ : ∀ x y, x ≠ y → (P x y ↔ Q x y)) (hK : ∀ x, K x ↔ K' x) :
    IndepOn P K ↔ IndepOn Q K' :=
  cliqueOn_congr (fun x y hxy => not_congr (hPQ x y hxy)) hK

end Generic

/-! ### The three problems -/

section Problems

section Shorthands

variable {A : Type} [Language.markedGraph.Structure A]

/-- Adjacency in a marked graph. -/
def MGAdj (a b : A) : Prop := RelMap mgAdj ![a, b]

/-- Markedness in a marked graph. -/
def MGMarked (a : A) : Prop := RelMap mgMarked ![a]

end Shorthands

variable (A : Type) [Language.markedGraph.Structure A]

/-- A marked graph contains a clique at least as large as its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasLargeClique : Prop :=
  Finite A ∧ CliqueOn (MGAdj (A := A)) (MGMarked (A := A))

/-- A marked graph contains an independent set at least as large as its
marked set. -/
def HasLargeIndependentSet : Prop :=
  Finite A ∧ IndepOn (MGAdj (A := A)) (MGMarked (A := A))

/-- A marked graph contains a vertex cover at most as large as its marked
set. -/
def HasSmallVertexCover : Prop :=
  Finite A ∧ CoverOn (MGAdj (A := A)) (MGMarked (A := A))

end Problems

/-! ### Isomorphism-invariance and the bundled problems -/

section Iso

variable {A B : Type} [Language.markedGraph.Structure A] [Language.markedGraph.Structure B]

private theorem mgAdj_map (e : A ≃[Language.markedGraph] B) (a b : A) :
    MGAdj a b ↔ MGAdj (e a) (e b) :=
  relMap_equiv₂ e mgAdj a b

private theorem mgMarked_map (e : A ≃[Language.markedGraph] B) (a : A) :
    MGMarked a ↔ MGMarked (e a) :=
  relMap_equiv₁ e mgMarked a

/-- The clique threshold property is isomorphism-invariant. -/
theorem hasLargeClique_iso (e : A ≃[Language.markedGraph] B) :
    HasLargeClique A ↔ HasLargeClique B :=
  and_congr e.toEquiv.finite_iff
    (CliqueOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))

/-- The independent-set threshold property is isomorphism-invariant. -/
theorem hasLargeIndependentSet_iso (e : A ≃[Language.markedGraph] B) :
    HasLargeIndependentSet A ↔ HasLargeIndependentSet B :=
  and_congr e.toEquiv.finite_iff
    (IndepOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))

/-- The vertex-cover threshold property is isomorphism-invariant. -/
theorem hasSmallVertexCover_iso (e : A ≃[Language.markedGraph] B) :
    HasSmallVertexCover A ↔ HasSmallVertexCover B :=
  and_congr e.toEquiv.finite_iff
    (CoverOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))

end Iso

/-- CLIQUE, as a problem on marked graphs: is there a clique at least as
large as the marked set? -/
def Clique : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasLargeClique A inst
  iso_invariant := fun e => hasLargeClique_iso e

/-- INDEPENDENT SET, as a problem on marked graphs: is there an independent
set at least as large as the marked set? -/
def IndependentSet : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasLargeIndependentSet A inst
  iso_invariant := fun e => hasLargeIndependentSet_iso e

/-- VERTEX COVER, as a problem on marked graphs: is there a vertex cover at
most as large as the marked set? -/
def VertexCover : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasSmallVertexCover A inst
  iso_invariant := fun e => hasSmallVertexCover_iso e

end DescriptiveComplexity
