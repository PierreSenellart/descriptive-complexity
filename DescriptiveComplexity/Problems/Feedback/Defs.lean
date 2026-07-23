/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Numbers.Unary
import DescriptiveComplexity.Problems.CliqueFamily.Defs

/-!
# Feedback Vertex Set and Feedback Arc Set: definitions

The two feedback problems of [Karp 1972][karp1972reducibility] on *directed*
graphs – the adjacency relation of a structure is an arbitrary binary
relation, so a `FirstOrder.Language.markedGraph`-structure already is a
digraph:

* `DescriptiveComplexity.FeedbackVertexSet`: is there a set of at most `k` *vertices*
  whose removal leaves an acyclic digraph? The threshold `k` is the
  cardinality of the marked set, representation (A) of
  `DescriptiveComplexity.Numbers.Unary`, so the vocabulary is that of marked graphs;
* `DescriptiveComplexity.FeedbackArcSet`: is there a set of at most `k` *arcs* whose
  removal leaves an acyclic digraph? Its objective counts arcs, and a set of
  arcs can have quadratically many elements, which a marked *subset* of the
  universe cannot reach. The threshold therefore moves one arity up: the
  vocabulary `FirstOrder.Language.markedArcGraph` marks a binary relation, and
  the number it encodes is the `Set.ncard` of the corresponding set of pairs
  (`DescriptiveComplexity.nonempty_embedding_iff_ncard_le₂`). This is still
  representation (A) – order-free and isomorphism-invariant – simply read at
  arity 2.

## Acyclicity, and why it stays first-order checkable

Acyclicity is a transitive-closure condition (`DescriptiveComplexity.AcyclicRel`: no
vertex is reachable from itself along a nonempty path, `Relation.TransGen`
supplying “nonempty path”), so it is *not* first-order. It is however
equivalent to the existence of a strict partial order containing every
surviving arc (`DescriptiveComplexity.acyclicRel_iff_exists_order`) – the order being
the transitive closure itself in the interesting direction. Guessing that
order alongside the removed set is what puts both problems in `Σ₁`
(`DescriptiveComplexity.Problems.Feedback.Membership`), and it is also what makes the
reduction of `DescriptiveComplexity.Problems.Feedback.Reductions` provable without any
manipulation of cycles: each direction *builds an order* from another one.

Both problems are instances of the same generic property of a relation on a
type – `DescriptiveComplexity.FeedbackOn` removes vertices,
`DescriptiveComplexity.FeedbackArcOn` removes arcs – with the same acyclicity kit
underneath, which is what the shared certificate lemmas exploit.

Self-loops are cycles under this reading, as they should be: a self-loop at a
vertex forces that vertex (resp. that arc) into the removed set.
-/

/- The language of arc-marked graphs lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of arc-marked digraphs. -/
inductive markedArcGraphRel : ℕ → Type
  /-- `adj a b`: there is an arc from `a` to `b`. -/
  | adj : markedArcGraphRel 2
  /-- `markedArc a b`: the pair `(a, b)` belongs to the marked relation. -/
  | markedArc : markedArcGraphRel 2
  deriving DecidableEq

/-- The relational language of arc-marked digraphs: a digraph together with a
marked binary relation, whose cardinality (as a set of pairs) serves as
threshold. -/
protected def markedArcGraph : Language :=
  ⟨fun _ => Empty, markedArcGraphRel⟩
  deriving IsRelational

/-- The adjacency symbol of arc-marked digraphs. -/
abbrev magAdj : Language.markedArcGraph.Relations 2 := .adj

/-- The mark symbol of arc-marked digraphs. -/
abbrev magMarked : Language.markedArcGraph.Relations 2 := .markedArc

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Acyclicity and its first-order certificate -/

section Acyclicity

variable {A : Type}

/-- A relation is acyclic if no element is reachable from itself along a
nonempty path. -/
def AcyclicRel (R : A → A → Prop) : Prop :=
  ∀ x, ¬Relation.TransGen R x x

private theorem transGen_map {B : Type} (f : B → A) {RB : B → B → Prop}
    {RA : A → A → Prop} (hR : ∀ b b', RB b b' → RA (f b) (f b')) {b b' : B}
    (h : Relation.TransGen RB b b') : Relation.TransGen RA (f b) (f b') := by
  induction h with
  | single h => exact .single (hR _ _ h)
  | tail _ h₂ ih => exact ih.tail (hR _ _ h₂)

/-- **Acyclicity is first-order certifiable**: a relation is acyclic exactly
when some strict partial order contains it. The order is the transitive
closure in one direction; in the other, a cycle would give `Lt x x`. This is
what a `Σ₁` definition guesses, and what the reductions between the two
feedback problems build. -/
theorem acyclicRel_iff_exists_order (R : A → A → Prop) :
    AcyclicRel R ↔ ∃ Lt : A → A → Prop,
      (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧ ∀ a b, R a b → Lt a b := by
  constructor
  · intro hac
    exact ⟨Relation.TransGen R, fun _ _ _ h₁ h₂ => h₁.trans h₂, hac, fun _ _ h => .single h⟩
  · rintro ⟨Lt, htrans, hirr, hmono⟩ x hx
    have hlt : ∀ a b, Relation.TransGen R a b → Lt a b := by
      intro a b hab
      induction hab with
      | single h => exact hmono _ _ h
      | tail _ h₂ ih => exact htrans _ _ _ ih (hmono _ _ h₂)
    exact hirr x (hlt x x hx)

/-- Acyclicity transports along an equivalence commuting with the two
relations. -/
theorem AcyclicRel.of_equiv {B : Type} (u : B ≃ A) {RB : B → B → Prop}
    {RA : A → A → Prop} (hR : ∀ a a', RA a a' → RB (u.symm a) (u.symm a'))
    (h : AcyclicRel RB) : AcyclicRel RA :=
  fun x hx => h (u.symm x) (transGen_map u.symm hR hx)

end Acyclicity

/-! ### The generic properties -/

section Generic

variable {A : Type}

/-- An arc surviving the removal of the `Cp`-vertices: both endpoints are
outside `Cp` and the arc is present. -/
def SurvivingArc (Adjp : A → A → Prop) (Cp : A → Prop) (a b : A) : Prop :=
  ¬Cp a ∧ ¬Cp b ∧ Adjp a b

/-- An arc surviving the removal of the `Fp`-arcs: the arc is present and not
removed. -/
def UncutArc (Adjp : A → A → Prop) (Fp : A → A → Prop) (a b : A) : Prop :=
  Adjp a b ∧ ¬Fp a b

/-- Some set of vertices whose removal makes the digraph acyclic is at most as
large as the number encoded by the `Kp`-marked elements: “some feedback vertex
set is at most as large as the marked set”. -/
def FeedbackOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ C : A → Prop, AcyclicRel (SurvivingArc Adjp C) ∧ {x | C x}.ncard ≤ {x | Kp x}.ncard

/-- Some set of arcs whose removal makes the digraph acyclic is at most as
large as the number encoded by the `Kp`-marked pairs: “some feedback arc set
is at most as large as the marked relation”. -/
def FeedbackArcOn (Adjp : A → A → Prop) (Kp : A → A → Prop) : Prop :=
  ∃ F : A → A → Prop, AcyclicRel (UncutArc Adjp F) ∧
    {p : A × A | F p.1 p.2}.ncard ≤ {p : A × A | Kp p.1 p.2}.ncard

/-! #### The certified forms

The shape the second-order definitions guess: the removed set (of vertices or
of arcs), a strict partial order certifying that what survives is acyclic, and
an injection into the marked set (resp. the marked relation) witnessing the
threshold. -/

section Certificate

variable [Finite A]

/-- The feedback-vertex-set property, with acyclicity certified by an order
and the threshold by an injection. -/
theorem feedbackOn_iff_certificate (Adjp : A → A → Prop) (Kp : A → Prop) :
    FeedbackOn Adjp Kp ↔ ∃ C : A → Prop,
      (∃ Lt : A → A → Prop, (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
        ∀ a b, SurvivingArc Adjp C a b → Lt a b) ∧
      Nonempty ({x // C x} ↪ {x // Kp x}) :=
  exists_congr fun C =>
    and_congr (acyclicRel_iff_exists_order _) (nonempty_embedding_iff_ncard_le C Kp).symm

/-- The feedback-arc-set property, with acyclicity certified by an order and
the threshold by an injection of pairs. -/
theorem feedbackArcOn_iff_certificate (Adjp : A → A → Prop) (Kp : A → A → Prop) :
    FeedbackArcOn Adjp Kp ↔ ∃ F : A → A → Prop,
      (∃ Lt : A → A → Prop, (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
        ∀ a b, UncutArc Adjp F a b → Lt a b) ∧
      Nonempty ({p : A × A // F p.1 p.2} ↪ {p : A × A // Kp p.1 p.2}) :=
  exists_congr fun F =>
    and_congr (acyclicRel_iff_exists_order _) (nonempty_embedding_iff_ncard_le₂ F Kp).symm

end Certificate

/-! #### Transport along equivalences -/

variable {B : Type}

/-- `FeedbackOn` transports along an equivalence commuting with the two
predicates. -/
theorem FeedbackOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : FeedbackOn AdjB KB) : FeedbackOn AdjA KA := by
  obtain ⟨C, hac, hcard⟩ := h
  refine ⟨fun a => C (u.symm a), AcyclicRel.of_equiv u (fun a a' haa' => ?_) hac, ?_⟩
  · exact ⟨haa'.1, haa'.2.1, (hadj (u.symm a) (u.symm a')).mpr (by simpa using haa'.2.2)⟩
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u C]
    exact hcard

/-- `FeedbackArcOn` transports along an equivalence commuting with the two
relations. -/
theorem FeedbackArcOn.of_equiv (u : B ≃ A) {AdjB KB : B → B → Prop}
    {AdjA KA : A → A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b'))
    (hK : ∀ b b', KB b b' ↔ KA (u b) (u b')) (h : FeedbackArcOn AdjB KB) :
    FeedbackArcOn AdjA KA := by
  obtain ⟨F, hac, hcard⟩ := h
  refine ⟨fun a a' => F (u.symm a) (u.symm a'),
    AcyclicRel.of_equiv u (fun a a' haa' => ?_) hac, ?_⟩
  · exact ⟨(hadj (u.symm a) (u.symm a')).mpr (by simpa using haa'.1), haa'.2⟩
  · rw [← ncard_setOf_equiv₂ u hK,
      ← ncard_setOf_equiv₂ (RB := F) (RA := fun a a' => F (u.symm a) (u.symm a')) u
        (fun b b' => by simp)]
    exact hcard

private theorem feedback_symm_hUn {PB : B → Prop} {PA : A → Prop} (u : B ≃ A)
    (hP : ∀ b, PB b ↔ PA (u b)) (a : A) : PA a ↔ PB (u.symm a) := by
  rw [hP]
  simp

private theorem feedback_symm_hBin {RB : B → B → Prop} {RA : A → A → Prop} (u : B ≃ A)
    (hR : ∀ b b', RB b b' ↔ RA (u b) (u b')) (a a' : A) :
    RA a a' ↔ RB (u.symm a) (u.symm a') := by
  rw [hR]
  simp

/-- `FeedbackOn` transports along an equivalence, iff version. -/
theorem FeedbackOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    FeedbackOn AdjB KB ↔ FeedbackOn AdjA KA :=
  ⟨FeedbackOn.of_equiv u hadj hK,
    FeedbackOn.of_equiv u.symm (feedback_symm_hBin u hadj) (feedback_symm_hUn u hK)⟩

/-- `FeedbackArcOn` transports along an equivalence, iff version. -/
theorem FeedbackArcOn.equiv_iff (u : B ≃ A) {AdjB KB : B → B → Prop}
    {AdjA KA : A → A → Prop} (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b'))
    (hK : ∀ b b', KB b b' ↔ KA (u b) (u b')) :
    FeedbackArcOn AdjB KB ↔ FeedbackArcOn AdjA KA :=
  ⟨FeedbackArcOn.of_equiv u hadj hK,
    FeedbackArcOn.of_equiv u.symm (feedback_symm_hBin u hadj) (feedback_symm_hBin u hK)⟩

/-! #### Vertex covers are feedback vertex sets of the symmetrized graph -/

/-- **The reduction of Vertex Cover, semantically**: a set meets every edge of
a digraph iff it kills every cycle of the digraph symmetrized off the
diagonal. Killing all 2-cycles already removes every arc, which is why no
cycle of any length survives. -/
theorem coverOn_iff_feedbackOn (Adjp : A → A → Prop) (Kp : A → Prop) :
    CoverOn Adjp Kp ↔ FeedbackOn (fun x y => x ≠ y ∧ (Adjp x y ∨ Adjp y x)) Kp := by
  constructor
  · rintro ⟨C, hcov, hcard⟩
    have hempty : ∀ a b, ¬SurvivingArc (fun x y => x ≠ y ∧ (Adjp x y ∨ Adjp y x)) C a b := by
      rintro a b ⟨ha, hb, hne, hab⟩
      rcases hab with hab | hab
      · exact (hcov a b hne hab).elim ha hb
      · exact (hcov b a (Ne.symm hne) hab).elim hb ha
    have hno : ∀ a b, ¬Relation.TransGen
        (SurvivingArc (fun x y => x ≠ y ∧ (Adjp x y ∨ Adjp y x)) C) a b := by
      intro a b hab
      induction hab with
      | single h => exact hempty _ _ h
      | tail _ h₂ _ => exact hempty _ _ h₂
    exact ⟨C, fun x hx => hno x x hx, hcard⟩
  · rintro ⟨C, hac, hcard⟩
    refine ⟨C, fun x y hxy hadj => ?_, hcard⟩
    rcases Classical.em (C x) with hx | hx
    · exact Or.inl hx
    rcases Classical.em (C y) with hy | hy
    · exact Or.inr hy
    exact absurd (Relation.TransGen.tail (.single ⟨hx, hy, hxy, Or.inl hadj⟩)
      ⟨hy, hx, Ne.symm hxy, Or.inr hadj⟩) (hac x)

end Generic

/-! ### The two problems -/

section Problems

section Shorthands

variable {A : Type} [Language.markedArcGraph.Structure A]

/-- Adjacency in an arc-marked digraph. -/
def MAGAdj (a b : A) : Prop := RelMap magAdj ![a, b]

/-- Membership in the marked relation of an arc-marked digraph. -/
def MAGMarked (a b : A) : Prop := RelMap magMarked ![a, b]

end Shorthands

/-- A marked graph has a feedback vertex set at most as large as its marked
set. (Finiteness of the universe is part of the property: cardinality
thresholds are only meaningful on finite structures.) -/
def HasSmallFeedbackSet (A : Type) [Language.markedGraph.Structure A] : Prop :=
  Finite A ∧ FeedbackOn (MGAdj (A := A)) (MGMarked (A := A))

/-- An arc-marked digraph has a feedback arc set at most as large as its
marked relation. -/
def HasSmallFeedbackArcSet (A : Type) [Language.markedArcGraph.Structure A] : Prop :=
  Finite A ∧ FeedbackArcOn (MAGAdj (A := A)) (MAGMarked (A := A))

end Problems

section Iso

/-- The feedback-vertex-set threshold property is isomorphism-invariant. -/
theorem hasSmallFeedbackSet_iso {A B : Type} [Language.markedGraph.Structure A]
    [Language.markedGraph.Structure B] (e : A ≃[Language.markedGraph] B) :
    HasSmallFeedbackSet A ↔ HasSmallFeedbackSet B :=
  and_congr e.toEquiv.finite_iff
    (FeedbackOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e mgAdj a b)
      fun a => relMap_equiv₁ e mgMarked a)

/-- The feedback-arc-set threshold property is isomorphism-invariant. -/
theorem hasSmallFeedbackArcSet_iso {A B : Type} [Language.markedArcGraph.Structure A]
    [Language.markedArcGraph.Structure B] (e : A ≃[Language.markedArcGraph] B) :
    HasSmallFeedbackArcSet A ↔ HasSmallFeedbackArcSet B :=
  and_congr e.toEquiv.finite_iff
    (FeedbackArcOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e magAdj a b)
      fun a b => relMap_equiv₂ e magMarked a b)

end Iso

/-- FEEDBACK VERTEX SET, as a problem on marked graphs: is there a set of
vertices at most as large as the marked set whose removal leaves an acyclic
digraph? -/
def FeedbackVertexSet : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasSmallFeedbackSet A inst
  iso_invariant := fun e => hasSmallFeedbackSet_iso e

/-- FEEDBACK ARC SET, as a problem on arc-marked digraphs: is there a set of
arcs at most as large as the marked relation whose removal leaves an acyclic
digraph? -/
def FeedbackArcSet : DecisionProblem Language.markedArcGraph where
  Holds := fun A inst => @HasSmallFeedbackArcSet A inst
  iso_invariant := fun e => hasSmallFeedbackArcSet_iso e

end DescriptiveComplexity
