/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily
import DescriptiveComplexity.SecondOrder

/-!
# Feedback Vertex Set is NP-complete

FEEDBACK NODE SET ([Karp 1972][karp1972reducibility]), on the marked graphs of
`FirstOrder.Language.markedGraph` – whose adjacency relation is an arbitrary
binary relation, i.e. a *directed* graph: is there a set of at most `k`
vertices whose removal leaves an acyclic digraph? As everywhere in the
library, `k` is the cardinality of the marked set (representation (A)).

Acyclicity is stated on the arcs that survive the removal
(`DescriptiveComplexity.SurvivingArc`): no vertex is reachable from itself by a
nonempty path of such arcs, `Relation.TransGen` supplying “nonempty path”.
Self-loops are cycles under this reading, as they should be.

Two things make the problem fit the framework without new machinery:

* **Hardness** is the classical reduction from Vertex Cover, which replaces
  each undirected edge by a 2-cycle. Here the input adjacency is already an
  arbitrary relation, so the interpretation
  (`DescriptiveComplexity.symmetrizeInterp`, tag `Unit`, dimension 1,
  quantifier-free) simply *symmetrizes* it off the diagonal: every edge of
  the input becomes a 2-cycle of the output. A set of vertices then kills
  every cycle iff it meets every edge, since killing all 2-cycles already
  removes every arc (`DescriptiveComplexity.coverOn_iff_feedbackOn`). The marked set
  is copied, so the threshold needs no counting argument at all.
* **Membership** needs a first-order certificate for acyclicity, and the
  textbook one works: a strict partial order containing every surviving arc
  (`DescriptiveComplexity.acyclic_iff_exists_order`; the order is the transitive
  closure itself in the interesting direction). The `Σ₁` definition therefore
  guesses three relations – the removed set, the order, and an injection of
  the removed set into the marked set for the threshold – and checks
  transitivity, irreflexivity, arc-monotonicity, totality and injectivity
  first-order.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock BoundedFormula

/-! ### The generic property -/

section Generic

variable {A : Type}

/-- An arc surviving the removal of the `Cp`-vertices: both endpoints are
outside `Cp` and the arc is present. -/
def SurvivingArc (Adjp : A → A → Prop) (Cp : A → Prop) (a b : A) : Prop :=
  ¬Cp a ∧ ¬Cp b ∧ Adjp a b

/-- Removing the `Cp`-vertices leaves an acyclic digraph: no vertex is
reachable from itself along a nonempty path of surviving arcs. -/
def AcyclicOff (Adjp : A → A → Prop) (Cp : A → Prop) : Prop :=
  ∀ x, ¬Relation.TransGen (SurvivingArc Adjp Cp) x x

/-- Some set whose removal makes the digraph acyclic is at most as large as
the number encoded by the `Kp`-marked elements: “some feedback vertex set is
at most as large as the marked set”. -/
def FeedbackOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ C : A → Prop, AcyclicOff Adjp C ∧ {x | C x}.ncard ≤ {x | Kp x}.ncard

/-! #### Acyclicity, first-order certified

Acyclicity is a transitive-closure condition, hence not first-order; but it
is equivalent to the *existence* of a strict partial order containing the
surviving arcs, which is first-order once that order is guessed. This is the
certificate the `Σ₁` definition supplies. -/

private theorem transGen_map {B : Type} (f : B → A) {RB : B → B → Prop}
    {RA : A → A → Prop} (hR : ∀ b b', RB b b' → RA (f b) (f b')) {b b' : B}
    (h : Relation.TransGen RB b b') : Relation.TransGen RA (f b) (f b') := by
  induction h with
  | single h => exact .single (hR _ _ h)
  | tail _ h₂ ih => exact ih.tail (hR _ _ h₂)

/-- Acyclicity of the surviving digraph is witnessed by a strict partial
order containing every surviving arc. -/
theorem acyclic_iff_exists_order (Adjp : A → A → Prop) (Cp : A → Prop) :
    AcyclicOff Adjp Cp ↔ ∃ Lt : A → A → Prop,
      (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
      ∀ a b, SurvivingArc Adjp Cp a b → Lt a b := by
  constructor
  · intro hac
    exact ⟨Relation.TransGen (SurvivingArc Adjp Cp), fun _ _ _ h₁ h₂ => h₁.trans h₂,
      hac, fun _ _ h => .single h⟩
  · rintro ⟨Lt, htrans, hirr, hmono⟩ x hx
    have hlt : ∀ a b, Relation.TransGen (SurvivingArc Adjp Cp) a b → Lt a b := by
      intro a b hab
      induction hab with
      | single h => exact hmono _ _ h
      | tail _ h₂ ih => exact htrans _ _ _ ih (hmono _ _ h₂)
    exact hirr x (hlt x x hx)

/-- The feedback threshold as an injection of the removed set into the marked
set, with acyclicity in its certified form: the shape the second-order
definition guesses. -/
theorem feedbackOn_iff_certificate [Finite A] (Adjp : A → A → Prop) (Kp : A → Prop) :
    FeedbackOn Adjp Kp ↔ ∃ C : A → Prop,
      (∃ Lt : A → A → Prop, (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
        ∀ a b, SurvivingArc Adjp C a b → Lt a b) ∧
      Nonempty ({x // C x} ↪ {x // Kp x}) :=
  exists_congr fun C =>
    and_congr (acyclic_iff_exists_order Adjp C)
      (nonempty_embedding_iff_ncard_le C Kp).symm

/-! #### Transport along equivalences -/

variable {B : Type}

/-- `FeedbackOn` transports along an equivalence commuting with the two
predicates. -/
theorem FeedbackOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : FeedbackOn AdjB KB) : FeedbackOn AdjA KA := by
  obtain ⟨C, hac, hcard⟩ := h
  refine ⟨fun a => C (u.symm a), fun x hx => hac (u.symm x) ?_, ?_⟩
  · refine transGen_map u.symm (fun a b hab => ?_) hx
    refine ⟨by simpa using hab.1, by simpa using hab.2.1, ?_⟩
    exact (hadj (u.symm a) (u.symm b)).mpr (by simpa using hab.2.2)
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u C]
    exact hcard

private theorem feedback_symm_hadj {AdjB : B → B → Prop} {AdjA : A → A → Prop}
    (u : B ≃ A) (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (a a' : A) :
    AdjA a a' ↔ AdjB (u.symm a) (u.symm a') := by
  rw [hadj]
  simp

private theorem feedback_symm_hK {KB : B → Prop} {KA : A → Prop} (u : B ≃ A)
    (hK : ∀ b, KB b ↔ KA (u b)) (a : A) : KA a ↔ KB (u.symm a) := by
  rw [hK]
  simp

/-- `FeedbackOn` transports along an equivalence, iff version. -/
theorem FeedbackOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    FeedbackOn AdjB KB ↔ FeedbackOn AdjA KA :=
  ⟨FeedbackOn.of_equiv u hadj hK,
    FeedbackOn.of_equiv u.symm (feedback_symm_hadj u hadj) (feedback_symm_hK u hK)⟩

/-! #### Vertex covers are feedback vertex sets of the symmetrized graph -/

/-- **The reduction, semantically**: a set meets every edge of a digraph iff
it kills every cycle of the digraph symmetrized off the diagonal. Killing all
2-cycles already removes every arc, which is why no cycle of any length
survives. -/
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

/-! ### The problem -/

section Problem

variable (A : Type) [Language.markedGraph.Structure A]

/-- A marked graph has a feedback vertex set at most as large as its marked
set. (Finiteness of the universe is part of the property: cardinality
thresholds are only meaningful on finite structures.) -/
def HasSmallFeedbackSet : Prop :=
  Finite A ∧ FeedbackOn (MGAdj (A := A)) (MGMarked (A := A))

end Problem

section Iso

variable {A B : Type} [Language.markedGraph.Structure A] [Language.markedGraph.Structure B]

/-- The feedback-vertex-set threshold property is isomorphism-invariant. -/
theorem hasSmallFeedbackSet_iso (e : A ≃[Language.markedGraph] B) :
    HasSmallFeedbackSet A ↔ HasSmallFeedbackSet B :=
  and_congr e.toEquiv.finite_iff
    (FeedbackOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e mgAdj a b)
      fun a => relMap_equiv₁ e mgMarked a)

end Iso

/-- FEEDBACK VERTEX SET, as a problem on marked graphs: is there a set of
vertices at most as large as the marked set whose removal leaves an acyclic
digraph? -/
def FeedbackVertexSet : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasSmallFeedbackSet A inst
  iso_invariant := fun e => hasSmallFeedbackSet_iso e

/-! ### Vertex Cover reduces to Feedback Vertex Set -/

/-- The symmetrizing interpretation: adjacency becomes off-diagonal adjacency
in either direction – so every edge becomes a 2-cycle – and marks are
kept. -/
def symmetrizeInterp :
    FOInterpretation Language.markedGraph Language.markedGraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun _ =>
        ∼(Term.equal (Term.var (0, 0)) (Term.var (1, 0))) ⊓
          (mgAdj.formula₂ (Term.var (0, 0)) (Term.var (1, 0)) ⊔
            mgAdj.formula₂ (Term.var (1, 0)) (Term.var (0, 0)))
    | _, .marked => fun _ => mgMarked.formula₁ (Term.var (0, 0))

/-- The symmetrizing interpretation is quantifier-free. -/
theorem symmetrizeInterp_isQuantifierFree : symmetrizeInterp.IsQuantifierFree := by
  intro n R t
  cases R with
  | adj =>
    exact ((IsAtomic.equal _ _).isQF.imp isQF_bot).inf
      ((IsAtomic.rel _ _).isQF.sup (IsAtomic.rel _ _).isQF)
  | marked => exact (IsAtomic.rel _ _).isQF

section Characterizations

variable {A : Type} [Language.markedGraph.Structure A]

@[simp]
theorem symmetrize_adj (w₁ w₂ : Fin 1 → A) :
    RelMap (M := symmetrizeInterp.Map A) mgAdj ![((), w₁), ((), w₂)] ↔
      w₁ 0 ≠ w₂ 0 ∧ (RelMap mgAdj ![w₁ 0, w₂ 0] ∨ RelMap mgAdj ![w₂ 0, w₁ 0]) := by
  rw [FOInterpretation.relMap_map]
  simp [symmetrizeInterp, Formula.realize_rel₂]

@[simp]
theorem symmetrize_marked (w : Fin 1 → A) :
    RelMap (M := symmetrizeInterp.Map A) mgMarked ![((), w)] ↔ RelMap mgMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [symmetrizeInterp, Formula.realize_rel₁]

end Characterizations

section Correctness

variable (A : Type) [Language.markedGraph.Structure A]

private theorem symmetrize_hadj :
    ∀ b b' : symmetrizeInterp.Map A,
      MGAdj b b' ↔ (symmetrizeInterp.mapEquivSelf A b ≠ symmetrizeInterp.mapEquivSelf A b' ∧
        (MGAdj (symmetrizeInterp.mapEquivSelf A b) (symmetrizeInterp.mapEquivSelf A b') ∨
          MGAdj (symmetrizeInterp.mapEquivSelf A b') (symmetrizeInterp.mapEquivSelf A b))) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact symmetrize_adj w w'

private theorem symmetrize_hK :
    ∀ b : symmetrizeInterp.Map A,
      MGMarked b ↔ MGMarked (symmetrizeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact symmetrize_marked w

/-- Correctness of the symmetrizing interpretation. -/
theorem hasSmallVertexCover_iff_feedback_map :
    HasSmallVertexCover A ↔ HasSmallFeedbackSet (symmetrizeInterp.Map A) := by
  refine and_congr ((symmetrizeInterp.mapEquivSelf A).finite_iff).symm ?_
  rw [coverOn_iff_feedbackOn]
  exact (FeedbackOn.equiv_iff (symmetrizeInterp.mapEquivSelf A) (symmetrize_hadj A)
    (symmetrize_hK A)).symm

end Correctness

/-- **Vertex Cover FO-reduces to Feedback Vertex Set**, by symmetrizing the
adjacency relation: every edge becomes a 2-cycle, so the feedback vertex sets
are exactly the vertex covers. -/
def vertexCover_fo_reduction_feedbackVertexSet : VertexCover ≤ᶠᵒ FeedbackVertexSet where
  Tag := Unit
  dim := 1
  toInterpretation := symmetrizeInterp
  correct A _ _ := hasSmallVertexCover_iff_feedback_map A

/-! ### Membership -/

section SigmaOne

/-- The single existential block of the `Σ₁` definition of Feedback Vertex
Set: the removed set (unary), a strict partial order certifying acyclicity
(binary), and an injection of the removed set into the marked set
(binary). -/
def feedbackGuessBlock : SOBlock where
  ι := Option Bool
  arity := fun i => match i with
    | none => 1
    | some _ => 2

/-- The symbol of the removed-set relation variable. -/
def fvsSetSym : feedbackGuessBlock.lang.Relations 1 := ⟨none, rfl⟩

/-- The symbol of the order relation variable. -/
def fvsLtSym : feedbackGuessBlock.lang.Relations 2 := ⟨some true, rfl⟩

/-- The symbol of the injection relation variable. -/
def fvsInjSym : feedbackGuessBlock.lang.Relations 2 := ⟨some false, rfl⟩

/-- The vocabulary of the kernel: marked graphs together with the three
guessed relation variables. -/
abbrev fvsSOLang : Language := Language.markedGraph.sum feedbackGuessBlock.lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev fAdjSym : fvsSOLang.Relations 2 := Sum.inl mgAdj

/-- The mark symbol in the kernel's vocabulary. -/
abbrev fMarkedSym : fvsSOLang.Relations 1 := Sum.inl mgMarked

/-- The removed-set symbol in the kernel's vocabulary. -/
abbrev fSetSym : fvsSOLang.Relations 1 := Sum.inr fvsSetSym

/-- The order symbol in the kernel's vocabulary. -/
abbrev fLtSym : fvsSOLang.Relations 2 := Sum.inr fvsLtSym

/-- The injection symbol in the kernel's vocabulary. -/
abbrev fInjSym : fvsSOLang.Relations 2 := Sum.inr fvsInjSym

/-- Kernel conjunct: the guessed order is transitive. -/
private noncomputable def fvsTransClause : fvsSOLang.Sentence :=
  ((Relations.formula₂ fLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ fLtSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Relations.formula₂ fLtSym (Term.var (Sum.inr 0))
      (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel conjunct: the guessed order is irreflexive. -/
private noncomputable def fvsIrreflClause : fvsSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    (∼(Relations.formula₂ fLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))))

/-- Kernel conjunct: every surviving arc goes forward in the guessed
order. -/
private noncomputable def fvsArcClause : fvsSOLang.Sentence :=
  ((Relations.formula₂ fAdjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      ∼(Relations.formula₁ fSetSym (Term.var (Sum.inr 0))) ⊓
      ∼(Relations.formula₁ fSetSym (Term.var (Sum.inr 1)))).imp
    (Relations.formula₂ fLtSym (Term.var (Sum.inr 0))
      (Term.var (Sum.inr 1)))).iAlls (Fin 2)

/-- Kernel conjunct: the guessed injection maps every removed vertex to a
marked element. -/
private noncomputable def fvsTotalClause : fvsSOLang.Sentence :=
  ((Relations.formula₁ fSetSym (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ fInjSym (Term.var (Sum.inl (Sum.inr 0)))
        (Term.var (Sum.inr ())) ⊓
      Relations.formula₁ fMarkedSym (Term.var (Sum.inr ()))).iExs Unit)).iAlls (Fin 1)

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def fvsInjClause : fvsSOLang.Sentence :=
  ((Relations.formula₂ fInjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ fInjSym (Term.var (Sum.inr 1))
        (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- The first-order kernel of the `Σ₁` definition of Feedback Vertex Set. -/
noncomputable def feedbackKernel : fvsSOLang.Sentence :=
  fvsTransClause ⊓ (fvsIrreflClause ⊓ (fvsArcClause ⊓ (fvsTotalClause ⊓ fvsInjClause)))

/-- Realization of the kernel under an assignment of the three relation
variables. -/
private theorem realize_feedbackKernel {A : Type} [Language.markedGraph.Structure A]
    (ρ : feedbackGuessBlock.Assignment A) :
    (@Sentence.Realize fvsSOLang A
        (@sumStructure _ _ A _ (feedbackGuessBlock.structure ρ)) feedbackKernel) ↔
      (∀ x y z : A, ρ (some true) ![x, y] → ρ (some true) ![y, z] → ρ (some true) ![x, z]) ∧
        (∀ x : A, ¬ρ (some true) ![x, x]) ∧
        (∀ x y : A, MGAdj x y → ¬ρ none ![x] → ¬ρ none ![y] → ρ (some true) ![x, y]) ∧
        (∀ x : A, ρ none ![x] → ∃ y : A, ρ (some false) ![x, y] ∧ MGMarked y) ∧
        ∀ x x' y : A, ρ (some false) ![x, y] → ρ (some false) ![x', y] → x = x' := by
  letI := feedbackGuessBlock.structure ρ
  have hsubS : ∀ (w : Fin 1 → A),
      RelMap (L := fvsSOLang) (M := A) fSetSym w ↔ ρ none w := fun _ => Iff.rfl
  have hsubL : ∀ (w : Fin 2 → A),
      RelMap (L := fvsSOLang) (M := A) fLtSym w ↔ ρ (some true) w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := fvsSOLang) (M := A) fInjSym w ↔ ρ (some false) w := fun _ => Iff.rfl
  rw [feedbackKernel]
  simp only [fvsTransClause, fvsIrreflClause, fvsArcClause, fvsTotalClause,
    fvsInjClause, Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iExs, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Formula.realize_equal,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl,
    hsubS, hsubL, hsubI]
  refine and_congr ⟨fun h x y z hxy hyz => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x => ?_, fun h i => ?_⟩
      (and_congr ⟨fun h x y hadj hx hy => ?_, fun h i hi => ?_⟩
        (and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
          ⟨fun h x x' y hxy hx'y => ?_, fun h i hi => ?_⟩)))
  · exact h ![x, y, z] ⟨hxy, hyz⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2
  · exact h fun _ => x
  · exact h (i 0)
  · exact h ![x, y] ⟨⟨hadj, hx⟩, hy⟩
  · exact h (i 0) (i 1) hi.1.1 hi.1.2 hi.2
  · obtain ⟨y, hy1, hy2⟩ := h (fun _ => x) hx
    exact ⟨y (), hy1, hy2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy1, hy2⟩
  · exact h ![x, x', y] ⟨hxy, hx'y⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2

/-- **Feedback Vertex Set is `Σ₁`-definable**: existentially guess the
removed set, a strict partial order certifying that the rest is acyclic, and
an injection of the removed set into the marked set, then check all five
conditions first-order. Since NP is defined as `Σ₁`-definability, this is the
membership half of the NP-completeness of Feedback Vertex Set. -/
theorem feedbackVertexSet_sigmaSODefinable : SigmaSODefinable 1 FeedbackVertexSet := by
  refine ⟨[feedbackGuessBlock], rfl, feedbackKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hfvs⟩
    obtain ⟨C, ⟨Lt, htrans, hirr, hmono⟩, ⟨e⟩⟩ := (feedbackOn_iff_certificate _ _).mp hfvs
    refine ⟨fun i => match i with
      | none => fun w : Fin 1 → A => C (w 0)
      | some true => fun w : Fin 2 → A => Lt (w 0) (w 1)
      | some false => fun w : Fin 2 → A =>
          ∃ h : C (w 0), (e ⟨w 0, h⟩ : {x // MGMarked x}).1 = w 1, ?_⟩
    refine (realize_feedbackKernel _).mpr
      ⟨htrans, hirr,
        fun x y hadj hx hy => hmono x y ⟨hx, hy, hadj⟩,
        fun x hx => ⟨(e ⟨x, hx⟩).1, ⟨hx, rfl⟩, (e ⟨x, hx⟩).2⟩, ?_⟩
    rintro x x' y ⟨h, hy⟩ ⟨h', hy'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hy.trans hy'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htrans, hirr, harc, htot, hinj⟩ := (realize_feedbackKernel ρ).mp hρ
    have hch : ∀ x : {x : A // ρ none ![x]},
        ∃ y : A, ρ (some false) ![x.1, y] ∧ MGMarked y := fun x => htot x.1 x.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (feedbackOn_iff_certificate _ _).mpr
      ⟨fun a => ρ none ![a],
        ⟨fun x y => ρ (some true) ![x, y], htrans, hirr,
          fun a b hab => harc a b hab.2.2 hab.1 hab.2.1⟩,
        ⟨⟨fun x => ⟨f x, hf2 x⟩, fun x x' hxx' => ?_⟩⟩⟩⟩
    have hval : f x = f x' := congrArg Subtype.val hxx'
    refine Subtype.ext (hinj x.1 x'.1 (f x) (hf1 x) ?_)
    rw [hval]
    exact hf1 x'

end SigmaOne

/-! ### NP-completeness -/

/-- Feedback Vertex Set is in NP: it is `Σ₁`-definable. -/
theorem feedbackVertexSet_mem_NP : FeedbackVertexSet ∈ NP :=
  feedbackVertexSet_sigmaSODefinable

/-- Feedback Vertex Set is NP-hard: Vertex Cover, which is NP-hard, reduces
to it by symmetrizing the adjacency relation. -/
theorem feedbackVertexSet_NP_hard : NP.Hard FeedbackVertexSet :=
  NP.hard_of_foReduction vertexCover_fo_reduction_feedbackVertexSet vertexCover_NP_hard

/-- **Feedback Vertex Set is NP-complete**, derived from the first-order
reductions of this library and the Cook–Levin theorem. -/
theorem feedbackVertexSet_NP_complete : NP.Complete FeedbackVertexSet :=
  ⟨feedbackVertexSet_mem_NP, feedbackVertexSet_NP_hard⟩

end DescriptiveComplexity
