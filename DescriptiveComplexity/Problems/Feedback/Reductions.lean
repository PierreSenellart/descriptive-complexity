/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Feedback.Defs

/-!
# Hardness of the feedback problems

Two quantifier-free first-order reductions, both of dimension 1:

* `DescriptiveComplexity.vertexCover_fo_reduction_feedbackVertexSet`: **Vertex Cover
  reduces to Feedback Vertex Set**, by *symmetrizing* the adjacency relation
  off the diagonal (`DescriptiveComplexity.symmetrizeInterp`, tag `Unit`). Every edge
  of the input becomes a 2-cycle, so a set of vertices kills every cycle iff
  it meets every edge – killing all 2-cycles already removes every arc
  (`DescriptiveComplexity.coverOn_iff_feedbackOn`). The marked set is copied, so there
  is no counting step at all.

* `DescriptiveComplexity.feedbackVertexSet_fo_reduction_feedbackArcSet`: **Feedback
  Vertex Set reduces to Feedback Arc Set**, by the classical *vertex
  splitting* (`DescriptiveComplexity.splitInterp`, tag `Bool`): each vertex `v` becomes
  an in-copy `DescriptiveComplexity.inPt` and an out-copy `DescriptiveComplexity.outPt`
  joined by an internal arc, and each arc `(u, v)` of the input becomes the
  crossing arc from `u`'s out-copy to `v`'s in-copy. Cutting the internal arc
  of `v` is deleting the vertex `v`; the marked relation marks exactly the
  internal arcs of the marked vertices, so the threshold is preserved on the
  nose.

## Splitting, without ever manipulating a cycle

The correctness of the splitting is where the certificate form of acyclicity
(`DescriptiveComplexity.acyclicRel_iff_exists_order`) pays off: both directions build a
strict partial order out of another one, and no cycle is ever decomposed.

* Forward, a feedback vertex set `C` of the input with certificate order `Lt`
  gives the order `DescriptiveComplexity.splitLt`: the out-copies of `C` go to the
  bottom, the in-copies of `C` to the top, and everything else keeps `Lt`
  (with the in-copy of a vertex just below its out-copy). Every uncut arc goes
  forward in it – the case that needs `Lt` is exactly a crossing arc between
  two vertices outside `C`, which is a surviving arc of the input.
* Backward, a feedback arc set `F` of the split graph gives back the set of
  *source vertices* of the arcs in `F`, which is no larger
  (`Set.ncard_image_le`), and the order `fun u v => Lt' (inPt u) (inPt v)`.
  For an input arc `(u, v)` with both endpoints outside that set, neither the
  internal arc of `u` nor the crossing arc `(u_out, v_in)` can be in `F`,
  since both have source vertex `u`; so both go forward in `Lt'`, and
  transitivity closes the case.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

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

section SymmetrizeCharacterizations

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

end SymmetrizeCharacterizations

section SymmetrizeCorrectness

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

end SymmetrizeCorrectness

/-- **Vertex Cover FO-reduces to Feedback Vertex Set**, by symmetrizing the
adjacency relation: every edge becomes a 2-cycle, so the feedback vertex sets
are exactly the vertex covers. -/
def vertexCover_fo_reduction_feedbackVertexSet : VertexCover ≤ᶠᵒ FeedbackVertexSet where
  Tag := Unit
  dim := 1
  toInterpretation := symmetrizeInterp
  correct A _ _ := hasSmallVertexCover_iff_feedback_map A

/-! ### Feedback Vertex Set reduces to Feedback Arc Set

The vertex-splitting interpretation: the tag `true` carries the in-copy of a
vertex and the tag `false` its out-copy. -/

/-- The vertex-splitting interpretation: `v` becomes an in-copy and an
out-copy joined by an internal arc, an arc `(u, v)` becomes the crossing arc
from `u`'s out-copy to `v`'s in-copy, and the marked relation marks the
internal arcs of the marked vertices. -/
def splitInterp :
    FOInterpretation Language.markedGraph Language.markedArcGraph Bool 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t =>
      match t 0, t 1 with
      | true, false => Term.equal (Term.var (0, 0)) (Term.var (1, 0))
      | false, true => mgAdj.formula₂ (Term.var (0, 0)) (Term.var (1, 0))
      | _, _ => ⊥
    | _, .markedArc => fun t =>
      match t 0, t 1 with
      | true, false =>
          Term.equal (Term.var (0, 0)) (Term.var (1, 0)) ⊓
            mgMarked.formula₁ (Term.var (0, 0))
      | _, _ => ⊥

/-- The vertex-splitting interpretation is quantifier-free. -/
theorem splitInterp_isQuantifierFree : splitInterp.IsQuantifierFree := by
  intro n R t
  cases R with
  | adj =>
    rcases h0 : t 0 with _ | _ <;> rcases h1 : t 1 with _ | _ <;>
      simp only [splitInterp, h0, h1]
    · exact isQF_bot
    · exact (IsAtomic.rel _ _).isQF
    · exact (IsAtomic.equal _ _).isQF
    · exact isQF_bot
  | markedArc =>
    rcases h0 : t 0 with _ | _ <;> rcases h1 : t 1 with _ | _ <;>
      simp only [splitInterp, h0, h1]
    · exact isQF_bot
    · exact isQF_bot
    · exact (IsAtomic.equal _ _).isQF.inf (IsAtomic.rel _ _).isQF
    · exact isQF_bot

/-! #### The two copies of a vertex -/

section Copies

variable {A : Type}

/-- The in-copy of a vertex in the split digraph. -/
def inPt (v : A) : splitInterp.Map A := (true, fun _ => v)

/-- The out-copy of a vertex in the split digraph. -/
def outPt (v : A) : splitInterp.Map A := (false, fun _ => v)

theorem inPt_injective : Function.Injective (inPt (A := A)) := by
  intro v v' h
  exact congrArg (fun p : Bool × (Fin 1 → A) => p.2 0) h

theorem outPt_injective : Function.Injective (outPt (A := A)) := by
  intro v v' h
  exact congrArg (fun p : Bool × (Fin 1 → A) => p.2 0) h

theorem inPt_ne_outPt (v v' : A) : inPt v ≠ outPt v' := by
  intro h
  exact Bool.noConfusion (congrArg (fun p : Bool × (Fin 1 → A) => p.1) h)

theorem inPt_eta (w : Fin 1 → A) : ((true, w) : splitInterp.Map A) = inPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

theorem outPt_eta (w : Fin 1 → A) : ((false, w) : splitInterp.Map A) = outPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

/-- Every element of the split universe is a copy of a vertex. -/
theorem eq_inPt_or_outPt (p : splitInterp.Map A) :
    (∃ v, p = inPt v) ∨ ∃ v, p = outPt v := by
  rcases p with ⟨b, w⟩
  cases b
  · exact Or.inr ⟨w 0, outPt_eta w⟩
  · exact Or.inl ⟨w 0, inPt_eta w⟩

end Copies

/-! #### The arcs and marks of the split digraph -/

section SplitCharacterizations

variable {A : Type} [Language.markedGraph.Structure A]

@[simp]
theorem split_adj_in_out (w₁ w₂ : Fin 1 → A) :
    RelMap (M := splitInterp.Map A) magAdj ![(true, w₁), (false, w₂)] ↔ w₁ 0 = w₂ 0 := by
  rw [FOInterpretation.relMap_map]
  simp [splitInterp]

@[simp]
theorem split_adj_out_in (w₁ w₂ : Fin 1 → A) :
    RelMap (M := splitInterp.Map A) magAdj ![(false, w₁), (true, w₂)] ↔
      RelMap mgAdj ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [splitInterp, Formula.realize_rel₂]

@[simp]
theorem split_adj_in_in (w₁ w₂ : Fin 1 → A) :
    ¬RelMap (M := splitInterp.Map A) magAdj ![(true, w₁), (true, w₂)] := by
  rw [FOInterpretation.relMap_map]
  simp [splitInterp]

@[simp]
theorem split_adj_out_out (w₁ w₂ : Fin 1 → A) :
    ¬RelMap (M := splitInterp.Map A) magAdj ![(false, w₁), (false, w₂)] := by
  rw [FOInterpretation.relMap_map]
  simp [splitInterp]

@[simp]
theorem split_marked_in_out (w₁ w₂ : Fin 1 → A) :
    RelMap (M := splitInterp.Map A) magMarked ![(true, w₁), (false, w₂)] ↔
      w₁ 0 = w₂ 0 ∧ RelMap mgMarked ![w₁ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [splitInterp, Formula.realize_rel₁]

@[simp]
theorem split_marked_in_in (w₁ w₂ : Fin 1 → A) :
    ¬RelMap (M := splitInterp.Map A) magMarked ![(true, w₁), (true, w₂)] := by
  rw [FOInterpretation.relMap_map]
  simp [splitInterp]

@[simp]
theorem split_marked_out_in (w₁ w₂ : Fin 1 → A) :
    ¬RelMap (M := splitInterp.Map A) magMarked ![(false, w₁), (true, w₂)] := by
  rw [FOInterpretation.relMap_map]
  simp [splitInterp]

@[simp]
theorem split_marked_out_out (w₁ w₂ : Fin 1 → A) :
    ¬RelMap (M := splitInterp.Map A) magMarked ![(false, w₁), (false, w₂)] := by
  rw [FOInterpretation.relMap_map]
  simp [splitInterp]

/-! #### The interface used by the correctness proofs

Rather than the raw characterizations, the proofs below use the two arc
constructors and the two “only these” lemmas, which never mention the shape of
an element of the interpreted universe. -/

/-- The internal arc of a vertex. -/
theorem split_adj_internal (v : A) : MAGAdj (inPt v) (outPt v) :=
  (split_adj_in_out (A := A) (fun _ => v) fun _ => v).mpr rfl

/-- The crossing arc attached to an arc of the input. -/
theorem split_adj_crossing {u v : A} (h : MGAdj u v) : MAGAdj (outPt u) (inPt v) :=
  (split_adj_out_in (A := A) (fun _ => u) fun _ => v).mpr h

/-- The arcs of the split digraph are the internal and the crossing ones. -/
theorem split_adj_cases {p q : splitInterp.Map A} (h : MAGAdj p q) :
    (∃ v, p = inPt v ∧ q = outPt v) ∨ ∃ u v, p = outPt u ∧ q = inPt v ∧ MGAdj u v := by
  rcases p with ⟨(_ | _), w⟩ <;> rcases q with ⟨(_ | _), w'⟩
  · exact absurd h (split_adj_out_out w w')
  · exact Or.inr ⟨w 0, w' 0, outPt_eta w, inPt_eta w', (split_adj_out_in w w').mp h⟩
  · exact Or.inl ⟨w 0, inPt_eta w,
      (outPt_eta w').trans (congrArg outPt ((split_adj_in_out w w').mp h).symm)⟩
  · exact absurd h (split_adj_in_in w w')

/-- The marked arcs of the split digraph are the internal arcs of the marked
vertices. -/
theorem split_marked_cases {p q : splitInterp.Map A} (h : MAGMarked p q) :
    ∃ v, MGMarked v ∧ p = inPt v ∧ q = outPt v := by
  rcases p with ⟨(_ | _), w⟩ <;> rcases q with ⟨(_ | _), w'⟩
  · exact absurd h (split_marked_out_out w w')
  · exact absurd h (split_marked_out_in w w')
  · obtain ⟨heq, hm⟩ := (split_marked_in_out w w').mp h
    exact ⟨w 0, hm, inPt_eta w, (outPt_eta w').trans (congrArg outPt heq.symm)⟩
  · exact absurd h (split_marked_in_in w w')

/-- The internal arc of a marked vertex is marked. -/
theorem split_marked_internal {v : A} (h : MGMarked v) : MAGMarked (inPt v) (outPt v) :=
  (split_marked_in_out (A := A) (fun _ => v) fun _ => v).mpr ⟨rfl, h⟩

end SplitCharacterizations

/-! #### Counting on the internal arcs -/

section SplitCounting

variable {A : Type}

/-- A relation on the split universe that only holds of internal arcs encodes
the same number as the set of vertices whose internal arc it holds of. -/
theorem ncard_internal_eq (P : A → Prop)
    (Q : splitInterp.Map A × splitInterp.Map A → Prop)
    (hshape : ∀ pq, Q pq → ∃ v, pq = (inPt v, outPt v))
    (hP : ∀ v : A, Q (inPt v, outPt v) ↔ P v) :
    {pq | Q pq}.ncard = {v | P v}.ncard := by
  have hinj : Function.Injective fun v : A => (inPt v, outPt v) := fun v v' h =>
    inPt_injective (congrArg Prod.fst h)
  have hset : {pq | Q pq} = (fun v : A => (inPt v, outPt v)) '' {v | P v} := by
    ext pq
    constructor
    · intro hq
      obtain ⟨v, rfl⟩ := hshape pq hq
      exact ⟨v, (hP v).mp hq, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hP v).mpr hv
  rw [hset, Set.ncard_image_of_injective _ hinj]

end SplitCounting

/-! #### Correctness of the splitting -/

section SplitOrder

variable {A : Type}

/-- The arcs cut by the interpretation for a set `C` of vertices: the internal
arcs of the members of `C`. -/
def cutArcs (C : A → Prop) (p q : splitInterp.Map A) : Prop :=
  ∃ v, C v ∧ p = inPt v ∧ q = outPt v

open Classical in
/-- The level of a copy in the order built from a feedback vertex set: the
out-copies of removed vertices go to the bottom, their in-copies to the top,
everything else in between. -/
noncomputable def splitLvl (C : A → Prop) (p : splitInterp.Map A) : ℕ :=
  if C (p.2 0) then (if p.1 then 2 else 0) else 1

/-- The order on the split digraph built from a certificate order of the
input: levels first, then the input order, with the in-copy of a vertex just
below its out-copy. -/
noncomputable def splitLt (C : A → Prop) (Lt : A → A → Prop)
    (p q : splitInterp.Map A) : Prop :=
  splitLvl C p < splitLvl C q ∨
    (splitLvl C p = 1 ∧ splitLvl C q = 1 ∧
      (Lt (p.2 0) (q.2 0) ∨ (p.2 0 = q.2 0 ∧ p.1 = true ∧ q.1 = false)))

open Classical in
private theorem splitLvl_inPt (C : A → Prop) (v : A) :
    splitLvl C (inPt v) = if C v then 2 else 1 := by
  classical
  simp [splitLvl, inPt]

open Classical in
private theorem splitLvl_outPt (C : A → Prop) (v : A) :
    splitLvl C (outPt v) = if C v then 0 else 1 := by
  classical
  simp [splitLvl, outPt]

private theorem splitLt_trans (C : A → Prop) (Lt : A → A → Prop)
    (htrans : ∀ x y z, Lt x y → Lt y z → Lt x z) (p q r : splitInterp.Map A)
    (hpq : splitLt C Lt p q) (hqr : splitLt C Lt q r) : splitLt C Lt p r := by
  rcases hpq with hpq | ⟨hp1, hq1, hinner⟩
  · rcases hqr with hqr | ⟨hq1, hr1, -⟩
    · exact Or.inl (lt_trans hpq hqr)
    · exact Or.inl (by omega)
  · rcases hqr with hqr | ⟨-, hr1, hinner'⟩
    · exact Or.inl (by omega)
    refine Or.inr ⟨hp1, hr1, ?_⟩
    rcases hinner with hlt | ⟨heq, hpin, hqout⟩ <;> rcases hinner' with hlt' | ⟨heq', hqin, hrout⟩
    · exact Or.inl (htrans _ _ _ hlt hlt')
    · exact Or.inl (heq' ▸ hlt)
    · exact Or.inl (heq ▸ hlt')
    · exact absurd (hqout.symm.trans hqin) (by simp)

private theorem splitLt_irrefl (C : A → Prop) (Lt : A → A → Prop)
    (hirr : ∀ x, ¬Lt x x) (p : splitInterp.Map A) : ¬splitLt C Lt p p := by
  rintro (h | ⟨-, -, hlt | ⟨-, hin, hout⟩⟩)
  · exact absurd h (lt_irrefl _)
  · exact hirr _ hlt
  · exact absurd (hout.symm.trans hin) (by simp)

end SplitOrder

section SplitCorrectness

variable {A : Type} [Language.markedGraph.Structure A]

/-- Correctness of the vertex splitting: a graph has a feedback vertex set at
most as large as its marked set iff the split digraph has a feedback arc set
at most as large as its marked relation. -/
theorem hasSmallFeedbackSet_iff_feedbackArc_map (A : Type)
    [Language.markedGraph.Structure A] :
    HasSmallFeedbackSet A ↔ HasSmallFeedbackArcSet (splitInterp.Map A) := by
  have hmarked : ∀ [Finite A],
      {pq : splitInterp.Map A × splitInterp.Map A | MAGMarked pq.1 pq.2}.ncard
        = {v : A | MGMarked v}.ncard := by
    intro _
    refine ncard_internal_eq MGMarked _ (fun pq h => ?_) fun v => ⟨fun h => ?_, ?_⟩
    · obtain ⟨v, -, h1, h2⟩ := split_marked_cases h
      exact ⟨v, Prod.ext h1 h2⟩
    · obtain ⟨v', hv', h1, -⟩ := split_marked_cases h
      exact inPt_injective h1 ▸ hv'
    · exact fun h => split_marked_internal h
  constructor
  · rintro ⟨hfin, hfvs⟩
    haveI := hfin
    haveI : Finite (splitInterp.Map A) := splitInterp.map_finite A
    obtain ⟨C, ⟨Lt, htrans, hirr, hmono⟩, ⟨e⟩⟩ := (feedbackOn_iff_certificate _ _).mp hfvs
    have hforward : ∀ p q : splitInterp.Map A,
        UncutArc MAGAdj (cutArcs C) p q → splitLt C Lt p q := by
      rintro p q ⟨hadj, hcut⟩
      rcases split_adj_cases hadj with ⟨v, rfl, rfl⟩ | ⟨u, v, rfl, rfl, huv⟩
      · have hv : ¬C v := fun hv => hcut ⟨v, hv, rfl, rfl⟩
        exact Or.inr ⟨by rw [splitLvl_inPt, if_neg hv], by rw [splitLvl_outPt, if_neg hv],
          Or.inr ⟨rfl, rfl, rfl⟩⟩
      · rcases Classical.em (C u) with hu | hu
        · refine Or.inl ?_
          rw [splitLvl_outPt, if_pos hu, splitLvl_inPt]
          split <;> omega
        rcases Classical.em (C v) with hv | hv
        · refine Or.inl ?_
          rw [splitLvl_outPt, if_neg hu, splitLvl_inPt, if_pos hv]
          omega
        · exact Or.inr ⟨by rw [splitLvl_outPt, if_neg hu], by rw [splitLvl_inPt, if_neg hv],
            Or.inl (hmono u v ⟨hu, hv, huv⟩)⟩
    have hcut : {pq : splitInterp.Map A × splitInterp.Map A | cutArcs C pq.1 pq.2}.ncard
        = {v : A | C v}.ncard := by
      refine ncard_internal_eq C _ (fun pq h => ?_) fun v => ⟨fun h => ?_, ?_⟩
      · obtain ⟨v, -, h1, h2⟩ := h
        exact ⟨v, Prod.ext h1 h2⟩
      · obtain ⟨v', hv', h1, -⟩ := h
        exact inPt_injective h1 ▸ hv'
      · exact fun hv => ⟨v, hv, rfl, rfl⟩
    refine ⟨inferInstance, (feedbackArcOn_iff_certificate _ _).mpr
      ⟨cutArcs C, ⟨splitLt C Lt, splitLt_trans C Lt htrans, splitLt_irrefl C Lt hirr,
        hforward⟩, (nonempty_embedding_iff_ncard_le₂ _ _).mpr ?_⟩⟩
    rw [hcut, hmarked]
    exact (nonempty_embedding_iff_ncard_le C MGMarked).mp ⟨e⟩
  · rintro ⟨hfin, hfas⟩
    haveI := hfin
    have hA : Finite A := Finite.of_injective _ (inPt_injective (A := A))
    haveI := hA
    obtain ⟨F, ⟨Lt', htrans, hirr, hmono⟩, ⟨e⟩⟩ := (feedbackArcOn_iff_certificate _ _).mp hfas
    -- the removed set is the set of source vertices of the cut arcs
    set C : A → Prop := fun v => ∃ p q, F p q ∧ (p = inPt v ∨ p = outPt v) with hC
    have hforward : ∀ u v : A, SurvivingArc MGAdj C u v → Lt' (inPt u) (inPt v) := by
      rintro u v ⟨hu, hv, huv⟩
      have hint : ¬F (inPt u) (outPt u) := fun h => hu ⟨_, _, h, Or.inl rfl⟩
      have hcross : ¬F (outPt u) (inPt v) := fun h => hu ⟨_, _, h, Or.inr rfl⟩
      exact htrans _ _ _ (hmono _ _ ⟨split_adj_internal u, hint⟩)
        (hmono _ _ ⟨split_adj_crossing huv, hcross⟩)
    have hsrc : {v : A | C v} ⊆
        (fun pq : splitInterp.Map A × splitInterp.Map A => pq.1.2 0) ''
          {pq | F pq.1 pq.2} := by
      rintro v ⟨p, q, hF, hp | hp⟩
      · exact ⟨(p, q), hF, by rw [hp, inPt]⟩
      · exact ⟨(p, q), hF, by rw [hp, outPt]⟩
    refine ⟨hA, (feedbackOn_iff_certificate _ _).mpr
      ⟨C, ⟨fun u v => Lt' (inPt u) (inPt v), fun x y z hxy hyz => htrans _ _ _ hxy hyz,
        fun x => hirr _, hforward⟩, (nonempty_embedding_iff_ncard_le _ _).mpr ?_⟩⟩
    calc {v : A | C v}.ncard
        ≤ ((fun pq : splitInterp.Map A × splitInterp.Map A => pq.1.2 0) ''
            {pq | F pq.1 pq.2}).ncard := Set.ncard_le_ncard hsrc (Set.toFinite _)
      _ ≤ {pq : splitInterp.Map A × splitInterp.Map A | F pq.1 pq.2}.ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ ≤ {pq : splitInterp.Map A × splitInterp.Map A | MAGMarked pq.1 pq.2}.ncard :=
          (nonempty_embedding_iff_ncard_le₂ _ _).mp ⟨e⟩
      _ = {v : A | MGMarked v}.ncard := hmarked

end SplitCorrectness

/-- **Feedback Vertex Set FO-reduces to Feedback Arc Set**, by vertex
splitting: deleting a vertex becomes cutting its internal arc. -/
def feedbackVertexSet_fo_reduction_feedbackArcSet :
    FeedbackVertexSet ≤ᶠᵒ FeedbackArcSet where
  Tag := Bool
  dim := 1
  toInterpretation := splitInterp
  correct A _ _ := hasSmallFeedbackSet_iff_feedbackArc_map A

end DescriptiveComplexity
