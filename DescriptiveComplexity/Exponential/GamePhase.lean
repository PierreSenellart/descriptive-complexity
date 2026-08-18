/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameNode

/-!
# The sentences a phased game is made of

Every game this development builds over a tag-extended block —
`DescriptiveComplexity.SOGameSpec.exBlock` in
`DescriptiveComplexity.Exponential.GameSO`, and the graph game that carries
`DescriptiveComplexity.EXPTIME` to SO-GAME — says the same three things and
nothing else:

* **which phase a state is in**, in one copy or in the second one of a move
  (`DescriptiveComplexity.atTagF`, `DescriptiveComplexity.atTagTwoF`);
* **that the phase of the state a move enters is exactly one phase**, so that a
  junk state — two tag bits set — is never reachable
  (`DescriptiveComplexity.exists_tagAssign_two`);
* **that the listed relation variables do not change**, which is how a move
  freezes the part of the state it must not touch
  (`DescriptiveComplexity.varsFrozenS`).

`Exponential.GameSO` proves these for its own block; here they are stated once
for an **arbitrary** block and an arbitrary finite tag type, which is what the
graph game needs, its states being the nodes of
`DescriptiveComplexity.ExpExpansion.nodeBlock` — a merged tuple of rounds rather
than a `DescriptiveComplexity.SOBlock.cons`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0}) (C : SOBlock) (T : Type) [Finite T]

/-! ### The phase of a state -/

/-- The state is a well-formed one carrying the tag `p`. -/
noncomputable def atTagF (p : T) : ((L.sum Language.order).sum (C.withTag T).lang).Sentence :=
  SOBlock.tagGuardF (L := L.sum Language.order) C T ⊓ SOBlock.tagBitF C T p

/-- The tag bit of `p` in the second copy of a move. -/
noncomputable def tagTwoF (p : T) :
    (((L.sum Language.order).sum (C.withTag T).lang).sum (C.withTag T).lang).Sentence :=
  Relations.formula (Sum.inr (⟨Sum.inl p, rfl⟩ : (C.withTag T).lang.Relations 0)) Fin.elim0

open Classical in
/-- The second copy of a move carries exactly the tag `p`: its bit is set and no
other is. This is what keeps a junk state out of play. -/
noncomputable def atTagTwoF (p : T) :
    (((L.sum Language.order).sum (C.withTag T).lang).sum (C.withTag T).lang).Sentence :=
  tagTwoF L C T p ⊓
    listInf ((finEnum T).map fun q => if q = p then ⊤ else ∼(tagTwoF L C T q))

/-! ### Freezing part of a state -/

/-- The variable `i` of the block, in the first copy of a move. -/
abbrev varFstSym (i : C.ι) :
    (((L.sum Language.order).sum (C.withTag T).lang).sum
      (C.withTag T).lang).Relations (C.arity i) :=
  Sum.inl (Sum.inr ⟨Sum.inr i, rfl⟩)

/-- The variable `i` of the block, in the second copy of a move. -/
abbrev varSndSym (i : C.ι) :
    (((L.sum Language.order).sum (C.withTag T).lang).sum
      (C.withTag T).lang).Relations (C.arity i) :=
  Sum.inr ⟨Sum.inr i, rfl⟩

/-- The variable `i` is unchanged by the move. -/
noncomputable def varAgreeS (i : C.ι) :
    (((L.sum Language.order).sum (C.withTag T).lang).sum (C.withTag T).lang).Sentence :=
  Formula.iAlls (Fin (C.arity i))
    (((Relations.formula (varFstSym L C T i) fun j => Term.var (Sum.inr j)).imp
        (Relations.formula (varSndSym L C T i) fun j => Term.var (Sum.inr j))) ⊓
      ((Relations.formula (varSndSym L C T i) fun j => Term.var (Sum.inr j)).imp
        (Relations.formula (varFstSym L C T i) fun j => Term.var (Sum.inr j))))

/-- **The listed variables are unchanged by the move.** -/
noncomputable def varsFrozenS (vs : List C.ι) :
    (((L.sum Language.order).sum (C.withTag T).lang).sum (C.withTag T).lang).Sentence :=
  listInf (vs.map (varAgreeS L C T))

variable {L C T} {A : Type} [instL : L.Structure A] [LinearOrder A]

/-! ### What they say -/

theorem realize_atTagF (p q : T) (ν : C.Assignment A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₁ (L.sum Language.order) (C.withTag T) A
        (@sumOrderStructure L A instL _) (SOBlock.tagAssign q ν)) (atTagF L C T p) ↔ p = q) := by
  letI := @SOBlock.structure₁ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) (SOBlock.tagAssign q ν)
  refine Iff.trans Formula.realize_inf (and_iff_right ?_)
  exact (SOBlock.realize_tagGuardF (L := L.sum Language.order) _).mpr ⟨q, ν, rfl⟩

theorem realize_tagTwoF' (p : T) (σ τ : (C.withTag T).Assignment A)
    (x : Fin ((C.withTag T).arity (Sum.inl p)) → A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
        (@sumOrderStructure L A instL _) σ τ) (tagTwoF L C T p) ↔ τ (Sum.inl p) x) := by
  letI := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ τ
  haveI : IsEmpty (Fin ((C.withTag T).arity (Sum.inl p))) := inferInstanceAs (IsEmpty (Fin 0))
  exact iff_of_eq (congrArg (τ (Sum.inl p)) (funext fun i => isEmptyElim i))

theorem realize_tagTwoF (p q : T) (σ : (C.withTag T).Assignment A) (ν : C.Assignment A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
        (@sumOrderStructure L A instL _) σ (SOBlock.tagAssign q ν)) (tagTwoF L C T p) ↔ p = q) :=
  realize_tagTwoF' p σ (SOBlock.tagAssign q ν) fun i => i.elim0

open Classical in
theorem realize_atTagTwoF (p q : T) (σ : (C.withTag T).Assignment A) (ν : C.Assignment A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
        (@sumOrderStructure L A instL _) σ (SOBlock.tagAssign q ν))
      (atTagTwoF L C T p) ↔ p = q) := by
  letI := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ (SOBlock.tagAssign q ν)
  refine Iff.trans Formula.realize_inf ?_
  constructor
  · rintro ⟨h, -⟩
    exact (realize_tagTwoF p q σ ν).mp h
  · intro hpq
    refine ⟨(realize_tagTwoF p q σ ν).mpr hpq, ?_⟩
    rw [realize_listInf]
    intro ψ hψ
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hψ
    rcases eq_or_ne r p with rfl | hne
    · rw [if_pos rfl]
      exact Formula.realize_top.mpr trivial
    · rw [if_neg hne, Formula.realize_not]
      exact fun h => hne (((realize_tagTwoF r q σ ν).mp h).trans hpq.symm)

open Classical in
/-- **The guarded phase of the second copy pins its shape.** -/
theorem exists_tagAssign_two (p : T) (σ τ : (C.withTag T).Assignment A)
    (h : @Sentence.Realize _ A
      (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
        (@sumOrderStructure L A instL _) σ τ) (atTagTwoF L C T p)) :
    τ = SOBlock.tagAssign p (SOBlock.dropTag τ) := by
  letI := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ τ
  obtain ⟨hset, hrest⟩ := Formula.realize_inf.mp h
  rw [realize_listInf] at hrest
  funext i
  match i with
  | Sum.inl r =>
    funext x
    refine propext ⟨fun hr => ?_, fun hr => ?_⟩
    · rcases eq_or_ne r p with rfl | hne
      · rfl
      · have hne' := hrest _ (List.mem_map.mpr ⟨r, mem_finEnum r, rfl⟩)
        rw [if_neg hne, Formula.realize_not] at hne'
        exact absurd ((realize_tagTwoF' r σ τ x).mpr hr) hne'
    · have hrp : r = p := hr
      rw [hrp] at *
      exact (realize_tagTwoF' p σ τ x).mp hset
  | Sum.inr _ => rfl

end DescriptiveComplexity
