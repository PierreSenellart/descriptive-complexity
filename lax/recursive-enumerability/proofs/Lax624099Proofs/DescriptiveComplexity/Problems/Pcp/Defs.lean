/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.List.Forall2
import Lax624099Proofs.DescriptiveComplexity.Interpretation
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# PCP: Post's correspondence problem

*Given a list of pairs of words, is there a nonempty sequence of them whose
top words and whose bottom words have the same concatenation?*
([Post 1946][post1946variant]) This file carries the instance encoding – a
list of domino pairs, presented as a finite structure – and its semantics;
membership in RE lives in the sibling files.

## The encoding

The elements of an instance play three roles at once – dominoes, letters, and
positions inside a word – and, as in `Lax624099Proofs.DescriptiveComplexity.FINSAT`, nothing
forces those roles to be disjoint:

* `dom` marks the dominoes: a solution is a sequence of *marked* elements, so
  everything outside `dom` is junk that the semantics never reads;
* `uAt d p c` says that the **top** word of the domino `d` carries the letter
  `c` at the position `p`, and `vAt` the same for its **bottom** word;
* `le` is a linear order on the instance. A word is a *string*, so an encoding
  of one may certainly carry the order of its own positions; there is nothing
  else a position could be, and the semantics has to read the order to know in
  which order the letters of a word come.

The positions carrying the letters of a word are *not* required to form an
initial segment of the order: the word of `d` is the sequence of its letters
at the positions used, whichever those are. A partial map from a finite linear
order to letters already is a word, canonically, so the extra condition would
be one more thing to check and to establish for the image of a reduction, and
would buy nothing.

## The semantics

`Lax624099Proofs.DescriptiveComplexity.DecisionProblem.Holds` is a predicate on *every* type,
finite or not, so the word of a domino may not be defined by sorting a
`Finset` of the universe. Instead the enumeration of the positions is an
existential: `Lax624099Proofs.DescriptiveComplexity.Pcp.IsWordU d w` says that some strictly
increasing list enumerates exactly the positions used by the top word of `d`
and that `w` carries the letters at them. Such a list is unique when it exists
(two sorted duplicate-free lists with the same members are equal), so
`IsWordU d` holds of at most one list, and it holds of one as soon as the used
positions are finite. The problem is then exactly Post's
(`Lax624099Proofs.DescriptiveComplexity.Pcp.PcpOn`): a nonempty sequence of marked dominoes
whose top words and bottom words have the same concatenation.

## What is and is not claimed

RE is the logically defined class of
`Lax624099Proofs.DescriptiveComplexity.RecursivelyEnumerable` (definability in `∃SO[new]`), so
membership of PCP in it is a statement about that logic. RE-*hardness* is the
computation-history dominoes from the halting problem
(`Lax624099Proofs.DescriptiveComplexity.halt_ordered_fo_reduction_pcp`, in
`Lax624099Proofs.DescriptiveComplexity.Problems.Pcp.Hardness`) – a machine construction of
necessity, since unlike `Lax624099Proofs.DescriptiveComplexity.FINSAT`, PCP is not the
syntactic image of any logic. Together the two halves make PCP RE-complete
and Post's problem undecidable (`Lax624099Proofs.DescriptiveComplexity.pcp_RE_complete`,
`Lax624099Proofs.DescriptiveComplexity.pcp_not_computable`, in
`Lax624099Proofs.DescriptiveComplexity.Computability.PcpComplete`).
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Pcp

/-! ### Reading the encoding -/

section Reading

variable {A : Type} [Lax624099.PostCorrespondence.pcp.Structure A]

end Reading

/-! ### Well-formedness

Little is required of an instance, and all of it is first-order: the order
symbol is a linear order, and each of the two word relations is *functional in
the position*. Functionality is the only shape condition, and it cannot be
dispensed with – without it a “word” would carry a set of letters at some
position rather than a letter, and the letters that the two concatenations of
a solution must agree on would not be determined by the instance. Nothing is
required of the dominoes: an element outside `dom` may carry whatever letters
it likes, since no solution ever names it. -/

/-! ### The words of a domino

The word of a domino is the sequence of its letters, read in the order of the
positions carrying them. The enumeration of those positions is an existential
rather than a construction, so that the definition needs no finiteness of the
universe: a strictly increasing list whose members are exactly the used
positions, together with the letters at them. -/

section Words

variable {A : Type} [Lax624099.PostCorrespondence.pcp.Structure A]

end Words

/-! ### The problem -/

/-! ### Isomorphism-invariance

Everything the semantics reads is a relation of the instance, so an
isomorphism transports it: the sequence of dominoes and the two lists of words
are carried over by `List.map`, and the enumerations of the positions with
them. Only one direction is proved; the converse is the same statement at the
inverse isomorphism. -/

section Iso

variable {A B : Type} [Lax624099.PostCorrespondence.pcp.Structure A] [Lax624099.PostCorrespondence.pcp.Structure B]

variable (e : A ≃[Lax624099.PostCorrespondence.pcp] B)

theorem ord_equiv (x y : A) : Lax624099.PostCorrespondence.Pcp.Ord x y ↔ Lax624099.PostCorrespondence.Pcp.Ord (e x) (e y) := relMap_equiv₂ e _ x y

theorem ordLt_equiv (x y : A) : Lax624099.PostCorrespondence.Pcp.OrdLt x y ↔ Lax624099.PostCorrespondence.Pcp.OrdLt (e x) (e y) :=
  and_congr (ord_equiv e x y)
    (not_congr ⟨fun h => h ▸ rfl, fun h => EmbeddingLike.injective e h⟩)

theorem domG_equiv (d : A) : Lax624099.PostCorrespondence.Pcp.DomG d ↔ Lax624099.PostCorrespondence.Pcp.DomG (e d) := relMap_equiv₁ e _ d

theorem uAt_equiv (d p c : A) : Lax624099.PostCorrespondence.Pcp.UAt d p c ↔ Lax624099.PostCorrespondence.Pcp.UAt (e d) (e p) (e c) := relMap_equiv₃ e _ d p c

theorem vAt_equiv (d p c : A) : Lax624099.PostCorrespondence.Pcp.VAt d p c ↔ Lax624099.PostCorrespondence.Pcp.VAt (e d) (e p) (e c) := relMap_equiv₃ e _ d p c

theorem usedU_equiv (d p : A) : Lax624099.PostCorrespondence.Pcp.UsedU d p ↔ Lax624099.PostCorrespondence.Pcp.UsedU (e d) (e p) := by
  refine ⟨fun ⟨c, hc⟩ => ⟨e c, (uAt_equiv e d p c).mp hc⟩, fun ⟨c, hc⟩ => ⟨e.symm c, ?_⟩⟩
  refine (uAt_equiv e d p (e.symm c)).mpr ?_
  rwa [e.apply_symm_apply]

theorem usedV_equiv (d p : A) : Lax624099.PostCorrespondence.Pcp.UsedV d p ↔ Lax624099.PostCorrespondence.Pcp.UsedV (e d) (e p) := by
  refine ⟨fun ⟨c, hc⟩ => ⟨e c, (vAt_equiv e d p c).mp hc⟩, fun ⟨c, hc⟩ => ⟨e.symm c, ?_⟩⟩
  refine (vAt_equiv e d p (e.symm c)).mpr ?_
  rwa [e.apply_symm_apply]

/-! The same transports read backwards, at the inverse isomorphism: the shape
every field of `Lax624099Proofs.DescriptiveComplexity.Pcp.isWF_map` needs. -/

theorem ord_equiv' (x y : B) : Lax624099.PostCorrespondence.Pcp.Ord x y ↔ Lax624099.PostCorrespondence.Pcp.Ord (e.symm x) (e.symm y) := by
  have h := (ord_equiv e (e.symm x) (e.symm y)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem uAt_equiv' (d p c : B) : Lax624099.PostCorrespondence.Pcp.UAt d p c ↔ Lax624099.PostCorrespondence.Pcp.UAt (e.symm d) (e.symm p) (e.symm c) := by
  have h := (uAt_equiv e (e.symm d) (e.symm p) (e.symm c)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h

theorem vAt_equiv' (d p c : B) : Lax624099.PostCorrespondence.Pcp.VAt d p c ↔ Lax624099.PostCorrespondence.Pcp.VAt (e.symm d) (e.symm p) (e.symm c) := by
  have h := (vAt_equiv e (e.symm d) (e.symm p) (e.symm c)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h

private theorem eq_of_symm_eq {x y : B} (h : e.symm x = e.symm y) : x = y := by
  have h' := congrArg e h
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h'

/-- Well-formedness transports along an isomorphism. -/
theorem isWF_map (e : A ≃[Lax624099.PostCorrespondence.pcp] B) (h : Lax624099.PostCorrespondence.Pcp.IsWF A) : Lax624099.PostCorrespondence.Pcp.IsWF B where
  ord_refl x := (ord_equiv' e x x).mpr (h.ord_refl _)
  ord_trans x y z hxy hyz := (ord_equiv' e x z).mpr
    (h.ord_trans _ _ _ ((ord_equiv' e x y).mp hxy) ((ord_equiv' e y z).mp hyz))
  ord_antisymm x y hxy hyx := eq_of_symm_eq e
    (h.ord_antisymm _ _ ((ord_equiv' e x y).mp hxy) ((ord_equiv' e y x).mp hyx))
  ord_total x y := (h.ord_total (e.symm x) (e.symm y)).imp
    (ord_equiv' e x y).mpr (ord_equiv' e y x).mpr
  uAt_fun d p c c' hc hc' := eq_of_symm_eq e
    (h.uAt_fun _ _ _ _ ((uAt_equiv' e d p c).mp hc) ((uAt_equiv' e d p c').mp hc'))
  vAt_fun d p c c' hc hc' := eq_of_symm_eq e
    (h.vAt_fun _ _ _ _ ((vAt_equiv' e d p c).mp hc) ((vAt_equiv' e d p c').mp hc'))

end Iso

/-! ### Transporting lists

Two small facts about lists, stated for arbitrary relations because the words
and the sequence of dominoes need them at four different instances: a sorted
list stays sorted under a map preserving the order, and `List.Forall₂` is
functorial. -/

section ListTransport

variable {α β γ δ : Type}

theorem pairwise_map_of {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (hf : ∀ a b, R a b → S (f a) (f b)) :
    ∀ {l : List α}, l.Pairwise R → (l.map f).Pairwise S
  | [], _ => by simp
  | _ :: l, hl => by
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨fun b hb => ?_, pairwise_map_of f hf hl.2⟩
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    exact hf _ _ (hl.1 b' hb')

theorem forall₂_map_map {R : α → β → Prop} {S : γ → δ → Prop} (f : α → γ) (g : β → δ)
    (hfg : ∀ a b, R a b → S (f a) (g b)) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S (l₁.map f) (l₂.map g)
  | [], [], _ => List.Forall₂.nil
  | _ :: _, _ :: _, h => by
    rcases h with _ | ⟨hab, htl⟩
    exact List.Forall₂.cons (hfg _ _ hab) (forall₂_map_map f g hfg htl)

end ListTransport

section IsoWords

variable {A B : Type} [Lax624099.PostCorrespondence.pcp.Structure A] [Lax624099.PostCorrespondence.pcp.Structure B]

variable (e : A ≃[Lax624099.PostCorrespondence.pcp] B)

/-- The top word of a domino transports along an isomorphism. -/
theorem isWordU_map {d : A} {w : List A} (h : Lax624099.PostCorrespondence.Pcp.IsWordU d w) : Lax624099.PostCorrespondence.Pcp.IsWordU (e d) (w.map e) := by
  obtain ⟨ps, hsort, hmem, hall⟩ := h
  refine ⟨ps.map e, pairwise_map_of e (fun a b hab => (ordLt_equiv e a b).mp hab) hsort,
    fun q => ?_, ?_⟩
  · obtain ⟨p, rfl⟩ : ∃ p, q = e p := ⟨e.symm q, (e.apply_symm_apply q).symm⟩
    simp only [List.mem_map]
    constructor
    · rintro ⟨p', hp', hpe⟩
      have hpp : p' = p := EmbeddingLike.injective e hpe
      rw [hpp] at hp'
      exact (usedU_equiv e d p).mp ((hmem p).mp hp')
    · exact fun hq => ⟨p, (hmem p).mpr ((usedU_equiv e d p).mpr hq), rfl⟩
  · exact forall₂_map_map e e (fun a b hab => (uAt_equiv e d a b).mp hab) hall

/-- The bottom word of a domino transports along an isomorphism. -/
theorem isWordV_map {d : A} {w : List A} (h : Lax624099.PostCorrespondence.Pcp.IsWordV d w) : Lax624099.PostCorrespondence.Pcp.IsWordV (e d) (w.map e) := by
  obtain ⟨ps, hsort, hmem, hall⟩ := h
  refine ⟨ps.map e, pairwise_map_of e (fun a b hab => (ordLt_equiv e a b).mp hab) hsort,
    fun q => ?_, ?_⟩
  · obtain ⟨p, rfl⟩ : ∃ p, q = e p := ⟨e.symm q, (e.apply_symm_apply q).symm⟩
    simp only [List.mem_map]
    constructor
    · rintro ⟨p', hp', hpe⟩
      have hpp : p' = p := EmbeddingLike.injective e hpe
      rw [hpp] at hp'
      exact (usedV_equiv e d p).mp ((hmem p).mp hp')
    · exact fun hq => ⟨p, (hmem p).mpr ((usedV_equiv e d p).mpr hq), rfl⟩
  · exact forall₂_map_map e e (fun a b hab => (vAt_equiv e d a b).mp hab) hall

/-- The problem transports along an isomorphism (one direction; the converse
is this statement at `e.symm`). -/
theorem pcpOn_map (e : A ≃[Lax624099.PostCorrespondence.pcp] B) (h : Lax624099.PostCorrespondence.Pcp.PcpOn A) : Lax624099.PostCorrespondence.Pcp.PcpOn B := by
  obtain ⟨hwf, l, us, vs, hne, hdom, hu, hv, hflat⟩ := h
  refine ⟨isWF_map e hwf, l.map e, us.map (List.map e), vs.map (List.map e), ?_, ?_,
    forall₂_map_map e (List.map e) (fun _ _ hab => isWordU_map e hab) hu,
    forall₂_map_map e (List.map e) (fun _ _ hab => isWordV_map e hab) hv, ?_⟩
  · intro hcon
    exact hne (by simpa using hcon)
  · intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
    exact (domG_equiv e d').mp (hdom d' hd')
  · rw [← List.map_flatten, ← List.map_flatten, hflat]

end IsoWords

end Pcp

open Pcp in
/-- **PCP**: Post's correspondence problem – has this list of domino pairs a
match? ([Post 1946][post1946variant]) The second problem of the catalog whose
certificate is unbounded in the instance, and the first whose certificate is a
*sequence* rather than a structure. -/
def PCP : Lax904597.Problems.DecisionProblem Lax624099.PostCorrespondence.pcp where
  Holds A _ := Lax624099.PostCorrespondence.Pcp.PcpOn A
  iso_invariant e := ⟨pcpOn_map e, pcpOn_map e.symm⟩

end Lax624099Proofs.DescriptiveComplexity


