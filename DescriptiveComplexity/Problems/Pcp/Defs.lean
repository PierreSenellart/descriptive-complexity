/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.List.Forall2
import DescriptiveComplexity.Interpretation

/-!
# PCP: Post's correspondence problem

*Given a list of pairs of words, is there a nonempty sequence of them whose
top words and whose bottom words have the same concatenation?*
([Post 1946][post1946variant]) This file carries the instance encoding – a
list of domino pairs, presented as a finite structure – and its semantics;
membership in RE lives in the sibling files.

## The encoding

The elements of an instance play three roles at once – dominoes, letters, and
positions inside a word – and, as in `DescriptiveComplexity.FINSAT`, nothing
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

`DescriptiveComplexity.DecisionProblem.Holds` is a predicate on *every* type,
finite or not, so the word of a domino may not be defined by sorting a
`Finset` of the universe. Instead the enumeration of the positions is an
existential: `DescriptiveComplexity.Pcp.IsWordU d w` says that some strictly
increasing list enumerates exactly the positions used by the top word of `d`
and that `w` carries the letters at them. Such a list is unique when it exists
(two sorted duplicate-free lists with the same members are equal), so
`IsWordU d` holds of at most one list, and it holds of one as soon as the used
positions are finite. The problem is then exactly Post's
(`DescriptiveComplexity.Pcp.PcpOn`): a nonempty sequence of marked dominoes
whose top words and bottom words have the same concatenation.

## What is and is not claimed

RE is the logically defined class of
`DescriptiveComplexity.RecursivelyEnumerable` (definability in `∃SO[new]`), so
membership of PCP in it is a statement about that logic. RE-*hardness* is the
computation-history dominoes from the halting problem
(`DescriptiveComplexity.halt_ordered_fo_reduction_pcp`, in
`DescriptiveComplexity.Problems.Pcp.Hardness`) – a machine construction of
necessity, since unlike `DescriptiveComplexity.FINSAT`, PCP is not the
syntactic image of any logic. Together the two halves make PCP RE-complete
and Post's problem undecidable (`DescriptiveComplexity.pcp_RE_complete`,
`DescriptiveComplexity.pcp_not_computable`, in
`DescriptiveComplexity.Computability.PcpComplete`).
-/

/- The language of encoded domino lists lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.sat` and
`Language.finsat`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of Post correspondence systems. -/
inductive pcpRel : ℕ → Type
  /-- `le x y`: the order of the positions. -/
  | le : pcpRel 2
  /-- `dom d`: the element `d` is one of the dominoes. -/
  | dom : pcpRel 1
  /-- `uAt d p c`: the top word of the domino `d` has the letter `c` at the
  position `p`. -/
  | uAt : pcpRel 3
  /-- `vAt d p c`: the bottom word of the domino `d` has the letter `c` at the
  position `p`. -/
  | vAt : pcpRel 3
  deriving DecidableEq

/-- The relational vocabulary of Post correspondence systems: marked dominoes
carrying two words each, over a universe ordered by the order of the positions
of those words. -/
protected def pcp : Language :=
  ⟨fun _ => Empty, pcpRel⟩

instance : IsRelational Language.pcp :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The order symbol of the positions. -/
abbrev pcpLeSym : Language.pcp.Relations 2 := .le

/-- The symbol marking the dominoes. -/
abbrev pcpDomSym : Language.pcp.Relations 1 := .dom

/-- The symbol giving the letters of the top words. -/
abbrev pcpUSym : Language.pcp.Relations 3 := .uAt

/-- The symbol giving the letters of the bottom words. -/
abbrev pcpVSym : Language.pcp.Relations 3 := .vAt

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Pcp

/-! ### Reading the encoding -/

section Reading

variable {A : Type} [Language.pcp.Structure A]

/-- `x` precedes `y` in the order of the positions. -/
def Ord (x y : A) : Prop := RelMap Language.pcpLeSym ![x, y]

/-- `x` strictly precedes `y` in the order of the positions. -/
def OrdLt (x y : A) : Prop := Ord x y ∧ x ≠ y

/-- The element `d` is one of the dominoes. -/
def DomG (d : A) : Prop := RelMap Language.pcpDomSym ![d]

/-- The top word of the domino `d` has the letter `c` at the position `p`. -/
def UAt (d p c : A) : Prop := RelMap Language.pcpUSym ![d, p, c]

/-- The bottom word of the domino `d` has the letter `c` at the position
`p`. -/
def VAt (d p c : A) : Prop := RelMap Language.pcpVSym ![d, p, c]

/-- The position `p` carries a letter of the top word of the domino `d`. -/
def UsedU (d p : A) : Prop := ∃ c, UAt d p c

/-- The position `p` carries a letter of the bottom word of the domino `d`. -/
def UsedV (d p : A) : Prop := ∃ c, VAt d p c

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

/-- **Well-formedness of a Post correspondence system**: the order symbol is a
linear order, and each domino carries at most one letter at each position of
each of its two words. -/
structure IsWF (A : Type) [Language.pcp.Structure A] : Prop where
  /-- The order of the positions is reflexive. -/
  ord_refl : ∀ x : A, Ord x x
  /-- The order of the positions is transitive. -/
  ord_trans : ∀ x y z : A, Ord x y → Ord y z → Ord x z
  /-- The order of the positions is antisymmetric. -/
  ord_antisymm : ∀ x y : A, Ord x y → Ord y x → x = y
  /-- The order of the positions is total. -/
  ord_total : ∀ x y : A, Ord x y ∨ Ord y x
  /-- A top word has at most one letter at each position. -/
  uAt_fun : ∀ d p c c' : A, UAt d p c → UAt d p c' → c = c'
  /-- A bottom word has at most one letter at each position. -/
  vAt_fun : ∀ d p c c' : A, VAt d p c → VAt d p c' → c = c'

/-! ### The words of a domino

The word of a domino is the sequence of its letters, read in the order of the
positions carrying them. The enumeration of those positions is an existential
rather than a construction, so that the definition needs no finiteness of the
universe: a strictly increasing list whose members are exactly the used
positions, together with the letters at them. -/

section Words

variable {A : Type} [Language.pcp.Structure A]

/-- **The top word of the domino `d` is `w`**: some strictly increasing list
enumerates exactly the positions used by the top word of `d`, and `w` carries
the letters at them. -/
def IsWordU (d : A) (w : List A) : Prop :=
  ∃ ps : List A, ps.Pairwise OrdLt ∧ (∀ p, p ∈ ps ↔ UsedU d p) ∧ List.Forall₂ (UAt d) ps w

/-- **The bottom word of the domino `d` is `w`**, as in
`DescriptiveComplexity.Pcp.IsWordU`. -/
def IsWordV (d : A) (w : List A) : Prop :=
  ∃ ps : List A, ps.Pairwise OrdLt ∧ (∀ p, p ∈ ps ↔ UsedV d p) ∧ List.Forall₂ (VAt d) ps w

end Words

/-! ### The problem -/

/-- **The system has a match**: the instance is well-formed and there is a
nonempty sequence of dominoes whose top words and whose bottom words have the
same concatenation. -/
def PcpOn (A : Type) [Language.pcp.Structure A] : Prop :=
  IsWF A ∧ ∃ (l : List A) (us vs : List (List A)),
    l ≠ [] ∧ (∀ d ∈ l, DomG d) ∧
      List.Forall₂ IsWordU l us ∧ List.Forall₂ IsWordV l vs ∧ us.flatten = vs.flatten

/-! ### Isomorphism-invariance

Everything the semantics reads is a relation of the instance, so an
isomorphism transports it: the sequence of dominoes and the two lists of words
are carried over by `List.map`, and the enumerations of the positions with
them. Only one direction is proved; the converse is the same statement at the
inverse isomorphism. -/

section Iso

variable {A B : Type} [Language.pcp.Structure A] [Language.pcp.Structure B]
variable (e : A ≃[Language.pcp] B)

theorem ord_equiv (x y : A) : Ord x y ↔ Ord (e x) (e y) := relMap_equiv₂ e _ x y

theorem ordLt_equiv (x y : A) : OrdLt x y ↔ OrdLt (e x) (e y) :=
  and_congr (ord_equiv e x y)
    (not_congr ⟨fun h => h ▸ rfl, fun h => EmbeddingLike.injective e h⟩)

theorem domG_equiv (d : A) : DomG d ↔ DomG (e d) := relMap_equiv₁ e _ d

theorem uAt_equiv (d p c : A) : UAt d p c ↔ UAt (e d) (e p) (e c) := relMap_equiv₃ e _ d p c

theorem vAt_equiv (d p c : A) : VAt d p c ↔ VAt (e d) (e p) (e c) := relMap_equiv₃ e _ d p c

theorem usedU_equiv (d p : A) : UsedU d p ↔ UsedU (e d) (e p) := by
  refine ⟨fun ⟨c, hc⟩ => ⟨e c, (uAt_equiv e d p c).mp hc⟩, fun ⟨c, hc⟩ => ⟨e.symm c, ?_⟩⟩
  refine (uAt_equiv e d p (e.symm c)).mpr ?_
  rwa [e.apply_symm_apply]

theorem usedV_equiv (d p : A) : UsedV d p ↔ UsedV (e d) (e p) := by
  refine ⟨fun ⟨c, hc⟩ => ⟨e c, (vAt_equiv e d p c).mp hc⟩, fun ⟨c, hc⟩ => ⟨e.symm c, ?_⟩⟩
  refine (vAt_equiv e d p (e.symm c)).mpr ?_
  rwa [e.apply_symm_apply]

/-! The same transports read backwards, at the inverse isomorphism: the shape
every field of `DescriptiveComplexity.Pcp.isWF_map` needs. -/

theorem ord_equiv' (x y : B) : Ord x y ↔ Ord (e.symm x) (e.symm y) := by
  have h := (ord_equiv e (e.symm x) (e.symm y)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem uAt_equiv' (d p c : B) : UAt d p c ↔ UAt (e.symm d) (e.symm p) (e.symm c) := by
  have h := (uAt_equiv e (e.symm d) (e.symm p) (e.symm c)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h

theorem vAt_equiv' (d p c : B) : VAt d p c ↔ VAt (e.symm d) (e.symm p) (e.symm c) := by
  have h := (vAt_equiv e (e.symm d) (e.symm p) (e.symm c)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h

private theorem eq_of_symm_eq {x y : B} (h : e.symm x = e.symm y) : x = y := by
  have h' := congrArg e h
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h'

/-- Well-formedness transports along an isomorphism. -/
theorem isWF_map (e : A ≃[Language.pcp] B) (h : IsWF A) : IsWF B where
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

variable {A B : Type} [Language.pcp.Structure A] [Language.pcp.Structure B]
variable (e : A ≃[Language.pcp] B)

/-- The top word of a domino transports along an isomorphism. -/
theorem isWordU_map {d : A} {w : List A} (h : IsWordU d w) : IsWordU (e d) (w.map e) := by
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
theorem isWordV_map {d : A} {w : List A} (h : IsWordV d w) : IsWordV (e d) (w.map e) := by
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
theorem pcpOn_map (e : A ≃[Language.pcp] B) (h : PcpOn A) : PcpOn B := by
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
def PCP : DecisionProblem Language.pcp where
  Holds A _ := PcpOn A
  iso_invariant e := ⟨pcpOn_map e, pcpOn_map e.symm⟩

end DescriptiveComplexity
