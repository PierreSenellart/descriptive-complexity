/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Pcp.Defs
import DescriptiveComplexity.Problems.Pcp.Enum

/-!
# A match, read off as a finite certificate

The mathematical content of `DescriptiveComplexity.PCP ∈ RE`: a Post system
has a match exactly when a **finite** amount of data witnesses it, and that
data is a handful of relations over the instance extended by a segment of
invented *slots* – the places of the sequence of dominoes.

## The shape of the certificate

`DescriptiveComplexity.Pcp.Cert` is the data:

* `SLe` – a linear order on the slots, so that they are a *sequence*;
* `Dm` – the domino sitting at each slot;
* `Mt` – the **matching between the two parses**.

The common word is not invented, and no length or position of it is ever
named. The top concatenation is cut into blocks by the slots, so its letters
are indexed by the pairs (slot, position of the top word of the domino there),
in lexicographic order (`DescriptiveComplexity.Pcp.parseIx`); the bottom
concatenation is indexed the same way by its own parse. `Mt s p s' p'` says
that the letter at the top index `(s, p)` is the *same occurrence* as the
letter at the bottom index `(s', p')`.

## Why a matching is as good as an equality

Equality of the two concatenations is not first-order in the instance: it
compares two words of unbounded length. A matching is a relation variable, and
what a kernel can ask of it is local: that it lands in the two parses, that it
is defined everywhere on both, that it reflects the two lexicographic orders,
and that matched indices carry the same letter. That is already enough
(`DescriptiveComplexity.Pcp.forall₂_of_matching`): a relation between the
members of two strictly sorted lists that is total on both sides and reflects
the order pairs their entries index by index, so the two concatenations agree
letter by letter. Functionality and injectivity of the matching are *not*
asked: they follow.

The two directions of `DescriptiveComplexity.Pcp.pcpOn_iff_cert` are therefore
not symmetric in effort. A match hands its matching back for free – the two
parses have the same length, so pairing them index by index
(`DescriptiveComplexity.Pcp.IdxMatch`) does it – while a certificate has to
rebuild the two words from their enumerations before the matching lemma
applies.
-/

namespace DescriptiveComplexity

namespace Pcp

open FirstOrder

open Language Structure

/-! ### The certificate -/

/-- **A match of a Post correspondence system, as relations on a segment of
invented slots.** `SLe` orders the slots; `Dm s d` says the domino `d` sits at
the slot `s`; `Mt s p s' p'` matches the position `p` of the top word at the
slot `s` with the position `p'` of the bottom word at the slot `s'`, as
occurrences of the same letter of the common word. -/
structure Cert (A D : Type) where
  /-- The order of the slots. -/
  SLe : D → D → Prop
  /-- `Dm s d`: the domino `d` sits at the slot `s`. -/
  Dm : D → A → Prop
  /-- `Mt s p s' p'`: the top index `(s, p)` and the bottom index `(s', p')`
  are the same occurrence of the common word. -/
  Mt : D → A → D → A → Prop

namespace Cert

variable {A D : Type} [Language.pcp.Structure A] (c : Cert A D)

/-- Strictly earlier, in the order of the slots. -/
def SLt (s t : D) : Prop := c.SLe s t ∧ s ≠ t

/-- `p` is a position of the top word of the domino sitting at the slot `s`. -/
def TopIx (s : D) (p : A) : Prop := ∃ d, c.Dm s d ∧ UsedU d p

/-- `p` is a position of the bottom word of the domino sitting at the slot
`s`. -/
def BotIx (s : D) (p : A) : Prop := ∃ d, c.Dm s d ∧ UsedV d p

/-- The lexicographic order on the indices of a parse: first the slot, then the
position inside the word sitting there. Both parses are ordered by it, which is
why one matching relates them. -/
def LexLt (s : D) (p : A) (t : D) (q : A) : Prop := c.SLt s t ∨ (s = t ∧ OrdLt p q)

end Cert

/-- **The conditions on a certificate.** The instance is well-formed, the slots
are a nonempty sequence carrying one domino each, and the matching is a
letter-preserving order isomorphism between the two parses – stated as being
inside them, defined everywhere on both, order-reflecting, and
letter-preserving. -/
structure CertOK {A D : Type} [Language.pcp.Structure A] (c : Cert A D) : Prop where
  /-- The instance is well-formed. -/
  wf : IsWF A
  /-- The slots are linearly ordered. -/
  sle_lin : IsLinOrd c.SLe
  /-- There is at least one slot: a match is a *nonempty* sequence. -/
  slot_ex : ∃ s : D, c.SLe s s
  /-- Every slot carries a domino. -/
  dm_tot : ∀ s : D, ∃ d, c.Dm s d
  /-- A slot carries only one domino. -/
  dm_fun : ∀ (s : D) (d d' : A), c.Dm s d → c.Dm s d' → d = d'
  /-- What a slot carries is a domino of the instance. -/
  dm_dom : ∀ (s : D) (d : A), c.Dm s d → DomG d
  /-- The matching relates an index of the top parse to one of the bottom
  parse. -/
  mt_ix : ∀ (s : D) (p : A) (s' : D) (p' : A), c.Mt s p s' p' → c.TopIx s p ∧ c.BotIx s' p'
  /-- Every index of the top parse is matched. -/
  mt_left : ∀ (s : D) (p : A), c.TopIx s p → ∃ s' p', c.Mt s p s' p'
  /-- Every index of the bottom parse is matched. -/
  mt_right : ∀ (s' : D) (p' : A), c.BotIx s' p' → ∃ s p, c.Mt s p s' p'
  /-- The matching reflects the lexicographic order of the two parses. -/
  mt_mono : ∀ (s : D) (p : A) (s' : D) (p' : A) (t : D) (q : A) (t' : D) (q' : A),
    c.Mt s p s' p' → c.Mt t q t' q' → (c.LexLt s p t q ↔ c.LexLt s' p' t' q')
  /-- Matched indices carry the same letter. -/
  mt_lab : ∀ (s : D) (p : A) (s' : D) (p' : A) (d d' ℓ : A),
    c.Mt s p s' p' → c.Dm s d → c.Dm s' d' → (UAt d p ℓ ↔ VAt d' p' ℓ)

/-! ### The order of the positions -/

section Order

variable {A : Type} [Language.pcp.Structure A]

/-- The order symbol of a well-formed instance is a linear order. -/
theorem isLinOrd_ord (h : IsWF A) : IsLinOrd (Ord (A := A)) :=
  ⟨h.ord_refl, h.ord_trans, h.ord_antisymm, h.ord_total⟩

/-- Strict precedence of positions is asymmetric. -/
theorem asymm_ordLt (h : IsWF A) (a b : A) (hab : OrdLt a b) (hba : OrdLt b a) : False :=
  asymm_strict (isLinOrd_ord h) a b hab hba

end Order

/-! ### From a certificate to a match -/

section Sound

variable {A D : Type} [Language.pcp.Structure A] [Finite A] [Finite D] {c : Cert A D}

/-- **A certificate exhibits a match.** The slots are enumerated in their
order, the positions of each word in theirs, and the matching lemma turns the
guessed relation into the equality of the two concatenations. -/
theorem pcpOn_of_cert (h : CertOK c) : PcpOn A := by
  classical
  choose dm hdm using h.dm_tot
  obtain ⟨slots, hslotsp, hslotsm⟩ := exists_isEnum h.sle_lin fun _ : D => True
  have hmem : ∀ s : D, s ∈ slots := fun s => (hslotsm s).mpr trivial
  have hord := isLinOrd_ord h.wf
  choose psU hpsUp hpsUm using fun s : D => exists_isEnum hord (UsedU (dm s))
  choose psV hpsVp hpsVm using fun s : D => exists_isEnum hord (UsedV (dm s))
  choose wU hwU using fun s : D =>
    exists_forall₂ (R := UAt (dm s)) fun p hp => (hpsUm s p).mp hp
  choose wV hwV using fun s : D =>
    exists_forall₂ (R := VAt (dm s)) fun p hp => (hpsVm s p).mp hp
  -- the two parses, indexed lexicographically
  have hasym : ∀ x y : D × A, LexOf c.SLt OrdLt x y → LexOf c.SLt OrdLt y x → False :=
    asymm_lexOf (asymm_strict h.sle_lin) (asymm_ordLt h.wf)
  have hpU : (parseIx slots psU).Pairwise (LexOf c.SLt OrdLt) :=
    pairwise_parseIx hslotsp hpsUp
  have hpV : (parseIx slots psV).Pairwise (LexOf c.SLt OrdLt) :=
    pairwise_parseIx hslotsp hpsVp
  have hfU : List.Forall₂ (fun x ℓ => UAt (dm x.1) x.2 ℓ) (parseIx slots psU)
      (slots.flatMap wU) := forall₂_parseIx fun s _ => hwU s
  have hfV : List.Forall₂ (fun x ℓ => VAt (dm x.1) x.2 ℓ) (parseIx slots psV)
      (slots.flatMap wV) := forall₂_parseIx fun s _ => hwV s
  -- the matching pairs the two parses entry by entry
  have hM : List.Forall₂ (fun x y : D × A => c.Mt x.1 x.2 y.1 y.2)
      (parseIx slots psU) (parseIx slots psV) := by
    refine forall₂_of_matching hasym hasym hpU hpV ?_ ?_ ?_
      fun x y x' y' hxy hxy' => h.mt_mono _ _ _ _ _ _ _ _ hxy hxy'
    · rintro ⟨s, p⟩ ⟨s', p'⟩ hmt
      obtain ⟨⟨d, hd, hu⟩, ⟨d', hd', hv⟩⟩ := h.mt_ix s p s' p' hmt
      rw [h.dm_fun s d (dm s) hd (hdm s)] at hu
      rw [h.dm_fun s' d' (dm s') hd' (hdm s')] at hv
      exact ⟨mem_parseIx.mpr ⟨hmem s, (hpsUm s p).mpr hu⟩,
        mem_parseIx.mpr ⟨hmem s', (hpsVm s' p').mpr hv⟩⟩
    · rintro ⟨s, p⟩ hx
      obtain ⟨s', p', hmt⟩ := h.mt_left s p ⟨dm s, hdm s, (hpsUm s p).mp (mem_parseIx.mp hx).2⟩
      exact ⟨(s', p'), hmt⟩
    · rintro ⟨s', p'⟩ hy
      obtain ⟨s, p, hmt⟩ :=
        h.mt_right s' p' ⟨dm s', hdm s', (hpsVm s' p').mp (mem_parseIx.mp hy).2⟩
      exact ⟨(s, p), hmt⟩
  refine ⟨h.wf, slots.map dm, slots.map wU, slots.map wV, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, -⟩ := h.slot_ex
    exact fun hc => absurd (List.map_eq_nil_iff.mp hc ▸ hmem s) List.not_mem_nil
  · rintro d hd
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hd
    exact h.dm_dom s (dm s) (hdm s)
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact fun s _ => ⟨psU s, hpsUp s, hpsUm s, hwU s⟩
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact fun s _ => ⟨psV s, hpsVp s, hpsVm s, hwV s⟩
  · rw [← List.flatMap_def, ← List.flatMap_def]
    refine eq_of_forall₂ ?_ hM hfU hfV
    rintro ⟨s, p⟩ ⟨s', p'⟩ ℓ ℓ' hmt hu hv
    exact h.wf.vAt_fun _ _ _ _
      ((h.mt_lab s p s' p' (dm s) (dm s') ℓ hmt (hdm s) (hdm s')).mp hu) hv

end Sound

/-! ### From a match to a certificate -/

section Complete

variable {A : Type} [Language.pcp.Structure A]

/-- **A match is a certificate.** The slots are the places of the sequence of
dominoes, and the matching is the pairing of the two parses index by index,
which is legitimate exactly because the two concatenations are the same
word. -/
theorem cert_of_pcpOn (h : PcpOn A) : ∃ (n : ℕ) (c : Cert A (Fin n)), CertOK c := by
  classical
  obtain ⟨hwf, l, us, vs, hne, hdom, hu, hv, hflat⟩ := h
  obtain ⟨uw, huwmap, huw⟩ := exists_fun_of_forall₂ hu
  obtain ⟨vw, hvwmap, hvw⟩ := exists_fun_of_forall₂ hv
  choose psU hpsUp hpsUm hpsUw using huw
  choose psV hpsVp hpsVm hpsVw using hvw
  set slots := List.finRange l.length with hslots
  set TU := parseIx slots psU with hTU
  set TV := parseIx slots psV with hTV
  have hfU : List.Forall₂ (fun x ℓ => UAt (l.get x.1) x.2 ℓ) TU (slots.flatMap uw) :=
    forall₂_parseIx fun i _ => hpsUw i
  have hUV : slots.flatMap vw = slots.flatMap uw := by
    rw [List.flatMap_def, List.flatMap_def, huwmap, hvwmap, hflat]
  have hfV : List.Forall₂ (fun x ℓ => VAt (l.get x.1) x.2 ℓ) TV (slots.flatMap uw) := by
    rw [← hUV]
    exact forall₂_parseIx fun i _ => hpsVw i
  have hlen : TU.length = TV.length := by rw [hfU.length_eq, hfV.length_eq]
  -- the slots are ordered as the indices of the sequence
  have hslotsp : slots.Pairwise fun s t : Fin l.length => s ≤ t ∧ s ≠ t :=
    (List.pairwise_lt_finRange _).imp fun h => ⟨le_of_lt h, ne_of_lt h⟩
  have hasym : ∀ x y : Fin l.length × A,
      LexOf (fun s t : Fin l.length => s ≤ t ∧ s ≠ t) OrdLt x y →
      LexOf (fun s t : Fin l.length => s ≤ t ∧ s ≠ t) OrdLt y x → False :=
    asymm_lexOf (asymm_strict isLinOrd_le) (asymm_ordLt hwf)
  have hpU : TU.Pairwise (LexOf (fun s t : Fin l.length => s ≤ t ∧ s ≠ t) OrdLt) :=
    pairwise_parseIx hslotsp hpsUp
  have hpV : TV.Pairwise (LexOf (fun s t : Fin l.length => s ≤ t ∧ s ≠ t) OrdLt) :=
    pairwise_parseIx hslotsp hpsVp
  refine ⟨l.length, ⟨fun s t => s ≤ t, fun s d => d = l.get s,
    fun s p s' p' => IdxMatch TU TV (s, p) (s', p')⟩, ?_⟩
  refine ⟨hwf, isLinOrd_le, ⟨⟨0, List.length_pos_of_ne_nil hne⟩, le_refl _⟩,
    fun s => ⟨l.get s, rfl⟩, fun _ d d' hd hd' => hd.trans hd'.symm, ?_, ?_, ?_, ?_,
    fun s p s' p' t q t' q' => idxMatch_mono hasym hasym hpU hpV, ?_⟩
  · rintro s d rfl
    exact hdom _ (List.get_mem l s)
  · intro s p s' p' hmt
    obtain ⟨hx, hy⟩ := idxMatch_mem hmt
    exact ⟨⟨l.get s, rfl, (hpsUm s p).mp (mem_parseIx.mp hx).2⟩,
      ⟨l.get s', rfl, (hpsVm s' p').mp (mem_parseIx.mp hy).2⟩⟩
  · rintro s p ⟨d, rfl, hup⟩
    obtain ⟨⟨s', p'⟩, hmt⟩ :=
      idxMatch_left hlen (mem_parseIx (x := (s, p)).mpr ⟨List.mem_finRange s, (hpsUm s p).mpr hup⟩)
    exact ⟨s', p', hmt⟩
  · rintro s' p' ⟨d, rfl, hvp⟩
    obtain ⟨⟨s, p⟩, hmt⟩ :=
      idxMatch_right hlen
        (mem_parseIx (x := (s', p')).mpr ⟨List.mem_finRange s', (hpsVm s' p').mpr hvp⟩)
    exact ⟨s, p, hmt⟩
  · rintro s p s' p' d d' ℓ ⟨i, hi₁, hi₂, hxe, hye⟩ rfl rfl
    have hU := forall₂_getElem hfU hi₁ (hfU.length_eq ▸ hi₁)
    have hV := forall₂_getElem hfV hi₂ (hfV.length_eq ▸ hi₂)
    rw [hxe] at hU
    rw [hye] at hV
    refine ⟨fun hℓ => ?_, fun hℓ => ?_⟩
    · rwa [hwf.uAt_fun _ _ _ _ hℓ hU]
    · rwa [hwf.vAt_fun _ _ _ _ hℓ hV]

end Complete

/-- **A Post system has a match exactly when a finite certificate says so.**
The certificate invents a segment of slots and nothing else: the common word,
whose length no function of the instance bounds, is never written down – only
the matching between the two ways of cutting it into blocks is. -/
theorem pcpOn_iff_cert (A : Type) [Language.pcp.Structure A] [Finite A] :
    PcpOn A ↔ ∃ (n : ℕ) (c : Cert A (Fin n)), CertOK c :=
  ⟨cert_of_pcpOn, fun ⟨_, _, h⟩ => pcpOn_of_cert h⟩

end Pcp

end DescriptiveComplexity
