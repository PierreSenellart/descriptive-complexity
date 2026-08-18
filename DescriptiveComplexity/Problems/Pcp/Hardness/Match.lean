/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Pcp.Hardness.Draw
import DescriptiveComplexity.Problems.Pcp.Cert

/-!
# The drawn instance has a match exactly when the machine accepts

The combinatorial half of the correctness of the reduction from
`DescriptiveComplexity.HALT` to `DescriptiveComplexity.PCP`, over any
`Language.pcp`-structure whose four relations read as the semantic predicates
of `DescriptiveComplexity.Problems.Pcp.Hardness.Draw`
(`DescriptiveComplexity.HaltPcp.Reads`) – which is exactly what the
interpretation of the sibling `Interp` file provides.

## Words by tables

Everything a word of the drawn instance says is of the form “the pair
(position, letter) is an entry of a zipped table”, with the position side
strictly increasing. Two abstract lemmas turn such a table into the *unique*
word of a domino (`DescriptiveComplexity.HaltPcp.isWord_of_zip`,
`DescriptiveComplexity.HaltPcp.eq_of_isWord_zip`): the enumeration of the used
positions is pinned by sortedness, and the letters by functionality of the
zip. The short words instantiate them at the shared position prefix; the start
domino's bottom word at its own layout, whose table
`DescriptiveComplexity.HaltPcp.startBotAt_iff_zip` is proved by walking the
input page along the enumeration of the positions.

## The two directions

A match of `DescriptiveComplexity.Pcp.History` maps to a solution of the
instance by encoding each abstract domino
(`DescriptiveComplexity.HaltPcp.exists_encode`) and reading the tables
forward; a solution maps back by decoding each marked element
(`DescriptiveComplexity.HaltPcp.decodeDom`) and using uniqueness of the words,
injectivity of the letter map turning the equality of the two concatenations
back into the equality of the abstract words. Chained with
`DescriptiveComplexity.HaltPcp.acceptsU_iff_hasMatch`, this gives the
correctness statement `DescriptiveComplexity.HaltPcp.pcpOn_iff_of_reads` the
`Interp` file consumes.
-/

namespace DescriptiveComplexity

namespace HaltPcp

open FirstOrder

open Language Structure

/-! ### Sorted lists, zips and tables -/

section Generic

variable {α β : Type}

/-- Two strictly sorted lists with the same members are equal. -/
theorem sorted_eq {Lt : α → α → Prop} (hasym : ∀ a b, Lt a b → Lt b a → False) :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise Lt → l₂.Pairwise Lt →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: l₂, _, _, hm => absurd ((hm b).mpr List.mem_cons_self) (by simp)
  | a :: l₁, [], _, _, hm => absurd ((hm a).mp List.mem_cons_self) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, hm => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      rcases List.mem_cons.mp ((hm a).mp List.mem_cons_self) with h | h
      · exact h
      · rcases List.mem_cons.mp ((hm b).mpr List.mem_cons_self) with h' | h'
        · exact h'.symm
        · exact absurd (h₁.1 b h') fun hc => hasym _ _ hc (h₂.1 a h)
    subst hab
    have hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂ := by
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_of_mem a hx)) with rfl | hx'
        · exact absurd (h₁.1 x hx) (Pcp.irrefl_of_asymm hasym x)
        · exact hx'
      · intro hx
        rcases List.mem_cons.mp ((hm x).mpr (List.mem_cons_of_mem a hx)) with rfl | hx'
        · exact absurd (h₂.1 x hx) (Pcp.irrefl_of_asymm hasym x)
        · exact hx'
    rw [sorted_eq hasym h₁.2 h₂.2 hmem]

/-- The entries of a zip of two lists of equal length, by index. -/
theorem mem_zip_iff {l : List α} {w : List β} (hlen : l.length = w.length) {p : α} {c : β} :
    (p, c) ∈ l.zip w ↔
      ∃ (i : ℕ) (h : i < l.length), l[i] = p ∧ w[i]'(hlen ▸ h) = c := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hget⟩
    rw [List.length_zip, hlen, min_self] at hi
    refine ⟨i, hlen ▸ hi, ?_, ?_⟩
    · exact congrArg Prod.fst (List.getElem_zip.symm.trans hget)
    · exact congrArg Prod.snd (List.getElem_zip.symm.trans hget)
  · rintro ⟨i, hi, hp, hc⟩
    refine ⟨i, ?_, ?_⟩
    · rw [List.length_zip, hlen, min_self]
      exact hlen ▸ hi
    · rw [List.getElem_zip, hp, hc]

/-- With a duplicate-free position side, a zip is functional. -/
theorem zip_fun {l : List α} {w : List β} (hlen : l.length = w.length) (hnd : l.Nodup)
    {p : α} {c c' : β} (h : (p, c) ∈ l.zip w) (h' : (p, c') ∈ l.zip w) : c = c' := by
  obtain ⟨i, hi, hpi, hci⟩ := (mem_zip_iff hlen).mp h
  obtain ⟨j, hj, hpj, hcj⟩ := (mem_zip_iff hlen).mp h'
  obtain rfl : i = j :=
    (hnd.getElem_inj_iff (hi := hi) (hj := hj)).mp (hpi.trans hpj.symm)
  rw [← hci, ← hcj]

/-- A position of the table carries a letter exactly when it is on the
position side. -/
theorem exists_mem_zip {l : List α} {w : List β} (hlen : l.length = w.length) {p : α} :
    (∃ c, (p, c) ∈ l.zip w) ↔ p ∈ l := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨i, hi, rfl, -⟩ := (mem_zip_iff hlen).mp hc
    exact List.getElem_mem hi
  · intro hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    exact ⟨w[i]'(hlen ▸ hi), (mem_zip_iff hlen).mpr ⟨i, hi, rfl, rfl⟩⟩

/-- A zip relates its two sides entry by entry. -/
theorem forall₂_zip_self :
    ∀ {l : List α} {w : List β}, l.length = w.length →
      List.Forall₂ (fun p c => (p, c) ∈ l.zip w) l w
  | [], [], _ => List.Forall₂.nil
  | p :: l, c :: w, hlen => by
    refine List.Forall₂.cons (by simp) ?_
    refine (forall₂_zip_self (by simpa using hlen)).imp ?_
    intro a b hab
    rw [List.zip_cons_cons]
    exact List.mem_cons_of_mem _ hab

/-- A functional `List.Forall₂` determines its right list. -/
theorem forall₂_unique {R : α → β → Prop} :
    ∀ {l : List α} {w w' : List β},
      (∀ a ∈ l, ∀ b b', R a b → R a b' → b = b') →
      List.Forall₂ R l w → List.Forall₂ R l w' → w = w'
  | [], _, _, _, h, h' => by
    rw [List.forall₂_nil_left_iff.mp h, List.forall₂_nil_left_iff.mp h']
  | a :: l, _, _, hfun, h, h' => by
    rcases h with - | ⟨hb, ht⟩
    rcases h' with - | ⟨hb', ht'⟩
    rw [hfun a List.mem_cons_self _ _ hb hb',
      forall₂_unique (fun x hx => hfun x (List.mem_cons_of_mem a hx)) ht ht']

end Generic

/-! ### Reading the instance -/

variable {A : Type} [Language.turing.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {B : Type} [Language.pcp.Structure B]

/-- **The four relations of the instance read as the drawn predicates**, along
an equivalence of the universes. This is what the defining formulas of the
interpretation are proved to realize. -/
structure Reads (e : B ≃ PV A) : Prop where
  /-- The order of the positions is the drawn order. -/
  ord : ∀ x y : B, Pcp.Ord x y ↔ PLe (e x) (e y)
  /-- The marked dominoes are the drawn dominoes. -/
  dom : ∀ x : B, Pcp.DomG x ↔ PDom (e x)
  /-- The top words read off the top tables. -/
  uAt : ∀ d p c : B, Pcp.UAt d p c ↔ PUAt (e d) (e p) (e c)
  /-- The bottom words read off the bottom tables. -/
  vAt : ∀ d p c : B, Pcp.VAt d p c ↔ PVAt (e d) (e p) (e c)

variable {e : B ≃ PV A}

theorem Reads.ordLt (h : Reads e) (x y : B) : Pcp.OrdLt x y ↔ PLt (e x) (e y) :=
  and_congr (h.ord x y) (not_congr ⟨congrArg e, fun hc => e.injective hc⟩)

/-! ### Tables are words

`DescriptiveComplexity.Pcp.IsWordU`/`IsWordV` both have the shape “some
strictly increasing enumeration of the used positions carries the word”; the
two lemmas below handle any letter relation given by a zipped table with a
strictly increasing position side. -/

section Word

variable {R : B → B → Prop} {P W : List (PV A)}

/-- **A table is a word**: the position side, transported, enumerates the
used positions in order and carries the letter side. -/
theorem isWord_of_zip (h : Reads e) (hlen : P.length = W.length)
    (hsort : P.Pairwise PLt) (htab : ∀ p c : B, R p c ↔ (e p, e c) ∈ P.zip W) :
    ∃ ps : List B, ps.Pairwise Pcp.OrdLt ∧ (∀ p, p ∈ ps ↔ ∃ c, R p c) ∧
      List.Forall₂ R ps (W.map e.symm) := by
  refine ⟨P.map e.symm, ?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    refine hsort.imp ?_
    intro x y hxy
    refine (h.ordLt _ _).mpr ?_
    simpa using hxy
  · intro p
    constructor
    · intro hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      have hx' : e (e.symm x) ∈ P := by simpa using hx
      obtain ⟨c', hc'⟩ := (exists_mem_zip hlen).mpr hx'
      exact ⟨e.symm c', (htab _ _).mpr (by simpa using hc')⟩
    · rintro ⟨c, hc⟩
      have := (exists_mem_zip hlen).mp ⟨e c, (htab p c).mp hc⟩
      exact List.mem_map.mpr ⟨e p, this, by simp⟩
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine (forall₂_zip_self hlen).imp ?_
    intro p c hpc
    refine (htab _ _).mpr ?_
    simpa using hpc

/-- **The word of a table is unique**: any word of the letter relation is the
letter side of the table. -/
theorem eq_of_isWord_zip (h : Reads e)
    (hasym : ∀ x y : B, Pcp.OrdLt x y → Pcp.OrdLt y x → False)
    (hlen : P.length = W.length) (hsort : P.Pairwise PLt)
    (htab : ∀ p c : B, R p c ↔ (e p, e c) ∈ P.zip W) {ps : List B} {w : List B}
    (hps : ps.Pairwise Pcp.OrdLt) (hmem : ∀ p, p ∈ ps ↔ ∃ c, R p c)
    (hf : List.Forall₂ R ps w) : w = W.map e.symm := by
  obtain ⟨ps₀, hs₀, hm₀, hf₀⟩ := isWord_of_zip h hlen hsort htab
  have hnd : P.Nodup := hsort.imp fun hxy => hxy.2
  have hfun : ∀ p ∈ ps, ∀ c c', R p c → R p c' → c = c' := by
    intro p _ c c' hc hc'
    have := zip_fun hlen hnd ((htab p c).mp hc) ((htab p c').mp hc')
    exact e.injective this
  have hps₀ : ps = ps₀ :=
    sorted_eq hasym hps hs₀ fun x => (hmem x).trans (hm₀ x).symm
  subst hps₀
  exact forall₂_unique hfun hf hf₀

end Word

/-! ### The tables of the dominoes -/

section Tags

/-- Every short word fits in the shared positions. -/
theorem uSpec_length_le : ∀ t : PTag, (uSpec t).length ≤ 8 := by decide

/-- Every short bottom word fits in the shared positions. -/
theorem vSpec_length_le : ∀ t : PTag, (vSpec t).length ≤ 8 := by decide

/-- Away from the start domino, the bottom relation is its table. -/
theorem pVAt_of_ne {d p c : PV A} (hne : d.1 ≠ PTag.dStart) :
    PVAt d p c ↔ (p, c) ∈ (posPrefix (vSpec d.1).length).zip (vWord d) := by
  obtain ⟨t, w⟩ := d
  cases t <;> first
    | exact absurd rfl hne
    | exact Iff.rfl

/-- At the start domino, the bottom relation is the page layout. -/
theorem pVAt_start {d p c : PV A} (hd : d.1 = PTag.dStart) :
    PVAt d p c ↔ StartBotAt p c := by
  obtain ⟨t, w⟩ := d
  cases hd
  exact Iff.rfl

omit [Language.turing.Structure A] in
/-- The lengths of the two sides of a short top table agree. -/
theorem length_posPrefix (n : ℕ) : (posPrefix (A := A) n).length = n := by
  simp [posPrefix]

end Tags

/-! ### The start domino's table -/

section StartTable

omit [Language.turing.Structure A] in
/-- The shared position prefix, spelt out. -/
theorem posPrefix_seven :
    posPrefix (A := A) 7 = [cstE .pos0, cstE .pos1, cstE .pos2, cstE .pos3,
      cstE .pos4, cstE .pos5, cstE .pos6] := by
  simp [posPrefix, List.range_succ, posE]

/-- The entries of the page block of the start table. -/
theorem mem_zip_page (hwf : (tmData A).WellFormed) {ps inp : List A}
    (hinp : List.Forall₂ (tmData A).InitTape ps inp) {p c : PV A} :
    (p, c) ∈ (pagePos ps).zip (pageBot inp) ↔
      ∃ q a, q ∈ ps ∧ (tmData A).InitTape q a ∧
        ((p = idxE .pairSym q ∧ c = idxE .ltSym a) ∨
          (p = idxE .pairStar q ∧ c = cstE .ltStar)) := by
  induction hinp with
  | nil => simp [pagePos, pageBot]
  | @cons q a ps' inp' hqa hf ih =>
    rw [pagePos, pageBot, List.flatMap_cons, List.flatMap_cons, ← pagePos, ← pageBot]
    rw [show ([idxE (A := A) .pairSym q, idxE .pairStar q] ++ pagePos ps') =
      idxE .pairSym q :: idxE .pairStar q :: pagePos ps' from rfl]
    rw [show ([idxE (A := A) .ltSym a, cstE .ltStar] ++ pageBot inp') =
      idxE .ltSym a :: cstE .ltStar :: pageBot inp' from rfl]
    rw [List.zip_cons_cons, List.zip_cons_cons]
    simp only [List.mem_cons, ih, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨q', a', hq', ha', hcase⟩)
      · exact ⟨q, a, by simp, hqa, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨q, a, by simp, hqa, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨q', a', by simp [hq'], ha', hcase⟩
    · rintro ⟨q', a', hq', ha', hcase⟩
      rcases hq' with rfl | hq''
      · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, by rw [TMData.initTape_functional hwf ha' hqa]⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨q', a', hq'', ha', hcase⟩)

/-- **The layout of the start domino's bottom word is its table**: the letter
relation of the start domino says exactly that the pair is an entry of the
zipped layout. -/
theorem startBotAt_iff_zip (hwf : (tmData A).WellFormed) {ps inp : List A}
    (hps : IsPosEnum (tmData A) ps) (hinp : List.Forall₂ (tmData A).InitTape ps inp)
    {p c : PV A} :
    StartBotAt p c ↔ (p, c) ∈ (startPos ps).zip (startBot inp) := by
  have hlen2 : (pagePos (A := A) ps).length = (pageBot (A := A) inp).length := by
    simp [hinp.length_eq]
  have hsplit : (startPos ps).zip (startBot inp) =
      ((posPrefix 7).zip [cstE .ltStar, cstE .ltTri, cstE .ltStar, cstE .ltLft,
        cstE .ltStar, cstE .ltBoot, cstE .ltStar] ++
        (pagePos ps).zip (pageBot inp)) ++
        ([cstE .hi0, cstE .hi1, cstE .hi2, cstE .hi3].zip
          [cstE .ltRgt, cstE .ltStar, cstE .ltSep, cstE .ltStar]) := by
    rw [startPos, startBot, List.zip_append, List.zip_append] <;>
      (simp [length_posPrefix, hinp.length_eq]; try omega)
  rw [hsplit, posPrefix_seven]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq]
  rw [mem_zip_page hwf hinp]
  constructor
  · intro h
    rw [StartBotAt] at h
    split at h
    · exact Or.inl (Or.inl (Or.inl ⟨h.1, h.2⟩))
    · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨h.1, h.2⟩)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩)))))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))))))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩)))))))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2⟩)))))))
    · obtain ⟨hposn, hp, a, ha, hc⟩ := h
      exact Or.inl (Or.inr ⟨p.2 0, a, (hps.2 _).mpr hposn, ha, Or.inl ⟨hp, hc⟩⟩)
    · obtain ⟨hposn, hp, hc⟩ := h
      obtain ⟨a, ha⟩ : ∃ a, (tmData A).InitTape (p.2 0) a := by
        by_cases hex : ∃ a, TMInp (p.2 0) a
        · obtain ⟨a, ha⟩ := hex
          exact ⟨a, Or.inl ha⟩
        · obtain ⟨b, hb⟩ := hwf.2.2.2.1
          exact ⟨b, Or.inr ⟨fun b' hb' => hex ⟨b', hb'⟩, hb⟩⟩
      exact Or.inl (Or.inr ⟨p.2 0, a, (hps.2 _).mpr hposn, ha, Or.inr ⟨hp, hc⟩⟩)
    · exact Or.inr (Or.inl ⟨h.1, h.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2⟩)))
    · exact h.elim
  · intro h
    rcases h with ((h | h | h | h | h | h | h) | hpage) | (h | h | h | h)
    all_goals try (obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    obtain ⟨q, a, hq, ha, hcase⟩ := hpage
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(hps.2 q).mp hq, rfl, a, ha, rfl⟩
    · exact ⟨(hps.2 q).mp hq, rfl, rfl⟩

end StartTable

/-! ### More `Forall₂` plumbing -/

section Forall

variable {α β : Type} {R S : α → β → Prop} {f : α → β}

theorem eq_map_of_forall₂ :
    ∀ {l : List α} {w : List β}, List.Forall₂ (fun a b => b = f a) l w → w = l.map f
  | [], _, h => List.forall₂_nil_left_iff.mp h
  | a :: l, _, h => by
    rcases h with - | ⟨hb, ht⟩
    rw [List.map_cons, hb, eq_map_of_forall₂ ht]

theorem forall₂_imp_mem :
    ∀ {l : List α} {w : List β}, (∀ a ∈ l, ∀ b, R a b → S a b) →
      List.Forall₂ R l w → List.Forall₂ S l w
  | [], _, _, h => by
    rw [List.forall₂_nil_left_iff.mp h]
    exact List.Forall₂.nil
  | a :: l, _, himp, h => by
    rcases h with - | ⟨hb, ht⟩
    exact List.Forall₂.cons (himp a List.mem_cons_self _ hb)
      (forall₂_imp_mem (fun x hx => himp x (List.mem_cons_of_mem a hx)) ht)

theorem forall₂_mem_right :
    ∀ {l : List α} {w : List β}, List.Forall₂ R l w → ∀ {b}, b ∈ w → ∃ a ∈ l, R a b
  | [], _, h, b, hb => by
    rw [List.forall₂_nil_left_iff.mp h] at hb
    exact absurd hb (by simp)
  | a :: l, _, h, b, hb => by
    rcases h with - | ⟨hb', ht⟩
    rcases List.mem_cons.mp hb with rfl | hb''
    · exact ⟨a, List.mem_cons_self, hb'⟩
    · obtain ⟨a', ha', hr⟩ := forall₂_mem_right ht hb''
      exact ⟨a', List.mem_cons_of_mem a ha', hr⟩

theorem flatten_map {δ ε ζ : Type} (f : δ → List ε) (g : ε → ζ) (l : List δ) :
    (l.map fun d => (f d).map g).flatten = ((l.map f).flatten).map g := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [ih]

end Forall

/-! ### The words of the drawn dominoes -/

section Words

variable (h : Reads e)

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- Every input cell holds something: its input symbol or the blank. -/
theorem initTape_exists (hwf : (tmData A).WellFormed) (p : A) :
    ∃ a, (tmData A).InitTape p a := by
  by_cases hex : ∃ a, TMInp p a
  · obtain ⟨a, ha⟩ := hex
    exact ⟨a, Or.inl ha⟩
  · obtain ⟨b, hb⟩ := hwf.2.2.2.1
    exact ⟨b, Or.inr ⟨fun b' hb' => hex ⟨b', hb'⟩, hb⟩⟩

include h in
/-- The top word of any element is its top table. -/
theorem isWordU_elem (d : B) : Pcp.IsWordU d ((uWord (e d)).map e.symm) :=
  isWord_of_zip h (by simp [uWord, length_posPrefix])
    (pairwise_posPrefix (uSpec_length_le _)) (fun p c => h.uAt d p c)

include h in
/-- The top word of any element is only its top table. -/
theorem eq_of_isWordU (hwfB : Pcp.IsWF B) {d : B} {w : List B}
    (hw : Pcp.IsWordU d w) : w = (uWord (e d)).map e.symm := by
  obtain ⟨ps, hs, hm, hf⟩ := hw
  exact eq_of_isWord_zip h (fun a b => Pcp.asymm_ordLt hwfB a b)
    (by simp [uWord, length_posPrefix]) (pairwise_posPrefix (uSpec_length_le _))
    (fun p c => h.uAt d p c) hs hm hf

include h in
/-- The bottom word of an element other than the start domino is its bottom
table. -/
theorem isWordV_elem_ne {d : B} (hne : (e d).1 ≠ .dStart) :
    Pcp.IsWordV d ((vWord (e d)).map e.symm) :=
  isWord_of_zip h (by simp [vWord, length_posPrefix])
    (pairwise_posPrefix (vSpec_length_le _))
    (fun p c => (h.vAt d p c).trans (pVAt_of_ne hne))

include h in
theorem eq_of_isWordV_ne (hwfB : Pcp.IsWF B) {d : B} (hne : (e d).1 ≠ .dStart)
    {w : List B} (hw : Pcp.IsWordV d w) : w = (vWord (e d)).map e.symm := by
  obtain ⟨ps, hs, hm, hf⟩ := hw
  exact eq_of_isWord_zip h (fun a b => Pcp.asymm_ordLt hwfB a b)
    (by simp [vWord, length_posPrefix]) (pairwise_posPrefix (vSpec_length_le _))
    (fun p c => (h.vAt d p c).trans (pVAt_of_ne hne)) hs hm hf

include h in
/-- The bottom word of the start domino is its layout. -/
theorem isWordV_elem_start (hwf : (tmData A).WellFormed) {ps inp : List A}
    (hps : IsPosEnum (tmData A) ps) (hinp : List.Forall₂ (tmData A).InitTape ps inp)
    {d : B} (hd : (e d).1 = .dStart) :
    Pcp.IsWordV d ((startBot inp).map e.symm) :=
  isWord_of_zip h (length_startPos hinp.length_eq) (pairwise_startPos hps.1)
    (fun p c => ((h.vAt d p c).trans (pVAt_start hd)).trans
      (startBotAt_iff_zip hwf hps hinp))

include h in
theorem eq_of_isWordV_start (hwfB : Pcp.IsWF B) (hwf : (tmData A).WellFormed)
    {ps inp : List A} (hps : IsPosEnum (tmData A) ps)
    (hinp : List.Forall₂ (tmData A).InitTape ps inp) {d : B} (hd : (e d).1 = .dStart)
    {w : List B} (hw : Pcp.IsWordV d w) : w = (startBot inp).map e.symm := by
  obtain ⟨qs, hs, hm, hf⟩ := hw
  exact eq_of_isWord_zip h (fun a b => Pcp.asymm_ordLt hwfB a b)
    (length_startPos hinp.length_eq) (pairwise_startPos hps.1)
    (fun p c => ((h.vAt d p c).trans (pVAt_start hd)).trans
      (startBotAt_iff_zip hwf hps hinp)) hs hm hf

omit [Language.turing.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- The start tag decodes to the abstract start domino. -/
theorem decode_of_tag_start {x : PV A} (hx : x.1 = PTag.dStart) :
    decodeDom x = Pcp.History.Dom.start := by
  obtain ⟨t, w⟩ := x
  have ht : t = PTag.dStart := hx
  subst ht
  rfl

end Words

/-- The start layout is functional in the position. -/
theorem startBotAt_fun (hwf : (tmData A).WellFormed) {p c c' : PV A}
    (h₁ : StartBotAt p c) (h₂ : StartBotAt p c') : c = c' := by
  obtain ⟨t, w⟩ := p
  cases t <;> first
    | exact h₁.elim
    | (exact h₁.2.trans h₂.2.symm)
    | skip
  case pairSym =>
    obtain ⟨-, -, a, ha, rfl⟩ := h₁
    obtain ⟨-, -, a', ha', rfl⟩ := h₂
    rw [TMData.initTape_functional hwf ha ha']
  case pairStar =>
    exact h₁.2.2.trans h₂.2.2.symm

/-! ### Well-formedness of the drawn instance -/

theorem isWF_of_reads (h : Reads e) (hwf : (tmData A).WellFormed) : Pcp.IsWF B where
  ord_refl x := (h.ord x x).mpr (pLe_refl _)
  ord_trans x y z hxy hyz :=
    (h.ord x z).mpr (pLe_trans hwf.1 ((h.ord x y).mp hxy) ((h.ord y z).mp hyz))
  ord_antisymm x y hxy hyx :=
    e.injective (pLe_antisymm hwf.1 ((h.ord x y).mp hxy) ((h.ord y x).mp hyx))
  ord_total x y :=
    (pLe_total hwf.1 (e x) (e y)).imp (h.ord x y).mpr (h.ord y x).mpr
  uAt_fun d p c c' hc hc' := by
    have hnd : (posPrefix (A := A) (uSpec (e d).1).length).Nodup :=
      (pairwise_posPrefix (uSpec_length_le _)).imp fun hxy => hxy.2
    refine e.injective (zip_fun (by simp [uWord, length_posPrefix]) hnd
      ((h.uAt d p c).mp hc) ((h.uAt d p c').mp hc'))
  vAt_fun d p c c' hc hc' := by
    by_cases hd : (e d).1 = .dStart
    · have h₁ := (pVAt_start hd).mp ((h.vAt d p c).mp hc)
      have h₂ := (pVAt_start hd).mp ((h.vAt d p c').mp hc')
      exact e.injective (startBotAt_fun hwf h₁ h₂)
    · have hnd : (posPrefix (A := A) (vSpec (e d).1).length).Nodup :=
        (pairwise_posPrefix (vSpec_length_le _)).imp fun hxy => hxy.2
      refine e.injective (zip_fun (by simp [vWord, length_posPrefix]) hnd
        ((pVAt_of_ne hd).mp ((h.vAt d p c).mp hc))
        ((pVAt_of_ne hd).mp ((h.vAt d p c').mp hc')))

/-! ### The equivalence -/

/-- **Correctness of the drawn instance**: it is a yes-instance of PCP exactly
when the machine is well-formed and accepts. -/
theorem pcpOn_iff_of_reads (h : Reads e) :
    Pcp.PcpOn B ↔ (tmData A).WellFormed ∧ (tmData A).AcceptsU := by
  constructor
  · rintro ⟨hwfB, l, us, vs, hlne, hdom, hu, hv, hflat⟩
    obtain ⟨d₀, hd₀⟩ := List.exists_mem_of_ne_nil l hlne
    have hwf : (tmData A).WellFormed := ((h.dom d₀).mp (hdom d₀ hd₀)).1
    refine ⟨hwf, ?_⟩
    obtain ⟨ps, hpsp, hpsm⟩ := Pcp.exists_isEnum hwf.1 (tmData A).Posn
    have hps : IsPosEnum (tmData A) ps := ⟨hpsp, hpsm⟩
    obtain ⟨inp, hinp⟩ := Pcp.exists_forall₂ (R := (tmData A).InitTape)
      fun p _ => initTape_exists hwf p
    rw [acceptsU_iff_hasMatch hwf hps hinp]
    have hpdom : ∀ d ∈ l, PDom (e d) := fun d hd => (h.dom d).mp (hdom d hd)
    refine ⟨l.map (fun d => decodeDom (e d)), by simpa using hlne, ?_, ?_⟩
    · intro d hd
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
      exact ok_decodeDom (hpdom d' hd')
    · -- both concatenations are the transported abstract concatenations
      have g : PV A → B := fun x => e.symm x
      have hus : us = l.map fun d =>
          ((Pcp.History.topW TapeLetter.halt (decodeDom (e d))).map letterElem).map
            e.symm := by
        refine eq_map_of_forall₂ (forall₂_imp_mem ?_ hu)
        intro d hd w hw
        rw [eq_of_isWordU h hwfB hw, uWord_eq (hpdom d hd)]
      have hvs : vs = l.map fun d =>
          ((Pcp.History.botW (startWord inp) (decodeDom (e d))).map letterElem).map
            e.symm := by
        refine eq_map_of_forall₂ (forall₂_imp_mem ?_ hv)
        intro d hd w hw
        by_cases hstart : (e d).1 = .dStart
        · rw [eq_of_isWordV_start h hwfB hwf hps hinp hstart hw, startBot_eq,
            decode_of_tag_start hstart]
        · rw [eq_of_isWordV_ne h hwfB hstart hw, vWord_eq (hpdom d hd) hstart]
      have hinj : Function.Injective fun ℓ => e.symm (letterElem (A := A) ℓ) :=
        e.symm.injective.comp letterElem_injective
      have key : ∀ F : B → List (Pcp.History.Letter (TapeLetter A)),
          (l.map fun d => ((F d).map letterElem).map e.symm).flatten =
            ((l.map F).flatten).map fun ℓ => e.symm (letterElem ℓ) := by
        intro F
        rw [← flatten_map F (fun ℓ => e.symm (letterElem ℓ)) l]
        congr 1
        refine List.map_congr_left fun d _ => ?_
        rw [List.map_map]
        rfl
      have hds : ∀ F : Pcp.History.Dom (TapeLetter A) → List (Pcp.History.Letter (TapeLetter A)),
          (l.map fun d => decodeDom (e d)).map F =
            l.map fun d => F (decodeDom (e d)) := by
        intro F
        rw [List.map_map]
        rfl
      have h1 : us.flatten = (Pcp.History.tops TapeLetter.halt
          (l.map fun d => decodeDom (e d))).map fun ℓ => e.symm (letterElem ℓ) := by
        rw [hus, key, Pcp.History.tops, hds]
      have h2 : vs.flatten = (Pcp.History.bots (startWord inp)
          (l.map fun d => decodeDom (e d))).map fun ℓ => e.symm (letterElem ℓ) := by
        rw [hvs, key, Pcp.History.bots, hds]
      exact List.map_injective_iff.mpr hinj ((h1.symm.trans hflat).trans h2)
  · rintro ⟨hwf, hacc⟩
    obtain ⟨ps, hpsp, hpsm⟩ := Pcp.exists_isEnum hwf.1 (tmData A).Posn
    have hps : IsPosEnum (tmData A) ps := ⟨hpsp, hpsm⟩
    obtain ⟨inp, hinp⟩ := Pcp.exists_forall₂ (R := (tmData A).InitTape)
      fun p _ => initTape_exists hwf p
    rw [acceptsU_iff_hasMatch hwf hps hinp] at hacc
    obtain ⟨ds, hdsne, hok, heq⟩ := hacc
    obtain ⟨el, hel⟩ := Pcp.exists_forall₂ (R := fun d x => PDom x ∧ decodeDom x = d)
      fun d hd => exists_encode hwf (hok d hd)
    have hkey : ∀ F : Pcp.History.Dom (TapeLetter A) →
        List (Pcp.History.Letter (TapeLetter A)),
        (ds.map fun d => ((F d).map letterElem).map e.symm).flatten =
          ((ds.map F).flatten).map fun ℓ => e.symm (letterElem ℓ) := by
      intro F
      rw [← flatten_map F (fun ℓ => e.symm (letterElem ℓ)) ds]
      congr 1
      refine List.map_congr_left fun d _ => ?_
      rw [List.map_map]
      rfl
    refine ⟨isWF_of_reads h hwf, el.map e.symm,
      ds.map fun d => ((Pcp.History.topW TapeLetter.halt d).map letterElem).map e.symm,
      ds.map fun d => ((Pcp.History.botW (startWord inp) d).map letterElem).map e.symm,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro hcon
      rw [List.map_eq_nil_iff] at hcon
      subst hcon
      rw [List.forall₂_nil_right_iff] at hel
      exact hdsne hel
    · intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      obtain ⟨d', hd', hpd, -⟩ := forall₂_mem_right hel hx
      refine (h.dom _).mpr ?_
      simpa using hpd
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine forall₂_imp_mem ?_ hel.flip
      rintro x hx d ⟨hpd, rfl⟩
      have hword := isWordU_elem h (e.symm x)
      simp only [Equiv.apply_symm_apply] at hword
      rwa [uWord_eq hpd] at hword
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine forall₂_imp_mem ?_ hel.flip
      rintro x hx d ⟨hpd, rfl⟩
      by_cases hstart : x.1 = PTag.dStart
      · rw [decode_of_tag_start hstart, ← startBot_eq]
        refine isWordV_elem_start h hwf hps hinp ?_
        simpa using hstart
      · rw [← vWord_eq hpd hstart]
        have hword := isWordV_elem_ne h (d := e.symm x) (by simpa using hstart)
        simpa only [Equiv.apply_symm_apply] using hword
    · rw [hkey, hkey]
      rw [show (ds.map (Pcp.History.topW TapeLetter.halt)).flatten =
        Pcp.History.tops TapeLetter.halt ds from rfl]
      rw [show (ds.map (Pcp.History.botW (startWord inp))).flatten =
        Pcp.History.bots (startWord inp) ds from rfl]
      rw [heq]

end HaltPcp

end DescriptiveComplexity
