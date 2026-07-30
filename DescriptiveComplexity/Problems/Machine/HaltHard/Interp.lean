/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.Input
import DescriptiveComplexity.Problems.CodeHalt.Hardness.Interp
import DescriptiveComplexity.Problems.Machine.Defs

/-!
# Drawing the simulating machine and its input page

The interpretation of the reduction `P ≤ᶠᵒ[≤] HALT`: the states, symbols and
transitions of the simulating machine are tags – constant at every instance
size – and the cells of its initial tape are tagged tuples of the source
structure: one bit cell and one fold cell per tuple of each source relation
(the chain of `DescriptiveComplexity.HaltHard.inputChain`), and a handful of
constant cells for the markers and the spelled initial value `[0, n]`.

The one order key of the whole universe, junk included: the block index of
the tag, then the tuple in **descending** lexicographic order with the last
coordinate most significant – matching the little-endian significance of
`DescriptiveComplexity.tupleIdx`, so that position-ascending order reads the
flattened relation table reversed, which is the order the chain folds – and
a static sub-index that interleaves each bit cell with its fold cell.
Unused coordinates are pinned to the minimum
(`DescriptiveComplexity.Canon`), so cells enumerate exactly once.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec FirstOrder Language Structure

variable {L : Language.{0, 0}} (V : FinVocab L)

/-! ### The cell tags -/

/-- The tags of the input cells: the left marker, one bit cell and one fold
cell per source symbol (carrying a tuple of its arity), the procedure cell,
the middle marker, the inner blank, and the spelled initial value `[0, n]` –
a separator, one digit cell per element, a separator, and the right
marker. -/
inductive CellTag (V : FinVocab L) where
  /-- The cell of `endL`. -/
  | cEndL : CellTag V
  /-- A bit cell of the chain: one per tuple of the source symbol `i`. -/
  | cBit (i : Fin V.numSyms) : CellTag V
  /-- The fold cell paired with a bit cell. -/
  | cFold (i : Fin V.numSyms) : CellTag V
  /-- The cell of the final `comp` header, the semi-decision procedure. -/
  | cProc : CellTag V
  /-- The cell of `mid`. -/
  | cMid : CellTag V
  /-- The one blank of the inner gap. -/
  | cGap : CellTag V
  /-- The separator left of the digits. -/
  | cComL : CellTag V
  /-- A digit cell of the spelled size: one per element. -/
  | cOne : CellTag V
  /-- The separator right of the digits. -/
  | cComR : CellTag V
  /-- The cell of `endR`. -/
  | cEndR : CellTag V

namespace CellTag

/-- An injective numbering of the cell tags, for finiteness. -/
def key : CellTag V → Fin 10 × Fin (V.numSyms + 1)
  | .cEndL => (0, 0)
  | .cBit i => (1, i.castSucc)
  | .cFold i => (2, i.castSucc)
  | .cProc => (3, 0)
  | .cMid => (4, 0)
  | .cGap => (5, 0)
  | .cComL => (6, 0)
  | .cOne => (7, 0)
  | .cComR => (8, 0)
  | .cEndR => (9, 0)

theorem key_injective : Function.Injective (key V) := by
  intro a b h
  rcases a <;> rcases b <;>
    simp only [key, Prod.mk.injEq] at h <;> simp_all

instance : Finite (CellTag V) := Finite.of_injective _ (key_injective V)

instance : Nonempty (CellTag V) := ⟨.cEndL⟩

/-- The coordinates a cell tag uses; the rest are pinned to the minimum. -/
def used : CellTag V → ℕ
  | .cBit i => V.arity i
  | .cFold i => V.arity i
  | .cOne => 1
  | _ => 0

theorem used_le_dimOf : ∀ c : CellTag V, used V c ≤ dimOf V
  | .cBit i => arity_le_dimOf V i
  | .cFold i => arity_le_dimOf V i
  | .cOne => dimOf_pos V
  | .cEndL | .cProc | .cMid | .cGap | .cComL | .cComR | .cEndR => Nat.zero_le _

end CellTag

/-! ### The tags of the drawn instance -/

variable (cF cP : Code)

/-- The tags of the drawn instance: a machine element – a state, a symbol or
a transition of the simulating machine – or an input cell. -/
abbrev HTag : Type := SimU (allCode cF cP) ⊕ CellTag V

instance : Finite (HTag V cF cP) := by
  have : Finite (SimU (allCode cF cP)) := by
    have : Finite (SimQ (allCode cF cP) × SimSym (allCode cF cP)) := Finite.instProd
    exact Finite.instSum
  exact Finite.instSum

instance : Nonempty (HTag V cF cP) := ⟨Sum.inr .cEndL⟩

/-- The coordinates a tag uses. -/
def HTag.used : HTag V cF cP → ℕ
  | .inl _ => 0
  | .inr c => CellTag.used V c

/-- A chosen injective numbering of the machine elements, for the order on
the junk. -/
noncomputable def uCode : SimU (allCode cF cP) → ℕ :=
  (exists_injective_nat (SimU (allCode cF cP))).choose

theorem uCode_injective : Function.Injective (uCode cF cP) :=
  (exists_injective_nat (SimU (allCode cF cP))).choose_spec

/-- **The block index of a tag** – the primary component of the one order
key. The chain blocks descend along the symbols, each shared by the bit and
fold tags; the machine elements sit above everything, ordered by the chosen
numbering. -/
noncomputable def blockIdx : HTag V cF cP → ℕ
  | .inr .cEndL => 0
  | .inr (.cBit i) => 1 + (V.numSyms - 1 - i)
  | .inr (.cFold i) => 1 + (V.numSyms - 1 - i)
  | .inr .cProc => V.numSyms + 1
  | .inr .cMid => V.numSyms + 2
  | .inr .cGap => V.numSyms + 3
  | .inr .cComL => V.numSyms + 4
  | .inr .cOne => V.numSyms + 5
  | .inr .cComR => V.numSyms + 6
  | .inr .cEndR => V.numSyms + 7
  | .inl u => V.numSyms + 8 + uCode cF cP u

/-- The sub-index breaking the tie inside a chain block: the fold cell sits
right of its bit cell. -/
def subIdx : HTag V cF cP → ℕ
  | .inr (.cFold _) => 1
  | _ => 0

/-- The pair of indices determines the tag. -/
theorem tag_eq_of_idx {t t' : HTag V cF cP} (hb : blockIdx V cF cP t = blockIdx V cF cP t')
    (hs : subIdx V cF cP t = subIdx V cF cP t') : t = t' := by
  have hcell : ∀ c : CellTag V, blockIdx V cF cP (Sum.inr c) ≤ V.numSyms + 7 := by
    intro c
    rcases c with - | i | i | - | - | - | - | - | - | - <;> simp only [blockIdx] <;> omega
  rcases t with u | c <;> rcases t' with u' | c'
  · simp only [blockIdx] at hb
    exact congrArg _ (uCode_injective cF cP (by omega))
  · refine absurd hb ?_
    have h1 := hcell c'
    have h2 : blockIdx V cF cP (Sum.inl u) = V.numSyms + 8 + uCode cF cP u := rfl
    omega
  · refine absurd hb ?_
    have h1 := hcell c
    have h2 : blockIdx V cF cP (Sum.inl u') = V.numSyms + 8 + uCode cF cP u' := rfl
    omega
  · rcases c with - | i | i | - | - | - | - | - | - | - <;>
      rcases c' with - | i' | i' | - | - | - | - | - | - | - <;>
      simp only [blockIdx, subIdx] at hb hs <;>
      first
      | rfl
      | omega
      | (have h1 := i.isLt; have h2 := i'.isLt; omega)
      | (have h1 := i.isLt; have h2 := i'.isLt
         exact congrArg _ (congrArg _ (Fin.ext (by omega))))

/-! ### The reversed lexicographic order on tuples -/

section RevLex

variable {A : Type} [LinearOrder A] {D : ℕ}

/-- `u` is below `w` in the reversed lexicographic order: they differ, and at
the highest differing coordinate `u` is smaller. Matching the little-endian
significance of `DescriptiveComplexity.tupleIdx`, this is comparison of
tuple numbers. -/
def RevLexLt (u w : Fin D → A) : Prop :=
  ∃ j, u j < w j ∧ ∀ j', j < j' → u j' = w j'

theorem RevLexLt.irrefl {u : Fin D → A} (h : RevLexLt u u) : False := by
  obtain ⟨j, hj, -⟩ := h
  exact absurd hj (lt_irrefl _)

theorem RevLexLt.asymm {u w : Fin D → A} (h : RevLexLt u w) (h' : RevLexLt w u) : False := by
  obtain ⟨j, hj, htl⟩ := h
  obtain ⟨j', hj', htl'⟩ := h'
  rcases lt_trichotomy j j' with hlt | rfl | hlt
  · rw [htl j' hlt] at hj'
    exact absurd hj' (lt_irrefl _)
  · exact absurd (hj.trans hj') (lt_irrefl _)
  · rw [htl' j hlt] at hj
    exact absurd hj (lt_irrefl _)

theorem RevLexLt.trans {u w x : Fin D → A} (h : RevLexLt u w) (h' : RevLexLt w x) :
    RevLexLt u x := by
  obtain ⟨j, hj, htl⟩ := h
  obtain ⟨j', hj', htl'⟩ := h'
  rcases lt_trichotomy j j' with hlt | rfl | hlt
  · exact ⟨j', (htl j' hlt).symm ▸ hj', fun k hk => (htl k (hlt.trans hk)).trans (htl' k hk)⟩
  · exact ⟨j, hj.trans hj', fun k hk => (htl k hk).trans (htl' k hk)⟩
  · exact ⟨j, htl' j hlt ▸ hj, fun k hk => (htl k hk).trans (htl' k (hlt.trans hk))⟩

theorem revLexLt_trichotomy (u w : Fin D → A) : RevLexLt u w ∨ u = w ∨ RevLexLt w u := by
  classical
  by_cases heq : u = w
  · exact Or.inr (Or.inl heq)
  have hne : (Finset.univ.filter fun j : Fin D => u j ≠ w j).Nonempty := by
    by_contra hcon
    refine heq (funext fun j => ?_)
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have := hcon (Finset.mem_univ j)
    simpa using this
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := (Finset.univ.filter fun j : Fin D => u j ≠ w j).exists_max_image
    id hne
  have hj₀ : u j₀ ≠ w j₀ := by simpa using hj₀mem
  have htail : ∀ j', j₀ < j' → u j' = w j' := by
    intro j' hj'
    by_contra hcon
    have hmem : j' ∈ Finset.univ.filter fun j : Fin D => u j ≠ w j := by simpa using hcon
    exact absurd (hj₀max j' hmem) (by simpa using hj')
  rcases lt_or_gt_of_ne hj₀ with hlt | hgt
  · exact Or.inl ⟨j₀, hlt, htail⟩
  · exact Or.inr (Or.inr ⟨j₀, hgt, fun j' hj' => (htail j' hj').symm⟩)

end RevLex

/-! ### The one order of the whole universe -/

section Order

variable {A : Type} [LinearOrder A]

/-- **The order of the drawn universe, junk included**: block index of the
tag, then the tuple – descending along the reversed lexicographic order, so
that ascending positions read descending tuple numbers – then the
sub-index. -/
noncomputable def HLe (x y : HTag V cF cP × (Fin (dimOf V) → A)) : Prop :=
  blockIdx V cF cP x.1 < blockIdx V cF cP y.1 ∨
    (blockIdx V cF cP x.1 = blockIdx V cF cP y.1 ∧
      (RevLexLt y.2 x.2 ∨ (x.2 = y.2 ∧ subIdx V cF cP x.1 ≤ subIdx V cF cP y.1)))

theorem isLinOrd_hLe : IsLinOrd (HLe V cF cP (A := A)) := by
  refine ⟨fun a => ?_, fun a b c hab hbc => ?_, fun a b hab hba => ?_, fun a b => ?_⟩
  · exact Or.inr ⟨rfl, Or.inr ⟨rfl, le_refl _⟩⟩
  · rcases hab with h1 | ⟨h1, h2⟩ <;> rcases hbc with h3 | ⟨h3, h4⟩
    · exact Or.inl (h1.trans h3)
    · exact Or.inl (h3 ▸ h1)
    · exact Or.inl (h1 ▸ h3)
    · refine Or.inr ⟨h1.trans h3, ?_⟩
      rcases h2 with h2 | ⟨h2, h2'⟩ <;> rcases h4 with h4 | ⟨h4, h4'⟩
      · exact Or.inl (h4.trans h2)
      · exact Or.inl (h4 ▸ h2)
      · exact Or.inl (h2 ▸ h4)
      · exact Or.inr ⟨h2.trans h4, h2'.trans h4'⟩
  · rcases hab with h1 | ⟨h1, h2⟩ <;> rcases hba with h3 | ⟨h3, h4⟩
    · exact absurd (h1.trans h3) (lt_irrefl _)
    · exact absurd h1 (by omega)
    · exact absurd h3 (by omega)
    · have htag : a.1 = b.1 := by
        rcases h2 with h2 | ⟨h2, h2'⟩ <;> rcases h4 with h4 | ⟨h4, h4'⟩
        · exact absurd h4 h2.asymm
        · exact absurd (h4 ▸ h2) RevLexLt.irrefl
        · exact absurd (h2 ▸ h4) RevLexLt.irrefl
        · exact tag_eq_of_idx V cF cP h1 (le_antisymm h2' h4')
      have htup : a.2 = b.2 := by
        rcases h2 with h2 | ⟨h2, -⟩ <;> rcases h4 with h4 | ⟨h4, -⟩
        · exact absurd h4 h2.asymm
        · exact h4.symm
        · exact h2
        · exact h2
      exact Prod.ext htag htup
  · rcases lt_trichotomy (blockIdx V cF cP a.1) (blockIdx V cF cP b.1) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases revLexLt_trichotomy b.2 a.2 with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨h, Or.inl h2⟩)
      · rcases le_total (subIdx V cF cP a.1) (subIdx V cF cP b.1) with h3 | h3
        · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h2.symm, h3⟩⟩)
        · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨h2, h3⟩⟩)
      · exact Or.inr (Or.inr ⟨h.symm, Or.inl h2⟩)
    · exact Or.inr (Or.inl h)

end Order

/-! ### The defining formulas -/

section Formulas

open CodeProgRed

/-- The reversed lexicographic comparison, as a formula: `p` is below `q`. -/
noncomputable def revLexLtF {γ : Type} (p q : Fin (dimOf V) → γ) :
    (L.sum Language.order).Formula γ :=
  listSup ((List.finRange (dimOf V)).map fun j =>
    ltF (Term.var (p j)) (Term.var (q j)) ⊓
      listInf ((List.finRange (dimOf V)).map fun j' : Fin (dimOf V) =>
        if (j : ℕ) < (j' : ℕ) then Term.equal (Term.var (p j')) (Term.var (q j')) else ⊤))

/-- Being a position: a cell tag on a canonically padded tuple. -/
noncomputable def hPosnF (t : HTag V cF cP) :
    (L.sum Language.order).Formula (Fin 1 × Fin (dimOf V)) :=
  match t with
  | .inl _ => ⊥
  | .inr c => canonF (CellTag.used V c) (sel₀ V)

open scoped Classical in
/-- A unary machine predicate: the tag is a machine element satisfying it,
canonically padded. -/
noncomputable def mUnaryF (Q : SimU (allCode cF cP) → Prop) (t : HTag V cF cP) :
    (L.sum Language.order).Formula (Fin 1 × Fin (dimOf V)) :=
  match t with
  | .inl u => if Q u then canonF 0 (sel₀ V) else ⊥
  | .inr _ => ⊥

open scoped Classical in
/-- A binary machine predicate: two machine elements satisfying it,
canonically padded. -/
noncomputable def mBinaryF (Q : SimU (allCode cF cP) → SimU (allCode cF cP) → Prop)
    (t t' : HTag V cF cP) : (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) :=
  match t, t' with
  | .inl u, .inl u' => if Q u u' then canonF 0 (selA V) ⊓ canonF 0 (selB V) else ⊥
  | _, _ => ⊥

open scoped Classical in
/-- The order, by the one key: block index, then the reversed lexicographic
order descending, then the sub-index. -/
noncomputable def hLeF (t t' : HTag V cF cP) :
    (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) :=
  if blockIdx V cF cP t < blockIdx V cF cP t' then ⊤
  else if blockIdx V cF cP t' < blockIdx V cF cP t then ⊥
  else revLexLtF V (selB V) (selA V) ⊔
    (eqTupF (selA V) (selB V) ⊓ (if subIdx V cF cP t ≤ subIdx V cF cP t' then ⊤ else ⊥))

/-- **The letter a cell initially holds**, semantically: the marker of its
tag, and on a bit cell the pushed bit reads the source relation. -/
noncomputable def InpOn {A : Type} [L.Structure A] [LinearOrder A] (c : CellTag V)
    (u : SimU (allCode cF cP)) (w : Fin (dimOf V) → A) : Prop :=
  match c with
  | .cEndL => u = sts .endL
  | .cBit i => (u = sts (.hComp (posBit cF cP true)) ∧ bitOf V i w) ∨
      (u = sts (.hComp (posBit cF cP false)) ∧ ¬bitOf V i w)
  | .cFold _ => u = sts (.hComp (posFold cF cP))
  | .cProc => u = sts (.hComp (posProc cF cP))
  | .cMid => u = sts .mid
  | .cGap => u = sts .bk
  | .cComL => u = sts .com
  | .cOne => u = sts .one
  | .cComR => u = sts .com
  | .cEndR => u = sts .endR

open scoped Classical in
/-- The body of the initial-tape relation, per cell tag and letter. -/
noncomputable def inpBodyF (c : CellTag V) (u : SimU (allCode cF cP)) :
    (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) :=
  match c with
  | .cEndL => if u = sts .endL then ⊤ else ⊥
  | .cBit i =>
      if u = sts (.hComp (posBit cF cP true)) then relAtF i
      else if u = sts (.hComp (posBit cF cP false)) then ∼(relAtF i) else ⊥
  | .cFold _ => if u = sts (.hComp (posFold cF cP)) then ⊤ else ⊥
  | .cProc => if u = sts (.hComp (posProc cF cP)) then ⊤ else ⊥
  | .cMid => if u = sts .mid then ⊤ else ⊥
  | .cGap => if u = sts .bk then ⊤ else ⊥
  | .cComL => if u = sts .com then ⊤ else ⊥
  | .cOne => if u = sts .one then ⊤ else ⊥
  | .cComR => if u = sts .com then ⊤ else ⊥
  | .cEndR => if u = sts .endR then ⊤ else ⊥

/-- The initial-tape relation: a cell and a canonically padded symbol
element, related by the body. -/
noncomputable def hInpF (t t' : HTag V cF cP) :
    (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) :=
  match t, t' with
  | .inr c, .inl u =>
      canonF (CellTag.used V c) (selA V) ⊓ canonF 0 (selB V) ⊓ inpBodyF V cF cP c u
  | _, _ => ⊥

/-- **The interpretation**: machine elements and input cells as tagged
tuples, the machine relations read off `DescriptiveComplexity.HaltHard.simTM`
at the tags, the input page reading the source relations. -/
noncomputable def haltTuringInterp :
    FOInterpretation (L.sum Language.order) Language.turing (HTag V cF cP) (dimOf V) where
  relFormula {n} R ts :=
    match n, R with
    | _, .posn => hPosnF V cF cP (ts 0)
    | _, .tr => mUnaryF V cF cP (simTM (allCode cF cP)).Tr (ts 0)
    | _, .start => mUnaryF V cF cP (simTM (allCode cF cP)).Start (ts 0)
    | _, .acc => mUnaryF V cF cP (simTM (allCode cF cP)).Acc (ts 0)
    | _, .blank => mUnaryF V cF cP (simTM (allCode cF cP)).Blank (ts 0)
    | _, .right => mUnaryF V cF cP (simTM (allCode cF cP)).Right (ts 0)
    | _, .le => hLeF V cF cP (ts 0) (ts 1)
    | _, .tsrc => mBinaryF V cF cP (simTM (allCode cF cP)).Src (ts 0) (ts 1)
    | _, .tread => mBinaryF V cF cP (simTM (allCode cF cP)).Read (ts 0) (ts 1)
    | _, .tdst => mBinaryF V cF cP (simTM (allCode cF cP)).Dst (ts 0) (ts 1)
    | _, .twrite => mBinaryF V cF cP (simTM (allCode cF cP)).Write (ts 0) (ts 1)
    | _, .inp => hInpF V cF cP (ts 0) (ts 1)

end Formulas

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {V cF cP} {A : Type} [L.Structure A] [LinearOrder A]

open CodeProgRed

/-- The element of the drawn instance with a given tag and tuple. -/
def hPt (t : HTag V cF cP) (w : Fin (dimOf V) → A) : (haltTuringInterp V cF cP).Map A := (t, w)

omit [L.Structure A] [LinearOrder A] in
theorem exists_hPt (x : (haltTuringInterp V cF cP).Map A) : ∃ t w, x = hPt t w :=
  ⟨x.1, x.2, rfl⟩

omit [L.Structure A] in
/-- The order, with the projections of the point reduced. -/
theorem hLe_def (t t' : HTag V cF cP) (w w' : Fin (dimOf V) → A) :
    HLe V cF cP (t, w) (t', w') ↔
      blockIdx V cF cP t < blockIdx V cF cP t' ∨
        (blockIdx V cF cP t = blockIdx V cF cP t' ∧
          (RevLexLt w' w ∨ (w = w' ∧ subIdx V cF cP t ≤ subIdx V cF cP t'))) := Iff.rfl

theorem realize_revLexLtF {γ : Type} {p q : Fin (dimOf V) → γ} {v : γ → A} :
    (revLexLtF V p q).Realize v ↔ RevLexLt (fun j => v (p j)) (fun j => v (q j)) := by
  rw [revLexLtF, realize_listSup]
  constructor
  · rintro ⟨φ, hφ, hr⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_inf, realize_listInf] at hr
    refine ⟨j, by simpa using hr.1, ?_⟩
    intro j' hj'
    have h := hr.2 _ (List.mem_map.mpr ⟨j', List.mem_finRange j', rfl⟩)
    rw [if_pos (show (j : ℕ) < (j' : ℕ) from hj')] at h
    simpa using h
  · rintro ⟨j, hj, htl⟩
    refine ⟨_, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, ?_⟩
    rw [Formula.realize_inf, realize_listInf]
    refine ⟨by simpa using hj, ?_⟩
    intro φ hφ
    obtain ⟨j', -, rfl⟩ := List.mem_map.mp hφ
    by_cases h : (j : ℕ) < (j' : ℕ)
    · rw [if_pos h]
      simpa using htl j' h
    · rw [if_neg h]
      simp

theorem relMap_posn (t : HTag V cF cP) (w : Fin (dimOf V) → A) :
    TMPosn (hPt t w) ↔ ∃ c, t = Sum.inr c ∧ Canon (CellTag.used V c) w := by
  rw [TMPosn, FOInterpretation.relMap_map]
  change (hPosnF V cF cP t).Realize _ ↔ _
  cases t with
  | inl u => exact iff_of_false (by simp [hPosnF]) (by simp)
  | inr c =>
    rw [show hPosnF V cF cP (Sum.inr c) = canonF (CellTag.used V c) (sel₀ V) from rfl,
      realize_canonF]
    simp only [Sum.inr.injEq]
    constructor
    · intro h
      exact ⟨c, rfl, h⟩
    · rintro ⟨c', rfl, h⟩
      exact h

theorem relMap_unary (Q : SimU (allCode cF cP) → Prop)
    (R : Language.turingRel 1)
    (hR : ∀ ts : Fin 1 → HTag V cF cP,
      (haltTuringInterp V cF cP).relFormula R ts = mUnaryF V cF cP Q (ts 0))
    (t : HTag V cF cP) (w : Fin (dimOf V) → A) :
    (RelMap (show Language.turing.Relations 1 from R) ![hPt t w] : Prop) ↔
      (∃ u, t = Sum.inl u ∧ Q u) ∧ Canon 0 w := by
  rw [FOInterpretation.relMap_map, hR]
  change (mUnaryF V cF cP Q t).Realize _ ↔ _
  classical
  cases t with
  | inl u =>
    by_cases hQ : Q u
    · rw [show mUnaryF V cF cP Q (Sum.inl u) = if Q u then canonF 0 (sel₀ V) else ⊥ from rfl,
        if_pos hQ, realize_canonF]
      simp only [Sum.inl.injEq]
      exact ⟨fun h => ⟨⟨u, rfl, hQ⟩, h⟩, fun h => h.2⟩
    · rw [show mUnaryF V cF cP Q (Sum.inl u) = if Q u then canonF 0 (sel₀ V) else ⊥ from rfl,
        if_neg hQ]
      refine iff_of_false (by simp) ?_
      rintro ⟨⟨u', hu, hQ'⟩, -⟩
      obtain rfl : u' = u := by simpa using hu.symm
      exact hQ hQ'
  | inr c =>
    refine iff_of_false (by simp [mUnaryF]) ?_
    rintro ⟨⟨u, hu, -⟩, -⟩
    simp at hu

theorem relMap_binary (Q : SimU (allCode cF cP) → SimU (allCode cF cP) → Prop)
    (R : Language.turingRel 2)
    (hR : ∀ ts : Fin 2 → HTag V cF cP,
      (haltTuringInterp V cF cP).relFormula R ts = mBinaryF V cF cP Q (ts 0) (ts 1))
    (t t' : HTag V cF cP) (w w' : Fin (dimOf V) → A) :
    (RelMap (show Language.turing.Relations 2 from R) ![hPt t w, hPt t' w'] : Prop) ↔
      (∃ u u', t = Sum.inl u ∧ t' = Sum.inl u' ∧ Q u u') ∧ Canon 0 w ∧ Canon 0 w' := by
  rw [FOInterpretation.relMap_map, hR]
  change (mBinaryF V cF cP Q t t').Realize _ ↔ _
  classical
  rcases t with u | c
  · rcases t' with u' | c'
    · by_cases hQ : Q u u'
      · rw [show mBinaryF V cF cP Q (Sum.inl u) (Sum.inl u') =
            if Q u u' then canonF 0 (selA V) ⊓ canonF 0 (selB V) else ⊥ from rfl,
          if_pos hQ, Formula.realize_inf, realize_canonF, realize_canonF]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨u, u', rfl, rfl, hQ⟩, h1, h2⟩
        · rintro ⟨-, h1, h2⟩
          exact ⟨h1, h2⟩
      · rw [show mBinaryF V cF cP Q (Sum.inl u) (Sum.inl u') =
            if Q u u' then canonF 0 (selA V) ⊓ canonF 0 (selB V) else ⊥ from rfl,
          if_neg hQ]
        refine iff_of_false (by simp) ?_
        rintro ⟨⟨u₁, u₂, h1, h2, hQ'⟩, -⟩
        obtain rfl : u₁ = u := by simpa using h1.symm
        obtain rfl : u₂ = u' := by simpa using h2.symm
        exact hQ hQ'
    · refine iff_of_false (by simp [mBinaryF]) ?_
      rintro ⟨⟨u₁, u₂, -, h2, -⟩, -⟩
      simp at h2
  · refine iff_of_false (by cases t' <;> simp [mBinaryF]) ?_
    rintro ⟨⟨u₁, u₂, h1, -, -⟩, -⟩
    simp at h1

theorem relMap_le (t t' : HTag V cF cP) (w w' : Fin (dimOf V) → A) :
    TMLe (hPt t w) (hPt t' w') ↔ HLe V cF cP (t, w) (t', w') := by
  rw [TMLe, FOInterpretation.relMap_map]
  change (hLeF V cF cP t t').Realize _ ↔ _
  classical
  rw [hLe_def]
  rcases lt_trichotomy (blockIdx V cF cP t) (blockIdx V cF cP t') with h | h | h
  · rw [hLeF, if_pos h]
    exact iff_of_true (by simp) (Or.inl h)
  · rw [hLeF, if_neg (by omega), if_neg (by omega), Formula.realize_sup,
      Formula.realize_inf, realize_revLexLtF, realize_eqTupF]
    constructor
    · rintro (hr | ⟨he, hs⟩)
      · exact Or.inr ⟨h, Or.inl hr⟩
      · refine Or.inr ⟨h, Or.inr ⟨?_, ?_⟩⟩
        · funext j
          exact (congrFun he j).symm
        · by_contra hcon
          rw [if_neg hcon] at hs
          simp at hs
    · rintro (hlt | ⟨-, hr | ⟨he, hs⟩⟩)
      · omega
      · exact Or.inl hr
      · refine Or.inr ⟨?_, ?_⟩
        · funext j
          exact (congrFun he j).symm
        · rw [if_pos hs]
          simp
  · rw [hLeF, if_neg (by omega), if_pos h]
    refine iff_of_false (by simp) ?_
    rintro (hlt | ⟨he, -⟩) <;> omega

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem val_sel₀ (t : HTag V cF cP) (w : Fin (dimOf V) → A) (j : Fin (dimOf V)) :
    (![hPt t w] (sel₀ V j).1).2 (sel₀ V j).2 = w j := rfl

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem val_selA (t t' : HTag V cF cP) (w w' : Fin (dimOf V) → A) (j : Fin (dimOf V)) :
    (![hPt t w, hPt t' w'] (selA V j).1).2 (selA V j).2 = w j := rfl

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem val_selB (t t' : HTag V cF cP) (w w' : Fin (dimOf V) → A) (j : Fin (dimOf V)) :
    (![hPt t w, hPt t' w'] (selB V j).1).2 (selB V j).2 = w' j := rfl

omit [L.Structure A] [LinearOrder A] in
theorem posBit_true_ne_false : posBit cF cP true ≠ posBit cF cP false := by
  have h1 : posBit cF cP true = posBit1 cF cP := rfl
  have h0 : posBit cF cP false = posBit0 cF cP := rfl
  rw [h1, h0, posBit1, posBit0]
  intro h
  injection h with h
  injection h

omit [L.Structure A] [LinearOrder A] in
theorem posBit_false_ne_true : posBit cF cP false ≠ posBit cF cP true :=
  fun h => posBit_true_ne_false h.symm

theorem relMap_inp (t t' : HTag V cF cP) (w w' : Fin (dimOf V) → A) :
    TMInp (hPt t w) (hPt t' w') ↔
      ∃ c u, t = Sum.inr c ∧ t' = Sum.inl u ∧ Canon (CellTag.used V c) w ∧ Canon 0 w' ∧
        InpOn V cF cP c u w := by
  rw [TMInp, FOInterpretation.relMap_map]
  change (hInpF V cF cP t t').Realize _ ↔ _
  classical
  rcases t with u₀ | c
  · refine iff_of_false (by cases t' <;> simp [hInpF]) ?_
    rintro ⟨c, u, h1, -⟩
    simp at h1
  rcases t' with u | c₀
  swap
  · refine iff_of_false (by simp [hInpF]) ?_
    rintro ⟨c', u, -, h2, -⟩
    simp at h2
  rw [show hInpF V cF cP (Sum.inr c) (Sum.inl u) =
      canonF (CellTag.used V c) (selA V) ⊓ canonF 0 (selB V) ⊓ inpBodyF V cF cP c u from rfl,
    Formula.realize_inf, Formula.realize_inf, realize_canonF, realize_canonF]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨c, u, rfl, rfl, h1, h2, ?_⟩
    revert h3
    rcases c with - | i | i | - | - | - | - | - | - | - <;>
      simp only [inpBodyF, InpOn] <;> (try split_ifs) <;>
      intro h3 <;>
      simp_all [Formula.realize_not, realize_relAtF, posBit_true_ne_false,
        posBit_false_ne_true]
  · rintro ⟨c', u', hc, hu, h1, h2, h3⟩
    have hcc : c' = c := by simpa using hc.symm
    have huu : u' = u := by simpa using hu.symm
    rw [hcc, huu] at h3
    rw [hcc] at h1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact h1
    · exact h2
    revert h3
    rcases c with - | i | i | - | - | - | - | - | - | - <;>
      simp only [inpBodyF, InpOn] <;> (try split_ifs) <;>
      intro h3 <;>
      simp_all [Formula.realize_not, realize_relAtF, posBit_true_ne_false,
        posBit_false_ne_true]

end Characterizations

end HaltHard

end DescriptiveComplexity
