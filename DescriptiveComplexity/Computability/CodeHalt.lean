/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.Halting
import DescriptiveComplexity.Computability.Catalog
import DescriptiveComplexity.Problems.CodeHalt.Membership

/-!
# Drawing a partial recursive code as a concrete instance

The computable half of the undecidability bridge: a primitive recursive map

```
Nat.Partrec.Code → FirstOrder.Language.FinStruct codeVocab
```

whose image is a yes-instance of `DescriptiveComplexity.CODEHALT` exactly when
the code halts on `0` (`DescriptiveComplexity.codehalt_toPred_codeStruct`).

Nothing here simulates anything: the code *is* the instance, so the map is a
plain tree flattening. `DescriptiveComplexity.codeNodes` lists the nodes of a code
in preorder, each node carrying its constructor tag and the *relative* offsets
of its children – relative, so that the flattening of a subterm is literally a
segment of the flattening of the whole (`DescriptiveComplexity.Seg`), which is
what makes the correctness proof an induction on the code and nothing more.

This is exactly what the machine route could not deliver. Mathlib's universal
machine `Turing.PartrecToTM2.tr` is not finite-state, so `code ↦ machine
instance` is not available; `code ↦ syntax tree` is trivially primitive
recursive, and pushes the whole difficulty into `CODEHALT ∈ RE`, an ordinary
membership proof of the catalog
(`DescriptiveComplexity.Problems.CodeHalt.Membership`).

Whence the two results the layer exists for:
`DescriptiveComplexity.not_computablePred_of_RE_hard`, every RE-hard problem is
undecidable, and its first instance
`DescriptiveComplexity.finsat_not_computable`, Trakhtenbrot's theorem.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

instance : DecidableEq ((n : ℕ) × Language.code.Relations n) :=
  inferInstanceAs (DecidableEq ((n : ℕ) × codeRel n))

/-- **The vocabulary of code instances, presented**: eleven symbols, nine
unary and two binary. -/
def codeVocab : FinVocab Language.code :=
  FinVocab.ofList
    [⟨1, .croot⟩, ⟨1, .czero⟩, ⟨1, .csucc⟩, ⟨1, .cleft⟩, ⟨1, .cright⟩, ⟨1, .cpair⟩,
      ⟨1, .ccomp⟩, ⟨1, .cprec⟩, ⟨1, .crfind⟩, ⟨2, .carg1⟩, ⟨2, .carg2⟩]
    (by decide) (by rintro ⟨n, R⟩; cases R <;> simp)

/-! ### Flattening a code into a list of nodes -/

/-- The reading of an index outside the flattening: a tag no constructor
carries, and no children. -/
def nodeNone : ℕ × ℕ × ℕ := (8, 0, 0)

/-- **The nodes of a code, in preorder.** Each node carries its constructor
tag and the offsets of its children *relative to itself*, `0` meaning "no such
child". Relative offsets are what make the flattening of a subterm a segment
of the flattening of the whole. -/
def codeNodes : Nat.Partrec.Code → List (ℕ × ℕ × ℕ)
  | .zero => [(0, 0, 0)]
  | .succ => [(1, 0, 0)]
  | .left => [(2, 0, 0)]
  | .right => [(3, 0, 0)]
  | .pair cf cg => (4, 1, (codeNodes cf).length + 1) :: (codeNodes cf ++ codeNodes cg)
  | .comp cf cg => (5, 1, (codeNodes cf).length + 1) :: (codeNodes cf ++ codeNodes cg)
  | .prec cf cg => (6, 1, (codeNodes cf).length + 1) :: (codeNodes cf ++ codeNodes cg)
  | .rfind' cf => (7, 1, 0) :: codeNodes cf

theorem flat_ne_nil : ∀ c : Nat.Partrec.Code, codeNodes c ≠ []
  | .zero | .succ | .left | .right => by simp [codeNodes]
  | .pair _ _ | .comp _ _ | .prec _ _ | .rfind' _ => by simp [codeNodes]

theorem flat_length_pos (c : Nat.Partrec.Code) : 0 < (codeNodes c).length :=
  List.length_pos_iff.mpr (flat_ne_nil c)

/-! ### Segments -/

/-- `Seg L M i`: the list `M` sits inside `L` starting at index `i`. -/
def Seg (L M : List (ℕ × ℕ × ℕ)) (i : ℕ) : Prop :=
  i + M.length ≤ L.length ∧ ∀ k, k < M.length → L.getD (i + k) nodeNone = M.getD k nodeNone

theorem seg_self (M : List (ℕ × ℕ × ℕ)) : Seg M M 0 :=
  ⟨by simp, fun k _ => by simp⟩

theorem Seg.head {L M : List (ℕ × ℕ × ℕ)} {i : ℕ} (h : Seg L M i) (hM : M ≠ []) :
    L.getD i nodeNone = M.getD 0 nodeNone := by
  have := h.2 0 (List.length_pos_iff.mpr hM)
  simpa using this

theorem Seg.tail {L : List (ℕ × ℕ × ℕ)} {a : ℕ × ℕ × ℕ} {M : List (ℕ × ℕ × ℕ)} {i : ℕ}
    (h : Seg L (a :: M) i) : Seg L M (i + 1) := by
  refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using h.1, fun k hk => ?_⟩
  have := h.2 (k + 1) (by simpa using hk)
  simpa [Nat.add_assoc, Nat.add_comm 1, Nat.add_left_comm] using this

theorem Seg.appendLeft {L M N : List (ℕ × ℕ × ℕ)} {i : ℕ} (h : Seg L (M ++ N) i) :
    Seg L M i := by
  refine ⟨by simpa using le_trans (by simp) h.1, fun k hk => ?_⟩
  have := h.2 k (by simpa using Nat.lt_of_lt_of_le hk (by simp))
  rw [this]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem Seg.appendRight {L M N : List (ℕ × ℕ × ℕ)} {i : ℕ} (h : Seg L (M ++ N) i) :
    Seg L N (i + M.length) := by
  refine ⟨by simpa [Nat.add_assoc] using h.1, fun k hk => ?_⟩
  have := h.2 (M.length + k) (by simpa using hk)
  rw [show i + (M.length + k) = i + M.length + k by omega] at this
  rw [this]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : M.length ≤ M.length + k)]

/-! ### The instance a code draws -/

/-- The constructor tag of the node at index `i`. -/
def tagAt (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ := (L.getD i nodeNone).1

/-- The offset of the first child of the node at index `i`, `0` for none. -/
def off1At (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ := (L.getD i nodeNone).2.1

/-- The offset of the second child of the node at index `i`, `0` for none. -/
def off2At (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ := (L.getD i nodeNone).2.2

/-- The relations a list of nodes denotes. -/
def codeRelBool (L : List (ℕ × ℕ × ℕ)) : ∀ {n : ℕ}, Language.code.Relations n →
    (Fin n → Fin (L.length + 1)) → Bool
  | _, .croot, x => decide ((x 0 : ℕ) = 0)
  | _, .czero, x => decide (tagAt L (x 0) = 0)
  | _, .csucc, x => decide (tagAt L (x 0) = 1)
  | _, .cleft, x => decide (tagAt L (x 0) = 2)
  | _, .cright, x => decide (tagAt L (x 0) = 3)
  | _, .cpair, x => decide (tagAt L (x 0) = 4)
  | _, .ccomp, x => decide (tagAt L (x 0) = 5)
  | _, .cprec, x => decide (tagAt L (x 0) = 6)
  | _, .crfind, x => decide (tagAt L (x 0) = 7)
  | _, .carg1, x =>
      decide (off1At L (x 0) ≠ 0 ∧ (x 1 : ℕ) = (x 0 : ℕ) + off1At L (x 0))
  | _, .carg2, x =>
      decide (off2At L (x 0) ≠ 0 ∧ (x 1 : ℕ) = (x 0 : ℕ) + off2At L (x 0))

/-- **The instance a list of nodes draws.** One element per node, and one
spare element at the end which carries no mark – out-of-range readings return
`DescriptiveComplexity.nodeNone`, whose tag is no constructor's. -/
def listStruct (L : List (ℕ × ℕ × ℕ)) : FinStruct codeVocab :=
  FinStruct.ofTable codeVocab L.length fun R x => codeRelBool L R x

/-- **The instance a code draws.** -/
def codeStruct (c : Nat.Partrec.Code) : FinStruct codeVocab := listStruct (codeNodes c)

@[simp] theorem card_listStruct (L : List (ℕ × ℕ × ℕ)) :
    (listStruct L).card = L.length + 1 := rfl

theorem relMapBool_listStruct (L : List (ℕ × ℕ × ℕ)) {n : ℕ} (R : Language.code.Relations n)
    (x : Fin n → (listStruct L).Univ) :
    (listStruct L).relMapBool R x = codeRelBool L R x :=
  FinStruct.relMapBool_ofTable _ _ _ R x

section Sem

variable (L : List (ℕ × ℕ × ℕ))

theorem cRoot_iff (i : (listStruct L).Univ) : CRoot i ↔ (i : ℕ) = 0 := by
  rw [CRoot, FinStruct.relMap_iff, relMapBool_listStruct]
  simp only [codeRelBool, Matrix.cons_val_zero]
  exact Iff.of_eq (decide_eq_true_eq (p := ((i : ℕ) = 0)))

theorem cZero_iff (i : (listStruct L).Univ) : CZero i ↔ tagAt L i = 0 := by
  rw [CZero, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cSucc_iff (i : (listStruct L).Univ) : CSucc i ↔ tagAt L i = 1 := by
  rw [CSucc, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cLeft_iff (i : (listStruct L).Univ) : CLeft i ↔ tagAt L i = 2 := by
  rw [CLeft, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cRight_iff (i : (listStruct L).Univ) : CRight i ↔ tagAt L i = 3 := by
  rw [CRight, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cPair_iff (i : (listStruct L).Univ) : CPair i ↔ tagAt L i = 4 := by
  rw [CPair, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cComp_iff (i : (listStruct L).Univ) : CComp i ↔ tagAt L i = 5 := by
  rw [CComp, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cPrec_iff (i : (listStruct L).Univ) : CPrec i ↔ tagAt L i = 6 := by
  rw [CPrec, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cRfind_iff (i : (listStruct L).Univ) : CRfind i ↔ tagAt L i = 7 := by
  rw [CRfind, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cArg1_iff (i j : (listStruct L).Univ) :
    CArg1 i j ↔ off1At L i ≠ 0 ∧ (j : ℕ) = (i : ℕ) + off1At L i := by
  rw [CArg1, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem cArg2_iff (i j : (listStruct L).Univ) :
    CArg2 i j ↔ off2At L i ≠ 0 ∧ (j : ℕ) = (i : ℕ) + off2At L i := by
  rw [CArg2, FinStruct.relMap_iff, relMapBool_listStruct]
  simp [codeRelBool]

theorem head_flat {L : List (ℕ × ℕ × ℕ)} {c : Nat.Partrec.Code} {i : ℕ}
    (h : Seg L (codeNodes c) i) : L.getD i nodeNone = (codeNodes c).getD 0 nodeNone :=
  h.head (flat_ne_nil c)

end Sem

/-! ### The instance a code draws does draw it -/

/-- **Every subterm is drawn at its segment.** -/
theorem decodesTo_of_seg (L : List (ℕ × ℕ × ℕ)) :
    ∀ (c : Nat.Partrec.Code) (i : ℕ) (hi : i < L.length + 1), Seg L (codeNodes c) i →
      DecodesTo (⟨i, hi⟩ : (listStruct L).Univ) c := by
  intro c
  induction c with
  | zero =>
    intro i hi h
    have hd := head_flat h
    refine (cZero_iff L _).mpr ?_
    change tagAt L i = 0
    simp only [tagAt]; rw [hd]; simp [codeNodes]
  | succ =>
    intro i hi h
    have hd := head_flat h
    refine (cSucc_iff L _).mpr ?_
    change tagAt L i = 1
    simp only [tagAt]; rw [hd]; simp [codeNodes]
  | left =>
    intro i hi h
    have hd := head_flat h
    refine (cLeft_iff L _).mpr ?_
    change tagAt L i = 2
    simp only [tagAt]; rw [hd]; simp [codeNodes]
  | right =>
    intro i hi h
    have hd := head_flat h
    refine (cRight_iff L _).mpr ?_
    change tagAt L i = 3
    simp only [tagAt]; rw [hd]; simp [codeNodes]
  | pair cf cg ihf ihg =>
    intro i hi h
    have hd : L.getD i nodeNone = (4, 1, (codeNodes cf).length + 1) := by
      have := head_flat h; simpa [codeNodes] using this
    have hf : Seg L (codeNodes cf) (i + 1) := h.tail.appendLeft
    have hg : Seg L (codeNodes cg) (i + 1 + (codeNodes cf).length) := h.tail.appendRight
    have hbf : i + 1 < L.length + 1 := by have := hf.1; have := flat_length_pos cf; omega
    have hbg : i + 1 + (codeNodes cf).length < L.length + 1 := by
      have := hg.1; have := flat_length_pos cg; omega
    have h1 : off1At L i = 1 := by simp only [off1At]; rw [hd]
    have h2 : off2At L i = (codeNodes cf).length + 1 := by simp only [off2At]; rw [hd]
    have ht : tagAt L i = 4 := by simp only [tagAt]; rw [hd]
    have ha1 : CArg1 (⟨i, hi⟩ : (listStruct L).Univ) ⟨i + 1, hbf⟩ := by
      refine (cArg1_iff L _ _).mpr ⟨?_, ?_⟩
      · change off1At L i ≠ 0
        rw [h1]; omega
      · change i + 1 = i + off1At L i
        rw [h1]
    have ha2 : CArg2 (⟨i, hi⟩ : (listStruct L).Univ) ⟨i + 1 + (codeNodes cf).length, hbg⟩ := by
      refine (cArg2_iff L _ _).mpr ⟨?_, ?_⟩
      · change off2At L i ≠ 0
        rw [h2]; omega
      · change i + 1 + (codeNodes cf).length = i + off2At L i
        rw [h2]; omega
    exact ⟨(cPair_iff L _).mpr ht, ⟨i + 1, hbf⟩, ⟨i + 1 + (codeNodes cf).length, hbg⟩,
      ha1, ha2, ihf _ hbf hf, ihg _ hbg hg⟩
  | comp cf cg ihf ihg =>
    intro i hi h
    have hd : L.getD i nodeNone = (5, 1, (codeNodes cf).length + 1) := by
      have := head_flat h; simpa [codeNodes] using this
    have hf : Seg L (codeNodes cf) (i + 1) := h.tail.appendLeft
    have hg : Seg L (codeNodes cg) (i + 1 + (codeNodes cf).length) := h.tail.appendRight
    have hbf : i + 1 < L.length + 1 := by have := hf.1; have := flat_length_pos cf; omega
    have hbg : i + 1 + (codeNodes cf).length < L.length + 1 := by
      have := hg.1; have := flat_length_pos cg; omega
    have h1 : off1At L i = 1 := by simp only [off1At]; rw [hd]
    have h2 : off2At L i = (codeNodes cf).length + 1 := by simp only [off2At]; rw [hd]
    have ht : tagAt L i = 5 := by simp only [tagAt]; rw [hd]
    have ha1 : CArg1 (⟨i, hi⟩ : (listStruct L).Univ) ⟨i + 1, hbf⟩ := by
      refine (cArg1_iff L _ _).mpr ⟨?_, ?_⟩
      · change off1At L i ≠ 0
        rw [h1]; omega
      · change i + 1 = i + off1At L i
        rw [h1]
    have ha2 : CArg2 (⟨i, hi⟩ : (listStruct L).Univ) ⟨i + 1 + (codeNodes cf).length, hbg⟩ := by
      refine (cArg2_iff L _ _).mpr ⟨?_, ?_⟩
      · change off2At L i ≠ 0
        rw [h2]; omega
      · change i + 1 + (codeNodes cf).length = i + off2At L i
        rw [h2]; omega
    exact ⟨(cComp_iff L _).mpr ht, ⟨i + 1, hbf⟩, ⟨i + 1 + (codeNodes cf).length, hbg⟩,
      ha1, ha2, ihf _ hbf hf, ihg _ hbg hg⟩
  | prec cf cg ihf ihg =>
    intro i hi h
    have hd : L.getD i nodeNone = (6, 1, (codeNodes cf).length + 1) := by
      have := head_flat h; simpa [codeNodes] using this
    have hf : Seg L (codeNodes cf) (i + 1) := h.tail.appendLeft
    have hg : Seg L (codeNodes cg) (i + 1 + (codeNodes cf).length) := h.tail.appendRight
    have hbf : i + 1 < L.length + 1 := by have := hf.1; have := flat_length_pos cf; omega
    have hbg : i + 1 + (codeNodes cf).length < L.length + 1 := by
      have := hg.1; have := flat_length_pos cg; omega
    have h1 : off1At L i = 1 := by simp only [off1At]; rw [hd]
    have h2 : off2At L i = (codeNodes cf).length + 1 := by simp only [off2At]; rw [hd]
    have ht : tagAt L i = 6 := by simp only [tagAt]; rw [hd]
    have ha1 : CArg1 (⟨i, hi⟩ : (listStruct L).Univ) ⟨i + 1, hbf⟩ := by
      refine (cArg1_iff L _ _).mpr ⟨?_, ?_⟩
      · change off1At L i ≠ 0
        rw [h1]; omega
      · change i + 1 = i + off1At L i
        rw [h1]
    have ha2 : CArg2 (⟨i, hi⟩ : (listStruct L).Univ) ⟨i + 1 + (codeNodes cf).length, hbg⟩ := by
      refine (cArg2_iff L _ _).mpr ⟨?_, ?_⟩
      · change off2At L i ≠ 0
        rw [h2]; omega
      · change i + 1 + (codeNodes cf).length = i + off2At L i
        rw [h2]; omega
    exact ⟨(cPrec_iff L _).mpr ht, ⟨i + 1, hbf⟩, ⟨i + 1 + (codeNodes cf).length, hbg⟩,
      ha1, ha2, ihf _ hbf hf, ihg _ hbg hg⟩
  | rfind' cf ihf =>
    intro i hi h
    have hd : L.getD i nodeNone = (7, 1, 0) := by
      have := head_flat h; simpa [codeNodes] using this
    have hf : Seg L (codeNodes cf) (i + 1) := h.tail
    have hbf : i + 1 < L.length + 1 := by have := hf.1; have := flat_length_pos cf; omega
    have h1 : off1At L i = 1 := by simp only [off1At]; rw [hd]
    have ht : tagAt L i = 7 := by simp only [tagAt]; rw [hd]
    have ha1 : CArg1 (⟨i, hi⟩ : (listStruct L).Univ) ⟨i + 1, hbf⟩ := by
      refine (cArg1_iff L _ _).mpr ⟨?_, ?_⟩
      · change off1At L i ≠ 0
        rw [h1]; omega
      · change i + 1 = i + off1At L i
        rw [h1]
    exact ⟨(cRfind_iff L _).mpr ht, ⟨i + 1, hbf⟩, ha1, ihf _ hbf hf⟩

/-- The root of the instance a code draws does draw that code. -/
theorem decodesTo_root (c : Nat.Partrec.Code) :
    DecodesTo (⟨0, by simp⟩ : (codeStruct c).Univ) c :=
  decodesTo_of_seg (codeNodes c) c 0 (by simp) (seg_self (codeNodes c))

/-! ### The instance a code draws is well formed -/

/-- The tag number a constructor tag is drawn with. -/
def tagNum : CodeTag → ℕ
  | .zero => 0
  | .succ => 1
  | .left => 2
  | .right => 3
  | .pair => 4
  | .comp => 5
  | .prec => 6
  | .rfind => 7

theorem mark_iff (L : List (ℕ × ℕ × ℕ)) (t : CodeTag) (a : (listStruct L).Univ) :
    Mark t a ↔ tagAt L a = tagNum t := by
  cases t
  · exact cZero_iff L a
  · exact cSucc_iff L a
  · exact cLeft_iff L a
  · exact cRight_iff L a
  · exact cPair_iff L a
  · exact cComp_iff L a
  · exact cPrec_iff L a
  · exact cRfind_iff L a

theorem codeWF_listStruct (L : List (ℕ × ℕ × ℕ)) : CodeWF (listStruct L).Univ where
  exclusive a t t' h1 h2 := by
    have e1 := (mark_iff L t a).mp h1
    have e2 := (mark_iff L t' a).mp h2
    have heq : tagNum t = tagNum t' := by rw [← e1, ← e2]
    cases t <;> cases t' <;> first | rfl | exact absurd heq (by simp [tagNum])
  arg1_fun a b b' h1 h2 :=
    Fin.ext (((cArg1_iff L a b).mp h1).2.trans ((cArg1_iff L a b').mp h2).2.symm)
  arg2_fun a b b' h1 h2 :=
    Fin.ext (((cArg2_iff L a b).mp h1).2.trans ((cArg2_iff L a b').mp h2).2.symm)

/-! ### The instance draws the code, and nothing else -/

/-- **The instance a code draws is a yes-instance exactly when the code halts
on `0`.** -/
theorem codehalt_codeStruct (c : Nat.Partrec.Code) :
    CODEHALT (codeStruct c).Univ ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  constructor
  · rintro ⟨n, c', hr, hd, hh⟩
    have hn : n = ⟨0, by simp⟩ := Fin.ext ((cRoot_iff _ n).mp hr)
    subst hn
    have hc := decodesTo_unique (codeWF_listStruct (codeNodes c)) c c' _ (decodesTo_root c) hd
    rwa [← hc] at hh
  · intro hh
    exact ⟨⟨0, by simp⟩, c, (cRoot_iff _ _).mpr rfl, decodesTo_root c, hh⟩

theorem codehalt_toPred_codeStruct (c : Nat.Partrec.Code) :
    CODEHALT.toPred codeVocab (codeStruct c) ↔ (Nat.Partrec.Code.eval c 0).Dom :=
  codehalt_codeStruct c

/-! ### The map is primitive recursive -/

theorem primrec_flat : Primrec codeNodes := by
  have hmk : ∀ t : ℕ, Primrec fun a : Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code ×
      List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) =>
      ((t, 1, a.2.2.2.1.length + 1) :: (a.2.2.2.1 ++ a.2.2.2.2)) := by
    intro t
    have hf : Primrec fun a : Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code ×
        List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) => a.2.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hg : Primrec fun a : Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code ×
        List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) => a.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact Primrec.list_cons.comp
      ((Primrec.const t).pair ((Primrec.const 1).pair
        (Primrec.succ.comp (Primrec.list_length.comp hf))))
      (Primrec.list_append.comp hf hg)
  have hrf : Primrec fun a : Nat.Partrec.Code × Nat.Partrec.Code × List (ℕ × ℕ × ℕ) =>
      (((7 : ℕ), (1 : ℕ), (0 : ℕ)) :: a.2.2) :=
    Primrec.list_cons.comp (Primrec.const _) (Primrec.snd.comp Primrec.snd)
  have key := Nat.Partrec.Code.primrec_recOn
    (c := fun a : Nat.Partrec.Code => a) (hc := Primrec.id)
    (z := fun _ => [((0 : ℕ), (0 : ℕ), (0 : ℕ))]) (hz := Primrec.const _)
    (s := fun _ => [((1 : ℕ), (0 : ℕ), (0 : ℕ))]) (hs := Primrec.const _)
    (l := fun _ => [((2 : ℕ), (0 : ℕ), (0 : ℕ))]) (hl := Primrec.const _)
    (r := fun _ => [((3 : ℕ), (0 : ℕ), (0 : ℕ))]) (hr := Primrec.const _)
    (pr := fun _ _ _ hf hg => ((4 : ℕ), (1 : ℕ), hf.length + 1) :: (hf ++ hg)) (hpr := hmk 4)
    (co := fun _ _ _ hf hg => ((5 : ℕ), (1 : ℕ), hf.length + 1) :: (hf ++ hg)) (hco := hmk 5)
    (pc := fun _ _ _ hf hg => ((6 : ℕ), (1 : ℕ), hf.length + 1) :: (hf ++ hg)) (hpc := hmk 6)
    (rf := fun _ _ hf => ((7 : ℕ), (1 : ℕ), (0 : ℕ)) :: hf) (hrf := hrf)
  refine key.of_eq fun c => ?_
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair cf cg ihf ihg => simp only [codeNodes]; rw [← ihf, ← ihg]
  | comp cf cg ihf ihg => simp only [codeNodes]; rw [← ihf, ← ihg]
  | prec cf cg ihf ihg => simp only [codeNodes]; rw [← ihf, ← ihg]
  | rfind' cf ihf => simp only [codeNodes]; rw [← ihf]

theorem primrec_codeStruct : Primrec codeStruct := by
  have hflat : Primrec codeNodes := primrec_flat
  have hlen : Primrec fun c : Nat.Partrec.Code => (codeNodes c).length :=
    Primrec.list_length.comp hflat
  have hdig : ∀ j : ℕ, Primrec fun q : Nat.Partrec.Code × ℕ =>
      digitAt ((codeNodes q.1).length + 1) q.2 j := fun j =>
    (FirstOrder.Language.primrec_digitAt j).comp
      (Primrec.succ.comp (hlen.comp Primrec.fst)) Primrec.snd
  have hnode : ∀ j : ℕ, Primrec fun q : Nat.Partrec.Code × ℕ =>
      (codeNodes q.1).getD (digitAt ((codeNodes q.1).length + 1) q.2 j) nodeNone := fun j =>
    (Primrec.list_getD nodeNone).comp (hflat.comp Primrec.fst) (hdig j)
  have htag : Primrec fun q : Nat.Partrec.Code × ℕ =>
      tagAt (codeNodes q.1) (digitAt ((codeNodes q.1).length + 1) q.2 0) :=
    Primrec.fst.comp (hnode 0)
  have hoff1 : Primrec fun q : Nat.Partrec.Code × ℕ =>
      off1At (codeNodes q.1) (digitAt ((codeNodes q.1).length + 1) q.2 0) :=
    Primrec.fst.comp (Primrec.snd.comp (hnode 0))
  have hoff2 : Primrec fun q : Nat.Partrec.Code × ℕ =>
      off2At (codeNodes q.1) (digitAt ((codeNodes q.1).length + 1) q.2 0) :=
    Primrec.snd.comp (Primrec.snd.comp (hnode 0))
  refine ((FinStruct.primrec_mk codeVocab).comp hlen (Primrec.list_ofFn ?_)).of_eq fun _ => rfl
  intro i'
  refine Primrec.list_map
    (Primrec.list_range.comp
      ((FirstOrder.Language.primrec_pow_const (codeVocab.arity i')).comp
        (Primrec.succ.comp hlen))) ?_
  fin_cases i'
  · exact ((Primrec.eq.comp (hdig 0) (Primrec.const 0)).decide).of_eq fun _ => rfl
  · exact ((Primrec.eq.comp htag (Primrec.const 0)).decide).of_eq fun _ => rfl
  · exact ((Primrec.eq.comp htag (Primrec.const 1)).decide).of_eq fun _ => rfl
  · exact ((Primrec.eq.comp htag (Primrec.const 2)).decide).of_eq fun _ => rfl
  · exact ((Primrec.eq.comp htag (Primrec.const 3)).decide).of_eq fun _ => rfl
  · exact ((Primrec.eq.comp htag (Primrec.const 4)).decide).of_eq fun _ => rfl
  · exact ((Primrec.eq.comp htag (Primrec.const 5)).decide).of_eq fun _ => rfl
  · exact ((Primrec.eq.comp htag (Primrec.const 6)).decide).of_eq fun _ => rfl
  · exact ((Primrec.eq.comp htag (Primrec.const 7)).decide).of_eq fun _ => rfl
  · exact (((PrimrecPred.not (Primrec.eq.comp hoff1 (Primrec.const 0))).and
      (Primrec.eq.comp (hdig 1) (Primrec.nat_add.comp (hdig 0) hoff1))).decide).of_eq
      fun _ => rfl
  · exact (((PrimrecPred.not (Primrec.eq.comp hoff2 (Primrec.const 0))).and
      (Primrec.eq.comp (hdig 1) (Primrec.nat_add.comp (hdig 0) hoff2))).decide).of_eq
      fun _ => rfl

/-! ### Undecidability -/

/-- **CODEHALT is undecidable.** Mathlib's halting problem maps into it by the
tree encoding, which is primitive recursive, so a decision procedure for the
concrete instances would decide whether a partial recursive code halts. -/
theorem not_computablePred_codehalt : ¬ComputablePred (CODEHALT.toPred codeVocab) := by
  intro h
  refine ComputablePred.halting_problem 0 ?_
  obtain ⟨D, hD⟩ := h
  refine ComputablePred.of_eq (p := fun c : Nat.Partrec.Code =>
    CODEHALT.toPred codeVocab (codeStruct c))
    ⟨fun c => D _, hD.comp primrec_codeStruct.to_comp⟩ ?_
  intro c
  exact codehalt_toPred_codeStruct c

/-- **An RE-hard problem is undecidable.** Hardness in this library is cofinal,
so an RE-hard problem is in particular a target of `CODEHALT`, which is
undecidable; and a first-order reduction is a computable many-one reduction of
the induced sets
(`DescriptiveComplexity.not_computablePred_of_relOrderedReduction`).

This is the leverage the whole `DescriptiveComplexity.Computability` layer
exists for: every completeness theorem for RE now yields undecidability with no
computability work of its own. -/
theorem not_computablePred_of_RE_hard {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} (hP : RE.Hard P) (V : FinVocab L) :
    ¬ComputablePred (P.toPred V) := by
  obtain ⟨f⟩ := (hard_RE_iff P).mp hP CODEHALT codehalt_mem_RE
  exact not_computablePred_of_relOrderedReduction f codeVocab V not_computablePred_codehalt

/-- **Trakhtenbrot's theorem**: whether a first-order sentence has a *finite*
model is undecidable. -/
theorem finsat_not_computable : ¬ComputablePred (FINSAT.toPred finsatVocab) :=
  not_computablePred_of_RE_hard finsat_RE_hard finsatVocab

end DescriptiveComplexity
