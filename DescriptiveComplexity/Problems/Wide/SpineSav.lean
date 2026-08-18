/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxSpineSem

/-!
# The two scratch registers are parked at the marker

`DescriptiveComplexity.Draw.DrawData.ixLegStB_fields` says a leg of the spine
leaves the mirror, the working register, the bottom mark, the stage tracks and
the last-pass flag alone. It says nothing about the two *scratch* registers, SAV
and TARGET, because a leg does write them – and the evaluation's exit asks that
they be back at the marker when the spine is over (`hsavL`, `htgtL`).

This file closes that: an atom parks both at the marker when it is a stage atom
and touches neither otherwise (`ixKindEndSt`), so a state entered with them
parked leaves with them parked, and the property rides the matrix's chain, the
round, the VAL loop's thread and the whole branched spine. The marker being the
empty address, the entry state has them parked for free.
-/

namespace DescriptiveComplexity

namespace Draw

namespace DrawData

open FirstOrder

open Language Structure

section Parked

variable {L : Language.{0, 0}} {dt : DrawData L} {A R P I : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P] [Finite I] [Nonempty A]
variable [L.IsRelational] [L.Structure A] [Finite dt.KIx]
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable {v : Univ A R P dt.KIx dt.dd → Prop}

variable (dt) in
/-- **Both scratch registers are parked at the marker.** -/
def Parked (st : TapeSt dt A R P I) (elt : I → Univ A R P dt.KIx dt.dd)
    (v : Univ A R P dt.KIx dt.dd → Prop) : Prop :=
  st.sav = ixMark elt v ∧ st.tgt = ixMark elt v

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A]
  [Finite R] [Finite P] [Finite I] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **An atom leaves the scratch parked**: a stage atom parks both registers at
the marker, and every other kind touches neither. -/
theorem parked_ixKindEndSt {vi : dt.VarIx} {st : TapeSt dt A R P I}
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi)) (hst : dt.Parked st elt v) :
    dt.Parked (dt.ixKindEndSt (elt := elt) vi v κ st) elt v := by
  cases κ with
  | stage _ _ => exact ⟨rfl, rfl⟩
  | _ => exact hst

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A]
  [Finite R] [Finite P] [Finite I] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **The matrix's chain leaves the scratch parked.** -/
theorem parked_ixMatSt {vi : dt.VarIx} {st : TapeSt dt A R P I}
    (hst : dt.Parked st elt v) (n : ℕ) :
    dt.Parked (dt.ixMatSt (elt := elt) vi st v n) elt v := by
  induction n with
  | zero => exact hst
  | succ n ih =>
    rw [ixMatSt]
    split
    · exact parked_ixKindEndSt _ ih
    · exact ih

end Parked

section Round

variable {L : Language.{0, 0}} {dt : DrawData L} {A R P I : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P] [Finite I] [Nonempty A]
variable [L.IsRelational] [L.Structure A] [Finite dt.KIx]
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable {v : Univ A R P dt.KIx dt.dd → Prop}
variable {F : LaidFile dt A R P I} {zero one : A}
variable {hhas : F.toLayout.HasName zero}

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite I] [Finite dt.KIx] in
/-- **A round leaves the scratch parked**: it is the matrix's chain when the
gates pass and the identity when they do not. -/
theorem parked_ixRoundEndSt {vi : dt.VarIx} {stV : TapeSt dt A R P I}
    (hst : dt.Parked stV elt v) (f₀ : dt.CtlIx → A) :
    dt.Parked (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀) elt v := by
  rw [ixRoundEndSt]
  split
  · exact parked_ixMatSt hst _
  · exact hst

end Round

/-! ### Up the tower: the VAL loop, the leg and the spine -/

section Tower

variable {L : Language.{0, 0}} {dt : DrawData L} {A R P I : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P] [Finite I] [Nonempty A]
variable [L.IsRelational] [L.Structure A] [Finite dt.KIx]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable {v : Univ A R P dt.KIx dt.dd → Prop}
variable (F : LaidFile dt A R P I)
variable (hinj : Function.Injective elt) (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}
variable (mV : ιV → I → Prop)

omit [Finite R] [Finite P] [Finite I] [Finite dt.KIx] [Finite ιV] in
/-- **The VAL loop's thread leaves the scratch parked**: the pair it carries is
the round's, and a round parks both registers. -/
theorem parked_ixVarSTT {vi : dt.VarIx} {st : TapeSt dt A R P I}
    {semT : ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf vi),
        dt.IxKindSem PR.zero PR.one vi
          (dt.ixMatSt (elt := elt) vi (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf vi b)}
    (hst : dt.Parked st elt v) (fG : dt.CtlIx → A) (a : ιV) :
    (dt.ixVarSTT (PR := PR) (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).1 =
        ixMark elt v ∧
      (dt.ixVarSTT (PR := PR) (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).2 =
        ixMark elt v := by
  rw [ixVarSTT, ixVarPairT]
  refine iterOrd_invariant (Inv := fun q : IxScratch dt A R P I × (dt.CtlIx → A) =>
    q.1.1 = ixMark elt v ∧ q.1.2 = ixMark elt v) ⟨hst.1, hst.2⟩ (fun b q hq => ?_) a
  exact parked_ixRoundEndSt (elt := elt) (F := F) (hhas := hhasP)
    (stV := dt.ixVarRdSt st q.1 (mV b)) ⟨hq.1, hq.2⟩ q.2

omit [Finite R] [Finite P] [Finite I] [Finite dt.KIx] [Finite ιV] in
/-- **A VAL round's exit state leaves the scratch parked.** -/
theorem parked_ixVarStE {vi : dt.VarIx} {st : TapeSt dt A R P I}
    {semT : ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf vi),
        dt.IxKindSem PR.zero PR.one vi
          (dt.ixMatSt (elt := elt) vi (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf vi b)}
    (hst : dt.Parked st elt v) (fG : dt.CtlIx → A) (a : ιV) :
    dt.Parked (dt.ixVarStE (PR := PR) (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)
      elt v := by
  rw [ixVarStE]
  refine parked_ixRoundEndSt (elt := elt) (F := F) (hhas := hhasP) ?_ _
  obtain ⟨h1, h2⟩ := parked_ixVarSTT (PR := PR) F hinj hhasP heltP mV
    (semT := semT) hst fG a
  exact ⟨h1, h2⟩

omit [Finite R] [Finite P] [Finite I] [Finite dt.KIx] [Finite ιV] in
/-- **A leg leaves the scratch parked**: gated, it is the VAL loop's exit state
with the stage bit written; ungated, it writes nothing but that bit. -/
theorem parked_ixLegStB {j : Fin dt.nv} {st : TapeSt dt A R P I}
    {semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
      ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b)}
    (hst : dt.Parked st elt v) (f₀ : dt.CtlIx → A) :
    dt.Parked (dt.ixLegStB (PR := PR) (elt := elt) (v := v) (aT := aT)
      F hinj hhasP heltP mV j st semT f₀) elt v := by
  classical
  rw [ixLegStB]
  split
  · exact parked_ixVarStE (PR := PR) F hinj hhasP heltP mV hst _ aT
  · exact hst

omit [Finite R] [Finite P] [Finite I] [Finite dt.KIx] [Finite ιV] in
/-- **The branched spine leaves the scratch parked**, position by position: the
`hsavL` and `htgtL` an evaluation's exit asks for, at any file. -/
theorem parked_ixSpineStOfB {st₀ : TapeSt dt A R P I} {f₀ : dt.CtlIx → A}
    {semB : ∀ (w : Univ A R P dt.KIx dt.dd → Prop) (j : Fin dt.nv)
      (st : TapeSt dt A R P I),
      dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
      ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b)}
    (hst₀ : dt.Parked st₀ elt v) (k : Fin (dt.nv + 1)) :
    dt.Parked (dt.ixSpineStOfB (PR := PR) (elt := elt) (v := v) (aT := aT)
      F hinj hhasP heltP mV st₀ f₀ semB k) elt v := by
  have hn : ∀ n : ℕ, dt.Parked (dt.ixSpineNodeB (PR := PR) (elt := elt) (v := v)
      (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB n).1 elt v := by
    intro n
    induction n with
    | zero => exact hst₀
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dif_pos hm]
        exact parked_ixLegStB (PR := PR) F hinj hhasP heltP mV ih _
      · rw [dif_neg hm]
        exact ih
  exact hn (k : ℕ)

end Tower

end DrawData

end Draw

end DescriptiveComplexity
