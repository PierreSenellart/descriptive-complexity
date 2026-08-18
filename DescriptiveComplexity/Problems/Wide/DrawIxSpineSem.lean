/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxVerdict
import DescriptiveComplexity.Problems.Wide.DrawIxPack
import DescriptiveComplexity.Problems.Wide.DrawSpineSem
import DescriptiveComplexity.Problems.Wide.DrawIxEval

/-!
# What the spine does to the tape, at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawSpineSem` read at a coarse file: what a
whole spine leaves on the tape at one address, the sweep's fold over the
addresses, and the semantic packs the positions are run with.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable {P : Type}
variable [LinearOrder (P)]
variable [Language.wide.Structure
  (Univ A R (P) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (P)]
variable {PR : Prog A R (P) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}
variable {I : Type} [Finite I]
variable (F : LaidFile dt A R (P) I)
variable {elt : I → Univ A R (P) dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)
variable {e₀ : Univ A R (P) dt.KIx dt.dd}
variable (he₀ : ∀ y, WMLe e₀ y)
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R (P) dt.KIx dt.dd),
  Use u → WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]
-- The marks-to-shapes bridge at a coarse file (see `DrawIxRoundSem`).
variable (hpassEnc : ∀ (vi : dt.VarIx)
    (stV : TapeSt dt A R (P) I)
    (ℓ : Fin (dt.nIn vi)),
  dt.ixIGPassP (elt := elt) F PR.zero PR.one vi stV ℓ ↔
    IsEnc dt.ly PR.zero PR.one (wmBlk (ixAddr elt stV.val)
      (Tag.arg (toLex (dt.igBlk vi ℓ)) :
        Tag R (P) dt.KIx)))
-- The gates' marks-to-shapes bridge at a coarse file: a position is gated
-- exactly when the blocks of its mirror's **address** below the variable's
-- arity are encodings. Free at the elementwise file
-- (`DescriptiveComplexity.Draw.Data.isEnc_of_gatedAt` and its converse).
variable (hgateEnc : ∀ (j : Fin dt.nv)
    (st : TapeSt dt A R (P) I),
  dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st ↔
    ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      IsEnc dt.ly PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (P) dt.KIx)))
variable [Finite dt.KIx]

/-! ### One position's write -/

variable {v : Univ A R (P) dt.KIx dt.dd → Prop}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
open Classical in
/-- **What a position writes**: the variable's cell at the marker, nothing
else. -/
theorem ixNew_postVarSt (st : TapeSt dt A R (P) I)
    (m : I → Prop)
    (i' i : dt.d.B.ι) (b : Prop)
    (r : Univ A R (P) dt.KIx dt.dd → Prop) :
    (dt.ixPostVarSt v st m i b).new i' r =
      (if i' = i ∧ r = v then b else st.new i' r) := rfl

/-! ### The spine's writes -/

section Spine

variable {mOf : Fin dt.nv → (I → Prop)}
variable {stOf : Fin (dt.nv + 1) →
  TapeSt dt A R (P) I}
variable {bOf : Fin dt.nv → Prop}
variable (hst : ∀ j : Fin dt.nv, stOf j.succ =
  dt.ixPostVarSt v (stOf j.castSucc) (mOf j) (dt.varList.get j) (bOf j))

open Classical in
/-- **The only thing the `new` tracks need of a position**: its own cell at
the marker holds its verdict and every other cell rides. Weaker than the
cover equation `hst`, and weaker on purpose — a *branched* position's leg
is not literally a
`DescriptiveComplexity.Draw.Data.ixPostVarSt` of the position's entry
state (its VAL loop may normalize the two scratch registers first), while
this projection of it is
(`DescriptiveComplexity.Draw.Data.ixLegStB_new`). -/
abbrev IxWritesNew
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (P) I)
    (bOf : Fin dt.nv → Prop) : Prop :=
  ∀ (j : Fin dt.nv) (i' : dt.d.B.ι)
    (r : Univ A R (P) dt.KIx dt.dd → Prop),
    (stOf j.succ).new i' r =
      (if i' = dt.varList.get j ∧ r = v then bOf j
        else (stOf j.castSucc).new i' r)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
/-- The cover equation gives the projection. -/
theorem ixWritesNew_of_hst : dt.IxWritesNew (v := v) stOf bOf := by
  classical
  intro j i' r
  rw [hst j]
  rfl

variable (hstN : dt.IxWritesNew (v := v) stOf bOf)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
/-- **Anything a position's write leaves alone rides the whole spine**: the
induction along the positions, once, for every field but `val` and `new`. -/
theorem ixSpineRide {β : Sort _}
    (G : TapeSt dt A R (P) I → β)
    (hF : ∀ st m i b, G (dt.ixPostVarSt v st m i b) = G st)
    (k : Fin (dt.nv + 1)) :
    G (stOf k) = G (stOf 0) := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := hst ⟨n, hnv⟩
    exact Eq.trans (congrArg G hstep) (Eq.trans (hF _ _ _ _) (ih _))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
/-- The stage dictionary rides the spine. -/
theorem ixSpine_old (k : Fin (dt.nv + 1)) : (stOf k).old = (stOf 0).old :=
  dt.ixSpineRide hst (fun st => st.old) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
/-- The working address rides the spine. -/
theorem ixSpine_mir (k : Fin (dt.nv + 1)) : (stOf k).mir = (stOf 0).mir :=
  dt.ixSpineRide hst (fun st => st.mir) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
/-- The three markers ride the spine. -/
theorem ixSpine_wk (k : Fin (dt.nv + 1)) : (stOf k).wk = (stOf 0).wk :=
  dt.ixSpineRide hst (fun st => st.wk) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
theorem ixSpine_bot (k : Fin (dt.nv + 1)) : (stOf k).bot = (stOf 0).bot :=
  dt.ixSpineRide hst (fun st => st.bot) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
theorem ixSpine_ltp (k : Fin (dt.nv + 1)) : (stOf k).ltp = (stOf 0).ltp :=
  dt.ixSpineRide hst (fun st => st.ltp) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hstN in
/-- **Off the marker, the `new` tracks ride the spine**: a position writes
its own cell only. -/
theorem ixSpine_new_off (k : Fin (dt.nv + 1)) (i : dt.d.B.ι)
    {r : Univ A R (P) dt.KIx dt.dd → Prop}
    (hr : r ≠ v) : (stOf k).new i r ↔ (stOf 0).new i r := by
  classical
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := hstN ⟨n, hnv⟩ i r
    have hsucc : (⟨n, hnv⟩ : Fin dt.nv).succ = ⟨n + 1, hn⟩ := rfl
    have hcast : (⟨n, hnv⟩ : Fin dt.nv).castSucc =
        ⟨n, Nat.lt_succ_of_lt hnv⟩ := rfl
    rw [hsucc, hcast] at hstep
    exact (iff_of_eq (hstep.trans
      (if_neg (fun h : i = dt.varList.get ⟨n, hnv⟩ ∧ r = v => hr h.2)))).trans
      (ih _)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hstN in
/-- **At the marker, a variable's `new` cell is the verdict of its own
position**: it is written there, and no later position writes it, the
enumeration being duplicate-free. -/
theorem ixNew_last_get (j : Fin dt.nv) :
    (stOf (Fin.last dt.nv)).new (dt.varList.get j) v ↔ bOf j := by
  classical
  have key : ∀ (n : ℕ) (hn : n < dt.nv + 1) (j : Fin dt.nv), (j : ℕ) < n →
      ((stOf ⟨n, hn⟩).new (dt.varList.get j) v ↔ bOf j) := by
    intro n
    induction n with
    | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero _)
    | succ n ih =>
      intro hn j hj
      have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
      have hcong := hstN ⟨n, hnv⟩ (dt.varList.get j) v
      have hsucc : (⟨n, hnv⟩ : Fin dt.nv).succ = ⟨n + 1, hn⟩ := rfl
      have hcast : (⟨n, hnv⟩ : Fin dt.nv).castSucc =
          ⟨n, Nat.lt_succ_of_lt hnv⟩ := rfl
      rw [hsucc, hcast] at hcong
      rcases Nat.lt_or_ge (j : ℕ) n with hlt | hge
      · -- an earlier position: this write is at another variable
        have hne : dt.varList.get j ≠ dt.varList.get ⟨n, hnv⟩ := by
          intro hc
          have hjj : j = (⟨n, hnv⟩ : Fin dt.nv) := varList_get_inj hc
          exact absurd (congrArg Fin.val hjj) (show (j : ℕ) ≠ n by omega)
        exact (iff_of_eq (hcong.trans (if_neg
          (fun h : dt.varList.get j = dt.varList.get ⟨n, hnv⟩ ∧ v = v =>
            hne h.1)))).trans (ih _ j hlt)
      · -- this very position
        have hjn : j = (⟨n, hnv⟩ : Fin dt.nv) :=
          Fin.ext (show (j : ℕ) = n by omega)
        subst hjn
        exact iff_of_eq (hcong.trans (if_pos ⟨rfl, rfl⟩))
  exact key dt.nv (Nat.lt_succ_self _) j j.isLt

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hstN in
/-- **At an address every position rejects, the marker's `new` cells are
all clear** — the junk legs
(`DescriptiveComplexity.Draw.Data.ixVarLegFail_run`,
`DescriptiveComplexity.Draw.Data.ixVarLegUngated_run`) store `False`, which
is what the stage dictionary holds at an address that encodes no tuple. -/
theorem ixNew_last_of_false (hbOf : ∀ j : Fin dt.nv, ¬bOf j)
    (i : dt.d.B.ι) : ¬(stOf (Fin.last dt.nv)).new i v := by
  obtain ⟨j, hj⟩ := dt.exists_varList_get i
  subst hj
  exact fun hc => hbOf j ((dt.ixNew_last_get hstN j).mp hc)

end Spine

/-! ### The spine's semantic reading -/

section SpineNext

variable [LinearOrder (dt.X.Map A)]
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → I → Prop)
variable (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)

include hinj hhasP heltP hix hblkP hmono hup hpassEnc hUse in
omit [Finite I] [Finite dt.KIx] in
/-- **After the spine, one variable's `new` cell holds its own step of the
iteration** — the per-position form: only the position of that variable, its
pack and its verdict are named, so an address where *other* positions are
junk is covered too (which is what a sweep needs, the gates being per
variable). -/
theorem ixNew_last_next_at
    (hlin : IsLinOrd (WMLe (A := Univ A R (P)
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : Tag R (P) dt.KIx)
      (w : Fin dt.dd → A), ixAddr elt (mV a) (t, w) →
        ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (P) I}
    {bOf : Fin dt.nv → Prop} (j : Fin dt.nv)
    (semOfJ : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) elt (dt.kindOf (dt.varAt j) b))
    (fG : dt.CtlIx → A)
    (hstN : dt.IxWritesNew (v := v) stOf bOf)
    (hmirOf : (stOf j.castSucc).mir = (stOf 0).mir)
    (holdOf : (stOf j.castSucc).old = (stOf 0).old)
    (hbj : bOf j ↔
      dt.accVerdict PR.one (dt.polOf (dt.varAt j))
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP (dt.varAt j) (stOf j.castSucc) v mV semOfJ
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP
              (dt.varAt j) (stOf j.castSucc) v mV semOfJ fG aT) aT)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt (stOf j.castSucc) (mV aT)) v)))
    (mbW : Fin (dt.arOf (dt.varAt j)) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.ixMirBlk (elt := elt) (stOf 0) (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ))
    {Below : (Univ A R (P) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      ((stOf 0).old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP (dt.varAt j) ts
        { dt.ixRoundSt (stOf j.castSucc) (mV a) with sav := ixMark elt v }
        (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ)
      (b : Fin (dt.natOf (dt.varAt j)))
      (hmb' : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        wmBlk (ixAddr elt (dt.ixRoundSt (stOf j.castSucc) (mV a)).mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (P) dt.KIx) =
          encMap dt.ly PR.zero PR.one (mbW ℓ)),
      semOfJ a hp b = dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc) (dt.varAt j)
        (dt.ixRoundSt (stOf j.castSucc) (mV a)) hp mbW hmb' b) :
    (stOf (Fin.last dt.nv)).new (dt.varList.get j) v ↔
      dt.d.next σ (dt.varList.get j) mbW := by
  classical
  have hmbj : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.ixMirBlk (elt := elt) (stOf j.castSucc)
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ) := fun ℓ =>
    (congrFun (ixMirBlk_of_mir (elt := elt) hmirOf) _).trans (hmb _)
  have hdictj : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      ((stOf j.castSucc).old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x) :=
    fun iv x hs => (iff_of_eq (congrFun (congrFun holdOf iv) _)).trans
      (hdict iv x hs)
  refine (dt.ixNew_last_get hstN j).trans (hbj.trans ?_)
  exact ixAccVerdict_next (dt := dt) (elt := elt) (F := F) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
    (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc)
    (st := stOf j.castSucc) (mV := mV) (i := dt.varList.get j) (semOf := semOfJ)
    (hlin := hlin) (hord := hord) (hbotV := hbotV) (hmV0 := hmV0)
    (hUse := hUse) (hIncr := hIncr) (hKin := hKin) (hTop := hTop) (σ := σ)
    (mbW := mbW) (hmb := hmbj) (hdict := hdictj) (hbelow := hbelow)
    (hordP := hordP) (hsem := fun a hp b => hsem a hp b _) (fG := fG)

include hinj hhasP heltP hix hblkP hmono hup hpassEnc hUse in
omit [Finite I] [Finite dt.KIx] in
/-- **After the spine, every `new` track holds the next stage at the
address's points.** The position of a variable writes its verdict, which
`DescriptiveComplexity.Draw.Data.ixAccVerdict_next` reads as
`DescriptiveComplexity.StepDef.next`; the mirror and the dictionary ride
the spine, so the semantic hypotheses need only be given at the entry
state. -/
theorem ixNew_last_next
    (hlin : IsLinOrd (WMLe (A := Univ A R (P)
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : Tag R (P) dt.KIx)
      (w : Fin dt.dd → A), ixAddr elt (mV a) (t, w) →
        ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (P) I}
    {bOf : Fin dt.nv → Prop}
    (semOfJ : ∀ (j : Fin dt.nv) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) elt (dt.kindOf (dt.varAt j) b))
    (fGOf : Fin dt.nv → dt.CtlIx → A)
    (hstN : dt.IxWritesNew (v := v) stOf bOf)
    (hmirOf : ∀ k : Fin (dt.nv + 1), (stOf k).mir = (stOf 0).mir)
    (holdOf : ∀ k : Fin (dt.nv + 1), (stOf k).old = (stOf 0).old)
    (hbOf : ∀ j : Fin dt.nv, bOf j ↔
      dt.accVerdict PR.one (dt.polOf (dt.varAt j))
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
            (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP
              (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
              (fGOf j) aT) aT)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt (stOf j.castSucc) (mV aT)) v)))
    (pt : Fin dt.ko → dt.X.Map A)
    (hpt : ∀ k : Fin dt.ko,
      dt.ixMirBlk (elt := elt) (stOf 0) k = encMap dt.ly PR.zero PR.one (pt k))
    {Below : (Univ A R (P) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      ((stOf 0).old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP (dt.varAt j) ts
        { dt.ixRoundSt (stOf j.castSucc) (mV a) with sav := ixMark elt v }
        (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (j : Fin dt.nv) (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ)
      (b : Fin (dt.natOf (dt.varAt j)))
      (hmb' : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        wmBlk (ixAddr elt (dt.ixRoundSt (stOf j.castSucc) (mV a)).mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (P) dt.KIx) =
          encMap dt.ly PR.zero PR.one
            (pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))),
      semOfJ j a hp b = dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc) (dt.varAt j)
        (dt.ixRoundSt (stOf j.castSucc) (mV a)) hp
        (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ)) hmb' b)
    (i : dt.d.B.ι) :
    (stOf (Fin.last dt.nv)).new i v ↔
      dt.d.next σ i
        (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (some i)) ℓ)) := by
  classical
  obtain ⟨j, hj⟩ := dt.exists_varList_get i
  subst hj
  exact ixNew_last_next_at (dt := dt) (elt := elt) (F := F) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
    (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc) (mV := mV)
    (hUse := hUse) (hlin := hlin) (hord := hord) (hbotV := hbotV)
    (hmV0 := hmV0) (hIncr := hIncr) (hKin := hKin) (hTop := hTop) (σ := σ)
    (j := j) (semOfJ := semOfJ j) (fG := fGOf j) (hstN := hstN)
    (hmirOf := hmirOf j.castSucc) (holdOf := holdOf j.castSucc) (hbj := hbOf j)
    (mbW := fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
    (hmb := fun ℓ => hpt _) (hdict := hdict) (hbelow := hbelow j)
    (hordP := hordP) (hsem := fun a hp b hmb' => hsem j a hp b hmb')

end SpineNext

/-! ### What a whole sweep leaves behind -/

section SweepDict

variable {v : Univ A R (P) dt.KIx dt.dd → Prop}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **A sweep rewrites the `new` tracks of exactly the addresses it has
passed.** The address-by-address induction
(`DescriptiveComplexity.holds_of_wideRounds`) over the two facts one
address contributes — its own cell now holds the target (`hat`, which
`ixNew_last_next` and `ixNew_last_of_false` supply), every other cell is
untouched (`hoff`, which `ixSpine_new_off` supplies) — with the entry state
of the next address read off the sweep's own tape family (`hSW`, the
`hSW` of `DescriptiveComplexity.Draw.Data.reaches_sweep`).

Below the address reached, the tracks are the target; elsewhere they are
still the sweep's initial ones. Stated for an arbitrary target family `N`,
so the same lemma serves the stage sweep (`N` the dictionary of
`d.next σ`) and any other. -/
theorem ixSweep_new
    (hlin : IsLinOrd (WMLe (A := Univ A R (P)
      dt.KIx dt.dd)))
    {s₀ s₁ : Univ A R (P) dt.KIx dt.dd → Prop}
    {SW stE : (Univ A R (P) dt.KIx dt.dd →
      Prop) → TapeSt dt A R (P) I}
    {N : dt.d.B.ι →
      (Univ A R (P) dt.KIx dt.dd → Prop) → Prop}
    (hat : ∀ w, WMSetLe WMLe s₀ w → WMSetLt WMLe w s₁ →
      ∀ i, ((stE w).new i w ↔ N i w))
    (hoff : ∀ w, WMSetLe WMLe s₀ w → WMSetLt WMLe w s₁ →
      ∀ (i : dt.d.B.ι) (r : Univ A R (P)
        dt.KIx dt.dd → Prop), r ≠ w → ((stE w).new i r ↔ (SW w).new i r))
    (hSW : ∀ w w', WMIncr WMLe w w' → WMSetLe WMLe s₀ w →
      WMSetLe WMLe w' s₁ → SW w' = { dt.atSt (stE w) w' with mir := ixMark elt w' }) :
    ∀ w, WMSetLe WMLe s₀ w → WMSetLe WMLe w s₁ →
      (∀ (i : dt.d.B.ι) (r : Univ A R (P)
          dt.KIx dt.dd → Prop),
        WMSetLe WMLe s₀ r → WMSetLt WMLe r w → ((SW w).new i r ↔ N i r)) ∧
      (∀ (i : dt.d.B.ι) (r : Univ A R (P)
          dt.KIx dt.dd → Prop),
        ¬(WMSetLe WMLe s₀ r ∧ WMSetLt WMLe r w) →
          ((SW w).new i r ↔ (SW s₀).new i r)) := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  refine holds_of_wideRounds hlin (Q := fun w =>
    (∀ (i : dt.d.B.ι) (r : Univ A R (P)
        dt.KIx dt.dd → Prop),
      WMSetLe WMLe s₀ r → WMSetLt WMLe r w → ((SW w).new i r ↔ N i r)) ∧
    (∀ (i : dt.d.B.ι) (r : Univ A R (P)
        dt.KIx dt.dd → Prop),
      ¬(WMSetLe WMLe s₀ r ∧ WMSetLt WMLe r w) →
        ((SW w).new i r ↔ (SW s₀).new i r)))
    ⟨fun i r hlb hlt => ?_, fun _ _ _ => Iff.rfl⟩ ?_
  · -- nothing is both above and strictly below the start
    exact absurd (hset.2.2.1 r s₀ ((wmSetLt_iff _ _).mp hlt).1 hlb)
      ((wmSetLt_iff _ _).mp hlt).2
  intro w w' hi hlb hub hQ
  -- the address just swept is in the stretch
  have hww' : WMSetLt WMLe w w' :=
    (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
  have hwS : WMSetLt WMLe w s₁ :=
    (wmSetLt_iff _ _).mpr
      ⟨hset.2.1 w w' s₁ (wmSetLe_of_wmIncr hi) hub, fun hc =>
        ne_of_wmIncr hi (hset.2.2.1 w w' (wmSetLe_of_wmIncr hi) (hc ▸ hub))⟩
  -- the next address's entry state carries the swept one's tracks
  have hnew : ∀ (i : dt.d.B.ι)
      (r : Univ A R (P) dt.KIx dt.dd → Prop),
      (SW w').new i r = (stE w).new i r := by
    intro i r
    rw [hSW w w' hi hlb hub]
    rfl
  refine ⟨fun i r hrlb hrlt => ?_, fun i r hout => ?_⟩
  · rw [hnew i r]
    rcases eq_or_ne r w with rfl | hne
    · exact hat r hlb hwS i
    · have hrw : WMSetLt WMLe r w :=
        (wmSetLt_iff _ _).mpr
          ⟨(wmSetLt_iff_of_wmIncr hlin hi r).mp hrlt, hne⟩
      exact (hoff w hlb hwS i r hne).trans (hQ.1 i r hrlb hrw)
  · rw [hnew i r]
    have hne : r ≠ w := fun hc => hout ⟨hc ▸ hlb, hc ▸ hww'⟩
    refine (hoff w hlb hwS i r hne).trans (hQ.2 i r fun hc => hout ⟨hc.1, ?_⟩)
    refine (wmSetLt_iff _ _).mpr ⟨hset.2.1 r w w'
      ((wmSetLt_iff _ _).mp hc.2).1 (wmSetLe_of_wmIncr hi), fun hrw => ?_⟩
    have hw'w : WMSetLe WMLe w' w := by
      rw [← hrw]
      exact ((wmSetLt_iff _ _).mp hc.2).1
    exact ne_of_wmIncr hi (hset.2.2.1 w w' (wmSetLe_of_wmIncr hi) hw'w)

end SweepDict

/-! ### The address's cell, in dictionary form -/

section AddrDict

variable [LinearOrder (dt.X.Map A)]
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → I → Prop)
variable (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)

omit [LinearOrder R] [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [Finite dt.KIx] in
omit [Finite I] in
/-- **At a junk address the cell and the dictionary are both empty**: the
legs store `False` (`ixNew_last_of_false`) and a track holds nothing where a
block below the variable's arity encodes no point
(`DescriptiveComplexity.Draw.not_trackOf_of_notEnc`), so the two readings
agree there too. -/
theorem ixNew_last_trackOf_of_junk
    {stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (P) I}
    {bOf : Fin dt.nv → Prop}
    (hstN : dt.IxWritesNew (v := v) stOf bOf)
    (hbOf : ∀ j : Fin dt.nv, ¬bOf j)
    (σ : dt.d.B.Assignment (dt.X.Map A)) (i : dt.d.B.ι)
    {ℓ₀ : Fin (dt.d.B.arity i)}
    (hℓ : ∀ p : dt.X.Map A,
      wmBlk v (argOut dt.ki (Fin.castLE (dt.arOf_le_ko (some i)) ℓ₀)) ≠
        encMap dt.ly PR.zero PR.one p) :
    ((stOf (Fin.last dt.nv)).new i v ↔
      trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i))
        (dt.d.next σ) v) :=
  iff_of_false (dt.ixNew_last_of_false hstN hbOf i)
    (not_trackOf_of_notEnc (dt.arOf_le_ko (some i)) (dt.d.next σ) hℓ)

include hinj hhasP heltP hix hblkP hmono hup hpassEnc hUse in
omit [Finite I] [Finite dt.KIx] in
/-- **At an encoded address the cell holds the dictionary of the next
stage**: `ixNew_last_next` read through
`DescriptiveComplexity.Draw.trackOf_of_blocks`, the sweep's mirror
invariant (`hmir`) turning the address's blocks into the ones the
machinery read. This is the form the sweep's induction
(`ixSweep_new`) consumes, and the form the *next* sweep's `hdict` is in. -/
theorem ixNew_last_trackOf
    (hlin : IsLinOrd (WMLe (A := Univ A R (P)
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : Tag R (P) dt.KIx)
      (w : Fin dt.dd → A), ixAddr elt (mV a) (t, w) →
        ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (P) I}
    {bOf : Fin dt.nv → Prop}
    (semOfJ : ∀ (j : Fin dt.nv) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) elt (dt.kindOf (dt.varAt j) b))
    (fGOf : Fin dt.nv → dt.CtlIx → A)
    (hstN : dt.IxWritesNew (v := v) stOf bOf)
    (hmirOf : ∀ k : Fin (dt.nv + 1), (stOf k).mir = (stOf 0).mir)
    (holdOf : ∀ k : Fin (dt.nv + 1), (stOf k).old = (stOf 0).old)
    (hbOf : ∀ j : Fin dt.nv, bOf j ↔
      dt.accVerdict PR.one (dt.polOf (dt.varAt j))
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
            (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP
              (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
              (fGOf j) aT) aT)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt (stOf j.castSucc) (mV aT)) v)))
    (pt : Fin dt.ko → dt.X.Map A) (hmir : ixAddr elt (stOf 0).mir = v)
    (hpt : ∀ k : Fin dt.ko,
      wmBlk v (argOut dt.ki k) = encMap dt.ly PR.zero PR.one (pt k))
    {Below : (Univ A R (P) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      ((stOf 0).old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP (dt.varAt j) ts
        { dt.ixRoundSt (stOf j.castSucc) (mV a) with sav := ixMark elt v }
        (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (j : Fin dt.nv) (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ)
      (b : Fin (dt.natOf (dt.varAt j)))
      (hmb' : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        wmBlk (ixAddr elt (dt.ixRoundSt (stOf j.castSucc) (mV a)).mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (P) dt.KIx) =
          encMap dt.ly PR.zero PR.one
            (pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))),
      semOfJ j a hp b = dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc) (dt.varAt j)
        (dt.ixRoundSt (stOf j.castSucc) (mV a)) hp
        (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ)) hmb' b)
    (i : dt.d.B.ι) :
    ((stOf (Fin.last dt.nv)).new i v ↔
      trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i))
        (dt.d.next σ) v) := by
  refine (ixNew_last_next (dt := dt) (elt := elt) (F := F) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
    (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc) (mV := mV)
    (hUse := hUse) (hlin := hlin) (hord := hord) (hbotV := hbotV)
    (hmV0 := hmV0) (hIncr := hIncr) (hKin := hKin) (hTop := hTop) (σ := σ)
    (semOfJ := semOfJ) (fGOf := fGOf) (hstN := hstN) (hmirOf := hmirOf)
    (holdOf := holdOf) (hbOf := hbOf) (pt := pt) (hpt := ?_) (hdict := hdict)
    (hbelow := hbelow) (hordP := hordP) (hsem := hsem) (i := i)).trans
    (trackOf_of_blocks PR.zero_ne_one (dt.arOf_le_ko (some i)) (dt.d.next σ)
      (fun ℓ => hpt _)).symm
  intro k
  change wmBlk (ixAddr elt (stOf 0).mir)
    (Tag.arg (toLex (Sum.inl k : Fin dt.ko ⊕ Fin dt.ki)) :
      Tag R (P) dt.KIx) = _
  rw [hmir]
  exact hpt k

end AddrDict

/-! ### The semantic pack, transported along the spine -/


/-! ### The per-position families, built -/

section Family

variable [LinearOrder (dt.X.Map A)]
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}
variable (mV : ιV → I → Prop)
variable (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)
variable (st₀ : TapeSt dt A R (P) I)
variable (f₀ : dt.CtlIx → A)
variable (sem₀ : ∀ (j : Fin dt.nv) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st₀ (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st₀ (mV a))
      elt (dt.kindOf (dt.varAt j) b))
variable (tOf : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)

/-- **One node of the spine**: the tape state, the proof that its mirror is
still the address's — which is what lets the *next* node build its pack —
and the control. The three have to be produced together: the pack a
position's leg needs is typed at that position's state, and is available
only because the mirror rode (`ixSpineSem`). -/
noncomputable def ixSpineNode :
    ℕ → Σ' st : TapeSt dt A R (P) I,
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := ixSpineNode n
    if h : n < dt.nv then
      let f' := dt.ixLegCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
        mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
        (dt.ixSpineSem F PR.zero PR.one (dt.varAt ⟨n, h⟩) mV (sem₀ ⟨n, h⟩)
          prev.2.1) prev.2.2
      ⟨dt.ixPostVarSt v prev.1 (mV aT) (dt.varList.get ⟨n, h⟩)
          ((dt.varArgsOf PR.zero PR.one (dt.varAt ⟨n, h⟩)).accBit f'),
        prev.2.1, f'⟩
    else prev

/-- The tape family of the spine. -/
noncomputable def ixSpineStOf (k : Fin (dt.nv + 1)) :
    TapeSt dt A R (P) I :=
  (dt.ixSpineNode (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf (k : ℕ)).1

/-- The control family of the spine. -/
noncomputable def ixSpineFsOf (k : Fin (dt.nv + 1)) : dt.CtlIx → A :=
  (dt.ixSpineNode (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ sem₀ tOf (k : ℕ)).2.2

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The mirror rides the built family** — by construction, not by the
after-the-fact induction of `ixSpine_mir`. -/
theorem ixSpineStOf_mir (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf k).mir = st₀.mir :=
  (dt.ixSpineNode (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ sem₀ tOf (k : ℕ)).2.1

/-- The packs of the built family: the entry state's, carried. -/
noncomputable def ixSpineSemOf (j : Fin dt.nv) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
        (dt.ixRoundSt (dt.ixSpineStOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf
          j.castSucc) (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixRoundSt (dt.ixSpineStOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
        mV st₀ f₀ sem₀ tOf
        j.castSucc) (mV a)) elt (dt.kindOf (dt.varAt j) b) :=
  dt.ixSpineSem F PR.zero PR.one (dt.varAt j) mV (sem₀ j)
    (dt.ixSpineStOf_mir (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf j.castSucc)
    a hp b

omit [Finite I] [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem ixSpineStOf_zero :
    dt.ixSpineStOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf 0 = st₀ := rfl

omit [Finite I] [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem ixSpineFsOf_zero :
    dt.ixSpineFsOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf 0 = f₀ := rfl

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The control's cover equation** — `ixEvalSpine_run`'s `hfs`. -/
theorem ixSpineFsOf_succ (j : Fin dt.nv) :
    dt.ixSpineFsOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf j.succ =
      dt.ixLegCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf j.castSucc)
        (tOf j)
        (dt.ixSpineSemOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf j)
        (dt.ixSpineFsOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf j.castSucc) := by
  change (dt.ixSpineNode (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf
    ((j : ℕ) + 1)).2.2 = _
  rw [ixSpineNode, dif_pos j.isLt]
  rfl

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The tape's cover equation** — `ixEvalSpine_run`'s `hst`. -/
theorem ixSpineStOf_succ (j : Fin dt.nv) :
    dt.ixSpineStOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf j.succ =
      dt.ixPostVarSt v
        (dt.ixSpineStOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf j.castSucc)
        (mV aT) (dt.varList.get j)
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.ixLegCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
            (dt.ixSpineStOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
              mV st₀ f₀ sem₀ tOf j.castSucc)
            (tOf j)
            (dt.ixSpineSemOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
              mV st₀ f₀ sem₀ tOf j)
            (dt.ixSpineFsOf (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf
              j.castSucc))) := by
  change (dt.ixSpineNode (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf
    ((j : ℕ) + 1)).1 = _
  rw [ixSpineNode, dif_pos j.isLt]
  rfl

/-! ### The per-position families, threaded -/

/-- **One node of the spine, threaded**: as
`DescriptiveComplexity.Draw.Data.ixSpineNode`, with the leg's own exit
state — SAV and TARGET as its VAL loop left them — instead of the
normalized one. The mirror still rides, which is what makes the next
position's pack exist. -/
noncomputable def ixSpineNodeT :
    ℕ → Σ' st : TapeSt dt A R (P) I,
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := ixSpineNodeT n
    if h : n < dt.nv then
      ⟨dt.ixLegStT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.ixSpineSemT F PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2,
        (dt.ixLegStT_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.ixSpineSemT F PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2).1.trans prev.2.1,
        dt.ixLegCtlT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.ixSpineSemT F PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2⟩
    else prev

/-- The threaded tape family of the spine. -/
noncomputable def ixSpineStOfT (k : Fin (dt.nv + 1)) :
    TapeSt dt A R (P) I :=
  (dt.ixSpineNodeT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf (k : ℕ)).1

/-- The threaded control family of the spine. -/
noncomputable def ixSpineFsOfT (k : Fin (dt.nv + 1)) : dt.CtlIx → A :=
  (dt.ixSpineNodeT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ sem₀ tOf (k : ℕ)).2.2

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The mirror rides the threaded family too** — by construction. -/
theorem ixSpineStOfT_mir (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf k).mir = st₀.mir :=
  (dt.ixSpineNodeT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ sem₀ tOf (k : ℕ)).2.1

/-- The packs of the threaded family: the address's entry state's,
transported to the loop's own states. -/
noncomputable def ixSpineSemOfT (j : Fin dt.nv)
    (p : IxScratch dt A R (P) I) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
        (dt.ixVarRdSt (dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf
          j.castSucc) p (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j)
        (dt.ixVarRdSt (dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf
          j.castSucc) p (mV a)) v (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b) :=
  dt.ixSpineSemT F PR.zero PR.one (dt.varAt j) (v := v) mV (sem₀ j)
    (dt.ixSpineStOfT_mir (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf j.castSucc)
    p a hp b

omit [Finite I] [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem ixSpineStOfT_zero :
    dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf 0 = st₀ := rfl

omit [Finite I] [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem ixSpineFsOfT_zero :
    dt.ixSpineFsOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf 0 = f₀ := rfl

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The threaded control's cover equation** — `ixEvalSpine_run_thread`'s
`hfs`. -/
theorem ixSpineFsOfT_succ (j : Fin dt.nv) :
    dt.ixSpineFsOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf j.succ =
      dt.ixLegCtlT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf j.castSucc)
        (tOf j)
        (dt.ixSpineSemOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf j)
        (dt.ixSpineFsOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf j.castSucc) := by
  change (dt.ixSpineNodeT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf
    ((j : ℕ) + 1)).2.2 = _
  rw [ixSpineNodeT, dif_pos j.isLt]
  rfl

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The threaded tape's cover equation** — `ixEvalSpine_run_thread`'s
`hst`. -/
theorem ixSpineStOfT_succ (j : Fin dt.nv) :
    dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf j.succ =
      dt.ixLegStT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf j.castSucc)
        (tOf j)
        (dt.ixSpineSemOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf j)
        (dt.ixSpineFsOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ sem₀ tOf j.castSucc) := by
  change (dt.ixSpineNodeT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf
    ((j : ℕ) + 1)).1 = _
  rw [ixSpineNodeT, dif_pos j.isLt]
  rfl

/-! ### The per-position families, branched

The threaded family above runs the gated leg at every position, which a
sweep cannot afford: it visits junk addresses too. The branched family
takes whichever of the three legs each position's own gates call for
(`DescriptiveComplexity.Draw.Data.ixLegStB`), and is otherwise the same
recursion — the mirror still rides, because no leg writes it.

Its semantic parameter is **not** the entry state's pack transported: it is
the *conditioned* family `DescriptiveComplexity.Draw.Data.ixGatedSem`
inhabits — a pack at every gated position of every state, at every address.
Conditioned, because at a junk position no pack exists (the argument blocks
encode nothing there); quantified over the address as well, because
`DescriptiveComplexity.Draw.Data.ixStEndB` runs this spine at `v := w` for
an address `w` its own binders are fixed before. With that type the
parameter is supplied outright at the top — `fun w => dt.ixGatedSem hzo hlin
mV` — and no semantic assumption about a position survives in the run
layer. -/

variable (semB : ∀ (w : Univ A R (P) dt.KIx
    dt.dd → Prop) (j : Fin dt.nv)
  (st : TapeSt dt A R (P) I),
  dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
  ∀ (p : IxScratch dt A R (P) I) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b))

/-- **One node of the spine, branched**. -/
noncomputable def ixSpineNodeB :
    ℕ → Σ' st : TapeSt dt A R (P) I,
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := ixSpineNodeB n
    if h : n < dt.nv then
      ⟨dt.ixLegStB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2,
        (dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2).1.trans prev.2.1,
        dt.ixLegCtlB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2⟩
    else prev

/-- The branched tape family of the spine. -/
noncomputable def ixSpineStOfB (k : Fin (dt.nv + 1)) :
    TapeSt dt A R (P) I :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).1

/-- The branched control family of the spine. -/
noncomputable def ixSpineFsOfB (k : Fin (dt.nv + 1)) : dt.CtlIx → A :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).2.2

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The mirror rides the branched family** — by construction. -/
theorem ixSpineStOfB_mir (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).mir = st₀.mir :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).2.1

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The marker rides the branched family**: no leg writes the working
register, so the `hwkOf` a spine asks for is the entry state's. -/
theorem ixSpineStOfB_wk (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).wk = st₀.wk := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.wk = st₀.wk := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dif_pos hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.1).trans ih
      · rw [dif_neg hm]
        exact ih
  exact hn (k : ℕ)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The bottom mark rides the branched family** — the `hbotOf` a spine asks
for. -/
theorem ixSpineStOfB_bot (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).bot = st₀.bot := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.bot = st₀.bot := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dif_pos hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.2.1).trans ih
      · rw [dif_neg hm]
        exact ih
  exact hn (k : ℕ)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The dictionary rides the branched family**: no leg of the evaluation
writes the `old` tracks, so the stage the spine reads at its last checkpoint is
the stage it was entered with. This is what lets a *guessing* program discharge
the output's `hdict`: what its guess wrote is what the verdict is read
against. -/
theorem ixSpineStOfB_old (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).old = st₀.old := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.old = st₀.old := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dif_pos hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.2.2.1).trans ih
      · rw [dif_neg hm]
        exact ih
  exact hn (k : ℕ)

/-- The packs of the branched family: the parameter's own, at the position's
state — the gate being what makes them exist. -/
noncomputable def ixSpineSemOfB (j : Fin dt.nv)
    (hg : dt.ixGatedAt (PR := PR) (elt := elt) F j
      (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
        mV st₀ f₀ semB j.castSucc))
    (p : IxScratch dt A R (P) I) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
        (dt.ixVarRdSt (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB
          j.castSucc) p (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j)
        (dt.ixVarRdSt (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB
          j.castSucc) p (mV a)) v (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b) :=
  semB v j (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB j.castSucc) hg p a
    hp b

omit [Finite I] [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem ixSpineStOfB_zero :
    dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB 0 = st₀ := rfl

omit [Finite I] [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem ixSpineFsOfB_zero :
    dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB 0 = f₀ := rfl

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The branched control's cover equation** — `ixEvalSpineB_run`'s
`hfs`. -/
theorem ixSpineFsOfB_succ (j : Fin dt.nv) :
    dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j.succ =
      dt.ixLegCtlB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc)
        (dt.ixSpineSemOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j)
        (dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc) := by
  change (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB ((j : ℕ) + 1)).2.2 = _
  rw [ixSpineNodeB, dif_pos j.isLt]
  rfl

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The branched tape's cover equation** — `ixEvalSpineB_run`'s `hst`. -/
theorem ixSpineStOfB_succ (j : Fin dt.nv) :
    dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j.succ =
      dt.ixLegStB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc)
        (dt.ixSpineSemOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j)
        (dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc) := by
  change (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB ((j : ℕ) + 1)).1 = _
  rw [ixSpineNodeB, dif_pos j.isLt]
  rfl

/-- **The verdicts of the branched family**: at each position, the stage
bit its own leg writes. -/
noncomputable def ixSpineBitOfB (j : Fin dt.nv) : Prop :=
  dt.ixLegBitB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j.castSucc)
    (dt.ixSpineSemOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j)
    (dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j.castSucc)

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The branched family writes what a spine writes** — the projection of
the cover equation the `new` tracks read, which is all the dictionary
lemmas ask of a leg (`DescriptiveComplexity.Draw.Data.ixLegStB_new`). -/
theorem ixSpineStOfB_writesNew :
    dt.IxWritesNew (v := v) (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB)
      (dt.ixSpineBitOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB) := by
  intro j i' r
  rw [dt.ixSpineStOfB_succ (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j,
    dt.ixLegStB_new (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j _ _ _ i' r]
  rfl

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **A field no leg writes rides the branched spine.** -/
theorem ixSpineRideB {β : Sort _}
    (G : TapeSt dt A R (P) I → β)
    (hF : ∀ (j : Fin dt.nv)
      (st : TapeSt dt A R (P) I)
      (semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
        ∀ (p : IxScratch dt A R (P) I) (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
            (dt.ixVarRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.IxKindSem PR.zero PR.one (dt.varAt j)
            (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
            elt (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      G (dt.ixLegStB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j st semT f) = G st)
    (k : Fin (dt.nv + 1)) :
    G (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k) = G st₀ := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := dt.ixSpineStOfB_succ (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB
      ⟨n, hnv⟩
    exact Eq.trans (congrArg G hstep) (Eq.trans (hF _ _ _ _) (ih _))

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **A field a threaded leg leaves alone rides the whole spine** — the
twin of `DescriptiveComplexity.Draw.Data.ixSpineRide` at the legs the
threaded family is built from. -/
theorem ixSpineRideT {β : Sort _}
    (G : TapeSt dt A R (P) I → β)
    (hF : ∀ (j : Fin dt.nv)
      (st : TapeSt dt A R (P) I)
      (tOf' : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
      (semT : ∀ (p : IxScratch dt A R (P) I)
        (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
            (dt.ixVarRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.IxKindSem PR.zero PR.one (dt.varAt j)
            (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
            elt (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      G (dt.ixLegStT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
        mV j st tOf' semT f) = G st)
    (k : Fin (dt.nv + 1)) :
    G (dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf k) = G st₀ := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := dt.ixSpineStOfT_succ (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf
      ⟨n, hnv⟩
    exact Eq.trans (congrArg G hstep) (Eq.trans (hF _ _ _ _ _) (ih _))

/-! ### The branched spine's dictionary at one address

Gating is per variable, and so is the reading: at an address whose blocks
below a variable's arity all encode points, that variable's cell holds one
step of the iteration there; where one of them does not, the position takes
an ungated leg, writes `False`, and the dictionary is `False` too. Nothing
is assumed of the *other* variables' blocks — which is what a sweep needs,
since it passes every address. -/

include hinj hhasP heltP hix hblkP hmono hup hpassEnc hgateEnc hUse in
omit [Finite dt.KIx] [Finite I] in
/-- **What the branched spine leaves at one address, per variable.** -/
theorem ixNew_last_trackOf_B
    (hlin : IsLinOrd (WMLe (A := Univ A R (P)
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : Tag R (P) dt.KIx)
      (w : Fin dt.dd → A), ixAddr elt (mV a) (t, w) →
        ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (hreg : ¬∃ u : I, v = F.cell u)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (hmir₀ : ixAddr elt st₀.mir = v)
    {Below : (Univ A R (P) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st₀.old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeSt dt A R (P) I),
      Below (ixAddr elt (dt.ixStageTgt F hhasP (dt.varAt j) ts
        { dt.ixRoundSt st (mV a) with sav := ixMark elt v }
        (dt.d.B.arity iv))))
    (i : dt.d.B.ι) :
    ((dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀
        (fun w j st hg => dt.ixGatedSem (elt := elt)
          F hpassEnc hgateEnc PR.zero_ne_one hlin mV (v := w) j st hg)
        (Fin.last dt.nv)).new i v ↔
      trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i)) (dt.d.next σ) v) := by
  classical
  obtain ⟨j, hj⟩ := dt.exists_varList_get i
  subst hj
  set semB : ∀ (w : Univ A R (P) dt.KIx dt.dd →
      Prop) (j : Fin dt.nv)
      (st : TapeSt dt A R (P) I),
      dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st → _ :=
    fun w j st hg => dt.ixGatedSem (elt := elt)
      F hpassEnc hgateEnc PR.zero_ne_one hlin mV (v := w) j st hg
    with hsemB
  set stj := dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB j.castSucc
    with hstj
  have hmirj : stj.mir = st₀.mir :=
    dt.ixSpineStOfB_mir (elt := elt) F hinj hhasP heltP mV st₀ f₀ semB j.castSucc
  have holdj : stj.old = st₀.old :=
    dt.ixSpineRideB (elt := elt) F hinj hhasP heltP mV st₀ f₀ semB (fun st => st.old)
      (fun j' st' semT f' =>
        (dt.ixLegStB_fields (elt := elt) (aT := aT) F hinj hhasP heltP
          mV j' st' semT f').2.2.2.1) j.castSucc
  have hwr := dt.ixSpineStOfB_writesNew (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB
  by_cases hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j stj
  · -- the blocks below this variable's arity encode: the cell is one step
    have hmb : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        dt.ixMirBlk st₀ (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) =
          encMap dt.ly PR.zero PR.one
            ((ixIsEnc_of_gatedAt (dt := dt) (elt := elt) (F := F) (hgateEnc := hgateEnc)
        j stj hg ℓ).choose) :=
      fun ℓ => (congrFun (ixMirBlk_of_mir (elt := elt) hmirj) _).symm.trans
        ((ixIsEnc_of_gatedAt (dt := dt) (elt := elt) (F := F) (hgateEnc := hgateEnc)
        j stj hg ℓ).choose_spec)
    refine (ixNew_last_next_at (dt := dt) (elt := elt) (F := F) (hinj := hinj)
      (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
      (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc) (mV := mV)
      (hUse := hUse) (hlin := hlin) (hord := hord) (hbotV := hbotV)
      (hmV0 := hmV0) (hIncr := hIncr) (hKin := hKin) (hTop := hTop) (σ := σ)
      (j := j)
      (semOfJ := dt.ixGatedSem₀ (elt := elt) F hpassEnc hgateEnc PR.zero_ne_one
        hlin mV j stj hg)
      (fG := dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) stj v
        (dt.ixTagAt (PR := PR) (elt := elt) j stj)
        (dt.ixSpineFsOfB (elt := elt) F hinj hhasP heltP mV st₀ f₀ semB
          j.castSucc))
      (hstN := hwr) (hmirOf := hmirj) (holdOf := holdj)
      (hbj := iff_of_eq (ixLegBitB_gatedSem (dt := dt) (elt := elt) (F := F)
        (hinj := hinj) (hhasP := hhasP) (heltP := heltP)
        (hpassEnc := hpassEnc) (hgateEnc := hgateEnc) (hzo := PR.zero_ne_one)
        (hlin := hlin)
        (hreg := hreg) (mV := mV) (j := j) (st := stj) (hg := hg) (f₀ :=
        dt.ixSpineFsOfB (elt := elt) F hinj hhasP heltP mV st₀ f₀ semB
          j.castSucc)))
      (hmb := hmb) (hdict := hdict)
      (hbelow := fun a iv' ts => hbelow j a iv' ts _) (hordP := hordP)
      (hsem := fun _ _ _ _ => rfl)).trans ?_
    refine (trackOf_of_blocks PR.zero_ne_one (dt.arOf_le_ko
      (some (dt.varList.get j))) (dt.d.next σ) (fun ℓ => ?_)).symm
    rw [← hmir₀]
    exact hmb ℓ
  · -- one of them does not: the position writes `False`, and so does the
    -- dictionary
    have hbit : ¬dt.ixSpineBitOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB j := by
      rw [ixSpineBitOfB, ixLegBitB, dif_neg hg]
      exact id
    refine iff_of_false (fun hc => hbit ((dt.ixNew_last_get hwr j).mp hc)) ?_
    obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ : Fin (dt.arOf (dt.varAt j)),
        ¬IsEnc dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt stj.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (P) dt.KIx)) := by
      by_contra hc
      exact hg (ixGatedAt_of_isEnc (dt := dt) (elt := elt) (F := F) (hgateEnc := hgateEnc) j stj
        (fun ℓ => not_not.mp fun h => hc ⟨ℓ, h⟩))
    refine not_trackOf_of_notEnc (dt.arOf_le_ko (some (dt.varList.get j)))
      (dt.d.next σ) (ℓ₀ := ℓ₀) (fun p hp => hℓ₀ ⟨p, ?_⟩)
    rw [hmirj, hmir₀]
    exact hp


include hinj hhasP heltP hix hblkP hmono hup hpassEnc hUse in
omit [Finite I] [Finite dt.KIx] in
/-- **The verdict the output's leg leaves is the output sentence**, at the
stage the tracks hold. The output variable is nullary, so its blocks encode
the empty tuple and there is nothing to ask of them – which is why this is the
one verdict a program can take at the address its head starts on. This is the
`hacc` a run through the output's machinery
(`DescriptiveComplexity.Draw.Data.nexIxEvalOutB_reachesIn`) asks for, and the
reason the accepting bit says anything at all. -/
theorem ixOutAcc_iff_out
    (hlin : IsLinOrd (WMLe (A := Univ A R (P) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R (P) dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (st : TapeSt dt A R (P) I)
    {Below : (Univ A R (P) dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st.old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP none ts
        { dt.ixRoundSt st (mV a) with sav := ixMark elt v } (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (f₀ : dt.CtlIx → A) :
    (dt.varArgsOf PR.zero PR.one none).accBit
        (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf
          (fun a hp b => dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc)
            none (dt.ixRoundSt st (mV a)) hp (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) b)
          f₀) ↔
      @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out :=
  dt.ixAccVerdict_out (elt := elt) (F := F) (hinj := hinj) (hhasP := hhasP)
    (heltP := heltP) (hix := hix) (hblkP := hblkP) (hmono := hmono) (hup := hup)
    (hpassEnc := hpassEnc) (st := st) (mV := mV) (hlin := hlin) (hord := hord)
    (hbotV := hbotV) (hmV0 := hmV0) (hUse := hUse) (hIncr := hIncr)
    (hKin := hKin) (hTop := hTop) (σ := σ) (hdict := hdict) (hbelow := hbelow)
    (hordP := hordP) (hsem := fun _ _ _ => rfl) (fG := _)

end Family

/-! ### The sweep's families, over an arbitrary per-address leg

Everything the sweep's families need of an address's evaluation is *what
state and control it ends in*. Taking those two as parameters makes the
whole layer — the iteration, its two cover equations, and the ride lemmas
that discharge `reaches_sweep`'s `hwkE`/`hmirE`/`hltpE` — serve any
evaluation: the spine as first built, its threaded twin, and the branched
form a junk address will need. -/

section SweepGen

variable (stE : (Univ A R (P) dt.KIx dt.dd →
    Prop) → TapeSt dt A R (P) I →
  (dt.CtlIx → A) → TapeSt dt A R (P) I)
variable (fsE : (Univ A R (P) dt.KIx dt.dd →
    Prop) → TapeSt dt A R (P) I →
  (dt.CtlIx → A) → dt.CtlIx → A)
variable (hlin : IsLinOrd (WMLe (A := Univ A R (P) dt.KIx dt.dd)))
variable (st₀ : TapeSt dt A R (P) I)
variable (f₀ : dt.CtlIx → A)

/-- **The pair the sweep arrives at each address with**: the base at the
empty address, and at every increment the previous address's evaluation
exit — its marker moved on and its mirror set to the new address, exactly
the shape `DescriptiveComplexity.Draw.Data.reaches_sweep` demands. -/
noncomputable def ixSweepPairG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (P) I × (dt.CtlIx → A) :=
  addrIter (isLinOrd_wmSetLe hlin) (st₀, f₀)
    (fun u p =>
      ({ dt.atSt (stE u p.1 p.2) (wmNext hlin u) with mir := ixMark elt (wmNext hlin u) },
        fsE u p.1 p.2)) w

/-- The sweep's tape family — `reaches_sweep`'s `SW`. -/
noncomputable def ixSweepSWG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (P) I :=
  (dt.ixSweepPairG (elt := elt) stE fsE hlin st₀ f₀ w).1

/-- The sweep's control family — `reaches_sweep`'s `FS`. -/
noncomputable def ixSweepFSG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  (dt.ixSweepPairG (elt := elt) stE fsE hlin st₀ f₀ w).2

/-- The state the sweep leaves each address in — `reaches_sweep`'s
`stE`. -/
noncomputable def ixSweepStEG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (P) I :=
  stE w (dt.ixSweepSWG (elt := elt)
    stE fsE hlin st₀ f₀ w) (dt.ixSweepFSG (elt := elt) stE fsE hlin st₀ f₀ w)

/-- The control the sweep leaves each address in — `reaches_sweep`'s
`fsE`. -/
noncomputable def ixSweepFsEG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  fsE w (dt.ixSweepSWG (elt := elt)
    stE fsE hlin st₀ f₀ w) (dt.ixSweepFSG (elt := elt) stE fsE hlin st₀ f₀ w)

omit [Finite I] [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
theorem ixSweepSWG_bot :
    dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ (fun _ => False) = st₀ :=
  congrArg Prod.fst (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)

omit [Finite I] [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
theorem ixSweepFSG_bot :
    dt.ixSweepFSG (elt := elt) stE fsE hlin st₀ f₀ (fun _ => False) = f₀ :=
  congrArg Prod.snd (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **The tape's cover equation** — `reaches_sweep`'s `hSW`, on the nose. -/
theorem ixSweepSWG_incr
    {w w' : Univ A R (P) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ w' =
      { dt.atSt (dt.ixSweepStEG (elt := elt)
        stE fsE hlin st₀ f₀ w) w' with mir := ixMark elt w' } := by
  have h := congrArg Prod.fst
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (stE u p.1 p.2) (wmNext hlin u) with mir := ixMark elt (wmNext hlin u) },
          fsE u p.1 p.2)))
  rw [wmNext_eq hlin hi] at h
  exact h

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **The control's cover equation** — `reaches_sweep`'s `hFS`. -/
theorem ixSweepFSG_incr
    {w w' : Univ A R (P) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.ixSweepFSG (elt := elt) stE fsE hlin st₀ f₀ w' =
      dt.ixSweepFsEG (elt := elt) stE fsE hlin st₀ f₀ w :=
  congrArg Prod.snd
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (stE u p.1 p.2) (wmNext hlin u) with mir := ixMark elt (wmNext hlin u) },
          fsE u p.1 p.2)))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **A field neither an address's evaluation nor the advance writes rides
the whole sweep.** -/
theorem ixSweepSWG_ride {β : Sort _}
    (F : TapeSt dt A R (P) I → β)
    (hFE : ∀ u st f, F (stE u st f) = F st)
    (hFa : ∀ st u, F { dt.atSt st u with mir := ixMark elt u } = F st)
    {s₁ : Univ A R (P) dt.KIx dt.dd → Prop}
    (w : Univ A R (P) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    F (dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ w) = F st₀ := by
  refine holds_of_wideRounds hlin
    (Q := fun u => F (dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ u) = F st₀) ?_ ?_ w
    hlb hub
  · rw [dt.ixSweepSWG_bot (elt := elt) stE fsE hlin st₀ f₀]
  · intro u u' hi _ _ ih
    rw [dt.ixSweepSWG_incr (elt := elt) stE fsE hlin st₀ f₀ hi, hFa, ixSweepStEG, hFE]
    exact ih

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **The marker is at the address**, at every entry state of the sweep. -/
theorem ixSweepSWG_wk (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    {s₁ : Univ A R (P) dt.KIx dt.dd → Prop}
    (w : Univ A R (P) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ w).wk = fun r => r = w := by
  refine holds_of_wideRounds hlin
    (Q := fun u => (dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ u).wk = fun r => r = u)
    ?_ ?_ w hlb hub
  · rw [dt.ixSweepSWG_bot (elt := elt) stE fsE hlin st₀ f₀]
    exact hwk₀
  · intro u u' hi _ _ _
    rw [dt.ixSweepSWG_incr (elt := elt) stE fsE hlin st₀ f₀ hi]
    rfl

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **The mirror is at the address**, at every entry state of the sweep. -/
theorem ixSweepSWG_mir (hmir₀ : st₀.mir = fun _ => False)
    {s₁ : Univ A R (P) dt.KIx dt.dd → Prop}
    (w : Univ A R (P) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ w).mir = ixMark elt w := by
  refine holds_of_wideRounds hlin
    (Q := fun u => (dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ u).mir =
      ixMark elt u) ?_ ?_ w
    hlb hub
  · rw [dt.ixSweepSWG_bot (elt := elt) stE fsE hlin st₀ f₀]
    exact hmir₀
  · intro u u' hi _ _ _
    rw [dt.ixSweepSWG_incr (elt := elt) stE fsE hlin st₀ f₀ hi]

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **`reaches_sweep`'s `hwkE`**: the marker is still at the address when
the address's evaluation ends. -/
theorem ixSweepStEG_wk (hFE : ∀ u st f, (stE u st f).wk = st.wk)
    (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    {s₁ : Univ A R (P) dt.KIx dt.dd → Prop}
    (w : Univ A R (P) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepStEG (elt := elt) stE fsE hlin st₀ f₀ w).wk = fun r => r = w :=
  (hFE w _ _).trans
    (dt.ixSweepSWG_wk (elt := elt) stE fsE hlin st₀ f₀ hwk₀ (s₁ := s₁) w hlb hub)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **`reaches_sweep`'s `hmirE`**: so is the mirror. -/
theorem ixSweepStEG_mir (hFE : ∀ u st f, (stE u st f).mir = st.mir)
    (hmir₀ : st₀.mir = fun _ => False)
    {s₁ : Univ A R (P) dt.KIx dt.dd → Prop}
    (w : Univ A R (P) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.ixSweepStEG (elt := elt) stE fsE hlin st₀ f₀ w).mir = ixMark elt w :=
  (hFE w _ _).trans
    (dt.ixSweepSWG_mir (elt := elt) stE fsE hlin st₀ f₀ hmir₀ (s₁ := s₁) w hlb hub)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **`reaches_sweep`'s `hltpE`**: the address is not the marked end, the
mark being where the reduction planted it. -/
theorem ixSweepStEG_ltp (hFE : ∀ u st f, (stE u st f).ltp = st.ltp)
    {s₁ : Univ A R (P) dt.KIx dt.dd → Prop}
    (w : Univ A R (P) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁)
    (hltp₀ : ¬st₀.ltp w) :
    ¬(dt.ixSweepStEG (elt := elt) stE fsE hlin st₀ f₀ w).ltp w := by
  rw [ixSweepStEG, hFE, dt.ixSweepSWG_ride (elt := elt) stE fsE hlin st₀ f₀ (fun st => st.ltp)
    hFE (fun _ _ => rfl) (s₁ := s₁) w hlb hub]
  exact hltp₀

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **`reaches_sweep`'s `hmirE` when the evaluation sets the mirror
itself**: the variant of
`DescriptiveComplexity.Draw.Data.ixSweepStEG_mir` for an evaluation that
normalizes the mirror to the address it is run at, which makes the
invariant definitional instead of inductive. -/
theorem ixSweepStEG_mir' (hFE : ∀ u st f, (stE u st f).mir = ixMark elt u)
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    (dt.ixSweepStEG (elt := elt) stE fsE hlin st₀ f₀ w).mir = ixMark elt w :=
  hFE w _ _

end SweepGen

/-! ### The sweep's families -/


/-! ### The stage atom's restore, as an algebra

`DescriptiveComplexity.Draw.Data.stageEndSt st v = { st with sav := v,
tgt := v }`: the random access **writes** the home address into SAV and
TARGET whatever they held, so a stage atom is transparent exactly when they
held it already — which is what `ixStageEndSt_eq`'s two hypotheses say, and
why they are not a proof artifact.

Closing the sweep's gap by "reading the mirror" therefore means *threading*
that normalization rather than assuming it away: an atom's exit state is
`ixStageEndSt st v`, and the layers above carry it. These are the equations
that threading needs; they are all definitional, which is what makes the
propagation mechanical. -/

section StageEnd

variable {v : Univ A R (P) dt.KIx dt.dd → Prop}
variable (st : TapeStD dt A R (P))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- Normalizing commutes with a round's VAL write. -/
theorem ixStageEndSt_roundSt (m : Univ A R (P) dt.KIx dt.dd → Prop) :
    dt.stageEndSt (dt.ixRoundSt st m) v = dt.ixRoundSt (dt.stageEndSt st v) m :=
  rfl

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- **A normalized state meets the stage atom's two hypotheses by
`rfl`** — which is what makes the threaded form hypothesis-free. -/
theorem ixStageEndSt_home :
    (dt.stageEndSt st v).sav = v ∧ (dt.stageEndSt st v).tgt = v :=
  ⟨rfl, rfl⟩

end StageEnd

end Data

end Draw

end DescriptiveComplexity
