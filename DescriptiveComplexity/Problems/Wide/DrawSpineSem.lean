/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawVerdict
import DescriptiveComplexity.Problems.Wide.DrawInstEval
import DescriptiveComplexity.Problems.Wide.DrawRun

/-!
# What the spine does to the tape at one address

`DescriptiveComplexity.Draw.DrawData.evalSpine_run` takes the per-position
tape family `stOf` as a parameter, tied together by one cover equation per
position (`stOf j.succ = postVarSt …`). This file reads that family: what
the whole spine leaves on the tape at the address it was run at.

Two halves, both by the same induction along the positions:

* **everything but `val` and the marker's `new` cells rides** — the stage
  dictionary, the mirror and the three markers are the same at every
  position (`spineRide`, and the named corollaries): the spine writes only
  the cell it stands on, which is why the *next* address's leg may assume
  the same dictionary;
* **the marker's `new` cell of a variable is that variable's verdict**
  (`new_last_get`): the write happens at the position the variable sits at,
  and no later position touches it — the enumeration
  `DescriptiveComplexity.Draw.DrawData.varList` being `Finset.univ.toList`,
  hence duplicate-free and complete (`exists_varList_get`).

Joined with `DescriptiveComplexity.Draw.DrawData.accVerdict_next`, that is
**`new_last_next`**: after the spine, the `new` track of every variable
holds, at the address, one step of the iteration at the address's points —
the per-address obligation the sweep's induction carries.

One obstacle sits between this and the instantiation, and the last
section removes it: a position's semantic pack is *typed* at that
position's tape state, so a family of packs looks like it has to be built
position by position — while the pack can only be built once the mirror
invariant is known, which is what the family's own defining equations give.
`KindSem` in fact reads the state only through the levels' register sets
(`lvSet_congr`) and the pass condition through the VAL register alone
(`igPassP_congr`, `igPassP_roundSt` — a file test reads the block mark, the
VAL digit, the padding mark and the names, all of which either ride or are
the tape's permanent geometry). So **one** pack transports along the whole
spine (`kindSemCast`, packaged as `spineSem`), and its content survives the
transport (`kindSemCast_mkKindSem`, `passW_congr`, `kindSemCast_passSem`,
packaged as `spineSem_passSem`) — which is what discharges each position's
`hsem`.

With that, the families themselves are **built**, not assumed:
`spineNode` recurses along the positions producing the tape state, the
proof that its mirror is still the address's, and the control — the three
together, because the pack a position's leg needs is typed at that
position's state and is available only because the mirror rode. Its
projections `spineStOf`/`spineFsOf`/`spineSemOf` satisfy
`spineStOf_succ` and `spineFsOf_succ`, which *are* the `hst` and `hfs`
`DescriptiveComplexity.Draw.DrawData.evalSpine_run` asks for.

One scale up, the same is done for the sweep: `sweepSW`/`sweepFS` are the
pair the sweep arrives at each address with — with `sweepStE_wk`,
`sweepStE_mir` and `sweepStE_ltp` discharging three of the four remaining
obligations of `DescriptiveComplexity.Draw.DrawData.reaches_sweep`, and
`eq_of_sweepSW_sav` recording why the fourth (`hspine`) cannot be met
until the program refreshes SAV and TARGET at each address — an iteration along the
addresses (`addrIter`), because the control accumulates even though the
tape's writes are local — and `sweepSW_incr`/`sweepFS_incr` are exactly
`DescriptiveComplexity.Draw.DrawData.reaches_sweep`'s `hSW` and `hFS`.

On top of it, the same statement in the form the *next* sweep reads its
input in — `new_last_trackOf` at an address whose blocks encode a tuple,
`new_last_trackOf_of_junk` where they do not, both sides being empty there
— and the sweep itself: **`sweep_new`**, the address-by-address induction
(`DescriptiveComplexity.holds_of_wideRounds`) saying a sweep rewrites the
`new` tracks of exactly the addresses it has passed, everything else still
carrying what it started with.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### Iterating along the addresses

The sweep's families cannot both be written in closed form: the tape's
`new` tracks are local to the address a leg stands on — `sweep_new` is
their closed form — but the **control threads**, a leg's exit control being
its entry control transformed. So the pair is defined by an iteration along
the address order, which is `DescriptiveComplexity.Draw.iterOrd` at the
linear order the addresses already carry
(`DescriptiveComplexity.isLinOrd_wmSetLe`, turned into an instance *locally*
— the order must never be an ambient instance on `α → Prop`, which carries
Pi's own).

The successor is named rather than quantified (`wmNext`): a step of
`iterOrd` is indexed by the address it leaves, while the state it produces
mentions the one it arrives at. -/

section AddrIter

variable {α : Type} [Finite α] {Le : α → α → Prop} {Q' : Type*}

open Classical in
/-- **The next address**, chosen: the increment where one exists, the
address itself at the full set (where the sweep has ended). -/
noncomputable def wmNext (h : IsLinOrd Le) (w : α → Prop) : α → Prop :=
  if hx : ∃ x, ¬w x then (exists_wmIncr h hx).choose else w

/-- At an address with an increment, `wmNext` is it — the increment being
unique. -/
theorem wmNext_eq (h : IsLinOrd Le) {w w' : α → Prop} (hi : WMIncr Le w w') :
    wmNext h w = w' := by
  classical
  have hx : ∃ x, ¬w x := by
    obtain ⟨u, hu, -, -⟩ := hi
    exact ⟨u, hu⟩
  rw [wmNext, dif_pos hx]
  exact wmIncr_functional h (exists_wmIncr h hx).choose_spec hi

/-- **A value iterated along the addresses**: the base at the empty
address, one step per increment. -/
noncomputable def addrIter (h : IsLinOrd (WMSetLe Le)) (init : Q')
    (step : (α → Prop) → Q' → Q') (w : α → Prop) : Q' :=
  letI := h.toLinearOrder
  iterOrd init step w

/-- At the empty address the iteration is the base. -/
theorem addrIter_bot (hL : IsLinOrd Le) (h : IsLinOrd (WMSetLe Le))
    (init : Q') (step : (α → Prop) → Q' → Q') :
    addrIter h init step (fun _ => False) = init := by
  letI := h.toLinearOrder
  exact iterOrd_bot (a₀ := (fun _ => False : α → Prop))
    (fun b => wmSetLe_of_empty hL (fun _ hc => hc) b)

/-- **Across an increment the iteration steps once**, at the address it
leaves. -/
theorem addrIter_incr (hL : IsLinOrd Le) (h : IsLinOrd (WMSetLe Le))
    {w w' : α → Prop} (hi : WMIncr Le w w') (init : Q')
    (step : (α → Prop) → Q' → Q') :
    addrIter h init step w' = step w (addrIter h init step w) := by
  letI := h.toLinearOrder
  refine iterOrd_covers ?_ ?_
  · exact ⟨wmSetLe_of_wmIncr hi, fun hc =>
      ne_of_wmIncr hi (h.2.2.1 w w' (wmSetLe_of_wmIncr hi) hc)⟩
  · rintro b ⟨hb1, hb2⟩
    have hblt : WMSetLt Le b w' :=
      (wmSetLt_iff b w').mpr ⟨hb2.1, fun hc => hb2.2 (hc ▸ h.1 b)⟩
    exact hb1.2 ((wmSetLt_iff_of_wmIncr hL hi b).mp hblt)

end AddrIter

namespace DrawData

variable {L : Language.{0, 0}} (dt : DrawData L)

/-! ### The enumeration of the variables -/

/-- The enumeration lists every variable. -/
theorem exists_varList_get (i : dt.d.B.ι) :
    ∃ j : Fin dt.nv, dt.varList.get j = i := by
  letI := Fintype.ofFinite dt.d.B.ι
  have hmem : i ∈ dt.varList := by
    rw [varList]
    exact Finset.mem_toList.mpr (Finset.mem_univ i)
  obtain ⟨j, hj⟩ := List.get_of_mem hmem
  exact ⟨⟨(j : ℕ), j.isLt⟩, hj⟩

/-- The enumeration lists each variable once. -/
theorem varList_nodup : dt.varList.Nodup := by
  letI := Fintype.ofFinite dt.d.B.ι
  rw [varList]
  exact Finset.nodup_toList _

variable {dt} in
/-- Two positions carrying the same variable are the same position. -/
theorem varList_get_inj {j j' : Fin dt.nv}
    (h : dt.varList.get j = dt.varList.get j') : j = j' :=
  List.nodup_iff_injective_get.mp dt.varList_nodup h

variable {A R : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
variable [Language.wide.Structure
  (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
variable {PR : Prog A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}
variable (RF : RegFile (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable [Finite dt.KIx]

/-! ### One position's write -/

variable {v : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
open Classical in
/-- **What a position writes**: the variable's cell at the marker, nothing
else. -/
theorem new_postVarSt (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (m : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (i' i : dt.d.B.ι) (b : Prop)
    (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    (dt.postVarSt v st m i b).new i' r =
      (if i' = i ∧ r = v then b else st.new i' r) := rfl

/-! ### The spine's writes -/

section Spine

variable {mOf : Fin dt.nv →
  (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)}
variable {stOf : Fin (dt.nv + 1) →
  TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
variable {bOf : Fin dt.nv → Prop}
variable (hst : ∀ j : Fin dt.nv, stOf j.succ =
  dt.postVarSt v (stOf j.castSucc) (mOf j) (dt.varList.get j) (bOf j))

open Classical in
/-- **The only thing the `new` tracks need of a position**: its own cell at
the marker holds its verdict and every other cell rides. Weaker than the
cover equation `hst`, and weaker on purpose — a *branched* position's leg
is not literally a
`DescriptiveComplexity.Draw.DrawData.postVarSt` of the position's entry
state (its VAL loop may normalize the two scratch registers first), while
this projection of it is
(`DescriptiveComplexity.Draw.DrawData.legStB_new`). -/
abbrev WritesNew
    (stOf : Fin (dt.nv + 1) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (bOf : Fin dt.nv → Prop) : Prop :=
  ∀ (j : Fin dt.nv) (i' : dt.d.B.ι)
    (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
    (stOf j.succ).new i' r =
      (if i' = dt.varList.get j ∧ r = v then bOf j
        else (stOf j.castSucc).new i' r)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hst in
/-- The cover equation gives the projection. -/
theorem writesNew_of_hst : dt.WritesNew (v := v) stOf bOf := by
  classical
  intro j i' r
  rw [hst j]
  rfl

variable (hstN : dt.WritesNew (v := v) stOf bOf)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hst in
/-- **Anything a position's write leaves alone rides the whole spine**: the
induction along the positions, once, for every field but `val` and `new`. -/
theorem spineRide {β : Sort _}
    (F : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) → β)
    (hF : ∀ st m i b, F (dt.postVarSt v st m i b) = F st)
    (k : Fin (dt.nv + 1)) :
    F (stOf k) = F (stOf 0) := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := hst ⟨n, hnv⟩
    exact Eq.trans (congrArg F hstep) (Eq.trans (hF _ _ _ _) (ih _))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hst in
/-- The stage dictionary rides the spine. -/
theorem spine_old (k : Fin (dt.nv + 1)) : (stOf k).old = (stOf 0).old :=
  dt.spineRide hst (fun st => st.old) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hst in
/-- The working address rides the spine. -/
theorem spine_mir (k : Fin (dt.nv + 1)) : (stOf k).mir = (stOf 0).mir :=
  dt.spineRide hst (fun st => st.mir) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hst in
/-- The three markers ride the spine. -/
theorem spine_wk (k : Fin (dt.nv + 1)) : (stOf k).wk = (stOf 0).wk :=
  dt.spineRide hst (fun st => st.wk) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hst in
theorem spine_bot (k : Fin (dt.nv + 1)) : (stOf k).bot = (stOf 0).bot :=
  dt.spineRide hst (fun st => st.bot) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hst in
theorem spine_ltp (k : Fin (dt.nv + 1)) : (stOf k).ltp = (stOf 0).ltp :=
  dt.spineRide hst (fun st => st.ltp) (fun _ _ _ _ => rfl) k

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hstN in
/-- **Off the marker, the `new` tracks ride the spine**: a position writes
its own cell only. -/
theorem spine_new_off (k : Fin (dt.nv + 1)) (i : dt.d.B.ι)
    {r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
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
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hstN in
/-- **At the marker, a variable's `new` cell is the verdict of its own
position**: it is written there, and no later position writes it, the
enumeration being duplicate-free. -/
theorem new_last_get (j : Fin dt.nv) :
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
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
include hstN in
/-- **At an address every position rejects, the marker's `new` cells are
all clear** — the junk legs
(`DescriptiveComplexity.Draw.DrawData.varLegFail_run`,
`DescriptiveComplexity.Draw.DrawData.varLegUngated_run`) store `False`, which
is what the stage dictionary holds at an address that encodes no tuple. -/
theorem new_last_of_false (hbOf : ∀ j : Fin dt.nv, ¬bOf j)
    (i : dt.d.B.ι) : ¬(stOf (Fin.last dt.nv)).new i v := by
  obtain ⟨j, hj⟩ := dt.exists_varList_get i
  subst hj
  exact fun hc => hbOf j ((dt.new_last_get hstN j).mp hc)

end Spine

/-! ### The spine's semantic reading -/

section SpineNext

variable [LinearOrder (dt.X.Map A)]
variable {v : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
  Prop)

omit [Finite dt.KIx] in
/-- **After the spine, one variable's `new` cell holds its own step of the
iteration** — the per-position form: only the position of that variable, its
pack and its verdict are named, so an address where *other* positions are
junk is covered too (which is what a sweep needs, the gates being per
variable). -/
theorem new_last_next_at
    (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {stOf : Fin (dt.nv + 1) →
      TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    {bOf : Fin dt.nv → Prop} (j : Fin dt.nv)
    (semOfJ : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) (dt.kindOf (dt.varAt j) b))
    (fG : dt.CtlIx → A)
    (hstN : dt.WritesNew (v := v) stOf bOf)
    (hmirOf : (stOf j.castSucc).mir = (stOf 0).mir)
    (holdOf : (stOf j.castSucc).old = (stOf 0).old)
    (hbj : bOf j ↔
      dt.accVerdict PR.one (dt.polOf (dt.varAt j))
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.roundFX RF hord (dt.varAt j) (stOf j.castSucc) v mV semOfJ
            (dt.varFM RF hord (dt.varAt j) (stOf j.castSucc) v mV semOfJ fG aT) aT)
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.roundSt (stOf j.castSucc) (mV aT)) v)))
    (mbW : Fin (dt.arOf (dt.varAt j)) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.mirBlk (stOf 0) (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ))
    {Below : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι)
      (s : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      Below s → ((stOf 0).old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j))),
      Below (dt.stageTgtD PR.zero (dt.varAt j) iv ts
        (dt.roundSt (stOf j.castSucc) (mV a)) v (dt.d.B.arity iv)))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) ℓ)
      (b : Fin (dt.natOf (dt.varAt j)))
      (hmb' : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        wmBlk (dt.roundSt (stOf j.castSucc) (mV a)).mir
          (DrawTag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
          encMap dt.ly PR.zero PR.one (mbW ℓ)),
      semOfJ a hp b = dt.passSem RF PR.zero_ne_one hlin (dt.varAt j)
        (dt.roundSt (stOf j.castSucc) (mV a)) hp mbW hmb' b) :
    (stOf (Fin.last dt.nv)).new (dt.varList.get j) v ↔
      dt.d.next σ (dt.varList.get j) mbW := by
  classical
  have hmbj : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.mirBlk (stOf j.castSucc)
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ) := fun ℓ =>
    (congrFun (mirBlk_of_mir hmirOf) _).trans (hmb _)
  have hdictj : ∀ (iv : dt.d.B.ι)
      (s : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      Below s → ((stOf j.castSucc).old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s) :=
    fun iv s hs => (iff_of_eq (congrFun (congrFun holdOf iv) s)).trans
      (hdict iv s hs)
  refine (dt.new_last_get hstN j).trans (hbj.trans ?_)
  exact dt.accVerdict_next RF (stOf j.castSucc) mV (dt.varList.get j)
    semOfJ hlin hord hbotV hmV0 hIncr hKin hTop σ mbW hmbj hdictj hbelow
    hordP (fun a hp b => hsem a hp b _) fG

omit [Finite dt.KIx] in
/-- **After the spine, every `new` track holds the next stage at the
address's points.** The position of a variable writes its verdict, which
`DescriptiveComplexity.Draw.DrawData.accVerdict_next` reads as
`DescriptiveComplexity.StepDef.next`; the mirror and the dictionary ride
the spine, so the semantic hypotheses need only be given at the entry
state. -/
theorem new_last_next
    (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {stOf : Fin (dt.nv + 1) →
      TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    {bOf : Fin dt.nv → Prop}
    (semOfJ : ∀ (j : Fin dt.nv) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) (dt.kindOf (dt.varAt j) b))
    (fGOf : Fin dt.nv → dt.CtlIx → A)
    (hstN : dt.WritesNew (v := v) stOf bOf)
    (hmirOf : ∀ k : Fin (dt.nv + 1), (stOf k).mir = (stOf 0).mir)
    (holdOf : ∀ k : Fin (dt.nv + 1), (stOf k).old = (stOf 0).old)
    (hbOf : ∀ j : Fin dt.nv, bOf j ↔
      dt.accVerdict PR.one (dt.polOf (dt.varAt j))
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.roundFX RF hord (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
            (dt.varFM RF hord (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
              (fGOf j) aT) aT)
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.roundSt (stOf j.castSucc) (mV aT)) v)))
    (pt : Fin dt.ko → dt.X.Map A)
    (hpt : ∀ k : Fin dt.ko,
      dt.mirBlk (stOf 0) k = encMap dt.ly PR.zero PR.one (pt k))
    {Below : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι)
      (s : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      Below s → ((stOf 0).old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j))),
      Below (dt.stageTgtD PR.zero (dt.varAt j) iv ts
        (dt.roundSt (stOf j.castSucc) (mV a)) v (dt.d.B.arity iv)))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (j : Fin dt.nv) (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) ℓ)
      (b : Fin (dt.natOf (dt.varAt j)))
      (hmb' : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        wmBlk (dt.roundSt (stOf j.castSucc) (mV a)).mir
          (DrawTag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
          encMap dt.ly PR.zero PR.one
            (pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))),
      semOfJ j a hp b = dt.passSem RF PR.zero_ne_one hlin (dt.varAt j)
        (dt.roundSt (stOf j.castSucc) (mV a)) hp
        (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ)) hmb' b)
    (i : dt.d.B.ι) :
    (stOf (Fin.last dt.nv)).new i v ↔
      dt.d.next σ i
        (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (some i)) ℓ)) := by
  classical
  obtain ⟨j, hj⟩ := dt.exists_varList_get i
  subst hj
  exact dt.new_last_next_at RF mV hlin hord hbotV hmV0 hIncr hKin hTop σ j
    (semOfJ j) (fGOf j) hstN (hmirOf j.castSucc) (holdOf j.castSucc)
    (hbOf j) (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
    (fun ℓ => hpt _) hdict (hbelow j) hordP
    (fun a hp b hmb' => hsem j a hp b hmb')

end SpineNext

/-! ### What a whole sweep leaves behind -/

section SweepDict

variable {v : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **A sweep rewrites the `new` tracks of exactly the addresses it has
passed.** The address-by-address induction
(`DescriptiveComplexity.holds_of_wideRounds`) over the two facts one
address contributes — its own cell now holds the target (`hat`, which
`new_last_next` and `new_last_of_false` supply), every other cell is
untouched (`hoff`, which `spine_new_off` supplies) — with the entry state
of the next address read off the sweep's own tape family (`hSW`, the
`hSW` of `DescriptiveComplexity.Draw.DrawData.reaches_sweep`).

Below the address reached, the tracks are the target; elsewhere they are
still the sweep's initial ones. Stated for an arbitrary target family `N`,
so the same lemma serves the stage sweep (`N` the dictionary of
`d.next σ`) and any other. -/
theorem sweep_new
    (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd)))
    {s₀ s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    {SW stE : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    {N : dt.d.B.ι →
      (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) → Prop}
    (hat : ∀ w, WMSetLe WMLe s₀ w → WMSetLt WMLe w s₁ →
      ∀ i, ((stE w).new i w ↔ N i w))
    (hoff : ∀ w, WMSetLe WMLe s₀ w → WMSetLt WMLe w s₁ →
      ∀ (i : dt.d.B.ι) (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
        dt.KIx dt.dd → Prop), r ≠ w → ((stE w).new i r ↔ (SW w).new i r))
    (hSW : ∀ w w', WMIncr WMLe w w' → WMSetLe WMLe s₀ w →
      WMSetLe WMLe w' s₁ → SW w' = { dt.atSt (stE w) w' with mir := w' }) :
    ∀ w, WMSetLe WMLe s₀ w → WMSetLe WMLe w s₁ →
      (∀ (i : dt.d.B.ι) (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
          dt.KIx dt.dd → Prop),
        WMSetLe WMLe s₀ r → WMSetLt WMLe r w → ((SW w).new i r ↔ N i r)) ∧
      (∀ (i : dt.d.B.ι) (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
          dt.KIx dt.dd → Prop),
        ¬(WMSetLe WMLe s₀ r ∧ WMSetLt WMLe r w) →
          ((SW w).new i r ↔ (SW s₀).new i r)) := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  refine holds_of_wideRounds hlin (Q := fun w =>
    (∀ (i : dt.d.B.ι) (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
        dt.KIx dt.dd → Prop),
      WMSetLe WMLe s₀ r → WMSetLt WMLe r w → ((SW w).new i r ↔ N i r)) ∧
    (∀ (i : dt.d.B.ι) (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
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
      (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
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
variable {v : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
  Prop)

omit [LinearOrder R] [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [Finite dt.KIx] in
/-- **At a junk address the cell and the dictionary are both empty**: the
legs store `False` (`new_last_of_false`) and a track holds nothing where a
block below the variable's arity encodes no point
(`DescriptiveComplexity.Draw.not_trackOf_of_notEnc`), so the two readings
agree there too. -/
theorem new_last_trackOf_of_junk
    {stOf : Fin (dt.nv + 1) →
      TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    {bOf : Fin dt.nv → Prop}
    (hstN : dt.WritesNew (v := v) stOf bOf)
    (hbOf : ∀ j : Fin dt.nv, ¬bOf j)
    (σ : dt.d.B.Assignment (dt.X.Map A)) (i : dt.d.B.ι)
    {ℓ₀ : Fin (dt.d.B.arity i)}
    (hℓ : ∀ p : dt.X.Map A,
      wmBlk v (argOut dt.ki (Fin.castLE (dt.arOf_le_ko (some i)) ℓ₀)) ≠
        encMap dt.ly PR.zero PR.one p) :
    ((stOf (Fin.last dt.nv)).new i v ↔
      trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i))
        (dt.d.next σ) v) :=
  iff_of_false (dt.new_last_of_false hstN hbOf i)
    (not_trackOf_of_notEnc (dt.arOf_le_ko (some i)) (dt.d.next σ) hℓ)

omit [Finite dt.KIx] in
/-- **At an encoded address the cell holds the dictionary of the next
stage**: `new_last_next` read through
`DescriptiveComplexity.Draw.trackOf_of_blocks`, the sweep's mirror
invariant (`hmir`) turning the address's blocks into the ones the
machinery read. This is the form the sweep's induction
(`sweep_new`) consumes, and the form the *next* sweep's `hdict` is in. -/
theorem new_last_trackOf
    (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {stOf : Fin (dt.nv + 1) →
      TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    {bOf : Fin dt.nv → Prop}
    (semOfJ : ∀ (j : Fin dt.nv) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) (dt.kindOf (dt.varAt j) b))
    (fGOf : Fin dt.nv → dt.CtlIx → A)
    (hstN : dt.WritesNew (v := v) stOf bOf)
    (hmirOf : ∀ k : Fin (dt.nv + 1), (stOf k).mir = (stOf 0).mir)
    (holdOf : ∀ k : Fin (dt.nv + 1), (stOf k).old = (stOf 0).old)
    (hbOf : ∀ j : Fin dt.nv, bOf j ↔
      dt.accVerdict PR.one (dt.polOf (dt.varAt j))
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.roundFX RF hord (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
            (dt.varFM RF hord (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
              (fGOf j) aT) aT)
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.roundSt (stOf j.castSucc) (mV aT)) v)))
    (pt : Fin dt.ko → dt.X.Map A) (hmir : (stOf 0).mir = v)
    (hpt : ∀ k : Fin dt.ko,
      wmBlk v (argOut dt.ki k) = encMap dt.ly PR.zero PR.one (pt k))
    {Below : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι)
      (s : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      Below s → ((stOf 0).old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j))),
      Below (dt.stageTgtD PR.zero (dt.varAt j) iv ts
        (dt.roundSt (stOf j.castSucc) (mV a)) v (dt.d.B.arity iv)))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (j : Fin dt.nv) (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) ℓ)
      (b : Fin (dt.natOf (dt.varAt j)))
      (hmb' : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        wmBlk (dt.roundSt (stOf j.castSucc) (mV a)).mir
          (DrawTag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
          encMap dt.ly PR.zero PR.one
            (pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))),
      semOfJ j a hp b = dt.passSem RF PR.zero_ne_one hlin (dt.varAt j)
        (dt.roundSt (stOf j.castSucc) (mV a)) hp
        (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ)) hmb' b)
    (i : dt.d.B.ι) :
    ((stOf (Fin.last dt.nv)).new i v ↔
      trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i))
        (dt.d.next σ) v) := by
  refine (dt.new_last_next RF mV hlin hord hbotV hmV0 hIncr hKin hTop σ semOfJ
    fGOf hstN hmirOf holdOf hbOf pt ?_ hdict hbelow hordP hsem i).trans
    (trackOf_of_blocks PR.zero_ne_one (dt.arOf_le_ko (some i)) (dt.d.next σ)
      (fun ℓ => hpt _)).symm
  intro k
  change wmBlk (stOf 0).mir
    (DrawTag.arg (toLex (Sum.inl k : Fin dt.ko ⊕ Fin dt.ki)) :
      DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) = _
  rw [hmir]
  exact hpt k

end AddrDict

/-! ### The semantic pack, transported along the spine -/

section PackCast

variable [LinearOrder (dt.X.Map A)]

omit [Fintype dt.SlotIx] [L.IsRelational] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] in
/-- **A passing round's valuation depends on the registers alone**: both
states' choices encode the same block value, and the encoding is
injective. -/
theorem passW_congr {zero one : A} (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd)))
    (vi : dt.VarIx)
    {st st' : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    (hmir : st.mir = st'.mir) (hval : st.val = st'.val)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi st ℓ)
    (hp' : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi st' ℓ)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk st.mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
        encMap dt.ly zero one (mbW ℓ))
    (hmb' : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk st'.mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
        encMap dt.ly zero one (mbW ℓ)) :
    dt.passW RF zero one hzo hlin vi st hp mbW =
      dt.passW RF zero one hzo hlin vi st' hp' mbW := by
  funext j
  refine encMap_injective dt.ly hzo ?_
  rw [← dt.passW_hENC RF hzo hlin vi st hp mbW hmb j,
    ← dt.passW_hENC RF hzo hlin vi st' hp' mbW hmb' j,
    dt.lvSet_congr vi hmir hval j]

omit [Fintype dt.SlotIx] [L.IsRelational] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] in
/-- **The pass's pack transports to the pass's pack**: what a spine
position's `hsem` is discharged by, when its pack is the entry state's
carried forward by `kindSemCast`. -/
theorem kindSemCast_passSem {zero one : A} (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd)))
    (vi : dt.VarIx)
    {st st' : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    (hmir : st.mir = st'.mir) (hval : st.val = st'.val)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi st ℓ)
    (hp' : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi st' ℓ)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk st.mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
        encMap dt.ly zero one (mbW ℓ))
    (hmb' : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk st'.mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
        encMap dt.ly zero one (mbW ℓ))
    (b : Fin (dt.natOf vi)) :
    dt.kindSemCast zero one vi hmir hval (dt.kindOf vi b)
        (dt.passSem RF hzo hlin vi st hp mbW hmb b) =
      dt.passSem RF hzo hlin vi st' hp' mbW hmb' b :=
  dt.kindSemCast_mkKindSem zero one vi hmir hval
    (dt.passW_congr RF hzo hlin vi hmir hval hp hp' mbW hmb hmb')
    (dt.passW_hENC RF hzo hlin vi st hp mbW hmb)
    (dt.passW_hENC RF hzo hlin vi st' hp' mbW hmb') (dt.kindOf vi b)

section OnePack

variable {ιV : Type}

/-- **One pack, carried to every position of the spine**: the packs of the
positions are the entry state's, transported. This is what makes the
per-position family *definable* — the recursion that builds the tape
family needs a pack at each of its own states, and here it has one as soon
as the mirror rides. -/
noncomputable def spineSem (zero one : A) (vi : dt.VarIx)
    {st₀ st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    (mV : ιV → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (sem₀ : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF zero one vi (dt.roundSt st₀ (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf vi),
        dt.KindSem zero one vi (dt.roundSt st₀ (mV a)) (dt.kindOf vi b))
    (hmir : st.mir = st₀.mir) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn vi),
      dt.igPassP RF zero one vi (dt.roundSt st (mV a)) ℓ)
    (b : Fin (dt.natOf vi)) :
    dt.KindSem zero one vi (dt.roundSt st (mV a)) (dt.kindOf vi b) :=
  dt.kindSemCast zero one vi (st := dt.roundSt st₀ (mV a))
    (st' := dt.roundSt st (mV a)) hmir.symm rfl (dt.kindOf vi b)
    (sem₀ a (fun ℓ =>
      (dt.igPassP_roundSt RF zero one vi st st₀ (mV a) ℓ).mp (hp ℓ)) b)

/-- **One pack, carried to every round of every position — threaded**: as
`DescriptiveComplexity.Draw.DrawData.spineSem`, at the states the VAL loop's
own thread produces. Those differ from the position's entry state in the
two scratch registers and the register they enumerate, and a pack reads
the state through the mirror and VAL alone, so the entry state's pack
transports to all of them. -/
noncomputable def spineSemT (zero one : A) (vi : dt.VarIx)
    {st₀ st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    {v : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (mV : ιV → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (sem₀ : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF zero one vi (dt.roundSt st₀ (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf vi),
        dt.KindSem zero one vi (dt.roundSt st₀ (mV a)) (dt.kindOf vi b))
    (hmir : st.mir = st₀.mir)
    (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn vi),
      dt.igPassP RF zero one vi (dt.varRdSt st p (mV a)) ℓ)
    (b : Fin (dt.natOf vi)) :
    dt.KindSem zero one vi
      (dt.matSt vi (dt.varRdSt st p (mV a)) v (b : ℕ)) (dt.kindOf vi b) :=
  dt.kindSemCast zero one vi
    (st := dt.varRdSt st p (mV a))
    (st' := dt.matSt vi (dt.varRdSt st p (mV a)) v (b : ℕ))
    ((dt.matSt_fields (v := v) (st := dt.varRdSt st p (mV a)) (b : ℕ)).2.1).symm
    ((dt.matSt_fields (v := v)
      (st := dt.varRdSt st p (mV a)) (b : ℕ)).2.2.2.1).symm
    (dt.kindOf vi b)
    (dt.kindSemCast zero one vi (st := dt.roundSt st₀ (mV a))
      (st' := dt.varRdSt st p (mV a)) hmir.symm rfl (dt.kindOf vi b)
      (sem₀ a (fun ℓ =>
        (dt.igPassP_congr RF zero one vi
          (st := dt.varRdSt st p (mV a))
          (st' := dt.roundSt st₀ (mV a)) rfl ℓ).mp (hp ℓ)) b))

omit [Fintype dt.SlotIx] [L.IsRelational] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] in
/-- **A carried pack is the pass's pack**: so a family defined by
`spineSem` discharges every position's `hsem`
(`new_last_next`, `new_last_trackOf`). -/
theorem spineSem_passSem {zero one : A} (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd)))
    (vi : dt.VarIx)
    {st₀ st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
    (mV : ιV → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (sem₀ : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF zero one vi (dt.roundSt st₀ (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf vi),
        dt.KindSem zero one vi (dt.roundSt st₀ (mV a)) (dt.kindOf vi b))
    (hmir : st.mir = st₀.mir)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hsem₀ : ∀ (a : ιV)
      (hp₀ : ∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF zero one vi (dt.roundSt st₀ (mV a)) ℓ)
      (b : Fin (dt.natOf vi))
      (hm₀ : ∀ ℓ : Fin (dt.arOf vi),
        wmBlk (dt.roundSt st₀ (mV a)).mir
          (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
          encMap dt.ly zero one (mbW ℓ)),
      sem₀ a hp₀ b =
        dt.passSem RF hzo hlin vi (dt.roundSt st₀ (mV a)) hp₀ mbW hm₀ b)
    (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn vi),
      dt.igPassP RF zero one vi (dt.roundSt st (mV a)) ℓ)
    (b : Fin (dt.natOf vi))
    (hm : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk (dt.roundSt st (mV a)).mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
        encMap dt.ly zero one (mbW ℓ)) :
    dt.spineSem RF zero one vi mV sem₀ hmir a hp b =
      dt.passSem RF hzo hlin vi (dt.roundSt st (mV a)) hp mbW hm b := by
  have hm₀ : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk (dt.roundSt st₀ (mV a)).mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
        encMap dt.ly zero one (mbW ℓ) := by
    intro ℓ
    rw [show (dt.roundSt st₀ (mV a)).mir = st₀.mir from rfl, ← hmir]
    exact hm ℓ
  refine Eq.trans (congrArg
    (dt.kindSemCast zero one vi (st := dt.roundSt st₀ (mV a))
      (st' := dt.roundSt st (mV a)) hmir.symm rfl (dt.kindOf vi b))
    (hsem₀ a _ b hm₀)) ?_
  exact dt.kindSemCast_passSem RF hzo hlin vi (st := dt.roundSt st₀ (mV a))
    (st' := dt.roundSt st (mV a)) hmir.symm rfl _ hp mbW hm₀ hm b

end OnePack

end PackCast

/-! ### What a gated position knows

The branch `DescriptiveComplexity.Draw.DrawData.gatedAt` takes is not merely
the one where the machine runs the machinery: it is the one where the
argument blocks **are** encodings, which is what a semantic pack needs to
exist at all. `DescriptiveComplexity.Draw.DrawData.gate_trichotomy` says the
three legs are exhaustive; read in the other direction it says a gated
position's blocks encode points. -/

omit [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx] [L.IsRelational] [Finite R] in
/-- **A gated position's argument blocks are encodings** — the converse of
`testOf_of_encMap`/`wit_of_encMap`/`domHolds_of_encMap`, off the
trichotomy. This is what makes a position's semantic pack *constructible*
rather than assumed: at a junk position no pack exists, and at a gated one
the points are the blocks' own. -/
theorem isEnc_of_gatedAt (hzo : PR.zero ≠ PR.one)
    (hlin : IsLinOrd
      (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hg : dt.gatedAt (PR := PR) RF j st)
    (ℓ : Fin (dt.arOf (dt.varAt j))) :
    IsEnc dt.ly PR.zero PR.one
      (wmBlk st.mir
        (DrawTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)) := by
  classical
  have hpt : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.mir =
      bitVal PR.zero PR.one (bitAtOf RF.cell st.mir r) := fun _ => rfl
  rcases dt.gate_trichotomy RF hzo hlin st
    (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ)) with
    h | ⟨u₀, hbad⟩ | ⟨-, hbad⟩
  · exact h
  · refine absurd ?_ hbad
    have h := hg.1 ℓ u₀
    rwa [shapeAt, passTracks_of_back RF.toIx hpt (RF.cell u₀)] at h
  · exact absurd ⟨(hg.2 ℓ).1, (hg.2 ℓ).2⟩ hbad

omit [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx] [L.IsRelational] [Finite R] in
/-- **A position whose blocks are encodings is gated** — the converse of
`isEnc_of_gatedAt`, assembled from
`DescriptiveComplexity.Draw.DrawData.testOf_of_encMap`,
`wit_of_encMap` and `domHolds_of_encMap`. With the two directions together,
gating at a position *is* «the blocks below that variable's arity encode
points», which is the dichotomy a sweep's dictionary splits on — and it is
per variable, since the arities differ. -/
theorem gatedAt_of_isEnc (hzo : PR.zero ≠ PR.one)
    (hlin : IsLinOrd
      (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (henc : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      IsEnc dt.ly PR.zero PR.one
        (wmBlk st.mir
          (DrawTag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))) :
    dt.gatedAt (PR := PR) RF j st := by
  classical
  have hpt : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.mir =
      bitVal PR.zero PR.one (bitAtOf RF.cell st.mir r) := fun _ => rfl
  refine ⟨fun ℓ u => ?_, fun ℓ => ?_⟩
  · obtain ⟨p, hp⟩ := henc ℓ
    rw [shapeAt, passTracks_of_back RF.toIx hpt (RF.cell u)]
    exact dt.testOf_of_encMap RF hzo hlin hp u
  · obtain ⟨p, hp⟩ := henc ℓ
    have htag : dt.tagAt (PR := PR) j st ℓ = p.1.1 :=
      dt.dspTagOf_encMap hzo hp
    refine ⟨fun t' => ?_, ?_⟩
    · rw [htag]
      exact dt.wit_of_encMap hzo hp t'
    · rw [htag]
      exact dt.domHolds_of_encMap hzo hp

/-- **A gated position's semantic pack, built** — not assumed. The blocks
are encodings (`isEnc_of_gatedAt`), so their points are the valuation the
pass decodes, and `passSem` builds the pack there; `kindSemCast` carries it
to the state the matrix's atoms run at, which differs from it in the two
scratch registers alone. This is what a branched leg's `semT` is. -/
noncomputable def gatedSem (hzo : PR.zero ≠ PR.one)
    (hlin : IsLinOrd
      (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {v : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    {ιV : Type} (mV : ιV →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (j : Fin dt.nv) (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hg : dt.gatedAt (PR := PR) RF j st)
    (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.KindSem PR.zero PR.one (dt.varAt j)
      (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
      (dt.kindOf (dt.varAt j) b) :=
  dt.kindSemCast PR.zero PR.one (dt.varAt j)
    ((dt.matSt_fields (v := v)
      (st := dt.varRdSt st p (mV a)) (b : ℕ)).2.1).symm
    ((dt.matSt_fields (v := v)
      (st := dt.varRdSt st p (mV a)) (b : ℕ)).2.2.2.1).symm
    (dt.kindOf (dt.varAt j) b)
    (dt.passSem RF hzo hlin (dt.varAt j) (dt.varRdSt st p (mV a)) hp
      (fun ℓ => (dt.isEnc_of_gatedAt RF hzo hlin j st hg ℓ).choose)
      (fun ℓ => (dt.isEnc_of_gatedAt RF hzo hlin j st hg ℓ).choose_spec) b)

/-- **The gated position's pack at the round state** — the same points, at
the state the *semantics* names. `gatedSem` is this pack transported
(`gatedSem_eq_semCastT`), which is what the VAL loop's bridge asks of a
threaded family. -/
noncomputable def gatedSem₀ (hzo : PR.zero ≠ PR.one)
    (hlin : IsLinOrd
      (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {ιV : Type} (mV : ιV →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (j : Fin dt.nv) (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hg : dt.gatedAt (PR := PR) RF j st) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.KindSem PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a))
      (dt.kindOf (dt.varAt j) b) :=
  dt.passSem RF hzo hlin (dt.varAt j) (dt.roundSt st (mV a)) hp
    (fun ℓ => (dt.isEnc_of_gatedAt RF hzo hlin j st hg ℓ).choose)
    (fun ℓ => (dt.isEnc_of_gatedAt RF hzo hlin j st hg ℓ).choose_spec) b

omit [L.IsRelational] [Finite dt.KIx] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] in
/-- **A gated position's pack is one pack transported**: its points are the
address's blocks, which the scratch registers do not touch, so the family
the machinery is run with is `semCastT` at
`DescriptiveComplexity.Draw.DrawData.gatedSem₀` — the hypothesis the VAL
loop's bridge (`varFMT_eq_varFM`) is stated under. -/
theorem gatedSem_eq_semCastT (hzo : PR.zero ≠ PR.one)
    (hlin : IsLinOrd
      (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    {ιV : Type} (mV : ιV →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (j : Fin dt.nv) (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hg : dt.gatedAt (PR := PR) RF j st) :
    dt.gatedSem RF hzo hlin mV (v := v) j st hg =
      dt.semCastT RF (dt.varAt j) st v mV (dt.gatedSem₀ RF hzo hlin mV j st hg) := by
  funext p a hp b
  have hval : (dt.varRdSt st p (mV a)).val =
      (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ)).val :=
    ((dt.matSt_fields (v := v) (st := dt.varRdSt st p (mV a)) (b : ℕ)).2.2.2.1).symm
  have hpA : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.igPassP RF PR.zero PR.one (dt.varAt j)
        (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ)) ℓ :=
    fun ℓ => (dt.igPassP_congr RF PR.zero PR.one (dt.varAt j) hval ℓ).mp (hp ℓ)
  have hmbA : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      wmBlk (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ)).mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx) =
        encMap dt.ly PR.zero PR.one
          ((dt.isEnc_of_gatedAt RF hzo hlin j st hg ℓ).choose) := by
    intro ℓ
    rw [(dt.matSt_fields (v := v) (st := dt.varRdSt st p (mV a)) (b : ℕ)).2.1]
    exact (dt.isEnc_of_gatedAt RF hzo hlin j st hg ℓ).choose_spec
  exact (dt.kindSemCast_passSem RF hzo hlin (dt.varAt j) _ _ hp hpA _ _ hmbA b).trans
    (dt.kindSemCast_passSem RF hzo hlin (dt.varAt j) _ _ _ hpA _ _ hmbA b).symm

omit [Finite dt.KIx] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] in
/-- **A gated position's stage bit is the verdict the semantics reads**:
the branched leg takes the gated leg there, its threaded fold is the
unthreaded one (`legCtlT_eq_legCtl`), and its pack is one pack transported
(`gatedSem_eq_semCastT`). This is `new_last_next`'s `hbOf` at the family a
sweep actually runs. -/
theorem legBitB_gatedSem (hzo : PR.zero ≠ PR.one)
    (hlin : IsLinOrd
      (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hreg : ¬∃ u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      v = RF.cell u)
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}
    (mV : ιV → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (j : Fin dt.nv) (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hg : dt.gatedAt (PR := PR) RF j st) (f₀ : dt.CtlIx → A) :
    dt.legBitB (v := v) (aT := aT) RF hord mV j st
        (fun hg' => dt.gatedSem RF hzo hlin mV (v := v) j st hg') f₀ =
      (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
        (dt.legCtl (v := v) (aT := aT) RF hord mV j st (dt.tagAt (PR := PR) j st)
          (dt.gatedSem₀ RF hzo hlin mV j st hg) f₀) := by
  classical
  rw [legBitB, dif_pos hg, dt.gatedSem_eq_semCastT RF hzo hlin mV j st hg,
    dt.legCtlT_eq_legCtl RF hord mV hreg j st (dt.tagAt (PR := PR) j st) _ f₀]

/-! ### The per-position families, built -/

section Family

variable [LinearOrder (dt.X.Map A)]
variable {v : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}
variable (mV : ιV → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
  Prop)
variable (st₀ : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
variable (f₀ : dt.CtlIx → A)
variable (sem₀ : ∀ (j : Fin dt.nv) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.roundSt st₀ (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.KindSem PR.zero PR.one (dt.varAt j) (dt.roundSt st₀ (mV a))
      (dt.kindOf (dt.varAt j) b))
variable (tOf : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)

/-- **One node of the spine**: the tape state, the proof that its mirror is
still the address's — which is what lets the *next* node build its pack —
and the control. The three have to be produced together: the pack a
position's leg needs is typed at that position's state, and is available
only because the mirror rode (`spineSem`). -/
noncomputable def spineNode :
    ℕ → Σ' st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)),
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := spineNode n
    if h : n < dt.nv then
      let f' := dt.legCtl (v := v) (aT := aT) RF hord mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
        (dt.spineSem RF PR.zero PR.one (dt.varAt ⟨n, h⟩) mV (sem₀ ⟨n, h⟩)
          prev.2.1) prev.2.2
      ⟨dt.postVarSt v prev.1 (mV aT) (dt.varList.get ⟨n, h⟩)
          ((dt.varArgsOf PR.zero PR.one (dt.varAt ⟨n, h⟩)).accBit f'),
        prev.2.1, f'⟩
    else prev

/-- The tape family of the spine. -/
noncomputable def spineStOf (k : Fin (dt.nv + 1)) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  (dt.spineNode (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf (k : ℕ)).1

/-- The control family of the spine. -/
noncomputable def spineFsOf (k : Fin (dt.nv + 1)) : dt.CtlIx → A :=
  (dt.spineNode (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf (k : ℕ)).2.2

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The mirror rides the built family** — by construction, not by the
after-the-fact induction of `spine_mir`. -/
theorem spineStOf_mir (k : Fin (dt.nv + 1)) :
    (dt.spineStOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf k).mir = st₀.mir :=
  (dt.spineNode (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf (k : ℕ)).2.1

/-- The packs of the built family: the entry state's, carried. -/
noncomputable def spineSemOf (j : Fin dt.nv) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.igPassP RF PR.zero PR.one (dt.varAt j)
        (dt.roundSt (dt.spineStOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
          j.castSucc) (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.KindSem PR.zero PR.one (dt.varAt j)
      (dt.roundSt (dt.spineStOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
        j.castSucc) (mV a)) (dt.kindOf (dt.varAt j) b) :=
  dt.spineSem RF PR.zero PR.one (dt.varAt j) mV (sem₀ j)
    (dt.spineStOf_mir (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc)
    a hp b

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem spineStOf_zero :
    dt.spineStOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf 0 = st₀ := rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem spineFsOf_zero :
    dt.spineFsOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf 0 = f₀ := rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The control's cover equation** — `evalSpine_run`'s `hfs`. -/
theorem spineFsOf_succ (j : Fin dt.nv) :
    dt.spineFsOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.succ =
      dt.legCtl (v := v) (aT := aT) RF hord mV j
        (dt.spineStOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc)
        (tOf j)
        (dt.spineSemOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j)
        (dt.spineFsOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc) := by
  change (dt.spineNode (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
    ((j : ℕ) + 1)).2.2 = _
  rw [spineNode, dif_pos j.isLt]
  rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The tape's cover equation** — `evalSpine_run`'s `hst`. -/
theorem spineStOf_succ (j : Fin dt.nv) :
    dt.spineStOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.succ =
      dt.postVarSt v
        (dt.spineStOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc)
        (mV aT) (dt.varList.get j)
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.legCtl (v := v) (aT := aT) RF hord mV j
            (dt.spineStOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc)
            (tOf j)
            (dt.spineSemOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j)
            (dt.spineFsOf (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
              j.castSucc))) := by
  change (dt.spineNode (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
    ((j : ℕ) + 1)).1 = _
  rw [spineNode, dif_pos j.isLt]
  rfl

/-! ### The per-position families, threaded -/

/-- **One node of the spine, threaded**: as
`DescriptiveComplexity.Draw.DrawData.spineNode`, with the leg's own exit
state — SAV and TARGET as its VAL loop left them — instead of the
normalized one. The mirror still rides, which is what makes the next
position's pack exist. -/
noncomputable def spineNodeT :
    ℕ → Σ' st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)),
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := spineNodeT n
    if h : n < dt.nv then
      ⟨dt.legStT (v := v) (aT := aT) RF hord mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.spineSemT RF PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2,
        (dt.legStT_fields (v := v) (aT := aT) RF hord mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.spineSemT RF PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2).1.trans prev.2.1,
        dt.legCtlT (v := v) (aT := aT) RF hord mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.spineSemT RF PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2⟩
    else prev

/-- The threaded tape family of the spine. -/
noncomputable def spineStOfT (k : Fin (dt.nv + 1)) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  (dt.spineNodeT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf (k : ℕ)).1

/-- The threaded control family of the spine. -/
noncomputable def spineFsOfT (k : Fin (dt.nv + 1)) : dt.CtlIx → A :=
  (dt.spineNodeT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf (k : ℕ)).2.2

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The mirror rides the threaded family too** — by construction. -/
theorem spineStOfT_mir (k : Fin (dt.nv + 1)) :
    (dt.spineStOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf k).mir = st₀.mir :=
  (dt.spineNodeT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf (k : ℕ)).2.1

/-- The packs of the threaded family: the address's entry state's,
transported to the loop's own states. -/
noncomputable def spineSemOfT (j : Fin dt.nv)
    (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.igPassP RF PR.zero PR.one (dt.varAt j)
        (dt.varRdSt (dt.spineStOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
          j.castSucc) p (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.KindSem PR.zero PR.one (dt.varAt j)
      (dt.matSt (dt.varAt j)
        (dt.varRdSt (dt.spineStOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
          j.castSucc) p (mV a)) v (b : ℕ))
      (dt.kindOf (dt.varAt j) b) :=
  dt.spineSemT RF PR.zero PR.one (dt.varAt j) (v := v) mV (sem₀ j)
    (dt.spineStOfT_mir (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc)
    p a hp b

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem spineStOfT_zero :
    dt.spineStOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf 0 = st₀ := rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem spineFsOfT_zero :
    dt.spineFsOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf 0 = f₀ := rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The threaded control's cover equation** — `evalSpine_run_thread`'s
`hfs`. -/
theorem spineFsOfT_succ (j : Fin dt.nv) :
    dt.spineFsOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.succ =
      dt.legCtlT (v := v) (aT := aT) RF hord mV j
        (dt.spineStOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc)
        (tOf j)
        (dt.spineSemOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j)
        (dt.spineFsOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc) := by
  change (dt.spineNodeT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
    ((j : ℕ) + 1)).2.2 = _
  rw [spineNodeT, dif_pos j.isLt]
  rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The threaded tape's cover equation** — `evalSpine_run_thread`'s
`hst`. -/
theorem spineStOfT_succ (j : Fin dt.nv) :
    dt.spineStOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.succ =
      dt.legStT (v := v) (aT := aT) RF hord mV j
        (dt.spineStOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc)
        (tOf j)
        (dt.spineSemOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j)
        (dt.spineFsOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf j.castSucc) := by
  change (dt.spineNodeT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
    ((j : ℕ) + 1)).1 = _
  rw [spineNodeT, dif_pos j.isLt]
  rfl

/-! ### The per-position families, branched

The threaded family above runs the gated leg at every position, which a
sweep cannot afford: it visits junk addresses too. The branched family
takes whichever of the three legs each position's own gates call for
(`DescriptiveComplexity.Draw.DrawData.legStB`), and is otherwise the same
recursion — the mirror still rides, because no leg writes it.

Its semantic parameter is **not** the entry state's pack transported: it is
the *conditioned* family `DescriptiveComplexity.Draw.DrawData.gatedSem`
inhabits — a pack at every gated position of every state, at every address.
Conditioned, because at a junk position no pack exists (the argument blocks
encode nothing there); quantified over the address as well, because
`DescriptiveComplexity.Draw.DrawData.stEndB` runs this spine at `v := w` for
an address `w` its own binders are fixed before. With that type the
parameter is supplied outright at the top — `fun w => dt.gatedSem hzo hlin
mV` — and no semantic assumption about a position survives in the run
layer. -/

variable (semB : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
    dt.dd → Prop) (j : Fin dt.nv)
  (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))),
  dt.gatedAt (PR := PR) RF j st →
  ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.KindSem PR.zero PR.one (dt.varAt j)
      (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) w (b : ℕ))
      (dt.kindOf (dt.varAt j) b))

/-- **One node of the spine, branched**. -/
noncomputable def spineNodeB :
    ℕ → Σ' st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)),
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := spineNodeB n
    if h : n < dt.nv then
      ⟨dt.legStB (v := v) (aT := aT) RF hord mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2,
        (dt.legStB_fields (v := v) (aT := aT) RF hord mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2).1.trans prev.2.1,
        dt.legCtlB (v := v) (aT := aT) RF hord mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2⟩
    else prev

/-- The branched tape family of the spine. -/
noncomputable def spineStOfB (k : Fin (dt.nv + 1)) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  (dt.spineNodeB (v := v) (aT := aT) RF hord mV st₀ f₀ semB (k : ℕ)).1

/-- The branched control family of the spine. -/
noncomputable def spineFsOfB (k : Fin (dt.nv + 1)) : dt.CtlIx → A :=
  (dt.spineNodeB (v := v) (aT := aT) RF hord mV st₀ f₀ semB (k : ℕ)).2.2

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The mirror rides the branched family** — by construction. -/
theorem spineStOfB_mir (k : Fin (dt.nv + 1)) :
    (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB k).mir = st₀.mir :=
  (dt.spineNodeB (v := v) (aT := aT) RF hord mV st₀ f₀ semB (k : ℕ)).2.1

/-- The packs of the branched family: the parameter's own, at the position's
state — the gate being what makes them exist. -/
noncomputable def spineSemOfB (j : Fin dt.nv)
    (hg : dt.gatedAt (PR := PR) RF j
      (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc))
    (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.igPassP RF PR.zero PR.one (dt.varAt j)
        (dt.varRdSt (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB
          j.castSucc) p (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.KindSem PR.zero PR.one (dt.varAt j)
      (dt.matSt (dt.varAt j)
        (dt.varRdSt (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB
          j.castSucc) p (mV a)) v (b : ℕ))
      (dt.kindOf (dt.varAt j) b) :=
  semB v j (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc) hg p a
    hp b

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem spineStOfB_zero :
    dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB 0 = st₀ := rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem spineFsOfB_zero :
    dt.spineFsOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB 0 = f₀ := rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The branched control's cover equation** — `evalSpineB_run`'s
`hfs`. -/
theorem spineFsOfB_succ (j : Fin dt.nv) :
    dt.spineFsOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.succ =
      dt.legCtlB (v := v) (aT := aT) RF hord mV j
        (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc)
        (dt.spineSemOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j)
        (dt.spineFsOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc) := by
  change (dt.spineNodeB (v := v) (aT := aT) RF hord mV st₀ f₀ semB ((j : ℕ) + 1)).2.2 = _
  rw [spineNodeB, dif_pos j.isLt]
  rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The branched tape's cover equation** — `evalSpineB_run`'s `hst`. -/
theorem spineStOfB_succ (j : Fin dt.nv) :
    dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.succ =
      dt.legStB (v := v) (aT := aT) RF hord mV j
        (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc)
        (dt.spineSemOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j)
        (dt.spineFsOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc) := by
  change (dt.spineNodeB (v := v) (aT := aT) RF hord mV st₀ f₀ semB ((j : ℕ) + 1)).1 = _
  rw [spineNodeB, dif_pos j.isLt]
  rfl

/-- **The verdicts of the branched family**: at each position, the stage
bit its own leg writes. -/
noncomputable def spineBitOfB (j : Fin dt.nv) : Prop :=
  dt.legBitB (v := v) (aT := aT) RF hord mV j
    (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc)
    (dt.spineSemOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j)
    (dt.spineFsOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The branched family writes what a spine writes** — the projection of
the cover equation the `new` tracks read, which is all the dictionary
lemmas ask of a leg (`DescriptiveComplexity.Draw.DrawData.legStB_new`). -/
theorem spineStOfB_writesNew :
    dt.WritesNew (v := v) (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB)
      (dt.spineBitOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB) := by
  intro j i' r
  rw [dt.spineStOfB_succ (v := v) (aT := aT) RF hord mV st₀ f₀ semB j,
    dt.legStB_new (v := v) (aT := aT) RF hord mV j _ _ _ i' r]
  rfl

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **A field no leg writes rides the branched spine.** -/
theorem spineRideB {β : Sort _}
    (F : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) → β)
    (hF : ∀ (j : Fin dt.nv)
      (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (semT : dt.gatedAt (PR := PR) RF j st →
        ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.igPassP RF PR.zero PR.one (dt.varAt j)
            (dt.varRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.KindSem PR.zero PR.one (dt.varAt j)
            (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
            (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      F (dt.legStB (v := v) (aT := aT) RF hord mV j st semT f) = F st)
    (k : Fin (dt.nv + 1)) :
    F (dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB k) = F st₀ := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := dt.spineStOfB_succ (v := v) (aT := aT) RF hord mV st₀ f₀ semB
      ⟨n, hnv⟩
    exact Eq.trans (congrArg F hstep) (Eq.trans (hF _ _ _ _) (ih _))

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **A field a threaded leg leaves alone rides the whole spine** — the
twin of `DescriptiveComplexity.Draw.DrawData.spineRide` at the legs the
threaded family is built from. -/
theorem spineRideT {β : Sort _}
    (F : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) → β)
    (hF : ∀ (j : Fin dt.nv)
      (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (tOf' : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
      (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
        (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.igPassP RF PR.zero PR.one (dt.varAt j)
            (dt.varRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.KindSem PR.zero PR.one (dt.varAt j)
            (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
            (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      F (dt.legStT (v := v) (aT := aT) RF hord mV j st tOf' semT f) = F st)
    (k : Fin (dt.nv + 1)) :
    F (dt.spineStOfT (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf k) = F st₀ := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := dt.spineStOfT_succ (v := v) (aT := aT) RF hord mV st₀ f₀ sem₀ tOf
      ⟨n, hnv⟩
    exact Eq.trans (congrArg F hstep) (Eq.trans (hF _ _ _ _ _) (ih _))

/-! ### The branched spine's dictionary at one address

Gating is per variable, and so is the reading: at an address whose blocks
below a variable's arity all encode points, that variable's cell holds one
step of the iteration there; where one of them does not, the position takes
an ungated leg, writes `False`, and the dictionary is `False` too. Nothing
is assumed of the *other* variables' blocks — which is what a sweep needs,
since it passes every address. -/

omit [Finite dt.KIx] in
/-- **What the branched spine leaves at one address, per variable.** -/
theorem new_last_trackOf_B
    (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF))
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (hreg : ¬∃ u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      v = RF.cell u)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (hmir₀ : st₀.mir = v)
    {Below : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι)
      (s : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      Below s → (st₀.old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))),
      Below (dt.stageTgtD PR.zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) v (dt.d.B.arity iv)))
    (i : dt.d.B.ι) :
    ((dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀
        (fun w j st hg => dt.gatedSem RF PR.zero_ne_one hlin mV (v := w) j st hg)
        (Fin.last dt.nv)).new i v ↔
      trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i)) (dt.d.next σ) v) := by
  classical
  obtain ⟨j, hj⟩ := dt.exists_varList_get i
  subst hj
  set semB : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) (j : Fin dt.nv)
      (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))),
      dt.gatedAt (PR := PR) RF j st → _ :=
    fun w j st hg => dt.gatedSem RF PR.zero_ne_one hlin mV (v := w) j st hg
    with hsemB
  set stj := dt.spineStOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j.castSucc
    with hstj
  have hmirj : stj.mir = st₀.mir :=
    dt.spineStOfB_mir RF hord mV st₀ f₀ semB j.castSucc
  have holdj : stj.old = st₀.old :=
    dt.spineRideB RF hord mV st₀ f₀ semB (fun st => st.old)
      (fun j' st' semT f' =>
        (dt.legStB_fields (aT := aT) RF hord mV j' st' semT f').2.2.2.1) j.castSucc
  have hwr := dt.spineStOfB_writesNew (v := v) (aT := aT) RF hord mV st₀ f₀ semB
  by_cases hg : dt.gatedAt (PR := PR) RF j stj
  · -- the blocks below this variable's arity encode: the cell is one step
    have hmb : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        dt.mirBlk st₀ (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) =
          encMap dt.ly PR.zero PR.one
            ((dt.isEnc_of_gatedAt RF PR.zero_ne_one hlin j stj hg ℓ).choose) :=
      fun ℓ => (congrFun (mirBlk_of_mir hmirj) _).symm.trans
        ((dt.isEnc_of_gatedAt RF PR.zero_ne_one hlin j stj hg ℓ).choose_spec)
    refine (dt.new_last_next_at RF mV hlin hord hbotV hmV0 hIncr hKin hTop σ j
      (dt.gatedSem₀ RF PR.zero_ne_one hlin mV j stj hg)
      (dt.varFG (PR := PR) RF (dt.varAt j) stj v (dt.tagAt (PR := PR) j stj)
        (dt.spineFsOfB RF hord mV st₀ f₀ semB j.castSucc))
      hwr hmirj holdj
      (iff_of_eq (dt.legBitB_gatedSem RF hord PR.zero_ne_one hlin hreg mV j stj hg
        (dt.spineFsOfB RF hord mV st₀ f₀ semB j.castSucc)))
      _ hmb hdict (fun a iv' ts => hbelow j a iv' ts _) hordP
      (fun _ _ _ _ => rfl)).trans ?_
    refine (trackOf_of_blocks PR.zero_ne_one (dt.arOf_le_ko
      (some (dt.varList.get j))) (dt.d.next σ) (fun ℓ => ?_)).symm
    rw [← hmir₀]
    exact hmb ℓ
  · -- one of them does not: the position writes `False`, and so does the
    -- dictionary
    have hbit : ¬dt.spineBitOfB (v := v) (aT := aT) RF hord mV st₀ f₀ semB j := by
      rw [spineBitOfB, legBitB, dif_neg hg]
      exact id
    refine iff_of_false (fun hc => hbit ((dt.new_last_get hwr j).mp hc)) ?_
    obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ : Fin (dt.arOf (dt.varAt j)),
        ¬IsEnc dt.ly PR.zero PR.one
          (wmBlk stj.mir
            (DrawTag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)) := by
      by_contra hc
      exact hg (dt.gatedAt_of_isEnc RF PR.zero_ne_one hlin j stj
        (fun ℓ => not_not.mp fun h => hc ⟨ℓ, h⟩))
    refine not_trackOf_of_notEnc (dt.arOf_le_ko (some (dt.varList.get j)))
      (dt.d.next σ) (ℓ₀ := ℓ₀) (fun p hp => hℓ₀ ⟨p, ?_⟩)
    rw [hmirj, hmir₀]
    exact hp

end Family

/-! ### The sweep's families, over an arbitrary per-address leg

Everything the sweep's families need of an address's evaluation is *what
state and control it ends in*. Taking those two as parameters makes the
whole layer — the iteration, its two cover equations, and the ride lemmas
that discharge `reaches_sweep`'s `hwkE`/`hmirE`/`hltpE` — serve any
evaluation: the spine as first built, its threaded twin, and the branched
form a junk address will need. -/

section SweepGen

variable (stE : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
    Prop) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) →
  (dt.CtlIx → A) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
variable (fsE : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
    Prop) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) →
  (dt.CtlIx → A) → dt.CtlIx → A)
variable (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh
  (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
variable (st₀ : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
variable (f₀ : dt.CtlIx → A)

/-- **The pair the sweep arrives at each address with**: the base at the
empty address, and at every increment the previous address's evaluation
exit — its marker moved on and its mirror set to the new address, exactly
the shape `DescriptiveComplexity.Draw.DrawData.reaches_sweep` demands. -/
noncomputable def sweepPairG
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) × (dt.CtlIx → A) :=
  addrIter (isLinOrd_wmSetLe hlin) (st₀, f₀)
    (fun u p =>
      ({ dt.atSt (stE u p.1 p.2) (wmNext hlin u) with mir := wmNext hlin u },
        fsE u p.1 p.2)) w

/-- The sweep's tape family — `reaches_sweep`'s `SW`. -/
noncomputable def sweepSWG
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  (dt.sweepPairG stE fsE hlin st₀ f₀ w).1

/-- The sweep's control family — `reaches_sweep`'s `FS`. -/
noncomputable def sweepFSG
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  (dt.sweepPairG stE fsE hlin st₀ f₀ w).2

/-- The state the sweep leaves each address in — `reaches_sweep`'s
`stE`. -/
noncomputable def sweepStEG
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  stE w (dt.sweepSWG stE fsE hlin st₀ f₀ w) (dt.sweepFSG stE fsE hlin st₀ f₀ w)

/-- The control the sweep leaves each address in — `reaches_sweep`'s
`fsE`. -/
noncomputable def sweepFsEG
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  fsE w (dt.sweepSWG stE fsE hlin st₀ f₀ w) (dt.sweepFSG stE fsE hlin st₀ f₀ w)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
theorem sweepSWG_bot :
    dt.sweepSWG stE fsE hlin st₀ f₀ (fun _ => False) = st₀ :=
  congrArg Prod.fst (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
theorem sweepFSG_bot :
    dt.sweepFSG stE fsE hlin st₀ f₀ (fun _ => False) = f₀ :=
  congrArg Prod.snd (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **The tape's cover equation** — `reaches_sweep`'s `hSW`, on the nose. -/
theorem sweepSWG_incr
    {w w' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.sweepSWG stE fsE hlin st₀ f₀ w' =
      { dt.atSt (dt.sweepStEG stE fsE hlin st₀ f₀ w) w' with mir := w' } := by
  have h := congrArg Prod.fst
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (stE u p.1 p.2) (wmNext hlin u) with mir := wmNext hlin u },
          fsE u p.1 p.2)))
  rw [wmNext_eq hlin hi] at h
  exact h

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **The control's cover equation** — `reaches_sweep`'s `hFS`. -/
theorem sweepFSG_incr
    {w w' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.sweepFSG stE fsE hlin st₀ f₀ w' =
      dt.sweepFsEG stE fsE hlin st₀ f₀ w :=
  congrArg Prod.snd
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (stE u p.1 p.2) (wmNext hlin u) with mir := wmNext hlin u },
          fsE u p.1 p.2)))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **A field neither an address's evaluation nor the advance writes rides
the whole sweep.** -/
theorem sweepSWG_ride {β : Sort _}
    (F : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) → β)
    (hFE : ∀ u st f, F (stE u st f) = F st)
    (hFa : ∀ st u, F { dt.atSt st u with mir := u } = F st)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    F (dt.sweepSWG stE fsE hlin st₀ f₀ w) = F st₀ := by
  refine holds_of_wideRounds hlin
    (Q := fun u => F (dt.sweepSWG stE fsE hlin st₀ f₀ u) = F st₀) ?_ ?_ w
    hlb hub
  · rw [dt.sweepSWG_bot stE fsE hlin st₀ f₀]
  · intro u u' hi _ _ ih
    rw [dt.sweepSWG_incr stE fsE hlin st₀ f₀ hi, hFa, sweepStEG, hFE]
    exact ih

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **The marker is at the address**, at every entry state of the sweep. -/
theorem sweepSWG_wk (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepSWG stE fsE hlin st₀ f₀ w).wk = fun r => r = w := by
  refine holds_of_wideRounds hlin
    (Q := fun u => (dt.sweepSWG stE fsE hlin st₀ f₀ u).wk = fun r => r = u)
    ?_ ?_ w hlb hub
  · rw [dt.sweepSWG_bot stE fsE hlin st₀ f₀]
    exact hwk₀
  · intro u u' hi _ _ _
    rw [dt.sweepSWG_incr stE fsE hlin st₀ f₀ hi]
    rfl

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **The mirror is at the address**, at every entry state of the sweep. -/
theorem sweepSWG_mir (hmir₀ : st₀.mir = fun _ => False)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepSWG stE fsE hlin st₀ f₀ w).mir = w := by
  refine holds_of_wideRounds hlin
    (Q := fun u => (dt.sweepSWG stE fsE hlin st₀ f₀ u).mir = u) ?_ ?_ w
    hlb hub
  · rw [dt.sweepSWG_bot stE fsE hlin st₀ f₀]
    exact hmir₀
  · intro u u' hi _ _ _
    rw [dt.sweepSWG_incr stE fsE hlin st₀ f₀ hi]

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **`reaches_sweep`'s `hwkE`**: the marker is still at the address when
the address's evaluation ends. -/
theorem sweepStEG_wk (hFE : ∀ u st f, (stE u st f).wk = st.wk)
    (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepStEG stE fsE hlin st₀ f₀ w).wk = fun r => r = w :=
  (hFE w _ _).trans
    (dt.sweepSWG_wk stE fsE hlin st₀ f₀ hwk₀ (s₁ := s₁) w hlb hub)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **`reaches_sweep`'s `hmirE`**: so is the mirror. -/
theorem sweepStEG_mir (hFE : ∀ u st f, (stE u st f).mir = st.mir)
    (hmir₀ : st₀.mir = fun _ => False)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepStEG stE fsE hlin st₀ f₀ w).mir = w :=
  (hFE w _ _).trans
    (dt.sweepSWG_mir stE fsE hlin st₀ f₀ hmir₀ (s₁ := s₁) w hlb hub)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **`reaches_sweep`'s `hltpE`**: the address is not the marked end, the
mark being where the reduction planted it. -/
theorem sweepStEG_ltp (hFE : ∀ u st f, (stE u st f).ltp = st.ltp)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁)
    (hltp₀ : ¬st₀.ltp w) :
    ¬(dt.sweepStEG stE fsE hlin st₀ f₀ w).ltp w := by
  rw [sweepStEG, hFE, dt.sweepSWG_ride stE fsE hlin st₀ f₀ (fun st => st.ltp)
    hFE (fun _ _ => rfl) (s₁ := s₁) w hlb hub]
  exact hltp₀

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **`reaches_sweep`'s `hmirE` when the evaluation sets the mirror
itself**: the variant of
`DescriptiveComplexity.Draw.DrawData.sweepStEG_mir` for an evaluation that
normalizes the mirror to the address it is run at, which makes the
invariant definitional instead of inductive. -/
theorem sweepStEG_mir' (hFE : ∀ u st f, (stE u st f).mir = u)
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    (dt.sweepStEG stE fsE hlin st₀ f₀ w).mir = w :=
  hFE w _ _

end SweepGen

/-! ### The sweep's families -/

section SweepFamily

variable [LinearOrder (dt.X.Map A)]
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}
variable (mV : ιV → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
  Prop)
variable (semOf : ∀ (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
  (j : Fin dt.nv) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.KindSem PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a))
      (dt.kindOf (dt.varAt j) b))
variable (tOf : ∀ (_st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
  (j : Fin dt.nv), Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)

/-- **The state one address's spine ends in**, from the pair it starts
with. -/
noncomputable def stEnd
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  dt.spineStOf (v := w) (aT := aT) RF hord mV st f (semOf st) (tOf st)
    (Fin.last dt.nv)

/-- **The control one address's spine ends in.** -/
noncomputable def fsEnd
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.spineFsOf (v := w) (aT := aT) RF hord mV st f (semOf st) (tOf st)
    (Fin.last dt.nv)

/-! ### The threaded per-address evaluation

The mirror is normalized to the address the evaluation is run at. It is
already there — the advance sets it, and `sweepSWG_mir` proves it — but
writing it makes the equation **definitional**, which is what lets the
pack family be indexed by the address rather than quantified over
arbitrary states. That is the same move as `varRdSt` one scale down, and
for the same reason: a pack at a state whose mirror holds junk does not
exist, so the mirror has to be pinned before the pack is asked for. -/

variable (semAt : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
    dt.dd → Prop)
  (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (j : Fin dt.nv)
  (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.igPassP RF PR.zero PR.one (dt.varAt j)
      (dt.roundSt { st with mir := w } (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.KindSem PR.zero PR.one (dt.varAt j)
      (dt.roundSt { st with mir := w } (mV a)) (dt.kindOf (dt.varAt j) b))
variable (tAt : ∀ (_w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
    dt.dd → Prop)
  (_st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (j : Fin dt.nv),
  Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)

/-- **The state one address's spine ends in, threaded**, with the mirror
pinned at the address. -/
noncomputable def stEndT
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  dt.spineStOfT (v := w) (aT := aT) RF hord mV { st with mir := w } f (semAt w st)
    (tAt w st) (Fin.last dt.nv)

/-- **The control one address's spine ends in, threaded.** -/
noncomputable def fsEndT
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.spineFsOfT (v := w) (aT := aT) RF hord mV { st with mir := w } f (semAt w st)
    (tAt w st) (Fin.last dt.nv)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **The mirror the threaded evaluation ends at is the address**, by
construction — `reaches_sweep`'s `hmirE` through `sweepStEG_mir'`. -/
theorem stEndT_mir
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) :
    (dt.stEndT (aT := aT) RF hord mV semAt tAt w st f).mir = w :=
  dt.spineStOfT_mir (v := w) (aT := aT) RF hord mV { st with mir := w } f (semAt w st)
    (tAt w st) (Fin.last dt.nv)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **What the threaded evaluation leaves alone**: the marker, the bottom
and end marks and the stage dictionary — `reaches_sweep`'s `hwkE` and
`hltpE` through `sweepStEG_wk` and `sweepStEG_ltp`. -/
theorem stEndT_ride {β : Sort _}
    (F : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) → β)
    (hFmir : ∀ (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))) m,
      F { st with mir := m } = F st)
    (hFleg : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
        dt.dd → Prop)
      (j : Fin dt.nv) (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (tOf' : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
      (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
        (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.igPassP RF PR.zero PR.one (dt.varAt j)
            (dt.varRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.KindSem PR.zero PR.one (dt.varAt j)
            (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) w (b : ℕ))
            (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      F (dt.legStT (v := w) (aT := aT) RF hord mV j st tOf' semT f) = F st)
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) :
    F (dt.stEndT (aT := aT) RF hord mV semAt tAt w st f) = F st :=
  (dt.spineRideT (v := w) (aT := aT) RF hord mV { st with mir := w } f (semAt w st)
    (tAt w st) F (fun j st' tOf' semT f' => hFleg w j st' tOf' semT f')
    (Fin.last dt.nv)).trans (hFmir st w)

/-! The branched evaluation's semantic parameter is the conditioned family
of `DescriptiveComplexity.Draw.DrawData.gatedSem`, quantified over the address
as well: `DescriptiveComplexity.Draw.DrawData.stEndB` runs the spine at
`v := w` for an address bound after it. -/

variable (semAtB : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
    dt.dd → Prop) (j : Fin dt.nv)
  (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))),
  dt.gatedAt (PR := PR) RF j st →
  ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.KindSem PR.zero PR.one (dt.varAt j)
      (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) w (b : ℕ))
      (dt.kindOf (dt.varAt j) b))

/-- **The state one address's evaluation ends in**, with each position
taking whichever leg its gates call for and the mirror pinned at the
address — what a sweep over *every* address needs, gated or junk. -/
noncomputable def stEndB
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  dt.spineStOfB (v := w) (aT := aT) RF hord mV { st with mir := w } f semAtB
    (Fin.last dt.nv)

/-- **The control one address's evaluation ends in**, branched. -/
noncomputable def fsEndB
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.spineFsOfB (v := w) (aT := aT) RF hord mV { st with mir := w } f semAtB
    (Fin.last dt.nv)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **`reaches_sweep`'s `hmirE`** for the branched evaluation, by
construction — through `sweepStEG_mir'`. -/
theorem stEndB_mir
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) :
    (dt.stEndB (aT := aT) RF hord mV semAtB w st f).mir = w :=
  dt.spineStOfB_mir (v := w) (aT := aT) RF hord mV { st with mir := w } f semAtB
    (Fin.last dt.nv)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **What the branched evaluation leaves alone** — `reaches_sweep`'s
`hwkE` and `hltpE` through `sweepStEG_wk` and `sweepStEG_ltp`. -/
theorem stEndB_ride {β : Sort _}
    (F : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) → β)
    (hFmir : ∀ (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))) m,
      F { st with mir := m } = F st)
    (hFleg : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
        dt.dd → Prop)
      (j : Fin dt.nv) (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (semT : dt.gatedAt (PR := PR) RF j st →
        ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.igPassP RF PR.zero PR.one (dt.varAt j)
            (dt.varRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.KindSem PR.zero PR.one (dt.varAt j)
            (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) w (b : ℕ))
            (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      F (dt.legStB (v := w) (aT := aT) RF hord mV j st semT f) = F st)
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) :
    F (dt.stEndB (aT := aT) RF hord mV semAtB w st f) = F st :=
  (dt.spineRideB (v := w) (aT := aT) RF hord mV { st with mir := w } f semAtB
    F (fun j st' semT f' => hFleg w j st' semT f')
    (Fin.last dt.nv)).trans (hFmir st w)

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **Off the address it is run at, the branched evaluation leaves the stage
tracks alone** — a position writes its own cell only
(`spine_new_off`). -/
theorem stEndB_new_off
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (f : dt.CtlIx → A) (i : dt.d.B.ι)
    {r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hr : r ≠ w) :
    (dt.stEndB (aT := aT) RF hord mV semAtB w st f).new i r ↔ st.new i r :=
  dt.spine_new_off (dt.spineStOfB_writesNew (v := w) (aT := aT) RF hord mV
    { st with mir := w } f semAtB) (Fin.last dt.nv) i hr

variable (hlin : IsLinOrd (WMLe (A := Univ A R (OuterPh
  (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
variable (st₀ : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
variable (f₀ : dt.CtlIx → A)

/-- **The pair the sweep arrives at each address with**: the base at the
empty address, and at every increment the previous address's spine exit —
its marker moved on and its mirror set to the new address, exactly the
shape `DescriptiveComplexity.Draw.DrawData.reaches_sweep` demands. -/
noncomputable def sweepPair
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) × (dt.CtlIx → A) :=
  addrIter (isLinOrd_wmSetLe hlin) (st₀, f₀)
    (fun u p =>
      ({ dt.atSt (dt.stEnd (aT := aT) RF hord mV semOf tOf u p.1 p.2)
            (wmNext hlin u) with mir := wmNext hlin u },
        dt.fsEnd (aT := aT) RF hord mV semOf tOf u p.1 p.2)) w

/-- The sweep's tape family — `reaches_sweep`'s `SW`. -/
noncomputable def sweepSW
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  (dt.sweepPair (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).1

/-- The sweep's control family — `reaches_sweep`'s `FS`. -/
noncomputable def sweepFS
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  (dt.sweepPair (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).2

/-- The state the sweep leaves each address in — `reaches_sweep`'s
`stE`. -/
noncomputable def sweepStE
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  dt.stEnd (aT := aT) RF hord mV semOf tOf w
    (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w)
    (dt.sweepFS (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w)

/-- The control the sweep leaves each address in — `reaches_sweep`'s
`fsE`. -/
noncomputable def sweepFsE
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  dt.fsEnd (aT := aT) RF hord mV semOf tOf w
    (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w)
    (dt.sweepFS (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w)

omit [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem sweepSW_bot :
    dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ (fun _ => False) = st₀ :=
  congrArg Prod.fst
    (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)

omit [LinearOrder (dt.X.Map A)] [Finite ιV] in
theorem sweepFS_bot :
    dt.sweepFS (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ (fun _ => False) = f₀ :=
  congrArg Prod.snd
    (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)

omit [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The tape's cover equation** — `reaches_sweep`'s `hSW`, on the nose:
the next address's entry state is this one's spine exit, its marker moved
on and its mirror at the new address. -/
theorem sweepSW_incr
    {w w' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w' =
      { dt.atSt (dt.sweepStE (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w) w' with
        mir := w' } := by
  have h := congrArg Prod.fst
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (dt.stEnd (aT := aT) RF hord mV semOf tOf u p.1 p.2)
              (wmNext hlin u) with mir := wmNext hlin u },
          dt.fsEnd (aT := aT) RF hord mV semOf tOf u p.1 p.2)))
  rw [wmNext_eq hlin hi] at h
  exact h

omit [LinearOrder (dt.X.Map A)] [Finite ιV] in
/-- **The control's cover equation** — `reaches_sweep`'s `hFS`: the next
address's entry control is this one's spine exit control. -/
theorem sweepFS_incr
    {w w' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.sweepFS (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w' =
      dt.sweepFsE (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w :=
  congrArg Prod.snd
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (dt.stEnd (aT := aT) RF hord mV semOf tOf u p.1 p.2)
              (wmNext hlin u) with mir := wmNext hlin u },
          dt.fsEnd (aT := aT) RF hord mV semOf tOf u p.1 p.2)))

/-! ### What the sweep's entry and exit states hold -/

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **A field a leg's write leaves alone rides one address's spine.** -/
theorem sweepStE_ride {β : Sort _}
    (F : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) → β)
    (hF : ∀ (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
      st m i b, F (dt.postVarSt u st m i b) = F st)
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    F (dt.sweepStE (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w) =
      F (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w) :=
  dt.spineRide
    (hst := fun j => dt.spineStOf_succ (v := w) (aT := aT) RF hord mV
      (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w)
      (dt.sweepFS (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w)
      (semOf (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w))
      (tOf (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w)) j)
    F (fun st _ i b => hF w st _ i b) (Fin.last dt.nv)

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **A field neither a leg nor the advance writes rides the whole
sweep.** -/
theorem sweepSW_ride {β : Sort _}
    (F : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) → β)
    (hF : ∀ (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
      st m i b, F (dt.postVarSt u st m i b) = F st)
    (hFa : ∀ st u, F { dt.atSt st u with mir := u } = F st)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    F (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w) = F st₀ := by
  refine holds_of_wideRounds hlin
    (Q := fun u => F (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ u) =
      F st₀) ?_ ?_ w hlb hub
  · rw [dt.sweepSW_bot (aT := aT) RF hord mV semOf tOf hlin st₀ f₀]
  · intro u u' hi _ _ ih
    rw [dt.sweepSW_incr (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ hi, hFa,
      dt.sweepStE_ride (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ F hF u]
    exact ih

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **The marker is at the address**, at every entry state of the sweep. -/
theorem sweepSW_wk (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).wk = fun r => r = w := by
  refine holds_of_wideRounds hlin
    (Q := fun u => (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ u).wk =
      fun r => r = u) ?_ ?_ w hlb hub
  · rw [dt.sweepSW_bot (aT := aT) RF hord mV semOf tOf hlin st₀ f₀]
    exact hwk₀
  · intro u u' hi _ _ _
    rw [dt.sweepSW_incr (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ hi]
    rfl

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **The mirror is at the address**, at every entry state of the sweep. -/
theorem sweepSW_mir (hmir₀ : st₀.mir = fun _ => False)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).mir = w := by
  refine holds_of_wideRounds hlin
    (Q := fun u => (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ u).mir = u)
    ?_ ?_ w hlb hub
  · rw [dt.sweepSW_bot (aT := aT) RF hord mV semOf tOf hlin st₀ f₀]
    exact hmir₀
  · intro u u' hi _ _ _
    rw [dt.sweepSW_incr (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ hi]

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **`DescriptiveComplexity.Draw.DrawData.reaches_sweep`'s `hwkE`**: the
marker is still at the address when the address's spine ends. -/
theorem sweepStE_wk (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepStE (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).wk = fun r => r = w :=
  (dt.sweepStE_ride (aT := aT) RF hord mV semOf tOf hlin st₀ f₀
    (fun st => st.wk) (fun _ _ _ _ _ => rfl) w).trans
    (dt.sweepSW_wk (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ hwk₀ (s₁ := s₁) w hlb hub)

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **`reaches_sweep`'s `hmirE`**: so is the mirror. -/
theorem sweepStE_mir (hmir₀ : st₀.mir = fun _ => False)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepStE (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).mir = w :=
  (dt.sweepStE_ride (aT := aT) RF hord mV semOf tOf hlin st₀ f₀
    (fun st => st.mir) (fun _ _ _ _ _ => rfl) w).trans
    (dt.sweepSW_mir (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ hmir₀ (s₁ := s₁) w hlb hub)

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **The permanent `ltp` mark rides the sweep**: neither a leg nor the
advance writes it. -/
theorem sweepStE_ltp_eq
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepStE (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).ltp = st₀.ltp :=
  (dt.sweepStE_ride (aT := aT) RF hord mV semOf tOf hlin st₀ f₀
    (fun st => st.ltp) (fun _ _ _ _ _ => rfl) w).trans
    (dt.sweepSW_ride (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ (fun st => st.ltp)
      (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (s₁ := s₁) w hlb hub)

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **`reaches_sweep`'s `hltpE`**: the address is not the marked end, the
mark being where the reduction planted it. -/
theorem sweepStE_ltp
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁)
    (hltp₀ : ¬st₀.ltp w) :
    ¬(dt.sweepStE (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).ltp w := by
  rw [dt.sweepStE_ltp_eq (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ (s₁ := s₁) w
    hlb hub]
  exact hltp₀

/-! ### The SAV/TGT gap

`DescriptiveComplexity.Draw.DrawData.evalSpine_run` asks, at every address, for
`hsavOf`/`htgtOf` — the SAV and TARGET registers holding *that address* —
because `DescriptiveComplexity.Draw.DrawData.matrix_run` reads them there. But
the advance refreshes only the marker and the mirror (`reaches_sweep`'s
`hSW` is `atSt … with mir := …`), so those two registers **ride** the whole
sweep, and the requirement is met at one address at most. The two lemmas
below are that statement, not a workaround: whichever way the gap is closed
— the advance copying the mirror into SAV and TARGET, the evaluation
refreshing them at its entry, or `matrix_run` reading the mirror instead —
the fix is in the *program*, not here. -/

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **SAV rides the sweep.** -/
theorem sweepSW_sav
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁) :
    (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w).sav = st₀.sav :=
  dt.sweepSW_ride (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ (fun st => st.sav)
    (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (s₁ := s₁) w hlb hub

omit [Finite ιV] [LinearOrder (dt.X.Map A)] in
/-- **So SAV can hold the address at one address only**: the spine's
requirement `(SW w).sav = w` forces the sweep's range to be a single
cell. -/
theorem eq_of_sweepSW_sav
    {s₁ w₁ w₂ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hlb₁ : WMSetLe WMLe (fun _ => False) w₁) (hub₁ : WMSetLe WMLe w₁ s₁)
    (hlb₂ : WMSetLe WMLe (fun _ => False) w₂) (hub₂ : WMSetLe WMLe w₂ s₁)
    (h₁ : (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w₁).sav = w₁)
    (h₂ : (dt.sweepSW (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ w₂).sav = w₂) :
    w₁ = w₂ := by
  rw [← h₁, ← h₂,
    dt.sweepSW_sav (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ (s₁ := s₁) w₁ hlb₁ hub₁,
    dt.sweepSW_sav (aT := aT) RF hord mV semOf tOf hlin st₀ f₀ (s₁ := s₁) w₂ hlb₂ hub₂]

/-! ### The sweep's per-address run

`reaches_sweep` asks for the evaluation's run at each address of the
interval, from the pair the sweep arrives with to the pair it leaves. With
the branched evaluation that is now provable outright: the entry state's
mirror *is* the address (`sweepSWG_mir`, which the advance guarantees), so
pinning it changes nothing, and the marker and the bottom mark ride from
the sweep's base. -/

/-! ### What a whole sweep leaves, in dictionary form

`sweep_new` at the branched evaluation: each address's own reading is
`new_last_trackOf_B`, everything else it leaves alone is `spine_new_off`,
and the next address's entry state is the sweep's own cover equation. Below
the address reached, every stage track holds the dictionary of the *next*
stage; elsewhere it still holds what the sweep started with. -/

/-- **A sweep rewrites the stage tracks of exactly the addresses it has
passed**, at the concrete branched evaluation. -/
theorem sweep_new_trackOf
    (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {Below : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict₀ : ∀ (iv : dt.d.B.ι)
      (s : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      Below s → (st₀.old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
      Below (dt.stageTgtD PR.zero (dt.varAt j) iv ts (dt.roundSt st (mV a)) w
        (dt.d.B.arity iv)))
    {gbot : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (hbot : ∀ y, WMLe gbot y)
    {s₁ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hs₁ : WMSetLt WMLe s₁ (RF.cell gbot)) :
    ∀ w, WMSetLe WMLe (fun _ => False) w → WMSetLe WMLe w s₁ →
      (∀ (i : dt.d.B.ι)
          (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
        WMSetLe WMLe (fun _ => False) r → WMSetLt WMLe r w →
          ((dt.sweepSWG
              (dt.stEndB (aT := aT) RF hord mV
                (fun w' j st hg =>
                  dt.gatedSem RF PR.zero_ne_one hlin mV (v := w') j st hg))
              (dt.fsEndB (aT := aT) RF hord mV
                (fun w' j st hg =>
                  dt.gatedSem RF PR.zero_ne_one hlin mV (v := w') j st hg))
              hlin st₀ f₀ w).new i r ↔
            trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i))
              (dt.d.next σ) r)) ∧
      (∀ (i : dt.d.B.ι)
          (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop),
        ¬(WMSetLe WMLe (fun _ => False) r ∧ WMSetLt WMLe r w) →
          ((dt.sweepSWG
              (dt.stEndB (aT := aT) RF hord mV
                (fun w' j st hg =>
                  dt.gatedSem RF PR.zero_ne_one hlin mV (v := w') j st hg))
              (dt.fsEndB (aT := aT) RF hord mV
                (fun w' j st hg =>
                  dt.gatedSem RF PR.zero_ne_one hlin mV (v := w') j st hg))
              hlin st₀ f₀ w).new i r ↔ st₀.new i r)) := by
  classical
  set semG : ∀ (w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd →
      Prop) (j : Fin dt.nv)
      (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))),
      dt.gatedAt (PR := PR) RF j st → _ :=
    fun w j st hg => dt.gatedSem RF PR.zero_ne_one hlin mV (v := w) j st hg
    with hsemG
  have hset := isLinOrd_wmSetLe hlin
  -- the stage dictionary rides the sweep
  have hold : ∀ w, WMSetLe WMLe (fun _ => False) w → WMSetLe WMLe w s₁ →
      (dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semG)
        (dt.fsEndB (aT := aT) RF hord mV semG) hlin st₀ f₀ w).old = st₀.old :=
    fun w hlb hub => dt.sweepSWG_ride _ _ hlin st₀ f₀ (fun st => st.old)
      (fun u st f => dt.stEndB_ride (aT := aT) RF hord mV semG (fun st => st.old)
        (fun _ _ => rfl)
        (fun _ _ _ _ _ =>
          (dt.legStB_fields (aT := aT) RF hord mV _ _ _ _).2.2.2.1) u st f)
      (fun _ _ => rfl) (s₁ := s₁) w hlb hub
  -- every address of the stretch lies below the register file
  have hreg : ∀ w, WMSetLe WMLe w s₁ →
      ¬∃ u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
        w = RF.cell u := by
    intro w hub
    refine RF.not_exists_cell_of_lt_bot hlin hbot ((wmSetLt_iff _ _).mpr
      ⟨hset.2.1 w s₁ (RF.cell gbot) hub ((wmSetLt_iff _ _).mp hs₁).1, fun hc => ?_⟩)
    exact ((wmSetLt_iff _ _).mp hs₁).2
      (hset.2.2.1 s₁ (RF.cell gbot) ((wmSetLt_iff _ _).mp hs₁).1 (hc ▸ hub))
  have key := dt.sweep_new hlin
    (s₀ := fun _ => False) (s₁ := s₁)
    (SW := dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semG)
      (dt.fsEndB (aT := aT) RF hord mV semG) hlin st₀ f₀)
    (stE := dt.sweepStEG (dt.stEndB (aT := aT) RF hord mV semG)
      (dt.fsEndB (aT := aT) RF hord mV semG) hlin st₀ f₀)
    (N := fun i r =>
      trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some i)) (dt.d.next σ) r)
    (fun w hlb hub i => ?_) (fun w hlb hub i r hr => ?_)
    (fun w w' hi _ _ => dt.sweepSWG_incr _ _ hlin st₀ f₀ hi)
  · intro w hlb hub
    refine ⟨(key w hlb hub).1, fun i r hr => ((key w hlb hub).2 i r hr).trans ?_⟩
    rw [dt.sweepSWG_bot (dt.stEndB (aT := aT) RF hord mV semG)
      (dt.fsEndB (aT := aT) RF hord mV semG) hlin st₀ f₀]
  · -- the address's own cell, by the branched spine's dictionary
    have hub' : WMSetLe WMLe w s₁ := ((wmSetLt_iff _ _).mp hub).1
    exact dt.new_last_trackOf_B RF mV
      { dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semG)
          (dt.fsEndB (aT := aT) RF hord mV semG) hlin st₀ f₀ w with mir := w }
      (dt.sweepFSG (dt.stEndB (aT := aT) RF hord mV semG)
        (dt.fsEndB (aT := aT) RF hord mV semG) hlin st₀ f₀ w)
      hlin hord hbotV hmV0 hIncr hKin hTop (hreg w hub') hordP σ rfl
      (fun iv s hs =>
        (iff_of_eq (congrFun (congrFun (hold w hlb hub') iv) s)).trans
          (hdict₀ iv s hs))
      (fun j a iv ts st => hbelow j a iv ts st w) i
  · -- every other cell rides the address's own evaluation
    exact dt.stEndB_new_off (aT := aT) RF hord mV semG w _ _ i hr

section SweepRun

variable {v' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {rEmb : ∀ i : dt.SEF, dt.SESh i → R}
variable {a₀ : ιV}

omit [LinearOrder (dt.X.Map A)] in
include hlin in
/-- **`DescriptiveComplexity.Draw.DrawData.reaches_sweep`'s `hspine`, at one
address**: the whole per-address evaluation runs, whichever legs each
position's gates call for. -/
theorem reaches_spineB
    (hrules : ∀ (i : dt.SEF) (ρ : dt.SESh i),
      PR.rules (rEmb i ρ) =
        dt.evalRuleF PR.zero PR.one
          (fun w => dt.varArgsOf PR.zero PR.one w) i ρ)
    (hR : PR.table.Reads)
    (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    (hwork : ∀ {r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop},
      ¬r gbot → ∀ u, WMSetLt WMLe r (RF.cell u))
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (hTestF : ∀ a, a < aT → ∃ u, ¬dt.InnerFull (fun u => tagBlk u.1) (mV a) u)
    (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    (hmir₀ : st₀.mir = fun _ => False)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    {s₁ w : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hlb : WMSetLe WMLe (fun _ => False) w) (hub : WMSetLe WMLe w s₁)
    (hv : WMSetLt WMLe w (RF.cell gbot)) (hvi : WMIncr WMLe w v') :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk 0))
          (dt.sweepFSG (dt.stEndB (aT := aT) RF hord mV semAtB)
            (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w)), Sum.inl w,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semAtB)
              (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w))
          (dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semAtB)
            (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last dt.nv)))
          (dt.sweepFsEG (dt.stEndB (aT := aT) RF hord mV semAtB)
            (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w)), Sum.inl w,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.sweepStEG (dt.stEndB (aT := aT) RF hord mV semAtB)
              (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w))
          (dt.sweepStEG (dt.stEndB (aT := aT) RF hord mV semAtB)
            (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hmirSW : (dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semAtB)
      (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w).mir = w :=
    dt.sweepSWG_mir _ _ hlin st₀ f₀ hmir₀ (s₁ := s₁) w hlb hub
  have hwkSW : (dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semAtB)
      (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w).wk = fun r => r = w :=
    dt.sweepSWG_wk _ _ hlin st₀ f₀ hwk₀ (s₁ := s₁) w hlb hub
  have hbotSW : (dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semAtB)
      (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w).bot =
      fun r => r = (fun _ => False) := by
    refine Eq.trans (dt.sweepSWG_ride _ _ hlin st₀ f₀ (fun st => st.bot) ?_
      (fun _ _ => rfl) (s₁ := s₁) w hlb hub) hbot₀
    exact fun u st f => dt.stEndB_ride (aT := aT) RF hord mV semAtB (fun st => st.bot)
      (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields (aT := aT) RF hord mV _ _ _ _).2.2.1) u st f
  -- pinning the mirror at the address is the identity on the entry state
  have hpin : ∀ X : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)),
      X.mir = w → ({ X with mir := w } : TapeStD dt A R
        (OuterPh (EvalPh dt.nv dt.PMF))) = X := by
    intro X hX
    rw [← hX]
  rw [← hpin _ hmirSW]
  refine dt.evalSpineB_run RF hord hrules hR hlin htop hbot hwork hv hvi hbotV htopV
    mV hmV0 hIncr hTestT hTestF
    (stOf := dt.spineStOfB (v := w) (aT := aT) RF hord mV
      { dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semAtB)
          (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w with mir := w }
      (dt.sweepFSG (dt.stEndB (aT := aT) RF hord mV semAtB)
        (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w)
      semAtB)
    (fsOf := dt.spineFsOfB (v := w) (aT := aT) RF hord mV
      { dt.sweepSWG (dt.stEndB (aT := aT) RF hord mV semAtB)
          (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w with mir := w }
      (dt.sweepFSG (dt.stEndB (aT := aT) RF hord mV semAtB)
        (dt.fsEndB (aT := aT) RF hord mV semAtB) hlin st₀ f₀ w)
      semAtB)
    ?_ ?_ ?_
    (semTJ := dt.spineSemOfB (v := w) (aT := aT) RF hord mV _ _ _)
    (fun j => dt.spineStOfB_succ (v := w) (aT := aT) RF hord mV _ _ _ j)
    (fun j => dt.spineFsOfB_succ (v := w) (aT := aT) RF hord mV _ _ _ j)
  · intro k
    refine Eq.trans (dt.spineRideB (v := w) (aT := aT) RF hord mV _ _ _
      (fun st => st.wk)
      (fun _ _ _ _ => (dt.legStB_fields (aT := aT) RF hord mV _ _ _ _).2.1) k) hwkSW
  · intro j
    exact dt.spineStOfB_mir (v := w) (aT := aT) RF hord mV _ _ _ j.castSucc
  · intro j
    refine Eq.trans (dt.spineRideB (v := w) (aT := aT) RF hord mV _ _ _
      (fun st => st.bot)
      (fun _ _ _ _ => (dt.legStB_fields (aT := aT) RF hord mV _ _ _ _).2.2.1)
      j.castSucc) hbotSW

end SweepRun

end SweepFamily

/-! ### The stage atom's restore, as an algebra

`DescriptiveComplexity.Draw.DrawData.stageEndSt st v = { st with sav := v,
tgt := v }`: the random access **writes** the home address into SAV and
TARGET whatever they held, so a stage atom is transparent exactly when they
held it already — which is what `stageEndSt_eq`'s two hypotheses say, and
why they are not a proof artifact.

Closing the sweep's gap by "reading the mirror" therefore means *threading*
that normalization rather than assuming it away: an atom's exit state is
`stageEndSt st v`, and the layers above carry it. These are the equations
that threading needs; they are all definitional, which is what makes the
propagation mechanical. -/

section StageEnd

variable {P : Type} [LinearOrder P] [Finite P]
variable {v : Univ A R P dt.KIx dt.dd → Prop}
variable (st : TapeStD dt A R P)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx]
  [LinearOrder P] [Finite P] in
/-- Normalizing twice is normalizing once. -/
theorem stageEndSt_idem : dt.stageEndSt (dt.stageEndSt st v) v =
    dt.stageEndSt st v := rfl

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx]
  [LinearOrder P] [Finite P] in
/-- Normalizing commutes with a round's VAL write. -/
theorem stageEndSt_roundSt (m : Univ A R P dt.KIx dt.dd → Prop) :
    dt.stageEndSt (dt.roundSt st m) v = dt.roundSt (dt.stageEndSt st v) m :=
  rfl

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx]
  [LinearOrder P] [Finite P] in
/-- Normalizing leaves the mirror, the markers and the tracks alone — so
every ride lemma of this file is blind to it. -/
theorem stageEndSt_fields :
    (dt.stageEndSt st v).mir = st.mir ∧ (dt.stageEndSt st v).val = st.val ∧
      (dt.stageEndSt st v).wk = st.wk ∧ (dt.stageEndSt st v).bot = st.bot ∧
      (dt.stageEndSt st v).ltp = st.ltp ∧
      (dt.stageEndSt st v).old = st.old ∧
      (dt.stageEndSt st v).new = st.new :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
  [Language.wide.Structure
    (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx]
  [LinearOrder P] [Finite P] in
/-- **A normalized state meets the stage atom's two hypotheses by
`rfl`** — which is what makes the threaded form hypothesis-free. -/
theorem stageEndSt_home :
    (dt.stageEndSt st v).sav = v ∧ (dt.stageEndSt st v).tgt = v :=
  ⟨rfl, rfl⟩

end StageEnd

end DrawData

end Draw

end DescriptiveComplexity
