/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawRunOuter
import DescriptiveComplexity.Problems.Wide.DrawSpineSem

/-!
# The sweep and MAIN, at the concrete program

`DescriptiveComplexity.Draw.Data.reaches_sweep` takes the per-address
evaluation as four hypothesis families — the run itself (`hspine`) and
three facts about the state it ends in — beside the two cover equations of
the tape and control families. All six are now theorems about the branched
evaluation, and this file feeds them in
(`DescriptiveComplexity.Draw.Data.reaches_sweepB`); then it does the same
one scale up, defining the stage families the machine iterates and feeding
`DescriptiveComplexity.Draw.Data.reaches_main`
(`DescriptiveComplexity.Draw.Data.reaches_mainB`), after which the only
hypotheses left about the run are *semantic* — which stage converges.

Two joints are crossed here. The evaluation layer is stated at an
arbitrary program and names the phases `OuterPh (EvalPh dt.nv dt.PMF)`,
which is `DescriptiveComplexity.Draw.Data.PF` up to unfolding — hence
the `@[reducible]` on `PF` and `PEF`, without which instance search does
not connect the two spellings. And the program's `zero`/`one` are its own
arguments only up to unfolding, so the program is named once
(`DescriptiveComplexity.Draw.Data.progOf`, reducible) and pinned
explicitly wherever a pack's *type* mentions them.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A : Type} (zero one : A)
variable [LinearOrder A] [Fintype dt.SlotIx]
variable [Finite A] [Finite dt.KIx]
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable (hzo : zero ≠ one)
variable [LinearOrder (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))]
variable [LinearOrder dt.PF]
variable (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
variable [Language.wide.Structure (Univ A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx dt.dd)]
variable [Finite (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))]
variable [Finite dt.PF]

/-- **The reduction's own machine**: the program at the packs
`DescriptiveComplexity.Draw.Data.varArgsOf` computes. Reducible, so that
its `zero` and `one` are its arguments for unification and its rules are
the tower's by `rfl`. -/
@[reducible] noncomputable def progOf :
    Prog A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
      dt.CtlIx dt.SlotIx dt.KIx dt.dd :=
  dt.prog zero one hzo (fun w => dt.varArgsOf zero one w) hpl

variable {dt zero one hzo hpl}

section Sweep

variable (hR : (dt.progOf zero one hzo hpl).table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)
variable {gtop gbot : Univ A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
variable (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
variable (mV : ιV → Univ A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
  dt.dd → Prop)
variable (hmV0 : mV a₀ = fun _ => False)
variable (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  WMIncr WMLe (mV a) (mV a'))
variable (hTestT : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
variable (hTestF : ∀ a, a < aT → ∃ u, ¬dt.InnerFull (fun u => tagBlk u.1) (mV a) u)
variable (semAt : ∀ (w : Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd → Prop) (j : Fin dt.nv)
  (st : TapeStD dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
    dt.PF),
  dt.gatedAt (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) j st →
  ∀ (p : Scratch dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.igPassP (wmSegFile hlin) zero one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.KindSem zero one (dt.varAt j)
      (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) w (b : ℕ))
      (dt.kindOf (dt.varAt j) b))
variable (st₀ : TapeStD dt A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
variable (f₀ : dt.CtlIx → A)
variable (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
variable (hmir₀ : st₀.mir = fun _ => False)
variable (hbot₀ : st₀.bot = fun r => r = (fun _ => False))

include hR hlin hord htop hbot hbotV htopV hmV0 hIncr hTestT hTestF hwk₀
  hmir₀ hbot₀ in
/-- **One whole sweep of the evaluation, at the concrete program**: from
the first address of the stretch to the last, one branched evaluation and
one advance per address, the tape and control families the sweep's own.
Every hypothesis `DescriptiveComplexity.Draw.Data.reaches_sweep` asks
about the evaluation is discharged here; what is left to the caller is the
geometry of the stretch and the end marker's position. -/
theorem reaches_sweepB
    {s₀ s₁ : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop}
    (hs₀ : WMSetLe WMLe s₀ s₁) (hs₁ : WMSetLt WMLe s₁ (wmSeg gbot))
    (hltp₀ : ∀ w, WMSetLe WMLe s₀ w → WMSetLt WMLe w s₁ → ¬st₀.ltp w) :
    Relation.ReflTransGen (wideData (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)).Step
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0))
          (dt.sweepFSG
            (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
            (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
            hlin st₀ f₀ s₀)), Sum.inl s₀,
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.val
          (dt.back wmSeg zero one dt.dd0Le
            (dt.sweepSWG
              (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV
                semAt)
              (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV
                semAt) hlin st₀ f₀ s₀))
          (dt.sweepSWG
            (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
            (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
            hlin st₀ f₀ s₀).val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0))
          (dt.sweepFSG
            (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
            (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
            hlin st₀ f₀ s₁)), Sum.inl s₁,
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.val
          (dt.back wmSeg zero one dt.dd0Le
            (dt.sweepSWG
              (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV
                semAt)
              (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV
                semAt) hlin st₀ f₀ s₁))
          (dt.sweepSWG
            (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
            (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
            hlin st₀ f₀ s₁).val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩ := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  -- `≤` then `<` gives `<`, as in `reaches_sweep`'s own proof
  have hlelt : ∀ a b c : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop,
      WMSetLe WMLe a b → WMSetLt WMLe b c → WMSetLt WMLe a c := by
    intro a b c hab hbc
    rw [wmSetLt_iff] at hbc ⊢
    refine ⟨hset.2.1 a b c hab hbc.1, fun hac => hbc.2 ?_⟩
    subst hac
    exact hset.2.2.1 b a hbc.1 hab
  -- the empty address is below every address
  have hemp : ∀ x : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop, WMSetLe WMLe (fun _ => False) x :=
    fun x => wmSetLe_of_empty hlin (fun _ hc => hc) x
  -- what a leg leaves alone, at the sweep's scale
  have hFwk : ∀ u st f, (dt.stEndB (PR := dt.progOf zero one hzo hpl)
      (aT := aT) (wmSegFile hlin) hord mV semAt u st f).wk = st.wk :=
    fun u st f => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin)
        hord mV semAt (fun st => st.wk) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.1) u st f
  have hFltp : ∀ u st f, (dt.stEndB (PR := dt.progOf zero one hzo hpl)
      (aT := aT) (wmSegFile hlin) hord mV semAt u st f).ltp = st.ltp :=
    fun u st f => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin)
        hord mV semAt (fun st => st.ltp) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.2.2.2) u
      st f
  refine dt.reaches_sweep hR hlin hord htop hbot hs₀ hs₁
    ?_ ?_ ?_ ?_
    (fun v v' hi _ _ => dt.sweepSWG_incr _ _ hlin st₀ f₀ hi)
    (fun v v' hi _ _ => dt.sweepFSG_incr _ _ hlin st₀ f₀ hi)
  · -- the run at each address
    intro v hlb hvS
    have hv : WMSetLt WMLe v (wmSeg gbot) :=
      hlelt _ _ _ ((wmSetLt_iff _ _).mp hvS).1 hs₁
    have hnotfull : ∃ x, ¬v x := by
      by_contra hc
      have hfull : ∀ x, v x :=
        fun x => Classical.byContradiction fun hx => hc ⟨x, hx⟩
      have hle := wmSetLe_of_full hlin hfull (wmSeg gbot)
      rw [wmSetLt_iff] at hv
      exact hv.2 (hset.2.2.1 _ _ hv.1 hle)
    obtain ⟨v', hvi⟩ := exists_wmIncr hlin hnotfull
    exact dt.reaches_spineB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) mV
      semAt hlin st₀ f₀
      (fun i ρ => dt.prog_rules_eval zero one hzo _ hpl i ρ) hR hord htop hbot
      (fun hr u => wmSetLt_wmSeg_of_not_bot hbot hr u) hbotV htopV hmV0 hIncr hTestT hTestF hwk₀
        hmir₀ hbot₀ (hemp v)
      ((wmSetLt_iff _ _).mp hvS).1 hv hvi
  · -- the marker, at the end of each address's evaluation
    intro v hlb hvS
    exact dt.sweepStEG_wk _ _ hlin st₀ f₀ hFwk hwk₀ v (hemp v)
      ((wmSetLt_iff _ _).mp hvS).1
  · -- the mirror: pinned by the branched evaluation
    intro v _ _
    exact dt.sweepStEG_mir' _ _ hlin st₀ f₀
      (fun u st f => dt.stEndB_mir (PR := dt.progOf zero one hzo hpl)
        (aT := aT) (wmSegFile hlin) hord mV semAt u st f) v
  · -- the end marker is where the reduction planted it
    intro v hlb hvS
    exact dt.sweepStEG_ltp _ _ hlin st₀ f₀ hFltp v (hemp v)
      ((wmSetLt_iff _ _).mp hvS).1 (hltp₀ v hlb hvS)

/-! ### The stage families

`DescriptiveComplexity.Draw.Data.reaches_main` asks for the sweep and the
top address's evaluation *per stage*, beside the two equations that say how
one stage's exit becomes the next one's entry. Those equations are what the
families below are defined by, so they hold by `rfl`; and the four registers
the stages must keep — the marker, the mirror, the bottom and end marks —
ride, because the sweep, the spine, and the copy-back all leave them alone
(`atSt`, `offSt` and `copySt` write `wk` and `old`, nothing else). -/

section Stages

variable (ltpAddr : Univ A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
  dt.dd → Prop)

variable (hpl) in
/-- **The state one stage's top-address evaluation ends in** — what its
convergence test reads. -/
noncomputable def stageEnd
    (st : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f : dt.CtlIx → A) :
    TapeStD dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF :=
  dt.sweepStEG (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV
      semAt)
    (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt) hlin
    st f ltpAddr

variable (hpl) in
/-- **The control one stage's top-address evaluation ends in.** -/
noncomputable def stageEndFs
    (st : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.sweepFsEG (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV
      semAt)
    (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt) hlin
    st f ltpAddr

variable (hpl) in
/-- **The pair the machine enters each stage with**: the reduction's own at
stage zero, and at every later stage the previous stage's exit — its
marker and mirror back at the empty address and its stage tracks copied
back, which is `reaches_main`'s `hnextSt`/`hnextFs` by construction. -/
noncomputable def stagePair
    (st₀ : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) :
    ℕ → TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF ×
      (dt.CtlIx → A)
  | 0 => (st₀, f₀)
  | n + 1 =>
    let p := stagePair st₀ f₀ n
    (dt.copySt zero one hzo (fun w => dt.varArgsOf zero one w)
      { dt.atSt (dt.offSt (dt.stageEnd hpl hlin hord (aT := aT) mV
          semAt ltpAddr p.1 p.2)) (fun _ => False) with
        mir := fun _ => False } ltpAddr,
      dt.stageEndFs hpl hlin hord (aT := aT) mV semAt ltpAddr p.1 p.2)

variable (hpl) in
/-- The tape family of the stages — `reaches_main`'s `entrySt`. -/
noncomputable def stageSt
    (st₀ : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    TapeStD dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF :=
  (dt.stagePair hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n).1

variable (hpl) in
/-- The control family of the stages — `reaches_main`'s `entryFs`. -/
noncomputable def stageFs
    (st₀ : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) (n : ℕ) : dt.CtlIx → A :=
  (dt.stagePair hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n).2

omit [Finite ιV] in
/-- The stage families start where the reduction puts them. -/
theorem stageSt_zero (st₀ : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) :
    dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ 0 = st₀ := rfl

omit [Finite ιV] in
/-- The control family of the stages starts at the reduction's pointer. -/
theorem stageFs_zero (st₀ : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) :
    dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ 0 = f₀ := rfl

omit [Finite ιV] in
/-- **`reaches_main`'s `hnextSt`** — by construction. -/
theorem stageSt_succ (st₀ : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
        (n + 1) =
      dt.copySt zero one hzo (fun w => dt.varArgsOf zero one w)
        { dt.atSt (dt.offSt (dt.stageEnd hpl hlin hord (aT := aT) mV
            semAt ltpAddr
            (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀
              f₀ n)
            (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀
              f₀ n))) (fun _ => False) with
          mir := fun _ => False } ltpAddr := rfl

omit [Finite ιV] in
/-- **`reaches_main`'s `hnextFs`** — by construction. -/
theorem stageFs_succ (st₀ : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
        (n + 1) =
      dt.stageEndFs hpl hlin hord (aT := aT) mV semAt ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
          n) := rfl

omit [Finite ιV] in
/-- **A register no leg and no advance writes rides a whole stage** — the
sweep by `sweepSWG_ride`, the top address's own evaluation by
`stEndB_ride`. -/
theorem stageEnd_ride {β : Sort _}
    (F : TapeStD dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF → β)
    (hFmir : ∀ (X : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF) m,
      F { X with mir := m } = F X)
    (hFa : ∀ (X : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF) u,
      F { dt.atSt X u with mir := u } = F X)
    (hFleg : ∀ (w : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd → Prop)
      (j : Fin dt.nv)
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (semT : dt.gatedAt (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) j st →
        ∀ (p : Scratch dt A
            (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
          (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.igPassP (wmSegFile hlin) zero one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.KindSem zero one (dt.varAt j)
            (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) w (b : ℕ))
            (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      F (dt.legStB (PR := dt.progOf zero one hzo hpl) (v := w) (aT := aT) (wmSegFile hlin) hord mV j
        st semT f) = F st)
    (st : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f : dt.CtlIx → A) :
    F (dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr st f) =
      F st := by
  have hFE : ∀ u s g, F (dt.stEndB (PR := dt.progOf zero one hzo hpl)
      (aT := aT) (wmSegFile hlin) hord mV semAt u s g) = F s :=
    fun u s g => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord
        mV semAt F hFmir (fun w j st' semT f' => hFleg w j st' semT f') u s g
  refine Eq.trans (hFE ltpAddr _ _) ?_
  exact dt.sweepSWG_ride _ _ hlin st f F hFE hFa
    (s₁ := ltpAddr) ltpAddr
    (wmSetLe_of_empty hlin (fun _ hc => hc) ltpAddr)
    ((isLinOrd_wmSetLe hlin).1 ltpAddr)

omit [Finite ιV] in
/-- **The four registers the stages must keep**: the marker back at the
empty address, the mirror with it, the bottom mark, and the end marker
where the reduction planted it. The first two are rewritten by the
copy-back's own itinerary, the last two ride. -/
theorem stageSt_fields (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    (hmir₀ : st₀.mir = fun _ => False)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    (hltp₀ : st₀.ltp = fun r => r = ltpAddr) (n : ℕ) :
    (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n).wk =
        (fun r => r = (fun _ => False)) ∧
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
        n).mir = (fun _ => False) ∧
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
        n).bot = (fun r => r = (fun _ => False)) ∧
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
        n).ltp = (fun r => r = ltpAddr) := by
  induction n with
  | zero => exact ⟨hwk₀, hmir₀, hbot₀, hltp₀⟩
  | succ n ih =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact Eq.trans (dt.stageEnd_ride hlin hord mV semAt ltpAddr
        (fun st => st.bot) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ _ _ _ => (dt.legStB_fields
          (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.2.1)
        _ _) ih.2.2.1
    · exact Eq.trans (dt.stageEnd_ride hlin hord mV semAt ltpAddr
        (fun st => st.ltp) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ _ _ _ => (dt.legStB_fields
          (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.2.2.2)
        _ _) ih.2.2.2

/-! ### The stage tracks, stage by stage

The dictionary invariant is what turns `reaches_main`'s two remaining
hypotheses into statements about `DescriptiveComplexity.StepDef.partStage`:
a stage's `old` tracks hold that stage *over the logical interval*, its
sweep writes the next stage into the `new` ones (`sweep_new_trackOf`), and
the copy-back moves those into `old`. The restriction to the interval is
not a convenience: outside it the tracks say nothing, an address there
being able to read a stage all the same — a tuple's address with one
non-argument cell added lies *above* the interval, non-argument tags being
the most significant. -/

variable [LinearOrder (dt.X.Map A)]

omit [Finite dt.KIx]
  [LinearOrder (dt.RIx zero one hzo fun w => dt.varArgsOf zero one w)]
  [LinearOrder dt.PF]
  [Language.wide.Structure (Univ A
    (dt.RIx zero one hzo fun w => dt.varArgsOf zero one w) dt.PF dt.KIx dt.dd)]
  [Finite (dt.RIx zero one hzo fun w => dt.varArgsOf zero one w)]
  [Finite dt.PF] in
/-- **A blank tape is stage `0`**: the empty stage writes an empty track
(`trackOf_botAssign`), so a tape whose stage tracks hold nothing holds stage
`0` — everywhere, the interval included. This is `stageSt_old`'s `hold₀` at
the initial configuration. -/
theorem old_trackOf_zero_of_blank
    {st : TapeStD dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF}
    (hblank : ∀ (iv : dt.d.B.ι) (s : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
      dt.KIx dt.dd → Prop), ¬st.old iv s)
    (iv : dt.d.B.ι) (s : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
      dt.KIx dt.dd → Prop) :
    st.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
      (dt.d.partStage (dt.X.Map A) 0) s :=
  iff_of_false (hblank iv s) (trackOf_botAssign _ s)

include hord hbot hbotV hmV0 hIncr hTestT in
/-- **A stage's tracks hold that stage of the iteration**, over the logical
interval: stage `0` is the initial tape, and each later one is the previous
stage's sweep copied back. -/
theorem stageSt_old
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hKin : ∀ (a : ιV)
      (t : Tag (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        dt.PF dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot))
    (hold₀ : ∀ (iv : dt.d.B.ι) (s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe s ltpAddr →
      (st₀.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) 0) s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe (dt.stageTgtD zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) w (dt.d.B.arity iv)) ltpAddr)
    (n : ℕ) :
    ∀ (iv : dt.d.B.ι) (s : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop), WMSetLt WMLe s ltpAddr →
      ((dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀
          n).old iv s ↔
        trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
          (dt.d.partStage (dt.X.Map A) n) s) := by
  classical
  set semG : ∀ (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop) (j : Fin dt.nv)
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF),
      dt.gatedAt (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) j st → _ :=
    fun w j st hg => dt.gatedSem
      (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg
    with hsemG
  have hcopy : ∀ (X : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (iv : dt.d.B.ι) (r : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      (dt.copySt zero one hzo (fun w => dt.varArgsOf zero one w) X
        ltpAddr).old iv r =
        (if WMSetLt WMLe r ltpAddr then X.new iv r else X.old iv r) :=
    fun _ _ _ => rfl
  induction n with
  | zero => exact hold₀
  | succ n ih =>
    intro iv s hs
    have hsw := dt.sweep_new_trackOf (PR := dt.progOf zero one hzo hpl)
      (aT := aT) (wmSegFile hlin) mV hlin
      (dt.stageSt hpl hlin hord (aT := aT) mV semG ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semG ltpAddr st₀ f₀ n)
      hord hbotV hmV0 hIncr hKin hTestT hordP
      (dt.d.partStage (dt.X.Map A) n) ih hbelow hbot (s₁ := ltpAddr) hlt
      ltpAddr (wmSetLe_of_empty hlin (fun _ hc => hc) ltpAddr)
      ((isLinOrd_wmSetLe hlin).1 ltpAddr)
    rw [dt.stageSt_succ hlin hord mV semG ltpAddr st₀ f₀ n, hcopy, if_pos hs,
      dt.d.partStage_succ (A := dt.X.Map A) n]
    exact (dt.stEndB_new_off (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV
      semG ltpAddr _
      (dt.sweepFSG
        (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semG)
        (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semG)
        hlin (dt.stageSt hpl hlin hord (aT := aT) mV semG ltpAddr st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV semG ltpAddr st₀ f₀ n) ltpAddr)
      iv (fun hc => ((wmSetLt_iff _ _).mp hs).2 hc)).trans
      (hsw.1 iv s (wmSetLe_of_empty hlin (fun _ hc => hc) s) hs)

include hord hbot hbotV hmV0 hIncr hTestT in
/-- **What the convergence test compares**: at the end of a stage the `old`
tracks still hold that stage. -/
theorem stageEnd_old_trackOf
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hKin : ∀ (a : ιV)
      (t : Tag (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        dt.PF dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot))
    (hold₀ : ∀ (iv : dt.d.B.ι) (s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe s ltpAddr →
      (st₀.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) 0) s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe (dt.stageTgtD zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) w (dt.d.B.arity iv)) ltpAddr)
    (n : ℕ) (iv : dt.d.B.ι) {s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop}
    (hs : WMSetLt WMLe s ltpAddr) :
    ((dt.stageEnd hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
        ltpAddr st₀ f₀ n)).old iv s ↔
      trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) n) s) := by
  refine (iff_of_eq (congrFun (congrFun (dt.stageEnd_ride hlin hord mV _ ltpAddr
    (fun st => st.old) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ _ => (dt.legStB_fields
      (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.2.2.1)
    _ _) iv) s)).trans ?_
  exact dt.stageSt_old hlin hord hbot hbotV mV hmV0 hIncr hTestT st₀ f₀
    ltpAddr hordP hKin hlt hold₀ hbelow n iv s hs

include hord hbot hbotV hmV0 hIncr hTestT in
/-- **And the `new` tracks hold the next one**: the stage's own sweep wrote
them, and the top address's evaluation leaves every other cell alone. -/
theorem stageEnd_new_trackOf
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hKin : ∀ (a : ιV)
      (t : Tag (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        dt.PF dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot))
    (hold₀ : ∀ (iv : dt.d.B.ι) (s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe s ltpAddr →
      (st₀.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) 0) s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe (dt.stageTgtD zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) w (dt.d.B.arity iv)) ltpAddr)
    (n : ℕ) (iv : dt.d.B.ι) {s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop}
    (hs : WMSetLt WMLe s ltpAddr) :
    ((dt.stageEnd hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
        ltpAddr st₀ f₀ n)).new iv s ↔
      trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) (n + 1)) s) := by
  classical
  set semG : ∀ (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop) (j : Fin dt.nv)
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF),
      dt.gatedAt (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) j st → _ :=
    fun w j st hg => dt.gatedSem
      (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg
    with hsemG
  have hsw := dt.sweep_new_trackOf (PR := dt.progOf zero one hzo hpl)
    (aT := aT) (wmSegFile hlin) mV hlin
    (dt.stageSt hpl hlin hord (aT := aT) mV semG ltpAddr st₀ f₀ n)
    (dt.stageFs hpl hlin hord (aT := aT) mV semG ltpAddr st₀ f₀ n)
    hord hbotV hmV0 hIncr hKin hTestT hordP
    (dt.d.partStage (dt.X.Map A) n)
    (dt.stageSt_old hlin hord hbot hbotV mV hmV0 hIncr hTestT st₀ f₀ ltpAddr
      hordP hKin hlt hold₀ hbelow n)
    hbelow hbot (s₁ := ltpAddr) hlt ltpAddr
    (wmSetLe_of_empty hlin (fun _ hc => hc) ltpAddr)
    ((isLinOrd_wmSetLe hlin).1 ltpAddr)
  rw [dt.d.partStage_succ (A := dt.X.Map A) n]
  exact (dt.stEndB_new_off (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV
    semG ltpAddr _
    (dt.sweepFSG
      (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semG)
      (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semG)
      hlin (dt.stageSt hpl hlin hord (aT := aT) mV semG ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semG ltpAddr st₀ f₀ n) ltpAddr)
    iv (fun hc => ((wmSetLt_iff _ _).mp hs).2 hc)).trans
    (hsw.1 iv s (wmSetLe_of_empty hlin (fun _ hc => hc) s) hs)

include hord hbot hbotV hmV0 hIncr hTestT in
/-- **The convergence test, semantically**: a stage's test passes exactly
when its stage and the next agree at every address of the logical interval —
`reaches_main`'s `hconv`/`hnotconv` as statements about
`DescriptiveComplexity.StepDef.partStage` and nothing else. -/
theorem stageEnd_conv_iff
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hKin : ∀ (a : ιV)
      (t : Tag (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        dt.PF dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot))
    (hold₀ : ∀ (iv : dt.d.B.ι) (s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe s ltpAddr →
      (st₀.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) 0) s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe (dt.stageTgtD zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) w (dt.d.B.arity iv)) ltpAddr)
    (n : ℕ) :
    ((∀ (r : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop), WMSetLt WMLe r ltpAddr →
      ∀ iv : dt.d.B.ι,
        ((dt.stageEnd hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
        ltpAddr st₀ f₀ n)).old iv r ↔
          (dt.stageEnd hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
        ltpAddr st₀ f₀ n)).new iv r)) ↔
      ∀ (r : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop), WMSetLt WMLe r ltpAddr →
        ∀ iv : dt.d.B.ι,
          (trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
              (dt.d.partStage (dt.X.Map A) n) r ↔
            trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
              (dt.d.partStage (dt.X.Map A) (n + 1)) r)) := by
  refine forall_congr' fun r => forall_congr' fun hr => forall_congr' fun iv => ?_
  exact iff_congr
    (dt.stageEnd_old_trackOf hlin hord hbot hbotV mV hmV0 hIncr hTestT st₀ f₀
      ltpAddr hordP hKin hlt hold₀ hbelow n iv hr)
    (dt.stageEnd_new_trackOf hlin hord hbot hbotV mV hmV0 hIncr hTestT st₀ f₀
      ltpAddr hordP hKin hlt hold₀ hbelow n iv hr)

include hord hbot hbotV hmV0 hIncr hTestT in
/-- **`reaches_main`'s `hconv`, from a stable stage**: if the stage does not
move, neither does its dictionary. -/
theorem stageEnd_conv_of_eq
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hKin : ∀ (a : ιV)
      (t : Tag (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        dt.PF dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot))
    (hold₀ : ∀ (iv : dt.d.B.ι) (s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe s ltpAddr →
      (st₀.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) 0) s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe (dt.stageTgtD zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) w (dt.d.B.arity iv)) ltpAddr)
    {n : ℕ} (hN : dt.d.partStage (dt.X.Map A) n =
      dt.d.partStage (dt.X.Map A) (n + 1)) :
    ∀ (r : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop), WMSetLt WMLe r ltpAddr →
      ∀ iv : dt.d.B.ι,
        ((dt.stageEnd hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
        ltpAddr st₀ f₀ n)).old iv r ↔
          (dt.stageEnd hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
        ltpAddr st₀ f₀ n)).new iv r) := by
  refine (dt.stageEnd_conv_iff hlin hord hbot hbotV mV hmV0 hIncr hTestT st₀ f₀
    ltpAddr hordP hKin hlt hold₀ hbelow n).mpr (fun r _ iv => ?_)
  rw [hN]

include hord hbot hbotV hmV0 hIncr hTestT in
/-- **`reaches_main`'s `hnotconv`, from a moving stage**: the dictionary is
faithful over an interval that carries every tuple's own address
(`assignment_ext_of_trackOf`), so a stage that moves moves its tracks. -/
theorem stageEnd_not_conv_of_ne
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hKin : ∀ (a : ιV)
      (t : Tag (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        dt.PF dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot))
    (hold₀ : ∀ (iv : dt.d.B.ι) (s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe s ltpAddr →
      (st₀.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) 0) s))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop),
      WMSetLt WMLe (dt.stageTgtD zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) w (dt.d.B.arity iv)) ltpAddr)
    (hS : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      WMSetLt WMLe (tupAddr dt.ly zero one
        (R := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        (P := dt.PF) (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ltpAddr)
    {n : ℕ} (hN : dt.d.partStage (dt.X.Map A) n ≠
      dt.d.partStage (dt.X.Map A) (n + 1)) :
    ¬∀ (r : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
        dt.KIx dt.dd → Prop), WMSetLt WMLe r ltpAddr →
      ∀ iv : dt.d.B.ι,
        ((dt.stageEnd hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
        ltpAddr st₀ f₀ n)).old iv r ↔
          (dt.stageEnd hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
        (dt.stageSt hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg) ltpAddr
            st₀ f₀ n)
        (dt.stageFs hpl hlin hord (aT := aT) mV (fun w j st hg => dt.gatedSem
          (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
        ltpAddr st₀ f₀ n)).new iv r) := by
  intro htest
  refine hN (assignment_ext_of_trackOf hzo (fun iv => dt.arOf_le_ko (some iv))
    (fun s => WMSetLt WMLe s ltpAddr) hS (fun s hs iv => ?_))
  exact (dt.stageEnd_conv_iff hlin hord hbot hbotV mV hmV0 hIncr hTestT st₀ f₀
    ltpAddr hordP hKin hlt hold₀ hbelow n).mp htest s hs iv

omit [LinearOrder (dt.X.Map A)] in
include hR hord htop hbot hbotV htopV hmV0 hIncr hTestT hTestF in
/-- **MAIN, at the concrete program**: from the first stage's entry at the
empty address to the out machinery's entry, one sweep and one convergence
test per stage, the stage families the reduction's own. Everything the
machine does is now discharged; what is left of the theorem is *semantic* —
which stage converges (`hnotconv`, `hconv`) — plus the geometry of the
logical interval. -/
theorem reaches_mainB
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot)) (hneT : ∃ x, ltpAddr x)
    {v₁ : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop}
    (hiE : WMIncr WMLe (fun _ => False) v₁)
    (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    (hmir₀ : st₀.mir = fun _ => False)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    (hltp₀ : st₀.ltp = fun r => r = ltpAddr)
    {N : ℕ}
    (hnotconv : ∀ n, n < N → ¬∀ r, WMSetLt WMLe r ltpAddr → ∀ i,
      ((dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            n)
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            n)).old i r ↔
        (dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            n)
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            n)).new i r))
    (hconv : ∀ r, WMSetLt WMLe r ltpAddr → ∀ i,
      ((dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            N)
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            N)).old i r ↔
        (dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            N)
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            N)).new i r)) :
    Relation.ReflTransGen (wideData (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)).Step
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0)) f₀),
        Sum.inl (fun _ => False),
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.val
          (dt.back wmSeg zero one dt.dd0Le st₀) st₀.val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt
          (.evalP (.sub (dt.smEntryOut)))
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀
            (N + 1))), Sum.inl v₁,
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.val
          (dt.back wmSeg zero one dt.dd0Le
            { dt.atSt (dt.offSt (dt.stageEnd hpl hlin hord (aT := aT)
                mV semAt ltpAddr
                (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr
                  st₀ f₀ N)
                (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr
                  st₀ f₀ N))) (fun _ => False) with
              mir := fun _ => False })
          { dt.atSt (dt.offSt (dt.stageEnd hpl hlin hord (aT := aT)
              mV semAt ltpAddr
              (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr
                st₀ f₀ N)
              (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr
                st₀ f₀ N))) (fun _ => False) with
            mir := fun _ => False }.val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩ := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  have hemp : ∀ x : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop, WMSetLe WMLe (fun _ => False) x :=
    fun x => wmSetLe_of_empty hlin (fun _ hc => hc) x
  have hFwk : ∀ u st f, (dt.stEndB (PR := dt.progOf zero one hzo hpl)
      (aT := aT) (wmSegFile hlin) hord mV semAt u st f).wk = st.wk :=
    fun u st f => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin)
        hord mV semAt (fun st => st.wk) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.1) u st f
  -- the stage invariant, once
  have hfields := fun n => dt.stageSt_fields (hpl := hpl) hlin hord (aT := aT)
    mV semAt st₀ f₀ ltpAddr hwk₀ hmir₀ hbot₀ hltp₀ n
  refine dt.reaches_main hR hlin hord htop hbot hlt hneT hiE
    (entrySt := dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr
      st₀ f₀)
    (entryFs := dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr
      st₀ f₀)
    (topSt := fun n => dt.sweepSWG
      (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
      (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt) hlin
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      ltpAddr)
    (topFs := fun n => dt.sweepFSG
      (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt)
      (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV semAt) hlin
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      ltpAddr)
    (stT := fun n => dt.stageEnd hpl hlin hord (aT := aT) mV semAt
      ltpAddr
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n))
    (fsT := fun n => dt.stageEndFs hpl hlin hord (aT := aT) mV semAt
      ltpAddr
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n))
    ?_ ?_ ?_ ?_ ?_ hnotconv hconv
    (fun n _ => dt.stageSt_succ hlin hord mV semAt ltpAddr st₀ f₀ n)
    (fun n _ => dt.stageFs_succ hlin hord mV semAt ltpAddr st₀ f₀ n)
  · -- the sweep, per stage
    intro n _
    have h := dt.reaches_sweepB hR hlin hord htop hbot hbotV htopV mV hmV0
      hIncr hTestT hTestF semAt
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (hfields n).1 (hfields n).2.1
      (hfields n).2.2.1 (s₀ := fun _ => False) (s₁ := ltpAddr)
      (hemp ltpAddr) hlt
      (fun w _ hwlt => by
        rw [(hfields n).2.2.2]
        exact fun hc => ((wmSetLt_iff _ _).mp hwlt).2 hc)
    rw [dt.sweepSWG_bot _ _ hlin _ _, dt.sweepFSG_bot _ _ hlin _ _] at h
    exact h
  · -- the top address's own evaluation, per stage
    intro n _
    have hnotfull : ∃ x, ¬ltpAddr x := by
      by_contra hc
      have hfull : ∀ x, ltpAddr x :=
        fun x => Classical.byContradiction fun hx => hc ⟨x, hx⟩
      have hle := wmSetLe_of_full hlin hfull (wmSeg gbot)
      rw [wmSetLt_iff] at hlt
      exact hlt.2 (hset.2.2.1 _ _ hlt.1 hle)
    obtain ⟨v', hvi⟩ := exists_wmIncr hlin hnotfull
    exact dt.reaches_spineB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) mV
      semAt hlin _ _
      (fun i ρ => dt.prog_rules_eval zero one hzo _ hpl i ρ) hR hord htop hbot
      (fun hr u => wmSetLt_wmSeg_of_not_bot hbot hr u) hbotV htopV hmV0 hIncr hTestT hTestF (hfields
        n).1 (hfields n).2.1
      (hfields n).2.2.1 (hemp ltpAddr) (hset.1 ltpAddr) hlt hvi
  · -- the marker, at the end of each stage
    intro n _
    exact dt.sweepStEG_wk _ _ hlin _ _ hFwk (hfields n).1 ltpAddr
      (hemp ltpAddr) (hset.1 ltpAddr)
  · -- the end marker, at the end of each stage
    intro n _
    exact Eq.trans (dt.stageEnd_ride hlin hord mV semAt ltpAddr
      (fun st => st.ltp) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.2.2.2)
      _ _) (hfields n).2.2.2
  · -- the bottom mark, at the end of each stage
    intro n _
    exact Eq.trans (dt.stageEnd_ride hlin hord mV semAt ltpAddr
      (fun st => st.bot) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.2.1)
      _ _) (hfields n).2.2.1

omit [LinearOrder (dt.X.Map A)] in
include hR hord htop hbot hbotV htopV hmV0 hIncr hTestT hTestF in
/-- **One stage of MAIN, when its convergence test fails**: from a stage's
entry at the empty address to the next stage's, in at least one step. The
strictness is the sweep's: it leaves the head at the end-marked address, which
is not the empty one — and it is what
`DescriptiveComplexity.TMData.not_acceptsSpace_of_chain` asks of a link, so
that a *diverging* iteration keeps the machine off every halting
configuration. -/
theorem transGen_stageB
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot)) (hneT : ∃ x, ltpAddr x)
    (hwk₀ : st₀.wk = fun r => r = (fun _ => False))
    (hmir₀ : st₀.mir = fun _ => False)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    (hltp₀ : st₀.ltp = fun r => r = ltpAddr) (n : ℕ)
    (hnc : ¬∀ r, WMSetLt WMLe r ltpAddr → ∀ i,
      ((dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)).old i r ↔
        (dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)).new i r)) :
    Relation.TransGen (wideData (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)).Step
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0))
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)),
        Sum.inl (fun _ => False),
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.val
          (dt.back wmSeg zero one dt.dd0Le
            (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n))
          (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n).val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0))
          (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ (n + 1))),
        Sum.inl (fun _ => False),
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.val
          (dt.back wmSeg zero one dt.dd0Le
            (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ (n + 1)))
          (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ (n + 1)).val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩ := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  have hemp : ∀ x : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop, WMSetLe WMLe (fun _ => False) x :=
    fun x => wmSetLe_of_empty hlin (fun _ hc => hc) x
  have hFwk : ∀ u st f, (dt.stEndB (PR := dt.progOf zero one hzo hpl)
      (aT := aT) (wmSegFile hlin) hord mV semAt u st f).wk = st.wk :=
    fun u st f => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin)
        hord mV semAt (fun st => st.wk) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.1) u st f
  have hfields := fun m => dt.stageSt_fields (hpl := hpl) hlin hord (aT := aT)
    mV semAt st₀ f₀ ltpAddr hwk₀ hmir₀ hbot₀ hltp₀ m
  -- the sweep, which leaves the head at the end-marked address
  have hsw := dt.reaches_sweepB hR hlin hord htop hbot hbotV htopV mV hmV0
    hIncr hTestT hTestF semAt
    (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
    (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
    (hfields n).1 (hfields n).2.1
    (hfields n).2.2.1 (s₀ := fun _ => False) (s₁ := ltpAddr)
    (hemp ltpAddr) hlt
    (fun w _ hwlt => by
      rw [(hfields n).2.2.2]
      exact fun hc => ((wmSetLt_iff _ _).mp hwlt).2 hc)
  rw [dt.sweepSWG_bot _ _ hlin _ _, dt.sweepFSG_bot _ _ hlin _ _] at hsw
  -- the top address's own evaluation
  have hnotfull : ∃ x, ¬ltpAddr x := by
    by_contra hc
    have hfull : ∀ x, ltpAddr x :=
      fun x => Classical.byContradiction fun hx => hc ⟨x, hx⟩
    have hle := wmSetLe_of_full hlin hfull (wmSeg gbot)
    rw [wmSetLt_iff] at hlt
    exact hlt.2 (hset.2.2.1 _ _ hlt.1 hle)
  obtain ⟨v', hvi⟩ := exists_wmIncr hlin hnotfull
  have hsp := dt.reaches_spineB (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) mV
      semAt hlin
    (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
    (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
    (fun i ρ => dt.prog_rules_eval zero one hzo _ hpl i ρ) hR hord htop hbot
    (fun hr u => wmSetLt_wmSeg_of_not_bot hbot hr u) hbotV htopV hmV0 hIncr hTestT hTestF (hfields
      n).1 (hfields n).2.1
    (hfields n).2.2.1 (hemp ltpAddr) (hset.1 ltpAddr) hlt hvi
  -- the closing ring of a failing stage
  have hwkT : (dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)).wk =
      fun r => r = ltpAddr :=
    dt.sweepStEG_wk _ _ hlin _ _ hFwk (hfields n).1 ltpAddr
      (hemp ltpAddr) (hset.1 ltpAddr)
  have hltpT : (dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)).ltp =
      fun r => r = ltpAddr :=
    Eq.trans (dt.stageEnd_ride hlin hord mV semAt ltpAddr
      (fun st => st.ltp) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.2.2.2)
      _ _) (hfields n).2.2.2
  have hbotT : (dt.stageEnd hpl hlin hord (aT := aT) mV semAt ltpAddr
      (dt.stageSt hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin hord (aT := aT) mV semAt ltpAddr st₀ f₀ n)).bot =
      fun r => r = (fun _ => False) :=
    Eq.trans (dt.stageEnd_ride hlin hord mV semAt ltpAddr
      (fun st => st.bot) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) (wmSegFile hlin) hord mV _ _ _ _).2.2.1)
      _ _) (hfields n).2.2.1
  have hclose := stageClose_neg hR hlin hord htop hbot hlt hneT hsp hwkT hltpT
    hbotT hnc
  rw [dt.stageSt_succ hlin hord mV semAt ltpAddr st₀ f₀ n,
    dt.stageFs_succ hlin hord mV semAt ltpAddr st₀ f₀ n]
  -- the sweep is not empty: it moves the head off the empty address
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hsw with heq | htr
  · exact absurd (Sum.inl.inj (congrArg Config.head heq))
      (fun hc => hneT.elim fun x hx => (hc ▸ hx : (fun _ => False) x))
  · exact htr.trans_left hclose

end Stages

/-! ### From the initial configuration to MAIN

`DescriptiveComplexity.Draw.Data.reaches_startup` stops one rule short of
`reaches_mainB`: the mirror clear leaves the head on the marker at the empty
address in `clearMir1P .run`, and two steps join that to the evaluation's
first checkpoint — the exit rule, which steps *right* off the marker, and one
`stay` step of the checkpoint, which walks back *left* onto it. The two
presentations of the tape are one term (`trackTape_val_eq_mir`), so no
conversion is needed beyond naming it. -/

section Entry

variable (hR : (dt.progOf zero one hzo hpl).table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx dt.dd)))

include hR hlin in
/-- **The startup's exit**: at the marker, the exit guard holds and the rule
steps right into the evaluation's first checkpoint. -/
theorem step_clearMir1_exit
    {v' : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') {fc : dt.CtlIx → A}
    {st : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    (hreg : ¬∃ u : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd, (fun _ => False) = wmSeg u) :
    (wideData (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)).Step
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.clearMir1P .run) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0)) fc),
        Sum.inl v',
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩ := by
  refine Prog.step_move hR hlin hi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo
      (fun w => dt.varArgsOf zero one w)).rule OuterSite.clearMir1
      (Sum.inr ())).guard fc ((dt.progOf zero one hzo hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le st) st.mir (fun _ => False)) := by
    refine ⟨?_, ?_⟩
    · rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm, back_reg]
      exact fun hc => hreg ((bitVal_iff hzo).mp hc)
  exact dt.prog_hasRight zero one hzo _ hpl .clearMir1 (Sum.inr ()) hg trivial

include hR hlin in
/-- **The checkpoint walks back to the marker**: off the marker the
checkpoint's `stay` rule fires and moves left, which is the one step between
the startup's exit and `reaches_mainB`'s starting configuration. -/
theorem step_chk0_back
    {v' : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') {fc : dt.CtlIx → A}
    {st : TapeStD dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False) :
    (wideData (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)).Step
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0)) fc),
        Sum.inl v',
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0)) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩ := by
  refine Prog.step_moveBack hR hlin hi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo
      (fun w => dt.varArgsOf zero one w)).rule
      (OuterSite.eval (EvalSite.chk 0)) EvalChkRule.stay).guard fc
      ((dt.progOf zero one hzo hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le st) st.mir v') := by
    change (dt.progOf zero one hzo hpl).passTracksAt wmSeg Slot.mir
      (dt.back wmSeg zero one dt.dd0Le st) st.mir v' Slot.wk ≠ one
    rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk,
      bitVal_neg (Ne.symm (ne_of_wmIncr hi))]
    exact hzo
  exact dt.prog_hasLeft zero one hzo _ hpl (.eval (.chk 0)) EvalChkRule.stay
    hg not_false

include hR hlin in
/-- **From the initial configuration to MAIN's starting configuration**: the
startup, its exit, and the walk back onto the marker. The state is
`DescriptiveComplexity.Draw.Data.startupSt` — the bottom mark at the empty
address, the end marker at the logical top, both registers home and every
stage track still clear — which is what `reaches_mainB` asks of its `st₀`. -/
theorem reaches_evalEntry
    (hord : ∀ x y : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd, WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y) :
    Relation.ReflTransGen
      (wideData (Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd)).Step
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt .start fun _ => zero),
        Sum.inl (fun _ => False),
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
            (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
            (P' := dt.PF))) (fun _ => False))
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0))
          fun _ => zero), Sum.inl (fun _ => False),
        wideTape ((dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.val
          (dt.back wmSeg zero one dt.dd0Le (dt.startupSt (A := A)
            (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
            (P' := dt.PF)))
          (dt.startupSt (A := A)
            (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
            (P' := dt.PF)).val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩ := by
  classical
  obtain ⟨v', hi⟩ := exists_wmIncr (Le := WMLe (A := Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd)) hlin (s := fun _ => False) ⟨gbot, not_false⟩
  have hreg : ¬∃ u : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd, (fun _ => False) = wmSeg u := by
    rintro ⟨u, hu⟩
    have h := wmSetLt_empty_wmSeg (A := Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd) hlin u
    rw [hu] at h
    exact ((wmSetLt_iff _ _).mp h).2 rfl
  have hwk : (dt.startupSt (A := A)
      (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      (P' := dt.PF)).wk = fun r => r = fun _ => False := rfl
  have htape : (dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.val
      (dt.back wmSeg zero one dt.dd0Le (dt.startupSt (A := A)
      (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      (P' := dt.PF))) (dt.startupSt (A := A)
      (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      (P' := dt.PF)).val =
      (dt.progOf zero one hzo hpl).trackTapeAt wmSeg Slot.mir
      (dt.back wmSeg zero one dt.dd0Le (dt.startupSt (A := A)
      (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      (P' := dt.PF))) (dt.startupSt (A := A)
      (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      (P' := dt.PF)).mir :=
    trackTape_val_eq_mir (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) _
  rw [htape]
  refine (dt.reaches_startup zero one hzo (fun w => dt.varArgsOf zero one w)
    hpl hR hlin hord htop hbot).trans ?_
  exact (Relation.ReflTransGen.single
    (step_clearMir1_exit hR hlin hi hwk hreg)).trans
    (Relation.ReflTransGen.single (step_chk0_back hR hlin hi hwk))

end Entry

end Sweep

end Data

end Draw

end DescriptiveComplexity
