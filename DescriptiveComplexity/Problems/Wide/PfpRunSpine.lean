/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpRunOuter
import DescriptiveComplexity.Problems.Wide.PfpSpineSem

/-!
# The sweep and MAIN, at the concrete program

`DescriptiveComplexity.Pfp.PfpData.reaches_sweep` takes the per-address
evaluation as four hypothesis families — the run itself (`hspine`) and
three facts about the state it ends in — beside the two cover equations of
the tape and control families. All six are now theorems about the branched
evaluation, and this file feeds them in
(`DescriptiveComplexity.Pfp.PfpData.reaches_sweepB`); then it does the same
one scale up, defining the stage families the machine iterates and feeding
`DescriptiveComplexity.Pfp.PfpData.reaches_main`
(`DescriptiveComplexity.Pfp.PfpData.reaches_mainB`), after which the only
hypotheses left about the run are *semantic* — which stage converges.

Two joints are crossed here. The evaluation layer is stated at an
arbitrary program and names the phases `OuterPh (EvalPh dt.nv dt.PMF)`,
which is `DescriptiveComplexity.Pfp.PfpData.PF` up to unfolding — hence
the `@[reducible]` on `PF` and `PEF`, without which instance search does
not connect the two spellings. And the program's `zero`/`one` are its own
arguments only up to unfolding, so the program is named once
(`DescriptiveComplexity.Pfp.PfpData.progOf`, reducible) and pinned
explicitly wherever a pack's *type* mentions them.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A : Type} (zero one : A)
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
`DescriptiveComplexity.Pfp.PfpData.varArgsOf` computes. Reducible, so that
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
variable (hTestT : ∀ u, dt.InnerFull (mV aT) u)
variable (hTestF : ∀ a, a < aT → ∃ u, ¬dt.InnerFull (mV a) u)
variable (semAt : ∀ (w : Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd → Prop)
  (st : TapeSt dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
    dt.PF)
  (j : Fin dt.nv) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.igPassP zero one (dt.varAt j)
      (dt.roundSt { st with mir := w } (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.KindSem zero one (dt.varAt j)
      (dt.roundSt { st with mir := w } (mV a)) (dt.kindOf (dt.varAt j) b))
variable (st₀ : TapeSt dt A
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
Every hypothesis `DescriptiveComplexity.Pfp.PfpData.reaches_sweep` asks
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
            (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
            (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
            hlin st₀ f₀ s₀)), Sum.inl s₀,
        wideTape ((dt.progOf zero one hzo hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le
            (dt.sweepSWG
              (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV
                semAt)
              (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV
                semAt) hlin st₀ f₀ s₀))
          (dt.sweepSWG
            (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
            (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
            hlin st₀ f₀ s₀).val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0))
          (dt.sweepFSG
            (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
            (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
            hlin st₀ f₀ s₁)), Sum.inl s₁,
        wideTape ((dt.progOf zero one hzo hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le
            (dt.sweepSWG
              (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV
                semAt)
              (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV
                semAt) hlin st₀ f₀ s₁))
          (dt.sweepSWG
            (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
            (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
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
      (aT := aT) mV semAt u st f).wk = st.wk :=
    fun u st f => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT)
      mV semAt (fun st => st.wk) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) mV _ _ _ _).2.1) u st f
  have hFltp : ∀ u st f, (dt.stEndB (PR := dt.progOf zero one hzo hpl)
      (aT := aT) mV semAt u st f).ltp = st.ltp :=
    fun u st f => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT)
      mV semAt (fun st => st.ltp) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) mV _ _ _ _).2.2.2.2) u
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
    exact dt.reaches_spineB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV
      semAt hlin st₀ f₀
      (fun i ρ => dt.prog_rules_eval zero one hzo _ hpl i ρ) hR hord htop hbot
      hbotV htopV hmV0 hIncr hTestT hTestF hwk₀ hmir₀ hbot₀ (hemp v)
      ((wmSetLt_iff _ _).mp hvS).1 hv hvi
  · -- the marker, at the end of each address's evaluation
    intro v hlb hvS
    exact dt.sweepStEG_wk _ _ hlin st₀ f₀ hFwk hwk₀ v (hemp v)
      ((wmSetLt_iff _ _).mp hvS).1
  · -- the mirror: pinned by the branched evaluation
    intro v _ _
    exact dt.sweepStEG_mir' _ _ hlin st₀ f₀
      (fun u st f => dt.stEndB_mir (PR := dt.progOf zero one hzo hpl)
        (aT := aT) mV semAt u st f) v
  · -- the end marker is where the reduction planted it
    intro v hlb hvS
    exact dt.sweepStEG_ltp _ _ hlin st₀ f₀ hFltp v (hemp v)
      ((wmSetLt_iff _ _).mp hvS).1 (hltp₀ v hlb hvS)

/-! ### The stage families

`DescriptiveComplexity.Pfp.PfpData.reaches_main` asks for the sweep and the
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
    (st : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f : dt.CtlIx → A) :
    TapeSt dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF :=
  dt.sweepStEG (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV
      semAt)
    (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt) hlin
    st f ltpAddr

variable (hpl) in
/-- **The control one stage's top-address evaluation ends in.** -/
noncomputable def stageEndFs
    (st : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.sweepFsEG (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV
      semAt)
    (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt) hlin
    st f ltpAddr

variable (hpl) in
/-- **The pair the machine enters each stage with**: the reduction's own at
stage zero, and at every later stage the previous stage's exit — its
marker and mirror back at the empty address and its stage tracks copied
back, which is `reaches_main`'s `hnextSt`/`hnextFs` by construction. -/
noncomputable def stagePair
    (st₀ : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) :
    ℕ → TapeSt dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF ×
      (dt.CtlIx → A)
  | 0 => (st₀, f₀)
  | n + 1 =>
    let p := stagePair st₀ f₀ n
    (dt.copySt zero one hzo (fun w => dt.varArgsOf zero one w)
      { dt.atSt (dt.offSt (dt.stageEnd hpl hlin (aT := aT) mV
          semAt ltpAddr p.1 p.2)) (fun _ => False) with
        mir := fun _ => False } ltpAddr,
      dt.stageEndFs hpl hlin (aT := aT) mV semAt ltpAddr p.1 p.2)

variable (hpl) in
/-- The tape family of the stages — `reaches_main`'s `entrySt`. -/
noncomputable def stageSt
    (st₀ : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    TapeSt dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF :=
  (dt.stagePair hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n).1

variable (hpl) in
/-- The control family of the stages — `reaches_main`'s `entryFs`. -/
noncomputable def stageFs
    (st₀ : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) (n : ℕ) : dt.CtlIx → A :=
  (dt.stagePair hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n).2

omit [Finite ιV] in
/-- **`reaches_main`'s `hnextSt`** — by construction. -/
theorem stageSt_succ (st₀ : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
        (n + 1) =
      dt.copySt zero one hzo (fun w => dt.varArgsOf zero one w)
        { dt.atSt (dt.offSt (dt.stageEnd hpl hlin (aT := aT) mV
            semAt ltpAddr
            (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀
              f₀ n)
            (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀
              f₀ n))) (fun _ => False) with
          mir := fun _ => False } ltpAddr := rfl

omit [Finite ιV] in
/-- **`reaches_main`'s `hnextFs`** — by construction. -/
theorem stageFs_succ (st₀ : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
        (n + 1) =
      dt.stageEndFs hpl hlin (aT := aT) mV semAt ltpAddr
        (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
        (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
          n) := rfl

omit [Finite ιV] in
/-- **A register no leg and no advance writes rides a whole stage** — the
sweep by `sweepSWG_ride`, the top address's own evaluation by
`stEndB_ride`. -/
theorem stageEnd_ride {β : Sort _}
    (F : TapeSt dt A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF → β)
    (hFmir : ∀ (X : TapeSt dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF) m,
      F { X with mir := m } = F X)
    (hFa : ∀ (X : TapeSt dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF) u,
      F { dt.atSt X u with mir := u } = F X)
    (hFleg : ∀ (w : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd → Prop)
      (j : Fin dt.nv)
      (st : TapeSt dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (semT : dt.gatedAt (PR := dt.progOf zero one hzo hpl) j st →
        ∀ (p : Scratch dt A
            (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
          (a : ιV),
        (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
          dt.igPassP zero one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
        ∀ b : Fin (dt.natOf (dt.varAt j)),
          dt.KindSem zero one (dt.varAt j)
            (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) w (b : ℕ))
            (dt.kindOf (dt.varAt j) b))
      (f : dt.CtlIx → A),
      F (dt.legStB (PR := dt.progOf zero one hzo hpl) (v := w) (aT := aT) mV j
        st semT f) = F st)
    (st : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (f : dt.CtlIx → A) :
    F (dt.stageEnd hpl hlin (aT := aT) mV semAt ltpAddr st f) =
      F st := by
  have hFE : ∀ u s g, F (dt.stEndB (PR := dt.progOf zero one hzo hpl)
      (aT := aT) mV semAt u s g) = F s :=
    fun u s g => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT)
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
    (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n).wk =
        (fun r => r = (fun _ => False)) ∧
      (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
        n).mir = (fun _ => False) ∧
      (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
        n).bot = (fun r => r = (fun _ => False)) ∧
      (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
        n).ltp = (fun r => r = ltpAddr) := by
  induction n with
  | zero => exact ⟨hwk₀, hmir₀, hbot₀, hltp₀⟩
  | succ n ih =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact Eq.trans (dt.stageEnd_ride hlin mV semAt ltpAddr
        (fun st => st.bot) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ _ _ _ => (dt.legStB_fields
          (PR := dt.progOf zero one hzo hpl) (aT := aT) mV _ _ _ _).2.2.1)
        _ _) ih.2.2.1
    · exact Eq.trans (dt.stageEnd_ride hlin mV semAt ltpAddr
        (fun st => st.ltp) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ _ _ _ => (dt.legStB_fields
          (PR := dt.progOf zero one hzo hpl) (aT := aT) mV _ _ _ _).2.2.2.2)
        _ _) ih.2.2.2

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
      ((dt.stageEnd hpl hlin (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            n)
          (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            n)).old i r ↔
        (dt.stageEnd hpl hlin (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            n)
          (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            n)).new i r))
    (hconv : ∀ r, WMSetLt WMLe r ltpAddr → ∀ i,
      ((dt.stageEnd hpl hlin (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            N)
          (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            N)).old i r ↔
        (dt.stageEnd hpl hlin (aT := aT) mV semAt ltpAddr
          (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            N)
          (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            N)).new i r)) :
    Relation.ReflTransGen (wideData (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)).Step
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt (.evalP (.chk 0)) f₀),
        Sum.inl (fun _ => False),
        wideTape ((dt.progOf zero one hzo hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st₀) st₀.val)
          ((dt.progOf zero one hzo hpl).syElt
            (dt.progOf zero one hzo hpl).blank)⟩
      ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt
          (.evalP (.sub (dt.smEntryOut)))
          (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀
            (N + 1))), Sum.inl v₁,
        wideTape ((dt.progOf zero one hzo hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le
            { dt.atSt (dt.offSt (dt.stageEnd hpl hlin (aT := aT)
                mV semAt ltpAddr
                (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr
                  st₀ f₀ N)
                (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr
                  st₀ f₀ N))) (fun _ => False) with
              mir := fun _ => False })
          { dt.atSt (dt.offSt (dt.stageEnd hpl hlin (aT := aT)
              mV semAt ltpAddr
              (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr
                st₀ f₀ N)
              (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr
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
      (aT := aT) mV semAt u st f).wk = st.wk :=
    fun u st f => dt.stEndB_ride (PR := dt.progOf zero one hzo hpl) (aT := aT)
      mV semAt (fun st => st.wk) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) mV _ _ _ _).2.1) u st f
  -- the stage invariant, once
  have hfields := fun n => dt.stageSt_fields (hpl := hpl) hlin (aT := aT)
    mV semAt st₀ f₀ ltpAddr hwk₀ hmir₀ hbot₀ hltp₀ n
  refine dt.reaches_main hR hlin hord htop hbot hlt hneT hiE
    (entrySt := dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr
      st₀ f₀)
    (entryFs := dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr
      st₀ f₀)
    (topSt := fun n => dt.sweepSWG
      (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
      (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt) hlin
      (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      ltpAddr)
    (topFs := fun n => dt.sweepFSG
      (dt.stEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt)
      (dt.fsEndB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV semAt) hlin
      (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      ltpAddr)
    (stT := fun n => dt.stageEnd hpl hlin (aT := aT) mV semAt
      ltpAddr
      (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n))
    (fsT := fun n => dt.stageEndFs hpl hlin (aT := aT) mV semAt
      ltpAddr
      (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n))
    ?_ ?_ ?_ ?_ ?_ hnotconv hconv
    (fun n _ => dt.stageSt_succ hlin mV semAt ltpAddr st₀ f₀ n)
    (fun n _ => dt.stageFs_succ hlin mV semAt ltpAddr st₀ f₀ n)
  · -- the sweep, per stage
    intro n _
    have h := dt.reaches_sweepB hR hlin hord htop hbot hbotV htopV mV hmV0
      hIncr hTestT hTestF semAt
      (dt.stageSt hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
      (dt.stageFs hpl hlin (aT := aT) mV semAt ltpAddr st₀ f₀ n)
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
    exact dt.reaches_spineB (PR := dt.progOf zero one hzo hpl) (aT := aT) mV
      semAt hlin _ _
      (fun i ρ => dt.prog_rules_eval zero one hzo _ hpl i ρ) hR hord htop hbot
      hbotV htopV hmV0 hIncr hTestT hTestF (hfields n).1 (hfields n).2.1
      (hfields n).2.2.1 (hemp ltpAddr) (hset.1 ltpAddr) hlt hvi
  · -- the marker, at the end of each stage
    intro n _
    exact dt.sweepStEG_wk _ _ hlin _ _ hFwk (hfields n).1 ltpAddr
      (hemp ltpAddr) (hset.1 ltpAddr)
  · -- the end marker, at the end of each stage
    intro n _
    exact Eq.trans (dt.stageEnd_ride hlin mV semAt ltpAddr
      (fun st => st.ltp) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) mV _ _ _ _).2.2.2.2)
      _ _) (hfields n).2.2.2
  · -- the bottom mark, at the end of each stage
    intro n _
    exact Eq.trans (dt.stageEnd_ride hlin mV semAt ltpAddr
      (fun st => st.bot) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := aT) mV _ _ _ _).2.2.1)
      _ _) (hfields n).2.2.1

end Stages

end Sweep

end PfpData

end Pfp

end DescriptiveComplexity
