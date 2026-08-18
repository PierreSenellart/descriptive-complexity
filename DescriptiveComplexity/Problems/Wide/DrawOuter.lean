/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawSites
import DescriptiveComplexity.Problems.Wide.DrawReset
import DescriptiveComplexity.Problems.Wide.DrawAsm

/-!
# The outer program: every call site but the evaluation

The EXPSPACE program factors as an **outer loop** – startup, the sweep's
advance, the convergence test, the copy-back, the output dispatch – around a
**per-address evaluation** whose internals (gates, the VAL loop, the atom
subroutines) are an order of magnitude larger. This file is the outer loop,
with the evaluation abstract: its phase type `PE`, its site family and its
boundary rules are parameters, exactly as
`DescriptiveComplexity.Draw.Prog.reaches_fileRoundTrip` abstracts the middle of a
trip.

The control flow:

* `start` – one rule: plant `bot` and the marker at the empty address, step
  into the pattern write.
* `tgtTop` – load TARGET with the logical-top pattern
  (`DescriptiveComplexity.Draw.MapKit`); exit into the startup seek.
* `seek1` – seek the marker to the logical top
  (`DescriptiveComplexity.Draw.SeekKit`); its exit plants the permanent `ltp`
  mark while erasing the marker, entering the reset.
* `reset1`/`clearMir1` – marker and mirror back to the empty address; exit
  into the evaluation of the first address.
* `sweepAdv` – one round of the sweep
  (`DescriptiveComplexity.Draw.AdvKit`); its landing exit re-enters the
  evaluation. The evaluation's own boundary rules dispatch back: to the
  advance below the `ltp` cell, to `reset2` at it.
* `reset2`/`clearMir2` – marker and mirror home after a completed sweep;
  `clearMir2`'s two exits ask COMPARE's question at the empty address and
  enter the passing or failing phase accordingly (a sweep's first step
  happens in the entering rule – there is no cell to the left to enter
  from).
* `compare` – the convergence test
  (`DescriptiveComplexity.Draw.FlagSweepKit`); at the `ltp` cell its verdict
  exits leave: passing to the output evaluation's walk home, failing to the
  copy-back's.
* `homeCmp`/`copy`/`homeCopy` – walk home, copy the next stage over the
  current one (`DescriptiveComplexity.Draw.WriteSweepKit`, its first step in
  `homeCmp`'s exit), walk home, and re-enter the evaluation for the next
  sweep.
* `homeOut` – walk home and enter the output evaluation; its accepting exit
  is the program's single accepting phase, its failing verdict halts (no
  rule), which is a correct *no*.

Everything here is rules and shapes; the runs are `DrawRun`'s.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The outer phases -/

/-- **The phases of the outer program**: one copy of its kit's phase shape
per call site, the four bespoke phases, and the evaluation's phases. -/
inductive OuterPh (PE : Type) : Type
  /-- The initial phase. -/
  | start : OuterPh PE
  /-- Loading TARGET with the logical-top pattern. -/
  | tgtTopP : TrackPh → OuterPh PE
  /-- The startup seek to the logical top. -/
  | seek1P : SeekPh → OuterPh PE
  /-- The startup reset. -/
  | reset1P : ResetPh → OuterPh PE
  /-- Clearing the mirror after the startup reset. -/
  | clearMir1P : TrackPh → OuterPh PE
  /-- One round of the sweep. -/
  | advP : AdvPh → OuterPh PE
  /-- The reset after a completed sweep. -/
  | reset2P : ResetPh → OuterPh PE
  /-- Clearing the mirror before the convergence test. -/
  | clearMir2P : TrackPh → OuterPh PE
  /-- The convergence test. -/
  | cmpP : SweepPh → OuterPh PE
  /-- Walking home after a failed test. -/
  | homeCmpP : OuterPh PE
  /-- The copy-back. -/
  | copyP : OuterPh PE
  /-- Walking home after the copy-back. -/
  | homeCopyP : OuterPh PE
  /-- Walking home after a passed test. -/
  | homeOutP : OuterPh PE
  /-- The accepting phase: no rule leaves it. -/
  | acceptP : OuterPh PE
  /-- A phase of the evaluation. -/
  | evalP : PE → OuterPh PE

instance {PE : Type} [Finite PE] : Finite (OuterPh PE) :=
  Finite.of_injective
    (fun p => match p with
      | .start => (Sum.inl (Sum.inl 0) : (Fin 6 ⊕ (Fin 4 × TrackPh)) ⊕
          (SeekPh ⊕ ResetPh ⊕ ResetPh ⊕ AdvPh ⊕ SweepPh ⊕ PE))
      | .homeCmpP => Sum.inl (Sum.inl 1)
      | .copyP => Sum.inl (Sum.inl 2)
      | .homeCopyP => Sum.inl (Sum.inl 3)
      | .homeOutP => Sum.inl (Sum.inl 4)
      | .acceptP => Sum.inl (Sum.inl 5)
      | .tgtTopP t => Sum.inl (Sum.inr (0, t))
      | .clearMir1P t => Sum.inl (Sum.inr (1, t))
      | .clearMir2P t => Sum.inl (Sum.inr (2, t))
      | .seek1P s => Sum.inr (Sum.inl s)
      | .reset1P r => Sum.inr (Sum.inr (Sum.inl r))
      | .reset2P r => Sum.inr (Sum.inr (Sum.inr (Sum.inl r)))
      | .advP a => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))
      | .cmpP c => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))))
      | .evalP e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr e))))))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-! ### The outer sites -/

/-- **The call sites of the outer program**, plus the evaluation's. -/
inductive OuterSite (SE : Type) : Type
  /-- The initial step. -/
  | start : OuterSite SE
  /-- The pattern write of startup. -/
  | tgtTop : OuterSite SE
  /-- The startup seek. -/
  | seek1 : OuterSite SE
  /-- The startup reset. -/
  | reset1 : OuterSite SE
  /-- The startup mirror clear. -/
  | clearMir1 : OuterSite SE
  /-- The sweep's advance. -/
  | sweepAdv : OuterSite SE
  /-- The post-sweep reset. -/
  | reset2 : OuterSite SE
  /-- The pre-compare mirror clear. -/
  | clearMir2 : OuterSite SE
  /-- The convergence test. -/
  | compare : OuterSite SE
  /-- The walk home before the copy-back. -/
  | homeCmp : OuterSite SE
  /-- The copy-back. -/
  | copy : OuterSite SE
  /-- The walk home after the copy-back. -/
  | homeCopy : OuterSite SE
  /-- The walk home before the output evaluation. -/
  | homeOut : OuterSite SE
  /-- The accepting phase's site: no rules. -/
  | accept : OuterSite SE
  /-- An evaluation site. -/
  | eval : SE → OuterSite SE

/-- **The rule shape of each outer site**: the kit's rules, summed with the
site's exit rules. -/
def OuterSh (SE : Type) (ShE : SE → Type) : OuterSite SE → Type
  | .start => Unit
  | .tgtTop => TrackRule ⊕ Unit
  | .seek1 => SeekRule ⊕ Unit
  | .reset1 => ResetRule ⊕ Unit
  | .clearMir1 => TrackRule ⊕ Unit
  | .sweepAdv => AdvRule ⊕ Unit
  | .reset2 => ResetRule ⊕ Unit
  | .clearMir2 => TrackRule ⊕ Bool
  | .compare => SweepRule ⊕ Bool
  | .homeCmp => HomeKit.HomeRule ⊕ Unit
  | .copy => WSweepRule ⊕ Unit
  | .homeCopy => HomeKit.HomeRule ⊕ Unit
  | .homeOut => HomeKit.HomeRule ⊕ Unit
  | .accept => Empty
  | .eval e => ShE e

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A Q PE SE : Type}
variable (zero one : A) {ShE : SE → Type}

/-- The standard exit guard at a kit end phase: at the marker, which is
nobody's register. -/
def exitG (g : dt.SlotIx → A) : Prop :=
  g .wk = one ∧ g .reg ≠ one

/-- COMPARE's per-cell question, shared by the test's rules and the entering
exits. -/
def cmpG (g : dt.SlotIx → A) : Prop :=
  ∀ i : dt.d.B.ι, (g (.old i) = one ↔ g (.new i) = one)

/-- **The rules of the outer program**: each site's kit rules at its phase
copy, and its exit rules. The evaluation's rules – including its boundary
rules into `sweepAdv`'s and `reset2`'s entries – are the parameter
`ruleE`. -/
noncomputable def outerRule
    (ruleE : ∀ e : SE, ShE e → Rule A Q dt.SlotIx (OuterPh PE))
    (evalEntry evalEntryOut : PE) :
    ∀ i : OuterSite SE, OuterSh SE ShE i → Rule A Q dt.SlotIx (OuterPh PE)
  | .start, _ =>
    { guard := fun _ _ => True
      srcPh := .start
      dstPh := .tgtTopP .up
      dstSt := fun f _ => f
      wr := fun _ g => Function.update (Function.update g .wk one) .bot one
      moveRight := True }
  | .tgtTop, Sum.inl ρ => (dt.tgtTopKit one .tgtTopP).rule zero one ρ
  | .tgtTop, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .tgtTopP .run
      dstPh := .seek1P .chk
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .seek1, Sum.inl ρ => (dt.seekKit .seek1P).rule zero one ρ
  | .seek1, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .seek1P .ty
      dstPh := .reset1P .scan
      dstSt := fun f _ => f
      wr := fun _ g => Function.update (Function.update g .wk zero) .ltp one
      moveRight := True }
  | .reset1, Sum.inl ρ => (ResetKit.mk (A := A) (Q := Q) .mir .bot .wk .reset1P).rule one ρ
  | .reset1, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .reset1P .done
      dstPh := .clearMir1P .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .clearMir1, Sum.inl ρ => (dt.clearMirKit .clearMir1P).rule zero one ρ
  | .clearMir1, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .clearMir1P .run
      dstPh := .evalP evalEntry
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .sweepAdv, Sum.inl ρ => (dt.advKit .advP).rule zero one ρ
  | .sweepAdv, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .advP .a4
      dstPh := .evalP evalEntry
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .reset2, Sum.inl ρ => (ResetKit.mk (A := A) (Q := Q) .mir .bot .wk .reset2P).rule one ρ
  | .reset2, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .reset2P .done
      dstPh := .clearMir2P .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .clearMir2, Sum.inl ρ => (dt.clearMirKit .clearMir2P).rule zero one ρ
  | .clearMir2, Sum.inr b =>
    { guard := fun _ g => dt.exitG one g ∧ (dt.cmpG one g ↔ b = true)
      srcPh := .clearMir2P .run
      dstPh := .cmpP (if b then .py else .pn)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .compare, Sum.inl ρ => (dt.compareKit one .cmpP).rule one ρ
  | .compare, Sum.inr b =>
    { guard := fun _ g => g .ltp = one
      srcPh := .cmpP (if b then .py else .pn)
      dstPh := if b then .homeOutP else .homeCmpP
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .homeCmp, Sum.inl ρ => (HomeKit.mk (A := A) (Q := Q) .mir .wk .homeCmpP).rule one ρ
  | .homeCmp, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .homeCmpP
      dstPh := .copyP
      dstSt := fun f _ => f
      wr := fun _ g => (dt.copyKit (A := A) (Q := Q) (P := OuterPh PE) .copyP).wrG g
      moveRight := True }
  | .copy, Sum.inl ρ => (dt.copyKit .copyP).rule one ρ
  | .copy, Sum.inr _ =>
    { guard := fun _ g => g .ltp = one
      srcPh := .copyP
      dstPh := .homeCopyP
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .homeCopy, Sum.inl ρ => (HomeKit.mk (A := A) (Q := Q) .mir .wk .homeCopyP).rule one ρ
  | .homeCopy, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .homeCopyP
      dstPh := .evalP evalEntry
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .homeOut, Sum.inl ρ => (HomeKit.mk (A := A) (Q := Q) .mir .wk .homeOutP).rule one ρ
  | .homeOut, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := .homeOutP
      dstPh := .evalP evalEntryOut
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .accept, e => e.elim
  | .eval e, ρ => ruleE e ρ

/-- **The owner of each phase**: the site whose copy of a phase shape it is;
the evaluation's phases are owned through the parameter. -/
def outerOwner (ownE : PE → SE) : OuterPh PE → OuterSite SE
  | .start => .start
  | .tgtTopP _ => .tgtTop
  | .seek1P _ => .seek1
  | .reset1P _ => .reset1
  | .clearMir1P _ => .clearMir1
  | .advP _ => .sweepAdv
  | .reset2P _ => .reset2
  | .clearMir2P _ => .clearMir2
  | .cmpP _ => .compare
  | .homeCmpP => .homeCmp
  | .copyP => .copy
  | .homeCopyP => .homeCopy
  | .homeOutP => .homeOut
  | .acceptP => .accept
  | .evalP p => .eval (ownE p)

/-! ### The in-shape separation, site by site -/

section Sep

variable (hzo : zero ≠ one)
variable {ruleE : ∀ e : SE, ShE e → Rule A Q dt.SlotIx (OuterPh PE)}
variable {evalEntry evalEntryOut : PE}
variable (hsepE : ∀ (e : SE) (ρ ρ' : ShE e) (f : Q → A) (g : dt.SlotIx → A),
  (ruleE e ρ).guard f g → (ruleE e ρ').guard f g →
  (ruleE e ρ).srcPh = (ruleE e ρ').srcPh → ρ = ρ')

include hzo hsepE in
/-- **Each outer site separates in-shape**: the kit's separation on its own
rules, its exit-disjointness against the exits, and the exits' guards or
target phases against each other. This is the `hsep` field of the program's
`DescriptiveComplexity.Draw.Assembly`. -/
theorem outerSep :
    ∀ (i : OuterSite SE) (ρ ρ' : OuterSh SE ShE i) (f : Q → A) (g : dt.SlotIx → A),
      (dt.outerRule zero one ruleE evalEntry evalEntryOut i ρ).guard f g →
      (dt.outerRule zero one ruleE evalEntry evalEntryOut i ρ').guard f g →
      (dt.outerRule zero one ruleE evalEntry evalEntryOut i ρ).srcPh =
        (dt.outerRule zero one ruleE evalEntry evalEntryOut i ρ').srcPh →
      ρ = ρ' := by
  have htgt : Function.Injective (OuterPh.tgtTopP (PE := PE)) :=
    fun x y h => by cases h; rfl
  have hsk : Function.Injective (OuterPh.seek1P (PE := PE)) :=
    fun x y h => by cases h; rfl
  have hr1 : Function.Injective (OuterPh.reset1P (PE := PE)) :=
    fun x y h => by cases h; rfl
  have hc1 : Function.Injective (OuterPh.clearMir1P (PE := PE)) :=
    fun x y h => by cases h; rfl
  have hadv : Function.Injective (OuterPh.advP (PE := PE)) :=
    fun x y h => by cases h; rfl
  have hr2 : Function.Injective (OuterPh.reset2P (PE := PE)) :=
    fun x y h => by cases h; rfl
  have hc2 : Function.Injective (OuterPh.clearMir2P (PE := PE)) :=
    fun x y h => by cases h; rfl
  have hcmp : Function.Injective (OuterPh.cmpP (PE := PE)) :=
    fun x y h => by cases h; rfl
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .start, _, _ => rfl
  | .tgtTop, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (MapKit.sep _ zero one htgt σ σ' f g hg hg' hph)
  | .tgtTop, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      MapKit.exit_disjoint _ zero one htgt σ f g hg hg'.1 hg'.2 hp)
  | .tgtTop, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      MapKit.exit_disjoint _ zero one htgt σ f g hg' hg.1 hg.2 hp)
  | .tgtTop, Sum.inr _, Sum.inr _ => rfl
  | .seek1, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (SeekKit.sep _ zero one hzo hsk σ σ' f g hg hg' hph)
  | .seek1, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      SeekKit.exit_disjoint _ zero one hsk σ f g hg hg'.1 hg'.2 hp)
  | .seek1, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      SeekKit.exit_disjoint _ zero one hsk σ f g hg' hg.1 hg.2 hp)
  | .seek1, Sum.inr _, Sum.inr _ => rfl
  | .reset1, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ResetKit.sep _ one hr1 σ σ' f g hg hg' hph)
  | .reset1, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp => ResetKit.exit_disjoint _ one hr1 σ f g hg hp)
  | .reset1, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp => ResetKit.exit_disjoint _ one hr1 σ f g hg' hp)
  | .reset1, Sum.inr _, Sum.inr _ => rfl
  | .clearMir1, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ClearKit.sep _ zero one hc1 σ σ' f g hg hg' hph)
  | .clearMir1, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      ClearKit.exit_disjoint _ zero one hc1 σ f g hg hg'.1 hg'.2 hp)
  | .clearMir1, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      ClearKit.exit_disjoint _ zero one hc1 σ f g hg' hg.1 hg.2 hp)
  | .clearMir1, Sum.inr _, Sum.inr _ => rfl
  | .sweepAdv, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (AdvKit.sep _ zero one hzo hadv σ σ' f g hg hg' hph)
  | .sweepAdv, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      AdvKit.exit_disjoint _ zero one hadv σ f g hg hg'.1 hg'.2 hp)
  | .sweepAdv, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      AdvKit.exit_disjoint _ zero one hadv σ f g hg' hg.1 hg.2 hp)
  | .sweepAdv, Sum.inr _, Sum.inr _ => rfl
  | .reset2, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ResetKit.sep _ one hr2 σ σ' f g hg hg' hph)
  | .reset2, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp => ResetKit.exit_disjoint _ one hr2 σ f g hg hp)
  | .reset2, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp => ResetKit.exit_disjoint _ one hr2 σ f g hg' hp)
  | .reset2, Sum.inr _, Sum.inr _ => rfl
  | .clearMir2, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ClearKit.sep _ zero one hc2 σ σ' f g hg hg' hph)
  | .clearMir2, Sum.inl σ, Sum.inr b =>
    exact absurd hph (fun hp =>
      ClearKit.exit_disjoint _ zero one hc2 σ f g hg hg'.1.1 hg'.1.2 hp)
  | .clearMir2, Sum.inr b, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      ClearKit.exit_disjoint _ zero one hc2 σ f g hg' hg.1.1 hg.1.2 hp)
  | .clearMir2, Sum.inr b, Sum.inr b' =>
    have hbb : b = b' := by
      have h2 := hg.2.symm.trans hg'.2
      cases b <;> cases b' <;> simp_all
    rw [hbb]
  | .compare, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (FlagSweepKit.sep _ one hcmp σ σ' f g hg hg' hph)
  | .compare, Sum.inl σ, Sum.inr b =>
    exact absurd hg' (fun hp => FlagSweepKit.exit_disjoint _ one σ f g hg hp)
  | .compare, Sum.inr b, Sum.inl σ =>
    exact absurd hg (fun hp => FlagSweepKit.exit_disjoint _ one σ f g hg' hp)
  | .compare, Sum.inr b, Sum.inr b' =>
    have hbb : b = b' := by
      have h2 := hcmp hph
      cases b <;> cases b' <;> simp_all
    rw [hbb]
  | .homeCmp, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (HomeKit.sep _ one σ σ' f g hg hg' hph)
  | .homeCmp, Sum.inl σ, Sum.inr _ =>
    exact absurd hg'.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg hp)
  | .homeCmp, Sum.inr _, Sum.inl σ =>
    exact absurd hg.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg' hp)
  | .homeCmp, Sum.inr _, Sum.inr _ => rfl
  | .copy, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (WriteSweepKit.sep _ one σ σ' f g hg hg' hph)
  | .copy, Sum.inl σ, Sum.inr _ =>
    exact absurd hg' (fun hp => WriteSweepKit.exit_disjoint _ one σ f g hg hp)
  | .copy, Sum.inr _, Sum.inl σ =>
    exact absurd hg (fun hp => WriteSweepKit.exit_disjoint _ one σ f g hg' hp)
  | .copy, Sum.inr _, Sum.inr _ => rfl
  | .homeCopy, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (HomeKit.sep _ one σ σ' f g hg hg' hph)
  | .homeCopy, Sum.inl σ, Sum.inr _ =>
    exact absurd hg'.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg hp)
  | .homeCopy, Sum.inr _, Sum.inl σ =>
    exact absurd hg.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg' hp)
  | .homeCopy, Sum.inr _, Sum.inr _ => rfl
  | .homeOut, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (HomeKit.sep _ one σ σ' f g hg hg' hph)
  | .homeOut, Sum.inl σ, Sum.inr _ =>
    exact absurd hg'.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg hp)
  | .homeOut, Sum.inr _, Sum.inl σ =>
    exact absurd hg.1 (fun hp => HomeKit.exit_disjoint _ one σ f g hg' hp)
  | .homeOut, Sum.inr _, Sum.inr _ => rfl
  | .accept, e, _ => exact e.elim
  | .eval e, σ, σ' => exact hsepE e σ σ' f g hg hg' hph

end Sep

/-! ### Ownership, and the assembly -/

section Asm

variable {ruleE : ∀ e : SE, ShE e → Rule A Q dt.SlotIx (OuterPh PE)}
variable {evalEntry evalEntryOut : PE} {ownE : PE → SE}
variable (hosrcE : ∀ (e : SE) (ρ : ShE e),
  ∃ p : PE, (ruleE e ρ).srcPh = .evalP p ∧ ownE p = e)

include hosrcE in
/-- **Every rule fires from a phase its site owns.** -/
theorem outerHowner :
    ∀ (i : OuterSite SE) (ρ : OuterSh SE ShE i),
      outerOwner ownE
        ((dt.outerRule zero one ruleE evalEntry evalEntryOut i ρ).srcPh) = i := by
  intro i ρ
  match i, ρ with
  | .start, _ => rfl
  | .tgtTop, Sum.inl σ => cases σ <;> rfl
  | .tgtTop, Sum.inr _ => rfl
  | .seek1, Sum.inl σ => cases σ <;> rfl
  | .seek1, Sum.inr _ => rfl
  | .reset1, Sum.inl σ => cases σ <;> rfl
  | .reset1, Sum.inr _ => rfl
  | .clearMir1, Sum.inl σ => cases σ <;> rfl
  | .clearMir1, Sum.inr _ => rfl
  | .sweepAdv, Sum.inl σ => cases σ <;> rfl
  | .sweepAdv, Sum.inr _ => rfl
  | .reset2, Sum.inl σ => cases σ <;> rfl
  | .reset2, Sum.inr _ => rfl
  | .clearMir2, Sum.inl σ => cases σ <;> rfl
  | .clearMir2, Sum.inr _ => rfl
  | .compare, Sum.inl σ => cases σ <;> rfl
  | .compare, Sum.inr b => cases b <;> rfl
  | .homeCmp, Sum.inl σ => (cases σ; rfl)
  | .homeCmp, Sum.inr _ => rfl
  | .copy, Sum.inl σ => (cases σ; rfl)
  | .copy, Sum.inr _ => rfl
  | .homeCopy, Sum.inl σ => (cases σ; rfl)
  | .homeCopy, Sum.inr _ => rfl
  | .homeOut, Sum.inl σ => (cases σ; rfl)
  | .homeOut, Sum.inr _ => rfl
  | .accept, e => exact e.elim
  | .eval e, σ =>
    obtain ⟨p, hp, he⟩ := hosrcE e σ
    change outerOwner ownE (ruleE e σ).srcPh = OuterSite.eval e
    rw [hp]
    exact congrArg OuterSite.eval he

variable [Fintype Q] [Fintype dt.SlotIx]

/-- **The outer program, assembled**: the sites, their rules, ownership and
in-shape separation, ready for `DescriptiveComplexity.Draw.Assembly.prog` and
its `Table.Sep`. The evaluation contributes its site family, its boundary
data and its own separation as parameters. -/
noncomputable def outerAsm (hzo : zero ≠ one)
    (hsepE : ∀ (e : SE) (ρ ρ' : ShE e) (f : Q → A) (g : dt.SlotIx → A),
      (ruleE e ρ).guard f g → (ruleE e ρ').guard f g →
      (ruleE e ρ).srcPh = (ruleE e ρ').srcPh → ρ = ρ') :
    Assembly A Q dt.SlotIx (OuterPh PE) (OuterSite SE) where
  Sh := OuterSh SE ShE
  rule := dt.outerRule zero one ruleE evalEntry evalEntryOut
  owner := outerOwner ownE
  howner := outerHowner (dt := dt) (zero := zero) (one := one) (hosrcE := hosrcE)
  hsep := outerSep (dt := dt) (zero := zero) (one := one) (hzo := hzo) (hsepE := hsepE)

end Asm

end Data

end Draw

end DescriptiveComplexity
