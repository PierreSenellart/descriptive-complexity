/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawSweep
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawKit
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMLe WMSetLe wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Kits for the plain sweeps

The kits wrapping the two plain-sweep composites of
`DescriptiveComplexity.Problems.Wide.DrawSweep` – one step per address of a
stretch, no register visits. `DescriptiveComplexity.Draw.FlagSweepKit` asks
one question per cell with the verdict in the phase (COMPARE);
`DescriptiveComplexity.Draw.WriteSweepKit` rewrites each cell once (COPY).

Both composites take their rules **bounded to the stretch**, and the kits
realize the bound the way the program does: a
permanent end marker `ltp` planted at the top of the stretch once, at
startup. Every stepping rule is guarded `ltp ≠ one`, so the sweep has no
rule at the marked cell and stops there; the caller's exit rule at
`ltp = one` is disjoint from every rule here.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The flag sweep's shapes -/

/-- **The phases of a flag sweep**: still passing, or failed. -/
inductive SweepPh : Type
  /-- Every cell so far passed. -/
  | py : SweepPh
  /-- Some cell failed. -/
  | pn : SweepPh
  deriving DecidableEq

instance : Finite SweepPh :=
  Finite.of_injective
    (fun p => match p with | .py => (0 : Fin 2) | .pn => 1)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule families of a flag sweep.** -/
inductive SweepRule : Type
  /-- The cell passes: step on in the passing phase. -/
  | yGo : SweepRule
  /-- The cell fails: step on in the failing phase. -/
  | yFail : SweepRule
  /-- Cruise in the failing phase. -/
  | nGo : SweepRule
  deriving DecidableEq

instance : Finite SweepRule :=
  Finite.of_injective
    (fun p => match p with | .yGo => (0 : Fin 3) | .yFail => 1 | .nGo => 2)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **A flag-sweep kit**: the walked track, the end-marker slot, the per-cell
question, and the phases. -/
structure FlagSweepKit (A Q W P : Type) where
  /-- The walked track. -/
  t : W
  /-- The end-marker slot: set exactly at the top of the stretch. -/
  ltp : W
  /-- The per-cell question, decided by the tracks. -/
  TestG : (W → A) → Prop
  /-- The kit's phases in the program. -/
  emb : SweepPh → P

namespace FlagSweepKit

variable {A Q W P : Type} (κ : FlagSweepKit A Q W P) (one : A)

/-- **The kit's rules.** -/
def rule : SweepRule → Rule A Q W P
  | .yGo =>
    { guard := fun _ g => κ.TestG g ∧ g κ.ltp ≠ one
      srcPh := κ.emb .py
      dstPh := κ.emb .py
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .yFail =>
    { guard := fun _ g => ¬κ.TestG g ∧ g κ.ltp ≠ one
      srcPh := κ.emb .py
      dstPh := κ.emb .pn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .nGo =>
    { guard := fun _ g => g κ.ltp ≠ one
      srcPh := κ.emb .pn
      dstPh := κ.emb .pn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }

/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : SweepRule) (f : Q → A) (g : W → A),
      (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
      (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd hg.1 hg'.1
    | exact absurd hg'.1 hg.1
    | (have hbb := hemb hph; cases hbb)

/-- **Exit disjointness**: no kit rule fires at the end-marked cell, in any
phase – the caller's exit rules there, guarded `ltp = one`, are disjoint from
the whole kit. -/
theorem exit_disjoint : ∀ (ρ : SweepRule) (f : Q → A) (g : W → A),
    (κ.rule one ρ).guard f g → g κ.ltp = one → False := by
  intro ρ f g hg hltp
  cases ρ <;> simp only [rule] at hg <;> first
    | exact absurd hltp hg.2
    | exact absurd hltp hg

/-! ### The discharge -/

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

variable [Lax822549.WideMachines.wide.Structure (Univ A R P K dd)]

variable [Finite A] [Finite R] [Finite P] [Finite K]

variable {PR : Prog A R P Q W K dd} {κ : FlagSweepKit A Q W P}

variable {rEmb : SweepRule → R}

variable (hrules : ∀ ρ : SweepRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)

variable {cell : Univ A R P K dd → (Univ A R P K dd → Prop)}

variable (hR : PR.table.Reads) (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R P K dd)))

variable (hneltp : κ.ltp ≠ κ.t)

variable {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}

variable {ltpAddr : Univ A R P K dd → Prop}

variable (hltp : ∀ r : Univ A R P K dd → Prop,
  rest r κ.ltp = bitVal PR.zero PR.one (r = ltpAddr))

variable {Test : (Univ A R P K dd → Prop) → Prop}

variable (hcompat : ∀ r : Univ A R P K dd → Prop,
  κ.TestG (PR.passTracksAt cell κ.t rest m r) ↔ Test r)

variable {fc : Q → A}

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Lax822549.WideMachines.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight` witness. -/
private theorem has_of_rule {ρ : SweepRule} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.one ρ).guard f g) :
    ∀ _hmr : (κ.rule PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh ((κ.rule PR.one ρ).dstSt f g)
        ((κ.rule PR.one ρ).wr f g) := fun hmr =>
  ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
    by rw [hrules], by rw [hrules], by rw [hrules]; exact hmr⟩

include hrules hR hlin hneltp hltp hcompat in
/-- **The kit runs its sweep**: one step per address of the stretch, the
verdict in the phase via `DescriptiveComplexity.sweepState`. The stretch's
top must sit at or below the end marker's address. -/
theorem reachesIn {s₀ s₁ : Univ A R P K dd → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁)
    (htp : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₁ ltpAddr) :
    (Lax822549.WideMachines.wideData (Univ A R P K dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (sweepState Test (PR.stElt (κ.emb .py) fc) (PR.stElt (κ.emb .pn) fc) s₀),
        Sum.inl s₀, wideTape (PR.trackTapeAt cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (sweepState Test (PR.stElt (κ.emb .py) fc) (PR.stElt (κ.emb .pn) fc) s₁),
        Sum.inl s₁, wideTape (PR.trackTapeAt cell κ.t rest m) (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- a cell strictly inside the stretch is not the end marker's
  have hoff : ∀ r r' : Univ A R P K dd → Prop, WMIncr Lax822549.WideMachines.WMLe r r' → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r' s₁ →
      PR.passTracksAt cell κ.t rest m r κ.ltp ≠ PR.one := by
    intro r r' hi hub
    have hlt : WMSetLt Lax822549.WideMachines.WMLe r ltpAddr := by
      refine (wmSetLt_iff _ _).mpr
        ⟨hlinSet.2.1 _ _ _ (wmSetLe_of_wmIncr hi) (hlinSet.2.1 _ _ _ hub htp), ?_⟩
      rintro rfl
      have hlt' : WMSetLt Lax822549.WideMachines.WMLe r r' :=
        (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
      exact ((wmSetLt_iff _ _).mp hlt').2
        (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hlt').1 (hlinSet.2.1 _ _ _ hub htp))
    rw [Prog.passTracks_of_ne hneltp, hltp, bitVal_neg ((wmSetLt_iff _ _).mp hlt).2]
    exact PR.zero_ne_one
  exact Prog.reachesIn_flagSweep hR hlin (t := κ.t) (rest := rest) (m := m)
    (Test := Test) (py := κ.emb .py) (pn := κ.emb .pn) (f := fc) hle
    (fun r r' hi _hlb hub hTest =>
      has_of_rule hrules (ρ := .yGo)
        ⟨(hcompat r).mpr hTest, hoff r r' hi hub⟩ trivial)
    (fun r r' hi _hlb hub hTest =>
      has_of_rule hrules (ρ := .yFail)
        ⟨fun hc => hTest ((hcompat r).mp hc), hoff r r' hi hub⟩ trivial)
    (fun r r' hi _hlb hub =>
      has_of_rule hrules (ρ := .nGo) (hoff r r' hi hub) trivial)

include hrules hR hlin hneltp hltp hcompat in
/-- **The kit runs its sweep**, the budget forgotten. -/
theorem reaches {s₀ s₁ : Univ A R P K dd → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁)
    (htp : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₁ ltpAddr) :
    Relation.ReflTransGen (Lax822549.WideMachines.wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (sweepState Test (PR.stElt (κ.emb .py) fc) (PR.stElt (κ.emb .pn) fc) s₀),
        Sum.inl s₀, wideTape (PR.trackTapeAt cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (sweepState Test (PR.stElt (κ.emb .py) fc) (PR.stElt (κ.emb .pn) fc) s₁),
        Sum.inl s₁, wideTape (PR.trackTapeAt cell κ.t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn hrules hR hlin hneltp hltp hcompat hle htp).reflTransGen

end Discharge

end FlagSweepKit

/-! ### The write sweep's shape -/

/-- **The rule of a write sweep**: one family, rewriting each cell as the head
leaves it. -/
inductive WSweepRule : Type
  /-- Rewrite the cell and step on. -/
  | put : WSweepRule
  deriving DecidableEq

instance : Finite WSweepRule :=
  Finite.of_injective (fun _ => (0 : Fin 1)) (by intro a b _; cases a; cases b; rfl)

/-- **A write-sweep kit**: the walked track, the end-marker slot, the per-cell
rewrite as a function of the tracks, and the one phase. -/
structure WriteSweepKit (A Q W P : Type) where
  /-- The walked track. -/
  t : W
  /-- The end-marker slot: set exactly at the top of the stretch. -/
  ltp : W
  /-- The per-cell rewrite, computed from the tracks. -/
  wrG : (W → A) → (W → A)
  /-- The kit's phase in the program. -/
  ph : P

namespace WriteSweepKit

variable {A Q W P : Type} (κ : WriteSweepKit A Q W P) (one : A)

/-- **The kit's rule.** -/
def rule : WSweepRule → Rule A Q W P
  | .put =>
    { guard := fun _ g => g κ.ltp ≠ one
      srcPh := κ.ph
      dstPh := κ.ph
      dstSt := fun f _ => f
      wr := fun _ g => κ.wrG g
      moveRight := True }

/-- **In-shape separation**: one rule, nothing to separate. -/
theorem sep : ∀ (ρ ρ' : WSweepRule) (f : Q → A) (g : W → A),
    (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
    (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' _f _g _hg _hg' _hph
  cases ρ; cases ρ'; rfl

/-- **Exit disjointness**: the single rule never fires at the end-marked
cell. -/
theorem exit_disjoint : ∀ (ρ : WSweepRule) (f : Q → A) (g : W → A),
    (κ.rule one ρ).guard f g → g κ.ltp = one → False := by
  intro ρ f g hg hltp
  cases ρ
  exact absurd hltp hg

/-! ### The discharge -/

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

variable [Lax822549.WideMachines.wide.Structure (Univ A R P K dd)]

variable [Finite A] [Finite R] [Finite P] [Finite K]

variable {PR : Prog A R P Q W K dd} {κ : WriteSweepKit A Q W P}

variable {rEmb : WSweepRule → R}

variable (hrules : ∀ ρ : WSweepRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)

variable {cell : Univ A R P K dd → (Univ A R P K dd → Prop)}

variable (hR : PR.table.Reads) (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R P K dd)))

variable (hneltp : κ.ltp ≠ κ.t)

variable {m : Univ A R P K dd → Prop}

variable {restAt : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}

variable {ltpAddr : Univ A R P K dd → Prop}

variable (hltp : ∀ k r : Univ A R P K dd → Prop,
  restAt k r κ.ltp = bitVal PR.zero PR.one (r = ltpAddr))

variable {fc : Q → A}

include hrules hR hlin hneltp hltp in
/-- **The kit runs its sweep**: one rewrite per address, the background a
function of the frontier. The rewrite the kit's rule computes must match the
background's change at each cell, which is the one semantic hypothesis. -/
theorem reachesIn {s₀ s₁ : Univ A R P K dd → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁)
    (htp : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₁ ltpAddr)
    (hframe : ∀ s u : Univ A R P K dd → Prop, WMIncr Lax822549.WideMachines.WMLe s u →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe u s₁ →
      ∀ r : Univ A R P K dd → Prop, r ≠ s → restAt u r = restAt s r)
    (hwr : ∀ s u : Univ A R P K dd → Prop, WMIncr Lax822549.WideMachines.WMLe s u →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe u s₁ →
      κ.wrG (PR.passTracksAt cell κ.t (restAt s) m s) = PR.passTracksAt cell κ.t (restAt u) m s) :
    (Lax822549.WideMachines.wideData (Univ A R P K dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt κ.ph fc), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell κ.t (restAt s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt κ.ph fc), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell κ.t (restAt s₁) m) (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  have hoff : ∀ r r' : Univ A R P K dd → Prop, WMIncr Lax822549.WideMachines.WMLe r r' → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r' s₁ →
      PR.passTracksAt cell κ.t (restAt r) m r κ.ltp ≠ PR.one := by
    intro r r' hi hub
    have hlt : WMSetLt Lax822549.WideMachines.WMLe r ltpAddr := by
      refine (wmSetLt_iff _ _).mpr
        ⟨hlinSet.2.1 _ _ _ (wmSetLe_of_wmIncr hi) (hlinSet.2.1 _ _ _ hub htp), ?_⟩
      rintro rfl
      have hlt' : WMSetLt Lax822549.WideMachines.WMLe r r' :=
        (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
      exact ((wmSetLt_iff _ _).mp hlt').2
        (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hlt').1 (hlinSet.2.1 _ _ _ hub htp))
    rw [Prog.passTracks_of_ne hneltp, hltp, bitVal_neg ((wmSetLt_iff _ _).mp hlt).2]
    exact PR.zero_ne_one
  refine Prog.reachesIn_writeSweep hR hlin (t := κ.t) (m := m) (restAt := restAt)
    (p := κ.ph) (f := fc) hle hframe fun s u hi hlb hub => ?_
  have hput := (show ∀ _hmr : (κ.rule PR.one .put).moveRight,
      PR.HasRight (κ.rule PR.one .put).srcPh fc (PR.passTracksAt cell κ.t (restAt s) m s)
        (κ.rule PR.one .put).dstPh
        ((κ.rule PR.one .put).dstSt fc (PR.passTracksAt cell κ.t (restAt s) m s))
        ((κ.rule PR.one .put).wr fc (PR.passTracksAt cell κ.t (restAt s) m s)) from
    fun hmr => ⟨rEmb .put, by rw [hrules]; exact hoff s u hi hub,
      by rw [hrules], by rw [hrules], by rw [hrules], by rw [hrules],
      by rw [hrules]; exact hmr⟩) trivial
  rw [show (κ.rule PR.one .put).wr fc (PR.passTracksAt cell κ.t (restAt s) m s) =
      PR.passTracksAt cell κ.t (restAt u) m s from hwr s u hi hlb hub] at hput
  exact hput

include hrules hR hlin hneltp hltp in
/-- **The kit runs its sweep**, the budget forgotten. -/
theorem reaches {s₀ s₁ : Univ A R P K dd → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁)
    (htp : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₁ ltpAddr)
    (hframe : ∀ s u : Univ A R P K dd → Prop, WMIncr Lax822549.WideMachines.WMLe s u →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe u s₁ →
      ∀ r : Univ A R P K dd → Prop, r ≠ s → restAt u r = restAt s r)
    (hwr : ∀ s u : Univ A R P K dd → Prop, WMIncr Lax822549.WideMachines.WMLe s u →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe u s₁ →
      κ.wrG (PR.passTracksAt cell κ.t (restAt s) m s) = PR.passTracksAt cell κ.t (restAt u) m s) :
    Relation.ReflTransGen (Lax822549.WideMachines.wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt κ.ph fc), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell κ.t (restAt s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt κ.ph fc), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell κ.t (restAt s₁) m) (PR.syElt PR.blank)⟩ :=
  (reachesIn hrules hR hlin hneltp hltp hle htp hframe hwr).reflTransGen

end Discharge

end WriteSweepKit

end Draw

end Lax822549Proofs.DescriptiveComplexity


