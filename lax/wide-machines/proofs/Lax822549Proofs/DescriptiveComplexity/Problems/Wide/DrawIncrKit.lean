/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawTripKits
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
export Lax822549.WideMachines (WMLe WMSetLe WPoint wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The increment kit: a round trip around the block-indexed mirror increment

The kit wrapping `DescriptiveComplexity.Draw.Prog.reaches_fileIncrBlk` in its round
trip: scan up to the file top, bounce, run the binary increment down the file
– clearing set digits until the first clear one, setting it – and return to
the marker **in the phase of the block that carried**. The inner VAL loop of
the EXPSPACE program folds its accumulators against exactly that block,
which is why the landing phase is indexed.

The carry block is read off the *mark* of the register cell that carried: the
kit takes one slot per block (`bs`), set exactly at the registers of that
block, and its `set` rule comes in one copy per block. The one-hot clause in
that rule's guard is what makes two copies separable – at an arbitrary
symbol two block slots could both be set, and the third hardening of the
layer (`DescriptiveComplexity.Draw.Prog.reaches_fileIncrBlk`'s one-hot hypothesis)
made the demand and the guard match.

Rules are owned by their source phase: entry (at the scan phase) and exit
(at the marker, in a landing phase, guarded `wk = one ∧ rg ≠ one`) belong to
the caller.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The increment trip's shapes -/

/-- **The phases of an increment trip**: the up-scan, the bounce, the carry
phase, and one landing phase per block. -/
inductive IncrPh (B : Type) : Type
  /-- Scanning up to the file top. -/
  | up : IncrPh B
  /-- Bounced off the top, about to re-enter rightwards. -/
  | b2 : IncrPh B
  /-- Clearing set digits, looking for the first clear one. -/
  | pc : IncrPh B
  /-- The digit of this block was set: walking home. -/
  | pd : B → IncrPh B

instance {B : Type} [Finite B] : Finite (IncrPh B) :=
  Finite.of_injective
    (fun p => match p with
      | .up => (Sum.inl 0 : Fin 3 ⊕ B) | .b2 => Sum.inl 1 | .pc => Sum.inl 2
      | .pd b => Sum.inr b)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule families of an increment trip**, the acting ones per block. -/
inductive IncrRule (B : Type) : Type
  /-- Scan right while the file-top mark is clear. -/
  | up : IncrRule B
  /-- At the file top: step left into the bounce phase. -/
  | b1 : IncrRule B
  /-- Bounce: step back right into the carry phase. -/
  | b2go : IncrRule B
  /-- At a register with a set digit: clear it, carry on. -/
  | clear : IncrRule B
  /-- At a register of this block with a clear digit: set it, land. -/
  | set : B → IncrRule B
  /-- Walk left over unmarked cells in the carry phase. -/
  | walk : IncrRule B
  /-- Hold at registers, walk and return, in this block's landing phase. -/
  | stay : B → IncrRule B

instance {B : Type} [Finite B] : Finite (IncrRule B) :=
  Finite.of_injective
    (fun p => match p with
      | .up => (Sum.inl 0 : Fin 5 ⊕ (Bool × B)) | .b1 => Sum.inl 1
      | .b2go => Sum.inl 2 | .clear => Sum.inl 3 | .walk => Sum.inl 4
      | .set b => Sum.inr (false, b) | .stay b => Sum.inr (true, b))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **An increment kit**: the walked track, the service slots, the per-block
mark slots, and the phases. -/
structure IncrKit (A Q W P B : Type) where
  /-- The walked track being incremented. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The block mark: set exactly at the registers of that block. -/
  bs : B → W
  /-- The kit's phases in the program. -/
  emb : IncrPh B → P

namespace IncrKit

variable {A Q W P B : Type} [DecidableEq W] (κ : IncrKit A Q W P B) (zero one : A)

/-- **The kit's rules.** -/
def rule : IncrRule B → Rule A Q W P
  | .up =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .up
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .b1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .up
      dstPh := κ.emb .b2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .b2go =>
    { guard := fun _ _ => True
      srcPh := κ.emb .b2
      dstPh := κ.emb .pc
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .clear =>
    { guard := fun _ g => g κ.t = one ∧ g κ.rg = one
      srcPh := κ.emb .pc
      dstPh := κ.emb .pc
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t zero
      moveRight := False }
  | .set b =>
    { guard := fun _ g => g κ.t = zero ∧ g κ.rg = one ∧ g (κ.bs b) = one ∧
        ∀ b' : B, g (κ.bs b') = one → b' = b
      srcPh := κ.emb .pc
      dstPh := κ.emb (.pd b)
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t one
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .pc
      dstPh := κ.emb .pc
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stay b =>
    { guard := fun _ g => g κ.rg = one ∨ g κ.wk ≠ one
      srcPh := κ.emb (.pd b)
      dstPh := κ.emb (.pd b)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **The trip stays inside its own phases**: every rule lands in one the kit
was given. -/
theorem dstPh_emb (ρ : IncrRule B) : ∃ p, (κ.rule zero one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩

/-- **In-shape separation.** The two indexed families separate through their
index: the `set` rules by the one-hot clause of their guards, the `stay` rules
by their source phases. -/
theorem sep (hzo : zero ≠ one) (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : IncrRule B) (f : Q → A) (g : W → A),
      (κ.rule zero one ρ).guard f g → (κ.rule zero one ρ').guard f g →
      (κ.rule zero one ρ).srcPh = (κ.rule zero one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd (hg.1.symm.trans hg'.1) hzo
    | exact absurd (hg'.1.symm.trans hg.1) hzo
    | exact absurd hg.2 hg'.1
    | exact absurd hg'.2 hg.1
    | exact absurd hg.2.1 hg'.1
    | exact absurd hg'.2.1 hg.1
    | exact congrArg IncrRule.set (hg'.2.2.2 _ hg.2.2.1)
    | (have hbb := hemb hph; cases hbb <;> rfl)

/-- **Exit disjointness** at the kit's landing phases. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : IncrRule B) (f : Q → A) (g : W → A) (b : B),
      (κ.rule zero one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule zero one ρ).srcPh = κ.emb (.pd b) → False := by
  intro ρ f g b hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact hg.elim (fun h1 => hrg h1) (fun h2 => h2 hwk)
    | (have hbb := hemb hph; cases hbb)

/-! ### The discharge -/

section Discharge

variable {A R P Q W K B : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

variable [Lax822549.WideMachines.wide.Structure (Univ A R P K dd)]

variable [Finite A] [Finite R] [Finite P] [Finite K]

variable {PR : Prog A R P Q W K dd} {κ : IncrKit A Q W P B}

variable {rEmb : IncrRule B → R}

variable (hrules : ∀ ρ : IncrRule B, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)

variable {I : Type} [Finite I] {ile : I → I → Prop}

variable (F : IxFile (Univ A R P K dd) I ile)

variable (hR : PR.table.Reads) (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R P K dd))) (hix : Lax904597.Machines.IsLinOrd ile)

variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)

variable (hbs : ∀ b : B, κ.bs b ≠ κ.t)

variable {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)

variable {rest : (Univ A R P K dd → Prop) → W → A} {m m' : I → Prop}

variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt Lax822549.WideMachines.WMLe wkAddr (F.cell gbot))

variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))

variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = F.cell gtop))

variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))

variable {blkOf : I → B}

variable (hblk : ∀ (u : I) (b : B),
  rest (F.cell u) (κ.bs b) = bitVal PR.zero PR.one (blkOf u = b))

variable {fc : Q → A} {s : Univ A R P K dd → Prop}

variable (hsle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s (F.cell gtop))

variable {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ w)

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Lax822549.WideMachines.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : IncrRule B} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.zero PR.one ρ).guard f g) :
    (∀ _hmr : (κ.rule PR.zero PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.zero PR.one ρ).srcPh f g
        (κ.rule PR.zero PR.one ρ).dstPh ((κ.rule PR.zero PR.one ρ).dstSt f g)
        ((κ.rule PR.zero PR.one ρ).wr f g)) ∧
    (∀ _hml : ¬(κ.rule PR.zero PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.zero PR.one ρ).srcPh f g
        (κ.rule PR.zero PR.one ρ).dstPh ((κ.rule PR.zero PR.one ρ).dstSt f g)
        ((κ.rule PR.zero PR.one ρ).wr f g)) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], fun hc => hml (by rw [hrules] at hc; exact hc)⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite I] in
include F hlin hix hnewk hbot hwkLt hwkS in
private theorem wkOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : I, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (F.cell x) r) :
    PR.passTracksAt F.cell κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (F.cell gbot) (F.cell x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((F.lt_iff hix gbot x).mpr
        ⟨hbot x, fun hc => hne (hix.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
omit [Finite I] in
include F hnerg hrg in
private theorem rgOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hno : ∀ x : I, r ≠ F.cell x) :
    PR.passTracksAt F.cell κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one

include hrules F hR hlin hix hnerg hnerl hnewk hbs htop hbot hwkLt hrg hrl hwkS hblk hsle hgap in
/-- **The kit increments its track**, and lands at the marker in the phase of
the block that carried: from the scan phase anywhere, up to the file top, the
binary increment down the file, and back. -/
theorem reachesIn (hi : WMIncr ile m m') :
    ∃ u₀ : I, (¬m u₀ ∧ ∀ v, WMLt ile u₀ v → m v) ∧
      (Lax822549.WideMachines.wideData (Univ A R P K dd)).ReachesIn
      (wideRank (F.cell gtop) + 2 + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
        wideRank (F.cell gbot))
        ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
          wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (κ.emb (.pd (blkOf u₀))) fc), Sum.inl wkAddr,
          wideTape (PR.trackTapeAt F.cell κ.t rest m') (PR.syElt PR.blank)⟩ := by
  obtain ⟨u₀, pend, hu₀, hpend, hpass⟩ := Prog.reachesIn_fileIncrBlk F hR hlin hix hi
    (t := κ.t) (rg := κ.rg) hnerg (rest := rest) hrg
    (B := B) (bs := κ.bs) hbs (blkOf := blkOf) hblk
    (pc := κ.emb .pc) (pd := fun b => κ.emb (.pd b)) (fc := fc)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .clear) ⟨h1, h2⟩).2 not_false)
    (fun b _g h1 h2 h3 h4 =>
      (has_of_rule hrules (ρ := .set b) ⟨h1, h2, h3, h4⟩).2 not_false)
    (fun b _g h1 => (has_of_rule hrules (ρ := .stay b) (Or.inl h1)).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk)
        ⟨rgOff F hnerg hrg k r hno, wkOff F hlin hix hnewk hbot hwkLt hwkS k r hbnd⟩).2
        not_false)
    (fun b k r hbnd hno =>
      (has_of_rule hrules (ρ := .stay b)
        (Or.inr (wkOff F hlin hix hnewk hbot hwkLt hwkS k r hbnd))).2 not_false)
    (w := w) hgap (top := gtop) (bot := gbot) htop hbot
  refine ⟨u₀, hu₀, ?_⟩
  refine (Prog.reachesIn_fileRoundTrip F hR hlin hix hnerl hnewk hbot (rest := rest)
    (m := m) (m₂ := m') (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .pc) (pOut := κ.emb (.pd (blkOf u₀)))
    (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracksAt F.cell κ.t rest m (F.cell gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    hpend hpass
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .stay (blkOf u₀)) (Or.inr hwk)).2 not_false)
    hwkLt hsle).mono (by
    have h₁ : wideRank (F.cell gtop) - wideRank s ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
    have h₂ : wideRank pend - wideRank wkAddr ≤ wideRank (F.cell gbot) :=
      le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hpend))
    omega)

end Discharge

end IncrKit

end Draw

end Lax822549Proofs.DescriptiveComplexity


