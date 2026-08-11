/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTrip
import DescriptiveComplexity.Problems.Wide.PfpKit

/-!
# Kits for the round trips: the file test

The kit wrapping the file-test round trip, by the template of
`DescriptiveComplexity.Problems.Wide.PfpKit`: a phase inductive, a rule
inductive with concrete guards, the rules function at a phase embedding, an
in-shape separation lemma, and a discharge – any program whose rule set
contains the kit's rules satisfies the composite's run theorem
(`DescriptiveComplexity.Pfp.TestKit.reaches_pos`/`_neg`: scan up to the file
top, bounce, one question per register on the way down, verdict in the phase,
return to the marker).

The verdict phases double as return phases, which is where the cell-coupled
forms of the layer earn their keep: the walking rule of the passing phase is
guarded `rg ≠ one ∧ wk ≠ one`, disjoint from the register rules, and the
coupled hypotheses of `DescriptiveComplexity.Pfp.Prog.reaches_roundTrip` are
exactly what shows it fires wherever the composite needs it. The failing
phase hosts no register rule, so its single rule takes the disjunction
`rg = one ∨ wk ≠ one` and serves hold, walk and return at once.

Rules are owned by their source phase: how a program *enters* the kit (at the
scan phase, off the marker) and how it *leaves* the two verdict phases (at
the marker, guarded `wk = one ∧ rg ≠ one`, disjoint from every rule here) is
the caller's business.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The file test's shapes -/

/-- **The phases of a test trip**: the up-scan, the bounce, and the two
verdict phases – the passing one doubling as the descent phase of the pass. -/
inductive TestPh : Type
  /-- Scanning up to the file top. -/
  | up : TestPh
  /-- Bounced off the top, about to re-enter rightwards. -/
  | b2 : TestPh
  /-- Every register so far passed (also: returning with verdict *yes*). -/
  | ty : TestPh
  /-- Some register failed (also: returning with verdict *no*). -/
  | tn : TestPh
  deriving DecidableEq

instance : Finite TestPh :=
  Finite.of_injective
    (fun p => match p with
      | .up => (0 : Fin 4) | .b2 => 1 | .ty => 2 | .tn => 3)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule families of a test trip**, one constructor each. -/
inductive TestRule : Type
  /-- Scan right while the file-top mark is clear. -/
  | up : TestRule
  /-- At the file top: step left into the bounce phase. -/
  | b1 : TestRule
  /-- Bounce: step back right into the pass. -/
  | b2go : TestRule
  /-- At a register that passes the question: carry on down. -/
  | pass : TestRule
  /-- At a register that fails it: switch to the failing phase. -/
  | fail : TestRule
  /-- Walk left over unmarked cells, and return, in the passing phase. -/
  | walkY : TestRule
  /-- Hold at registers, walk and return, in the failing phase. -/
  | stayN : TestRule
  deriving DecidableEq

instance : Finite TestRule :=
  Finite.of_injective
    (fun p => match p with
      | .up => (0 : Fin 7) | .b1 => 1 | .b2go => 2 | .pass => 3 | .fail => 4
      | .walkY => 5 | .stayN => 6)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **A file-test kit**: the walked track, the three service slots, the
per-register question as a predicate of the tracks, and where its phases sit
in the program. -/
structure TestKit (A Q W P : Type) where
  /-- The walked track being questioned. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The per-register question, decided by the tracks. -/
  TestG : (W → A) → Prop
  /-- The kit's phases in the program. -/
  emb : TestPh → P

namespace TestKit

variable {A Q W P : Type} (κ : TestKit A Q W P) (one : A)

/-- **The kit's rules.** -/
def rule : TestRule → Rule A Q W P
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
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .pass =>
    { guard := fun _ g => κ.TestG g ∧ g κ.rg = one
      srcPh := κ.emb .ty
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .fail =>
    { guard := fun _ g => ¬κ.TestG g ∧ g κ.rg = one
      srcPh := κ.emb .ty
      dstPh := κ.emb .tn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .walkY =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .ty
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stayN =>
    { guard := fun _ g => g κ.rg = one ∨ g κ.wk ≠ one
      srcPh := κ.emb .tn
      dstPh := κ.emb .tn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **In-shape separation**: two of the kit's rules firing in the same phase
on the same data are the same rule. -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : TestRule) (f : Q → A) (g : W → A),
      (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
      (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg.1 hg'.1
    | exact absurd hg'.1 hg.1
    | exact absurd hg.2 hg'.1
    | exact absurd hg'.2 hg.1

/-- **Exit disjointness**: at the kit's two verdict phases – where a caller's
exit rule, guarded `wk = one ∧ rg ≠ one`, lives – no kit rule fires on a
symbol satisfying that guard. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : TestRule) (f : Q → A) (g : W → A), (κ.rule one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      ((κ.rule one ρ).srcPh = κ.emb .ty ∨ (κ.rule one ρ).srcPh = κ.emb .tn) →
      False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> rcases hph with hph | hph <;> first
    | exact absurd hg.2 hrg
    | exact absurd hwk hg.2
    | exact hg.elim (fun h1 => hrg h1) (fun h2 => h2 hwk)
    | (have hbb := hemb hph; cases hbb)

/-! ### The discharge -/

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : TestKit A Q W P}
variable {rEmb : TestRule → R}
variable (hrules : ∀ ρ : TestRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)
variable {gtop gbot : Univ A R P K dd} (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (wmSeg gbot))
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = wmSeg gtop))
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))
variable {Test : Univ A R P K dd → Prop}
variable (hcompat : ∀ u : Univ A R P K dd,
  κ.TestG (PR.passTracks κ.t rest m (wmSeg u)) ↔ Test u)
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness. -/
private theorem has_of_rule {ρ : TestRule} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.one ρ).guard f g)
    (hkeepSt : (κ.rule PR.one ρ).dstSt f g = f)
    (hkeepWr : (κ.rule PR.one ρ).wr f g = g) :
    (∀ _hmr : (κ.rule PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh f g) ∧
    (∀ _hml : ¬(κ.rule PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh f g) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules]; exact hkeepSt, by rw [hrules]; exact hkeepWr,
      by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules]; exact hkeepSt, by rw [hrules]; exact hkeepWr,
      fun hc => hml (by rw [hrules] at hc; exact hc)⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
include hlin hnewk hbot hwkLt hwkS in
/-- The marker slot is clear at or above the register file. -/
private theorem wkOff (k r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) :
    PR.passTracks κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (wmSeg gbot) (wmSeg x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((wmSetLt_wmSeg_iff hlin gbot x).mpr
        ⟨hbot x, fun hc => hne (hlin.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hnerg hrg in
/-- The register mark is clear at unmarked cells. -/
private theorem rgOff (k r : Univ A R P K dd → Prop)
    (hno : ∀ x : Univ A R P K dd, r ≠ wmSeg x) :
    PR.passTracks κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one

include hrules hR hlin hnerg hnewk htop hbot hwkLt hrg hwkS hcompat in
/-- The pass down the file, verdict in the state. -/
private theorem test_part :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (wmSeg gbot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (κ.emb .ty) fc), Sum.inl (wmSeg gtop),
          wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (accStateAfter Test (PR.stElt (κ.emb .ty) fc)
            (PR.stElt (κ.emb .tn) fc) gbot), Sum.inl q,
          wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩ :=
  Prog.reaches_testG (Test := Test) (TestG := κ.TestG)
    hR hlin (m := m) (t := κ.t) (rg := κ.rg) hnerg (rest := rest) hrg hcompat
    (py := κ.emb .ty) (pn := κ.emb .tn) (f := fc)
    (fun _g hT hg1 =>
      (has_of_rule hrules (ρ := .pass) ⟨hT, hg1⟩ rfl rfl).2 not_false)
    (fun _g hT hg1 =>
      (has_of_rule hrules (ρ := .fail) ⟨hT, hg1⟩ rfl rfl).2 not_false)
    (fun _g hg1 =>
      (has_of_rule hrules (ρ := .stayN) (Or.inl hg1) rfl rfl).2 not_false)
    (fun r hbnd hno =>
      (has_of_rule hrules (ρ := .walkY)
        ⟨rgOff hnerg hrg m r hno, wkOff hlin hnewk hbot hwkLt hwkS m r hbnd⟩
        rfl rfl).2 not_false)
    (fun r hbnd _hno =>
      (has_of_rule hrules (ρ := .stayN)
        (Or.inr (wkOff hlin hnewk hbot hwkLt hwkS m r hbnd)) rfl rfl).2 not_false)
    (top := gtop) (bot := gbot) htop hbot

include hrules hR hlin hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hcompat in
/-- **The kit runs a passing file test**: from the scan phase anywhere, up to
the file top, down the file – every register passing – and back to the marker
in the passing phase. -/
theorem reaches_pos (hTest : ∀ u, Test u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .ty) fc), Sum.inl wkAddr,
        wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, htest⟩ := test_part hrules hR hlin hnerg hnewk htop hbot
    hwkLt hrg hwkS hcompat (fc := fc)
  rw [accStateAfter_bot_pos hTest] at htest
  exact Prog.reaches_roundTrip hR hlin hnerl hnewk htop hbot (rest := rest)
    (m := m) (m₂ := m) (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .ty) (pOut := κ.emb .ty) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg rfl rfl).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracks κ.t rest m (wmSeg gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)
      rfl rfl).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial rfl rfl).1 trivial)
    hq htest
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .walkY)
        ⟨rgOff hnerg hrg m r hno, hwk⟩ rfl rfl).2 not_false)
    hwkLt

include hrules hR hlin hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hcompat in
/-- **The kit runs a failing file test**: some register fails, and the trip
ends at the marker in the failing phase. -/
theorem reaches_neg {u : Univ A R P K dd} (hTest : ¬Test u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .tn) fc), Sum.inl wkAddr,
        wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, htest⟩ := test_part hrules hR hlin hnerg hnewk htop hbot
    hwkLt hrg hwkS hcompat (fc := fc)
  rw [accStateAfter_bot_neg hbot hTest] at htest
  exact Prog.reaches_roundTrip hR hlin hnerl hnewk htop hbot (rest := rest)
    (m := m) (m₂ := m) (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .ty) (pOut := κ.emb .tn) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg rfl rfl).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracks κ.t rest m (wmSeg gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)
      rfl rfl).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial rfl rfl).1 trivial)
    hq htest
    (fun r _hno hwk =>
      (has_of_rule hrules (ρ := .stayN) (Or.inr hwk) rfl rfl).2 not_false)
    hwkLt

end Discharge

end TestKit

/-! ### The clear and copy trips

The same itinerary with a writing pass in the middle: one phase runs the
descent and the return alike, its register rule rewriting the walked digit
and its walking rule – guarded `rg ≠ one ∧ wk ≠ one` – serving the gaps of
the file and the way home. -/

/-- **The phases of a write-pass trip**: the up-scan, the bounce, and the one
pass-and-return phase. -/
inductive TrackPh : Type
  /-- Scanning up to the file top. -/
  | up : TrackPh
  /-- Bounced off the top, about to re-enter rightwards. -/
  | b2 : TrackPh
  /-- Running the pass down the file, and returning. -/
  | run : TrackPh
  deriving DecidableEq

instance : Finite TrackPh :=
  Finite.of_injective
    (fun p => match p with | .up => (0 : Fin 3) | .b2 => 1 | .run => 2)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule families of a write-pass trip.** -/
inductive TrackRule : Type
  /-- Scan right while the file-top mark is clear. -/
  | up : TrackRule
  /-- At the file top: step left into the bounce phase. -/
  | b1 : TrackRule
  /-- Bounce: step back right into the pass. -/
  | b2go : TrackRule
  /-- At a register: rewrite the walked digit and carry on down. -/
  | put : TrackRule
  /-- Walk left over unmarked cells, and return. -/
  | walk : TrackRule
  deriving DecidableEq

instance : Finite TrackRule :=
  Finite.of_injective
    (fun p => match p with
      | .up => (0 : Fin 5) | .b1 => 1 | .b2go => 2 | .put => 3 | .walk => 4)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **A track-clearing kit**: the walked track, the three service slots, and
the phases. -/
structure ClearKit (A Q W P : Type) where
  /-- The walked track being cleared. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The kit's phases in the program. -/
  emb : TrackPh → P

namespace ClearKit

variable {A Q W P : Type} [DecidableEq W] (κ : ClearKit A Q W P) (zero one : A)

/-- **The kit's rules.** -/
def rule : TrackRule → Rule A Q W P
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
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .put =>
    { guard := fun _ g => g κ.rg = one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t zero
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : TrackRule) (f : Q → A) (g : W → A),
      (κ.rule zero one ρ).guard f g → (κ.rule zero one ρ').guard f g →
      (κ.rule zero one ρ).srcPh = (κ.rule zero one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg hg'.1
    | exact absurd hg' hg.1

/-- **Exit disjointness** at the kit's pass-and-return phase. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : TrackRule) (f : Q → A) (g : W → A), (κ.rule zero one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule zero one ρ).srcPh = κ.emb .run → False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact absurd hg hrg
    | exact absurd hwk hg.2
    | (have hbb := hemb hph; cases hbb)

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : ClearKit A Q W P}
variable {rEmb : TrackRule → R}
variable (hrules : ∀ ρ : TrackRule, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)
variable {gtop gbot : Univ A R P K dd} (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (wmSeg gbot))
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = wmSeg gtop))
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : TrackRule} {f : Q → A} {g : W → A}
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

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
include hlin hnewk hbot hwkLt hwkS in
private theorem wkOff (k r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) :
    PR.passTracks κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (wmSeg gbot) (wmSeg x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((wmSetLt_wmSeg_iff hlin gbot x).mpr
        ⟨hbot x, fun hc => hne (hlin.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hnerg hrg in
private theorem rgOff (k r : Univ A R P K dd → Prop)
    (hno : ∀ x : Univ A R P K dd, r ≠ wmSeg x) :
    PR.passTracks κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one

include hrules hR hlin hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS in
/-- **The kit clears its track**: from the scan phase anywhere, up to the file
top, one pass writing the clear digit at every register, and back to the
marker. -/
theorem reaches :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTape κ.t rest fun _ => False) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hpass⟩ := Prog.reaches_clearTrack hR hlin (t := κ.t) (rg := κ.rg)
    hnerg (rest := rest) hrg (m := m) (p := κ.emb .run) (f := fc)
    (fun _g hg1 => (has_of_rule hrules (ρ := .put) hg1).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk)
        ⟨rgOff hnerg hrg k r hno, wkOff hlin hnewk hbot hwkLt hwkS k r hbnd⟩).2
        not_false)
    (top := gtop) (bot := gbot) htop hbot
  exact Prog.reaches_roundTrip hR hlin hnerl hnewk htop hbot (rest := rest)
    (m := m) (m₂ := fun _ => False) (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .run) (pOut := κ.emb .run) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracks κ.t rest m (wmSeg gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    hq hpass
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .walk) ⟨rgOff hnerg hrg _ r hno, hwk⟩).2 not_false)
    hwkLt

end Discharge

end ClearKit

/-- **A track-copying kit**: the walked track, the source slot – which must
hold a bit at every register – the three service slots, and the phases. -/
structure CopyKit (A Q W P : Type) where
  /-- The walked track being overwritten. -/
  t : W
  /-- The source slot whose digit is copied. -/
  src : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The kit's phases in the program. -/
  emb : TrackPh → P

namespace CopyKit

variable {A Q W P : Type} [DecidableEq W] (κ : CopyKit A Q W P) (one : A)

/-- **The kit's rules.** -/
def rule : TrackRule → Rule A Q W P
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
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .put =>
    { guard := fun _ g => g κ.rg = one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t (g κ.src)
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : TrackRule) (f : Q → A) (g : W → A),
      (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
      (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg hg'.1
    | exact absurd hg' hg.1

/-- **Exit disjointness** at the kit's pass-and-return phase. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : TrackRule) (f : Q → A) (g : W → A), (κ.rule one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule one ρ).srcPh = κ.emb .run → False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact absurd hg hrg
    | exact absurd hwk hg.2
    | (have hbb := hemb hph; cases hbb)

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : CopyKit A Q W P}
variable {rEmb : TrackRule → R}
variable (hrules : ∀ ρ : TrackRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)
variable (hnesrc : κ.src ≠ κ.t)
variable {gtop gbot : Univ A R P K dd} (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (wmSeg gbot))
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = wmSeg gtop))
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))
variable (hsrcBit : ∀ u : Univ A R P K dd,
  rest (wmSeg u) κ.src = PR.zero ∨ rest (wmSeg u) κ.src = PR.one)
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : TrackRule} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.one ρ).guard f g) :
    (∀ _hmr : (κ.rule PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh ((κ.rule PR.one ρ).dstSt f g)
        ((κ.rule PR.one ρ).wr f g)) ∧
    (∀ _hml : ¬(κ.rule PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh ((κ.rule PR.one ρ).dstSt f g)
        ((κ.rule PR.one ρ).wr f g)) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], fun hc => hml (by rw [hrules] at hc; exact hc)⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
include hlin hnewk hbot hwkLt hwkS in
private theorem wkOff (k r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) :
    PR.passTracks κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (wmSeg gbot) (wmSeg x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((wmSetLt_wmSeg_iff hlin gbot x).mpr
        ⟨hbot x, fun hc => hne (hlin.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hnerg hrg in
private theorem rgOff (k r : Univ A R P K dd → Prop)
    (hno : ∀ x : Univ A R P K dd, r ≠ wmSeg x) :
    PR.passTracks κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one

include hrules hR hlin hnerg hnerl hnewk hnesrc htop hbot hwkLt hrg hrl hwkS hsrcBit in
/-- **The kit copies the source slot into its track**: from the scan phase
anywhere, up to the file top, one pass replacing every register's walked digit
by its source digit, and back to the marker. -/
theorem reaches :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTape κ.t rest fun u => rest (wmSeg u) κ.src = PR.one)
          (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hpass⟩ := Prog.reaches_copyTrack hR hlin (t := κ.t) (rg := κ.rg)
    (src := κ.src) hnerg hnesrc (rest := rest) hrg hsrcBit (m := m)
    (p := κ.emb .run) (f := fc)
    (fun _g hg1 => (has_of_rule hrules (ρ := .put) hg1).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk)
        ⟨rgOff hnerg hrg k r hno, wkOff hlin hnewk hbot hwkLt hwkS k r hbnd⟩).2
        not_false)
    (top := gtop) (bot := gbot) htop hbot
  exact Prog.reaches_roundTrip hR hlin hnerl hnewk htop hbot (rest := rest)
    (m := m) (m₂ := fun u => rest (wmSeg u) κ.src = PR.one) (wkAddr := wkAddr)
    hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .run) (pOut := κ.emb .run) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracks κ.t rest m (wmSeg gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    hq hpass
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .walk) ⟨rgOff hnerg hrg _ r hno, hwk⟩).2 not_false)
    hwkLt

end Discharge

end CopyKit

/-- **A track-mapping kit**: the walked track is rewritten by a bit the
*other* tracks at each register decide – the pattern writes of the program,
a target register loaded from the marks. The function ignoring the walked
slot is the discharge's frame hypothesis. -/
structure MapKit (A Q W P : Type) where
  /-- The walked track being overwritten. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The written bit, computed from the tracks. -/
  Fb : (W → A) → Prop
  /-- The kit's phases in the program. -/
  emb : TrackPh → P

namespace MapKit

variable {A Q W P : Type} [DecidableEq W] (κ : MapKit A Q W P) (zero one : A)

/-- **The kit's rules.** -/
noncomputable def rule : TrackRule → Rule A Q W P
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
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .put =>
    { guard := fun _ g => g κ.rg = one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t (bitVal zero one (κ.Fb g))
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : TrackRule) (f : Q → A) (g : W → A),
      (κ.rule zero one ρ).guard f g → (κ.rule zero one ρ').guard f g →
      (κ.rule zero one ρ).srcPh = (κ.rule zero one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg hg'.1
    | exact absurd hg' hg.1

/-- **Exit disjointness** at the kit's pass-and-return phase. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : TrackRule) (f : Q → A) (g : W → A), (κ.rule zero one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule zero one ρ).srcPh = κ.emb .run → False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact absurd hg hrg
    | exact absurd hwk hg.2
    | (have hbb := hemb hph; cases hbb)

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : MapKit A Q W P}
variable {rEmb : TrackRule → R}
variable (hrules : ∀ ρ : TrackRule, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)
variable {gtop gbot : Univ A R P K dd} (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (wmSeg gbot))
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = wmSeg gtop))
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))
variable (hFb : ∀ g g' : W → A, (∀ s : W, s ≠ κ.t → g s = g' s) → (κ.Fb g ↔ κ.Fb g'))
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : TrackRule} {f : Q → A} {g : W → A}
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

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
include hlin hnewk hbot hwkLt hwkS in
private theorem wkOff (k r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) :
    PR.passTracks κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (wmSeg gbot) (wmSeg x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((wmSetLt_wmSeg_iff hlin gbot x).mpr
        ⟨hbot x, fun hc => hne (hlin.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hnerg hrg in
private theorem rgOff (k r : Univ A R P K dd → Prop)
    (hno : ∀ x : Univ A R P K dd, r ≠ wmSeg x) :
    PR.passTracks κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one

include hrules hR hlin hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hFb in
/-- **The kit rewrites its track by the function**: from the scan phase
anywhere, up to the file top, one pass writing the computed bit at every
register, and back to the marker. -/
theorem reaches :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTape κ.t rest
          fun u => κ.Fb (PR.passTracks κ.t rest m (wmSeg u))) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hpass⟩ := Prog.reaches_mapTrack hR hlin (t := κ.t) (rg := κ.rg)
    hnerg (rest := rest) hrg (Fb := κ.Fb) hFb (m := m) (p := κ.emb .run) (f := fc)
    (fun _g hg1 => (has_of_rule hrules (ρ := .put) hg1).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk)
        ⟨rgOff hnerg hrg k r hno, wkOff hlin hnewk hbot hwkLt hwkS k r hbnd⟩).2
        not_false)
    (top := gtop) (bot := gbot) htop hbot
  exact Prog.reaches_roundTrip hR hlin hnerl hnewk htop hbot (rest := rest)
    (m := m) (m₂ := fun u => κ.Fb (PR.passTracks κ.t rest m (wmSeg u)))
    (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .run) (pOut := κ.emb .run) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracks κ.t rest m (wmSeg gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    hq hpass
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .walk) ⟨rgOff hnerg hrg _ r hno, hwk⟩).2 not_false)
    hwkLt

end Discharge

end MapKit

end Pfp

end DescriptiveComplexity
