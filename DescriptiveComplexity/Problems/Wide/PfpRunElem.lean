/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpElem
import DescriptiveComplexity.Problems.Wide.PfpLoop

/-!
# The element loop's run

The run theorem of `DescriptiveComplexity.Pfp.elemRule`, in the kit-discharge
idiom: one hypothesis – the program's rules at an injection of rule names are
the loop's – and the geometry of the working cell, and the machine carries
itself from the loop's entry checkpoint to its exit phase, the control folded
over every tuple of the enumeration.

The shape of the statement follows the loop's shape. The enumeration is
**abstract** – a finite linear order `ι`, in practice the lexicographic order
on control-held tuples – and the control's evolution is a family per index:
`fsOf a j` is the pointer before the `j`-th read of round `a`, tied together
by four equations (the entry initializes round `a₀`, each read stores its bit,
each advance dispatch opens the next round, the last round is recognized by
the exhaustion guard). Every read trip is one
`DescriptiveComplexity.Pfp.ReadKit` discharge; the store, dispatch and
walk-back steps are single `DescriptiveComplexity.Pfp.Prog.step_move` /
`step_moveBack` steps; the loop closes by
`DescriptiveComplexity.Pfp.reachesIn_of_ordLoop_card`.

The run is proved **with its cost** (`elem_reachesIn`): given a width `c` for
one read trip, a round costs `2 + (c + 2) · nr` – the dispatch, the walk back,
and per read the trip, the store and the walk back – and the whole loop that
once per element of the enumeration, plus the round that opens it and the step
that leaves. `elem_run` is the same run with the budget forgotten, at the width
every trip has anyway: twice the number of addresses. A space-bounded caller
reads that one; a clocked program compares the count with its clock.

Every track the loop touches – the read tracks and a reference track `t₀` the
tape is presented along – is **backed**: its digits are carried by the
background at its own slot, which is what
`DescriptiveComplexity.Pfp.PfpData.back` provides and what lets consecutive
trips walking different tracks share one tape term
(`DescriptiveComplexity.Pfp.trackTape_of_back`).

**What indexes the file is a parameter** (`DescriptiveComplexity.IxFile`): a
track is a set of registers and the cells the reads stop at are registers, so
nothing here asks the file to have one register per element of the universe.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

section Backed

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [Language.wide.Structure (Univ A R P K dd)]
variable {PR : Prog A R P Q W K dd}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R P K dd) I ile)

/-- **A backed track presents the naked background**: a walked track whose
digits the background already carries at its own slot adds nothing to the
tape. This is what lets one leg's conclusion be the next leg's hypothesis
when the two walk different tracks. -/
theorem trackTape_of_back {t : W} {rest : (Univ A R P K dd → Prop) → W → A}
    {m : I → Prop}
    (hm : ∀ r, rest r t = bitVal PR.zero PR.one (bitAtOf RF.cell m r)) :
    PR.trackTapeAt RF.cell t rest m = fun r => PR.syElt (rest r) := by
  refine funext fun r => ?_
  change PR.syElt (fun s => if s = t then bitVal PR.zero PR.one (bitAtOf RF.cell m r)
    else rest r s) = PR.syElt (rest r)
  refine congrArg _ (funext fun s => ?_)
  by_cases hs : s = t
  · subst hs
    rw [if_pos rfl, hm]
  · rw [if_neg hs]

/-- A backed track's pass presentation is the background itself. -/
theorem passTracks_of_back {t : W} {rest : (Univ A R P K dd → Prop) → W → A}
    {m : I → Prop}
    (hm : ∀ r, rest r t = bitVal PR.zero PR.one (bitAtOf RF.cell m r))
    (r : Univ A R P K dd → Prop) :
    PR.passTracksAt RF.cell t rest m r = rest r := by
  refine funext fun s => ?_
  change (if s = t then bitVal PR.zero PR.one (bitAtOf RF.cell m r) else rest r s) =
    rest r s
  by_cases hs : s = t
  · subst hs
    rw [if_pos rfl, hm]
  · rw [if_neg hs]

end Backed

section ElemRun

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {nr : ℕ}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R P K dd) I ile)
variable {wk rg : W} {emb : ElemPh nr → P}
variable {rdTrack : Fin nr → W}
variable {MatchOf : Fin nr → (Q → A) → (W → A) → Prop}
variable {setFlag : Fin nr → Bool → (Q → A) → (W → A) → (Q → A)}
variable {initEl advEl exitSt : (Q → A) → (W → A) → (Q → A)}
variable {IsMaxEl : (Q → A) → Prop}
variable {exitPh : P}
variable {rEmb : ∀ i : ElemSite nr, ElemSh nr i → R}
variable (hrules : ∀ (i : ElemSite nr) (ρ : ElemSh nr i),
  PR.rules (rEmb i ρ) = elemRule PR.one wk rg emb rdTrack MatchOf setFlag
    initEl advEl exitSt IsMaxEl exitPh i ρ)

/-- The phase before the `k`-th read of a round – the fold checkpoint once
the reads are exhausted. `DescriptiveComplexity.Pfp.elemFirstRd` is this at
`0`, `DescriptiveComplexity.Pfp.elemNextRd j` at `j + 1`. -/
def elemPhaseAt (emb : ElemPh nr → P) (k : ℕ) : P :=
  if h : k < nr then emb (.rdP ⟨k, h⟩ .start) else emb .e1

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [LinearOrder K] [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A rule of the loop with a true guard is a `HasRight` witness, its
attributes handed over as equations. -/
private theorem hasRight_of_rule {i : ElemSite nr} {ρ : ElemSh nr i}
    {f f' : Q → A} {g g' : W → A} {p p' : P}
    (hg : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).guard f g)
    (hp : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).srcPh = p)
    (hp' : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).dstPh = p')
    (hf' : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).dstSt f g = f')
    (hg' : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).wr f g = g')
    (hmr : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).moveRight) :
    PR.HasRight p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'], by rw [hrules]; exact hmr⟩

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [LinearOrder K] [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A rule of the loop with a true guard is a `HasLeft` witness. -/
private theorem hasLeft_of_rule {i : ElemSite nr} {ρ : ElemSh nr i}
    {f f' : Q → A} {g g' : W → A} {p p' : P}
    (hg : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).guard f g)
    (hp : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).srcPh = p)
    (hp' : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).dstPh = p')
    (hf' : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).dstSt f g = f')
    (hg' : (elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).wr f g = g')
    (hml : ¬(elemRule PR.one wk rg emb rdTrack MatchOf setFlag initEl advEl
      exitSt IsMaxEl exitPh i ρ).moveRight) :
    PR.HasLeft p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'],
    fun hc => hml (by rw [hrules] at hc; exact hc)⟩

variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hix : IsLinOrd ile)
variable {gbot : I} (hbot : ∀ y, ile gbot y)
variable {v v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (RF.cell gbot))
variable (hvi : WMIncr WMLe v v')
variable {rest : (Univ A R P K dd → Prop) → W → A}
variable (hwkS : ∀ r, rest r wk = bitVal PR.zero PR.one (r = v))
variable (hrg : ∀ r, rest r rg =
  bitVal PR.zero PR.one (∃ u : I, r = RF.cell u))
variable {m : Fin nr → I → Prop}
variable (hm : ∀ (j : Fin nr) (r : Univ A R P K dd → Prop),
  rest r (rdTrack j) = bitVal PR.zero PR.one (bitAtOf RF.cell (m j) r))
variable (hnewk : ∀ j, wk ≠ rdTrack j) (hnerg : ∀ j, rg ≠ rdTrack j)
variable {t₀ : W} {m₀ : I → Prop}
variable (hm₀ : ∀ r, rest r t₀ = bitVal PR.zero PR.one (bitAtOf RF.cell m₀ r))
variable (hwkt₀ : wk ≠ t₀) (hrgt₀ : rg ≠ t₀)

omit hrules [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
include hlin hix hbot hv in
/-- The working cell is nobody's register. -/
theorem not_reg_of_lt_bot : ∀ u : I, v ≠ RF.cell u := by
  intro u hvu
  rw [hvu] at hv
  exact ((RF.lt_iff hix u gbot).mp hv).2 (hbot u)

section Reads

variable (fs : Fin (nr + 1) → Q → A) (x : Fin nr → I)
variable (hname : ∀ j : Fin nr, MatchOf j (fs j.castSucc)
  (PR.passTracksAt RF.cell (rdTrack j) rest (m j) (RF.cell (x j))))
variable (huniq : ∀ (j : Fin nr) (r : Univ A R P K dd → Prop),
  MatchOf j (fs j.castSucc) (PR.passTracksAt RF.cell (rdTrack j) rest (m j) r) →
    r = RF.cell (x j))
variable (hfsT : ∀ j : Fin nr, m j (x j) →
  fs j.succ = setFlag j true (fs j.castSucc) (rest v))
variable (hfsF : ∀ j : Fin nr, ¬m j (x j) →
  fs j.succ = setFlag j false (fs j.castSucc) (rest v))
-- The width of one read trip: a clocked caller supplies a bound, a
-- space-bounded one the maximum over the finitely many reads.
variable (c : ℕ) (hcost : ∀ j : Fin nr,
  2 * (wideRank (RF.cell (x j)) - wideRank v) + 2 ≤ c)

include hrules RF hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg hm₀
  hname huniq hfsT hfsF hcost in
/-- **One round of reads**: from the phase before the `k`-th read to the fold
checkpoint, each read trip storing its bit into the control – and each costing
the trip, the store and the walk back. -/
private theorem elem_reads : ∀ (k : ℕ) (hk : k ≤ nr),
    (wideData (Univ A R P K dd)).ReachesIn ((c + 2) * (nr - k))
      ⟨Sum.inr (PR.stElt (elemPhaseAt emb k) (fs ⟨k, Nat.lt_succ_of_le hk⟩)),
        Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .e1) (fs (Fin.last nr))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot RF hlin hix hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  intro k hk
  induction hd : nr - k generalizing k with
  | zero =>
    have hkn : k = nr := by omega
    subst hkn
    have hph : elemPhaseAt emb k = emb .e1 := dif_neg (lt_irrefl k)
    have hfk : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (k + 1)) = Fin.last k :=
      Fin.ext rfl
    rw [hph, hfk, Nat.mul_zero]
    exact TMData.reachesIn_refl
  | succ n ih =>
    have hkl : k < nr := by omega
    set j : Fin nr := ⟨k, hkl⟩ with hj
    have hph : elemPhaseAt emb k = emb (.rdP j .start) := dif_pos hkl
    have hcast : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (nr + 1)) = j.castSucc :=
      Fin.ext rfl
    -- the read kit at read `j`
    have hrulesK : ∀ ρ : ReadRule,
        PR.rules (rEmb (.rd j) (Sum.inl ρ)) =
          (ReadKit.mk (rdTrack j) wk (MatchOf j)
            (fun rp => emb (.rdP j rp))).rule PR.one ρ :=
      fun ρ => hrules (.rd j) (Sum.inl ρ)
    -- the shared tape, in the read track's presentation and the reference's
    have hTj : PR.trackTapeAt RF.cell (rdTrack j) rest (m j) =
        PR.trackTapeAt RF.cell t₀ rest m₀ :=
      (trackTape_of_back RF (hm j)).trans (trackTape_of_back RF hm₀).symm
    -- the symbol under the head at the marker, in the read track's presentation
    have hsymv : PR.passTracksAt RF.cell (rdTrack j) rest (m j) v = rest v :=
      passTracks_of_back RF (hm j) v
    -- the store step: at the marker, rightwards, folding the bit
    have hstore : ∀ b : Bool,
        (fs j.succ = setFlag j b (fs j.castSucc) (rest v)) →
        (wideData (Univ A R P K dd)).Step
          ⟨Sum.inr (PR.stElt (emb (.rdP j (if b then .ry else .rn)))
              (fs j.castSucc)), Sum.inl v,
            wideTape (PR.trackTapeAt RF.cell (rdTrack j) rest (m j))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (elemNextRd emb j) (fs j.succ)), Sum.inl v',
            wideTape (PR.trackTapeAt RF.cell (rdTrack j) rest (m j))
              (PR.syElt PR.blank)⟩ := by
      intro b hb
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      refine hasRight_of_rule hrules (i := .rd j) (ρ := Sum.inr b) ?_ rfl rfl
        ?_ rfl trivial
      · constructor
        · rw [Prog.passTracks_of_ne (hnewk j), hwkS]
          exact bitVal_pos rfl
        · rw [Prog.passTracks_of_ne (hnerg j), hrg,
            bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
          exact PR.zero_ne_one
      · change setFlag j b (fs j.castSucc)
          (PR.passTracksAt RF.cell (rdTrack j) rest (m j) v) = fs j.succ
        rw [hsymv, hb]
    -- the walk back to the marker, in the next phase
    have hback :
        (wideData (Univ A R P K dd)).Step
          ⟨Sum.inr (PR.stElt (elemNextRd emb j) (fs j.succ)), Sum.inl v',
            wideTape (PR.trackTapeAt RF.cell (rdTrack j) rest (m j))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (elemNextRd emb j) (fs j.succ)), Sum.inl v,
            wideTape (PR.trackTapeAt RF.cell (rdTrack j) rest (m j))
              (PR.syElt PR.blank)⟩ := by
      have hwkv' : PR.passTracksAt RF.cell (rdTrack j) rest (m j) v' wk ≠ PR.one := by
        rw [Prog.passTracks_of_ne (hnewk j), hwkS,
          bitVal_neg (Ne.symm hvv')]
        exact PR.zero_ne_one
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      by_cases hlt : (j : ℕ) + 1 < nr
      · have hnx : elemNextRd emb j = emb (.rdP ⟨(j : ℕ) + 1, hlt⟩ .start) :=
          dif_pos hlt
        rw [hnx]
        exact hasLeft_of_rule hrules
          (i := .rd ⟨(j : ℕ) + 1, hlt⟩) (ρ := Sum.inl .stayS)
          hwkv' rfl rfl rfl rfl not_false
      · have hnx : elemNextRd emb j = emb .e1 := dif_neg hlt
        rw [hnx]
        exact hasLeft_of_rule hrules (i := .e1) (ρ := .stay)
          hwkv' rfl rfl rfl rfl not_false
    -- the read trip, by the kit, then store, walk back, and the tail
    rw [hph, hcast, show wideTape (PR.trackTapeAt RF.cell t₀ rest m₀)
      (PR.syElt PR.blank) = wideTape (PR.trackTapeAt RF.cell (rdTrack j) rest (m j))
      (PR.syElt PR.blank) from congrArg (wideTape · (PR.syElt PR.blank))
        hTj.symm]
    have htail :
        (wideData (Univ A R P K dd)).ReachesIn ((c + 2) * n)
          ⟨Sum.inr (PR.stElt (elemNextRd emb j) (fs j.succ)), Sum.inl v,
            wideTape (PR.trackTapeAt RF.cell (rdTrack j) rest (m j))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (emb .e1) (fs (Fin.last nr))), Sum.inl v,
            wideTape (PR.trackTapeAt RF.cell (rdTrack j) rest (m j))
              (PR.syElt PR.blank)⟩ := by
      have hnx : elemNextRd emb j = elemPhaseAt emb (k + 1) := rfl
      have hsucc : j.succ = ⟨k + 1, Nat.lt_succ_of_le (by omega)⟩ :=
        Fin.ext rfl
      rw [hnx, hsucc, show wideTape (PR.trackTapeAt RF.cell (rdTrack j) rest (m j))
        (PR.syElt PR.blank) = wideTape (PR.trackTapeAt RF.cell t₀ rest m₀)
        (PR.syElt PR.blank) from congrArg (wideTape · (PR.syElt PR.blank)) hTj]
      exact ih (k + 1) (by omega) (by omega)
    have hbudget : c + 1 + 1 + (c + 2) * n ≤ (c + 2) * (n + 1) := by
      rw [Nat.mul_succ]
      omega
    by_cases hbit : m j (x j)
    · refine TMData.ReachesIn.mono hbudget ?_
      refine ((((ReadKit.reachesIn_pos (F := RF) hrulesK hR hlin hix (hnewk j)
        hbot hv hwkS (hname j) (huniq j) hbit).mono (hcost j)).tail
        (hstore true (hfsT j hbit))).tail hback).trans htail
    · refine TMData.ReachesIn.mono hbudget ?_
      refine ((((ReadKit.reachesIn_neg (F := RF) hrulesK hR hlin hix (hnewk j)
        hbot hv hwkS (hname j) (huniq j) hbit).mono (hcost j)).tail
        (hstore false (hfsF j hbit))).tail hback).trans htail

end Reads

section Loop

variable {ι : Type} [LinearOrder ι] [Finite ι] {a₀ aT : ι}
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)
variable (F : ι → Q → A) (fsOf : ι → Fin (nr + 1) → Q → A)
variable (hlastF : ∀ a, fsOf a (Fin.last nr) = F a)
variable (x : ι → Fin nr → I)
variable (hname : ∀ (a : ι) (j : Fin nr), MatchOf j (fsOf a j.castSucc)
  (PR.passTracksAt RF.cell (rdTrack j) rest (m j) (RF.cell (x a j))))
variable (huniq : ∀ (a : ι) (j : Fin nr) (r : Univ A R P K dd → Prop),
  MatchOf j (fsOf a j.castSucc) (PR.passTracksAt RF.cell (rdTrack j) rest (m j) r) →
    r = RF.cell (x a j))
variable (hfsT : ∀ (a : ι) (j : Fin nr), m j (x a j) →
  fsOf a j.succ = setFlag j true (fsOf a j.castSucc) (rest v))
variable (hfsF : ∀ (a : ι) (j : Fin nr), ¬m j (x a j) →
  fsOf a j.succ = setFlag j false (fsOf a j.castSucc) (rest v))
variable (hadv : ∀ a a' : ι, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  advEl (F a) (rest v) = fsOf a' 0)
variable (hmaxT : IsMaxEl (F aT))
variable (hmaxF : ∀ a, a < aT → ¬IsMaxEl (F a))
-- The width of one read trip, as in the reads above.
variable (c : ℕ) (hcost : ∀ (a : ι) (j : Fin nr),
  2 * (wideRank (RF.cell (x a j)) - wideRank v) + 2 ≤ c)

omit hrgt₀ [LinearOrder ι] [Finite ι] in
include hrules RF hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg hm₀ hwkt₀
  hlastF hname huniq hfsT hfsF hcost in
/-- **A round is opened from the marker**: the step off it into the first
read, the walk back, and the reads – from any phase and pointer whose
dispatch enters the round, at the dispatch, the walk back and the reads. -/
private theorem elem_round {p : P} {f : Q → A} {a : ι}
    (hstep : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (elemFirstRd emb) (fsOf a 0)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩) :
    (wideData (Univ A R P K dd)).ReachesIn (2 + (c + 2) * nr)
      ⟨Sum.inr (PR.stElt p f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .e1) (F a)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  -- the walk back into the first read's phase (or the fold checkpoint)
  have hback :
      (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (elemFirstRd emb) (fsOf a 0)), Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (elemFirstRd emb) (fsOf a 0)), Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
    have hwkv' : PR.passTracksAt RF.cell t₀ rest m₀ v' wk ≠ PR.one := by
      rw [Prog.passTracks_of_ne hwkt₀, hwkS, bitVal_neg (Ne.symm hvv')]
      exact PR.zero_ne_one
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    by_cases hlt : 0 < nr
    · have hfr : elemFirstRd emb = emb (.rdP ⟨0, hlt⟩ .start) := dif_pos hlt
      rw [hfr]
      exact hasLeft_of_rule hrules (i := .rd ⟨0, hlt⟩) (ρ := Sum.inl .stayS)
        hwkv' rfl rfl rfl rfl not_false
    · have hfr : elemFirstRd emb = emb .e1 := dif_neg hlt
      rw [hfr]
      exact hasLeft_of_rule hrules (i := .e1) (ρ := .stay)
        hwkv' rfl rfl rfl rfl not_false
  have hreads := elem_reads RF hrules hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg
    hm₀ (fsOf a) (x a) (hname a) (huniq a) (hfsT a) (hfsF a) c (hcost a) 0
    (Nat.zero_le nr)
  have hf0 : (⟨0, Nat.lt_succ_of_le (Nat.zero_le nr)⟩ : Fin (nr + 1)) = 0 :=
    Fin.ext rfl
  rw [hf0] at hreads
  have hfirst : elemPhaseAt emb 0 = elemFirstRd emb := rfl
  rw [hfirst] at hreads
  rw [hlastF a, Nat.sub_zero] at hreads
  exact TMData.ReachesIn.mono (by omega)
    (((TMData.reachesIn_of_step hstep).tail hback).trans hreads)

include hrules RF hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg hm₀ hwkt₀ hrgt₀
  hbotI htopI hlastF hname huniq hfsT hfsF hadv hmaxT hmaxF hcost in
/-- **The element loop's run, on a clock**: from the entry checkpoint at the
marker to the exit phase one cell to its right, the control folded over the
whole enumeration – entered with `initEl`, each round's reads stored by
`setFlag`, each advance by `advEl`, the verdict handed to `exitSt` at the top
index – and the cost is one round's width once per element of the enumeration,
plus the round that opens it and the step that leaves. -/
theorem elem_reachesIn {f₀ : Q → A}
    (hinit : initEl f₀ (rest v) = fsOf a₀ 0) :
    (wideData (Univ A R P K dd)).ReachesIn
      ((2 + (c + 2) * nr) * (Nat.card ι + 1) + 1)
      ⟨Sum.inr (PR.stElt (emb .e0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (exitSt (F aT) (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot RF hlin hix hbot hv
  have hsymv : PR.passTracksAt RF.cell t₀ rest m₀ v = rest v :=
    passTracks_of_back RF hm₀ v
  -- the two marker-side guard facts every dispatch reads
  have hgwk : PR.passTracksAt RF.cell t₀ rest m₀ v wk = PR.one := by
    rw [Prog.passTracks_of_ne hwkt₀, hwkS]
    exact bitVal_pos rfl
  have hgrg : PR.passTracksAt RF.cell t₀ rest m₀ v rg ≠ PR.one := by
    rw [Prog.passTracks_of_ne hrgt₀, hrg,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact PR.zero_ne_one
  -- the entry dispatch
  have hentry : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb .e0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (elemFirstRd emb) (fsOf a₀ 0)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule hrules (i := .e0) (ρ := .dspA)
      ⟨hgwk, hgrg⟩ rfl rfl ?_ rfl trivial
    change initEl f₀ (PR.passTracksAt RF.cell t₀ rest m₀ v) = fsOf a₀ 0
    rw [hsymv]
    exact hinit
  -- the loop over the enumeration
  have hloop : (wideData (Univ A R P K dd)).ReachesIn
      ((2 + (c + 2) * nr) * Nat.card ι)
      ⟨Sum.inr (PR.stElt (emb .e1) (F a₀)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .e1) (F aT)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
    refine reachesIn_of_ordLoop_card (conf := fun a =>
      (⟨Sum.inr (PR.stElt (emb .e1) (F a)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ :
          Config (WPoint (Univ A R P K dd)))) ?_ hbotI aT
    intro a a' hlt hnb
    have hmax : ¬IsMaxEl (F a) := hmaxF a (lt_of_lt_of_le hlt (htopI a'))
    refine elem_round RF hrules hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg hm₀
      hwkt₀ F fsOf hlastF x hname huniq hfsT hfsF c hcost ?_
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule hrules (i := .e1) (ρ := .dspA)
      ⟨⟨hgwk, hgrg⟩, hmax⟩ rfl rfl ?_ rfl trivial
    change advEl (F a) (PR.passTracksAt RF.cell t₀ rest m₀ v) = fsOf a' 0
    rw [hsymv]
    exact hadv a a' hlt hnb
  -- the exit dispatch
  have hexit : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb .e1) (F aT)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (exitSt (F aT) (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule hrules (i := .e1) (ρ := .dspB)
      ⟨⟨hgwk, hgrg⟩, hmaxT⟩ rfl rfl ?_ rfl trivial
    change exitSt (F aT) (PR.passTracksAt RF.cell t₀ rest m₀ v) =
      exitSt (F aT) (rest v)
    rw [hsymv]
  have hopen := elem_round RF hrules hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg
    hm₀ hwkt₀ F fsOf hlastF x hname huniq hfsT hfsF c hcost (a := a₀) hentry
  refine TMData.ReachesIn.mono ?_ ((hopen.trans hloop).tail hexit)
  rw [Nat.mul_succ]
  omega

include hrules RF hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg hm₀ hwkt₀ hrgt₀
  hbotI htopI hlastF hname huniq hfsT hfsF hadv hmaxT hmaxF in
/-- **The element loop's run**, the budget forgotten: what a space-bounded
caller reads. The width of a trip is then the largest of the finitely many the
loop takes. -/
theorem elem_run {f₀ : Q → A}
    (hinit : initEl f₀ (rest v) = fsOf a₀ 0) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb .e0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (exitSt (F aT) (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  exact (elem_reachesIn RF hrules hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg
    hm₀ hwkt₀ hrgt₀ hbotI htopI F fsOf hlastF x hname huniq hfsT hfsF hadv hmaxT
    hmaxF (2 * Nat.card {p : WPoint (Univ A R P K dd) //
        (wideData (Univ A R P K dd)).Posn p} + 2)
    (fun a j => by
      have := wideRank_lt_card (A := Univ A R P K dd) (RF.cell (x a j))
      omega) hinit).reflTransGen

end Loop

end ElemRun

end Pfp

end DescriptiveComplexity
