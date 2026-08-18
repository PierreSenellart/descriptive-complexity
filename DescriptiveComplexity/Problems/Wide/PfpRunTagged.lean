/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTagged
import DescriptiveComplexity.Problems.Wide.PfpRunElem

/-!
# The tag-branched machinery's run

The run theorem of `DescriptiveComplexity.Pfp.tagRule`: the witness reads
store the argument points' tags one-hot into the control, the branch
checkpoint dispatches on the decoded tuple – its guard `TagsAre` holding at
exactly one tag tuple – and that tuple's element loop runs to the shared exit
phase by `DescriptiveComplexity.Pfp.elem_reachesIn`.

The run comes **with its cost** (`tag_reachesIn`): the chain's reads at the
trip width the caller fixes, the branch's dispatch and walk back, and the
loop's own count. `tag_run` is it with the budget forgotten, at the width every
trip has anyway.

As in the element loop's run, the machinery is entered *at* its first phase
on the marker (the caller's dispatch steps right and
`DescriptiveComplexity.Pfp.tag_back` walks back down), and it leaves through
the loop's exit dispatch one cell to the marker's right.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

section TagRun

variable {A R P Q W K T : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {m : ℕ} {nrOf : T → ℕ}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R P K dd) I ile)
variable {wk rg : W} {emb : TagPh m T nrOf → P}
variable {rdTrackT : Fin m → W}
variable {MatchT : Fin m → (Q → A) → (W → A) → Prop}
variable {setTagFlag : Fin m → Bool → (Q → A) → (W → A) → (Q → A)}
variable {TagsAre : T → (Q → A) → Prop}
variable {rdTrackE : (τ : T) → Fin (nrOf τ) → W}
variable {MatchE : (τ : T) → Fin (nrOf τ) → (Q → A) → (W → A) → Prop}
variable {setFlagE : (τ : T) → Fin (nrOf τ) → Bool → (Q → A) → (W → A) → (Q → A)}
variable {initEl advEl exitSt : T → (Q → A) → (W → A) → (Q → A)}
variable {IsMaxEl : T → (Q → A) → Prop}
variable {exitPh : P}
variable {rEmb : ∀ i : TagSite m T nrOf, TagSh m T nrOf i → R}
variable (hrules : ∀ (i : TagSite m T nrOf) (ρ : TagSh m T nrOf i),
  PR.rules (rEmb i ρ) = tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag
    TagsAre rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ)

/-- The phase before the `k`-th witness read – the branch checkpoint once
they are exhausted. -/
def tagPhaseAt (emb : TagPh m T nrOf → P) (k : ℕ) : P :=
  if h : k < m then emb (.tagRdP ⟨k, h⟩ .start) else emb .brP

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [LinearOrder K] [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A rule of the machinery with a true guard is a `HasRight` witness. -/
private theorem hasRight_of_rule {i : TagSite m T nrOf} {ρ : TagSh m T nrOf i}
    {f f' : Q → A} {g g' : W → A} {p p' : P}
    (hg : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).guard f g)
    (hp : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).srcPh = p)
    (hp' : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).dstPh = p')
    (hf' : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).dstSt f g
        = f')
    (hg' : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).wr f g
        = g')
    (hmr : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).moveRight) :
    PR.HasRight p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'], by rw [hrules]; exact hmr⟩

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [LinearOrder K] [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A rule of the machinery with a true guard is a `HasLeft` witness. -/
private theorem hasLeft_of_rule {i : TagSite m T nrOf} {ρ : TagSh m T nrOf i}
    {f f' : Q → A} {g g' : W → A} {p p' : P}
    (hg : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).guard f g)
    (hp : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).srcPh = p)
    (hp' : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).dstPh = p')
    (hf' : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).dstSt f g
        = f')
    (hg' : (tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).wr f g
        = g')
    (hml : ¬(tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag TagsAre
      rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).moveRight) :
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
variable {mT : Fin m → I → Prop}
variable (hmT : ∀ (i : Fin m) (r : Univ A R P K dd → Prop),
  rest r (rdTrackT i) = bitVal PR.zero PR.one (bitAtOf RF.cell (mT i) r))
variable (hnewkT : ∀ i, wk ≠ rdTrackT i) (hnergT : ∀ i, rg ≠ rdTrackT i)
variable {t₀ : W} {m₀ : I → Prop}
variable (hm₀ : ∀ r, rest r t₀ = bitVal PR.zero PR.one (bitAtOf RF.cell m₀ r))
variable (hwkt₀ : wk ≠ t₀) (hrgt₀ : rg ≠ t₀)

omit hrules hm₀ in
include hlin hvi hwkS hwkt₀ in
/-- The one leftward step a caller's rightward dispatch into the machinery
owes: at its first phase, the walk back down to the marker. -/
theorem tag_back (hR : PR.table.Reads)
    (hrules : ∀ (i : TagSite m T nrOf) (ρ : TagSh m T nrOf i),
      PR.rules (rEmb i ρ) = tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag
        TagsAre rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ)
    {f : Q → A} :
    (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hwkv' : PR.passTracksAt RF.cell t₀ rest m₀ v' wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hwkt₀, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  by_cases hlt : 0 < m
  · have hfr : tagFirstRd emb = emb (.tagRdP ⟨0, hlt⟩ .start) := dif_pos hlt
    rw [hfr]
    exact hasLeft_of_rule hrules (i := .tagRd ⟨0, hlt⟩) (ρ := Sum.inl .stayS)
      hwkv' rfl rfl rfl rfl not_false
  · have hfr : tagFirstRd emb = emb .brP := dif_neg hlt
    rw [hfr]
    exact hasLeft_of_rule hrules (i := .br) (ρ := .stay)
      hwkv' rfl rfl rfl rfl not_false

section Chain

variable (fsT : Fin (m + 1) → Q → A) (xT : Fin m → I)
variable (hnameT : ∀ i : Fin m, MatchT i (fsT i.castSucc)
  (PR.passTracksAt RF.cell (rdTrackT i) rest (mT i) (RF.cell (xT i))))
variable (huniqT : ∀ (i : Fin m) (r : Univ A R P K dd → Prop),
  MatchT i (fsT i.castSucc) (PR.passTracksAt RF.cell (rdTrackT i) rest (mT i) r) →
    r = RF.cell (xT i))
variable (hfsTT : ∀ i : Fin m, mT i (xT i) →
  fsT i.succ = setTagFlag i true (fsT i.castSucc) (rest v))
variable (hfsTF : ∀ i : Fin m, ¬mT i (xT i) →
  fsT i.succ = setTagFlag i false (fsT i.castSucc) (rest v))

-- The width of one read trip, as in the element loop.
variable (c : ℕ) (hcostT : ∀ i : Fin m,
  2 * (wideRank (RF.cell (xT i)) - wideRank v) + 2 ≤ c)

include RF hrules hR hlin hix hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀
  hnameT huniqT hfsTT hfsTF hcostT in
/-- **The witness chain**: from the phase before the `k`-th witness read to
the branch checkpoint, each read trip storing its one-hot bit – and each
costing the trip, the store and the walk back. -/
private theorem tag_reads : ∀ (k : ℕ) (hk : k ≤ m),
    (wideData (Univ A R P K dd)).ReachesIn ((c + 2) * (m - k))
      ⟨Sum.inr (PR.stElt (tagPhaseAt emb k) (fsT ⟨k, Nat.lt_succ_of_le hk⟩)),
        Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .brP) (fsT (Fin.last m))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot RF hlin hix hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  intro k hk
  induction hd : m - k generalizing k with
  | zero =>
    have hkn : k = m := by omega
    subst hkn
    have hph : tagPhaseAt emb k = emb .brP := dif_neg (lt_irrefl k)
    have hfk : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (k + 1)) = Fin.last k :=
      Fin.ext rfl
    rw [hph, hfk, Nat.mul_zero]
    exact TMData.reachesIn_refl
  | succ n ih =>
    have hkl : k < m := by omega
    set i : Fin m := ⟨k, hkl⟩ with hi
    have hph : tagPhaseAt emb k = emb (.tagRdP i .start) := dif_pos hkl
    have hcast : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (m + 1)) = i.castSucc :=
      Fin.ext rfl
    have hrulesK : ∀ ρ : ReadRule,
        PR.rules (rEmb (.tagRd i) (Sum.inl ρ)) =
          (ReadKit.mk (rdTrackT i) wk (MatchT i)
            (fun rp => emb (.tagRdP i rp))).rule PR.one ρ :=
      fun ρ => hrules (.tagRd i) (Sum.inl ρ)
    have hTi : PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i) =
        PR.trackTapeAt RF.cell t₀ rest m₀ :=
      (trackTape_of_back RF (hmT i)).trans (trackTape_of_back RF hm₀).symm
    have hsymv : PR.passTracksAt RF.cell (rdTrackT i) rest (mT i) v = rest v :=
      passTracks_of_back RF (hmT i) v
    have hstore : ∀ b : Bool,
        (fsT i.succ = setTagFlag i b (fsT i.castSucc) (rest v)) →
        (wideData (Univ A R P K dd)).Step
          ⟨Sum.inr (PR.stElt (emb (.tagRdP i (if b then .ry else .rn)))
              (fsT i.castSucc)), Sum.inl v,
            wideTape (PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (tagNextRd emb i) (fsT i.succ)), Sum.inl v',
            wideTape (PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i))
              (PR.syElt PR.blank)⟩ := by
      intro b hb
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      refine hasRight_of_rule hrules (i := .tagRd i) (ρ := Sum.inr b) ?_ rfl rfl
        ?_ rfl trivial
      · constructor
        · rw [Prog.passTracks_of_ne (hnewkT i), hwkS]
          exact bitVal_pos rfl
        · rw [Prog.passTracks_of_ne (hnergT i), hrg,
            bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
          exact PR.zero_ne_one
      · change setTagFlag i b (fsT i.castSucc)
          (PR.passTracksAt RF.cell (rdTrackT i) rest (mT i) v) = fsT i.succ
        rw [hsymv, hb]
    have hback :
        (wideData (Univ A R P K dd)).Step
          ⟨Sum.inr (PR.stElt (tagNextRd emb i) (fsT i.succ)), Sum.inl v',
            wideTape (PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (tagNextRd emb i) (fsT i.succ)), Sum.inl v,
            wideTape (PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i))
              (PR.syElt PR.blank)⟩ := by
      have hwkv' : PR.passTracksAt RF.cell (rdTrackT i) rest (mT i) v' wk ≠ PR.one := by
        rw [Prog.passTracks_of_ne (hnewkT i), hwkS,
          bitVal_neg (Ne.symm hvv')]
        exact PR.zero_ne_one
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      by_cases hlt : (i : ℕ) + 1 < m
      · have hnx : tagNextRd emb i = emb (.tagRdP ⟨(i : ℕ) + 1, hlt⟩ .start) :=
          dif_pos hlt
        rw [hnx]
        exact hasLeft_of_rule hrules
          (i := .tagRd ⟨(i : ℕ) + 1, hlt⟩) (ρ := Sum.inl .stayS)
          hwkv' rfl rfl rfl rfl not_false
      · have hnx : tagNextRd emb i = emb .brP := dif_neg hlt
        rw [hnx]
        exact hasLeft_of_rule hrules (i := .br) (ρ := .stay)
          hwkv' rfl rfl rfl rfl not_false
    rw [hph, hcast, show wideTape (PR.trackTapeAt RF.cell t₀ rest m₀)
      (PR.syElt PR.blank) = wideTape (PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i))
      (PR.syElt PR.blank) from congrArg (wideTape · (PR.syElt PR.blank))
        hTi.symm]
    have htail :
        (wideData (Univ A R P K dd)).ReachesIn ((c + 2) * n)
          ⟨Sum.inr (PR.stElt (tagNextRd emb i) (fsT i.succ)), Sum.inl v,
            wideTape (PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (emb .brP) (fsT (Fin.last m))), Sum.inl v,
            wideTape (PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i))
              (PR.syElt PR.blank)⟩ := by
      have hnx : tagNextRd emb i = tagPhaseAt emb (k + 1) := rfl
      have hsucc : i.succ = ⟨k + 1, Nat.lt_succ_of_le (by omega)⟩ :=
        Fin.ext rfl
      rw [hnx, hsucc, show wideTape (PR.trackTapeAt RF.cell (rdTrackT i) rest (mT i))
        (PR.syElt PR.blank) = wideTape (PR.trackTapeAt RF.cell t₀ rest m₀)
        (PR.syElt PR.blank) from congrArg (wideTape · (PR.syElt PR.blank)) hTi]
      exact ih (k + 1) (by omega) (by omega)
    have hbudget : c + 1 + 1 + (c + 2) * n ≤ (c + 2) * (n + 1) := by
      rw [Nat.mul_succ]
      omega
    by_cases hbit : mT i (xT i)
    · refine TMData.ReachesIn.mono hbudget ?_
      refine ((((ReadKit.reachesIn_pos (F := RF) hrulesK hR hlin hix (hnewkT i)
        hbot hv hwkS (hnameT i) (huniqT i) hbit).mono (hcostT i)).tail
        (hstore true (hfsTT i hbit))).tail hback).trans htail
    · refine TMData.ReachesIn.mono hbudget ?_
      refine ((((ReadKit.reachesIn_neg (F := RF) hrulesK hR hlin hix (hnewkT i)
        hbot hv hwkS (hnameT i) (huniqT i) hbit).mono (hcostT i)).tail
        (hstore false (hfsTF i hbit))).tail hback).trans htail

variable {τ : T} (hτ : TagsAre τ (fsT (Fin.last m)))
variable {mE : Fin (nrOf τ) → I → Prop}
variable (hmE : ∀ (j : Fin (nrOf τ)) (r : Univ A R P K dd → Prop),
  rest r (rdTrackE τ j) = bitVal PR.zero PR.one (bitAtOf RF.cell (mE j) r))
variable (hnewkE : ∀ j, wk ≠ rdTrackE τ j) (hnergE : ∀ j, rg ≠ rdTrackE τ j)
variable {ι : Type} [LinearOrder ι] [Finite ι] {a₀ aT : ι}
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)
variable (F : ι → Q → A) (fsOf : ι → Fin (nrOf τ + 1) → Q → A)
variable (hlastF : ∀ a, fsOf a (Fin.last (nrOf τ)) = F a)
variable (xE : ι → Fin (nrOf τ) → I)
variable (hnameE : ∀ (a : ι) (j : Fin (nrOf τ)),
  MatchE τ j (fsOf a j.castSucc)
    (PR.passTracksAt RF.cell (rdTrackE τ j) rest (mE j) (RF.cell (xE a j))))
variable (huniqE : ∀ (a : ι) (j : Fin (nrOf τ)) (r : Univ A R P K dd → Prop),
  MatchE τ j (fsOf a j.castSucc)
    (PR.passTracksAt RF.cell (rdTrackE τ j) rest (mE j) r) → r = RF.cell (xE a j))
variable (hfsET : ∀ (a : ι) (j : Fin (nrOf τ)), mE j (xE a j) →
  fsOf a j.succ = setFlagE τ j true (fsOf a j.castSucc) (rest v))
variable (hfsEF : ∀ (a : ι) (j : Fin (nrOf τ)), ¬mE j (xE a j) →
  fsOf a j.succ = setFlagE τ j false (fsOf a j.castSucc) (rest v))
variable (hadv : ∀ a a' : ι, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  advEl τ (F a) (rest v) = fsOf a' 0)
variable (hmaxT : IsMaxEl τ (F aT))
variable (hmaxF : ∀ a, a < aT → ¬IsMaxEl τ (F a))
variable (hinit : initEl τ (fsT (Fin.last m)) (rest v) = fsOf a₀ 0)

variable (hcostE : ∀ (a : ι) (j : Fin (nrOf τ)),
  2 * (wideRank (RF.cell (xE a j)) - wideRank v) + 2 ≤ c)

include RF hrules hR hlin hix hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀ hwkt₀ hrgt₀
  hnameT huniqT hfsTT hfsTF hτ hmE hnewkE hnergE hbotI htopI hlastF
  hnameE huniqE hfsET hfsEF hadv hmaxT hmaxF hinit hcostT hcostE in
/-- **The tag-branched machinery's run, on a clock**: from its first phase at
the marker – the witness chain, the branch on the decoded tag tuple, and that
tuple's element loop – to the exit phase one cell to the marker's right, at the
chain's reads, the branch's two steps and the loop's own cost. -/
theorem tag_reachesIn :
    (wideData (Univ A R P K dd)).ReachesIn
      ((c + 2) * m + 2 + ((2 + (c + 2) * nrOf τ) * (Nat.card ι + 1) + 1))
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) (fsT 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (exitSt τ (F aT) (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot RF hlin hix hbot hv
  -- the witness chain, from the machinery's first phase
  have hchain := tag_reads RF hrules hR hlin hix hbot hv hvi hwkS hrg hmT hnewkT
    hnergT hm₀ fsT xT hnameT huniqT hfsTT hfsTF c hcostT 0 (Nat.zero_le m)
  have hf0 : (⟨0, Nat.lt_succ_of_le (Nat.zero_le m)⟩ : Fin (m + 1)) = 0 :=
    Fin.ext rfl
  rw [hf0] at hchain
  have hfirst : tagPhaseAt emb 0 = tagFirstRd emb := rfl
  rw [hfirst] at hchain
  -- the branch dispatch, into the loop's entry checkpoint
  have hgwk : PR.passTracksAt RF.cell t₀ rest m₀ v wk = PR.one := by
    rw [Prog.passTracks_of_ne hwkt₀, hwkS]
    exact bitVal_pos rfl
  have hgrg : PR.passTracksAt RF.cell t₀ rest m₀ v rg ≠ PR.one := by
    rw [Prog.passTracks_of_ne hrgt₀, hrg,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact PR.zero_ne_one
  have hdsp : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb .brP) (fsT (Fin.last m))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.loopP τ .e0)) (fsT (Fin.last m))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    exact hasRight_of_rule hrules (i := .br) (ρ := .dsp τ)
      ⟨⟨hgwk, hgrg⟩, hτ⟩ rfl rfl rfl rfl trivial
  -- the walk back into the loop's entry checkpoint
  have hback : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.loopP τ .e0)) (fsT (Fin.last m))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.loopP τ .e0)) (fsT (Fin.last m))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
    have hvv' : v ≠ v' := ne_of_wmIncr hvi
    have hwkv' : PR.passTracksAt RF.cell t₀ rest m₀ v' wk ≠ PR.one := by
      rw [Prog.passTracks_of_ne hwkt₀, hwkS, bitVal_neg (Ne.symm hvv')]
      exact PR.zero_ne_one
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    exact hasLeft_of_rule hrules (i := .loop τ .e0) (ρ := .stay)
      hwkv' rfl rfl rfl rfl not_false
  -- the branch's element loop
  have hloop := elem_reachesIn
    (emb := fun p => emb (.loopP τ p)) (rdTrack := rdTrackE τ)
    (MatchOf := MatchE τ) (setFlag := setFlagE τ) (initEl := initEl τ)
    (advEl := advEl τ) (exitSt := exitSt τ) (IsMaxEl := IsMaxEl τ)
    (exitPh := exitPh) (rEmb := fun s ρ => rEmb (.loop τ s) ρ)
    RF (fun s ρ => hrules (.loop τ s) ρ)
    hR hlin hix hbot hv hvi hwkS hrg hmE hnewkE hnergE hm₀ hwkt₀ hrgt₀
    hbotI htopI F fsOf hlastF xE hnameE huniqE hfsET hfsEF hadv hmaxT hmaxF
    c hcostE hinit
  rw [Nat.sub_zero] at hchain
  exact TMData.ReachesIn.mono (by omega)
    (((hchain.tail hdsp).tail hback).trans hloop)

include RF hrules hR hlin hix hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀ hwkt₀ hrgt₀
  hnameT huniqT hfsTT hfsTF hτ hmE hnewkE hnergE hbotI htopI hlastF
  hnameE huniqE hfsET hfsEF hadv hmaxT hmaxF hinit in
/-- **The tag-branched machinery's run**, the budget forgotten: what a
space-bounded caller reads, at the width every trip has anyway. -/
theorem tag_run :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) (fsT 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (exitSt τ (F aT) (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ :=
  (tag_reachesIn RF hrules hR hlin hix hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀
    hwkt₀ hrgt₀ fsT xT hnameT huniqT hfsTT hfsTF
    (2 * Nat.card {p : WPoint (Univ A R P K dd) //
      (wideData (Univ A R P K dd)).Posn p} + 2)
    (fun i => by
      have := wideRank_lt_card (A := Univ A R P K dd) (RF.cell (xT i))
      omega)
    hτ hmE hnewkE hnergE hbotI htopI F fsOf hlastF xE hnameE huniqE hfsET hfsEF
    hadv hmaxT hmaxF hinit
    (fun a j => by
      have := wideRank_lt_card (A := Univ A R P K dd) (RF.cell (xE a j))
      omega)).reflTransGen

end Chain

end TagRun

end Pfp

end DescriptiveComplexity
