/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpRunElem
import DescriptiveComplexity.Problems.Wide.PfpRunTagged
import DescriptiveComplexity.Problems.Wide.PfpRunTuple

/-!
# Generated control families: the runs, iterated

The run theorems of the layer take their control evolution as abstract
*families* over the enumeration – `fsOf a j`, the pointer before the `j`-th
read of round `a` – tied together by per-cover equations. An instantiation
has to produce such a family, and its rounds are defined by *iteration*: the
next round's entry is a function of the previous round's exit. This file
builds the family once, for every instantiation:

* `DescriptiveComplexity.Pfp.iterOrd` – a state iterated along a finite
  linear order, by recursion on `DescriptiveComplexity.orank` (the bottom is
  the base, each cover one step);
* `DescriptiveComplexity.Pfp.chainSt` – the within-round read chain, each
  read's stored bit chosen classically;
* `DescriptiveComplexity.Pfp.elem_run_iter` – the element loop's run at the
  generated family: the caller supplies only the name guards at the
  generated states, the exhaustion conditions, and the geometry.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### Iteration along a finite linear order -/

section Iter

variable {ι : Type} {Q' : Type*} [LinearOrder ι] [Finite ι]

open Classical in
/-- The iterated state at a rank: the base at `0`, one step per rank – the
element of that rank supplying the step's index. -/
noncomputable def iterState (init : Q') (step : ι → Q' → Q') : ℕ → Q'
  | 0 => init
  | n + 1 =>
    if h : ∃ a : ι, orank a = n then step h.choose (iterState init step n)
    else iterState init step n

/-- **A state iterated along the order**: the base at the bottom, one step
per cover. -/
noncomputable def iterOrd (init : Q') (step : ι → Q' → Q') (a : ι) : Q' :=
  iterState init step (orank a)

omit [Finite ι] in
/-- At the bottom the iteration is the base. -/
theorem iterOrd_bot {init : Q'} {step : ι → Q' → Q'} {a₀ : ι}
    (hbot : ∀ b, a₀ ≤ b) : iterOrd init step a₀ = init := by
  rw [iterOrd, orank_eq_zero hbot]
  rfl

/-- Across a cover the iteration steps once, at the covered element. -/
theorem iterOrd_covers {init : Q'} {step : ι → Q' → Q'} {a a' : ι}
    (hlt : a < a') (hnb : ∀ b, ¬(a < b ∧ b < a')) :
    iterOrd init step a' = step a (iterOrd init step a) := by
  classical
  have hcov : a ⋖ a' := ⟨hlt, fun c h1 h2 => hnb c ⟨h1, h2⟩⟩
  have hrk : orank a' = orank a + 1 := orank_covBy hcov
  have hex : ∃ b : ι, orank b = orank a := ⟨a, rfl⟩
  rw [iterOrd, hrk]
  simp only [iterState]
  rw [dif_pos hex, orank_inj hex.choose_spec]
  rfl

omit [Finite ι] in
/-- **An invariant of the step is an invariant of the iteration**: what the
base satisfies and every step preserves holds at every element. This is what
a threaded tape family's field lemmas are proved by — the fields a round
leaves alone are preserved by each step, hence along the whole loop. -/
theorem iterOrd_invariant {init : Q'} {step : ι → Q' → Q'} {Inv : Q' → Prop}
    (hinit : Inv init) (hstep : ∀ a q, Inv q → Inv (step a q)) (a : ι) :
    Inv (iterOrd init step a) := by
  classical
  have key : ∀ n : ℕ, Inv (iterState init step n) := by
    intro n
    induction n with
    | zero => exact hinit
    | succ n ih =>
      rw [iterState]
      split
      · exact hstep _ _ ih
      · exact ih
  exact key (orank a)

end Iter

/-! ### The within-round read chain -/

section Chain

variable {Q' : Type} {nr : ℕ}

open Classical in
/-- **The read chain of one round**: the `j`-th prefix of the reads applied
to the round's entry state, each stored bit the read's. -/
noncomputable def chainSt (bit : Fin nr → Prop) (upd : Fin nr → Bool → Q' → Q')
    (base : Q') : ℕ → Q'
  | 0 => base
  | j + 1 =>
    if h : j < nr then
      upd ⟨j, h⟩ (if bit ⟨j, h⟩ then true else false)
        (chainSt bit upd base j)
    else chainSt bit upd base j

@[simp]
theorem chainSt_zero {bit : Fin nr → Prop} {upd : Fin nr → Bool → Q' → Q'}
    {base : Q'} : chainSt bit upd base 0 = base := rfl

/-- A positive read's link. -/
theorem chainSt_succ_pos {bit : Fin nr → Prop} {upd : Fin nr → Bool → Q' → Q'}
    {base : Q'} {j : ℕ} (h : j < nr) (hb : bit ⟨j, h⟩) :
    chainSt bit upd base (j + 1) =
      upd ⟨j, h⟩ true (chainSt bit upd base j) := by
  classical
  simp only [chainSt]
  rw [dif_pos h, if_pos hb]

/-- A negative read's link. -/
theorem chainSt_succ_neg {bit : Fin nr → Prop} {upd : Fin nr → Bool → Q' → Q'}
    {base : Q'} {j : ℕ} (h : j < nr) (hb : ¬bit ⟨j, h⟩) :
    chainSt bit upd base (j + 1) =
      upd ⟨j, h⟩ false (chainSt bit upd base j) := by
  classical
  simp only [chainSt]
  rw [dif_pos h, if_neg hb]

end Chain

/-! ### The element loop's run, at the generated family -/

section ElemIter

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {nr : ℕ}
variable {wk rg : W} {emb : ElemPh nr → P}
variable {rdTrack : Fin nr → W}
variable {MatchOf : Fin nr → (Q → A) → (W → A) → Prop}
variable {setFlag : Fin nr → Bool → (Q → A) → (W → A) → (Q → A)}
variable {initEl advEl exitSt : (Q → A) → (W → A) → (Q → A)}
variable {IsMaxEl : (Q → A) → Prop}
variable {exitPh : P}
variable {rEmb : ∀ i : ElemSite nr, ElemSh nr i → R}
variable {ι : Type} [LinearOrder ι] [Finite ι]
variable {rest : (Univ A R P K dd → Prop) → W → A}
variable {v : Univ A R P K dd → Prop}
variable {m : Fin nr → Univ A R P K dd → Prop}

variable (setFlag initEl advEl rest v m) in
/-- **The generated round-entry state**: the loop's `initEl` at the bottom,
each cover the previous round's reads folded and advanced. -/
noncomputable def elemIter (xOf : ι → Fin nr → Univ A R P K dd) (f₀ : Q → A)
    (a : ι) : Q → A :=
  iterOrd (initEl f₀ (rest v))
    (fun a q =>
      advEl (chainSt (fun j => m j (xOf a j))
        (fun j b q' => setFlag j b q' (rest v)) q nr) (rest v)) a

variable (setFlag initEl advEl rest v m) in
/-- **The generated within-round family**: the read chain of round `a`
applied to its entry state. -/
noncomputable def elemFam (xOf : ι → Fin nr → Univ A R P K dd) (f₀ : Q → A)
    (a : ι) (j : Fin (nr + 1)) : Q → A :=
  chainSt (fun j' => m j' (xOf a j'))
    (fun j' b q' => setFlag j' b q' (rest v))
    (elemIter setFlag initEl advEl rest v m xOf f₀ a) (j : ℕ)

/-! **The background is read at the working cell alone.** Both generated
families mention `rest` only as `rest v`, so a background that moves
elsewhere — at a register cell, say, where the four register slots live —
generates the same control. This is what makes a loop blind to the two
scratch registers of the state it is run at. -/

section CongrRest

variable {rest' : (Univ A R P K dd → Prop) → W → A}

omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] [Finite ι] in
/-- Two backgrounds agreeing at the working cell give one round-entry
family. -/
theorem elemIter_congr_rest (h : rest v = rest' v)
    (xOf : ι → Fin nr → Univ A R P K dd) (f₀ : Q → A) (a : ι) :
    elemIter setFlag initEl advEl rest v m xOf f₀ a =
      elemIter setFlag initEl advEl rest' v m xOf f₀ a := by
  simp only [elemIter, h]

omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] [Finite ι] in
/-- Two backgrounds agreeing at the working cell give one within-round
family. -/
theorem elemFam_congr_rest (h : rest v = rest' v)
    (xOf : ι → Fin nr → Univ A R P K dd) (f₀ : Q → A) (a : ι)
    (j : Fin (nr + 1)) :
    elemFam setFlag initEl advEl rest v m xOf f₀ a j =
      elemFam setFlag initEl advEl rest' v m xOf f₀ a j := by
  simp only [elemFam, h, elemIter_congr_rest h]

end CongrRest

variable (hrules : ∀ (i : ElemSite nr) (ρ : ElemSh nr i),
  PR.rules (rEmb i ρ) = elemRule PR.one wk rg emb rdTrack MatchOf setFlag
    initEl advEl exitSt IsMaxEl exitPh i ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable {gbot : Univ A R P K dd} (hbot : ∀ y, WMLe gbot y)
variable {v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (wmSeg gbot))
variable (hvi : WMIncr WMLe v v')
variable (hwkS : ∀ r, rest r wk = bitVal PR.zero PR.one (r = v))
variable (hrg : ∀ r, rest r rg =
  bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hm : ∀ (j : Fin nr) (r : Univ A R P K dd → Prop),
  rest r (rdTrack j) = bitVal PR.zero PR.one (regBit (m j) r))
variable (hnewk : ∀ j, wk ≠ rdTrack j) (hnerg : ∀ j, rg ≠ rdTrack j)
variable {t₀ : W} {m₀ : Univ A R P K dd → Prop}
variable (hm₀ : ∀ r, rest r t₀ = bitVal PR.zero PR.one (regBit m₀ r))
variable (hwkt₀ : wk ≠ t₀) (hrgt₀ : rg ≠ t₀)
variable {a₀ aT : ι}
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)
variable (xOf : ι → Fin nr → Univ A R P K dd) (f₀ : Q → A)
variable (hname : ∀ (a : ι) (j : Fin nr),
  MatchOf j (elemFam setFlag initEl advEl rest v m xOf f₀ a j.castSucc)
    (PR.passTracks (rdTrack j) rest (m j) (wmSeg (xOf a j))))
variable (huniq : ∀ (a : ι) (j : Fin nr) (r : Univ A R P K dd → Prop),
  MatchOf j (elemFam setFlag initEl advEl rest v m xOf f₀ a j.castSucc)
    (PR.passTracks (rdTrack j) rest (m j) r) → r = wmSeg (xOf a j))
variable (hmaxT : IsMaxEl (elemFam setFlag initEl advEl rest v m xOf f₀ aT (Fin.last nr)))
variable (hmaxF : ∀ a, a < aT →
  ¬IsMaxEl (elemFam setFlag initEl advEl rest v m xOf f₀ a (Fin.last nr)))

include hrules hR hlin hbot hv hvi hwkS hrg hm hnewk hnerg hm₀ hwkt₀ hrgt₀
  hbotI htopI hname huniq hmaxT hmaxF in
/-- **The element loop's run at the generated family**: only the name guards
at the generated states, the exhaustion conditions and the geometry are
owed; the family equations hold by construction. -/
theorem elem_run_iter :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb .e0) f₀), Sum.inl v,
        wideTape (PR.trackTape t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (exitSt (elemFam setFlag initEl advEl rest v m xOf f₀ aT (Fin.last nr))
            (rest v))), Sum.inl v',
        wideTape (PR.trackTape t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  classical
  refine elem_run hrules hR hlin hbot hv hvi hwkS hrg hm hnewk hnerg hm₀
    hwkt₀ hrgt₀ hbotI htopI
    (fun a => elemFam setFlag initEl advEl rest v m xOf f₀ a (Fin.last nr))
    (elemFam setFlag initEl advEl rest v m xOf f₀) (fun _ => rfl) xOf hname huniq
    ?_ ?_ ?_ hmaxT hmaxF ?_
  · intro a j hbit
    exact chainSt_succ_pos j.isLt (by
      exact (show m j (xOf a j) from hbit))
  · intro a j hbit
    exact chainSt_succ_neg j.isLt hbit
  · intro a a' hlt hnb
    exact (iterOrd_covers (init := initEl f₀ (rest v))
      (step := fun a q => advEl (chainSt (fun j => m j (xOf a j))
        (fun j b q' => setFlag j b q' (rest v)) q nr) (rest v))
      hlt hnb).symm
  · exact (iterOrd_bot (init := initEl f₀ (rest v))
      (step := fun a q => advEl (chainSt (fun j => m j (xOf a j))
        (fun j b q' => setFlag j b q' (rest v)) q nr) (rest v))
      hbotI).symm

end ElemIter

/-! ### The tag-branched machinery's run, at the generated families -/

section TagIter

variable {A R P Q W K T : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {m : ℕ} {nrOf : T → ℕ}
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
variable {rest : (Univ A R P K dd → Prop) → W → A}
variable {v : Univ A R P K dd → Prop}
variable {mT : Fin m → Univ A R P K dd → Prop}

variable (setTagFlag rest v mT) in
/-- **The generated witness chain**: the `i`-th prefix of the witness reads
applied to the entry control, each one-hot bit the read's. -/
noncomputable def tagFam (xT : Fin m → Univ A R P K dd) (f₀ : Q → A)
    (i : Fin (m + 1)) : Q → A :=
  chainSt (fun i' => mT i' (xT i'))
    (fun i' b q => setTagFlag i' b q (rest v)) f₀ (i : ℕ)

omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] in
/-- **The witness chain reads its background at the working cell alone.** -/
theorem tagFam_congr_rest {rest' : (Univ A R P K dd → Prop) → W → A}
    (h : rest v = rest' v) (xT : Fin m → Univ A R P K dd) (f₀ : Q → A)
    (i : Fin (m + 1)) :
    tagFam setTagFlag rest v mT xT f₀ i =
      tagFam setTagFlag rest' v mT xT f₀ i := by
  simp only [tagFam, h]

variable {rEmb : ∀ i : TagSite m T nrOf, TagSh m T nrOf i → R}
variable (hrules : ∀ (i : TagSite m T nrOf) (ρ : TagSh m T nrOf i),
  PR.rules (rEmb i ρ) = tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag
    TagsAre rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable {gbot : Univ A R P K dd} (hbot : ∀ y, WMLe gbot y)
variable {v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (wmSeg gbot))
variable (hvi : WMIncr WMLe v v')
variable (hwkS : ∀ r, rest r wk = bitVal PR.zero PR.one (r = v))
variable (hrg : ∀ r, rest r rg =
  bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hmT : ∀ (i : Fin m) (r : Univ A R P K dd → Prop),
  rest r (rdTrackT i) = bitVal PR.zero PR.one (regBit (mT i) r))
variable (hnewkT : ∀ i, wk ≠ rdTrackT i) (hnergT : ∀ i, rg ≠ rdTrackT i)
variable {t₀ : W} {m₀ : Univ A R P K dd → Prop}
variable (hm₀ : ∀ r, rest r t₀ = bitVal PR.zero PR.one (regBit m₀ r))
variable (hwkt₀ : wk ≠ t₀) (hrgt₀ : rg ≠ t₀)
variable (xT : Fin m → Univ A R P K dd) (f₀ : Q → A)
variable (hnameT : ∀ i : Fin m,
  MatchT i (tagFam setTagFlag rest v mT xT f₀ i.castSucc)
    (PR.passTracks (rdTrackT i) rest (mT i) (wmSeg (xT i))))
variable (huniqT : ∀ (i : Fin m) (r : Univ A R P K dd → Prop),
  MatchT i (tagFam setTagFlag rest v mT xT f₀ i.castSucc)
    (PR.passTracks (rdTrackT i) rest (mT i) r) → r = wmSeg (xT i))
variable {τ : T}
variable (hτ : TagsAre τ (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)))
variable {mE : Fin (nrOf τ) → Univ A R P K dd → Prop}
variable (hmE : ∀ (j : Fin (nrOf τ)) (r : Univ A R P K dd → Prop),
  rest r (rdTrackE τ j) = bitVal PR.zero PR.one (regBit (mE j) r))
variable (hnewkE : ∀ j, wk ≠ rdTrackE τ j) (hnergE : ∀ j, rg ≠ rdTrackE τ j)
variable {ι : Type} [LinearOrder ι] [Finite ι] {a₀ aT : ι}
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)
variable (xE : ι → Fin (nrOf τ) → Univ A R P K dd)
variable (hnameE : ∀ (a : ι) (j : Fin (nrOf τ)),
  MatchE τ j (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
      (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) a j.castSucc)
    (PR.passTracks (rdTrackE τ j) rest (mE j) (wmSeg (xE a j))))
variable (huniqE : ∀ (a : ι) (j : Fin (nrOf τ)) (r : Univ A R P K dd → Prop),
  MatchE τ j (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
      (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) a j.castSucc)
    (PR.passTracks (rdTrackE τ j) rest (mE j) r) → r = wmSeg (xE a j))
variable (hmaxT : IsMaxEl τ
  (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
    (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) aT (Fin.last (nrOf τ))))
variable (hmaxF : ∀ a, a < aT → ¬IsMaxEl τ
  (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
    (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) a (Fin.last (nrOf τ))))

include hrules hR hlin hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀ hwkt₀ hrgt₀
  hnameT huniqT hτ hmE hnewkE hnergE hbotI htopI hnameE huniqE hmaxT hmaxF in
/-- **The tag-branched machinery's run at the generated families**: the
witness chain and the branch's element loop are both generated, so only the
name guards, the branch decode and the exhaustion conditions are owed. -/
theorem tag_run_iter :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f₀), Sum.inl v,
        wideTape (PR.trackTape t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (exitSt τ (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
            (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) aT
            (Fin.last (nrOf τ))) (rest v))), Sum.inl v',
        wideTape (PR.trackTape t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  classical
  refine tag_run hrules hR hlin hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀
    hwkt₀ hrgt₀ (tagFam setTagFlag rest v mT xT f₀) xT hnameT huniqT
    ?_ ?_ hτ hmE hnewkE hnergE hbotI htopI
    (fun a => elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
      (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) a (Fin.last (nrOf τ)))
    (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
      (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)))
    (fun _ => rfl) xE hnameE huniqE ?_ ?_ ?_ hmaxT hmaxF ?_
  · intro i hbit
    exact chainSt_succ_pos i.isLt (show mT i (xT i) from hbit)
  · intro i hbit
    exact chainSt_succ_neg i.isLt hbit
  · intro a j hbit
    exact chainSt_succ_pos j.isLt (show mE j (xE a j) from hbit)
  · intro a j hbit
    exact chainSt_succ_neg j.isLt hbit
  · intro a a' hlt hnb
    exact (iterOrd_covers
      (init := initEl τ (tagFam setTagFlag rest v mT xT f₀ (Fin.last m))
        (rest v))
      (step := fun a q => advEl τ (chainSt (fun j => mE j (xE a j))
        (fun j b q' => setFlagE τ j b q' (rest v)) q (nrOf τ)) (rest v))
      hlt hnb).symm
  · exact (iterOrd_bot
      (init := initEl τ (tagFam setTagFlag rest v mT xT f₀ (Fin.last m))
        (rest v))
      (step := fun a q => advEl τ (chainSt (fun j => mE j (xE a j))
        (fun j b q' => setFlagE τ j b q' (rest v)) q (nrOf τ)) (rest v))
      hbotI).symm

end TagIter

/-! ### The tuple loop's run, at the generated families -/

section TupleIter

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}
variable {wk rg : W} {emb : ChainPh 3 TuplePS → P}
variable {tSrc tDst : W}
variable {MatchS MatchD : (Q → A) → (W → A) → Prop}
variable {bitFlag : (Q → A) → Prop}
variable {setBit : Bool → (Q → A) → (W → A) → (Q → A)}
variable {initLv advLv : (Q → A) → (W → A) → (Q → A)}
variable {IsMaxLv : (Q → A) → Prop}
variable {exitPh : P}
variable {ι : Type} [LinearOrder ι] [Finite ι]
variable {mSrc : Univ A R P K dd → Prop}
variable {v : Univ A R P K dd → Prop}
variable {restF : (Univ A R P K dd → Prop) →
  (Univ A R P K dd → Prop) → W → A}

variable (mSrc) in
/-- **The generated destination track**: empty of the loop's bits at the
bottom, each cover the round's copy applied. -/
noncomputable def tupleIterD (xS xD : ι → Univ A R P K dd)
    (mD₀ : Univ A R P K dd → Prop) (a : ι) : Univ A R P K dd → Prop :=
  iterOrd mD₀
    (fun a' m => fun y => (y = xD a' ∧ mSrc (xS a')) ∨ (y ≠ xD a' ∧ m y)) a

variable (setBit initLv advLv restF mSrc v) in
open Classical in
/-- **The generated pre-store control**: the loop's `initLv` at the bottom,
each cover the previous round folded and advanced, the round's symbol read
from the destination-dependent background. -/
noncomputable def tupleIter0 (xS xD : ι → Univ A R P K dd)
    (mD₀ : Univ A R P K dd → Prop) (f₀ : Q → A) (a : ι) : Q → A :=
  iterOrd (initLv f₀ (restF mD₀ v))
    (fun a' q =>
      advLv (if mSrc (xS a') then setBit true q (restF
          (tupleIterD mSrc xS xD mD₀ a') v)
        else setBit false q (restF (tupleIterD mSrc xS xD mD₀ a') v))
        (restF (tupleIterD mSrc xS xD mD₀ a') v)) a

variable (setBit initLv advLv restF mSrc v) in
open Classical in
/-- **The generated post-store control**: the round's bit stored. -/
noncomputable def tupleIter1 (xS xD : ι → Univ A R P K dd)
    (mD₀ : Univ A R P K dd → Prop) (f₀ : Q → A) (a : ι) : Q → A :=
  if mSrc (xS a) then
    setBit true (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
      (restF (tupleIterD mSrc xS xD mD₀ a) v)
  else
    setBit false (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
      (restF (tupleIterD mSrc xS xD mD₀ a) v)

section CongrRestF

variable {restF' : (Univ A R P K dd → Prop) →
  (Univ A R P K dd → Prop) → W → A}

omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] [Finite ι] in
/-- **The copy loop reads its background at the working cell alone** — at
every destination content, the cell being the same one. -/
theorem tupleIter0_congr_restF (h : ∀ m', restF m' v = restF' m' v)
    (xS xD : ι → Univ A R P K dd) (mD₀ : Univ A R P K dd → Prop)
    (f₀ : Q → A) (a : ι) :
    tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a =
      tupleIter0 setBit initLv advLv mSrc v restF' xS xD mD₀ f₀ a := by
  simp only [tupleIter0, h]

omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] [Finite ι] in
/-- The same, after the round's store. -/
theorem tupleIter1_congr_restF (h : ∀ m', restF m' v = restF' m' v)
    (xS xD : ι → Univ A R P K dd) (mD₀ : Univ A R P K dd → Prop)
    (f₀ : Q → A) (a : ι) :
    tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a =
      tupleIter1 setBit initLv advLv mSrc v restF' xS xD mD₀ f₀ a := by
  simp only [tupleIter1, h, tupleIter0_congr_restF h]

end CongrRestF

variable {rEmb : ∀ i : ChainSite 3 TupleSS, ChainSh 3 TupleSS TupleSh i → R}
variable (hrules : ∀ (i : ChainSite 3 TupleSS) (ρ : ChainSh 3 TupleSS TupleSh i),
  PR.rules (rEmb i ρ) = tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS
    MatchD bitFlag setBit initLv advLv IsMaxLv exitPh i ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable {gbot : Univ A R P K dd} (hbot : ∀ y, WMLe gbot y)
variable {v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (wmSeg gbot))
variable (hvi : WMIncr WMLe v v')
variable {a₀ aT : ι}
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)
variable (xS xD : ι → Univ A R P K dd)
variable (mD₀ : Univ A R P K dd → Prop) (f₀ : Q → A)
variable (hwkS : ∀ m' r, restF m' r wk = bitVal PR.zero PR.one (r = v))
variable (hrg : ∀ m' r, restF m' r rg =
  bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hsrc : ∀ m' r, restF m' r tSrc =
  bitVal PR.zero PR.one (regBit mSrc r))
variable (hdst : ∀ m' r, restF m' r tDst =
  bitVal PR.zero PR.one (regBit m' r))
variable (hoff : ∀ m₁ m₂ r s, s ≠ tDst → restF m₁ r s = restF m₂ r s)
variable (hwkSrc : wk ≠ tSrc) (hwkDst : wk ≠ tDst)
variable (hrgSrc : rg ≠ tSrc) (hrgDst : rg ≠ tDst)
variable (hnameS : ∀ a, MatchS
  (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
  (PR.passTracks tSrc (restF (tupleIterD mSrc xS xD mD₀ a)) mSrc
    (wmSeg (xS a))))
variable (huniqS : ∀ (a : ι) (r : Univ A R P K dd → Prop),
  MatchS (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
    (PR.passTracks tSrc (restF (tupleIterD mSrc xS xD mD₀ a)) mSrc r) →
      r = wmSeg (xS a))
variable (hnameD : ∀ a, MatchD
  (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
  (PR.passTracks tDst (restF (tupleIterD mSrc xS xD mD₀ a))
    (tupleIterD mSrc xS xD mD₀ a) (wmSeg (xD a))))
variable (huniqD : ∀ (a : ι) (r : Univ A R P K dd → Prop),
  MatchD (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
    (PR.passTracks tDst (restF (tupleIterD mSrc xS xD mD₀ a))
      (tupleIterD mSrc xS xD mD₀ a) r) → r = wmSeg (xD a))
variable (hbitFlag : ∀ a,
  bitFlag (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a) ↔
    mSrc (xS a))
variable (hmaxT : IsMaxLv
  (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ aT))
variable (hmaxF : ∀ a, a < aT →
  ¬IsMaxLv (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a))

include hrules hR hlin hbot hv hvi hbotI htopI hwkS hrg hsrc hdst hoff
  hwkSrc hwkDst hrgSrc hrgDst hnameS huniqS hnameD huniqD hbitFlag
  hmaxT hmaxF in
/-- **The tuple loop's run at the generated families**: only the name
guards, the copied-bit read-back and the exhaustion conditions are owed. -/
theorem tuple_run_iter :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨0, by omega⟩)) f₀), Sum.inl v,
        wideTape (PR.trackTape tSrc (restF (tupleIterD mSrc xS xD mD₀ a₀))
          mSrc) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ aT)),
        Sum.inl v',
        wideTape (PR.trackTape tDst (restF (tupleIterD mSrc xS xD mD₀ aT))
          (tuplePost mSrc (tupleIterD mSrc xS xD mD₀) xS xD aT))
          (PR.syElt PR.blank)⟩ := by
  classical
  refine tuple_run hrules hR hlin hbot hv hvi hbotI htopI
    (restOf := fun a => restF (tupleIterD mSrc xS xD mD₀ a))
    (mD := tupleIterD mSrc xS xD mD₀)
    (fun a r => hwkS _ r) (fun a r => hrg _ r) (fun a r => hsrc _ r)
    (fun a r => hdst _ r) hwkSrc hwkDst hrgSrc hrgDst xS xD
    (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀)
    (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀)
    hnameS huniqS hnameD huniqD ?_ ?_ hbitFlag ?_ ?_ ?_ hmaxT hmaxF ?_
  · intro a hb
    rw [tupleIter1, if_pos hb]
  · intro a hb
    rw [tupleIter1, if_neg hb]
  · intro a a' hlt hnb
    have hcov : tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a' =
        advLv (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
          (restF (tupleIterD mSrc xS xD mD₀ a) v) := by
      rw [tupleIter1]
      exact iterOrd_covers hlt hnb
    exact hcov.symm
  · intro a a' hlt hnb y
    have hcov : tupleIterD mSrc xS xD mD₀ a' = fun y =>
        (y = xD a ∧ mSrc (xS a)) ∨
        (y ≠ xD a ∧ tupleIterD mSrc xS xD mD₀ a y) :=
      iterOrd_covers hlt hnb
    rw [hcov]
    exact Iff.rfl
  · intro a a' hlt hnb r s hs
    exact hoff _ _ r s hs
  · have hD0 : tupleIterD mSrc xS xD mD₀ a₀ = mD₀ :=
      iterOrd_bot hbotI
    have hI0 : tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a₀ =
        initLv f₀ (restF mD₀ v) :=
      iterOrd_bot hbotI
    rw [hD0, hI0]

/-! ### The destination track, in closed form -/

section TupleContent

variable {A R P K : Type} {dd : ℕ}
variable {ι : Type} [LinearOrder ι] [Finite ι]

/-- **What the copy loop can hold**: every cell of the destination track is
either one the loop wrote — a destination cell of some round — or one it
started with. A property of cells closed under both is therefore closed
under the whole loop; that is how the target of a random access is known to
be an address of argument cells alone. -/
theorem tupleIterD_of_mem {mSrc : Univ A R P K dd → Prop}
    {xS xD : ι → Univ A R P K dd} {mD₀ : Univ A R P K dd → Prop}
    (Q : Univ A R P K dd → Prop) (hxD : ∀ a : ι, Q (xD a))
    (h₀ : ∀ y, mD₀ y → Q y) (b : ι) {y : Univ A R P K dd}
    (hy : tupleIterD mSrc xS xD mD₀ b y) : Q y := by
  induction b using order_induction with
  | hmin z hz =>
    rw [show tupleIterD mSrc xS xD mD₀ z = mD₀ from iterOrd_bot hz] at hy
    exact h₀ y hy
  | hstep w z hwz hnb ih =>
    rw [show tupleIterD mSrc xS xD mD₀ z = fun y =>
      (y = xD w ∧ mSrc (xS w)) ∨ (y ≠ xD w ∧ tupleIterD mSrc xS xD mD₀ w y)
      from iterOrd_covers hwz hnb] at hy
    rcases hy with ⟨rfl, -⟩ | ⟨-, hw⟩
    · exact hxD w
    · exact ih hw

/-- **What the copy loop has written**: a cell holds a bit exactly when some
earlier round wrote it – that round's source bit – or it held one from the
start and no round has touched it. The destination cells being distinct is
what makes the disjunction honest: a cell is written at most once. -/
theorem tupleIterD_iff {mSrc : Univ A R P K dd → Prop}
    {xS xD : ι → Univ A R P K dd}
    (hinj : ∀ u u' : ι, xD u = xD u' → u = u')
    {mD₀ : Univ A R P K dd → Prop} (b : ι) (y : Univ A R P K dd) :
    tupleIterD mSrc xS xD mD₀ b y ↔
      ((∃ u < b, y = xD u ∧ mSrc (xS u)) ∨
        ((∀ u < b, y ≠ xD u) ∧ mD₀ y)) := by
  induction b using order_induction with
  | hmin z hz =>
    have hz0 : tupleIterD mSrc xS xD mD₀ z = mD₀ := iterOrd_bot hz
    have hnou : ∀ u : ι, ¬u < z := fun u hu =>
      absurd (hz u) (not_le_of_gt hu)
    rw [hz0]
    constructor
    · intro h
      exact Or.inr ⟨fun u hu => absurd hu (hnou u), h⟩
    · rintro (⟨u, hu, -⟩ | ⟨-, h⟩)
      · exact absurd hu (hnou u)
      · exact h
  | hstep w z hwz hnb ih =>
    have hz2 : tupleIterD mSrc xS xD mD₀ z = fun y =>
        (y = xD w ∧ mSrc (xS w)) ∨ (y ≠ xD w ∧ tupleIterD mSrc xS xD mD₀ w y) :=
      iterOrd_covers hwz hnb
    have hltz : ∀ u : ι, u < z ↔ u ≤ w := fun u =>
      ⟨fun h => le_of_not_gt fun hgt => hnb u ⟨hgt, h⟩,
        fun h => lt_of_le_of_lt h hwz⟩
    rw [hz2]
    constructor
    · rintro (⟨hy, hsrc⟩ | ⟨hne, hw⟩)
      · exact Or.inl ⟨w, hwz, hy, hsrc⟩
      · rcases ih.mp hw with ⟨u, hu, hy, hsrc⟩ | ⟨hno, hm⟩
        · exact Or.inl ⟨u, lt_trans hu hwz, hy, hsrc⟩
        · refine Or.inr ⟨fun u hu => ?_, hm⟩
          rcases lt_or_eq_of_le ((hltz u).mp hu) with h | h
          · exact hno u h
          · rw [h]
            exact hne
    · rintro (⟨u, hu, hy, hsrc⟩ | ⟨hno, hm⟩)
      · rcases lt_or_eq_of_le ((hltz u).mp hu) with h | h
        · refine Or.inr ⟨?_, ih.mpr (Or.inl ⟨u, h, hy, hsrc⟩)⟩
          intro hc
          rw [hy] at hc
          exact absurd (hinj u w hc) (ne_of_lt h)
        · rw [h] at hy hsrc
          exact Or.inl ⟨hy, hsrc⟩
      · refine Or.inr ⟨hno w hwz, ih.mpr (Or.inr
          ⟨fun u hu => hno u (lt_trans hu hwz), hm⟩)⟩

end TupleContent

end TupleIter

end Pfp

end DescriptiveComplexity
