/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.SimCons

/-!
# The pop phase of the simulation

The second half of the simulation: from the resting configuration of a
continuation, the machine finds the top frame and performs the pop that
`Turing.ToPartrec.stepRet` prescribes – accepting on the empty continuation,
erasing a `comp` header, inspecting the flag of a `fix`, transferring the
stored head of a `cons₂`, or exchanging value and stored value of a `cons₁`.

The frame region is taken apart by
`DescriptiveComplexity.HaltHard.FrameSeg.gap_split`: a leading blank gap,
then the top frame (`DescriptiveComplexity.HaltHard.TopSeg`). Each pop lemma
ends either back at rest – for the pops that consume no code – or at the
dispatch point of a child, where `DescriptiveComplexity.HaltHard.sim_norm`
takes over.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec

variable {c : Code}

/-! ### The top frame -/

/-- The frame region with its leading gap peeled: the top frame comes
first. -/
inductive TopSeg : PCont c → List (SimSym c) → Prop
  /-- The empty continuation: nothing at all. -/
  | halt : TopSeg .halt []
  /-- A `cons₁` frame on top. -/
  | cons₁ {p : CPos c} {as : List ℕ} {k : PCont c} {w : List (SimSym c)} :
      FrameSeg k w → TopSeg (.cons₁ p as k) (.hCons₁ p :: (encVal as ++ w))
  /-- A `cons₂` frame on top. -/
  | cons₂ {ns : List ℕ} {k : PCont c} {w : List (SimSym c)} :
      FrameSeg k w → TopSeg (.cons₂ ns k) (.hCons₂ :: ((encVal ns).reverse ++ w))
  /-- A `comp` frame on top. -/
  | comp {p : CPos c} {k : PCont c} {w : List (SimSym c)} :
      FrameSeg k w → TopSeg (.comp p k) (.hComp p :: w)
  /-- A `fix` frame on top. -/
  | fix {p : CPos c} {k : PCont c} {w : List (SimSym c)} :
      FrameSeg k w → TopSeg (.fix p k) (.hFix p :: w)

/-- A frame region splits into its leading gap and its top frame. -/
theorem FrameSeg.gap_split {k : PCont c} {fr : List (SimSym c)} (h : FrameSeg k fr) :
    ∃ n w, fr = List.replicate n SimSym.bk ++ w ∧ TopSeg k w := by
  induction h with
  | halt => exact ⟨0, [], rfl, TopSeg.halt⟩
  | gap _ ih =>
    obtain ⟨n, w, rfl, hw⟩ := ih
    exact ⟨n + 1, w, by simp [List.replicate_succ], hw⟩
  | cons₁ h => exact ⟨0, _, rfl, TopSeg.cons₁ h⟩
  | cons₂ h => exact ⟨0, _, rfl, TopSeg.cons₂ h⟩
  | comp h => exact ⟨0, _, rfl, TopSeg.comp h⟩
  | fix h => exact ⟨0, _, rfl, TopSeg.fix h⟩

/-- Gaps may be prepended to a frame region wholesale. -/
theorem FrameSeg.gaps {k : PCont c} {w : List (SimSym c)} (n : ℕ) (h : FrameSeg k w) :
    FrameSeg k (List.replicate n SimSym.bk ++ w) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [List.replicate_succ, List.cons_append]; exact FrameSeg.gap ih

/-! ### Pass lemmas for the pops -/

section Pass

variable {σ : SimSym c} {p : CPos c}

theorem pass_fxGo (h : σ ≠ .endR) : simStep (.fxGo p) σ = some (σ, .fxGo p, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_fxDropL (h : σ ≠ .endL) :
    simStep (c := c) .fxDropL σ = some (σ, .fxDropL, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_swGo (h : σ ≠ .endR) : simStep (c := c) .swGo σ = some (σ, .swGo, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_swCar₁ (h : σ ≠ .endL) :
    simStep (c := c) .swCar₁ σ = some (σ, .swCar₁, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_swCarC (h : σ ≠ .endL) :
    simStep (c := c) .swCarC σ = some (σ, .swCarC, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_swHdr (h : σ ≠ .endL) :
    simStep (c := c) .swHdr σ = some (σ, .swHdr, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_swOut (h : ∀ q, σ ≠ .hCons₁ q) :
    simStep (c := c) .swOut σ = some (σ, .swOut, true) := by
  cases σ <;> first | rfl | exact absurd rfl (h _)

theorem pass_swApp₁ (h : σ ≠ .endR) :
    simStep (c := c) .swApp₁ σ = some (σ, .swApp₁, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_swAppC (h : σ ≠ .endR) :
    simStep (c := c) .swAppC σ = some (σ, .swAppC, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_swBack (h : σ ≠ .endL) :
    simStep (c := c) .swBack σ = some (σ, .swBack, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_ppGo (h : σ ≠ .endR) : simStep (c := c) .ppGo σ = some (σ, .ppGo, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_ppBack (h : σ ≠ .endL) :
    simStep (c := c) .ppBack σ = some (σ, .ppBack, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_ppCar (h : σ ≠ .endR) : simStep (c := c) .ppCar σ = some (σ, .ppCar, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

/-- `fxDropR` re-crosses the gap blanks. -/
theorem pass_fxDropR (h : σ = .bk) :
    simStep (c := c) .fxDropR σ = some (σ, .fxDropR, true) := by
  subst h; rfl

/-- `fxOnes` erases the digits of the head block, walking left. -/
theorem pass_fxOnes (h : σ = .one) :
    simStep (.fxOnes p) σ = some (.bk, .fxOnes p, false) := by
  subst h; rfl

/-- `ppFind` crosses the gap blanks. -/
theorem pass_ppFind (h : σ = .bk) :
    simStep (c := c) .ppFind σ = some (σ, .ppFind, true) := by
  subst h; rfl

/-- `ppScan` passes the frame content. -/
theorem pass_ppScan (h : σ = .one ∨ σ = .com) :
    simStep (c := c) .ppScan σ = some (σ, .ppScan, true) := by
  rcases h with rfl | rfl <;> rfl

/-- `ppScan` stops on the first letter that is not frame content. -/
theorem stop_ppScan (h1 : σ ≠ .one) (h2 : σ ≠ .com) :
    simStep (c := c) .ppScan σ = some (σ, .ppLast, false) := by
  cases σ <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2

/-- `ppKill` erases the spent frame content, walking left. -/
theorem pass_ppKill (h : σ = .one ∨ σ = .com) :
    simStep (c := c) .ppKill σ = some (.bk, .ppKill, false) := by
  rcases h with rfl | rfl <;> rfl

/-- `swScan` passes the frame content. -/
theorem pass_swScan (h : σ = .one ∨ σ = .com) :
    simStep (c := c) .swScan σ = some (σ, .swScan, true) := by
  rcases h with rfl | rfl <;> rfl

/-- `swScan` stops on the first letter that is not frame content. -/
theorem stop_swScan (h1 : σ ≠ .one) (h2 : σ ≠ .com) :
    simStep (c := c) .swScan σ = some (σ, .swLast, false) := by
  cases σ <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2

end Pass

/-! ### Where a content scan stops

Whatever follows a frame region starts with a header, a blank or `mid`, never
a content letter – frames start with headers – so a rightward scan over
`one`/`com` stops deterministically. The two splits below extract that stop
letter, absorbing an erased zone of blanks in front. -/

/-- A frame region followed by `mid` starts with a letter that is not frame
content. -/
theorem FrameSeg.head_split {k' : PCont c} {w' : List (SimSym c)} (hw' : FrameSeg k' w')
    (R : List (SimSym c)) :
    ∃ x X, w' ++ SimSym.mid :: R = x :: X ∧ x ≠ SimSym.one ∧ x ≠ SimSym.com := by
  cases hw' with
  | halt => exact ⟨.mid, R, rfl, by simp, by simp⟩
  | gap _ => exact ⟨.bk, _, rfl, by simp, by simp⟩
  | cons₁ _ => exact ⟨.hCons₁ _, _, rfl, by simp, by simp⟩
  | cons₂ _ => exact ⟨.hCons₂, _, rfl, by simp, by simp⟩
  | comp _ => exact ⟨.hComp _, _, rfl, by simp, by simp⟩
  | fix _ => exact ⟨.hFix _, _, rfl, by simp, by simp⟩

/-- A blank run in front preserves the shape of the stop letter. -/
theorem bk_head_split (e : ℕ) {x : SimSym c} (hx1 : x ≠ SimSym.one)
    (hx2 : x ≠ SimSym.com) (X : List (SimSym c)) :
    ∃ x₂ X₂, List.replicate e SimSym.bk ++ x :: X = x₂ :: X₂ ∧
      x₂ ≠ SimSym.one ∧ x₂ ≠ SimSym.com := by
  rcases e with - | e
  · exact ⟨x, X, rfl, hx1, hx2⟩
  · exact ⟨.bk, List.replicate e SimSym.bk ++ x :: X,
      by simp [List.replicate_succ], by simp, by simp⟩

/-! ### The `comp` pop -/

/-- **Popping a `comp` frame**: seek the top frame, erase its header, and
walk to the dispatch point of its code. The header cell joins the gap. -/
theorem pop_comp {p : CPos c} {k' : PCont c} (n : ℕ) {w' : List (SimSym c)}
    (hw' : FrameSeg k' w') (g : ℕ) (v : List ℕ) (j t : ℕ) :
    Reach (restCfg g (List.replicate n SimSym.bk ++ SimSym.hComp p :: w') v j t)
      (atMid (.nSeekR p) g (List.replicate (n + 1) SimSym.bk ++ w') v j t) := by
  -- wake up: retL on endL hands over to retR, which crosses the gap
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .retL SimSym.endL = some (.endL, .retR, true) from rfl)
    (P := fun σ => σ = SimSym.bk)
    (fun τ hτ => by rw [hτ]; rfl)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    (SimSym.hComp p) (List.replicate g SimSym.bk)
    (w' ++ SimSym.mid :: valR v j t)
  -- erase the header and walk to mid
  have r2 := reach_step_then_walkR
    (show simStep (c := c) .retR (SimSym.hComp p) = some (.bk, .nSeekR p, true) from rfl)
    (P := fun σ => σ ≠ SimSym.mid) (fun τ hτ => pass_nSeekR hτ)
    w' (fun τ hτ => ((hw'.mem_frameSym τ hτ).ne).2.1)
    SimSym.mid
    ((List.replicate n SimSym.bk).reverse ++ SimSym.endL :: List.replicate g SimSym.bk)
    (valR v j t)
  refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
  refine Reach.trans r2 ?_
  refine Reach.cast ?_ rfl (Reach.refl _)
  simp [midL, List.replicate_succ']

/-! ### The `halt` pop -/

/-- **The empty continuation accepts**: the frame region is a bare blank gap,
so the wake-up walk crosses it, meets `mid` and accepts. -/
theorem pop_halt (n g : ℕ) (v : List ℕ) (j t : ℕ) :
    ∃ y : LCfg c, y.q = .acc ∧
      Reach (restCfg g (List.replicate n SimSym.bk) v j t) y := by
  -- wake up: retL on endL hands over to retR, which crosses the gap
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .retL SimSym.endL = some (.endL, .retR, true) from rfl)
    (P := fun σ => σ = SimSym.bk) (fun τ hτ => by rw [hτ]; rfl)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    SimSym.mid (List.replicate g SimSym.bk) (valR v j t)
  -- accept on mid
  have r2 := lstep_right
    (show simStep (c := c) .retR SimSym.mid = some (.mid, .acc, true) from rfl)
    ((List.replicate n SimSym.bk).reverse ++ SimSym.endL :: List.replicate g SimSym.bk)
    SimSym.bk
    (List.replicate j SimSym.bk ++
      ((encVal v).reverse ++ SimSym.endR :: List.replicate t SimSym.bk))
  refine ⟨⟨.acc, SimSym.mid :: ((List.replicate n SimSym.bk).reverse ++
      SimSym.endL :: List.replicate g SimSym.bk), SimSym.bk,
      List.replicate j SimSym.bk ++
        ((encVal v).reverse ++ SimSym.endR :: List.replicate t SimSym.bk)⟩, rfl, ?_⟩
  refine Reach.trans r1 ?_
  exact Reach.single ((congrArg lstep (by simp [List.replicate_succ])).trans r2)

/-! ### The `fix` pop -/

/-- **Dropping a spent `fix` frame**: from `fxDropL` on `endL`, re-cross the
gap, erase the kept header stepping left, and walk home to rest – the header
cell joins the gap. -/
theorem fix_drop {p : CPos c} (n g : ℕ) {w' : List (SimSym c)} (R : List (SimSym c)) :
    Reach ⟨.fxDropL, List.replicate g SimSym.bk, SimSym.endL,
        List.replicate n SimSym.bk ++ SimSym.hFix p :: (w' ++ SimSym.mid :: R)⟩
      ⟨.retL, List.replicate g SimSym.bk, SimSym.endL,
        List.replicate (n + 1) SimSym.bk ++ (w' ++ SimSym.mid :: R)⟩ := by
  -- re-cross the gap to the kept header
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .fxDropL SimSym.endL = some (.endL, .fxDropR, true) from rfl)
    (P := fun σ => σ = SimSym.bk) (fun τ hτ => pass_fxDropR hτ)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    (SimSym.hFix p) (List.replicate g SimSym.bk) (w' ++ SimSym.mid :: R)
  -- erase the header and walk home
  have r2 := reach_step_then_walkL
    (show simStep (c := c) .fxDropR (SimSym.hFix p) = some (.bk, .retL, false) from rfl)
    (P := fun σ => σ ≠ SimSym.endL) (fun τ hτ => pass_retL hτ)
    (List.replicate n SimSym.bk)
    (fun τ hτ => by simp [List.eq_of_mem_replicate hτ])
    SimSym.endL (List.replicate g SimSym.bk) (w' ++ SimSym.mid :: R)
  refine Reach.trans r1 ?_
  refine Reach.trans (Reach.cast (by simp) rfl r2) ?_
  exact Reach.cast rfl (by simp [replicate_glue]) (Reach.refl _)

/-- **Popping a `fix` frame, zero or empty flag**: the wake-up walk keeps the
header and `fxGo` inspects the last letter of the value at `endR` – a blank
for the empty value, restored after a probe step, or the head block's lone
separator, consumed as the new `endR` – then `fxDropL`/`fxDropR` drop the
kept frame and return to rest over the tail of the value. -/
theorem pop_fix_stop {p : CPos c} {k' : PCont c} (n : ℕ) {w' : List (SimSym c)}
    (hw' : FrameSeg k' w') (g : ℕ) {v : List ℕ} (hv : v.headI = 0) (j t : ℕ) :
    ∃ t', Reach (restCfg g (List.replicate n SimSym.bk ++ SimSym.hFix p :: w') v j t)
      (restCfg g (List.replicate (n + 1) SimSym.bk ++ w') v.tail j t') := by
  -- wake up: cross the gap to the header
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .retL SimSym.endL = some (.endL, .retR, true) from rfl)
    (P := fun σ => σ = SimSym.bk) (fun τ hτ => by rw [hτ]; rfl)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    (SimSym.hFix p) (List.replicate g SimSym.bk) (w' ++ SimSym.mid :: valR v j t)
  -- keep the header, walk right to endR
  have r2 := reach_step_then_walkR
    (show simStep (c := c) .retR (SimSym.hFix p) = some (.hFix p, .fxGo p, true) from rfl)
    (P := fun σ => σ ≠ SimSym.endR) (fun τ hτ => pass_fxGo hτ)
    (w' ++ SimSym.mid :: (List.replicate (j + 1) SimSym.bk ++ (encVal v).reverse))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact ((hw'.mem_frameSym τ hτ).ne).2.2.1
      · rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        rcases List.mem_append.mp hτ with hτ | hτ
        · simp [List.eq_of_mem_replicate hτ]
        · rcases mem_encVal (List.mem_reverse.mp hτ) with rfl | rfl <;> simp)
    SimSym.endR
    ((List.replicate n SimSym.bk).reverse ++ SimSym.endL :: List.replicate g SimSym.bk)
    (List.replicate t SimSym.bk)
  rcases v with - | ⟨n₀, vs⟩
  · -- empty value: probe the blank right of the erased endR, restore it
    refine ⟨t, ?_⟩
    have r3 := lstep_left
      (show simStep (c := c) (.fxGo p) SimSym.endR = some (.bk, .fxLook p, false) from rfl)
      SimSym.bk
      (List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++ SimSym.hFix p ::
        (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)))
      (List.replicate t SimSym.bk)
    have r4 := lstep_right
      (show simStep (c := c) (.fxLook p) SimSym.bk = some (.bk, .fxRest p, true) from rfl)
      (List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++ SimSym.hFix p ::
        (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)))
      SimSym.bk (List.replicate t SimSym.bk)
    have r5 := lstep_left
      (show simStep (c := c) (.fxRest p) SimSym.bk = some (.endR, .fxDropL, false) from rfl)
      SimSym.bk
      (List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++ SimSym.hFix p ::
        (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)))
      (List.replicate t SimSym.bk)
    -- walk left to endL, then drop the frame
    have r6 := reach_walkL (P := fun σ => σ ≠ SimSym.endL) (fun σ hσ => pass_fxDropL hσ)
      (List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++ SimSym.hFix p ::
        List.replicate n SimSym.bk))
      (by
        intro τ hτ
        rcases List.mem_append.mp hτ with hτ | hτ
        · simp [List.eq_of_mem_replicate hτ]
        rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        rcases List.mem_append.mp hτ with hτ | hτ
        · exact ((hw'.mem_frameSym τ (List.mem_reverse.mp hτ)).ne).1
        rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        · simp [List.eq_of_mem_replicate hτ])
      (s := SimSym.bk) (by simp) SimSym.endL (List.replicate g SimSym.bk)
      (SimSym.endR :: List.replicate t SimSym.bk)
    have r7 := fix_drop (p := p) n g (w' := w')
      (List.replicate j SimSym.bk ++ SimSym.bk :: SimSym.endR :: List.replicate t SimSym.bk)
    refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
    refine Reach.trans (Reach.cast (by simp [valR]) rfl r2) ?_
    refine Reach.head ((congrArg lstep (by simp [List.replicate_succ, replicate_glue])).trans r3) ?_
    refine Reach.head r4 ?_
    refine Reach.head r5 ?_
    refine Reach.trans (Reach.cast (by simp) rfl r6) ?_
    refine Reach.trans (Reach.cast (by simp) rfl r7) ?_
    exact Reach.cast rfl (by simp [restCfg, valR, List.replicate_succ, replicate_glue])
      (Reach.refl _)
  · -- head block is a lone separator: consume it as the new endR
    obtain rfl : n₀ = 0 := hv
    refine ⟨t + 1, ?_⟩
    have r3 := lstep_left
      (show simStep (c := c) (.fxGo p) SimSym.endR = some (.bk, .fxLook p, false) from rfl)
      SimSym.com
      (encVal vs ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: (w'.reverse ++
        SimSym.hFix p ::
          (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk))))
      (List.replicate t SimSym.bk)
    -- the separator becomes the new endR; walk left to endL and drop the frame
    have r4 := reach_step_walkL (P := fun σ => σ ≠ SimSym.endL)
      (show simStep (c := c) (.fxLook p) SimSym.com = some (.endR, .fxDropL, false) from rfl)
      (fun σ hσ => pass_fxDropL hσ)
      (encVal vs ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: (w'.reverse ++
        SimSym.hFix p :: List.replicate n SimSym.bk)))
      (by
        intro τ hτ
        rcases List.mem_append.mp hτ with hτ | hτ
        · rcases mem_encVal hτ with rfl | rfl <;> simp
        rcases List.mem_append.mp hτ with hτ | hτ
        · simp [List.eq_of_mem_replicate hτ]
        rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        rcases List.mem_append.mp hτ with hτ | hτ
        · exact ((hw'.mem_frameSym τ (List.mem_reverse.mp hτ)).ne).1
        rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        · simp [List.eq_of_mem_replicate hτ])
      SimSym.endL (List.replicate g SimSym.bk) (SimSym.bk :: List.replicate t SimSym.bk)
    have r5 := fix_drop (p := p) n g (w' := w')
      (List.replicate (j + 1) SimSym.bk ++ (encVal vs).reverse ++
        SimSym.endR :: SimSym.bk :: List.replicate t SimSym.bk)
    refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
    refine Reach.trans (Reach.cast (by simp [valR, encNum]) rfl r2) ?_
    refine Reach.head ((congrArg lstep (by simp [encNum])).trans r3) ?_
    refine Reach.trans (Reach.cast (by simp) rfl r4) ?_
    refine Reach.trans (Reach.cast (by simp) rfl r5) ?_
    exact Reach.cast rfl (by simp [restCfg, valR, List.replicate_succ])
      (Reach.refl _)

/-- **Popping a `fix` frame, positive flag**: `fxGo` finds a digit at `endR`,
`fxOnes` erases the head block down to its separator – which becomes the new
`endR` – and `nSeekL` walks back to `mid` to dispatch the body over the tail
of the value, the frame kept in place. -/
theorem pop_fix_go {p : CPos c} {k' : PCont c} (n : ℕ) {w' : List (SimSym c)}
    (hw' : FrameSeg k' w') (g : ℕ) {v : List ℕ} {y : ℕ} (hv : v.headI = y + 1) (j t : ℕ) :
    ∃ t', Reach (restCfg g (List.replicate n SimSym.bk ++ SimSym.hFix p :: w') v j t)
      (atMid (.nSeekL p) g (List.replicate n SimSym.bk ++ SimSym.hFix p :: w') v.tail j t') := by
  rcases v with - | ⟨n₀, vs⟩
  · exact absurd hv (by simp)
  obtain rfl : n₀ = y + 1 := hv
  refine ⟨y + 1 + 1 + t, ?_⟩
  -- wake up: cross the gap to the header
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .retL SimSym.endL = some (.endL, .retR, true) from rfl)
    (P := fun σ => σ = SimSym.bk) (fun τ hτ => by rw [hτ]; rfl)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    (SimSym.hFix p) (List.replicate g SimSym.bk)
    (w' ++ SimSym.mid :: valR ((y + 1) :: vs) j t)
  -- keep the header, walk right to endR
  have r2 := reach_step_then_walkR
    (show simStep (c := c) .retR (SimSym.hFix p) = some (.hFix p, .fxGo p, true) from rfl)
    (P := fun σ => σ ≠ SimSym.endR) (fun τ hτ => pass_fxGo hτ)
    (w' ++ SimSym.mid :: (List.replicate (j + 1) SimSym.bk ++
      ((encVal vs).reverse ++ SimSym.com :: List.replicate (y + 1) SimSym.one)))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact ((hw'.mem_frameSym τ hτ).ne).2.2.1
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · simp [List.eq_of_mem_replicate hτ]
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases mem_encVal (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      · simp [List.eq_of_mem_replicate hτ])
    SimSym.endR
    ((List.replicate n SimSym.bk).reverse ++ SimSym.endL :: List.replicate g SimSym.bk)
    (List.replicate t SimSym.bk)
  -- erase endR, look left: a digit
  have r3 := lstep_left
    (show simStep (c := c) (.fxGo p) SimSym.endR = some (.bk, .fxLook p, false) from rfl)
    SimSym.one
    (List.replicate y SimSym.one ++ SimSym.com :: (encVal vs ++
      (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: (w'.reverse ++ SimSym.hFix p ::
        (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)))))
    (List.replicate t SimSym.bk)
  -- erase the remaining digits down to the separator
  have r4 := reach_step_walkL_map (P := fun σ => σ = SimSym.one) (f := fun _ => SimSym.bk)
    (show simStep (c := c) (.fxLook p) SimSym.one = some (.bk, .fxOnes p, false) from rfl)
    (fun σ hσ => pass_fxOnes hσ)
    (List.replicate y SimSym.one) (fun σ hσ => List.eq_of_mem_replicate hσ)
    SimSym.com
    (encVal vs ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: (w'.reverse ++
      SimSym.hFix p ::
        (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk))))
    (SimSym.bk :: List.replicate t SimSym.bk)
  -- the separator becomes the new endR; seek mid to dispatch the body
  have r5 := reach_step_walkL (P := fun σ => σ ≠ SimSym.mid)
    (show simStep (c := c) (.fxOnes p) SimSym.com = some (.endR, .nSeekL p, false) from rfl)
    (fun σ hσ => pass_nSeekL hσ)
    (encVal vs ++ List.replicate (j + 1) SimSym.bk)
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases mem_encVal hτ with rfl | rfl <;> simp
      · simp [List.eq_of_mem_replicate hτ])
    SimSym.mid
    (w'.reverse ++ SimSym.hFix p ::
      (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk))
    (List.replicate y SimSym.bk ++ SimSym.bk :: SimSym.bk :: List.replicate t SimSym.bk)
  refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
  refine Reach.trans (Reach.cast (by simp [valR, encNum]) rfl r2) ?_
  refine Reach.head ((congrArg lstep (by simp [List.replicate_succ, replicate_glue])).trans r3) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r4) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r5) ?_
  refine Reach.cast rfl ?_ (Reach.refl _)
  simp [atMid, valR, midL, replicate_glue]

/-! ### The `cons₂` pop -/

/-- Merging two adjacent blank runs – the shape the frame erasures leave. -/
theorem replicate_merge (a b : ℕ) (s : SimSym c) (l : List (SimSym c)) :
    List.replicate a s ++ (List.replicate b s ++ l) = List.replicate (a + b) s ++ l := by
  simp [← List.append_assoc]

/-- **One round of the `cons₂` transfer**: from the header, scan to the end
of the remaining content, step back onto its last digit, erase it, carry it
to `endR`, append it by the endR-shift and walk back to the header. The
erased zone right of the content – abstracted, with the letter after it, into
`x :: Y'` – grows by one blank, the appended run by one digit. -/
theorem pp_iter {x : SimSym c} {Y' : List (SimSym c)}
    (hx1 : x ≠ SimSym.one) (hx2 : x ≠ SimSym.com)
    (hY : ∀ σ ∈ x :: Y', σ ≠ SimSym.endR ∧ σ ≠ SimSym.endL)
    {C : List (SimSym c)} (hC : ∀ σ ∈ C, σ = SimSym.one ∨ σ = SimSym.com)
    (n g a m : ℕ) :
    Reach
      ⟨.ppFind, List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk,
        SimSym.hCons₂,
        (C ++ [SimSym.one]) ++ x :: Y' ++
          SimSym.com :: List.replicate a SimSym.one ++
          SimSym.endR :: List.replicate m SimSym.bk⟩
      ⟨.ppFind, List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk,
        SimSym.hCons₂,
        C ++ SimSym.bk :: x :: Y' ++
          SimSym.com :: List.replicate (a + 1) SimSym.one ++
          SimSym.endR :: List.replicate (m - 1) SimSym.bk⟩ := by
  -- scan over the remaining content to its end
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .ppFind SimSym.hCons₂ = some (.hCons₂, .ppScan, true) from rfl)
    (P := fun σ => σ = SimSym.one ∨ σ = SimSym.com) (fun τ hτ => pass_ppScan hτ)
    (C ++ [SimSym.one])
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact hC τ hτ
      · exact Or.inl (List.mem_singleton.mp hτ))
    x (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)
    (Y' ++ SimSym.com :: List.replicate a SimSym.one ++
      SimSym.endR :: List.replicate m SimSym.bk)
  -- step back onto the last digit
  have r2 := lstep_left (stop_ppScan hx1 hx2) SimSym.one
    (C.reverse ++ SimSym.hCons₂ ::
      (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk))
    (Y' ++ SimSym.com :: List.replicate a SimSym.one ++
      SimSym.endR :: List.replicate m SimSym.bk)
  -- erase it and carry right to endR
  have r3 := reach_step_then_walkR
    (show simStep (c := c) .ppLast SimSym.one = some (.bk, .ppCar, true) from rfl)
    (P := fun σ => σ ≠ SimSym.endR) (fun τ hτ => pass_ppCar hτ)
    (x :: Y' ++ SimSym.com :: List.replicate a SimSym.one)
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact (hY τ hτ).1
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      · simp [List.eq_of_mem_replicate hτ])
    SimSym.endR
    (C.reverse ++ SimSym.hCons₂ ::
      (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk))
    (List.replicate m SimSym.bk)
  -- append it over endR, re-write endR one cell right
  have r4 := lstep_right_pad
    (show simStep (c := c) .ppCar SimSym.endR = some (.one, .ppCarS, true) from rfl)
    ((x :: Y' ++ SimSym.com :: List.replicate a SimSym.one).reverse ++
      SimSym.bk :: (C.reverse ++ SimSym.hCons₂ ::
        (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk))) m
  have r5 := lstep_left
    (show simStep (c := c) .ppCarS SimSym.bk = some (.endR, .ppBack, false) from rfl)
    SimSym.one
    ((x :: Y' ++ SimSym.com :: List.replicate a SimSym.one).reverse ++
      SimSym.bk :: (C.reverse ++ SimSym.hCons₂ ::
        (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)))
    (List.replicate (m - 1) SimSym.bk)
  -- walk back to endL
  have r6 := reach_walkL (P := fun σ => σ ≠ SimSym.endL) (fun σ hσ => pass_ppBack hσ)
    (List.replicate a SimSym.one ++ SimSym.com :: (Y'.reverse ++ x ::
      SimSym.bk :: (C.reverse ++ SimSym.hCons₂ :: List.replicate n SimSym.bk)))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · simp [List.eq_of_mem_replicate hτ]
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact (hY τ (by simp [List.mem_reverse.mp hτ])).2
      rcases List.mem_cons.mp hτ with rfl | hτ
      · exact (hY _ (by simp)).2
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases hC τ (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      · simp [List.eq_of_mem_replicate hτ])
    (s := SimSym.one) (by simp) SimSym.endL (List.replicate g SimSym.bk)
    (SimSym.endR :: List.replicate (m - 1) SimSym.bk)
  -- re-cross the gap to the header
  have r7 := reach_step_then_walkR
    (show simStep (c := c) .ppBack SimSym.endL = some (.endL, .ppFind, true) from rfl)
    (P := fun σ => σ = SimSym.bk) (fun τ hτ => pass_ppFind hτ)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    SimSym.hCons₂ (List.replicate g SimSym.bk)
    (C ++ SimSym.bk :: x :: Y' ++ SimSym.com :: List.replicate a SimSym.one ++
      SimSym.one :: SimSym.endR :: List.replicate (m - 1) SimSym.bk)
  refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
  refine Reach.head ((congrArg lstep (by simp)).trans r2) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r3) ?_
  refine Reach.head r4 ?_
  refine Reach.head r5 ?_
  refine Reach.trans (Reach.cast (by simp) rfl r6) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r7) ?_
  exact Reach.cast rfl (by simp [replicate_glue]) (Reach.refl _)

/-- **The `cons₂` transfer loop**: the rounds of
`DescriptiveComplexity.HaltHard.pp_iter`, iterated over the digits of the
head block – the rightmost content letters, the frame being mirrored. -/
theorem pp_loop {C : List (SimSym c)} (hC : ∀ σ ∈ C, σ = SimSym.one ∨ σ = SimSym.com)
    (n g : ℕ) : ∀ (y : ℕ) {x : SimSym c} {Y' : List (SimSym c)},
    x ≠ SimSym.one → x ≠ SimSym.com →
    (∀ σ ∈ x :: Y', σ ≠ SimSym.endR ∧ σ ≠ SimSym.endL) → ∀ (a m : ℕ),
    Reach
      ⟨.ppFind, List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk,
        SimSym.hCons₂,
        (C ++ List.replicate y SimSym.one) ++ x :: Y' ++
          SimSym.com :: List.replicate a SimSym.one ++
          SimSym.endR :: List.replicate m SimSym.bk⟩
      ⟨.ppFind, List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk,
        SimSym.hCons₂,
        C ++ (List.replicate y SimSym.bk ++ x :: Y') ++
          SimSym.com :: List.replicate (a + y) SimSym.one ++
          SimSym.endR :: List.replicate (m - y) SimSym.bk⟩ := by
  intro y
  induction y with
  | zero =>
    intro x Y' _ _ _ a m
    exact Reach.cast (by simp) rfl (Reach.refl _)
  | succ y ih =>
    intro x Y' hx1 hx2 hY a m
    have r1 := pp_iter hx1 hx2 hY (C := C ++ List.replicate y SimSym.one)
      (by
        intro σ hσ
        rcases List.mem_append.mp hσ with hσ | hσ
        · exact hC σ hσ
        · exact Or.inl (List.eq_of_mem_replicate hσ))
      n g a m
    have r2 := ih (x := SimSym.bk) (Y' := x :: Y') (by simp) (by simp)
      (by
        intro σ hσ
        rcases List.mem_cons.mp hσ with rfl | hσ
        · exact ⟨by simp, by simp⟩
        · exact hY σ hσ)
      (a + 1) (m - 1)
    refine Reach.trans (Reach.cast (by simp [List.replicate_succ']) rfl r1) ?_
    refine Reach.cast (by simp) ?_ r2
    have ha : a + 1 + y = a + (y + 1) := by omega
    have hm : m - 1 - y = m - (y + 1) := by omega
    simp [ha, hm, replicate_glue]

/-- **Discarding the spent `cons₂` frame**: the digits gone, the scan finds
the head block's separator last; `ppLast` erases it, `ppKill` sweeps the rest
of the content into blanks, erases the header, and `retL` walks home. -/
theorem pp_kill {x : SimSym c} (e : ℕ) {T' : List (SimSym c)}
    (hx1 : x ≠ SimSym.one) (hx2 : x ≠ SimSym.com)
    {B : List (SimSym c)} (hB : ∀ σ ∈ B, σ = SimSym.one ∨ σ = SimSym.com)
    (n g : ℕ) :
    Reach
      ⟨.ppFind, List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk,
        SimSym.hCons₂,
        (B ++ [SimSym.com]) ++ (List.replicate e SimSym.bk ++ x :: T')⟩
      ⟨.retL, List.replicate g SimSym.bk, SimSym.endL,
        List.replicate (n + 1 + B.length + 1) SimSym.bk ++
          (List.replicate e SimSym.bk ++ x :: T')⟩ := by
  obtain ⟨x₂, X₂, h₂, hx₂1, hx₂2⟩ := bk_head_split e hx1 hx2 T'
  -- scan over the remaining content to its end
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .ppFind SimSym.hCons₂ = some (.hCons₂, .ppScan, true) from rfl)
    (P := fun σ => σ = SimSym.one ∨ σ = SimSym.com) (fun τ hτ => pass_ppScan hτ)
    (B ++ [SimSym.com])
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact hB τ hτ
      · exact Or.inr (List.mem_singleton.mp hτ))
    x₂ (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk) X₂
  -- step back onto the separator
  have r2 := lstep_left (stop_ppScan hx₂1 hx₂2) SimSym.com
    (B.reverse ++ SimSym.hCons₂ ::
      (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)) X₂
  -- erase it and sweep the rest of the content into blanks
  have r3 := reach_step_walkL_map
    (P := fun σ => σ = SimSym.one ∨ σ = SimSym.com) (f := fun _ => SimSym.bk)
    (show simStep (c := c) .ppLast SimSym.com = some (.bk, .ppKill, false) from rfl)
    (fun σ hσ => pass_ppKill hσ)
    B.reverse (fun σ hσ => hB σ (List.mem_reverse.mp hσ))
    SimSym.hCons₂
    (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)
    (x₂ :: X₂)
  -- erase the header and walk home
  have r4 := reach_step_then_walkL
    (show simStep (c := c) .ppKill SimSym.hCons₂ = some (.bk, .retL, false) from rfl)
    (P := fun σ => σ ≠ SimSym.endL) (fun τ hτ => pass_retL hτ)
    (List.replicate n SimSym.bk)
    (fun τ hτ => by simp [List.eq_of_mem_replicate hτ])
    SimSym.endL (List.replicate g SimSym.bk)
    ((B.reverse.map fun _ => SimSym.bk).reverse ++ SimSym.bk :: x₂ :: X₂)
  refine Reach.trans (Reach.cast (by rw [h₂]) rfl r1) ?_
  refine Reach.head ((congrArg lstep (by simp)).trans r2) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r3) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r4) ?_
  refine Reach.cast rfl ?_ (Reach.refl _)
  rw [h₂]
  simp [replicate_glue, replicate_merge, List.map_const']
  omega

/-- **Popping a `cons₂` frame**: the wake-up walk keeps the header; `ppGo`
appends the new block's separator at `endR` and `ppBack`/`ppFind` return to
the header; the transfer loop moves the digits of the frame's head block –
the rightmost content letters, the frame being mirrored – one by one to
`endR`; and once the separator is reached the rest of the frame is swept into
blanks and the machine returns to rest, the head of the stored value now
prepended to the value. -/
theorem pop_cons₂ {k' : PCont c} (ns : List ℕ) (n : ℕ) {w' : List (SimSym c)}
    (hw' : FrameSeg k' w') (g : ℕ) (v : List ℕ) (j t : ℕ) :
    ∃ t', Reach
      (restCfg g (List.replicate n SimSym.bk ++
        SimSym.hCons₂ :: ((encVal ns).reverse ++ w')) v j t)
      (restCfg g (List.replicate (n + (encVal (c := c) ns).length + 1) SimSym.bk ++ w')
        (ns.headI :: v) j t') := by
  obtain ⟨x, X, hsplit, hx1, hx2⟩ :=
    hw'.head_split (List.replicate (j + 1) SimSym.bk ++ (encVal v).reverse)
  have hsplit' : ∀ Z : List (SimSym c), x :: (X ++ Z) =
      w' ++ SimSym.mid :: (List.replicate (j + 1) SimSym.bk ++ ((encVal v).reverse ++ Z)) := by
    intro Z
    have h := congrArg (· ++ Z) hsplit
    simpa using h.symm
  have hY : ∀ σ ∈ x :: X, σ ≠ SimSym.endR ∧ σ ≠ SimSym.endL := by
    rw [← hsplit]
    intro σ hσ
    rcases List.mem_append.mp hσ with hσ | hσ
    · exact ⟨((hw'.mem_frameSym σ hσ).ne).2.2.1, ((hw'.mem_frameSym σ hσ).ne).1⟩
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact ⟨by simp, by simp⟩
    rcases List.mem_append.mp hσ with hσ | hσ
    · simp [List.eq_of_mem_replicate hσ]
    · rcases mem_encVal (List.mem_reverse.mp hσ) with rfl | rfl <;> exact ⟨by simp, by simp⟩
  -- wake up: cross the gap to the header
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .retL SimSym.endL = some (.endL, .retR, true) from rfl)
    (P := fun σ => σ = SimSym.bk) (fun τ hτ => by rw [hτ]; rfl)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    SimSym.hCons₂ (List.replicate g SimSym.bk)
    ((encVal ns).reverse ++ w' ++ SimSym.mid :: valR v j t)
  -- keep the header, walk right to endR
  have r2 := reach_step_then_walkR
    (show simStep (c := c) .retR SimSym.hCons₂ = some (.hCons₂, .ppGo, true) from rfl)
    (P := fun σ => σ ≠ SimSym.endR) (fun τ hτ => pass_ppGo hτ)
    ((encVal ns).reverse ++ w' ++ SimSym.mid ::
      (List.replicate (j + 1) SimSym.bk ++ (encVal v).reverse))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases List.mem_append.mp hτ with hτ | hτ
        · rcases mem_encVal (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
        · exact ((hw'.mem_frameSym τ hτ).ne).2.2.1
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · simp [List.eq_of_mem_replicate hτ]
      · rcases mem_encVal (List.mem_reverse.mp hτ) with rfl | rfl <;> simp)
    SimSym.endR
    ((List.replicate n SimSym.bk).reverse ++ SimSym.endL :: List.replicate g SimSym.bk)
    (List.replicate t SimSym.bk)
  -- append the separator over endR, re-write endR one cell right
  have r3 := lstep_right_pad
    (show simStep (c := c) .ppGo SimSym.endR = some (.com, .ppShift, true) from rfl)
    (((encVal ns).reverse ++ w' ++ SimSym.mid ::
      (List.replicate (j + 1) SimSym.bk ++ (encVal v).reverse)).reverse ++
      SimSym.hCons₂ ::
        ((List.replicate n SimSym.bk).reverse ++ SimSym.endL :: List.replicate g SimSym.bk)) t
  have r4 := lstep_left
    (show simStep (c := c) .ppShift SimSym.bk = some (.endR, .ppBack, false) from rfl)
    SimSym.com
    (((encVal ns).reverse ++ w' ++ SimSym.mid ::
      (List.replicate (j + 1) SimSym.bk ++ (encVal v).reverse)).reverse ++
      SimSym.hCons₂ ::
        ((List.replicate n SimSym.bk).reverse ++ SimSym.endL :: List.replicate g SimSym.bk))
    (List.replicate (t - 1) SimSym.bk)
  -- walk back to endL
  have r5 := reach_walkL (P := fun σ => σ ≠ SimSym.endL) (fun σ hσ => pass_ppBack hσ)
    (((encVal ns).reverse ++ w' ++ SimSym.mid ::
      (List.replicate (j + 1) SimSym.bk ++ (encVal v).reverse)).reverse ++
      SimSym.hCons₂ :: List.replicate n SimSym.bk)
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rw [List.mem_reverse] at hτ
        rcases List.mem_append.mp hτ with hτ | hτ
        · rcases List.mem_append.mp hτ with hτ | hτ
          · rcases mem_encVal (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
          · exact ((hw'.mem_frameSym τ hτ).ne).1
        rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        rcases List.mem_append.mp hτ with hτ | hτ
        · simp [List.eq_of_mem_replicate hτ]
        · rcases mem_encVal (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      · simp [List.eq_of_mem_replicate hτ])
    (s := SimSym.com) (by simp) SimSym.endL (List.replicate g SimSym.bk)
    (SimSym.endR :: List.replicate (t - 1) SimSym.bk)
  -- re-cross the gap to the header, the separator now appended
  have r6 := reach_step_then_walkR
    (show simStep (c := c) .ppBack SimSym.endL = some (.endL, .ppFind, true) from rfl)
    (P := fun σ => σ = SimSym.bk) (fun τ hτ => pass_ppFind hτ)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    SimSym.hCons₂ (List.replicate g SimSym.bk)
    ((encVal ns).reverse ++ w' ++ SimSym.mid ::
      (List.replicate (j + 1) SimSym.bk ++ (encVal v).reverse) ++
      SimSym.com :: SimSym.endR :: List.replicate (t - 1) SimSym.bk)
  rcases ns with - | ⟨n₁, ns'⟩
  · -- empty stored value: the scan stops at once, the header goes, rest
    refine ⟨t - 1, ?_⟩
    have e1 := reach_step_then_walkR
      (show simStep (c := c) .ppFind SimSym.hCons₂ = some (.hCons₂, .ppScan, true) from rfl)
      (P := fun σ => σ = SimSym.one ∨ σ = SimSym.com) (fun τ hτ => pass_ppScan hτ)
      [] (by simp) x
      (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)
      (X ++ SimSym.com :: SimSym.endR :: List.replicate (t - 1) SimSym.bk)
    have e2 := lstep_left (stop_ppScan hx1 hx2) SimSym.hCons₂
      (List.replicate n SimSym.bk ++ SimSym.endL :: List.replicate g SimSym.bk)
      (X ++ SimSym.com :: SimSym.endR :: List.replicate (t - 1) SimSym.bk)
    have e3 := reach_step_then_walkL
      (show simStep (c := c) .ppLast SimSym.hCons₂ = some (.bk, .retL, false) from rfl)
      (P := fun σ => σ ≠ SimSym.endL) (fun τ hτ => pass_retL hτ)
      (List.replicate n SimSym.bk)
      (fun τ hτ => by simp [List.eq_of_mem_replicate hτ])
      SimSym.endL (List.replicate g SimSym.bk)
      (x :: (X ++ SimSym.com :: SimSym.endR :: List.replicate (t - 1) SimSym.bk))
    refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
    refine Reach.trans (Reach.cast (by simp [valR]) rfl r2) ?_
    refine Reach.head r3 ?_
    refine Reach.head r4 ?_
    refine Reach.trans (Reach.cast (by simp) rfl r5) ?_
    refine Reach.trans (Reach.cast (by simp) rfl r6) ?_
    refine Reach.trans (Reach.cast (by simp [hsplit']) rfl e1) ?_
    refine Reach.head ((congrArg lstep (by simp)).trans e2) ?_
    refine Reach.trans (Reach.cast (by simp) rfl e3) ?_
    refine Reach.cast rfl ?_ (Reach.refl _)
    simp [restCfg, valR, encNum, replicate_glue, hsplit']
  · -- transfer the digits of the head block, then discard the frame
    refine ⟨t - 1 - n₁, ?_⟩
    have hB : ∀ σ ∈ (encVal (c := c) ns').reverse, σ = SimSym.one ∨ σ = SimSym.com :=
      fun σ hσ => mem_encVal (List.mem_reverse.mp hσ)
    have rloop := pp_loop (C := (encVal ns').reverse ++ [SimSym.com])
      (by
        intro σ hσ
        rcases List.mem_append.mp hσ with hσ | hσ
        · exact hB σ hσ
        · exact Or.inr (List.mem_singleton.mp hσ))
      n g n₁ hx1 hx2 hY 0 (t - 1)
    have rkill := pp_kill (x := x) n₁ hx1 hx2 hB n g
      (T' := X ++ SimSym.com :: List.replicate (0 + n₁) SimSym.one ++
        SimSym.endR :: List.replicate (t - 1 - n₁) SimSym.bk)
    refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
    refine Reach.trans (Reach.cast (by simp [valR]) rfl r2) ?_
    refine Reach.head r3 ?_
    refine Reach.head r4 ?_
    refine Reach.trans (Reach.cast (by simp) rfl r5) ?_
    refine Reach.trans (Reach.cast (by simp) rfl r6) ?_
    refine Reach.trans (Reach.cast (by simp [encNum, hsplit']) rfl rloop) ?_
    refine Reach.trans (Reach.cast (by simp) rfl rkill) ?_
    refine Reach.cast rfl ?_ (Reach.refl _)
    rw [show n + (encVal (c := c) (n₁ :: ns')).length + 1 =
        n + 1 + ((encVal (c := c) ns').reverse).length + 1 + n₁ by simp [encNum]; omega]
    simp [restCfg, valR, encNum, replicate_merge, hsplit']

/-! ### The `cons₁` pop, phase one: the value moves into a fresh `cons₂` frame -/

/-- **One round of the value move**: `swGo` sits on `endR`; the marker is
erased, the last value letter peeked, `endR` slides onto its cell, the letter
is carried over the whole tape – the middle abstracted into `M` – to `endL`
and written by the endL-shift, and `swGo` walks back onto `endR`. Stated over
an abstract carry state so the digit and separator instances share the
proof. -/
theorem sw_iter {u : SimSym c} {Qcar : SimQ c}
    (hu : u = SimSym.one ∨ u = SimSym.com)
    (h1 : simStep (c := c) .swPeek u = some (.endR, Qcar, false))
    (h2 : ∀ τ : SimSym c, τ ≠ SimSym.endL → simStep Qcar τ = some (τ, Qcar, false))
    (h3 : simStep Qcar SimSym.endL = some (u, .swEndS, false))
    {M : List (SimSym c)} (hM : ∀ σ ∈ M, σ ≠ SimSym.endL ∧ σ ≠ SimSym.endR)
    {V : List (SimSym c)} (hV : ∀ σ ∈ V, σ = SimSym.one ∨ σ = SimSym.com)
    {D : List (SimSym c)} (hD : ∀ σ ∈ D, σ = SimSym.one ∨ σ = SimSym.com)
    (g' m : ℕ) :
    Reach
      ⟨.swGo, (V ++ [u]).reverse ++
          (M ++ (D.reverse ++ SimSym.endL :: List.replicate g' SimSym.bk)),
        SimSym.endR, List.replicate m SimSym.bk⟩
      ⟨.swGo, V.reverse ++
          (M ++ ((u :: D).reverse ++ SimSym.endL :: List.replicate (g' - 1) SimSym.bk)),
        SimSym.endR, List.replicate (m + 1) SimSym.bk⟩ := by
  -- erase endR, stepping left onto the last value letter
  have r1 := lstep_left
    (show simStep (c := c) .swGo SimSym.endR = some (.bk, .swPeek, false) from rfl)
    u (V.reverse ++ (M ++ (D.reverse ++ SimSym.endL :: List.replicate g' SimSym.bk)))
    (List.replicate m SimSym.bk)
  -- endR slides onto its cell; carry the letter home to endL
  have r2 := reach_step_then_walkL h1 h2
    (V.reverse ++ M ++ D.reverse)
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases List.mem_append.mp hτ with hτ | hτ
        · rcases hV τ (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
        · exact (hM τ hτ).1
      · rcases hD τ (List.mem_reverse.mp hτ) with rfl | rfl <;> simp)
    SimSym.endL (List.replicate g' SimSym.bk)
    (SimSym.bk :: List.replicate m SimSym.bk)
  -- write it over endL, re-write endL one cell left
  have r3 := lstep_left_pad h3 g'
    ((V.reverse ++ M ++ D.reverse).reverse ++
      SimSym.endR :: SimSym.bk :: List.replicate m SimSym.bk)
  have r4 := lstep_right
    (show simStep (c := c) .swEndS SimSym.bk = some (.endL, .swGo, true) from rfl)
    (List.replicate (g' - 1) SimSym.bk) u
    ((V.reverse ++ M ++ D.reverse).reverse ++
      SimSym.endR :: SimSym.bk :: List.replicate m SimSym.bk)
  -- walk right back onto endR
  have r5 := reach_walkR (P := fun σ => σ ≠ SimSym.endR) (fun σ hσ => pass_swGo hσ)
    (D ++ M.reverse ++ V)
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases List.mem_append.mp hτ with hτ | hτ
        · rcases hD τ hτ with rfl | rfl <;> simp
        · exact (hM τ (List.mem_reverse.mp hτ)).2
      · rcases hV τ hτ with rfl | rfl <;> simp)
    (s := u) (by rcases hu with rfl | rfl <;> simp)
    (SimSym.endL :: List.replicate (g' - 1) SimSym.bk) SimSym.endR
    (SimSym.bk :: List.replicate m SimSym.bk)
  refine Reach.head ((congrArg lstep (by simp)).trans r1) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r2) ?_
  refine Reach.head r3 ?_
  refine Reach.head r4 ?_
  refine Reach.trans (Reach.cast (by simp) rfl r5) ?_
  exact Reach.cast rfl (by simp [List.replicate_succ]) (Reach.refl _)

/-- **The value move, iterated**: the whole value crosses into the region at
`endL`, mirrored – consumed at `endR`, written by endL-shifts – while the
left blanks shrink and the right pad grows by its length. -/
theorem sw_loop {M : List (SimSym c)}
    (hM : ∀ σ ∈ M, σ ≠ SimSym.endL ∧ σ ≠ SimSym.endR) :
    ∀ (V : List (SimSym c)), (∀ σ ∈ V, σ = SimSym.one ∨ σ = SimSym.com) →
    ∀ {D : List (SimSym c)}, (∀ σ ∈ D, σ = SimSym.one ∨ σ = SimSym.com) →
    ∀ (g' m : ℕ),
    Reach
      ⟨.swGo, V.reverse ++
          (M ++ (D.reverse ++ SimSym.endL :: List.replicate g' SimSym.bk)),
        SimSym.endR, List.replicate m SimSym.bk⟩
      ⟨.swGo, M ++ ((V ++ D).reverse ++
          SimSym.endL :: List.replicate (g' - V.length) SimSym.bk),
        SimSym.endR, List.replicate (m + V.length) SimSym.bk⟩ := by
  intro V
  induction V using List.reverseRecOn with
  | nil =>
    intro _ D hD g' m
    exact Reach.cast (by simp) rfl (Reach.refl _)
  | append_singleton V u ihV =>
    intro hV D hD g' m
    have hu : u = SimSym.one ∨ u = SimSym.com := hV u (by simp)
    have hV' : ∀ σ ∈ V, σ = SimSym.one ∨ σ = SimSym.com :=
      fun σ hσ => hV σ (by simp [hσ])
    have hD' : ∀ σ ∈ u :: D, σ = SimSym.one ∨ σ = SimSym.com := by
      intro σ hσ
      rcases List.mem_cons.mp hσ with rfl | hσ
      · exact hu
      · exact hD σ hσ
    have riter : Reach
        ⟨.swGo, (V ++ [u]).reverse ++
            (M ++ (D.reverse ++ SimSym.endL :: List.replicate g' SimSym.bk)),
          SimSym.endR, List.replicate m SimSym.bk⟩
        ⟨.swGo, V.reverse ++
            (M ++ ((u :: D).reverse ++ SimSym.endL :: List.replicate (g' - 1) SimSym.bk)),
          SimSym.endR, List.replicate (m + 1) SimSym.bk⟩ := by
      rcases hu with rfl | rfl
      · exact sw_iter (Or.inl rfl) rfl (fun τ hτ => pass_swCar₁ hτ) rfl hM hV' hD g' m
      · exact sw_iter (Or.inr rfl) rfl (fun τ hτ => pass_swCarC hτ) rfl hM hV' hD g' m
    have rih := ihV hV' hD' (g' - 1) (m + 1)
    refine Reach.trans riter ?_
    refine Reach.cast rfl ?_ rih
    have h1 : g' - 1 - V.length = g' - (V.length + 1) := by omega
    have h2 : m + 1 + V.length = m + (V.length + 1) := by omega
    simp [h1, h2]

/-! ### The `cons₁` pop, phase two: the stored value moves out to `endR` -/

/-- **One round of the stored-value move**: `swOut` finds the old header past
the new frame – its content and the gap abstracted into `DN` – `swScan`
crosses the remaining content, `swLast` steps back onto its last letter,
erases it, and the carry appends it at `endR` by the endR-shift before
`swBack`/`swOut` re-enter. Stated over an abstract carry state so the digit
and separator instances share the proof. -/
theorem sw2_iter {p : CPos c} {u : SimSym c} {Qapp : SimQ c}
    (hu : u = SimSym.one ∨ u = SimSym.com)
    (h1 : simStep (c := c) .swLast u = some (.bk, Qapp, true))
    (h2 : ∀ τ : SimSym c, τ ≠ SimSym.endR → simStep Qapp τ = some (τ, Qapp, true))
    (h3 : simStep Qapp SimSym.endR = some (u, .swAppS, true))
    {DN : List (SimSym c)}
    (hDN : ∀ σ ∈ DN, (∀ q, σ ≠ SimSym.hCons₁ q) ∧ σ ≠ SimSym.endL)
    {C₂ : List (SimSym c)} (hC₂ : ∀ σ ∈ C₂, σ = SimSym.one ∨ σ = SimSym.com)
    {x : SimSym c} {Y' : List (SimSym c)}
    (hx1 : x ≠ SimSym.one) (hx2 : x ≠ SimSym.com)
    (hY : ∀ σ ∈ x :: Y', σ ≠ SimSym.endR ∧ σ ≠ SimSym.endL)
    {ap : List (SimSym c)} (hap : ∀ σ ∈ ap, σ = SimSym.one ∨ σ = SimSym.com)
    (gg m : ℕ) :
    Reach
      ⟨.swOut, SimSym.endL :: List.replicate gg SimSym.bk, SimSym.hCons₂,
        DN ++ SimSym.hCons₁ p :: ((C₂ ++ [u]) ++ x :: Y' ++
          (ap ++ SimSym.endR :: List.replicate m SimSym.bk))⟩
      ⟨.swOut, SimSym.endL :: List.replicate gg SimSym.bk, SimSym.hCons₂,
        DN ++ SimSym.hCons₁ p :: (C₂ ++ SimSym.bk :: x :: Y' ++
          ((ap ++ [u]) ++ SimSym.endR :: List.replicate (m - 1) SimSym.bk))⟩ := by
  -- find the old header past the new frame
  have r1 := reach_walkR (P := fun σ => ∀ q, σ ≠ SimSym.hCons₁ q)
    (fun σ hσ => pass_swOut hσ)
    DN (fun σ hσ => (hDN σ hσ).1) (s := SimSym.hCons₂) (by simp)
    (SimSym.endL :: List.replicate gg SimSym.bk) (SimSym.hCons₁ p)
    ((C₂ ++ [u]) ++ x :: Y' ++ (ap ++ SimSym.endR :: List.replicate m SimSym.bk))
  -- scan over the remaining content to its end
  have r2 := reach_step_then_walkR
    (show simStep (c := c) .swOut (SimSym.hCons₁ p) =
      some (.hCons₁ p, .swScan, true) from rfl)
    (P := fun σ => σ = SimSym.one ∨ σ = SimSym.com) (fun τ hτ => pass_swScan hτ)
    (C₂ ++ [u])
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact hC₂ τ hτ
      · rw [List.mem_singleton.mp hτ]; exact hu)
    x (DN.reverse ++ SimSym.hCons₂ :: SimSym.endL :: List.replicate gg SimSym.bk)
    (Y' ++ (ap ++ SimSym.endR :: List.replicate m SimSym.bk))
  -- step back onto the last content letter
  have r3 := lstep_left (stop_swScan hx1 hx2) u
    (C₂.reverse ++ SimSym.hCons₁ p ::
      (DN.reverse ++ SimSym.hCons₂ :: SimSym.endL :: List.replicate gg SimSym.bk))
    (Y' ++ (ap ++ SimSym.endR :: List.replicate m SimSym.bk))
  -- erase it and carry right to endR
  have r4 := reach_step_then_walkR h1 h2
    (x :: Y' ++ ap)
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact (hY τ hτ).1
      · rcases hap τ hτ with rfl | rfl <;> simp)
    SimSym.endR
    (C₂.reverse ++ SimSym.hCons₁ p ::
      (DN.reverse ++ SimSym.hCons₂ :: SimSym.endL :: List.replicate gg SimSym.bk))
    (List.replicate m SimSym.bk)
  -- append it over endR, re-write endR one cell right
  have r5 := lstep_right_pad h3
    ((x :: Y' ++ ap).reverse ++ SimSym.bk :: (C₂.reverse ++ SimSym.hCons₁ p ::
      (DN.reverse ++ SimSym.hCons₂ :: SimSym.endL :: List.replicate gg SimSym.bk))) m
  have r6 := lstep_left
    (show simStep (c := c) .swAppS SimSym.bk = some (.endR, .swBack, false) from rfl)
    u
    ((x :: Y' ++ ap).reverse ++ SimSym.bk :: (C₂.reverse ++ SimSym.hCons₁ p ::
      (DN.reverse ++ SimSym.hCons₂ :: SimSym.endL :: List.replicate gg SimSym.bk)))
    (List.replicate (m - 1) SimSym.bk)
  -- walk back to endL
  have r7 := reach_walkL (P := fun σ => σ ≠ SimSym.endL) (fun σ hσ => pass_swBack hσ)
    (ap.reverse ++ (Y'.reverse ++ x :: SimSym.bk :: (C₂.reverse ++ SimSym.hCons₁ p ::
      (DN.reverse ++ [SimSym.hCons₂]))))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases hap τ (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact (hY τ (by simp [List.mem_reverse.mp hτ])).2
      rcases List.mem_cons.mp hτ with rfl | hτ
      · exact (hY _ (by simp)).2
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases hC₂ τ (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact (hDN τ (List.mem_reverse.mp hτ)).2
      · rw [List.mem_singleton.mp hτ]; simp)
    (s := u) (by rcases hu with rfl | rfl <;> simp)
    SimSym.endL (List.replicate gg SimSym.bk)
    (SimSym.endR :: List.replicate (m - 1) SimSym.bk)
  -- re-enter through the new frame
  have r8 := lstep_right
    (show simStep (c := c) .swBack SimSym.endL = some (.endL, .swOut, true) from rfl)
    (List.replicate gg SimSym.bk) SimSym.hCons₂
    (DN ++ SimSym.hCons₁ p :: (C₂ ++ SimSym.bk :: x :: Y' ++
      ((ap ++ [u]) ++ SimSym.endR :: List.replicate (m - 1) SimSym.bk)))
  refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r2) ?_
  refine Reach.head ((congrArg lstep (by simp)).trans r3) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r4) ?_
  refine Reach.head r5 ?_
  refine Reach.head r6 ?_
  refine Reach.trans (Reach.cast (by simp) rfl r7) ?_
  refine Reach.head ((congrArg lstep (by simp)).trans r8) ?_
  exact Reach.refl _

/-- **The stored-value move, iterated**: the stored value crosses out to the
value region, mirrored – consumed at the content's right end, appended by
endR-shifts – while the erased zone between the old header and what follows
grows by its length. -/
theorem sw2_loop {p : CPos c} {DN : List (SimSym c)}
    (hDN : ∀ σ ∈ DN, (∀ q, σ ≠ SimSym.hCons₁ q) ∧ σ ≠ SimSym.endL)
    {C₂ : List (SimSym c)} (hC₂ : ∀ σ ∈ C₂, σ = SimSym.one ∨ σ = SimSym.com)
    (gg : ℕ) :
    ∀ (S : List (SimSym c)), (∀ σ ∈ S, σ = SimSym.one ∨ σ = SimSym.com) →
    ∀ {x : SimSym c} {Y' : List (SimSym c)}, x ≠ SimSym.one → x ≠ SimSym.com →
    (∀ σ ∈ x :: Y', σ ≠ SimSym.endR ∧ σ ≠ SimSym.endL) →
    ∀ {ap : List (SimSym c)}, (∀ σ ∈ ap, σ = SimSym.one ∨ σ = SimSym.com) →
    ∀ (m : ℕ),
    Reach
      ⟨.swOut, SimSym.endL :: List.replicate gg SimSym.bk, SimSym.hCons₂,
        DN ++ SimSym.hCons₁ p :: ((C₂ ++ S) ++ x :: Y' ++
          (ap ++ SimSym.endR :: List.replicate m SimSym.bk))⟩
      ⟨.swOut, SimSym.endL :: List.replicate gg SimSym.bk, SimSym.hCons₂,
        DN ++ SimSym.hCons₁ p :: (C₂ ++ (List.replicate S.length SimSym.bk ++ x :: Y') ++
          ((ap ++ S.reverse) ++ SimSym.endR :: List.replicate (m - S.length) SimSym.bk))⟩ := by
  intro S
  induction S using List.reverseRecOn with
  | nil =>
    intro _ x Y' _ _ _ ap _ m
    exact Reach.cast (by simp) rfl (Reach.refl _)
  | append_singleton S u ihS =>
    intro hS x Y' hx1 hx2 hY ap hap m
    have hu : u = SimSym.one ∨ u = SimSym.com := hS u (by simp)
    have hS' : ∀ σ ∈ S, σ = SimSym.one ∨ σ = SimSym.com :=
      fun σ hσ => hS σ (by simp [hσ])
    have hCS : ∀ σ ∈ C₂ ++ S, σ = SimSym.one ∨ σ = SimSym.com := by
      intro σ hσ
      rcases List.mem_append.mp hσ with hσ | hσ
      · exact hC₂ σ hσ
      · exact hS' σ hσ
    have hap' : ∀ σ ∈ ap ++ [u], σ = SimSym.one ∨ σ = SimSym.com := by
      intro σ hσ
      rcases List.mem_append.mp hσ with hσ | hσ
      · exact hap σ hσ
      · rw [List.mem_singleton.mp hσ]; exact hu
    have hY' : ∀ σ ∈ SimSym.bk :: x :: Y', σ ≠ SimSym.endR ∧ σ ≠ SimSym.endL := by
      intro σ hσ
      rcases List.mem_cons.mp hσ with rfl | hσ
      · exact ⟨by simp, by simp⟩
      · exact hY σ hσ
    have riter : Reach
        ⟨.swOut, SimSym.endL :: List.replicate gg SimSym.bk, SimSym.hCons₂,
          DN ++ SimSym.hCons₁ p :: (((C₂ ++ S) ++ [u]) ++ x :: Y' ++
            (ap ++ SimSym.endR :: List.replicate m SimSym.bk))⟩
        ⟨.swOut, SimSym.endL :: List.replicate gg SimSym.bk, SimSym.hCons₂,
          DN ++ SimSym.hCons₁ p :: ((C₂ ++ S) ++ SimSym.bk :: x :: Y' ++
            ((ap ++ [u]) ++ SimSym.endR :: List.replicate (m - 1) SimSym.bk))⟩ := by
      rcases hu with rfl | rfl
      · exact sw2_iter (Or.inl rfl) rfl (fun τ hτ => pass_swApp₁ hτ) rfl hDN hCS
          hx1 hx2 hY hap gg m
      · exact sw2_iter (Or.inr rfl) rfl (fun τ hτ => pass_swAppC hτ) rfl hDN hCS
          hx1 hx2 hY hap gg m
    have rih := ihS hS' (x := SimSym.bk) (Y' := x :: Y') (by simp) (by simp) hY'
      (ap := ap ++ [u]) hap' (m - 1)
    refine Reach.trans (Reach.cast (by simp) rfl riter) ?_
    refine Reach.cast (by simp) ?_ rih
    have h1 : m - 1 - S.length = m - (S.length + 1) := by omega
    simp [h1, replicate_glue]

/-- **Popping a `cons₁` frame**: phase one moves the value into a fresh
`cons₂` frame at `endL` – consumed at `endR`, so the frame stores it
mirrored – and closes it with its header; phase two finds the old `cons₁`
header – the first such header right of `endL` – and moves its stored value
out to `endR` the same way, so the value region receives it mirrored; the old
header erased, `nSeekR` walks to `mid` to dispatch the body of the pending
`fix`. -/
theorem pop_cons₁ {p : CPos c} {as : List ℕ} {k' : PCont c} (n : ℕ)
    {w' : List (SimSym c)} (hw' : FrameSeg k' w') (g : ℕ) (v : List ℕ) (j t : ℕ) :
    ∃ t', Reach
      (restCfg g (List.replicate n SimSym.bk ++
        SimSym.hCons₁ p :: (encVal as ++ w')) v j t)
      (atMid (.nSeekR p) (g - ((encVal (c := c) v).length + 1))
        (SimSym.hCons₂ :: ((encVal v).reverse ++
          (List.replicate (n + (encVal (c := c) as).length + 1) SimSym.bk ++ w')))
        as j t') := by
  refine ⟨t + (encVal (c := c) v).length - (encVal (c := c) as).length, ?_⟩
  obtain ⟨x, X, hsplit, hx1, hx2⟩ := hw'.head_split (List.replicate (j + 1) SimSym.bk)
  have hsplit' : ∀ Z : List (SimSym c), x :: (X ++ Z) =
      w' ++ SimSym.mid :: (List.replicate (j + 1) SimSym.bk ++ Z) := by
    intro Z
    have h := congrArg (· ++ Z) hsplit
    simpa using h.symm
  have hY : ∀ σ ∈ x :: X, σ ≠ SimSym.endR ∧ σ ≠ SimSym.endL := by
    rw [← hsplit]
    intro σ hσ
    rcases List.mem_append.mp hσ with hσ | hσ
    · exact ⟨((hw'.mem_frameSym σ hσ).ne).2.2.1, ((hw'.mem_frameSym σ hσ).ne).1⟩
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact ⟨by simp, by simp⟩
    · simp [List.eq_of_mem_replicate hσ]
  have hVv : ∀ σ ∈ (encVal (c := c) v).reverse, σ = SimSym.one ∨ σ = SimSym.com :=
    fun σ hσ => mem_encVal (List.mem_reverse.mp hσ)
  have hAs : ∀ σ ∈ encVal (c := c) as, σ = SimSym.one ∨ σ = SimSym.com :=
    fun σ hσ => mem_encVal hσ
  have hM : ∀ σ ∈ List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: (w'.reverse ++
      ((encVal (c := c) as).reverse ++ SimSym.hCons₁ p :: List.replicate n SimSym.bk)),
      σ ≠ SimSym.endL ∧ σ ≠ SimSym.endR := by
    intro σ hσ
    rcases List.mem_append.mp hσ with hσ | hσ
    · simp [List.eq_of_mem_replicate hσ]
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact ⟨by simp, by simp⟩
    rcases List.mem_append.mp hσ with hσ | hσ
    · exact ⟨((hw'.mem_frameSym σ (List.mem_reverse.mp hσ)).ne).1,
        ((hw'.mem_frameSym σ (List.mem_reverse.mp hσ)).ne).2.2.1⟩
    rcases List.mem_append.mp hσ with hσ | hσ
    · rcases mem_encVal (List.mem_reverse.mp hσ) with rfl | rfl <;> exact ⟨by simp, by simp⟩
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact ⟨by simp, by simp⟩
    · simp [List.eq_of_mem_replicate hσ]
  have hDN : ∀ σ ∈ (encVal (c := c) v).reverse ++ List.replicate n SimSym.bk,
      (∀ q, σ ≠ SimSym.hCons₁ q) ∧ σ ≠ SimSym.endL := by
    intro σ hσ
    rcases List.mem_append.mp hσ with hσ | hσ
    · rcases hVv σ hσ with rfl | rfl <;> exact ⟨by simp, by simp⟩
    · simp [List.eq_of_mem_replicate hσ]
  -- wake up: cross the gap to the header
  have r1 := reach_step_then_walkR
    (show simStep (c := c) .retL SimSym.endL = some (.endL, .retR, true) from rfl)
    (P := fun σ => σ = SimSym.bk) (fun τ hτ => by rw [hτ]; rfl)
    (List.replicate n SimSym.bk) (fun τ hτ => List.eq_of_mem_replicate hτ)
    (SimSym.hCons₁ p) (List.replicate g SimSym.bk)
    (encVal as ++ w' ++ SimSym.mid :: valR v j t)
  -- keep the header, walk right to endR
  have r2 := reach_step_then_walkR
    (show simStep (c := c) .retR (SimSym.hCons₁ p) =
      some (.hCons₁ p, .swGo, true) from rfl)
    (P := fun σ => σ ≠ SimSym.endR) (fun τ hτ => pass_swGo hτ)
    (encVal as ++ w' ++ SimSym.mid ::
      (List.replicate (j + 1) SimSym.bk ++ (encVal v).reverse))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases List.mem_append.mp hτ with hτ | hτ
        · rcases mem_encVal hτ with rfl | rfl <;> simp
        · exact ((hw'.mem_frameSym τ hτ).ne).2.2.1
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · simp [List.eq_of_mem_replicate hτ]
      · rcases mem_encVal (List.mem_reverse.mp hτ) with rfl | rfl <;> simp)
    SimSym.endR
    ((List.replicate n SimSym.bk).reverse ++ SimSym.endL :: List.replicate g SimSym.bk)
    (List.replicate t SimSym.bk)
  -- phase one: the value crosses into the fresh frame
  have rloop1 := sw_loop hM ((encVal (c := c) v).reverse) hVv (D := []) (by simp) g t
  -- the value spent: probe the gap blank, restore endR
  have e1 := lstep_left
    (show simStep (c := c) .swGo SimSym.endR = some (.bk, .swPeek, false) from rfl)
    SimSym.bk
    (List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++
      ((encVal (c := c) as).reverse ++ SimSym.hCons₁ p :: (List.replicate n SimSym.bk ++
        (encVal v ++ SimSym.endL ::
          List.replicate (g - ((encVal (c := c) v).reverse).length) SimSym.bk)))))
    (List.replicate (t + ((encVal (c := c) v).reverse).length) SimSym.bk)
  have e2 := lstep_right
    (show simStep (c := c) .swPeek SimSym.bk = some (.bk, .swRest, true) from rfl)
    (List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++
      ((encVal (c := c) as).reverse ++ SimSym.hCons₁ p :: (List.replicate n SimSym.bk ++
        (encVal v ++ SimSym.endL ::
          List.replicate (g - ((encVal (c := c) v).reverse).length) SimSym.bk)))))
    SimSym.bk (List.replicate (t + ((encVal (c := c) v).reverse).length) SimSym.bk)
  have e3 := lstep_left
    (show simStep (c := c) .swRest SimSym.bk = some (.endR, .swHdr, false) from rfl)
    SimSym.bk
    (List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++
      ((encVal (c := c) as).reverse ++ SimSym.hCons₁ p :: (List.replicate n SimSym.bk ++
        (encVal v ++ SimSym.endL ::
          List.replicate (g - ((encVal (c := c) v).reverse).length) SimSym.bk)))))
    (List.replicate (t + ((encVal (c := c) v).reverse).length) SimSym.bk)
  -- walk left to endL and write the cons₂ header
  have e4 := reach_walkL (P := fun σ => σ ≠ SimSym.endL) (fun σ hσ => pass_swHdr hσ)
    (List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++
      ((encVal (c := c) as).reverse ++ SimSym.hCons₁ p :: (List.replicate n SimSym.bk ++
        encVal v))))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · simp [List.eq_of_mem_replicate hτ]
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact ((hw'.mem_frameSym τ (List.mem_reverse.mp hτ)).ne).1
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases mem_encVal (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
      rcases List.mem_cons.mp hτ with rfl | hτ
      · simp
      rcases List.mem_append.mp hτ with hτ | hτ
      · simp [List.eq_of_mem_replicate hτ]
      · rcases mem_encVal hτ with rfl | rfl <;> simp)
    (s := SimSym.bk) (by simp) SimSym.endL
    (List.replicate (g - ((encVal (c := c) v).reverse).length) SimSym.bk)
    (SimSym.endR ::
      List.replicate (t + ((encVal (c := c) v).reverse).length) SimSym.bk)
  have e5 := lstep_left_pad
    (show simStep (c := c) .swHdr SimSym.endL = some (.hCons₂, .swHdrS, false) from rfl)
    (g - ((encVal (c := c) v).reverse).length)
    ((List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++
      ((encVal (c := c) as).reverse ++ SimSym.hCons₁ p :: (List.replicate n SimSym.bk ++
        encVal v)))).reverse ++
      SimSym.bk :: SimSym.endR ::
        List.replicate (t + ((encVal (c := c) v).reverse).length) SimSym.bk)
  have e6 := lstep_right
    (show simStep (c := c) .swHdrS SimSym.bk = some (.endL, .swOut, true) from rfl)
    (List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    SimSym.hCons₂
    ((List.replicate j SimSym.bk ++ SimSym.mid :: (w'.reverse ++
      ((encVal (c := c) as).reverse ++ SimSym.hCons₁ p :: (List.replicate n SimSym.bk ++
        encVal v)))).reverse ++
      SimSym.bk :: SimSym.endR ::
        List.replicate (t + ((encVal (c := c) v).reverse).length) SimSym.bk)
  -- phase two: the stored value crosses out to the value region
  have rloop2 := sw2_loop (p := p) hDN (C₂ := []) (by simp)
    (g - ((encVal (c := c) v).reverse).length - 1)
    (encVal (c := c) as) hAs hx1 hx2 hY (ap := []) (by simp)
    (t + ((encVal (c := c) v).reverse).length)
  -- the content spent: erase the old header and seek mid
  obtain ⟨x₂, X₂, h₂, hx₂1, hx₂2⟩ := bk_head_split (encVal (c := c) as).length hx1 hx2
    (X ++ ((encVal (c := c) as).reverse ++ SimSym.endR :: List.replicate
      (t + ((encVal (c := c) v).reverse).length - (encVal (c := c) as).length) SimSym.bk))
  have f1 := reach_walkR (P := fun σ => ∀ q, σ ≠ SimSym.hCons₁ q)
    (fun σ hσ => pass_swOut hσ)
    ((encVal (c := c) v).reverse ++ List.replicate n SimSym.bk)
    (fun σ hσ => (hDN σ hσ).1) (s := SimSym.hCons₂) (by simp)
    (SimSym.endL ::
      List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    (SimSym.hCons₁ p) (x₂ :: X₂)
  have f2 := lstep_right
    (show simStep (c := c) .swOut (SimSym.hCons₁ p) =
      some (.hCons₁ p, .swScan, true) from rfl)
    (((encVal (c := c) v).reverse ++ List.replicate n SimSym.bk).reverse ++
      SimSym.hCons₂ :: SimSym.endL ::
        List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    x₂ X₂
  have f3 := lstep_left (stop_swScan hx₂1 hx₂2) (SimSym.hCons₁ p)
    (((encVal (c := c) v).reverse ++ List.replicate n SimSym.bk).reverse ++
      SimSym.hCons₂ :: SimSym.endL ::
        List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    X₂
  have f4 := reach_step_then_walkR
    (show simStep (c := c) .swLast (SimSym.hCons₁ p) =
      some (.bk, .nSeekR p, true) from rfl)
    (P := fun σ => σ ≠ SimSym.mid) (fun τ hτ => pass_nSeekR hτ)
    (List.replicate (encVal (c := c) as).length SimSym.bk ++ w')
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · simp [List.eq_of_mem_replicate hτ]
      · exact ((hw'.mem_frameSym τ hτ).ne).2.1)
    SimSym.mid
    (((encVal (c := c) v).reverse ++ List.replicate n SimSym.bk).reverse ++
      SimSym.hCons₂ :: SimSym.endL ::
        List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    (List.replicate (j + 1) SimSym.bk ++ ((encVal (c := c) as).reverse ++
      SimSym.endR :: List.replicate
        (t + ((encVal (c := c) v).reverse).length - (encVal (c := c) as).length) SimSym.bk))
  refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
  refine Reach.trans (Reach.cast (by simp [valR]) rfl r2) ?_
  refine Reach.trans (Reach.cast (by simp) rfl rloop1) ?_
  refine Reach.head ((congrArg lstep (by simp [List.replicate_succ])).trans e1) ?_
  refine Reach.head e2 ?_
  refine Reach.head e3 ?_
  refine Reach.trans (Reach.cast (by simp) rfl e4) ?_
  refine Reach.head e5 ?_
  refine Reach.head e6 ?_
  refine Reach.trans (Reach.cast (by simp [hsplit', replicate_glue]) rfl rloop2) ?_
  refine Reach.trans (Reach.cast (by rw [← h₂]; simp [hsplit']) rfl f1) ?_
  refine Reach.head f2 ?_
  refine Reach.head ((congrArg lstep (by simp)).trans f3) ?_
  refine Reach.trans (Reach.cast (by rw [← h₂]; simp [hsplit']) rfl f4) ?_
  refine Reach.cast rfl ?_ (Reach.refl _)
  rw [show n + (encVal (c := c) as).length + 1 =
    (encVal (c := c) as).length + 1 + n from by omega]
  simp [atMid, midL, valR, replicate_glue, replicate_merge]
  omega

end HaltHard

end DescriptiveComplexity
