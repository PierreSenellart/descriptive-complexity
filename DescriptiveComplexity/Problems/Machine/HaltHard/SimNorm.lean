/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.Zip

/-!
# The dispatch phase of the simulation

The first half of the simulation of `Turing.ToPartrec.step` by the machine of
`Table.lean`: from the dispatch of a code at the separator `mid`, the machine
reaches the resting configuration of the `Turing.ToPartrec.Cfg` that
`Turing.ToPartrec.stepNormal` computes – in the positioned form
`DescriptiveComplexity.HaltHard.pStepNormal`, whose projection to the library
semantics is `DescriptiveComplexity.HaltHard.pStepNormal_toCont`.

The tape regions are described by
`DescriptiveComplexity.HaltHard.valR`/`midL`/`restCfg`/`atMid`, and the frame
region by the relation `DescriptiveComplexity.HaltHard.FrameSeg`, which
spells a continuation as frames separated by arbitrary blank gaps. One lemma
per code shape moves the machine from the dispatch at `mid` to the next
dispatch (for the four node shapes, having pushed the frame) or back to rest
(for the three leaves, having transformed the value);
`DescriptiveComplexity.HaltHard.sim_norm` chains them by induction on the
size of the dispatched code.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec

variable {c : Code}

/-! ### The tape regions -/

/-- The value-region strip right of `mid`: the inner gap – never empty, so a
separator can always be closed next to an empty value – the mirrored value,
the right marker and the trailing blanks. -/
abbrev valR (v : List ℕ) (j t : ℕ) : List (SimSym c) :=
  List.replicate (j + 1) .bk ++ (encVal v).reverse ++ .endR :: List.replicate t .bk

/-- The left context of a head sitting on `mid`: the frame region, the left
marker, the left blanks. -/
abbrev midL (g : ℕ) (fr : List (SimSym c)) : List (SimSym c) :=
  fr.reverse ++ .endL :: List.replicate g .bk

/-- The configuration at the dispatch point: head on `mid`. -/
abbrev atMid (Q : SimQ c) (g : ℕ) (fr : List (SimSym c)) (v : List ℕ) (j t : ℕ) : LCfg c :=
  ⟨Q, midL g fr, .mid, valR v j t⟩

/-- The resting configuration between abstract steps: head on `endL` in the
seek state. -/
abbrev restCfg (g : ℕ) (fr : List (SimSym c)) (v : List ℕ) (j t : ℕ) : LCfg c :=
  ⟨.retL, List.replicate g .bk, .endL, fr ++ .mid :: valR v j t⟩

/-- **The frame region of a continuation**: the frames in order, top first,
separated by arbitrary blank gaps. A `cons₁` frame stores its value straight,
a `cons₂` frame mirrored. -/
inductive FrameSeg : PCont c → List (SimSym c) → Prop
  /-- The empty continuation has an empty frame region. -/
  | halt : FrameSeg .halt []
  /-- A blank gap may precede the frames. -/
  | gap {k : PCont c} {w : List (SimSym c)} : FrameSeg k w → FrameSeg k (.bk :: w)
  /-- A `cons₁` frame: header, then the stored value, straight. -/
  | cons₁ {p : CPos c} {as : List ℕ} {k : PCont c} {w : List (SimSym c)} :
      FrameSeg k w → FrameSeg (.cons₁ p as k) (.hCons₁ p :: (encVal as ++ w))
  /-- A `cons₂` frame: header, then the stored value, mirrored. -/
  | cons₂ {ns : List ℕ} {k : PCont c} {w : List (SimSym c)} :
      FrameSeg k w → FrameSeg (.cons₂ ns k) (.hCons₂ :: ((encVal ns).reverse ++ w))
  /-- A `comp` frame: a bare header. -/
  | comp {p : CPos c} {k : PCont c} {w : List (SimSym c)} :
      FrameSeg k w → FrameSeg (.comp p k) (.hComp p :: w)
  /-- A `fix` frame: a bare header. -/
  | fix {p : CPos c} {k : PCont c} {w : List (SimSym c)} :
      FrameSeg k w → FrameSeg (.fix p k) (.hFix p :: w)

/-- The letters a frame region can hold. -/
def FrameSym (σ : SimSym c) : Prop :=
  σ = .bk ∨ σ = .one ∨ σ = .com ∨ σ = .hCons₂ ∨
    (∃ p, σ = .hCons₁ p) ∨ (∃ p, σ = .hComp p) ∨ (∃ p, σ = .hFix p)

theorem mem_encVal {v : List ℕ} {σ : SimSym c} (h : σ ∈ encVal v) :
    σ = .one ∨ σ = .com := by
  induction v with
  | nil => simp [encVal] at h
  | cons n w ih =>
    rw [encVal_cons, List.mem_append] at h
    rcases h with h | h
    · rw [encNum, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl (List.eq_of_mem_replicate h)
      · exact Or.inr (by simpa using h)
    · exact ih h

theorem FrameSeg.mem_frameSym {k : PCont c} {fr : List (SimSym c)} (h : FrameSeg k fr) :
    ∀ σ ∈ fr, FrameSym σ := by
  induction h with
  | halt => simp
  | gap _ ih =>
    intro σ hσ
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact Or.inl rfl
    · exact ih σ hσ
  | cons₁ _ ih =>
    intro σ hσ
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
    · rcases List.mem_append.mp hσ with hσ | hσ
      · rcases mem_encVal hσ with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
      · exact ih σ hσ
  | cons₂ _ ih =>
    intro σ hσ
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rcases List.mem_append.mp hσ with hσ | hσ
      · rcases mem_encVal (List.mem_reverse.mp hσ) with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
      · exact ih σ hσ
  | comp _ ih =>
    intro σ hσ
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
    · exact ih σ hσ
  | fix _ ih =>
    intro σ hσ
    rcases List.mem_cons.mp hσ with rfl | hσ
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))))
    · exact ih σ hσ

/-- What a frame letter is not: none of the markers, none of the primes. -/
theorem FrameSym.ne {σ : SimSym c} (h : FrameSym σ) :
    σ ≠ .endL ∧ σ ≠ .mid ∧ σ ≠ .endR ∧ σ ≠ .one' ∧ σ ≠ .com' := by
  rcases h with rfl | rfl | rfl | rfl | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
    exact ⟨by simp, by simp, by simp, by simp, by simp⟩

/-! ### Pass lemmas

Each walk state passes every letter but its stop letter; the catch-all rows
of the table make these case bashes. -/

section Pass

variable {σ : SimSym c} {p : CPos c}

theorem pass_retL (h : σ ≠ .endL) : simStep (c := c) .retL σ = some (σ, .retL, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_nSeekL (h : σ ≠ .mid) : simStep (.nSeekL p) σ = some (σ, .nSeekL p, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_nSeekR (h : σ ≠ .mid) : simStep (.nSeekR p) σ = some (σ, .nSeekR p, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_zGo (h : σ ≠ .endR) : simStep (c := c) .zGo σ = some (σ, .zGo, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_suGo (h : σ ≠ .endR) : simStep (c := c) .suGo σ = some (σ, .suGo, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_tlGo (h : σ ≠ .endR) : simStep (c := c) .tlGo σ = some (σ, .tlGo, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_caGo (h : σ ≠ .endR) : simStep (.caGo p) σ = some (σ, .caGo p, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_coHdr (h : σ ≠ .endL) : simStep (.coHdr p) σ = some (σ, .coHdr p, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_fiHdr (h : σ ≠ .endL) : simStep (.fiHdr p) σ = some (σ, .fiHdr p, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_suKill (h : σ = .one ∨ σ = .com ∨ σ = .bk) :
    simStep (c := c) .suKill σ = some (.bk, .suKill, false) := by
  rcases h with rfl | rfl | rfl <;> rfl

end Pass

/-- Reachability transported along equalities of the two configurations. -/
theorem Reach.cast {x x' y y' : LCfg c} (hx : x = x') (hy : y = y') (h : Reach x' y') :
    Reach x y := hx ▸ hy ▸ h

/-- Gluing the letter behind the head back onto a run of its own kind – the
shape the region equalities take after a walk re-crosses a run it wrote. -/
theorem replicate_glue (a : SimSym c) (n : ℕ) (R : List (SimSym c)) :
    List.replicate n a ++ a :: R = List.replicate (n + 1) a ++ R := by
  rw [List.replicate_succ']
  simp

/-! ### Hand-over walks

Each phase of a dispatch is one step that hands over to a walk state,
followed by the walk itself: the combinators below package the two, so that
an empty walked run – the hand-over landing directly on the stop letter –
needs no case split at the use sites. -/

section StepWalk

variable {q q' : SimQ c} {P : SimSym c → Prop} {f : SimSym c → SimSym c} {s σ' : SimSym c}

/-- A rightward hand-over step, then a rightward walk to the stop letter. -/
theorem reach_step_walkR (hs : simStep q s = some (σ', q', true))
    (hq : ∀ σ, P σ → simStep q' σ = some (σ, q', true)) (w : List (SimSym c))
    (hw : ∀ σ ∈ w, P σ) (L : List (SimSym c)) (t : SimSym c) (R : List (SimSym c)) :
    Reach ⟨q, L, s, w ++ t :: R⟩ ⟨q', w.reverse ++ σ' :: L, t, R⟩ := by
  rcases w with - | ⟨a, w⟩
  · exact Reach.single (lstep_right hs L t R)
  · refine Reach.head (lstep_right hs L a (w ++ t :: R)) ?_
    have h := reach_walkR hq w (fun σ hσ => hw σ (by simp [hσ])) (hw a (by simp)) (σ' :: L) t R
    exact Reach.cast rfl (by simp) h

/-- A leftward hand-over step, then a leftward walk to the stop letter,
rewriting each crossed letter by `f`. -/
theorem reach_step_walkL_map (hs : simStep q s = some (σ', q', false))
    (hq : ∀ σ, P σ → simStep q' σ = some (f σ, q', false)) (w : List (SimSym c))
    (hw : ∀ σ ∈ w, P σ) (t : SimSym c) (L R : List (SimSym c)) :
    Reach ⟨q, w ++ t :: L, s, R⟩ ⟨q', L, t, (w.map f).reverse ++ σ' :: R⟩ := by
  rcases w with - | ⟨a, w⟩
  · exact Reach.single (lstep_left hs t L R)
  · refine Reach.head (lstep_left hs a (w ++ t :: L) R) ?_
    have h := reach_walkL_map hq w (fun σ hσ => hw σ (by simp [hσ])) (hw a (by simp)) t L (σ' :: R)
    exact Reach.cast rfl (by simp) h

/-- A leftward hand-over step, then a leftward walk to the stop letter. -/
theorem reach_step_walkL (hs : simStep q s = some (σ', q', false))
    (hq : ∀ σ, P σ → simStep q' σ = some (σ, q', false)) (w : List (SimSym c))
    (hw : ∀ σ ∈ w, P σ) (t : SimSym c) (L R : List (SimSym c)) :
    Reach ⟨q, w ++ t :: L, s, R⟩ ⟨q', L, t, w.reverse ++ σ' :: R⟩ := by
  have h := reach_step_walkL_map (f := id) hs (fun σ hσ => hq σ hσ) w hw t L R
  simpa using h

end StepWalk

/-! ### The positioned `stepNormal` -/

/-- **`Turing.ToPartrec.stepNormal`, over positions**: the continuation and
value of the configuration the dispatched code immediately becomes –
`stepNormal` always returns a `Cfg.ret`, so a pair suffices. -/
def pStepNormal (p : CPos c) (k : PCont c) (v : List ℕ) : PCont c × List ℕ :=
  match _h : codeAt p with
  | .zero' => (k, 0 :: v)
  | .succ => (k, [v.headI.succ])
  | .tail => (k, v.tail)
  | .cons _ _ => pStepNormal (c₁ p) (.cons₁ (c₂ p) v k) v
  | .comp _ _ => pStepNormal (c₂ p) (.comp (c₁ p) k) v
  | .case _ _ =>
    match v.headI with
    | 0 => pStepNormal (c₁ p) k v.tail
    | y + 1 => pStepNormal (c₂ p) k (y :: v.tail)
  | .fix _ => pStepNormal (c₁ p) (.fix (c₁ p) k) v
  termination_by sizeOf (codeAt p)
  decreasing_by
  · rw [codeAt_c₁_cons _h, _h]; simp; try omega
  · rw [codeAt_c₂_comp _h, _h]; simp; try omega
  · rw [codeAt_c₁_case _h, _h]; simp; try omega
  · rw [codeAt_c₂_case _h, _h]; simp; try omega
  · rw [codeAt_c₁_fix _h, _h]; simp; try omega

/-- The positioned `stepNormal` projects onto the library's. -/
theorem pStepNormal_toCont (p : CPos c) (k : PCont c) (v : List ℕ) :
    stepNormal (codeAt p) k.toCont v =
      Cfg.ret (pStepNormal p k v).1.toCont (pStepNormal p k v).2 := by
  fun_induction pStepNormal p k v with
  | case1 p k v h => rw [h]; rfl
  | case2 p k v h => rw [h]; rfl
  | case3 p k v h => rw [h]; rfl
  | case4 p k v f fs h ih =>
    rw [← ih, codeAt_c₁_cons h, h]
    change stepNormal f (Cont.cons₁ fs v k.toCont) v =
      stepNormal f (Cont.cons₁ (codeAt (c₂ p)) v k.toCont) v
    rw [codeAt_c₂_cons h]
  | case5 p k v f g h ih =>
    rw [← ih, codeAt_c₂_comp h, h]
    change stepNormal g (Cont.comp f k.toCont) v =
      stepNormal g (Cont.comp (codeAt (c₁ p)) k.toCont) v
    rw [codeAt_c₁_comp h]
  | case6 p k v f g h hv ih =>
    rw [← ih, codeAt_c₁_case h, h]
    simp [stepNormal, hv]
  | case7 p k v f g h y hv ih =>
    rw [← ih, codeAt_c₂_case h, h]
    simp [stepNormal, hv]
  | case8 p k v f h ih =>
    rw [← ih, codeAt_c₁_fix h, h]
    change stepNormal f (Cont.fix f k.toCont) v =
      stepNormal f (Cont.fix (codeAt (c₁ p)) k.toCont) v
    rw [codeAt_c₁_fix h]

/-! ### The leaf dispatches -/

/-- **`zero'`**: walk to `endR`, append a separator, return to rest. The
value gains a `0` in front – a separator at the right end of the mirrored
region. -/
theorem norm_zero' {p : CPos c} (h : codeAt p = .zero') {Q : SimQ c}
    (hQ : simStep Q .mid = some (dispatch p)) (g : ℕ) {fr : List (SimSym c)}
    (hfr : ∀ σ ∈ fr, FrameSym σ) (v : List ℕ) (j t : ℕ) :
    Reach (atMid Q g fr v j t) (restCfg g fr (0 :: v) j (t - 1)) := by
  have hd : simStep Q .mid = some (.mid, .zGo, true) := by
    rw [hQ]; simp only [dispatch, h]
  have hval : ∀ σ ∈ (encVal (c := c) v).reverse, σ ≠ SimSym.endR ∧ σ ≠ SimSym.endL := by
    intro σ hσ
    rcases mem_encVal (List.mem_reverse.mp hσ) with rfl | rfl <;> exact ⟨by simp, by simp⟩
  -- enter the gap
  have r1 : lstep (atMid Q g fr v j t) = some ⟨.zGo, SimSym.mid :: midL g fr, SimSym.bk,
      List.replicate j SimSym.bk ++
        ((encVal v).reverse ++ SimSym.endR :: List.replicate t SimSym.bk)⟩ := by
    have := lstep_right hd (midL g fr) SimSym.bk
      (List.replicate j SimSym.bk ++
        ((encVal v).reverse ++ SimSym.endR :: List.replicate t SimSym.bk))
    refine Eq.trans (congrArg lstep ?_) this
    simp [List.replicate_succ]
  -- walk to endR
  have r2 := reach_walkR (P := fun σ => σ ≠ SimSym.endR) (fun σ hσ => pass_zGo hσ)
    (List.replicate j SimSym.bk ++ (encVal v).reverse)
    (by
      intro σ hσ
      rcases List.mem_append.mp hσ with hσ | hσ
      · simp [List.eq_of_mem_replicate hσ]
      · exact (hval σ hσ).1)
    (s := SimSym.bk) (by simp)
    (SimSym.mid :: midL g fr) SimSym.endR (List.replicate t SimSym.bk)
  -- write the separator over endR, re-write endR one cell right of it
  have r3 := lstep_right_pad
    (show simStep (c := c) .zGo .endR = some (.com, .zEnd, true) from rfl)
    ((List.replicate j SimSym.bk ++ (encVal v).reverse).reverse ++
      SimSym.bk :: SimSym.mid :: midL g fr) t
  have r4 := lstep_left
    (show simStep (c := c) .zEnd .bk = some (.endR, .retL, false) from rfl)
    SimSym.com
    ((List.replicate j SimSym.bk ++ (encVal v).reverse).reverse ++
      SimSym.bk :: SimSym.mid :: midL g fr)
    (List.replicate (t - 1) SimSym.bk)
  -- walk back to endL
  have r5 := reach_walkL (P := fun σ => σ ≠ SimSym.endL) (fun σ hσ => pass_retL hσ)
    ((List.replicate j SimSym.bk ++ (encVal v).reverse).reverse ++
      SimSym.bk :: SimSym.mid :: fr.reverse)
    (by
      intro σ hσ
      rcases List.mem_append.mp hσ with hσ | hσ
      · rcases List.mem_append.mp (List.mem_reverse.mp hσ) with hσ | hσ
        · simp [List.eq_of_mem_replicate hσ]
        · exact (hval σ hσ).2
      · rcases List.mem_cons.mp hσ with rfl | hσ
        · simp
        rcases List.mem_cons.mp hσ with rfl | hσ
        · simp
        · exact ((hfr σ (List.mem_reverse.mp hσ)).ne).1)
    (s := SimSym.com) (by simp) .endL (List.replicate g .bk)
    (SimSym.endR :: List.replicate (t - 1) SimSym.bk)
  refine Reach.head r1 (Reach.trans (Reach.cast (by simp) rfl r2) ?_)
  refine Reach.head r3 ?_
  refine Reach.head r4 ?_
  refine Reach.cast ?_ ?_ r5
  · simp [midL]
  · simp [restCfg, valR, List.replicate_succ, encNum]

/-- **`comp` push**: walk left over the frames to `endL`, write the `comp`
header over it, re-write `endL` one cell into the left blanks, and walk back
to `mid` to dispatch the second child: the frame region gains a bare header,
the left blanks lose a cell. -/
theorem norm_comp {p : CPos c} {f g₂ : Code} (h : codeAt p = .comp f g₂)
    {Q : SimQ c} (hQ : simStep Q .mid = some (dispatch p)) (g : ℕ)
    {fr : List (SimSym c)} (hfr : ∀ σ ∈ fr, FrameSym σ) (v : List ℕ) (j t : ℕ) :
    Reach (atMid Q g fr v j t)
      (atMid (.nSeekR (c₂ p)) (g - 1) (SimSym.hComp (c₁ p) :: fr) v j t) := by
  have hd : simStep Q .mid = some (.mid, .coHdr p, false) := by
    rw [hQ]; simp only [dispatch, h]
  -- to `endL`, over the frame region
  have r1 := reach_step_walkL (P := fun σ => σ ≠ SimSym.endL) hd
    (fun σ hσ => pass_coHdr hσ) fr.reverse
    (fun σ hσ => ((hfr σ (List.mem_reverse.mp hσ)).ne).1)
    SimSym.endL (List.replicate g SimSym.bk) (valR v j t)
  -- write the header over `endL`, re-write `endL` one cell left
  have r2 := lstep_left_pad
    (show simStep (c := c) (.coHdr p) .endL = some (.hComp (c₁ p), .coHdrS p, false) from rfl)
    g (fr.reverse.reverse ++ SimSym.mid :: valR v j t)
  have r3 := lstep_right
    (show simStep (c := c) (.coHdrS p) .bk = some (.endL, .nSeekR (c₂ p), true) from rfl)
    (List.replicate (g - 1) SimSym.bk) (SimSym.hComp (c₁ p))
    (fr.reverse.reverse ++ SimSym.mid :: valR v j t)
  -- back to `mid`, over the grown frame region
  have r4 := reach_walkR (P := fun σ => σ ≠ SimSym.mid)
    (fun σ hσ => pass_nSeekR (p := c₂ p) hσ)
    fr.reverse.reverse (fun σ hσ => ((hfr σ (by simpa using hσ)).ne).2.1)
    (s := SimSym.hComp (c₁ p)) (by simp)
    (SimSym.endL :: List.replicate (g - 1) SimSym.bk) SimSym.mid (valR v j t)
  refine Reach.trans r1 (Reach.head r2 (Reach.head r3 (Reach.cast rfl ?_ r4)))
  simp [midL]

/-- **`succ`**: append a digit at `endR` – a fresh separator and a digit, if
the value was empty – then walk back over the head block and erase every
letter between it and `mid`: the value becomes the singleton successor of its
head, the erased blocks joining the inner gap. -/
theorem norm_succ {p : CPos c} (h : codeAt p = .succ) {Q : SimQ c}
    (hQ : simStep Q .mid = some (dispatch p)) (g : ℕ) {fr : List (SimSym c)}
    (hfr : ∀ σ ∈ fr, FrameSym σ) (v : List ℕ) (j t : ℕ) :
    ∃ j' t', Reach (atMid Q g fr v j t) (restCfg g fr [v.headI.succ] j' t') := by
  have hd : simStep Q .mid = some (.mid, .suScan, true) := by
    rw [hQ]; simp only [dispatch, h]
  rcases v with - | ⟨n, w⟩
  · -- empty value: append a separator and a digit at `endR`
    refine ⟨j, t - 1 - 1, ?_⟩
    have r1 := reach_step_walkR (P := fun σ => σ = SimSym.bk) hd
      (fun σ hσ => by subst hσ; rfl)
      (List.replicate (j + 1) SimSym.bk) (fun σ hσ => List.eq_of_mem_replicate hσ)
      (midL g fr) SimSym.endR (List.replicate t SimSym.bk)
    have r2 := lstep_right_pad
      (show simStep (c := c) .suScan .endR = some (.com, .suE₁, true) from rfl)
      (SimSym.bk :: (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr)) t
    have r3 := lstep_right_pad
      (show simStep (c := c) .suE₁ .bk = some (.one, .suE₂, true) from rfl)
      (SimSym.com :: (SimSym.bk :: (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr)))
      (t - 1)
    have r4 := lstep_left
      (show simStep (c := c) .suE₂ .bk = some (.endR, .retL, false) from rfl)
      SimSym.one
      (SimSym.com :: (SimSym.bk :: (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr)))
      (List.replicate (t - 1 - 1) SimSym.bk)
    have r5 := reach_walkL (P := fun σ => σ ≠ SimSym.endL) (fun σ hσ => pass_retL hσ)
      (SimSym.com :: SimSym.bk :: (List.replicate j SimSym.bk ++ SimSym.mid :: fr.reverse))
      (fun σ hσ => by
        rcases List.mem_cons.mp hσ with rfl | hσ
        · simp
        rcases List.mem_cons.mp hσ with rfl | hσ
        · simp
        rcases List.mem_append.mp hσ with hσ | hσ
        · simp [List.eq_of_mem_replicate hσ]
        · rcases List.mem_cons.mp hσ with rfl | hσ
          · simp
          · exact ((hfr σ (List.mem_reverse.mp hσ)).ne).1)
      (s := SimSym.one) (by simp) SimSym.endL (List.replicate g SimSym.bk)
      (SimSym.endR :: List.replicate (t - 1 - 1) SimSym.bk)
    refine Reach.trans (Reach.cast (by simp [atMid, valR]) rfl r1) ?_
    refine Reach.head
      ((congrArg lstep (by simp [List.replicate_succ, replicate_glue])).trans r2) ?_
    refine Reach.head r3 ?_
    refine Reach.head r4 ?_
    exact Reach.cast (by simp [midL])
      (by simp [restCfg, valR, encNum, List.replicate_succ, replicate_glue]) r5
  · -- nonempty value: append a digit, then erase all blocks but the head one
    refine ⟨(encVal (c := c) w).length + j, t - 1, ?_⟩
    obtain ⟨e, es, he⟩ : ∃ e es, (encVal (c := c) (n :: w)).reverse = e :: es := by
      rcases hrev : (encVal (c := c) (n :: w)).reverse with - | ⟨e, es⟩
      · exact absurd (List.reverse_eq_nil_iff.mp hrev) (by simp)
      · exact ⟨e, es, rfl⟩
    have hmem : ∀ σ ∈ (e :: es : List (SimSym c)), σ = SimSym.one ∨ σ = SimSym.com := by
      rw [← he]
      exact fun σ hσ => mem_encVal (List.mem_reverse.mp hσ)
    have hL : ∀ X : List (SimSym c), es.reverse ++ e :: X =
        List.replicate n SimSym.one ++ (SimSym.com :: (encVal w ++ X)) := by
      intro X
      have h1 : es.reverse ++ [e] = encVal (c := c) (n :: w) := by
        rw [← List.reverse_cons, ← he, List.reverse_reverse]
      calc es.reverse ++ e :: X = (es.reverse ++ [e]) ++ X := by simp
        _ = encVal (c := c) (n :: w) ++ X := by rw [h1]
        _ = _ := by simp [encNum]
    have hse : simStep (c := c) .suScan e = some (e, .suGo, true) := by
      rcases hmem e (by simp) with rfl | rfl <;> rfl
    have r1 := reach_step_walkR (P := fun σ => σ = SimSym.bk) hd
      (fun σ hσ => by subst hσ; rfl)
      (List.replicate (j + 1) SimSym.bk) (fun σ hσ => List.eq_of_mem_replicate hσ)
      (midL g fr) e (es ++ SimSym.endR :: List.replicate t SimSym.bk)
    have r2 := reach_step_walkR (P := fun σ => σ = SimSym.one ∨ σ = SimSym.com) hse
      (fun σ hσ => pass_suGo (by rcases hσ with rfl | rfl <;> simp))
      es (fun σ hσ => hmem σ (by simp [hσ]))
      ((List.replicate (j + 1) SimSym.bk).reverse ++ SimSym.mid :: midL g fr)
      SimSym.endR (List.replicate t SimSym.bk)
    have r3 := lstep_right_pad
      (show simStep (c := c) .suGo .endR = some (.one, .suEnd, true) from rfl)
      (es.reverse ++
        e :: ((List.replicate (j + 1) SimSym.bk).reverse ++ SimSym.mid :: midL g fr)) t
    have r4 := lstep_left
      (show simStep (c := c) .suEnd .bk = some (.endR, .suBack, false) from rfl)
      SimSym.one
      (es.reverse ++
        e :: ((List.replicate (j + 1) SimSym.bk).reverse ++ SimSym.mid :: midL g fr))
      (List.replicate (t - 1) SimSym.bk)
    have r5 := reach_walkL (q := .suBack) (P := fun σ => σ = SimSym.one)
      (fun σ hσ => by subst hσ; rfl)
      (List.replicate n SimSym.one) (fun σ hσ => List.eq_of_mem_replicate hσ)
      (s := SimSym.one) rfl SimSym.com
      (encVal w ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: midL g fr))
      (SimSym.endR :: List.replicate (t - 1) SimSym.bk)
    have r6 := reach_step_walkL_map
      (P := fun σ => σ = SimSym.one ∨ σ = SimSym.com ∨ σ = SimSym.bk)
      (f := fun _ => SimSym.bk)
      (show simStep (c := c) .suBack .com = some (.com, .suKill, false) from rfl)
      (fun σ hσ => pass_suKill hσ)
      (encVal w ++ List.replicate (j + 1) SimSym.bk)
      (fun σ hσ => by
        rcases List.mem_append.mp hσ with hσ | hσ
        · rcases mem_encVal hσ with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (List.eq_of_mem_replicate hσ)))
      SimSym.mid (midL g fr)
      ((List.replicate n SimSym.one).reverse ++
        SimSym.one :: SimSym.endR :: List.replicate (t - 1) SimSym.bk)
    have r7 := reach_step_walkL (P := fun σ => σ ≠ SimSym.endL)
      (show simStep (c := c) .suKill .mid = some (.mid, .retL, false) from rfl)
      (fun σ hσ => pass_retL hσ)
      fr.reverse (fun σ hσ => ((hfr σ (List.mem_reverse.mp hσ)).ne).1)
      SimSym.endL (List.replicate g SimSym.bk)
      (((encVal (c := c) w ++ List.replicate (j + 1) SimSym.bk).map fun _ => SimSym.bk).reverse ++
        SimSym.com :: ((List.replicate n SimSym.one).reverse ++
          SimSym.one :: SimSym.endR :: List.replicate (t - 1) SimSym.bk))
    refine Reach.trans (Reach.cast (by simp only [atMid, valR, he]; simp) rfl r1) ?_
    refine Reach.trans r2 ?_
    refine Reach.head r3 ?_
    refine Reach.head r4 ?_
    refine Reach.trans (Reach.cast (by simp [hL]) rfl r5) ?_
    refine Reach.trans (Reach.cast (by simp) rfl r6) ?_
    refine Reach.trans r7 ?_
    exact Reach.cast rfl
      (by simp [restCfg, valR, encNum, List.replicate_succ, replicate_glue]) (Reach.refl _)

/-- **`tail`**: walk to `endR`, erase it, and look at the last letter of the
value – a blank for an empty value, restored after a probe step to its right;
a lone separator, consumed; a digit, starting an erasure of the head block
down to its separator – then re-write `endR` and return to rest. -/
theorem norm_tail {p : CPos c} (h : codeAt p = .tail) {Q : SimQ c}
    (hQ : simStep Q .mid = some (dispatch p)) (g : ℕ) {fr : List (SimSym c)}
    (hfr : ∀ σ ∈ fr, FrameSym σ) (v : List ℕ) (j t : ℕ) :
    ∃ t', Reach (atMid Q g fr v j t) (restCfg g fr v.tail j t') := by
  have hd : simStep Q .mid = some (.mid, .tlGo, true) := by
    rw [hQ]; simp only [dispatch, h]
  rcases v with - | ⟨n, w⟩
  · -- empty value: probe the blank right of the erased `endR`, restore it
    refine ⟨t, ?_⟩
    have r1 := reach_step_walkR (P := fun σ => σ = SimSym.bk) hd
      (fun σ hσ => by subst hσ; rfl)
      (List.replicate (j + 1) SimSym.bk) (fun σ hσ => List.eq_of_mem_replicate hσ)
      (midL g fr) SimSym.endR (List.replicate t SimSym.bk)
    have r2 := lstep_left
      (show simStep (c := c) .tlGo .endR = some (.bk, .tlLook, false) from rfl)
      SimSym.bk (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr)
      (List.replicate t SimSym.bk)
    have r3 := lstep_right
      (show simStep (c := c) .tlLook .bk = some (.bk, .tlRest, true) from rfl)
      (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr) SimSym.bk
      (List.replicate t SimSym.bk)
    have r4 := lstep_left
      (show simStep (c := c) .tlRest .bk = some (.endR, .retL, false) from rfl)
      SimSym.bk (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr)
      (List.replicate t SimSym.bk)
    have r5 := reach_walkL (P := fun σ => σ ≠ SimSym.endL) (fun σ hσ => pass_retL hσ)
      (List.replicate j SimSym.bk ++ SimSym.mid :: fr.reverse)
      (fun σ hσ => by
        rcases List.mem_append.mp hσ with hσ | hσ
        · simp [List.eq_of_mem_replicate hσ]
        · rcases List.mem_cons.mp hσ with rfl | hσ
          · simp
          · exact ((hfr σ (List.mem_reverse.mp hσ)).ne).1)
      (s := SimSym.bk) (by simp) SimSym.endL (List.replicate g SimSym.bk)
      (SimSym.endR :: List.replicate t SimSym.bk)
    refine Reach.trans (Reach.cast (by simp [atMid, valR]) rfl r1) ?_
    refine Reach.head
      ((congrArg lstep (by simp [List.replicate_succ, replicate_glue])).trans r2) ?_
    refine Reach.head r3 ?_
    refine Reach.head r4 ?_
    exact Reach.cast (by simp [midL])
      (by simp [restCfg, valR, List.replicate_succ, replicate_glue]) r5
  rcases n with - | n
  · -- head block is a lone separator: consume it
    refine ⟨t + 1, ?_⟩
    have r1 := reach_step_walkR (P := fun σ => σ ≠ SimSym.endR) hd
      (fun σ hσ => pass_tlGo hσ)
      (List.replicate (j + 1) SimSym.bk ++ (encVal (0 :: w)).reverse)
      (fun σ hσ => by
        rcases List.mem_append.mp hσ with hσ | hσ
        · simp [List.eq_of_mem_replicate hσ]
        · rcases mem_encVal (List.mem_reverse.mp hσ) with rfl | rfl <;> simp)
      (midL g fr) SimSym.endR (List.replicate t SimSym.bk)
    have r2 := lstep_left
      (show simStep (c := c) .tlGo .endR = some (.bk, .tlLook, false) from rfl)
      SimSym.com
      (encVal w ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: midL g fr))
      (List.replicate t SimSym.bk)
    have r3 := reach_step_walkL (P := fun σ => σ ≠ SimSym.endL)
      (show simStep (c := c) .tlLook .com = some (.endR, .retL, false) from rfl)
      (fun σ hσ => pass_retL hσ)
      (encVal w ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: fr.reverse))
      (fun σ hσ => by
        rcases List.mem_append.mp hσ with hσ | hσ
        · rcases mem_encVal hσ with rfl | rfl <;> simp
        · rcases List.mem_append.mp hσ with hσ | hσ
          · simp [List.eq_of_mem_replicate hσ]
          · rcases List.mem_cons.mp hσ with rfl | hσ
            · simp
            · exact ((hfr σ (List.mem_reverse.mp hσ)).ne).1)
      SimSym.endL (List.replicate g SimSym.bk) (SimSym.bk :: List.replicate t SimSym.bk)
    refine Reach.trans r1 ?_
    refine Reach.head
      ((congrArg lstep (by simp [encNum, List.replicate_succ, replicate_glue])).trans r2) ?_
    refine Reach.trans (Reach.cast (by simp [midL]) rfl r3) ?_
    exact Reach.cast rfl
      (by simp [restCfg, valR, List.replicate_succ, replicate_glue]) (Reach.refl _)
  · -- a nonempty head block: erase its digits down to the separator
    refine ⟨n + t + 2, ?_⟩
    have r1 := reach_step_walkR (P := fun σ => σ ≠ SimSym.endR) hd
      (fun σ hσ => pass_tlGo hσ)
      (List.replicate (j + 1) SimSym.bk ++ (encVal ((n + 1) :: w)).reverse)
      (fun σ hσ => by
        rcases List.mem_append.mp hσ with hσ | hσ
        · simp [List.eq_of_mem_replicate hσ]
        · rcases mem_encVal (List.mem_reverse.mp hσ) with rfl | rfl <;> simp)
      (midL g fr) SimSym.endR (List.replicate t SimSym.bk)
    have r2 := lstep_left
      (show simStep (c := c) .tlGo .endR = some (.bk, .tlLook, false) from rfl)
      SimSym.one
      (List.replicate n SimSym.one ++
        SimSym.com :: (encVal w ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: midL g fr)))
      (List.replicate t SimSym.bk)
    have r3 := reach_step_walkL_map (P := fun σ => σ = SimSym.one) (f := fun _ => SimSym.bk)
      (show simStep (c := c) .tlLook .one = some (.bk, .tlOnes, false) from rfl)
      (fun σ hσ => by subst hσ; rfl)
      (List.replicate n SimSym.one) (fun σ hσ => List.eq_of_mem_replicate hσ)
      SimSym.com
      (encVal w ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: midL g fr))
      (SimSym.bk :: List.replicate t SimSym.bk)
    have r4 := reach_step_walkL (P := fun σ => σ ≠ SimSym.endL)
      (show simStep (c := c) .tlOnes .com = some (.endR, .retL, false) from rfl)
      (fun σ hσ => pass_retL hσ)
      (encVal w ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: fr.reverse))
      (fun σ hσ => by
        rcases List.mem_append.mp hσ with hσ | hσ
        · rcases mem_encVal hσ with rfl | rfl <;> simp
        · rcases List.mem_append.mp hσ with hσ | hσ
          · simp [List.eq_of_mem_replicate hσ]
          · rcases List.mem_cons.mp hσ with rfl | hσ
            · simp
            · exact ((hfr σ (List.mem_reverse.mp hσ)).ne).1)
      SimSym.endL (List.replicate g SimSym.bk)
      (List.replicate n SimSym.bk ++ SimSym.bk :: SimSym.bk :: List.replicate t SimSym.bk)
    refine Reach.trans r1 ?_
    refine Reach.head
      ((congrArg lstep (by simp [encNum, List.replicate_succ, replicate_glue])).trans r2) ?_
    refine Reach.trans (Reach.cast (by simp) rfl r3) ?_
    refine Reach.trans (Reach.cast (by simp [midL, replicate_glue]) rfl r4) ?_
    exact Reach.cast rfl
      (by simp [restCfg, valR, List.replicate_succ, replicate_glue]) (Reach.refl _)

/-- **`case`, zero or empty head**: walk to `endR`, look left of it – a blank
for an empty value, restored after a probe step to its right, or the head
block's separator, consumed – re-write `endR` and walk back to `mid` to
dispatch the first child on the tail of the value. -/
theorem norm_case_zero {p : CPos c} {f g₂ : Code} (h : codeAt p = .case f g₂)
    {Q : SimQ c} (hQ : simStep Q .mid = some (dispatch p)) (g : ℕ) {fr : List (SimSym c)}
    (_hfr : ∀ σ ∈ fr, FrameSym σ) {v : List ℕ} (hv : v.headI = 0) (j t : ℕ) :
    ∃ t', Reach (atMid Q g fr v j t) (atMid (.nSeekL (c₁ p)) g fr v.tail j t') := by
  have hd : simStep Q .mid = some (.mid, .caGo p, true) := by
    rw [hQ]; simp only [dispatch, h]
  rcases v with - | ⟨n, w⟩
  · -- empty value: probe the blank right of the erased `endR`, restore it
    refine ⟨t, ?_⟩
    have r1 := reach_step_walkR (P := fun σ => σ = SimSym.bk) hd
      (fun σ hσ => by subst hσ; rfl)
      (List.replicate (j + 1) SimSym.bk) (fun σ hσ => List.eq_of_mem_replicate hσ)
      (midL g fr) SimSym.endR (List.replicate t SimSym.bk)
    have r2 := lstep_left
      (show simStep (c := c) (.caGo p) .endR = some (.bk, .caLook p, false) from rfl)
      SimSym.bk (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr)
      (List.replicate t SimSym.bk)
    have r3 := lstep_right
      (show simStep (c := c) (.caLook p) .bk = some (.bk, .caRest p, true) from rfl)
      (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr) SimSym.bk
      (List.replicate t SimSym.bk)
    have r4 := lstep_left
      (show simStep (c := c) (.caRest p) .bk = some (.endR, .nSeekL (c₁ p), false) from rfl)
      SimSym.bk (List.replicate j SimSym.bk ++ SimSym.mid :: midL g fr)
      (List.replicate t SimSym.bk)
    have r5 := reach_walkL (P := fun σ => σ ≠ SimSym.mid)
      (fun σ hσ => pass_nSeekL (p := c₁ p) hσ)
      (List.replicate j SimSym.bk)
      (fun σ hσ => by simp [List.eq_of_mem_replicate hσ])
      (s := SimSym.bk) (by simp) SimSym.mid (midL g fr)
      (SimSym.endR :: List.replicate t SimSym.bk)
    refine Reach.trans (Reach.cast (by simp [atMid, valR]) rfl r1) ?_
    refine Reach.head
      ((congrArg lstep (by simp [List.replicate_succ, replicate_glue])).trans r2) ?_
    refine Reach.head r3 ?_
    refine Reach.head r4 ?_
    exact Reach.cast rfl (by simp [atMid, valR, replicate_glue]) r5
  · -- head block is a lone separator: consume it
    obtain rfl : n = 0 := hv
    refine ⟨t + 1, ?_⟩
    have r1 := reach_step_walkR (P := fun σ => σ ≠ SimSym.endR) hd
      (fun σ hσ => pass_caGo hσ)
      (List.replicate (j + 1) SimSym.bk ++ (encVal (0 :: w)).reverse)
      (fun σ hσ => by
        rcases List.mem_append.mp hσ with hσ | hσ
        · simp [List.eq_of_mem_replicate hσ]
        · rcases mem_encVal (List.mem_reverse.mp hσ) with rfl | rfl <;> simp)
      (midL g fr) SimSym.endR (List.replicate t SimSym.bk)
    have r2 := lstep_left
      (show simStep (c := c) (.caGo p) .endR = some (.bk, .caLook p, false) from rfl)
      SimSym.com
      (encVal w ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: midL g fr))
      (List.replicate t SimSym.bk)
    have r3 := reach_step_walkL (P := fun σ => σ ≠ SimSym.mid)
      (show simStep (c := c) (.caLook p) .com = some (.endR, .nSeekL (c₁ p), false) from rfl)
      (fun σ hσ => pass_nSeekL (p := c₁ p) hσ)
      (encVal w ++ List.replicate (j + 1) SimSym.bk)
      (fun σ hσ => by
        rcases List.mem_append.mp hσ with hσ | hσ
        · rcases mem_encVal hσ with rfl | rfl <;> simp
        · simp [List.eq_of_mem_replicate hσ])
      SimSym.mid (midL g fr) (SimSym.bk :: List.replicate t SimSym.bk)
    refine Reach.trans r1 ?_
    refine Reach.head ((congrArg lstep (by simp [encNum])).trans r2) ?_
    refine Reach.trans (Reach.cast (by simp) rfl r3) ?_
    exact Reach.cast rfl
      (by simp [atMid, valR, List.replicate_succ, replicate_glue]) (Reach.refl _)

/-- **`case`, positive head**: walk to `endR`, find a digit left of it – the
head block is nonempty – consume it as `endR` and walk back to `mid` to
dispatch the second child on the decremented head. -/
theorem norm_case_succ {p : CPos c} {f g₂ : Code} (h : codeAt p = .case f g₂)
    {Q : SimQ c} (hQ : simStep Q .mid = some (dispatch p)) (g : ℕ) {fr : List (SimSym c)}
    (_hfr : ∀ σ ∈ fr, FrameSym σ) {v : List ℕ} {y : ℕ} (hv : v.headI = y + 1) (j t : ℕ) :
    ∃ t', Reach (atMid Q g fr v j t) (atMid (.nSeekL (c₂ p)) g fr (y :: v.tail) j t') := by
  have hd : simStep Q .mid = some (.mid, .caGo p, true) := by
    rw [hQ]; simp only [dispatch, h]
  rcases v with - | ⟨n, w⟩
  · exact absurd hv (by simp)
  obtain rfl : n = y + 1 := hv
  refine ⟨t + 1, ?_⟩
  have r1 := reach_step_walkR (P := fun σ => σ ≠ SimSym.endR) hd
    (fun σ hσ => pass_caGo hσ)
    (List.replicate (j + 1) SimSym.bk ++ (encVal ((y + 1) :: w)).reverse)
    (fun σ hσ => by
      rcases List.mem_append.mp hσ with hσ | hσ
      · simp [List.eq_of_mem_replicate hσ]
      · rcases mem_encVal (List.mem_reverse.mp hσ) with rfl | rfl <;> simp)
    (midL g fr) SimSym.endR (List.replicate t SimSym.bk)
  have r2 := lstep_left
    (show simStep (c := c) (.caGo p) .endR = some (.bk, .caLook p, false) from rfl)
    SimSym.one
    (List.replicate y SimSym.one ++
      SimSym.com :: (encVal w ++ (List.replicate (j + 1) SimSym.bk ++ SimSym.mid :: midL g fr)))
    (List.replicate t SimSym.bk)
  have r3 := reach_step_walkL (P := fun σ => σ ≠ SimSym.mid)
    (show simStep (c := c) (.caLook p) .one = some (.endR, .nSeekL (c₂ p), false) from rfl)
    (fun σ hσ => pass_nSeekL (p := c₂ p) hσ)
    (List.replicate y SimSym.one ++ SimSym.com :: (encVal w ++ List.replicate (j + 1) SimSym.bk))
    (fun σ hσ => by
      rcases List.mem_append.mp hσ with hσ | hσ
      · simp [List.eq_of_mem_replicate hσ]
      · rcases List.mem_cons.mp hσ with rfl | hσ
        · simp
        · rcases List.mem_append.mp hσ with hσ | hσ
          · rcases mem_encVal hσ with rfl | rfl <;> simp
          · simp [List.eq_of_mem_replicate hσ])
    SimSym.mid (midL g fr) (SimSym.bk :: List.replicate t SimSym.bk)
  refine Reach.trans r1 ?_
  refine Reach.head
    ((congrArg lstep (by simp [encNum, List.replicate_succ, replicate_glue])).trans r2) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r3) ?_
  exact Reach.cast rfl
    (by simp [atMid, valR, encNum, List.replicate_succ, replicate_glue]) (Reach.refl _)

/-- **`fix` push**: walk left over the frames to `endL`, write the `fix`
header over it, re-write `endL` one cell into the left blanks, and walk back
to `mid` to dispatch the body: the frame region gains a bare header, the left
blanks lose a cell. -/
theorem norm_fix {p : CPos c} {f : Code} (h : codeAt p = .fix f)
    {Q : SimQ c} (hQ : simStep Q .mid = some (dispatch p)) (g : ℕ)
    {fr : List (SimSym c)} (hfr : ∀ σ ∈ fr, FrameSym σ) (v : List ℕ) (j t : ℕ) :
    Reach (atMid Q g fr v j t)
      (atMid (.nSeekR (c₁ p)) (g - 1) (SimSym.hFix (c₁ p) :: fr) v j t) := by
  have hd : simStep Q .mid = some (.mid, .fiHdr p, false) := by
    rw [hQ]; simp only [dispatch, h]
  -- to `endL`, over the frame region
  have r1 := reach_step_walkL (P := fun σ => σ ≠ SimSym.endL) hd
    (fun σ hσ => pass_fiHdr hσ) fr.reverse
    (fun σ hσ => ((hfr σ (List.mem_reverse.mp hσ)).ne).1)
    SimSym.endL (List.replicate g SimSym.bk) (valR v j t)
  -- write the header over `endL`, re-write `endL` one cell left
  have r2 := lstep_left_pad
    (show simStep (c := c) (.fiHdr p) .endL = some (.hFix (c₁ p), .fiHdrS p, false) from rfl)
    g (fr.reverse.reverse ++ SimSym.mid :: valR v j t)
  have r3 := lstep_right
    (show simStep (c := c) (.fiHdrS p) .bk = some (.endL, .nSeekR (c₁ p), true) from rfl)
    (List.replicate (g - 1) SimSym.bk) (SimSym.hFix (c₁ p))
    (fr.reverse.reverse ++ SimSym.mid :: valR v j t)
  -- back to `mid`, over the grown frame region
  have r4 := reach_walkR (P := fun σ => σ ≠ SimSym.mid)
    (fun σ hσ => pass_nSeekR (p := c₁ p) hσ)
    fr.reverse.reverse (fun σ hσ => ((hfr σ (by simpa using hσ)).ne).2.1)
    (s := SimSym.hFix (c₁ p)) (by simp)
    (SimSym.endL :: List.replicate (g - 1) SimSym.bk) SimSym.mid (valR v j t)
  refine Reach.trans r1 (Reach.head r2 (Reach.head r3 (Reach.cast rfl ?_ r4)))
  simp [midL]

end HaltHard

end DescriptiveComplexity
