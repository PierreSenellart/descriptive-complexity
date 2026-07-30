/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.SimNorm

/-!
# The `cons` push, and the assembled dispatch simulation

The one non-destructive copy of the machine: dispatching a `cons` copies the
value into a fresh `cons₁` frame at `endL`, priming each letter on the way so
the scan finds the next one, then unprimes the value and dispatches the first
child. `DescriptiveComplexity.HaltHard.cp_loop` is the copy loop – one
iteration primes one letter, carries it home and returns – and
`DescriptiveComplexity.HaltHard.norm_cons` wraps it with the header write and
the unpriming sweep.

With every code shape handled,
`DescriptiveComplexity.HaltHard.sim_norm` assembles the whole dispatch phase:
from the dispatch of the code at `p`, the machine reaches the resting
configuration of `DescriptiveComplexity.HaltHard.pStepNormal p k v`, by
induction on the size of the dispatched code.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec

variable {c : Code}

/-! ### Priming -/

/-- Marking a letter as copied. -/
def prime : SimSym c → SimSym c
  | .one => .one'
  | .com => .com'
  | σ => σ

/-- Unmarking a letter. -/
def unprime : SimSym c → SimSym c
  | .one' => .one
  | .com' => .com
  | σ => σ

theorem unprime_prime {σ : SimSym c} (h : σ = .one ∨ σ = .com) :
    unprime (prime σ) = σ := by
  rcases h with rfl | rfl <;> rfl

theorem prime_ne {σ : SimSym c} (h : σ = .one ∨ σ = .com) :
    prime σ ≠ .endL ∧ prime σ ≠ .mid ∧ prime σ ≠ .endR := by
  rcases h with rfl | rfl <;> exact ⟨by simp [prime], by simp [prime], by simp [prime]⟩

/-! ### Fused step-and-walk combinators -/

section StepWalk

variable {q q₂ : SimQ c} {σ σ' : SimSym c} {P : SimSym c → Prop} {f : SimSym c → SimSym c}

/-- One left move, then a leftward walk over passed letters: the fused form
every carry uses, sound whether or not the walked span is empty. -/
theorem reach_step_then_walkL (hstep : simStep q σ = some (σ', q₂, false))
    (hpass : ∀ τ, P τ → simStep q₂ τ = some (τ, q₂, false))
    (w : List (SimSym c)) (hw : ∀ τ ∈ w, P τ) (x : SimSym c) (L R : List (SimSym c)) :
    Reach ⟨q, w ++ x :: L, σ, R⟩ ⟨q₂, L, x, w.reverse ++ σ' :: R⟩ := by
  rcases w with - | ⟨a, w⟩
  · exact Reach.single (lstep_left hstep x L R)
  · refine Reach.head (lstep_left hstep a (w ++ x :: L) R) ?_
    have h := reach_walkL hpass w (fun τ hτ => hw τ (by simp [hτ]))
      (hw a (by simp)) x L (σ' :: R)
    refine Reach.cast rfl ?_ h
    simp

/-- One right move, then a rightward walk over passed letters. -/
theorem reach_step_then_walkR (hstep : simStep q σ = some (σ', q₂, true))
    (hpass : ∀ τ, P τ → simStep q₂ τ = some (τ, q₂, true))
    (w : List (SimSym c)) (hw : ∀ τ ∈ w, P τ) (x : SimSym c) (L R : List (SimSym c)) :
    Reach ⟨q, L, σ, w ++ x :: R⟩ ⟨q₂, w.reverse ++ σ' :: L, x, R⟩ := by
  rcases w with - | ⟨a, w⟩
  · exact Reach.single (lstep_right hstep L x R)
  · refine Reach.head (lstep_right hstep L a (w ++ x :: R)) ?_
    have h := reach_walkR hpass w (fun τ hτ => hw τ (by simp [hτ]))
      (hw a (by simp)) (σ' :: L) x R
    refine Reach.cast rfl ?_ h
    simp

/-- One right move, then a rightward transducing walk. -/
theorem reach_step_then_walkR_map (hstep : simStep q σ = some (σ', q₂, true))
    (hpass : ∀ τ, P τ → simStep q₂ τ = some (f τ, q₂, true))
    (w : List (SimSym c)) (hw : ∀ τ ∈ w, P τ) (x : SimSym c) (L R : List (SimSym c)) :
    Reach ⟨q, L, σ, w ++ x :: R⟩ ⟨q₂, (w.map f).reverse ++ σ' :: L, x, R⟩ := by
  rcases w with - | ⟨a, w⟩
  · exact Reach.single (lstep_right hstep L x R)
  · refine Reach.head (lstep_right hstep L a (w ++ x :: R)) ?_
    have h := reach_walkR_map hpass w (fun τ hτ => hw τ (by simp [hτ]))
      (hw a (by simp)) (σ' :: L) x R
    refine Reach.cast rfl ?_ h
    simp

end StepWalk

/-! ### Pass lemmas for the copy -/

section Pass

variable {σ : SimSym c} {p : CPos c}

theorem pass_cpCar₁ (h : σ ≠ .endL) :
    simStep (.cpCar₁ p) σ = some (σ, .cpCar₁ p, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_cpCarC (h : σ ≠ .endL) :
    simStep (.cpCarC p) σ = some (σ, .cpCarC p, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_cpBack (h : σ ≠ .mid) :
    simStep (.cpBack p) σ = some (σ, .cpBack p, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_cpHdr (h : σ ≠ .endL) :
    simStep (.cpHdr p) σ = some (σ, .cpHdr p, false) := by
  cases σ <;> first | rfl | exact absurd rfl h

theorem pass_cpUnp (h : σ ≠ .mid) :
    simStep (.cpUnp p) σ = some (σ, .cpUnp p, true) := by
  cases σ <;> first | rfl | exact absurd rfl h

/-- The scan passes blanks and primed letters. -/
theorem pass_cpFetch (h : σ = .bk ∨ σ = .one' ∨ σ = .com') :
    simStep (.cpFetch p) σ = some (σ, .cpFetch p, true) := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- The unpriming sweep, as a transducing pass. -/
theorem pass_cpUnp₂ (h : σ = .bk ∨ σ = .one' ∨ σ = .com') :
    simStep (.cpUnp₂ p) σ = some (unprime σ, .cpUnp₂ p, true) := by
  rcases h with rfl | rfl | rfl <;> rfl

end Pass

/-! ### The copy loop -/

/-- **One iteration of the copy**: with the scan on the next unprimed letter,
prime it, carry it home to `endL`, write it by the endL-shift and walk back
onto the gap – the loop entry one letter further. Stated over an abstract
carry state so the digit and separator instances share the proof. -/
theorem cp_iter (p : CPos c) {u : SimSym c} {Qcar : SimQ c}
    (hu : u = SimSym.one ∨ u = SimSym.com)
    (h1 : simStep (.cpFetch p) u = some (prime u, Qcar, false))
    (h2 : ∀ τ : SimSym c, τ ≠ SimSym.endL → simStep Qcar τ = some (τ, Qcar, false))
    (h3 : simStep Qcar SimSym.endL = some (u, .cpEndS p, false))
    (P : List (SimSym c)) (hP : ∀ σ ∈ P, σ = SimSym.one ∨ σ = SimSym.com)
    (g : ℕ) {fr : List (SimSym c)} (hfr : ∀ σ ∈ fr, FrameSym σ)
    (j : ℕ) (Y : List (SimSym c)) :
    Reach
      ⟨.cpFetch p,
        (List.replicate j SimSym.bk ++ P.map prime).reverse ++
          SimSym.bk :: SimSym.mid ::
            (fr.reverse ++ (P ++ SimSym.endL :: List.replicate g SimSym.bk)),
        u, Y⟩
      ⟨.cpFetch p,
        SimSym.mid ::
          (fr.reverse ++ ((P ++ [u]) ++ SimSym.endL :: List.replicate (g - 1) SimSym.bk)),
        SimSym.bk,
        List.replicate j SimSym.bk ++ ((P ++ [u]).map prime ++ Y)⟩ := by
  -- prime the letter and carry it home
  have r2 := reach_step_then_walkL h1 h2
    ((List.replicate j SimSym.bk ++ P.map prime).reverse ++
      SimSym.bk :: SimSym.mid :: (fr.reverse ++ P))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases List.mem_append.mp (List.mem_reverse.mp hτ) with hτ | hτ
        · simp [List.eq_of_mem_replicate hτ]
        · obtain ⟨τ', hτ', rfl⟩ := List.mem_map.mp hτ
          exact (prime_ne (hP τ' hτ')).1
      · rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        rcases List.mem_append.mp hτ with hτ | hτ
        · exact ((hfr τ (List.mem_reverse.mp hτ)).ne).1
        · rcases hP τ hτ with rfl | rfl <;> simp)
    SimSym.endL (List.replicate g SimSym.bk) Y
  -- write it at endL, shift endL left
  have r3 := lstep_left_pad h3 g
    (((List.replicate j SimSym.bk ++ P.map prime).reverse ++
      SimSym.bk :: SimSym.mid :: (fr.reverse ++ P)).reverse ++ prime u :: Y)
  have r4 := lstep_right
    (show simStep (c := c) (.cpEndS p) SimSym.bk = some (.endL, .cpBack p, true) from rfl)
    (List.replicate (g - 1) SimSym.bk) u
    (((List.replicate j SimSym.bk ++ P.map prime).reverse ++
      SimSym.bk :: SimSym.mid :: (fr.reverse ++ P)).reverse ++ prime u :: Y)
  -- walk right back onto mid
  have r5 := reach_step_then_walkR
    (pass_cpBack (p := p) (σ := u) (by rcases hu with rfl | rfl <;> simp))
    (P := fun σ => σ ≠ SimSym.mid) (fun τ hτ => pass_cpBack hτ)
    (P.reverse ++ fr)
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases hP τ (List.mem_reverse.mp hτ) with rfl | rfl <;> simp
      · exact ((hfr τ hτ).ne).2.1)
    SimSym.mid (SimSym.endL :: List.replicate (g - 1) SimSym.bk)
    (SimSym.bk :: (List.replicate j SimSym.bk ++ (P.map prime ++ prime u :: Y)))
  -- one step onto the gap
  have r6 := lstep_right
    (show simStep (c := c) (.cpBack p) SimSym.mid = some (SimSym.mid, .cpFetch p, true)
      from rfl)
    ((P.reverse ++ fr).reverse ++ u :: SimSym.endL :: List.replicate (g - 1) SimSym.bk)
    SimSym.bk
    (List.replicate j SimSym.bk ++ (P.map prime ++ prime u :: Y))
  refine Reach.trans (Reach.cast (by simp) rfl r2) ?_
  refine Reach.head r3 ?_
  refine Reach.head r4 ?_
  refine Reach.trans (Reach.cast (by simp) rfl r5) ?_
  refine Reach.trans (Reach.cast (by simp) rfl (Reach.single r6)) ?_
  exact Reach.cast (by simp) rfl (Reach.refl _)

/-- **One pass of the copy loop, iterated to the end of the value**: with the
prefix `P` already primed and copied and `U` still to do, the scan fetches
each letter of `U` in turn, carries it to `endL`, writes it by the endL-shift
and returns; the loop ends with the scan on `endR`. The copied content sits
between `endL` and the old frame region, spatially reversed – which is what
makes it `encVal v` when the value region held `(encVal v).reverse`. -/
theorem cp_loop (p : CPos c) : ∀ (U P : List (SimSym c)),
    (∀ σ ∈ U, σ = SimSym.one ∨ σ = SimSym.com) →
    (∀ σ ∈ P, σ = SimSym.one ∨ σ = SimSym.com) →
    ∀ (g : ℕ) {fr : List (SimSym c)}, (∀ σ ∈ fr, FrameSym σ) →
    ∀ (j t : ℕ),
    Reach
      ⟨.cpFetch p,
        SimSym.mid :: (fr.reverse ++ (P ++ SimSym.endL :: List.replicate g SimSym.bk)),
        SimSym.bk,
        List.replicate j SimSym.bk ++
          (P.map prime ++ (U ++ SimSym.endR :: List.replicate t SimSym.bk))⟩
      ⟨.cpFetch p,
        (List.replicate j SimSym.bk ++ (P ++ U).map prime).reverse ++
          SimSym.bk :: SimSym.mid ::
            (fr.reverse ++
              ((P ++ U) ++ SimSym.endL :: List.replicate (g - U.length) SimSym.bk)),
        SimSym.endR, List.replicate t SimSym.bk⟩ := by
  intro U
  induction U with
  | nil =>
    intro P _ hP g fr hfr j t
    have h := reach_walkR (P := fun σ => σ = SimSym.bk ∨ σ = SimSym.one' ∨ σ = SimSym.com')
      (fun σ hσ => pass_cpFetch (p := p) hσ)
      (List.replicate j SimSym.bk ++ P.map prime)
      (by
        intro σ hσ
        rcases List.mem_append.mp hσ with hσ | hσ
        · exact Or.inl (List.eq_of_mem_replicate hσ)
        · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hσ
          rcases hP τ hτ with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl))
      (s := SimSym.bk) (Or.inl rfl)
      (SimSym.mid :: (fr.reverse ++ (P ++ SimSym.endL :: List.replicate g SimSym.bk)))
      SimSym.endR (List.replicate t SimSym.bk)
    refine Reach.cast (by simp) (by simp) h
  | cons u U' ih =>
    intro P hU hP g fr hfr j t
    have hu : u = SimSym.one ∨ u = SimSym.com := hU u (by simp)
    have hU' : ∀ σ ∈ U', σ = SimSym.one ∨ σ = SimSym.com :=
      fun σ hσ => hU σ (by simp [hσ])
    have hP' : ∀ σ ∈ P ++ [u], σ = SimSym.one ∨ σ = SimSym.com := by
      intro σ hσ
      rcases List.mem_append.mp hσ with hσ | hσ
      · exact hP σ hσ
      · rw [List.mem_singleton.mp hσ]; exact hu
    -- the fetch: scan right to the first unprimed letter
    have r1 := reach_walkR (P := fun σ => σ = SimSym.bk ∨ σ = SimSym.one' ∨ σ = SimSym.com')
      (fun σ hσ => pass_cpFetch (p := p) hσ)
      (List.replicate j SimSym.bk ++ P.map prime)
      (by
        intro σ hσ
        rcases List.mem_append.mp hσ with hσ | hσ
        · exact Or.inl (List.eq_of_mem_replicate hσ)
        · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hσ
          rcases hP τ hτ with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl))
      (s := SimSym.bk) (Or.inl rfl)
      (SimSym.mid :: (fr.reverse ++ (P ++ SimSym.endL :: List.replicate g SimSym.bk)))
      u (U' ++ SimSym.endR :: List.replicate t SimSym.bk)
    -- one iteration of the copy
    have riter : Reach
        ⟨.cpFetch p,
          (List.replicate j SimSym.bk ++ P.map prime).reverse ++
            SimSym.bk :: SimSym.mid ::
              (fr.reverse ++ (P ++ SimSym.endL :: List.replicate g SimSym.bk)),
          u, U' ++ SimSym.endR :: List.replicate t SimSym.bk⟩
        ⟨.cpFetch p,
          SimSym.mid ::
            (fr.reverse ++ ((P ++ [u]) ++ SimSym.endL :: List.replicate (g - 1) SimSym.bk)),
          SimSym.bk,
          List.replicate j SimSym.bk ++
            ((P ++ [u]).map prime ++ (U' ++ SimSym.endR :: List.replicate t SimSym.bk))⟩ := by
      rcases hu with rfl | rfl
      · exact cp_iter p (Or.inl rfl) rfl (fun τ hτ => pass_cpCar₁ hτ) rfl P hP g hfr j _
      · exact cp_iter p (Or.inr rfl) rfl (fun τ hτ => pass_cpCarC hτ) rfl P hP g hfr j _
    have rih := ih (P ++ [u]) hU' hP' (g - 1) hfr j t
    refine Reach.trans (Reach.cast (by simp) rfl r1) ?_
    refine Reach.trans riter ?_
    refine Reach.cast rfl ?_ rih
    have hlen : g - 1 - U'.length = g - (U'.length + 1) := by omega
    simp [hlen]

/-- Unpriming undoes priming, letterwise on a value word. -/
theorem unprime_map_prime {l : List (SimSym c)}
    (hl : ∀ σ ∈ l, σ = SimSym.one ∨ σ = SimSym.com) :
    (l.map prime).map unprime = l := by
  rw [List.map_map]
  refine List.map_congr_left (fun σ hσ => unprime_prime (hl σ hσ)) |>.trans l.map_id

/-- **The `cons` dispatch**: copy the value into a fresh `cons₁` frame at
`endL` – mirrored back to straight by the endL-shifts – write the header,
unprime the value, and dispatch the first child. -/
theorem norm_cons {p : CPos c} {f fs : Code} (h : codeAt p = .cons f fs) {Q : SimQ c}
    (hQ : simStep Q .mid = some (dispatch p)) (g : ℕ) {fr : List (SimSym c)}
    (hfr : ∀ σ ∈ fr, FrameSym σ) (v : List ℕ) (j t : ℕ) :
    Reach (atMid Q g fr v j t)
      (atMid (.nSeekL (c₁ p)) (g - ((encVal (c := c) v).length + 1))
        (SimSym.hCons₁ (c₂ p) :: (encVal v ++ fr)) v j t) := by
  have hd : simStep Q .mid = some (.mid, .cpFetch p, true) := by
    rw [hQ]; simp only [dispatch, h]
  have hEv : ∀ σ ∈ (encVal (c := c) v).reverse, σ = SimSym.one ∨ σ = SimSym.com :=
    fun σ hσ => mem_encVal (List.mem_reverse.mp hσ)
  -- enter the gap
  have r1 := lstep_right hd (midL g fr) SimSym.bk
    (List.replicate j SimSym.bk ++
      ((encVal v).reverse ++ SimSym.endR :: List.replicate t SimSym.bk))
  -- the copy loop
  have r2 := cp_loop p (encVal v).reverse [] hEv (by simp) g hfr j t
  -- write the header at endL
  have r3 := reach_step_then_walkL
    (show simStep (c := c) (.cpFetch p) SimSym.endR = some (.endR, .cpHdr p, false) from rfl)
    (P := fun σ => σ ≠ SimSym.endL) (fun τ hτ => pass_cpHdr hτ)
    ((List.replicate j SimSym.bk ++ ((encVal v).reverse).map prime).reverse ++
      SimSym.bk :: SimSym.mid :: (fr.reverse ++ (encVal v).reverse))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases List.mem_append.mp (List.mem_reverse.mp hτ) with hτ | hτ
        · simp [List.eq_of_mem_replicate hτ]
        · obtain ⟨τ', hτ', rfl⟩ := List.mem_map.mp hτ
          exact (prime_ne (hEv τ' hτ')).1
      · rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        rcases List.mem_cons.mp hτ with rfl | hτ
        · simp
        rcases List.mem_append.mp hτ with hτ | hτ
        · exact ((hfr τ (List.mem_reverse.mp hτ)).ne).1
        · rcases hEv τ hτ with rfl | rfl <;> simp)
    SimSym.endL
    (List.replicate (g - ((encVal (c := c) v).reverse).length) SimSym.bk)
    (List.replicate t SimSym.bk)
  -- shift endL left of the header
  have r4 := lstep_left_pad
    (show simStep (c := c) (.cpHdr p) SimSym.endL =
      some (.hCons₁ (c₂ p), .cpHdrS p, false) from rfl)
    (g - ((encVal (c := c) v).reverse).length)
    (((List.replicate j SimSym.bk ++ ((encVal v).reverse).map prime).reverse ++
      SimSym.bk :: SimSym.mid :: (fr.reverse ++ (encVal v).reverse)).reverse ++
      SimSym.endR :: List.replicate t SimSym.bk)
  have r5 := lstep_right
    (show simStep (c := c) (.cpHdrS p) SimSym.bk = some (.endL, .cpUnp p, true) from rfl)
    (List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    (SimSym.hCons₁ (c₂ p))
    (((List.replicate j SimSym.bk ++ ((encVal v).reverse).map prime).reverse ++
      SimSym.bk :: SimSym.mid :: (fr.reverse ++ (encVal v).reverse)).reverse ++
      SimSym.endR :: List.replicate t SimSym.bk)
  -- walk right to mid
  have r6 := reach_step_then_walkR
    (pass_cpUnp (p := p) (σ := SimSym.hCons₁ (c₂ p)) (by simp))
    (P := fun σ => σ ≠ SimSym.mid) (fun τ hτ => pass_cpUnp hτ)
    ((encVal (c := c) v ++ fr))
    (by
      intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · rcases mem_encVal hτ with rfl | rfl <;> simp
      · exact ((hfr τ hτ).ne).2.1)
    SimSym.mid
    (SimSym.endL ::
      List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    (SimSym.bk :: (List.replicate j SimSym.bk ++ ((encVal v).reverse).map prime) ++
      SimSym.endR :: List.replicate t SimSym.bk)
  -- the unpriming sweep
  have r7 := reach_step_then_walkR_map
    (show simStep (c := c) (.cpUnp p) SimSym.mid = some (.mid, .cpUnp₂ p, true) from rfl)
    (P := fun σ => σ = SimSym.bk ∨ σ = SimSym.one' ∨ σ = SimSym.com')
    (f := unprime) (fun τ hτ => pass_cpUnp₂ hτ)
    (SimSym.bk :: (List.replicate j SimSym.bk ++ ((encVal v).reverse).map prime))
    (by
      intro τ hτ
      rcases List.mem_cons.mp hτ with rfl | hτ
      · exact Or.inl rfl
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact Or.inl (List.eq_of_mem_replicate hτ)
      · obtain ⟨τ', hτ', rfl⟩ := List.mem_map.mp hτ
        rcases hEv τ' hτ' with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl))
    SimSym.endR
    (((encVal (c := c) v ++ fr)).reverse ++ SimSym.hCons₁ (c₂ p) ::
      SimSym.endL ::
        List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    (List.replicate t SimSym.bk)
  -- hand over to the child's seek
  have r8 := reach_step_then_walkL
    (show simStep (c := c) (.cpUnp₂ p) SimSym.endR =
      some (.endR, .nSeekL (c₁ p), false) from rfl)
    (P := fun σ => σ ≠ SimSym.mid) (fun τ hτ => pass_nSeekL hτ)
    ((((SimSym.bk :: (List.replicate j SimSym.bk ++
        ((encVal v).reverse).map prime)).map unprime).reverse))
    (by
      intro τ hτ
      rw [List.mem_reverse] at hτ
      obtain ⟨τ', hτ', rfl⟩ := List.mem_map.mp hτ
      rcases List.mem_cons.mp hτ' with rfl | hτ'
      · simp [unprime]
      rcases List.mem_append.mp hτ' with hτ' | hτ'
      · simp [List.eq_of_mem_replicate hτ', unprime]
      · obtain ⟨τ'', hτ'', rfl⟩ := List.mem_map.mp hτ'
        rcases hEv τ'' hτ'' with rfl | rfl <;> simp [prime, unprime])
    SimSym.mid
    (((encVal (c := c) v ++ fr)).reverse ++ SimSym.hCons₁ (c₂ p) ::
      SimSym.endL ::
        List.replicate (g - ((encVal (c := c) v).reverse).length - 1) SimSym.bk)
    (List.replicate t SimSym.bk)
  -- glue
  have hup : ((SimSym.bk :: (List.replicate j SimSym.bk ++
      ((encVal (c := c) v).reverse).map prime)).map unprime) =
      SimSym.bk :: (List.replicate j SimSym.bk ++ (encVal v).reverse) := by
    have h1 : (List.replicate j (SimSym.bk (c := c))).map unprime =
        List.replicate j SimSym.bk := by
      simp [List.map_replicate, unprime]
    have h2 := unprime_map_prime hEv
    simp only [List.map_cons, List.map_append, h1, h2]
    rfl
  refine Reach.head (Eq.trans (congrArg lstep (by simp [List.replicate_succ])) r1) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r2) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r3) ?_
  refine Reach.head r4 ?_
  refine Reach.head r5 ?_
  refine Reach.trans (Reach.cast (by simp) rfl r6) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r7) ?_
  refine Reach.trans (Reach.cast (by simp) rfl r8) ?_
  refine Reach.cast ?_ rfl (Reach.refl _)
  have hlen : g - (encVal (c := c) v).length - 1 =
      g - ((encVal (c := c) v).length + 1) := by omega
  have hmapc : List.map (unprime ∘ prime) (encVal (c := c) v) = encVal v :=
    (List.map_congr_left fun σ hσ => unprime_prime (mem_encVal hσ)).trans
      (List.map_id _)
  simp [midL, hlen, List.replicate_succ, unprime, hmapc]

/-! ### Reading `pStepNormal` off the code shape -/

section Shapes

variable {p : CPos c} {k : PCont c} {v : List ℕ}

theorem pStepNormal_zero' (h : codeAt p = .zero') : pStepNormal p k v = (k, 0 :: v) := by
  rw [pStepNormal.eq_def]
  split <;> simp_all

theorem pStepNormal_succ (h : codeAt p = .succ) : pStepNormal p k v = (k, [v.headI.succ]) := by
  rw [pStepNormal.eq_def]
  split <;> simp_all

theorem pStepNormal_tail (h : codeAt p = .tail) : pStepNormal p k v = (k, v.tail) := by
  rw [pStepNormal.eq_def]
  split <;> simp_all

theorem pStepNormal_cons {f fs : Code} (h : codeAt p = .cons f fs) :
    pStepNormal p k v = pStepNormal (c₁ p) (.cons₁ (c₂ p) v k) v := by
  rw [pStepNormal.eq_def]
  split <;> simp_all

theorem pStepNormal_comp {f g₂ : Code} (h : codeAt p = .comp f g₂) :
    pStepNormal p k v = pStepNormal (c₂ p) (.comp (c₁ p) k) v := by
  rw [pStepNormal.eq_def]
  split <;> simp_all

theorem pStepNormal_case_zero {f g₂ : Code} (h : codeAt p = .case f g₂)
    (hv : v.headI = 0) : pStepNormal p k v = pStepNormal (c₁ p) k v.tail := by
  rw [pStepNormal.eq_def]
  split <;> simp_all

theorem pStepNormal_case_succ {f g₂ : Code} {y : ℕ} (h : codeAt p = .case f g₂)
    (hv : v.headI = y + 1) : pStepNormal p k v = pStepNormal (c₂ p) k (y :: v.tail) := by
  rw [pStepNormal.eq_def]
  split <;> simp_all

theorem pStepNormal_fix {f : Code} (h : codeAt p = .fix f) :
    pStepNormal p k v = pStepNormal (c₁ p) (.fix (c₁ p) k) v := by
  rw [pStepNormal.eq_def]
  split <;> simp_all

end Shapes

/-! ### The assembled dispatch phase -/

/-- Every code has size at least one. -/
theorem one_le_sizeOf_code (c' : Code) : 1 ≤ sizeOf c' := by
  cases c' <;> simp <;> omega

/-- **The dispatch phase of the simulation**: from the dispatch of the code
at `p` – any state that hands over to `dispatch p` on `mid` – the machine
reaches the resting configuration of `pStepNormal p k v`, by induction on the
size of the dispatched code. -/
theorem sim_norm : ∀ (n : ℕ) (p : CPos c), sizeOf (codeAt p) ≤ n →
    ∀ (k : PCont c) (v : List ℕ) {Q : SimQ c}, simStep Q .mid = some (dispatch p) →
    ∀ (g : ℕ) {fr : List (SimSym c)}, FrameSeg k fr → ∀ (j t : ℕ),
    ∃ g' fr' j' t', FrameSeg (pStepNormal p k v).1 fr' ∧
      Reach (atMid Q g fr v j t) (restCfg g' fr' (pStepNormal p k v).2 j' t') := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have := one_le_sizeOf_code (codeAt p)
    omega
  | succ n ihn =>
    intro p hp k v Q hQ g fr hfr j t
    rcases hsh : codeAt p with - | - | - | ⟨f, fs⟩ | ⟨f, g₂⟩ | ⟨f, g₂⟩ | ⟨f⟩
    · refine ⟨g, fr, j, t - 1, ?_, ?_⟩ <;> rw [pStepNormal_zero' hsh]
      · exact hfr
      · exact norm_zero' hsh hQ g hfr.mem_frameSym v j t
    · obtain ⟨j', t', hr⟩ := norm_succ hsh hQ g hfr.mem_frameSym v j t
      refine ⟨g, fr, j', t', ?_, ?_⟩ <;> rw [pStepNormal_succ hsh]
      · exact hfr
      · exact hr
    · obtain ⟨t', hr⟩ := norm_tail hsh hQ g hfr.mem_frameSym v j t
      refine ⟨g, fr, j, t', ?_, ?_⟩ <;> rw [pStepNormal_tail hsh]
      · exact hfr
      · exact hr
    · -- cons: push the frame, copy, dispatch the first child
      have hsize : sizeOf (codeAt (c₁ p)) ≤ n := by
        have hle := hp
        rw [hsh] at hle
        rw [codeAt_c₁_cons hsh]
        simp at hle
        omega
      obtain ⟨g', fr', j', t', hfr', hr⟩ := ihn (c₁ p) hsize (.cons₁ (c₂ p) v k) v
        (Q := .nSeekL (c₁ p)) rfl (g - ((encVal (c := c) v).length + 1))
        (FrameSeg.cons₁ hfr) j t
      refine ⟨g', fr', j', t', ?_, ?_⟩ <;> rw [pStepNormal_cons hsh]
      · exact hfr'
      · exact Reach.trans (norm_cons hsh hQ g hfr.mem_frameSym v j t) hr
    · -- comp: push the frame, dispatch the second child
      have hsize : sizeOf (codeAt (c₂ p)) ≤ n := by
        have hle := hp
        rw [hsh] at hle
        rw [codeAt_c₂_comp hsh]
        simp at hle
        omega
      obtain ⟨g', fr', j', t', hfr', hr⟩ := ihn (c₂ p) hsize (.comp (c₁ p) k) v
        (Q := .nSeekR (c₂ p)) rfl (g - 1) (FrameSeg.comp hfr) j t
      refine ⟨g', fr', j', t', ?_, ?_⟩ <;> rw [pStepNormal_comp hsh]
      · exact hfr'
      · exact Reach.trans (norm_comp hsh hQ g hfr.mem_frameSym v j t) hr
    · -- case: consume the head, dispatch a child
      rcases hv : v.headI with - | y
      · have hsize : sizeOf (codeAt (c₁ p)) ≤ n := by
          have hle := hp
          rw [hsh] at hle
          rw [codeAt_c₁_case hsh]
          simp at hle
          omega
        obtain ⟨t', hr⟩ := norm_case_zero hsh hQ g hfr.mem_frameSym hv j t
        obtain ⟨g', fr', j', t'', hfr', hr'⟩ := ihn (c₁ p) hsize k v.tail
          (Q := .nSeekL (c₁ p)) rfl g hfr j t'
        refine ⟨g', fr', j', t'', ?_, ?_⟩ <;> rw [pStepNormal_case_zero hsh hv]
        · exact hfr'
        · exact Reach.trans hr hr'
      · have hsize : sizeOf (codeAt (c₂ p)) ≤ n := by
          have hle := hp
          rw [hsh] at hle
          rw [codeAt_c₂_case hsh]
          simp at hle
          omega
        obtain ⟨t', hr⟩ := norm_case_succ hsh hQ g hfr.mem_frameSym hv j t
        obtain ⟨g', fr', j', t'', hfr', hr'⟩ := ihn (c₂ p) hsize k (y :: v.tail)
          (Q := .nSeekL (c₂ p)) rfl g hfr j t'
        refine ⟨g', fr', j', t'', ?_, ?_⟩ <;> rw [pStepNormal_case_succ hsh hv]
        · exact hfr'
        · exact Reach.trans hr hr'
    · -- fix: push the frame, dispatch the body
      have hsize : sizeOf (codeAt (c₁ p)) ≤ n := by
        have hle := hp
        rw [hsh] at hle
        rw [codeAt_c₁_fix hsh]
        simp at hle
        omega
      obtain ⟨g', fr', j', t', hfr', hr⟩ := ihn (c₁ p) hsize (.fix (c₁ p) k) v
        (Q := .nSeekR (c₁ p)) rfl (g - 1) (FrameSeg.fix hfr) j t
      refine ⟨g', fr', j', t', ?_, ?_⟩ <;> rw [pStepNormal_fix hsh]
      · exact hfr'
      · exact Reach.trans (norm_fix hsh hQ g hfr.mem_frameSym v j t) hr

end HaltHard

end DescriptiveComplexity
