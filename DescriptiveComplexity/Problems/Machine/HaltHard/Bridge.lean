/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.Sim

/-!
# The simulating machine as rewriting, and the transport to a drawn machine

Two bridges. The first identifies runs of the zipper semantics
(`DescriptiveComplexity.HaltHard.lstep`) with derivations of the rewriting
system `DescriptiveComplexity.HaltPcp.MRule` of the machine packaged as a
`DescriptiveComplexity.TMData` (`DescriptiveComplexity.HaltHard.simTM`, over
the three-block universe `DescriptiveComplexity.HaltHard.SimU` – states,
symbols, and one transition per applicable state–symbol pair; the machine is
deterministic, so the pair is the transition). A zipper configuration *is* a
configuration word (`DescriptiveComplexity.HaltHard.wordOf`), one `lstep` is
one rewriting step, and the boot and halting phases close the two ends:
`DescriptiveComplexity.HaltHard.derives_startWord_iff_evalDom` states the
result directly against `Turing.ToPartrec.Cont.eval`, through
`DescriptiveComplexity.HaltHard.reach_acc_iff_evalDom`.

The second bridge is the rule-correspondence transport: a machine whose
predicates are the images of `simTM`'s along an injection
(`DescriptiveComplexity.HaltHard.TMEmbed` – the shape of the machine the
interpretation of `Interp.lean` draws, whose universe also carries the tape
positions and the junk) derives the halting word from an image word exactly
when `simTM` does from its preimage
(`DescriptiveComplexity.HaltHard.TMEmbed.derives_halt_iff`). Together with
`DescriptiveComplexity.HaltPcp.acceptsU_iff_derives` on the drawn side, this
turns `DescriptiveComplexity.TMData.AcceptsU` of the drawn machine into
termination of the abstract evaluation, with no tape-function bookkeeping.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec HaltPcp Pcp

variable {c : Code}

/-! ### The universe of the simulating machine -/

/-- The universe of the simulating machine as a `DescriptiveComplexity.TMData`:
states, symbols, and one transition per state–symbol pair the table acts on. -/
abbrev SimU (c : Code) : Type := SimQ c ⊕ SimSym c ⊕ SimQ c × SimSym c

/-- A state, as an element of the machine universe. -/
abbrev stq (q : SimQ c) : SimU c := Sum.inl q

/-- A symbol, as an element of the machine universe. -/
abbrev sts (σ : SimSym c) : SimU c := Sum.inr (Sum.inl σ)

/-- A transition – a state–symbol pair – as an element of the machine
universe. -/
abbrev stt (τ : SimQ c × SimSym c) : SimU c := Sum.inr (Sum.inr τ)

/-- **The simulating machine as machine data**: one transition per pair on
which the table acts, its attributes read off `simStep`. The position block
is empty – the rewriting system of a machine never mentions positions, and
the bridge to a drawn machine goes through words alone. -/
def simTM (c : Code) : TMData (SimU c) where
  Posn _ := False
  Le _ _ := False
  Inp _ _ := False
  Tr x := ∃ q σ r, x = stt (q, σ) ∧ simStep q σ = some r
  Start x := x = stq .retL
  Acc x := x = stq .acc
  Blank x := x = sts .bk
  Right x := ∃ q σ b q', x = stt (q, σ) ∧ simStep q σ = some (b, q', true)
  Src x y := ∃ q σ, x = stt (q, σ) ∧ y = stq q
  Read x y := ∃ q σ, x = stt (q, σ) ∧ y = sts σ
  Dst x y := ∃ q σ b q' d, x = stt (q, σ) ∧ simStep q σ = some (b, q', d) ∧ y = stq q'
  Write x y := ∃ q σ b q' d, x = stt (q, σ) ∧ simStep q σ = some (b, q', d) ∧ y = sts b

/-! ### Zipper configurations as words -/

/-- The symbol letters of a run of tape letters. -/
def symsOf (l : List (SimSym c)) : List (TapeLetter (SimU c)) :=
  l.map fun σ => TapeLetter.sym (sts σ)

@[simp]
theorem symsOf_nil : symsOf (c := c) [] = [] := rfl

@[simp]
theorem symsOf_cons (σ : SimSym c) (l : List (SimSym c)) :
    symsOf (σ :: l) = TapeLetter.sym (sts σ) :: symsOf l := rfl

@[simp]
theorem symsOf_append (l l' : List (SimSym c)) :
    symsOf (l ++ l') = symsOf l ++ symsOf l' := List.map_append ..

/-- **The word of a zipper configuration**: the recorded cells left to right
between the endmarkers, the state letter wedged before the head's cell. -/
def wordOf (x : LCfg c) : List (TapeLetter (SimU c)) :=
  (TapeLetter.lft :: symsOf x.L.reverse) ++
    TapeLetter.state (stq x.q) ::
      TapeLetter.sym (sts x.s) :: (symsOf x.R ++ [TapeLetter.rgt])

theorem halt_not_mem_wordOf (x : LCfg c) : TapeLetter.halt ∉ wordOf x := by
  simp [wordOf, symsOf]

theorem boot_not_mem_wordOf (x : LCfg c) : TapeLetter.boot ∉ wordOf x := by
  simp [wordOf, symsOf]

/-! ### Locating the unique marked letter -/

/-- Splitting a list at a marked letter when the reference decomposition has
none on either side: the two decompositions coincide. -/
theorem eq_of_unique_marked {Γ : Type} {P : Γ → Prop} :
    ∀ {A : List Γ} {x : List Γ} {s s' : Γ} {B y : List Γ},
      (∀ a ∈ A, ¬P a) → (∀ a ∈ B, ¬P a) → P s' →
      A ++ s :: B = x ++ s' :: y → A = x ∧ s = s' ∧ B = y := by
  intro A
  induction A with
  | nil =>
    intro x s s' B y _ hB hs' heq
    cases x with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      exact ⟨rfl, heq.1, heq.2⟩
    | cons b x' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      exact absurd hs' (hB s' (heq.2 ▸ (by simp)))
  | cons a A' ih =>
    intro x s s' B y hA hB hs' heq
    cases x with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      exact absurd (heq.1 ▸ hs') (hA a (by simp))
    | cons b x' =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq2⟩ := heq
      obtain ⟨h1, h2, h3⟩ := ih (fun t ht => hA t (by simp [ht])) hB hs' heq2
      exact ⟨by rw [h1], h2, h3⟩

/-- Being a state letter. -/
def IsStateL (a : TapeLetter (SimU c)) : Prop := ∃ u, a = TapeLetter.state u

theorem not_isStateL_left (L : List (SimSym c)) :
    ∀ a ∈ TapeLetter.lft :: symsOf (c := c) L, ¬IsStateL a := by
  rintro a ha ⟨u, rfl⟩
  rcases List.mem_cons.mp ha with h | h
  · simp at h
  · obtain ⟨σ, -, hh⟩ := List.mem_map.mp h
    simp at hh

theorem not_isStateL_right (s : SimSym c) (R : List (SimSym c)) :
    ∀ a ∈ TapeLetter.sym (sts s) :: (symsOf (c := c) R ++ [TapeLetter.rgt]), ¬IsStateL a := by
  rintro a ha ⟨u, rfl⟩
  rcases List.mem_cons.mp ha with h | h
  · simp at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨σ, -, hh⟩ := List.mem_map.mp h
    simp at hh
  · simp at h

/-- Splitting the word of a configuration at a state letter: the state letter
is the configuration's, and the two sides are its two half-tapes. -/
theorem wordOf_state_split {q : SimQ c} {L : List (SimSym c)} {s : SimSym c}
    {R : List (SimSym c)} {u v : List (TapeLetter (SimU c))} {w : SimU c}
    {m : List (TapeLetter (SimU c))}
    (h : wordOf ⟨q, L, s, R⟩ = u ++ (TapeLetter.state w :: m) ++ v) :
    u = TapeLetter.lft :: symsOf L.reverse ∧ w = stq q ∧
      m ++ v = TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt]) := by
  have h' : (TapeLetter.lft :: symsOf L.reverse) ++
      TapeLetter.state (stq q) ::
        (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt])) =
      u ++ TapeLetter.state w :: (m ++ v) := by
    have h₀ : (TapeLetter.lft :: symsOf L.reverse) ++
        TapeLetter.state (stq q) ::
          (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt])) =
        wordOf ⟨q, L, s, R⟩ := by
      simp [wordOf]
    rw [h₀, h]
    simp
  obtain ⟨h1, h2, h3⟩ := eq_of_unique_marked (P := IsStateL (c := c))
    (not_isStateL_left L.reverse) (not_isStateL_right s R) ⟨w, rfl⟩ h'
  refine ⟨h1.symm, ?_, h3.symm⟩
  injection h2 with h2
  exact h2.symm

/-! ### Decoding the attributes of a transition -/

/-- The attribute values of a transition of `simTM` all decode through one
application of the table, and its direction is the `Right` predicate. -/
theorem decode_attrs {τ u a u' b : SimU c} (hsrc : (simTM c).Src τ u)
    (hread : (simTM c).Read τ a) (hdst : (simTM c).Dst τ u')
    (hwrite : (simTM c).Write τ b) :
    ∃ q σ b₀ q₀ d, u = stq q ∧ a = sts σ ∧ simStep q σ = some (b₀, q₀, d) ∧
      u' = stq q₀ ∧ b = sts b₀ ∧ ((simTM c).Right τ ↔ d = true) := by
  obtain ⟨q, σ, rfl, rfl⟩ := hsrc
  obtain ⟨q₂, σ₂, hτ₂, ha⟩ := hread
  have he2 : q₂ = q ∧ σ₂ = σ := by simpa using hτ₂.symm
  obtain ⟨q₃, σ₃, b₃, q₃', d₃, hτ₃, hs₃, hu'⟩ := hdst
  have he3 : q₃ = q ∧ σ₃ = σ := by simpa using hτ₃.symm
  rw [he3.1, he3.2] at hs₃
  obtain ⟨q₄, σ₄, b₄, q₄', d₄, hτ₄, hs₄, hb⟩ := hwrite
  have he4 : q₄ = q ∧ σ₄ = σ := by simpa using hτ₄.symm
  rw [he4.1, he4.2, hs₃] at hs₄
  have hb43 : b₄ = b₃ := (congrArg (fun p => p.1) (Option.some_inj.mp hs₄)).symm
  refine ⟨q, σ, b₃, q₃', d₃, rfl, ?_, hs₃, hu', ?_, ?_, ?_⟩
  · rw [ha, he2.2]
  · rw [hb, hb43]
  · rintro ⟨q₅, σ₅, b₅, q₅', hτ₅, hs₅⟩
    have he5 : q₅ = q ∧ σ₅ = σ := by simpa using hτ₅.symm
    rw [he5.1, he5.2, hs₃] at hs₅
    exact congrArg (fun p => p.2.2) (Option.some_inj.mp hs₅)
  · rintro rfl
    exact ⟨q, σ, b₃, q₃', rfl, hs₃⟩

/-! ### One machine step is one rewriting step -/

/-- **Forward**: one zipper step rewrites the word by one move rule. -/
theorem step_wordOf {x y : LCfg c} (h : lstep x = some y) :
    History.Step (MRule (simTM c)) (wordOf x) (wordOf y) := by
  obtain ⟨q, L, s, R⟩ := x
  rcases hs : simStep q s with - | ⟨b, q', d⟩
  · rw [lstep] at h
    rw [hs] at h
    simp at h
  · rw [lstep] at h
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    cases d with
    | true =>
      cases R with
      | nil =>
        subst h
        exact ⟨TapeLetter.lft :: symsOf L.reverse,
          [.state (stq q), .sym (sts s), .rgt],
          [.sym (sts b), .state (stq q'), .sym (sts .bk), .rgt], [],
          MRule.moveREnd (τ := stt (q, s)) ⟨q, s, _, rfl, hs⟩ ⟨q, s, b, q', rfl, hs⟩
            ⟨q, s, rfl, rfl⟩ ⟨q, s, rfl, rfl⟩ ⟨q, s, b, q', true, rfl, hs, rfl⟩
            ⟨q, s, b, q', true, rfl, hs, rfl⟩ rfl,
          by simp [wordOf], by simp [wordOf]⟩
      | cons t R' =>
        subst h
        exact ⟨TapeLetter.lft :: symsOf L.reverse,
          [.state (stq q), .sym (sts s), .sym (sts t)],
          [.sym (sts b), .state (stq q'), .sym (sts t)], symsOf R' ++ [TapeLetter.rgt],
          MRule.moveR (τ := stt (q, s)) ⟨q, s, _, rfl, hs⟩ ⟨q, s, b, q', rfl, hs⟩
            ⟨q, s, rfl, rfl⟩ ⟨q, s, rfl, rfl⟩ ⟨q, s, b, q', true, rfl, hs, rfl⟩
            ⟨q, s, b, q', true, rfl, hs, rfl⟩,
          by simp [wordOf], by simp [wordOf]⟩
    | false =>
      have hnr : ¬(simTM c).Right (stt (q, s)) := by
        rintro ⟨q₅, σ₅, b₅, q₅', hτ₅, hs₅⟩
        have he5 : q₅ = q ∧ σ₅ = s := by simpa using hτ₅.symm
        rw [he5.1, he5.2, hs] at hs₅
        exact absurd (congrArg (fun p => p.2.2) (Option.some_inj.mp hs₅)) (by simp)
      cases L with
      | nil =>
        subst h
        exact ⟨[],
          [.lft, .state (stq q), .sym (sts s)],
          [.lft, .state (stq q'), .sym (sts .bk), .sym (sts b)], symsOf R ++ [TapeLetter.rgt],
          MRule.moveLEnd (τ := stt (q, s)) ⟨q, s, _, rfl, hs⟩ hnr
            ⟨q, s, rfl, rfl⟩ ⟨q, s, rfl, rfl⟩ ⟨q, s, b, q', false, rfl, hs, rfl⟩
            ⟨q, s, b, q', false, rfl, hs, rfl⟩ rfl,
          by simp [wordOf], by simp [wordOf]⟩
      | cons t L' =>
        subst h
        exact ⟨TapeLetter.lft :: symsOf L'.reverse,
          [.sym (sts t), .state (stq q), .sym (sts s)],
          [.state (stq q'), .sym (sts t), .sym (sts b)], symsOf R ++ [TapeLetter.rgt],
          MRule.moveL (τ := stt (q, s)) ⟨q, s, _, rfl, hs⟩ hnr
            ⟨q, s, rfl, rfl⟩ ⟨q, s, rfl, rfl⟩ ⟨q, s, b, q', false, rfl, hs, rfl⟩
            ⟨q, s, b, q', false, rfl, hs, rfl⟩,
          by simp [wordOf], by simp [wordOf]⟩

/-- **Backward**: a rewriting step from a configuration word either performs
the configuration's own machine step, or fires the halting rule – in which
case the configuration accepts. -/
theorem step_inversion_wordOf {x : LCfg c} {w : List (TapeLetter (SimU c))}
    (h : History.Step (MRule (simTM c)) (wordOf x) w) :
    (∃ y, lstep x = some y ∧ w = wordOf y) ∨ x.q = SimQ.acc := by
  obtain ⟨q, L, s, R⟩ := x
  obtain ⟨u, l, r, v, hrule, hu, hv⟩ := h
  cases hrule with
  | boot hst =>
    exact absurd (show TapeLetter.boot ∈ wordOf (⟨q, L, s, R⟩ : LCfg c) by rw [hu]; simp)
      (boot_not_mem_wordOf _)
  | eraseSymL cc =>
    exact absurd (show TapeLetter.halt ∈ wordOf (⟨q, L, s, R⟩ : LCfg c) by rw [hu]; simp)
      (halt_not_mem_wordOf _)
  | eraseLft =>
    exact absurd (show TapeLetter.halt ∈ wordOf (⟨q, L, s, R⟩ : LCfg c) by rw [hu]; simp)
      (halt_not_mem_wordOf _)
  | eraseSymR cc =>
    exact absurd (show TapeLetter.halt ∈ wordOf (⟨q, L, s, R⟩ : LCfg c) by rw [hu]; simp)
      (halt_not_mem_wordOf _)
  | eraseRgt =>
    exact absurd (show TapeLetter.halt ∈ wordOf (⟨q, L, s, R⟩ : LCfg c) by rw [hu]; simp)
      (halt_not_mem_wordOf _)
  | @acc qq hacc =>
    obtain ⟨-, hw, -⟩ := wordOf_state_split (m := []) hu
    refine Or.inr ?_
    have h : stq (c := c) q = stq SimQ.acc := by
      rw [← hw]
      exact hacc
    simpa using h
  | @moveR τ qq aa bb qq' cc htr hR hsrc hread hdst hwrite =>
    obtain ⟨rfl, hw, hm⟩ :=
      wordOf_state_split (m := [TapeLetter.sym aa, TapeLetter.sym cc]) hu
    obtain ⟨q₀, σ₀, b₀, q₀', d₀, hq₀, ha₀, hstep₀, hq₀', hb₀, hd₀⟩ :=
      decode_attrs hsrc hread hdst hwrite
    have hqq : q₀ = q := by simpa using hq₀.symm.trans hw
    simp only [List.cons_append, List.nil_append, List.cons.injEq,
      TapeLetter.sym.injEq] at hm
    obtain ⟨ha, hm2⟩ := hm
    have hσσ : σ₀ = s := by simpa using ha₀.symm.trans ha
    rw [hqq, hσσ] at hstep₀
    obtain rfl : d₀ = true := hd₀.mp hR
    cases R with
    | nil =>
      simp only [symsOf_nil, List.nil_append] at hm2
      simp at hm2
    | cons t R' =>
      simp only [symsOf_cons, List.cons_append, List.cons.injEq,
        TapeLetter.sym.injEq] at hm2
      refine Or.inl ⟨⟨q₀', b₀ :: L, t, R'⟩, lstep_right hstep₀ L t R', ?_⟩
      rw [hv, hq₀', hb₀, hm2.1, hm2.2]
      simp [wordOf]
  | @moveREnd τ qq aa bb qq' bk htr hR hsrc hread hdst hwrite hbk =>
    obtain ⟨rfl, hw, hm⟩ :=
      wordOf_state_split (m := [TapeLetter.sym aa, TapeLetter.rgt]) hu
    obtain ⟨q₀, σ₀, b₀, q₀', d₀, hq₀, ha₀, hstep₀, hq₀', hb₀, hd₀⟩ :=
      decode_attrs hsrc hread hdst hwrite
    have hqq : q₀ = q := by simpa using hq₀.symm.trans hw
    simp only [List.cons_append, List.nil_append, List.cons.injEq,
      TapeLetter.sym.injEq] at hm
    obtain ⟨ha, hm2⟩ := hm
    have hσσ : σ₀ = s := by simpa using ha₀.symm.trans ha
    rw [hqq, hσσ] at hstep₀
    obtain rfl : d₀ = true := hd₀.mp hR
    obtain rfl : bk = sts SimSym.bk := hbk
    cases R with
    | cons t R' =>
      simp only [symsOf_cons, List.cons_append, List.cons.injEq] at hm2
      exact absurd hm2.1 (by simp)
    | nil =>
      simp only [symsOf_nil, List.nil_append, List.cons.injEq] at hm2
      refine Or.inl ⟨⟨q₀', b₀ :: L, .bk, []⟩, lstep_right_end hstep₀ L, ?_⟩
      rw [hv, hq₀', hb₀, hm2.2]
      simp [wordOf]
  | @moveL τ qq aa bb qq' cc htr hR hsrc hread hdst hwrite =>
    have hu' : wordOf (⟨q, L, s, R⟩ : LCfg c) =
        (u ++ [TapeLetter.sym cc]) ++ (TapeLetter.state qq :: [TapeLetter.sym aa]) ++ v := by
      rw [hu]
      simp
    obtain ⟨hleft, hw, hm⟩ := wordOf_state_split (m := [TapeLetter.sym aa]) hu'
    obtain ⟨q₀, σ₀, b₀, q₀', d₀, hq₀, ha₀, hstep₀, hq₀', hb₀, hd₀⟩ :=
      decode_attrs hsrc hread hdst hwrite
    have hqq : q₀ = q := by simpa using hq₀.symm.trans hw
    simp only [List.cons_append, List.nil_append, List.cons.injEq,
      TapeLetter.sym.injEq] at hm
    obtain ⟨ha, hv'⟩ := hm
    have hσσ : σ₀ = s := by simpa using ha₀.symm.trans ha
    rw [hqq, hσσ] at hstep₀
    have hd0 : d₀ = false := by
      rcases d₀ with - | -
      · rfl
      · exact absurd (hd₀.mpr rfl) hR
    rw [hd0] at hstep₀
    cases L with
    | nil =>
      exfalso
      simp only [List.reverse_nil, symsOf_nil] at hleft
      rcases u with - | ⟨e, u'⟩
      · simp at hleft
      · simp only [List.cons_append, List.cons.injEq] at hleft
        exact absurd hleft.2 (by simp)
    | cons t L' =>
      have hleft' : u ++ [TapeLetter.sym cc] =
          (TapeLetter.lft :: symsOf L'.reverse) ++ [TapeLetter.sym (sts t)] := by
        rw [hleft]
        simp
      obtain ⟨hup, hcc⟩ := List.append_inj' hleft' rfl
      have hcc' : cc = sts t := by simpa using hcc
      refine Or.inl ⟨⟨q₀', L', t, b₀ :: R⟩, lstep_left hstep₀ t L' R, ?_⟩
      rw [hv, hup, hq₀', hcc', hb₀, hv']
      simp [wordOf]
  | @moveLEnd τ qq aa bb qq' bk htr hR hsrc hread hdst hwrite hbk =>
    have hu' : wordOf (⟨q, L, s, R⟩ : LCfg c) =
        (u ++ [TapeLetter.lft]) ++ (TapeLetter.state qq :: [TapeLetter.sym aa]) ++ v := by
      rw [hu]
      simp
    obtain ⟨hleft, hw, hm⟩ := wordOf_state_split (m := [TapeLetter.sym aa]) hu'
    obtain ⟨q₀, σ₀, b₀, q₀', d₀, hq₀, ha₀, hstep₀, hq₀', hb₀, hd₀⟩ :=
      decode_attrs hsrc hread hdst hwrite
    have hqq : q₀ = q := by simpa using hq₀.symm.trans hw
    simp only [List.cons_append, List.nil_append, List.cons.injEq,
      TapeLetter.sym.injEq] at hm
    obtain ⟨ha, hv'⟩ := hm
    have hσσ : σ₀ = s := by simpa using ha₀.symm.trans ha
    rw [hqq, hσσ] at hstep₀
    have hd0 : d₀ = false := by
      rcases d₀ with - | -
      · rfl
      · exact absurd (hd₀.mpr rfl) hR
    rw [hd0] at hstep₀
    obtain rfl : bk = sts SimSym.bk := hbk
    cases L with
    | cons t L' =>
      exfalso
      have hleft' : u ++ [TapeLetter.lft] =
          (TapeLetter.lft :: symsOf L'.reverse) ++ [TapeLetter.sym (sts t)] := by
        rw [hleft]
        simp
      obtain ⟨-, hcc⟩ := List.append_inj' hleft' rfl
      simp at hcc
    | nil =>
      simp only [List.reverse_nil, symsOf_nil] at hleft
      obtain rfl : u = [] := by
        rcases u with - | ⟨e, u'⟩
        · rfl
        · exfalso
          simp only [List.cons_append, List.cons.injEq] at hleft
          exact absurd hleft.2 (by simp)
      refine Or.inl ⟨⟨q₀', [], .bk, b₀ :: R⟩, lstep_left_end hstep₀ R, ?_⟩
      rw [hv, hq₀', hb₀, hv']
      simp [wordOf]

/-! ### Whole runs -/

/-- A run of the machine is a derivation between the two words. -/
theorem derives_wordOf_of_reach {x y : LCfg c} (h : Reach x y) :
    History.Derives (MRule (simTM c)) (wordOf x) (wordOf y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (step_wordOf hstep)

/-- From an accepting configuration the derivation closes: the state letter
becomes the halting letter, which swallows the rest of the word. -/
theorem derives_halt_of_acc {x : LCfg c} (hx : x.q = SimQ.acc) :
    History.Derives (MRule (simTM c)) (wordOf x) [TapeLetter.halt] := by
  obtain ⟨q, L, s, R⟩ := x
  obtain rfl : q = SimQ.acc := hx
  -- the state letter becomes the halting letter
  have h1 : History.Step (MRule (simTM c)) (wordOf ⟨.acc, L, s, R⟩)
      ((TapeLetter.lft :: symsOf L.reverse) ++ TapeLetter.halt ::
        (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt]))) :=
    ⟨TapeLetter.lft :: symsOf L.reverse, [TapeLetter.state (stq .acc)], [TapeLetter.halt],
      TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt]),
      MRule.acc rfl, by simp [wordOf], by simp⟩
  -- the halting letter swallows the left half
  have h2 : History.Derives (MRule (simTM c))
      ((TapeLetter.lft :: symsOf L.reverse) ++ TapeLetter.halt ::
        (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt])))
      ([TapeLetter.lft, TapeLetter.halt] ++
        (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt]))) := by
    have h := (derives_eraseL (M := simTM c) (L.reverse.map sts)).congr [TapeLetter.lft]
      (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt]))
    have hsyms : (L.reverse.map sts).map TapeLetter.sym = symsOf (c := c) L.reverse := by
      simp [symsOf, List.map_map, Function.comp_def]
    rw [hsyms] at h
    simpa using h
  -- the left endmarker
  have h3 : History.Step (MRule (simTM c))
      ([TapeLetter.lft, TapeLetter.halt] ++
        (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt])))
      (TapeLetter.halt :: (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt]))) :=
    ⟨[], [TapeLetter.lft, TapeLetter.halt], [TapeLetter.halt],
      TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt]),
      MRule.eraseLft, by simp, by simp⟩
  -- the right half
  have h4 : History.Derives (MRule (simTM c))
      (TapeLetter.halt :: (TapeLetter.sym (sts s) :: (symsOf R ++ [TapeLetter.rgt])))
      [TapeLetter.halt, TapeLetter.rgt] := by
    have h := (derives_eraseR (M := simTM c) ((s :: R).map sts)).congr [] [TapeLetter.rgt]
    have hsyms : ((s :: R).map sts).map TapeLetter.sym =
        TapeLetter.sym (sts s) :: symsOf (c := c) R := by
      simp [symsOf, List.map_map, Function.comp_def]
    rw [hsyms] at h
    simpa using h
  -- the right endmarker
  have h5 : History.Step (MRule (simTM c)) [TapeLetter.halt, TapeLetter.rgt]
      [TapeLetter.halt] :=
    ⟨[], [TapeLetter.halt, TapeLetter.rgt], [TapeLetter.halt], [],
      MRule.eraseRgt, by simp, by simp⟩
  exact (((Relation.ReflTransGen.head h1 h2).tail h3).trans h4).tail h5

/-- **Backward**: a derivation of the halting word from a configuration word
yields an accepting run of the machine. -/
theorem reach_acc_of_derives : ∀ {w : List (TapeLetter (SimU c))},
    History.Derives (MRule (simTM c)) w [TapeLetter.halt] →
    ∀ x : LCfg c, w = wordOf x → ∃ y, y.q = SimQ.acc ∧ Reach x y := by
  intro w hder
  induction hder using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro x hx
    obtain ⟨q, L, s, R⟩ := x
    simp [wordOf] at hx
  | @head w' w₁ hstep hrest ih =>
    rintro x rfl
    rcases step_inversion_wordOf hstep with ⟨y, hy, rfl⟩ | hacc
    · obtain ⟨z, hz, hr⟩ := ih y rfl
      exact ⟨z, hz, Reach.head hy hr⟩
    · exact ⟨x, hacc, Reach.refl x⟩

/-! ### The boot phase, and the abstract statement -/

/-- **Derivability from the start word is machine acceptance**, at the
zipper: the first step of any derivation is the boot rule, and boot lands the
machine in the resting state at the left end of the spelled tape. -/
theorem derives_startWord_iff (σ₀ : SimSym c) (R₀ : List (SimSym c)) :
    History.Derives (MRule (simTM c))
      (startWord ((σ₀ :: R₀).map sts)) [TapeLetter.halt] ↔
      ∃ y, y.q = SimQ.acc ∧ Reach (⟨.retL, [], σ₀, R₀⟩ : LCfg c) y := by
  have hword : (TapeLetter.lft :: TapeLetter.state (stq (c := c) SimQ.retL) ::
      (((σ₀ :: R₀).map sts).map TapeLetter.sym ++ [TapeLetter.rgt])) =
      wordOf ⟨.retL, [], σ₀, R₀⟩ := by
    simp [wordOf, symsOf, List.map_map, Function.comp_def]
  constructor
  · intro hder
    rcases Relation.ReflTransGen.cases_head hder with heq | ⟨w₁, hstep, hrest⟩
    · exfalso
      rw [startWord] at heq
      injection heq with hcon
      exact TapeLetter.absurd_of_ne hcon
    obtain ⟨x, l, r, y, hrule, hu, hv⟩ := hstep
    have hcnt0 : stateCount (startWord ((σ₀ :: R₀).map sts)) = 0 := stateCount_startWord _
    have hhaltnot : TapeLetter.halt ∉ startWord ((σ₀ :: R₀).map (sts (c := c))) := by
      simp [startWord]
    cases hrule with
    | moveR htr hR hsrc hread hdst hwrite =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | moveREnd htr hR hsrc hread hdst hwrite hbk =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | moveL htr hR hsrc hread hdst hwrite =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | moveLEnd htr hR hsrc hread hdst hwrite hbk =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | acc hacc =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | eraseSymL cc => exact absurd (by rw [hu]; simp) hhaltnot
    | eraseLft => exact absurd (by rw [hu]; simp) hhaltnot
    | eraseSymR cc => exact absurd (by rw [hu]; simp) hhaltnot
    | eraseRgt => exact absurd (by rw [hu]; simp) hhaltnot
    | @boot q₀ hq₀ =>
      obtain ⟨rfl, hst, rfl⟩ :=
        eq_of_unique_marked (P := fun a => a = (TapeLetter.boot : TapeLetter (SimU c)))
          (A := [TapeLetter.lft])
          (B := ((σ₀ :: R₀).map sts).map TapeLetter.sym ++ [TapeLetter.rgt])
          (by simp)
          (by
            intro a ha
            rcases List.mem_append.mp ha with hm | hm
            · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
              simp
            · obtain rfl : a = TapeLetter.rgt := by simpa using hm
              simp)
          rfl (by simpa [startWord] using hu)
      obtain rfl : q₀ = stq SimQ.retL := hq₀
      have hw₁ : w₁ = wordOf ⟨.retL, [], σ₀, R₀⟩ := by
        rw [hv, ← hword]
        simp
      exact reach_acc_of_derives (hw₁ ▸ hrest) _ rfl
  · rintro ⟨y, hy, hr⟩
    have hboot : History.Step (MRule (simTM c)) (startWord ((σ₀ :: R₀).map sts))
        (wordOf ⟨.retL, [], σ₀, R₀⟩) :=
      ⟨[TapeLetter.lft], [TapeLetter.boot], [TapeLetter.state (stq SimQ.retL)],
        ((σ₀ :: R₀).map sts).map TapeLetter.sym ++ [TapeLetter.rgt],
        MRule.boot rfl, by simp [startWord], by rw [← hword]; simp⟩
    exact Relation.ReflTransGen.head hboot
      ((derives_wordOf_of_reach hr).trans (derives_halt_of_acc hy))

/-- **The abstract bridge**: the rewriting system of the simulating machine
derives the halting word from the spelled resting configuration of `k` and
`v` exactly when the abstract evaluation of `k` on `v` terminates. -/
theorem derives_startWord_iff_evalDom {k : PCont c} {fr : List (SimSym c)}
    (hfr : FrameSeg k fr) (v : List ℕ) (j t : ℕ) :
    History.Derives (MRule (simTM c))
      (startWord ((SimSym.endL :: (fr ++ SimSym.mid :: valR v j t)).map sts))
      [TapeLetter.halt] ↔ (k.toCont.eval v).Dom := by
  rw [derives_startWord_iff]
  exact reach_acc_iff_evalDom hfr 0 v j t

/-! ### Transport along an injection

The machine the interpretation draws has the same states, symbols and
transitions, embedded in a larger universe that also carries the tape
positions and the junk. Its predicates are the images of the abstract ones,
and derivations of the halting word correspond exactly. -/

/-- Mapping the machine elements of a tape letter. -/
def _root_.DescriptiveComplexity.HaltPcp.TapeLetter.map {A B : Type} (f : A → B) :
    TapeLetter A → TapeLetter B
  | .lft => .lft
  | .rgt => .rgt
  | .boot => .boot
  | .halt => .halt
  | .sym a => .sym (f a)
  | .state a => .state (f a)

/-- **A machine embedded in a larger universe**: an injection under which
every predicate of the target is the image of the corresponding predicate of
the source. -/
structure TMEmbed {A B : Type} (f : A → B) (M : TMData A) (N : TMData B) : Prop where
  /-- The embedding is injective. -/
  inj : Function.Injective f
  /-- Transitions correspond. -/
  tr : ∀ b, N.Tr b ↔ ∃ a, b = f a ∧ M.Tr a
  /-- Start states correspond. -/
  start : ∀ b, N.Start b ↔ ∃ a, b = f a ∧ M.Start a
  /-- Accepting states correspond. -/
  acc : ∀ b, N.Acc b ↔ ∃ a, b = f a ∧ M.Acc a
  /-- Blanks correspond. -/
  blank : ∀ b, N.Blank b ↔ ∃ a, b = f a ∧ M.Blank a
  /-- Directions correspond. -/
  right : ∀ b, N.Right b ↔ ∃ a, b = f a ∧ M.Right a
  /-- Source states correspond. -/
  src : ∀ b b', N.Src b b' ↔ ∃ a a', b = f a ∧ b' = f a' ∧ M.Src a a'
  /-- Read symbols correspond. -/
  read : ∀ b b', N.Read b b' ↔ ∃ a a', b = f a ∧ b' = f a' ∧ M.Read a a'
  /-- Destination states correspond. -/
  dst : ∀ b b', N.Dst b b' ↔ ∃ a a', b = f a ∧ b' = f a' ∧ M.Dst a a'
  /-- Written symbols correspond. -/
  write : ∀ b b', N.Write b b' ↔ ∃ a a', b = f a ∧ b' = f a' ∧ M.Write a a'

namespace TMEmbed

variable {A B : Type} {f : A → B} {M : TMData A} {N : TMData B}

/-- The start word is mapped letterwise. -/
theorem _root_.DescriptiveComplexity.HaltPcp.startWord_map {A B : Type} (f : A → B)
    (inp : List A) :
    (startWord inp).map (TapeLetter.map f) = startWord (inp.map f) := by
  simp [startWord, TapeLetter.map, List.map_map, Function.comp_def]

/-- **Forward transport of a rule.** -/
theorem mRule_map (h : TMEmbed f M N) {l r : List (TapeLetter A)} (hrule : MRule M l r) :
    MRule N (l.map (TapeLetter.map f)) (r.map (TapeLetter.map f)) := by
  cases hrule with
  | boot hst => exact MRule.boot ((h.start _).mpr ⟨_, rfl, hst⟩)
  | moveR htr hR hsrc hread hdst hwrite =>
    exact MRule.moveR ((h.tr _).mpr ⟨_, rfl, htr⟩) ((h.right _).mpr ⟨_, rfl, hR⟩)
      ((h.src _ _).mpr ⟨_, _, rfl, rfl, hsrc⟩) ((h.read _ _).mpr ⟨_, _, rfl, rfl, hread⟩)
      ((h.dst _ _).mpr ⟨_, _, rfl, rfl, hdst⟩) ((h.write _ _).mpr ⟨_, _, rfl, rfl, hwrite⟩)
  | moveREnd htr hR hsrc hread hdst hwrite hbk =>
    exact MRule.moveREnd ((h.tr _).mpr ⟨_, rfl, htr⟩) ((h.right _).mpr ⟨_, rfl, hR⟩)
      ((h.src _ _).mpr ⟨_, _, rfl, rfl, hsrc⟩) ((h.read _ _).mpr ⟨_, _, rfl, rfl, hread⟩)
      ((h.dst _ _).mpr ⟨_, _, rfl, rfl, hdst⟩) ((h.write _ _).mpr ⟨_, _, rfl, rfl, hwrite⟩)
      ((h.blank _).mpr ⟨_, rfl, hbk⟩)
  | moveL htr hR hsrc hread hdst hwrite =>
    refine MRule.moveL ((h.tr _).mpr ⟨_, rfl, htr⟩) ?_
      ((h.src _ _).mpr ⟨_, _, rfl, rfl, hsrc⟩) ((h.read _ _).mpr ⟨_, _, rfl, rfl, hread⟩)
      ((h.dst _ _).mpr ⟨_, _, rfl, rfl, hdst⟩) ((h.write _ _).mpr ⟨_, _, rfl, rfl, hwrite⟩)
    rintro hcon
    obtain ⟨a, ha, hra⟩ := (h.right _).mp hcon
    exact hR (h.inj ha ▸ hra)
  | moveLEnd htr hR hsrc hread hdst hwrite hbk =>
    refine MRule.moveLEnd ((h.tr _).mpr ⟨_, rfl, htr⟩) ?_
      ((h.src _ _).mpr ⟨_, _, rfl, rfl, hsrc⟩) ((h.read _ _).mpr ⟨_, _, rfl, rfl, hread⟩)
      ((h.dst _ _).mpr ⟨_, _, rfl, rfl, hdst⟩) ((h.write _ _).mpr ⟨_, _, rfl, rfl, hwrite⟩)
      ((h.blank _).mpr ⟨_, rfl, hbk⟩)
    rintro hcon
    obtain ⟨a, ha, hra⟩ := (h.right _).mp hcon
    exact hR (h.inj ha ▸ hra)
  | acc hacc => exact MRule.acc ((h.acc _).mpr ⟨_, rfl, hacc⟩)
  | eraseSymL cc => exact MRule.eraseSymL (f cc)
  | eraseLft => exact MRule.eraseLft
  | eraseSymR cc => exact MRule.eraseSymR (f cc)
  | eraseRgt => exact MRule.eraseRgt

/-! #### Decomposing image words -/

theorem cons_eq_map {α β : Type} {f : α → β} {x : β} {xs : List β} {l : List α}
    (h : x :: xs = l.map f) : ∃ a l₀, l = a :: l₀ ∧ x = f a ∧ xs = l₀.map f := by
  cases l with
  | nil => simp at h
  | cons a l₀ =>
    rw [List.map_cons] at h
    injection h with h1 h2
    exact ⟨a, l₀, rfl, h1, h2⟩

theorem nil_eq_map {α β : Type} {f : α → β} {l : List α}
    (h : ([] : List β) = l.map f) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l₀ => simp at h

theorem append_eq_map {α β : Type} {f : α → β} : ∀ {x y : List β} {l : List α},
    x ++ y = l.map f →
    ∃ lx ly, l = lx ++ ly ∧ x = lx.map f ∧ y = ly.map f := by
  intro x
  induction x with
  | nil =>
    intro y l h
    exact ⟨[], l, rfl, rfl, by simpa using h⟩
  | cons a x' ih =>
    intro y l h
    rw [List.cons_append] at h
    obtain ⟨a₀, l₀, rfl, ha, h₂⟩ := cons_eq_map h
    obtain ⟨lx, ly, rfl, hx, hy⟩ := ih h₂
    exact ⟨a₀ :: lx, ly, rfl, by rw [List.map_cons, ← ha, ← hx], hy⟩

section Letters

variable {A B : Type} {f : A → B} {a : TapeLetter A}

theorem eq_map_state {q : B} (h : TapeLetter.state q = TapeLetter.map f a) :
    ∃ q₀, a = TapeLetter.state q₀ ∧ q = f q₀ := by
  cases a <;> simp only [TapeLetter.map] at h
  case state q₀ => exact ⟨q₀, rfl, by injection h⟩
  all_goals exact absurd h (by simp)

theorem eq_map_sym {q : B} (h : TapeLetter.sym q = TapeLetter.map f a) :
    ∃ q₀, a = TapeLetter.sym q₀ ∧ q = f q₀ := by
  cases a <;> simp only [TapeLetter.map] at h
  case sym q₀ => exact ⟨q₀, rfl, by injection h⟩
  all_goals exact absurd h (by simp)

theorem eq_map_lft (h : TapeLetter.lft = TapeLetter.map f a) : a = TapeLetter.lft := by
  cases a <;> simp only [TapeLetter.map] at h
  case lft => rfl
  all_goals exact absurd h (by simp)

theorem eq_map_rgt (h : TapeLetter.rgt = TapeLetter.map f a) : a = TapeLetter.rgt := by
  cases a <;> simp only [TapeLetter.map] at h
  case rgt => rfl
  all_goals exact absurd h (by simp)

theorem eq_map_boot (h : TapeLetter.boot = TapeLetter.map f a) : a = TapeLetter.boot := by
  cases a <;> simp only [TapeLetter.map] at h
  case boot => rfl
  all_goals exact absurd h (by simp)

theorem eq_map_halt (h : TapeLetter.halt = TapeLetter.map f a) : a = TapeLetter.halt := by
  cases a <;> simp only [TapeLetter.map] at h
  case halt => rfl
  all_goals exact absurd h (by simp)

end Letters

/-- **Backward transport of a rule**: a target rule whose left side is an
image has an image right side, and comes from a source rule. -/
theorem mRule_inv (h : TMEmbed f M N) {l' r' : List (TapeLetter B)}
    (hrule : MRule N l' r') {l : List (TapeLetter A)}
    (hl : l' = l.map (TapeLetter.map f)) :
    ∃ r, r' = r.map (TapeLetter.map f) ∧ MRule M l r := by
  cases hrule with
  | @boot q hst =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain rfl := nil_eq_map hl1
    obtain rfl := eq_map_boot h1
    obtain ⟨q₀, rfl, hst₀⟩ := (h.start _).mp hst
    exact ⟨[.state q₀], by simp [TapeLetter.map], MRule.boot hst₀⟩
  | @moveR τ q a b q' cc htr hR hsrc hread hdst hwrite =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain ⟨x2, l2, rfl, h2, hl2⟩ := cons_eq_map hl1
    obtain ⟨x3, l3, rfl, h3, hl3⟩ := cons_eq_map hl2
    obtain rfl := nil_eq_map hl3
    obtain ⟨q₁, rfl, rfl⟩ := eq_map_state h1
    obtain ⟨a₁, rfl, rfl⟩ := eq_map_sym h2
    obtain ⟨c₁, rfl, rfl⟩ := eq_map_sym h3
    obtain ⟨τ₀, rfl, htr₀⟩ := (h.tr _).mp htr
    obtain ⟨τ₂, q₂, hτ₂, hq₂, hsrc₀⟩ := (h.src _ _).mp hsrc
    rw [← h.inj hτ₂, ← h.inj hq₂] at hsrc₀
    obtain ⟨τ₃, a₃, hτ₃, ha₃, hread₀⟩ := (h.read _ _).mp hread
    rw [← h.inj hτ₃, ← h.inj ha₃] at hread₀
    obtain ⟨τ₄, q₄, hτ₄, rfl, hdst₀⟩ := (h.dst _ _).mp hdst
    rw [← h.inj hτ₄] at hdst₀
    obtain ⟨τ₅, b₅, hτ₅, rfl, hwrite₀⟩ := (h.write _ _).mp hwrite
    rw [← h.inj hτ₅] at hwrite₀
    have hR₀ : M.Right τ₀ := by
      obtain ⟨a₆, ha₆, hra₆⟩ := (h.right _).mp hR
      rwa [h.inj ha₆]
    exact ⟨[.sym b₅, .state q₄, .sym c₁], by simp [TapeLetter.map],
      MRule.moveR htr₀ hR₀ hsrc₀ hread₀ hdst₀ hwrite₀⟩
  | @moveREnd τ q a b q' bk htr hR hsrc hread hdst hwrite hbk =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain ⟨x2, l2, rfl, h2, hl2⟩ := cons_eq_map hl1
    obtain ⟨x3, l3, rfl, h3, hl3⟩ := cons_eq_map hl2
    obtain rfl := nil_eq_map hl3
    obtain ⟨q₁, rfl, rfl⟩ := eq_map_state h1
    obtain ⟨a₁, rfl, rfl⟩ := eq_map_sym h2
    obtain rfl := eq_map_rgt h3
    obtain ⟨τ₀, rfl, htr₀⟩ := (h.tr _).mp htr
    obtain ⟨τ₂, q₂, hτ₂, hq₂, hsrc₀⟩ := (h.src _ _).mp hsrc
    rw [← h.inj hτ₂, ← h.inj hq₂] at hsrc₀
    obtain ⟨τ₃, a₃, hτ₃, ha₃, hread₀⟩ := (h.read _ _).mp hread
    rw [← h.inj hτ₃, ← h.inj ha₃] at hread₀
    obtain ⟨τ₄, q₄, hτ₄, rfl, hdst₀⟩ := (h.dst _ _).mp hdst
    rw [← h.inj hτ₄] at hdst₀
    obtain ⟨τ₅, b₅, hτ₅, rfl, hwrite₀⟩ := (h.write _ _).mp hwrite
    rw [← h.inj hτ₅] at hwrite₀
    obtain ⟨bk₀, rfl, hbk₀⟩ := (h.blank _).mp hbk
    have hR₀ : M.Right τ₀ := by
      obtain ⟨a₆, ha₆, hra₆⟩ := (h.right _).mp hR
      rwa [h.inj ha₆]
    exact ⟨[.sym b₅, .state q₄, .sym bk₀, .rgt], by simp [TapeLetter.map],
      MRule.moveREnd htr₀ hR₀ hsrc₀ hread₀ hdst₀ hwrite₀ hbk₀⟩
  | @moveL τ q a b q' cc htr hR hsrc hread hdst hwrite =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain ⟨x2, l2, rfl, h2, hl2⟩ := cons_eq_map hl1
    obtain ⟨x3, l3, rfl, h3, hl3⟩ := cons_eq_map hl2
    obtain rfl := nil_eq_map hl3
    obtain ⟨c₁, rfl, rfl⟩ := eq_map_sym h1
    obtain ⟨q₁, rfl, rfl⟩ := eq_map_state h2
    obtain ⟨a₁, rfl, rfl⟩ := eq_map_sym h3
    obtain ⟨τ₀, rfl, htr₀⟩ := (h.tr _).mp htr
    obtain ⟨τ₂, q₂, hτ₂, hq₂, hsrc₀⟩ := (h.src _ _).mp hsrc
    rw [← h.inj hτ₂, ← h.inj hq₂] at hsrc₀
    obtain ⟨τ₃, a₃, hτ₃, ha₃, hread₀⟩ := (h.read _ _).mp hread
    rw [← h.inj hτ₃, ← h.inj ha₃] at hread₀
    obtain ⟨τ₄, q₄, hτ₄, rfl, hdst₀⟩ := (h.dst _ _).mp hdst
    rw [← h.inj hτ₄] at hdst₀
    obtain ⟨τ₅, b₅, hτ₅, rfl, hwrite₀⟩ := (h.write _ _).mp hwrite
    rw [← h.inj hτ₅] at hwrite₀
    have hR₀ : ¬M.Right τ₀ := fun hcon => hR ((h.right _).mpr ⟨τ₀, rfl, hcon⟩)
    exact ⟨[.state q₄, .sym c₁, .sym b₅], by simp [TapeLetter.map],
      MRule.moveL htr₀ hR₀ hsrc₀ hread₀ hdst₀ hwrite₀⟩
  | @moveLEnd τ q a b q' bk htr hR hsrc hread hdst hwrite hbk =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain ⟨x2, l2, rfl, h2, hl2⟩ := cons_eq_map hl1
    obtain ⟨x3, l3, rfl, h3, hl3⟩ := cons_eq_map hl2
    obtain rfl := nil_eq_map hl3
    obtain rfl := eq_map_lft h1
    obtain ⟨q₁, rfl, rfl⟩ := eq_map_state h2
    obtain ⟨a₁, rfl, rfl⟩ := eq_map_sym h3
    obtain ⟨τ₀, rfl, htr₀⟩ := (h.tr _).mp htr
    obtain ⟨τ₂, q₂, hτ₂, hq₂, hsrc₀⟩ := (h.src _ _).mp hsrc
    rw [← h.inj hτ₂, ← h.inj hq₂] at hsrc₀
    obtain ⟨τ₃, a₃, hτ₃, ha₃, hread₀⟩ := (h.read _ _).mp hread
    rw [← h.inj hτ₃, ← h.inj ha₃] at hread₀
    obtain ⟨τ₄, q₄, hτ₄, rfl, hdst₀⟩ := (h.dst _ _).mp hdst
    rw [← h.inj hτ₄] at hdst₀
    obtain ⟨τ₅, b₅, hτ₅, rfl, hwrite₀⟩ := (h.write _ _).mp hwrite
    rw [← h.inj hτ₅] at hwrite₀
    obtain ⟨bk₀, rfl, hbk₀⟩ := (h.blank _).mp hbk
    have hR₀ : ¬M.Right τ₀ := fun hcon => hR ((h.right _).mpr ⟨τ₀, rfl, hcon⟩)
    exact ⟨[.lft, .state q₄, .sym bk₀, .sym b₅], by simp [TapeLetter.map],
      MRule.moveLEnd htr₀ hR₀ hsrc₀ hread₀ hdst₀ hwrite₀ hbk₀⟩
  | @acc q hacc =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain rfl := nil_eq_map hl1
    obtain ⟨q₁, rfl, rfl⟩ := eq_map_state h1
    obtain ⟨q₀, hq, hacc₀⟩ := (h.acc _).mp hacc
    rw [← h.inj hq] at hacc₀
    exact ⟨[.halt], by simp [TapeLetter.map], MRule.acc hacc₀⟩
  | @eraseSymL cc =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain ⟨x2, l2, rfl, h2, hl2⟩ := cons_eq_map hl1
    obtain rfl := nil_eq_map hl2
    obtain ⟨c₁, rfl, rfl⟩ := eq_map_sym h1
    obtain rfl := eq_map_halt h2
    exact ⟨[.halt], by simp [TapeLetter.map], MRule.eraseSymL c₁⟩
  | eraseLft =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain ⟨x2, l2, rfl, h2, hl2⟩ := cons_eq_map hl1
    obtain rfl := nil_eq_map hl2
    obtain rfl := eq_map_lft h1
    obtain rfl := eq_map_halt h2
    exact ⟨[.halt], by simp [TapeLetter.map], MRule.eraseLft⟩
  | @eraseSymR cc =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain ⟨x2, l2, rfl, h2, hl2⟩ := cons_eq_map hl1
    obtain rfl := nil_eq_map hl2
    obtain rfl := eq_map_halt h1
    obtain ⟨c₁, rfl, rfl⟩ := eq_map_sym h2
    exact ⟨[.halt], by simp [TapeLetter.map], MRule.eraseSymR c₁⟩
  | eraseRgt =>
    obtain ⟨x1, l1, rfl, h1, hl1⟩ := cons_eq_map hl
    obtain ⟨x2, l2, rfl, h2, hl2⟩ := cons_eq_map hl1
    obtain rfl := nil_eq_map hl2
    obtain rfl := eq_map_halt h1
    obtain rfl := eq_map_rgt h2
    exact ⟨[.halt], by simp [TapeLetter.map], MRule.eraseRgt⟩

/-- Forward transport of a rewriting step. -/
theorem step_map (h : TMEmbed f M N) {u v : List (TapeLetter A)}
    (hs : History.Step (MRule M) u v) :
    History.Step (MRule N) (u.map (TapeLetter.map f)) (v.map (TapeLetter.map f)) := by
  obtain ⟨x, l, r, y, hrule, rfl, rfl⟩ := hs
  exact ⟨x.map (TapeLetter.map f), l.map (TapeLetter.map f), r.map (TapeLetter.map f),
    y.map (TapeLetter.map f), h.mRule_map hrule, by simp, by simp⟩

/-- Backward transport of a rewriting step: from an image word, every step
lands on an image word, by the image step. -/
theorem step_inv (h : TMEmbed f M N) {W : List (TapeLetter A)}
    {w' : List (TapeLetter B)}
    (hs : History.Step (MRule N) (W.map (TapeLetter.map f)) w') :
    ∃ V, w' = V.map (TapeLetter.map f) ∧ History.Step (MRule M) W V := by
  obtain ⟨x, l, r, y, hrule, hu, rfl⟩ := hs
  obtain ⟨XL, Y, rfl, hxl, hy⟩ := append_eq_map hu.symm
  obtain ⟨X, L₀, rfl, hx, hlm⟩ := append_eq_map hxl
  obtain ⟨R₀, hr, hruleM⟩ := h.mRule_inv hrule hlm
  refine ⟨X ++ R₀ ++ Y, ?_, X, L₀, R₀, Y, hruleM, rfl, rfl⟩
  rw [hx, hr, hy]
  simp

/-- Forward transport of a derivation. -/
theorem derives_map (h : TMEmbed f M N) {u v : List (TapeLetter A)}
    (hd : History.Derives (MRule M) u v) :
    History.Derives (MRule N) (u.map (TapeLetter.map f)) (v.map (TapeLetter.map f)) := by
  induction hd with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (h.step_map hstep)

/-- Backward transport of a derivation of the halting word. -/
theorem derives_halt_of_map (h : TMEmbed f M N) : ∀ {w' : List (TapeLetter B)},
    History.Derives (MRule N) w' [TapeLetter.halt] →
    ∀ {w : List (TapeLetter A)}, w' = w.map (TapeLetter.map f) →
    History.Derives (MRule M) w [TapeLetter.halt] := by
  intro w' hd
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro w hw
    obtain rfl : w = [TapeLetter.halt] := by
      obtain ⟨a, l₀, rfl, h1, h2⟩ := cons_eq_map hw
      obtain rfl := nil_eq_map h2
      obtain rfl := eq_map_halt h1
      rfl
    exact Relation.ReflTransGen.refl
  | @head a d hstep hrest ih =>
    rintro w rfl
    obtain ⟨V, rfl, hstepM⟩ := h.step_inv hstep
    exact Relation.ReflTransGen.head hstepM (ih rfl)

/-- **Derivations of the halting word transport along an embedding.** -/
theorem derives_halt_iff (h : TMEmbed f M N) {w : List (TapeLetter A)} :
    History.Derives (MRule N) (w.map (TapeLetter.map f)) [TapeLetter.halt] ↔
      History.Derives (MRule M) w [TapeLetter.halt] := by
  constructor
  · intro hd
    exact h.derives_halt_of_map hd rfl
  · intro hd
    have := h.derives_map hd
    simpa [TapeLetter.map] using this

end TMEmbed

/-- **The whole bridge, for a drawn machine**: a machine whose predicates are
the images of `simTM`'s derives the halting word from the image of the
spelled resting configuration exactly when the abstract evaluation
terminates. -/
theorem TMEmbed.derives_iff_evalDom {B : Type} {f : SimU c → B} {N : TMData B}
    (h : TMEmbed f (simTM c) N) {k : PCont c} {fr : List (SimSym c)}
    (hfr : FrameSeg k fr) (v : List ℕ) (j t : ℕ) :
    History.Derives (MRule N)
      (startWord (((SimSym.endL :: (fr ++ SimSym.mid :: valR v j t)).map sts).map f))
      [TapeLetter.halt] ↔ (k.toCont.eval v).Dom := by
  rw [← startWord_map, h.derives_halt_iff]
  exact derives_startWord_iff_evalDom hfr v j t

end HaltHard

end DescriptiveComplexity
