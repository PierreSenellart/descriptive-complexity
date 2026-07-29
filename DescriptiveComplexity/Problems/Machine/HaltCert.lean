/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.MachinesUnbounded
import DescriptiveComplexity.OrderWalk

/-!
# An accepting run, read off as a finite certificate

The mathematical content of `HALT ∈ RE`: a machine accepts on an unbounded
tape exactly when a **finite** amount of data witnesses it, namely a finite
linear order of time points, a finite linear order of pages with a distinguished
input page, and the state, the head and the tape contents at each time.

Neither order is bounded by the instance – that is the whole point, and it is
why the certificate needs *invented values* rather than tuples of the universe –
but both are finite, because a run of `n` steps has `n + 1` time points and
moves the head by at most one page per step
(`DescriptiveComplexity.TMData.page_dist_stepsInU`), so it stays inside a band
of `2n + 1` pages.

## The shape of the certificate

`DescriptiveComplexity.TMData.RunCert` is the data – four functions, not
relations, because the combinatorics is much lighter that way; the first-order
kernel of the membership proof adds their totality and functionality as
conjuncts – and `DescriptiveComplexity.TMData.RunOK` the conditions:

* at a **least** time point the configuration is initial: a start state, the
  head on the lowest position of the input page, the input on that page and
  blanks on every other;
* between two time points **one covering the other**, some transition applies,
  writes, moves and leaves every other cell alone;
* at a **greatest** time point the state is accepting.

The conditions are stated with “least” and “greatest” as hypotheses rather than
with `⊥` and `⊤` so that they transcribe literally into first-order logic, where
that is how the ends of a guessed order are named.

The page successor of the step clause is
`DescriptiveComplexity.TMData.SuccCellAt`, which is
`DescriptiveComplexity.TMData.SuccCell` with `z + 1` replaced by “`z` is covered
by `z'`”: the certificate's pages are an abstract order, and covering is what a
first-order kernel can say about one.
-/

namespace DescriptiveComplexity

namespace TMData

/-! ### Reading a run off as a sequence

`DescriptiveComplexity.TMData.StepsInU` is an existential chain; the certificate
needs it as a function of the time index, which is what these two lemmas
supply. -/

section Sequence

variable {A : Type} {M : TMData A}

/-- **A run is a sequence of configurations.** -/
theorem exists_runU : ∀ (n : ℕ) (c d : ConfigU A), M.StepsInU n c d →
    ∃ f : ℕ → ConfigU A, f 0 = c ∧ f n = d ∧ ∀ i, i < n → M.StepU (f i) (f (i + 1)) := by
  intro n
  induction n with
  | zero =>
    intro c d h
    exact ⟨fun _ => c, rfl, show c = d from h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    rintro c d ⟨e, hstep, hrest⟩
    obtain ⟨g, hg0, hgn, hgs⟩ := ih e d hrest
    refine ⟨fun i => match i with | 0 => c | j + 1 => g j, rfl, hgn, fun i hi => ?_⟩
    cases i with
    | zero =>
      change M.StepU c (g 0)
      rw [hg0]
      exact hstep
    | succ j => exact hgs j (Nat.lt_of_succ_lt_succ hi)

/-- The prefix of a sequence of steps is a run. -/
theorem stepsInU_of_steps {n : ℕ} {f : ℕ → ConfigU A}
    (hs : ∀ i, i < n → M.StepU (f i) (f (i + 1))) :
    ∀ i, i ≤ n → M.StepsInU i (f 0) (f i) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    exact (ih (Nat.le_of_succ_le hj)).trans_step (hs j (Nat.lt_of_succ_le hj))

end Sequence

/-! ### The certificate -/

section Cert

variable {A : Type}

/-- **The next cell, over an abstract order of pages**:
`DescriptiveComplexity.TMData.SuccCell` with “the next page” read as covering
rather than as `z + 1`. -/
def SuccCellAt {P : Type} [Preorder P] (M : TMData A) (z : P) (p : A) (z' : P) (p' : A) : Prop :=
  (z' = z ∧ SuccPos M.Le M.Posn p p') ∨
    (z ⋖ z' ∧ MaxPos M.Le M.Posn p ∧ MinPos M.Le M.Posn p')

/-- **A run, as finite data**: the state, the page and the offset of the head,
and the contents of every cell, at each time point. -/
structure RunCert (A T P : Type) where
  /-- The state at a time point. -/
  st : T → A
  /-- The page the head is on at a time point. -/
  hdP : T → P
  /-- The position within that page. -/
  hdC : T → A
  /-- The symbol a cell holds at a time point. -/
  sym : T → P → A → A

/-- **The conditions making the data a run**: initial at a least time point,
one transition along every cover, accepting at a greatest one. -/
structure RunOK {A T P : Type} [Preorder T] [Preorder P] (M : TMData A) (zero : P)
    (r : RunCert A T P) : Prop where
  /-- At a least time point the configuration is initial. -/
  init : ∀ t : T, (∀ t', t ≤ t') →
    M.Start (r.st t) ∧ r.hdP t = zero ∧ MinPos M.Le M.Posn (r.hdC t) ∧
      ∀ p, M.Posn p → M.InitTape p (r.sym t zero p) ∧ ∀ z, z ≠ zero → M.Blank (r.sym t z p)
  /-- Along a cover of the time order, one transition applies. -/
  step : ∀ t t' : T, t ⋖ t' → ∃ τ, M.Tr τ ∧ M.Src τ (r.st t) ∧
    M.Read τ (r.sym t (r.hdP t) (r.hdC t)) ∧ M.Dst τ (r.st t') ∧
    M.Write τ (r.sym t' (r.hdP t) (r.hdC t)) ∧
    (∀ z p, ¬(z = r.hdP t ∧ p = r.hdC t) → r.sym t' z p = r.sym t z p) ∧
    ((M.Right τ ∧ SuccCellAt M (r.hdP t) (r.hdC t) (r.hdP t') (r.hdC t')) ∨
      (¬M.Right τ ∧ SuccCellAt M (r.hdP t') (r.hdC t') (r.hdP t) (r.hdC t)))
  /-- At a greatest time point the state is accepting. -/
  acc : ∀ t : T, (∀ t', t' ≤ t) → M.Acc (r.st t)

end Cert

/-! ### From a run to a certificate

The time points are `Fin (n + 1)` and the pages `Fin (2n + 1)`, the page `z`
standing for the integer `z - n`: by
`DescriptiveComplexity.TMData.page_dist_stepsInU` the head of a run of `n` steps
starting on page `0` never leaves that band. -/

section OfRun

variable {A : Type} {M : TMData A}

/-- The integer a page index of the band stands for. -/
private def pgOf (n : ℕ) (z : Fin (2 * n + 1)) : ℤ := (z : ℤ) - n

private theorem pgOf_injective (n : ℕ) : Function.Injective (pgOf n) := by
  intro z z' h
  have hz : (z : ℤ) = (z' : ℤ) := by simpa [pgOf] using h
  exact Fin.ext (by exact_mod_cast hz)

/-- The page index of a cell of the band. -/
private def ixOf (n : ℕ) (x : ℤ) : Fin (2 * n + 1) :=
  if h : (x + n).toNat < 2 * n + 1 then ⟨(x + n).toNat, h⟩ else ⟨0, Nat.succ_pos _⟩

private theorem pgOf_ixOf {n : ℕ} {x : ℤ} (h1 : -(n : ℤ) ≤ x) (h2 : x ≤ n) :
    pgOf n (ixOf n x) = x := by
  have hb : (x + n).toNat < 2 * n + 1 := by omega
  simp only [ixOf, dif_pos hb, pgOf]
  omega

/-- The certificate a sequence of configurations carries. Named, rather than
written as a structure literal inside the proof, so that its four projections
have stated equations and `rw` applies under them. -/
private def runOfSeq (n : ℕ) (f : ℕ → ConfigU A) :
    RunCert A (Fin (n + 1)) (Fin (2 * n + 1)) where
  st i := (f i).state
  hdP i := ixOf n (f i).head.1
  hdC i := (f i).head.2
  sym i z p := (f i).tape (pgOf n z, p)

@[simp] private theorem runOfSeq_st (n : ℕ) (f : ℕ → ConfigU A) (i : Fin (n + 1)) :
    (runOfSeq n f).st i = (f i).state := rfl

@[simp] private theorem runOfSeq_hdP (n : ℕ) (f : ℕ → ConfigU A) (i : Fin (n + 1)) :
    (runOfSeq n f).hdP i = ixOf n (f i).head.1 := rfl

@[simp] private theorem runOfSeq_hdC (n : ℕ) (f : ℕ → ConfigU A) (i : Fin (n + 1)) :
    (runOfSeq n f).hdC i = (f i).head.2 := rfl

@[simp] private theorem runOfSeq_sym (n : ℕ) (f : ℕ → ConfigU A) (i : Fin (n + 1))
    (z : Fin (2 * n + 1)) (p : A) :
    (runOfSeq n f).sym i z p = (f i).tape (pgOf n z, p) := rfl

/-- **A run yields a certificate**: the time points are the steps of the run and
the pages the band the head stays inside. -/
theorem runCert_of_acceptsU (h : M.AcceptsU) :
    ∃ (n : ℕ) (zero : Fin (2 * n + 1)) (r : RunCert A (Fin (n + 1)) (Fin (2 * n + 1))),
      RunOK M zero r := by
  obtain ⟨c₀, c, n, hinit, hrun, hacc⟩ := h
  obtain ⟨f, hf0, hfn, hfs⟩ := exists_runU n c₀ c hrun
  -- the head stays inside the band `[-n, n]` of pages
  have hband : ∀ i : Fin (n + 1), -(n : ℤ) ≤ (f i).head.1 ∧ (f i).head.1 ≤ n := by
    intro i
    have hrun' := stepsInU_of_steps hfs (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)
    have hd := page_dist_stepsInU hrun'
    have h0 : (f 0).head.1 = 0 := by rw [hf0]; exact hinit.2.1
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    rw [h0] at hd
    omega
  have hpg : ∀ i : Fin (n + 1), pgOf n (ixOf n (f i).head.1) = (f i).head.1 :=
    fun i => pgOf_ixOf (hband i).1 (hband i).2
  have hhead : ∀ i : Fin (n + 1),
      ((pgOf n (ixOf n (f i).head.1), (f i).head.2) : ℤ × A) = (f i).head :=
    fun i => Prod.ext (hpg i) rfl
  have hzero : pgOf n (ixOf n (0 : ℤ)) = 0 :=
    pgOf_ixOf (by simp) (by simp)
  refine ⟨n, ixOf n 0, runOfSeq n f, ?_, ?_, ?_⟩
  · -- initial, at the least time point
    intro t ht
    have ht0 : t = 0 := le_antisymm (ht 0) (Fin.zero_le t)
    subst ht0
    have hinit0 : M.IsInitU (f ((0 : Fin (n + 1)) : ℕ)) := by
      rw [show f ((0 : Fin (n + 1)) : ℕ) = c₀ from hf0]
      exact hinit
    simp only [runOfSeq_st, runOfSeq_hdP, runOfSeq_hdC, runOfSeq_sym, hzero]
    refine ⟨hinit0.1, congrArg (ixOf n) hinit0.2.1, hinit0.2.2.1, fun p hp => ⟨?_, ?_⟩⟩
    · exact (hinit0.2.2.2 0 p hp).1 rfl
    · intro z hz
      have hzne : pgOf n z ≠ 0 := fun hcon => hz (pgOf_injective n (hcon.trans hzero.symm))
      exact (hinit0.2.2.2 (pgOf n z) p hp).2 hzne
  · -- one step along every cover of the time order
    intro t t' hcov
    have hsucc : (t : ℕ) + 1 = (t' : ℕ) := finCovBy_iff.mp hcov
    have hlt : (t : ℕ) < n := by omega
    have hstep := hfs (t : ℕ) hlt
    rw [show (t : ℕ) + 1 = (t' : ℕ) from hsucc] at hstep
    obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
    simp only [runOfSeq_st, runOfSeq_hdP, runOfSeq_hdC, runOfSeq_sym, hhead t]
    refine ⟨τ, hτ, hsrc, hread, hdst, hwrite, ?_, ?_⟩
    · intro z p hzp
      refine hframe (pgOf n z, p) ?_
      rw [← hhead t]
      intro hcon
      have h1 : pgOf n z = pgOf n (ixOf n (f t).head.1) := congrArg Prod.fst hcon
      have h2 : p = (f t).head.2 := congrArg Prod.snd hcon
      exact hzp ⟨pgOf_injective n h1, h2⟩
    · -- the move, transported from `SuccCell` to `SuccCellAt`
      have hcell : ∀ i j : Fin (n + 1), M.SuccCell (f i).head (f j).head →
          SuccCellAt M (ixOf n (f i).head.1) (f i).head.2
            (ixOf n (f j).head.1) (f j).head.2 := by
        intro i j hs
        rcases hs with ⟨hz, hp⟩ | ⟨hz, hmax, hmin⟩
        · exact Or.inl ⟨congrArg (ixOf n) hz, hp⟩
        · refine Or.inr ⟨finCovBy_iff.mpr ?_, hmax, hmin⟩
          have h1 := hpg i
          have h2 := hpg j
          simp only [pgOf] at h1 h2
          omega
      rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨hr, hcell t t' hs⟩
      · exact Or.inr ⟨hr, hcell t' t hs⟩
  · -- accepting, at the greatest time point
    intro t ht
    have htn : t = Fin.last n := le_antisymm (Fin.le_last t) (ht (Fin.last n))
    subst htn
    have hacc0 : M.Acc (f ((Fin.last n : Fin (n + 1)) : ℕ)).state := by
      rw [show f ((Fin.last n : Fin (n + 1)) : ℕ) = c from hfn]
      exact hacc
    exact hacc0

end OfRun


/-! ### From a certificate to a run

The converse: an abstract certificate is realized by an actual run on the
unbounded tape. The pages are embedded into `ℤ` by their rank, shifted so that
the input page goes to `0`; every cell outside that image holds the blank, and
the head never reaches one, since the step clause moves it along a cover of the
page order. -/

section OfCert

variable {A T P : Type}

/-- The rank of a page is strictly monotone, hence injective: what makes the
embedding of the pages into `ℤ` faithful. -/
private theorem orank_lt_orank [LinearOrder P] [Finite P] {a b : P} (hab : a < b) :
    orank a < orank b :=
  Set.ncard_lt_ncard
    ((Set.ssubset_iff_of_subset fun _ hy => lt_trans hy hab).mpr ⟨a, hab, lt_irrefl a⟩)
    (Set.toFinite _)

private theorem orank_injective [LinearOrder P] [Finite P] :
    Function.Injective (orank : P → ℕ) := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (Nat.ne_of_lt (orank_lt_orank h))
  · exact h
  · exact absurd hab.symm (Nat.ne_of_lt (orank_lt_orank h))

/-- The integer a page stands for: its rank, shifted so that the input page is
cell `0`. -/
private noncomputable def pgEmb [LinearOrder P] (zero : P) (z : P) : ℤ :=
  (orank z : ℤ) - (orank zero : ℤ)

private theorem pgEmb_injective [LinearOrder P] [Finite P] (zero : P) :
    Function.Injective (pgEmb zero : P → ℤ) := by
  intro a b hab
  refine orank_injective ?_
  have : (orank a : ℤ) = (orank b : ℤ) := by simp only [pgEmb] at hab; omega
  exact_mod_cast this

private theorem pgEmb_self [LinearOrder P] (zero : P) : pgEmb zero zero = 0 := by
  simp [pgEmb]

private theorem pgEmb_covBy [LinearOrder P] [Finite P] {zero a b : P} (h : a ⋖ b) :
    pgEmb zero b = pgEmb zero a + 1 := by
  have := orank_covBy h
  simp only [pgEmb, this]
  push_cast
  ring

open Classical in
/-- The tape a certificate induces: the certificate's symbol where the cell is
the image of a page, and the blank everywhere else. -/
private noncomputable def tapeOf (r : RunCert A T P) (pg : P → ℤ) (b₀ : A) (t : T)
    (x : ℤ × A) : A :=
  if hx : ∃ z, pg z = x.1 then r.sym t hx.choose x.2 else b₀

/-- The configuration a certificate induces at a time point. -/
private noncomputable def confOf [LinearOrder P] (r : RunCert A T P) (pg : P → ℤ) (b₀ : A)
    (t : T) : ConfigU A :=
  ⟨r.st t, (pg (r.hdP t), r.hdC t), tapeOf r pg b₀ t⟩

@[simp] private theorem confOf_state [LinearOrder P] (r : RunCert A T P) (pg : P → ℤ) (b₀ : A)
    (t : T) : (confOf r pg b₀ t).state = r.st t := rfl

@[simp] private theorem confOf_head [LinearOrder P] (r : RunCert A T P) (pg : P → ℤ) (b₀ : A)
    (t : T) : (confOf r pg b₀ t).head = (pg (r.hdP t), r.hdC t) := rfl

@[simp] private theorem confOf_tape [LinearOrder P] (r : RunCert A T P) (pg : P → ℤ) (b₀ : A)
    (t : T) : (confOf r pg b₀ t).tape = tapeOf r pg b₀ t := rfl

private theorem tapeOf_pg {r : RunCert A T P} {pg : P → ℤ} {b₀ : A} (hinj : Function.Injective pg)
    (t : T) (z : P) (p : A) : tapeOf r pg b₀ t (pg z, p) = r.sym t z p := by
  classical
  have hex : ∃ z', pg z' = ((pg z, p) : ℤ × A).1 := ⟨z, rfl⟩
  simp only [tapeOf, dif_pos hex]
  exact congrArg (fun w => r.sym t w p) (hinj hex.choose_spec)

private theorem tapeOf_out {r : RunCert A T P} {pg : P → ℤ} {b₀ : A} (t : T) {x : ℤ × A}
    (hx : ∀ z, pg z ≠ x.1) : tapeOf r pg b₀ t x = b₀ := by
  classical
  have : ¬∃ z, pg z = x.1 := fun ⟨z, hz⟩ => hx z hz
  simp only [tapeOf, dif_neg this]

variable {M : TMData A}

/-- **A certificate is realized by a run**: the abstract time order supplies the
steps and the abstract page order the cells, so an accepting certificate makes
the machine accept on the unbounded tape. -/
theorem acceptsU_of_runCert [LinearOrder T] [Finite T] [Nonempty T] [LinearOrder P] [Finite P]
    (hb : ∃ b, M.Blank b) {zero : P} {r : RunCert A T P} (h : RunOK M zero r) : M.AcceptsU := by
  classical
  obtain ⟨b₀, hb₀⟩ := hb
  have hinj : Function.Injective (pgEmb zero : P → ℤ) := pgEmb_injective zero
  have hzero : pgEmb zero zero = 0 := pgEmb_self zero
  have htp := tapeOf_pg (r := r) (b₀ := b₀) hinj
  have htpout := tapeOf_out (r := r) (pg := (pgEmb zero : P → ℤ)) (b₀ := b₀)
  -- a least and a greatest time point
  obtain ⟨t₀, -, ht₀'⟩ := Set.exists_min_image (Set.univ : Set T) (id : T → T) (Set.toFinite _)
    ⟨Classical.arbitrary T, trivial⟩
  obtain ⟨t₁, -, ht₁'⟩ := Set.exists_max_image (Set.univ : Set T) (id : T → T) (Set.toFinite _)
    ⟨Classical.arbitrary T, trivial⟩
  have ht₀ : ∀ t' : T, t₀ ≤ t' := fun t' => ht₀' t' trivial
  have ht₁ : ∀ t' : T, t' ≤ t₁ := fun t' => ht₁' t' trivial
  -- the initial configuration
  obtain ⟨hst, hpz, hmin, htape⟩ := h.init t₀ ht₀
  have hinit : M.IsInitU (confOf r (pgEmb zero) b₀ t₀) := by
    refine ⟨hst, ?_, ?_, ?_⟩
    · simp only [confOf_head]
      rw [hpz]
      exact hzero
    · simp only [confOf_head]
      exact hmin
    · intro z p hp
      simp only [confOf_tape]
      constructor
      · rintro rfl
        rw [show ((0 : ℤ), p) = (pgEmb zero zero, p) by rw [hzero], htp t₀ zero p]
        exact (htape p hp).1
      · intro hz
        by_cases hex : ∃ z', pgEmb zero z' = z
        · obtain ⟨z', rfl⟩ := hex
          have hz' : z' ≠ zero := fun hcon => hz (by rw [hcon, hzero])
          rw [htp t₀ z' p]
          exact (htape p hp).2 z' hz'
        · rw [htpout t₀ (x := (z, p)) (fun z' hcon => hex ⟨z', hcon⟩)]
          exact hb₀
  -- one step of the run, along a cover of the time order
  have hstep : ∀ w z : T, w ⋖ z →
      M.StepU (confOf r (pgEmb zero) b₀ w) (confOf r (pgEmb zero) b₀ z) := by
    intro w z hcov
    obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := h.step w z hcov
    have hcell : ∀ (z₁ : P) (p₁ : A) (z₂ : P) (p₂ : A), SuccCellAt M z₁ p₁ z₂ p₂ →
        M.SuccCell (pgEmb zero z₁, p₁) (pgEmb zero z₂, p₂) := by
      rintro z₁ p₁ z₂ p₂ (⟨he, hp⟩ | ⟨hc, hmax, hmn⟩)
      · exact Or.inl ⟨by rw [he], hp⟩
      · exact Or.inr ⟨pgEmb_covBy hc, hmax, hmn⟩
    refine ⟨τ, hτ, hsrc, ?_, hdst, ?_, ?_, ?_⟩
    · simp only [confOf_head, confOf_tape, htp w (r.hdP w) (r.hdC w)]
      exact hread
    · simp only [confOf_head, confOf_tape, htp z (r.hdP w) (r.hdC w)]
      exact hwrite
    · simp only [confOf_head, confOf_tape]
      intro x hx
      by_cases hex : ∃ z', pgEmb zero z' = x.1
      · obtain ⟨z', hz'⟩ := hex
        have hxe : x = (pgEmb zero z', x.2) := Prod.ext hz'.symm rfl
        rw [hxe, htp z z' x.2, htp w z' x.2]
        refine hframe z' x.2 ?_
        rintro ⟨rfl, hp2⟩
        exact hx (by rw [hxe, hz', hp2])
      · rw [htpout z (x := x) (fun z' hcon => hex ⟨z', hcon⟩),
          htpout w (x := x) (fun z' hcon => hex ⟨z', hcon⟩)]
    · simp only [confOf_head]
      rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨hr, hcell _ _ _ _ hs⟩
      · exact Or.inr ⟨hr, hcell _ _ _ _ hs⟩
  -- every time point is reached from the least one
  have hreach : ∀ t : T, ∃ k : ℕ,
      M.StepsInU k (confOf r (pgEmb zero) b₀ t₀) (confOf r (pgEmb zero) b₀ t) := by
    intro t
    refine order_induction
      (P := fun t => ∃ k : ℕ,
        M.StepsInU k (confOf r (pgEmb zero) b₀ t₀) (confOf r (pgEmb zero) b₀ t)) ?_ ?_ t
    · intro y hy
      have hy0 : t₀ = y := le_antisymm (ht₀ y) (hy t₀)
      refine ⟨0, ?_⟩
      change confOf r (pgEmb zero) b₀ t₀ = confOf r (pgEmb zero) b₀ y
      rw [hy0]
    · rintro w y hwy hnb ⟨k, hk⟩
      exact ⟨k + 1, hk.trans_step (hstep w y ⟨hwy, fun c hc hcy => hnb c ⟨hc, hcy⟩⟩)⟩
  obtain ⟨k, hk⟩ := hreach t₁
  exact ⟨_, _, k, hinit, hk, h.acc t₁ ht₁⟩

end OfCert


/-! ### The equivalence -/

section Bridge

variable {A : Type} {M : TMData A}

/-- **Acceptance on an unbounded tape is a finite certificate**: a machine
accepts exactly when some finite linear order of time points and some finite
linear order of pages carry a run of it. The two orders are not bounded by the
instance, which is why the certificate needs invented values; they are finite,
which is why it is a certificate at all. -/
theorem acceptsU_iff_runCert (hb : ∃ b, M.Blank b) :
    M.AcceptsU ↔ ∃ (T P : Type) (_ : LinearOrder T) (_ : Finite T) (_ : Nonempty T)
      (_ : LinearOrder P) (_ : Finite P) (zero : P) (r : RunCert A T P), RunOK M zero r := by
  constructor
  · intro h
    obtain ⟨n, zero, r, hr⟩ := runCert_of_acceptsU h
    exact ⟨Fin (n + 1), Fin (2 * n + 1), inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, zero, r, hr⟩
  · rintro ⟨T, P, iT, fT, nT, iP, fP, zero, r, hr⟩
    letI := iT
    letI := fT
    letI := nT
    letI := iP
    letI := fP
    exact acceptsU_of_runCert hb hr

end Bridge

end TMData

end DescriptiveComplexity
