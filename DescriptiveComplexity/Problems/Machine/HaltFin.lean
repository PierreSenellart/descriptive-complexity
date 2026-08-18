/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Halt
import DescriptiveComplexity.Problems.Machine.HaltCert

/-!
# The certificate as relations on invented values

`DescriptiveComplexity.TMData.RunCert` carries the two orders as *types* and the
run as *functions*, which is what made the combinatorics of
`DescriptiveComplexity.TMData.acceptsU_iff_runCert` short. An `∃SO[new]`
certificate cannot: its relation variables range over `A ⊕ Fin m`, so the two
sorts have to become unary predicates on the invented values, their orders
binary relations, and the four functions relations with totality and
functionality demanded of them.

`DescriptiveComplexity.TMData.RunRel` is that presentation and
`DescriptiveComplexity.TMData.RunRelOK` its conditions, each of them a clause
the first-order kernel can mirror. The two ends of the time order and the
step relation are `DescriptiveComplexity.MinPos`,
`DescriptiveComplexity.MaxPos` and `DescriptiveComplexity.SuccPos` – the same
order vocabulary the bounded machine problems already use, reused here on a
*guessed* order rather than on the instance's.

**The two sorts need not be disjoint.** `Time` and `Page` are independent
predicates on the invented values, and nothing asks them to be apart; that is
what lets the run of `n` steps be read off over `Fin (2n + 1)` alone, with the
time points the first `n + 1` values and the pages all of them, instead of over
a disjoint sum that would then have to be transported to a `Fin m`.
-/

namespace DescriptiveComplexity

namespace TMData

/-! ### Linear orders on a marked subset -/

section LinOrdOn

variable {D : Type}

/-- A relation is a linear order **on the elements marked by `S`**: the form a
first-order kernel states a guessed order in, since the guessed order says
nothing outside the sort it is meant for. -/
def IsLinOrdOn (Le : D → D → Prop) (S : D → Prop) : Prop :=
  (∀ x, S x → Le x x) ∧
    (∀ x y z, S x → S y → S z → Le x y → Le y z → Le x z) ∧
    (∀ x y, S x → S y → Le x y → Le y x → x = y) ∧
    (∀ x y, S x → S y → Le x y ∨ Le y x)

variable {Le : D → D → Prop} {S : D → Prop}

/-- A linear order on a marked subset is a linear order on the subtype it
marks. -/
theorem isLinOrd_subtype (h : IsLinOrdOn Le S) :
    IsLinOrd (fun x y : {d : D // S d} => Le x y) :=
  ⟨fun x => h.1 x x.2, fun x y z => h.2.1 x y z x.2 y.2 z.2,
    fun x y hxy hyx => Subtype.ext (h.2.2.1 x y x.2 y.2 hxy hyx),
    fun x y => h.2.2.2 x y x.2 y.2⟩

end LinOrdOn

/-! ### The certificate, as relations -/

section Rel

variable {A D : Type}

/-- **A run, as relations on the invented values**: two sorts with their
orders, the input page, and the state, the head and the tape contents as
relations rather than functions. -/
structure RunRel (A D : Type) where
  /-- The invented values that are time points. -/
  Time : D → Prop
  /-- The order of time. -/
  TLe : D → D → Prop
  /-- The invented values that are pages. -/
  Page : D → Prop
  /-- The order of the pages. -/
  PLe : D → D → Prop
  /-- The input page. -/
  Zero : D → Prop
  /-- `St t q`: the state at the time point `t`. -/
  St : D → A → Prop
  /-- `HdP t z`: the page the head is on at the time point `t`. -/
  HdP : D → D → Prop
  /-- `HdC t p`: the position within that page. -/
  HdC : D → A → Prop
  /-- `Sym t z p a`: the cell `(z, p)` holds `a` at the time point `t`. -/
  Sym : D → D → A → A → Prop

/-- The next cell, over the guessed order of the pages:
`DescriptiveComplexity.TMData.SuccCellAt` with covering replaced by
`DescriptiveComplexity.SuccPos` on the marked pages. -/
def SuccCellRel (M : TMData A) (c : RunRel A D) (z : D) (p : A) (z' : D) (p' : A) : Prop :=
  (z' = z ∧ SuccPos M.Le M.Posn p p') ∨
    (SuccPos c.PLe c.Page z z' ∧ MaxPos M.Le M.Posn p ∧ MinPos M.Le M.Posn p')

/-- **The conditions making the relations a run.** Beside the shape conditions
– the two orders are linear on their sorts, the input page is unique, and the
four relations are total and functional where they are read – there are the
three of `DescriptiveComplexity.TMData.RunOK`: initial at the lowest time point,
one transition along every step of the time order, accepting at the highest. -/
structure RunRelOK (M : TMData A) (c : RunRel A D) : Prop where
  /-- There is a time point. -/
  time_ne : ∃ t, c.Time t
  /-- Time is linearly ordered. -/
  tle_lin : IsLinOrdOn c.TLe c.Time
  /-- There is a page. -/
  page_ne : ∃ z, c.Page z
  /-- The pages are linearly ordered. -/
  ple_lin : IsLinOrdOn c.PLe c.Page
  /-- There is an input page. -/
  zero_ex : ∃ z, c.Zero z
  /-- The input page is a page. -/
  zero_page : ∀ z, c.Zero z → c.Page z
  /-- There is at most one input page. -/
  zero_uniq : ∀ z z', c.Zero z → c.Zero z' → z = z'
  /-- Every time point has a state. -/
  st_tot : ∀ t, c.Time t → ∃ q, c.St t q
  /-- A time point has at most one state. -/
  st_fun : ∀ t q q', c.St t q → c.St t q' → q = q'
  /-- At every time point the head is on a page. -/
  hdP_tot : ∀ t, c.Time t → ∃ z, c.Page z ∧ c.HdP t z
  /-- The head is on at most one page. -/
  hdP_fun : ∀ t z z', c.HdP t z → c.HdP t z' → z = z'
  /-- At every time point the head is at a position of its page. -/
  hdC_tot : ∀ t, c.Time t → ∃ p, c.HdC t p
  /-- The head is at most at one position. -/
  hdC_fun : ∀ t p p', c.HdC t p → c.HdC t p' → p = p'
  /-- Every cell holds a symbol at every time point. -/
  sym_tot : ∀ t z p, c.Time t → c.Page z → ∃ a, c.Sym t z p a
  /-- A cell holds at most one symbol. -/
  sym_fun : ∀ t z p a a', c.Sym t z p a → c.Sym t z p a' → a = a'
  /-- At the lowest time point the configuration is initial. -/
  init : ∀ t q z p, MinPos c.TLe c.Time t → c.St t q → c.HdP t z → c.HdC t p →
    M.Start q ∧ c.Zero z ∧ MinPos M.Le M.Posn p ∧
      ∀ z' p' a, c.Page z' → M.Posn p' → c.Sym t z' p' a →
        (c.Zero z' → M.InitTape p' a) ∧ (¬c.Zero z' → M.Blank a)
  /-- Along every step of the time order, one transition applies. -/
  step : ∀ t t' q q' z p a a', SuccPos c.TLe c.Time t t' →
    c.St t q → c.St t' q' → c.HdP t z → c.HdC t p → c.Sym t z p a → c.Sym t' z p a' →
    ∃ τ, M.Tr τ ∧ M.Src τ q ∧ M.Read τ a ∧ M.Dst τ q' ∧ M.Write τ a' ∧
      (∀ z₁ p₁ b b', c.Page z₁ → ¬(z₁ = z ∧ p₁ = p) →
        c.Sym t z₁ p₁ b → c.Sym t' z₁ p₁ b' → b = b') ∧
      ∀ z₂ p₂, c.HdP t' z₂ → c.HdC t' p₂ →
        (M.Right τ ∧ SuccCellRel M c z p z₂ p₂) ∨
          (¬M.Right τ ∧ SuccCellRel M c z₂ p₂ z p)
  /-- At the highest time point the state is accepting. -/
  acc : ∀ t q, MaxPos c.TLe c.Time t → c.St t q → M.Acc q

end Rel

/-! ### From the relations to a run

The two sorts become the subtypes they mark, the four relations become
functions by choice, and `DescriptiveComplexity.TMData.acceptsU_of_runCert`
does the rest. The only work is the dictionary between the order vocabulary on
the marked sets (`MinPos`, `MaxPos`, `SuccPos`) and the order of the subtype
(least, greatest, covering). -/

section OfRel

variable {A D : Type} {M : TMData A} {Le : D → D → Prop} {S : D → Prop}

/-! The dictionary between the order vocabulary on a marked set (`MinPos`,
`MaxPos`, `SuccPos`) and the order of the subtype it marks (least, greatest,
covering). Stated for an arbitrary linear order on the subtype whose `≤` is the
marked relation, so that the instance built by
`DescriptiveComplexity.IsLinOrd.toLinearOrder` is not baked into the
statements. -/

section Sub

variable [LinearOrder {d : D // S d}]

/-- A least element of the subtype is a lowest marked element. -/
theorem minPos_of_le (hle : ∀ a b : {d : D // S d}, a ≤ b ↔ Le a.val b.val)
    {t : {d : D // S d}} (ht : ∀ t', t ≤ t') : MinPos Le S t.val :=
  ⟨t.2, fun q hq => (hle _ _).mp (ht ⟨q, hq⟩)⟩

/-- A greatest element of the subtype is a highest marked element. -/
theorem maxPos_of_le (hle : ∀ a b : {d : D // S d}, a ≤ b ↔ Le a.val b.val)
    {t : {d : D // S d}} (ht : ∀ t', t' ≤ t) : MaxPos Le S t.val :=
  ⟨t.2, fun q hq => (hle _ _).mp (ht ⟨q, hq⟩)⟩

/-- Covering in the subtype is the successor relation on the marked set. -/
theorem succPos_of_covBy (hle : ∀ a b : {d : D // S d}, a ≤ b ↔ Le a.val b.val)
    {a b : {d : D // S d}} (hab : a ⋖ b) : SuccPos Le S a.val b.val := by
  refine ⟨a.2, b.2, (hle _ _).mp hab.1.le, fun hcon => ?_, fun r hr h1 h2 => ?_⟩
  · exact absurd (Subtype.ext hcon : a = b) (ne_of_lt hab.1)
  · rcases le_or_gt (⟨r, hr⟩ : {d : D // S d}) a with hra | hra
    · exact Or.inl (congrArg Subtype.val (le_antisymm hra ((hle _ _).mpr h1)))
    · have hnb : ¬((⟨r, hr⟩ : {d : D // S d}) < b) := hab.2 hra
      exact Or.inr (congrArg Subtype.val (le_antisymm ((hle _ _).mpr h2) (not_lt.mp hnb)))

/-- …and conversely. -/
theorem covBy_of_succPos (hle : ∀ a b : {d : D // S d}, a ≤ b ↔ Le a.val b.val)
    {a b : {d : D // S d}} (hs : SuccPos Le S a.val b.val) : a ⋖ b := by
  have hab : a < b :=
    lt_of_le_of_ne ((hle _ _).mpr hs.2.2.1) fun hcon => hs.2.2.2.1 (congrArg Subtype.val hcon)
  refine ⟨hab, fun u hu hub => ?_⟩
  rcases hs.2.2.2.2 u.val u.2 ((hle _ _).mp hu.le) ((hle _ _).mp hub.le) with heq | heq
  · exact absurd (Subtype.ext heq : u = a) (ne_of_gt hu)
  · exact absurd (Subtype.ext heq : u = b) (ne_of_lt hub)

end Sub

/-- **The relations are realized by a run**: the two sorts are the subtypes
they mark, and the four relations become functions by choice. -/
theorem acceptsU_of_runRel [Finite D] (hb : ∃ b, M.Blank b) {c : RunRel A D}
    (h : RunRelOK M c) : M.AcceptsU := by
  classical
  let ordT : LinearOrder {d : D // c.Time d} := (isLinOrd_subtype h.tle_lin).toLinearOrder
  let ordP : LinearOrder {d : D // c.Page d} := (isLinOrd_subtype h.ple_lin).toLinearOrder
  have hleT : ∀ a b : {d : D // c.Time d}, a ≤ b ↔ c.TLe a.val b.val := fun _ _ => Iff.rfl
  have hleP : ∀ a b : {d : D // c.Page d}, a ≤ b ↔ c.PLe a.val b.val := fun _ _ => Iff.rfl
  have : Nonempty {d : D // c.Time d} := ⟨⟨h.time_ne.choose, h.time_ne.choose_spec⟩⟩
  -- the four functions
  have hstT : ∀ t : {d : D // c.Time d}, ∃ q, c.St t.val q := fun t => h.st_tot t.val t.2
  have hhdPT : ∀ t : {d : D // c.Time d}, ∃ z, c.Page z ∧ c.HdP t.val z :=
    fun t => h.hdP_tot t.val t.2
  have hhdCT : ∀ t : {d : D // c.Time d}, ∃ p, c.HdC t.val p := fun t => h.hdC_tot t.val t.2
  have hsymT : ∀ (t : {d : D // c.Time d}) (z : {d : D // c.Page d}) (p : A),
      ∃ a, c.Sym t.val z.val p a := fun t z p => h.sym_tot t.val z.val p t.2 z.2
  set st : {d : D // c.Time d} → A := fun t => (hstT t).choose with hstdef
  set hdP : {d : D // c.Time d} → {d : D // c.Page d} :=
    fun t => ⟨(hhdPT t).choose, (hhdPT t).choose_spec.1⟩ with hdPdef
  set hdC : {d : D // c.Time d} → A := fun t => (hhdCT t).choose with hdCdef
  set sym : {d : D // c.Time d} → {d : D // c.Page d} → A → A :=
    fun t z p => (hsymT t z p).choose with symdef
  have hst : ∀ t, c.St t.val (st t) := fun t => (hstT t).choose_spec
  have hhdP : ∀ t, c.HdP t.val (hdP t).val := fun t => (hhdPT t).choose_spec.2
  have hhdC : ∀ t, c.HdC t.val (hdC t) := fun t => (hhdCT t).choose_spec
  have hsym : ∀ t z p, c.Sym t.val z.val p (sym t z p) := fun t z p => (hsymT t z p).choose_spec
  set zero : {d : D // c.Page d} :=
    ⟨h.zero_ex.choose, h.zero_page _ h.zero_ex.choose_spec⟩ with zerodef
  have hzero : c.Zero zero.val := h.zero_ex.choose_spec
  have hzeroiff : ∀ z : {d : D // c.Page d}, c.Zero z.val ↔ z = zero :=
    fun z => ⟨fun hz => Subtype.ext (h.zero_uniq _ _ hz hzero), fun hz => hz ▸ hzero⟩
  refine acceptsU_of_runCert hb (zero := zero) (r := ⟨st, hdP, hdC, sym⟩) ⟨?_, ?_, ?_⟩
  · -- initial
    intro t ht
    obtain ⟨hstart, hz, hmin, htape⟩ :=
      h.init t.val (st t) (hdP t).val (hdC t) (minPos_of_le hleT ht) (hst t) (hhdP t) (hhdC t)
    refine ⟨hstart, (hzeroiff (hdP t)).mp hz, hmin, fun p hp => ⟨?_, fun z hzne => ?_⟩⟩
    · exact (htape zero.val p (sym t zero p) zero.2 hp (hsym t zero p)).1 hzero
    · exact (htape z.val p (sym t z p) z.2 hp (hsym t z p)).2
        fun hcon => hzne ((hzeroiff z).mp hcon)
  · -- one step
    intro w z hcov
    obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ :=
      h.step w.val z.val (st w) (st z) (hdP w).val (hdC w) (sym w (hdP w) (hdC w))
        (sym z (hdP w) (hdC w)) (succPos_of_covBy hleT hcov) (hst w) (hst z) (hhdP w)
        (hhdC w) (hsym w (hdP w) (hdC w)) (hsym z (hdP w) (hdC w))
    refine ⟨τ, hτ, hsrc, hread, hdst, hwrite, ?_, ?_⟩
    · intro z₁ p₁ hne
      exact (hframe z₁.val p₁ (sym w z₁ p₁) (sym z z₁ p₁) z₁.2
        (fun hcon => hne ⟨Subtype.ext hcon.1, hcon.2⟩) (hsym w z₁ p₁) (hsym z z₁ p₁)).symm
    · have hcell : ∀ (z₁ : {d : D // c.Page d}) (p₁ : A) (z₂ : {d : D // c.Page d}) (p₂ : A),
          SuccCellRel M c z₁.val p₁ z₂.val p₂ → SuccCellAt M z₁ p₁ z₂ p₂ := by
        rintro z₁ p₁ z₂ p₂ (⟨he, hp⟩ | ⟨hs, hmax, hmn⟩)
        · exact Or.inl ⟨Subtype.ext he, hp⟩
        · exact Or.inr ⟨covBy_of_succPos hleP hs, hmax, hmn⟩
      rcases hmove (hdP z).val (hdC z) (hhdP z) (hhdC z) with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨hr, hcell _ _ _ _ hs⟩
      · exact Or.inr ⟨hr, hcell _ _ _ _ hs⟩
  · -- accepting
    intro t ht
    exact h.acc t.val (st t) (maxPos_of_le hleT ht) (hst t)

end OfRel

/-! ### From a run to the relations

The time points are the first `n + 1` values of `Fin (2n + 1)` and the pages all
of them: the two sorts are *not* disjoint, and need not be, which is what keeps
the invented values a single `Fin m` with no disjoint sum to transport. -/

section ToRel

variable {A : Type} {M : TMData A}

/-- The time index a value of the band denotes, clamped so as to be total. -/
private def tIx (n : ℕ) (d : Fin (2 * n + 1)) : Fin (n + 1) := ⟨min (d : ℕ) n, by omega⟩

private theorem tIx_val {n : ℕ} {d : Fin (2 * n + 1)} (hd : (d : ℕ) < n + 1) :
    (tIx n d : ℕ) = (d : ℕ) := by
  simp only [tIx]
  omega

private theorem tIx_eq {n : ℕ} {d : Fin (2 * n + 1)} {i : Fin (n + 1)} (hd : (d : ℕ) < n + 1)
    (hi : (d : ℕ) = (i : ℕ)) : tIx n d = i := Fin.ext ((tIx_val hd).trans hi)

/-- A run over the band, read as relations on `Fin (2n + 1)`. -/
private def toRunRel {n : ℕ} (zero : Fin (2 * n + 1))
    (r : RunCert A (Fin (n + 1)) (Fin (2 * n + 1))) : RunRel A (Fin (2 * n + 1)) where
  Time d := (d : ℕ) < n + 1
  TLe d d' := (d : ℕ) ≤ (d' : ℕ)
  Page _ := True
  PLe d d' := (d : ℕ) ≤ (d' : ℕ)
  Zero d := d = zero
  St d q := (d : ℕ) < n + 1 ∧ q = r.st (tIx n d)
  HdP d z := (d : ℕ) < n + 1 ∧ z = r.hdP (tIx n d)
  HdC d p := (d : ℕ) < n + 1 ∧ p = r.hdC (tIx n d)
  Sym d z p a := (d : ℕ) < n + 1 ∧ a = r.sym (tIx n d) z p

section Eqns

variable {n : ℕ} {zero : Fin (2 * n + 1)} {r : RunCert A (Fin (n + 1)) (Fin (2 * n + 1))}
variable (d d' z : Fin (2 * n + 1)) (q p a : A)

@[simp] private theorem toRunRel_time :
    (toRunRel zero r).Time d ↔ (d : ℕ) < n + 1 := Iff.rfl

@[simp] private theorem toRunRel_tle :
    (toRunRel zero r).TLe d d' ↔ (d : ℕ) ≤ (d' : ℕ) := Iff.rfl

@[simp] private theorem toRunRel_page : (toRunRel zero r).Page d ↔ True := Iff.rfl

@[simp] private theorem toRunRel_ple :
    (toRunRel zero r).PLe d d' ↔ (d : ℕ) ≤ (d' : ℕ) := Iff.rfl

@[simp] private theorem toRunRel_zero : (toRunRel zero r).Zero d ↔ d = zero := Iff.rfl

@[simp] private theorem toRunRel_st :
    (toRunRel zero r).St d q ↔ (d : ℕ) < n + 1 ∧ q = r.st (tIx n d) := Iff.rfl

@[simp] private theorem toRunRel_hdP :
    (toRunRel zero r).HdP d z ↔ (d : ℕ) < n + 1 ∧ z = r.hdP (tIx n d) := Iff.rfl

@[simp] private theorem toRunRel_hdC :
    (toRunRel zero r).HdC d p ↔ (d : ℕ) < n + 1 ∧ p = r.hdC (tIx n d) := Iff.rfl

@[simp] private theorem toRunRel_sym :
    (toRunRel zero r).Sym d z p a ↔ (d : ℕ) < n + 1 ∧ a = r.sym (tIx n d) z p := Iff.rfl

end Eqns

/-- Covering of the pages is their successor relation, both being one step of
the order of `Fin (2n + 1)`. -/
private theorem succPage_of_covBy {n : ℕ} {zero : Fin (2 * n + 1)}
    {r : RunCert A (Fin (n + 1)) (Fin (2 * n + 1))} {z z' : Fin (2 * n + 1)} (h : z ⋖ z') :
    SuccPos (toRunRel zero r).PLe (toRunRel zero r).Page z z' := by
  have hv : (z : ℕ) + 1 = (z' : ℕ) := finCovBy_iff.mp h
  refine ⟨trivial, trivial, ?_, fun hcon => ?_, fun w _ h1 h2 => ?_⟩
  · simp only [toRunRel_ple]; omega
  · rw [hcon] at hv; omega
  · simp only [toRunRel_ple] at h1 h2
    rcases Nat.lt_or_ge (w : ℕ) (z' : ℕ) with hw | hw
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Fin.ext (by omega))

/-- **A run over the band yields the relations.** -/
private theorem runRelOK_toRunRel {n : ℕ} {zero : Fin (2 * n + 1)}
    {r : RunCert A (Fin (n + 1)) (Fin (2 * n + 1))} (h : RunOK M zero r) :
    RunRelOK M (toRunRel zero r) := by
  -- the least, the greatest and the successive time values
  have hmin : ∀ t : Fin (2 * n + 1), MinPos (toRunRel zero r).TLe (toRunRel zero r).Time t →
      tIx n t = 0 := by
    intro t ht
    have h1 : ((t : Fin (2 * n + 1)) : ℕ) < n + 1 := ht.1
    have h0 := ht.2 ⟨0, by omega⟩ (by simp)
    simp only [toRunRel_tle] at h0
    exact tIx_eq h1 (by simpa using Nat.le_zero.mp h0)
  have hmax : ∀ t : Fin (2 * n + 1), MaxPos (toRunRel zero r).TLe (toRunRel zero r).Time t →
      tIx n t = Fin.last n := by
    intro t ht
    have h1 : ((t : Fin (2 * n + 1)) : ℕ) < n + 1 := ht.1
    have h0 := ht.2 ⟨n, by omega⟩ (by simp)
    simp only [toRunRel_tle] at h0
    exact tIx_eq h1 (by simp only [Fin.val_last]; omega)
  have hcov : ∀ t t' : Fin (2 * n + 1),
      SuccPos (toRunRel zero r).TLe (toRunRel zero r).Time t t' → tIx n t ⋖ tIx n t' := by
    intro t t' hs
    obtain ⟨h1, h2, hle, hne, hbet⟩ := hs
    simp only [toRunRel_time] at h1 h2
    simp only [toRunRel_tle] at hle
    have hv : (t : ℕ) + 1 = (t' : ℕ) := by
      by_contra hcon
      have hne' : (t : ℕ) ≠ (t' : ℕ) := fun hh => hne (Fin.ext hh)
      have hlt : (t : ℕ) + 1 < (t' : ℕ) := by omega
      have hb : ((⟨(t : ℕ) + 1, by omega⟩ : Fin (2 * n + 1)) : ℕ) = (t : ℕ) + 1 := rfl
      rcases hbet ⟨(t : ℕ) + 1, by omega⟩ (by simp only [toRunRel_time]; omega)
        (by simp only [toRunRel_tle]; omega) (by simp only [toRunRel_tle]; omega) with
        heq | heq
      · exact absurd (congrArg Fin.val heq) (by rw [hb]; omega)
      · exact absurd (congrArg Fin.val heq) (by rw [hb]; omega)
    exact finCovBy_iff.mpr (by rw [tIx_val h1, tIx_val h2]; omega)
  refine ⟨⟨⟨0, by omega⟩, by simp⟩, ⟨fun _ _ => le_rfl, fun _ _ _ _ _ _ => le_trans,
    fun x y _ _ hxy hyx => Fin.ext (le_antisymm hxy hyx), fun x y _ _ => le_total _ _⟩,
    ⟨⟨0, by omega⟩, trivial⟩, ⟨fun _ _ => le_rfl, fun _ _ _ _ _ _ => le_trans,
      fun x y _ _ hxy hyx => Fin.ext (le_antisymm hxy hyx), fun x y _ _ => le_total _ _⟩,
    ⟨zero, rfl⟩, fun _ _ => trivial, fun z z' hz hz' => hz.trans hz'.symm, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t ht => ⟨r.st (tIx n t), ht, rfl⟩
  · exact fun _ _ _ hq hq' => hq.2.trans hq'.2.symm
  · exact fun t ht => ⟨r.hdP (tIx n t), trivial, ht, rfl⟩
  · exact fun _ _ _ hz hz' => hz.2.trans hz'.2.symm
  · exact fun t ht => ⟨r.hdC (tIx n t), ht, rfl⟩
  · exact fun _ _ _ hp hp' => hp.2.trans hp'.2.symm
  · exact fun t z p ht _ => ⟨r.sym (tIx n t) z p, ht, rfl⟩
  · exact fun _ _ _ _ _ ha ha' => ha.2.trans ha'.2.symm
  · -- initial
    intro t q z p htmin hq hz hp
    have hti := hmin t htmin
    obtain ⟨hstart, hpz, hminp, htape⟩ :=
      h.init (tIx n t) (by rw [hti]; exact fun i => Fin.zero_le i)
    simp only [toRunRel_st, toRunRel_hdP, toRunRel_hdC] at hq hz hp
    rw [hq.2, hz.2, hp.2]
    refine ⟨hstart, ?_, hminp, fun z' p' a _ hp' ha => ?_⟩
    · simpa using hpz
    · simp only [toRunRel_sym] at ha
      simp only [toRunRel_zero]
      refine ⟨fun hz' => ?_, fun hz' => ?_⟩
      · rw [ha.2, hz']
        exact (htape p' hp').1
      · rw [ha.2]
        exact (htape p' hp').2 z' hz'
  · -- one step
    intro t t' q q' z p a a' hsucc hq hq' hz hp ha ha'
    obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := h.step _ _ (hcov t t' hsucc)
    simp only [toRunRel_st, toRunRel_hdP, toRunRel_hdC, toRunRel_sym] at hq hq' hz hp ha ha'
    rw [hq.2, hq'.2, ha.2, ha'.2, hz.2, hp.2]
    refine ⟨τ, hτ, hsrc, hread, hdst, hwrite, ?_, fun z₂ p₂ hz₂ hp₂ => ?_⟩
    · intro z₁ p₁ b b' _ hne hb hb'
      simp only [toRunRel_sym] at hb hb'
      rw [hb.2, hb'.2]
      exact (hframe z₁ p₁ fun hcon => hne ⟨hcon.1, hcon.2⟩).symm
    · simp only [toRunRel_hdP, toRunRel_hdC] at hz₂ hp₂
      rw [hz₂.2, hp₂.2]
      have hcellmap : ∀ (z₁ : Fin (2 * n + 1)) (p₁ : A) (z₂' : Fin (2 * n + 1)) (p₂' : A),
          SuccCellAt M z₁ p₁ z₂' p₂' → SuccCellRel M (toRunRel zero r) z₁ p₁ z₂' p₂' := by
        rintro z₁ p₁ z₂' p₂' (⟨he, hs⟩ | ⟨hc, hmx, hmn⟩)
        · exact Or.inl ⟨he, hs⟩
        · exact Or.inr ⟨succPage_of_covBy hc, hmx, hmn⟩
      rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨hr, hcellmap _ _ _ _ hs⟩
      · exact Or.inr ⟨hr, hcellmap _ _ _ _ hs⟩
  · -- accepting
    intro t q htmax hq
    have hti := hmax t htmax
    simp only [toRunRel_st] at hq
    rw [hq.2, hti]
    exact h.acc (Fin.last n) fun i => Fin.le_last i

/-- **A machine that accepts carries a relational certificate on `Fin m`.** -/
theorem runRel_of_acceptsU (h : M.AcceptsU) :
    ∃ (m : ℕ) (c : RunRel A (Fin m)), RunRelOK M c := by
  obtain ⟨n, zero, r, hr⟩ := runCert_of_acceptsU h
  exact ⟨2 * n + 1, toRunRel zero r, runRelOK_toRunRel hr⟩

/-- **Acceptance on an unbounded tape is a relational certificate on invented
values**: the statement the `∃SO[new]` kernel of the membership proof mirrors
clause by clause. -/
theorem acceptsU_iff_runRel (hb : ∃ b, M.Blank b) :
    M.AcceptsU ↔ ∃ (m : ℕ) (c : RunRel A (Fin m)), RunRelOK M c :=
  ⟨runRel_of_acceptsU, fun ⟨_, _, hc⟩ => acceptsU_of_runRel hb hc⟩

end ToRel

end TMData

/-! ### The statement the kernel mirrors

Everything above, at the problem: what remains for `HALT ∈ RE` is to write
`DescriptiveComplexity.TMData.RunRelOK` and
`DescriptiveComplexity.TMData.WellFormed` as a first-order kernel over the
extended universe, with each quantifier guarded by its sort. -/

section Problem

open FirstOrder Language

/-- **`HALT` is well-formedness together with a relational certificate on
invented values.** The right-hand side is a conjunction of first-order
conditions on the instance and on a block of nine relation variables, which is
exactly what an `∃SO[new]` sentence says. -/
theorem halt_iff_runRel (A : Type) [Language.turing.Structure A] :
    HALT A ↔ (tmData A).WellFormed ∧
      ∃ (m : ℕ) (c : TMData.RunRel A (Fin m)), TMData.RunRelOK (tmData A) c := by
  constructor
  · rintro ⟨hwf, hacc⟩
    exact ⟨hwf, (TMData.acceptsU_iff_runRel hwf.2.2.2.1).mp hacc⟩
  · rintro ⟨hwf, hc⟩
    exact ⟨hwf, (TMData.acceptsU_iff_runRel hwf.2.2.2.1).mpr hc⟩

end Problem

end DescriptiveComplexity
