/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Program
import DescriptiveComplexity.OrderedComposition
import Mathlib.Data.Fintype.Lattice

/-!
# The tape of the unit-propagation machine

The layout half of `HORNSAT ≤ᶠᵒ[≤] DTMAccept`, stage 4 of the machine bridge:
which tagged tuples are positions, in what order, and why there are enough of
them. The program that runs on this tape is in
`DescriptiveComplexity.Problems.Machine.HornHardness`.

## The layout

As for the SAT machine of stage 3: one cell per element of the instance,
bracketed by two markers, followed by filler cells supplying time. The
difference is the **dimension**: this machine does `n` propagation rounds of
one check-and-mark pass per clause, `O(n³)` steps in all, so the interpreted
universe is `HTag × A³` and sixteen filler tags give `16n³` positions.

A cell holds its element together with a mark – `sU x` unmarked, `sM x`
marked – and the marked set is the machine's working copy of the unit
propagation closure `DescriptiveComplexity.Forced`.

## The program's tags

All the machine's tags are declared here, as for stage 3: symbols, states and
transitions get indices above the position tags, which leaves the order of the
positions undisturbed. The states carry up to two elements – the current round
and the current clause – which is what the third dimension of the payload
accommodates.
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### The tags -/

/-- The tags of the unit-propagation machine. Position tags first – their
constructor order is the tape order – then symbols, states and transitions. -/
inductive HTag : Type
  /-- The left marker cell. -/
  | pStart
  /-- The cell of an element: one per element of the instance. -/
  | pCell
  /-- The right marker cell. -/
  | pEnd
  /-- Filler cells, sixteen tags' worth, supplying the time budget. -/
  | pFill (i : Fin 16)
  /-- The left-marker symbol `⊢`. -/
  | sStart
  /-- The right-marker symbol `⊣`. -/
  | sEnd
  /-- The blank symbol. -/
  | sBlank
  /-- The symbol `(x, unmarked)`. -/
  | sU
  /-- The symbol `(x, marked)`. -/
  | sM
  /-- The dispatch state, at the left marker. -/
  | qInit
  /-- Checking the current clause, sweeping right: `f` says every negative
  literal seen so far is marked. Payload: the round and the clause. -/
  | qChk (f : Bool)
  /-- The return sweep of a clause: `m` says the check succeeded, so the
  positive literal is marked in passing. Payload: the round and the clause. -/
  | qMark (m : Bool)
  /-- Verifying the clause of the payload against the final marks, flag `f`,
  sweeping in direction `d`. -/
  | qVer (f d : Bool)
  /-- The accepting state. -/
  | qAcc
  /-- Dispatch: a clause exists, start the first check sweep. -/
  | tInitChk
  /-- Dispatch: no clause at all, accept. -/
  | tInitAcc
  /-- Check sweep: read a cell with mark `m` under flag `f`. -/
  | tChk (m f : Bool)
  /-- Check sweep over: turn round at `⊣` into the return sweep. -/
  | tChkEnd (f : Bool)
  /-- Return sweep: read a cell with mark `m`; if `mk`, mark the positive
  literal of the clause in passing. -/
  | tMark (m mk : Bool)
  /-- Return sweep over, another clause follows in this round. -/
  | tMarkEndNext (mk : Bool)
  /-- Return sweep over, last clause, another round follows. -/
  | tMarkEndRound (mk : Bool)
  /-- Return sweep over, last clause of the last round: verification begins. -/
  | tMarkEndVer (mk : Bool)
  /-- Verification sweep: read a cell with mark `m` under flag `f`, sweeping
  in direction `d`. -/
  | tVer (m f d : Bool)
  /-- Verified: the clause is satisfied and another one follows. -/
  | tVerNext (d : Bool)
  /-- Verified: the last clause is satisfied, and the instance is Horn. -/
  | tVerAcc (d : Bool)
  deriving DecidableEq, Fintype

instance : Nonempty HTag := ⟨HTag.pStart⟩

/-- The position of a tag in the tape order. -/
def hTagIdx : HTag → ℕ
  | .pStart => 0
  | .pCell => 1
  | .pEnd => 2
  | .pFill i => 3 + (i : ℕ)
  | .sStart => 19
  | .sEnd => 20
  | .sBlank => 21
  | .sU => 22
  | .sM => 23
  | .qInit => 24
  | .qChk f => 25 + (if f then 1 else 0)
  | .qMark m => 27 + (if m then 1 else 0)
  | .qVer f d => 29 + (if f then 1 else 0) + (if d then 2 else 0)
  | .qAcc => 33
  | .tInitChk => 34
  | .tInitAcc => 35
  | .tChk m f => 36 + (if m then 1 else 0) + (if f then 2 else 0)
  | .tChkEnd f => 40 + (if f then 1 else 0)
  | .tMark m mk => 42 + (if m then 1 else 0) + (if mk then 2 else 0)
  | .tMarkEndNext mk => 46 + (if mk then 1 else 0)
  | .tMarkEndRound mk => 48 + (if mk then 1 else 0)
  | .tMarkEndVer mk => 50 + (if mk then 1 else 0)
  | .tVer m f d => 52 + (if m then 1 else 0) + (if f then 2 else 0) + (if d then 4 else 0)
  | .tVerNext d => 60 + (if d then 1 else 0)
  | .tVerAcc d => 62 + (if d then 1 else 0)

set_option maxRecDepth 8000 in
theorem hTagIdx_injective : Function.Injective hTagIdx := fun {s t} h =>
  (by decide : ∀ s t : HTag, hTagIdx s = hTagIdx t → s = t) s t h

/-- The tape order on tags. -/
instance : LinearOrder HTag := LinearOrder.lift' hTagIdx hTagIdx_injective

/-! ### The intended positions -/

section Positions

variable {A : Type} [LinearOrder A]

/-- The tuple of minima at dimension three: what markers and constants are
pinned to. -/
def IsMinTup3 (w : Fin 3 → A) : Prop :=
  (∀ a : A, w 0 ≤ a) ∧ (∀ a : A, w 1 ≤ a) ∧ ∀ a : A, w 2 ≤ a

theorem isMinTup3_unique {w w' : Fin 3 → A} (h : IsMinTup3 w) (h' : IsMinTup3 w') : w = w' := by
  funext i
  fin_cases i
  · exact le_antisymm (h.1 _) (h'.1 _)
  · exact le_antisymm (h.2.1 _) (h'.2.1 _)
  · exact le_antisymm (h.2.2 _) (h'.2.2 _)

/-- The tagged tuples that are positions: the markers on the triple of minima,
an element's cell that element with a minimal rest, the fillers unrestricted. -/
def HPosn (p : HTag × (Fin 3 → A)) : Prop :=
  match p.1 with
  | .pStart => IsMinTup3 p.2
  | .pCell => (∀ a : A, p.2 1 ≤ a) ∧ ∀ a : A, p.2 2 ≤ a
  | .pEnd => IsMinTup3 p.2
  | .pFill _ => True
  | _ => False

variable [Finite A] [Nonempty A]

theorem exists_isMinTup3 : ∃ w : Fin 3 → A, IsMinTup3 w := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  exact ⟨fun _ => m, hm, hm, hm⟩

/-- The blank symbol of the machine: pinned to the triple of minima. -/
def HBlank (p : HTag × (Fin 3 → A)) : Prop := p.1 = HTag.sBlank ∧ IsMinTup3 p.2

theorem exists_hBlank : ∃ p : HTag × (Fin 3 → A), HBlank p := by
  obtain ⟨w, hw⟩ := exists_isMinTup3 (A := A)
  exact ⟨(HTag.sBlank, w), rfl, hw⟩

omit [Finite A] [Nonempty A] in
theorem hBlank_unique {p q : HTag × (Fin 3 → A)} (hp : HBlank p) (hq : HBlank q) : p = q :=
  Prod.ext (hp.1.trans hq.1.symm) (isMinTup3_unique hp.2 hq.2)

/-- **The initial tape**: the markers hold their own symbols and the cell of
an element holds that element, unmarked. -/
def HInp (p a : HTag × (Fin 3 → A)) : Prop :=
  (p.1 = HTag.pStart ∧ a.1 = HTag.sStart ∧ IsMinTup3 a.2) ∨
    (p.1 = HTag.pCell ∧ a.1 = HTag.sU ∧ a.2 0 = p.2 0 ∧
      (∀ b : A, a.2 1 ≤ b) ∧ ∀ b : A, a.2 2 ≤ b) ∨
      (p.1 = HTag.pEnd ∧ a.1 = HTag.sEnd ∧ IsMinTup3 a.2)

omit [Finite A] [Nonempty A] in
/-- The initial tape is functional. -/
theorem hInp_functional {p a b : HTag × (Fin 3 → A)} (ha : HInp p a) (hb : HInp p b) :
    a = b := by
  have htup : ∀ u v : Fin 3 → A, u 0 = p.2 0 → (∀ c : A, u 1 ≤ c) → (∀ c : A, u 2 ≤ c) →
      v 0 = p.2 0 → (∀ c : A, v 1 ≤ c) → (∀ c : A, v 2 ≤ c) → u = v := by
    intro u v hu0 hu1 hu2 hv0 hv1 hv2
    funext i
    fin_cases i
    · exact hu0.trans hv0.symm
    · exact le_antisymm (hu1 _) (hv1 _)
    · exact le_antisymm (hu2 _) (hv2 _)
  rcases ha with ⟨hp, hat, haw⟩ | ⟨hp, hat, ha0, ha1, ha2⟩ | ⟨hp, hat, haw⟩ <;>
    rcases hb with ⟨hq, hbt, hbw⟩ | ⟨hq, hbt, hb0, hb1, hb2⟩ | ⟨hq, hbt, hbw⟩ <;>
      first
        | exact Prod.ext (hat.trans hbt.symm) (isMinTup3_unique haw hbw)
        | exact Prod.ext (hat.trans hbt.symm) (htup _ _ ha0 ha1 ha2 hb0 hb1 hb2)
        | (rw [hp] at hq; exact absurd hq (by decide))

/-- There is a position: the left marker. -/
theorem exists_hPosn : ∃ p : HTag × (Fin 3 → A), HPosn p := by
  obtain ⟨w, hw⟩ := exists_isMinTup3 (A := A)
  exact ⟨(HTag.pStart, w), hw⟩

omit [Finite A] [Nonempty A] in
private theorem isLinOrd_of_linearOrder {X : Type} (o : LinearOrder X) : IsLinOrd o.le :=
  ⟨fun a => @le_refl X o.toPreorder a, fun a b c => @le_trans X o.toPreorder a b c,
    fun a b => @le_antisymm X o.toPartialOrder a b, fun a b => @le_total X o a b⟩

omit [Finite A] [Nonempty A] in
/-- **The interpreted order is linear**, from `DescriptiveComplexity.tagTupleOrder` –
no tag-pair case analysis, exactly as for stage 3. -/
theorem isLinOrd_hTagTupleLe :
    IsLinOrd (tagTupleLe (Tag := HTag) (d := 3) (A := A)) := by
  have heq : (tagTupleLe (Tag := HTag) (d := 3) (A := A)) =
      (tagTupleOrder : LinearOrder (HTag × (Fin 3 → A))).le := by
    funext p q
    exact propext (tagTupleLe_iff_le p q)
  rw [heq]
  exact isLinOrd_of_linearOrder _

end Positions

/-! ### The budget -/

/-- **The filler cells alone are enough.** One dispatch step, two sweeps per
round and clause, one sweep per clause of verification: at most
`(2n² + n + 2)(n + 2)` steps for `n` elements, while the sixteen filler tags
contribute `16n³` positions by themselves. -/
theorem horn_budget {n : ℕ} (hn : 1 ≤ n) :
    (2 * n * n + n + 2) * (n + 2) < 16 * n * n * n := by
  nlinarith [hn, Nat.mul_le_mul (Nat.mul_le_mul hn hn) hn]

/-- The tape really has that many positions: the filler tuples alone inject
into the positions. -/
theorem card_le_card_hPosn (A : Type) [LinearOrder A] [Finite A] :
    16 * Nat.card A * Nat.card A * Nat.card A ≤
      Nat.card {p : HTag × (Fin 3 → A) // HPosn p} := by
  have hinj : Function.Injective
      (fun q : Fin 16 × A × A × A => (⟨(HTag.pFill q.1, ![q.2.1, q.2.2.1, q.2.2.2]), trivial⟩ :
        {p : HTag × (Fin 3 → A) // HPosn p})) := by
    rintro ⟨i, a, b, c⟩ ⟨i', a', b', c'⟩ h
    have h' := congrArg Subtype.val h
    obtain ⟨ht, hw⟩ := Prod.mk.injEq .. ▸ h'
    have h0 := congrFun hw 0
    have h1 := congrFun hw 1
    have h2 := congrFun hw 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
    cases ht
    simp_all
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 16),
    Fintype.card_fin, ← mul_assoc, ← mul_assoc] at h

end DescriptiveComplexity
