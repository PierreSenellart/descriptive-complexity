/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpKit
import DescriptiveComplexity.EqPattern

/-!
# What a rule owes the interpretation, and the algebra that discharges it

A hardness reduction into `DescriptiveComplexity.DWideAcceptSpace` emits a
machine, and an interpretation has to *write that machine down*: one formula per
relation symbol and tag tuple, read at the coordinates a transition's payload
occupies. So each rule owes, of its guard and of the two things it computes,
that a formula defines them — **the same formula at every instance**, since an
interpretation carries one.

## The obligation is quantified over the structure

The quantifier therefore sits outside the existential, and what it ranges over
is `DescriptiveComplexity.Pfp.Env`: a finite nonempty linearly ordered structure
of the source vocabulary together with the two designated elements the reduction
may name — the order's least and greatest. Bundling them into one record is what
keeps the algebra readable: every statement below has a single extra binder `e`,
and instance resolution finds the order, the finiteness and the structure inside
it.

## Guards are formulas; writes are sources

A guard may ask anything first-order of its data, and it has to: the program
evaluates a *logic*, so a guard eventually compares two control slots in the
**order**, or asks a **relation of the source vocabulary** of them — neither of
which is a function of the equality pattern of the data. So
`DescriptiveComplexity.Pfp.UGDefinable` carries a formula over the payload
coordinates, with `DescriptiveComplexity.patSetF` still available as one way of
building it.

A *write*, by contrast, never asks anything: every value the program stores is a
copy of one of its slots, one of the two designated elements, or the **next**
element after a slot (which is what advancing a loop variable needs). So
`DescriptiveComplexity.Pfp.USlotDefinable` is a formula for the *graph* of the
value, and `DescriptiveComplexity.SlotVal` builds all three cases.

## The three obligations

A rule is written with its pointer and its tracks apart, so the obligations are
carried in that shape: `UGDefinable` for the guard, `UStDefinable` for the
pointer it leaves, `UTrDefinable` for the tracks it writes — with
`DescriptiveComplexity.Pfp.URuleDefinable` bundling the three together with the
staticness of its two phases and its direction. That is what travels through the
program's tower, one statement per rule, composed site by site, with a kit's
abstract parameters (`Match`, `setFlag`, …) contributing hypotheses of the same
shape.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### Which coordinate a slot occupies -/

section Slots

variable {Q W : Type} [Fintype Q] [Fintype W]

/-- **A relation of the source vocabulary, in the ordered expansion**: named,
because a raw `Sum.inl` is not recognised at the transparency `rw` matches
at. -/
abbrev baseSym {L : Language.{0, 0}} {m : ℕ} (r : L.Relations m) :
    (L.sum Language.order).Relations m := Sum.inl r

/-- **The coordinate of a slot** in a rule's payload. -/
@[reducible] noncomputable def slotIx (d : Q ⊕ W) : Fin (Fintype.card (Q ⊕ W)) :=
  Fintype.equivFin (Q ⊕ W) d

variable {A : Type}

theorem unslot_eq_slotIx (w : Fin (Fintype.card (Q ⊕ W)) → A) (d : Q ⊕ W) :
    unslot w d = w (slotIx d) := rfl

/-- **The two halves of a rule's data, put back together**, is the data. -/
theorem elim_unslot (w : Fin (Fintype.card (Q ⊕ W)) → A) (d : Q ⊕ W) :
    Sum.elim (fun q => unslot w (Sum.inl q)) (fun s => unslot w (Sum.inr s)) d =
      w (slotIx d) := by
  cases d <;> rfl

end Slots

/-! ### The structures a reduction's rules are read at -/

/-- **An environment**: a finite nonempty linearly ordered structure of the
source vocabulary, with the two elements a reduction may designate – the
order's least and greatest, the only ones an interpretation can name. The
program's rules are functions of one of these, and their definability is a
statement about *all* of them, which is what an interpretation needs. -/
structure Env (L : Language.{0, 0}) : Type 1 where
  /-- The universe. -/
  α : Type
  /-- Its order. -/
  [ord : LinearOrder α]
  /-- Which is finite. -/
  [fin : Finite α]
  /-- And nonempty. -/
  [ne : Nonempty α]
  /-- And carries the source structure. -/
  [str : L.Structure α]
  /-- The element a clear track holds. -/
  zero : α
  /-- The element a set track holds. -/
  one : α
  /-- The clear element is the order's least. -/
  hbot : IsBot zero
  /-- The set element is its greatest. -/
  htop : IsTop one
  /-- The two differ. -/
  hzo : zero ≠ one

attribute [instance] Env.ord Env.fin Env.ne Env.str

section EnvLemmas

variable {L : Language.{0, 0}} (e : Env L)

/-- In a linear order, being a minimum is being *the* designated minimum. -/
theorem Env.isBot_iff (a : e.α) : IsBot a ↔ a = e.zero :=
  ⟨fun h => le_antisymm (h e.zero) (e.hbot a), fun h => h ▸ e.hbot⟩

/-- And dually. -/
theorem Env.isTop_iff (a : e.α) : IsTop a ↔ a = e.one :=
  ⟨fun h => le_antisymm (e.htop a) (h e.one), fun h => h ▸ e.htop⟩

end EnvLemmas

/-! ### The three obligations, uniformly -/

section Uniform

variable {L : Language.{0, 0}} {Q W P : Type} [Fintype Q] [Fintype W]

/-- **A guard is definable**: one formula over the payload coordinates decides
it at every environment. -/
def UGDefinable (N : ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop) : Prop :=
  ∃ φ : (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W))),
    ∀ (e : Env L) (w : Fin (Fintype.card (Q ⊕ W)) → e.α),
      N e (fun q => unslot w (Sum.inl q)) (fun s => unslot w (Sum.inr s)) ↔ φ.Realize w

/-- **A written value is definable**: one formula over the payload coordinates
and one more variable defines its graph. -/
def USlotDefinable (V : ∀ e : Env L, (Q → e.α) → (W → e.α) → e.α) : Prop :=
  ∃ ψ : (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W)) ⊕ Unit),
    ∀ (e : Env L) (w : Fin (Fintype.card (Q ⊕ W)) → e.α) (y : e.α),
      (y = V e (fun q => unslot w (Sum.inl q)) fun s => unslot w (Sum.inr s)) ↔
        ψ.Realize (Sum.elim w fun _ => y)

/-- **A pointer a rule leaves is definable**: one value per control slot. -/
def UStDefinable (F : ∀ e : Env L, (Q → e.α) → (W → e.α) → Q → e.α) : Prop :=
  ∀ q : Q, USlotDefinable fun e f g => F e f g q

/-- **And so are the tracks it writes**: one value per track slot. -/
def UTrDefinable (F : ∀ e : Env L, (Q → e.α) → (W → e.α) → W → e.α) : Prop :=
  ∀ s : W, USlotDefinable fun e f g => F e f g s

/-- **A rule is definable**: its two phases and its direction do not depend on
the instance at all – they are decided when the formula is built – its guard is
defined by a formula, and the pointer it leaves and the tracks it writes are
named slot by slot. This is what travels through the program's tower. -/
structure URuleDefinable (rl : ∀ e : Env L, Rule e.α Q W P) : Prop where
  /-- The phase it fires from is the same at every instance. -/
  srcPh : ∃ p : P, ∀ e : Env L, (rl e).srcPh = p
  /-- And so is the phase it moves to. -/
  dstPh : ∃ p : P, ∀ e : Env L, (rl e).dstPh = p
  /-- And so is its direction. -/
  right : ∃ b : Bool, ∀ e : Env L, ((rl e).moveRight ↔ b = true)
  /-- The guard is defined by a formula. -/
  guard : UGDefinable fun e => (rl e).guard
  /-- The pointer it leaves is definable slot by slot. -/
  dst : UStDefinable fun e => (rl e).dstSt
  /-- And so are the tracks it writes. -/
  wr : UTrDefinable fun e => (rl e).wr

omit [Fintype Q] [Fintype W] in
/-- **The static half of a rule, when it is written down as a constant**: the
shape every kit's rule has, its phases and its direction being literals. -/
theorem uStatic_rfl {rl : ∀ e : Env L, Rule e.α Q W P} {p p' : P} {b : Bool}
    (hs : ∀ e : Env L, (rl e).srcPh = p) (hd : ∀ e : Env L, (rl e).dstPh = p')
    (hr : ∀ e : Env L, ((rl e).moveRight ↔ b = true)) :
    (∃ p : P, ∀ e : Env L, (rl e).srcPh = p) ∧
      (∃ p : P, ∀ e : Env L, (rl e).dstPh = p) ∧
      ∃ b : Bool, ∀ e : Env L, ((rl e).moveRight ↔ b = true) :=
  ⟨⟨p, hs⟩, ⟨p', hd⟩, ⟨b, hr⟩⟩

/-- **A whole site's rules are definable.** -/
def URulesDefinable {S : Type} {Sh : S → Type}
    (rules : ∀ (e : Env L) (i : S), Sh i → Rule e.α Q W P) : Prop :=
  ∀ (i : S) (ρ : Sh i), URuleDefinable fun e => rules e i ρ

/-! ### The atoms of a guard

A slot holds one of the two designated elements; two slots hold the same
element; one slot is at most another; and a relation of the source vocabulary
holds of a tuple of slots. The last two are what an equality pattern cannot
say, and what a program that evaluates a logic needs. -/

theorem uGDefinable_slotOne (d : Q ⊕ W) :
    UGDefinable (L := L) fun e f g => Sum.elim f g d = e.one :=
  ⟨topF (slotIx d), fun e w => by
    simp only [elim_unslot, realize_topF]
    exact (e.isTop_iff _).symm⟩

theorem uGDefinable_slotZero (d : Q ⊕ W) :
    UGDefinable (L := L) fun e f g => Sum.elim f g d = e.zero :=
  ⟨botF (slotIx d), fun e w => by
    simp only [elim_unslot, realize_botF]
    exact (e.isBot_iff _).symm⟩

theorem uGDefinable_slotEq (d d' : Q ⊕ W) :
    UGDefinable (L := L) fun _ f g => Sum.elim f g d = Sum.elim f g d' :=
  ⟨Term.equal (Term.var (slotIx d)) (Term.var (slotIx d')), fun _ _ => by
    simp only [elim_unslot, Formula.realize_equal, Term.realize_var]⟩

/-- **One slot is at most another.** -/
theorem uGDefinable_slotLe (d d' : Q ⊕ W) :
    UGDefinable (L := L) fun _ f g => Sum.elim f g d ≤ Sum.elim f g d' :=
  ⟨Relations.formula₂ leSymb (Term.var (slotIx d)) (Term.var (slotIx d')),
    fun _ _ => by
      simp only [elim_unslot, Formula.realize_rel₂, Term.realize_var,
        relMap_leSymb, Matrix.cons_val_zero, Matrix.cons_val_one]⟩

/-- **A relation of the source vocabulary, of a tuple of slots**: the one thing
a guard asks of the instance itself, and the reason a guard is a formula rather
than a reading of the equality pattern. -/
theorem uGDefinable_slotRel {m : ℕ} (r : L.Relations m) (ts : Fin m → Q ⊕ W) :
    UGDefinable (L := L) fun e f g =>
      @RelMap L e.α _ m r fun j => Sum.elim f g (ts j) :=
  ⟨Relations.formula (baseSym r) fun j => Term.var (slotIx (ts j)), fun _ _ => by
    rw [Formula.realize_rel]
    simp only [elim_unslot, baseSym, relMap_sumInl, Term.realize_var]⟩

theorem uGDefinable_ctlOne (q : Q) :
    UGDefinable (L := L) (W := W) fun e f _ => f q = e.one :=
  uGDefinable_slotOne (Sum.inl q)

theorem uGDefinable_ctlZero (q : Q) :
    UGDefinable (L := L) (W := W) fun e f _ => f q = e.zero :=
  uGDefinable_slotZero (Sum.inl q)

theorem uGDefinable_trkOne (s : W) :
    UGDefinable (L := L) (Q := Q) fun e _ g => g s = e.one :=
  uGDefinable_slotOne (Sum.inr s)

theorem uGDefinable_trkZero (s : W) :
    UGDefinable (L := L) (Q := Q) fun e _ g => g s = e.zero :=
  uGDefinable_slotZero (Sum.inr s)

theorem uGDefinable_ctlEq (q q' : Q) :
    UGDefinable (L := L) (W := W) fun _ f _ => f q = f q' :=
  uGDefinable_slotEq (W := W) (Sum.inl q) (Sum.inl q')

theorem uGDefinable_trkEq (s s' : W) :
    UGDefinable (L := L) (Q := Q) fun _ _ g => g s = g s' :=
  uGDefinable_slotEq (Q := Q) (Sum.inr s) (Sum.inr s')

theorem uGDefinable_mixEq (q : Q) (s : W) :
    UGDefinable (L := L) fun _ f g => f q = g s :=
  uGDefinable_slotEq (Sum.inl q) (Sum.inr s)

theorem uGDefinable_ctlLe (q q' : Q) :
    UGDefinable (L := L) (W := W) fun _ f _ => f q ≤ f q' :=
  uGDefinable_slotLe (W := W) (Sum.inl q) (Sum.inl q')

theorem uGDefinable_ctlRel {m : ℕ} (r : L.Relations m) (ts : Fin m → Q) :
    UGDefinable (L := L) (W := W) fun e f _ =>
      @RelMap L e.α _ m r fun j => f (ts j) :=
  uGDefinable_slotRel (W := W) r fun j => Sum.inl (ts j)

open Classical in
/-- **A condition of the kit, not of the data**: decided when the formula is
built, so any `Prop` will do – the two ends among them. -/
theorem uGDefinable_const (p : Prop) :
    UGDefinable (L := L) (Q := Q) (W := W) fun _ _ _ => p := by
  by_cases hp : p
  · exact ⟨⊤, fun _ _ => iff_of_true hp (by simp)⟩
  · exact ⟨⊥, fun _ _ => iff_of_false hp (by simp)⟩

theorem uGDefinable_true :
    UGDefinable (L := L) (Q := Q) (W := W) fun _ _ _ => True :=
  uGDefinable_const True

theorem uGDefinable_false :
    UGDefinable (L := L) (Q := Q) (W := W) fun _ _ _ => False :=
  uGDefinable_const False

/-! ### And their connectives -/

variable {N N' : ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}

/-- A guard stated one way is a guard stated any equivalent way. -/
theorem UGDefinable.congr (h : UGDefinable N) (he : ∀ e f g, N' e f g ↔ N e f g) :
    UGDefinable N' :=
  h.imp fun _ hφ e w => (he _ _ _).trans (hφ e w)

theorem UGDefinable.and (h : UGDefinable N) (h' : UGDefinable N') :
    UGDefinable fun e f g => N e f g ∧ N' e f g := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨φ', hφ'⟩ := h'
  exact ⟨φ ⊓ φ', fun e w => by
    rw [Formula.realize_inf]
    exact and_congr (hφ e w) (hφ' e w)⟩

theorem UGDefinable.or (h : UGDefinable N) (h' : UGDefinable N') :
    UGDefinable fun e f g => N e f g ∨ N' e f g := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨φ', hφ'⟩ := h'
  exact ⟨φ ⊔ φ', fun e w => by
    rw [Formula.realize_sup]
    exact or_congr (hφ e w) (hφ' e w)⟩

theorem UGDefinable.not (h : UGDefinable N) :
    UGDefinable fun e f g => ¬N e f g := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨∼φ, fun e w => by
    rw [Formula.realize_not]
    exact not_congr (hφ e w)⟩

open Classical in
theorem UGDefinable.imp (h : UGDefinable N) (h' : UGDefinable N') :
    UGDefinable fun e f g => N e f g → N' e f g :=
  (h.not.or h').congr fun _ _ _ => imp_iff_not_or

open Classical in
theorem UGDefinable.iff (h : UGDefinable N) (h' : UGDefinable N') :
    UGDefinable fun e f g => (N e f g ↔ N' e f g) :=
  ((h.imp h').and (h'.imp h)).congr fun _ _ _ => iff_iff_implies_and_implies

open Classical in
/-- A conjunction over any finite index type – the shape a one-hot clause or a
`Match` over a block of slots has. -/
theorem uGDefinable_forall {ι : Type*} [Finite ι]
    {R : ι → ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    (h : ∀ i, UGDefinable (R i)) :
    UGDefinable fun e f g => ∀ i, R i e f g := by
  letI := Fintype.ofFinite ι
  choose φ hφ using h
  refine ⟨listInf ((Finset.univ : Finset ι).toList.map φ), fun e w => ?_⟩
  rw [realize_listInf]
  constructor
  · rintro hall ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (hφ i e w).mp (hall i)
  · intro hall i
    exact (hφ i e w).mpr (hall _ (List.mem_map.mpr
      ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩))

open Classical in
/-- And a disjunction over any finite index type. -/
theorem uGDefinable_exists {ι : Type*} [Finite ι]
    {R : ι → ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    (h : ∀ i, UGDefinable (R i)) :
    UGDefinable fun e f g => ∃ i, R i e f g := by
  letI := Fintype.ofFinite ι
  choose φ hφ using h
  refine ⟨listSup ((Finset.univ : Finset ι).toList.map φ), fun e w => ?_⟩
  rw [realize_listSup]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨φ i, List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩,
      (hφ i e w).mp hi⟩
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact ⟨i, (hφ i e w).mpr hr⟩

/-- A condition decided when the formula is built – by the kit, not by the
data. -/
theorem UGDefinable.ite {p : Prop} [Decidable p] (h : UGDefinable N)
    (h' : UGDefinable N') :
    UGDefinable fun e f g => if p then N e f g else N' e f g := by
  by_cases hp : p
  · exact h.congr fun _ _ _ => iff_of_eq (if_pos hp)
  · exact h'.congr fun _ _ _ => iff_of_eq (if_neg hp)

/-! ### The atoms of a written value -/

/-- The variable a written value is named at. -/
private abbrev outVar : Fin (Fintype.card (Q ⊕ W)) ⊕ Unit := Sum.inr ()

/-- A guard's formula, read in the context a written value is named in. -/
private def liftG (φ : (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W)))) :
    (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W)) ⊕ Unit) :=
  Formula.relabel Sum.inl φ

private theorem realize_liftG
    {φ : (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W)))} {e : Env L}
    {w : Fin (Fintype.card (Q ⊕ W)) → e.α} {y : e.α} :
    (liftG (Q := Q) (W := W) φ).Realize (Sum.elim w fun _ => y) ↔ φ.Realize w := by
  rw [liftG, Formula.realize_relabel]
  exact Iff.rfl

/-- **A source names a written value**: the three cases of
`DescriptiveComplexity.SlotVal`, read at the payload coordinates. -/
theorem uSlotDefinable_of_slotVal (sv : SlotVal (Fintype.card (Q ⊕ W)))
    {V : ∀ e : Env L, (Q → e.α) → (W → e.α) → e.α}
    (hV : ∀ (e : Env L) (w : Fin (Fintype.card (Q ⊕ W)) → e.α),
      V e (fun q => unslot w (Sum.inl q)) (fun s => unslot w (Sum.inr s)) =
        sv.eval e.zero e.one w) :
    USlotDefinable V := by
  refine ⟨slotValF (fun k => Sum.inl k) (outVar (Q := Q) (W := W)) sv,
    fun e w y => ?_⟩
  rw [realize_slotValF e.hbot e.htop, hV e w]
  exact Iff.rfl

theorem uSlotDefinable_zero :
    USlotDefinable (L := L) (Q := Q) (W := W) fun e _ _ => e.zero :=
  uSlotDefinable_of_slotVal .bot fun _ _ => rfl

theorem uSlotDefinable_one :
    USlotDefinable (L := L) (Q := Q) (W := W) fun e _ _ => e.one :=
  uSlotDefinable_of_slotVal .top fun _ _ => rfl

theorem uSlotDefinable_ctl (q : Q) :
    USlotDefinable (L := L) (W := W) fun _ f _ => f q :=
  uSlotDefinable_of_slotVal (.copy (slotIx (Sum.inl q))) fun _ _ => rfl

theorem uSlotDefinable_trk (s : W) :
    USlotDefinable (L := L) (Q := Q) fun _ _ g => g s :=
  uSlotDefinable_of_slotVal (.copy (slotIx (Sum.inr s))) fun _ _ => rfl

/-- **The next element after a control slot** – what advancing a loop variable
writes, and the only source that reads the order. -/
theorem uSlotDefinable_ctlSucc (q : Q) :
    USlotDefinable (L := L) (W := W) fun _ f _ => ordSucc (f q) :=
  uSlotDefinable_of_slotVal (.succ (slotIx (Sum.inl q))) fun _ _ => rfl

theorem uSlotDefinable_trkSucc (s : W) :
    USlotDefinable (L := L) (Q := Q) fun _ _ g => ordSucc (g s) :=
  uSlotDefinable_of_slotVal (.succ (slotIx (Sum.inr s))) fun _ _ => rfl

variable {V V' : ∀ e : Env L, (Q → e.α) → (W → e.α) → e.α}

theorem USlotDefinable.congr (h : USlotDefinable V)
    (he : ∀ e f g, V' e f g = V e f g) : USlotDefinable V' :=
  h.imp fun _ hψ e w y => by rw [he]; exact hψ e w y

/-- **A bit is a written value**: the two designated elements, chosen by a
guard – so every `DescriptiveComplexity.Pfp.bitVal` a rule writes is definable
as soon as the question behind it is. -/
theorem uSlotDefinable_bitVal (h : UGDefinable N) :
    USlotDefinable fun e f g => bitVal e.zero e.one (N e f g) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(liftG φ ⊓ topF (outVar (Q := Q) (W := W))) ⊔
    (∼(liftG φ) ⊓ botF (outVar (Q := Q) (W := W))), fun e w y => ?_⟩
  rw [Formula.realize_sup, Formula.realize_inf, Formula.realize_inf,
    Formula.realize_not, realize_liftG, realize_topF, realize_botF,
    e.isTop_iff, e.isBot_iff]
  change (y = bitVal e.zero e.one
      (N e (fun q => unslot w (Sum.inl q)) fun s => unslot w (Sum.inr s))) ↔
    (φ.Realize w ∧ y = e.one) ∨ (¬φ.Realize w ∧ y = e.zero)
  by_cases hN : N e (fun q => unslot w (Sum.inl q)) fun s => unslot w (Sum.inr s)
  · rw [bitVal_pos hN]
    exact ⟨fun hy => Or.inl ⟨(hφ e w).mp hN, hy⟩,
      fun hc => hc.elim (fun h1 => h1.2) fun h2 => absurd ((hφ e w).mp hN) h2.1⟩
  · rw [bitVal_neg hN]
    exact ⟨fun hy => Or.inr ⟨fun hc => hN ((hφ e w).mpr hc), hy⟩,
      fun hc => hc.elim (fun h1 => absurd ((hφ e w).mpr h1.1) hN) fun h2 => h2.2⟩

/-- **A value chosen by a condition of the kit** – not of the data – is
definable when both branches are. -/
theorem USlotDefinable.ite {p : Prop} [Decidable p] (h : USlotDefinable V)
    (h' : USlotDefinable V') :
    USlotDefinable fun e f g => if p then V e f g else V' e f g := by
  by_cases hp : p
  · exact h.congr fun _ _ _ => if_pos hp
  · exact h'.congr fun _ _ _ => if_neg hp

open Classical in
/-- **A value chosen by definable cases**: finitely many conditions, each
definable, at most one of which is asked to hold, with a default. This is what
a write depending on *which* coordinate of a tuple rolled over needs. -/
theorem uSlotDefinable_cases {ι : Type*} [Finite ι]
    {R : ι → ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    {U : ι → ∀ e : Env L, (Q → e.α) → (W → e.α) → e.α}
    (hR : ∀ i, UGDefinable (R i)) (hU : ∀ i, USlotDefinable (U i))
    (h₀ : USlotDefinable V')
    (hpos : ∀ e f g i, R i e f g → V e f g = U i e f g)
    (hneg : ∀ e f g, (∀ i, ¬R i e f g) → V e f g = V' e f g) :
    USlotDefinable V := by
  letI := Fintype.ofFinite ι
  choose φ hφ using hR
  choose ψ hψ using hU
  obtain ⟨ψ₀, hψ₀⟩ := h₀
  refine ⟨listSup ((Finset.univ : Finset ι).toList.map fun i =>
      liftG (φ i) ⊓ ψ i) ⊔
    (listInf ((Finset.univ : Finset ι).toList.map fun i =>
      ∼(liftG (φ i))) ⊓ ψ₀), fun e w y => ?_⟩
  rw [Formula.realize_sup, Formula.realize_inf, realize_listSup, realize_listInf]
  constructor
  · intro hy
    by_cases hex : ∃ i, R i e (fun q => unslot w (Sum.inl q))
        fun s => unslot w (Sum.inr s)
    · obtain ⟨i, hi⟩ := hex
      refine Or.inl ⟨_, List.mem_map.mpr
        ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩, ?_⟩
      rw [Formula.realize_inf, realize_liftG]
      exact ⟨(hφ i e w).mp hi, (hψ i e w y).mp (hy.trans (hpos _ _ _ i hi))⟩
    · push Not at hex
      refine Or.inr ⟨fun χ hχ => ?_, (hψ₀ e w y).mp (hy.trans (hneg _ _ _ hex))⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hχ
      rw [Formula.realize_not, realize_liftG]
      exact fun hc => hex i ((hφ i e w).mpr hc)
  · rintro (⟨χ, hχ, hr⟩ | ⟨hall, h0⟩)
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hχ
      rw [Formula.realize_inf, realize_liftG] at hr
      exact ((hψ i e w y).mpr hr.2).trans (hpos _ _ _ i ((hφ i e w).mpr hr.1)).symm
    · refine ((hψ₀ e w y).mpr h0).trans (hneg _ _ _ fun i hc => ?_).symm
      have hm := hall _ (List.mem_map.mpr
        ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩)
      rw [Formula.realize_not, realize_liftG] at hm
      exact hm ((hφ i e w).mp hc)

/-! ### Values a slot may be compared with -/

/-- **A readable value**: one a slot may be compared with. Every written value
is one, the comparison being the graph formula read at that slot. -/
def UReadable (V : ∀ e : Env L, (Q → e.α) → (W → e.α) → e.α) : Prop :=
  ∀ s : W, UGDefinable fun e f g => g s = V e f g

/-- **Every written value is readable.** -/
theorem USlotDefinable.readable (h : USlotDefinable V) : UReadable V := by
  obtain ⟨ψ, hψ⟩ := h
  intro s
  refine ⟨ψ.relabel (Sum.elim id fun _ => slotIx (Sum.inr s)), fun e w => ?_⟩
  rw [Formula.realize_relabel]
  refine (hψ e w (w (slotIx (Sum.inr s)))).trans (iff_of_eq (congrArg _ (funext ?_)))
  rintro (k | ⟨⟩) <;> rfl

theorem uReadable_zero :
    UReadable (L := L) (Q := Q) (W := W) fun e _ _ => e.zero :=
  fun s => uGDefinable_trkZero s

theorem uReadable_one :
    UReadable (L := L) (Q := Q) (W := W) fun e _ _ => e.one :=
  fun s => uGDefinable_trkOne s

theorem uReadable_ctl (q : Q) :
    UReadable (L := L) (W := W) fun _ f _ => f q :=
  fun s => (uGDefinable_mixEq (L := L) q s).congr fun _ _ _ => eq_comm

theorem uReadable_trk (t : W) :
    UReadable (L := L) (Q := Q) fun _ _ g => g t :=
  fun s => uGDefinable_trkEq s t

theorem UReadable.congr (h : UReadable V) (he : ∀ e f g, V' e f g = V e f g) :
    UReadable V' :=
  fun s => (h s).congr fun e f g => by rw [he]

/-- A value chosen by a condition of the kit, not of the data. -/
theorem UReadable.ite {p : Prop} [Decidable p] (h : UReadable V)
    (h' : UReadable V') :
    UReadable fun e f g => if p then V e f g else V' e f g := by
  by_cases hp : p
  · exact h.congr fun _ _ _ => if_pos hp
  · exact h'.congr fun _ _ _ => if_neg hp

/-! ### From slots to payloads -/

theorem uStDefinable_id :
    UStDefinable (L := L) (Q := Q) (W := W) fun _ f _ => f :=
  fun q => uSlotDefinable_ctl q

theorem uTrDefinable_id :
    UTrDefinable (L := L) (Q := Q) (W := W) fun _ _ g => g :=
  fun s => uSlotDefinable_trk s

variable {F F' : ∀ e : Env L, (Q → e.α) → (W → e.α) → Q → e.α}

theorem UStDefinable.congr (h : UStDefinable F)
    (he : ∀ e f g q, F' e f g q = F e f g q) : UStDefinable F' :=
  fun q => (h q).congr fun e f g => he e f g q

variable {G G' : ∀ e : Env L, (Q → e.α) → (W → e.α) → W → e.α}

theorem UTrDefinable.congr (h : UTrDefinable G)
    (he : ∀ e f g s, G' e f g s = G e f g s) : UTrDefinable G' :=
  fun s => (h s).congr fun e f g => he e f g s

/-- **Updating one control slot**: every other slot is what it was, and the
choice between the two cases is made per slot, when the formula is built. -/
theorem UStDefinable.update [DecidableEq Q] (h : UStDefinable F) (q₀ : Q)
    (hV : USlotDefinable V) :
    UStDefinable fun e f g => Function.update (F e f g) q₀ (V e f g) := by
  intro q
  by_cases hq : q = q₀
  · subst hq
    exact hV.congr fun _ _ _ => Function.update_self _ _ _
  · exact (h q).congr fun _ _ _ => Function.update_of_ne hq _ _

/-- **Updating one track slot.** -/
theorem UTrDefinable.update [DecidableEq W] (h : UTrDefinable G) (s₀ : W)
    (hV : USlotDefinable V) :
    UTrDefinable fun e f g => Function.update (G e f g) s₀ (V e f g) := by
  intro s
  by_cases hs : s = s₀
  · subst hs
    exact hV.congr fun _ _ _ => Function.update_self _ _ _
  · exact (h s).congr fun _ _ _ => Function.update_of_ne hs _ _

/-- **A pointer written by cases**, the cases being decided by the kit. -/
theorem UStDefinable.ite {p : Prop} [Decidable p] (h : UStDefinable F)
    (h' : UStDefinable F') :
    UStDefinable fun e f g => if p then F e f g else F' e f g := by
  by_cases hp : p
  · exact h.congr fun _ _ _ _ => by rw [if_pos hp]
  · exact h'.congr fun _ _ _ _ => by rw [if_neg hp]

/-! ### The payload statements the interpretation reads -/

/-- **A payload transformation is definable**: one formula over the input and
the output coordinates defines its graph. -/
def UPayloadDefinable
    (F : ∀ e : Env L, (Fin (Fintype.card (Q ⊕ W)) → e.α) →
      Fin (Fintype.card (Q ⊕ W)) → e.α) : Prop :=
  ∃ χ : (L.sum Language.order).Formula
      (Fin (Fintype.card (Q ⊕ W)) ⊕ Fin (Fintype.card (Q ⊕ W))),
    ∀ (e : Env L) (w y : Fin (Fintype.card (Q ⊕ W)) → e.α),
      (y = F e w) ↔ χ.Realize (Sum.elim w y)

open Classical in
/-- **A payload is definable when each of its coordinates is**, the coordinate
formulas being conjoined at the output variables they name. -/
theorem uPayloadDefinable_of_slots
    {F : ∀ e : Env L, (Fin (Fintype.card (Q ⊕ W)) → e.α) →
      Fin (Fintype.card (Q ⊕ W)) → e.α}
    {V : ∀ (_k : Fin (Fintype.card (Q ⊕ W))) (e : Env L),
      (Q → e.α) → (W → e.α) → e.α}
    (hV : ∀ k, USlotDefinable (L := L) (V k))
    (hF : ∀ (e : Env L) (w : Fin (Fintype.card (Q ⊕ W)) → e.α)
      (k : Fin (Fintype.card (Q ⊕ W))),
      F e w k = V k e (fun q => unslot w (Sum.inl q)) fun s => unslot w (Sum.inr s)) :
    UPayloadDefinable F := by
  choose ψ hψ using hV
  refine ⟨listInf ((List.finRange (Fintype.card (Q ⊕ W))).map fun k =>
    Formula.relabel (Sum.elim Sum.inl fun _ => Sum.inr k) (ψ k)), fun e w y => ?_⟩
  have hkey : ∀ k : Fin (Fintype.card (Q ⊕ W)),
      (Formula.relabel (Sum.elim Sum.inl fun _ => Sum.inr k) (ψ k)).Realize
          (Sum.elim w y) ↔ y k = F e w k := by
    intro k
    rw [Formula.realize_relabel, hF e w k]
    refine Iff.trans (iff_of_eq (congrArg _ (funext fun j => ?_))) (hψ k e w (y k)).symm
    rcases j with (j | ⟨⟩) <;> rfl
  rw [realize_listInf, funext_iff]
  constructor
  · intro hall χ hχ
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hχ
    exact (hkey k).mpr (hall k)
  · intro hall k
    exact (hkey k).mp (hall _ (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))

open Classical in
/-- **A definable pointer is a definable destination payload.** The control
slots are what the rule computes and the track slots are cleared. -/
theorem uPayloadDefinable_stPl (h : UStDefinable F) :
    UPayloadDefinable fun e (w : Fin (Fintype.card (Q ⊕ W)) → e.α) =>
      stPl (W := W) e.zero (F e (fun q => unslot w (Sum.inl q))
        fun s => unslot w (Sum.inr s)) := by
  refine uPayloadDefinable_of_slots
    (V := fun k e f g => match (Fintype.equivFin (Q ⊕ W)).symm k with
      | Sum.inl q => F e f g q
      | Sum.inr _ => e.zero)
    (fun k => ?_) fun e w k => ?_
  · match hk : (Fintype.equivFin (Q ⊕ W)).symm k with
    | Sum.inl q => exact (h q).congr fun _ _ _ => rfl
    | Sum.inr s =>
      exact (uSlotDefinable_zero (L := L) (Q := Q) (W := W)).congr fun _ _ _ => rfl
  · change stVec (W := W) e.zero (F e _ _) ((Fintype.equivFin (Q ⊕ W)).symm k) = _
    match hk : (Fintype.equivFin (Q ⊕ W)).symm k with
    | Sum.inl q => rw [stVec_inl]
    | Sum.inr s => rfl

open Classical in
/-- **A definable track family is a definable written payload.** -/
theorem uPayloadDefinable_syPl (h : UTrDefinable G) :
    UPayloadDefinable fun e (w : Fin (Fintype.card (Q ⊕ W)) → e.α) =>
      syPl (Q := Q) e.zero (G e (fun q => unslot w (Sum.inl q))
        fun s => unslot w (Sum.inr s)) := by
  refine uPayloadDefinable_of_slots
    (V := fun k e f g => match (Fintype.equivFin (Q ⊕ W)).symm k with
      | Sum.inl _ => e.zero
      | Sum.inr s => G e f g s)
    (fun k => ?_) fun e w k => ?_
  · match hk : (Fintype.equivFin (Q ⊕ W)).symm k with
    | Sum.inl q =>
      exact (uSlotDefinable_zero (L := L) (Q := Q) (W := W)).congr fun _ _ _ => rfl
    | Sum.inr s => exact (h s).congr fun _ _ _ => rfl
  · change syVec (Q := Q) e.zero (G e _ _) ((Fintype.equivFin (Q ⊕ W)).symm k) = _
    match hk : (Fintype.equivFin (Q ⊕ W)).symm k with
    | Sum.inl q => rfl
    | Sum.inr s => rw [syVec_inr]

/-! ### The direction, written as a literal -/

omit [Fintype Q] [Fintype W] in
/-- A rule that always moves right. -/
theorem uRight_of_true {rl : ∀ e : Env L, Rule e.α Q W P}
    (h : ∀ e : Env L, (rl e).moveRight) :
    ∃ b : Bool, ∀ e : Env L, ((rl e).moveRight ↔ b = true) :=
  ⟨true, fun e => iff_of_true (h e) rfl⟩

omit [Fintype Q] [Fintype W] in
/-- And one that always moves left. -/
theorem uRight_of_false {rl : ∀ e : Env L, Rule e.α Q W P}
    (h : ∀ e : Env L, ¬(rl e).moveRight) :
    ∃ b : Bool, ∀ e : Env L, ((rl e).moveRight ↔ b = true) :=
  ⟨false, fun e => iff_of_false (h e) Bool.false_ne_true⟩

/-! ### The shape of most of the program's rules -/

/-- **A guard, with the pointer and the tracks riding along unchanged.** -/
theorem uRuleDefinable_of_keep {rl : ∀ e : Env L, Rule e.α Q W P}
    (hst : (∃ p : P, ∀ e : Env L, (rl e).srcPh = p) ∧
      (∃ p : P, ∀ e : Env L, (rl e).dstPh = p) ∧
      ∃ b : Bool, ∀ e : Env L, ((rl e).moveRight ↔ b = true))
    (hg : UGDefinable fun e => (rl e).guard)
    (hd : ∀ (e : Env L) f g, (rl e).dstSt f g = f)
    (hw : ∀ (e : Env L) f g, (rl e).wr f g = g) :
    URuleDefinable rl :=
  ⟨hst.1, hst.2.1, hst.2.2, hg,
    (uStDefinable_id (L := L) (Q := Q) (W := W)).congr fun e f g q => by rw [hd],
    (uTrDefinable_id (L := L) (Q := Q) (W := W)).congr fun e f g s => by rw [hw]⟩

/-- **A rule that keeps its pointer**, writing only its tracks. -/
theorem uRuleDefinable_of_keepSt {rl : ∀ e : Env L, Rule e.α Q W P}
    (hst : (∃ p : P, ∀ e : Env L, (rl e).srcPh = p) ∧
      (∃ p : P, ∀ e : Env L, (rl e).dstPh = p) ∧
      ∃ b : Bool, ∀ e : Env L, ((rl e).moveRight ↔ b = true))
    (hg : UGDefinable fun e => (rl e).guard)
    (hd : ∀ (e : Env L) f g, (rl e).dstSt f g = f)
    (hw : UTrDefinable fun e => (rl e).wr) :
    URuleDefinable rl :=
  ⟨hst.1, hst.2.1, hst.2.2, hg,
    (uStDefinable_id (L := L) (Q := Q) (W := W)).congr fun e f g q => by rw [hd], hw⟩

/-- **A rule that keeps its tracks**, writing only its pointer – every
checkpoint's dispatch. -/
theorem uRuleDefinable_of_keepWr {rl : ∀ e : Env L, Rule e.α Q W P}
    (hst : (∃ p : P, ∀ e : Env L, (rl e).srcPh = p) ∧
      (∃ p : P, ∀ e : Env L, (rl e).dstPh = p) ∧
      ∃ b : Bool, ∀ e : Env L, ((rl e).moveRight ↔ b = true))
    (hg : UGDefinable fun e => (rl e).guard)
    (hd : UStDefinable fun e => (rl e).dstSt)
    (hw : ∀ (e : Env L) f g, (rl e).wr f g = g) :
    URuleDefinable rl :=
  ⟨hst.1, hst.2.1, hst.2.2, hg, hd,
    (uTrDefinable_id (L := L) (Q := Q) (W := W)).congr fun e f g s => by rw [hw]⟩

end Uniform

end Pfp

end DescriptiveComplexity
