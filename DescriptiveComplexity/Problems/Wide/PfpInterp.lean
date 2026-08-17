/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpDefExp
import DescriptiveComplexity.Problems.Wide.PfpShape
import DescriptiveComplexity.Problems.Wide.PfpTable

/-!
# Writing the emitted machine down

`DescriptiveComplexity.Problems.Wide.PfpTable` says what the eleven relations of
a wide-machine instance are, as predicates on tagged tuples; the definability
layer (`DescriptiveComplexity.Problems.Wide.PfpFactor` and the files above it)
says that every attribute of every rule is decided by **one formula for every
instance**. This file joins the two: the shapes each relation has, as formulas,
with their realizations.

## Where the coordinates go

A defining formula of an `n`-ary relation has free variables `Fin n × Fin dd`:
the `i`-th argument's tuple is `fun j => v (i, j)`. A rule's *payload* occupies
the first `c = card (CtlIx ⊕ SlotIx)` of those, so the guard and payload
formulas the definability layer hands over – which live over `Fin c` and over
`Fin c ⊕ Fin c` – are **relabelled** onto `(i, castLE hpl k)` and nothing else
happens to them.

## What a tag decides

Everything a tag decides is decided when the formula is built, by
`DescriptiveComplexity.Pfp.sideF`: which rule a transition is, and so its two
phases and its direction; which phase a state is in; that a symbol is a symbol.
What is left for the formula is the *shape* – a tuple is canonically padded
(`DescriptiveComplexity.canonF`, read at the layout's `IsPad` by
`DescriptiveComplexity.Pfp.realize_canonF_isPad`) – and the payload.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### A condition the tag decides -/

section Side

variable {L : Language.{0, 0}} {γ : Type}

open Classical in
/-- **A condition decided when the formula is built.** -/
noncomputable def sideF (γ : Type) (p : Prop) : (L.sum Language.order).Formula γ :=
  if p then ⊤ else ⊥

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

@[simp] theorem realize_sideF {p : Prop} : (sideF (L := L) γ p).Realize v ↔ p := by
  classical
  rw [sideF]
  by_cases h : p
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

end Side

/-! ### The coordinates a payload occupies -/

section Coords

variable {Q W : Type} [Fintype Q] [Fintype W] {dd : ℕ}

/-- The coordinates of the `i`-th argument. -/
abbrev argVar (n dd : ℕ) (i : Fin n) : Fin dd → Fin n × Fin dd := fun j => (i, j)

/-- The coordinates the `i`-th argument's **payload** occupies. -/
abbrev payVar (n : ℕ) (hc : Fintype.card (Q ⊕ W) ≤ dd) (i : Fin n) :
    Fin (Fintype.card (Q ⊕ W)) → Fin n × Fin dd :=
  fun k => (i, Fin.castLE hc k)

end Coords

/-! ### A guard and a payload, relabelled -/

section Builders

variable {L : Language.{0, 0}} {Q W : Type} [Fintype Q] [Fintype W] {dd n : ℕ}
variable (hc : Fintype.card (Q ⊕ W) ≤ dd)

/-- **A guard, at the payload of the `i`-th argument.** -/
noncomputable def guardAt (i : Fin n)
    (φ : (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W)))) :
    (L.sum Language.order).Formula (Fin n × Fin dd) :=
  Formula.relabel (payVar n hc i) φ

/-- **A payload written from another, at two arguments.** -/
noncomputable def payAt (i i' : Fin n)
    (χ : (L.sum Language.order).Formula
      (Fin (Fintype.card (Q ⊕ W)) ⊕ Fin (Fintype.card (Q ⊕ W)))) :
    (L.sum Language.order).Formula (Fin n × Fin dd) :=
  Formula.relabel (Sum.elim (payVar n hc i) (payVar n hc i')) χ

variable {A : Type} [L.Structure A] [LinearOrder A] {v : Fin n × Fin dd → A}

theorem realize_guardAt {i : Fin n}
    {φ : (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W)))} :
    (guardAt (L := L) hc i φ).Realize v ↔
      φ.Realize (unpad hc fun j => v (i, j)) := by
  rw [guardAt, Formula.realize_relabel]
  exact Iff.rfl

theorem realize_payAt {i i' : Fin n}
    {χ : (L.sum Language.order).Formula
      (Fin (Fintype.card (Q ⊕ W)) ⊕ Fin (Fintype.card (Q ⊕ W)))} :
    (payAt (L := L) hc i i' χ).Realize v ↔
      χ.Realize (Sum.elim (unpad hc fun j => v (i, j))
        (unpad hc fun j => v (i', j))) := by
  rw [payAt, Formula.realize_relabel]
  refine iff_of_eq (congrArg _ (funext fun k => ?_))
  rcases k with (k | k) <;> rfl

end Builders

/-! ### The three shapes a defining formula has

Every one of the eleven relations is one of three shapes: a **guarded padded
tuple** (a transition, an accepting state), an **attribute** – an element of a
tag the formula names whose payload is written from another's – or a
**constant**, a tag and the all-clear tuple. -/

section Shapes

variable {L : Language.{0, 0}} {Q W : Type} [Fintype Q] [Fintype W] {dd : ℕ}
variable {A : Type} [L.Structure A] [LinearOrder A] {zero : A}

omit [LinearOrder A] in
/-- **Being a given padded tuple** splits into being padded and carrying the
payload, which is what a defining formula can say separately. -/
theorem eq_pad_iff (hc : Fintype.card (Q ⊕ W) ≤ dd)
    (u : Fin dd → A) (w : Fin (Fintype.card (Q ⊕ W)) → A) :
    u = pad zero w ↔ (IsPad (Fintype.card (Q ⊕ W)) zero u ∧ unpad hc u = w) := by
  constructor
  · rintro rfl
    exact ⟨isPad_pad, unpad_pad hc⟩
  · rintro ⟨hp, rfl⟩
    exact (pad_unpad hc hp).symm

end Shapes

section Formulas

variable {L : Language.{0, 0}} {Q W : Type} [Fintype Q] [Fintype W] {dd : ℕ}
variable (hc : Fintype.card (Q ⊕ W) ≤ dd) {Tag : Type}

/-- **A guarded padded tuple**: the tag decides everything but the shape, and
the guard is the definability layer's formula at the payload. -/
noncomputable def padGuardF (p : Prop)
    (φ : (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W)))) :
    (L.sum Language.order).Formula (Fin 1 × Fin dd) :=
  sideF _ p ⊓ canonF (Fintype.card (Q ⊕ W)) (argVar 1 dd 0) ⊓ guardAt hc 0 φ

/-- **An attribute of a transition**: an element of the tag the rule names,
whose payload the rule writes from the transition's own. -/
noncomputable def attrF (p : Prop)
    (χ : (L.sum Language.order).Formula
      (Fin (Fintype.card (Q ⊕ W)) ⊕ Fin (Fintype.card (Q ⊕ W)))) :
    (L.sum Language.order).Formula (Fin 2 × Fin dd) :=
  sideF _ p ⊓ canonF (Fintype.card (Q ⊕ W)) (argVar 2 dd 1) ⊓ payAt hc 0 1 χ

variable {A : Type} [L.Structure A] [LinearOrder A] {zero : A}

theorem realize_padGuardF (h₀ : IsBot zero) {p : Prop}
    {φ : (L.sum Language.order).Formula (Fin (Fintype.card (Q ⊕ W)))}
    {v : Fin 1 × Fin dd → A} :
    (padGuardF (L := L) hc p φ).Realize v ↔
      (p ∧ IsPad (Fintype.card (Q ⊕ W)) zero (fun j => v (0, j)) ∧
        φ.Realize (unpad hc fun j => v (0, j))) := by
  rw [padGuardF]
  simp only [Formula.realize_inf, realize_sideF, realize_guardAt,
    realize_canonF_isPad h₀]
  exact and_assoc

theorem realize_attrF (h₀ : IsBot zero) {p : Prop}
    {χ : (L.sum Language.order).Formula
      (Fin (Fintype.card (Q ⊕ W)) ⊕ Fin (Fintype.card (Q ⊕ W)))}
    {F : (Fin (Fintype.card (Q ⊕ W)) → A) → Fin (Fintype.card (Q ⊕ W)) → A}
    (hχ : ∀ w y : Fin (Fintype.card (Q ⊕ W)) → A,
      (y = F w) ↔ χ.Realize (Sum.elim w y))
    {v : Fin 2 × Fin dd → A} :
    (attrF (L := L) hc p χ).Realize v ↔
      (p ∧ (fun j => v (1, j)) = pad zero (F (unpad hc fun j => v (0, j)))) := by
  rw [attrF]
  simp only [Formula.realize_inf, realize_sideF, realize_payAt,
    realize_canonF_isPad h₀]
  rw [← hχ]
  rw [and_assoc, eq_pad_iff hc]

end Formulas

/-! ### A constant: a tag and the all-clear tuple -/

section Const

variable {L : Language.{0, 0}} {dd : ℕ}

/-- **A constant**: a tag and the all-clear tuple – the start state, the
blank. -/
noncomputable def constF (p : Prop) : (L.sum Language.order).Formula (Fin 1 × Fin dd) :=
  sideF _ p ⊓ canonF 0 (argVar 1 dd 0)

variable {A : Type} [L.Structure A] [LinearOrder A] {zero : A}

theorem realize_constF (h₀ : IsBot zero) {p : Prop} {v : Fin 1 × Fin dd → A} :
    (constF (L := L) p).Realize v ↔
      (p ∧ (fun j => v (0, j)) = fun _ => zero) := by
  rw [constF]
  simp only [Formula.realize_inf, realize_sideF, realize_canonF]
  refine and_congr Iff.rfl ⟨fun h => funext fun j => ?_, fun h j _ => ?_⟩
  · exact le_antisymm (h j (Nat.zero_le _) zero) (h₀ _)
  · have hj : v (0, j) = zero := congrFun h j
    change IsBot (v (0, j))
    rw [hj]
    exact h₀

end Const

/-! ### The two extremes of the interpreted universe

The input channel's mark asks whether a cell is the **first** or the **last**
of the tape, and the tape is ordered block-major. It would be a mistake to
write those as quantifiers over the interpreted universe: in that order an
element is least exactly when its tag is the least tag and its tuple is
all-clear, and greatest exactly when its tag is the greatest and its tuple is
all-set – a decision the tag makes, conjoined with a shape formula. -/

section Extremes

variable {Tag : Type} [LinearOrder Tag] {d : ℕ} {A : Type} [LinearOrder A]

/-- **A tuple below every other is the all-clear one.** -/
theorem tupLeLex_all_iff (u : Fin d → A) :
    (∀ v : Fin d → A, tupLeLex u v) ↔ ∀ j, IsBot (u j) := by
  classical
  constructor
  · intro hall j b
    by_contra hlt
    rcases hall (Function.update u j b) with heq | ⟨p, hbelow, hp⟩
    · exact hlt (le_of_eq ((congrFun heq j).trans (Function.update_self j b u)))
    · rcases eq_or_ne p j with rfl | hne
      · rw [Function.update_self] at hp
        exact hlt (le_of_lt hp)
      · rw [Function.update_of_ne hne] at hp
        exact absurd rfl (ne_of_lt hp)
  · intro hbot v
    by_cases heq : u = v
    · exact Or.inl heq
    · have hex : (Finset.univ.filter fun j : Fin d => u j ≠ v j).Nonempty := by
        by_contra hc
        refine heq (funext fun j => ?_)
        by_contra hj
        exact hc ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
      have hne : u ((Finset.univ.filter fun j : Fin d => u j ≠ v j).min' hex) ≠
          v ((Finset.univ.filter fun j : Fin d => u j ≠ v j).min' hex) :=
        (Finset.mem_filter.mp
          ((Finset.univ.filter fun j : Fin d => u j ≠ v j).min'_mem hex)).2
      refine Or.inr ⟨_, fun i hi => ?_, lt_of_le_of_ne (hbot _ (v _)) hne⟩
      by_contra hc
      exact absurd ((Finset.univ.filter fun j : Fin d => u j ≠ v j).min'_le i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)) (not_le.mpr hi)

/-- **A tagged tuple below every other**: the least tag and the all-clear
tuple. -/
theorem isLeast_tagTupleLe_iff (x : Tag × (Fin d → A)) :
    (∀ y : Tag × (Fin d → A), tagTupleLe x y) ↔
      ((∀ t : Tag, x.1 ≤ t) ∧ ∀ j, IsBot (x.2 j)) := by
  constructor
  · intro hall
    refine ⟨fun t => ?_, (tupLeLex_all_iff x.2).mp fun v => ?_⟩
    · rcases hall (t, x.2) with h | ⟨h, -⟩
      · exact le_of_lt h
      · exact le_of_eq h
    · rcases hall (x.1, v) with h | ⟨-, h⟩
      · exact absurd h (lt_irrefl _)
      · exact h
  · rintro ⟨htag, hbot⟩ y
    rcases lt_or_eq_of_le (htag y.1) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, (tupLeLex_all_iff x.2).mpr hbot y.2⟩

/-- **A tuple above every other is the all-set one.** -/
theorem tupLeLex_all_iff' (u : Fin d → A) :
    (∀ v : Fin d → A, tupLeLex v u) ↔ ∀ j, IsTop (u j) := by
  classical
  constructor
  · intro hall j b
    by_contra hlt
    rcases hall (Function.update u j b) with heq | ⟨p, hbelow, hp⟩
    · exact hlt (le_of_eq ((Function.update_self j b u).symm.trans (congrFun heq j)))
    · rcases eq_or_ne p j with rfl | hne
      · rw [Function.update_self] at hp
        exact hlt (le_of_lt hp)
      · rw [Function.update_of_ne hne] at hp
        exact absurd rfl (ne_of_lt hp)
  · intro htop v
    by_cases heq : v = u
    · exact Or.inl heq
    · have hex : (Finset.univ.filter fun j : Fin d => v j ≠ u j).Nonempty := by
        by_contra hc
        refine heq (funext fun j => ?_)
        by_contra hj
        exact hc ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
      have hne : v ((Finset.univ.filter fun j : Fin d => v j ≠ u j).min' hex) ≠
          u ((Finset.univ.filter fun j : Fin d => v j ≠ u j).min' hex) :=
        (Finset.mem_filter.mp
          ((Finset.univ.filter fun j : Fin d => v j ≠ u j).min'_mem hex)).2
      refine Or.inr ⟨_, fun i hi => ?_, lt_of_le_of_ne (htop _ (v _)) hne⟩
      by_contra hc
      exact absurd ((Finset.univ.filter fun j : Fin d => v j ≠ u j).min'_le i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)) (not_le.mpr hi)

/-- **A tagged tuple above every other**: the greatest tag and the all-set
tuple. -/
theorem isGreatest_tagTupleLe_iff (x : Tag × (Fin d → A)) :
    (∀ y : Tag × (Fin d → A), tagTupleLe y x) ↔
      ((∀ t : Tag, t ≤ x.1) ∧ ∀ j, IsTop (x.2 j)) := by
  constructor
  · intro hall
    refine ⟨fun t => ?_, (tupLeLex_all_iff' x.2).mp fun v => ?_⟩
    · rcases hall (t, x.2) with h | ⟨h, -⟩
      · exact le_of_lt h
      · exact le_of_eq h
    · rcases hall (x.1, v) with h | ⟨-, h⟩
      · exact absurd h (lt_irrefl _)
      · exact h
  · rintro ⟨htag, htop⟩ y
    rcases lt_or_eq_of_le (htag y.1) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, (tupLeLex_all_iff' x.2).mpr htop y.2⟩

end Extremes

/-! ### The static data of a rule, extracted

`DescriptiveComplexity.Pfp.URuleDefinable` says the two phases, the direction,
the guard and the two payloads of a rule do not depend on the instance. What an
interpretation writes down is those, and this is where they are named. -/

namespace PfpData

variable {L : Language.{0, 0}} {dt : PfpData L} [Fintype dt.SlotIx]
variable {rules : ∀ (e : Env L) (i : dt.SF), dt.SFSh i →
  Rule e.α dt.CtlIx dt.SlotIx dt.PF}

/-- **The rule names of the emitted machine**, as a type the instance does not
mention. -/
abbrev RTag (dt : PfpData L) : Type := (i : dt.SF) × dt.SFSh i

/-- **The tags of the interpreted universe.** -/
abbrev ITag (dt : PfpData L) : Type := PfpTag dt.RTag dt.PF dt.KIx

variable (hdef : URulesDefinable rules)

/-- The phase a rule fires from. -/
noncomputable def srcPhOf (r : dt.RTag) : dt.PF := (hdef r.1 r.2).srcPh.choose

/-- The phase it moves to. -/
noncomputable def dstPhOf (r : dt.RTag) : dt.PF := (hdef r.1 r.2).dstPh.choose

/-- Its direction. -/
noncomputable def rightOf (r : dt.RTag) : Bool := (hdef r.1 r.2).right.choose

/-- Its guard, as a formula over the payload coordinates. -/
noncomputable def guardFOf (r : dt.RTag) :
    (L.sum Language.order).Formula (Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx))) :=
  (hdef r.1 r.2).guard.choose

/-- The payload of the state it moves to, as a formula. -/
noncomputable def dstFOf (r : dt.RTag) :
    (L.sum Language.order).Formula
      (Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) ⊕
        Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx))) :=
  (uPayloadDefinable_stPl (hdef r.1 r.2).dst).choose

/-- The payload of the symbol it writes, as a formula. -/
noncomputable def wrFOf (r : dt.RTag) :
    (L.sum Language.order).Formula
      (Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) ⊕
        Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx))) :=
  (uPayloadDefinable_syPl (hdef r.1 r.2).wr).choose

/-- The payload of the state a rule fires *in*: the pointer, unchanged. One
formula for every rule. -/
noncomputable def srcFOf :
    (L.sum Language.order).Formula
      (Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) ⊕
        Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx))) :=
  (uPayloadDefinable_stPl (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
    (F := fun _ f _ => f) uStDefinable_id).choose

/-- And of the symbol it reads: the tracks, unchanged. -/
noncomputable def readFOf :
    (L.sum Language.order).Formula
      (Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) ⊕
        Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx))) :=
  (uPayloadDefinable_syPl (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
    (G := fun _ _ g => g) uTrDefinable_id).choose

/-! ### What they say -/

theorem srcPhOf_spec (r : dt.RTag) (e : Env L) :
    (rules e r.1 r.2).srcPh = dt.srcPhOf hdef r := (hdef r.1 r.2).srcPh.choose_spec e

theorem dstPhOf_spec (r : dt.RTag) (e : Env L) :
    (rules e r.1 r.2).dstPh = dt.dstPhOf hdef r := (hdef r.1 r.2).dstPh.choose_spec e

theorem rightOf_spec (r : dt.RTag) (e : Env L) :
    ((rules e r.1 r.2).moveRight ↔ dt.rightOf hdef r = true) :=
  (hdef r.1 r.2).right.choose_spec e

theorem guardFOf_spec (r : dt.RTag) (e : Env L)
    (w : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → e.α) :
    (rules e r.1 r.2).guard (fun q => unslot w (Sum.inl q))
        (fun s => unslot w (Sum.inr s)) ↔ (dt.guardFOf hdef r).Realize w :=
  (hdef r.1 r.2).guard.choose_spec e w

theorem dstFOf_spec (r : dt.RTag) (e : Env L)
    (w y : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → e.α) :
    (y = stPl (W := dt.SlotIx) e.zero
        ((rules e r.1 r.2).dstSt (fun q => unslot w (Sum.inl q))
          fun s => unslot w (Sum.inr s))) ↔
      (dt.dstFOf hdef r).Realize (Sum.elim w y) :=
  (uPayloadDefinable_stPl (hdef r.1 r.2).dst).choose_spec e w y

theorem wrFOf_spec (r : dt.RTag) (e : Env L)
    (w y : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → e.α) :
    (y = syPl (Q := dt.CtlIx) e.zero
        ((rules e r.1 r.2).wr (fun q => unslot w (Sum.inl q))
          fun s => unslot w (Sum.inr s))) ↔
      (dt.wrFOf hdef r).Realize (Sum.elim w y) :=
  (uPayloadDefinable_syPl (hdef r.1 r.2).wr).choose_spec e w y

theorem srcFOf_spec (e : Env L)
    (w y : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → e.α) :
    (y = stPl (W := dt.SlotIx) e.zero fun q => unslot w (Sum.inl q)) ↔
      (dt.srcFOf (L := L)).Realize (Sum.elim w y) :=
  (uPayloadDefinable_stPl (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
    (F := fun _ f _ => f) uStDefinable_id).choose_spec e w y

theorem readFOf_spec (e : Env L)
    (w y : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → e.α) :
    (y = syPl (Q := dt.CtlIx) e.zero fun s => unslot w (Sum.inr s)) ↔
      (dt.readFOf (L := L)).Realize (Sum.elim w y) :=
  (uPayloadDefinable_syPl (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
    (G := fun _ _ g => g) uTrDefinable_id).choose_spec e w y

end PfpData

/-! ### The transitions, and their five attributes

Each is one of the shapes above at the data the tag names: a transition is a
guarded padded tuple, its four payload attributes are attributes, and its
direction is decided outright. -/

namespace PfpData

section Formulas

variable {L : Language.{0, 0}} {dt : PfpData L} [Fintype dt.SlotIx]
variable {rules : ∀ (e : Env L) (i : dt.SF), dt.SFSh i →
  Rule e.α dt.CtlIx dt.SlotIx dt.PF}
variable (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
variable (hdef : URulesDefinable rules)

/-- **Being a transition.** -/
noncomputable def trF : dt.ITag → (L.sum Language.order).Formula (Fin 1 × Fin dt.dd)
  | .ctrl r => padGuardF hpl True (dt.guardFOf hdef r)
  | _ => ⊥

/-- **Moving the head right.** -/
noncomputable def rightF : dt.ITag → (L.sum Language.order).Formula (Fin 1 × Fin dt.dd)
  | .ctrl r => sideF _ (dt.rightOf hdef r = true)
  | _ => ⊥

/-- **The state a transition applies in.** -/
noncomputable def srcF (t t' : dt.ITag) :
    (L.sum Language.order).Formula (Fin 2 × Fin dt.dd) :=
  match t with
  | .ctrl r => attrF hpl (t' = PfpTag.phase (dt.srcPhOf hdef r)) dt.srcFOf
  | _ => ⊥

/-- **The symbol it reads.** -/
noncomputable def readF (t t' : dt.ITag) :
    (L.sum Language.order).Formula (Fin 2 × Fin dt.dd) :=
  match t with
  | .ctrl _ => attrF hpl (t' = PfpTag.sym) dt.readFOf
  | _ => ⊥

/-- **The state it moves to.** -/
noncomputable def dstF (t t' : dt.ITag) :
    (L.sum Language.order).Formula (Fin 2 × Fin dt.dd) :=
  match t with
  | .ctrl r => attrF hpl (t' = PfpTag.phase (dt.dstPhOf hdef r)) (dt.dstFOf hdef r)
  | _ => ⊥

/-- **The symbol it writes.** -/
noncomputable def writeF (t t' : dt.ITag) :
    (L.sum Language.order).Formula (Fin 2 × Fin dt.dd) :=
  match t with
  | .ctrl r => attrF hpl (t' = PfpTag.sym) (dt.wrFOf hdef r)
  | _ => ⊥

/-! ### What they say -/

variable (e : Env L)

theorem realize_trF_ctrl (r : dt.RTag) {v : Fin 1 × Fin dt.dd → e.α} :
    (dt.trF hpl hdef (.ctrl r)).Realize v ↔
      (IsPad (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) e.zero (fun j => v (0, j)) ∧
        (rules e r.1 r.2).guard
          (fun q => unslot (unpad hpl fun j => v (0, j)) (Sum.inl q))
          fun s => unslot (unpad hpl fun j => v (0, j)) (Sum.inr s)) := by
  rw [trF, realize_padGuardF hpl e.hbot]
  exact ⟨fun h => ⟨h.2.1, (dt.guardFOf_spec hdef r e _).mpr h.2.2⟩,
    fun h => ⟨trivial, h.1, (dt.guardFOf_spec hdef r e _).mp h.2⟩⟩

theorem realize_rightF_ctrl (r : dt.RTag) {v : Fin 1 × Fin dt.dd → e.α} :
    (dt.rightF hdef (.ctrl r)).Realize v ↔ (rules e r.1 r.2).moveRight := by
  rw [rightF, realize_sideF]
  exact (dt.rightOf_spec hdef r e).symm

theorem realize_srcF_ctrl (r : dt.RTag) (t' : dt.ITag)
    {v : Fin 2 × Fin dt.dd → e.α} :
    (dt.srcF hpl hdef (.ctrl r) t').Realize v ↔
      ((t', fun j => v (1, j)) : dt.ITag × (Fin dt.dd → e.α)) =
        stateElt e.zero (dt.srcPhOf hdef r)
          (stPl (W := dt.SlotIx) e.zero fun q =>
            unslot (unpad hpl fun j => v (0, j)) (Sum.inl q)) := by
  rw [srcF, realize_attrF hpl e.hbot (dt.srcFOf_spec e)]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem realize_readF_ctrl (r : dt.RTag) (t' : dt.ITag)
    {v : Fin 2 × Fin dt.dd → e.α} :
    (dt.readF hpl (.ctrl r) t').Realize v ↔
      ((t', fun j => v (1, j)) : dt.ITag × (Fin dt.dd → e.α)) =
        symElt e.zero (syPl (Q := dt.CtlIx) e.zero fun s =>
          unslot (unpad hpl fun j => v (0, j)) (Sum.inr s)) := by
  rw [readF, realize_attrF hpl e.hbot (dt.readFOf_spec e)]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem realize_dstF_ctrl (r : dt.RTag) (t' : dt.ITag)
    {v : Fin 2 × Fin dt.dd → e.α} :
    (dt.dstF hpl hdef (.ctrl r) t').Realize v ↔
      ((t', fun j => v (1, j)) : dt.ITag × (Fin dt.dd → e.α)) =
        stateElt e.zero (dt.dstPhOf hdef r)
          (stPl (W := dt.SlotIx) e.zero
            ((rules e r.1 r.2).dstSt
              (fun q => unslot (unpad hpl fun j => v (0, j)) (Sum.inl q))
              fun s => unslot (unpad hpl fun j => v (0, j)) (Sum.inr s))) := by
  rw [dstF, realize_attrF hpl e.hbot (dt.dstFOf_spec hdef r e)]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem realize_writeF_ctrl (r : dt.RTag) (t' : dt.ITag)
    {v : Fin 2 × Fin dt.dd → e.α} :
    (dt.writeF hpl hdef (.ctrl r) t').Realize v ↔
      ((t', fun j => v (1, j)) : dt.ITag × (Fin dt.dd → e.α)) =
        symElt e.zero
          (syPl (Q := dt.CtlIx) e.zero
            ((rules e r.1 r.2).wr
              (fun q => unslot (unpad hpl fun j => v (0, j)) (Sum.inl q))
              fun s => unslot (unpad hpl fun j => v (0, j)) (Sum.inr s))) := by
  rw [writeF, realize_attrF hpl e.hbot (dt.wrFOf_spec hdef r e)]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

end Formulas

end PfpData

/-! ### Two more shapes: a bit, and an all-set tuple -/

section Bits

variable {L : Language.{0, 0}} {γ : Type}

/-- **A variable holds the bit of a condition.** -/
noncomputable def bitAtF (y : γ) (φ : (L.sum Language.order).Formula γ) :
    (L.sum Language.order).Formula γ :=
  (φ ⊓ topF y) ⊔ (∼φ ⊓ botF y)

/-- **Every coordinate of a tuple is the greatest element**: the mirror of
`DescriptiveComplexity.canonF` at length `0`. -/
noncomputable def topTupF {D : ℕ} (u : Fin D → γ) :
    (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun j => topF (u j))

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A} {zero one : A}

theorem realize_bitAtF (h₀ : IsBot zero) (h₁ : IsTop one) {y : γ}
    {φ : (L.sum Language.order).Formula γ} :
    (bitAtF (L := L) y φ).Realize v ↔ v y = bitVal zero one (φ.Realize v) := by
  rw [bitAtF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_topF, realize_botF]
  by_cases hφ : φ.Realize v
  · rw [bitVal_pos hφ]
    exact ⟨fun h => h.elim (fun h1 => le_antisymm (h₁ _) (h1.2 one))
        fun h2 => absurd hφ h2.1,
      fun h => Or.inl ⟨hφ, h ▸ h₁⟩⟩
  · rw [bitVal_neg hφ]
    exact ⟨fun h => h.elim (fun h1 => absurd h1.1 hφ)
        fun h2 => le_antisymm (h2.2 zero) (h₀ _),
      fun h => Or.inr ⟨hφ, h ▸ h₀⟩⟩

theorem realize_topTupF {D : ℕ} {u : Fin D → γ} :
    (topTupF (L := L) u).Realize v ↔ ∀ j : Fin D, IsTop (v (u j)) := by
  rw [topTupF, realize_listInf]
  constructor
  · intro h j
    exact realize_topF.mp (h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    exact realize_topF.mpr (h j)

end Bits

namespace PfpData

section MoreFormulas

variable {L : Language.{0, 0}} {dt : PfpData L} [Fintype dt.SlotIx]
variable (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
variable {accept : ∀ e : Env L, dt.PF → (dt.CtlIx → e.α) → Prop}
variable (hacc : ∀ p : dt.PF,
  UGDefinable fun e f (_ : dt.SlotIx → e.α) => accept e p f)

/-- The accepting predicate of a phase, as a formula. -/
noncomputable def accFOf (p : dt.PF) :
    (L.sum Language.order).Formula (Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx))) :=
  (hacc p).choose

theorem accFOf_spec (p : dt.PF) (e : Env L)
    (w : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → e.α) :
    accept e p (fun q => unslot w (Sum.inl q)) ↔ (dt.accFOf hacc p).Realize w :=
  (hacc p).choose_spec e w

/-- **Being an accepting state.** -/
noncomputable def accF : dt.ITag → (L.sum Language.order).Formula (Fin 1 × Fin dt.dd)
  | .phase p => padGuardF hpl True (dt.accFOf hacc p)
  | _ => ⊥

/-- **Being the start state**: the start phase and the all-clear tuple. -/
noncomputable def startF (p₀ : dt.PF) (t : dt.ITag) :
    (L.sum Language.order).Formula (Fin 1 × Fin dt.dd) :=
  constF (t = PfpTag.phase p₀)

/-- **Being the blank**: the alphabet tag and the all-clear tuple. -/
noncomputable def blankF (t : dt.ITag) :
    (L.sum Language.order).Formula (Fin 1 × Fin dt.dd) :=
  constF (t = PfpTag.sym)

variable (e : Env L)

theorem realize_accF_phase (p : dt.PF) {v : Fin 1 × Fin dt.dd → e.α} :
    (dt.accF hpl hacc (.phase p)).Realize v ↔
      (IsPad (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) e.zero (fun j => v (0, j)) ∧
        accept e p fun q =>
          unslot (unpad hpl fun j => v (0, j)) (Sum.inl q)) := by
  rw [accF, realize_padGuardF hpl e.hbot]
  exact ⟨fun h => ⟨h.2.1, (dt.accFOf_spec hacc p e _).mpr h.2.2⟩,
    fun h => ⟨trivial, h.1, (dt.accFOf_spec hacc p e _).mp h.2⟩⟩

omit [Fintype dt.SlotIx] in
theorem realize_startF (p₀ : dt.PF) (t : dt.ITag) {v : Fin 1 × Fin dt.dd → e.α} :
    (dt.startF p₀ t).Realize v ↔
      ((t, fun j => v (0, j)) : dt.ITag × (Fin dt.dd → e.α)) =
        (PfpTag.phase p₀, fun _ => e.zero) := by
  rw [startF, realize_constF e.hbot]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

omit [Fintype dt.SlotIx] in
theorem realize_blankF (t : dt.ITag) {v : Fin 1 × Fin dt.dd → e.α} :
    (dt.blankF t).Realize v ↔
      ((t, fun j => v (0, j)) : dt.ITag × (Fin dt.dd → e.α)) =
        (PfpTag.sym, fun _ => e.zero) := by
  rw [blankF, realize_constF e.hbot]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

end MoreFormulas

end PfpData

/-! ### The input channel

The one relation with content. The mark a cell starts with
(`DescriptiveComplexity.Pfp.slotMark`) is a *register file*: the register flag
is set, the first and last cells of the tape are flagged, the block flags decode
the cell's tag, the name slots carry the cell's own first `dd₀` coordinates and
the padding flag says the rest are clear. Every one of those is a tag decision,
a shape formula, or an equality of variables – the two extremes because of
`DescriptiveComplexity.Pfp.isLeast_tagTupleLe_iff` and its dual. -/

namespace PfpData

section Mark

variable {L : Language.{0, 0}} {dt : PfpData L} [Fintype dt.SlotIx]
variable [LinearOrder dt.RTag] [LinearOrder dt.PF]
variable (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)

/-- **What one slot of a cell's mark holds**, at the variable that slot
occupies. -/
noncomputable def markSlotF (t : dt.ITag) (y : Fin 2 × Fin dt.dd) :
    dt.SlotIx → (L.sum Language.order).Formula (Fin 2 × Fin dt.dd)
  | .reg => topF y
  | .regFirst =>
    bitAtF y (sideF _ (∀ t' : dt.ITag, t ≤ t') ⊓ canonF 0 (argVar 2 dt.dd 0))
  | .regLast =>
    bitAtF y (sideF _ (∀ t' : dt.ITag, t' ≤ t) ⊓ topTupF (argVar 2 dt.dd 0))
  | .blk b => bitAtF y (sideF _ (tagBlk t = b))
  | .name j =>
    Term.equal (Term.var y) (Term.var (argVar 2 dt.dd 0 (Fin.castLE dt.dd0Le j)))
  | .pdd => bitAtF y (canonF dt.dd0 (argVar 2 dt.dd 0))
  | _ => botF y

/-- **One coordinate of a cell's mark**: the control slots of a symbol are
clear, the track slots are the register file's. -/
noncomputable def markCoordF (t : dt.ITag)
    (k : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx))) :
    (L.sum Language.order).Formula (Fin 2 × Fin dt.dd) :=
  match (Fintype.equivFin (dt.CtlIx ⊕ dt.SlotIx)).symm k with
  | Sum.inl _ => botF (payVar 2 hpl 1 k)
  | Sum.inr s => dt.markSlotF t (payVar 2 hpl 1 k) s

/-- **The whole mark**, coordinate by coordinate. -/
noncomputable def markF (t : dt.ITag) :
    (L.sum Language.order).Formula (Fin 2 × Fin dt.dd) :=
  listInf ((List.finRange (Fintype.card (dt.CtlIx ⊕ dt.SlotIx))).map
    (dt.markCoordF hpl t))

/-- **The input channel**: the cell of an element holds that element's mark. -/
noncomputable def inpF (t t' : dt.ITag) :
    (L.sum Language.order).Formula (Fin 2 × Fin dt.dd) :=
  sideF _ (t' = PfpTag.sym) ⊓
    canonF (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) (argVar 2 dt.dd 1) ⊓
    dt.markF hpl t

variable (e : Env L)

omit [Fintype dt.SlotIx] in
theorem realize_markSlotF (t : dt.ITag) (y : Fin 2 × Fin dt.dd) (s : dt.SlotIx)
    {v : Fin 2 × Fin dt.dd → e.α} :
    (dt.markSlotF t y s).Realize v ↔
      v y = slotMark e.zero e.one dt.dd0Le
        ((t, fun j => v (0, j)) : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) s := by
  match s with
  | .reg => exact realize_topF.trans (e.isTop_iff _)
  | .regFirst =>
    have hP : ((sideF (L := L) _ (∀ t' : dt.ITag, t ≤ t') ⊓
        canonF 0 (argVar 2 dt.dd 0)).Realize v) ↔
        ∀ y' : Univ e.α dt.RTag dt.PF dt.KIx dt.dd,
          tagTupleLe ((t, fun j => v (0, j)) :
            Univ e.α dt.RTag dt.PF dt.KIx dt.dd) y' := by
      rw [Formula.realize_inf, realize_sideF, realize_canonF]
      refine Iff.trans (and_congr Iff.rfl ?_)
        (isLeast_tagTupleLe_iff ((t, fun j => v (0, j)) :
          Univ e.α dt.RTag dt.PF dt.KIx dt.dd)).symm
      exact ⟨fun h j => h j (Nat.zero_le _), fun h j _ => h j⟩
    simp only [markSlotF]
    rw [realize_bitAtF e.hbot e.htop, bitVal_congr hP]
    exact Iff.rfl
  | .regLast =>
    have hP : ((sideF (L := L) _ (∀ t' : dt.ITag, t' ≤ t) ⊓
        topTupF (argVar 2 dt.dd 0)).Realize v) ↔
        ∀ y' : Univ e.α dt.RTag dt.PF dt.KIx dt.dd,
          tagTupleLe y' ((t, fun j => v (0, j)) :
            Univ e.α dt.RTag dt.PF dt.KIx dt.dd) := by
      rw [Formula.realize_inf, realize_sideF, realize_topTupF]
      exact (isGreatest_tagTupleLe_iff ((t, fun j => v (0, j)) :
        Univ e.α dt.RTag dt.PF dt.KIx dt.dd)).symm
    simp only [markSlotF]
    rw [realize_bitAtF e.hbot e.htop, bitVal_congr hP]
    exact Iff.rfl
  | .blk b =>
    have hP : ((sideF (L := L) (Fin 2 × Fin dt.dd) (tagBlk t = b)).Realize v) ↔
        (tagBlk t = b) := realize_sideF
    simp only [markSlotF]
    rw [realize_bitAtF e.hbot e.htop, bitVal_congr hP]
    exact Iff.rfl
  | .name j =>
    simp only [markSlotF]
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact Iff.rfl
  | .pdd =>
    have hP : ((canonF (L := L) dt.dd0 (argVar 2 dt.dd 0)).Realize v) ↔
        ∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → v (0, j) = e.zero := by
      rw [realize_canonF]
      exact forall_congr' fun j => imp_congr Iff.rfl (e.isBot_iff _)
    simp only [markSlotF]
    rw [realize_bitAtF e.hbot e.htop, bitVal_congr hP]
    exact Iff.rfl
  | .mir => exact realize_botF.trans (e.isBot_iff _)
  | .tgt => exact realize_botF.trans (e.isBot_iff _)
  | .sav => exact realize_botF.trans (e.isBot_iff _)
  | .val => exact realize_botF.trans (e.isBot_iff _)
  | .wk => exact realize_botF.trans (e.isBot_iff _)
  | .bot => exact realize_botF.trans (e.isBot_iff _)
  | .ltp => exact realize_botF.trans (e.isBot_iff _)
  | .old i => exact realize_botF.trans (e.isBot_iff _)
  | .new i => exact realize_botF.trans (e.isBot_iff _)

theorem realize_markCoordF (t : dt.ITag)
    (k : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)))
    {v : Fin 2 × Fin dt.dd → e.α} :
    (dt.markCoordF hpl t k).Realize v ↔
      unpad hpl (fun j => v (1, j)) k =
        syPl (Q := dt.CtlIx) e.zero
          (slotMark e.zero e.one dt.dd0Le
            ((t, fun j => v (0, j)) : Univ e.α dt.RTag dt.PF dt.KIx dt.dd)) k := by
  have hsy : ∀ g : dt.SlotIx → e.α,
      syPl (Q := dt.CtlIx) e.zero g k =
        syVec (Q := dt.CtlIx) e.zero g
          ((Fintype.equivFin (dt.CtlIx ⊕ dt.SlotIx)).symm k) := fun _ => rfl
  simp only [markCoordF]
  match hk : (Fintype.equivFin (dt.CtlIx ⊕ dt.SlotIx)).symm k with
  | Sum.inl q =>
    refine realize_botF.trans ((e.isBot_iff _).trans ?_)
    rw [hsy, hk]
    exact Iff.rfl
  | Sum.inr s =>
    refine (dt.realize_markSlotF e t (payVar 2 hpl 1 k) s).trans ?_
    rw [hsy, hk]
    exact Iff.rfl

theorem realize_markF (t : dt.ITag) {v : Fin 2 × Fin dt.dd → e.α} :
    (dt.markF hpl t).Realize v ↔
      unpad hpl (fun j => v (1, j)) =
        syPl (Q := dt.CtlIx) e.zero
          (slotMark e.zero e.one dt.dd0Le
            ((t, fun j => v (0, j)) : Univ e.α dt.RTag dt.PF dt.KIx dt.dd)) := by
  rw [markF, realize_listInf, funext_iff]
  constructor
  · intro hall k
    exact (dt.realize_markCoordF hpl e t k).mp
      (hall _ (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))
  · intro hall ψ hψ
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hψ
    exact (dt.realize_markCoordF hpl e t k).mpr (hall k)

theorem realize_inpF (t t' : dt.ITag) {v : Fin 2 × Fin dt.dd → e.α} :
    (dt.inpF hpl t t').Realize v ↔
      ((t', fun j => v (1, j)) : dt.ITag × (Fin dt.dd → e.α)) =
        symElt e.zero
          (syPl (Q := dt.CtlIx) e.zero
            (slotMark e.zero e.one dt.dd0Le
              ((t, fun j => v (0, j)) : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
                dt.SlotIx → e.α)) := by
  rw [inpF]
  simp only [Formula.realize_inf, realize_sideF, realize_canonF_isPad e.hbot,
    dt.realize_markF hpl e t]
  rw [and_assoc, ← eq_pad_iff hpl]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

end Mark

end PfpData

/-! ### The interpretation

Eleven relation symbols, eleven formulas – the ten above and the order, which
is `DescriptiveComplexity.lexLeF`, the tags compared when the formula is
built. -/

namespace PfpData

section Interp

variable {L : Language.{0, 0}} {dt : PfpData L} [Fintype dt.SlotIx]
variable [LinearOrder dt.RTag] [LinearOrder dt.PF]
variable {rules : ∀ (e : Env L) (i : dt.SF), dt.SFSh i →
  Rule e.α dt.CtlIx dt.SlotIx dt.PF}
variable {accept : ∀ e : Env L, dt.PF → (dt.CtlIx → e.α) → Prop}
variable (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
variable (hdef : URulesDefinable rules)
variable (hacc : ∀ p : dt.PF,
  UGDefinable fun e f (_ : dt.SlotIx → e.α) => accept e p f)
variable (p₀ : dt.PF)

/-! ### The program the interpretation writes down -/

section Prog

variable {L : Language.{0, 0}} {dt : PfpData L} [Fintype dt.SlotIx]
variable [LinearOrder dt.RTag] [LinearOrder dt.PF]
variable (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) (e : Env L)
variable (rl : ∀ i : dt.SF, dt.SFSh i → Rule e.α dt.CtlIx dt.SlotIx dt.PF)
variable (p₀ : dt.PF) (acc : dt.PF → (dt.CtlIx → e.α) → Prop)

/-- **The program at one instance**: the rules the definability layer hands
over, with the reduction's constants – an all-clear pointer, an all-clear
blank and the register file of `DescriptiveComplexity.Pfp.slotMark`. -/
noncomputable def progFrom :
    Prog e.α dt.RTag dt.PF dt.CtlIx dt.SlotIx dt.KIx dt.dd where
  zero := e.zero
  one := e.one
  zero_ne_one := e.hzo
  payload_le := hpl
  rules r := rl r.1 r.2
  startPh := p₀
  startSt _ := e.zero
  accept := acc
  blank _ := e.zero
  mark := slotMark e.zero e.one dt.dd0Le

omit [Fintype dt.SlotIx] [LinearOrder dt.RTag] [LinearOrder dt.PF] in
/-- A payload of clear elements pads to a tuple of clear elements. -/
theorem pad_const {c : ℕ} :
    pad (dd := dt.dd) e.zero (fun _ : Fin c => e.zero) = fun _ => e.zero := by
  funext j
  rw [pad]
  split <;> rfl

omit [LinearOrder dt.RTag] [LinearOrder dt.PF] in
/-- The pointer the machine starts with is clear at every slot. -/
theorem stPl_const :
    stPl (W := dt.SlotIx) e.zero (fun _ : dt.CtlIx => e.zero) = fun _ => e.zero := by
  funext k
  change Sum.elim (fun _ => e.zero) (fun _ => e.zero)
    ((Fintype.equivFin (dt.CtlIx ⊕ dt.SlotIx)).symm k) = e.zero
  rcases (Fintype.equivFin (dt.CtlIx ⊕ dt.SlotIx)).symm k with q | s <;> rfl

omit [LinearOrder dt.RTag] [LinearOrder dt.PF] in
/-- And so is the blank. -/
theorem syPl_const :
    syPl (Q := dt.CtlIx) e.zero (fun _ : dt.SlotIx => e.zero) = fun _ => e.zero := by
  funext k
  change Sum.elim (fun _ => e.zero) (fun _ => e.zero)
    ((Fintype.equivFin (dt.CtlIx ⊕ dt.SlotIx)).symm k) = e.zero
  rcases (Fintype.equivFin (dt.CtlIx ⊕ dt.SlotIx)).symm k with q | s <;> rfl

end Prog

/-- **The emitted machine, written down**: an interpretation of the
wide-machine vocabulary in the ordered source vocabulary, tagged by the
program's own tags. -/
noncomputable def pfpInterp :
    FOInterpretation (L.sum Language.order) Language.wide dt.ITag dt.dd where
  relFormula {n} R :=
    match n, R with
    | _, .wle => fun t => lexLeF L dt.dd (t 0) (t 1)
    | _, .tr => fun t => dt.trF hpl hdef (t 0)
    | _, .start => fun t => dt.startF p₀ (t 0)
    | _, .acc => fun t => dt.accF hpl hacc (t 0)
    | _, .blank => fun t => dt.blankF (t 0)
    | _, .right => fun t => dt.rightF hdef (t 0)
    | _, .src => fun t => dt.srcF hpl hdef (t 0) (t 1)
    | _, .read => fun t => dt.readF hpl (t 0) (t 1)
    | _, .dst => fun t => dt.dstF hpl hdef (t 0) (t 1)
    | _, .write => fun t => dt.writeF hpl hdef (t 0) (t 1)
    | _, .inp => fun t => dt.inpF hpl (t 0) (t 1)

variable (e : Env L)

/-- The structure the interpretation puts on the emitted universe. -/
noncomputable abbrev wideStr :
    Language.wide.Structure (Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :=
  (dt.pfpInterp hpl hdef hacc p₀).mapStructure e.α

variable [ws : Language.wide.Structure (Univ e.α dt.RTag dt.PF dt.KIx dt.dd)]
variable (hws : ws = dt.wideStr hpl hdef hacc p₀ e)

include hws in
/-- The valuation a unary relation's argument supplies. -/
theorem relMap_one {R : Language.wide.Relations 1}
    {φ : dt.ITag → (L.sum Language.order).Formula (Fin 1 × Fin dt.dd)}
    (hR : (dt.pfpInterp hpl hdef hacc p₀).relFormula R = fun t => φ (t 0))
    (x : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    RelMap R ![x] ↔ (φ x.1).Realize fun q => x.2 q.2 := by
  have h : RelMap R ![x] ↔
      ((dt.pfpInterp hpl hdef hacc p₀).relFormula R fun i => (![x] i).1).Realize
        (fun q => (![x] q.1).2 q.2) := by rw [hws]; exact Iff.rfl
  rw [h, hR]
  simp only [Matrix.cons_val_fin_one]

include hws in
/-- The valuation a binary relation's arguments supply. -/
theorem relMap_two {R : Language.wide.Relations 2}
    {φ : dt.ITag → dt.ITag → (L.sum Language.order).Formula (Fin 2 × Fin dt.dd)}
    (hR : (dt.pfpInterp hpl hdef hacc p₀).relFormula R = fun t => φ (t 0) (t 1))
    (x y : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    RelMap R ![x, y] ↔
      (φ x.1 y.1).Realize fun z => (if z.1 = 0 then x.2 else y.2) z.2 := by
  have h : RelMap R ![x, y] ↔
      ((dt.pfpInterp hpl hdef hacc p₀).relFormula R fun i => (![x, y] i).1).Realize
        (fun q => (![x, y] q.1).2 q.2) := by rw [hws]; exact Iff.rfl
  rw [h, hR]
  refine iff_of_eq (congrArg _ (funext fun z => ?_))
  obtain ⟨i, j⟩ := z
  fin_cases i <;> rfl

/-! ### The interpreted structure reads the table

Eleven definitional unfoldings: each relation of the interpreted structure is
its formula at the tags of its arguments, and each formula was built to say
what the table says. The only two rewrites are the two phases of a rule, which
`DescriptiveComplexity.Pfp.PfpData.srcPhOf` and `dstPhOf` name. -/

include hws in
theorem relMap_le (x y : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMLe x y ↔ tagTupleLe x y := by
  rw [WMLe, dt.relMap_two hpl hdef hacc p₀ e hws (R := Language.wmLe)
      (φ := fun t t' => lexLeF L dt.dd t t') rfl, realize_lexLeF]
  rfl

include hws in
theorem relMap_tr (τ : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMTr τ ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.IsTr τ := by
  obtain ⟨t, u⟩ := τ
  rw [WMTr, dt.relMap_one hpl hdef hacc p₀ e hws (R := Language.wmTr)
    (φ := fun t => dt.trF hpl hdef t) rfl]
  match t with
  | .ctrl r => exact dt.realize_trF_ctrl hpl hdef e r
  | .sym => exact Iff.rfl
  | .phase p => exact Iff.rfl
  | .arg i => exact Iff.rfl

include hws in
theorem relMap_right (τ : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMRight τ ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.IsRight τ := by
  obtain ⟨t, u⟩ := τ
  rw [WMRight, dt.relMap_one hpl hdef hacc p₀ e hws (R := Language.wmRight)
    (φ := fun t => dt.rightF hdef t) rfl]
  match t with
  | .ctrl r => exact dt.realize_rightF_ctrl hdef e r
  | .sym => exact Iff.rfl
  | .phase p => exact Iff.rfl
  | .arg i => exact Iff.rfl

include hws in
theorem relMap_src (τ q : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMSrc τ q ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.Src τ q := by
  obtain ⟨t, u⟩ := τ
  rw [WMSrc, dt.relMap_two hpl hdef hacc p₀ e hws (R := Language.wmSrc)
    (φ := fun t t' => dt.srcF hpl hdef t t') rfl]
  match t with
  | .ctrl r =>
    rw [dt.realize_srcF_ctrl hpl hdef e r q.1, ← dt.srcPhOf_spec hdef r e]
    exact Iff.rfl
  | .sym => exact Iff.rfl
  | .phase p => exact Iff.rfl
  | .arg i => exact Iff.rfl

include hws in
theorem relMap_read (τ a : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMRead τ a ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.Read τ a := by
  obtain ⟨t, u⟩ := τ
  rw [WMRead, dt.relMap_two hpl hdef hacc p₀ e hws (R := Language.wmRead)
    (φ := fun t t' => dt.readF hpl t t') rfl]
  match t with
  | .ctrl r => exact dt.realize_readF_ctrl hpl e r a.1
  | .sym => exact Iff.rfl
  | .phase p => exact Iff.rfl
  | .arg i => exact Iff.rfl

include hws in
theorem relMap_dst (τ q : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMDst τ q ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.Dst τ q := by
  obtain ⟨t, u⟩ := τ
  rw [WMDst, dt.relMap_two hpl hdef hacc p₀ e hws (R := Language.wmDst)
    (φ := fun t t' => dt.dstF hpl hdef t t') rfl]
  match t with
  | .ctrl r =>
    rw [dt.realize_dstF_ctrl hpl hdef e r q.1, ← dt.dstPhOf_spec hdef r e]
    exact Iff.rfl
  | .sym => exact Iff.rfl
  | .phase p => exact Iff.rfl
  | .arg i => exact Iff.rfl

include hws in
theorem relMap_write (τ a : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMWrite τ a ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.Write τ a := by
  obtain ⟨t, u⟩ := τ
  rw [WMWrite, dt.relMap_two hpl hdef hacc p₀ e hws (R := Language.wmWrite)
    (φ := fun t t' => dt.writeF hpl hdef t t') rfl]
  match t with
  | .ctrl r => exact dt.realize_writeF_ctrl hpl hdef e r a.1
  | .sym => exact Iff.rfl
  | .phase p => exact Iff.rfl
  | .arg i => exact Iff.rfl

include hws in
theorem relMap_start (q : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMStart q ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.IsStart q := by
  obtain ⟨t, u⟩ := q
  rw [WMStart, dt.relMap_one hpl hdef hacc p₀ e hws (R := Language.wmStart)
    (φ := fun t => dt.startF p₀ t) rfl, dt.realize_startF e p₀ t]
  change _ ↔ ((t, u) : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) =
    (PfpTag.phase p₀, pad e.zero (stPl (W := dt.SlotIx) e.zero fun _ => e.zero))
  rw [dt.stPl_const e, dt.pad_const e]

include hws in
theorem relMap_blank (a : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMBlank a ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.IsBlank a := by
  obtain ⟨t, u⟩ := a
  rw [WMBlank, dt.relMap_one hpl hdef hacc p₀ e hws (R := Language.wmBlank)
    (φ := fun t => dt.blankF t) rfl, dt.realize_blankF e t]
  change _ ↔ ((t, u) : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) =
    (PfpTag.sym, pad e.zero (syPl (Q := dt.CtlIx) e.zero fun _ => e.zero))
  rw [dt.syPl_const e, dt.pad_const e]

include hws in
theorem relMap_acc (q : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMAcc q ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.IsAcc q := by
  obtain ⟨t, u⟩ := q
  rw [WMAcc, dt.relMap_one hpl hdef hacc p₀ e hws (R := Language.wmAcc)
    (φ := fun t => dt.accF hpl hacc t) rfl]
  match t with
  | .phase p => exact dt.realize_accF_phase hpl hacc e p
  | .ctrl r => exact Iff.rfl
  | .sym => exact Iff.rfl
  | .arg i => exact Iff.rfl

include hws in
theorem relMap_inp (x a : Univ e.α dt.RTag dt.PF dt.KIx dt.dd) :
    WMInp x a ↔ (dt.progFrom hpl e (rules e) p₀ (accept e)).table.Inp x a := by
  rw [WMInp, dt.relMap_two hpl hdef hacc p₀ e hws (R := Language.wmInp)
    (φ := fun t t' => dt.inpF hpl t t') rfl, dt.realize_inpF hpl e x.1 a.1]
  exact Iff.rfl

include hws in
/-- **The interpreted structure reads the program's table**: the eleven
obligations of `DescriptiveComplexity.Pfp.Table.Reads`, one per relation
symbol. Everything the run layer proves is proved under exactly this. -/
theorem reads_progFrom :
    (dt.progFrom hpl e (rules e) p₀ (accept e)).table.Reads where
  le := dt.relMap_le hpl hdef hacc p₀ e hws
  tr := dt.relMap_tr hpl hdef hacc p₀ e hws
  start := dt.relMap_start hpl hdef hacc p₀ e hws
  acc := dt.relMap_acc hpl hdef hacc p₀ e hws
  blank := dt.relMap_blank hpl hdef hacc p₀ e hws
  right := dt.relMap_right hpl hdef hacc p₀ e hws
  src := dt.relMap_src hpl hdef hacc p₀ e hws
  read := dt.relMap_read hpl hdef hacc p₀ e hws
  dst := dt.relMap_dst hpl hdef hacc p₀ e hws
  write := dt.relMap_write hpl hdef hacc p₀ e hws
  inp := dt.relMap_inp hpl hdef hacc p₀ e hws

end Interp

end PfpData

end Pfp

end DescriptiveComplexity
