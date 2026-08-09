/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Defs
import DescriptiveComplexity.Exponential.Order

/-!
# What the promises of a wide machine come to

`DescriptiveComplexity.WideAccept` folds
`DescriptiveComplexity.TMData.WellFormed` into its yes-instances, and that
promise is about the machine's *universe* – the addresses – rather than about the
instance. This file discharges it: the promise holds exactly when the instance
itself is well formed (`DescriptiveComplexity.wideData_wellFormed_iff`), namely
when

* its order `wmLe` is linear,
* its input is functional, and
* it has exactly one blank symbol.

The same holds of the determinism promise
(`DescriptiveComplexity.wideData_deterministic_iff`), which is what lets the
deterministic side of EXPSPACE be proved hard and the nondeterministic one
inherit it.

Nothing is asked of the addresses, which is the point: the binary-number order a
linear order induces on the subsets of a finite set is linear
(`DescriptiveComplexity.isLinOrd_wmSetLe`), and it is inherited from
`DescriptiveComplexity.setLinearOrder` rather than proved again – the same
reduction `DescriptiveComplexity.Exponential.Order` makes for the order on an
expanded universe.

This is the lemma a *reduction into* a wide machine will need: an interpretation
writing a wide machine down owes only three first-order conditions about the
instance it draws, and none about its power set.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section WellFormed

variable {A : Type} [Language.wide.Structure A]

/-- **Well-formedness of a wide-machine instance**: a linear order, a functional
input, and exactly one blank. Every conjunct is first-order over the
instance. -/
def WideWF (A : Type) [Language.wide.Structure A] : Prop :=
  IsLinOrd (WMLe (A := A)) ∧ (∀ x a b : A, WMInp x a → WMInp x b → a = b) ∧
    (∃ b : A, WMBlank b) ∧ ∀ a b : A, WMBlank a → WMBlank b → a = b

omit [Language.wide.Structure A] in
/-- **The machine has `2ⁿ` positions.** The step bound of
`DescriptiveComplexity.WideAccept` counts the positions, as every bound in this
library does, and the positions are the addresses – the subsets of the instance.
So the bound is exponential by construction and no arithmetic appears in the
definition, exactly as `DescriptiveComplexity.NTMAccept`'s bound is `n` by
construction. -/
theorem card_wpPosn [Finite A] :
    Nat.card {p : WPoint A // wpPosn p} = 2 ^ Nat.card A := by
  classical
  have he : {p : WPoint A // wpPosn p} ≃ (A → Prop) :=
    { toFun := fun p =>
        match p with
        | ⟨Sum.inl s, _⟩ => s
        | ⟨Sum.inr _, h⟩ => False.elim h
      invFun := fun s => ⟨Sum.inl s, trivial⟩
      left_inv := by
        rintro ⟨s | x, h⟩
        · rfl
        · exact False.elim h
      right_inv := fun _ => rfl }
  rw [Nat.card_congr he, Nat.card_fun]
  congr 1
  refine Nat.card_eq_two_iff.mpr ⟨True, False, by simp, Set.eq_univ_of_forall fun p => ?_⟩
  by_cases h : p <;> simp [h, eq_true, eq_false]

/-- **Determinism of a wide-machine instance**: one start state, at most one
transition per state and symbol read, and functional destination and written
symbol. Every conjunct is first-order over the instance, exactly as for
`DescriptiveComplexity.TMData.Deterministic` itself. -/
def WideDet (A : Type) [Language.wide.Structure A] : Prop :=
  (∀ q q' : A, WMStart q → WMStart q' → q = q') ∧
    (∀ τ τ' q a : A, WMTr τ → WMTr τ' → WMSrc τ q → WMSrc τ' q → WMRead τ a →
      WMRead τ' a → τ = τ') ∧
    (∀ τ q q' : A, WMDst τ q → WMDst τ q' → q = q') ∧
    ∀ τ a a' : A, WMWrite τ a → WMWrite τ a' → a = a'

/-- **A wide machine is deterministic exactly when its instance is.** The
addresses contribute nothing – no address is a state, a symbol or a transition –
so the promise `DescriptiveComplexity.DWideAcceptSpace` folds in is again a
first-order condition about the instance, which is what lets the deterministic
side be proved hard and the nondeterministic one inherit it. -/
theorem wideData_deterministic_iff : (wideData A).Deterministic ↔ WideDet A := by
  constructor
  · rintro ⟨hstart, huniq, hdst, hwrite⟩
    refine ⟨fun q q' hq hq' => Sum.inr_injective (hstart (Sum.inr q) (Sum.inr q') hq hq'),
      fun τ τ' q a h1 h2 h3 h4 h5 h6 => Sum.inr_injective
        (huniq (Sum.inr τ) (Sum.inr τ') (Sum.inr q) (Sum.inr a) h1 h2 h3 h4 h5 h6),
      fun τ q q' h1 h2 => Sum.inr_injective (hdst (Sum.inr τ) (Sum.inr q) (Sum.inr q') h1 h2),
      fun τ a a' h1 h2 => Sum.inr_injective (hwrite (Sum.inr τ) (Sum.inr a) (Sum.inr a') h1 h2)⟩
  · rintro ⟨hstart, huniq, hdst, hwrite⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (s | q) (t | q') h1 h2 <;>
        first
          | exact False.elim h1
          | exact False.elim h2
          | exact congrArg Sum.inr (hstart q q' h1 h2)
    · rintro (s | τ) (s' | τ') (t | q) (t' | a) h1 h2 h3 h4 h5 h6 <;>
        first
          | exact False.elim h1
          | exact False.elim h2
          | exact False.elim h3
          | exact False.elim h4
          | exact False.elim h5
          | exact False.elim h6
          | exact congrArg Sum.inr (huniq τ τ' q a h1 h2 h3 h4 h5 h6)
    · rintro (s | τ) (t | q) (t' | q') h1 h2 <;>
        first
          | exact False.elim h1
          | exact False.elim h2
          | exact congrArg Sum.inr (hdst τ q q' h1 h2)
    · rintro (s | τ) (t | a) (t' | a') h1 h2 <;>
        first
          | exact False.elim h1
          | exact False.elim h2
          | exact congrArg Sum.inr (hwrite τ a a' h1 h2)

/-- Two elements cutting the same initial segment are equal. -/
theorem eq_of_wmDown (h : IsLinOrd (WMLe (A := A))) {s : A → Prop} {x y : A}
    (hx : WMDown WMLe s x) (hy : WMDown WMLe s y) : x = y := by
  refine h.2.2.1 x y ((hy x).mp ((hx x).mpr (h.1 x))) ((hx y).mp ((hy y).mpr (h.1 y)))

/-- **The binary-number order on addresses is a linear order**, inherited from
`DescriptiveComplexity.setLinearOrder`: the comparison is the same, so
`DescriptiveComplexity.isLinOrd_of_key` at the identity key transports the
axioms. Stated at an arbitrary order relation, since everything the address
layer says is independent of where the order comes from. -/
theorem isLinOrd_wmSetLe {α : Type} [Finite α] {Le : α → α → Prop} (h : IsLinOrd Le) :
    IsLinOrd (WMSetLe Le) := by
  letI := h.toLinearOrder
  have hkey : ∀ s t : α → Prop, WMSetLe Le s t ↔ (setLinearOrder α).le s t := by
    intro s t
    rw [show ((setLinearOrder α).le s t ↔ _) from
      @le_iff_lt_or_eq _ (setLinearOrder α).toPartialOrder s t, setLinearOrder_lt_iff,
      WMSetLe]
    constructor
    · rintro (hag | ⟨x, hb, hs, ht⟩)
      · exact Or.inr (funext fun z => propext (hag z))
      · exact Or.inl ⟨x, fun j hj => hb j hj, hs, ht⟩
    · rintro (⟨x, hb, hs, ht⟩ | rfl)
      · exact Or.inr ⟨x, fun j hj => hb j hj, hs, ht⟩
      · exact Or.inl fun _ => Iff.rfl
  have hK : IsLinOrd (setLinearOrder α).le :=
    ⟨fun a => (setLinearOrder α).le_refl a, fun a b c => (setLinearOrder α).le_trans a b c,
      fun a b => (setLinearOrder α).le_antisymm a b, fun a b => (setLinearOrder α).le_total a b⟩
  exact isLinOrd_of_key hK id Function.injective_id hkey

/-- **The order of a wide machine is linear** as soon as the instance's is: the
addresses are ordered as binary numbers, the control elements as in the
instance, and the addresses come first. -/
theorem isLinOrd_wpLe [Finite A] (h : IsLinOrd (WMLe (A := A))) :
    IsLinOrd (wpLe (A := A)) := by
  have hs := isLinOrd_wmSetLe h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (s | x)
    · exact hs.1 s
    · exact h.1 x
  · rintro (s | x) (t | y) (u | z) h1 h2 <;>
      first
        | exact trivial
        | exact False.elim h1
        | exact False.elim h2
        | exact hs.2.1 _ _ _ h1 h2
        | exact h.2.1 _ _ _ h1 h2
  · rintro (s | x) (t | y) h1 h2 <;>
      first
        | exact False.elim h1
        | exact False.elim h2
        | exact congrArg Sum.inl (hs.2.2.1 _ _ h1 h2)
        | exact congrArg Sum.inr (h.2.2.1 _ _ h1 h2)
  · rintro (s | x) (t | y)
    · exact hs.2.2.2 s t
    · exact Or.inl trivial
    · exact Or.inr trivial
    · exact h.2.2.2 x y

/-- **The promise of a wide machine is a promise about its instance**: the
universe of addresses contributes nothing, so an interpretation writing a wide
machine down owes three first-order conditions and no more. -/
theorem wideData_wellFormed_iff [Finite A] : (wideData A).WellFormed ↔ WideWF A := by
  constructor
  · rintro ⟨hlin, -, hinp, ⟨b, hb⟩, huniq⟩
    have h1 : IsLinOrd (WMLe (A := A)) :=
      ⟨fun x => hlin.1 (Sum.inr x),
        fun x y z h1 h2 => hlin.2.1 (Sum.inr x) (Sum.inr y) (Sum.inr z) h1 h2,
        fun x y h1 h2 => Sum.inr_injective (hlin.2.2.1 (Sum.inr x) (Sum.inr y) h1 h2),
        fun x y => hlin.2.2.2 (Sum.inr x) (Sum.inr y)⟩
    refine ⟨h1, fun x a c ha hc => ?_, ?_, fun a c ha hc => ?_⟩
    · have hd : WMDown (WMLe (A := A)) (fun z => WMLe z x) x := fun _ => Iff.rfl
      exact Sum.inr_injective (hinp (Sum.inl fun z => WMLe z x) (Sum.inr a) (Sum.inr c)
        ⟨x, hd, ha⟩ ⟨x, hd, hc⟩)
    · match b with
      | Sum.inl s => exact False.elim hb
      | Sum.inr y => exact ⟨y, hb⟩
    · exact Sum.inr_injective (huniq (Sum.inr a) (Sum.inr c) ha hc)
  · rintro ⟨hlin, hinp, ⟨b, hb⟩, huniq⟩
    refine ⟨isLinOrd_wpLe hlin, ⟨Sum.inl fun _ => False, trivial⟩, ?_, ⟨Sum.inr b, hb⟩, ?_⟩
    · rintro (s | x) (a | a) (c | c) h1 h2 <;>
        first
          | exact False.elim h1
          | exact False.elim h2
          | skip
      obtain ⟨u, hu, hau⟩ := h1
      obtain ⟨v, hv, hcv⟩ := h2
      exact congrArg Sum.inr (hinp u a c hau ((eq_of_wmDown hlin hv hu) ▸ hcv))
    · rintro (s | x) (t | y) h1 h2 <;>
        first
          | exact False.elim h1
          | exact False.elim h2
          | exact congrArg Sum.inr (huniq x y h1 h2)

end WellFormed

end DescriptiveComplexity
