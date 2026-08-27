/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureReductionDet
import DescriptiveComplexity.FixedPointReductionStrict

/-!
# FO(TC) reductions are strictly stronger than first-order ones

`DescriptiveComplexity.FOReduction.toTC` embeds every first-order reduction
into the FO(TC) ones. The embedding is **strict**, and unconditionally:
`DescriptiveComplexity.EVEN` reduces in FO(≤, TC) to a problem it does not
reduce to first-order at all
(`DescriptiveComplexity.exists_tcReduction_not_orderedReduction`).

The witness is the one of `DescriptiveComplexity.FixedPointReductionStrict`,
now at the weakest reduction notion that can carry it: the target is
`DescriptiveComplexity.NONEMPTYMARK`, “some element is marked”, which is
first-order definable, so nothing first-order-reducing to it can escape
first-order logic – and EVEN does
(`DescriptiveComplexity.even_not_foDefinable`). The reduction marks every
element when the universe is even and none when it is odd, and the walk that
decides which is the one already in the catalog
(`DescriptiveComplexity.evenSpec`: step to the successor, flip a bit), read as
an atom through `DescriptiveComplexity.TCSpec.acceptsF`.

Since an FO(TC) reduction is an FO(LFP) reduction, this strengthens the
separation of `DescriptiveComplexity.FixedPointReductionStrict`: the gap
between `≤ᶠᵒ[≤]` and `≤ˡᶠᵖ` opens already at the logarithmic-space notion, and
needs neither a fixed point nor a hard problem – only a walk along the order.

The last section sharpens it once more. The parity walk is *functional* – the
mode flips and the immediate successor is unique
(`DescriptiveComplexity.evenSpec_functional`) – so it survives determinization,
and the separation holds already for the **deterministic** logarithmic-space
reductions (`DescriptiveComplexity.exists_dtcReduction_not_orderedReduction`),
which is the reduction notion of the textbooks. The same observation gives EVEN
its FO(DTC) definition (`DescriptiveComplexity.even_dtcDefinable`), and so its
membership in `DescriptiveComplexity.LOGSPACE` by the logic rather than through
the bit-level stack.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The interpretation -/

/-- The FO(TC) interpretation reducing EVEN to `DescriptiveComplexity.NONEMPTYMARK`:
the universe unchanged, every element marked exactly when the parity walk
accepts. -/
noncomputable def evenMarkTCInterp :
    TCInterpretation (Language.empty.sum Language.order) Language.markedSet Unit 1 where
  fam := evenSpec.toFamily
  toRel :=
    { relFormula := fun {_n} _R _t => evenSpec.acceptsF.relabel fun z => z.elim
      domFormula := fun _ => ⊤ }

variable (A : Type) [Language.empty.Structure A] [LinearOrder A]

/-- Every point of the interpreted universe is marked exactly when the parity
walk accepts. -/
theorem relMap_evenMarkTCInterp (xs : Fin 1 → evenMarkTCInterp.Map A) :
    RelMap (M := evenMarkTCInterp.Map A) Language.markedSetMark xs ↔ evenSpec.Accepts A := by
  let : ((Language.empty.sum Language.order).sum evenMarkTCInterp.fam.block.lang).Structure A :=
    evenMarkTCInterp.expStructure A
  let : ((Language.empty.sum Language.order).sum evenSpec.toFamily.block.lang).Structure A :=
    evenMarkTCInterp.expStructure A
  refine Iff.trans (Formula.realize_relabel (g := fun z : Empty => z.elim)) ?_
  refine Iff.trans (iff_of_eq (congrArg (Formula.Realize evenSpec.acceptsF)
    (Subsingleton.elim _ (default : Empty → A)))) ?_
  exact evenSpec.realize_acceptsF

/-- The interpreted universe is all of the base universe: the domain formula
is `⊤`. -/
theorem evenMarkTCInterp_nonempty [Nonempty A] : Nonempty (evenMarkTCInterp.Map A) :=
  letI := evenMarkTCInterp.expStructure A
  ⟨⟨((), fun _ => Classical.arbitrary A), Formula.realize_top.mpr trivial⟩⟩

/-! ### The reduction and the separation -/

/-- **EVEN FO(TC)-reduces to NONEMPTYMARK**: one walk along the order decides
the parity of the universe, and the reduction marks everything or nothing
accordingly. -/
theorem even_tcReduction_nonemptyMark : Nonempty (EVEN ≤ᵗᶜ NONEMPTYMARK) := by
  refine ⟨{ Tag := Unit
            dim := 1
            toInterpretation := evenMarkTCInterp
            map_nonempty := fun A _ _ _ _ => evenMarkTCInterp_nonempty A
            correct := fun A _ _ _ _ => ?_ }⟩
  have hne : Nonempty (evenMarkTCInterp.Map A) := evenMarkTCInterp_nonempty A
  refine Iff.trans (accepts_evenSpec_iff (A := A)).symm ⟨fun hacc => ?_, fun ⟨x, hx⟩ => ?_⟩
  · exact ⟨hne.some, (relMap_evenMarkTCInterp A _).mpr hacc⟩
  · exact (relMap_evenMarkTCInterp A _).mp hx

/-- **FO(TC) reductions are strictly stronger than first-order ones**, with
EVEN as the witness: it reduces to `DescriptiveComplexity.NONEMPTYMARK` in
FO(≤, TC) and by no first-order reduction. No complexity-theoretic assumption
enters either half. -/
theorem exists_tcReduction_not_orderedReduction :
    ∃ (L : Language.{0, 0}) (_ : L.IsRelational) (Q : DecisionProblem L),
      Nonempty (EVEN ≤ᵗᶜ Q) ∧ IsEmpty (EVEN ≤ᶠᵒ[≤] Q) :=
  ⟨Language.markedSet, inferInstance, NONEMPTYMARK,
    even_tcReduction_nonemptyMark, even_not_orderedReduction_nonemptyMark⟩

/-! ### The walk is deterministic, so the separation is one notion lower -/

section Deterministic

/-- **The parity walk is functional**: a node has at most one successor – the
mode flips, and an element covers at most one element in a linear order. -/
theorem evenSpec_functional : evenSpec.Functional A := by
  intro a b c h₁ h₂
  obtain ⟨hm₁, hc₁⟩ := (step_evenSpec_iff a.1 b.1 a.2 b.2).mp h₁
  obtain ⟨hm₂, hc₂⟩ := (step_evenSpec_iff a.1 c.1 a.2 c.2).mp h₂
  have key : ∀ u v w : Fin 1 → A, u 0 ⋖ v 0 → u 0 ⋖ w 0 → v = w := by
    intro u v w huv huw
    have h0 : v 0 = w 0 := by
      rcases lt_trichotomy (v 0) (w 0) with h | h | h
      · exact absurd h (huw.2 huv.1)
      · exact h
      · exact absurd h (huv.2 huw.1)
    funext i
    rw [Subsingleton.elim i 0]
    exact h0
  exact Prod.ext_iff.mpr ⟨hm₁.trans hm₂.symm,
    key (fun i => a.2 i) (fun i => b.2 i) (fun i => c.2 i) hc₁ hc₂⟩

/-- Determinization does not change what the parity walk reaches. -/
theorem reach_det_evenSpec_iff (a b : evenSpec.Node A) :
    evenSpec.det.Reach a b ↔ evenSpec.Reach a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih =>
      exact ih.tail ((TCSpec.det_step_of_functional (evenSpec_functional A) c d).mp hcd)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih =>
      exact ih.tail ((TCSpec.det_step_of_functional (evenSpec_functional A) c d).mpr hcd)

/-- The deterministic reading of the parity walk accepts exactly when the walk
does: determinization changes nothing on a functional walk. -/
theorem accepts_det_evenSpec_iff : evenSpec.det.Accepts A ↔ evenSpec.Accepts A :=
  ⟨fun ⟨u, v, hu, hv, huv⟩ => ⟨u, v, hu, hv, (reach_det_evenSpec_iff A u v).mp huv⟩,
    fun ⟨u, v, hu, hv, huv⟩ => ⟨u, v, hu, hv, (reach_det_evenSpec_iff A u v).mpr huv⟩⟩

/-- **EVEN is FO(DTC) definable**: the parity walk is deterministic, so the
walk that defines EVEN survives Immerman's determinization. Hence EVEN is in
`DescriptiveComplexity.LOGSPACE` by the logic, the bit-level route
(`DescriptiveComplexity.even_mem_LOGSPACE_bit`) being a second proof. -/
theorem even_dtcDefinable : DTCDefinable EVEN := by
  refine ⟨evenSpec, fun A _ _ _ _ => ?_⟩
  exact (accepts_evenSpec_iff (A := A)).symm.trans (accepts_det_evenSpec_iff A).symm

/-- The parity walk, as a parameterized walk, is functional too. -/
theorem evenSpec_toParam_functional : (evenSpec.toParam).Functional A := by
  intro z a b c hb hc
  exact evenSpec_functional A a b c ((evenSpec.stepAt_toParam z a b).mp hb)
    ((evenSpec.stepAt_toParam z a c).mp hc)

/-- The one-element family of the parity walk is functional. -/
theorem evenSpec_toFamily_functional : (evenSpec.toFamily).Functional A :=
  fun _ => evenSpec_toParam_functional A

/-- Every point of the interpreted universe is marked exactly when the
*determinized* parity walk accepts – which, the walk being functional, is when
the universe is even. -/
theorem relMap_evenMarkDetInterp
    (xs : Fin 1 → (TCInterpretation.mk evenSpec.toFamily.det evenMarkTCInterp.toRel).Map A) :
    RelMap (M := (TCInterpretation.mk evenSpec.toFamily.det evenMarkTCInterp.toRel).Map A)
      Language.markedSetMark xs ↔ evenSpec.Accepts A := by
  let : ((Language.empty.sum Language.order).sum
      (TCInterpretation.mk evenSpec.toFamily.det evenMarkTCInterp.toRel).fam.block.lang).Structure
      A := (TCInterpretation.mk evenSpec.toFamily.det evenMarkTCInterp.toRel).expStructure A
  let : ((Language.empty.sum Language.order).sum evenSpec.toFamily.block.lang).Structure A :=
    (TCInterpretation.mk evenSpec.toFamily.det evenMarkTCInterp.toRel).expStructure A
  refine Iff.trans (Formula.realize_relabel (g := fun z : Empty => z.elim)) ?_
  refine Iff.trans (iff_of_eq (congrArg (Formula.Realize evenSpec.acceptsF)
    (Subsingleton.elim _ (default : Empty → A)))) ?_
  exact evenSpec.realize_acceptsF_det (evenSpec_toFamily_functional A)

/-- **EVEN reduces to NONEMPTYMARK by a deterministic logarithmic-space
reduction**: the walk that decides the parity of the universe follows, from
each element, its unique successor. -/
theorem even_dtcReduction_nonemptyMark : Nonempty (EVEN ≤ᵈᵗᶜ NONEMPTYMARK) := by
  refine ⟨{ Tag := Unit
            dim := 1
            fam := evenSpec.toFamily
            toRel := evenMarkTCInterp.toRel
            map_nonempty := fun A _ _ _ _ => ?_
            correct := fun A _ _ _ _ => ?_ }⟩
  · let := (TCInterpretation.mk evenSpec.toFamily.det evenMarkTCInterp.toRel).expStructure A
    exact ⟨⟨((), fun _ => Classical.arbitrary A), Formula.realize_top.mpr trivial⟩⟩
  · have hne : Nonempty ((TCInterpretation.mk evenSpec.toFamily.det
        evenMarkTCInterp.toRel).Map A) := by
      let := (TCInterpretation.mk evenSpec.toFamily.det evenMarkTCInterp.toRel).expStructure A
      exact ⟨⟨((), fun _ => Classical.arbitrary A), Formula.realize_top.mpr trivial⟩⟩
    refine Iff.trans (accepts_evenSpec_iff (A := A)).symm ⟨fun hacc => ?_, fun ⟨x, hx⟩ => ?_⟩
    · exact ⟨hne.some, (relMap_evenMarkDetInterp A _).mpr hacc⟩
    · exact (relMap_evenMarkDetInterp A _).mp hx

/-- **Deterministic logarithmic-space reductions are already strictly stronger
than first-order ones**: EVEN reduces to `DescriptiveComplexity.NONEMPTYMARK`
in FO(≤, DTC) – one walk that never has a choice – and by no first-order
reduction. This is the sharpest form of the separation: the notion on the left
is the many-one reduction of the textbooks. -/
theorem exists_dtcReduction_not_orderedReduction :
    ∃ (L : Language.{0, 0}) (_ : L.IsRelational) (Q : DecisionProblem L),
      Nonempty (EVEN ≤ᵈᵗᶜ Q) ∧ IsEmpty (EVEN ≤ᶠᵒ[≤] Q) :=
  ⟨Language.markedSet, inferInstance, NONEMPTYMARK,
    even_dtcReduction_nonemptyMark, even_not_orderedReduction_nonemptyMark⟩

end Deterministic

end DescriptiveComplexity
