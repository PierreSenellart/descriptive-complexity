/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointOrderTransfer
import DescriptiveComplexity.FixedPointInflationaryLFP
import DescriptiveComplexity.FixedPointPartialMachine
import DescriptiveComplexity.FixedPointStratify
import DescriptiveComplexity.Invariant.Backward

/-!
# The Abiteboul–Vianu theorem

**The inflationary and partial fixed-point logics have the same expressive
power on unordered finite structures exactly when `PTIME = PSPACE`**
([Abiteboul–Vianu 1991][abiteboul1991generic];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 7):
`DescriptiveComplexity.ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace`.
The two classes `PTIME` and `PSPACE` are the library's logically defined
ones; the machine-model reading is supplied beside them by
`DescriptiveComplexity.dtmAccept_PTIME_complete` and
`DescriptiveComplexity.dtmAcceptSpace_PSPACE_complete`.

Right to left, from the coincidence of the classes: a `PSPACE` problem is
FO(≤, PFP) definable (`DescriptiveComplexity.pfpDefinable_iff_mem_PSPACE`),
its order relativization is order-free FO(PFP) definable
(`DescriptiveComplexity.FixedPointOrderTransfer`), hence by hypothesis
order-free FO(IFP) definable, so the problem is FO(≤, IFP) definable and in
`PTIME` (`DescriptiveComplexity.ifpDefinable_iff_mem_PTIME`).

Left to right, through the invariant structure
(`DescriptiveComplexity.Invariant`): an order-free FO(PFP) definition has a
`k`-variable budget, so its stages are `≡ᵏ`-invariant and its whole
computation runs on the invariant structure `Iᵏ A`
(`DescriptiveComplexity.StepDef.pfpHolds_invStepDef`) – a problem over the
invariant vocabulary, order-free FO(PFP) definable *by construction*, hence
in `PSPACE`, hence by the hypothesis in `PTIME`, hence FO(≤, IFP) definable.
On `Iᵏ A` the order is not given but *computed*: the canonical order on
`≡ᵏ`-classes is one inflationary induction
(`DescriptiveComplexity.Invariant.OrderDef`), and the ordered induction
delivered by the capture pulls back along the quotient map to an order-free
induction over `A` reading that computed order
(`DescriptiveComplexity.StepDef.ifpHolds_backStepDef`), the two glued into a
single induction by stratification
(`DescriptiveComplexity.StepDef.ifpHolds_stratify`). The theorem is stated
for the IFP-versus-PFP form, as in Abiteboul and Vianu's original;
Gurevich–Shelah (order-free LFP = IFP) is deliberately not involved.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **The easy inclusion between the two logically defined classes**:
`PTIME ⊆ PSPACE`, read on membership witnesses – an SO-Horn definition is an
FO(LFP) one, hence FO(≤, IFP), hence FO(≤, PFP), hence SO(TC). -/
theorem SigmaSOHornDefinable.sotcDefinable {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} (h : SigmaSOHornDefinable P) : SOTCDefinable P :=
  h.lfpDefinable.ifpDefinable.pfpDefinable.sotcDefinable

/-- **Abiteboul–Vianu, right to left**: if the order-free inflationary and
partial fixed-point logics have the same expressive power, then
`PTIME = PSPACE`. A PSPACE problem is FO(≤, PFP) definable; its ordered
relativization is order-free FO(PFP) definable, hence – by the hypothesis –
order-free FO(IFP) definable, so the problem itself is FO(≤, IFP) definable
and lands in PTIME. -/
theorem ptime_eq_pspace_of_ifpDefinableFree_eq_pfpDefinableFree
    (h : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
        IFPDefinableFree P ↔ PFPDefinableFree P) :
    PTIME = PSPACE := by
  have hMem : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
      SigmaSOHornDefinable P ↔ SOTCDefinable P := by
    intro L _ P
    constructor
    · exact SigmaSOHornDefinable.sotcDefinable
    · intro hp
      have hfree : PFPDefinableFree P.withOrder :=
        (pfpDefinable_iff_pfpDefinableFree_withOrder P).mp
          ((pfpDefinable_iff_sotcDefinable P).mpr hp)
      have hifp : IFPDefinable P :=
        (ifpDefinable_iff_ifpDefinableFree_withOrder P).mpr
          ((h P.withOrder).mpr hfree)
      exact (lfpDefinable_iff_sigmaSOHornDefinable P).mp
        ((ifpDefinable_iff_lfpDefinable P).mp hifp)
  refine ComplexityClass.ext (fun P => hMem P) fun P => ?_
  constructor
  · intro hh L' _ S hS L'' _ Q hQ
    exact hh S hS Q ((hMem Q).mpr hQ)
  · intro hh L' _ S hS L'' _ Q hQ
    exact hh S hS Q ((hMem Q).mp hQ)

/-- **Abiteboul–Vianu, left to right**: if `PTIME = PSPACE`, an order-free
FO(PFP) definable problem is order-free FO(IFP) definable. The whole
computation factors through the invariant structure `Iᵏ A`; there – ordered
by the canonical, itself inflationary-definable order on `≡ᵏ`-classes – the
hypothesis turns the PSPACE computation into a PTIME one, delivered as an
ordered inflationary induction, which pulls back along the quotient map and
is glued to the order's own induction by stratification. -/
theorem ifpDefinableFree_of_pfpDefinableFree_of_ptime_eq_pspace
    (hPP : PTIME = PSPACE) {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} (h : PFPDefinableFree P) : IFPDefinableFree P := by
  classical
  obtain ⟨d, hd⟩ := h
  obtain ⟨S, hSfin, hrels⟩ := d.exists_usesRels
  obtain ⟨k₀, hb₀⟩ := d.exists_varBound
  set k := max k₀ (qdepth d.out) with hk
  have hbound : d.VarBound k := hb₀.mono (le_max_left _ _)
  have houtd : qdepth d.out ≤ k := le_max_right _ _
  have harity : ∀ i, d.B.arity i ≤ k := fun i => hbound.arity_le i
  -- the induced problem on the invariant vocabulary
  set Q : DecisionProblem (invLang L k) :=
    ⟨fun I _ => (d.invStepDef k harity).PFPHolds I,
      fun e => (d.invStepDef k harity).pfpHolds_equiv e⟩ with hQdef
  have hQfree : PFPDefinableFree Q :=
    ⟨d.invStepDef k harity, fun I _ _ _ => Iff.rfl⟩
  -- `PTIME = PSPACE` turns its PSPACE membership into an ordered IFP definition
  have hQspace : Q ∈ PSPACE := mem_PSPACE_of_pfpDefinable hQfree.pfpDefinable
  have hQtime : SigmaSOHornDefinable Q := by
    rw [← hPP] at hQspace
    exact hQspace
  obtain ⟨e', he⟩ := (SigmaSOHornDefinable.lfpDefinable hQtime).ifpDefinable
  -- the order's induction, stratified under the pulled-back one
  refine ⟨(ordStepDef L k S hSfin).stratify (e'.backStepDef S), ?_⟩
  intro A instL hFin hNe
  -- the canonical order on classes, and the frozen order variable
  letI lo : LinearOrder (InvMap S k A) :=
    letI := bitVecLinearOrder L k S hSfin
    invLinearOrder (S := S) (colorAgree_atomColor L k S)
  have htp : toPebble ((ordStepDef L k S hSfin).inflLimit A) =
      (letI := bitVecLinearOrder L k S hSfin;
        OrdK (atomColor L k S (A := A))) :=
    toPebble_inflLimit_ordStepDef L k S hSfin
  have h1 : IncompRel (toPebble ((ordStepDef L k S hSfin).inflLimit A)) =
      EquivK (atomicAgreeOn S A k) := by
    rw [htp]
    letI := bitVecLinearOrder L k S hSfin
    rw [incompRel_ordK_eq, colorAgree_atomColor]
  have h2 : ∀ u v : Fin k → A,
      (toPebble ((ordStepDef L k S hSfin).inflLimit A) u v ∨
        EquivK (atomicAgreeOn S A k) u v) ↔
      (letI := lo; InvMap.mk S u ≤ InvMap.mk S v) := by
    intro u v
    rw [htp]
    letI := bitVecLinearOrder L k S hSfin
    exact (invLinearOrder_le_iff (S := S) (colorAgree_atomColor L k S) u v).symm
  -- the chain: stratified value = pulled-back value = value on `Iᵏ A`
  --   = the original partial value = `P A`
  have hstrat := (ordStepDef L k S hSfin).ifpHolds_stratify (e'.backStepDef S)
    (A := A)
  have hback := e'.ifpHolds_backStepDef
    (σ := (ordStepDef L k S hSfin).inflLimit A) lo h1 h2
  have hclass := he (InvMap S k A)
  have hforward : Q (InvMap S k A) ↔ P A :=
    (d.pfpHolds_invStepDef hbound hrels houtd).trans (hd A).symm
  exact (hforward.symm.trans hclass).trans (hback.symm.trans hstrat.symm)

/-- **The Abiteboul–Vianu theorem.** The inflationary and partial fixed-point
logics have the same expressive power on unordered finite structures exactly
when polynomial time and polynomial space coincide. -/
theorem ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace :
    (∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
        IFPDefinableFree P ↔ PFPDefinableFree P) ↔ PTIME = PSPACE := by
  constructor
  · exact ptime_eq_pspace_of_ifpDefinableFree_eq_pfpDefinableFree
  · intro hPP L _ P
    exact ⟨IFPDefinableFree.pfpDefinableFree,
      ifpDefinableFree_of_pfpDefinableFree_of_ptime_eq_pspace hPP⟩

end DescriptiveComplexity
