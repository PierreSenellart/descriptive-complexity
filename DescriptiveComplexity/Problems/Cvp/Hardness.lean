/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Cvp.Hardness.Value
import DescriptiveComplexity.OrderedComposition

/-!
# CVP is `PTIME`-hard

The reduction, and the hardness it discharges. Three steps:

* the **certificate**, on the source side: a Horn instance fails to be a
  yes-instance exactly when it is not Horn or some goal clause has all its
  negative literals forced (`DescriptiveComplexity.CvpVal.not_hornSatisfiable_iff_glVal`),
  which is `DescriptiveComplexity.exists_goalClause` in one direction and
  `DescriptiveComplexity.forced_subset_model` in the other;
* the **circuit**, on the target side: the drawn circuit accepts exactly when
  the value of its output gate – the top of the goal chain – holds, which is
  the two halves of `DescriptiveComplexity.Problems.Cvp.Hardness.Value` put
  together;
* the **complement**, on the class side: what the reduction gives is hardness
  of `CVP` for `HORNSAT`ᶜ, and polynomial time is closed under complement
  (`DescriptiveComplexity.SigmaSOHornDefinable.compl`), so complementing the
  Horn discharge turns that into hardness for every problem of the class.

Reducing from the complement is what keeps the circuit monotone: a circuit
reporting *satisfiability* would have to negate the propagation, while one
reporting failure only has to detect a falsified goal clause.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc CvpDraw CvpVal

namespace CvpVal

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The certificate on the source side -/

omit [Nonempty A] in
/-- **A Horn instance fails exactly when the goal chain fires**: either it is
not Horn, or some goal clause has all its negative literals forced. -/
theorem not_hornSatisfiable_iff_glVal {M : A} (hM : ∀ a : A, a ≤ M) :
    ¬HornSatisfiable A ↔ GlVal M := by
  constructor
  · intro h
    by_cases hhorn : AtMostOnePositive A
    · have hunsat : ¬Satisfiable A := fun hsat => h ⟨hhorn, hsat⟩
      obtain ⟨c, hc, hneg, hnp⟩ := exists_goalClause hunsat
      exact Or.inr ⟨c, hM c, hc, hnp, hneg⟩
    · exact Or.inl hhorn
  · rintro (hhorn | ⟨c, -, hc, hnp, hneg⟩) h
    · exact hhorn h.1
    · obtain ⟨hhorn, ν, hν⟩ := h
      obtain ⟨x, hx⟩ := hν c hc
      rcases hx with ⟨hp, -⟩ | ⟨hn, hnv⟩
      · exact hnp x hp
      · exact hnv (forced_subset_model hhorn hν x (hneg x hn))

/-! ### What the drawn circuit accepts -/

/-- **The drawn circuit accepts exactly the failures of Horn satisfiability.**
The output gate is the top of the goal chain, so this is the two halves of the
evaluation read at that gate, against the certificate above. -/
theorem circuitAccepts_iff :
    CircuitAccepts (cvpInterp.Map A) ↔ ¬HornSatisfiable A := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := by
    obtain ⟨m, hm⟩ := Finite.exists_min (id : A → A)
    exact ⟨m, hm⟩
  obtain ⟨M, hM⟩ : ∃ M : A, ∀ a : A, a ≤ M := by
    obtain ⟨M, hM⟩ := Finite.exists_max (id : A → A)
    exact ⟨M, hM⟩
  rw [not_hornSatisfiable_iff_glVal hM]
  constructor
  · rintro ⟨p, hout, hval⟩
    obtain ⟨t, w⟩ := p
    obtain ⟨rfl, htop, -, -⟩ := (out_iff t w).mp hout
    have hgl : GlVal (w 0) := val_of_gateVal hm hM hval rfl
    rwa [le_antisymm (hM (w 0)) (htop M)] at hgl
  · intro hgl
    exact ⟨glPt m M, (out_iff .gl _).mpr ⟨rfl, fun a => hM a, fun a => hm a, fun a => hm a⟩,
      gateVal_gl hm hM M hgl⟩

end CvpVal

/-! ### The reduction and the completeness theorem -/

/-- **The reduction**: the complement of HORN-SAT ordered-FO-reduces to CVP,
by drawing the unit-propagation circuit inside the instance. -/
noncomputable def hornSatCompl_ordered_fo_reduction_cvp : HORNSATᶜ ≤ᶠᵒ[≤] CVP where
  Tag := CvpTag
  dim := 3
  toInterpretation := cvpInterp
  correct := fun _A _ _ _ _ => CvpVal.circuitAccepts_iff.symm

/-- **CVP is `PTIME`-hard**: every SO-Horn definable problem reduces to it.
The route is the Horn discharge applied to the *complement* of the problem,
complemented back – which is available because polynomial time is closed under
complement. -/
theorem cvp_PTIME_hard : PTIME.Hard CVP := by
  refine (hard_PTIME_iff CVP).mpr fun Q hQ => ?_
  obtain ⟨f⟩ := hornSat_hard_of_sigmaSOHornDefinable Qᶜ hQ.compl
  exact ⟨((f.compl.congrSource fun A _ _ => not_not).trans
    hornSatCompl_ordered_fo_reduction_cvp).toRel⟩

end DescriptiveComplexity
