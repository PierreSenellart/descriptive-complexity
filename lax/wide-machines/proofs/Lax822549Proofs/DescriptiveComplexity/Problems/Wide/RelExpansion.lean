/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RelExp
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (replicate)
end Lax904597.SecondOrder.SOBlock

/-!
# The expansion, relativized to the marked part

The doubled universe of `DescriptiveComplexity.Problems.Wide.Double` is never a
singleton, which is what the machine needs, but it is no longer the instance.
`DescriptiveComplexity.Draw.relExp` repairs that on the expansion's side: every
sentence of the expansion is renamed and relativized to the mark, and every
block assignment is required to be **supported** – to hold only of marked tuples
– so that a point of the relativized expansion over the doubled universe is a
point of the original expansion over the instance.

One tag is added. `FirstOrder.Language.ExpExpansion` requires its domain
sentence to be satisfiable at *every* structure, including ones with no marked
part at all, where a relativized sentence has nothing to be about; the tag
`none` is the point that exists exactly there, and over a doubled universe – one
that always has a marked part – it contributes nothing.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### Two sentences about a structure with no marked part -/

section Fallback

variable (L : Language.{0, 0}) [L.IsRelational] (B : Lax904597.SecondOrder.SOBlock)

/-- **No element is marked**, as a sentence. -/
noncomputable def noOldSentence : (((newLang L).sum Language.order).sum B.lang).Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.BoundedFormula.not
        (FirstOrder.Language.Relations.formula₁ (oldGuard (L := L) B) (FirstOrder.Language.Term.var (Sum.inr 0))))

open Classical in
/-- **Every relation variable of the block is empty**, as a sentence. -/
noncomputable def emptyBlocksSentence :
    (((newLang L).sum Language.order).sum B.lang).Sentence :=
  letI := Fintype.ofFinite B.ι
  listInf ((Finset.univ : Finset B.ι).toList.map fun i =>
    Formula.iAlls (Fin (B.arity i))
      (∼(Relations.formula (blkSym L B i) fun k => Term.var (Sum.inr k))))

variable {L B}

variable {M : Type} [(newLang L).Structure M] [LinearOrder M]

omit [L.IsRelational] in
theorem realize_noOldSentence (ρ : B.Assignment M) :
    @Sentence.Realize _ M (B.structure₁ ρ) (noOldSentence L B) ↔
      ∀ x : M, ¬RelMap (oldNewSym L) ![x] := by
  let := B.structure₁ (L := (newLang L).sum Language.order) ρ
  rw [noOldSentence]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

omit [L.IsRelational] in
theorem realize_emptyBlocksSentence (ρ : B.Assignment M) :
    @Sentence.Realize _ M (B.structure₁ ρ) (emptyBlocksSentence L B) ↔
      ∀ (i : B.ι) (w : Fin (B.arity i) → M), ¬ρ i w := by
  classical
  let := Fintype.ofFinite B.ι
  let := B.structure₁ (L := (newLang L).sum Language.order) ρ
  rw [emptyBlocksSentence]
  simp only [Sentence.Realize, realize_listInf, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and, forall_exists_index]
  constructor
  · intro h i w hw
    have hi := h _ i rfl
    rw [Formula.realize_iAlls] at hi
    exact (Formula.realize_not.mp (hi w)) (by
      rw [Formula.realize_rel]
      exact hw)
  · rintro h ψ i rfl
    rw [Formula.realize_iAlls]
    intro w
    rw [Formula.realize_not, Formula.realize_rel]
    exact h i _

end Fallback

/-! ### The relativized expansion -/

section RelExpansion

variable {L : Language.{0, 0}} [L.IsRelational]

open Classical in
/-- **The expansion, relativized to the marked part**: the same block and the
same expanded vocabulary, every sentence renamed and relativized, every
assignment required to be supported, and one extra tag for the structures with
no marked part. -/
noncomputable def relExp (X : Lax480241.Expansions.ExpExpansion L) : Lax480241.Expansions.ExpExpansion (newLang L) where
  Tag := Option X.Tag
  B := X.B
  E := X.E
  dom t :=
    match t with
    | some t =>
      relativizeTo (oldGuard (L := L) X.B) ((newBlockLHom X.B).onSentence (X.dom t)) ⊓
        suppSentence L X.B
    | none => noOldSentence L X.B ⊓ emptyBlocksSentence L X.B
  relSentence {n} r τ :=
    if h : ∃ σ : Fin n → X.Tag, ∀ i, τ i = some (σ i) then
      relativizeTo (oldGuard (L := L) (X.B.replicate n))
        ((newBlockLHom (X.B.replicate n)).onSentence (X.relSentence r h.choose))
    else ⊥
  dom_nonempty := by
    classical
    intro M _ _ _ _
    by_cases hne : Nonempty (MarkPart L M)
    · obtain ⟨t, ρ₀, h⟩ := X.dom_nonempty (MarkPart L M)
      refine ⟨some t, extAssignM X.B ρ₀, ?_⟩
      let := X.B.structure₁ (L := (newLang L).sum Language.order) (extAssignM X.B ρ₀)
      refine Formula.realize_inf.mpr ⟨?_, ?_⟩
      · exact (realize_relOldMark X.B ρ₀ (X.dom t)).mpr h
      · exact (realize_suppSentence X.B (extAssignM X.B ρ₀)).mpr
          (supported_extAssignM X.B ρ₀)
    · refine ⟨none, (fun _ _ => False), ?_⟩
      let := X.B.structure₁ (L := (newLang L).sum Language.order)
        (show X.B.Assignment M from fun _ _ => False)
      refine Formula.realize_inf.mpr ⟨?_, ?_⟩
      · exact (realize_noOldSentence (fun _ _ => False)).mpr fun x hx =>
          hne ⟨MarkPart.mk x hx⟩
      · exact (realize_emptyBlocksSentence (fun _ _ => False)).mpr fun _ _ h => h

end RelExpansion

end Draw

end Lax822549Proofs.DescriptiveComplexity


