/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.FreeCopy
import Lax480241Proofs.DescriptiveComplexity.FixedPointPartialMachine
import Lax480241Proofs.DescriptiveComplexity.FixedPointStepRel
import Lax480241Proofs.DescriptiveComplexity.PSpaceHierarchy
import Lax480241Proofs.DescriptiveComplexity.Exponential.Classes
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241.SecondOrderFixedPoints
end Lax480241.SecondOrderFixedPoints

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity.SOTCDefinable
end Lax480241Proofs.DescriptiveComplexity.SOTCDefinable

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.SecondOrderFixedPoints (ExpExpansionFree SOPFPDefinable SOPFPDefinableFree)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (PFPDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# “Some copy answers yes” stays in polynomial space

`DescriptiveComplexity.ExpExpansion.someCls` reads the inner problem inside one
of the copies of an order-guessing expansion, and the copy is quantified
**existentially**. This file shows that the quantifier costs nothing at
`DescriptiveComplexity.PSPACE`, which is what makes the order-free reading of
`DescriptiveComplexity.EXPSPACE` possible. The copy is *guessed*, as a relation,
which is what a walk can do and a fixed point cannot; the deterministic class
pays for the same existential differently, by naming the copy with one of its
points (`DescriptiveComplexity.Exponential.FreeTime`).

Three closure properties of `DescriptiveComplexity.SOTCDefinable` do the work:

* **guessing a relation**: `DescriptiveComplexity.SOTCDefinable.exBlock` carries
  a guessed block in the state of the walk and never touches it again. The
  guessed block here is one unary relation variable
  (`DescriptiveComplexity.markBlock`), the copy;
* **conjoining a first-order condition**
  (`DescriptiveComplexity.SOTCDefinable.and_sentence`): the sentence goes into
  the source condition of the walk. It is what asks the guessed relation to be
  a copy;
* **restricting to a definable part**: reading the inner problem inside the
  guessed copy is a *relativized* ordered reduction to it, and membership is
  closed under those
  (`DescriptiveComplexity.PFPDefinable.of_relOrderedReduction`).
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Conjoining a first-order condition to a walk -/

/-- **SO(TC) is closed under conjoining a first-order sentence**: the sentence
goes into the source condition of the walk, which no step and no target can
undo. -/
theorem SOTCDefinable.and_sentence {F : Language.{0, 0}} [F.IsRelational]
    {P R : Lax904597.Problems.DecisionProblem F} (hR : Lax134656.SecondOrderTransitiveClosure.SOTCDefinable R) (γ : (F.sum Language.order).Sentence)
    (h : ∀ (M : Type) [F.Structure M] [LinearOrder M] [Finite M] [Nonempty M],
      P M ↔ (@Sentence.Realize _ M (Lax904597.Interpretations.sumOrderStructure F M) γ ∧ R M)) :
    Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P := by
  obtain ⟨spec, hspec⟩ := hR
  refine ⟨{ B := spec.B
            step := spec.step
            src := (LHom.sumInl : (F.sum Language.order) →ᴸ
              ((F.sum Language.order).sum spec.B.lang)).onSentence γ ⊓ spec.src
            tgt := spec.tgt }, ?_⟩
  intro M _ _ _ _
  have hsrc : ∀ ρ : spec.B.Assignment M,
      @Sentence.Realize _ M (spec.B.structure₁ (L := F.sum Language.order) ρ)
          ((LHom.sumInl : (F.sum Language.order) →ᴸ
            ((F.sum Language.order).sum spec.B.lang)).onSentence γ ⊓ spec.src) ↔
        (@Sentence.Realize _ M (Lax904597.Interpretations.sumOrderStructure F M) γ ∧ spec.IsSrc ρ) := by
    intro ρ
    let := spec.B.structure ρ
    refine Iff.trans Formula.realize_inf (and_congr ?_ Iff.rfl)
    exact LHom.realize_onSentence (M := M)
      (LHom.sumInl : (F.sum Language.order) →ᴸ ((F.sum Language.order).sum spec.B.lang)) γ
  rw [h M, hspec M]
  constructor
  · rintro ⟨hγ, ρ, σ, hρ, hσ, hreach⟩
    exact ⟨ρ, σ, (hsrc ρ).mpr ⟨hγ, hρ⟩, hσ, hreach⟩
  · rintro ⟨ρ, σ, hρ, hσ, hreach⟩
    obtain ⟨hγ, hρ'⟩ := (hsrc ρ).mp hρ
    exact ⟨hγ, ρ, σ, hρ', hσ, hreach⟩

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

export Lax480241Proofs.DescriptiveComplexity.SOTCDefinable (and_sentence)

end Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The block that guesses a copy -/

/-- The block of a single unary relation variable: the guessed copy. -/
def markBlock : Lax904597.SecondOrder.SOBlock where
  ι := Unit
  arity _ := 1

/-- The guessed copy, as a symbol of the block's vocabulary. -/
abbrev markBlockSym : markBlock.lang.Relations 1 := ⟨(), rfl⟩

/-- The guessed copy, as a symbol of the vocabulary the inner problem is read
over. -/
abbrev markSym (F : Language.{0, 0}) : (F.sum markBlock.lang).Relations 1 :=
  Sum.inr markBlockSym

section Marked

variable (F : Language.{0, 0}) (M : Type) [(F.sum markBlock.lang).Structure M]

/-- The marked part. -/
def markSet : Set M := {x | RelMap (markSym F) ![x]}

/-- The marked part when it is nonempty, and the whole structure when it is
not: a definable domain has to be inhabited, and nothing marks the guess as
nonempty. -/
def effSet : Set M := {x | x ∈ markSet F M ∨ ∀ y : M, y ∉ markSet F M}

variable {F M}

theorem effSet_nonempty [Nonempty M] : (effSet F M).Nonempty := by
  by_cases h : ∃ x : M, x ∈ markSet F M
  · obtain ⟨x, hx⟩ := h
    exact ⟨x, Or.inl hx⟩
  · obtain ⟨x⟩ := ‹Nonempty M›
    exact ⟨x, Or.inr fun y hy => h ⟨y, hy⟩⟩

theorem effSet_eq_markSet {x : M} (hx : x ∈ markSet F M) : effSet F M = markSet F M := by
  ext y
  exact ⟨fun h => h.elim id fun h' => (h' x hx).elim, Or.inl⟩

variable {N : Type} [(F.sum markBlock.lang).Structure N] (e : M ≃[F.sum markBlock.lang] N)

theorem mem_markSet_equiv (x : M) : x ∈ markSet F M ↔ e x ∈ markSet F N :=
  relMap_equiv₁ e (markSym F) x

theorem image_markSet : e '' markSet F M = markSet F N := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_markSet_equiv e x).mp hx
  · intro hy
    refine ⟨e.symm y, (mem_markSet_equiv e (e.symm y)).mpr ?_, e.apply_symm_apply y⟩
    rwa [e.apply_symm_apply]

theorem image_effSet : e '' effSet F M = effSet F N := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine hx.elim (fun h => Or.inl ((mem_markSet_equiv e x).mp h)) fun h => Or.inr fun z hz => ?_
    refine h (e.symm z) ((mem_markSet_equiv e (e.symm z)).mpr ?_)
    rwa [e.apply_symm_apply]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    refine hy.elim (fun h => Or.inl ((mem_markSet_equiv e (e.symm y)).mpr ?_))
      fun h => Or.inr fun z hz => h (e z) ((mem_markSet_equiv e z).mp hz)
    rwa [e.apply_symm_apply]

end Marked

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-! ### The inner problem, read in the marked copy -/

/-- The vocabulary the inner problem is read over: the order-guessing one, plus
the guessed copy. -/
noncomputable abbrev markLangOf : Language.{0, 0} := X.orderFree.E.sum markBlock.lang

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (markLangOf)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-- The order-guessing structure underlying a structure that also carries a
guessed copy. -/
@[instance_reducible]
noncomputable def markReduct (M : Type) [X.markLangOf.Structure M] : X.orderFree.E.Structure M :=
  (LHom.sumInl : X.orderFree.E →ᴸ X.markLangOf).reduct M

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (markReduct)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-- **The inner problem read in the marked part** – or in the whole structure
when nothing is marked, so that the part is never empty. -/
def effProblem (Q : Lax904597.Problems.DecisionProblem X.E) : Lax904597.Problems.DecisionProblem X.markLangOf where
  Holds M _ :=
    letI := X.markReduct M
    Q (X.clsPart (effSet X.orderFree.E M))
  iso_invariant := by
    intro M N _ _ e
    let := X.markReduct M
    let := X.markReduct N
    let e' := reductEquiv (LHom.sumInl : X.orderFree.E →ᴸ X.markLangOf) e
    have himg : (⇑e' '' effSet X.orderFree.E M) = effSet X.orderFree.E N := image_effSet e
    refine Iff.trans (Q.iso_invariant (clsPartEquiv X e' (effSet X.orderFree.E M))) ?_
    exact himg ▸ Iff.rfl

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (effProblem)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-- **The guessed copy is a copy, and the inner problem holds in it.** -/
def clsProblem (Q : Lax904597.Problems.DecisionProblem X.E) : Lax904597.Problems.DecisionProblem X.markLangOf where
  Holds M _ :=
    (letI := X.markReduct M; IsCls X (markSet X.orderFree.E M)) ∧ X.effProblem Q M
  iso_invariant := by
    intro M N _ _ e
    let := X.markReduct M
    let := X.markReduct N
    let e' := reductEquiv (LHom.sumInl : X.orderFree.E →ᴸ X.markLangOf) e
    have hm : (⇑e' '' markSet X.orderFree.E M) = markSet X.orderFree.E N := image_markSet e
    have hm' : (⇑e'.symm '' markSet X.orderFree.E N) = markSet X.orderFree.E M :=
      image_markSet e.symm
    refine and_congr ⟨fun h => ?_, fun h => ?_⟩ ((X.effProblem Q).iso_invariant e)
    · exact hm ▸ isCls_image X e' _ h
    · exact hm' ▸ isCls_image X e'.symm _ h

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (clsProblem)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-! ### Reading the inner problem inside the marked part, as a reduction

The marked part is a *definable* subset of the structure, so reading the inner
problem there is a relativized ordered reduction to it – and PSPACE membership
is closed under those. The domain formula is the marked part, widened to the
whole structure when nothing is marked, since a definable domain must be
inhabited. -/

section Reduction

/-- The mark, as a symbol of the source vocabulary of the reduction. -/
noncomputable abbrev markSymO : (X.markLangOf.sum Language.order).Relations 1 :=
  Sum.inl (markSym X.orderFree.E)

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (markSymO)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

/-- A relation of the original vocabulary, as a symbol of the source vocabulary
of the reduction. -/
noncomputable abbrev origSymO {n : ℕ} (r : X.E.Relations n) :
    (X.markLangOf.sum Language.order).Relations n :=
  Sum.inl (Sum.inl (X.origSym r))

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (origSymO)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

/-- The unary shift of a nullary symbol, as a symbol of the source vocabulary of
the reduction. -/
noncomputable abbrev nullSymO (s : X.E.Relations 0) :
    (X.markLangOf.sum Language.order).Relations 1 :=
  Sum.inl (Sum.inl (X.nullSym s))

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (nullSymO)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

/-- Nothing is marked. -/
noncomputable def noMarkF {α : Type} : (X.markLangOf.sum Language.order).Formula α :=
  Formula.iAlls (Fin 1) (∼(Relations.formula₁ (X.markSymO) (Term.var (Sum.inr 0))))

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (noMarkF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

/-- The domain of the reduction: the marked part, or everything when nothing is
marked. -/
noncomputable def effF {α : Type} (x : α) : (X.markLangOf.sum Language.order).Formula α :=
  Relations.formula₁ (X.markSymO) (Term.var x) ⊔ X.noMarkF

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (effF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

theorem realize_noMarkF {α : Type} (v : α → M) :
    (X.noMarkF (α := α)).Realize v ↔ ∀ y : M, y ∉ markSet X.orderFree.E M := by
  simp only [noMarkF, Formula.realize_iAlls, Formula.realize_not, Formula.realize_rel₁,
    Term.realize_var, Sum.elim_inr]
  exact ⟨fun h y hy => h (fun _ => y) hy, fun h i hi => h (i 0) hi⟩

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_noMarkF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

theorem realize_effF {α : Type} (v : α → M) (x : α) :
    (X.effF x).Realize v ↔ v x ∈ effSet X.orderFree.E M := by
  refine Iff.trans Formula.realize_sup ?_
  refine or_congr ?_ (realize_noMarkF v)
  exact Formula.realize_rel₁

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_effF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

/-- **The interpretation reading the original vocabulary inside the marked
part**: one point per element of the part, the relations read off the ambient
structure, a nullary symbol read off the unary shift at a point of the part. -/
noncomputable def effInterp : Lax904597.Relativized.RelFOInterpretation (X.markLangOf.sum Language.order) X.E Unit 1 where
  relFormula {n} r _ :=
    match n, r with
    | 0, r => Formula.iExs (Fin 1)
        (X.effF (Sum.inr 0) ⊓ Relations.formula₁ (X.nullSymO r) (Term.var (Sum.inr 0)))
    | (_ + 1), r => Relations.formula (X.origSymO r) fun i => Term.var (i, 0)
  domFormula _ := X.effF (0 : Fin 1)

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (effInterp)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

theorem mem_effInterp_dom (t : Unit) (w : Fin 1 → M) :
    ((X.effInterp).domFormula t).Realize w ↔ w 0 ∈ effSet X.orderFree.E M :=
  realize_effF w 0

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (mem_effInterp_dom)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

/-- **The interpreted universe is the marked part.** -/
noncomputable def effInterpEquiv :
    letI := X.markReduct M
    X.clsPart (effSet X.orderFree.E M) ≃[X.E] (X.effInterp).MapRel M :=
  letI := X.markReduct M
  { toFun := fun y => ⟨((), fun _ => y.1), (mem_effInterp_dom () _).mpr y.2⟩
    invFun := fun z => ⟨z.1.2 0, (mem_effInterp_dom () _).mp z.2⟩
    left_inv := fun _ => rfl
    right_inv := fun z => Subtype.ext (Prod.ext rfl (funext fun i => by
      fin_cases i
      rfl))
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} r x => by
      match n, r with
      | 0, r =>
        refine Iff.trans ?_ (relMap_clsPart_zero r x).symm
        refine Iff.trans (RelFOInterpretation.relMap_mapRel _ _ _ _) ?_
        refine Iff.trans Formula.realize_iExs ?_
        constructor
        · rintro ⟨i, hi⟩
          refine ⟨i 0, ?_, ?_⟩
          · exact (realize_effF (Sum.elim _ i) (Sum.inr 0)).mp (Formula.realize_inf.mp hi).1
          · have h' : RelMap (X.nullSymO r) ![i 0] :=
              Formula.realize_rel₁.mp (Formula.realize_inf.mp hi).2
            rw [vec_one_eq] at h'
            exact h'
        · rintro ⟨y, hy, hyr⟩
          refine ⟨fun _ => y, Formula.realize_inf.mpr ⟨?_, ?_⟩⟩
          · exact (realize_effF (Sum.elim _ fun _ => y) (Sum.inr 0)).mpr hy
          · refine Formula.realize_rel₁.mpr ?_
            simp only [Term.realize_var, Sum.elim_inr]
            rw [vec_one_eq]
            exact hyr
      | (m + 1), r =>
        refine Iff.trans ?_ (relMap_clsPart_succ r x).symm
        refine Iff.trans (RelFOInterpretation.relMap_mapRel _ _ _ _) ?_
        exact Formula.realize_rel }

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (effInterpEquiv)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

/-- **Reading the inner problem in the marked part is a relativized ordered
reduction to it.** -/
noncomputable def effReduction (Q : Lax904597.Problems.DecisionProblem X.E) : X.effProblem Q ≤ʳᶠᵒ[≤] Q where
  Tag := Unit
  dim := 1
  toRelInterpretation := X.effInterp
  dom_nonempty := by
    intro A _ _ _ _
    obtain ⟨x, hx⟩ := effSet_nonempty (F := X.orderFree.E) (M := A)
    exact ⟨(), fun _ => x, (mem_effInterp_dom () _).mpr hx⟩
  correct := by
    intro A _ _ _ _
    exact Q.iso_invariant (effInterpEquiv (X := X) (M := A))

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (effReduction)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

/-- **The inner problem read in the marked part stays in polynomial space.** -/
theorem mem_PSPACE_effProblem {Q : Lax904597.Problems.DecisionProblem X.E} (hQ : Q ∈ PSPACE) :
    X.effProblem Q ∈ PSPACE :=
  (pfpDefinable_iff_mem_PSPACE _).mp
    (PFPDefinable.of_relOrderedReduction (X.effReduction Q)
      ((pfpDefinable_iff_mem_PSPACE Q).mpr hQ))

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (mem_PSPACE_effProblem)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

/-! ### The guessed copy is a copy: the first-order guard -/

/-- The same-order symbol, in the source vocabulary of the reduction. -/
noncomputable abbrev sameSymO : (X.markLangOf.sum Language.order).Relations 2 :=
  Sum.inl (Sum.inl X.sameSym)

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (sameSymO)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

/-- **The guard**: the marked part is nonempty, and it holds exactly the points
carrying the order of any one of its members. -/
noncomputable def isClsS : (X.markLangOf.sum Language.order).Sentence :=
  Formula.iExs (Fin 1) (Relations.formula₁ X.markSymO (Term.var (Sum.inr 0))) ⊓
    Formula.iAlls (Fin 2)
      (Relations.formula₁ X.markSymO (Term.var (Sum.inr 0)) ⟹
        (Relations.formula₁ X.markSymO (Term.var (Sum.inr 1)) ⇔
          Relations.formula₂ X.sameSymO (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))))

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (isClsS)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

theorem realize_isClsS :
    @Sentence.Realize _ M (Lax904597.Interpretations.sumOrderStructure X.markLangOf M) X.isClsS ↔
      letI := X.markReduct M
      IsCls X (markSet X.orderFree.E M) := by
  let := X.markReduct M
  have hmark : ∀ x : M, (RelMap (X.markSymO) ![x] ↔ x ∈ markSet X.orderFree.E M) :=
    fun _ => Iff.rfl
  have hsame : ∀ x y : M,
      (RelMap (X.sameSymO) ![x, y] ↔ RelMap X.sameSym ![x, y]) := fun _ _ => Iff.rfl
  refine Iff.trans Formula.realize_inf (and_congr ?_ ?_)
  · refine Iff.trans Formula.realize_iExs ?_
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i 0, (hmark (i 0)).mp (Formula.realize_rel₁.mp hi)⟩
    · rintro ⟨x, hx⟩
      exact ⟨fun _ => x, Formula.realize_rel₁.mpr ((hmark x).mpr hx)⟩
  · refine Iff.trans Formula.realize_iAlls ?_
    constructor
    · intro hh x hx y
      have h := Formula.realize_imp.mp (hh ![x, y])
      simp only [Formula.realize_rel₁, Term.realize_var, Sum.elim_inr] at h
      have h2 := Formula.realize_iff.mp (h ((hmark x).mpr hx))
      simp only [Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr] at h2
      exact Iff.trans ((hmark y).symm.trans h2) (hsame x y)
    · intro hh i
      refine Formula.realize_imp.mpr fun hx => ?_
      simp only [Formula.realize_rel₁, Term.realize_var, Sum.elim_inr] at hx
      refine Formula.realize_iff.mpr ?_
      simp only [Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr]
      exact Iff.trans (hh (i 0) ((hmark (i 0)).mp hx) (i 1)) (hsame (i 0) (i 1)).symm

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_isClsS)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

/-- **Guessing a copy and checking it stays in polynomial space.** -/
theorem mem_PSPACE_clsProblem {Q : Lax904597.Problems.DecisionProblem X.E} (hQ : Q ∈ PSPACE) :
    X.clsProblem Q ∈ PSPACE := by
  refine (mem_PSPACE_iff _).mpr (SOTCDefinable.and_sentence
    ((mem_PSPACE_iff _).mp (X.mem_PSPACE_effProblem hQ)) X.isClsS ?_)
  intro N _ _ _ _
  exact and_congr_left' realize_isClsS.symm

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (mem_PSPACE_clsProblem)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

/-! ### Guessing the copy: “some copy answers yes” is in polynomial space -/

/-- **The copy, guessed as a relation variable**: a copy of the expansion is
exactly a marked part that the guard accepts. -/
theorem someCls_iff_exists_mark {Q : Lax904597.Problems.DecisionProblem X.E} (N : Type)
    [X.orderFree.E.Structure N] :
    someCls X Q N ↔ ∃ ρ : markBlock.Assignment N,
      @Lax904597.Problems.DecisionProblem.Holds _ _ (X.clsProblem Q) N (markBlock.structure₁ ρ) := by
  constructor
  · rintro ⟨S, hS, hQS⟩
    refine ⟨fun _ (w : Fin 1 → N) => w 0 ∈ S, ?_⟩
    let := markBlock.structure₁ (L := X.orderFree.E) fun _ (w : Fin 1 → N) => w 0 ∈ S
    have hset : markSet X.orderFree.E N = S := rfl
    obtain ⟨x₀, hx₀⟩ := hS.1
    have heff : effSet X.orderFree.E N = S := by
      rw [effSet_eq_markSet (x := x₀) (hset ▸ hx₀), hset]
    refine ⟨hset ▸ hS, ?_⟩
    change Q (X.clsPart (effSet X.orderFree.E N))
    exact heff ▸ hQS
  · rintro ⟨ρ, hcls, heff⟩
    let := markBlock.structure₁ (L := X.orderFree.E) ρ
    obtain ⟨x₀, hx₀⟩ := hcls.1
    have heff' : Q (X.clsPart (effSet X.orderFree.E N)) := heff
    exact ⟨markSet X.orderFree.E N, hcls, effSet_eq_markSet hx₀ ▸ heff'⟩

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (someCls_iff_exists_mark)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

/-- **“Some copy answers yes” stays in polynomial space**: the copy is guessed
into the state of the walk, the guard is a first-order condition on the source
state, and the inner problem is read in the copy by a relativized reduction. -/
theorem mem_PSPACE_someCls {Q : Lax904597.Problems.DecisionProblem X.E} (hQ : Q ∈ PSPACE) :
    someCls X Q ∈ PSPACE :=
  (mem_PSPACE_iff _).mpr
    (SOTCDefinable.exBlock ((mem_PSPACE_iff _).mp (X.mem_PSPACE_clsProblem hQ))
      fun N _ _ _ => someCls_iff_exists_mark X N)

end Reduction

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (mem_PSPACE_someCls)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Reduction

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

variable {X} {M : Type} [X.markLangOf.Structure M] [LinearOrder M]

variable (X)

end Reduction

end ExpExpansion

/-! ### EXPSPACE needs no order -/

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **PSPACE over an expanded universe needs no order.** Left to right the order
is guessed into the block of the expansion
(`DescriptiveComplexity.ExpExpansion.orderFree`) and the inner problem is
replaced by “some copy answers yes”
(`DescriptiveComplexity.ExpExpansion.someCls`), which is again in `PSPACE`; right
to left an expansion that never mentions the order is one that ignores it. -/
theorem expDefinable_PSPACE_iff_free (P : Lax904597.Problems.DecisionProblem L) :
    ExpDefinable PSPACE P ↔ ExpDefinableFree PSPACE P := by
  constructor
  · rintro ⟨X, Q, hQ, hX⟩
    refine ⟨X.orderFree, ExpExpansion.someCls X Q, X.mem_PSPACE_someCls hQ, ?_⟩
    intro A _ _ _
    rw [ExpExpansion.someCls_map_iff]
    constructor
    · intro hP
      let lo := finiteLinearOrder A
      exact ⟨lo, (hX A).mp hP⟩
    · rintro ⟨lo, h⟩
      let := lo
      exact (hX A).mpr h
  · exact fun h => h.expDefinable

theorem sopfpDefinableFree_iff_expDefinableFree (P : Lax904597.Problems.DecisionProblem L) :
    Lax480241.SecondOrderFixedPoints.SOPFPDefinableFree P ↔ ExpDefinableFree PSPACE P :=
  exists_congr fun _X => exists_congr fun Q =>
    and_congr_left' (pfpDefinable_iff_mem_PSPACE Q)

/-- **SO(≤, PFP) = SO(PFP)**: the order of the expansion can be guessed. -/
theorem sopfpDefinable_iff_free (P : Lax904597.Problems.DecisionProblem L) :
    Lax480241.SecondOrderFixedPoints.SOPFPDefinable P ↔ Lax480241.SecondOrderFixedPoints.SOPFPDefinableFree P :=
  (sopfpDefinable_iff_expDefinable P).trans
    ((expDefinable_PSPACE_iff_free P).trans (sopfpDefinableFree_iff_expDefinableFree P).symm)

/-- **EXPSPACE is SO(PFP), no order needed.** -/
theorem mem_EXPSPACE_iff_sopfpDefinableFree (P : Lax904597.Problems.DecisionProblem L) :
    P ∈ EXPSPACE ↔ Lax480241.SecondOrderFixedPoints.SOPFPDefinableFree P :=
  (mem_EXPSPACE_iff P).trans (sopfpDefinable_iff_free P)

end Lax480241Proofs.DescriptiveComplexity


