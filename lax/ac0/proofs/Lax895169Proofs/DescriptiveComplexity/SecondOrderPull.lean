/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.Composition
import Lax895169Proofs.DescriptiveComplexity.SecondOrder
import Mathlib.Data.Finite.Sigma
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax895169Proofs.DescriptiveComplexity.FOInterpretation
end Lax895169Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax895169Proofs.DescriptiveComplexity.PiSODefinable
end Lax895169Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax895169Proofs.DescriptiveComplexity.SOAtom
end Lax895169Proofs.DescriptiveComplexity.SOAtom

namespace Lax895169Proofs.DescriptiveComplexity.SOBlock
end Lax895169Proofs.DescriptiveComplexity.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax895169Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable soLang)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Pulling second-order definability back through an interpretation

If `P ≤ᶠᵒ Q` and `Q` is `Σₖ`- (resp. `Πₖ`-) definable, then so is `P`
(`DescriptiveComplexity.SigmaSODefinable.of_foReduction`,
`DescriptiveComplexity.PiSODefinable.of_foReduction`): the levels of the polynomial
hierarchy, defined by second-order alternation, are closed under first-order
reductions.

The proof pulls the defining second-order sentence back through the
interpretation `I` underlying the reduction, block by block:

* a second-order quantifier over an `n`-ary relation on the interpreted
  universe `Tag × A^d` becomes a family of second-order quantifiers over
  `(n·d)`-ary relations on `A`, one per `n`-tuple of tags
  (`DescriptiveComplexity.SOBlock.pull`; assignments transfer bijectively via
  `DescriptiveComplexity.SOBlock.pullAssign` / `DescriptiveComplexity.SOBlock.mergeAssign`);
* the interpretation extends to the languages expanded by a block
  (`DescriptiveComplexity.FOInterpretation.extendSO`): relation variables of the block
  are interpreted by the corresponding pulled relation variables, reading the
  tag tuple off statically; interpreting-then-expanding agrees with
  expanding-then-interpreting (`DescriptiveComplexity.FOInterpretation.extendSOEquiv`);
* the first-order kernel is pulled back by
  `DescriptiveComplexity.FOInterpretation.pull` from `DescriptiveComplexity.Composition`, packaged
  at the sentence level as `DescriptiveComplexity.FOInterpretation.pullSentence`.

`DescriptiveComplexity.sorealize_pullSO` puts these together: alternating second-order
satisfaction in the interpreted structure coincides with alternating
second-order satisfaction of the pulled sentence (over the pulled blocks) in
the base structure.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### Pulling back a sentence -/

section PullSentence

end PullSentence

/-! ### Pulling back a block -/

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

/-- The pullback of a second-order quantifier block through a tagged
`d`-dimensional interpretation: an `n`-ary relation variable on the
interpreted universe `Tag × A^d` becomes one `(n·d)`-ary relation variable on
`A` per `n`-tuple of tags. -/
def SOBlock.pull (B : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock where
  ι := Σ i : B.ι, Fin (B.arity i) → Tag
  arity p := B.arity p.1 * d

end PullBlock

end Lax895169Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax895169Proofs.DescriptiveComplexity.SOBlock (pull)

end Lax904597.SecondOrder.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

/-- Transfer of an assignment on the interpreted universe to an assignment of
the pulled block on the base universe. -/
def SOBlock.pullAssign (B : Lax904597.SecondOrder.SOBlock) (ρ : B.Assignment (Tag × (Fin d → A))) :
    (B.pull Tag d).Assignment A :=
  fun p x => ρ p.1 fun k => (p.2 k, fun j => x (finProdFinEquiv (k, j)))

end PullBlock

end Lax895169Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax895169Proofs.DescriptiveComplexity.SOBlock (pullAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

/-- Transfer of an assignment of the pulled block on the base universe to an
assignment on the interpreted universe. -/
def SOBlock.mergeAssign (B : Lax904597.SecondOrder.SOBlock) (σ : (B.pull Tag d).Assignment A) :
    B.Assignment (Tag × (Fin d → A)) :=
  fun i y => σ ⟨i, fun k => (y k).1⟩
    fun m => (y (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2

end PullBlock

end Lax895169Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax895169Proofs.DescriptiveComplexity.SOBlock (mergeAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

/-- The two assignment transfers are inverse (in the direction needed to
biject the second-order quantifiers). -/
theorem SOBlock.pullAssign_mergeAssign (B : Lax904597.SecondOrder.SOBlock) (σ : (B.pull Tag d).Assignment A) :
    B.pullAssign (B.mergeAssign σ) = σ := by
  funext p x
  change σ p
    (fun m => x (finProdFinEquiv
      ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2))) = σ p x
  exact congrArg (σ p) (funext fun m => congrArg x (Equiv.apply_symm_apply _ _))

end PullBlock

end Lax895169Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax895169Proofs.DescriptiveComplexity.SOBlock (pullAssign_mergeAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

end PullBlock

/-! ### Extending an interpretation along a block -/

section ExtendSO

end ExtendSO

/-! ### Pulling back an alternating second-order sentence -/

section PullSO

end PullSO

/-! ### Closure of the definability levels under FO reductions -/

section Closure

end Closure

/-! ### Pulling back atoms, guards and tag assignments

The clausal fragments (SO-Horn, SO-Krom) pull a *clause list* back through an
interpretation rather than a formula: each clause becomes one clause per static
assignment of tags to its universally quantified variables, its guard becoming
an ordinary formula pullback and its atoms becoming atoms of the pulled
relation variables. The pieces that do not depend on the shape of a clause are
collected here, and are shared by `DescriptiveComplexity.SecondOrderHornPull` and
`DescriptiveComplexity.SecondOrderKromPull`. -/

section Clausal

variable {Tag : Type} [Finite Tag] {d : ℕ} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-- The pullback of a second-order atom at a static assignment of tags to the
universally quantified variables: the atom of the pulled relation variable
selected by the tags, its arguments the `d` coordinates of each original
argument. -/
def SOAtom.pull (a : Lax485149.SecondOrderAtoms.SOAtom B k) (d : ℕ) (t : Fin k → Tag) :
    Lax485149.SecondOrderAtoms.SOAtom (B.pull Tag d) (k * d) where
  idx := ⟨a.idx, fun j => t (a.args j)⟩
  args := fun m =>
    finProdFinEquiv (a.args (finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)

end Clausal

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.SecondOrderAtoms.SOAtom

export Lax895169Proofs.DescriptiveComplexity.SOAtom (pull)

end Lax485149.SecondOrderAtoms.SOAtom

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section Clausal

variable {Tag : Type} [Finite Tag] {d : ℕ} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-- The interpreted valuation determined by a tag assignment and a valuation
of the coordinates. -/
def tagVal (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {A : Type} (t : Fin k → Tag)
    (w : Fin (k * d) → A) : Fin k → I.Map A :=
  fun p => (t p, fun j => w (finProdFinEquiv (p, j)))

theorem SOAtom.pull_holds {A : Type} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (a : Lax485149.SecondOrderAtoms.SOAtom B k)
    (t : Fin k → Tag) (ρ : B.Assignment (I.Map A)) (w : Fin (k * d) → A) :
    (a.pull d t).Holds (B.pullAssign ρ) w ↔ a.Holds ρ (tagVal I t w) := by
  refine iff_of_eq (congrArg (ρ a.idx) (funext fun j => ?_))
  refine Prod.ext_iff.mpr ⟨rfl, funext fun i => ?_⟩
  refine congrArg w ?_
  change finProdFinEquiv (a.args (finProdFinEquiv.symm (finProdFinEquiv (j, i))).1,
    (finProdFinEquiv.symm (finProdFinEquiv (j, i))).2) = finProdFinEquiv (a.args j, i)
  rw [Equiv.symm_apply_apply]

end Clausal

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.SecondOrderAtoms.SOAtom

export Lax895169Proofs.DescriptiveComplexity.SOAtom (pull_holds)

end Lax485149.SecondOrderAtoms.SOAtom

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section Clausal

variable {Tag : Type} [Finite Tag] {d : ℕ} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

omit [Finite Tag] in
/-- Splitting an interpreted valuation into its tags and its coordinates. -/
theorem tagVal_split {A : Type} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (v : Fin k → I.Map A) :
    tagVal I (fun p => (v p).1)
      (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2) = v := by
  funext p
  refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
  rw [tagVal]
  exact congrArg₂ (fun (q : Fin k) (i : Fin d) => (v q).2 i)
    (congrArg Prod.fst (Equiv.symm_apply_apply _ _))
    (congrArg Prod.snd (Equiv.symm_apply_apply _ _))

section Guards

variable [L₂.IsRelational]

/-- The pullback of a guard: the ordinary formula pullback at the tag
assignment `t`, its variables re-indexed as coordinates. -/
noncomputable def guardPull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (φ : L₂.Formula (Fin k))
    (t : Fin k → Tag) : L₁.Formula (Fin (k * d)) :=
  (I.pull (φ : L₂.BoundedFormula (Fin k) 0) (Sum.elim t finZeroElim)).relabel
    fun p => finProdFinEquiv (Sum.elim id finZeroElim p.1, p.2)

theorem realize_guardPull {A : Type} [L₁.Structure A] (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    (φ : L₂.Formula (Fin k)) (t : Fin k → Tag) (w : Fin (k * d) → A) :
    (guardPull I φ t).Realize w ↔ φ.Realize (M := I.Map A) (tagVal I t w) := by
  rw [guardPull, Formula.realize_relabel, I.realize_pull]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.Map A) (φ : L₂.BoundedFormula (Fin k) 0) a b)
    (funext fun _ => rfl) (Subsingleton.elim _ _))

end Guards

open Classical in
/-- All assignments of tags to the `k` universally quantified variables, as a
list: the pullback of a clause is instantiated at each of them. -/
noncomputable def allTagAssign (Tag : Type) [Finite Tag] (k : ℕ) : List (Fin k → Tag) :=
  letI : Fintype Tag := Fintype.ofFinite Tag
  (Finset.univ : Finset (Fin k → Tag)).toList

open Classical in
theorem mem_allTagAssign (t : Fin k → Tag) : t ∈ allTagAssign Tag k := by
  let : Fintype Tag := Fintype.ofFinite Tag
  exact Finset.mem_toList.mpr (Finset.mem_univ t)

end Clausal

end Lax895169Proofs.DescriptiveComplexity


