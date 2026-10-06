/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.SecondOrderKrom
import Lax895169Proofs.DescriptiveComplexity.SecondOrderPull
import Lax895169Proofs.DescriptiveComplexity.OrderedComposition
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

namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax895169Proofs.DescriptiveComplexity.KromClause
end Lax895169Proofs.DescriptiveComplexity.KromClause

namespace Lax895169Proofs.DescriptiveComplexity.KromLit
end Lax895169Proofs.DescriptiveComplexity.KromLit

namespace Lax895169Proofs.DescriptiveComplexity.KromProgram
end Lax895169Proofs.DescriptiveComplexity.KromProgram

namespace Lax895169Proofs.DescriptiveComplexity.SigmaSOKromDefinable
end Lax895169Proofs.DescriptiveComplexity.SigmaSOKromDefinable

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
export Lax904597.SecondOrder (SOBlock)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.KromFragment (KromClause KromLit KromProgram SigmaSOKromDefinable)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Pulling SO-Krom definability back through an interpretation

SO-Krom definability is closed under (ordered) first-order reductions
(`DescriptiveComplexity.SigmaSOKromDefinable.of_orderedReduction`). This is what makes
the fragment a `DescriptiveComplexity.ComplexityClass` – the class
`DescriptiveComplexity.NL` – rather than a mere definability predicate.

The argument is the one of `DescriptiveComplexity.SecondOrderHornPull`, and it works
for the same structural reason: the Krom condition constrains the occurrences
of the *second-order* variables only, while an interpretation rewrites the
*input-vocabulary* atoms, which live in the guard, where anything is allowed.
Pulling a clause back through a `d`-dimensional interpretation with tag type
`Tag`:

* the block is pulled as in `DescriptiveComplexity.SOBlock.pull`: an `n`-ary relation
  variable on `Tag × A^d` becomes one `(n·d)`-ary relation variable on `A` per
  `n`-tuple of tags;
* a clause becomes one clause per assignment `t : Fin k → Tag` of tags to its
  universally quantified variables (`DescriptiveComplexity.KromClause.pull`), with the
  `k` variables replaced by `k · d` coordinates;
* its guard becomes the ordinary formula pullback
  `DescriptiveComplexity.guardPull` at the tag assignment `t` – an arbitrary first-order
  formula, which is fine, guards being unconstrained;
* each literal keeps its sign and its atom becomes the atom of the
  corresponding pulled relation variable (`DescriptiveComplexity.SOAtom.pull`), so the
  clause still has at most two second-order literals – which is what keeps it
  Krom.

The shared pieces (`DescriptiveComplexity.SOAtom.pull`, `DescriptiveComplexity.guardPull`,
`DescriptiveComplexity.tagVal`, `DescriptiveComplexity.allTagAssign`) are in
`DescriptiveComplexity.SecondOrderPull`, and the order enters exactly as it does for
SO-Horn: the pullback interprets the target's order by the lexicographic order
on tagged tuples (`DescriptiveComplexity.FOInterpretation.ordExtend`).
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

/-! ### Pulling back a literal, a clause and a program -/

/-- The pullback of a literal: same sign, pulled atom. -/
def KromLit.pull (l : Lax485149.KromFragment.KromLit B k) (d : ℕ) (t : Fin k → Tag) :
    Lax485149.KromFragment.KromLit (B.pull Tag d) (k * d) where
  atom := l.atom.pull d t
  positive := l.positive

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromLit

export Lax895169Proofs.DescriptiveComplexity.KromLit (pull)

end Lax485149.KromFragment.KromLit

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

omit [L₂.IsRelational] in
theorem KromLit.pull_holds {A : Type} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (l : Lax485149.KromFragment.KromLit B k)
    (t : Fin k → Tag) (ρ : B.Assignment (I.Map A)) (w : Fin (k * d) → A) :
    (l.pull d t).Holds (B.pullAssign ρ) w ↔ l.Holds ρ (tagVal I t w) := by
  rw [Lax485149.KromFragment.KromLit.Holds, Lax485149.KromFragment.KromLit.Holds, KromLit.pull]
  cases l.positive with
  | false => exact not_congr (l.atom.pull_holds I t ρ w)
  | true => exact l.atom.pull_holds I t ρ w

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromLit

export Lax895169Proofs.DescriptiveComplexity.KromLit (pull_holds)

end Lax485149.KromFragment.KromLit

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

omit [L₂.IsRelational] in
theorem KromLit.slotHolds_pull {A : Type} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    (o : Option (Lax485149.KromFragment.KromLit B k)) (t : Fin k → Tag) (ρ : B.Assignment (I.Map A))
    (w : Fin (k * d) → A) :
    Lax485149.KromFragment.KromLit.slotHolds (o.map fun l => l.pull d t) (B.pullAssign ρ) w ↔
      Lax485149.KromFragment.KromLit.slotHolds o ρ (tagVal I t w) := by
  rw [Lax485149.KromFragment.KromLit.slotHolds, Lax485149.KromFragment.KromLit.slotHolds]
  cases o with
  | none => exact Iff.rfl
  | some l => exact l.pull_holds I t ρ w

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromLit

export Lax895169Proofs.DescriptiveComplexity.KromLit (slotHolds_pull)

end Lax485149.KromFragment.KromLit

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

/-- The pullback of a Krom clause at a tag assignment: guards pull back as
formulas, literals keep their signs – so the result is again a Krom clause. -/
noncomputable def KromClause.pull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    (c : Lax485149.KromFragment.KromClause L₂ B k) (t : Fin k → Tag) : Lax485149.KromFragment.KromClause L₁ (B.pull Tag d) (k * d) where
  guard := guardPull I c.guard t
  lit₁ := c.lit₁.map fun l => l.pull d t
  lit₂ := c.lit₂.map fun l => l.pull d t

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromClause

export Lax895169Proofs.DescriptiveComplexity.KromClause (pull)

end Lax485149.KromFragment.KromClause

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

theorem KromClause.pull_holds {A : Type} [L₁.Structure A]
    (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (c : Lax485149.KromFragment.KromClause L₂ B k) (t : Fin k → Tag)
    (ρ : B.Assignment (I.Map A)) (w : Fin (k * d) → A) :
    (c.pull I t).Holds (B.pullAssign ρ) w ↔ c.Holds ρ (tagVal I t w) := by
  rw [Lax485149.KromFragment.KromClause.Holds, Lax485149.KromFragment.KromClause.Holds, KromClause.pull]
  exact imp_congr (realize_guardPull I c.guard t w)
    (or_congr (KromLit.slotHolds_pull I c.lit₁ t ρ w) (KromLit.slotHolds_pull I c.lit₂ t ρ w))

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromClause

export Lax895169Proofs.DescriptiveComplexity.KromClause (pull_holds)

end Lax485149.KromFragment.KromClause

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

/-- The pullback of a Krom program: one clause per clause of the program and
per assignment of tags to its universally quantified variables. -/
noncomputable def KromProgram.pull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    (prog : Lax485149.KromFragment.KromProgram L₂ B k) : Lax485149.KromFragment.KromProgram L₁ (B.pull Tag d) (k * d) :=
  prog.flatMap fun c => (allTagAssign Tag k).map fun t => c.pull I t

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromProgram

export Lax895169Proofs.DescriptiveComplexity.KromProgram (pull)

end Lax485149.KromFragment.KromProgram

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

theorem KromProgram.pull_mem (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    {prog : Lax485149.KromFragment.KromProgram L₂ B k} {c : Lax485149.KromFragment.KromClause L₂ B k} (hc : c ∈ prog)
    (t : Fin k → Tag) : c.pull I t ∈ prog.pull I := by
  rw [KromProgram.pull, List.mem_flatMap]
  exact ⟨c, hc, List.mem_map.mpr ⟨t, mem_allTagAssign t, rfl⟩⟩

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromProgram

export Lax895169Proofs.DescriptiveComplexity.KromProgram (pull_mem)

end Lax485149.KromFragment.KromProgram

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

theorem KromProgram.pull_cases (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    {prog : Lax485149.KromFragment.KromProgram L₂ B k} {c' : Lax485149.KromFragment.KromClause L₁ (B.pull Tag d) (k * d)}
    (hc' : c' ∈ prog.pull I) : ∃ c ∈ prog, ∃ t : Fin k → Tag, c' = c.pull I t := by
  rw [KromProgram.pull, List.mem_flatMap] at hc'
  obtain ⟨c, hc, hmem⟩ := hc'
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hmem
  exact ⟨c, hc, t, rfl⟩

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromProgram

export Lax895169Proofs.DescriptiveComplexity.KromProgram (pull_cases)

end Lax485149.KromFragment.KromProgram

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

/-! ### Correctness of the pullback -/

section Correctness

variable {A : Type} [L₁.Structure A] (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)

variable (prog : Lax485149.KromFragment.KromProgram L₂ B k)

/-- An assignment satisfies a program on the interpreted structure iff its
transfer satisfies the pulled program on the base structure. -/
theorem KromProgram.pull_holds (ρ : B.Assignment (I.Map A)) :
    (prog.pull I).Holds (B.pullAssign ρ) ↔ prog.Holds ρ := by
  constructor
  · intro h v c hc
    have hp := h (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2)
      (c.pull I fun p => (v p).1) (KromProgram.pull_mem I hc _)
    have h2 := (KromClause.pull_holds I c (fun p => (v p).1) ρ _).mp hp
    rwa [tagVal_split I v] at h2
  · intro h w c' hc'
    obtain ⟨c, hc, t, rfl⟩ := KromProgram.pull_cases I hc'
    exact (KromClause.pull_holds I c t ρ w).mpr (h (tagVal I t w) c hc)

end Correctness

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromProgram

export Lax895169Proofs.DescriptiveComplexity.KromProgram (pull_holds)

end Lax485149.KromFragment.KromProgram

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

section Correctness

variable {A : Type} [L₁.Structure A] (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)

variable (prog : Lax485149.KromFragment.KromProgram L₂ B k)

/-- **The pullback is correct**: the program is satisfiable on the interpreted
structure iff its pullback is satisfiable on the base structure. -/
theorem KromProgram.exists_holds_pull :
    (∃ ρ : B.Assignment (I.Map A), prog.Holds ρ) ↔
      ∃ σ : (B.pull Tag d).Assignment A, (prog.pull I).Holds σ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨B.pullAssign ρ, (KromProgram.pull_holds I prog ρ).mpr hρ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨B.mergeAssign σ, (KromProgram.pull_holds I prog (B.mergeAssign σ)).mp ?_⟩
    rw [B.pullAssign_mergeAssign σ]
    exact hσ

end Correctness

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromProgram

export Lax895169Proofs.DescriptiveComplexity.KromProgram (exists_holds_pull)

end Lax485149.KromFragment.KromProgram

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

section Correctness

variable {A : Type} [L₁.Structure A] (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)

variable (prog : Lax485149.KromFragment.KromProgram L₂ B k)

end Correctness

/-! ### Closure under reductions -/

section Closure

variable [L₁.IsRelational] {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}

/-- **SO-Krom definability is closed under ordered first-order reductions.**
The Krom shape survives the pullback because an interpretation only rewrites
the input-vocabulary atoms, which live in the guards; the second-order
literals keep their signs and are merely re-indexed. -/
theorem SigmaSOKromDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q)
    (h : Lax485149.KromFragment.SigmaSOKromDefinable Q) : Lax485149.KromFragment.SigmaSOKromDefinable P := by
  obtain ⟨B, k, prog, hprog⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨B.pull f.Tag f.dim, k * f.dim,
    KromProgram.pull f.toInterpretation.ordExtend prog, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hprog (f.toInterpretation.Map A)).trans ?_)
  refine Iff.trans ?_ (KromProgram.exists_holds_pull f.toInterpretation.ordExtend prog)
  exact (KromProgram.exists_holds_equiv (f.toInterpretation.ordExtendLEquiv A) prog).symm

end Closure

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.SigmaSOKromDefinable

export Lax895169Proofs.DescriptiveComplexity.SigmaSOKromDefinable (of_orderedReduction)

end Lax485149.KromFragment.SigmaSOKromDefinable

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

section Closure

variable [L₁.IsRelational] {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}

/-- SO-Krom definability is closed under first-order reductions. -/
theorem SigmaSOKromDefinable.of_foReduction (f : P ≤ᶠᵒ Q)
    (h : Lax485149.KromFragment.SigmaSOKromDefinable Q) : Lax485149.KromFragment.SigmaSOKromDefinable P :=
  h.of_orderedReduction f.toOrdered

end Closure

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.SigmaSOKromDefinable

export Lax895169Proofs.DescriptiveComplexity.SigmaSOKromDefinable (of_foReduction)

end Lax485149.KromFragment.SigmaSOKromDefinable

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable [L₂.IsRelational]

section Closure

variable [L₁.IsRelational] {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}

end Closure

end Lax895169Proofs.DescriptiveComplexity


