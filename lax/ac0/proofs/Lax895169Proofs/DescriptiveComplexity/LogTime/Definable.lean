/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.ArithmeticDefinable
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

namespace Lax895169.ArithmeticLogic
end Lax895169.ArithmeticLogic

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.ArithmeticLogic (AC0Definable)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax895169.ArithmeticLogic (arith)
end FirstOrder.Language

/-!
# Arithmetically definable relations: AC⁰ definability with free variables

`DescriptiveComplexity.AC0Definable` is a statement about *sentences*, and a
sentence is an awkward thing to build by hand: every construction carries its
own variable bookkeeping through `FirstOrder.Language.Formula.iExs` and
`Sum.elim`. This file does that bookkeeping once, and then never again:
`DescriptiveComplexity.ArithDef` says that a *family* of relations on
valuations – one relation for every nonempty finite ordered structure – is
realized by a single formula of the arithmetic expansion, and the lemmas below
close the notion under the Boolean connectives and under quantification.

Everything downstream is then semantic. A construction states what its relation
*means* on ranks, chains the closure lemmas, and reads the sentence off at the
end with `DescriptiveComplexity.ArithDef.ac0Definable`; no formula is ever
inspected again.

## Conventions

Variables are indexed by an arbitrary type `α`, as `Formula α` is, and a
quantifier binds the variables of `Fin 1` in `α ⊕ Fin 1`
(`DescriptiveComplexity.ArithDef.ex`, `DescriptiveComplexity.ArithDef.all`) –
the layout of `FirstOrder.Language.Formula.iExs`, so that no relabeling is
needed at the quantifier step. Moving between variable layouts is
`DescriptiveComplexity.ArithDef.relabel`, and a relation with *no* free
variables (`α = Empty`) is literally a sentence, which is what
`DescriptiveComplexity.ArithDef.ac0Definable` reads.

## The three groups of lemmas

* **Atoms** – the order, the two numeric predicates, equality, and an input
  relation read at a tuple of variables
  (`DescriptiveComplexity.arithDef_le`, `_plus`, `_times`, `_eq`, `_rel`).
* **Connectives** – negation, conjunction, disjunction, implication, and the
  two constants.
* **Quantifiers** – `DescriptiveComplexity.ArithDef.ex` and
  `DescriptiveComplexity.ArithDef.all`, together with the vector forms
  `DescriptiveComplexity.ArithDef.exs` and `DescriptiveComplexity.ArithDef.alls`
  binding a whole `Fin k` of variables at once.

A `DescriptiveComplexity.ArithDef.congr` lemma lets a relation be replaced by a
pointwise-equivalent one, which is how a semantic reformulation – the shape most
proofs actually want – is fed to the closure lemmas.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {α β : Type}

/-! ### Relations on valuations of a finite ordered structure -/

/-- A **family of relations** on `α`-indexed valuations: one relation for every
nonempty finite ordered `L`-structure. The instance arguments are those of
`DescriptiveComplexity.AC0Definable`, since that is what the family is
eventually read as. -/
abbrev ArithRel (L : Language.{0, 0}) (α : Type) : Type 1 :=
  ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], (α → A) → Prop

/-- A family of relations is **arithmetically definable** when one formula of
the arithmetic expansion realizes it in every nonempty finite ordered
structure – first-order logic with `≤`, `+` and `×` on the ranks, with free
variables indexed by `α`. -/
def ArithDef (R : ArithRel L α) : Prop :=
  ∃ φ : (L.sum Lax895169.ArithmeticLogic.arith).Formula α,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A),
      R A v ↔ φ.Realize v

namespace ArithDef

/-- Definability transfers along a pointwise equivalence of relations: the
formula is unchanged, only the semantic reading of it is. -/
theorem congr {R S : ArithRel L α} (h : ArithDef R)
    (he : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A),
      R A v ↔ S A v) : ArithDef S := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, fun A _ _ _ _ v => (he A v).symm.trans (hφ A v)⟩

/-- **Renaming the free variables**: a definable relation read through a
substitution of variables is definable. -/
theorem relabel {R : ArithRel L α} (h : ArithDef R) (f : α → β) :
    ArithDef (L := L) (α := β) (fun A _ _ _ _ v => R A (v ∘ f)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.relabel f, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_relabel]
  exact hφ A _

/-! ### Connectives -/

/-- The negation of a definable relation is definable. -/
theorem not {R : ArithRel L α} (h : ArithDef R) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ¬ R A v) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨∼φ, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_not]
  exact not_congr (hφ A v)

/-- The conjunction of two definable relations is definable. -/
theorem and {R S : ArithRel L α} (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => R A v ∧ S A v) := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  refine ⟨φ ⊓ ψ, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_inf]
  exact and_congr (hφ A v) (hψ A v)

/-- The disjunction of two definable relations is definable. -/
theorem or {R S : ArithRel L α} (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => R A v ∨ S A v) := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  refine ⟨φ ⊔ ψ, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_sup]
  exact or_congr (hφ A v) (hψ A v)

/-- An implication between definable relations is definable. -/
theorem imp {R S : ArithRel L α} (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => R A v → S A v) := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  refine ⟨φ.imp ψ, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_imp]
  exact imp_congr (hφ A v) (hψ A v)

/-- The always-true relation is definable. -/
theorem top : ArithDef (L := L) (α := α) (fun _ _ _ _ _ _ => True) :=
  ⟨⊤, fun A _ _ _ _ v => by simp⟩

/-- A case distinction made outside the structure – a condition on the
*machine*, not on the instance – is definable when both branches are. -/
theorem ite {R S : ArithRel L α} (c : Prop) [Decidable c] (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => if c then R A v else S A v) := by
  by_cases hc : c
  · simpa [hc] using h
  · simpa [hc] using h'

end ArithDef

/-! ### Atoms -/

section Atoms

/-- The order between two variables is definable. -/
theorem arithDef_le (x y : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => v x ≤ v y) :=
  ⟨aLeF x y, fun A _ _ _ _ v => by rw [realize_aLeF]⟩

/-- Equality between two variables is definable. -/
theorem arithDef_eq (x y : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => v x = v y) :=
  ⟨Term.equal (Term.var x) (Term.var y), fun A _ _ _ _ v => by
    rw [Formula.realize_equal]; exact Iff.rfl⟩

/-- Addition of the ranks of three variables is definable. -/
theorem arithDef_plus (x y z : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => Lax895169.BitPredicate.orank (v x) + Lax895169.BitPredicate.orank (v y) = Lax895169.BitPredicate.orank (v z)) :=
  ⟨aPlusF x y z, fun A _ _ _ _ v => by rw [realize_aPlusF]⟩

/-- Multiplication of the ranks of three variables is definable. -/
theorem arithDef_times (x y z : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => Lax895169.BitPredicate.orank (v x) * Lax895169.BitPredicate.orank (v y) = Lax895169.BitPredicate.orank (v z)) :=
  ⟨aTimesF x y z, fun A _ _ _ _ v => by rw [realize_aTimesF]⟩

/-- An input relation symbol, in the arithmetic expansion of its vocabulary.
Named, as every symbol of a sum vocabulary in this library is, so that `rw`
matches it. -/
abbrev inSym {a : ℕ} (R : L.Relations a) : (L.sum Lax895169.ArithmeticLogic.arith).Relations a := Sum.inl R

/-- **Reading the input**: an atom of the input vocabulary, at a tuple of
variables, is definable. This is the only place the instance is looked at – in
the machine reading of this logic it is the query instruction. -/
theorem arithDef_rel {a : ℕ} (R : L.Relations a) (arg : Fin a → α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => RelMap R fun t => v (arg t)) :=
  ⟨Relations.formula (inSym R) fun t => Term.var (arg t), fun A _ _ _ _ v => by
    rw [Formula.realize_rel]
    exact Iff.rfl⟩

end Atoms

/-! ### Quantifiers -/

namespace ArithDef

/-- **Existential quantification** of one variable: the variable of `Fin 1` in
`α ⊕ Fin 1`, which is the layout `FirstOrder.Language.Formula.iExs` binds. -/
theorem ex {R : ArithRel L (α ⊕ Fin 1)} (h : ArithDef R) :
    ArithDef (L := L) (α := α)
      (fun A _ _ _ _ v => ∃ a, R A (Sum.elim v fun _ => a)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.iExs (Fin 1), fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_iExs]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, (hφ A _).mp ha⟩
  · rintro ⟨w, hw⟩
    refine ⟨w 0, (hφ A _).mpr ?_⟩
    have hw' : (fun _ : Fin 1 => w 0) = w := funext fun i => by
      rw [Subsingleton.elim (0 : Fin 1) i]
    rwa [hw']

/-- **Universal quantification** of one variable, in the same layout. -/
theorem all {R : ArithRel L (α ⊕ Fin 1)} (h : ArithDef R) :
    ArithDef (L := L) (α := α)
      (fun A _ _ _ _ v => ∀ a, R A (Sum.elim v fun _ => a)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.iAlls (Fin 1), fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_iAlls]
  constructor
  · intro ha w
    have hw' : (fun _ : Fin 1 => w 0) = w := funext fun i => by
      rw [Subsingleton.elim (0 : Fin 1) i]
    exact hw' ▸ (hφ A _).mp (ha (w 0))
  · intro hw a
    exact (hφ A _).mpr (hw fun _ => a)

/-- **Existential quantification of a block** of `k` variables at once. -/
theorem exs {k : ℕ} {R : ArithRel L (α ⊕ Fin k)} (h : ArithDef R) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∃ w : Fin k → A, R A (Sum.elim v w)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.iExs (Fin k), fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_iExs]
  exact exists_congr fun w => hφ A _

/-- **Universal quantification of a block** of `k` variables at once. -/
theorem alls {k : ℕ} {R : ArithRel L (α ⊕ Fin k)} (h : ArithDef R) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ w : Fin k → A, R A (Sum.elim v w)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.iAlls (Fin k), fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_iAlls]
  exact forall_congr' fun w => hφ A _

end ArithDef

/-! ### From a closed relation to a sentence -/

/-- **The bridge to `DescriptiveComplexity.AC0Definable`**: a definable relation
with no free variables *is* an AC⁰ definition of the problem it states – a
formula over `Empty` is a sentence. -/
theorem ArithDef.ac0Definable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L} {R : ArithRel L Empty}
    (h : ArithDef R)
    (hP : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ R A Empty.elim) :
    Lax895169.ArithmeticLogic.AC0Definable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, ?_⟩
  intro A _ _ _ _
  rw [hP A, Sentence.Realize]
  exact (hφ A _).trans (by rw [Subsingleton.elim (Empty.elim : Empty → A) default])

end Lax895169Proofs.DescriptiveComplexity


