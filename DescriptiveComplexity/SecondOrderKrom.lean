/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrder
import DescriptiveComplexity.Ordered

/-!
# SO-Krom: existential second-order logic with a Krom kernel

The fragment SO-Krom of Grädel ([Grädel 1992][gradel1992capturing]): existential
second-order sentences whose first-order kernel is a conjunction of *Krom
clauses* – 2-clauses – in the quantified relation variables. On ordered
structures SO-Krom captures nondeterministic logarithmic space, the NL analogue
of the SO-Horn characterization of polynomial time
(`DescriptiveComplexity.SecondOrderHorn`).

## Horn and Krom, side by side

Both fragments restrict the occurrences of the *second-order* variables only,
leaving the input vocabulary unconstrained – it is *evaluated* in the
structure, not guessed. They ration the guessed relations differently:

* SO-Horn: any number of negative second-order atoms, **at most one positive**.
  A satisfiable Horn formula has a *least* model, computable by unit
  propagation, which is what makes the guess deterministic and the class P.
* SO-Krom: **at most two second-order atoms**, of either sign. A 2-CNF has no
  least model, so the guess stays a genuine guess; what keeps it below NP is
  that binary clauses propagate one implication at a time, i.e. along a *path*.
  Satisfiability of the instantiated kernel is 2-SAT, decided by reachability
  in the implication graph.

Neither fragment contains the other: Horn clauses may be arbitrarily wide,
Krom clauses may have two positive literals.

## The kernel, as data

As in the Horn case, the kernel is represented as data rather than carved out
of `FirstOrder.Language.BoundedFormula` by a syntactic predicate. A clause is

```
guard(x̄) → ℓ₁ ∨ ℓ₂
```

where each `ℓᵢ` is a *signed* atom in the relation variables
(`DescriptiveComplexity.KromLit`) and `guard` is an arbitrary first-order formula over
the input vocabulary alone (in the definability notion below, over its ordered
expansion). A `DescriptiveComplexity.KromClause` carries its guard and its two literals
as `Option`s, so unit clauses and the empty clause (`guard → ⊥`, the goal
clause of the Horn presentation) need no separate treatment; a
`DescriptiveComplexity.KromProgram` is a list of clauses sharing `k` universally
quantified first-order variables. This clausal form is what a reduction
consuming an SO-Krom definition needs to see: a discharge emits one
propositional 2-clause per clause and per instantiation of the `k` variables,
its literal signs read off the clause.

`DescriptiveComplexity.SigmaSOKromDefinable` is the resulting definability notion; it is
closed under (ordered) first-order reductions by
`DescriptiveComplexity.SecondOrderKromPull`, which is what makes it a
`DescriptiveComplexity.ComplexityClass` – the class `DescriptiveComplexity.NL` of
`DescriptiveComplexity.LogSpace`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Krom programs -/

/-- A literal in the relation variables of a block: an atom together with a
sign (`positive = false` for a negated atom). -/
structure KromLit (B : SOBlock) (k : ℕ) where
  /-- The underlying second-order atom. -/
  atom : SOAtom B k
  /-- The sign of the literal: `true` for the atom, `false` for its
  negation. -/
  positive : Bool

/-- A Krom clause over the input vocabulary `L` and the block `B`, with `k`
universally quantified first-order variables: an arbitrary first-order guard
over `L` implies the disjunction of at most two signed second-order literals.
A `none` literal is absent, so a clause with both literals absent is the goal
clause `guard → ⊥`. -/
structure KromClause (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) where
  /-- The first-order guard, over the input vocabulary alone. -/
  guard : L.Formula (Fin k)
  /-- The first literal of the clause, if any. -/
  lit₁ : Option (KromLit B k)
  /-- The second literal of the clause, if any. -/
  lit₂ : Option (KromLit B k)

/-- An SO-Krom kernel, as data: a finite conjunction of Krom clauses, each
implicitly universally quantified over the same `k` first-order variables. -/
abbrev KromProgram (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) : Type :=
  List (KromClause L B k)

/-! ### Semantics -/

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

/-- The truth value of a literal: its atom, or the negation of its atom. -/
def KromLit.Holds (l : KromLit B k) (ρ : B.Assignment A) (v : Fin k → A) : Prop :=
  if l.positive then l.atom.Holds ρ v else ¬l.atom.Holds ρ v

/-- The truth value of one of the two literal slots of a clause: `False` when
the literal is absent. -/
def KromLit.slotHolds (o : Option (KromLit B k)) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  o.elim False fun l => l.Holds ρ v

theorem KromLit.slotHolds_iff {o : Option (KromLit B k)} {ρ : B.Assignment A}
    {v : Fin k → A} : KromLit.slotHolds o ρ v ↔ ∃ l ∈ o, l.Holds ρ v := by
  cases o with
  | none => simp [KromLit.slotHolds]
  | some l => simp [KromLit.slotHolds]

/-- A Krom clause holds at a valuation when its guard forces one of its (at
most two) literals. -/
def KromClause.Holds (c : KromClause L B k) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  c.guard.Realize v →
    (KromLit.slotHolds c.lit₁ ρ v ∨ KromLit.slotHolds c.lit₂ ρ v)

/-- An assignment satisfies a program when every clause holds at every
valuation of the universally quantified variables. -/
def KromProgram.Holds (prog : KromProgram L B k) (ρ : B.Assignment A) : Prop :=
  ∀ v : Fin k → A, ∀ c ∈ prog, c.Holds ρ v

end Semantics

/-! ### Isomorphism-invariance -/

section Iso

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {M N : Type}
variable [L.Structure M] [L.Structure N]

theorem KromLit.holds_equiv (e : M ≃[L] N) (l : KromLit B k) (ρ : B.Assignment M)
    (v : Fin k → M) :
    l.Holds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔ l.Holds ρ v := by
  rw [KromLit.Holds, KromLit.Holds]
  cases l.positive with
  | false => exact not_congr (l.atom.holds_equiv e ρ v)
  | true => exact l.atom.holds_equiv e ρ v

theorem KromLit.slotHolds_equiv (e : M ≃[L] N) (o : Option (KromLit B k))
    (ρ : B.Assignment M) (v : Fin k → M) :
    KromLit.slotHolds o (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔
      KromLit.slotHolds o ρ v := by
  rw [KromLit.slotHolds, KromLit.slotHolds]
  cases o with
  | none => exact Iff.rfl
  | some l => exact l.holds_equiv e ρ v

theorem KromClause.holds_equiv (e : M ≃[L] N) (c : KromClause L B k)
    (ρ : B.Assignment M) (v : Fin k → M) :
    c.Holds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔ c.Holds ρ v :=
  imp_congr (StrongHomClass.realize_formula e c.guard)
    (or_congr (KromLit.slotHolds_equiv e c.lit₁ ρ v) (KromLit.slotHolds_equiv e c.lit₂ ρ v))

theorem KromProgram.holds_equiv (e : M ≃[L] N) (prog : KromProgram L B k)
    (ρ : B.Assignment M) : prog.Holds (B.mapAssign e.toEquiv ρ) ↔ prog.Holds ρ := by
  constructor
  · intro h v c hc
    exact (c.holds_equiv e ρ v).mp (h (fun j => e (v j)) c hc)
  · intro h v c hc
    have := (c.holds_equiv e ρ fun j => e.symm (v j)).mpr
      (h (fun j => e.symm (v j)) c hc)
    simpa using this

/-- **Krom satisfiability is isomorphism-invariant**: a program has a
satisfying assignment on one structure iff it has one on any isomorphic
structure. -/
theorem KromProgram.exists_holds_equiv (e : M ≃[L] N) (prog : KromProgram L B k) :
    (∃ ρ : B.Assignment M, prog.Holds ρ) ↔ ∃ ρ : B.Assignment N, prog.Holds ρ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨B.mapAssign e.toEquiv ρ, (prog.holds_equiv e ρ).mpr hρ⟩
  · rintro ⟨ρ, hρ⟩
    refine ⟨B.mapAssign e.toEquiv.symm ρ, ?_⟩
    have hkey : B.mapAssign e.toEquiv (B.mapAssign e.toEquiv.symm ρ) = ρ := by
      funext i x
      rw [SOBlock.mapAssign, SOBlock.mapAssign]
      exact congrArg _ (funext fun j => e.toEquiv.apply_symm_apply _)
    rw [← prog.holds_equiv e (B.mapAssign e.toEquiv.symm ρ), hkey]
    exact hρ

end Iso

/-! ### SO-Krom definability -/

variable {L : Language.{0, 0}}

/-- A decision problem is *SO-Krom definable* if, on nonempty finite *ordered*
structures, it is defined by an existential second-order sentence with a Krom
kernel: there is a block of relation variables and a Krom program over the
ordered expansion of the vocabulary such that the yes-instances are exactly
the structures admitting a satisfying assignment.

This is the SO-Krom analogue of `DescriptiveComplexity.SigmaSOHornDefinable`; a single
block suffices, since existential second-order quantifiers merge.

As for SO-Horn, the guards live over `L.sum Language.order` and the equivalence
is required for *every* linear order on `A`, so this is order-invariant
SO-Krom definability: the order is the setting of Grädel's capture theorem, and
it is forced by closure under ordered first-order reductions
(`DescriptiveComplexity.SigmaSOKromDefinable.of_orderedReduction`), which pull the
lexicographic order of the interpreted universe back into the guards. Nor can
the order be guessed away, as it is for the existential logics and – see
`DescriptiveComplexity.sotcDefinable_iff_free` – for SO(TC): a Krom kernel
cannot state that a guessed relation is transitive, that clause having three
second-order literals. -/
def SigmaSOKromDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ (B : SOBlock) (k : ℕ) (prog : KromProgram (L.sum Language.order) B k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ ∃ ρ : B.Assignment A, prog.Holds ρ

/-- SO-Krom definability only depends on the finite instances of a problem. -/
theorem sigmaSOKromDefinable_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    SigmaSOKromDefinable P ↔ SigmaSOKromDefinable Q := by
  constructor <;> rintro ⟨B, k, prog, hprog⟩ <;> refine ⟨B, k, prog, ?_⟩ <;>
    intro A _ _ _ _
  · exact (h A).symm.trans (hprog A)
  · exact (h A).trans (hprog A)

end DescriptiveComplexity
