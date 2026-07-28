/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat
import DescriptiveComplexity.Difference

/-!
# SAT-UNSAT, the canonical DP problem

**SAT-UNSAT** ([Papadimitriou & Yannakakis 1984][papadimitriou1984complexity]):
given *two* CNF formulas, is the first satisfiable *and* the second not? It is
the prototypical problem of `DescriptiveComplexity.DP`, the class of differences of
NP problems, and it wears its DP definition on its sleeve – one half is an NP
condition, the other a coNP one, and they are imposed on disjoint parts of the
vocabulary.

## The vocabulary

An instance carries the two formulas side by side: `Language.satPair` is two
copies of `Language.sat`, one per side. Both live on the same universe – there
is no need to keep the two formulas' variables apart, since each side's clauses
only mention their own occurrence relations, and a truth assignment for one
side is free to do as it likes on the other side's variables.

## What is here, and what is not

The vocabulary, the semantics and isomorphism-invariance, and the three
problems: `DescriptiveComplexity.SATUNSAT` itself together with its two halves
`DescriptiveComplexity.SatFirst` (an NP condition) and
`DescriptiveComplexity.UnsatSecond` (a coNP one), which are what a DP definition of
it will conjoin. Satisfiability of a side is stated once, parameterized by the
triple of relation symbols to read (`DescriptiveComplexity.SatWith`), since the two
sides differ only in that.

**Membership in DP and DP-hardness are not formalized yet.** Membership needs
the `Σ₁` kernel of `DescriptiveComplexity.sat_sigmaSODefinable` restated for a
parameterized symbol triple – the realization proof there is a `simp` normal
form that does not survive replacing the concrete relation symbols by
variables, so it wants either two copies of the kernel or a transport along the
language morphism embedding one side. Hardness needs the Cook–Levin discharge
and its complement run side by side into a single paired instance (see the note
in `DescriptiveComplexity.Difference`).
-/

namespace FirstOrder

namespace Language

/-- Relation symbols of the language of *pairs* of CNF instances: two copies of
`Language.satRel`, one per side. -/
inductive satPairRel : ℕ → Type
  /-- `isClause₁ c`: `c` is a clause of the first formula. -/
  | isClause₁ : satPairRel 1
  /-- `posIn₁ c x`: `x` occurs positively in the first formula's clause `c`. -/
  | posIn₁ : satPairRel 2
  /-- `negIn₁ c x`: `x` occurs negatively in the first formula's clause `c`. -/
  | negIn₁ : satPairRel 2
  /-- `isClause₂ c`: `c` is a clause of the second formula. -/
  | isClause₂ : satPairRel 1
  /-- `posIn₂ c x`: `x` occurs positively in the second formula's clause `c`. -/
  | posIn₂ : satPairRel 2
  /-- `negIn₂ c x`: `x` occurs negatively in the second formula's clause `c`. -/
  | negIn₂ : satPairRel 2
  deriving DecidableEq

/-- The relational vocabulary of pairs of CNF instances. -/
protected def satPair : Language :=
  ⟨fun _ => Empty, satPairRel⟩
  deriving IsRelational

/-- “Is a clause of the first formula”. -/
abbrev spIsCl₁ : Language.satPair.Relations 1 := .isClause₁

/-- “Occurs positively in”, first formula. -/
abbrev spPos₁ : Language.satPair.Relations 2 := .posIn₁

/-- “Occurs negatively in”, first formula. -/
abbrev spNeg₁ : Language.satPair.Relations 2 := .negIn₁

/-- “Is a clause of the second formula”. -/
abbrev spIsCl₂ : Language.satPair.Relations 1 := .isClause₂

/-- “Occurs positively in”, second formula. -/
abbrev spPos₂ : Language.satPair.Relations 2 := .posIn₂

/-- “Occurs negatively in”, second formula. -/
abbrev spNeg₂ : Language.satPair.Relations 2 := .negIn₂

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Satisfiability of one side -/

section Defs

variable (A : Type) [Language.satPair.Structure A]

/-- Satisfiability of the side of the instance read by the given triple of
symbols: some assignment of truth values makes every clause of that side
contain a true literal. Both sides of `SAT-UNSAT` are instances of this. -/
def SatWith (isCl : Language.satPair.Relations 1)
    (pos neg : Language.satPair.Relations 2) : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap isCl ![c] →
    ∃ x : A, (RelMap pos ![c, x] ∧ ν x) ∨ (RelMap neg ![c, x] ∧ ¬ν x)

end Defs

section Iso

variable {A B : Type} [Language.satPair.Structure A] [Language.satPair.Structure B]

private theorem satWith_of_iso (e : A ≃[Language.satPair] B)
    (isCl : Language.satPair.Relations 1) (pos neg : Language.satPair.Relations 2)
    (h : SatWith A isCl pos neg) : SatWith B isCl pos neg := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨x, hx⟩ := hν (e.symm c) ((relMap_equiv₁ e.symm isCl c).mp hc)
  refine ⟨e x, ?_⟩
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · refine Or.inl ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e pos (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e neg (e.symm c) x).mp hn

/-- Satisfiability of a side is isomorphism-invariant. -/
theorem satWith_iso (e : A ≃[Language.satPair] B) (isCl : Language.satPair.Relations 1)
    (pos neg : Language.satPair.Relations 2) :
    SatWith A isCl pos neg ↔ SatWith B isCl pos neg :=
  ⟨satWith_of_iso e isCl pos neg, satWith_of_iso e.symm isCl pos neg⟩

end Iso

/-- The first formula of the pair is satisfiable: the NP half of SAT-UNSAT. -/
def SatFirst : DecisionProblem Language.satPair where
  Holds := fun A inst => @SatWith A inst spIsCl₁ spPos₁ spNeg₁
  iso_invariant := fun e => satWith_iso e _ _ _

/-- The second formula of the pair is unsatisfiable: the coNP half. -/
def UnsatSecond : DecisionProblem Language.satPair where
  Holds := fun A inst => ¬@SatWith A inst spIsCl₂ spPos₂ spNeg₂
  iso_invariant := fun e => not_congr (satWith_iso e _ _ _)

/-- **SAT-UNSAT**: the first formula of the pair is satisfiable and the second
is not. -/
def SATUNSAT : DecisionProblem Language.satPair where
  Holds := fun A inst =>
    @SatWith A inst spIsCl₁ spPos₁ spNeg₁ ∧ ¬@SatWith A inst spIsCl₂ spPos₂ spNeg₂
  iso_invariant := fun e =>
    and_congr (satWith_iso e _ _ _) (not_congr (satWith_iso e _ _ _))

end DescriptiveComplexity
