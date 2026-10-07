/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Copies
import Lax480241Proofs.DescriptiveComplexity.Composition
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

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# Claiming the block atoms of a quantifier-free matrix

The second of the two normal forms that let a *machine* evaluate a fixed
first-order sentence with a finite control.
`DescriptiveComplexity.Exponential.AltQuant` turned a sentence into an
alternating prefix over a quantifier-free matrix; the matrix still mentions the
block, whose atoms live on the machine's tape and are not available to a
transition. This file removes them:

> a quantifier-free matrix over two copies of a block is a **base formula**
> determined by the truth values of finitely many block atoms, whose addresses
> are read off the valuation.

`DescriptiveComplexity.exists_blockClaims` produces the finite list of
occurrences (`DescriptiveComplexity.BlockAtom`: a copy, a relation variable, and
where its arguments sit among the matrix's variables) and, for each vector of
*claimed* truth values, the base formula the matrix becomes.

## What a machine does with it

The claims are `Bool`s and the statement is conditional on their correctness,
which is exactly the shape of the standard alternating check: the existential
player claims the whole vector `b` in one move – there are finitely many, so
this is one nondeterministic transition – the universal player then either
challenges one claim, which the machine settles by a single tape lookup at the
address `(copy, var, args)` names, or lets the base formula be evaluated. The
base formula has no block atoms left, so it is a condition on the source
structure alone: a *guard of the transition relation*, written by the
interpretation that emits the machine, and never something the machine has to
compute.

Everything is stated for the two-copy structure
`DescriptiveComplexity.SOBlock.structure₂`, the shape of an
`DescriptiveComplexity.SOGameSpec.move`.

## The relation symbols are named

A relation symbol of the two-copy language is a nested `Sum`, and a goal
mentioning a raw `Sum.inl (Sum.inl r)` is ill-typed at `implicit`
transparency – `Language.sum` has to be unfolded for it to typecheck – so
`rw` and `simp` fail on it. The three shapes are therefore named
(`DescriptiveComplexity.twoBaseSym`, `DescriptiveComplexity.twoFstSym`,
`DescriptiveComplexity.twoSndSym`), the case analysis goes through
`DescriptiveComplexity.exists_symCase`, and every realization lemma is stated
at a named symbol.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language BoundedFormula

/-! ### An occurrence of a block atom -/

/-- **An occurrence of a block atom in a matrix**: which of the two copies of
the block it reads, which relation variable of the block, and where each of its
arguments sits among the matrix's variables.

This is an *address*: on a machine's tape the cell it names is
`(copy, var, args applied to the valuation)`. -/
structure BlockAtom (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) where
  /-- The copy of the block the occurrence reads: `false` is the first copy. -/
  copy : Bool
  /-- The relation variable of the block. -/
  var : B.ι
  /-- Where the arguments of the occurrence sit among the matrix's variables. -/
  args : Fin (B.arity var) → Fin n

namespace BlockAtom

variable {B : Lax904597.SecondOrder.SOBlock} {n : ℕ} {A : Type}

/-- The truth value of an occurrence, under two assignments and a valuation. -/
def Holds (a : BlockAtom B n) (ρ σ : B.Assignment A) (v : Fin n → A) : Prop :=
  cond a.copy σ ρ a.var fun j => v (a.args j)

end BlockAtom

/-! ### The relation symbols of the two-copy language -/

section Symbols

variable {K : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {l : ℕ}

/-- A relation symbol of the base vocabulary, read in the two-copy language. -/
abbrev twoBaseSym (r : K.Relations l) : ((K.sum B.lang).sum B.lang).Relations l :=
  Sum.inl (Sum.inl r)

/-- A relation variable of the *first* copy of the block. -/
abbrev twoFstSym (s : B.lang.Relations l) : ((K.sum B.lang).sum B.lang).Relations l :=
  Sum.inl (Sum.inr s)

/-- A relation variable of the *second* copy of the block. -/
abbrev twoSndSym (s : B.lang.Relations l) : ((K.sum B.lang).sum B.lang).Relations l :=
  Sum.inr s

/-- **The three shapes of a relation symbol of the two-copy language.** -/
theorem exists_symCase (R : ((K.sum B.lang).sum B.lang).Relations l) :
    (∃ r, R = twoBaseSym (B := B) r) ∨ (∃ s, R = twoFstSym (K := K) s) ∨
      (∃ s, R = twoSndSym (K := K) s) := by
  match R with
  | Sum.inl (Sum.inl r) => exact Or.inl ⟨r, rfl⟩
  | Sum.inl (Sum.inr s) => exact Or.inr (Or.inl ⟨s, rfl⟩)
  | Sum.inr s => exact Or.inr (Or.inr ⟨s, rfl⟩)

end Symbols

/-! ### Realization at the two-copy structure -/

section TwoRealize

variable {K : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {A : Type} [K.Structure A] {n : ℕ}

/-- Realization of a formula over two stacked copies of a block, at the
assignments `ρ` (first copy) and `σ` (second). -/
def twoRealize (mat : ((K.sum B.lang).sum B.lang).BoundedFormula Empty n)
    (ρ σ : B.Assignment A) (v : Fin n → A) : Prop :=
  letI := B.structure₂ (L := K) ρ σ
  mat.Realize default v

variable (ρ σ : B.Assignment A) (v : Fin n → A)

theorem twoRealize_bot :
    ¬ twoRealize (⊥ : ((K.sum B.lang).sum B.lang).BoundedFormula Empty n) ρ σ v :=
  id

theorem twoRealize_imp (φ₁ φ₂ : ((K.sum B.lang).sum B.lang).BoundedFormula Empty n) :
    twoRealize (φ₁.imp φ₂) ρ σ v ↔ (twoRealize φ₁ ρ σ v → twoRealize φ₂ ρ σ v) :=
  letI := B.structure₂ (L := K) ρ σ
  realize_imp

end TwoRealize

/-! ### Every quantifier-free matrix is a base formula plus claims -/

section Claims

variable {K : Language.{0, 0}} [K.IsRelational] {B : Lax904597.SecondOrder.SOBlock} {n : ℕ} {A : Type}
  [K.Structure A] {ρ σ : B.Assignment A}

/-- The bound variable a term of a relational language over `Empty ⊕ Fin n`
reads. -/
def bvarOf (x : Empty ⊕ Fin n) : Fin n := Sum.elim (fun e => e.elim) id x

theorem elim_bvarOf (v : Fin n → A) (d : Empty → A) (x : Empty ⊕ Fin n) :
    Sum.elim d v x = v (bvarOf x) := by
  cases x with
  | inl e => exact e.elim
  | inr _ => rfl

variable {v : Fin n → A}

/-- An equality of the matrix is an equality of two of its variables. -/
theorem twoRealize_bdEqual (t₁ t₂ : ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    twoRealize (t₁.bdEqual t₂) ρ σ v ↔ v (bvarOf t₁.varOf) = v (bvarOf t₂.varOf) := by
  let := B.structure₂ (L := K) ρ σ
  change (t₁.bdEqual t₂).Realize default v ↔ _
  rw [realize_bdEqual, Lax480241Proofs.Foreign.FirstOrder.Language.Term.realize_varOf, Lax480241Proofs.Foreign.FirstOrder.Language.Term.realize_varOf, elim_bvarOf, elim_bvarOf]

/-- The arguments of an atom, realized: they are the variables they name. -/
private theorem args_eq {l : ℕ}
    (ts : Fin l → ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    letI := B.structure₂ (L := K) ρ σ
    (fun q => Term.realize (Sum.elim (default : Empty → A) v) (ts q)) =
      fun q => v (bvarOf (ts q).varOf) := by
  let := B.structure₂ (L := K) ρ σ
  exact funext fun q => by rw [Lax480241Proofs.Foreign.FirstOrder.Language.Term.realize_varOf, elim_bvarOf]

/-- A base atom of the matrix is the same atom of the base structure. -/
theorem twoRealize_base {l : ℕ} (r : K.Relations l)
    (ts : Fin l → ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    twoRealize (Relations.boundedFormula (twoBaseSym (B := B) r) ts) ρ σ v ↔
      Structure.RelMap r fun q => v (bvarOf (ts q).varOf) := by
  let := B.structure₂ (L := K) ρ σ
  change (Relations.boundedFormula (twoBaseSym (B := B) r) ts).Realize default v ↔ _
  rw [realize_rel, args_eq (ρ := ρ) (σ := σ) ts]
  exact Iff.rfl

/-- An atom of the first copy is the first assignment, read at the addresses
its arguments name. -/
theorem twoRealize_fst {l : ℕ} (s : B.lang.Relations l)
    (ts : Fin l → ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    twoRealize (Relations.boundedFormula (twoFstSym (K := K) s) ts) ρ σ v ↔
      ρ s.1 fun j => v (bvarOf (ts (Fin.cast s.2 j)).varOf) := by
  let := B.structure₂ (L := K) ρ σ
  change (Relations.boundedFormula (twoFstSym (K := K) s) ts).Realize default v ↔ _
  rw [realize_rel, args_eq (ρ := ρ) (σ := σ) ts]
  exact Iff.rfl

/-- An atom of the second copy is the second assignment, read at the addresses
its arguments name. -/
theorem twoRealize_snd {l : ℕ} (s : B.lang.Relations l)
    (ts : Fin l → ((K.sum B.lang).sum B.lang).Term (Empty ⊕ Fin n)) :
    twoRealize (Relations.boundedFormula (twoSndSym (K := K) s) ts) ρ σ v ↔
      σ s.1 fun j => v (bvarOf (ts (Fin.cast s.2 j)).varOf) := by
  let := B.structure₂ (L := K) ρ σ
  change (Relations.boundedFormula (twoSndSym (K := K) s) ts).Realize default v ↔ _
  rw [realize_rel, args_eq (ρ := ρ) (σ := σ) ts]
  exact Iff.rfl

/-- **A quantifier-free matrix over two copies of a block is a base formula
determined by the truth values of finitely many block atoms.**

The atoms are listed once and for all; the base formula depends on the vector
of *claimed* values, and the equivalence holds as soon as the claims are
correct. That conditional form is what a machine needs: it guesses `b`, has the
claims challenged one at a time by tape lookups, and evaluates the base formula
as a guard of its transition relation. -/
theorem exists_blockClaims :
    ∀ {mat : ((K.sum B.lang).sum B.lang).BoundedFormula Empty n}, mat.IsQF →
      ∃ (m : ℕ) (atoms : Fin m → BlockAtom B n)
        (sub : (Fin m → Bool) → K.BoundedFormula Empty n),
        ∀ (A : Type) [K.Structure A] (ρ σ : B.Assignment A) (v : Fin n → A) (b : Fin m → Bool),
          (∀ j, b j = true ↔ (atoms j).Holds ρ σ v) →
          (twoRealize mat ρ σ v ↔ (sub b).Realize default v) := by
  intro mat h
  induction h with
  | falsum =>
    exact ⟨0, Fin.elim0, fun _ => ⊥, fun A _ ρ σ v b _ =>
      ⟨fun hc => (twoRealize_bot ρ σ v hc).elim, fun hc => hc.elim⟩⟩
  | @of_isAtomic φ ha =>
    cases ha with
    | equal t₁ t₂ =>
      refine ⟨0, Fin.elim0, fun _ => (Term.var (Sum.inr (bvarOf t₁.varOf)) :
          K.Term (Empty ⊕ Fin n)).bdEqual (Term.var (Sum.inr (bvarOf t₂.varOf))),
        fun A _ ρ σ v b _ => ?_⟩
      rw [twoRealize_bdEqual t₁ t₂, realize_bdEqual]
      rfl
    | rel R ts =>
      rcases exists_symCase R with ⟨r, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
      · refine ⟨0, Fin.elim0,
          fun _ => r.boundedFormula fun q => Term.var (Sum.inr (bvarOf (ts q).varOf)),
          fun A _ ρ σ v b _ => ?_⟩
        rw [twoRealize_base r ts, realize_rel]
        rfl
      · refine ⟨1, fun _ => ⟨false, s.1, fun j => bvarOf (ts (Fin.cast s.2 j)).varOf⟩,
          fun b => if b 0 = true then ⊤ else ⊥, fun A _ ρ σ v b hb => ?_⟩
        have hb0 : b 0 = true ↔ ρ s.1 fun j => v (bvarOf (ts (Fin.cast s.2 j)).varOf) := hb 0
        rw [twoRealize_fst s ts, ← hb0]
        cases hv : b 0 <;> simp [hv]
      · refine ⟨1, fun _ => ⟨true, s.1, fun j => bvarOf (ts (Fin.cast s.2 j)).varOf⟩,
          fun b => if b 0 = true then ⊤ else ⊥, fun A _ ρ σ v b hb => ?_⟩
        have hb0 : b 0 = true ↔ σ s.1 fun j => v (bvarOf (ts (Fin.cast s.2 j)).varOf) := hb 0
        rw [twoRealize_snd s ts, ← hb0]
        cases hv : b 0 <;> simp [hv]
  | @imp φ₁ φ₂ _ _ ih₁ ih₂ =>
    obtain ⟨m₁, atoms₁, sub₁, hsub₁⟩ := ih₁
    obtain ⟨m₂, atoms₂, sub₂, hsub₂⟩ := ih₂
    refine ⟨m₁ + m₂, Fin.addCases (motive := fun _ => BlockAtom B n) atoms₁ atoms₂,
      fun b => (sub₁ fun j => b (Fin.castAdd m₂ j)).imp (sub₂ fun j => b (Fin.natAdd m₁ j)),
      fun A _ ρ σ v b hb => ?_⟩
    have hb₁ : ∀ j, b (Fin.castAdd m₂ j) = true ↔ (atoms₁ j).Holds ρ σ v := by
      intro j
      rw [hb (Fin.castAdd m₂ j), Fin.addCases_left]
    have hb₂ : ∀ j, b (Fin.natAdd m₁ j) = true ↔ (atoms₂ j).Holds ρ σ v := by
      intro j
      rw [hb (Fin.natAdd m₁ j), Fin.addCases_right]
    rw [twoRealize_imp, realize_imp]
    exact imp_congr (hsub₁ A ρ σ v _ hb₁) (hsub₂ A ρ σ v _ hb₂)

end Claims

end Lax480241Proofs.DescriptiveComplexity


