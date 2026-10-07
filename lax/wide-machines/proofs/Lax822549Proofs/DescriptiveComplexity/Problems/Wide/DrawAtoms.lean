/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawSpec
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawMatrix
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

/-!
# The atoms of a step matrix, classified

The EXPSPACE program evaluates the matrix of a step formula atom by atom
(`DescriptiveComplexity.Draw.qfValue`), and each atom gets a *different*
subroutine: a point equality is one file test, an order comparison another, a
relation of the expansion is an element-loop sub-fold, and a stage atom is a
random access. So the program's call sites are indexed by the atoms *with
their kinds*, and the kind must be **data** – computable from the formula
when the program is defined, not merely known to exist.

This file is that data. Over the matrix vocabulary – the base
`X.E.sum Language.order` expanded by the block, everything relational – a
term is a variable (`DescriptiveComplexity.Draw.matVar`), an atom is one of
four shapes (`DescriptiveComplexity.Draw.MatAtom`), the classifier
`DescriptiveComplexity.Draw.matAtom?` reads the shape off the syntax – total
on relation atoms, `none` only on non-atoms, which
`DescriptiveComplexity.Draw.qfAtoms` never emits
(`DescriptiveComplexity.Draw.isSome_matAtom?_of_mem_qfAtoms`) – and
`DescriptiveComplexity.Draw.realize_matAtom` is the semantic reading: the atom
holds at a valuation of the prefix exactly as its kind says, the stage atoms
reading the assignment, the order atoms the chosen order on points, the
expansion atoms the expanded structure.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### Terms are variables -/

/-- The variable a matrix term is: over a relational vocabulary with no free
names, nothing else is possible. -/
def matVar {LM : Language.{0, 0}} [LM.IsRelational] {n : ℕ} :
    LM.Term (Empty ⊕ Fin n) → Fin n
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr j) => j
  | .func f _ => isEmptyElim f

theorem realize_matVar {LM : Language.{0, 0}} [LM.IsRelational] {n : ℕ}
    {A : Type} [LM.Structure A] (xs : Empty → A) (w : Fin n → A) :
    ∀ t : LM.Term (Empty ⊕ Fin n), t.realize (Sum.elim xs w) = w (matVar t)
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr _) => rfl
  | .func f _ => isEmptyElim f

/-! ### The four kinds of atoms -/

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L}

variable {B : Lax904597.SecondOrder.SOBlock}

/-- **An atom of a step matrix, classified**: a point equality, an order
comparison, a relation of the expansion, or a stage atom of the iteration –
each with the prefix levels its arguments read. This is the index data of the
program's per-atom call sites. -/
inductive MatAtom (X : Lax480241.Expansions.ExpExpansion L) (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) : Type
  /-- A point equality between two prefix levels. -/
  | eq : Fin n → Fin n → MatAtom X B n
  /-- An order comparison between two prefix levels. -/
  | ord : Fin n → Fin n → MatAtom X B n
  /-- A relation of the expansion, at the given prefix levels. -/
  | exp : ∀ {k : ℕ}, X.E.Relations k → (Fin k → Fin n) → MatAtom X B n
  /-- An atom of the block's relation variables, at the given prefix levels: a
  *stage* of the iteration for a fixed-point program, a guessed relation for a
  nondeterministic one. -/
  | stage : (i : B.ι) → (Fin (B.arity i) → Fin n) → MatAtom X B n

/-- The classification of a relation atom, by its symbol's summand. -/
def relAtom : ∀ {n k : ℕ}, ((X.E.sum Language.order).sum B.lang).Relations k →
    (Fin k → ((X.E.sum Language.order).sum B.lang).Term (Empty ⊕ Fin n)) →
    MatAtom X B n
  | _, _, Sum.inl (Sum.inl e), ts => .exp e fun j => matVar (ts j)
  | _, _, Sum.inl (Sum.inr .le), ts => .ord (matVar (ts 0)) (matVar (ts 1))
  | _, _, Sum.inr b, ts => .stage b.1 fun j => matVar (ts (Fin.cast b.2 j))

/-- **The classifier**: the kind of an atom, read off the syntax; `none` only
on non-atoms. -/
def matAtom? : ∀ {n : ℕ},
    ((X.E.sum Language.order).sum B.lang).BoundedFormula Empty n →
      Option (MatAtom X B n)
  | _, .equal t₁ t₂ => some (.eq (matVar t₁) (matVar t₂))
  | _, .rel r ts => some (relAtom r ts)
  | _, .falsum => none
  | _, .imp _ _ => none
  | _, .all _ => none

/-- **Every atom of a matrix classifies**: the members of
`DescriptiveComplexity.Draw.qfAtoms` are equality and relation atoms, on which
the classifier is total. -/
theorem isSome_matAtom?_of_mem_qfAtoms :
    ∀ {n : ℕ} (ψ φ : ((X.E.sum Language.order).sum B.lang).BoundedFormula Empty n),
      φ ∈ qfAtoms ψ → (matAtom? φ).isSome := by
  intro n ψ
  induction ψ with
  | falsum => exact fun φ h => absurd h (List.not_mem_nil)
  | equal t₁ t₂ =>
    intro φ h
    rw [qfAtoms] at h
    rcases List.mem_singleton.mp h with rfl
    rfl
  | rel r ts =>
    intro φ h
    rw [qfAtoms] at h
    rcases List.mem_singleton.mp h with rfl
    rfl
  | imp f g ihf ihg =>
    intro φ h
    rw [qfAtoms] at h
    rcases List.mem_append.mp h with h | h
    · exact ihf φ h
    · exact ihg φ h
  | all f _ => exact fun φ h => absurd h (List.not_mem_nil)

/-! ### The semantic reading -/

section Semantics

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable [LinearOrder (X.Map A)]

/-- **What an atom says**, at a stage of the iteration and a valuation of the
prefix: the machine subroutine of the atom computes exactly this. -/
def MatAtom.holds (σ : B.Assignment (X.Map A)) {n : ℕ} (w : Fin n → X.Map A) :
    MatAtom X B n → Prop
  | .eq j₁ j₂ => w j₁ = w j₂
  | .ord j₁ j₂ => w j₁ ≤ w j₂
  | .exp e ts => RelMap (M := X.Map A) e fun j => w (ts j)
  | .stage i ts => σ i fun j => w (ts j)

omit [Finite A] [Nonempty A] in
/-- **The reading is correct**: a classified atom realizes at a valuation of
the prefix exactly as its kind says. -/
theorem realize_matAtom (σ : B.Assignment (X.Map A)) {n : ℕ}
    {φ : ((X.E.sum Language.order).sum B.lang).BoundedFormula Empty n}
    {κ : MatAtom X B n} (h : matAtom? φ = some κ) (w : Fin n → X.Map A) :
    (@BoundedFormula.Realize _ (X.Map A)
        (B.structure₁ (L := X.E.sum Language.order) σ) _ _ φ default w ↔
      κ.holds σ w) := by
  let inst := B.structure₁ (L := X.E.sum Language.order) σ
  match φ with
  | .falsum => simp [matAtom?] at h
  | .imp _ _ => simp [matAtom?] at h
  | .all _ => simp [matAtom?] at h
  | .equal t₁ t₂ =>
    obtain rfl : MatAtom.eq (X := X) (B := B) (matVar t₁) (matVar t₂) = κ :=
      Option.some.inj h
    change t₁.realize (Sum.elim default w) = t₂.realize (Sum.elim default w) ↔ _
    rw [realize_matVar, realize_matVar]
    exact Iff.rfl
  | .rel r ts =>
    obtain rfl : relAtom r ts = κ := Option.some.inj h
    change RelMap r (fun i => (ts i).realize (Sum.elim default w)) ↔ _
    simp only [realize_matVar]
    rcases r with (e | o) | b
    · exact Iff.rfl
    · cases o
      exact Iff.rfl
    · exact Iff.rfl

omit [Finite A] [Nonempty A] in
/-- **The matrix through its classified atoms**: a quantifier-free matrix
realizes exactly as its Boolean function at the kinds' readings – which is
what the machine computes once its per-atom subroutines have filled the
verdict slots. -/
theorem realize_iff_qfValue_holds {n : ℕ}
    {mat : ((X.E.sum Language.order).sum B.lang).BoundedFormula Empty n}
    (hqf : mat.IsQF) (σ : B.Assignment (X.Map A)) (w : Fin n → X.Map A) :
    (@BoundedFormula.Realize _ (X.Map A)
        (B.structure₁ (L := X.E.sum Language.order) σ) _ _ mat default w ↔
      qfValue mat fun a => (matAtom? a).elim False (MatAtom.holds σ w)) := by
  let inst := B.structure₁ (L := X.E.sum Language.order) σ
  refine (realize_qfValue hqf default w).trans (qfValue_congr _ _ _ fun a ha => ?_)
  obtain ⟨κ, hκ⟩ :=
    Option.isSome_iff_exists.mp (isSome_matAtom?_of_mem_qfAtoms mat a ha)
  rw [hκ]
  exact realize_matAtom σ hκ w

end Semantics

end Draw

end Lax822549Proofs.DescriptiveComplexity


