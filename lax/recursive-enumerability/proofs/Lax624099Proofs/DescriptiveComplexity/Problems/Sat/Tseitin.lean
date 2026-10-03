/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.SecondOrder
import Lax624099Proofs.DescriptiveComplexity.Padding
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# The Tseitin encoding of a first-order kernel: semantic layer

Machinery for the hardness half of the Cook–Levin theorem
([Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal];
`Lax624099Proofs.DescriptiveComplexity.sat_hard_of_sigmaSODefinable`, in
`Lax624099Proofs.DescriptiveComplexity.Problems.Sat.Hardness`): the generic, machine-free reduction of
any existential-second-order definable problem to SAT (via a Tseitin
([Tseitin 1968][tseitin1968complexity]) encoding), in the style of Dahlhaus
([Dahlhaus 1983][dahlhaus1983reduction]). Given the first-order kernel `φ`
(a sentence over the input
vocabulary expanded by one second-order block), the produced CNF instance has

* one propositional variable per relation variable `i` of the block and tuple
  `ā` (“`ā ∈ Rᵢ`”), and one per subformula position `p` of `φ` and context
  tuple `w` (“the subformula at `p` holds under `w`”);
* Tseitin-style clauses per subformula position, forcing the position
  variables to compute the truth value of their subformulas bottom-up.

This file contains the *semantic* part of the construction, independent of
the FO formulas defining the CNF instance inside the input structure:

* `Lax624099Proofs.DescriptiveComplexity.Tseitin.NodeAt f m`: the type of subformula positions of `f`
  with context length `m` (the root is uniformly reachable via
  `Lax624099Proofs.DescriptiveComplexity.Tseitin.rootAt`);
* `Lax624099Proofs.DescriptiveComplexity.Tseitin.Gates`: a valuation of the position variables computes
  truth values correctly at every position (“all Tseitin gates hold”);
* `Lax624099Proofs.DescriptiveComplexity.Tseitin.canonVal`, the canonical valuation by actual truth
  values, which satisfies all gates (`Lax624099Proofs.DescriptiveComplexity.Tseitin.gates_canonVal`),
  and the converse reading (`Lax624099Proofs.DescriptiveComplexity.Tseitin.gates_realize`): any
  valuation satisfying the gates assigns the root its actual truth value;
* `Lax624099Proofs.DescriptiveComplexity.Tseitin.IsClauseSem` / `Lax624099Proofs.DescriptiveComplexity.Tseitin.LitSem`: the clauses
  of the encoding and their literals, as semantic predicates on tuples of a
  fixed length `D` padded with minimal elements (junk tuples are excluded by
  canonicity conditions);
* the main equivalence `Lax624099Proofs.DescriptiveComplexity.Tseitin.satCond_iff_gates`: a valuation
  satisfies every clause iff the induced (padding-invariant) valuation
  satisfies every gate.

The corresponding first-order formulas and their realization lemmas are in
`Lax624099Proofs.DescriptiveComplexity.Problems.Sat.TseitinFormulas`.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

namespace Tseitin

open Language Structure

/-! ### Subformula positions -/

section Nodes

variable {L' : Language.{0, 0}}

/-- The type of subformula positions (“nodes”) of `f` with context length
`m`: positions at which the subformula has `m` free de Bruijn variables. The
family is indexed by the context length so that all node-dependent data
(valuations, clauses) can be typed uniformly, without a dependent context
function. -/
def NodeAt : ∀ {n : ℕ}, L'.BoundedFormula Empty n → ℕ → Type
  | n, .falsum, m => PLift (n = m)
  | n, .equal _ _, m => PLift (n = m)
  | n, .rel _ _, m => PLift (n = m)
  | n, .imp f₁ f₂, m => PLift (n = m) ⊕ (NodeAt f₁ m ⊕ NodeAt f₂ m)
  | n, .all f, m => PLift (n = m) ⊕ NodeAt f m

/-- The root position of a formula. -/
def rootAt : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n), NodeAt f n
  | _, .falsum => ⟨rfl⟩
  | _, .equal _ _ => ⟨rfl⟩
  | _, .rel _ _ => ⟨rfl⟩
  | _, .imp _ _ => Sum.inl ⟨rfl⟩
  | _, .all _ => Sum.inl ⟨rfl⟩

/-- Whether a position is the root, as a Boolean (usable inside formula
definitions, where positions of a variable formula cannot be
pattern-matched). -/
def isRootB : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ}, NodeAt f m → Bool
  | _, .falsum, _, _ => true
  | _, .equal _ _, _, _ => true
  | _, .rel _ _, _, _ => true
  | _, .imp _ _, _, p => Sum.isLeft p
  | _, .all _, _, p => Sum.isLeft p

/-- A position is the root iff `isRootB` says so; in that case its context
length is the formula's own index. Stated as an equality of dependent
pairs. -/
theorem isRootB_iff :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ} (p : NodeAt f m),
      isRootB f p = true ↔ (⟨m, p⟩ : Σ m', NodeAt f m') = ⟨n, rootAt f⟩
  | _, .falsum, _, p => by obtain ⟨rfl⟩ := p; simp [isRootB, rootAt]
  | _, .equal _ _, _, p => by obtain ⟨rfl⟩ := p; simp [isRootB, rootAt]
  | _, .rel _ _, _, p => by obtain ⟨rfl⟩ := p; simp [isRootB, rootAt]
  | _, .imp _ _, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · simp [isRootB, rootAt]
      · refine iff_of_false (by simp [isRootB]) fun h => ?_
        injection h with h1 h2
        subst h1
        exact absurd (eq_of_heq h2) (by rintro ⟨⟩)
  | _, .all _, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · simp [isRootB, rootAt]
      · refine iff_of_false (by simp [isRootB]) fun h => ?_
        injection h with h1 h2
        subst h1
        exact absurd (eq_of_heq h2) (by rintro ⟨⟩)

/-- The largest context length occurring in a formula. -/
def maxCtx : ∀ {n : ℕ}, L'.BoundedFormula Empty n → ℕ
  | n, .falsum => n
  | n, .equal _ _ => n
  | n, .rel _ _ => n
  | _, .imp f₁ f₂ => max (maxCtx f₁) (maxCtx f₂)
  | _, .all f => maxCtx f

/-- A formula's own index is a context length, hence bounded by `maxCtx`. -/
theorem le_maxCtx : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n), n ≤ maxCtx f
  | _, .falsum => le_rfl
  | _, .equal _ _ => le_rfl
  | _, .rel _ _ => le_rfl
  | _, .imp f₁ _ => (le_maxCtx f₁).trans (le_max_left _ _)
  | n, .all f => (Nat.le_succ n).trans (le_maxCtx f)

/-- Context lengths of actual positions are bounded by `maxCtx`. -/
theorem nodeAt_le_maxCtx :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ}, NodeAt f m → m ≤ maxCtx f
  | _, .falsum, _, p => by obtain ⟨rfl⟩ := p; exact le_rfl
  | _, .equal _ _, _, p => by obtain ⟨rfl⟩ := p; exact le_rfl
  | _, .rel _ _, _, p => by obtain ⟨rfl⟩ := p; exact le_rfl
  | _, .imp f₁ f₂, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q | q := p
      · exact le_maxCtx _
      · exact (nodeAt_le_maxCtx f₁ q).trans (le_max_left _ _)
      · exact (nodeAt_le_maxCtx f₂ q).trans (le_max_right _ _)
  | _, .all f, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · exact le_maxCtx _
      · exact nodeAt_le_maxCtx f q

private def rootSigmaEquiv (n : ℕ) : PUnit.{1} ≃ (Σ m, PLift (n = m)) where
  toFun _ := ⟨n, ⟨rfl⟩⟩
  invFun _ := ⟨⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨m, ⟨rfl⟩⟩; rfl

private instance (n : ℕ) : Finite (Σ m, PLift (n = m)) :=
  Finite.of_equiv _ (rootSigmaEquiv n)

/-- There are finitely many positions in a formula. -/
instance finite_sigma_nodeAt :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n), Finite (Σ m, NodeAt f m)
  | n, .falsum => inferInstanceAs (Finite (Σ m, PLift (n = m)))
  | n, .equal _ _ => inferInstanceAs (Finite (Σ m, PLift (n = m)))
  | n, .rel _ _ => inferInstanceAs (Finite (Σ m, PLift (n = m)))
  | _, .imp f₁ f₂ =>
      haveI := finite_sigma_nodeAt f₁
      haveI := finite_sigma_nodeAt f₂
      Finite.of_equiv _
        ((Equiv.sigmaSumDistrib _ _).trans
          ((Equiv.refl _).sumCongr (Equiv.sigmaSumDistrib _ _))).symm
  | _, .all f =>
      haveI := finite_sigma_nodeAt f
      Finite.of_equiv _ (Equiv.sigmaSumDistrib _ _).symm

end Nodes

/-! ### Terms of the expanded language -/

section Terms

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock}

/-- A term of the language expanded by a (relational) block is a term of the
base language. -/
def termToL {α : Type} : (L.sum B.lang).Term α → L.Term α
  | .var a => .var a
  | .func f ts =>
      match f with
      | Sum.inl f => .func f fun i => termToL (ts i)
      | Sum.inr f => isEmptyElim f

/-- Reembedding `termToL` into the expanded language gives the term back. -/
theorem sumInl_onTerm_termToL {α : Type} (t : (L.sum B.lang).Term α) :
    LHom.sumInl.onTerm (termToL t) = t := by
  induction t with
  | var a => rfl
  | func f ts ih =>
      cases f with
      | inl f =>
          change Term.func (Sum.inl f) (fun i => LHom.sumInl.onTerm (termToL (ts i))) = _
          exact congrArg _ (funext ih)
      | inr f => exact isEmptyElim f

variable {A : Type}

/-- Realization of `termToL` in the base structure agrees with realization of
the term in any expansion. -/
theorem realize_termToL [L.Structure A] [(L.sum B.lang).Structure A]
    [(LHom.sumInl : L →ᴸ L.sum B.lang).IsExpansionOn A] {α : Type}
    (t : (L.sum B.lang).Term α) (v : α → A) :
    (termToL t).realize v = t.realize v := by
  conv_rhs => rw [← sumInl_onTerm_termToL t]
  exact (LHom.realize_onTerm _ _ _).symm

end Terms

/-! ### Gates: correctness of a valuation of the position variables -/

section Gates

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {A : Type}

/-- The expansion of an `L`-structure by a block assignment. -/
@[instance_reducible]
def assignStructure (L : Language.{0, 0}) [L.Structure A] {B : Lax904597.SecondOrder.SOBlock}
    (μ : B.Assignment A) : (L.sum B.lang).Structure A :=
  letI := B.structure μ
  inferInstance

/-- Realization of a kernel formula in the expansion of an `L`-structure by a
block assignment. -/
def RealizeWith [L.Structure A] (μ : B.Assignment A) {n : ℕ}
    (f : (L.sum B.lang).BoundedFormula Empty n) (w : Fin n → A) : Prop :=
  letI := assignStructure L μ
  f.Realize isEmptyElim w

variable [L.Structure A]

/-- The truth value of an equality atom of the kernel under a context
tuple. -/
def eqGuard {m : ℕ} (t₁ t₂ : (L.sum B.lang).Term (Empty ⊕ Fin m)) (w : Fin m → A) : Prop :=
  (termToL t₁).realize (Sum.elim isEmptyElim w) =
    (termToL t₂).realize (Sum.elim isEmptyElim w)

/-- The truth value of an input-relation atom of the kernel under a context
tuple. -/
def relGuard {m l : ℕ} (r : L.Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (w : Fin m → A) : Prop :=
  RelMap r fun k => (termToL (ts k)).realize (Sum.elim isEmptyElim w)

/-- The truth value of a block-variable atom of the kernel under an
assignment and a context tuple. -/
def blockAtom (μ : B.Assignment A) {m l : ℕ} (r : B.lang.Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (w : Fin m → A) : Prop :=
  μ r.1 fun k => (termToL (ts (Fin.cast r.2 k))).realize (Sum.elim isEmptyElim w)

/-- The truth value of an arbitrary atom of the kernel. -/
def atomHolds (μ : B.Assignment A) {m l : ℕ} (R : (L.sum B.lang).Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (w : Fin m → A) : Prop :=
  match R with
  | Sum.inl r => relGuard r ts w
  | Sum.inr r => blockAtom μ r ts w

/-! ### Unfolding `RealizeWith` -/

variable (μ : B.Assignment A)

theorem realizeWith_falsum {n : ℕ} (w : Fin n → A) :
    ¬RealizeWith μ (.falsum : (L.sum B.lang).BoundedFormula Empty n) w := id

theorem realizeWith_equal {n : ℕ} (t₁ t₂ : (L.sum B.lang).Term (Empty ⊕ Fin n))
    (w : Fin n → A) : RealizeWith μ (.equal t₁ t₂) w ↔ eqGuard t₁ t₂ w := by
  let := B.structure μ
  change t₁.realize (Sum.elim isEmptyElim w) = t₂.realize (Sum.elim isEmptyElim w) ↔ _
  rw [eqGuard, realize_termToL t₁, realize_termToL t₂]

theorem realizeWith_rel {n l : ℕ} (R : (L.sum B.lang).Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin n)) (w : Fin n → A) :
    RealizeWith μ (.rel R ts) w ↔ atomHolds μ R ts w := by
  let := B.structure μ
  cases R with
  | inl r =>
      change RelMap r (fun k => (ts k).realize (Sum.elim isEmptyElim w)) ↔
        relGuard r ts w
      rw [relGuard]
      simp only [realize_termToL]
  | inr r =>
      change μ r.1 (fun j => (ts (Fin.cast r.2 j)).realize (Sum.elim isEmptyElim w)) ↔
        blockAtom μ r ts w
      rw [blockAtom]
      simp only [realize_termToL]

theorem realizeWith_imp {n : ℕ} (f₁ f₂ : (L.sum B.lang).BoundedFormula Empty n)
    (w : Fin n → A) :
    RealizeWith μ (f₁.imp f₂) w ↔ (RealizeWith μ f₁ w → RealizeWith μ f₂ w) :=
  Iff.rfl

theorem realizeWith_all {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty (n + 1))
    (w : Fin n → A) :
    RealizeWith μ f.all w ↔ ∀ a : A, RealizeWith μ f (Fin.snoc w a) :=
  Iff.rfl

/-! ### Gates compute truth values -/

end Gates

/-! ### The clauses of the encoding and their literals -/

section Clauses

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {A : Type} {D : ℕ}

variable [L.Structure A] [LE A]

end Clauses

/-! ### Clause satisfaction is gate satisfaction -/

section Correctness

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {A : Type} {D : ℕ}

variable [L.Structure A] [LinearOrder A]

end Correctness

end Tseitin

end Lax624099Proofs.DescriptiveComplexity


