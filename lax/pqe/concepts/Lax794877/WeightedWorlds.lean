import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Card
import Lax794877.PossibleWorlds
import Lax799700.Common
import Lax904597.SecondOrder
import Lax366625.CountingProblems
import Lax904597.Machines

/-!
---
title: Weighted possible worlds and the probability of a query
type: definition
---
A weighted instance gives every uncertain fact two weights, written in
binary along a linear order of the positions: a weight of presence $a$ and a
weight of absence $c$, the fact being present with probability $a/(a+c)$
independently of the others. The weight of a world is the product, over the
uncertain facts, of the weight each takes in it. Counting weighted possible
worlds is the counting problem whose value is the sum of the weights of the
worlds in which a sentence $\varphi$ holds, counted as the number of
witnesses that pick, for each uncertain fact, a number below its weight; it
is $0$ on an instance whose positions are not linearly ordered. The
probability of $\varphi$ is the probability of the event that it holds,
under the product distribution of the facts.
-/

namespace Lax794877.WeightedWorlds

open Lax794877.PossibleWorlds Lax799700.Common Lax904597.SecondOrder

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A probability assignment to a finite set `X` of Boolean variables: each
variable is assigned a rational probability in `[0, 1]`. -/
structure ProbAssignment (X : Type) where
  /-- The probability assigned to each variable. -/
  prob : X → ℚ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ x, 0 ≤ prob x
  /-- Probabilities are at most `1`. -/
  prob_le_one : ∀ x, prob x ≤ 1

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- Probability of a single valuation `v : X → Bool`, under the independence
assumption: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`. -/
def valProb (v : X → Bool) : ℚ :=
  ∏ x, if v x then P.prob x else 1 - P.prob x

/-- Probability of an event, a Boolean function of the valuation:
`Pr(f) = ∑_{v ⊨ f} Pr(v)`. -/
def funcProb (f : (X → Bool) → Bool) : ℚ :=
  ∑ v : X → Bool, if f v then P.valProb v else 0

end ProbAssignment

section Weights

variable (a c : X → ℕ)

/-- The probability assignment of a family of weights: the variable `x` is
true with probability `a x / (a x + c x)`. -/
def ProbAssignment.ofWeights (h : ∀ x, 0 < a x + c x) : ProbAssignment X where
  prob x := (a x : ℚ) / ((a x : ℚ) + c x)
  prob_nonneg x := div_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _))
  prob_le_one x := by
    have hpos : (0 : ℚ) < (a x : ℚ) + c x := by exact_mod_cast h x
    rw [div_le_one hpos]
    have : (0 : ℚ) ≤ c x := Nat.cast_nonneg _
    linarith

end Weights

open FirstOrder

open Language Structure

/-- The relation symbols of a weighted instance over the schema `L`: for each
symbol of the schema, the certain facts, the uncertain facts, and the bits of
the two weights of each fact; and one order, on the bit positions. -/
inductive WeightedRel (L : Language.{0, 0}) : ℕ → Type
  /-- The certain facts. -/
  | cert {n : ℕ} (R : L.Relations n) : WeightedRel L n
  /-- The uncertain facts. -/
  | unc {n : ℕ} (R : L.Relations n) : WeightedRel L n
  /-- `pres R (x̄, i)`: the bit of position `i` of the weight of the fact `R(x̄)`
  being present. -/
  | pres {n : ℕ} (R : L.Relations n) : WeightedRel L (n + 1)
  /-- `abs R (x̄, i)`: the bit of position `i` of the weight of the fact `R(x̄)`
  being absent. -/
  | abs {n : ℕ} (R : L.Relations n) : WeightedRel L (n + 1)
  /-- The order of the bit positions. -/
  | le : WeightedRel L 2

/-- The vocabulary of weighted instances over the schema `L`. -/
def weightedLang (L : Language.{0, 0}) : Language.{0, 0} :=
  ⟨fun _ => Empty, WeightedRel L⟩

instance (L : Language.{0, 0}) : (weightedLang L).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]

/-- The block guessing a weighted world: a world, and for each fact a number,
as the set of its bits. -/
def weightBlock (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] : SOBlock where
  ι := (Σ n, L.Relations n) ⊕ (Σ n, L.Relations n)
  arity := Sum.elim (fun p => p.1) fun p => p.1 + 1

section Kernel

variable {A : Type} [(weightedLang L).Structure A]

/-- The world of an assignment of the block. -/
def worldOf (σ : (weightBlock L).Assignment A) : (worldBlock L).Assignment A :=
  fun p x => σ (Sum.inl p) x

/-- The number an assignment of the block attaches to a fact, as its set of
bits. -/
def numOf (σ : (weightBlock L).Assignment A) (p : Σ n, L.Relations n) (x : Fin p.1 → A) :
    A → Prop :=
  fun i => σ (Sum.inr p) (Fin.snoc (α := fun _ => A) x i)

/-- The bits of a weight of a fact, read through a symbol of arity one more
than the fact's. -/
def bitsOf {n : ℕ} (S : WeightedRel L (n + 1)) (x : Fin n → A) : A → Prop :=
  fun i => RelMap (L := weightedLang L) S (Fin.snoc (α := fun _ => A) x i)

/-- The order of the positions of a weighted instance. -/
def WLe (L : Language.{0, 0}) (A : Type) [(weightedLang L).Structure A] (a b : A) : Prop :=
  RelMap (L := weightedLang L) WeightedRel.le ![a, b]

/-- One set of bits is below another, by the highest position at which they
differ. -/
def BitLt (Le : A → A → Prop) (b w : A → Prop) : Prop :=
  ∃ i, w i ∧ ¬b i ∧ ∀ j, Le i j → j ≠ i → (b j ↔ w j)

/-- What the kernel asks of an assignment at one fact: the world keeps a
certain fact and contains only certain or uncertain ones; at an *open* fact –
uncertain and not certain – the number is below the weight of presence if the
world keeps the fact, and below the weight of absence if not; at any other
fact the number is zero. -/
def WeightCond (σ : (weightBlock L).Assignment A) (p : Σ n, L.Relations n)
    (x : Fin p.1 → A) : Prop :=
  ((RelMap (L := weightedLang L) (WeightedRel.cert p.2) x → worldOf σ p x) ∧
      (worldOf σ p x → RelMap (L := weightedLang L) (WeightedRel.cert p.2) x ∨
        RelMap (L := weightedLang L) (WeightedRel.unc p.2) x)) ∧
    ((RelMap (L := weightedLang L) (WeightedRel.unc p.2) x ∧
          ¬RelMap (L := weightedLang L) (WeightedRel.cert p.2) x →
        (worldOf σ p x →
            BitLt (WLe L A) (numOf σ p x) (bitsOf (WeightedRel.pres p.2) x)) ∧
          (¬worldOf σ p x →
            BitLt (WLe L A) (numOf σ p x) (bitsOf (WeightedRel.abs p.2) x))) ∧
      (¬(RelMap (L := weightedLang L) (WeightedRel.unc p.2) x ∧
          ¬RelMap (L := weightedLang L) (WeightedRel.cert p.2) x) →
        ∀ i, ¬numOf σ p x i))

end Kernel

section Count

variable [L.IsRelational] {A : Type} [(weightedLang L).Structure A]

/-- The facts over a universe: a symbol of the schema and a tuple. -/
abbrev Fact (L : Language.{0, 0}) (A : Type) : Type := Σ p : Σ n, L.Relations n, Fin p.1 → A

/-- The fact is open: uncertain and not certain. -/
def IsOpen (q : Fact L A) : Prop :=
  RelMap (L := weightedLang L) (WeightedRel.unc q.1.2) q.2 ∧
    ¬RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2

/-- The open facts of a finite instance, as a finite type: the independent
Boolean variables of the instance. -/
noncomputable instance openFactFintype [Finite A] : Fintype {q : Fact L A // IsOpen q} :=
  Fintype.ofFinite _

/-- The weight of presence of an open fact. -/
noncomputable def presWeight (x : {q : Fact L A // IsOpen q}) : ℕ :=
  binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.pres x.1.1.2) x.1.2)

/-- The weight of absence of an open fact. -/
noncomputable def absWeight (x : {q : Fact L A // IsOpen q}) : ℕ :=
  binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.abs x.1.1.2) x.1.2)

/-- The world of a valuation of the open facts: the certain facts, and the
open facts the valuation makes true. -/
def worldOfVal (v : {q : Fact L A // IsOpen q} → Bool) : (worldBlock L).Assignment A :=
  fun p x => RelMap (L := weightedLang L) (WeightedRel.cert p.2) x ∨
    ∃ h : IsOpen (⟨p, x⟩ : Fact L A), v ⟨⟨p, x⟩, h⟩ = true

open Classical in
/-- The event “the sentence holds in the world”, as a Boolean function of the
valuation of the open facts. -/
noncomputable def holdsEvent (φ : L.Sentence) (v : {q : Fact L A // IsOpen q} → Bool) : Bool :=
  decide (@Sentence.Realize L A (worldStructure (worldOfVal v)) φ)

open Classical in
/-- **The probability of a sentence** over a weighted instance: each open fact
is present independently, with probability its weight of presence over the sum
of its two weights, and the probability is that of the event that the sentence
holds in the resulting world. -/
noncomputable def worldProb [Finite A] (φ : L.Sentence)
    (hpos : ∀ x : {q : Fact L A // IsOpen q}, 0 < presWeight x + absWeight x) : ℚ :=
  (ProbAssignment.ofWeights presWeight absWeight hpos).funcProb (holdsEvent φ)

end Count

open Lax366625.CountingProblems Lax904597.Machines

/-- **Counting weighted possible worlds**: the witnesses are the worlds in which
the sentence `φ` holds, each with one number per open fact below the weight
that fact takes in the world. -/
noncomputable def WeightedWorlds {L : Language.{0, 0}} [Finite
    (Σ n, L.Relations n)] [L.IsRelational]
    (φ : L.Sentence) : CountingProblem (weightedLang L) :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {σ : (weightBlock L).Assignment A // IsLinOrd (WLe L A) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
      @Sentence.Realize L A (worldStructure (worldOf σ)) φ}

end Lax794877.WeightedWorlds
