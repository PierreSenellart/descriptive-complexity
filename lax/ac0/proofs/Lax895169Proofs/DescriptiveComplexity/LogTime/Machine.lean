/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.LogTime.Bits
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

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax895169.LogTimeMachines
end Lax895169.LogTimeMachines

namespace Lax895169Proofs.DescriptiveComplexity.BitExpr
end Lax895169Proofs.DescriptiveComplexity.BitExpr

namespace Lax895169Proofs.DescriptiveComplexity.Sweep
end Lax895169Proofs.DescriptiveComplexity.Sweep

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (BitIx orank posCount prefixHolds)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.LogTimeMachines (BaseTest BitExpr LTDecidable LTMachine Sweep)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Alternating machines with a logarithmic clock, at the level of bits

The machine side of the bottom of the ladder: an **alternating random-access
machine** whose registers hold addresses of the instance, whose clock is the
number of *bit positions* of those addresses – logarithmic in the size of the
universe – and whose deterministic steps are **bit operations**, never a numeric
predicate.

## The three parts of a machine

* **Guesses.** A machine names `regs` registers and a polarity for each
  (`DescriptiveComplexity.LTMachine.pol`): the registers are filled in order,
  existentially or universally, by the two players. A register holds an element
  of the universe, that is, an address of `posCount A` bits, so filling one is a
  block of the classical `Σₖ-TIME(log n)` normal form – a logarithmic number of
  guessed bits – and an alternation is a change of polarity along the list.
* **Queries.** The instance is read only through
  `DescriptiveComplexity.BaseTest.query`: an input relation at a tuple of
  registers. This is the random access of the model, and in a structure-based
  framework it needs no index tape: *reading the input at an address is
  evaluating a relation at a tuple*.
* **Sweeps.** Everything the machine *computes* it computes bit by bit, with
  `DescriptiveComplexity.Sweep`: one pass over the bit positions, from the
  lowest to the highest, run by a finite automaton with `σ` state bits that
  reads, at each position, one bit of each register. A base test is a Boolean
  combination of sweeps, reads and queries, so a machine performs a *constant
  number of passes* over a logarithmic tape: a logarithmic clock, and a constant
  number of head reversals.
* **Reads.** `DescriptiveComplexity.BaseTest.bit`: the bit of one register at
  the position *named by another register*, that is,
  `DescriptiveComplexity.BitIx`. This is the second random access of the model –
  the machine addresses its own bits, not only the instance – and it is the one
  thing a sweep cannot do: finding the position `orank i` requires counting
  positions, which a finite automaton passing a constant number of bits cannot.

## Why the base has to be this weak, and what it can still do

Letting the base evaluate an atom of `≤`, `+` or `×` in one step would make the
model a prenex `FO(≤, +, ×)` sentence in disguise, and the bridge to the logic
vacuous. Sweeps and reads are the honest opposite: they see nothing but bits,
and the arithmetic has to be *built* – `DescriptiveComplexity.leSweep` and
`DescriptiveComplexity.plusSweep` (in `DescriptiveComplexity.LogTime.Arith`)
are the comparison and the ripple-carry addition, exactly as
`DescriptiveComplexity.HeadArith` builds them one resource bound higher. A read
is an addressing operation, not an arithmetic one: it computes nothing, and the
model still has no product.

Both restrictions are real, and their boundary is worth naming: a sweep carries
`σ` bits of state past each position, so a constant number of sweeps carries a
constant number of bits per position, that is, `O(log n)` bits of trace in
total – which is what a first-order formula can guess, one element per bit
vector (`DescriptiveComplexity.LogTime.Simulate`). A machine that could *count*
its positions, or revisit them unboundedly often, would leave that budget, and
with it the reach of the simulation.

Without the reads the model would be strictly weaker than AC⁰, and provably so:
with a base of sweeps alone every atom is a regular relation of the bit tracks,
alternating quantifiers over registers are projections, and the whole model
collapses to what a finite automaton reading `Nat.card A` in binary can decide.
That is the reason a read is a primitive here and not a convenience; see
`DescriptiveComplexity.LogTime`.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Boolean expressions over bits -/

namespace BitExpr

variable {V : Type}

/-- The value of an expression under a `Prop`-valued assignment: the reading a
first-order formula gives it. -/
def Holds (val : V → Prop) : Lax895169.LogTimeMachines.BitExpr V → Prop
  | .var v => val v
  | .tt => True
  | .ff => False
  | .not e => ¬ (Holds val e)
  | .and e f => (Holds val e) ∧ (Holds val f)
  | .or e f => (Holds val e) ∨ (Holds val f)

end BitExpr

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.BitExpr

export Lax895169Proofs.DescriptiveComplexity.BitExpr (Holds)

end Lax895169.LogTimeMachines.BitExpr

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitExpr

variable {V : Type}

/-- The two readings agree. -/
theorem holds_iff_eval (val : V → Bool) (e : Lax895169.LogTimeMachines.BitExpr V) :
    e.Holds (fun v => val v = true) ↔ e.eval val = true := by
  induction e with
  | var v => exact Iff.rfl
  | tt => simp [Holds, Lax895169.LogTimeMachines.BitExpr.eval]
  | ff => simp [Holds, Lax895169.LogTimeMachines.BitExpr.eval]
  | not e ih => simp [Holds, Lax895169.LogTimeMachines.BitExpr.eval, ih]
  | and e f ihe ihf => simp [Holds, Lax895169.LogTimeMachines.BitExpr.eval, ihe, ihf]
  | or e f ihe ihf => simp [Holds, Lax895169.LogTimeMachines.BitExpr.eval, ihe, ihf]

end BitExpr

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.BitExpr

export Lax895169Proofs.DescriptiveComplexity.BitExpr (holds_iff_eval)

end Lax895169.LogTimeMachines.BitExpr

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitExpr

variable {V : Type}

/-- Renaming the bit variables of an expression. -/
def mapVar {W : Type} (f : V → W) : Lax895169.LogTimeMachines.BitExpr V → Lax895169.LogTimeMachines.BitExpr W
  | .var v => .var (f v)
  | .tt => .tt
  | .ff => .ff
  | .not e => .not ((mapVar f e))
  | .and e g => .and ((mapVar f e)) ((mapVar f g))
  | .or e g => .or ((mapVar f e)) ((mapVar f g))

end BitExpr

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.BitExpr

export Lax895169Proofs.DescriptiveComplexity.BitExpr (mapVar)

end Lax895169.LogTimeMachines.BitExpr

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitExpr

variable {V : Type}

/-- Renaming bit variables is composition on the assignment. -/
theorem eval_mapVar {W : Type} (f : V → W) (val : W → Bool) (e : Lax895169.LogTimeMachines.BitExpr V) :
    (e.mapVar f).eval val = e.eval (val ∘ f) := by
  induction e with
  | var v => rfl
  | tt => rfl
  | ff => rfl
  | not e ih => rw [mapVar, Lax895169.LogTimeMachines.BitExpr.eval, ih, Lax895169.LogTimeMachines.BitExpr.eval]
  | and e g ihe ihg => rw [mapVar, Lax895169.LogTimeMachines.BitExpr.eval, ihe, ihg, Lax895169.LogTimeMachines.BitExpr.eval]
  | or e g ihe ihg => rw [mapVar, Lax895169.LogTimeMachines.BitExpr.eval, ihe, ihg, Lax895169.LogTimeMachines.BitExpr.eval]

end BitExpr

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.BitExpr

export Lax895169Proofs.DescriptiveComplexity.BitExpr (eval_mapVar)

end Lax895169.LogTimeMachines.BitExpr

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitExpr

variable {V : Type}

/-- Holding only depends on the assignment pointwise. -/
theorem holds_congr {val val' : V → Prop} (h : ∀ v, val v ↔ val' v) (e : Lax895169.LogTimeMachines.BitExpr V) :
    e.Holds val ↔ e.Holds val' := by
  induction e with
  | var v => exact h v
  | tt => exact Iff.rfl
  | ff => exact Iff.rfl
  | not e ih => exact not_congr ih
  | and e f ihe ihf => exact and_congr ihe ihf
  | or e f ihe ihf => exact or_congr ihe ihf

end BitExpr

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.BitExpr

export Lax895169Proofs.DescriptiveComplexity.BitExpr (holds_congr)

end Lax895169.LogTimeMachines.BitExpr

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitExpr

variable {V : Type}

end BitExpr

/-! ### Sweeps -/

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

omit [Finite A] in
@[simp]
theorem state_zero (S : Lax895169.LogTimeMachines.Sweep ρ) (x : Fin ρ → A) : S.state x 0 = S.init := rfl

end Sweep

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.Sweep

export Lax895169Proofs.DescriptiveComplexity.Sweep (state_zero)

end Lax895169.LogTimeMachines.Sweep

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

omit [Finite A] in
theorem state_succ (S : Lax895169.LogTimeMachines.Sweep ρ) (x : Fin ρ → A) (i : ℕ) (j : Fin S.σ) :
    S.state x (i + 1) j = (S.step j).eval
      (Sum.elim (S.state x i) fun k => (Lax895169.BitPredicate.orank (x k)).testBit i) := rfl

end Sweep

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.Sweep

export Lax895169Proofs.DescriptiveComplexity.Sweep (state_succ)

end Lax895169.LogTimeMachines.Sweep

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

/-- **Renaming the registers of a sweep**: what lets a sweep built once – the
comparison, the addition – be run on any registers of a larger machine. -/
def relabel {ρ' : ℕ} (S : Lax895169.LogTimeMachines.Sweep ρ) (f : Fin ρ → Fin ρ') : Lax895169.LogTimeMachines.Sweep ρ' where
  σ := S.σ
  init := S.init
  step := fun j => (S.step j).mapVar (Sum.map id f)
  acc := S.acc

end Sweep

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.Sweep

export Lax895169Proofs.DescriptiveComplexity.Sweep (relabel)

end Lax895169.LogTimeMachines.Sweep

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

omit [Finite A] in
/-- A renamed sweep runs the original one on the renamed registers. -/
theorem state_relabel {ρ' : ℕ} (S : Lax895169.LogTimeMachines.Sweep ρ) (f : Fin ρ → Fin ρ') (x : Fin ρ' → A) :
    ∀ (i : ℕ) (j : Fin S.σ), (S.relabel f).state x i j = S.state (fun k => x (f k)) i j := by
  intro i
  induction i with
  | zero => intro j; rfl
  | succ i ih =>
    intro j
    have h1 := BitExpr.eval_mapVar (Sum.map id f)
      (Sum.elim ((S.relabel f).state x i) fun k => (Lax895169.BitPredicate.orank (x k)).testBit i) (S.step j)
    have h2 : ((Sum.elim ((S.relabel f).state x i) fun k => (Lax895169.BitPredicate.orank (x k)).testBit i) ∘
        Sum.map id f) =
        Sum.elim (S.state (fun k => x (f k)) i) fun k => (Lax895169.BitPredicate.orank (x (f k))).testBit i := by
      funext z
      rcases z with j' | k
      · exact ih j'
      · rfl
    exact h1.trans (congrArg (fun v => (S.step j).eval v) h2)

end Sweep

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.Sweep

export Lax895169Proofs.DescriptiveComplexity.Sweep (state_relabel)

end Lax895169.LogTimeMachines.Sweep

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

/-- Acceptance of a renamed sweep. -/
theorem accepts_relabel {ρ' : ℕ} (S : Lax895169.LogTimeMachines.Sweep ρ) (f : Fin ρ → Fin ρ') (x : Fin ρ' → A) :
    (S.relabel f).Accepts x ↔ S.Accepts fun k => x (f k) := by
  have h : (S.relabel f).state x (Lax895169.BitPredicate.posCount A) = S.state (fun k => x (f k)) (Lax895169.BitPredicate.posCount A) :=
    funext fun j => state_relabel S f x _ j
  have hacc : (S.relabel f).Accepts x ↔ S.acc.eval ((S.relabel f).state x (Lax895169.BitPredicate.posCount A)) = true :=
    Iff.rfl
  rw [hacc, h]
  exact Iff.rfl

end Sweep

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.LogTimeMachines.Sweep

export Lax895169Proofs.DescriptiveComplexity.Sweep (accepts_relabel)

end Lax895169.LogTimeMachines.Sweep

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

end Sweep

/-! ### The deterministic base -/

namespace BaseTest

variable {L : Language.{0, 0}} {ρ : ℕ}

end BaseTest

/-! ### Machines, and the class they decide -/

/-- Prefixes only depend on their body pointwise. -/
theorem prefixHolds_congr {A : Type} :
    ∀ (m : ℕ) (pol : Fin m → Bool) {P Q : (Fin m → A) → Prop},
      (∀ v, P v ↔ Q v) → (Lax895169.BitPredicate.prefixHolds m pol P ↔ Lax895169.BitPredicate.prefixHolds m pol Q) := by
  intro m
  induction m with
  | zero => intro pol P Q h; exact h _
  | succ m ih =>
    intro pol P Q h
    refine ih (fun j => pol j.castSucc) fun v => ?_
    by_cases hp : pol (Fin.last m) = true
    · rw [if_pos hp, if_pos hp]
      exact exists_congr fun a => h _
    · rw [if_neg hp, if_neg hp]
      exact forall_congr' fun a => h _

/-! ### Prenexing: what a quantifier prefix does to the connectives

The three lemmas a bit-level *definability* API needs, so that a construction
built from the connectives and the quantifiers can be read off as a single
prefix over a quantifier-free kernel. They are about `prefixHolds` alone, and
they are what replaces a normal-form theorem: negation dualizes a prefix, a
prefix absorbs a side condition it does not mention, and two prefixes
concatenate. -/

/-- **Negating a prefix dualizes it**: every quantifier flips, and the body is
negated. Classical, as prenexing is. -/
theorem prefixHolds_not {A : Type} :
    ∀ (m : ℕ) (pol : Fin m → Bool) (P : (Fin m → A) → Prop),
      (¬ Lax895169.BitPredicate.prefixHolds m pol P) ↔ Lax895169.BitPredicate.prefixHolds m (fun j => !pol j) fun v => ¬ P v := by
  intro m
  induction m with
  | zero => intro pol P; exact Iff.rfl
  | succ m ih =>
    intro pol P
    rw [Lax895169.BitPredicate.prefixHolds, Lax895169.BitPredicate.prefixHolds, ih]
    refine prefixHolds_congr m _ fun v => ?_
    by_cases hp : pol (Fin.last m) = true
    · rw [if_pos hp, if_neg (by simp [hp])]
      exact not_exists
    · rw [if_neg hp, if_pos (by simp only [Bool.not_eq_true] at hp; simp [hp])]
      exact not_forall

/-- **A prefix absorbs a side condition** it does not mention. The universal
steps are what needs the universe to be nonempty. -/
theorem prefixHolds_and_const {A : Type} [Nonempty A] :
    ∀ (m : ℕ) (pol : Fin m → Bool) (P : (Fin m → A) → Prop) (Q : Prop),
      Lax895169.BitPredicate.prefixHolds m pol (fun v => P v ∧ Q) ↔ Lax895169.BitPredicate.prefixHolds m pol P ∧ Q := by
  intro m
  induction m with
  | zero => intro pol P Q; exact Iff.rfl
  | succ m ih =>
    intro pol P Q
    rw [Lax895169.BitPredicate.prefixHolds, Lax895169.BitPredicate.prefixHolds, ← ih]
    refine prefixHolds_congr m _ fun v => ?_
    by_cases hp : pol (Fin.last m) = true
    · rw [if_pos hp, if_pos hp]
      exact exists_and_right
    · rw [if_neg hp, if_neg hp]
      exact forall_and.trans (and_congr Iff.rfl (forall_const A))

/-- **Two prefixes concatenate**: a prefix of `k₁ + k₂` variables, read on a
body that splits its valuation into the first `k₁` and the last `k₂`, is the
first prefix wrapped around the second. This is the only place the index
arithmetic of `Fin` appears; everything downstream uses it as a black box. -/
theorem prefixHolds_add {A : Type} (k₁ : ℕ) :
    ∀ (k₂ : ℕ) (pol : Fin (k₁ + k₂) → Bool) (P : (Fin k₁ → A) → (Fin k₂ → A) → Prop),
      Lax895169.BitPredicate.prefixHolds (k₁ + k₂) pol
          (fun u => P (fun i => u (i.castAdd k₂)) fun j => u (j.natAdd k₁)) ↔
        Lax895169.BitPredicate.prefixHolds k₁ (fun i => pol (i.castAdd k₂))
          fun v => Lax895169.BitPredicate.prefixHolds k₂ (fun j => pol (j.natAdd k₁)) (P v) := by
  intro k₂
  induction k₂ with
  | zero =>
    intro pol P
    have hpol : (fun i : Fin k₁ => pol (i.castAdd 0)) = pol :=
      funext fun i => congrArg pol (Fin.ext rfl)
    rw [hpol]
    refine prefixHolds_congr k₁ _ fun u => ?_
    have h1 : (fun i : Fin k₁ => u (i.castAdd 0)) = u :=
      funext fun i => congrArg u (Fin.ext rfl)
    have h2 : (fun j : Fin 0 => u (j.natAdd k₁)) = Fin.elim0 := funext fun j => j.elim0
    rw [h1, h2]
    exact Iff.rfl
  | succ k₂ ih =>
    intro pol P
    have hstep : ∀ (v : Fin (k₁ + k₂) → A) (a : A) (w : Fin (k₁ + k₂ + 1) → A),
        w = Fin.snoc v a →
        (P (fun i => w (i.castAdd (k₂ + 1))) fun j => w (j.natAdd k₁)) =
          P (fun i => v (i.castAdd k₂)) (Fin.snoc (fun j => v (j.natAdd k₁)) a) := by
      intro v a w hw
      have h1 : (fun i : Fin k₁ => w (i.castAdd (k₂ + 1))) = fun i => v (i.castAdd k₂) := by
        funext i
        have h : (i.castAdd (k₂ + 1) : Fin (k₁ + k₂ + 1)) = (i.castAdd k₂).castSucc := Fin.ext rfl
        rw [hw, h, Fin.snoc_castSucc]
      have h2 : (fun j : Fin (k₂ + 1) => w (j.natAdd k₁)) =
          Fin.snoc (fun j : Fin k₂ => v (j.natAdd k₁)) a := by
        funext j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · have h : ((Fin.last k₂).natAdd k₁ : Fin (k₁ + k₂ + 1)) = Fin.last (k₁ + k₂) :=
            Fin.ext rfl
          rw [hw, h, Fin.snoc_last, Fin.snoc_last]
        · have h : ((j'.castSucc).natAdd k₁ : Fin (k₁ + k₂ + 1)) = (j'.natAdd k₁).castSucc :=
            Fin.ext rfl
          rw [hw, h, Fin.snoc_castSucc, Fin.snoc_castSucc]
      rw [h1, h2]
    refine Iff.trans (prefixHolds_congr (k₁ + k₂) (fun j => pol j.castSucc) ?_)
      (ih (fun j => pol j.castSucc)
        fun x y => if pol (Fin.last (k₁ + k₂)) = true then ∃ a, P x (Fin.snoc y a)
          else ∀ a, P x (Fin.snoc y a))
    intro v
    split
    · next hp =>
      have hp' : pol (Fin.last (k₁ + k₂)) = true := hp
      rw [if_pos hp']
      exact exists_congr fun a => Iff.of_eq (hstep v a _ rfl)
    · next hp =>
      have hp' : ¬ pol (Fin.last (k₁ + k₂)) = true := hp
      rw [if_neg hp']
      exact forall_congr' fun a => Iff.of_eq (hstep v a _ rfl)

/-- **A block of equal polarity is one quantifier** over the tuple it fills:
the existential case. -/
theorem prefixHolds_const_true {A : Type} :
    ∀ (m : ℕ) (P : (Fin m → A) → Prop),
      Lax895169.BitPredicate.prefixHolds m (fun _ => true) P ↔ ∃ w, P w := by
  intro m
  induction m with
  | zero =>
    intro P
    refine ⟨fun h => ⟨Fin.elim0, h⟩, fun hw => ?_⟩
    obtain ⟨w, hw⟩ := hw
    have hwe : w = Fin.elim0 := funext fun i => i.elim0
    rwa [hwe] at hw
  | succ m ih =>
    intro P
    refine Iff.trans (ih fun v => ∃ a, P (Fin.snoc v a)) ⟨?_, ?_⟩
    · rintro ⟨v, a, h⟩
      exact ⟨Fin.snoc v a, h⟩
    · rintro ⟨u, h⟩
      exact ⟨Fin.init u, u (Fin.last m), by rwa [Fin.snoc_init_self]⟩

/-- **A block of equal polarity is one quantifier**: the universal case. -/
theorem prefixHolds_const_false {A : Type} :
    ∀ (m : ℕ) (P : (Fin m → A) → Prop),
      Lax895169.BitPredicate.prefixHolds m (fun _ => false) P ↔ ∀ w, P w := by
  intro m
  induction m with
  | zero =>
    intro P
    refine ⟨fun h w => ?_, fun h => h _⟩
    have hwe : w = Fin.elim0 := funext fun i => i.elim0
    rwa [hwe]
  | succ m ih =>
    intro P
    refine Iff.trans (ih fun v => ∀ a, P (Fin.snoc v a)) ⟨?_, ?_⟩
    · intro h u
      have := h (Fin.init u) (u (Fin.last m))
      rwa [Fin.snoc_init_self] at this
    · intro h v a
      exact h _

end Lax895169Proofs.DescriptiveComplexity


