/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.MachinesAlt
import DescriptiveComplexity.Problems.Machine.Defs

/-!
# Alternating machine acceptance as a decision problem

The vocabulary of the machine bridge for the polynomial hierarchy, and the
problem the bridge is about: an alternating Turing machine with `k` quantifier
blocks is *data in an instance*, and

> does this machine accept its input within as many steps as there are
> positions?

is `DescriptiveComplexity.ATMAccept k start`, an ordinary iso-invariant problem
of the catalog. The semantics it reads is
`DescriptiveComplexity.ATMData`, defined without a vocabulary in
`DescriptiveComplexity.MachinesAlt`.

## The vocabulary

`FirstOrder.Language.turingAlt k` is `FirstOrder.Language.turing` – every
symbol of which it carries verbatim, under the constructor `base` – together
with `k` unary marks `blk i` splitting the states into quantifier blocks,
exactly as `FirstOrder.Language.qbf k` extends the vocabulary of SAT by `k`
marks on the propositional variables. The two families of marks meet in the
hardness proof, which turns the block of a variable into the block of the state
guessing it.

Making the marks a *family* indexed by `Fin k`, rather than a fixed pair of
marks “existential”/“universal”, is what lets the alternation *bound* be
first-order: a transition may not decrease the block index, and may raise it by
at most one, so a run passes through the blocks in order and alternates at most
`k - 1` times. That promise – `DescriptiveComplexity.ATMData.BlocksWellFormed` –
is folded into the yes-instances alongside
`DescriptiveComplexity.TMData.WellFormed`, in the style of
`DescriptiveComplexity.IsLinOrd` for Knapsack.

## The two families

`ATMAccept k true` starts with an existential block and is the `Σₖᵖ` candidate;
`ATMAccept k false` starts with a universal one and is the `Πₖᵖ` candidate. The
two are the *same* problem up to the polarity parameter, so the `Πₖᵖ` half of
the bridge costs nothing beyond swapping the marks – the machine-side reading
of `DescriptiveComplexity.QBF` and `DescriptiveComplexity.QBFPi` sharing a
single reduction.
-/

/- The language of alternating machine instances lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.turing`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of alternating machine instances: those of
`FirstOrder.Language.turing`, and one unary mark per quantifier block. -/
inductive turingAltRel (k : ℕ) : ℕ → Type
  /-- A symbol of the underlying machine vocabulary. -/
  | base {n : ℕ} : turingRel n → turingAltRel k n
  /-- `blk i q`: the state `q` belongs to the `i`-th quantifier block. -/
  | blk : Fin k → turingAltRel k 1

/-- The relational vocabulary of alternating machine instances with `k`
quantifier blocks. -/
protected def turingAlt (k : ℕ) : Language :=
  ⟨fun _ => Empty, turingAltRel k⟩

instance (k : ℕ) : IsRelational (Language.turingAlt k) :=
  fun _ => ⟨fun f => Empty.elim f⟩

variable {k : ℕ}

/-- The position symbol. -/
abbrev atmPosn : (Language.turingAlt k).Relations 1 := .base .posn

/-- The transition symbol. -/
abbrev atmTr : (Language.turingAlt k).Relations 1 := .base .tr

/-- The start-state symbol. -/
abbrev atmStart : (Language.turingAlt k).Relations 1 := .base .start

/-- The accepting-state symbol. -/
abbrev atmAcc : (Language.turingAlt k).Relations 1 := .base .acc

/-- The blank symbol. -/
abbrev atmBlank : (Language.turingAlt k).Relations 1 := .base .blank

/-- The move-right symbol. -/
abbrev atmRight : (Language.turingAlt k).Relations 1 := .base .right

/-- The order symbol. -/
abbrev atmLe : (Language.turingAlt k).Relations 2 := .base .le

/-- The transition-source symbol. -/
abbrev atmSrc : (Language.turingAlt k).Relations 2 := .base .tsrc

/-- The transition-read symbol. -/
abbrev atmRead : (Language.turingAlt k).Relations 2 := .base .tread

/-- The transition-destination symbol. -/
abbrev atmDst : (Language.turingAlt k).Relations 2 := .base .tdst

/-- The transition-write symbol. -/
abbrev atmWrite : (Language.turingAlt k).Relations 2 := .base .twrite

/-- The input symbol. -/
abbrev atmInp : (Language.turingAlt k).Relations 2 := .base .inp

/-- The mark of the `i`-th quantifier block. -/
abbrev atmBlk (i : Fin k) : (Language.turingAlt k).Relations 1 := .blk i

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {k : ℕ} {A : Type} [(Language.turingAlt k).Structure A]

/-- Being a position. -/
def ATMPosn (a : A) : Prop := RelMap (atmPosn (k := k)) ![a]

/-- Being a transition. -/
def ATMTr (a : A) : Prop := RelMap (atmTr (k := k)) ![a]

/-- Being a start state. -/
def ATMStart (a : A) : Prop := RelMap (atmStart (k := k)) ![a]

/-- Being an accepting state. -/
def ATMAcc (a : A) : Prop := RelMap (atmAcc (k := k)) ![a]

/-- Being the blank symbol. -/
def ATMBlank (a : A) : Prop := RelMap (atmBlank (k := k)) ![a]

/-- Moving the head right. -/
def ATMRight (a : A) : Prop := RelMap (atmRight (k := k)) ![a]

/-- The order on positions. -/
def ATMLe (a b : A) : Prop := RelMap (atmLe (k := k)) ![a, b]

/-- The state a transition applies in. -/
def ATMSrc (a b : A) : Prop := RelMap (atmSrc (k := k)) ![a, b]

/-- The symbol a transition reads. -/
def ATMRead (a b : A) : Prop := RelMap (atmRead (k := k)) ![a, b]

/-- The state a transition moves to. -/
def ATMDst (a b : A) : Prop := RelMap (atmDst (k := k)) ![a, b]

/-- The symbol a transition writes. -/
def ATMWrite (a b : A) : Prop := RelMap (atmWrite (k := k)) ![a, b]

/-- The initial contents of a cell. -/
def ATMInp (a b : A) : Prop := RelMap (atmInp (k := k)) ![a, b]

/-- The block of a state, read off the marks: the marks of the vocabulary are
indexed by `Fin k`, so a block index beyond `k` marks nothing. This is what
makes the “exactly one mark, below `k`” clause of
`DescriptiveComplexity.ATMData.BlocksWellFormed` a first-order statement. -/
def ATMBlk (j : ℕ) (a : A) : Prop := ∃ h : j < k, RelMap (atmBlk (⟨j, h⟩ : Fin k)) ![a]

/-- The alternating machine an instance describes. -/
def atmData (k : ℕ) (A : Type) [(Language.turingAlt k).Structure A] : ATMData A where
  Posn := ATMPosn (k := k)
  Le := ATMLe (k := k)
  Tr := ATMTr (k := k)
  Start := ATMStart (k := k)
  Acc := ATMAcc (k := k)
  Blank := ATMBlank (k := k)
  Right := ATMRight (k := k)
  Src := ATMSrc (k := k)
  Read := ATMRead (k := k)
  Dst := ATMDst (k := k)
  Write := ATMWrite (k := k)
  Inp := ATMInp (k := k)
  Blk := ATMBlk (k := k)

end Shorthands

/-! ### The problem -/

section Problem

variable {k : ℕ} {A B : Type}
  [(Language.turingAlt k).Structure A] [(Language.turingAlt k).Structure B]

/-- **An isomorphism makes the two machines agree.** Every symbol of the
vocabulary transports, which is all `DescriptiveComplexity.ATMData.AltAgree`
asks for. -/
theorem altAgree_of_equiv (e : A ≃[Language.turingAlt k] B) :
    (atmData k B).AltAgree e.symm.toEquiv (atmData k A) := by
  have h1 : ∀ (r : (Language.turingAlt k).Relations 1) (b : B),
      (RelMap r ![b] : Prop) ↔ RelMap r ![(e.symm b : A)] := fun r b => by
    have h := relMap_equiv₁ e r (e.symm b)
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b] at h
    exact h.symm
  have h2 : ∀ (r : (Language.turingAlt k).Relations 2) (b b' : B),
      (RelMap r ![b, b'] : Prop) ↔ RelMap r ![(e.symm b : A), (e.symm b' : A)] := fun r b b' => by
    have h := relMap_equiv₂ e r (e.symm b) (e.symm b')
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b,
      show (e (e.symm b') : B) = b' from e.toEquiv.apply_symm_apply b'] at h
    exact h.symm
  exact ⟨⟨fun b => h1 atmPosn b, fun b b' => h2 atmLe b b', fun b => h1 atmTr b,
      fun b => h1 atmStart b, fun b => h1 atmAcc b, fun b => h1 atmBlank b,
      fun b => h1 atmRight b, fun b b' => h2 atmSrc b b', fun b b' => h2 atmRead b b',
      fun b b' => h2 atmDst b b', fun b b' => h2 atmWrite b b', fun b b' => h2 atmInp b b'⟩,
    fun j b => exists_congr fun h => h1 (atmBlk ⟨j, h⟩) b⟩

/-- **Alternating machine acceptance.** Does the alternating machine described
by the instance accept its input within as many steps as there are positions?
The prefix starts with an existential block when `start` is `true`.

Both promises are folded into the yes-instances, as
`DescriptiveComplexity.NTMAccept` folds in
`DescriptiveComplexity.TMData.WellFormed`: the machine is well formed, and its
`k` block marks partition the states into blocks entered in order. -/
def ATMAccept (k : ℕ) (start : Bool) : DecisionProblem (Language.turingAlt k) where
  Holds := fun A inst => @TMData.WellFormed A (atmData k A).toTMData ∧
    @ATMData.BlocksWellFormed A (atmData k A) k ∧
    @ATMData.AltAccepts A (atmData k A) start
  iso_invariant := fun {A B} _ _ e => by
    have h := altAgree_of_equiv e
    exact (and_congr h.base.wellFormed
      (and_congr (h.blocksWellFormed k) (h.altAccepts start))).symm

end Problem

/-! ### Reading the block marks

The marks of the vocabulary are indexed by `Fin k`, so
`DescriptiveComplexity.ATMBlk` is `False` beyond `k` by construction; the two
lemmas below are the only unfolding the rest of the development needs. -/

section Marks

variable {k : ℕ} {A : Type} [(Language.turingAlt k).Structure A]

/-- A marked state has a block index below `k`. -/
theorem lt_of_atmBlk {j : ℕ} {a : A} (h : ATMBlk (k := k) j a) : j < k :=
  h.1

/-- The mark of a block, with its index bound supplied. -/
theorem atmBlk_iff {j : ℕ} (h : j < k) (a : A) :
    ATMBlk (k := k) j a ↔ RelMap (atmBlk (⟨j, h⟩ : Fin k)) ![a] :=
  ⟨fun hb => hb.2, fun hb => ⟨h, hb⟩⟩

end Marks

/-! ### The one-block instances

At `k = 1` the vocabulary has a single mark, the only block is `0` and its
polarity is that of `start`; so for `start = true` no state is universal, and
the alternating model is the nondeterministic one
(`DescriptiveComplexity.ATMData.altAccepts_iff_accepts`). -/

section OneBlock

variable {A : Type} [(Language.turingAlt 1).Structure A]

/-- **At one block nothing is universal**, when the prefix starts
existentially: the only block is `0`, whose polarity is `true`. -/
theorem not_isUniv_one (q : A) : ¬(atmData 1 A).IsUniv true q := by
  rintro ⟨j, hj, hpol⟩
  obtain rfl : j = 0 := by have := lt_of_atmBlk (k := 1) hj; omega
  exact Bool.noConfusion hpol

/-- **At one block, well-formedness of the block structure is just that every
state is marked.** Uniqueness and monotonicity are automatic: there is only one
mark to carry. -/
theorem blocksWellFormed_one_iff :
    (atmData 1 A).BlocksWellFormed 1 ↔ ∀ q : A, ATMBlk (k := 1) 0 q := by
  constructor
  · intro h q
    obtain ⟨j, hjk, hj, -⟩ := h.1 q
    obtain rfl : j = 0 := by omega
    exact hj
  · intro h
    refine ⟨fun q => ⟨0, by omega, h q, fun j' hj' => ?_⟩,
      fun τ q q' j j' _ _ _ hj hj' => ?_, fun q _ => h q⟩
    · have := lt_of_atmBlk (k := 1) hj'
      omega
    · have h1 := lt_of_atmBlk (k := 1) hj
      have h2 := lt_of_atmBlk (k := 1) hj'
      omega

end OneBlock

end DescriptiveComplexity
