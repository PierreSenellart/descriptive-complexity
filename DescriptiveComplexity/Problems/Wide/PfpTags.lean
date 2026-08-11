/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Marks
import DescriptiveComplexity.Problems.Wide.Blocks

/-!
# The universe the EXPSPACE reduction draws

The first piece of the hardness reduction into
`DescriptiveComplexity.DWideAcceptSpace`: the shape of the instance it emits.

A reduction is an interpretation, so its universe is a **tagged tuple** universe
`PfpTag K × (Fin dd → A)`, and `DescriptiveComplexity.Wide.tagTupleLe_iff_lexRel`
says the only order it can define on that is the block-major one – one block of
the address per tag. Which tags there are, and in what order, is therefore the
layout of the whole tape, and it is fixed here:

| tag | what its block is for |
|---|---|
| `ctrl r` | nothing: the transitions of the **rule** `r` are elements of this block |
| `sym` | nothing: the symbols are elements of this block |
| `phase i` | nothing: the states are elements of these blocks, one block per call site |
| `arg i` | a **point-valued** block: an argument of the fixed-point variable, or a
  variable of the step formula's quantifier prefix |

The argument index `K` is an arbitrary type, not `Fin κ`, and that is not
generality for its own sake. A program's *outer* loop runs the head over the
valuations of the fixed-point variable, so it needs one block per argument of it;
its *inner* loop runs a register over the valuations of the quantifier prefix of
the step formula, and a register is an address too, so it needs one block per
quantified variable. There is no reason for those two counts to agree, and they do
not, so `K` is their sum. Putting the fixed-point's arguments first makes the
extra blocks the *deeper* ones, which costs nothing: a stage is written at the
argument blocks only, hence is constant along the blocks below them, and may be
read at any address with the right prefix.

There is one `ctrl` tag per **rule** of the transition table and one `phase` tag
per **call site** of the program. Indexing the transitions by their rule is what
lets a rule's source and destination phases, its direction and the kind of symbol
it reads be read off the *tag* rather than encoded in coordinates – the library's
"index rules by attribute values, not by the transition" read at the level of the
layout. Which is why the
program's phases are tags rather than an encoding in coordinates: a subroutine
called from several places uses different states at each, so it needs no
continuation label, and giving each call site a tag costs only a junk block that
every logical address is required to leave empty.

**The order is the point.** `ctrl` and `sym` come first, so they are the *most*
significant blocks of an address; the `arg` blocks come last. The addresses a
program reasons about – the valuations of the fixed-point variable, whose `ctrl`
and `sym` blocks are empty – are therefore an **initial interval** of the tape
(`DescriptiveComplexity.Pfp.wmSetLe_logicalTop`), which is what the loop primitive
`DescriptiveComplexity.reaches_of_wideRounds` wants as its bounds. And the least
element of the universe lies in the `ctrl` block, so every cell of the register
file – all of which contain it – sits above every logical address
(`DescriptiveComplexity.wmSetLt_wmSeg_of_not_bot`): the program's data and its
registers cannot collide.

The states and symbols are *elements* carrying those tags rather than addresses,
which is what keeps the control an ordinary, polynomial part of the instance while
the tape is exponential.
-/

namespace DescriptiveComplexity

namespace Pfp

/-! ### The tags

The rules and the phases are **arbitrary types**, not `Fin γ` and `Fin π`: a
program's transition table is written as an inductive with one constructor per
rule family and one per call site, and matching on such a type is what makes the
table readable and its case analyses `rfl`. All the layout asks of them is a
linear order, and *which* order is immaterial – nothing ever compares two rules
or two phases. What the order on tags has to say is only that the argument
blocks come last. -/

/-- **The tags of the interpreted universe**: the control, the alphabet, and one
block per argument of the fixed-point variable. -/
inductive PfpTag (R P K : Type) : Type
  /-- The transitions of the rule `r` of the table. -/
  | ctrl : R → PfpTag R P K
  /-- The tape alphabet. -/
  | sym : PfpTag R P K
  /-- The phase `p` of the program: one per call site, so that a subroutine
  called from several places uses different states at each and needs no
  continuation label. -/
  | phase : P → PfpTag R P K
  /-- A point-valued block: an argument of the fixed-point variable, or a
  variable of the step formula's quantifier prefix. -/
  | arg : K → PfpTag R P K

variable {R P K : Type}

/-- The place of a tag in the layout, as a point of a lexicographic sum: the
control first, the alphabet next, the phases after them and the argument blocks
last. This is what orders the tags, and so the blocks of an address. -/
def tagKey : PfpTag R P K → R ⊕ₗ (Unit ⊕ₗ (P ⊕ₗ K))
  | .ctrl r => Sum.inlₗ r
  | .sym => Sum.inrₗ (Sum.inlₗ ())
  | .phase p => Sum.inrₗ (Sum.inrₗ (Sum.inlₗ p))
  | .arg i => Sum.inrₗ (Sum.inrₗ (Sum.inrₗ i))

theorem tagKey_injective : Function.Injective (tagKey (R := R) (P := P) (K := K)) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [tagKey, Sum.inlₗ, Sum.inrₗ]

section Order

variable [LinearOrder R] [LinearOrder P] [LinearOrder K]

instance : LinearOrder (PfpTag R P K) := LinearOrder.lift' tagKey tagKey_injective

theorem le_iff_tagKey (σ τ : PfpTag R P K) : σ ≤ τ ↔ tagKey σ ≤ tagKey τ := Iff.rfl

/-- The argument blocks come after the control, the alphabet and the phases,
which is what makes the logical addresses an initial interval. -/
theorem lt_arg (τ : PfpTag R P K) (i : K) (h : ∀ j : K, τ ≠ PfpTag.arg j) :
    τ < PfpTag.arg i := by
  refine lt_of_le_of_ne ((le_iff_tagKey _ _).mpr ?_) (h i)
  cases τ with
  | ctrl r => simp [tagKey]
  | sym => simp [tagKey]
  | phase p => simp [tagKey]
  | arg j => exact absurd rfl (h j)

end Order

instance [Finite R] [Finite P] [Finite K] : Finite (PfpTag R P K) :=
  Finite.of_injective
    (fun t => match t with
      | .ctrl r => (Sum.inl r : R ⊕ Unit ⊕ P ⊕ K)
      | .sym => Sum.inr (Sum.inl ())
      | .phase p => Sum.inr (Sum.inr (Sum.inl p))
      | .arg i => Sum.inr (Sum.inr (Sum.inr i)))
    (by intro a b; cases a <;> cases b <;> simp)

/-! ### The logical addresses are an initial interval

A *logical* address is one whose non-argument blocks are empty: those are the
valuations of the fixed-point variable, and the cells that hold its stage. They
are exactly the addresses at or below the one whose argument blocks are full,
because the blocks they are required to empty are the most significant ones.
-/

variable {V : Type} {LeV : V → V → Prop}

/-- **The last logical address**: every argument block full, the non-argument blocks empty. -/
def logicalTop : PfpTag R P K × V → Prop :=
  fun p => ∃ i : K, p.1 = PfpTag.arg i

@[simp]
theorem logicalTop_arg (i : K) (v : V) :
    logicalTop (PfpTag.arg (R := R) (P := P) i, v) :=
  ⟨i, rfl⟩

/-- **A tag that is not an argument holds nothing of the last logical address.**
Stated for every such tag, so the layout may grow one without disturbing it. -/
theorem not_logicalTop {τ : PfpTag R P K} (h : ∀ i : K, τ ≠ PfpTag.arg i) (v : V) :
    ¬logicalTop (τ, v) := by
  rintro ⟨i, hi⟩
  exact h i hi

/-- **A logical address is at or below the last one.** The blocks it is required
to empty are the most significant ones – every tag that is not an argument – so
the comparison is settled in the argument blocks, where the full block is above
everything. Stated for *all* non-argument tags rather than for `ctrl` and `sym` by
name, so that the layout may grow a tag without disturbing this.

This is the upper bound a program's outer loop is given. -/
theorem wmSetLe_logicalTop [LinearOrder R] [LinearOrder P] [LinearOrder K]
    [Finite R] [Finite P] [Finite K] [Finite V]
    (hV : IsLinOrd LeV) {s : PfpTag R P K × V → Prop}
    (hjunk : ∀ τ : PfpTag R P K, (∀ i : K, τ ≠ PfpTag.arg i) → ∀ v : V, ¬s (τ, v)) :
    WMSetLe (lexRel (· ≤ · : PfpTag R P K → PfpTag R P K → Prop) LeV)
      s logicalTop := by
  classical
  by_cases hall : ∀ τ : PfpTag R P K, ∀ v : V, (s (τ, v) ↔ logicalTop (τ, v))
  · exact Or.inl fun p => hall p.1 p.2
  -- Some block differs; take the first, which cannot be `ctrl` or `sym`.
  refine Or.inr ((wmSetLt_lexRel_iff isLinOrd_le s logicalTop).mpr ?_)
  obtain ⟨τ, hτ, hmin⟩ :=
    exists_least (Le := (· ≤ · : PfpTag R P K → PfpTag R P K → Prop)) isLinOrd_le
    (P := fun τ => ¬∀ v : V, (wmBlk s τ v ↔ wmBlk logicalTop τ v))
    (by
      by_contra hc
      exact hall fun τ v => not_not.mp (fun hcon => hc ⟨τ, fun hall' => hcon (hall' v)⟩) )
  refine ⟨τ, fun σ hσ v => not_not.mp fun hc => ?_, ?_⟩
  · exact hσ.2 (hmin σ fun hall' => hc (hall' v))
  -- At the first differing block the address is strictly below a full block.
  obtain ⟨i, rfl⟩ : ∃ i : K, τ = PfpTag.arg i := by
    by_contra hc
    have hne : ∀ i : K, τ ≠ PfpTag.arg i := fun i hi => hc ⟨i, hi⟩
    exact hτ fun v => iff_of_false (hjunk τ hne v) (not_logicalTop hne v)
  refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_full hV (fun v => logicalTop_arg i v) _, fun hc => ?_⟩
  exact hτ fun v => iff_of_eq (congrFun hc v)

end Pfp

end DescriptiveComplexity
