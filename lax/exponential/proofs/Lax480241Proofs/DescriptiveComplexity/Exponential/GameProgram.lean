/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.AltQuant
import Lax480241Proofs.DescriptiveComplexity.Exponential.BlockClaim
import Lax480241Proofs.DescriptiveComplexity.Exponential.Game
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

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# The six questions a machine playing a second-order game must answer

`DescriptiveComplexity.Exponential.AltQuant` and
`DescriptiveComplexity.Exponential.BlockClaim` are the two normal forms; this
file applies them to an `DescriptiveComplexity.SOGameSpec` and packages the
result as the interface a machine consumes.

## The six questions

A machine playing the game of a specification has to decide six sentences, not
four: the three one-copy sentences `won`, `univ`, `start`, the two-copy
sentence `move`, and the **negations** of `univ` and of `move`. The negations
are not a redundancy – a sentence is always used in the positive direction, an
existential branch that *proves* it and gets stuck otherwise, so refuting one
means proving another (`DescriptiveComplexity.GameQuestion`).

`DescriptiveComplexity.SOGameSpec.question` reads all six in the *same*
language, the two-copy one, the one-copy sentences traveling along
`FirstOrder.Language.LHom.sumInl`; that uniformity is what lets the machine's
tag be a plain product rather than a dependent sum.

## What the interface says

`DescriptiveComplexity.QuestionData` is what the machine's control needs about
one question:

* `vars` and `pol` – the length of the alternating prefix and whose turn each
  variable is, so a prefix phase is an index and a tuple coordinate;
* `atoms` – the occurrences of block atoms in the matrix, each an *address* on
  the tape;
* `sub` – for each vector of claimed truth values, the residual formula over
  the **base** vocabulary, which the interpretation writes into a transition
  guard.

`DescriptiveComplexity.QuestionData.Plays` states that this data decides the
sentence, and `DescriptiveComplexity.exists_questionData` produces it. The
matrix condition is stated as
`DescriptiveComplexity.QuestionData.MatrixHolds` – *there is a vector of
correct claims whose residual formula holds* – which is literally the round the
machine plays: the existential player claims the whole vector in one move, the
universal player challenges one claim by a tape lookup or lets the residual
formula be evaluated.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language BoundedFormula

/-! ### Reading a one-copy sentence in the two-copy language -/

section SumInl

variable {K : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {A : Type} [K.Structure A]

/-- A sentence over one copy of the block, read in the two-copy language, says
the same thing of the first copy. -/
theorem realize_sumInl_two (ρ σ : B.Assignment A) (ψ : (K.sum B.lang).Sentence) :
    @Sentence.Realize _ A (B.structure₂ (L := K) ρ σ)
        ((LHom.sumInl : (K.sum B.lang) →ᴸ ((K.sum B.lang).sum B.lang)).onSentence ψ) ↔
      @Sentence.Realize _ A (B.structure₁ (L := K) ρ) ψ :=
  letI := B.structure₁ (L := K) ρ
  letI := B.structure σ
  LHom.realize_onSentence (M := A) LHom.sumInl ψ

end SumInl

/-! ### The six questions -/

/-- **The six sentences a machine playing a second-order game must decide.**
The two negations are separate questions because a machine only ever *proves*:
an existential branch that fails to prove its sentence runs out of transitions,
so refuting a sentence has to be proving another one. -/
inductive GameQuestion
  /-- The current position wins outright. -/
  | won
  /-- The current position belongs to the universal player. -/
  | univ
  /-- The current position belongs to the existential player. -/
  | notUniv
  /-- The move from the current position to the candidate is legal. -/
  | move
  /-- The move from the current position to the candidate is illegal. -/
  | notMove
  /-- The current position starts the game. -/
  | start
  deriving DecidableEq

instance : Fintype GameQuestion :=
  ⟨{.won, .univ, .notUniv, .move, .notMove, .start}, by intro x; cases x <;> simp⟩

namespace SOGameSpec

variable {L : Language.{0, 0}} (spec : SOGameSpec L)

/-- The two-copy language of a specification: the base vocabulary and the
order, expanded by two copies of the block. -/
abbrev twoLang : Language.{0, 0} :=
  (((L.sum Language.order).sum spec.B.lang).sum spec.B.lang)

/-- **The sentence a question asks**, all six read in the two-copy language. -/
def question : GameQuestion → spec.twoLang.Sentence
  | .won => LHom.sumInl.onSentence spec.won
  | .univ => LHom.sumInl.onSentence spec.univ
  | .notUniv => ∼(LHom.sumInl.onSentence spec.univ)
  | .move => spec.move
  | .notMove => ∼spec.move
  | .start => LHom.sumInl.onSentence spec.start

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **What a question asks**, semantically: a condition on the current
position and the candidate. -/
def QuestionHolds (q : GameQuestion) (ρ σ : spec.State A) : Prop :=
  match q with
  | .won => spec.IsWon ρ
  | .univ => spec.IsUniv ρ
  | .notUniv => ¬ spec.IsUniv ρ
  | .move => spec.Move ρ σ
  | .notMove => ¬ spec.Move ρ σ
  | .start => spec.IsStart ρ

/-- **The sentence of a question says what the question asks.** -/
theorem realize_question (q : GameQuestion) (ρ σ : spec.State A) :
    @Sentence.Realize _ A (spec.B.structure₂ (L := L.sum Language.order) ρ σ) (spec.question q) ↔
      spec.QuestionHolds q ρ σ := by
  cases q with
  | won => exact realize_sumInl_two ρ σ spec.won
  | univ => exact realize_sumInl_two ρ σ spec.univ
  | notUniv =>
    let := spec.B.structure₂ (L := L.sum Language.order) ρ σ
    exact realize_not.trans (not_congr (realize_sumInl_two ρ σ spec.univ))
  | move => exact Iff.rfl
  | notMove =>
    let := spec.B.structure₂ (L := L.sum Language.order) ρ σ
    exact realize_not
  | start => exact realize_sumInl_two ρ σ spec.start

end SOGameSpec

/-! ### What the machine needs to know about one question -/

/-- **The machine-ready form of one sentence**: an alternating prefix, and a
matrix presented as finitely many block-atom addresses together with, for each
vector of claimed truth values, the residual formula over the base
vocabulary. -/
structure QuestionData (K : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) where
  /-- The number of variables of the prefix, and of the matrix. -/
  vars : ℕ
  /-- Whose turn each variable of the prefix is. -/
  pol : ℕ → Bool
  /-- The number of block-atom occurrences in the matrix. -/
  natoms : ℕ
  /-- The occurrences, each an address on the tape. -/
  atoms : Fin natoms → BlockAtom B vars
  /-- The residual formula, over the base vocabulary, of a vector of claims. -/
  sub : (Fin natoms → Bool) → K.BoundedFormula Empty vars

namespace QuestionData

variable {K : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} (d : QuestionData K B) {A : Type} [K.Structure A]

/-- **The matrix, as the machine settles it**: there is a vector of *correct*
claims about the block atoms whose residual formula holds. The existential
player claims the vector in one move; each claim is challengeable by a single
tape lookup, and the residual formula guards the transition that concludes. -/
def MatrixHolds (ρ σ : B.Assignment A) (w : Fin d.vars → A) : Prop :=
  ∃ b : Fin d.natoms → Bool,
    (∀ j, b j = true ↔ (d.atoms j).Holds ρ σ w) ∧ (d.sub b).Realize default w

/-- **The data decides the sentence**: the sentence is the alternating prefix
of the data, played over its matrix. The initial tuple is arbitrary – the
prefix overwrites every coordinate it reads. -/
def Plays (φ : ((K.sum B.lang).sum B.lang).Sentence) : Prop :=
  ∀ (A : Type) [K.Structure A] [Nonempty A] (ρ σ : B.Assignment A) (v : Fin d.vars → A),
    (@Sentence.Realize _ A (B.structure₂ ρ σ) φ ↔ altQuantFrom d.pol (d.MatrixHolds ρ σ) 0 v)

end QuestionData

/-- **Every sentence over two copies of a block has machine-ready form.** This
is the composite of the two normal forms, and it is everything a machine's
finite control needs in order to decide the sentence: a prefix of moves, a
finite set of tape addresses, and a family of transition guards over the base
vocabulary. -/
theorem exists_questionData {K : Language.{0, 0}} [K.IsRelational] {B : Lax904597.SecondOrder.SOBlock}
    (φ : ((K.sum B.lang).sum B.lang).Sentence) : ∃ d : QuestionData K B, d.Plays φ := by
  classical
  obtain ⟨n, pol, mat, hqf, hiff⟩ := exists_altQuant φ
  obtain ⟨m, atoms, sub, hsub⟩ := exists_blockClaims hqf
  refine ⟨⟨n, pol, m, atoms, sub⟩, fun A _ _ ρ σ v => ?_⟩
  refine Iff.trans (@hiff A (B.structure₂ ρ σ) ‹_› v) ?_
  refine iff_of_eq (congrArg (fun P => altQuantFrom pol P 0 v) (funext fun w => propext ?_))
  constructor
  · intro hmat
    refine ⟨fun j => decide ((atoms j).Holds ρ σ w), fun j => decide_eq_true_iff, ?_⟩
    exact (hsub A ρ σ w _ fun j => decide_eq_true_iff).mp hmat
  · rintro ⟨b, hb, hsb⟩
    exact (hsub A ρ σ w b hb).mpr hsb

end Lax480241Proofs.DescriptiveComplexity


