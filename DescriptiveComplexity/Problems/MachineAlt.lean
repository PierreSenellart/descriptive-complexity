/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltDefs
import DescriptiveComplexity.Problems.Machine.AltOne
import DescriptiveComplexity.Problems.Machine.AltRound
import DescriptiveComplexity.Problems.Machine.AltMembership
import DescriptiveComplexity.Problems.Machine.AltInterp
import DescriptiveComplexity.Problems.Qbf
import DescriptiveComplexity.SecondOrderReplicate
import DescriptiveComplexity.MachinesAltPlay

/-!
# Alternating machine acceptance, and the machine bridge for the hierarchy

Umbrella file for `DescriptiveComplexity.ATMAccept k start`, the problem “does
this alternating Turing machine with `k` quantifier blocks accept its input
within as many steps as there are positions?”, with the machine carried by the
instance as in `DescriptiveComplexity.NTMAccept`.

The problem is the polynomial hierarchy's analogue of the machine bridge that
`DescriptiveComplexity.Problems.Machine` provides for NP and PTIME: the levels
`Σₖᵖ`/`Πₖᵖ` of this library are *defined* by second-order alternation, and the
bridge is to say that they are the levels of the alternating-machine hierarchy
of [Chandra–Kozen–Stockmeyer 1981][chandra1981alternation].

## What is here

* **The model** – `DescriptiveComplexity.ATMData` and its acceptance
  (`DescriptiveComplexity.MachinesAlt`): a machine of
  `DescriptiveComplexity.TMData` whose states carry `k` block marks, with a
  budget recursion handing each move to the owner of the current state's block.
  The alternation bound is `DescriptiveComplexity.ATMData.BlocksWellFormed`,
  folded into the yes-instances: exactly one mark per state, and a transition
  either stays in its block or moves to the next one – a condition on a single
  transition, hence first-order.
* **The collapse lemmas** (`DescriptiveComplexity.MachinesAltPlay`), the
  mathematical content of the bridge's membership half: because the blocks are
  entered in order, the moves a player makes form one contiguous *play of the
  block*, so an existential block's configuration accepts exactly when *some*
  play of the block ends well
  (`DescriptiveComplexity.ATMData.altAcc_iff_exists_play`) and a universal
  one's exactly when *every* play does
  (`DescriptiveComplexity.ATMData.altAcc_iff_forall_play`). That is what lets a
  single second-order quantifier commit a whole phase of the run.
* **The round game** (`DescriptiveComplexity.Problems.Machine.AltGame`), the
  object the second-order blocks of the membership proof guess: `k` rounds,
  each choosing a walk – a configuration per position – legal only as far as
  its own block and reproducing what the earlier rounds committed
  (`DescriptiveComplexity.ATMData.AltGame`).
* **The translation between a walk and a play**, which is where the unary time
  bound is cashed in: reading a play off a walk
  (`DescriptiveComplexity.ATMData.exists_play_of_legalBelow`) and splicing a
  play into one (`DescriptiveComplexity.ATMData.roundCond_splice`), on the rank
  arithmetic of `DescriptiveComplexity.Problems.Machine.AltRank`.
* **The round induction**
  (`DescriptiveComplexity.ATMData.altAccepts_iff_altGame`): alternating
  acceptance *is* the `k`-round game. This is the membership half's
  mathematical content, and all that is left of that half is to write the game
  down as a `Σₖ` sentence.
* **The membership half at every level**
  (`DescriptiveComplexity.Problems.Machine.AltMembership`): the game is turned
  into an implication ladder – a universal round always *has* a move, so the
  existence clause of `DescriptiveComplexity.guardQ` is redundant
  (`DescriptiveComplexity.Problems.Machine.AltLadder`) – the ladder is rewritten
  over the relations a second-order block guesses
  (`DescriptiveComplexity.Problems.Machine.AltRel`), its quantifiers become the
  alternating prefix over one guess per round
  (`DescriptiveComplexity.Problems.Machine.AltMatrix`), and what is left is the
  first-order kernel of `DescriptiveComplexity.Problems.Machine.AltKernel`. So
  `ATMAccept (k+1) true` is in `Σₖ₊₁ᵖ` and `ATMAccept (k+1) false` in `Πₖ₊₁ᵖ`.
* **The bridge at one block**, below: at `k = 1` and an existential prefix no
  state is universal, so the model is the nondeterministic one and
  `ATMAccept 1 true` is NP-complete – by two identity interpretations, one
  marking every element and one forgetting the mark under a guard.

* **The hardness half at every level**: the machine `M_φ` of a quantified
  Boolean formula, one guessing sweep per quantifier block, built inside an
  ordered QBF instance. Its tape is the instance's elements bracketed by two
  markers; sweep `i` walks it once in each direction, and the only choice it
  ever makes is whether to set the cell of a variable block `i` marks – so the
  moves of round `i` are exactly the truth assignments of block `i`
  (`DescriptiveComplexity.Problems.Machine.AltGuess`). After the last sweep a
  deterministic check phase walks the clauses, which is where the matrix is
  read (`DescriptiveComplexity.Problems.Machine.AltVerdict`). The rounds
  compose into the quantifier prefix
  (`DescriptiveComplexity.Problems.Machine.AltRounds`), and
  `DescriptiveComplexity.Problems.Machine.AltInterp` writes the machine down as
  a two-dimensional interpretation. So `ATMAccept (k+1) true` is `Σₖ₊₁ᵖ`-hard
  and `ATMAccept (k+1) false` is `Πₖ₊₁ᵖ`-hard.

Both halves are complete at every level, so the levels of this library's
hierarchy are the levels of the alternating-machine one.
-/

namespace DescriptiveComplexity

/-- **The machine bridge at one block**: alternating acceptance with a single
existential block is NP-complete, so the alternating model agrees with
`DescriptiveComplexity.NTMAccept` where the two overlap. -/
theorem atmAccept_one_complete : NP.Complete (ATMAccept 1 true) :=
  atmAccept_one_NP_complete

/-- **Alternating acceptance with an existential first block is in `Σₖ₊₁ᵖ`**,
the membership half of the bridge. -/
theorem atmAccept_mem_sigmaP' (k : ℕ) : ATMAccept (k + 1) true ∈ SigmaP (k + 1) :=
  atmAccept_mem_sigmaP k

/-- **Alternating acceptance with a universal first block is in `Πₖ₊₁ᵖ`.** -/
theorem atmAccept_mem_piP' (k : ℕ) : ATMAccept (k + 1) false ∈ PiP (k + 1) :=
  atmAccept_mem_piP k

/-- **Alternating acceptance is the `k`-round game**, the semantic content of
the membership half at every level: an alternating machine accepts exactly when
the owner of block `0` can choose a run of its block, the owner of block `1`
cannot avoid one of its own, and so on for `k` rounds. -/
theorem ATMData.accepts_iff_game {A : Type} [Finite A] {M : ATMData A} {k : ℕ}
    (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le) (hk : 0 < k)
    {p₀ p₁ : A} (hmin : MinPos M.Le M.Posn p₀) (hmax : MaxPos M.Le M.Posn p₁)
    (start : Bool) : M.AltAccepts start ↔ M.AltGame start k :=
  M.altAccepts_iff_altGame hbwf hlin hmax start hmin hk

/-! ### The hardness half -/

/-- **Alternating acceptance with an existential first block is `Σₖ₊₁ᵖ`-hard**:
`DescriptiveComplexity.QBF` reduces to it by building the machine `M_φ` of the
formula inside the instance, one guessing sweep per quantifier block. -/
theorem atmAccept_sigmaP_hard (k : ℕ) : (SigmaP (k + 1)).Hard (ATMAccept (k + 1) true) :=
  (SigmaP (k + 1)).hard_of_orderedReduction
    (AltQbf.qbf_ordered_fo_reduction_atmAccept (Nat.succ_pos k) true ((k + 1) % 2 == 1))
    (qbf_hard k)

/-- **Alternating acceptance with a universal first block is `Πₖ₊₁ᵖ`-hard**, by
the same reduction at the other starting polarity: the machine is the same, and
only the matrix shape and the block that moves first change. -/
theorem atmAccept_piP_hard (k : ℕ) : (PiP (k + 1)).Hard (ATMAccept (k + 1) false) :=
  (PiP (k + 1)).hard_of_orderedReduction
    (AltQbf.qbf_ordered_fo_reduction_atmAccept (Nat.succ_pos k) false ((k + 1) % 2 == 0))
    (qbfPi_hard k)

/-! ### The bridge -/

/-- **The machine bridge for the polynomial hierarchy, existential half**:
alternating acceptance with `k + 1` blocks, the first existential, is
`Σₖ₊₁ᵖ`-complete. The classes of this library are defined by second-order
alternation; this theorem says they are the levels of the alternating-machine
hierarchy of [Chandra–Kozen–Stockmeyer 1981][chandra1981alternation]. -/
theorem atmAccept_sigmaP_complete (k : ℕ) :
    (SigmaP (k + 1)).Complete (ATMAccept (k + 1) true) :=
  ⟨atmAccept_mem_sigmaP k, atmAccept_sigmaP_hard k⟩

/-- **The machine bridge, universal half**: with a universal first block,
`Πₖ₊₁ᵖ`-complete. -/
theorem atmAccept_piP_complete (k : ℕ) :
    (PiP (k + 1)).Complete (ATMAccept (k + 1) false) :=
  ⟨atmAccept_mem_piP k, atmAccept_piP_hard k⟩

/-- **The machine characterization of `Σₖ₊₁ᵖ`**: a problem sits at the `k+1`-st
level exactly when it ordered-FO-reduces to acceptance by an alternating
machine with `k + 1` blocks starting existentially. Forward through
`DescriptiveComplexity.QBF`, backward because membership travels along
reductions. -/
theorem mem_sigmaP_iff_le_atmAccept {L : FirstOrder.Language.{0, 0}} (k : ℕ)
    (P : DecisionProblem L) :
    P ∈ SigmaP (k + 1) ↔ Nonempty (P ≤ᶠᵒ[≤] ATMAccept (k + 1) true) := by
  constructor
  · intro hP
    obtain ⟨g⟩ := qbf_hard_of_sigmaSODefinable k P hP
    exact ⟨g.trans (AltQbf.qbf_ordered_fo_reduction_atmAccept
      (Nat.succ_pos k) true ((k + 1) % 2 == 1))⟩
  · rintro ⟨f⟩
    exact (SigmaP (k + 1)).mem_of_orderedReduction f (atmAccept_mem_sigmaP k)

/-- **The machine characterization of `Πₖ₊₁ᵖ`.** -/
theorem mem_piP_iff_le_atmAccept {L : FirstOrder.Language.{0, 0}} (k : ℕ)
    (P : DecisionProblem L) :
    P ∈ PiP (k + 1) ↔ Nonempty (P ≤ᶠᵒ[≤] ATMAccept (k + 1) false) := by
  constructor
  · intro hP
    obtain ⟨g⟩ := qbfPi_hard_of_piSODefinable k P hP
    exact ⟨g.trans (AltQbf.qbf_ordered_fo_reduction_atmAccept
      (Nat.succ_pos k) false ((k + 1) % 2 == 0))⟩
  · rintro ⟨f⟩
    exact (PiP (k + 1)).mem_of_orderedReduction f (atmAccept_mem_piP k)

end DescriptiveComplexity
