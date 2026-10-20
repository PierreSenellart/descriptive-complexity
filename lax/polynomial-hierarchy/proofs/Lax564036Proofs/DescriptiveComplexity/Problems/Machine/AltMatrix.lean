/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.AltRel
import Lax564036Proofs.DescriptiveComplexity.SecondOrderReplicate
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

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax564036Proofs.DescriptiveComplexity.ATMData
end Lax564036Proofs.DescriptiveComplexity.ATMData

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMData blockPol)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax564036Proofs.DescriptiveComplexity

/-!
# The matrix of the ladder

The ladder of `DescriptiveComplexity.Problems.Machine.AltLadder` alternates its
own quantifiers; a `Σₖ` sentence puts the alternation in the *prefix* and leaves
a quantifier-free chain behind. This file is that reshuffling, at the level of
the semantics: `DescriptiveComplexity.ATMData.runMatrix` is the ladder with its
quantifiers stripped – a conjunction where the round is existential, an
implication where it is universal (`DescriptiveComplexity.polConn`) – read at a
family of assignments, one per round, and
`DescriptiveComplexity.ATMData.altBlockQuant_runMatrix` puts the quantifiers
back as the alternating prefix `DescriptiveComplexity.altBlockQuant`.

The two lemmas that make it work pull a condition on the round already chosen
out of the quantifiers over the rounds still to come
(`DescriptiveComplexity.altBlockQuant_and_left` and
`DescriptiveComplexity.altBlockQuant_imp_left`); both need the assignments to
form a nonempty type, which they do – the empty relation is one.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

/-! ### Pulling a condition out of the prefix -/

/-- The connective a round of the ladder uses: a conjunction where the round is
existential, an implication where it is universal. -/
def polConn (pol : Bool) (X Y : Prop) : Prop :=
  match pol with
  | true => X ∧ Y
  | false => X → Y

section Pull

variable {A : Type} {B : Lax904597.SecondOrder.SOBlock}

/-- A conjunct that does not mention the quantified rounds comes out of the
prefix. -/
theorem altBlockQuant_and_left (ρ₀ : B.Assignment A) :
    ∀ (m : ℕ) (F : Prop) (P : (Fin m → B.Assignment A) → Prop) (pol : Bool),
      altBlockQuant A B m (fun ρs => F ∧ P ρs) pol ↔ F ∧ altBlockQuant A B m P pol := by
  intro m
  induction m with
  | zero => intro F P pol; exact Iff.rfl
  | succ m ih =>
    intro F P pol
    cases pol with
    | true =>
      refine (exists_congr fun ρ => ih F _ false).trans ?_
      exact ⟨fun ⟨ρ, hF, h⟩ => ⟨hF, ρ, h⟩, fun ⟨hF, ρ, h⟩ => ⟨ρ, hF, h⟩⟩
    | false =>
      refine (forall_congr' fun ρ => ih F _ true).trans ?_
      exact ⟨fun h => ⟨(h ρ₀).1, fun ρ => (h ρ).2⟩, fun h ρ => ⟨h.1, h.2 ρ⟩⟩

/-- A hypothesis that does not mention the quantified rounds comes out of the
prefix. -/
theorem altBlockQuant_imp_left (ρ₀ : B.Assignment A) :
    ∀ (m : ℕ) (F : Prop) (P : (Fin m → B.Assignment A) → Prop) (pol : Bool),
      altBlockQuant A B m (fun ρs => F → P ρs) pol ↔ (F → altBlockQuant A B m P pol) := by
  classical
  intro m
  induction m with
  | zero => intro F P pol; exact Iff.rfl
  | succ m ih =>
    intro F P pol
    cases pol with
    | true =>
      refine (exists_congr fun ρ => ih F _ false).trans ?_
      by_cases hF : F
      · exact ⟨fun ⟨ρ, h⟩ _ => ⟨ρ, h hF⟩, fun h => ⟨(h hF).choose, fun _ => (h hF).choose_spec⟩⟩
      · exact ⟨fun _ hcon => absurd hcon hF, fun _ => ⟨ρ₀, fun hcon => absurd hcon hF⟩⟩
    | false =>
      refine (forall_congr' fun ρ => ih F _ true).trans ?_
      exact ⟨fun h hF ρ => h ρ hF, fun h ρ hF => h hF ρ⟩

/-- **One round of the prefix.** The outermost block of the prefix is the round
`DescriptiveComplexity.bareQ` quantifies, once the condition on it is pulled out
of the blocks that follow. -/
theorem altBlockQuant_step (ρ₀ : B.Assignment A) (m : ℕ) (pol : Bool)
    (C : B.Assignment A → Prop) (Q : B.Assignment A → (Fin m → B.Assignment A) → Prop)
    (R : B.Assignment A → Prop) (h : ∀ ρ, altBlockQuant A B m (Q ρ) (!pol) ↔ R ρ) :
    altBlockQuant A B (m + 1)
        (fun ρs => polConn pol (C (ρs 0)) (Q (ρs 0) fun j => ρs j.succ)) pol ↔
      bareQ pol C R := by
  cases pol with
  | true =>
    refine exists_congr fun ρ => ?_
    refine (altBlockQuant_congr m _ (fun ρs => C ρ ∧ Q ρ ρs) (fun _ => Iff.rfl) false).trans ?_
    exact (altBlockQuant_and_left ρ₀ m _ _ false).trans (and_congr Iff.rfl (h ρ))
  | false =>
    refine forall_congr' fun ρ => ?_
    refine (altBlockQuant_congr m _ (fun ρs => C ρ → Q ρ ρs) (fun _ => Iff.rfl) true).trans ?_
    exact (altBlockQuant_imp_left ρ₀ m _ _ true).trans (imp_congr Iff.rfl (h ρ))

end Pull

namespace ATMData

variable {A : Type}

/-! ### The matrix -/

/-- The condition round `i` puts on its guess, with the round before it – or
nothing at all, at the first round, which only has to be legal. -/
def RunGuard (M : Lax564036.AlternatingMachines.ATMData A) (i : ℕ) (prev : Option (tmGuessBlock.Assignment A))
    (ρ : tmGuessBlock.Assignment A) : Prop :=
  match prev with
  | none => M.RunLegalBelow ρ 1
  | some ρp => M.RunRoundCond ρp ρ i

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (RunGuard)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

namespace ATMData

variable {A : Type}

/-- **The ladder with its quantifiers stripped.** `runMatrix M start m i prev
ρs` is the chain of the `m` rounds still to play, starting at round `i` with
`prev` the round before it – `none` at the very first round, which has nothing
to inherit. When no round is left the last guess must accept. -/
def runMatrix (M : Lax564036.AlternatingMachines.ATMData A) (start : Bool) : ∀ (m _i : ℕ),
    Option (tmGuessBlock.Assignment A) → (Fin m → tmGuessBlock.Assignment A) → Prop
  | 0, _, none, _ => False
  | 0, _, some ρp, _ => M.RunAccAt ρp
  | m + 1, i, prev, ρs =>
      polConn (Lax564036.AlternatingMachines.blockPol start i) (RunFun (ρs 0) ∧ M.RunGuard i prev (ρs 0))
        (runMatrix M start m (i + 1) (some (ρs 0)) fun j => ρs j.succ)

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (runMatrix)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

namespace ATMData

variable {A : Type}

variable {M : Lax564036.AlternatingMachines.ATMData A} {start : Bool}

/-- **The prefix puts the rounds back**, from a round that has a predecessor
on. -/
theorem altBlockQuant_runMatrix_some :
    ∀ (m i : ℕ) (ρp : tmGuessBlock.Assignment A),
      altBlockQuant A tmGuessBlock m (M.runMatrix start m i (some ρp)) (Lax564036.AlternatingMachines.blockPol start i) ↔
        M.runLadder start i m ρp := by
  intro m
  induction m with
  | zero => intro i ρp; exact Iff.rfl
  | succ m ih =>
    intro i ρp
    have hmat : M.runMatrix start (m + 1) i (some ρp) =
        fun ρs => polConn (Lax564036.AlternatingMachines.blockPol start i) (RunFun (ρs 0) ∧ M.RunGuard i (some ρp) (ρs 0))
          (M.runMatrix start m (i + 1) (some (ρs 0)) fun j => ρs j.succ) := rfl
    have hlad : M.runLadder start i (m + 1) ρp =
        bareQ (Lax564036.AlternatingMachines.blockPol start i) (fun ρ => RunFun ρ ∧ M.RunGuard i (some ρp) ρ)
          (fun ρ => M.runLadder start (i + 1) m ρ) := rfl
    rw [hmat, hlad]
    refine altBlockQuant_step (fun _ _ => True) m (Lax564036.AlternatingMachines.blockPol start i)
      (fun ρ => RunFun ρ ∧ M.RunGuard i (some ρp) ρ)
      (fun ρ ρs => M.runMatrix start m (i + 1) (some ρ) ρs)
      (fun ρ => M.runLadder start (i + 1) m ρ) fun ρ => ?_
    rw [← blockPol_succ start i]
    exact ih (i + 1) ρ

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (altBlockQuant_runMatrix_some)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

namespace ATMData

variable {A : Type}

variable {M : Lax564036.AlternatingMachines.ATMData A} {start : Bool}

/-- **The prefix puts the rounds back**, at the first round: the alternating
second-order prefix over one guess per round says exactly what the ladder
does. -/
theorem altBlockQuant_runMatrix (n : ℕ) :
    altBlockQuant A tmGuessBlock n (M.runMatrix start n 0 none) start ↔
      M.RunAltLadder start n := by
  cases n with
  | zero => exact Iff.rfl
  | succ m =>
    have hmat : M.runMatrix start (m + 1) 0 none =
        fun ρs => polConn (Lax564036.AlternatingMachines.blockPol start 0) (RunFun (ρs 0) ∧ M.RunGuard 0 none (ρs 0))
          (M.runMatrix start m 1 (some (ρs 0)) fun j => ρs j.succ) := rfl
    have hlad : M.RunAltLadder start (m + 1) =
        bareQ (Lax564036.AlternatingMachines.blockPol start 0) (fun ρ => RunFun ρ ∧ M.RunGuard 0 none ρ)
          (fun ρ => M.runLadder start 1 m ρ) := rfl
    rw [hmat, hlad]
    refine altBlockQuant_step (fun _ _ => True) m (Lax564036.AlternatingMachines.blockPol start 0)
      (fun ρ => RunFun ρ ∧ M.RunGuard 0 none ρ)
      (fun ρ ρs => M.runMatrix start m 1 (some ρ) ρs)
      (fun ρ => M.runLadder start 1 m ρ) fun ρ => ?_
    rw [← blockPol_succ start 0]
    exact altBlockQuant_runMatrix_some m 1 ρ

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (altBlockQuant_runMatrix)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

namespace ATMData

variable {A : Type}

variable {M : Lax564036.AlternatingMachines.ATMData A} {start : Bool}

end ATMData

end Lax564036Proofs.DescriptiveComplexity


