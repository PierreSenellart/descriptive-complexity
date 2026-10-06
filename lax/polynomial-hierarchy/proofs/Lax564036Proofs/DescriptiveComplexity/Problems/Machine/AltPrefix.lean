/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.AltVerdict
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

namespace Lax564036.QuantifiedBooleanFormulas
end Lax564036.QuantifiedBooleanFormulas

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.QuantifiedBooleanFormulas (altQuant)
end Lax564036Proofs.DescriptiveComplexity

/-!
# The quantifier prefix, read from the middle

`DescriptiveComplexity.altQuant` quantifies the `k` block assignments from the
outside in, building the tuple with `Fin.cons`: the assignment of index `0` is
the outermost, and the type shrinks as the recursion goes. That is the right
shape for a *definition* and the wrong one for a run, which fixes the blocks in
place and rewrites them one at a time with `Function.update`.

`DescriptiveComplexity.AltQbf.AltTail` is the second shape: `AltTail P r m νs pol`
quantifies the `r` blocks from `m` up, leaving the blocks below `m` at whatever
`νs` says. The two agree (`DescriptiveComplexity.AltQbf.altTail_iff_altQuant`), by an
induction that pushes one block from the tail into the prefix at a time. The
gluing map `DescriptiveComplexity.AltQbf.glueTail` is what translates between them,
and the whole content of the bridge is that pushing a block past it is
`Function.update`.
-/

namespace Lax564036Proofs.DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

section Prefix

variable {k : ℕ} {A : Type}

/-! ### Quantification from the middle of the prefix -/

/-- One quantifier at the polarity `pol`. -/
def polQuant (pol : Bool) (Q : (A → Prop) → Prop) : Prop :=
  match pol with
  | true => ∃ ν : A → Prop, Q ν
  | false => ∀ ν : A → Prop, Q ν

/-- **Quantifying the last `r` blocks**, the ones below `m` already fixed by
`νs`. Each block is written in place, which is the shape a run of the machine
produces: round `m` replaces the `m`-th assignment and leaves the others
alone. -/
def AltTail (P : (Fin k → A → Prop) → Prop) : ℕ → ℕ → (Fin k → A → Prop) → Bool → Prop
  | 0, _, νs, _ => P νs
  | r + 1, m, νs, pol =>
      if h : m < k then
        polQuant pol fun ν => AltTail P r (m + 1) (Function.update νs ⟨m, h⟩ ν) (!pol)
      else P νs

theorem altTail_succ (P : (Fin k → A → Prop) → Prop) {r m : ℕ} (h : m < k)
    (νs : Fin k → A → Prop) (pol : Bool) :
    AltTail P (r + 1) m νs pol =
      polQuant pol fun ν => AltTail P r (m + 1) (Function.update νs ⟨m, h⟩ ν) (!pol) := by
  rw [AltTail, dif_pos h]

/-! ### Gluing a tail onto a prefix -/

/-- The tuple that follows `νs` below `m` and reads the `r` blocks from `m` up
off `σ`. -/
def glueTail (m r : ℕ) (νs : Fin k → A → Prop) (σ : Fin r → A → Prop) (i : Fin k) : A → Prop :=
  if (i : ℕ) < m then νs i
  else if h : (i : ℕ) - m < r then σ ⟨(i : ℕ) - m, h⟩ else νs i

/-- Gluing nothing leaves the prefix alone. -/
theorem glueTail_zero (m : ℕ) (νs : Fin k → A → Prop) (σ : Fin 0 → A → Prop) :
    glueTail m 0 νs σ = νs := by
  funext i
  simp only [glueTail, Nat.not_lt_zero]
  split <;> rfl

/-- **Pushing one block from the tail into the prefix is an update.** This is
the whole content of the bridge between the two shapes of the prefix. -/
theorem glueTail_cons {m r : ℕ} (h : m < k) (νs : Fin k → A → Prop) (ν : A → Prop)
    (σ : Fin r → A → Prop) :
    glueTail m (r + 1) νs (Fin.cons ν σ) =
      glueTail (m + 1) r (Function.update νs ⟨m, h⟩ ν) σ := by
  funext i
  rcases Nat.lt_trichotomy (i : ℕ) m with hlt | heq | hgt
  · have hne : i ≠ (⟨m, h⟩ : Fin k) := by
      intro hcon
      have : (i : ℕ) = m := by rw [hcon]
      omega
    simp only [glueTail, if_pos hlt, if_pos (show (i : ℕ) < m + 1 by omega),
      Function.update_of_ne hne]
  · have hi : i = (⟨m, h⟩ : Fin k) := Fin.ext heq
    subst hi
    simp only [glueTail, if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _), Function.update_self,
      Nat.sub_self, dif_pos (Nat.succ_pos r)]
    rfl
  · have hne : i ≠ (⟨m, h⟩ : Fin k) := by
      intro hcon
      have : (i : ℕ) = m := by rw [hcon]
      omega
    simp only [glueTail, if_neg (show ¬((i : ℕ) < m) by omega),
      if_neg (show ¬((i : ℕ) < m + 1) by omega), Function.update_of_ne hne]
    by_cases hr : (i : ℕ) - (m + 1) < r
    · rw [dif_pos (show (i : ℕ) - m < r + 1 by omega), dif_pos hr]
      have hsucc : (⟨(i : ℕ) - m, show (i : ℕ) - m < r + 1 by omega⟩ : Fin (r + 1)) =
          Fin.succ ⟨(i : ℕ) - (m + 1), hr⟩ := Fin.ext (by simp; omega)
      rw [hsucc, Fin.cons_succ]
    · rw [dif_neg (show ¬((i : ℕ) - m < r + 1) by omega), dif_neg hr]

/-! ### The two shapes agree -/

/-- **Quantifying from the middle is quantifying from the outside**, once the
blocks already fixed are glued back on. -/
theorem altTail_iff_altQuant (P : (Fin k → A → Prop) → Prop) :
    ∀ (r m : ℕ), m + r ≤ k → ∀ (νs : Fin k → A → Prop) (pol : Bool),
      AltTail P r m νs pol ↔ Lax564036.QuantifiedBooleanFormulas.altQuant A r (fun σ => P (glueTail m r νs σ)) pol := by
  intro r
  induction r with
  | zero =>
    intro m _ νs pol
    change P νs ↔ P (glueTail m 0 νs Fin.elim0)
    rw [glueTail_zero]
  | succ r ih =>
    intro m hmr νs pol
    have h : m < k := by omega
    rw [altTail_succ P h νs pol]
    cases pol with
    | true =>
      refine exists_congr fun ν => ?_
      refine (ih (m + 1) (by omega) (Function.update νs ⟨m, h⟩ ν) false).trans ?_
      exact altQuant_congr r _ _
        (fun σ => iff_of_eq (congrArg P (glueTail_cons h νs ν σ)).symm) false
    | false =>
      refine forall_congr' fun ν => ?_
      refine (ih (m + 1) (by omega) (Function.update νs ⟨m, h⟩ ν) true).trans ?_
      exact altQuant_congr r _ _
        (fun σ => iff_of_eq (congrArg P (glueTail_cons h νs ν σ)).symm) true

/-- **The whole prefix**: quantifying every block in place is the alternating
quantification of `DescriptiveComplexity.QbfProblem`. -/
theorem altTail_zero_iff_altQuant (P : (Fin k → A → Prop) → Prop) (νs : Fin k → A → Prop)
    (pol : Bool) : AltTail P k 0 νs pol ↔ Lax564036.QuantifiedBooleanFormulas.altQuant A k P pol := by
  refine (altTail_iff_altQuant P k 0 (by omega) νs pol).trans (altQuant_congr k _ _ ?_ pol)
  intro σ
  refine iff_of_eq (congrArg P (funext fun i => ?_))
  simp [glueTail]

end Prefix

end AltQbf

end Lax564036Proofs.DescriptiveComplexity


