/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Hamilton.CountingGadget
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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

namespace Lax280166.CountingHamiltonCircuits
end Lax280166.CountingHamiltonCircuits

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax799700.OneInSat
end Lax799700.OneInSat

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingHamiltonCircuits (IsCircuit)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.OneInSat (OneInProper)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatOccurs)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue OccIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

/-!
# The circuit of an exactly-one model

The forward half of the correspondence between the exactly-one models of a CNF
formula and the Hamilton circuits of its row graph
(`DescriptiveComplexity.Problems.Hamilton.CountingGadget`): the relation
`DescriptiveComplexity.HamGadget.S ν` of an exactly-one assignment `ν` is a Hamilton
circuit (`DescriptiveComplexity.HamGadget.isCircuit_S`).

No enumeration of the circuit is written. The relation follows the arcs
(`DescriptiveComplexity.HamGadget.arc_of_S`), leaves every vertex exactly once
(`DescriptiveComplexity.HamGadget.S_total`, `DescriptiveComplexity.HamGadget.S_functional`) and
reaches every vertex (`DescriptiveComplexity.HamGadget.S_surj`): four case analyses on
the kind of a vertex. And a potential increases along it everywhere but at the
exit of the last row (`DescriptiveComplexity.HamGadget.key_lt`): the variable first,
then the position in the row, counted from the left for a true variable and
from the right for a false one. That is a circuit, by
`DescriptiveComplexity.isCircuit_of_potential`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace HamGadget

open Language Structure SatOcc

section Forward

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A] {ν : A → Prop}

/-- The circuit of an assignment follows the arcs. -/
theorem arc_of_S {u v : Vtx A} (hu : Valid u) (h : S ν u v) : Arc u v := by
  refine ⟨hu, ?_⟩
  cases u with
  | top x =>
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨hu, rfl⟩
  | lft x =>
    rcases h with ⟨-, rfl⟩ | ⟨-, y, hy, rfl⟩
    exacts [⟨hu, rfl⟩, ⟨hy.occ_right, hy⟩]
  | rgt x =>
    rcases h with ⟨-, y, hy, rfl⟩ | ⟨-, c, s, hm, rfl⟩
    exacts [⟨hy.occ_right, hy⟩, ⟨hm.1, rfl, hm⟩]
  | pad0 x =>
    rcases h with ⟨-, c, s, hm, rfl⟩ | ⟨-, rfl⟩
    exacts [⟨hm.1, rfl, hm⟩, ⟨hu, rfl⟩]
  | ain s x c =>
    rcases h with ⟨-, ⟨hs, rfl⟩ | ⟨hs, rfl⟩⟩ | ⟨-, ⟨c', s', hst, rfl⟩ | ⟨hm, rfl⟩⟩
    exacts [⟨OccIn.isCl hu, hs, rfl⟩, ⟨hu, hs, hs, rfl, rfl⟩, ⟨hst.1, rfl, hst⟩,
      ⟨occurs_of_occIn hu, rfl, hm⟩]
  | bout s x c =>
    rcases h with ⟨-, rfl⟩ | ⟨-, ⟨hs, rfl⟩ | ⟨hs, rfl⟩⟩
    exacts [⟨hu, rfl, rfl, rfl⟩, ⟨hu, hs, hs, rfl, rfl⟩, ⟨OccIn.isCl hu, hs, rfl⟩]
  | pad s x c =>
    rcases h with ⟨-, ⟨c', s', hst, rfl⟩ | ⟨hm, rfl⟩⟩ | ⟨-, rfl⟩
    exacts [⟨hst.2.1, rfl, hst⟩, ⟨occurs_of_occIn hu, rfl, hm⟩, ⟨hu, rfl, rfl, rfl⟩]
  | cls c =>
    rcases h with ⟨x, ho, -, rfl⟩ | ⟨x, ho, -, rfl⟩
    exacts [⟨ho, rfl, rfl⟩, ⟨ho, rfl, rfl⟩]
  | zero =>
    have hv : v = .zero := h
    subst hv
    exact ⟨hu, trivial⟩

/-- The circuit of an exactly-one assignment leaves a vertex at most once. -/
theorem S_functional (hν : Lax799700.OneInSat.OneInProper ν) {u v v' : Vtx A} (h : S ν u v) (h' : S ν u v') :
    v = v' := by
  cases u with
  | top x =>
    rcases h with ⟨hx, h⟩ | ⟨hx, h⟩ <;> rcases h' with ⟨hx', h'⟩ | ⟨hx', h'⟩ <;>
      first | exact absurd hx hx' | exact absurd hx' hx | exact h.trans h'.symm
  | lft x =>
    rcases h with ⟨hx, h⟩ | ⟨hx, h⟩ <;> rcases h' with ⟨hx', h'⟩ | ⟨hx', h'⟩ <;>
      first | exact absurd hx hx' | exact absurd hx' hx | skip
    · exact h.trans h'.symm
    · obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨y', hy', rfl⟩ := h'
      rw [nextVar_right_unique hy hy']
  | rgt x =>
    rcases h with ⟨hx, h⟩ | ⟨hx, h⟩ <;> rcases h' with ⟨hx', h'⟩ | ⟨hx', h'⟩ <;>
      first | exact absurd hx hx' | exact absurd hx' hx | skip
    · obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨y', hy', rfl⟩ := h'
      rw [nextVar_right_unique hy hy']
    · obtain ⟨c, s, hm, rfl⟩ := h
      obtain ⟨c', s', hm', rfl⟩ := h'
      obtain ⟨hc, hs⟩ := varMax_unique hm hm'
      rw [hc, hs]
  | pad0 x =>
    rcases h with ⟨hx, h⟩ | ⟨hx, h⟩ <;> rcases h' with ⟨hx', h'⟩ | ⟨hx', h'⟩ <;>
      first | exact absurd hx hx' | exact absurd hx' hx | skip
    · obtain ⟨c, s, hm, rfl⟩ := h
      obtain ⟨c', s', hm', rfl⟩ := h'
      obtain ⟨hc, hs⟩ := varMin_unique hm hm'
      rw [hc, hs]
    · exact h.trans h'.symm
  | ain s x c =>
    rcases h with ⟨hx, h⟩ | ⟨hx, h⟩ <;> rcases h' with ⟨hx', h'⟩ | ⟨hx', h'⟩ <;>
      first | exact absurd hx hx' | exact absurd hx' hx | skip
    · rcases h with ⟨hs, h⟩ | ⟨hs, h⟩ <;> rcases h' with ⟨hs', h'⟩ | ⟨hs', h'⟩ <;>
        first
          | exact h.trans h'.symm
          | exact absurd (hs.symm.trans hs') (by decide)
    · rcases h with ⟨c₁, s₁, hst, rfl⟩ | ⟨hm, rfl⟩ <;>
        rcases h' with ⟨c₂, s₂, hst', rfl⟩ | ⟨hm', rfl⟩
      · obtain ⟨hc, hs⟩ := varStep_left_unique hst hst'
        rw [hc, hs]
      · exact absurd hm' (not_varMin_of_step hst)
      · exact absurd hm (not_varMin_of_step hst')
      · rfl
  | bout s x c =>
    rcases h with ⟨hx, h⟩ | ⟨hx, h⟩ <;> rcases h' with ⟨hx', h'⟩ | ⟨hx', h'⟩ <;>
      first | exact absurd hx hx' | exact absurd hx' hx | skip
    · exact h.trans h'.symm
    · rcases h with ⟨hs, h⟩ | ⟨hs, h⟩ <;> rcases h' with ⟨hs', h'⟩ | ⟨hs', h'⟩ <;>
        first
          | exact h.trans h'.symm
          | exact absurd (hs.symm.trans hs') (by decide)
  | pad s x c =>
    rcases h with ⟨hx, h⟩ | ⟨hx, h⟩ <;> rcases h' with ⟨hx', h'⟩ | ⟨hx', h'⟩ <;>
      first | exact absurd hx hx' | exact absurd hx' hx | skip
    · rcases h with ⟨c₁, s₁, hst, rfl⟩ | ⟨hm, rfl⟩ <;>
        rcases h' with ⟨c₂, s₂, hst', rfl⟩ | ⟨hm', rfl⟩
      · obtain ⟨hc, hs⟩ := varStep_right_unique hst hst'
        rw [hc, hs]
      · exact absurd hm' (not_varMax_of_step hst)
      · exact absurd hm (not_varMax_of_step hst')
      · rfl
    · exact h.trans h'.symm
  | cls c =>
    have key : ∀ {x x' : A} {s s' : Bool}, Lax799700.Common.SatOcc.OccIn c x s → Lax799700.Common.SatOcc.LitTrue ν x s → Lax799700.Common.SatOcc.OccIn c x' s' →
        Lax799700.Common.SatOcc.LitTrue ν x' s' → x = x' ∧ s = s' := by
      intro x x' s s' ho hT ho' hT'
      obtain ⟨x₀, s₀, -, -, huniq⟩ := hν c (OccIn.isCl ho)
      obtain ⟨h₁, h₂⟩ := huniq x s ho hT
      obtain ⟨h₁', h₂'⟩ := huniq x' s' ho' hT'
      exact ⟨h₁.trans h₁'.symm, h₂.trans h₂'.symm⟩
    rcases h with ⟨x, ho, hT, rfl⟩ | ⟨x, ho, hT, rfl⟩ <;>
      rcases h' with ⟨x', ho', hT', rfl⟩ | ⟨x', ho', hT', rfl⟩
    · rw [(key ho hT ho' hT').1]
    · exact absurd (key ho hT ho' hT').2 (by decide)
    · exact absurd (key ho hT ho' hT').2 (by decide)
    · rw [(key ho hT ho' hT').1]
  | zero => exact Eq.trans h (Eq.symm h')

variable [Finite A]

/-- The circuit of an exactly-one assignment leaves every vertex. -/
theorem S_total (hν : Lax799700.OneInSat.OneInProper ν) {u : Vtx A} (hu : Valid u) : ∃ v, S ν u v := by
  cases u with
  | top x =>
    by_cases h : ν x
    exacts [⟨_, Or.inl ⟨h, rfl⟩⟩, ⟨_, Or.inr ⟨h, rfl⟩⟩]
  | lft x =>
    by_cases h : ν x
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨y, hy⟩ := exists_nextVar hu
      exact ⟨_, Or.inr ⟨h, y, hy, rfl⟩⟩
  | rgt x =>
    by_cases h : ν x
    · obtain ⟨y, hy⟩ := exists_nextVar hu
      exact ⟨_, Or.inl ⟨h, y, hy, rfl⟩⟩
    · obtain ⟨c, s, hm⟩ := exists_varMax (exists_occIn_of_occurs hu)
      exact ⟨_, Or.inr ⟨h, c, s, hm, rfl⟩⟩
  | pad0 x =>
    by_cases h : ν x
    · obtain ⟨c, s, hm⟩ := exists_varMin (exists_occIn_of_occurs hu)
      exact ⟨_, Or.inl ⟨h, c, s, hm, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨h, rfl⟩⟩
  | ain s x c =>
    by_cases h : ν x
    · cases s
      exacts [⟨_, Or.inl ⟨h, Or.inr ⟨rfl, rfl⟩⟩⟩, ⟨_, Or.inl ⟨h, Or.inl ⟨rfl, rfl⟩⟩⟩]
    · rcases varMin_or_step hu with hm | ⟨c', s', hst⟩
      exacts [⟨_, Or.inr ⟨h, Or.inr ⟨hm, rfl⟩⟩⟩, ⟨_, Or.inr ⟨h, Or.inl ⟨c', s', hst, rfl⟩⟩⟩]
  | bout s x c =>
    by_cases h : ν x
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · cases s
      exacts [⟨_, Or.inr ⟨h, Or.inr ⟨rfl, rfl⟩⟩⟩, ⟨_, Or.inr ⟨h, Or.inl ⟨rfl, rfl⟩⟩⟩]
  | pad s x c =>
    by_cases h : ν x
    · rcases varMax_or_step hu with hm | ⟨c', s', hst⟩
      exacts [⟨_, Or.inl ⟨h, Or.inr ⟨hm, rfl⟩⟩⟩, ⟨_, Or.inl ⟨h, Or.inl ⟨c', s', hst, rfl⟩⟩⟩]
    · exact ⟨_, Or.inr ⟨h, rfl⟩⟩
  | cls c =>
    obtain ⟨x, s, ho, hT, -⟩ := hν c hu
    cases s
    exacts [⟨_, Or.inr ⟨x, ho, hT, rfl⟩⟩, ⟨_, Or.inl ⟨x, ho, hT, rfl⟩⟩]
  | zero => exact ⟨_, rfl⟩

/-- The circuit of an exactly-one assignment reaches every vertex. -/
theorem S_surj (hν : Lax799700.OneInSat.OneInProper ν) {v : Vtx A} (hv : Valid v) :
    ∃ u, Valid u ∧ S ν u v := by
  cases v with
  | top y =>
    obtain ⟨x, hx⟩ := exists_prevVar hv
    by_cases h : ν x
    exacts [⟨.rgt x, hx.occ_left, Or.inl ⟨h, y, hx, rfl⟩⟩,
      ⟨.lft x, hx.occ_left, Or.inr ⟨h, y, hx, rfl⟩⟩]
  | lft x =>
    by_cases h : ν x
    exacts [⟨.top x, hv, Or.inl ⟨h, rfl⟩⟩, ⟨.pad0 x, hv, Or.inr ⟨h, rfl⟩⟩]
  | rgt x =>
    by_cases h : ν x
    · obtain ⟨c, s, hm⟩ := exists_varMax (exists_occIn_of_occurs hv)
      exact ⟨.pad s x c, hm.1, Or.inl ⟨h, Or.inr ⟨hm, rfl⟩⟩⟩
    · exact ⟨.top x, hv, Or.inr ⟨h, rfl⟩⟩
  | pad0 x =>
    by_cases h : ν x
    · exact ⟨.lft x, hv, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨c, s, hm⟩ := exists_varMin (exists_occIn_of_occurs hv)
      exact ⟨.ain s x c, hm.1, Or.inr ⟨h, Or.inr ⟨hm, rfl⟩⟩⟩
  | ain s x c =>
    by_cases h : ν x
    · rcases varMin_or_step hv with hm | ⟨c', s', hst⟩
      exacts [⟨.pad0 x, occurs_of_occIn hv, Or.inl ⟨h, c, s, hm, rfl⟩⟩,
        ⟨.pad s' x c', hst.1, Or.inl ⟨h, Or.inl ⟨c, s, hst, rfl⟩⟩⟩]
    · cases s
      exacts [⟨.cls c, OccIn.isCl hv, Or.inr ⟨x, hv, h, rfl⟩⟩,
        ⟨.bout true x c, hv, Or.inr ⟨h, Or.inl ⟨rfl, rfl⟩⟩⟩]
  | bout s x c =>
    by_cases h : ν x
    · cases s
      exacts [⟨.ain false x c, hv, Or.inl ⟨h, Or.inr ⟨rfl, rfl⟩⟩⟩,
        ⟨.cls c, OccIn.isCl hv, Or.inl ⟨x, hv, h, rfl⟩⟩]
    · exact ⟨.pad s x c, hv, Or.inr ⟨h, rfl⟩⟩
  | pad s x c =>
    by_cases h : ν x
    · exact ⟨.bout s x c, hv, Or.inl ⟨h, rfl⟩⟩
    · rcases varMax_or_step hv with hm | ⟨c', s', hst⟩
      exacts [⟨.rgt x, occurs_of_occIn hv, Or.inr ⟨h, c, s, hm, rfl⟩⟩,
        ⟨.ain s' x c', hst.2.1, Or.inr ⟨h, Or.inl ⟨c, s, hst, rfl⟩⟩⟩]
  | cls c =>
    obtain ⟨x, s, ho, hT, -⟩ := hν c hv
    cases s
    exacts [⟨.bout false x c, ho, Or.inr ⟨hT, Or.inr ⟨rfl, rfl⟩⟩⟩,
      ⟨.ain true x c, ho, Or.inl ⟨hT, Or.inl ⟨rfl, rfl⟩⟩⟩]
  | zero => exact ⟨.zero, hv, rfl⟩

/-! ### The potential -/

/-- The vertices of the row graph are finitely many. -/
instance : Finite (Vtx A) := by
  let enc : Vtx A → Fin 9 × Bool × Option A × Option A := fun v =>
    match v with
    | .top x => (0, false, some x, none)
    | .lft x => (1, false, some x, none)
    | .rgt x => (2, false, some x, none)
    | .pad0 x => (3, false, some x, none)
    | .ain s x c => (4, s, some x, some c)
    | .bout s x c => (5, s, some x, some c)
    | .pad s x c => (6, s, some x, some c)
    | .cls c => (7, false, some c, none)
    | .zero => (8, false, none, none)
  refine Finite.of_injective enc fun u v h => ?_
  cases u <;> cases v <;> simp_all [enc]

open Classical in
/-- The true literal of a clause under an assignment, when there is one. -/
noncomputable def clsLit (ν : A → Prop) (c : A) : A × Bool :=
  if h : ∃ p : A × Bool, Lax799700.Common.SatOcc.OccIn c p.1 p.2 ∧ Lax799700.Common.SatOcc.LitTrue ν p.1 p.2 then h.choose else (c, false)

omit [LinearOrder A] [Finite A] in
theorem clsLit_eq (hν : Lax799700.OneInSat.OneInProper ν) {c x : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s)
    (hT : Lax799700.Common.SatOcc.LitTrue ν x s) : clsLit ν c = (x, s) := by
  have hex : ∃ p : A × Bool, Lax799700.Common.SatOcc.OccIn c p.1 p.2 ∧ Lax799700.Common.SatOcc.LitTrue ν p.1 p.2 := ⟨(x, s), ho, hT⟩
  simp only [clsLit, hex, ↓reduceDIte]
  obtain ⟨x₀, s₀, -, -, huniq⟩ := hν c (OccIn.isCl ho)
  obtain ⟨h₁, h₂⟩ := huniq x s ho hT
  obtain ⟨h₁', h₂'⟩ := huniq _ _ hex.choose_spec.1 hex.choose_spec.2
  exact Prod.ext (h₁'.trans h₁.symm) (h₂'.trans h₂.symm)

open Classical in
/-- The key of a row vertex: its variable, then its position, counted from the
left when the variable is true and from the right when it is false. -/
noncomputable def rowKey (ν : A → Prop) (x : A) (p : ℤ) : A ×ₗ ℤ :=
  toLex (x, if ν x then p else -p)

omit [Lax904597.Sat.sat.Structure A] [Finite A] in
theorem rowKey_lt_pos {x : A} {p q : ℤ} (hx : ν x) (h : p < q) :
    rowKey ν x p < rowKey ν x q := by
  rw [rowKey, rowKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, by simpa [hx] using h⟩

omit [Lax904597.Sat.sat.Structure A] [Finite A] in
theorem rowKey_lt_neg {x : A} {p q : ℤ} (hx : ¬ν x) (h : q < p) :
    rowKey ν x p < rowKey ν x q := by
  rw [rowKey, rowKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, by simpa [hx] using h⟩

variable [Nonempty A]

/-- **The potential**: the variable of a vertex, then its position in the row;
a clause vertex sits in the row of its true literal, between the two vertices
of the occurrence. -/
noncomputable def key (ν : A → Prop) : Vtx A → A ×ₗ ℤ
  | .top x => toLex (x, -(4 * (occTotal x : ℤ) + 8))
  | .lft x => rowKey ν x 1
  | .pad0 x => rowKey ν x 2
  | .ain s x c => rowKey ν x (4 * (occRank x c s : ℤ) + 3)
  | .bout s x c => rowKey ν x (4 * (occRank x c s : ℤ) + 5)
  | .pad s x c => rowKey ν x (4 * (occRank x c s : ℤ) + 6)
  | .rgt x => rowKey ν x (4 * (occTotal x : ℤ) + 7)
  | .cls c => rowKey ν (clsLit ν c).1 (4 * (occRank (clsLit ν c).1 c (clsLit ν c).2 : ℤ) + 4)
  | .zero => toLex (Classical.arbitrary A, 0)

omit [Finite A] [Nonempty A] in
theorem topKey_lt {x : A} {p : ℤ} (hp : 0 < p) (hp' : p ≤ 4 * (occTotal x : ℤ) + 7) :
    (toLex (x, -(4 * (occTotal x : ℤ) + 8)) : A ×ₗ ℤ) < rowKey ν x p := by
  classical
  rw [rowKey, Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨rfl, ?_⟩
  by_cases hx : ν x
  · simp only [hx, ↓reduceIte]
    omega
  · simp only [hx, ↓reduceIte]
    omega

omit [Finite A] in
theorem key_cls (hν : Lax799700.OneInSat.OneInProper ν) {c x : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s)
    (hT : Lax799700.Common.SatOcc.LitTrue ν x s) :
    key ν (.cls c) = rowKey ν x (4 * (occRank x c s : ℤ) + 4) := by
  change rowKey ν (clsLit ν c).1 _ = _
  rw [clsLit_eq hν ho hT]

/-- **The potential increases along the circuit of an exactly-one assignment**,
except at the exit of the last row – and at the loop of `zero`. -/
theorem key_lt (hν : Lax799700.OneInSat.OneInProper ν) {u v : Vtx A} (hu : Valid u) (h : S ν u v) :
    key ν u < key ν v ∨ (∃ x, VLast x ∧ ((ν x ∧ u = .rgt x) ∨ (¬ν x ∧ u = .lft x))) ∨
      u = .zero := by
  have hnext : ∀ {x y : A} (z : ℤ), NextVar x y →
      (rowKey ν x z < key ν (.top y)) ∨ VLast x := by
    intro x y z hxy
    rcases hxy.lt_or_last with hlt | hl
    · left
      rw [key, rowKey, Prod.Lex.toLex_lt_toLex]
      exact Or.inl hlt
    · exact Or.inr hl
  cases u with
  | top x =>
    left
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact topKey_lt (by norm_num) (by omega)
    · exact topKey_lt (by omega) le_rfl
  | lft x =>
    rcases h with ⟨hx, rfl⟩ | ⟨hx, y, hy, rfl⟩
    · exact Or.inl (rowKey_lt_pos hx (by norm_num))
    · rcases hnext 1 hy with h | h
      exacts [Or.inl h, Or.inr (Or.inl ⟨x, h, Or.inr ⟨hx, rfl⟩⟩)]
  | rgt x =>
    rcases h with ⟨hx, y, hy, rfl⟩ | ⟨hx, c, s, hm, rfl⟩
    · rcases hnext (4 * (occTotal x : ℤ) + 7) hy with h | h
      exacts [Or.inl h, Or.inr (Or.inl ⟨x, h, Or.inl ⟨hx, rfl⟩⟩)]
    · have := occRank_lt_total hm.1
      exact Or.inl (rowKey_lt_neg hx (by omega))
  | pad0 x =>
    left
    rcases h with ⟨hx, c, s, -, rfl⟩ | ⟨hx, rfl⟩
    · exact rowKey_lt_pos hx (by omega)
    · exact rowKey_lt_neg hx (by norm_num)
  | ain s x c =>
    left
    rcases h with ⟨hx, ⟨hs, rfl⟩ | ⟨hs, rfl⟩⟩ | ⟨hx, ⟨c', s', hst, rfl⟩ | ⟨hm, rfl⟩⟩
    · subst hs
      rw [key_cls hν hu hx]
      exact rowKey_lt_pos hx (by omega)
    · exact rowKey_lt_pos hx (by omega)
    · have := occRank_lt_of_varStep hst
      exact rowKey_lt_neg hx (by omega)
    · exact rowKey_lt_neg hx (by omega)
  | bout s x c =>
    left
    rcases h with ⟨hx, rfl⟩ | ⟨hx, ⟨hs, rfl⟩ | ⟨hs, rfl⟩⟩
    · exact rowKey_lt_pos hx (by omega)
    · exact rowKey_lt_neg hx (by omega)
    · subst hs
      rw [key_cls hν hu hx]
      exact rowKey_lt_neg hx (by omega)
  | pad s x c =>
    left
    rcases h with ⟨hx, ⟨c', s', hst, rfl⟩ | ⟨hm, rfl⟩⟩ | ⟨hx, rfl⟩
    · have := occRank_lt_of_varStep hst
      exact rowKey_lt_pos hx (by omega)
    · have := occRank_lt_total hu
      exact rowKey_lt_pos hx (by omega)
    · exact rowKey_lt_neg hx (by omega)
  | cls c =>
    left
    rcases h with ⟨x, ho, hx, rfl⟩ | ⟨x, ho, hx, rfl⟩
    · rw [key_cls hν ho hx]
      exact rowKey_lt_pos hx (by omega)
    · rw [key_cls hν ho hx]
      exact rowKey_lt_neg hx (by omega)
  | zero => exact Or.inr (Or.inr rfl)

/-- **The relation of an exactly-one assignment is a Hamilton circuit** of the
row graph. -/
theorem isCircuit_S (hν : Lax799700.OneInSat.OneInProper ν) :
    Lax280166.CountingHamiltonCircuits.IsCircuit (fun u v : {v : Vtx A // Valid v} => Arc u.1 v.1) fun u v => S ν u.1 v.1 := by
  classical
  have hW : Nonempty {v : Vtx A // Valid v} := by
    by_cases hcl : ∃ c : A, Lax799700.Common.SatOcc.IsCl c
    · obtain ⟨c, hc⟩ := hcl
      exact ⟨⟨.cls c, hc⟩⟩
    · exact ⟨⟨.zero, hcl⟩⟩
  obtain ⟨w₀⟩ := hW
  -- the exceptional vertex: the exit of the last row, or anything if there is no row
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : {v : Vtx A // Valid v}, ∀ x : A, VLast x →
      ((ν x → v₀.1 = .rgt x) ∧ (¬ν x → v₀.1 = .lft x)) := by
    by_cases hL : ∃ x : A, VLast x
    · obtain ⟨xL, hxL⟩ := hL
      have huniq : ∀ x : A, VLast x → x = xL := fun x hx =>
        le_antisymm (hxL.2 x hx.1) (hx.2 xL hxL.1)
      by_cases hx : ν xL
      · refine ⟨⟨.rgt xL, hxL.1⟩, fun x hxl => ?_⟩
        rw [huniq x hxl]
        exact ⟨fun _ => rfl, fun h => absurd hx h⟩
      · refine ⟨⟨.lft xL, hxL.1⟩, fun x hxl => ?_⟩
        rw [huniq x hxl]
        exact ⟨fun h => absurd h hx, fun _ => rfl⟩
    · exact ⟨w₀, fun x hx => absurd ⟨x, hx⟩ hL⟩
  refine isCircuit_of_potential (fun u => ?_) (fun u v v' h h' => ?_) (fun v => ?_)
    (fun u v h => arc_of_S u.2 h) (fun u => key ν u.1) v₀ (fun u v h hne => ?_)
  · obtain ⟨v, hv⟩ := S_total hν u.2
    exact ⟨⟨v, (arc_of_S u.2 hv).2.1⟩, hv⟩
  · exact Subtype.ext (S_functional hν h h')
  · obtain ⟨u, hu, huv⟩ := S_surj hν v.2
    exact ⟨⟨u, hu⟩, huv⟩
  · rcases key_lt hν u.2 h with hlt | ⟨x, hxl, hcase⟩ | hz
    · exact hlt
    · refine absurd (Subtype.ext ?_) hne
      rcases hcase with ⟨hx, hux⟩ | ⟨hx, hux⟩
      · rw [hux, ((hv₀ x hxl).1 hx)]
      · rw [hux, ((hv₀ x hxl).2 hx)]
    · -- `zero` is valid only when it is the whole graph
      have hnocl : ¬∃ c : A, Lax799700.Common.SatOcc.IsCl c := by
        have hu := u.2
        rw [hz] at hu
        exact hu
      refine absurd (Subtype.ext ?_) hne
      rw [hz]
      obtain ⟨v, hv⟩ := v₀
      cases v with
      | zero => rfl
      | top x => exact absurd (hv : Lax366625.CountingSat.SatOccurs A x) fun ⟨c, hc, _⟩ => hnocl ⟨c, hc⟩
      | lft x => exact absurd (hv : Lax366625.CountingSat.SatOccurs A x) fun ⟨c, hc, _⟩ => hnocl ⟨c, hc⟩
      | rgt x => exact absurd (hv : Lax366625.CountingSat.SatOccurs A x) fun ⟨c, hc, _⟩ => hnocl ⟨c, hc⟩
      | pad0 x => exact absurd (hv : Lax366625.CountingSat.SatOccurs A x) fun ⟨c, hc, _⟩ => hnocl ⟨c, hc⟩
      | ain s x c => exact absurd ⟨c, OccIn.isCl (hv : Lax799700.Common.SatOcc.OccIn c x s)⟩ hnocl
      | bout s x c => exact absurd ⟨c, OccIn.isCl (hv : Lax799700.Common.SatOcc.OccIn c x s)⟩ hnocl
      | pad s x c => exact absurd ⟨c, OccIn.isCl (hv : Lax799700.Common.SatOcc.OccIn c x s)⟩ hnocl
      | cls c => exact absurd ⟨c, (hv : Lax799700.Common.SatOcc.IsCl c)⟩ hnocl

end Forward

end HamGadget

end Lax280166Proofs.DescriptiveComplexity


