/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Hamilton.CountingForward
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

namespace Lax280166.CountingSatVariants
end Lax280166.CountingSatVariants

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSatVariants (OneInModel)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingHamiltonCircuits (IsCircuit)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatOccurs)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (OccIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

/-!
# Every circuit of the row graph is the circuit of a model

The reverse half of the correspondence of
`DescriptiveComplexity.Problems.Hamilton.CountingGadget`: a Hamilton circuit of the
row graph of a CNF formula is the relation `DescriptiveComplexity.HamGadget.S ν` of an
exactly-one model `ν` (`DescriptiveComplexity.HamGadget.Circ.eq_S`,
`DescriptiveComplexity.HamGadget.Circ.oneInModel`), the model being read off the
direction in which each row is entered.

Only the local reading of a circuit is used (`DescriptiveComplexity.HamGadget.Circ`,
from `DescriptiveComplexity.IsCircuit.local`): every vertex is left once and reached
once, along an arc, and no two vertices follow each other both ways.

* A padding vertex has two neighbours, so the circuit passes *through* it
  (`DescriptiveComplexity.HamGadget.Circ.through`).
* Hence an occurrence entered from the left is left to the right, visiting its
  clause vertex on the way iff it is positive
  (`DescriptiveComplexity.HamGadget.Circ.pairT`), and one entered from the right is
  left to the left, visiting it iff it is negative
  (`DescriptiveComplexity.HamGadget.Circ.pairF`).
* Hence a row is swept in one direction, by induction along its occurrences
  (`DescriptiveComplexity.HamGadget.Circ.rowT`, `DescriptiveComplexity.HamGadget.Circ.rowF`).

A clause vertex is then entered from each of its true literals, and it is
entered once.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace HamGadget

open Language Structure SatOcc

section Reverse

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

/-- A Hamilton circuit of the row graph, read locally. -/
structure Circ (N : Vtx A → Vtx A → Prop) : Prop where
  /-- Every vertex is left. -/
  succ : ∀ u, Valid u → ∃ v, N u v
  /-- Every vertex is reached. -/
  pred : ∀ v, Valid v → ∃ u, N u v
  /-- A vertex is left once. -/
  func : ∀ {u v v'}, N u v → N u v' → v = v'
  /-- A vertex is reached once. -/
  inj : ∀ {u u' v}, N u v → N u' v → u = u'
  /-- The circuit follows the arcs. -/
  arc : ∀ {u v}, N u v → Arc u v
  /-- Two vertices following each other both ways are the whole graph. -/
  two : ∀ {u v}, N u v → N v u → ∀ z, Valid z → z = u ∨ z = v

/-- The row predecessor of an occurrence: the first padding, or the padding of
the previous occurrence. -/
def IsPrev (pv : Vtx A) (s : Bool) (x c : A) : Prop :=
  (VarMin x c s ∧ pv = .pad0 x) ∨ ∃ c' s', VarStep x c' s' c s ∧ pv = .pad s' x c'

/-- The row successor of the padding of an occurrence: the next occurrence, or
the right end. -/
def IsNext (nv : Vtx A) (s : Bool) (x c : A) : Prop :=
  (VarMax x c s ∧ nv = .rgt x) ∨ ∃ c' s', VarStep x c s c' s' ∧ nv = .ain s' x c'

/-! ### The neighbours of a vertex -/

theorem step_pad0_out {x c : A} {s : Bool} (hm : VarMin x c s) {v : Vtx A}
    (h : Step (.pad0 x) v) : v = .lft x ∨ v = .ain s x c := by
  cases v with
  | lft y =>
    have hxy : x = y := h
    exact Or.inl (by rw [hxy])
  | ain s₁ y c₁ =>
    obtain ⟨hxy, hm₁⟩ : x = y ∧ VarMin x c₁ s₁ := h
    obtain ⟨hc, hs⟩ := varMin_unique hm hm₁
    exact Or.inr (by rw [← hxy, hc, hs])
  | _ => exact (h : False).elim

theorem step_pad0_in {x c : A} {s : Bool} (hm : VarMin x c s) {v : Vtx A}
    (h : Step v (.pad0 x)) : v = .lft x ∨ v = .ain s x c := by
  cases v with
  | lft y =>
    have hxy : y = x := h
    exact Or.inl (by rw [hxy])
  | ain s₁ y c₁ =>
    obtain ⟨hxy, hm₁⟩ : x = y ∧ VarMin x c₁ s₁ := h
    obtain ⟨hc, hs⟩ := varMin_unique hm hm₁
    exact Or.inr (by rw [← hxy, hc, hs])
  | _ => exact (h : False).elim

theorem step_pad_out {nv : Vtx A} {x c : A} {s : Bool} (hn : IsNext nv s x c) {v : Vtx A}
    (h : Step (.pad s x c) v) : v = .bout s x c ∨ v = nv := by
  cases v with
  | rgt y =>
    obtain ⟨hxy, hm⟩ : x = y ∧ VarMax x c s := h
    rcases hn with ⟨-, rfl⟩ | ⟨c', s', hst, -⟩
    · exact Or.inr (by rw [hxy])
    · exact absurd hm (not_varMax_of_step hst)
  | ain s₁ y c₁ =>
    obtain ⟨hxy, hst₁⟩ : x = y ∧ VarStep x c s c₁ s₁ := h
    rcases hn with ⟨hm, -⟩ | ⟨c', s', hst, rfl⟩
    · exact absurd hm (not_varMax_of_step hst₁)
    · obtain ⟨hc, hs⟩ := varStep_right_unique hst hst₁
      exact Or.inr (by rw [← hxy, hc, hs])
  | bout s₁ y c₁ =>
    obtain ⟨hs, hxy, hc⟩ : s = s₁ ∧ x = y ∧ c = c₁ := h
    exact Or.inl (by rw [hs, hxy, hc])
  | _ => exact (h : False).elim

theorem step_pad_in {nv : Vtx A} {x c : A} {s : Bool} (hn : IsNext nv s x c) {v : Vtx A}
    (h : Step v (.pad s x c)) : v = .bout s x c ∨ v = nv := by
  cases v with
  | rgt y =>
    obtain ⟨hxy, hm⟩ : x = y ∧ VarMax x c s := h
    rcases hn with ⟨-, rfl⟩ | ⟨c', s', hst, -⟩
    · exact Or.inr (by rw [hxy])
    · exact absurd hm (not_varMax_of_step hst)
  | ain s₁ y c₁ =>
    obtain ⟨hxy, hst₁⟩ : x = y ∧ VarStep x c s c₁ s₁ := h
    rcases hn with ⟨hm, -⟩ | ⟨c', s', hst, rfl⟩
    · exact absurd hm (not_varMax_of_step hst₁)
    · obtain ⟨hc, hs⟩ := varStep_right_unique hst hst₁
      exact Or.inr (by rw [← hxy, hc, hs])
  | bout s₁ y c₁ =>
    obtain ⟨hs, hxy, hc⟩ : s₁ = s ∧ y = x ∧ c₁ = c := h
    exact Or.inl (by rw [hs, hxy, hc])
  | _ => exact (h : False).elim

theorem step_ain_out {pv : Vtx A} {x c : A} {s : Bool} (hp : IsPrev pv s x c) {v : Vtx A}
    (h : Step (.ain s x c) v) :
    v = pv ∨ (s = true ∧ v = .cls c) ∨ (s = false ∧ v = .bout s x c) := by
  cases v with
  | pad0 y =>
    obtain ⟨hxy, hm⟩ : y = x ∧ VarMin y c s := h
    rcases hp with ⟨-, rfl⟩ | ⟨c', s', hst, -⟩
    · exact Or.inl (by rw [hxy])
    · exact absurd (hxy ▸ hm) (not_varMin_of_step hst)
  | pad s₁ y c₁ =>
    obtain ⟨hxy, hst₁⟩ : y = x ∧ VarStep y c₁ s₁ c s := h
    subst hxy
    rcases hp with ⟨hm, -⟩ | ⟨c', s', hst, rfl⟩
    · exact absurd hm (not_varMin_of_step hst₁)
    · obtain ⟨hc, hs⟩ := varStep_left_unique hst hst₁
      exact Or.inl (by rw [hc, hs])
  | cls c' =>
    obtain ⟨hs, hc⟩ : s = true ∧ c = c' := h
    exact Or.inr (Or.inl ⟨hs, by rw [hc]⟩)
  | bout s₁ y c₁ =>
    obtain ⟨hs, hs₁, hxy, hc⟩ : s = false ∧ s₁ = false ∧ x = y ∧ c = c₁ := h
    exact Or.inr (Or.inr ⟨hs, by rw [hs, hs₁, hxy, hc]⟩)
  | _ => exact (h : False).elim

theorem step_ain_in {pv : Vtx A} {x c : A} {s : Bool} (hp : IsPrev pv s x c) {v : Vtx A}
    (h : Step v (.ain s x c)) :
    v = pv ∨ (s = true ∧ v = .bout s x c) ∨ (s = false ∧ v = .cls c) := by
  cases v with
  | pad0 y =>
    obtain ⟨hxy, hm⟩ : y = x ∧ VarMin y c s := h
    rcases hp with ⟨-, rfl⟩ | ⟨c', s', hst, -⟩
    · exact Or.inl (by rw [hxy])
    · exact absurd (hxy ▸ hm) (not_varMin_of_step hst)
  | pad s₁ y c₁ =>
    obtain ⟨hxy, hst₁⟩ : y = x ∧ VarStep y c₁ s₁ c s := h
    subst hxy
    rcases hp with ⟨hm, -⟩ | ⟨c', s', hst, rfl⟩
    · exact absurd hm (not_varMin_of_step hst₁)
    · obtain ⟨hc, hs⟩ := varStep_left_unique hst hst₁
      exact Or.inl (by rw [hc, hs])
  | bout s₁ y c₁ =>
    obtain ⟨hs₁, hs, hxy, hc⟩ : s₁ = true ∧ s = true ∧ y = x ∧ c₁ = c := h
    exact Or.inr (Or.inl ⟨hs, by rw [hs, hs₁, hxy, hc]⟩)
  | cls c' =>
    obtain ⟨hs, hc⟩ : s = false ∧ c = c' := h
    exact Or.inr (Or.inr ⟨hs, by rw [hc]⟩)
  | _ => exact (h : False).elim

theorem step_bout_out {x c : A} {s : Bool} {v : Vtx A} (h : Step (.bout s x c) v) :
    v = .pad s x c ∨ (s = true ∧ v = .ain s x c) ∨ (s = false ∧ v = .cls c) := by
  cases v with
  | pad s₁ y c₁ =>
    obtain ⟨hs, hxy, hc⟩ : s = s₁ ∧ x = y ∧ c = c₁ := h
    exact Or.inl (by rw [hs, hxy, hc])
  | ain s₁ y c₁ =>
    obtain ⟨hs, hs₁, hxy, hc⟩ : s = true ∧ s₁ = true ∧ x = y ∧ c = c₁ := h
    exact Or.inr (Or.inl ⟨hs, by rw [hs, hs₁, hxy, hc]⟩)
  | cls c' =>
    obtain ⟨hs, hc⟩ : s = false ∧ c = c' := h
    exact Or.inr (Or.inr ⟨hs, by rw [hc]⟩)
  | _ => exact (h : False).elim

theorem step_bout_in {x c : A} {s : Bool} {v : Vtx A} (h : Step v (.bout s x c)) :
    v = .pad s x c ∨ (s = true ∧ v = .cls c) ∨ (s = false ∧ v = .ain s x c) := by
  cases v with
  | pad s₁ y c₁ =>
    obtain ⟨hs, hxy, hc⟩ : s₁ = s ∧ y = x ∧ c₁ = c := h
    exact Or.inl (by rw [hs, hxy, hc])
  | cls c' =>
    obtain ⟨hs, hc⟩ : s = true ∧ c = c' := h
    exact Or.inr (Or.inl ⟨hs, by rw [hc]⟩)
  | ain s₁ y c₁ =>
    obtain ⟨hs₁, hs, hxy, hc⟩ : s₁ = false ∧ s = false ∧ y = x ∧ c₁ = c := h
    exact Or.inr (Or.inr ⟨hs, by rw [hs, hs₁, hxy, hc]⟩)
  | _ => exact (h : False).elim

variable [Finite A]

theorem exists_isPrev {x c : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s) : ∃ pv, IsPrev pv s x c := by
  rcases varMin_or_step ho with hm | ⟨c', s', hst⟩
  exacts [⟨_, Or.inl ⟨hm, rfl⟩⟩, ⟨_, Or.inr ⟨c', s', hst, rfl⟩⟩]

theorem exists_isNext {x c : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s) : ∃ nv, IsNext nv s x c := by
  rcases varMax_or_step ho with hm | ⟨c', s', hst⟩
  exacts [⟨_, Or.inl ⟨hm, rfl⟩⟩, ⟨_, Or.inr ⟨c', s', hst, rfl⟩⟩]

/-! ### The local forcing -/

namespace Circ

variable {N : Vtx A → Vtx A → Prop}

omit [Finite A] in
/-- With a variable in the formula the graph has more than two vertices, so no
two of them follow each other both ways. -/
theorem no2 (hC : Circ N) {x : A} (hx : Lax366625.CountingSat.SatOccurs A x) {u v : Vtx A} (h : N u v)
    (h' : N v u) : False := by
  rcases hC.two h h' (.top x) hx with h₁ | h₁ <;> rcases hC.two h h' (.lft x) hx with h₂ | h₂ <;>
    rcases hC.two h h' (.rgt x) hx with h₃ | h₃ <;>
    first
      | exact absurd (h₁.trans h₂.symm) (by simp)
      | exact absurd (h₁.trans h₃.symm) (by simp)
      | exact absurd (h₂.trans h₃.symm) (by simp)

omit [Finite A] in
/-- **The circuit passes through a vertex with two neighbours.** -/
theorem through (hC : Circ N) (hno2 : ∀ a b, N a b → N b a → False) {p u w : Vtx A}
    (hp : Valid p) (hout : ∀ v, Step p v → v = u ∨ v = w)
    (hin : ∀ v, Step v p → v = u ∨ v = w) : (N u p ∧ N p w) ∨ (N w p ∧ N p u) := by
  obtain ⟨v, hv⟩ := hC.succ p hp
  obtain ⟨v', hv'⟩ := hC.pred p hp
  rcases hout v (hC.arc hv).2.2 with rfl | rfl <;> rcases hin v' (hC.arc hv').2.2 with rfl | rfl
  · exact (hno2 _ _ hv hv').elim
  · exact Or.inr ⟨hv', hv⟩
  · exact Or.inl ⟨hv', hv⟩
  · exact (hno2 _ _ hv hv').elim

omit [Finite A] in
/-- The circuit passes through the row predecessor of an occurrence. -/
theorem prev_adj (hC : Circ N) {pv : Vtx A} {x c : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s)
    (hp : IsPrev pv s x c) : N pv (.ain s x c) ∨ N (.ain s x c) pv := by
  have hno2 := fun a b => hC.no2 (N := N) (occurs_of_occIn ho) (u := a) (v := b)
  rcases hp with ⟨hm, rfl⟩ | ⟨c', s', hst, rfl⟩
  · rcases hC.through hno2 (p := .pad0 x) (occurs_of_occIn ho)
      (fun v => step_pad0_out hm) (fun v => step_pad0_in hm) with h | h
    exacts [Or.inl h.2, Or.inr h.1]
  · have hn : IsNext (.ain s x c) s' x c' := Or.inr ⟨c, s, hst, rfl⟩
    rcases hC.through hno2 (p := .pad s' x c') hst.1
      (fun v => step_pad_out hn) (fun v => step_pad_in hn) with h | h
    exacts [Or.inl h.2, Or.inr h.1]

/-- **An occurrence entered from the left is left to the right**, through its
clause vertex iff it is positive. -/
theorem pairT (hC : Circ N) {pv : Vtx A} {x c : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s)
    (hp : IsPrev pv s x c) (h : N pv (.ain s x c)) :
    (s = true → N (.ain s x c) (.cls c) ∧ N (.cls c) (.bout s x c)) ∧
      (s = false → N (.ain s x c) (.bout s x c)) ∧ N (.bout s x c) (.pad s x c) := by
  have hno2 := fun a b => hC.no2 (N := N) (occurs_of_occIn ho) (u := a) (v := b)
  have hpv : ∀ t y d, pv ≠ .bout t y d := by
    intro t y d
    rcases hp with ⟨-, rfl⟩ | ⟨c', s', -, rfl⟩ <;> simp
  obtain ⟨v, hv⟩ := hC.succ (.ain s x c) ho
  obtain ⟨w, hw⟩ := hC.succ (.bout s x c) ho
  obtain ⟨w', hw'⟩ := hC.pred (.bout s x c) ho
  rcases step_ain_out hp (hC.arc hv).2.2 with rfl | ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · exact (hno2 _ _ h hv).elim
  · -- positive: `ain → cls`, then `bout → pad` and `cls → bout`
    have hbq : N (.bout s x c) (.pad s x c) := by
      rcases step_bout_out (hC.arc hw).2.2 with rfl | ⟨-, rfl⟩ | ⟨hs', -⟩
      · exact hw
      · exact absurd (hC.inj h hw) (hpv _ _ _)
      · exact absurd (hs.symm.trans hs') (by decide)
    refine ⟨fun _ => ⟨hv, ?_⟩, fun hs' => absurd (hs.symm.trans hs') (by decide), hbq⟩
    rcases step_bout_in (hC.arc hw').2.2 with rfl | ⟨-, rfl⟩ | ⟨hs', -⟩
    · exact (hno2 _ _ hbq hw').elim
    · exact hw'
    · exact absurd (hs.symm.trans hs') (by decide)
  · -- negative: `ain → bout`, then `bout → pad`
    refine ⟨fun hs' => absurd (hs'.symm.trans hs) (by decide), fun _ => hv, ?_⟩
    rcases step_bout_out (hC.arc hw).2.2 with rfl | ⟨hs', -⟩ | ⟨-, rfl⟩
    · exact hw
    · exact absurd (hs'.symm.trans hs) (by decide)
    · -- `bout → cls`: then `bout` is reached from `ain`, and `pad` is stranded
      obtain ⟨nv, hn⟩ := exists_isNext ho
      rcases hC.through hno2 (p := .pad s x c) ho
        (fun v => step_pad_out hn) (fun v => step_pad_in hn) with h' | h'
      · exact absurd (hC.func h'.1 hw) (by simp)
      · exact absurd (hC.inj h'.2 hv) (by simp)

/-- **An occurrence entered from the right is left to the left**, through its
clause vertex iff it is negative. -/
theorem pairF (hC : Circ N) {pv : Vtx A} {x c : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s)
    (hp : IsPrev pv s x c) (h : N (.pad s x c) (.bout s x c)) :
    N (.ain s x c) pv ∧ (s = true → N (.bout s x c) (.ain s x c)) ∧
      (s = false → N (.bout s x c) (.cls c) ∧ N (.cls c) (.ain s x c)) := by
  have hno2 := fun a b => hC.no2 (N := N) (occurs_of_occIn ho) (u := a) (v := b)
  have hapv : N (.ain s x c) pv := by
    rcases hC.prev_adj ho hp with h' | h'
    · exact (hno2 _ _ (hC.pairT ho hp h').2.2 h).elim
    · exact h'
  obtain ⟨w, hw⟩ := hC.pred (.ain s x c) ho
  rcases step_ain_in hp (hC.arc hw).2.2 with rfl | ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · exact (hno2 _ _ hapv hw).elim
  · exact ⟨hapv, fun _ => hw, fun hs' => absurd (hs.symm.trans hs') (by decide)⟩
  · refine ⟨hapv, fun hs' => absurd (hs'.symm.trans hs) (by decide), fun _ => ⟨?_, hw⟩⟩
    obtain ⟨w', hw'⟩ := hC.succ (.bout s x c) ho
    rcases step_bout_out (hC.arc hw').2.2 with rfl | ⟨hs', -⟩ | ⟨-, rfl⟩
    · exact (hno2 _ _ hw' h).elim
    · exact absurd (hs'.symm.trans hs) (by decide)
    · exact hw'

end Circ

omit [Finite A] in
theorem isPrev_unique {pv pv' : Vtx A} {x c : A} {s : Bool} (h : IsPrev pv s x c)
    (h' : IsPrev pv' s x c) : pv = pv' := by
  rcases h with ⟨hm, rfl⟩ | ⟨c₁, s₁, hst, rfl⟩ <;> rcases h' with ⟨hm', rfl⟩ | ⟨c₂, s₂, hst', rfl⟩
  · rfl
  · exact absurd hm (not_varMin_of_step hst')
  · exact absurd hm' (not_varMin_of_step hst)
  · obtain ⟨hc, hs⟩ := varStep_left_unique hst hst'
    rw [hc, hs]

/-- The occurrence is traversed from the left. -/
def TLoc (N : Vtx A → Vtx A → Prop) (s : Bool) (x c : A) : Prop :=
  (∀ pv, IsPrev pv s x c → N pv (.ain s x c)) ∧
    (s = true → N (.ain s x c) (.cls c) ∧ N (.cls c) (.bout s x c)) ∧
    (s = false → N (.ain s x c) (.bout s x c)) ∧ N (.bout s x c) (.pad s x c)

/-- The occurrence is traversed from the right. -/
def FLoc (N : Vtx A → Vtx A → Prop) (s : Bool) (x c : A) : Prop :=
  N (.pad s x c) (.bout s x c) ∧ (s = true → N (.bout s x c) (.ain s x c)) ∧
    (s = false → N (.bout s x c) (.cls c) ∧ N (.cls c) (.ain s x c)) ∧
    ∀ pv, IsPrev pv s x c → N (.ain s x c) pv

namespace Circ

variable {N : Vtx A → Vtx A → Prop}

theorem tloc_of_enter (hC : Circ N) {pv : Vtx A} {x c : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s)
    (hp : IsPrev pv s x c) (h : N pv (.ain s x c)) : TLoc N s x c :=
  ⟨fun _ hp' => isPrev_unique hp hp' ▸ h, hC.pairT ho hp h⟩

theorem floc_of_enter (hC : Circ N) {x c : A} {s : Bool} (ho : Lax799700.Common.SatOcc.OccIn c x s)
    (h : N (.pad s x c) (.bout s x c)) : FLoc N s x c := by
  obtain ⟨pv, hp⟩ := exists_isPrev ho
  obtain ⟨h₁, h₂, h₃⟩ := hC.pairF ho hp h
  exact ⟨h, h₂, h₃, fun pv' hp' => isPrev_unique hp hp' ▸ h₁⟩

/-- **A row entered from the left is swept from the left.** -/
theorem rowT (hC : Circ N) {x : A} (hx : Lax366625.CountingSat.SatOccurs A x) (hν : N (.top x) (.lft x)) :
    N (.lft x) (.pad0 x) ∧ ∀ c s, Lax799700.Common.SatOcc.OccIn c x s → TLoc N s x c := by
  have hno2 := fun a b => hC.no2 (N := N) hx (u := a) (v := b)
  obtain ⟨c₁, s₁, hm⟩ := exists_varMin (exists_occIn_of_occurs hx)
  have hstart : N (.lft x) (.pad0 x) ∧ N (.pad0 x) (.ain s₁ x c₁) := by
    rcases hC.through hno2 (p := .pad0 x) hx
      (fun v => step_pad0_out hm) (fun v => step_pad0_in hm) with h | h
    · exact h
    · exact absurd (hC.inj hν h.2) (by simp)
  refine ⟨hstart.1, occ_induction_up (fun c s hm' => ?_) fun c s c' s' hst htl => ?_⟩
  · obtain ⟨hc, hs⟩ := varMin_unique hm hm'
    subst hc hs
    exact hC.tloc_of_enter hm.1 (Or.inl ⟨hm, rfl⟩) hstart.2
  · have hn : IsNext (.ain s' x c') s x c := Or.inr ⟨c', s', hst, rfl⟩
    rcases hC.through hno2 (p := .pad s x c) hst.1
      (fun v => step_pad_out hn) (fun v => step_pad_in hn) with h | h
    · exact hC.tloc_of_enter hst.2.1 (Or.inr ⟨c, s, hst, rfl⟩) h.2
    · exact (hno2 _ _ htl.2.2.2 h.2).elim

/-- **A row entered from the right is swept from the right.** -/
theorem rowF (hC : Circ N) {x : A} (hx : Lax366625.CountingSat.SatOccurs A x) (hν : ¬N (.top x) (.lft x)) :
    N (.top x) (.rgt x) ∧ (∀ c s, VarMax x c s → N (.rgt x) (.pad s x c)) ∧
      ∀ c s, Lax799700.Common.SatOcc.OccIn c x s → FLoc N s x c := by
  have hno2 := fun a b => hC.no2 (N := N) hx (u := a) (v := b)
  have htop : N (.top x) (.rgt x) := by
    obtain ⟨v, hv⟩ := hC.succ (.top x) hx
    have hst := (hC.arc hv).2.2
    cases v with
    | lft y =>
      have hxy : x = y := hst
      exact absurd (hxy ▸ hv) hν
    | rgt y =>
      have hxy : x = y := hst
      exact hxy ▸ hv
    | _ => exact (hst : False).elim
  have hmax : ∀ c s, VarMax x c s → N (.rgt x) (.pad s x c) ∧ N (.pad s x c) (.bout s x c) := by
    intro c s hm
    have hn : IsNext (.rgt x) s x c := Or.inl ⟨hm, rfl⟩
    rcases hC.through hno2 (p := .pad s x c) hm.1
      (fun v => step_pad_out hn) (fun v => step_pad_in hn) with h | h
    · exact absurd (hC.inj htop h.2) (by simp)
    · exact h
  refine ⟨htop, fun c s hm => (hmax c s hm).1,
    occ_induction_down (fun c s hm => hC.floc_of_enter hm.1 (hmax c s hm).2)
      fun c s c' s' hst hfl => ?_⟩
  have hn : IsNext (.ain s' x c') s x c := Or.inr ⟨c', s', hst, rfl⟩
  rcases hC.through hno2 (p := .pad s x c) hst.1
    (fun v => step_pad_out hn) (fun v => step_pad_in hn) with h | h
  · exact (hno2 _ _ h.2 (hfl.2.2.2 _ (Or.inr ⟨c, s, hst, rfl⟩))).elim
  · exact hC.floc_of_enter hst.1 h.2

/-- **Every arc of a circuit is an arc of the circuit of its assignment**: the
assignment making `x` true when its row is entered from the left. -/
theorem exists_S (hC : Circ N) {u : Vtx A} (hu : Valid u) :
    ∃ v, N u v ∧ S (fun x => N (.top x) (.lft x)) u v := by
  have tl : ∀ {x : A}, N (.top x) (.lft x) → ∀ c s, Lax799700.Common.SatOcc.OccIn c x s → TLoc N s x c :=
    fun {x} h c s ho => (hC.rowT (occurs_of_occIn ho) h).2 c s ho
  have fl : ∀ {x : A}, ¬N (.top x) (.lft x) → ∀ c s, Lax799700.Common.SatOcc.OccIn c x s → FLoc N s x c :=
    fun {x} h c s ho => (hC.rowF (occurs_of_occIn ho) h).2.2 c s ho
  cases u with
  | top x =>
    by_cases h : N (.top x) (.lft x)
    · exact ⟨_, h, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨_, (hC.rowF hu h).1, Or.inr ⟨h, rfl⟩⟩
  | lft x =>
    by_cases h : N (.top x) (.lft x)
    · exact ⟨_, (hC.rowT hu h).1, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨v, hv⟩ := hC.succ (.lft x) hu
      have hst := (hC.arc hv).2.2
      cases v with
      | pad0 y =>
        have hxy : x = y := hst
        subst hxy
        obtain ⟨c, s, hm⟩ := exists_varMin (exists_occIn_of_occurs hu)
        exact absurd (hC.inj hv ((fl h c s hm.1).2.2.2 _ (Or.inl ⟨hm, rfl⟩))) (by simp)
      | top y => exact ⟨_, hv, Or.inr ⟨h, y, hst, rfl⟩⟩
      | _ => exact (hst : False).elim
  | rgt x =>
    by_cases h : N (.top x) (.lft x)
    · obtain ⟨v, hv⟩ := hC.succ (.rgt x) hu
      have hst := (hC.arc hv).2.2
      cases v with
      | pad s y c =>
        obtain ⟨hxy, hm⟩ : y = x ∧ VarMax y c s := hst
        subst hxy
        exact absurd (hC.inj hv (tl h c s hm.1).2.2.2) (by simp)
      | top y => exact ⟨_, hv, Or.inl ⟨h, y, hst, rfl⟩⟩
      | _ => exact (hst : False).elim
    · obtain ⟨c, s, hm⟩ := exists_varMax (exists_occIn_of_occurs hu)
      exact ⟨_, (hC.rowF hu h).2.1 c s hm, Or.inr ⟨h, c, s, hm, rfl⟩⟩
  | pad0 x =>
    obtain ⟨c, s, hm⟩ := exists_varMin (exists_occIn_of_occurs hu)
    by_cases h : N (.top x) (.lft x)
    · exact ⟨_, (tl h c s hm.1).1 _ (Or.inl ⟨hm, rfl⟩), Or.inl ⟨h, c, s, hm, rfl⟩⟩
    · have hno2 := fun a b => hC.no2 (N := N) hu (u := a) (v := b)
      have hapv := (fl h c s hm.1).2.2.2 _ (Or.inl ⟨hm, rfl⟩)
      rcases hC.through hno2 (p := .pad0 x) hu
        (fun v => step_pad0_out hm) (fun v => step_pad0_in hm) with h' | h'
      · exact (hno2 _ _ h'.2 hapv).elim
      · exact ⟨_, h'.2, Or.inr ⟨h, rfl⟩⟩
  | ain s x c =>
    by_cases h : N (.top x) (.lft x)
    · have htl := tl h c s hu
      cases s
      · exact ⟨_, htl.2.2.1 rfl, Or.inl ⟨h, Or.inr ⟨rfl, rfl⟩⟩⟩
      · exact ⟨_, (htl.2.1 rfl).1, Or.inl ⟨h, Or.inl ⟨rfl, rfl⟩⟩⟩
    · obtain ⟨pv, hp⟩ := exists_isPrev hu
      have hapv := (fl h c s hu).2.2.2 pv hp
      rcases hp with ⟨hm, rfl⟩ | ⟨c', s', hst, rfl⟩
      · exact ⟨_, hapv, Or.inr ⟨h, Or.inr ⟨hm, rfl⟩⟩⟩
      · exact ⟨_, hapv, Or.inr ⟨h, Or.inl ⟨c', s', hst, rfl⟩⟩⟩
  | bout s x c =>
    by_cases h : N (.top x) (.lft x)
    · exact ⟨_, (tl h c s hu).2.2.2, Or.inl ⟨h, rfl⟩⟩
    · have hfl := fl h c s hu
      cases s
      · exact ⟨_, (hfl.2.2.1 rfl).1, Or.inr ⟨h, Or.inr ⟨rfl, rfl⟩⟩⟩
      · exact ⟨_, hfl.2.1 rfl, Or.inr ⟨h, Or.inl ⟨rfl, rfl⟩⟩⟩
  | pad s x c =>
    by_cases h : N (.top x) (.lft x)
    · have hno2 := fun a b => hC.no2 (N := N) (occurs_of_occIn hu) (u := a) (v := b)
      obtain ⟨nv, hn⟩ := exists_isNext hu
      have hqn : N (.pad s x c) nv := by
        rcases hC.through hno2 (p := .pad s x c) hu
          (fun v => step_pad_out hn) (fun v => step_pad_in hn) with h' | h'
        · exact h'.2
        · exact (hno2 _ _ (tl h c s hu).2.2.2 h'.2).elim
      rcases hn with ⟨hm, rfl⟩ | ⟨c', s', hst, rfl⟩
      · exact ⟨_, hqn, Or.inl ⟨h, Or.inr ⟨hm, rfl⟩⟩⟩
      · exact ⟨_, hqn, Or.inl ⟨h, Or.inl ⟨c', s', hst, rfl⟩⟩⟩
    · exact ⟨_, (fl h c s hu).1, Or.inr ⟨h, rfl⟩⟩
  | cls c =>
    obtain ⟨v, hv⟩ := hC.succ (.cls c) hu
    have hst := (hC.arc hv).2.2
    have hval := (hC.arc hv).2.1
    cases v with
    | bout s y c' =>
      obtain ⟨hs, hc⟩ : s = true ∧ c' = c := hst
      subst hs hc
      have hy : N (.top y) (.lft y) := by
        by_contra h
        exact absurd (hC.inj hv (fl h _ _ hval).1) (by simp)
      exact ⟨_, hv, Or.inl ⟨y, hval, hy, rfl⟩⟩
    | ain s y c' =>
      obtain ⟨hs, hc⟩ : s = false ∧ c' = c := hst
      subst hs hc
      have hy : ¬N (.top y) (.lft y) := by
        intro h
        obtain ⟨pv, hp⟩ := exists_isPrev hval
        have hpa := (tl h _ _ hval).1 pv hp
        rcases hp with ⟨-, rfl⟩ | ⟨c'', s'', -, rfl⟩ <;>
          exact absurd (hC.inj hv hpa) (by simp)
      exact ⟨_, hv, Or.inr ⟨y, hval, hy, rfl⟩⟩
    | _ => exact (hst : False).elim
  | zero =>
    obtain ⟨v, hv⟩ := hC.succ .zero hu
    have hst := (hC.arc hv).2.2
    cases v with
    | zero => exact ⟨_, hv, rfl⟩
    | _ => exact (hst : False).elim

/-- **The assignment of a circuit is an exactly-one model.** -/
theorem oneInModel (hC : Circ N) : Lax280166.CountingSatVariants.OneInModel A fun x => N (.top x) (.lft x) := by
  refine ⟨fun c hc => ?_, fun x hx => (hC.arc hx).1⟩
  obtain ⟨v, hv, hS⟩ := hC.exists_S (u := .cls c) hc
  rcases hS with ⟨x, ho, hx, rfl⟩ | ⟨x, ho, hx, rfl⟩
  · refine ⟨x, true, ho, hx, fun y t hy hT => ?_⟩
    cases t
    · have h := ((hC.rowF (occurs_of_occIn hy) hT).2.2 c false hy).2.2.1 rfl
      exact absurd (hC.func hv h.2) (by simp)
    · have h := ((hC.rowT (occurs_of_occIn hy) hT).2 c true hy).2.1 rfl
      have he := hC.func hv h.2
      simp only [Vtx.bout.injEq] at he
      exact ⟨he.2.1.symm, rfl⟩
  · refine ⟨x, false, ho, hx, fun y t hy hT => ?_⟩
    cases t
    · have h := ((hC.rowF (occurs_of_occIn hy) hT).2.2 c false hy).2.2.1 rfl
      have he := hC.func hv h.2
      simp only [Vtx.ain.injEq] at he
      exact ⟨he.2.1.symm, rfl⟩
    · have h := ((hC.rowT (occurs_of_occIn hy) hT).2 c true hy).2.1 rfl
      exact absurd (hC.func hv h.2) (by simp)

/-- **A circuit is the circuit of its assignment.** -/
theorem eq_S (hC : Circ N) {u v : Vtx A} (hu : Valid u) :
    N u v ↔ S (fun x => N (.top x) (.lft x)) u v := by
  obtain ⟨v₀, hv₀, hS₀⟩ := hC.exists_S hu
  constructor
  · intro h
    rw [hC.func h hv₀]
    exact hS₀
  · intro h
    rw [S_functional hC.oneInModel.1 h hS₀]
    exact hv₀

end Circ

/-! ### The correspondence -/

/-- A Hamilton circuit of the row graph, read locally. -/
theorem circ_of_isCircuit {Nxt : {v : Vtx A // Valid v} → {v : Vtx A // Valid v} → Prop}
    (h : Lax280166.CountingHamiltonCircuits.IsCircuit (fun u v : {v : Vtx A // Valid v} => Arc u.1 v.1) Nxt) :
    Circ fun u v => ∃ (hu : Valid u) (hv : Valid v), Nxt ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨htot, hfun, hsurj, hinj, hR, htwo⟩ := h.local
  refine ⟨fun u hu => ?_, fun v hv => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := htot ⟨u, hu⟩
    exact ⟨v.1, hu, v.2, hv⟩
  · obtain ⟨u, hu⟩ := hsurj ⟨v, hv⟩
    exact ⟨u.1, u.2, hv, hu⟩
  · rintro u v v' ⟨hu, hv, h₁⟩ ⟨hu', hv', h₂⟩
    exact congrArg Subtype.val (hfun _ _ _ h₁ h₂)
  · rintro u u' v ⟨hu, hv, h₁⟩ ⟨hu', hv', h₂⟩
    exact congrArg Subtype.val (hinj _ _ _ h₁ h₂)
  · rintro u v ⟨hu, hv, h₁⟩
    exact hR _ _ h₁
  · rintro u v ⟨hu, hv, h₁⟩ ⟨hv', hu', h₂⟩ z hz
    rcases htwo _ _ h₁ h₂ ⟨z, hz⟩ with h' | h'
    exacts [Or.inl (congrArg Subtype.val h'), Or.inr (congrArg Subtype.val h')]

variable (A) [Nonempty A]

/-- **The Hamilton circuits of the row graph are the exactly-one models of the
formula**, bijectively. -/
noncomputable def modelEquiv :
    {ν : A → Prop // Lax280166.CountingSatVariants.OneInModel A ν} ≃
      {Nxt : {v : Vtx A // Valid v} → {v : Vtx A // Valid v} → Prop //
        Lax280166.CountingHamiltonCircuits.IsCircuit (fun u v : {v : Vtx A // Valid v} => Arc u.1 v.1) Nxt} :=
  Equiv.ofBijective (fun ν => ⟨fun u v => S ν.1 u.1 v.1, isCircuit_S ν.2.1⟩) (by
    constructor
    · rintro ⟨ν, hν⟩ ⟨ν', hν'⟩ heq
      have hrel : ∀ u v : {v : Vtx A // Valid v}, S ν u.1 v.1 ↔ S ν' u.1 v.1 := fun u v =>
        iff_of_eq (congrFun (congrFun (congrArg Subtype.val heq) u) v)
      have key : ∀ {μ μ' : A → Prop}, Lax280166.CountingSatVariants.OneInModel A μ →
          (∀ u v : {v : Vtx A // Valid v}, S μ u.1 v.1 → S μ' u.1 v.1) →
          ∀ x, μ x → μ' x := by
        intro μ μ' hμ hsub x hx
        have hocc := hμ.2 x hx
        rcases hsub ⟨.top x, hocc⟩ ⟨.lft x, hocc⟩ (Or.inl ⟨hx, rfl⟩) with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exact absurd h (by simp)
      exact Subtype.ext (funext fun x => propext
        ⟨key hν (fun u v => (hrel u v).mp) x, key hν' (fun u v => (hrel u v).mpr) x⟩)
    · rintro ⟨Nxt, hN⟩
      have hC := circ_of_isCircuit hN
      refine ⟨⟨_, hC.oneInModel⟩, Subtype.ext (funext fun u => funext fun v => propext ?_)⟩
      refine (hC.eq_S u.2).symm.trans ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨u.2, v.2, h⟩⟩)

end Reverse

end HamGadget

end Lax280166Proofs.DescriptiveComplexity


