/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Hamilton.CircuitPerm
import Lax280166Proofs.DescriptiveComplexity.OccurrenceVar
import Lax280166Proofs.DescriptiveComplexity.Problems.OneInSat.Counting
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

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatOccurs)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl OccIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

/-!
# The row graph of a CNF formula

The graph whose Hamilton circuits are the exactly-one models of a CNF formula,
as a graph on a type of its own (`DescriptiveComplexity.HamGadget.Vtx`): the
interpretation that draws it in the formula is in
`DescriptiveComplexity.Problems.Hamilton.CountingHardness`, and everything about
circuits is proved here, where a vertex is a constructor and not a tagged
tuple.

## The graph

Each variable `x` of the formula has a **row**, a two-way path

`lft x, pad0 x, [ain o₁, bout o₁], pad o₁, [ain o₂, bout o₂], pad o₂, …, pad oₖ, rgt x`

through its occurrences `o₁ < … < oₖ` (`DescriptiveComplexity.SatOcc.VarStep`), and an
entry vertex `top x` with arcs to both ends; both ends have an arc to the
`top` of the next variable, cyclically. A row is traversed from `lft` to `rgt`
when the variable is true, from `rgt` to `lft` when it is false.

Inside the pair of an occurrence the path is *not* two-way. For a positive
occurrence in the clause `c` the arcs are `ain → cls c → bout` and
`bout → ain`: there is no arc `ain → bout`, so a row traversed from the left –
the direction making the literal true – *has to* visit the clause vertex. A
negative occurrence is the mirror image. A clause vertex is therefore visited
once per true literal, and a Hamilton circuit visits it once: exactly one
literal of each clause is true.

The `pad` vertices have their two row neighbours and nothing else, which is
what forces a row to be traversed in one sweep: a circuit cannot enter a
clause vertex from one row and leave into another without stranding a `pad`.

A formula with no clause has no row; its one model is matched by the single
vertex `zero`, with a loop.

## This file

The vertices, the arcs (`DescriptiveComplexity.HamGadget.Arc`), the circuit of an
assignment (`DescriptiveComplexity.HamGadget.S`), and the order lemmas both
directions of the correspondence use: the cyclic successor on the variables of
the formula, induction along the occurrences of a variable in both directions,
and the rank of an occurrence.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace HamGadget

open Language Structure SatOcc

/-- The vertices of the row graph. -/
inductive Vtx (A : Type) : Type
  /-- The entry of the row of the variable `x`. -/
  | top (x : A)
  /-- The left end of the row of `x`. -/
  | lft (x : A)
  /-- The right end of the row of `x`. -/
  | rgt (x : A)
  /-- The padding between the left end and the first occurrence of `x`. -/
  | pad0 (x : A)
  /-- The left vertex of the occurrence of sign `s` of `x` in `c`. -/
  | ain (s : Bool) (x c : A)
  /-- The right vertex of the occurrence of sign `s` of `x` in `c`. -/
  | bout (s : Bool) (x c : A)
  /-- The padding after the occurrence of sign `s` of `x` in `c`. -/
  | pad (s : Bool) (x c : A)
  /-- The vertex of the clause `c`. -/
  | cls (c : A)
  /-- The single vertex of a formula with no clause. -/
  | zero

section Order

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

/-! ### The cyclic order on the variables of the formula -/

/-- `x` is the first variable of the formula. -/
def VFirst (x : A) : Prop := Lax366625.CountingSat.SatOccurs A x ∧ ∀ z, Lax366625.CountingSat.SatOccurs A z → x ≤ z

/-- `x` is the last variable of the formula. -/
def VLast (x : A) : Prop := Lax366625.CountingSat.SatOccurs A x ∧ ∀ z, Lax366625.CountingSat.SatOccurs A z → z ≤ x

/-- `y` is the variable of the formula immediately after `x`. -/
def VStep (x y : A) : Prop :=
  Lax366625.CountingSat.SatOccurs A x ∧ Lax366625.CountingSat.SatOccurs A y ∧ x < y ∧ ∀ z, Lax366625.CountingSat.SatOccurs A z → ¬(x < z ∧ z < y)

/-- `y` follows `x` cyclically among the variables of the formula. -/
def NextVar (x y : A) : Prop := VStep x y ∨ (VLast x ∧ VFirst y)

theorem NextVar.occ_left {x y : A} (h : NextVar x y) : Lax366625.CountingSat.SatOccurs A x := by
  rcases h with h | ⟨h, -⟩
  exacts [h.1, h.1]

theorem NextVar.occ_right {x y : A} (h : NextVar x y) : Lax366625.CountingSat.SatOccurs A y := by
  rcases h with h | ⟨-, h⟩
  exacts [h.2.1, h.1]

theorem nextVar_right_unique {x y y' : A} (h : NextVar x y) (h' : NextVar x y') : y = y' := by
  rcases h with h | ⟨hl, hf⟩ <;> rcases h' with h' | ⟨hl', hf'⟩
  · rcases lt_trichotomy y y' with hlt | heq | hlt
    · exact absurd ⟨h.2.2.1, hlt⟩ (h'.2.2.2 y h.2.1)
    · exact heq
    · exact absurd ⟨h'.2.2.1, hlt⟩ (h.2.2.2 y' h'.2.1)
  · exact absurd (hl'.2 y h.2.1) (not_le.mpr h.2.2.1)
  · exact absurd (hl.2 y' h'.2.1) (not_le.mpr h'.2.2.1)
  · exact le_antisymm (hf.2 y' hf'.1) (hf'.2 y hf.1)

/-- A wrap-around step is not an increasing one. -/
theorem NextVar.lt_or_last {x y : A} (h : NextVar x y) : x < y ∨ VLast x :=
  h.elim (fun h => Or.inl h.2.2.1) fun h => Or.inr h.1

variable [Finite A]

theorem exists_vFirst (h : ∃ x : A, Lax366625.CountingSat.SatOccurs A x) : ∃ x : A, VFirst x := by
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image {x : A | Lax366625.CountingSat.SatOccurs A x} id (Set.toFinite _) h
  exact ⟨x, hx, fun z hz => hmin z hz⟩

theorem exists_vLast (h : ∃ x : A, Lax366625.CountingSat.SatOccurs A x) : ∃ x : A, VLast x := by
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image {x : A | Lax366625.CountingSat.SatOccurs A x} id (Set.toFinite _) h
  exact ⟨x, hx, fun z hz => hmax z hz⟩

theorem exists_nextVar {x : A} (hx : Lax366625.CountingSat.SatOccurs A x) : ∃ y, NextVar x y := by
  by_cases h : ∃ z, Lax366625.CountingSat.SatOccurs A z ∧ x < z
  · obtain ⟨y, hy, hmin⟩ :=
      Set.exists_min_image {z : A | Lax366625.CountingSat.SatOccurs A z ∧ x < z} id (Set.toFinite _) h
    exact ⟨y, Or.inl ⟨hx, hy.1, hy.2, fun z hz hzz =>
      absurd (hmin z ⟨hz, hzz.1⟩) (not_le.mpr hzz.2)⟩⟩
  · obtain ⟨y, hy⟩ := exists_vFirst ⟨x, hx⟩
    exact ⟨y, Or.inr ⟨⟨hx, fun z hz => not_lt.mp fun hlt => h ⟨z, hz, hlt⟩⟩, hy⟩⟩

theorem exists_prevVar {y : A} (hy : Lax366625.CountingSat.SatOccurs A y) : ∃ x, NextVar x y := by
  by_cases h : ∃ z, Lax366625.CountingSat.SatOccurs A z ∧ z < y
  · obtain ⟨x, hx, hmax⟩ :=
      Set.exists_max_image {z : A | Lax366625.CountingSat.SatOccurs A z ∧ z < y} id (Set.toFinite _) h
    exact ⟨x, Or.inl ⟨hx.1, hy, hx.2, fun z hz hzz =>
      absurd (hmax z ⟨hz, hzz.2⟩) (not_le.mpr hzz.1)⟩⟩
  · obtain ⟨x, hx⟩ := exists_vLast ⟨y, hy⟩
    exact ⟨x, Or.inr ⟨hx, hy, fun z hz => not_lt.mp fun hlt => h ⟨z, hz, hlt⟩⟩⟩

/-! ### The occurrences of a variable: ranks and inductions -/

/-- The rank of an occurrence of `x`: the number of occurrences of `x`
before it. -/
noncomputable def occRank (x c : A) (s : Bool) : ℕ :=
  {p : A × Bool | Lax799700.Common.SatOcc.OccIn p.1 x p.2 ∧ occLt p.1 p.2 c s}.ncard

/-- The number of occurrences of `x`. -/
noncomputable def occTotal (x : A) : ℕ :=
  {p : A × Bool | Lax799700.Common.SatOcc.OccIn p.1 x p.2}.ncard

theorem occRank_lt_of_occLt {x c c' : A} {s s' : Bool} (hc : Lax799700.Common.SatOcc.OccIn c x s)
    (h : occLt c s c' s') : occRank x c s < occRank x c' s' := by
  refine Set.ncard_lt_ncard ⟨fun p hp => ⟨hp.1, occLt_trans hp.2 h⟩, fun hsub => ?_⟩
  exact occLt_irrefl c s (hsub (show (c, s) ∈ _ from ⟨hc, h⟩)).2

theorem occRank_lt_of_varStep {x c c' : A} {s s' : Bool} (h : VarStep x c s c' s') :
    occRank x c s < occRank x c' s' :=
  occRank_lt_of_occLt h.1 h.2.2.1

theorem occRank_lt_total {x c : A} {s : Bool} (hc : Lax799700.Common.SatOcc.OccIn c x s) :
    occRank x c s < occTotal x := by
  refine Set.ncard_lt_ncard ⟨fun p hp => hp.1, fun hsub => ?_⟩
  exact occLt_irrefl c s (hsub (show (c, s) ∈ _ from hc)).2

/-- Induction along the occurrences of a variable, upward from the first. -/
theorem occ_induction_up {x : A} {P : A → Bool → Prop}
    (hmin : ∀ c s, VarMin x c s → P c s)
    (hstep : ∀ c s c' s', VarStep x c s c' s' → P c s → P c' s') :
    ∀ c s, Lax799700.Common.SatOcc.OccIn c x s → P c s := by
  intro c s
  induction hr : occRank x c s using Nat.strong_induction_on generalizing c s with
  | _ n ih =>
    intro hc
    by_cases hm : VarMin x c s
    · exact hmin c s hm
    · have hne : ∃ c' t, Lax799700.Common.SatOcc.OccIn c' x t ∧ occLt c' t c s := by
        by_contra hcon
        exact hm ⟨hc, fun c' t hct hlt => hcon ⟨c', t, hct, hlt⟩⟩
      obtain ⟨c', t, hst⟩ := exists_varStep_left hc hne
      exact hstep c' t c s hst
        (ih _ (hr ▸ occRank_lt_of_varStep hst) c' t rfl hst.1)

/-- Induction along the occurrences of a variable, downward from the last. -/
theorem occ_induction_down {x : A} {P : A → Bool → Prop}
    (hmax : ∀ c s, VarMax x c s → P c s)
    (hstep : ∀ c s c' s', VarStep x c s c' s' → P c' s' → P c s) :
    ∀ c s, Lax799700.Common.SatOcc.OccIn c x s → P c s := by
  intro c s
  induction hr : occTotal x - occRank x c s using Nat.strong_induction_on generalizing c s with
  | _ n ih =>
    intro hc
    by_cases hm : VarMax x c s
    · exact hmax c s hm
    · have hne : ∃ c' t, Lax799700.Common.SatOcc.OccIn c' x t ∧ occLt c s c' t := by
        by_contra hcon
        exact hm ⟨hc, fun c' t hct hlt => hcon ⟨c', t, hct, hlt⟩⟩
      obtain ⟨c', t, hst⟩ := exists_varStep_right hc hne
      have h₁ := occRank_lt_of_varStep hst
      have h₂ := occRank_lt_total hst.2.1
      exact hstep c s c' t hst (ih _ (by omega) c' t rfl hst.2.1)

omit [LinearOrder A] [Finite A] in
theorem exists_occIn_of_occurs {x : A} (hx : Lax366625.CountingSat.SatOccurs A x) : ∃ c s, Lax799700.Common.SatOcc.OccIn c x s := by
  obtain ⟨c, hc, h | h⟩ := hx
  exacts [⟨c, true, hc, h⟩, ⟨c, false, hc, h⟩]

omit [LinearOrder A] [Finite A] in
theorem occurs_of_occIn {x c : A} {s : Bool} (h : Lax799700.Common.SatOcc.OccIn c x s) : Lax366625.CountingSat.SatOccurs A x := by
  cases s
  · exact ⟨c, h.1, Or.inr h.2⟩
  · exact ⟨c, h.1, Or.inl h.2⟩

/-- An occurrence is the last one, or has a next one. -/
theorem varMax_or_step {x c : A} {s : Bool} (hc : Lax799700.Common.SatOcc.OccIn c x s) :
    VarMax x c s ∨ ∃ c' s', VarStep x c s c' s' := by
  by_cases hm : VarMax x c s
  · exact Or.inl hm
  · have hne : ∃ c' t, Lax799700.Common.SatOcc.OccIn c' x t ∧ occLt c s c' t := by
      by_contra hcon
      exact hm ⟨hc, fun c' t hct hlt => hcon ⟨c', t, hct, hlt⟩⟩
    exact Or.inr (exists_varStep_right hc hne)

/-- An occurrence is the first one, or has a previous one. -/
theorem varMin_or_step {x c : A} {s : Bool} (hc : Lax799700.Common.SatOcc.OccIn c x s) :
    VarMin x c s ∨ ∃ c' s', VarStep x c' s' c s := by
  by_cases hm : VarMin x c s
  · exact Or.inl hm
  · have hne : ∃ c' t, Lax799700.Common.SatOcc.OccIn c' x t ∧ occLt c' t c s := by
      by_contra hcon
      exact hm ⟨hc, fun c' t hct hlt => hcon ⟨c', t, hct, hlt⟩⟩
    exact Or.inr (exists_varStep_left hc hne)

omit [Finite A] in
theorem not_varMax_of_step {x c c' : A} {s s' : Bool} (h : VarStep x c s c' s') :
    ¬VarMax x c s := fun hm => hm.2 c' s' h.2.1 h.2.2.1

omit [Finite A] in
theorem not_varMin_of_step {x c c' : A} {s s' : Bool} (h : VarStep x c s c' s') :
    ¬VarMin x c' s' := fun hm => hm.2 c s h.1 h.2.2.1

end Order

/-! ### The graph -/

section Graph

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

/-- The vertices that exist: those of variables, occurrences and clauses of
the formula, and `zero` when there is no clause. -/
def Valid : Vtx A → Prop
  | .top x => Lax366625.CountingSat.SatOccurs A x
  | .lft x => Lax366625.CountingSat.SatOccurs A x
  | .rgt x => Lax366625.CountingSat.SatOccurs A x
  | .pad0 x => Lax366625.CountingSat.SatOccurs A x
  | .ain s x c => Lax799700.Common.SatOcc.OccIn c x s
  | .bout s x c => Lax799700.Common.SatOcc.OccIn c x s
  | .pad s x c => Lax799700.Common.SatOcc.OccIn c x s
  | .cls c => Lax799700.Common.SatOcc.IsCl c
  | .zero => ¬∃ c : A, Lax799700.Common.SatOcc.IsCl c

/-- The arcs of the row graph, between vertices assumed to exist. -/
def Step : Vtx A → Vtx A → Prop
  | .lft x, .pad0 y => x = y
  | .pad0 x, .lft y => x = y
  | .pad0 x, .ain s y c => x = y ∧ VarMin x c s
  | .ain s y c, .pad0 x => x = y ∧ VarMin x c s
  | .bout s x c, .pad s' x' c' => s = s' ∧ x = x' ∧ c = c'
  | .pad s x c, .bout s' x' c' => s = s' ∧ x = x' ∧ c = c'
  | .pad s x c, .ain s' x' c' => x = x' ∧ VarStep x c s c' s'
  | .ain s' x' c', .pad s x c => x = x' ∧ VarStep x c s c' s'
  | .pad s x c, .rgt y => x = y ∧ VarMax x c s
  | .rgt y, .pad s x c => x = y ∧ VarMax x c s
  | .ain s _ c, .cls c' => s = true ∧ c = c'
  | .cls c', .bout s _ c => s = true ∧ c = c'
  | .bout s x c, .ain s' x' c' => s = true ∧ s' = true ∧ x = x' ∧ c = c'
  | .bout s _ c, .cls c' => s = false ∧ c = c'
  | .cls c', .ain s _ c => s = false ∧ c = c'
  | .ain s x c, .bout s' x' c' => s = false ∧ s' = false ∧ x = x' ∧ c = c'
  | .top x, .lft y => x = y
  | .top x, .rgt y => x = y
  | .lft x, .top y => NextVar x y
  | .rgt x, .top y => NextVar x y
  | .zero, .zero => True
  | _, _ => False

/-- The arcs of the row graph. -/
def Arc (u v : Vtx A) : Prop := Valid u ∧ Valid v ∧ Step u v

/-- **The circuit of an assignment**, as its “comes next” relation: the row of
a true variable is traversed from the left, that of a false one from the
right, and a clause vertex is visited from the occurrence of a true literal. -/
def S (ν : A → Prop) : Vtx A → Vtx A → Prop
  | .top x, v => (ν x ∧ v = .lft x) ∨ (¬ν x ∧ v = .rgt x)
  | .lft x, v => (ν x ∧ v = .pad0 x) ∨ (¬ν x ∧ ∃ y, NextVar x y ∧ v = .top y)
  | .rgt x, v => (ν x ∧ ∃ y, NextVar x y ∧ v = .top y) ∨
      (¬ν x ∧ ∃ c s, VarMax x c s ∧ v = .pad s x c)
  | .pad0 x, v => (ν x ∧ ∃ c s, VarMin x c s ∧ v = .ain s x c) ∨ (¬ν x ∧ v = .lft x)
  | .ain s x c, v =>
      (ν x ∧ ((s = true ∧ v = .cls c) ∨ (s = false ∧ v = .bout s x c))) ∨
        (¬ν x ∧ ((∃ c' s', VarStep x c' s' c s ∧ v = .pad s' x c') ∨
          (VarMin x c s ∧ v = .pad0 x)))
  | .bout s x c, v =>
      (ν x ∧ v = .pad s x c) ∨
        (¬ν x ∧ ((s = true ∧ v = .ain s x c) ∨ (s = false ∧ v = .cls c)))
  | .pad s x c, v =>
      (ν x ∧ ((∃ c' s', VarStep x c s c' s' ∧ v = .ain s' x c') ∨
          (VarMax x c s ∧ v = .rgt x))) ∨
        (¬ν x ∧ v = .bout s x c)
  | .cls c, v =>
      (∃ x, Lax799700.Common.SatOcc.OccIn c x true ∧ ν x ∧ v = .bout true x c) ∨
        (∃ x, Lax799700.Common.SatOcc.OccIn c x false ∧ ¬ν x ∧ v = .ain false x c)
  | .zero, v => v = .zero

end Graph

end HamGadget

end Lax280166Proofs.DescriptiveComplexity


