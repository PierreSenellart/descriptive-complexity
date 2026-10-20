/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Numbers.BinRel
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax822549Proofs.DescriptiveComplexity.Config
end Lax822549Proofs.DescriptiveComplexity.Config

namespace Lax822549Proofs.DescriptiveComplexity.TMData
end Lax822549Proofs.DescriptiveComplexity.TMData

namespace Lax822549Proofs.DescriptiveComplexity.TMData.Agree
end Lax822549Proofs.DescriptiveComplexity.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity.TMData.ReachesIn
end Lax822549Proofs.DescriptiveComplexity.TMData.ReachesIn

namespace Lax822549Proofs.DescriptiveComplexity.TMData.StepsIn
end Lax822549Proofs.DescriptiveComplexity.TMData.StepsIn

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd MinPos SuccPos TMData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

/-!
# Turing machines over a universe, without a vocabulary

The semantics half of the machine bridge: what it means for a nondeterministic
Turing machine, presented as *relations on a universe*, to accept. No
vocabulary appears here – `DescriptiveComplexity.Problems.Machine.Defs` supplies one and
reads these definitions off a structure – so that the reductions, which build
machines rather than read them, can reason about runs without unfolding any
`RelMap`.

## The model

A machine is `DescriptiveComplexity.TMData`: the sorts (`Posn`, `Tr`), the marks
(`Start`, `Acc`, `Blank`, `Right`), the binary attributes of a transition
(`Src`, `Read`, `Dst`, `Write`), the initial tape `Inp`, and a linear order
`Le`. Two decisions are visible in the types.

* **Transitions are elements.** A transition is an element `τ` of the universe
  with four binary attributes, rather than a 5-ary relation; every relation
  here has arity at most two, which is what keeps the defining formulas of an
  interpretation indexed by *pairs* of tags.
* **Time steps and tape cells are the same sort.** A configuration's head is a
  position, and the time bound of `DescriptiveComplexity.TMData.Accepts` is the *number*
  of positions – a unary bound by construction, with no arithmetic. A head at
  the last position moving right has no successor
  (`DescriptiveComplexity.SuccPos` fails), and the run simply stops.

A run is read in three ways, and which one a construction uses is what its
resource bound can see. `DescriptiveComplexity.TMData.StepsIn` counts exactly, so
two phases of unknown length do not compose; `Relation.ReflTransGen` composes but
carries no count, so `DescriptiveComplexity.TMData.Accepts` cannot read it; and
`DescriptiveComplexity.TMData.ReachesIn` – a run of *at most* `n` steps – does
both, composing by adding budgets and weakening upwards. A clocked program is
written with the third and a space-bounded one with its erasure, which is how the
two share their phase lemmas.

The tape is a total function `A → A`, so the semantics is total: reading a cell
never fails. Which functions count as *initial* tapes is
`DescriptiveComplexity.TMData.InitTape` – the input where it is defined, blank elsewhere –
stated as a relation so that no choice is needed and so that the first-order
kernel of the membership proof can check it literally.

## Transport

`DescriptiveComplexity.TMData.Agree` records that two machines over different universes
correspond along an equivalence, fieldwise; `DescriptiveComplexity.TMData.Agree.accepts`
transports acceptance along it. This is all the isomorphism-invariance proof of
the decision problems needs.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

/-- **Reaching one configuration from another within a budget**: some run of at
most `n` steps.

This is the form in which a program's phases are stated when the machine is on a
clock. `DescriptiveComplexity.TMData.StepsIn` counts exactly, so two phases whose
lengths are not known separately do not compose; `Relation.ReflTransGen` composes
but carries no count, and `DescriptiveComplexity.TMData.Accepts` cannot read it.
A budget is what does both: it composes by adding
(`DescriptiveComplexity.TMData.ReachesIn.trans`), it weakens upwards
(`DescriptiveComplexity.TMData.ReachesIn.mono`), so a phase may be charged more
than it spends and the arithmetic done once at the end, and it still gives the
witness `Accepts` asks for. The space-bounded reading is its erasure
(`DescriptiveComplexity.TMData.ReachesIn.reflTransGen`). -/
def ReachesIn (n : ℕ) (c c' : Lax904597.Machines.Config A) : Prop :=
  ∃ k ≤ n, M.StepsIn k c c'

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (ReachesIn)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- A run extended by one more step at its end. -/
theorem StepsIn.trans_step : ∀ {n : ℕ} {c d e : Lax904597.Machines.Config A},
    M.StepsIn n c d → M.Step d e → M.StepsIn (n + 1) c e := by
  intro n
  induction n with
  | zero => intro c d e hcd hde; exact ⟨e, by rw [show c = d from hcd]; exact hde, rfl⟩
  | succ n ih =>
    rintro c d e ⟨m, hstep, hrest⟩ hde
    exact ⟨m, hstep, ih hrest hde⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.StepsIn

export Lax822549Proofs.DescriptiveComplexity.TMData.StepsIn (trans_step)

end Lax904597.Machines.TMData.StepsIn

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **A run decomposed at its far end**: `n + 1` steps are `n` steps and then
one. `DescriptiveComplexity.TMData.StepsIn` recurses at the near end; inductions along
the *time order* – the fixed-point description of a deterministic run – need
this reading. -/
theorem stepsIn_succ_iff : ∀ {n : ℕ} {c e : Lax904597.Machines.Config A},
    M.StepsIn (n + 1) c e ↔ ∃ d, M.StepsIn n c d ∧ M.Step d e := by
  intro n
  induction n with
  | zero =>
    intro c e
    constructor
    · rintro ⟨d, hstep, hde⟩
      exact ⟨c, rfl, (show d = e from hde) ▸ hstep⟩
    · rintro ⟨d, hcd, hstep⟩
      exact ⟨e, (show c = d from hcd) ▸ hstep, rfl⟩
  | succ n ih =>
    intro c e
    constructor
    · rintro ⟨d, hstep, hrest⟩
      obtain ⟨d', h1, h2⟩ := ih.mp hrest
      exact ⟨d', ⟨d, hstep, h1⟩, h2⟩
    · rintro ⟨d', ⟨d, hstep, h1⟩, h2⟩
      exact ⟨d, hstep, ih.mpr ⟨d', h1, h2⟩⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (stepsIn_succ_iff)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **A run splits anywhere**: `m + k` steps decompose into `m` and then `k`,
through the configuration reached halfway. This is what lets two runs from the
same configuration be compared at a common time. -/
theorem stepsIn_split : ∀ {m k : ℕ} {c e : Lax904597.Machines.Config A},
    M.StepsIn (m + k) c e → ∃ d, M.StepsIn m c d ∧ M.StepsIn k d e := by
  intro m
  induction m with
  | zero =>
    intro k c e h
    rw [Nat.zero_add] at h
    exact ⟨c, rfl, h⟩
  | succ m ih =>
    intro k c e h
    rw [Nat.succ_add] at h
    obtain ⟨d, hstep, hrest⟩ := h
    obtain ⟨d', h1, h2⟩ := ih hrest
    exact ⟨d', ⟨d, hstep, h1⟩, h2⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (stepsIn_split)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **Runs compose.** Phases of a constructed machine are proved one at a time
and chained with this; the step counts add, which is the form the budget
obligation of a reduction takes. -/
theorem StepsIn.trans : ∀ {n m : ℕ} {c d e : Lax904597.Machines.Config A},
    M.StepsIn n c d → M.StepsIn m d e → M.StepsIn (n + m) c e := by
  intro n
  induction n with
  | zero =>
    intro m c d e hcd hde
    rw [show c = d from hcd, Nat.zero_add]
    exact hde
  | succ n ih =>
    rintro m c d e ⟨f, hstep, hrest⟩ hde
    rw [Nat.succ_add]
    exact ⟨f, hstep, ih hrest hde⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.StepsIn

export Lax822549Proofs.DescriptiveComplexity.TMData.StepsIn (trans)

end Lax904597.Machines.TMData.StepsIn

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **A budgeted run is a run**: the space-bounded reading of acceptance forgets
the count, so every lemma stated with `DescriptiveComplexity.TMData.StepsIn` – the
sweep primitives of `DescriptiveComplexity.Problems.Machine.Program`, in
particular – feeds straight into it. -/
theorem reflTransGen_of_stepsIn : ∀ {n : ℕ} {c d : Lax904597.Machines.Config A},
    M.StepsIn n c d → Relation.ReflTransGen M.Step c d := by
  intro n
  induction n with
  | zero => intro c d h; exact (show c = d from h) ▸ Relation.ReflTransGen.refl
  | succ n ih => rintro c d ⟨e, he, hrest⟩; exact Relation.ReflTransGen.head he (ih hrest)

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (reflTransGen_of_stepsIn)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **Every run has a length**: the converse of
`DescriptiveComplexity.TMData.reflTransGen_of_stepsIn`. A reachability claim
carries no count, but a chain of steps has one, so a phase proved without a
budget can still be handed to a caller that needs one – the count is whatever
the chain happens to be. -/
theorem exists_stepsIn_of_reflTransGen {c d : Lax904597.Machines.Config A}
    (h : Relation.ReflTransGen M.Step c d) : ∃ n : ℕ, M.StepsIn n c d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hde ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, hn.trans_step hde⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (exists_stepsIn_of_reflTransGen)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-! ### The algebra of budgets -/

/-- A run of exactly `n` steps is a run within `n`. -/
theorem StepsIn.reachesIn {n : ℕ} {c d : Lax904597.Machines.Config A} (h : M.StepsIn n c d) :
    M.ReachesIn n c d :=
  ⟨n, Nat.le_refl n, h⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.StepsIn

export Lax822549Proofs.DescriptiveComplexity.TMData.StepsIn (reachesIn)

end Lax904597.Machines.TMData.StepsIn

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **Every run has a budget**, the same fact stated for
`DescriptiveComplexity.TMData.ReachesIn`. -/
theorem exists_reachesIn_of_reflTransGen {c d : Lax904597.Machines.Config A}
    (h : Relation.ReflTransGen M.Step c d) : ∃ n : ℕ, M.ReachesIn n c d := by
  obtain ⟨n, hn⟩ := exists_stepsIn_of_reflTransGen h
  exact ⟨n, hn.reachesIn⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (exists_reachesIn_of_reflTransGen)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **A budget may be raised**, which is what makes phases of different lengths
composable: each is charged a bound it need not meet. -/
theorem ReachesIn.mono {n m : ℕ} {c d : Lax904597.Machines.Config A} (hnm : n ≤ m) (h : M.ReachesIn n c d) :
    M.ReachesIn m c d := by
  obtain ⟨k, hk, hrun⟩ := h
  exact ⟨k, hk.trans hnm, hrun⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.ReachesIn

export Lax822549Proofs.DescriptiveComplexity.TMData.ReachesIn (mono)

end Lax904597.Machines.TMData.ReachesIn

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- Standing still costs nothing. -/
theorem reachesIn_refl {n : ℕ} {c : Lax904597.Machines.Config A} : M.ReachesIn n c c :=
  ⟨0, Nat.zero_le n, rfl⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (reachesIn_refl)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- One step costs one. -/
theorem reachesIn_of_step {c d : Lax904597.Machines.Config A} (h : M.Step c d) : M.ReachesIn 1 c d :=
  ⟨1, Nat.le_refl 1, ⟨d, h, rfl⟩⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (reachesIn_of_step)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **Budgeted runs compose, and their budgets add.** This is the whole reason
for the notion: a program's cost is read off its phases as a sum, and compared
with the clock once. -/
theorem ReachesIn.trans {n m : ℕ} {c d e : Lax904597.Machines.Config A}
    (hcd : M.ReachesIn n c d) (hde : M.ReachesIn m d e) : M.ReachesIn (n + m) c e := by
  obtain ⟨k, hk, hrun⟩ := hcd
  obtain ⟨l, hl, hrun'⟩ := hde
  exact ⟨k + l, Nat.add_le_add hk hl, hrun.trans hrun'⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.ReachesIn

export Lax822549Proofs.DescriptiveComplexity.TMData.ReachesIn (trans)

end Lax904597.Machines.TMData.ReachesIn

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- A budgeted run extended by one step at its end. -/
theorem ReachesIn.tail {n : ℕ} {c d e : Lax904597.Machines.Config A} (h : M.ReachesIn n c d) (hstep : M.Step d e) :
    M.ReachesIn (n + 1) c e :=
  h.trans (reachesIn_of_step hstep)

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.ReachesIn

export Lax822549Proofs.DescriptiveComplexity.TMData.ReachesIn (tail)

end Lax904597.Machines.TMData.ReachesIn

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- A budgeted run extended by one step at its start. -/
theorem ReachesIn.head {n : ℕ} {c d e : Lax904597.Machines.Config A} (hstep : M.Step c d) (h : M.ReachesIn n d e) :
    M.ReachesIn (n + 1) c e :=
  (Nat.add_comm 1 n) ▸ (reachesIn_of_step hstep).trans h

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.ReachesIn

export Lax822549Proofs.DescriptiveComplexity.TMData.ReachesIn (head)

end Lax904597.Machines.TMData.ReachesIn

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **A budgeted run is a run.** The erasure that turns every statement of a
clocked program into the corresponding statement of a space-bounded one, which is
why the two models share their phase lemmas. -/
theorem ReachesIn.reflTransGen {n : ℕ} {c d : Lax904597.Machines.Config A} (h : M.ReachesIn n c d) :
    Relation.ReflTransGen M.Step c d := by
  obtain ⟨_, -, hrun⟩ := h
  exact reflTransGen_of_stepsIn hrun

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.ReachesIn

export Lax822549Proofs.DescriptiveComplexity.TMData.ReachesIn (reflTransGen)

end Lax904597.Machines.TMData.ReachesIn

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- **A budgeted run that ends accepting makes the machine accept**, provided the
budget is below the clock. The one place a program's arithmetic meets
`DescriptiveComplexity.TMData.Accepts`. -/
theorem accepts_of_reachesIn {n : ℕ} {c₀ c : Lax904597.Machines.Config A} (hinit : M.IsInit c₀)
    (hrun : M.ReachesIn n c₀ c) (hlt : n < Nat.card {p : A // M.Posn p})
    (hacc : M.Acc c.state) : M.Accepts := by
  obtain ⟨k, hk, hrun⟩ := hrun
  exact ⟨c₀, c, k, hinit, Nat.lt_of_le_of_lt hk hlt, hrun, hacc⟩

end Steps

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (accepts_of_reachesIn)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

end Steps

section Unique

variable {M}

/-- **A well-formed initial tape is functional**: a cell holds either its
unique input symbol or the unique blank, and the two cases exclude each
other. -/
theorem initTape_functional (hwf : M.WellFormed) {p a b : A}
    (ha : M.InitTape p a) (hb : M.InitTape p b) : a = b := by
  rcases ha with ha | ⟨hna, ha⟩ <;> rcases hb with hb | ⟨hnb, hb⟩
  · exact hwf.2.2.1 p _ _ ha hb
  · exact absurd ha (hnb _)
  · exact absurd hb (hna _)
  · exact hwf.2.2.2.2 _ _ ha hb

end Unique

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (initTape_functional)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Unique

variable {M}

/-- **A machine with one start state has at most one initial configuration**:
the start state and the lowest position are pinned, and well-formedness makes
the initial tape functional. -/
theorem isInit_unique (hwf : M.WellFormed)
    (hstart : ∀ q q', M.Start q → M.Start q' → q = q')
    {c c' : Lax904597.Machines.Config A} (h : M.IsInit c) (h' : M.IsInit c') : c = c' := by
  refine Lax904597.Machines.Config.ext (hstart _ _ h.1 h'.1) ?_ (funext fun p => ?_)
  · exact hwf.1.2.2.1 _ _ (h.2.1.2 c'.head h'.2.1.1) (h'.2.1.2 c.head h.2.1.1)
  · exact initTape_functional hwf (h.2.2 p) (h'.2.2 p)

end Unique

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (isInit_unique)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Unique

variable {M}

/-- **A well-formed machine with a start state has an initial configuration**:
put the head on the lowest position and read the tape off the input, filling
the unwritten cells with the blank. -/
theorem exists_isInit [Finite A] (hwf : M.WellFormed) {q₀ : A} (hq : M.Start q₀) :
    ∃ c₀ : Lax904597.Machines.Config A, M.IsInit c₀ ∧ c₀.state = q₀ := by
  classical
  obtain ⟨p₀, hp₀⟩ := exists_minPos hwf.1 hwf.2.1
  obtain ⟨b₀, hb₀⟩ := hwf.2.2.2.1
  refine ⟨⟨q₀, p₀, fun p => if h : ∃ a, M.Inp p a then h.choose else b₀⟩, ⟨hq, hp₀, fun p => ?_⟩,
    rfl⟩
  by_cases h : ∃ a, M.Inp p a
  · exact Or.inl (by simpa only [dif_pos h] using h.choose_spec)
  · refine Or.inr ⟨fun b hb => h ⟨b, hb⟩, ?_⟩
    simpa only [dif_neg h] using hb₀

end Unique

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (exists_isInit)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Unique

variable {M}

end Unique

/-! ### Transport along an equivalence of universes -/

section Transport

variable {B : Type}

variable {M}

/-- Two machines over different universes **agree** along an equivalence when
every relation of one is the pullback of the other's. -/
structure Agree (u : B ≃ A) (N : Lax904597.Machines.TMData B) (M : Lax904597.Machines.TMData A) : Prop where
  /-- The positions correspond. -/
  posn : ∀ b, N.Posn b ↔ M.Posn (u b)
  /-- The orders correspond. -/
  le : ∀ b b', N.Le b b' ↔ M.Le (u b) (u b')
  /-- The transitions correspond. -/
  tr : ∀ b, N.Tr b ↔ M.Tr (u b)
  /-- The start states correspond. -/
  start : ∀ b, N.Start b ↔ M.Start (u b)
  /-- The accepting states correspond. -/
  acc : ∀ b, N.Acc b ↔ M.Acc (u b)
  /-- The blanks correspond. -/
  blank : ∀ b, N.Blank b ↔ M.Blank (u b)
  /-- The directions correspond. -/
  right : ∀ b, N.Right b ↔ M.Right (u b)
  /-- The sources correspond. -/
  src : ∀ b b', N.Src b b' ↔ M.Src (u b) (u b')
  /-- The read symbols correspond. -/
  read : ∀ b b', N.Read b b' ↔ M.Read (u b) (u b')
  /-- The destinations correspond. -/
  dst : ∀ b b', N.Dst b b' ↔ M.Dst (u b) (u b')
  /-- The written symbols correspond. -/
  write : ∀ b b', N.Write b b' ↔ M.Write (u b) (u b')
  /-- The inputs correspond. -/
  inp : ∀ b b', N.Inp b b' ↔ M.Inp (u b) (u b')

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (Agree)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (acc blank dst inp le posn read right src start tr write)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Linearity of corresponding orders, in both directions. -/
theorem isLinOrd_congr (u : B ≃ A) {LeB : B → B → Prop} {LeA : A → A → Prop}
    (hle : ∀ b b', LeB b b' ↔ LeA (u b) (u b')) : Lax904597.Machines.IsLinOrd LeB ↔ Lax904597.Machines.IsLinOrd LeA :=
  ⟨IsLinOrd.of_equiv u hle, IsLinOrd.of_equiv u.symm fun a a' => by
    rw [hle, Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (isLinOrd_congr)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Transport of a configuration along an equivalence. -/
def _root_.Lax822549Proofs.DescriptiveComplexity.Config.map (u : B ≃ A) (c : Lax904597.Machines.Config B) : Lax904597.Machines.Config A where
  state := u c.state
  head := u c.head
  tape := fun p => u (c.tape (u.symm p))

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.Config

export Lax822549Proofs.DescriptiveComplexity.Config (map)

end Lax904597.Machines.Config

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

@[simp] theorem _root_.Lax822549Proofs.DescriptiveComplexity.Config.map_state (u : B ≃ A) (c : Lax904597.Machines.Config B) :
    (c.map u).state = u c.state := rfl

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.Config

export Lax822549Proofs.DescriptiveComplexity.Config (map_state)

end Lax904597.Machines.Config

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

@[simp] theorem _root_.Lax822549Proofs.DescriptiveComplexity.Config.map_head (u : B ≃ A) (c : Lax904597.Machines.Config B) :
    (c.map u).head = u c.head := rfl

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.Config

export Lax822549Proofs.DescriptiveComplexity.Config (map_head)

end Lax904597.Machines.Config

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

@[simp] theorem _root_.Lax822549Proofs.DescriptiveComplexity.Config.map_tape (u : B ≃ A) (c : Lax904597.Machines.Config B) (p : A) :
    (c.map u).tape p = u (c.tape (u.symm p)) := rfl

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.Config

export Lax822549Proofs.DescriptiveComplexity.Config (map_tape)

end Lax904597.Machines.Config

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Every configuration over `A` is the transport of one over `B`. -/
theorem _root_.Lax822549Proofs.DescriptiveComplexity.Config.map_surjective (u : B ≃ A) :
    Function.Surjective (Config.map u) := by
  intro c
  exact ⟨⟨u.symm c.state, u.symm c.head, fun b => u.symm (c.tape (u b))⟩, by
    simp [Config.map, Equiv.apply_symm_apply]⟩

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.Config

export Lax822549Proofs.DescriptiveComplexity.Config (map_surjective)

end Lax904597.Machines.Config

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem _root_.Lax822549Proofs.DescriptiveComplexity.Config.map_injective (u : B ≃ A) :
    Function.Injective (Config.map u) := by
  rintro ⟨s, hd, t⟩ ⟨s', hd', t'⟩ hc
  simp only [Config.map, Lax904597.Machines.Config.mk.injEq] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have ht : t = t' := funext fun b => u.injective (by simpa using congrFun h3 (u b))
  simp [u.injective h1, u.injective h2, ht]

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.Config

export Lax822549Proofs.DescriptiveComplexity.Config (map_injective)

end Lax904597.Machines.Config

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.minPos (h : Agree u N M) {b : B} :
    Lax904597.Machines.MinPos N.Le N.Posn b ↔ Lax904597.Machines.MinPos M.Le M.Posn (u b) := by
  refine and_congr (h.posn b) ⟨fun hm a ha => ?_, fun hm a ha => ?_⟩
  · have := hm (u.symm a) ((h.posn _).mpr (by rwa [Equiv.apply_symm_apply]))
    rwa [(h.le _ _), Equiv.apply_symm_apply] at this
  · exact (h.le _ _).mpr (hm (u a) ((h.posn a).mp ha))

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (minPos)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.succPos (h : Agree u N M) {b b' : B} :
    Lax904597.Machines.SuccPos N.Le N.Posn b b' ↔ Lax904597.Machines.SuccPos M.Le M.Posn (u b) (u b') := by
  refine and_congr (h.posn b) (and_congr (h.posn b') (and_congr (h.le _ _)
    (and_congr u.injective.ne_iff.symm ⟨fun hs a ha h₁ h₂ => ?_, fun hs a ha h₁ h₂ => ?_⟩)))
  · have := hs (u.symm a) ((h.posn _).mpr (by rwa [Equiv.apply_symm_apply]))
      ((h.le _ _).mpr (by rwa [Equiv.apply_symm_apply]))
      ((h.le _ _).mpr (by rwa [Equiv.apply_symm_apply]))
    rcases this with h' | h' <;> [left; right] <;>
      exact u.symm_apply_eq.mp h'
  · rcases hs (u a) ((h.posn a).mp ha) ((h.le _ _).mp h₁) ((h.le _ _).mp h₂) with h' | h' <;>
      [left; right] <;> exact u.injective h'

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (succPos)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.initTape (h : Agree u N M) {b b' : B} :
    N.InitTape b b' ↔ M.InitTape (u b) (u b') := by
  refine or_congr (h.inp _ _) (and_congr ⟨fun hn a ha => ?_, fun hn a ha => ?_⟩ (h.blank _))
  · exact hn (u.symm a) ((h.inp _ _).mpr (by rwa [Equiv.apply_symm_apply]))
  · exact hn (u a) ((h.inp _ _).mp ha)

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (initTape)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.isInit (h : Agree u N M) {c : Lax904597.Machines.Config B} :
    N.IsInit c ↔ M.IsInit (c.map u) := by
  refine and_congr (h.start _) (and_congr h.minPos ⟨fun hi p => ?_, fun hi b => ?_⟩)
  · have := (h.initTape (u := u)).mp (hi (u.symm p))
    rwa [Equiv.apply_symm_apply] at this
  · exact (h.initTape (u := u)).mpr (by simpa using hi (u b))

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (isInit)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.step (h : Agree u N M) {c c' : Lax904597.Machines.Config B} :
    N.Step c c' ↔ M.Step (c.map u) (c'.map u) := by
  constructor
  · rintro ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩
    refine ⟨u τ, (h.tr _).mp hτ, (h.src _ _).mp hsrc, ?_, (h.dst _ _).mp hdst, ?_, ?_, ?_⟩
    · simpa using (h.read _ _).mp hread
    · simpa using (h.write _ _).mp hwrite
    · intro p hp
      have hb : u.symm p ≠ c.head := fun hcon => hp (by simp [← hcon])
      simpa using congrArg u (hframe (u.symm p) hb)
    · rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨(h.right _).mp hr, h.succPos.mp hs⟩
      · exact Or.inr ⟨fun hcon => hr ((h.right _).mpr hcon), h.succPos.mp hs⟩
  · rintro ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩
    refine ⟨u.symm τ, (h.tr _).mpr (by rwa [Equiv.apply_symm_apply]),
      (h.src _ _).mpr (by rwa [Equiv.apply_symm_apply]), ?_,
      (h.dst _ _).mpr (by rwa [Equiv.apply_symm_apply]), ?_, ?_, ?_⟩
    · refine (h.read _ _).mpr ?_
      rw [Equiv.apply_symm_apply]
      simpa [Config.map] using hread
    · refine (h.write _ _).mpr ?_
      rw [Equiv.apply_symm_apply]
      simpa [Config.map] using hwrite
    · intro p hp
      exact u.injective (by simpa [Config.map] using hframe (u p) (u.injective.ne_iff.mpr hp))
    · rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨(h.right _).mpr (by rwa [Equiv.apply_symm_apply]), h.succPos.mpr hs⟩
      · refine Or.inr ⟨fun hcon => hr ?_, h.succPos.mpr hs⟩
        rw [← Equiv.apply_symm_apply u τ]
        exact (h.right _).mp hcon

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (step)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.stepsIn (h : Agree u N M) :
    ∀ (n : ℕ) (c c' : Lax904597.Machines.Config B), N.StepsIn n c c' ↔ M.StepsIn n (c.map u) (c'.map u) := by
  intro n
  induction n with
  | zero =>
    intro c c'
    change c = c' ↔ Config.map u c = Config.map u c'
    exact ⟨congrArg (Config.map u), fun hc => Config.map_injective u hc⟩
  | succ n ih =>
    intro c c'
    constructor
    · rintro ⟨d, hstep, hrest⟩
      exact ⟨d.map u, h.step.mp hstep, (ih d c').mp hrest⟩
    · rintro ⟨d, hstep, hrest⟩
      obtain ⟨d₀, rfl⟩ := Config.map_surjective u d
      exact ⟨d₀, h.step.mpr hstep, (ih d₀ c').mpr hrest⟩

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (stepsIn)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- **Acceptance transports along an equivalence.** -/
theorem Agree.accepts (h : Agree u N M) : N.Accepts ↔ M.Accepts := by
  have hcard : Nat.card {b : B // N.Posn b} = Nat.card {a : A // M.Posn a} :=
    Nat.card_congr (u.subtypeEquiv fun b => h.posn b)
  constructor
  · rintro ⟨c₀, c, n, hinit, hle, hrun, hacc⟩
    exact ⟨c₀.map u, c.map u, n, h.isInit.mp hinit, hcard ▸ hle,
      (h.stepsIn n c₀ c).mp hrun, (h.acc _).mp hacc⟩
  · rintro ⟨c₀, c, n, hinit, hle, hrun, hacc⟩
    obtain ⟨d₀, rfl⟩ := Config.map_surjective u c₀
    obtain ⟨d, rfl⟩ := Config.map_surjective u c
    exact ⟨d₀, d, n, h.isInit.mpr hinit, hcard ▸ hle,
      (h.stepsIn n d₀ d).mpr hrun, (h.acc _).mpr hacc⟩

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (accepts)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Reachability in the configuration graph transports along an equivalence. -/
theorem Agree.reach (h : Agree u N M) (c c' : Lax904597.Machines.Config B) :
    Relation.ReflTransGen N.Step c c' ↔ Relation.ReflTransGen M.Step (c.map u) (c'.map u) := by
  constructor
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail d e _ hde ih => exact ih.tail (h.step.mp hde)
  · intro hr
    have key : ∀ x y : Lax904597.Machines.Config A, Relation.ReflTransGen M.Step x y →
        ∀ d e : Lax904597.Machines.Config B, x = d.map u → y = e.map u → Relation.ReflTransGen N.Step d e := by
      intro x y hxy
      induction hxy with
      | refl =>
        intro d e hd he
        exact (Config.map_injective u (hd.symm.trans he)) ▸ Relation.ReflTransGen.refl
      | @tail p q _ hpq ih =>
        intro d e hd he
        obtain ⟨p₀, rfl⟩ := Config.map_surjective u p
        exact (ih d p₀ hd rfl).tail (h.step.mpr (he ▸ hpq))
    exact key _ _ hr c c' rfl rfl

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (reach)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- **Acceptance in bounded space transports along an equivalence.** -/
theorem Agree.acceptsSpace (h : Agree u N M) : N.AcceptsSpace ↔ M.AcceptsSpace := by
  constructor
  · rintro ⟨c₀, c, hinit, hreach, hacc⟩
    exact ⟨c₀.map u, c.map u, h.isInit.mp hinit, (h.reach c₀ c).mp hreach, (h.acc _).mp hacc⟩
  · rintro ⟨c₀, c, hinit, hreach, hacc⟩
    obtain ⟨d₀, rfl⟩ := Config.map_surjective u c₀
    obtain ⟨d, rfl⟩ := Config.map_surjective u c
    exact ⟨d₀, d, h.isInit.mpr hinit, (h.reach d₀ d).mpr hreach, (h.acc _).mpr hacc⟩

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (acceptsSpace)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- **Determinism transports along an equivalence.** -/
theorem Agree.deterministic (h : Agree u N M) : N.Deterministic ↔ M.Deterministic := by
  have hstart : (∀ q q', N.Start q → N.Start q' → q = q') ↔
      ∀ q q', M.Start q → M.Start q' → q = q' :=
    ⟨fun hf q q' hq hq' => by
      simpa using congrArg u (hf (u.symm q) (u.symm q')
        ((h.start _).mpr (by rwa [Equiv.apply_symm_apply]))
        ((h.start _).mpr (by rwa [Equiv.apply_symm_apply]))),
      fun hf q q' hq hq' =>
        u.injective (hf (u q) (u q') ((h.start q).mp hq) ((h.start q').mp hq'))⟩
  have huniq : (∀ τ τ' q a, N.Tr τ → N.Tr τ' → N.Src τ q → N.Src τ' q →
        N.Read τ a → N.Read τ' a → τ = τ') ↔
      ∀ τ τ' q a, M.Tr τ → M.Tr τ' → M.Src τ q → M.Src τ' q →
        M.Read τ a → M.Read τ' a → τ = τ' :=
    ⟨fun hf τ τ' q a h1 h2 h3 h4 h5 h6 => by
      simpa using congrArg u (hf (u.symm τ) (u.symm τ') (u.symm q) (u.symm a)
        ((h.tr _).mpr (by rwa [Equiv.apply_symm_apply]))
        ((h.tr _).mpr (by rwa [Equiv.apply_symm_apply]))
        ((h.src _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
        ((h.src _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
        ((h.read _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
        ((h.read _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))),
      fun hf τ τ' q a h1 h2 h3 h4 h5 h6 =>
        u.injective (hf (u τ) (u τ') (u q) (u a) ((h.tr _).mp h1) ((h.tr _).mp h2)
          ((h.src _ _).mp h3) ((h.src _ _).mp h4) ((h.read _ _).mp h5) ((h.read _ _).mp h6))⟩
  have hdst : (∀ τ q q', N.Dst τ q → N.Dst τ q' → q = q') ↔
      ∀ τ q q', M.Dst τ q → M.Dst τ q' → q = q' :=
    ⟨fun hf τ q q' h1 h2 => by
      simpa using congrArg u (hf (u.symm τ) (u.symm q) (u.symm q')
        ((h.dst _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
        ((h.dst _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))),
      fun hf τ q q' h1 h2 =>
        u.injective (hf (u τ) (u q) (u q') ((h.dst _ _).mp h1) ((h.dst _ _).mp h2))⟩
  have hwrite : (∀ τ a a', N.Write τ a → N.Write τ a' → a = a') ↔
      ∀ τ a a', M.Write τ a → M.Write τ a' → a = a' :=
    ⟨fun hf τ a a' h1 h2 => by
      simpa using congrArg u (hf (u.symm τ) (u.symm a) (u.symm a')
        ((h.write _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
        ((h.write _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))),
      fun hf τ a a' h1 h2 =>
        u.injective (hf (u τ) (u a) (u a') ((h.write _ _).mp h1) ((h.write _ _).mp h2))⟩
  exact and_congr hstart (and_congr huniq (and_congr hdst hwrite))

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (deterministic)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- **Well-formedness transports along an equivalence.** -/
theorem Agree.wellFormed (h : Agree u N M) : N.WellFormed ↔ M.WellFormed := by
  have hinp : ∀ p a : A, M.Inp p a ↔ N.Inp (u.symm p) (u.symm a) := by
    intro p a; rw [h.inp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hblank : ∀ a : A, M.Blank a ↔ N.Blank (u.symm a) := by
    intro a; rw [h.blank, Equiv.apply_symm_apply]
  refine and_congr (isLinOrd_congr u fun b b' => h.le b b')
    (and_congr ⟨fun ⟨p, hp⟩ => ⟨u p, (h.posn p).mp hp⟩,
        fun ⟨p, hp⟩ => ⟨u.symm p, (h.posn _).mpr (by rwa [Equiv.apply_symm_apply])⟩⟩
      (and_congr ⟨fun hf p a b ha hb => ?_, fun hf p a b ha hb => ?_⟩
        (and_congr ⟨fun ⟨b, hb⟩ => ⟨u b, (h.blank b).mp hb⟩,
            fun ⟨b, hb⟩ => ⟨u.symm b, (h.blank _).mpr (by rwa [Equiv.apply_symm_apply])⟩⟩
          ⟨fun hb x y hx hy => ?_, fun hb x y hx hy => ?_⟩)))
  · exact u.symm.injective
      (hf (u.symm p) (u.symm a) (u.symm b) ((hinp p a).mp ha) ((hinp p b).mp hb))
  · exact u.injective (hf (u p) (u a) (u b) ((h.inp _ _).mp ha) ((h.inp _ _).mp hb))
  · exact u.symm.injective (hb (u.symm x) (u.symm y) ((hblank x).mp hx) ((hblank y).mp hy))
  · exact u.injective (hb (u x) (u y) ((h.blank _).mp hx) ((h.blank _).mp hy))

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax822549Proofs.DescriptiveComplexity.TMData.Agree (wellFormed)

end Lax904597.Machines.TMData.Agree

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

end Transport

end TMData

end Lax822549Proofs.DescriptiveComplexity


