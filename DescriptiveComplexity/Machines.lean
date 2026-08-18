/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel

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
`Le`. Two decisions from the plan are visible in the types.

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
correspond along an equivalence, fieldwise; `DescriptiveComplexity.TMData.accepts_congr`
transports acceptance along it. This is all the isomorphism-invariance proof of
the decision problems needs.
-/

namespace DescriptiveComplexity

/-- A configuration: the current state, the position of the head, and the
contents of the tape. -/
@[ext]
structure Config (A : Type) where
  /-- The current state. -/
  state : A
  /-- The cell the head is on. -/
  head : A
  /-- The symbol in each cell. -/
  tape : A → A

/-- A Turing machine presented as relations on a universe: the sorts, the
marks, the attributes of the transitions, the initial tape and the order along
which the head moves. -/
structure TMData (A : Type) where
  /-- Being a position – a tape cell, and equally a time step. -/
  Posn : A → Prop
  /-- The order on positions, along which the head moves. -/
  Le : A → A → Prop
  /-- Being a transition. -/
  Tr : A → Prop
  /-- Being a start state. -/
  Start : A → Prop
  /-- Being an accepting state. -/
  Acc : A → Prop
  /-- Being the blank symbol. -/
  Blank : A → Prop
  /-- This transition moves the head right (rather than left). -/
  Right : A → Prop
  /-- The state a transition applies in. -/
  Src : A → A → Prop
  /-- The symbol a transition reads. -/
  Read : A → A → Prop
  /-- The state a transition moves to. -/
  Dst : A → A → Prop
  /-- The symbol a transition writes. -/
  Write : A → A → Prop
  /-- The input: the symbol initially in a cell. -/
  Inp : A → A → Prop

namespace TMData

variable {A : Type} (M : TMData A)

/-- The symbols a cell may initially hold: the input symbol where the input is
defined, the blank elsewhere. -/
def InitTape (p a : A) : Prop := M.Inp p a ∨ ((∀ b, ¬ M.Inp p b) ∧ M.Blank a)

/-- Being an initial configuration: a start state, the head on the lowest
position, and an initial tape. -/
def IsInit (c : Config A) : Prop :=
  M.Start c.state ∧ MinPos M.Le M.Posn c.head ∧ ∀ p, M.InitTape p (c.tape p)

/-- **One step.** Some transition applies in the current state to the symbol
under the head: it writes in that cell, changes state, and moves the head to
the neighbouring position in the direction it names. Cells other than the one
under the head are unchanged, and a move off the end of the tape is impossible
– there being no such neighbour, no step is available and the run stops. -/
def Step (c c' : Config A) : Prop :=
  ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
    M.Dst τ c'.state ∧ M.Write τ (c'.tape c.head) ∧
    (∀ p, p ≠ c.head → c'.tape p = c.tape p) ∧
    ((M.Right τ ∧ SuccPos M.Le M.Posn c.head c'.head) ∨
      (¬ M.Right τ ∧ SuccPos M.Le M.Posn c'.head c.head))

/-- Reaching one configuration from another in exactly `n` steps. -/
def StepsIn : ℕ → Config A → Config A → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ d, M.Step c d ∧ StepsIn n d c'

/-- **Acceptance**: some run from an initial configuration reaches an accepting
state within as many steps as there are positions.

The bound is unary by construction – it counts elements of the universe – which
is what makes this an NP problem rather than an NEXP one, with no arithmetic
anywhere. A reduction buys itself `|Tag| · nᵈ` steps by choosing the dimension
`d` of its interpretation.

The bound is *strict* because the positions index the time points of the run:
`N` of them leave `N - 1` steps between them, which is what makes
`DescriptiveComplexity.TMData.accepts_iff_exists_walk` an equivalence on the nose. -/
def Accepts : Prop :=
  ∃ (c₀ c : Config A) (n : ℕ), M.IsInit c₀ ∧ n < Nat.card {p : A // M.Posn p} ∧
    M.StepsIn n c₀ c ∧ M.Acc c.state

/-- **Acceptance in bounded space**: some run from an initial configuration
reaches an accepting state, with *no bound on its length*.

This is `DescriptiveComplexity.TMData.Accepts` with the step bound dropped, and
that is all the difference between the time-bounded and the space-bounded model:
the space is already bounded by construction, since the tape is indexed by the
positions and a reduction of dimension `d` therefore buys `nᵈ` cells exactly as
it buys `nᵈ` steps. What changes is that a run no longer fits inside the
structure – it may visit exponentially many configurations – so acceptance is
*reachability* in the configuration graph rather than a walk indexed by the
positions, which is why the membership proof for the space-bounded problems is
an SO(TC) specification rather than a `Σ₁` definition. -/
def AcceptsSpace : Prop :=
  ∃ c₀ c : Config A, M.IsInit c₀ ∧ Relation.ReflTransGen M.Step c₀ c ∧ M.Acc c.state

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
def ReachesIn (n : ℕ) (c c' : Config A) : Prop :=
  ∃ k ≤ n, M.StepsIn k c c'

section Steps

variable {M}

/-- A run extended by one more step at its end. -/
theorem StepsIn.trans_step : ∀ {n : ℕ} {c d e : Config A},
    M.StepsIn n c d → M.Step d e → M.StepsIn (n + 1) c e := by
  intro n
  induction n with
  | zero => intro c d e hcd hde; exact ⟨e, by rw [show c = d from hcd]; exact hde, rfl⟩
  | succ n ih =>
    rintro c d e ⟨m, hstep, hrest⟩ hde
    exact ⟨m, hstep, ih hrest hde⟩

/-- **A run decomposed at its far end**: `n + 1` steps are `n` steps and then
one. `DescriptiveComplexity.TMData.StepsIn` recurses at the near end; inductions along
the *time order* – the fixed-point description of a deterministic run – need
this reading. -/
theorem stepsIn_succ_iff : ∀ {n : ℕ} {c e : Config A},
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

/-- **A run splits anywhere**: `m + k` steps decompose into `m` and then `k`,
through the configuration reached halfway. This is what lets two runs from the
same configuration be compared at a common time. -/
theorem stepsIn_split : ∀ {m k : ℕ} {c e : Config A},
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

/-- **Runs compose.** Phases of a constructed machine are proved one at a time
and chained with this; the step counts add, which is the form the budget
obligation of a reduction takes. -/
theorem StepsIn.trans : ∀ {n m : ℕ} {c d e : Config A},
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

/-- **A budgeted run is a run**: the space-bounded reading of acceptance forgets
the count, so every lemma stated with `DescriptiveComplexity.TMData.StepsIn` – the
sweep primitives of `DescriptiveComplexity.Problems.Machine.Program`, in
particular – feeds straight into it. -/
theorem reflTransGen_of_stepsIn : ∀ {n : ℕ} {c d : Config A},
    M.StepsIn n c d → Relation.ReflTransGen M.Step c d := by
  intro n
  induction n with
  | zero => intro c d h; exact (show c = d from h) ▸ Relation.ReflTransGen.refl
  | succ n ih => rintro c d ⟨e, he, hrest⟩; exact Relation.ReflTransGen.head he (ih hrest)

/-- **Every run has a length**: the converse of
`DescriptiveComplexity.TMData.reflTransGen_of_stepsIn`. A reachability claim
carries no count, but a chain of steps has one, so a phase proved without a
budget can still be handed to a caller that needs one – the count is whatever
the chain happens to be. -/
theorem exists_stepsIn_of_reflTransGen {c d : Config A}
    (h : Relation.ReflTransGen M.Step c d) : ∃ n : ℕ, M.StepsIn n c d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hde ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, hn.trans_step hde⟩

/-! ### The algebra of budgets -/

/-- A run of exactly `n` steps is a run within `n`. -/
theorem StepsIn.reachesIn {n : ℕ} {c d : Config A} (h : M.StepsIn n c d) :
    M.ReachesIn n c d :=
  ⟨n, Nat.le_refl n, h⟩

/-- **Every run has a budget**, the same fact stated for
`DescriptiveComplexity.TMData.ReachesIn`. -/
theorem exists_reachesIn_of_reflTransGen {c d : Config A}
    (h : Relation.ReflTransGen M.Step c d) : ∃ n : ℕ, M.ReachesIn n c d := by
  obtain ⟨n, hn⟩ := exists_stepsIn_of_reflTransGen h
  exact ⟨n, hn.reachesIn⟩

/-- **A budget may be raised**, which is what makes phases of different lengths
composable: each is charged a bound it need not meet. -/
theorem ReachesIn.mono {n m : ℕ} {c d : Config A} (hnm : n ≤ m) (h : M.ReachesIn n c d) :
    M.ReachesIn m c d := by
  obtain ⟨k, hk, hrun⟩ := h
  exact ⟨k, hk.trans hnm, hrun⟩

/-- Standing still costs nothing. -/
theorem reachesIn_refl {n : ℕ} {c : Config A} : M.ReachesIn n c c :=
  ⟨0, Nat.zero_le n, rfl⟩

/-- One step costs one. -/
theorem reachesIn_of_step {c d : Config A} (h : M.Step c d) : M.ReachesIn 1 c d :=
  ⟨1, Nat.le_refl 1, ⟨d, h, rfl⟩⟩

/-- **Budgeted runs compose, and their budgets add.** This is the whole reason
for the notion: a program's cost is read off its phases as a sum, and compared
with the clock once. -/
theorem ReachesIn.trans {n m : ℕ} {c d e : Config A}
    (hcd : M.ReachesIn n c d) (hde : M.ReachesIn m d e) : M.ReachesIn (n + m) c e := by
  obtain ⟨k, hk, hrun⟩ := hcd
  obtain ⟨l, hl, hrun'⟩ := hde
  exact ⟨k + l, Nat.add_le_add hk hl, hrun.trans hrun'⟩

/-- A budgeted run extended by one step at its end. -/
theorem ReachesIn.tail {n : ℕ} {c d e : Config A} (h : M.ReachesIn n c d) (hstep : M.Step d e) :
    M.ReachesIn (n + 1) c e :=
  h.trans (reachesIn_of_step hstep)

/-- A budgeted run extended by one step at its start. -/
theorem ReachesIn.head {n : ℕ} {c d e : Config A} (hstep : M.Step c d) (h : M.ReachesIn n d e) :
    M.ReachesIn (n + 1) c e :=
  (Nat.add_comm 1 n) ▸ (reachesIn_of_step hstep).trans h

/-- **Five legs, added up**: two runs of the same length with a step before,
between and after them. This is the shape a program's opening has – enter, a
sweep, turn round, a sweep, enter the next phase – and the addition is all there
is to its cost. -/
theorem reachesIn_five {n : ℕ} {c₀ c₁ c₂ c₃ c₄ c₅ : Config A}
    (h₁ : M.Step c₀ c₁) (h₂ : M.ReachesIn n c₁ c₂) (h₃ : M.Step c₂ c₃)
    (h₄ : M.ReachesIn n c₃ c₄) (h₅ : M.Step c₄ c₅) :
    M.ReachesIn (2 * n + 3) c₀ c₅ :=
  (((reachesIn_of_step h₁).trans h₂).trans
    ((reachesIn_of_step h₃).trans
      (h₄.trans (reachesIn_of_step h₅)))).mono (by omega)

/-- **A budgeted run is a run.** The erasure that turns every statement of a
clocked program into the corresponding statement of a space-bounded one, which is
why the two models share their phase lemmas. -/
theorem ReachesIn.reflTransGen {n : ℕ} {c d : Config A} (h : M.ReachesIn n c d) :
    Relation.ReflTransGen M.Step c d := by
  obtain ⟨_, -, hrun⟩ := h
  exact reflTransGen_of_stepsIn hrun

/-- **A budgeted run that ends accepting makes the machine accept**, provided the
budget is below the clock. The one place a program's arithmetic meets
`DescriptiveComplexity.TMData.Accepts`. -/
theorem accepts_of_reachesIn {n : ℕ} {c₀ c : Config A} (hinit : M.IsInit c₀)
    (hrun : M.ReachesIn n c₀ c) (hlt : n < Nat.card {p : A // M.Posn p})
    (hacc : M.Acc c.state) : M.Accepts := by
  obtain ⟨k, hk, hrun⟩ := hrun
  exact ⟨c₀, c, k, hinit, Nat.lt_of_le_of_lt hk hlt, hrun, hacc⟩

end Steps

/-- **Well-formedness**, folded into the yes-instances in the style of
`DescriptiveComplexity.IsLinOrd` for Knapsack: the order is linear, there is a position
to start on, the input is functional, and there is exactly one blank symbol.
Every conjunct is first-order, so the `Σ₁` kernel can check it. -/
def WellFormed : Prop :=
  IsLinOrd M.Le ∧ (∃ p, M.Posn p) ∧
    (∀ p a b, M.Inp p a → M.Inp p b → a = b) ∧
    (∃ b, M.Blank b) ∧ (∀ a b, M.Blank a → M.Blank b → a = b)

/-- **Determinism**, folded into the yes-instances of
`DescriptiveComplexity.DTMAccept`: one start state, at most one transition applicable
in a given state on a given symbol, and at most one destination and written
symbol per transition. Together with well-formedness this leaves at most one
step from any configuration (`DescriptiveComplexity.TMData.step_functional`) and at
most one initial configuration (`DescriptiveComplexity.TMData.isInit_unique`), so the
run is unique – the shape a least fixed point can compute. Every conjunct is
first-order. -/
def Deterministic : Prop :=
  (∀ q q', M.Start q → M.Start q' → q = q') ∧
    (∀ τ τ' q a, M.Tr τ → M.Tr τ' → M.Src τ q → M.Src τ' q → M.Read τ a → M.Read τ' a →
      τ = τ') ∧
    (∀ τ q q', M.Dst τ q → M.Dst τ q' → q = q') ∧
    ∀ τ a a', M.Write τ a → M.Write τ a' → a = a'

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

/-- **A machine with one start state has at most one initial configuration**:
the start state and the lowest position are pinned, and well-formedness makes
the initial tape functional. -/
theorem isInit_unique (hwf : M.WellFormed)
    (hstart : ∀ q q', M.Start q → M.Start q' → q = q')
    {c c' : Config A} (h : M.IsInit c) (h' : M.IsInit c') : c = c' := by
  refine Config.ext (hstart _ _ h.1 h'.1) ?_ (funext fun p => ?_)
  · exact hwf.1.2.2.1 _ _ (h.2.1.2 c'.head h'.2.1.1) (h'.2.1.2 c.head h.2.1.1)
  · exact initTape_functional hwf (h.2.2 p) (h'.2.2 p)

/-- **A well-formed machine with a start state has an initial configuration**:
put the head on the lowest position and read the tape off the input, filling
the unwritten cells with the blank. -/
theorem exists_isInit [Finite A] (hwf : M.WellFormed) {q₀ : A} (hq : M.Start q₀) :
    ∃ c₀ : Config A, M.IsInit c₀ ∧ c₀.state = q₀ := by
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

/-! ### Transport along an equivalence of universes -/

section Transport

variable {B : Type}

/- The transport lemmas take the machines implicitly, so that `Agree` field
notation applies their remaining arguments in the expected order. -/
variable {M}

/-- Two machines over different universes **agree** along an equivalence when
every relation of one is the pullback of the other's. -/
structure Agree (u : B ≃ A) (N : TMData B) (M : TMData A) : Prop where
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

variable {u : B ≃ A} {N : TMData B}

/-- Linearity of corresponding orders, in both directions. -/
private theorem isLinOrd_congr (u : B ≃ A) {LeB : B → B → Prop} {LeA : A → A → Prop}
    (hle : ∀ b b', LeB b b' ↔ LeA (u b) (u b')) : IsLinOrd LeB ↔ IsLinOrd LeA :=
  ⟨IsLinOrd.of_equiv u hle, IsLinOrd.of_equiv u.symm fun a a' => by
    rw [hle, Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩

/-- Transport of a configuration along an equivalence. -/
def _root_.DescriptiveComplexity.Config.map (u : B ≃ A) (c : Config B) : Config A where
  state := u c.state
  head := u c.head
  tape := fun p => u (c.tape (u.symm p))

@[simp] theorem _root_.DescriptiveComplexity.Config.map_state (u : B ≃ A) (c : Config B) :
    (c.map u).state = u c.state := rfl

@[simp] theorem _root_.DescriptiveComplexity.Config.map_head (u : B ≃ A) (c : Config B) :
    (c.map u).head = u c.head := rfl

@[simp] theorem _root_.DescriptiveComplexity.Config.map_tape (u : B ≃ A) (c : Config B) (p : A) :
    (c.map u).tape p = u (c.tape (u.symm p)) := rfl

/-- Every configuration over `A` is the transport of one over `B`. -/
theorem _root_.DescriptiveComplexity.Config.map_surjective (u : B ≃ A) :
    Function.Surjective (Config.map u) := by
  intro c
  exact ⟨⟨u.symm c.state, u.symm c.head, fun b => u.symm (c.tape (u b))⟩, by
    simp [Config.map, Equiv.apply_symm_apply]⟩

theorem _root_.DescriptiveComplexity.Config.map_injective (u : B ≃ A) :
    Function.Injective (Config.map u) := by
  rintro ⟨s, hd, t⟩ ⟨s', hd', t'⟩ hc
  simp only [Config.map, Config.mk.injEq] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have ht : t = t' := funext fun b => u.injective (by simpa using congrFun h3 (u b))
  simp [u.injective h1, u.injective h2, ht]

theorem Agree.minPos (h : Agree u N M) {b : B} :
    MinPos N.Le N.Posn b ↔ MinPos M.Le M.Posn (u b) := by
  refine and_congr (h.posn b) ⟨fun hm a ha => ?_, fun hm a ha => ?_⟩
  · have := hm (u.symm a) ((h.posn _).mpr (by rwa [Equiv.apply_symm_apply]))
    rwa [(h.le _ _), Equiv.apply_symm_apply] at this
  · exact (h.le _ _).mpr (hm (u a) ((h.posn a).mp ha))

theorem Agree.succPos (h : Agree u N M) {b b' : B} :
    SuccPos N.Le N.Posn b b' ↔ SuccPos M.Le M.Posn (u b) (u b') := by
  refine and_congr (h.posn b) (and_congr (h.posn b') (and_congr (h.le _ _)
    (and_congr u.injective.ne_iff.symm ⟨fun hs a ha h₁ h₂ => ?_, fun hs a ha h₁ h₂ => ?_⟩)))
  · have := hs (u.symm a) ((h.posn _).mpr (by rwa [Equiv.apply_symm_apply]))
      ((h.le _ _).mpr (by rwa [Equiv.apply_symm_apply]))
      ((h.le _ _).mpr (by rwa [Equiv.apply_symm_apply]))
    rcases this with h' | h' <;> [left; right] <;>
      exact u.symm_apply_eq.mp h'
  · rcases hs (u a) ((h.posn a).mp ha) ((h.le _ _).mp h₁) ((h.le _ _).mp h₂) with h' | h' <;>
      [left; right] <;> exact u.injective h'

theorem Agree.initTape (h : Agree u N M) {b b' : B} :
    N.InitTape b b' ↔ M.InitTape (u b) (u b') := by
  refine or_congr (h.inp _ _) (and_congr ⟨fun hn a ha => ?_, fun hn a ha => ?_⟩ (h.blank _))
  · exact hn (u.symm a) ((h.inp _ _).mpr (by rwa [Equiv.apply_symm_apply]))
  · exact hn (u a) ((h.inp _ _).mp ha)

theorem Agree.isInit (h : Agree u N M) {c : Config B} :
    N.IsInit c ↔ M.IsInit (c.map u) := by
  refine and_congr (h.start _) (and_congr h.minPos ⟨fun hi p => ?_, fun hi b => ?_⟩)
  · have := (h.initTape (u := u)).mp (hi (u.symm p))
    rwa [Equiv.apply_symm_apply] at this
  · exact (h.initTape (u := u)).mpr (by simpa using hi (u b))

theorem Agree.step (h : Agree u N M) {c c' : Config B} :
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

theorem Agree.stepsIn (h : Agree u N M) :
    ∀ (n : ℕ) (c c' : Config B), N.StepsIn n c c' ↔ M.StepsIn n (c.map u) (c'.map u) := by
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

/-- Reachability in the configuration graph transports along an equivalence. -/
theorem Agree.reach (h : Agree u N M) (c c' : Config B) :
    Relation.ReflTransGen N.Step c c' ↔ Relation.ReflTransGen M.Step (c.map u) (c'.map u) := by
  constructor
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail d e _ hde ih => exact ih.tail (h.step.mp hde)
  · intro hr
    have key : ∀ x y : Config A, Relation.ReflTransGen M.Step x y →
        ∀ d e : Config B, x = d.map u → y = e.map u → Relation.ReflTransGen N.Step d e := by
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

/-- **Acceptance in bounded space transports along an equivalence.** -/
theorem Agree.acceptsSpace (h : Agree u N M) : N.AcceptsSpace ↔ M.AcceptsSpace := by
  constructor
  · rintro ⟨c₀, c, hinit, hreach, hacc⟩
    exact ⟨c₀.map u, c.map u, h.isInit.mp hinit, (h.reach c₀ c).mp hreach, (h.acc _).mp hacc⟩
  · rintro ⟨c₀, c, hinit, hreach, hacc⟩
    obtain ⟨d₀, rfl⟩ := Config.map_surjective u c₀
    obtain ⟨d, rfl⟩ := Config.map_surjective u c
    exact ⟨d₀, d, h.isInit.mpr hinit, (h.reach d₀ d).mpr hreach, (h.acc _).mpr hacc⟩

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

end DescriptiveComplexity
