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
`d` of its interpretation. -/
def Accepts : Prop :=
  ∃ (c₀ c : Config A) (n : ℕ), M.IsInit c₀ ∧ n ≤ Nat.card {p : A // M.Posn p} ∧
    M.StepsIn n c₀ c ∧ M.Acc c.state

/-- **Well-formedness**, folded into the yes-instances in the style of
`DescriptiveComplexity.IsLinOrd` for Knapsack: the order is linear, there is a position
to start on, the input is functional, and there is exactly one blank symbol.
Every conjunct is first-order, so the `Σ₁` kernel can check it. -/
def WellFormed : Prop :=
  IsLinOrd M.Le ∧ (∃ p, M.Posn p) ∧
    (∀ p a b, M.Inp p a → M.Inp p b → a = b) ∧
    (∃ b, M.Blank b) ∧ (∀ a b, M.Blank a → M.Blank b → a = b)

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
