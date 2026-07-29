/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OrderWalk

/-!
# The inductive-counting machine, abstractly

The combinatorial heart of **Immerman–Szelepcsényi** ([Immerman
1988][immerman1988nondeterministic], [Szelepcsényi 1988][szelepcsenyi1988method]):
a nondeterministic walk on configurations that reaches an accepting
configuration exactly when *no* target is reachable from a source in a finite
graph.

Everything here is about an abstract finite linearly ordered node type `V` with
an edge relation `E` and source and target predicates `S`, `T`; nothing is
first-order yet. `DescriptiveComplexity.InductiveCounting.Sound` and
`DescriptiveComplexity.InductiveCounting.Complete` prove the two directions, and
`DescriptiveComplexity.TransitiveClosureCompl` runs the whole machine inside a single
`TC` by realizing each configuration as a mode together with a tuple of
elements.

## The algorithm

Write `Rset d` for the set of nodes reachable from a source in at most `d`
steps. The counts `|Rset d|` are computed by *inductive counting*: knowing
`|Rset d|` exactly, one can certify, for a given node `v`, whether
`v ∈ Rset (d+1)`, by running over *all* nodes `u` in order, guessing which
belong to `Rset d`, certifying each guess by a path of length at most `d` from
a source, and checking at the end that exactly `|Rset d|` of them were
certified – which forces the guessed set to be `Rset d` itself. Counting the
`v`'s that pass gives `|Rset (d+1)|`. The machine accepts when
`|Rset (d+1)| = |Rset d|`, at which point the reachable set is `Rset d`; since
every certified node is checked not to be a target, acceptance means no target
is reachable.

## The registers

The machine has eight registers, each holding an element of `WithBot V`: a
node, or a count read through `DescriptiveComplexity.orank` (so `⊥` is the count `0`
and the count `m` is the `m`-th value of `WithBot V`). This uniformity is what
lets a register be stored, in the first-order realization, as one tuple of
elements together with a finite mode.
-/

namespace DescriptiveComplexity

namespace InductiveCounting

/-! ### Layered reachability -/

section Reach

variable {V : Type} {E : V → V → Prop} {S : V → Prop}

/-- `RInLe E n a b`: the node `b` is reachable from `a` along `E` in at most
`n` steps. -/
def RInLe (E : V → V → Prop) : ℕ → V → V → Prop
  | 0, a, b => a = b
  | n + 1, a, b => RInLe E n a b ∨ ∃ c, RInLe E n a c ∧ E c b

@[simp] theorem rInLe_zero {a b : V} : RInLe E 0 a b ↔ a = b := Iff.rfl

theorem rInLe_succ {n : ℕ} {a b : V} :
    RInLe E (n + 1) a b ↔ RInLe E n a b ∨ ∃ c, RInLe E n a c ∧ E c b := Iff.rfl

theorem RInLe.step {n : ℕ} {a b : V} (h : RInLe E n a b) : RInLe E (n + 1) a b := Or.inl h

theorem RInLe.mono {n m : ℕ} {a b : V} (hnm : n ≤ m) (h : RInLe E n a b) : RInLe E m a b := by
  induction m with
  | zero => exact (Nat.le_zero.mp hnm) ▸ h
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.mp hlt)).step
    · exact (Nat.le_antisymm hnm hge) ▸ h

/-- Prepending an edge to a bounded walk. -/
theorem RInLe.cons {n : ℕ} {a b c : V} (hab : E a b) (h : RInLe E n b c) :
    RInLe E (n + 1) a c := by
  induction n generalizing c with
  | zero => exact Or.inr ⟨a, rfl, (rInLe_zero.mp h) ▸ hab⟩
  | succ n ih =>
    rcases rInLe_succ.mp h with h' | ⟨e, he, hec⟩
    · exact (ih h').step
    · exact Or.inr ⟨e, ih he, hec⟩

/-- The set of nodes reachable from a source in at most `d` steps. -/
def Rset (E : V → V → Prop) (S : V → Prop) : ℕ → Set V
  | 0 => {x | S x}
  | d + 1 => {x | ∃ y ∈ Rset E S d, y = x ∨ E y x}

theorem rset_zero : Rset E S 0 = {x | S x} := rfl

theorem mem_rset_succ {d : ℕ} {x : V} :
    x ∈ Rset E S (d + 1) ↔ ∃ y ∈ Rset E S d, y = x ∨ E y x := Iff.rfl

theorem Rset.subset_succ {d : ℕ} : Rset E S d ⊆ Rset E S (d + 1) :=
  fun _ hx => ⟨_, hx, Or.inl rfl⟩

theorem Rset.mono {d e : ℕ} (h : d ≤ e) : Rset E S d ⊆ Rset E S e := by
  induction e with
  | zero => exact (Nat.le_zero.mp h) ▸ subset_rfl
  | succ e ih =>
    rcases Nat.lt_or_ge d (e + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans Rset.subset_succ
    · exact (Nat.le_antisymm h hge) ▸ subset_rfl

/-- Walking on from a layer: a bounded walk out of `Rset i` lands in a later
layer. -/
theorem mem_rset_of_rInLe {i n : ℕ} {y b : V} (hy : y ∈ Rset E S i)
    (h : RInLe E n y b) : b ∈ Rset E S (i + n) := by
  induction n generalizing b with
  | zero => exact (rInLe_zero.mp h) ▸ hy
  | succ n ih =>
    rcases rInLe_succ.mp h with h' | ⟨c, hc, hcb⟩
    · exact Rset.subset_succ (ih h')
    · exact ⟨c, ih hc, Or.inr hcb⟩

/-- Every member of a layer carries a bounded walk from a source. -/
theorem exists_rInLe_of_mem_rset {d : ℕ} {x : V} (hx : x ∈ Rset E S d) :
    ∃ s, S s ∧ RInLe E d s x := by
  induction d generalizing x with
  | zero => exact ⟨x, hx, rfl⟩
  | succ d ih =>
    obtain ⟨y, hy, h⟩ := mem_rset_succ.mp hx
    obtain ⟨s, hs, hsy⟩ := ih hy
    rcases h with rfl | hyx
    · exact ⟨s, hs, hsy.step⟩
    · exact ⟨s, hs, Or.inr ⟨y, hsy, hyx⟩⟩

/-- The layers exhaust the reachable set. -/
theorem exists_mem_rset_of_reflTransGen {s x : V} (hs : S s)
    (h : Relation.ReflTransGen E s x) : ∃ d, x ∈ Rset E S d := by
  induction h with
  | refl => exact ⟨0, hs⟩
  | @tail b c _ hbc ih =>
    obtain ⟨d, hd⟩ := ih
    exact ⟨d + 1, ⟨b, hd, Or.inr hbc⟩⟩

/-- Conversely, every member of a layer is reachable from a source. -/
theorem reflTransGen_of_mem_rset {d : ℕ} {x : V} (hx : x ∈ Rset E S d) :
    ∃ s, S s ∧ Relation.ReflTransGen E s x := by
  induction d generalizing x with
  | zero => exact ⟨x, hx, Relation.ReflTransGen.refl⟩
  | succ d ih =>
    obtain ⟨y, hy, h⟩ := mem_rset_succ.mp hx
    obtain ⟨s, hs, hsy⟩ := ih hy
    rcases h with rfl | hyx
    · exact ⟨s, hs, hsy⟩
    · exact ⟨s, hs, hsy.tail hyx⟩

/-- Once a layer repeats, all later layers agree with it. -/
theorem rset_stabilizes {d : ℕ} (h : Rset E S (d + 1) = Rset E S d) :
    ∀ e, Rset E S (d + e) = Rset E S d := by
  intro e
  induction e with
  | zero => rfl
  | succ e ih =>
    have : Rset E S (d + e + 1) = Rset E S (d + 1) := by
      change {x | ∃ y ∈ Rset E S (d + e), y = x ∨ E y x} = {x | ∃ y ∈ Rset E S d, y = x ∨ E y x}
      rw [ih]
    rw [show d + (e + 1) = d + e + 1 from rfl, this, h]

/-- If no layer contains a target, no target is reachable from a source. -/
theorem not_reach_target_of_stable {d : ℕ} {T : V → Prop}
    (hstab : Rset E S (d + 1) = Rset E S d) (hT : ∀ y ∈ Rset E S d, ¬T y) :
    ¬∃ a b, S a ∧ T b ∧ Relation.ReflTransGen E a b := by
  rintro ⟨a, b, ha, hb, hab⟩
  obtain ⟨e, he⟩ := exists_mem_rset_of_reflTransGen ha hab
  have h1 : b ∈ Rset E S (d + e) := Rset.mono (Nat.le_add_left e d) he
  rw [rset_stabilizes hstab e] at h1
  exact hT b h1 hb

end Reach

/-! ### Registers, slots and atomic constraints -/

/-- The eight registers of the machine. -/
abbrev Reg := Fin 8

namespace Reg

/-- The stage counter: the current layer index `d`. -/
def d : Reg := 0

/-- The count of the current layer, `|Rset d|`. -/
def c : Reg := 1

/-- The count of the next layer being built, `|Rset (d+1)|`. -/
def c2 : Reg := 2

/-- The node scanned by the outer loop. -/
def v : Reg := 3

/-- The count of nodes certified in the inner loop. -/
def cnt : Reg := 4

/-- The node scanned by the inner loop. -/
def u : Reg := 5

/-- The node walked backwards along a certifying path. -/
def w : Reg := 6

/-- The countdown of the certifying path's remaining length. -/
def j : Reg := 7

end Reg

/-- A *slot*: a register, read either in the current configuration (`false`) or
in the next one (`true`). -/
abbrev Slot := Bool × Reg

/-- The slot reading a register in the current configuration. -/
abbrev old (r : Reg) : Slot := (false, r)

/-- The slot reading a register in the next configuration. -/
abbrev nxt (r : Reg) : Slot := (true, r)

/-- An atomic constraint relating the registers of two consecutive
configurations. Each one is realized, in the first-order construction, by one
formula over two tuples of variables. -/
inductive VAtom
  /-- Two slots hold the same value. -/
  | eqR (a b : Slot)
  /-- Two slots hold different values. -/
  | neqR (a b : Slot)
  /-- The second slot holds the immediate successor of the first. -/
  | succR (a b : Slot)
  /-- The two slots hold nodes joined by an edge. -/
  | edge (a b : Slot)
  /-- The two slots do not hold nodes joined by an edge. -/
  | nedge (a b : Slot)
  /-- The slot holds a source node. -/
  | srcR (a : Slot)
  /-- The slot does not hold a source node. -/
  | nsrcR (a : Slot)
  /-- The slot holds a target node. -/
  | tgtR (a : Slot)
  /-- The slot does not hold a target node. -/
  | ntgtR (a : Slot)
  /-- The slot holds the least node. -/
  | botNode (a : Slot)
  /-- The slot holds the greatest node. -/
  | topNode (a : Slot)
  /-- The slot holds the count zero. -/
  | isZero (a : Slot)

/-! ### Configurations and the transition table -/

/-- The control phases of the machine. -/
inductive Phase
  /-- Scanning all nodes to count the sources, that is `|Rset 0|`. -/
  | initCount
  /-- The inner loop: at node `u`, about to certify it or to skip it. -/
  | inner
  /-- Walking backwards along a certifying path for `u`. -/
  | walk
  /-- The certifying path is complete: count `u` in and test it against `v`. -/
  | certDone
  /-- The inner loop is over: check that the count matches `|Rset d|`. -/
  | check
  /-- The outer loop is over: `c2` holds `|Rset (d+1)|`. -/
  | stageEnd
  /-- The accepting phase. -/
  | accept
  deriving DecidableEq

instance : Finite Phase :=
  Finite.of_injective
    (β := Fin 7)
    (fun p => match p with
      | .initCount => 0
      | .inner => 1
      | .walk => 2
      | .certDone => 3
      | .check => 4
      | .stageEnd => 5
      | .accept => 6)
    (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- A configuration: a phase, the flag recording whether the current outer node
has been found in the next layer, and the eight registers. -/
structure Cfg (V : Type) where
  /-- The control phase. -/
  phase : Phase
  /-- The flag: `v` has been seen to lie in the next layer. -/
  flag : Bool
  /-- The registers. -/
  regs : Reg → WithBot V

section Table

open VAtom

/-- The transition table: a list of alternatives, each a list of atomic
constraints, for every pair of control states (a phase and the flag). The
algorithm of the module docstring is entirely contained here. -/
def table (p q : Phase × Bool) : List (List VAtom) :=
  match p.1, q.1 with
  | .initCount, .initCount =>
      if p.2 = q.2 then
        [[srcR (old .v), succR (old .c) (nxt .c), succR (old .v) (nxt .v)],
         [nsrcR (old .v), eqR (old .c) (nxt .c), succR (old .v) (nxt .v)]]
      else []
  | .initCount, .inner =>
      if q.2 = false then
        [[srcR (old .v), succR (old .c) (nxt .c), topNode (old .v), isZero (nxt .d),
          isZero (nxt .c2), isZero (nxt .cnt), botNode (nxt .v), botNode (nxt .u)],
         [nsrcR (old .v), eqR (old .c) (nxt .c), topNode (old .v), isZero (nxt .d),
          isZero (nxt .c2), isZero (nxt .cnt), botNode (nxt .v), botNode (nxt .u)]]
      else []
  | .inner, .inner =>
      if p.2 = q.2 then
        [[succR (old .u) (nxt .u), eqR (old .d) (nxt .d), eqR (old .c) (nxt .c),
          eqR (old .c2) (nxt .c2), eqR (old .v) (nxt .v), eqR (old .cnt) (nxt .cnt)]]
      else []
  | .inner, .check =>
      if p.2 = q.2 then
        [[topNode (old .u), eqR (old .d) (nxt .d), eqR (old .c) (nxt .c),
          eqR (old .c2) (nxt .c2), eqR (old .v) (nxt .v), eqR (old .cnt) (nxt .cnt)]]
      else []
  | .inner, .walk =>
      if p.2 = q.2 then
        [[ntgtR (old .u), eqR (old .u) (nxt .w), eqR (old .d) (nxt .j),
          eqR (old .d) (nxt .d), eqR (old .c) (nxt .c), eqR (old .c2) (nxt .c2),
          eqR (old .v) (nxt .v), eqR (old .cnt) (nxt .cnt), eqR (old .u) (nxt .u)]]
      else []
  | .walk, .walk =>
      if p.2 = q.2 then
        [[succR (nxt .j) (old .j), edge (nxt .w) (old .w),
          eqR (old .d) (nxt .d), eqR (old .c) (nxt .c), eqR (old .c2) (nxt .c2),
          eqR (old .v) (nxt .v), eqR (old .cnt) (nxt .cnt), eqR (old .u) (nxt .u)]]
      else []
  | .walk, .certDone =>
      if p.2 = q.2 then
        [[srcR (old .w), eqR (old .d) (nxt .d), eqR (old .c) (nxt .c),
          eqR (old .c2) (nxt .c2), eqR (old .v) (nxt .v), eqR (old .cnt) (nxt .cnt),
          eqR (old .u) (nxt .u)]]
      else []
  | .certDone, .inner =>
      let base := [succR (old .cnt) (nxt .cnt), succR (old .u) (nxt .u),
        eqR (old .d) (nxt .d), eqR (old .c) (nxt .c), eqR (old .c2) (nxt .c2),
        eqR (old .v) (nxt .v)]
      (if q.2 then [eqR (old .u) (old .v) :: base, edge (old .u) (old .v) :: base] else []) ++
        (if p.2 = q.2 then [neqR (old .u) (old .v) :: nedge (old .u) (old .v) :: base] else [])
  | .certDone, .check =>
      let base := [succR (old .cnt) (nxt .cnt), topNode (old .u),
        eqR (old .d) (nxt .d), eqR (old .c) (nxt .c), eqR (old .c2) (nxt .c2),
        eqR (old .v) (nxt .v)]
      (if q.2 then [eqR (old .u) (old .v) :: base, edge (old .u) (old .v) :: base] else []) ++
        (if p.2 = q.2 then [neqR (old .u) (old .v) :: nedge (old .u) (old .v) :: base] else [])
  | .check, .inner =>
      if q.2 = false then
        [(if p.2 then succR (old .c2) (nxt .c2) else eqR (old .c2) (nxt .c2)) ::
          [eqR (old .cnt) (old .c), succR (old .v) (nxt .v), isZero (nxt .cnt),
           botNode (nxt .u), eqR (old .d) (nxt .d), eqR (old .c) (nxt .c)]]
      else []
  | .check, .stageEnd =>
      if q.2 = false then
        [(if p.2 then succR (old .c2) (nxt .c2) else eqR (old .c2) (nxt .c2)) ::
          [eqR (old .cnt) (old .c), topNode (old .v),
           eqR (old .d) (nxt .d), eqR (old .c) (nxt .c)]]
      else []
  | .stageEnd, .inner =>
      if q.2 = false then
        [[succR (old .d) (nxt .d), eqR (old .c2) (nxt .c), isZero (nxt .c2),
          isZero (nxt .cnt), botNode (nxt .v), botNode (nxt .u)]]
      else []
  | .stageEnd, .accept => [[eqR (old .c2) (old .c)]]
  | _, _ => []

end Table

/-! ### The semantics of the machine -/

section Semantics

variable {V : Type} [LinearOrder V] (E : V → V → Prop) (S T : V → Prop)

/-- Two slots hold nodes joined by an edge. -/
def EW (a b : WithBot V) : Prop := ∃ p q : V, a = ↑p ∧ b = ↑q ∧ E p q

/-- A slot holds a node satisfying a predicate. -/
def PW (S : V → Prop) (a : WithBot V) : Prop := ∃ p : V, a = ↑p ∧ S p

/-- The value a slot reads, from the current and the next register vectors. -/
def slotVal (x y : Reg → WithBot V) : Slot → WithBot V
  | (false, r) => x r
  | (true, r) => y r

/-- What an atomic constraint asserts about two register vectors. -/
def VAtom.Holds (x y : Reg → WithBot V) : VAtom → Prop
  | .eqR a b => slotVal x y a = slotVal x y b
  | .neqR a b => slotVal x y a ≠ slotVal x y b
  | .succR a b => slotVal x y a ⋖ slotVal x y b
  | .edge a b => EW E (slotVal x y a) (slotVal x y b)
  | .nedge a b => ¬EW E (slotVal x y a) (slotVal x y b)
  | .srcR a => PW S (slotVal x y a)
  | .nsrcR a => ¬PW S (slotVal x y a)
  | .tgtR a => PW T (slotVal x y a)
  | .ntgtR a => ¬PW T (slotVal x y a)
  | .botNode a => PW (fun p => ∀ z : V, p ≤ z) (slotVal x y a)
  | .topNode a => PW (fun p => ∀ z : V, z ≤ p) (slotVal x y a)
  | .isZero a => slotVal x y a = ⊥

/-- All the constraints of an alternative hold. -/
def Sat (x y : Reg → WithBot V) (l : List VAtom) : Prop :=
  ∀ a ∈ l, VAtom.Holds E S T x y a

@[simp] theorem sat_nil (x y : Reg → WithBot V) : Sat E S T x y [] := by
  intro a ha; exact absurd ha (List.not_mem_nil)

@[simp] theorem sat_cons {a : VAtom} {l : List VAtom} (x y : Reg → WithBot V) :
    Sat E S T x y (a :: l) ↔ VAtom.Holds E S T x y a ∧ Sat E S T x y l := by
  constructor
  · exact fun h => ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem _ hb)⟩
  · rintro ⟨h1, h2⟩ b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact h1
    · exact h2 b hb'

/-- One step of the machine: some alternative of the table entry for the two
control states is satisfied by the two register vectors. -/
def CfgStep (s s' : Cfg V) : Prop :=
  ∃ l ∈ table (s.phase, s.flag) (s'.phase, s'.flag), Sat E S T s.regs s'.regs l

/-- Reachability between configurations. -/
abbrev CfgReach : Cfg V → Cfg V → Prop := Relation.ReflTransGen (CfgStep E S T)

/-- The initial configurations: the source scan is about to start, with a zero
count and the outer register at the least node. -/
def CfgIsSrc (s : Cfg V) : Prop :=
  s.phase = .initCount ∧ s.flag = false ∧ s.regs .c = ⊥ ∧
    PW (fun p => ∀ z : V, p ≤ z) (s.regs .v)

/-- The accepting configurations. -/
def CfgIsTgt (s : Cfg V) : Prop := s.phase = .accept

/-- The machine accepts: an accepting configuration is reachable from an
initial one. -/
def MachineAccepts : Prop :=
  ∃ s s' : Cfg V, CfgIsSrc s ∧ CfgIsTgt s' ∧ CfgReach E S T s s'

end Semantics

end InductiveCounting

end DescriptiveComplexity
