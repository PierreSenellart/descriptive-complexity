/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# The criterion for 2-satisfiability, abstractly

A 2-CNF over a type `V` of propositional variables is a relation `Cl` on
*literals* (`DescriptiveComplexity.TwoCnf.Lit`, a variable and a sign): `Cl p q` says
that `p ∨ q` is one of its clauses. Unit clauses are the case `q = p`; the empty
clause has no place here and is handled by whoever builds the formula, since it
is unsatisfiable outright.

This file proves the classical criterion ([Aspvall, Plass & Tarjan
1979][aspvall1979linear]) in this abstract setting: over a finite variable type,
the 2-CNF is satisfiable **iff no literal reaches its own negation and back** in
the implication graph, where the clause `p ∨ q` contributes the implications
`¬p → q` and `¬q → p` (`DescriptiveComplexity.TwoCnf.Step`).

Nothing here mentions first-order logic. That is the point: the criterion is
needed twice over, once for CNF structures over `FirstOrder.Language.sat`
(`DescriptiveComplexity.Problems.TwoSat.Ptime`, where it puts 2SAT in PTIME) and once
for the atoms of an arbitrary Krom program (where it turns a Krom definition
into a transitive closure), and the two differ only in what plays the part of a
variable.

The proof of the substantial direction builds a satisfying assignment greedily:
a set of literals that is *closed* under reachability and *consistent* (never
containing a literal together with its negation) can always be extended to
decide one more variable, by picking the sign whose literal does not reach its
own negation and adding everything reachable from it. Consistency survives by
contraposition (`DescriptiveComplexity.TwoCnf.reach_neg`), which turns a clash inside
the new part into the forbidden cycle and a clash with the old part into a
variable that was already decided. Deciding every variable in turn gives the
assignment, and closedness makes every clause true.
-/

namespace DescriptiveComplexity

namespace TwoCnf

variable {V : Type}

/-! ### Literals -/

/-- A literal: a variable together with a sign (`true` for the variable
itself, `false` for its negation). -/
abbrev Lit (V : Type) : Type := V × Bool

/-- The negation of a literal. -/
def neg (p : Lit V) : Lit V := (p.1, !p.2)

@[simp]
theorem neg_neg (p : Lit V) : neg (neg p) = p := by
  simp [neg]

@[simp]
theorem neg_fst (p : Lit V) : (neg p).1 = p.1 := rfl

/-- The literal is true under the assignment `ν`. -/
def LitTrue (ν : V → Prop) (p : Lit V) : Prop :=
  if p.2 then ν p.1 else ¬ν p.1

theorem litTrue_neg {ν : V → Prop} {p : Lit V} : LitTrue ν (neg p) ↔ ¬LitTrue ν p := by
  obtain ⟨x, s⟩ := p
  cases s <;> simp [LitTrue, neg]

/-! ### The implication graph -/

variable (Cl : Lit V → Lit V → Prop)

/-- The assignment satisfies the 2-CNF: every clause has a true literal. -/
def Satisfies (ν : V → Prop) : Prop :=
  ∀ p q : Lit V, Cl p q → LitTrue ν p ∨ LitTrue ν q

/-- One step of the implication graph: the clause `¬p ∨ q`, in either order,
is the implication `p → q`. -/
def Step (p q : Lit V) : Prop :=
  Cl (neg p) q ∨ Cl q (neg p)

/-- Reachability in the implication graph. -/
abbrev Reach : Lit V → Lit V → Prop :=
  Relation.ReflTransGen (Step Cl)

/-- **Contraposition, one step**: the implication `p → q` is also `¬q → ¬p`. -/
theorem step_neg {p q : Lit V} (h : Step Cl p q) : Step Cl (neg q) (neg p) := by
  rw [Step, neg_neg]
  exact h.symm

/-- **Contraposition**: `p ⇝ q` gives `¬q ⇝ ¬p`. -/
theorem reach_neg {p q : Lit V} (h : Reach Cl p q) : Reach Cl (neg q) (neg p) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (step_neg Cl hstep) ih

/-! ### Soundness -/

section Sound

variable {Cl} {ν : V → Prop}

/-- One implication step preserves truth. -/
theorem litTrue_of_step (hν : Satisfies Cl ν) {p q : Lit V} (hstep : Step Cl p q)
    (hp : LitTrue ν p) : LitTrue ν q := by
  rcases hstep with h | h
  · rcases hν _ _ h with h' | h'
    · exact absurd hp (litTrue_neg.mp h')
    · exact h'
  · rcases hν _ _ h with h' | h'
    · exact h'
    · exact absurd hp (litTrue_neg.mp h')

/-- **Implications are sound**: reachability preserves truth. -/
theorem litTrue_of_reach (hν : Satisfies Cl ν) {p q : Lit V} (h : Reach Cl p q)
    (hp : LitTrue ν p) : LitTrue ν q := by
  induction h with
  | refl => exact hp
  | tail _ hstep ih => exact litTrue_of_step hν hstep ih

end Sound

/-- **A satisfiable 2-CNF has no bad cycle**: a literal reaching its own
negation and back would be both true and false. -/
theorem no_bad_cycle_of_satisfies {ν : V → Prop} (hν : Satisfies Cl ν) (p : Lit V) :
    ¬(Reach Cl p (neg p) ∧ Reach Cl (neg p) p) := by
  rintro ⟨h1, h2⟩
  by_cases hp : LitTrue ν p
  · exact litTrue_neg.mp (litTrue_of_reach hν h1 hp) hp
  · exact hp (litTrue_of_reach hν h2 (litTrue_neg.mpr hp))

/-! ### Closed consistent sets of literals -/

section Greedy

/-- A set of literals closed under reachability. -/
def Closed (T : Set (Lit V)) : Prop :=
  ∀ p ∈ T, ∀ q, Reach Cl p q → q ∈ T

/-- A set of literals containing no literal together with its negation. -/
def Consistent (T : Set (Lit V)) : Prop :=
  ∀ p : Lit V, p ∈ T → neg p ∉ T

/-- The variable `x` is decided by `T`: one of its two literals is in `T`. -/
def Decides (T : Set (Lit V)) (x : V) : Prop :=
  ((x, true) : Lit V) ∈ T ∨ ((x, false) : Lit V) ∈ T

theorem closed_empty : Closed Cl (∅ : Set (Lit V)) := by
  intro p hp
  exact hp.elim

theorem consistent_empty : Consistent (∅ : Set (Lit V)) := by
  intro p hp
  exact hp.elim

variable {Cl}

/-- **The extension step**: a closed consistent set that does not decide `x`
can be extended to one that does, provided `x` has no bad cycle. -/
theorem exists_extend {T : Set (Lit V)} (hclosed : Closed Cl T) (hcons : Consistent T)
    {x : V} (hx : ¬Decides T x)
    (hcyc : ∀ s : Bool, ¬(Reach Cl ((x, s) : Lit V) (neg (x, s)) ∧
      Reach Cl (neg ((x, s) : Lit V)) (x, s))) :
    ∃ T' : Set (Lit V), Closed Cl T' ∧ Consistent T' ∧ T ⊆ T' ∧ Decides T' x := by
  classical
  -- a sign whose literal does not reach its own negation
  obtain ⟨s, hs⟩ : ∃ s : Bool, ¬Reach Cl ((x, s) : Lit V) (neg (x, s)) := by
    by_cases h : Reach Cl ((x, true) : Lit V) (neg (x, true))
    · refine ⟨false, fun h' => hcyc true ⟨h, ?_⟩⟩
      simpa [neg] using h'
    · exact ⟨true, h⟩
  refine ⟨T ∪ {q | Reach Cl ((x, s) : Lit V) q}, ?_, ?_, Set.subset_union_left, ?_⟩
  · -- closed: a union of two reachability-closed sets
    rintro p (hp | hp) q hq
    · exact Or.inl (hclosed p hp q hq)
    · exact Or.inr (hp.trans hq)
  · -- consistent
    rintro p (hp | hp) (hq | hq)
    · exact hcons p hp hq
    · -- `p ∈ T` and `¬p` reachable: contraposition puts `¬ℓ(x, s)` in `T`
      have hreach : Reach Cl (neg (neg p)) (neg ((x, s) : Lit V)) := reach_neg Cl hq
      rw [neg_neg] at hreach
      have hmem := hclosed p hp _ hreach
      refine hx ?_
      cases s with
      | false => exact Or.inl (by simpa [neg] using hmem)
      | true => exact Or.inr (by simpa [neg] using hmem)
    · -- `¬p ∈ T` and `p` reachable: the same argument
      have hreach : Reach Cl (neg p) (neg ((x, s) : Lit V)) := reach_neg Cl hp
      have hmem := hclosed (neg p) hq _ hreach
      refine hx ?_
      cases s with
      | false => exact Or.inl (by simpa [neg] using hmem)
      | true => exact Or.inr (by simpa [neg] using hmem)
    · -- both reachable from `ℓ(x, s)`: the forbidden cycle
      have hback : Reach Cl p (neg ((x, s) : Lit V)) := by
        have h := reach_neg Cl hq
        rwa [neg_neg] at h
      exact hs (hp.trans hback)
  · -- the new set decides `x`
    cases s with
    | false => exact Or.inr (Or.inr Relation.ReflTransGen.refl)
    | true => exact Or.inl (Or.inr Relation.ReflTransGen.refl)

/-- Deciding a whole finite set of variables, one extension at a time. -/
theorem exists_closed_consistent_deciding
    (hcyc : ∀ (x : V) (s : Bool), ¬(Reach Cl ((x, s) : Lit V) (neg (x, s)) ∧
      Reach Cl (neg ((x, s) : Lit V)) (x, s)))
    (S : Finset V) :
    ∃ T : Set (Lit V), Closed Cl T ∧ Consistent T ∧ ∀ x ∈ S, Decides T x := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨∅, closed_empty Cl, consistent_empty, by simp⟩
  | insert x S hx ih =>
    obtain ⟨T, hclosed, hcons, hdec⟩ := ih
    by_cases hxd : Decides T x
    · refine ⟨T, hclosed, hcons, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxd
      · exact hdec y hy
    · obtain ⟨T', hclosed', hcons', hsub, hdec'⟩ := exists_extend hclosed hcons hxd (hcyc x)
      refine ⟨T', hclosed', hcons', ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hdec'
      · rcases hdec y hy with h | h
        · exact Or.inl (hsub h)
        · exact Or.inr (hsub h)

variable [Finite V]

/-- **The criterion**: a 2-CNF with no literal reaching its own negation and
back is satisfiable. -/
theorem exists_satisfies_of_no_bad_cycle
    (hcyc : ∀ (x : V) (s : Bool), ¬(Reach Cl ((x, s) : Lit V) (neg (x, s)) ∧
      Reach Cl (neg ((x, s) : Lit V)) (x, s))) :
    ∃ ν : V → Prop, Satisfies Cl ν := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨T, hclosed, hcons, hdec⟩ :=
    exists_closed_consistent_deciding hcyc (Finset.univ : Finset V)
  have hdec' : ∀ x : V, Decides T x := fun x => hdec x (Finset.mem_univ x)
  refine ⟨fun y => ((y, true) : Lit V) ∈ T, fun p q hpq => ?_⟩
  -- membership of a literal in `T` is its truth value
  have hlit : ∀ r : Lit V, r ∈ T → LitTrue (fun y => ((y, true) : Lit V) ∈ T) r := by
    rintro ⟨y, t⟩ hr
    cases t with
    | false =>
      have := hcons (y, false) hr
      simpa [neg, LitTrue] using this
    | true => exact hr
  -- if the first literal is not in `T`, its negation is, and the clause's
  -- implication puts the second literal in `T`
  rcases hdec' p.1 with h | h
  · cases hp : p.2 with
    | false =>
      have hneg : neg p ∈ T := by
        obtain ⟨y, t⟩ := p
        simp only at hp
        subst hp
        simpa [neg] using h
      have hstep : Step Cl (neg p) q := Or.inl (by rwa [neg_neg])
      exact Or.inr (hlit q (hclosed _ hneg _ (Relation.ReflTransGen.single hstep)))
    | true =>
      refine Or.inl (hlit p ?_)
      obtain ⟨y, t⟩ := p
      simp only at hp
      subst hp
      exact h
  · cases hp : p.2 with
    | false =>
      refine Or.inl (hlit p ?_)
      obtain ⟨y, t⟩ := p
      simp only at hp
      subst hp
      exact h
    | true =>
      have hneg : neg p ∈ T := by
        obtain ⟨y, t⟩ := p
        simp only at hp
        subst hp
        simpa [neg] using h
      have hstep : Step Cl (neg p) q := Or.inl (by rwa [neg_neg])
      exact Or.inr (hlit q (hclosed _ hneg _ (Relation.ReflTransGen.single hstep)))

/-- **The criterion, as an equivalence**: a 2-CNF over a finite variable type
is satisfiable iff no literal reaches its own negation and back. -/
theorem exists_satisfies_iff_no_bad_cycle :
    (∃ ν : V → Prop, Satisfies Cl ν) ↔
      ∀ (x : V) (s : Bool), ¬(Reach Cl ((x, s) : Lit V) (neg (x, s)) ∧
        Reach Cl (neg ((x, s) : Lit V)) (x, s)) :=
  ⟨fun ⟨_, hν⟩ x s => no_bad_cycle_of_satisfies Cl hν (x, s),
    exists_satisfies_of_no_bad_cycle⟩

end Greedy

/-! ### A bad cycle as a single walk

A bad cycle is a *conjunction* of two reachabilities, `p ⇝ ¬p` and `¬p ⇝ p`,
which no single transitive closure can state. Carrying the literal the walk
started from, and a flag recording that its negation has been passed, turns the
pair into one walk: from `(p, p, false)` to `(p, p, true)`. This is what lets a
`DescriptiveComplexity.TCSpec` express unsatisfiability of a 2-CNF, the flag and the
two literals being the finite mode and the two tuples of a node. -/

section Carry

/-- A node of the cycle-witnessing graph: the literal the walk started from,
the literal it has reached, and whether it has already passed the negation of
the start. -/
abbrev CarryNode (V : Type) : Type := Lit V × Lit V × Bool

/-- One step of the cycle-witnessing graph: the start is kept, the current
literal moves along an implication, and the flag may turn from `false` to
`true` exactly on arrival at the negation of the start. -/
def CarryStep (a b : CarryNode V) : Prop :=
  b.1 = a.1 ∧ Step Cl a.2.1 b.2.1 ∧
    (b.2.2 = a.2.2 ∨ (a.2.2 = false ∧ b.2.2 = true ∧ b.2.1 = neg b.1))

variable {Cl}

/-- A walk of the cycle-witnessing graph projects to a walk of the implication
graph. -/
theorem reach_of_carryReach {a b : CarryNode V}
    (h : Relation.ReflTransGen (CarryStep Cl) a b) : Reach Cl a.2.1 b.2.1 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.2.1

/-- The start component is constant along a walk. -/
theorem start_of_carryReach {a b : CarryNode V}
    (h : Relation.ReflTransGen (CarryStep Cl) a b) : b.1 = a.1 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.1.trans ih

/-- A walk of the implication graph lifts to one of the cycle-witnessing graph
at any fixed start and flag. -/
theorem carryReach_of_reach (s : Lit V) (ph : Bool) {a b : Lit V} (h : Reach Cl a b) :
    Relation.ReflTransGen (CarryStep Cl) (s, a, ph) (s, b, ph) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail ⟨rfl, hstep, Or.inl rfl⟩

/-- What a walk that has raised its flag witnesses: the start's negation was
passed on the way. -/
theorem reach_neg_of_carryReach {s a : Lit V} {d : CarryNode V}
    (h : Relation.ReflTransGen (CarryStep Cl) ((s, a, false) : CarryNode V) d)
    (hd : d.2.2 = true) : Reach Cl a (neg s) ∧ Reach Cl (neg s) d.2.1 := by
  induction h with
  | refl => exact absurd hd (by simp)
  | @tail c d hac hcd ih =>
    obtain ⟨hstart, hstep, hphase⟩ := hcd
    have hc1 : c.1 = s := start_of_carryReach hac
    cases hcph : c.2.2 with
    | false =>
      -- the flag goes up now, so the step arrives at the negation of the start
      rcases hphase with hph | ⟨-, -, hneg⟩
      · rw [hcph] at hph
        exact absurd (hph.symm.trans hd) (by simp)
      · have hdneg : d.2.1 = neg s := by rw [hneg, hstart, hc1]
        refine ⟨?_, ?_⟩
        · have hreach : Reach Cl a c.2.1 := reach_of_carryReach hac
          rw [← hdneg]
          exact hreach.tail hstep
        · rw [hdneg]
    | true =>
      -- the flag was already up: extend the second half
      obtain ⟨h1, h2⟩ := ih hcph
      exact ⟨h1, h2.tail hstep⟩

/-- **A bad cycle is a single walk**: the literal `p` reaches its own negation
and comes back exactly when the cycle-witnessing graph takes `(p, p, false)` to
`(p, p, true)`. -/
theorem carryReach_iff (p : Lit V) :
    Relation.ReflTransGen (CarryStep Cl) ((p, p, false) : CarryNode V) (p, p, true) ↔
      (Reach Cl p (neg p) ∧ Reach Cl (neg p) p) := by
  constructor
  · intro h
    exact reach_neg_of_carryReach h rfl
  · rintro ⟨h1, h2⟩
    -- the first walk ends at `¬p`, which is not `p`, so it has a last step
    rcases Relation.ReflTransGen.cases_tail h1 with hEq | ⟨c, hac, hcb⟩
    · exact absurd hEq.symm (by simp [neg, Prod.ext_iff])
    · have hstep : CarryStep Cl ((p, c, false) : CarryNode V) (p, neg p, true) :=
        ⟨rfl, hcb, Or.inr ⟨rfl, rfl, rfl⟩⟩
      exact ((carryReach_of_reach p false hac).tail hstep).trans
        (carryReach_of_reach p true h2)

end Carry

end TwoCnf

end DescriptiveComplexity
