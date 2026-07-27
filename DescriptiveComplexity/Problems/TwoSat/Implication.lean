/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.TwoSat.Defs

/-!
# The implication graph of a width-two CNF

The classical criterion for 2-satisfiability ([Aspvall, Plass & Tarjan
1979][aspvall1979linear]), in the form the PTIME membership of 2SAT needs: a
width-two CNF with no empty clause is satisfiable **iff no variable reaches its
own negation and back** in the implication graph.

The implication graph is `DescriptiveComplexity.TwoSatImpl.Step` on *signed* literals
`A × Bool`: a clause covered by the two occurrences `(x, s)` and `(y, u)` is the
disjunction `ℓ(x, s) ∨ ℓ(y, u)`, hence the two implications `¬ℓ(x, s) → ℓ(y, u)`
and `¬ℓ(y, u) → ℓ(x, s)`. A unit clause is the case `(y, u) = (x, s)`, whose
implication `¬ℓ(x, s) → ℓ(x, s)` forces the literal, so it needs no separate
treatment (`DescriptiveComplexity.exists_covering_pair` always supplies a pair).

* the easy direction, `DescriptiveComplexity.TwoSatImpl.litTrue_of_reach`: implications
  are sound, so under a satisfying assignment reachability preserves truth, and
  a variable reaching its own negation and back would be both true and false;
* the substantial direction,
  `DescriptiveComplexity.TwoSatImpl.satisfiable_of_no_bad_cycle`: build a satisfying
  assignment greedily. A set of literals that is *closed* under reachability and
  *consistent* (never containing a literal and its negation) can be extended to
  decide one more variable `x`: pick the sign `s` with `¬(ℓ(x, s) ⇝ ¬ℓ(x, s))`,
  which exists exactly because `x` has no bad cycle, and add everything
  reachable from `ℓ(x, s)`. Consistency survives by contraposition
  (`DescriptiveComplexity.TwoSatImpl.reach_neg`: `p ⇝ q` gives `¬q ⇝ ¬p`), which turns
  a clash inside the new part into the forbidden cycle, and a clash with the old
  part into `x` having been decided already. Deciding every variable in turn
  (`Finset.induction`) yields the assignment, and closedness makes every clause
  true: if a clause's first literal is false, the implication puts its second
  literal in the set.

No strongly connected components and no topological order are needed, which is
what makes the argument short here.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

namespace TwoSatImpl

variable {A : Type} [Language.sat.Structure A]

/-! ### Literals, the implication graph, and reachability -/

/-- The negation of a signed literal. -/
def neg (p : A × Bool) : A × Bool := (p.1, !p.2)

omit [Language.sat.Structure A] in
@[simp]
theorem neg_neg (p : A × Bool) : neg (neg p) = p := by
  simp [neg]

/-- The clause `c` is covered by the two signed occurrences `(x, s)` and
`(y, u)`: both occur in it, and nothing else does. -/
def Covers (c x : A) (s : Bool) (y : A) (u : Bool) : Prop :=
  OccIn c x s ∧ OccIn c y u ∧ ∀ z t, OccIn c z t → (z = x ∧ t = s) ∨ (z = y ∧ t = u)

/-- One step of the implication graph: a clause covered by `(x, s)` and
`(y, u)` implies `¬ℓ(x, s) → ℓ(y, u)` and `¬ℓ(y, u) → ℓ(x, s)`. -/
def Step (p q : A × Bool) : Prop :=
  ∃ (c x : A) (s : Bool) (y : A) (u : Bool), Covers c x s y u ∧
    ((p = (x, !s) ∧ q = (y, u)) ∨ (p = (y, !u) ∧ q = (x, s)))

/-- Reachability in the implication graph. -/
abbrev Reach : (A × Bool) → (A × Bool) → Prop := Relation.ReflTransGen Step

/-- **Contraposition, one step**: an implication `p → q` is also the
implication `¬q → ¬p`. -/
theorem step_neg {p q : A × Bool} (h : Step p q) : Step (neg q) (neg p) := by
  obtain ⟨c, x, s, y, u, hcov, hpq⟩ := h
  refine ⟨c, x, s, y, u, hcov, ?_⟩
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, by simp [neg]⟩
  · exact Or.inl ⟨rfl, by simp [neg]⟩

/-- **Contraposition**: `p ⇝ q` gives `¬q ⇝ ¬p`. -/
theorem reach_neg {p q : A × Bool} (h : Reach p q) : Reach (neg q) (neg p) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (step_neg hstep) ih

/-! ### Soundness of the implication graph -/

section Sound

variable {ν : A → Prop}

/-- One implication step preserves truth, under an assignment satisfying every
clause. -/
theorem litTrue_of_step (hν : ∀ c : A, IsCl c → ∃ z t, OccIn c z t ∧ LitTrue ν z t)
    {p q : A × Bool} (hstep : Step p q) (hp : LitTrue ν p.1 p.2) :
    LitTrue ν q.1 q.2 := by
  obtain ⟨c, x, s, y, u, ⟨hx, hy, hcov⟩, hpq⟩ := hstep
  obtain ⟨z, t, hz, hzT⟩ := hν c hx.isCl
  rcases hcov z t hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- the first literal is true; the implication starts at its negation
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hzT (litTrue_not.mp hp)
    · exact hzT
  · -- the second literal is true
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hzT
    · exact absurd hzT (litTrue_not.mp hp)

/-- **Implications are sound**: under an assignment satisfying every clause,
reachability preserves truth. -/
theorem litTrue_of_reach (hν : ∀ c : A, IsCl c → ∃ z t, OccIn c z t ∧ LitTrue ν z t)
    {p q : A × Bool} (h : Reach p q) (hp : LitTrue ν p.1 p.2) : LitTrue ν q.1 q.2 := by
  induction h with
  | refl => exact hp
  | tail _ hstep ih => exact litTrue_of_step hν hstep ih

end Sound

/-- **No satisfiable instance has a bad cycle**: a variable reaching its own
negation and back would be both true and false. -/
theorem no_bad_cycle_of_satisfiable (h : Satisfiable A) (x : A) (s : Bool) :
    ¬(Reach ((x, s) : A × Bool) (x, !s) ∧ Reach ((x, !s) : A × Bool) (x, s)) := by
  obtain ⟨ν, hν⟩ := h
  have hocc := satClauses_occ hν
  rintro ⟨h1, h2⟩
  by_cases hx : LitTrue ν x s
  · exact litTrue_not.mp (litTrue_of_reach hocc h1 hx) hx
  · exact hx (litTrue_of_reach hocc h2 (litTrue_not.mpr hx))

/-! ### Closed consistent sets of literals -/

section Greedy

/-- A set of literals closed under reachability. -/
def Closed (T : Set (A × Bool)) : Prop :=
  ∀ p ∈ T, ∀ q, Reach p q → q ∈ T

/-- A set of literals containing no literal together with its negation. -/
def Consistent (T : Set (A × Bool)) : Prop :=
  ∀ p : A × Bool, p ∈ T → neg p ∉ T

/-- The variable `x` is decided by `T`: one of its two literals is in `T`. -/
def Decides (T : Set (A × Bool)) (x : A) : Prop :=
  ((x, true) : A × Bool) ∈ T ∨ ((x, false) : A × Bool) ∈ T

theorem closed_empty : Closed (∅ : Set (A × Bool)) := by
  intro p hp
  exact hp.elim

omit [Language.sat.Structure A] in
theorem consistent_empty : Consistent (∅ : Set (A × Bool)) := by
  intro p hp
  exact hp.elim

/-- **The extension step**: a closed consistent set that does not decide `x`
can be extended to one that does, provided `x` has no bad cycle. -/
theorem exists_extend {T : Set (A × Bool)} (hclosed : Closed T) (hcons : Consistent T)
    {x : A} (hx : ¬Decides T x)
    (hcyc : ∀ s : Bool, ¬(Reach ((x, s) : A × Bool) (x, !s) ∧ Reach ((x, !s) : A × Bool) (x, s))) :
    ∃ T' : Set (A × Bool), Closed T' ∧ Consistent T' ∧ T ⊆ T' ∧ Decides T' x := by
  classical
  -- a sign whose literal does not reach its own negation
  obtain ⟨s, hs⟩ : ∃ s : Bool, ¬Reach ((x, s) : A × Bool) (x, !s) := by
    by_cases h : Reach ((x, true) : A × Bool) (x, false)
    · refine ⟨false, fun h' => hcyc true ⟨h, ?_⟩⟩
      simpa using h'
    · exact ⟨true, by simpa using h⟩
  refine ⟨T ∪ {q | Reach ((x, s) : A × Bool) q}, ?_, ?_, Set.subset_union_left, ?_⟩
  · -- closed: a union of two reachability-closed sets
    rintro p (hp | hp) q hq
    · exact Or.inl (hclosed p hp q hq)
    · exact Or.inr (hp.trans hq)
  · -- consistent
    rintro p (hp | hp) (hq | hq)
    · exact hcons p hp hq
    · -- `p ∈ T` and `¬p` reachable: contraposition puts `¬ℓ(x, s)` in `T`
      have hreach : Reach (neg (neg p)) (neg ((x, s) : A × Bool)) := reach_neg hq
      rw [neg_neg] at hreach
      have hmem := hclosed p hp _ hreach
      refine hx ?_
      cases s with
      | false => exact Or.inl (by simpa [neg] using hmem)
      | true => exact Or.inr (by simpa [neg] using hmem)
    · -- `¬p ∈ T` and `p` reachable: the same argument
      have hreach : Reach (neg p) (neg ((x, s) : A × Bool)) := reach_neg hp
      have hmem := hclosed (neg p) hq _ hreach
      refine hx ?_
      cases s with
      | false => exact Or.inl (by simpa [neg] using hmem)
      | true => exact Or.inr (by simpa [neg] using hmem)
    · -- both reachable from `ℓ(x, s)`: the forbidden cycle
      have hback : Reach p ((x, !s) : A × Bool) := by
        have h := reach_neg hq
        rw [neg_neg] at h
        simpa [neg] using h
      exact hs (hp.trans hback)
  · -- the new set decides `x`
    cases s with
    | false => exact Or.inr (Or.inr Relation.ReflTransGen.refl)
    | true => exact Or.inl (Or.inr Relation.ReflTransGen.refl)

variable [Finite A]

omit [Finite A] in
/-- Deciding a whole finite set of variables, one extension at a time. -/
theorem exists_closed_consistent_deciding
    (hcyc : ∀ (x : A) (s : Bool),
      ¬(Reach ((x, s) : A × Bool) (x, !s) ∧ Reach ((x, !s) : A × Bool) (x, s)))
    (S : Finset A) :
    ∃ T : Set (A × Bool), Closed T ∧ Consistent T ∧ ∀ x ∈ S, Decides T x := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨∅, closed_empty, consistent_empty, by simp⟩
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

/-- **The criterion for 2-satisfiability**: a width-two CNF with no empty
clause and no variable reaching its own negation and back is satisfiable. -/
theorem satisfiable_of_no_bad_cycle (hw : WidthAtMostTwo A)
    (hempty : ∀ c : A, ¬EmptyCl c)
    (hcyc : ∀ (x : A) (s : Bool),
      ¬(Reach ((x, s) : A × Bool) (x, !s) ∧ Reach ((x, !s) : A × Bool) (x, s))) :
    Satisfiable A := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨T, hclosed, hcons, hdec⟩ :=
    exists_closed_consistent_deciding hcyc (Finset.univ : Finset A)
  have hdec' : ∀ x : A, Decides T x := fun x => hdec x (Finset.mem_univ x)
  -- the assignment reads off `T`
  refine ⟨fun y => ((y, true) : A × Bool) ∈ T, fun c hc => ?_⟩
  -- a clause has an occurrence, hence a covering pair
  obtain ⟨x, s, hx⟩ : ∃ (x : A) (s : Bool), OccIn c x s := by
    by_contra h
    push Not at h
    exact hempty c ⟨hc, fun z t => h z t⟩
  obtain ⟨y, u, hy, hcov⟩ := exists_covering_pair hw hx
  -- membership of a literal in `T` is its truth value
  have hlit : ∀ (z : A) (t : Bool), ((z, t) : A × Bool) ∈ T →
      LitTrue (fun w => ((w, true) : A × Bool) ∈ T) z t := by
    intro z t hz
    cases t with
    | false =>
      have := hcons (z, false) hz
      simpa [neg, LitTrue] using this
    | true => exact hz
  -- the first literal, or else the second by the implication
  have hstep : Step ((x, !s) : A × Bool) (y, u) :=
    ⟨c, x, s, y, u, ⟨hx, hy, hcov⟩, Or.inl ⟨rfl, rfl⟩⟩
  have hsome : ∃ (z : A) (t : Bool), OccIn c z t ∧
      LitTrue (fun w => ((w, true) : A × Bool) ∈ T) z t := by
    rcases hdec' x with h | h
    · cases s with
      | false =>
        -- `(x, true) ∈ T` while the occurrence is negative: use the implication
        have : ((y, u) : A × Bool) ∈ T :=
          hclosed _ (by simpa using h) _ (Relation.ReflTransGen.single (by simpa using hstep))
        exact ⟨y, u, hy, hlit y u this⟩
      | true => exact ⟨x, true, hx, hlit x true h⟩
    · cases s with
      | false => exact ⟨x, false, hx, hlit x false h⟩
      | true =>
        have : ((y, u) : A × Bool) ∈ T :=
          hclosed _ (by simpa using h) _ (Relation.ReflTransGen.single (by simpa using hstep))
        exact ⟨y, u, hy, hlit y u this⟩
  obtain ⟨z, t, hz, hzT⟩ := hsome
  cases t with
  | false => exact ⟨z, Or.inr ⟨hz.2, hzT⟩⟩
  | true => exact ⟨z, Or.inl ⟨hz.2, hzT⟩⟩

end Greedy

end TwoSatImpl

end DescriptiveComplexity
