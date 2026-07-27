/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderKrom
import DescriptiveComplexity.TwoCnf
import Mathlib.Data.Finite.Sigma

/-!
# The implication graph of a Krom program

A Krom program, instantiated in a structure, *is* a 2-CNF: its propositional
variables are the atoms of the block at tuples of elements
(`DescriptiveComplexity.KromImpl.KromAtom`), and each clause of the program contributes
one propositional clause per valuation of its universally quantified variables
satisfying its guard (`DescriptiveComplexity.KromImpl.clauseRel`).

So the criterion of `DescriptiveComplexity.TwoCnf` applies, and gives the fact this
file exists for:

```
(∃ ρ, prog.Holds ρ) ↔ no goal clause fires ∧ no literal reaches its own negation and back
```

(`DescriptiveComplexity.KromImpl.exists_holds_iff`). The first conjunct is the empty
clause of the 2-CNF, which has no place in the abstract criterion and is
therefore carried separately: a clause of the program with neither literal
slot filled is `guard → ⊥`, and its firing makes the program unsatisfiable
outright.

This is the Lean-level half of the converse translation from the Krom fragment
to FO(TC): what remains after it is to *express* the implication graph as a
`DescriptiveComplexity.TCSpec`, i.e. to build the transition formulas that walk it. The
half proved here is where the mathematics is; the other half is formula
plumbing.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace KromImpl

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ}

/-! ### The propositional variables -/

variable (B) in
/-- A propositional variable of the instantiated program: a relation variable
of the block together with a tuple of elements. -/
def KromAtom (A : Type) : Type := Σ i : B.ι, Fin (B.arity i) → A

instance (A : Type) [Finite A] : Finite (KromAtom B A) :=
  inferInstanceAs (Finite (Σ i : B.ι, Fin (B.arity i) → A))

section Semantics

variable {A : Type} [L.Structure A]

/-- The block assignment described by a truth assignment of the propositional
variables. -/
def toAssign (ν : KromAtom B A → Prop) : B.Assignment A :=
  fun i x => ν ⟨i, x⟩

/-- The truth assignment of the propositional variables described by a block
assignment. -/
def ofAssign (ρ : B.Assignment A) : KromAtom B A → Prop :=
  fun a => ρ a.1 a.2

@[simp]
theorem toAssign_ofAssign (ρ : B.Assignment A) : toAssign (ofAssign ρ) = ρ := rfl

@[simp]
theorem ofAssign_toAssign (ν : KromAtom B A → Prop) : ofAssign (toAssign ν) = ν := by
  funext a
  obtain ⟨i, x⟩ := a
  rfl

theorem eq_of_mem_option {α : Type} {o : Option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) :
    a = b := by
  have e₁ := Option.mem_def.mp ha
  have e₂ := Option.mem_def.mp hb
  rw [e₂, Option.some.injEq] at e₁
  exact e₁.symm

/-- The propositional variable an atom denotes at a valuation. -/
def atomVar (a : SOAtom B k) (v : Fin k → A) : KromAtom B A :=
  ⟨a.idx, fun j => v (a.args j)⟩

/-- The literal a Krom literal denotes at a valuation. -/
def litOf (l : KromLit B k) (v : Fin k → A) : TwoCnf.Lit (KromAtom B A) :=
  (atomVar l.atom v, l.positive)

theorem holds_iff_litTrue (l : KromLit B k) (ν : KromAtom B A → Prop) (v : Fin k → A) :
    l.Holds (toAssign ν) v ↔ TwoCnf.LitTrue ν (litOf l v) := by
  cases hpos : l.positive <;> simp [KromLit.Holds, TwoCnf.LitTrue, litOf, atomVar,
    toAssign, SOAtom.Holds, hpos]

end Semantics

/-! ### The 2-CNF of a program -/

section Program

variable {A : Type} [L.Structure A]

/-- The clauses of the instantiated program, as a 2-CNF in the sense of
`DescriptiveComplexity.TwoCnf`: a clause of the program whose guard holds at some
valuation contributes the disjunction of its two literals, read at that
valuation. A unit clause contributes the disjunction of its literal with
itself, which is what `DescriptiveComplexity.TwoCnf` expects. -/
def clauseRel (prog : KromProgram L B k) (p q : TwoCnf.Lit (KromAtom B A)) : Prop :=
  ∃ c ∈ prog, ∃ v : Fin k → A, c.guard.Realize v ∧
    ((∃ l₁ ∈ c.lit₁, ∃ l₂ ∈ c.lit₂, p = litOf l₁ v ∧ q = litOf l₂ v) ∨
      (∃ l₁ ∈ c.lit₁, c.lit₂ = none ∧ p = litOf l₁ v ∧ q = litOf l₁ v) ∨
      ∃ l₂ ∈ c.lit₂, c.lit₁ = none ∧ p = litOf l₂ v ∧ q = litOf l₂ v)

/-- The ordered pairs of literals a clause contributes to the implication
graph: the clause `ℓ₁ ∨ ℓ₂` gives the edges `¬ℓ₁ → ℓ₂` and `¬ℓ₂ → ℓ₁`, and a
unit clause `ℓ` the edge `¬ℓ → ℓ`. The pair records the two *clause* literals,
the edge running from the negation of the first to the second. -/
def edgePairs (c : KromClause L B k) : List (KromLit B k × KromLit B k) :=
  match c.lit₁, c.lit₂ with
  | some l₁, some l₂ => [(l₁, l₂), (l₂, l₁)]
  | some l₁, none => [(l₁, l₁)]
  | none, some l₂ => [(l₂, l₂)]
  | none, none => []

/-- **The implication graph, clause by clause**: there is an edge from `p` to
`q` exactly when some clause of the program, at some valuation satisfying its
guard, contributes the pair whose first literal is the negation of `p` and
whose second is `q`. The `DescriptiveComplexity.TwoCnf.Step` on the left is symmetric in
the two literals of a clause, which is why the *ordered* pairs of
`DescriptiveComplexity.KromImpl.edgePairs` suffice. -/
theorem step_iff_edgePairs (prog : KromProgram L B k)
    (p q : TwoCnf.Lit (KromAtom B A)) :
    TwoCnf.Step (clauseRel prog) p q ↔
      ∃ c ∈ prog, ∃ v : Fin k → A, c.guard.Realize v ∧
        ∃ pr ∈ edgePairs c, TwoCnf.neg p = litOf pr.1 v ∧ q = litOf pr.2 v := by
  constructor
  · rintro (⟨c, hc, v, hg, hcase⟩ | ⟨c, hc, v, hg, hcase⟩) <;>
      refine ⟨c, hc, v, hg, ?_⟩
    · rcases hcase with ⟨l₁, h₁, l₂, h₂, hp, hq⟩ | ⟨l₁, h₁, h₂, hp, hq⟩ |
        ⟨l₂, h₂, h₁, hp, hq⟩
      · refine ⟨(l₁, l₂), ?_, hp, hq⟩
        rw [edgePairs, Option.mem_def.mp h₁, Option.mem_def.mp h₂]
        simp
      · refine ⟨(l₁, l₁), ?_, hp, hq⟩
        rw [edgePairs, Option.mem_def.mp h₁, h₂]
        simp
      · refine ⟨(l₂, l₂), ?_, hp, hq⟩
        rw [edgePairs, Option.mem_def.mp h₂, h₁]
        simp
    · rcases hcase with ⟨l₁, h₁, l₂, h₂, hq, hp⟩ | ⟨l₁, h₁, h₂, hq, hp⟩ |
        ⟨l₂, h₂, h₁, hq, hp⟩
      · refine ⟨(l₂, l₁), ?_, hp, hq⟩
        rw [edgePairs, Option.mem_def.mp h₁, Option.mem_def.mp h₂]
        simp
      · refine ⟨(l₁, l₁), ?_, hp, hq⟩
        rw [edgePairs, Option.mem_def.mp h₁, h₂]
        simp
      · refine ⟨(l₂, l₂), ?_, hp, hq⟩
        rw [edgePairs, Option.mem_def.mp h₂, h₁]
        simp
  · rintro ⟨c, hc, v, hg, pr, hpr, hp, hq⟩
    rw [edgePairs] at hpr
    cases h₁ : c.lit₁ with
    | none =>
      cases h₂ : c.lit₂ with
      | none => rw [h₁, h₂] at hpr; simp at hpr
      | some l₂ =>
        rw [h₁, h₂] at hpr
        simp only [List.mem_singleton] at hpr
        subst hpr
        exact Or.inl ⟨c, hc, v, hg, Or.inr (Or.inr ⟨l₂, by simp [h₂], h₁, hp, hq⟩)⟩
    | some l₁ =>
      cases h₂ : c.lit₂ with
      | none =>
        rw [h₁, h₂] at hpr
        simp only [List.mem_singleton] at hpr
        subst hpr
        exact Or.inl ⟨c, hc, v, hg, Or.inr (Or.inl ⟨l₁, by simp [h₁], h₂, hp, hq⟩)⟩
      | some l₂ =>
        rw [h₁, h₂] at hpr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
        rcases hpr with rfl | rfl
        · exact Or.inl ⟨c, hc, v, hg, Or.inl ⟨l₁, by simp [h₁], l₂, by simp [h₂], hp, hq⟩⟩
        · exact Or.inr ⟨c, hc, v, hg, Or.inl ⟨l₁, by simp [h₁], l₂, by simp [h₂], hq, hp⟩⟩

/-- Some goal clause of the program fires: a clause with neither literal slot
filled whose guard holds. Such a clause is `guard → ⊥`, so the program is then
unsatisfiable, a case the abstract criterion does not cover. -/
def GoalFires (prog : KromProgram L B k) (A : Type) [L.Structure A] : Prop :=
  ∃ c ∈ prog, ∃ v : Fin k → A, c.guard.Realize v ∧ c.lit₁ = none ∧ c.lit₂ = none

/-- An assignment satisfies the program iff it satisfies the 2-CNF and no goal
clause fires. -/
theorem holds_iff_satisfies (prog : KromProgram L B k) (ν : KromAtom B A → Prop) :
    prog.Holds (toAssign ν) ↔ TwoCnf.Satisfies (clauseRel prog) ν ∧ ¬GoalFires prog A := by
  constructor
  · intro h
    constructor
    · rintro p q ⟨c, hc, v, hg, hcase⟩
      have hcl := h v c hc hg
      rcases hcase with ⟨l₁, h₁, l₂, h₂, rfl, rfl⟩ | ⟨l₁, h₁, h₂, rfl, rfl⟩ |
        ⟨l₂, h₂, h₁, rfl, rfl⟩
      · rcases hcl with hs | hs
        · exact Or.inl ((holds_iff_litTrue l₁ ν v).mp
            (by obtain ⟨l, hl, hlH⟩ := KromLit.slotHolds_iff.mp hs
                exact eq_of_mem_option hl h₁ ▸ hlH))
        · exact Or.inr ((holds_iff_litTrue l₂ ν v).mp
            (by obtain ⟨l, hl, hlH⟩ := KromLit.slotHolds_iff.mp hs
                exact eq_of_mem_option hl h₂ ▸ hlH))
      · refine Or.inl ((holds_iff_litTrue l₁ ν v).mp ?_)
        rcases hcl with hs | hs
        · obtain ⟨l, hl, hlH⟩ := KromLit.slotHolds_iff.mp hs
          exact eq_of_mem_option hl h₁ ▸ hlH
        · rw [KromLit.slotHolds, h₂] at hs
          exact hs.elim
      · refine Or.inl ((holds_iff_litTrue l₂ ν v).mp ?_)
        rcases hcl with hs | hs
        · rw [KromLit.slotHolds, h₁] at hs
          exact hs.elim
        · obtain ⟨l, hl, hlH⟩ := KromLit.slotHolds_iff.mp hs
          exact eq_of_mem_option hl h₂ ▸ hlH
    · rintro ⟨c, hc, v, hg, h₁, h₂⟩
      have hcl := h v c hc hg
      rw [KromLit.slotHolds, KromLit.slotHolds, h₁, h₂] at hcl
      rcases hcl with hs | hs
      exacts [hs.elim, hs.elim]
  · rintro ⟨hsat, hgoal⟩ v c hc hg
    -- a clause of the program: its slots, if any, give a clause of the 2-CNF
    cases h₁ : c.lit₁ with
    | none =>
      cases h₂ : c.lit₂ with
      | none => exact absurd ⟨c, hc, v, hg, h₁, h₂⟩ hgoal
      | some l₂ =>
        refine Or.inr ?_
        refine KromLit.slotHolds_iff.mpr ⟨l₂, by simp, ?_⟩
        refine (holds_iff_litTrue l₂ ν v).mpr ?_
        have : clauseRel prog (litOf l₂ v) (litOf l₂ v) :=
          ⟨c, hc, v, hg, Or.inr (Or.inr ⟨l₂, by simp [h₂], h₁, rfl, rfl⟩)⟩
        rcases hsat _ _ this with h | h
        exacts [h, h]
    | some l₁ =>
      cases h₂ : c.lit₂ with
      | none =>
        refine Or.inl ?_
        refine KromLit.slotHolds_iff.mpr ⟨l₁, by simp, ?_⟩
        refine (holds_iff_litTrue l₁ ν v).mpr ?_
        have : clauseRel prog (litOf l₁ v) (litOf l₁ v) :=
          ⟨c, hc, v, hg, Or.inr (Or.inl ⟨l₁, by simp [h₁], h₂, rfl, rfl⟩)⟩
        rcases hsat _ _ this with h | h
        exacts [h, h]
      | some l₂ =>
        have hcl : clauseRel prog (litOf l₁ v) (litOf l₂ v) :=
          ⟨c, hc, v, hg, Or.inl ⟨l₁, by simp [h₁], l₂, by simp [h₂], rfl, rfl⟩⟩
        rcases hsat _ _ hcl with h | h
        · exact Or.inl (KromLit.slotHolds_iff.mpr
            ⟨l₁, by simp, (holds_iff_litTrue l₁ ν v).mpr h⟩)
        · exact Or.inr (KromLit.slotHolds_iff.mpr
            ⟨l₂, by simp, (holds_iff_litTrue l₂ ν v).mpr h⟩)

variable [Finite A]

/-- **The criterion for a Krom program**: it is satisfiable exactly when no
goal clause fires and no literal of its implication graph reaches its own
negation and back. -/
theorem exists_holds_iff (prog : KromProgram L B k) :
    (∃ ρ : B.Assignment A, prog.Holds ρ) ↔
      ¬GoalFires prog A ∧
        ∀ p : TwoCnf.Lit (KromAtom B A),
          ¬(TwoCnf.Reach (clauseRel prog) p (TwoCnf.neg p) ∧
            TwoCnf.Reach (clauseRel prog) (TwoCnf.neg p) p) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hsat, hgoal⟩ := (holds_iff_satisfies prog (ofAssign ρ)).mp
      (by rwa [toAssign_ofAssign])
    exact ⟨hgoal, fun p => TwoCnf.no_bad_cycle_of_satisfies _ hsat p⟩
  · rintro ⟨hgoal, hcyc⟩
    obtain ⟨ν, hν⟩ := TwoCnf.exists_satisfies_of_no_bad_cycle (Cl := clauseRel prog)
      fun x s => hcyc (x, s)
    exact ⟨toAssign ν, (holds_iff_satisfies prog ν).mpr ⟨hν, hgoal⟩⟩

end Program

end KromImpl

end DescriptiveComplexity
