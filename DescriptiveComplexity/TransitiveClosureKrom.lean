/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosure
import DescriptiveComplexity.SecondOrderKrom
import DescriptiveComplexity.LogSpace

/-!
# From FO(TC) to the Krom fragment, through the complement

The complement of an FO(TC) definable problem is SO-Krom definable
(`DescriptiveComplexity.SigmaSOKromDefinable.compl_of_tcDefinable`), hence in
`DescriptiveComplexity.NL`.

The program is the arity-`k` generalization of the one that defines UNREACH in
`DescriptiveComplexity.Problems.Reachability`. Guess the set `U` of tuples from which
an accepting tuple is reachable, as a single `k`-ary relation variable, and
constrain it by three clauses over `2k` universally quantified first-order
variables – the first `k` holding the tuple `x̄`, the last `k` the tuple `ȳ`:

```
          tgt(x̄) → U(x̄)
  step(x̄, ȳ)     → ¬U(ȳ) ∨ U(x̄)
          src(x̄) → ¬U(x̄)
```

All three guards are the specification's own first-order formulas, relabelled
along the two halves of `Fin (k + k)`; the middle clause is the only one with
two literals, and it is what makes the program Krom rather than Horn.

Correctness is the argument the concrete case already used, with tuples in
place of vertices: the witness is `U = {x̄ | some accepting tuple is reachable
from x̄}`, and conversely a set containing the accepting tuples and closed under
predecessors contains every tuple from which one is reachable, so a starting
tuple could not be excluded if the structure were accepted.

**This is the direction that is free.** The converse – expressing reachability
itself in the Krom fragment – is Immerman–Szelepcsényi; see `ROADMAP.md` §4 and
the discussion in `DescriptiveComplexity.LogSpace`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

namespace TCKrom

variable {L : Language.{0, 0}}

/-! ### The block, the halves, and the guards -/

/-- The block of the Krom program: one `k`-ary relation variable, the set of
tuples from which an accepting tuple is reachable. An `abbrev`, so that the
arity reduces where tuples are applied. -/
abbrev uBlock (k : ℕ) : SOBlock where
  ι := Unit
  arity := fun _ => k

/-- The first half of the `2k` universally quantified variables: the tuple
`x̄`. -/
abbrev fst (k : ℕ) : Fin k → Fin (k + k) := Fin.castAdd k

/-- The second half of the `2k` universally quantified variables: the tuple
`ȳ`. -/
abbrev snd (k : ℕ) : Fin k → Fin (k + k) := Fin.natAdd k

/-- The atom `U` at one of the two halves. -/
def uAtom (k : ℕ) (half : Fin k → Fin (k + k)) : SOAtom (uBlock k) (k + k) where
  idx := ()
  args := half

/-- The literal `U` at one of the two halves, positive or negated. -/
def uLit (k : ℕ) (half : Fin k → Fin (k + k)) (pos : Bool) : KromLit (uBlock k) (k + k) where
  atom := uAtom k half
  positive := pos

variable (spec : TCSpec L)

/-- An accepting tuple belongs to `U`. -/
noncomputable def tgtClause :
    KromClause (L.sum Language.order) (uBlock spec.k) (spec.k + spec.k) where
  guard := spec.tgt.relabel (fst spec.k)
  lit₁ := some (uLit spec.k (fst spec.k) true)
  lit₂ := none

/-- `U` is closed under predecessors: a step into `U` starts in `U`. -/
noncomputable def stepClause :
    KromClause (L.sum Language.order) (uBlock spec.k) (spec.k + spec.k) where
  guard := spec.step.relabel (Sum.elim (fst spec.k) (snd spec.k))
  lit₁ := some (uLit spec.k (snd spec.k) false)
  lit₂ := some (uLit spec.k (fst spec.k) true)

/-- No starting tuple belongs to `U`. -/
noncomputable def srcClause :
    KromClause (L.sum Language.order) (uBlock spec.k) (spec.k + spec.k) where
  guard := spec.src.relabel (fst spec.k)
  lit₁ := some (uLit spec.k (fst spec.k) false)
  lit₂ := none

/-- The Krom program defining the complement of an FO(TC) definable
problem. -/
noncomputable def program :
    KromProgram (L.sum Language.order) (uBlock spec.k) (spec.k + spec.k) :=
  [tgtClause spec, stepClause spec, srcClause spec]

theorem tgtClause_mem : tgtClause spec ∈ program spec := by simp [program]

theorem stepClause_mem : stepClause spec ∈ program spec := by simp [program]

theorem srcClause_mem : srcClause spec ∈ program spec := by simp [program]

/-! ### Semantics -/

section Semantics

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The set guessed by an assignment of the block. -/
def URel (ρ : (uBlock spec.k).Assignment A) (x : Fin spec.k → A) : Prop := ρ () x

/-- The valuation of the `2k` variables holding the two tuples `x̄` and `ȳ`. -/
def pairVal (x y : Fin spec.k → A) : Fin (spec.k + spec.k) → A :=
  Fin.addCases x y

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem pairVal_fst (x y : Fin spec.k → A) (j : Fin spec.k) :
    pairVal spec x y (fst spec.k j) = x j :=
  Fin.addCases_left _

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem pairVal_snd (x y : Fin spec.k → A) (j : Fin spec.k) :
    pairVal spec x y (snd spec.k j) = y j :=
  Fin.addCases_right _

omit [L.Structure A] [LinearOrder A] in
theorem uLit_holds_true (ρ : (uBlock spec.k).Assignment A)
    (half : Fin spec.k → Fin (spec.k + spec.k)) (v : Fin (spec.k + spec.k) → A) :
    (uLit spec.k half true).Holds ρ v ↔ URel spec ρ fun j => v (half j) :=
  Iff.rfl

omit [L.Structure A] [LinearOrder A] in
theorem uLit_holds_false (ρ : (uBlock spec.k).Assignment A)
    (half : Fin spec.k → Fin (spec.k + spec.k)) (v : Fin (spec.k + spec.k) → A) :
    (uLit spec.k half false).Holds ρ v ↔ ¬URel spec ρ fun j => v (half j) :=
  Iff.rfl

theorem realize_tgt_relabel (v : Fin (spec.k + spec.k) → A) :
    (spec.tgt.relabel (fst spec.k)).Realize v ↔ spec.tgt.Realize fun j => v (fst spec.k j) :=
  Formula.realize_relabel

theorem realize_src_relabel (v : Fin (spec.k + spec.k) → A) :
    (spec.src.relabel (fst spec.k)).Realize v ↔ spec.src.Realize fun j => v (fst spec.k j) :=
  Formula.realize_relabel

theorem realize_step_relabel (v : Fin (spec.k + spec.k) → A) :
    (spec.step.relabel (Sum.elim (fst spec.k) (snd spec.k))).Realize v ↔
      spec.Step (fun j => v (fst spec.k j)) fun j => v (snd spec.k j) := by
  rw [Formula.realize_relabel, TCSpec.Step]
  refine iff_of_eq (congrArg spec.step.Realize (funext fun i => ?_))
  cases i <;> rfl

/-- What it means for an assignment to satisfy the program: the guessed set
contains the accepting tuples, is closed under predecessors, and avoids the
starting tuples. -/
theorem program_holds_iff (ρ : (uBlock spec.k).Assignment A) :
    (program spec).Holds ρ ↔
      (∀ x : Fin spec.k → A, spec.tgt.Realize x → URel spec ρ x) ∧
      (∀ x y : Fin spec.k → A, spec.Step x y → URel spec ρ y → URel spec ρ x) ∧
      (∀ x : Fin spec.k → A, spec.src.Realize x → ¬URel spec ρ x) := by
  have e1 : ∀ x y : Fin spec.k → A, (fun j => pairVal spec x y (fst spec.k j)) = x :=
    fun x y => funext (pairVal_fst spec x y)
  have e2 : ∀ x y : Fin spec.k → A, (fun j => pairVal spec x y (snd spec.k j)) = y :=
    fun x y => funext (pairVal_snd spec x y)
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x y hxy hy => ?_, fun x hx hu => ?_⟩
    · have hg : (tgtClause spec).guard.Realize (pairVal spec x x) := by
        rw [tgtClause, realize_tgt_relabel, e1 x x]
        exact hx
      have hcl := h (pairVal spec x x) (tgtClause spec) (tgtClause_mem spec) hg
      simp only [tgtClause, KromLit.slotHolds, Option.elim_some, Option.elim_none,
        or_false] at hcl
      have hU := (uLit_holds_true spec ρ (fst spec.k) (pairVal spec x x)).mp hcl
      rwa [e1 x x] at hU
    · have hg : (stepClause spec).guard.Realize (pairVal spec x y) := by
        rw [stepClause, realize_step_relabel, e1 x y, e2 x y]
        exact hxy
      have hcl := h (pairVal spec x y) (stepClause spec) (stepClause_mem spec) hg
      simp only [stepClause, KromLit.slotHolds, Option.elim_some] at hcl
      rcases hcl with hneg | hpos
      · have hU := (uLit_holds_false spec ρ (snd spec.k) (pairVal spec x y)).mp hneg
        rw [e2 x y] at hU
        exact absurd hy hU
      · have hU := (uLit_holds_true spec ρ (fst spec.k) (pairVal spec x y)).mp hpos
        rwa [e1 x y] at hU
    · have hg : (srcClause spec).guard.Realize (pairVal spec x x) := by
        rw [srcClause, realize_src_relabel, e1 x x]
        exact hx
      have hcl := h (pairVal spec x x) (srcClause spec) (srcClause_mem spec) hg
      simp only [srcClause, KromLit.slotHolds, Option.elim_some, Option.elim_none,
        or_false] at hcl
      have hU := (uLit_holds_false spec ρ (fst spec.k) (pairVal spec x x)).mp hcl
      rw [e1 x x] at hU
      exact hU hu
  · rintro ⟨h1, h2, h3⟩ v c hc
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · intro hg
      refine Or.inl ?_
      simp only [tgtClause, KromLit.slotHolds, Option.elim_some]
      exact (uLit_holds_true spec ρ (fst spec.k) v).mpr
        (h1 _ ((realize_tgt_relabel spec v).mp hg))
    · intro hg
      by_cases hy : URel spec ρ fun j => v (snd spec.k j)
      · refine Or.inr ?_
        simp only [stepClause, KromLit.slotHolds, Option.elim_some]
        exact (uLit_holds_true spec ρ (fst spec.k) v).mpr
          (h2 _ _ ((realize_step_relabel spec v).mp hg) hy)
      · refine Or.inl ?_
        simp only [stepClause, KromLit.slotHolds, Option.elim_some]
        exact (uLit_holds_false spec ρ (snd spec.k) v).mpr hy
    · intro hg
      refine Or.inl ?_
      simp only [srcClause, KromLit.slotHolds, Option.elim_some]
      exact (uLit_holds_false spec ρ (fst spec.k) v).mpr
        (h3 _ ((realize_src_relabel spec v).mp hg))

/-- The set of tuples from which an accepting tuple is reachable: the witness
of the nontrivial direction. -/
def coReachAssign : (uBlock spec.k).Assignment A :=
  fun _ x => ∃ w : Fin spec.k → A, spec.tgt.Realize w ∧ spec.Reach x w

@[simp]
theorem uRel_coReachAssign (x : Fin spec.k → A) :
    URel spec (coReachAssign spec) x ↔
      ∃ w : Fin spec.k → A, spec.tgt.Realize w ∧ spec.Reach x w :=
  Iff.rfl

/-- A set containing the accepting tuples and closed under predecessors
contains every tuple from which an accepting tuple is reachable. -/
theorem uRel_of_reach {ρ : (uBlock spec.k).Assignment A}
    (h2 : ∀ x y : Fin spec.k → A, spec.Step x y → URel spec ρ y → URel spec ρ x)
    {x y : Fin spec.k → A} (h : spec.Reach x y) : URel spec ρ y → URel spec ρ x := by
  induction h with
  | refl => exact id
  | @tail b c _ hbc ih => exact fun hc => ih (h2 _ _ hbc hc)

/-- **Correctness**: the program is satisfiable exactly when the structure is
*not* accepted. -/
theorem exists_holds_iff_not_accepts :
    (∃ ρ : (uBlock spec.k).Assignment A, (program spec).Holds ρ) ↔ ¬spec.Accepts A := by
  constructor
  · rintro ⟨ρ, hρ⟩ ⟨u, v, hu, hv, huv⟩
    obtain ⟨h1, h2, h3⟩ := (program_holds_iff spec ρ).mp hρ
    exact h3 u hu (uRel_of_reach spec h2 huv (h1 v hv))
  · intro h
    refine ⟨coReachAssign spec, (program_holds_iff spec _).mpr
      ⟨fun x hx => ⟨x, hx, Relation.ReflTransGen.refl⟩, fun x y hxy hy => ?_, fun x hx hu => ?_⟩⟩
    · obtain ⟨w, hw, hpath⟩ := hy
      exact ⟨w, hw, Relation.ReflTransGen.head hxy hpath⟩
    · obtain ⟨w, hw, hpath⟩ := hu
      exact h ⟨x, w, hx, hw, hpath⟩

end Semantics

end TCKrom

open TCKrom in
/-- **The complement of an FO(TC) definable problem is SO-Krom definable**:
guess the set of tuples from which an accepting tuple is reachable, close it
under predecessors with the 2-clause `¬U(ȳ) ∨ U(x̄)`, and forbid the starting
tuples. This is the direction a clausal fragment gives for free; the converse
is Immerman–Szelepcsényi. -/
theorem SigmaSOKromDefinable.compl_of_tcDefinable {L : Language.{0, 0}}
    {P : DecisionProblem L} (h : TCDefinable P) : SigmaSOKromDefinable Pᶜ := by
  obtain ⟨spec, hspec⟩ := h
  refine ⟨uBlock spec.k, spec.k + spec.k, program spec, ?_⟩
  intro A _ _ _ _
  exact (not_congr (hspec A)).trans (exists_holds_iff_not_accepts spec).symm

/-- **The complement of an FO(TC) definable problem is in NL.** -/
theorem mem_NL_compl_of_tcDefinable {L : Language.{0, 0}} {P : DecisionProblem L}
    (h : TCDefinable P) : Pᶜ ∈ NL :=
  (mem_NL_iff Pᶜ).mpr (SigmaSOKromDefinable.compl_of_tcDefinable h)

end DescriptiveComplexity
