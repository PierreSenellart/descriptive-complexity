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

The program is the general form of the one that defines UNREACH in
`DescriptiveComplexity.Problems.Reachability`. Guess the set `U` of *nodes* from which
an accepting node is reachable; a node being a mode together with a `k`-tuple,
that set is one `k`-ary relation variable per mode – the block's index type is
the specification's mode type. The clauses run over `2k` universally quantified
first-order variables, the first `k` holding the tuple `x̄` of the current node
and the last `k` the tuple `ȳ` of the next one:

```
                   tgt_p(x̄) → U_p(x̄)              (one clause per mode `p`)
  step_{p,q}(x̄, ȳ)          → ¬U_q(ȳ) ∨ U_p(x̄)   (one per pair of modes)
                   src_p(x̄) → ¬U_p(x̄)             (one clause per mode `p`)
```

All guards are the specification's own first-order formulas, relabeled along
the two halves of `Fin (k + k)`; the middle family is the only one with two
literals, and it is what makes the program Krom rather than Horn.

Correctness is the argument the concrete case already used, with nodes in place
of vertices: the witness is `U = {a | some accepting node is reachable from
a}`, and conversely a set containing the accepting nodes and closed under
predecessors contains every node from which one is reachable, so a starting
node could not be excluded if the structure were accepted.

**This is the direction that is free.** The converse – expressing reachability
itself in the Krom fragment – is Immerman–Szelepcsényi, proved through FO(TC)
in `DescriptiveComplexity.ImmermanSzelepcsenyi`; see also the discussion in
`DescriptiveComplexity.LogSpace`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

namespace TCKrom

variable {L : Language.{0, 0}}

/-! ### The block, the halves, and the modes -/

/-- The block of the Krom program: one `k`-ary relation variable per mode,
together holding the set of nodes from which an accepting node is reachable.
An `abbrev`, so that the arity reduces where tuples are applied. -/
abbrev uBlock (spec : TCSpec L) : SOBlock where
  ι := spec.Mode
  arity := fun _ => spec.k

/-- The first half of the `2k` universally quantified variables: the tuple `x̄`
of the current node. -/
abbrev fst (k : ℕ) : Fin k → Fin (k + k) := Fin.castAdd k

/-- The second half of the `2k` universally quantified variables: the tuple `ȳ`
of the next node. -/
abbrev snd (k : ℕ) : Fin k → Fin (k + k) := Fin.natAdd k

variable (spec : TCSpec L)

/-- The atom `U_m` at one of the two halves. -/
def uAtom (m : spec.Mode) (half : Fin spec.k → Fin (spec.k + spec.k)) :
    SOAtom (uBlock spec) (spec.k + spec.k) where
  idx := m
  args := half

/-- The literal `U_m` at one of the two halves, positive or negated. -/
def uLit (m : spec.Mode) (half : Fin spec.k → Fin (spec.k + spec.k)) (pos : Bool) :
    KromLit (uBlock spec) (spec.k + spec.k) where
  atom := uAtom spec m half
  positive := pos

open Classical in
/-- The modes, as a list: the clause families are instantiated at each of
them. -/
noncomputable def allModes : List spec.Mode :=
  letI : Fintype spec.Mode := Fintype.ofFinite spec.Mode
  (Finset.univ : Finset spec.Mode).toList

open Classical in
theorem mem_allModes (m : spec.Mode) : m ∈ allModes spec := by
  let : Fintype spec.Mode := Fintype.ofFinite spec.Mode
  exact Finset.mem_toList.mpr (Finset.mem_univ m)

/-! ### The clauses -/

/-- An accepting node belongs to `U`. -/
noncomputable def tgtClause (m : spec.Mode) :
    KromClause (L.sum Language.order) (uBlock spec) (spec.k + spec.k) where
  guard := (spec.tgt m).relabel (fst spec.k)
  lit₁ := some (uLit spec m (fst spec.k) true)
  lit₂ := none

/-- `U` is closed under predecessors: a step into `U` starts in `U`. -/
noncomputable def stepClause (p q : spec.Mode) :
    KromClause (L.sum Language.order) (uBlock spec) (spec.k + spec.k) where
  guard := (spec.step p q).relabel (Sum.elim (fst spec.k) (snd spec.k))
  lit₁ := some (uLit spec q (snd spec.k) false)
  lit₂ := some (uLit spec p (fst spec.k) true)

/-- No starting node belongs to `U`. -/
noncomputable def srcClause (m : spec.Mode) :
    KromClause (L.sum Language.order) (uBlock spec) (spec.k + spec.k) where
  guard := (spec.src m).relabel (fst spec.k)
  lit₁ := some (uLit spec m (fst spec.k) false)
  lit₂ := none

/-- The Krom program defining the complement of an FO(TC) definable
problem. -/
noncomputable def program :
    KromProgram (L.sum Language.order) (uBlock spec) (spec.k + spec.k) :=
  (allModes spec).map (tgtClause spec) ++
    (allModes spec).flatMap (fun p => (allModes spec).map (stepClause spec p)) ++
    (allModes spec).map (srcClause spec)

theorem tgtClause_mem (m : spec.Mode) : tgtClause spec m ∈ program spec := by
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
  exact List.mem_map.mpr ⟨m, mem_allModes spec m, rfl⟩

theorem stepClause_mem (p q : spec.Mode) : stepClause spec p q ∈ program spec := by
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
  exact List.mem_flatMap.mpr ⟨p, mem_allModes spec p,
    List.mem_map.mpr ⟨q, mem_allModes spec q, rfl⟩⟩

theorem srcClause_mem (m : spec.Mode) : srcClause spec m ∈ program spec := by
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_map.mpr ⟨m, mem_allModes spec m, rfl⟩

/-- The clauses of the program are exactly the three families. -/
theorem mem_program_iff
    {c : KromClause (L.sum Language.order) (uBlock spec) (spec.k + spec.k)} :
    c ∈ program spec ↔
      (∃ m, c = tgtClause spec m) ∨ (∃ p q, c = stepClause spec p q) ∨
        ∃ m, c = srcClause spec m := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨m, -, rfl⟩ := List.mem_map.mp h
        exact Or.inl ⟨m, rfl⟩
      · obtain ⟨p, -, h⟩ := List.mem_flatMap.mp h
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp h
        exact Or.inr (Or.inl ⟨p, q, rfl⟩)
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp h
      exact Or.inr (Or.inr ⟨m, rfl⟩)
  · rintro (⟨m, rfl⟩ | ⟨p, q, rfl⟩ | ⟨m, rfl⟩)
    exacts [tgtClause_mem spec m, stepClause_mem spec p q, srcClause_mem spec m]

/-! ### Semantics -/

section Semantics

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The set of nodes guessed by an assignment of the block. -/
def URel (ρ : (uBlock spec).Assignment A) (a : spec.Node A) : Prop := ρ a.1 a.2

/-- The valuation of the `2k` variables holding the tuples of two nodes. -/
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
theorem uLit_holds_true (ρ : (uBlock spec).Assignment A) (m : spec.Mode)
    (half : Fin spec.k → Fin (spec.k + spec.k)) (v : Fin (spec.k + spec.k) → A) :
    (uLit spec m half true).Holds ρ v ↔ URel spec ρ (m, fun j => v (half j)) :=
  Iff.rfl

omit [L.Structure A] [LinearOrder A] in
theorem uLit_holds_false (ρ : (uBlock spec).Assignment A) (m : spec.Mode)
    (half : Fin spec.k → Fin (spec.k + spec.k)) (v : Fin (spec.k + spec.k) → A) :
    (uLit spec m half false).Holds ρ v ↔ ¬URel spec ρ (m, fun j => v (half j)) :=
  Iff.rfl

theorem realize_tgt_relabel (m : spec.Mode) (v : Fin (spec.k + spec.k) → A) :
    ((spec.tgt m).relabel (fst spec.k)).Realize v ↔
      spec.IsTgt (m, fun j => v (fst spec.k j)) :=
  Formula.realize_relabel

theorem realize_src_relabel (m : spec.Mode) (v : Fin (spec.k + spec.k) → A) :
    ((spec.src m).relabel (fst spec.k)).Realize v ↔
      spec.IsSrc (m, fun j => v (fst spec.k j)) :=
  Formula.realize_relabel

theorem realize_step_relabel (p q : spec.Mode) (v : Fin (spec.k + spec.k) → A) :
    ((spec.step p q).relabel (Sum.elim (fst spec.k) (snd spec.k))).Realize v ↔
      spec.Step (p, fun j => v (fst spec.k j)) (q, fun j => v (snd spec.k j)) := by
  rw [Formula.realize_relabel, TCSpec.Step]
  refine iff_of_eq (congrArg (spec.step p q).Realize (funext fun i => ?_))
  cases i <;> rfl

/-- What it means for an assignment to satisfy the program: the guessed set
contains the accepting nodes, is closed under predecessors, and avoids the
starting nodes. -/
theorem program_holds_iff (ρ : (uBlock spec).Assignment A) :
    (program spec).Holds ρ ↔
      (∀ a : spec.Node A, spec.IsTgt a → URel spec ρ a) ∧
      (∀ a b : spec.Node A, spec.Step a b → URel spec ρ b → URel spec ρ a) ∧
      (∀ a : spec.Node A, spec.IsSrc a → ¬URel spec ρ a) := by
  have e1 : ∀ x y : Fin spec.k → A, (fun j => pairVal spec x y (fst spec.k j)) = x :=
    fun x y => funext (pairVal_fst spec x y)
  have e2 : ∀ x y : Fin spec.k → A, (fun j => pairVal spec x y (snd spec.k j)) = y :=
    fun x y => funext (pairVal_snd spec x y)
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun a b hab hb => ?_, fun a ha hu => ?_⟩
    · have hg : (tgtClause spec a.1).guard.Realize (pairVal spec a.2 a.2) := by
        rw [tgtClause, realize_tgt_relabel, e1 a.2 a.2]
        exact ha
      have hcl := h (pairVal spec a.2 a.2) (tgtClause spec a.1) (tgtClause_mem spec a.1) hg
      simp only [tgtClause, KromLit.slotHolds, Option.elim_some, Option.elim_none,
        or_false] at hcl
      have hU := (uLit_holds_true spec ρ a.1 (fst spec.k) (pairVal spec a.2 a.2)).mp hcl
      rw [e1 a.2 a.2] at hU
      exact hU
    · have hg : (stepClause spec a.1 b.1).guard.Realize (pairVal spec a.2 b.2) := by
        rw [stepClause, realize_step_relabel, e1 a.2 b.2, e2 a.2 b.2]
        exact hab
      have hcl := h (pairVal spec a.2 b.2) (stepClause spec a.1 b.1)
        (stepClause_mem spec a.1 b.1) hg
      simp only [stepClause, KromLit.slotHolds, Option.elim_some] at hcl
      rcases hcl with hneg | hpos
      · have hU := (uLit_holds_false spec ρ b.1 (snd spec.k) (pairVal spec a.2 b.2)).mp hneg
        rw [e2 a.2 b.2] at hU
        exact absurd hb hU
      · have hU := (uLit_holds_true spec ρ a.1 (fst spec.k) (pairVal spec a.2 b.2)).mp hpos
        rw [e1 a.2 b.2] at hU
        exact hU
    · have hg : (srcClause spec a.1).guard.Realize (pairVal spec a.2 a.2) := by
        rw [srcClause, realize_src_relabel, e1 a.2 a.2]
        exact ha
      have hcl := h (pairVal spec a.2 a.2) (srcClause spec a.1) (srcClause_mem spec a.1) hg
      simp only [srcClause, KromLit.slotHolds, Option.elim_some, Option.elim_none,
        or_false] at hcl
      have hU := (uLit_holds_false spec ρ a.1 (fst spec.k) (pairVal spec a.2 a.2)).mp hcl
      rw [e1 a.2 a.2] at hU
      exact hU hu
  · rintro ⟨h1, h2, h3⟩ v c hc
    rcases (mem_program_iff spec).mp hc with ⟨m, rfl⟩ | ⟨p, q, rfl⟩ | ⟨m, rfl⟩
    · intro hg
      refine Or.inl ?_
      simp only [tgtClause, KromLit.slotHolds, Option.elim_some]
      exact (uLit_holds_true spec ρ m (fst spec.k) v).mpr
        (h1 _ ((realize_tgt_relabel spec m v).mp hg))
    · intro hg
      by_cases hy : URel spec ρ (q, fun j => v (snd spec.k j))
      · refine Or.inr ?_
        simp only [stepClause, KromLit.slotHolds, Option.elim_some]
        exact (uLit_holds_true spec ρ p (fst spec.k) v).mpr
          (h2 _ _ ((realize_step_relabel spec p q v).mp hg) hy)
      · refine Or.inl ?_
        simp only [stepClause, KromLit.slotHolds, Option.elim_some]
        exact (uLit_holds_false spec ρ q (snd spec.k) v).mpr hy
    · intro hg
      refine Or.inl ?_
      simp only [srcClause, KromLit.slotHolds, Option.elim_some]
      exact (uLit_holds_false spec ρ m (fst spec.k) v).mpr
        (h3 _ ((realize_src_relabel spec m v).mp hg))

/-- The set of nodes from which an accepting node is reachable: the witness of
the nontrivial direction. -/
def coReachAssign : (uBlock spec).Assignment A :=
  fun m x => ∃ w : spec.Node A, spec.IsTgt w ∧ spec.Reach (m, x) w

@[simp]
theorem uRel_coReachAssign (a : spec.Node A) :
    URel spec (coReachAssign spec) a ↔ ∃ w : spec.Node A, spec.IsTgt w ∧ spec.Reach a w :=
  Iff.rfl

/-- A set containing the accepting nodes and closed under predecessors contains
every node from which an accepting node is reachable. -/
theorem uRel_of_reach {ρ : (uBlock spec).Assignment A}
    (h2 : ∀ a b : spec.Node A, spec.Step a b → URel spec ρ b → URel spec ρ a)
    {a b : spec.Node A} (h : spec.Reach a b) : URel spec ρ b → URel spec ρ a := by
  induction h with
  | refl => exact id
  | @tail c d _ hcd ih => exact fun hd => ih (h2 _ _ hcd hd)

/-- **Correctness**: the program is satisfiable exactly when the structure is
*not* accepted. -/
theorem exists_holds_iff_not_accepts :
    (∃ ρ : (uBlock spec).Assignment A, (program spec).Holds ρ) ↔ ¬spec.Accepts A := by
  constructor
  · rintro ⟨ρ, hρ⟩ ⟨u, v, hu, hv, huv⟩
    obtain ⟨h1, h2, h3⟩ := (program_holds_iff spec ρ).mp hρ
    exact h3 u hu (uRel_of_reach spec h2 huv (h1 v hv))
  · intro h
    refine ⟨coReachAssign spec, (program_holds_iff spec _).mpr
      ⟨fun a ha => ⟨a, ha, Relation.ReflTransGen.refl⟩, fun a b hab hb => ?_,
        fun a ha hu => ?_⟩⟩
    · obtain ⟨w, hw, hpath⟩ := hb
      exact ⟨w, hw, Relation.ReflTransGen.head hab hpath⟩
    · obtain ⟨w, hw, hpath⟩ := hu
      exact h ⟨a, w, ha, hw, hpath⟩

end Semantics

end TCKrom

open TCKrom in
/-- **The complement of an FO(TC) definable problem is SO-Krom definable**:
guess the set of nodes from which an accepting node is reachable – one `k`-ary
relation variable per mode – close it under predecessors with the 2-clause
`¬U_q(ȳ) ∨ U_p(x̄)`, and forbid the starting nodes. This is the direction a
clausal fragment gives for free; the converse is Immerman–Szelepcsényi. -/
theorem SigmaSOKromDefinable.compl_of_tcDefinable {L : Language.{0, 0}}
    [L.IsRelational] {P : DecisionProblem L} (h : TCDefinable P) : SigmaSOKromDefinable Pᶜ := by
  obtain ⟨spec, hspec⟩ := h
  refine ⟨uBlock spec, spec.k + spec.k, program spec, ?_⟩
  intro A _ _ _ _
  exact (not_congr (hspec A)).trans (exists_holds_iff_not_accepts spec).symm

/-- **The complement of an FO(TC) definable problem is in NL.** -/
theorem mem_NL_compl_of_tcDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : TCDefinable P) : Pᶜ ∈ NL :=
  (mem_NL_iff Pᶜ).mpr (SigmaSOKromDefinable.compl_of_tcDefinable h)

end DescriptiveComplexity
