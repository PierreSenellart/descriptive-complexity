/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Tactic.FinCases
import FOReduction.Complexity
import FOReduction.SecondOrder

/-!
# SAT: propositional satisfiability

The problem SAT, as a decision problem on first-order structures. A CNF
formula is a `FirstOrder.Language.sat`-structure: elements are clauses and
propositional variables, `satIsClause c` distinguishes the clauses, and
`satPosIn c x` / `satNegIn c x` say that the literal `x` / `¬x` occurs in
clause `c`. `FirstOrder.Satisfiable` is the usual satisfiability, and
`FirstOrder.SAT` the bundled decision problem.

SAT is the archetypical NP-complete problem: this is the Cook–Levin theorem,
assumed here as the axiom `FirstOrder.SAT_NP_complete` (see
`FOReduction.Complexity` for the axiomatic setting; a statement about finite
CNF structures only). Other problems' NP-completeness proofs derive from it
through first-order reductions; see e.g.
`FOReduction.Problems.ThreeColorability`.
-/

namespace FirstOrder

open Language Structure

namespace Language

/-- Relation symbols of the language of CNF instances. -/
inductive satRel : ℕ → Type
  /-- `isClause c`: the element `c` is a clause. -/
  | isClause : satRel 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : satRel 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : satRel 2
  deriving DecidableEq

/-- The relational language of CNF instances: a unary predicate singling out
clauses, and two binary predicates for positive and negative occurrences of a
variable in a clause. -/
protected def sat : Language :=
  ⟨fun _ => Empty, satRel⟩
  deriving IsRelational

/-- The symbol for "is a clause". -/
abbrev satIsClause : Language.sat.Relations 1 := .isClause

/-- The symbol for "occurs positively in". -/
abbrev satPosIn : Language.sat.Relations 2 := .posIn

/-- The symbol for "occurs negatively in". -/
abbrev satNegIn : Language.sat.Relations 2 := .negIn

end Language

section Sat

variable (A : Type) [Language.sat.Structure A]

/-- A `Language.sat`-structure is satisfiable if some assignment of truth
values to its elements makes every clause contain a true literal. (Elements
that are not variables of the CNF formula may be assigned arbitrarily; they are
harmless since no clause mentions them.) -/
def Satisfiable : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)

end Sat

section Iso

private theorem comp_vec₁ {A B : Type} (f : A → B) (a : A) : f ∘ ![a] = ![f a] := by
  funext j
  fin_cases j
  simp

private theorem comp_vec₂ {A B : Type} (f : A → B) (a b : A) : f ∘ ![a, b] = ![f a, f b] := by
  funext j
  fin_cases j <;> simp

private theorem satisfiable_of_iso {A B : Type} [Language.sat.Structure A]
    [Language.sat.Structure B] (e : A ≃[Language.sat] B) (h : Satisfiable A) :
    Satisfiable B := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  have hc' : RelMap satIsClause ![e.symm c] := by
    have h' := StrongHomClass.map_rel e.symm satIsClause ![c]
    rw [comp_vec₁] at h'
    exact h'.mpr hc
  obtain ⟨x, hx⟩ := hν (e.symm c) hc'
  refine ⟨e x, ?_⟩
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · refine Or.inl ⟨?_, by simpa using hT⟩
    have h' := (StrongHomClass.map_rel e satPosIn ![e.symm c, x]).mpr hp
    rw [comp_vec₂] at h'
    simpa using h'
  · refine Or.inr ⟨?_, by simpa using hT⟩
    have h' := (StrongHomClass.map_rel e satNegIn ![e.symm c, x]).mpr hn
    rw [comp_vec₂] at h'
    simpa using h'

/-- Satisfiability is isomorphism-invariant. -/
theorem satisfiable_iso {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]
    (e : A ≃[Language.sat] B) : Satisfiable A ↔ Satisfiable B :=
  ⟨satisfiable_of_iso e, satisfiable_of_iso e.symm⟩

end Iso

/-- SAT, as a problem on `Language.sat`-structures. -/
def SAT : DecisionProblem Language.sat where
  Holds := fun A inst => @Satisfiable A inst
  iso_invariant := fun e => satisfiable_iso e

/-- The Cook–Levin theorem, as an axiom: SAT is the archetypical NP-complete
problem. Its NP-hardness holds even under (ordered) first-order reductions
(Immerman), consistently with the abstract closure properties.

Like every statement about complexity classes, this is a statement about the
*finite* CNF structures only: by `ComplexityClass.mem_congr_finite` and
`ComplexityClass.hard_congr_finite`, membership and hardness are unaffected
by the behavior of `SAT` on infinite structures. -/
axiom SAT_NP_complete : NP.Complete SAT

/-- SAT is in NP. -/
theorem sat_mem_NP : SAT ∈ NP :=
  SAT_NP_complete.mem

/-- SAT is NP-hard. -/
theorem sat_NP_hard : NP.Hard SAT :=
  SAT_NP_complete.hard

/-- The complement of SAT (essentially, propositional entailment of `⊥`) is
in coNP. -/
theorem sat_compl_mem_coNP : SATᶜ ∈ coNP :=
  (compl_mem_coNP_iff SAT).mpr sat_mem_NP

/-! ### SAT is existential second-order definable

The membership half of Fagin's characterization of SAT's NP-membership: SAT
is `Σ₁`-definable in the sense of `FOReduction.SecondOrder` — "there exists a
truth assignment (a unary relation) making every clause true", the inner part
being first-order. This is a first consistency check of the second-order
definability layer against a concrete problem. -/

section SigmaOne

open SOBlock

/-- The single existential block of the `Σ₁` definition of SAT: one unary
relation variable, the truth assignment. -/
def satAssignBlock : SOBlock where
  num := 1
  arity := fun _ => 1

/-- The symbol of the truth-assignment relation variable. -/
def satNuSym : satAssignBlock.lang.Relations 1 := ⟨⟨0, Nat.one_pos⟩, rfl⟩

/-- The vocabulary of the kernel: CNF instances together with the
truth-assignment relation variable. -/
abbrev satSOLang : Language := Language.sat.sum satAssignBlock.lang

/-- The symbol for "is a clause" in the kernel's vocabulary. -/
abbrev kIsClSym : satSOLang.Relations 1 := Sum.inl satIsClause

/-- The symbol for "occurs positively in" in the kernel's vocabulary. -/
abbrev kPosSym : satSOLang.Relations 2 := Sum.inl satPosIn

/-- The symbol for "occurs negatively in" in the kernel's vocabulary. -/
abbrev kNegSym : satSOLang.Relations 2 := Sum.inl satNegIn

/-- The truth-assignment symbol in the kernel's vocabulary. -/
abbrev kNuSym : satSOLang.Relations 1 := Sum.inr satNuSym

/-- The first-order kernel of the `Σ₁` definition of SAT: every clause
contains a true literal. The universally quantified variable is the clause,
the existentially quantified one the literal's variable. -/
noncomputable def satKernel : satSOLang.Sentence :=
  ((Relations.formula₁ kIsClSym (Term.var (Sum.inr 0))).imp
    (((Relations.formula₂ kPosSym (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓
        Relations.formula₁ kNuSym (Term.var (Sum.inr ()))) ⊔
      (Relations.formula₂ kNegSym (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓
        ∼(Relations.formula₁ kNuSym (Term.var (Sum.inr ()))))).iExs
      Unit)).iAlls (Fin 1)

/-- Realization of the kernel under an assignment of the truth-assignment
variable: every clause contains a true literal. -/
private theorem realize_satKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) satKernel) ↔
      ∀ c : A, RelMap satIsClause ![c] → ∃ x : A,
        (RelMap satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
          (RelMap satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) := by
  letI := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [satKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  constructor
  · intro h c hc
    obtain ⟨x, hx⟩ := h (fun _ => c) hc
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨x (), Or.inl ⟨hp, hT⟩⟩
    · exact ⟨x (), Or.inr ⟨hn, hT⟩⟩
  · intro h i hc
    obtain ⟨x, hx⟩ := h (i 0) hc
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨fun _ => x, Or.inl ⟨hp, hT⟩⟩
    · exact ⟨fun _ => x, Or.inr ⟨hn, hT⟩⟩

/-- **SAT is `Σ₁`-definable**: satisfiability of a CNF structure is expressed
by existentially quantifying a truth assignment and checking, in first-order
logic, that every clause contains a true literal. -/
theorem sat_sigmaSODefinable : SigmaSODefinable 1 SAT := by
  refine ⟨[satAssignBlock], rfl, satKernel, ?_⟩
  intro A _ _
  constructor
  · rintro ⟨ν, hν⟩
    exact ⟨fun _ x => ν (x ⟨0, Nat.one_pos⟩),
      (realize_satKernel _).mpr fun c hc => hν c hc⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨fun a => ρ satNuSym.1 fun _ => a, fun c hc => (realize_satKernel ρ).mp hρ c hc⟩

end SigmaOne

end FirstOrder
