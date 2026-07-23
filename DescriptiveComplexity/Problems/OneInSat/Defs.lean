/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat
import DescriptiveComplexity.OccurrenceOrder

/-!
# 1-in-SAT: the problem, and its membership in NP

EXACTLY-ONE SATISFIABILITY: is there a truth assignment giving every clause
*exactly one* true literal? Like NAE-SAT, it lives on the vocabulary
`FirstOrder.Language.sat` unchanged and only its notion of satisfaction differs
(`DescriptiveComplexity.OneInProper`), so this adds a problem rather than a language.
It is the second Schaefer-style variant of satisfiability
([Schaefer 1978][schaefer1978complexity]) in the catalog.

Its value is as a reduction *source*, and specifically for Exact Cover: a
1-in-SAT instance becomes an exact cover with no counting and no gadget at
all, one set per literal `(x, s)` gathering `x` itself and the clauses where
`(x, s)` occurs. Covering the element `x` exactly once picks exactly one of
the two literals of `x` – an assignment – and covering a clause exactly once
*is* exactly-one satisfaction. That works at any clause width, which is why
the catalog wants unrestricted 1-in-SAT rather than a width-three restriction.

Membership reuses SAT's kernel (`DescriptiveComplexity.realize_satKernel`, “every clause
has a true literal”) and adds uniqueness, as three clauses – one per pattern
of signs, the mixed pattern being simply forbidden.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock SatOcc

/-! ### The problem -/

section Semantics

variable {A : Type} [Language.sat.Structure A]

/-- An assignment is *exactly-one proper* when every clause has exactly one
true literal occurrence. -/
def OneInProper (ν : A → Prop) : Prop :=
  ∀ c : A, IsCl c → ∃ x s, OccIn c x s ∧ LitTrue ν x s ∧
    ∀ y t, OccIn c y t → LitTrue ν y t → y = x ∧ t = s

end Semantics

section Problem

variable (A : Type) [Language.sat.Structure A]

/-- A `Language.sat`-structure is exactly-one satisfiable if some assignment
gives every clause exactly one true literal. -/
def OneInSatisfiable : Prop := ∃ ν : A → Prop, OneInProper ν

end Problem

section Iso

variable {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]

/-- Isomorphisms preserve literal occurrences. -/
theorem occIn_iso (e : A ≃[Language.sat] B) {c x : A} {s : Bool} :
    OccIn c x s ↔ OccIn (e c) (e x) s := by
  cases s with
  | false => exact and_congr (relMap_equiv₁ e satIsClause c) (relMap_equiv₂ e satNegIn c x)
  | true => exact and_congr (relMap_equiv₁ e satIsClause c) (relMap_equiv₂ e satPosIn c x)

private theorem oneInSatisfiable_of_iso (e : A ≃[Language.sat] B)
    (h : OneInSatisfiable A) : OneInSatisfiable B := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨x, s, hx, hT, huniq⟩ :=
    hν (e.symm c) ((relMap_equiv₁ e.symm satIsClause c).mp hc)
  refine ⟨e x, s, by simpa using (occIn_iso e).mp hx, ?_, fun y t hy hTy => ?_⟩
  · cases s <;> simpa [LitTrue] using hT
  · obtain ⟨h1, h2⟩ := huniq (e.symm y) t ((occIn_iso e.symm).mp hy)
      (by cases t <;> simpa [LitTrue] using hTy)
    exact ⟨by simpa using congrArg e h1, h2⟩

/-- Exactly-one satisfiability is isomorphism-invariant. -/
theorem oneInSatisfiable_iso (e : A ≃[Language.sat] B) :
    OneInSatisfiable A ↔ OneInSatisfiable B :=
  ⟨oneInSatisfiable_of_iso e, oneInSatisfiable_of_iso e.symm⟩

end Iso

/-- 1-in-SAT, as a problem on CNF instances: is there an assignment giving
every clause exactly one true literal? -/
def OneInSAT : DecisionProblem Language.sat where
  Holds := fun A inst => @OneInSatisfiable A inst
  iso_invariant := fun e => oneInSatisfiable_iso e

/-! ### Membership -/

section SigmaOne

/-- Kernel conjunct: a clause has at most one true *positive* literal. -/
private noncomputable def oiPPClause : satSOLang.Sentence :=
  ((Relations.formula₁ kIsClSym (Term.var (Sum.inr 0)) ⊓
      ((Relations.formula₂ kPosSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
          Relations.formula₁ kNuSym (Term.var (Sum.inr 1))) ⊓
        (Relations.formula₂ kPosSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
          Relations.formula₁ kNuSym (Term.var (Sum.inr 2))))).imp
    (Term.equal (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel conjunct: a clause has at most one true *negative* literal. -/
private noncomputable def oiNNClause : satSOLang.Sentence :=
  ((Relations.formula₁ kIsClSym (Term.var (Sum.inr 0)) ⊓
      ((Relations.formula₂ kNegSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
          ∼(Relations.formula₁ kNuSym (Term.var (Sum.inr 1)))) ⊓
        (Relations.formula₂ kNegSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
          ∼(Relations.formula₁ kNuSym (Term.var (Sum.inr 2)))))).imp
    (Term.equal (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel conjunct: a clause has no true positive *and* true negative
literal. -/
private noncomputable def oiPNClause : satSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    (∼(Relations.formula₁ kIsClSym (Term.var (Sum.inr 0)) ⊓
      ((Relations.formula₂ kPosSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
          Relations.formula₁ kNuSym (Term.var (Sum.inr 1))) ⊓
        (Relations.formula₂ kNegSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
          ∼(Relations.formula₁ kNuSym (Term.var (Sum.inr 2)))))))

/-- The first-order kernel of the `Σ₁` definition of 1-in-SAT: SAT's kernel
together with the three uniqueness clauses. -/
noncomputable def oneInKernel : satSOLang.Sentence :=
  satKernel ⊓ (oiPPClause ⊓ (oiNNClause ⊓ oiPNClause))

section Realize

variable {A : Type} [Language.sat.Structure A] (ρ : satAssignBlock.Assignment A)

private theorem realize_oiPPClause :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oiPPClause) ↔
      ∀ c x y : A, IsCl c → PosIn c x → (ρ satNuSym.1 fun _ => x) → PosIn c y →
        (ρ satNuSym.1 fun _ => y) → x = y := by
  letI := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [oiPPClause]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl,
    hsub]
  exact ⟨fun h c x y h1 h2 h3 h4 h5 => h ![c, x, y] ⟨h1, ⟨h2, h3⟩, h4, h5⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2.1.1 hi.2.1.2 hi.2.2.1 hi.2.2.2⟩

private theorem realize_oiNNClause :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oiNNClause) ↔
      ∀ c x y : A, IsCl c → NegIn c x → ¬(ρ satNuSym.1 fun _ => x) → NegIn c y →
        ¬(ρ satNuSym.1 fun _ => y) → x = y := by
  letI := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [oiNNClause]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr,
    Language.relMap_sumInl, hsub]
  exact ⟨fun h c x y h1 h2 h3 h4 h5 => h ![c, x, y] ⟨h1, ⟨h2, h3⟩, h4, h5⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2.1.1 hi.2.1.2 hi.2.2.1 hi.2.2.2⟩

private theorem realize_oiPNClause :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oiPNClause) ↔
      ∀ c x y : A, IsCl c → PosIn c x → (ρ satNuSym.1 fun _ => x) → NegIn c y →
        (ρ satNuSym.1 fun _ => y) := by
  letI := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [oiPNClause]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, Language.relMap_sumInl, hsub]
  constructor
  · intro h c x y h1 h2 h3 h4
    by_contra h5
    exact h ![c, x, y] ⟨h1, ⟨h2, h3⟩, h4, h5⟩
  · rintro h i ⟨h1, ⟨h2, h3⟩, h4, h5⟩
    exact h5 (h (i 0) (i 1) (i 2) h1 h2 h3 h4)

private theorem realize_oneInKernel :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) oneInKernel) ↔
      (∀ c : A, RelMap satIsClause ![c] → ∃ x : A,
          (RelMap satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
            (RelMap satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x)) ∧
        (∀ c x y : A, IsCl c → PosIn c x → (ρ satNuSym.1 fun _ => x) → PosIn c y →
            (ρ satNuSym.1 fun _ => y) → x = y) ∧
        (∀ c x y : A, IsCl c → NegIn c x → ¬(ρ satNuSym.1 fun _ => x) → NegIn c y →
            ¬(ρ satNuSym.1 fun _ => y) → x = y) ∧
        ∀ c x y : A, IsCl c → PosIn c x → (ρ satNuSym.1 fun _ => x) → NegIn c y →
          (ρ satNuSym.1 fun _ => y) := by
  rw [oneInKernel]
  simp only [Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_satKernel ρ)
    (and_congr (realize_oiPPClause ρ)
      (and_congr (realize_oiNNClause ρ) (realize_oiPNClause ρ)))

end Realize

/-- **1-in-SAT is `Σ₁`-definable**: guess the assignment, then check
first-order that every clause has a true literal – SAT's kernel – and that it
has no second one. -/
theorem oneInSat_sigmaSODefinable : SigmaSODefinable 1 OneInSAT := by
  refine ⟨[satAssignBlock], rfl, oneInKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨fun _ x => ν (x ⟨0, Nat.one_pos⟩), (realize_oneInKernel _).mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · intro c hc
      obtain ⟨x, s, hx, hT, -⟩ := hν c hc
      cases s with
      | false => exact ⟨x, Or.inr ⟨hx.2, hT⟩⟩
      | true => exact ⟨x, Or.inl ⟨hx.2, hT⟩⟩
    · intro c x y hc hx hTx hy hTy
      obtain ⟨z, u, -, -, huniq⟩ := hν c hc
      obtain ⟨h1, -⟩ := huniq x true ⟨hc, hx⟩ hTx
      obtain ⟨h2, -⟩ := huniq y true ⟨hc, hy⟩ hTy
      exact h1.trans h2.symm
    · intro c x y hc hx hTx hy hTy
      obtain ⟨z, u, -, -, huniq⟩ := hν c hc
      obtain ⟨h1, -⟩ := huniq x false ⟨hc, hx⟩ hTx
      obtain ⟨h2, -⟩ := huniq y false ⟨hc, hy⟩ hTy
      exact h1.trans h2.symm
    · intro c x y hc hx hTx hy
      by_contra hTy
      obtain ⟨z, u, -, -, huniq⟩ := hν c hc
      obtain ⟨-, h1⟩ := huniq x true ⟨hc, hx⟩ hTx
      obtain ⟨-, h2⟩ := huniq y false ⟨hc, hy⟩ hTy
      exact Bool.noConfusion (h1.trans h2.symm)
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hsat, hPP, hNN, hPN⟩ := (realize_oneInKernel ρ).mp hρ
    refine ⟨fun x => ρ satNuSym.1 fun _ => x, fun c hc => ?_⟩
    obtain ⟨x, s, hx, hT⟩ := satClauses_occ hsat c hc
    refine ⟨x, s, hx, hT, fun y t hy hTy => ?_⟩
    cases s with
    | false =>
      cases t with
      | false => exact ⟨hNN c y x hc hy.2 hTy hx.2 hT, rfl⟩
      | true => exact absurd (hPN c y x hc hy.2 hTy hx.2) hT
    | true =>
      cases t with
      | false => exact absurd (hPN c x y hc hx.2 hT hy.2) hTy
      | true => exact ⟨hPP c y x hc hy.2 hTy hx.2 hT, rfl⟩

end SigmaOne

end DescriptiveComplexity
