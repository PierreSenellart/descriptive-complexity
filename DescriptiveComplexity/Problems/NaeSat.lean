/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.OrderWalk

/-!
# NAE-SAT is NP-complete

NOT-ALL-EQUAL SAT: is there a truth assignment giving every clause both a
true and a false literal? It lives on the very same vocabulary as SAT,
`FirstOrder.Language.sat`, and only its notion of satisfaction differs
(`DescriptiveComplexity.NAEProper`), so this file adds a problem rather than a
language.

NAE-SAT is the first of the Schaefer-style variants of satisfiability
([Schaefer 1978][schaefer1978complexity]) in the catalog. Their value is as
reduction *sources*: their symmetry makes gadgets far more local than SAT's,
which is what the classical reduction to Max Cut runs on.

## The symmetry, and the fresh variable

The defining feature is that `DescriptiveComplexity.NAEProper` is closed under flipping
the assignment (`DescriptiveComplexity.NAEProper.not`): swapping true and false swaps
the two conjuncts of the condition. That symmetry is exactly what the
reduction from SAT exploits. Given a CNF formula, add one fresh variable `s`
occurring positively in every clause; then a NAE-assignment can be normalized
(by flipping, if needed) to one with `s` false, and once `s` is false the “some
true literal” half is a satisfying assignment of the original formula.

“One fresh variable” is what makes this an *ordered* reduction
(`DescriptiveComplexity.sat_ordered_fo_reduction_naeSat`, tag `Bool`, dimension 1): an
interpretation adds elements only by tags, and a tag contributes a whole copy
of the universe, so the single fresh variable has to be picked out inside its
copy – as the minimum, via `DescriptiveComplexity.minF`. One fresh variable *per
clause* would not do: with its own private `s`, every clause could be
satisfied by choosing `s` opposite to one of its literals, and the reduction
would be false.

Membership reuses SAT's kernel verbatim
(`DescriptiveComplexity.realize_satKernel`): the NAE kernel is that one conjoined with
its mirror image, the clause stating that every clause also has a *false*
literal.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock BoundedFormula

/-! ### The problem -/

section Semantics

variable {A : Type} [Language.sat.Structure A]

/-- An assignment is *not-all-equal proper* when every clause contains both a
true and a false literal. -/
def NAEProper (ν : A → Prop) : Prop :=
  ∀ c : A, RelMap satIsClause ![c] →
    (∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) ∧
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ¬ν x) ∨ (RelMap satNegIn ![c, x] ∧ ν x)

/-- **The defining symmetry**: flipping a not-all-equal proper assignment
gives a not-all-equal proper assignment, the two halves of the condition
exchanging roles. -/
theorem NAEProper.not {ν : A → Prop} (h : NAEProper ν) : NAEProper fun x => ¬ν x := by
  intro c hc
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h c hc
  constructor
  · refine ⟨y, ?_⟩
    rcases hy with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨hp, hT⟩
    · exact Or.inr ⟨hn, not_not_intro hT⟩
  · refine ⟨x, ?_⟩
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨hp, not_not_intro hT⟩
    · exact Or.inr ⟨hn, hT⟩

end Semantics

section Problem

variable (A : Type) [Language.sat.Structure A]

/-- A `Language.sat`-structure is not-all-equal satisfiable if some assignment
gives every clause both a true and a false literal. -/
def NAESatisfiable : Prop := ∃ ν : A → Prop, NAEProper ν

end Problem

section Iso

private theorem naeSatisfiable_of_iso {A B : Type} [Language.sat.Structure A]
    [Language.sat.Structure B] (e : A ≃[Language.sat] B) (h : NAESatisfiable A) :
    NAESatisfiable B := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hν (e.symm c) ((relMap_equiv₁ e.symm satIsClause c).mp hc)
  constructor
  · refine ⟨e x, ?_⟩
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨by simpa using (relMap_equiv₂ e satPosIn (e.symm c) x).mp hp,
        by simpa using hT⟩
    · exact Or.inr ⟨by simpa using (relMap_equiv₂ e satNegIn (e.symm c) x).mp hn,
        by simpa using hT⟩
  · refine ⟨e y, ?_⟩
    rcases hy with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨by simpa using (relMap_equiv₂ e satPosIn (e.symm c) y).mp hp,
        by simpa using hT⟩
    · exact Or.inr ⟨by simpa using (relMap_equiv₂ e satNegIn (e.symm c) y).mp hn,
        by simpa using hT⟩

/-- Not-all-equal satisfiability is isomorphism-invariant. -/
theorem naeSatisfiable_iso {A B : Type} [Language.sat.Structure A]
    [Language.sat.Structure B] (e : A ≃[Language.sat] B) :
    NAESatisfiable A ↔ NAESatisfiable B :=
  ⟨naeSatisfiable_of_iso e, naeSatisfiable_of_iso e.symm⟩

end Iso

/-- NAE-SAT, as a problem on CNF instances: is there an assignment giving
every clause both a true and a false literal? -/
def NAESAT : DecisionProblem Language.sat where
  Holds := fun A inst => @NAESatisfiable A inst
  iso_invariant := fun e => naeSatisfiable_iso e

/-! ### SAT reduces to NAE-SAT -/

/-- The “is a clause” symbol over the ordered expansion. -/
abbrev oIsClSym : (Language.sat.sum Language.order).Relations 1 := Sum.inl satIsClause

/-- The “occurs positively in” symbol over the ordered expansion. -/
abbrev oPosSym : (Language.sat.sum Language.order).Relations 2 := Sum.inl satPosIn

/-- The “occurs negatively in” symbol over the ordered expansion. -/
abbrev oNegSym : (Language.sat.sum Language.order).Relations 2 := Sum.inl satNegIn

/-- The interpretation of SAT into NAE-SAT: keep the formula on the copy of
tag `true`, and let the minimum of the copy of tag `false` be a fresh variable
occurring positively in every clause. -/
noncomputable def naeInterp :
    FOInterpretation (Language.sat.sum Language.order) Language.sat Bool 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
        if t 0 then Relations.formula₁ oIsClSym (Term.var (0, 0)) else ⊥
    | _, .posIn => fun t =>
        if t 0 then
          (if t 1 then Relations.formula₂ oPosSym (Term.var (0, 0)) (Term.var (1, 0))
          else Relations.formula₁ oIsClSym (Term.var (0, 0)) ⊓ minF (1, 0))
        else ⊥
    | _, .negIn => fun t =>
        if t 0 then
          (if t 1 then Relations.formula₂ oNegSym (Term.var (0, 0)) (Term.var (1, 0))
          else ⊥)
        else ⊥

section Points

variable {A : Type}

/-- The copy of an element carrying the original formula. -/
def oPt (v : A) : naeInterp.Map A := (true, fun _ => v)

/-- The copy of an element carrying the fresh variable (only its minimum is
used). -/
def xPt (v : A) : naeInterp.Map A := (false, fun _ => v)

theorem oPt_injective : Function.Injective (oPt (A := A)) :=
  fun _ _ h => congrArg (fun p : Bool × (Fin 1 → A) => p.2 0) h

theorem oPt_eta (w : Fin 1 → A) : ((true, w) : naeInterp.Map A) = oPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

theorem xPt_eta (w : Fin 1 → A) : ((false, w) : naeInterp.Map A) = xPt (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

/-- Every element of the interpreted universe is a copy of an element. -/
theorem eq_oPt_or_xPt (p : naeInterp.Map A) : (∃ v, p = oPt v) ∨ ∃ v, p = xPt v := by
  rcases p with ⟨b, w⟩
  cases b
  · exact Or.inr ⟨w 0, xPt_eta w⟩
  · exact Or.inl ⟨w 0, oPt_eta w⟩

end Points

section Characterizations

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

@[simp]
theorem nae_isClause_o (v : A) :
    RelMap (M := naeInterp.Map A) satIsClause ![oPt v] ↔ RelMap satIsClause ![v] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₁]

@[simp]
theorem nae_isClause_x (v : A) :
    ¬RelMap (M := naeInterp.Map A) satIsClause ![xPt v] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

@[simp]
theorem nae_pos_oo (c x : A) :
    RelMap (M := naeInterp.Map A) satPosIn ![oPt c, oPt x] ↔ RelMap satPosIn ![c, x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₂]

@[simp]
theorem nae_pos_ox (c x : A) :
    RelMap (M := naeInterp.Map A) satPosIn ![oPt c, xPt x] ↔
      RelMap satIsClause ![c] ∧ ∀ a : A, x ≤ a := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, xPt, Formula.realize_rel₁, realize_minF]

@[simp]
theorem nae_pos_x (p : naeInterp.Map A) (x : A) :
    ¬RelMap (M := naeInterp.Map A) satPosIn ![xPt x, p] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

@[simp]
theorem nae_neg_oo (c x : A) :
    RelMap (M := naeInterp.Map A) satNegIn ![oPt c, oPt x] ↔ RelMap satNegIn ![c, x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₂]

@[simp]
theorem nae_neg_ox (c x : A) :
    ¬RelMap (M := naeInterp.Map A) satNegIn ![oPt c, xPt x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, xPt]

@[simp]
theorem nae_neg_x (p : naeInterp.Map A) (x : A) :
    ¬RelMap (M := naeInterp.Map A) satNegIn ![xPt x, p] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

end Characterizations

section Correctness

variable (A : Type) [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- Correctness of the interpretation: a CNF formula is satisfiable iff the
formula obtained by adding one fresh variable positively to every clause is
not-all-equal satisfiable. -/
theorem satisfiable_iff_naeSatisfiable_map :
    Satisfiable A ↔ NAESatisfiable (naeInterp.Map A) := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨fun p => p.1 = true ∧ ν (p.2 0), fun p hp => ?_⟩
    obtain ⟨c, rfl⟩ : ∃ c, p = oPt c := by
      rcases eq_oPt_or_xPt p with ⟨c, rfl⟩ | ⟨x, rfl⟩
      · exact ⟨c, rfl⟩
      · exact absurd hp (nae_isClause_x x)
    have hc : RelMap satIsClause ![c] := (nae_isClause_o c).mp hp
    constructor
    · obtain ⟨x, hx⟩ := hν c hc
      refine ⟨oPt x, ?_⟩
      rcases hx with ⟨hpos, hT⟩ | ⟨hneg, hT⟩
      · exact Or.inl ⟨(nae_pos_oo c x).mpr hpos, ⟨rfl, hT⟩⟩
      · exact Or.inr ⟨(nae_neg_oo c x).mpr hneg, fun h => hT h.2⟩
    · exact ⟨xPt m, Or.inl ⟨(nae_pos_ox c m).mpr ⟨hc, hm⟩, fun h => Bool.noConfusion h.1⟩⟩
  · rintro ⟨ν, hν⟩
    -- normalize so that the fresh variable is false, using the flip symmetry
    obtain ⟨μ, hμ, hfalse⟩ : ∃ μ : naeInterp.Map A → Prop, NAEProper μ ∧ ¬μ (xPt m) := by
      rcases Classical.em (ν (xPt m)) with h | h
      · exact ⟨fun p => ¬ν p, hν.not, not_not_intro h⟩
      · exact ⟨ν, hν, h⟩
    refine ⟨fun v => μ (oPt v), fun c hc => ?_⟩
    obtain ⟨⟨p, hp⟩, -⟩ := hμ (oPt c) ((nae_isClause_o c).mpr hc)
    rcases eq_oPt_or_xPt p with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rcases hp with ⟨hpos, hT⟩ | ⟨hneg, hT⟩
      · exact ⟨x, Or.inl ⟨(nae_pos_oo c x).mp hpos, hT⟩⟩
      · exact ⟨x, Or.inr ⟨(nae_neg_oo c x).mp hneg, hT⟩⟩
    · rcases hp with ⟨hpos, hT⟩ | ⟨hneg, -⟩
      · obtain ⟨-, hmin⟩ := (nae_pos_ox c x).mp hpos
        exact absurd (le_antisymm (hmin m) (hm x) ▸ hT) hfalse
      · exact absurd hneg (nae_neg_ox c x)

end Correctness

/-- **SAT ordered-FO-reduces to NAE-SAT**: add one fresh variable, the minimum
of a spare copy of the universe, positively to every clause. -/
noncomputable def sat_ordered_fo_reduction_naeSat : SAT ≤ᶠᵒ[≤] NAESAT where
  Tag := Bool
  dim := 1
  toInterpretation := naeInterp
  correct A _ _ _ _ := satisfiable_iff_naeSatisfiable_map A

/-! ### Membership -/

section SigmaOne

/-- The mirror of `DescriptiveComplexity.satKernel`: every clause contains a *false*
literal. Together they say that no clause is all-equal. -/
noncomputable def naeFalseKernel : satSOLang.Sentence :=
  ((Relations.formula₁ kIsClSym (Term.var (Sum.inr 0))).imp
    (((Relations.formula₂ kPosSym (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓
        ∼(Relations.formula₁ kNuSym (Term.var (Sum.inr ())))) ⊔
      (Relations.formula₂ kNegSym (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓
        Relations.formula₁ kNuSym (Term.var (Sum.inr ())))).iExs
      Unit)).iAlls (Fin 1)

/-- The first-order kernel of the `Σ₁` definition of NAE-SAT: SAT's kernel
conjoined with its mirror image. -/
noncomputable def naeKernel : satSOLang.Sentence := satKernel ⊓ naeFalseKernel

private theorem realize_naeFalseKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) naeFalseKernel) ↔
      ∀ c : A, RelMap satIsClause ![c] → ∃ x : A,
        (RelMap satPosIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) ∨
          (RelMap satNegIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) := by
  letI := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [naeFalseKernel]
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

private theorem realize_naeKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) naeKernel) ↔
      (∀ c : A, RelMap satIsClause ![c] → ∃ x : A,
        (RelMap satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
          (RelMap satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x)) ∧
      ∀ c : A, RelMap satIsClause ![c] → ∃ x : A,
        (RelMap satPosIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) ∨
          (RelMap satNegIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) := by
  rw [naeKernel]
  simp only [Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_satKernel ρ) (realize_naeFalseKernel ρ)

/-- **NAE-SAT is `Σ₁`-definable**: guess the assignment, then check
first-order that every clause has a true literal – SAT's kernel – and a false
one. -/
theorem naeSat_sigmaSODefinable : SigmaSODefinable 1 NAESAT := by
  refine ⟨[satAssignBlock], rfl, naeKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨ν, hν⟩
    exact ⟨fun _ x => ν (x ⟨0, Nat.one_pos⟩),
      (realize_naeKernel _).mpr ⟨fun c hc => (hν c hc).1, fun c hc => (hν c hc).2⟩⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨h₁, h₂⟩ := (realize_naeKernel ρ).mp hρ
    exact ⟨fun x => ρ satNuSym.1 fun _ => x, fun c hc => ⟨h₁ c hc, h₂ c hc⟩⟩

end SigmaOne

/-! ### NP-completeness -/

/-- NAE-SAT is in NP: it is `Σ₁`-definable. -/
theorem naeSat_mem_NP : NAESAT ∈ NP :=
  naeSat_sigmaSODefinable

/-- NAE-SAT is NP-hard: SAT, which is NP-hard, ordered-FO-reduces to it. -/
theorem naeSat_NP_hard : NP.Hard NAESAT :=
  NP.hard_of_orderedReduction sat_ordered_fo_reduction_naeSat sat_NP_hard

/-- **NAE-SAT is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. -/
theorem naeSat_NP_complete : NP.Complete NAESAT :=
  ⟨naeSat_mem_NP, naeSat_NP_hard⟩

end DescriptiveComplexity
