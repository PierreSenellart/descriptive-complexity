/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.Sat
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases
import Lax799700Proofs.DescriptiveComplexity.Ordered
import Lax799700Proofs.DescriptiveComplexity.Padding
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
import Lax799700Proofs.DescriptiveComplexity.OrderWalk
import Lax799700Proofs.DescriptiveComplexity.OccurrenceOrder
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# NAE-SAT is NP-complete

NOT-ALL-EQUAL SAT: is there a truth assignment giving every clause both a
true and a false literal? It lives on the very same vocabulary as SAT,
`FirstOrder.Language.sat`, and only its notion of satisfaction differs
(`Lax799700Proofs.DescriptiveComplexity.NAEProper`), so this file adds a problem rather than a
language.

NAE-SAT is the first of the Schaefer-style variants of satisfiability
([Schaefer 1978][schaefer1978complexity]) in the catalog. Their value is as
reduction *sources*: their symmetry makes gadgets far more local than SAT's,
which is what the classical reduction to Max Cut runs on.

## The symmetry, and the fresh variable

The defining feature is that `Lax799700Proofs.DescriptiveComplexity.NAEProper` is closed under flipping
the assignment (`Lax799700Proofs.DescriptiveComplexity.NAEProper.not`): swapping true and false swaps
the two conjuncts of the condition. That symmetry is exactly what the
reduction from SAT exploits. Given a CNF formula, add one fresh variable `s`
occurring positively in every clause; then a NAE-assignment can be normalized
(by flipping, if needed) to one with `s` false, and once `s` is false the “some
true literal” half is a satisfying assignment of the original formula.

“One fresh variable” is what makes this an *ordered* reduction
(`Lax799700Proofs.DescriptiveComplexity.sat_ordered_fo_reduction_naeSat`, tag `Bool`, dimension 1): an
interpretation adds elements only by tags, and a tag contributes a whole copy
of the universe, so the single fresh variable has to be picked out inside its
copy – as the minimum, via `Lax799700Proofs.DescriptiveComplexity.minF`. One fresh variable *per
clause* would not do: with its own private `s`, every clause could be
satisfied by choosing `s` opposite to one of its literals, and the reduction
would be false.

Membership reuses SAT's kernel verbatim
(`Lax799700Proofs.DescriptiveComplexity.realize_satKernel`): the NAE kernel is that one conjoined with
its mirror image, the clause stating that every clause also has a *false*
literal.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock BoundedFormula SatOcc

/-! ### The problem -/

section Semantics

variable {A : Type} [Lax904597.Sat.sat.Structure A]

/-- **The defining symmetry**: flipping a not-all-equal proper assignment
gives a not-all-equal proper assignment, the two halves of the condition
exchanging roles. -/
theorem NAEProper.not {ν : A → Prop} (h : Lax799700.NaeSat.NAEProper ν) : Lax799700.NaeSat.NAEProper fun x => ¬ν x := by
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

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700.NaeSat.NAEProper

export Lax799700Proofs.DescriptiveComplexity.NAEProper (not)

end Lax799700.NaeSat.NAEProper

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock BoundedFormula SatOcc

section Semantics

variable {A : Type} [Lax904597.Sat.sat.Structure A]

omit [Lax904597.Sat.sat.Structure A] in
/-- Flipping the assignment flips the truth of every literal. -/
theorem litTrue_compl {ν : A → Prop} {x : A} {s : Bool} :
    Lax799700.Common.SatOcc.LitTrue (fun a => ¬ν a) x s ↔ ¬Lax799700.Common.SatOcc.LitTrue ν x s := by
  cases s <;> simp [Lax799700.Common.SatOcc.LitTrue]

/-- Occurrence form of not-all-equal properness: every clause has a true and a
false literal occurrence. -/
theorem naeProper_occ {ν : A → Prop} (h : Lax799700.NaeSat.NAEProper ν) (c : A)
    (hc : RelMap Lax904597.Sat.satIsClause ![c]) :
    (∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ Lax799700.Common.SatOcc.LitTrue ν x s) ∧ ∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ ¬Lax799700.Common.SatOcc.LitTrue ν x s := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h c hc
  constructor
  · rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨x, true, ⟨hc, hp⟩, hT⟩
    · exact ⟨x, false, ⟨hc, hn⟩, hT⟩
  · rcases hy with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨y, true, ⟨hc, hp⟩, hT⟩
    · exact ⟨y, false, ⟨hc, hn⟩, not_not_intro hT⟩

/-- Not-all-equal properness from the occurrence form. -/
theorem naeProper_of_occ {ν : A → Prop}
    (h : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] →
      (∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ Lax799700.Common.SatOcc.LitTrue ν x s) ∧ ∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ ¬Lax799700.Common.SatOcc.LitTrue ν x s) :
    Lax799700.NaeSat.NAEProper ν := by
  intro c hc
  obtain ⟨⟨x, s, hx, hT⟩, ⟨y, t, hy, hF⟩⟩ := h c hc
  constructor
  · cases s with
    | true => exact ⟨x, Or.inl ⟨hx.2, hT⟩⟩
    | false => exact ⟨x, Or.inr ⟨hx.2, hT⟩⟩
  · cases t with
    | true => exact ⟨y, Or.inl ⟨hy.2, hF⟩⟩
    | false => exact ⟨y, Or.inr ⟨hy.2, not_not.mp hF⟩⟩

end Semantics

section Problem

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end Problem

section Iso

private theorem naeSatisfiable_of_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) (h : Lax799700.NaeSat.NAESatisfiable A) :
    Lax799700.NaeSat.NAESatisfiable B := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hν (e.symm c) ((relMap_equiv₁ e.symm Lax904597.Sat.satIsClause c).mp hc)
  constructor
  · refine ⟨e x, ?_⟩
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨by simpa using (relMap_equiv₂ e Lax904597.Sat.satPosIn (e.symm c) x).mp hp,
        by simpa using hT⟩
    · exact Or.inr ⟨by simpa using (relMap_equiv₂ e Lax904597.Sat.satNegIn (e.symm c) x).mp hn,
        by simpa using hT⟩
  · refine ⟨e y, ?_⟩
    rcases hy with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨by simpa using (relMap_equiv₂ e Lax904597.Sat.satPosIn (e.symm c) y).mp hp,
        by simpa using hT⟩
    · exact Or.inr ⟨by simpa using (relMap_equiv₂ e Lax904597.Sat.satNegIn (e.symm c) y).mp hn,
        by simpa using hT⟩

/-- Not-all-equal satisfiability is isomorphism-invariant. -/
theorem naeSatisfiable_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) :
    Lax799700.NaeSat.NAESatisfiable A ↔ Lax799700.NaeSat.NAESatisfiable B :=
  ⟨naeSatisfiable_of_iso e, naeSatisfiable_of_iso e.symm⟩

end Iso

/-- NAE-SAT, as a problem on CNF instances: is there an assignment giving
every clause both a true and a false literal? -/
def NAESAT : Lax904597.Problems.DecisionProblem Lax904597.Sat.sat where
  Holds := fun A inst => @Lax799700.NaeSat.NAESatisfiable A inst
  iso_invariant := fun e => naeSatisfiable_iso e

/-! ### SAT reduces to NAE-SAT -/

/-- The “is a clause” symbol over the ordered expansion. -/
abbrev oIsClSym : (Lax904597.Sat.sat.sum Language.order).Relations 1 := Sum.inl Lax904597.Sat.satIsClause

/-- The “occurs positively in” symbol over the ordered expansion. -/
abbrev oPosSym : (Lax904597.Sat.sat.sum Language.order).Relations 2 := Sum.inl Lax904597.Sat.satPosIn

/-- The “occurs negatively in” symbol over the ordered expansion. -/
abbrev oNegSym : (Lax904597.Sat.sat.sum Language.order).Relations 2 := Sum.inl Lax904597.Sat.satNegIn

/-- The interpretation of SAT into NAE-SAT: keep the formula on the copy of
tag `true`, and let the minimum of the copy of tag `false` be a fresh variable
occurring positively in every clause. -/
noncomputable def naeInterp :
    Lax904597.Interpretations.FOInterpretation (Lax904597.Sat.sat.sum Language.order) Lax904597.Sat.sat Bool 1 where
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

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

@[simp]
theorem nae_isClause_o (v : A) :
    RelMap (M := naeInterp.Map A) Lax904597.Sat.satIsClause ![oPt v] ↔ RelMap Lax904597.Sat.satIsClause ![v] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₁]

@[simp]
theorem nae_isClause_x (v : A) :
    ¬RelMap (M := naeInterp.Map A) Lax904597.Sat.satIsClause ![xPt v] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

@[simp]
theorem nae_pos_oo (c x : A) :
    RelMap (M := naeInterp.Map A) Lax904597.Sat.satPosIn ![oPt c, oPt x] ↔ RelMap Lax904597.Sat.satPosIn ![c, x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₂]

@[simp]
theorem nae_pos_ox (c x : A) :
    RelMap (M := naeInterp.Map A) Lax904597.Sat.satPosIn ![oPt c, xPt x] ↔
      RelMap Lax904597.Sat.satIsClause ![c] ∧ ∀ a : A, x ≤ a := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, xPt, Formula.realize_rel₁, realize_minF]

@[simp]
theorem nae_pos_x (p : naeInterp.Map A) (x : A) :
    ¬RelMap (M := naeInterp.Map A) Lax904597.Sat.satPosIn ![xPt x, p] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

@[simp]
theorem nae_neg_oo (c x : A) :
    RelMap (M := naeInterp.Map A) Lax904597.Sat.satNegIn ![oPt c, oPt x] ↔ RelMap Lax904597.Sat.satNegIn ![c, x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, Formula.realize_rel₂]

@[simp]
theorem nae_neg_ox (c x : A) :
    ¬RelMap (M := naeInterp.Map A) Lax904597.Sat.satNegIn ![oPt c, xPt x] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, oPt, xPt]

@[simp]
theorem nae_neg_x (p : naeInterp.Map A) (x : A) :
    ¬RelMap (M := naeInterp.Map A) Lax904597.Sat.satNegIn ![xPt x, p] := by
  rw [FOInterpretation.relMap_map]
  simp [naeInterp, xPt]

end Characterizations

section Correctness

variable (A : Type) [Lax904597.Sat.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- Correctness of the interpretation: a CNF formula is satisfiable iff the
formula obtained by adding one fresh variable positively to every clause is
not-all-equal satisfiable. -/
theorem satisfiable_iff_naeSatisfiable_map :
    Lax904597.Sat.Satisfiable A ↔ Lax799700.NaeSat.NAESatisfiable (naeInterp.Map A) := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨fun p => p.1 = true ∧ ν (p.2 0), fun p hp => ?_⟩
    obtain ⟨c, rfl⟩ : ∃ c, p = oPt c := by
      rcases eq_oPt_or_xPt p with ⟨c, rfl⟩ | ⟨x, rfl⟩
      · exact ⟨c, rfl⟩
      · exact absurd hp (nae_isClause_x x)
    have hc : RelMap Lax904597.Sat.satIsClause ![c] := (nae_isClause_o c).mp hp
    constructor
    · obtain ⟨x, hx⟩ := hν c hc
      refine ⟨oPt x, ?_⟩
      rcases hx with ⟨hpos, hT⟩ | ⟨hneg, hT⟩
      · exact Or.inl ⟨(nae_pos_oo c x).mpr hpos, ⟨rfl, hT⟩⟩
      · exact Or.inr ⟨(nae_neg_oo c x).mpr hneg, fun h => hT h.2⟩
    · exact ⟨xPt m, Or.inl ⟨(nae_pos_ox c m).mpr ⟨hc, hm⟩, fun h => Bool.noConfusion h.1⟩⟩
  · rintro ⟨ν, hν⟩
    -- normalize so that the fresh variable is false, using the flip symmetry
    obtain ⟨μ, hμ, hfalse⟩ : ∃ μ : naeInterp.Map A → Prop, Lax799700.NaeSat.NAEProper μ ∧ ¬μ (xPt m) := by
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
noncomputable def sat_ordered_fo_reduction_naeSat : Lax904597.Sat.SAT ≤ᶠᵒ[≤] NAESAT where
  Tag := Bool
  dim := 1
  toInterpretation := naeInterp
  correct A _ _ _ _ := satisfiable_iff_naeSatisfiable_map A

/-! ### Membership -/

section SigmaOne

/-- The mirror of `Lax799700Proofs.DescriptiveComplexity.satKernel`: every clause contains a *false*
literal. Together they say that no clause is all-equal. -/
noncomputable def naeFalseKernel : satSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ kIsClSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 0))) ⊔
            FirstOrder.Language.Relations.formula₂ kNegSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 0)))))

/-- The first-order kernel of the `Σ₁` definition of NAE-SAT: SAT's kernel
conjoined with its mirror image. -/
noncomputable def naeKernel : satSOLang.Sentence := satKernel ⊓ naeFalseKernel

private theorem realize_naeFalseKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) naeFalseKernel) ↔
      ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
        (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) ∨
          (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) := by
  let := satAssignBlock.structure ρ
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
    · exact ⟨x 0, Or.inl ⟨hp, hT⟩⟩
    · exact ⟨x 0, Or.inr ⟨hn, hT⟩⟩
  · intro h i hc
    obtain ⟨x, hx⟩ := h (i 0) hc
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨fun _ => x, Or.inl ⟨hp, hT⟩⟩
    · exact ⟨fun _ => x, Or.inr ⟨hn, hT⟩⟩

private theorem realize_naeKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) naeKernel) ↔
      (∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
        (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
          (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x)) ∧
      ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] → ∃ x : A,
        (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) ∨
          (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) := by
  rw [naeKernel]
  simp only [Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_satKernel ρ) (realize_naeFalseKernel ρ)

/-- **NAE-SAT is `Σ₁`-definable**: guess the assignment, then check
first-order that every clause has a true literal – SAT's kernel – and a false
one. -/
theorem naeSat_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 NAESAT := by
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

end Lax799700Proofs.DescriptiveComplexity


