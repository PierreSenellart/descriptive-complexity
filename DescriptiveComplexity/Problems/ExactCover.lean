/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily
import DescriptiveComplexity.Problems.OneInSat
import DescriptiveComplexity.Problems.ThreeSat.ToSat

/-!
# Exact Cover is NP-complete

EXACT COVER ([Karp 1972][karp1972reducibility]): is there a subfamily covering
every ground element *exactly once*? The problem lives on
`FirstOrder.Language.setSystem` unchanged (`DescriptiveComplexity.ExactCover`,
`DescriptiveComplexity.Problems.SetFamily.Defs`) – exactness is a property of the
subfamily, not a new vocabulary, and it replaces the threshold, so the marked
set plays no role at all.

Hardness comes from exactly-one satisfiability
(`DescriptiveComplexity.Problems.OneInSat`) by a reduction with **no gadget and no
counting**, order-free and of dimension 1:

* the ground elements are the variables and the clauses, a variable being an
  element that occurs in some clause (`DescriptiveComplexity.SatOccurs`);
* the family has one set per literal `(x, s)` of a variable `x`, namely
  `{x} ∪ {clauses where (x, s) occurs}`.

Covering the element `x` exactly once picks exactly one of the two literals of
`x` – that *is* a truth assignment – and covering a clause exactly once is
exactly what exactly-one satisfaction asks. Nothing here depends on the width
of the clauses, which is why the source is unrestricted 1-in-SAT rather than
its width-three restriction.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace ExactCoverRed

open Language Structure SatOcc

/-- Tags of the reduction: the ground element of a variable, the ground
element of a clause, and the set of a literal. -/
inductive ECTag : Type
  /-- The ground element of a variable. -/
  | velt
  /-- The ground element of a clause. -/
  | celt
  /-- The set of the literal `(x, s)`. -/
  | lset (s : Bool)
  deriving DecidableEq

instance : Fintype ECTag where
  elems := {ECTag.velt, ECTag.celt, ECTag.lset true, ECTag.lset false}
  complete := by
    intro t
    cases t with
    | velt => decide
    | celt => decide
    | lset s => cases s <;> decide

instance : Nonempty ECTag := ⟨ECTag.velt⟩

/-! ### The interpretation -/

/-- `x` is a variable of the formula – it occurs in some clause –, as a
formula. Without this guard an element in no clause would be a ground element
with two singleton sets to choose from: harmless for the existence of an exact
cover, and a factor two in their number. -/
noncomputable def occursF {α : Type} (x : α) : Language.sat.Formula α :=
  Formula.iExs Unit (ThreeSatToSat.clF (Sum.inr ()) ⊓
    (ThreeSatToSat.posF (Sum.inr ()) (Sum.inl x) ⊔ ThreeSatToSat.negF (Sum.inr ()) (Sum.inl x)))

theorem realize_occursF {A : Type} [Language.sat.Structure A] {α : Type} {v : α → A} {x : α} :
    (occursF x).Realize v ↔ SatOccurs A (v x) := by
  simp only [occursF, Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup,
    ThreeSatToSat.realize_clF, ThreeSatToSat.realize_posF, ThreeSatToSat.realize_negF,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i (), hi⟩, fun ⟨c, hc⟩ => ⟨fun _ => c, hc⟩⟩

/-- Defining formula for the ground elements: the variables and the
clauses. -/
noncomputable def elemF : ECTag → Language.sat.Formula (Fin 1 × Fin 1)
  | .velt => occursF (0, 0)
  | .celt => ThreeSatToSat.clF (0, 0)
  | .lset _ => ⊥

/-- Defining formula for the family: one set per literal of a variable. -/
noncomputable def famF : ECTag → Language.sat.Formula (Fin 1 × Fin 1)
  | .lset _ => occursF (0, 0)
  | _ => ⊥

/-- Defining formula for incidence: the set of `(x, s)` contains the element
of `x` and the elements of the clauses where `(x, s)` occurs. -/
noncomputable def memF : ECTag → ECTag → Language.sat.Formula (Fin 2 × Fin 1)
  | .velt, .lset _ => ThreeSatToSat.eqF (0, 0) (1, 0)
  | .celt, .lset s => ThreeSatToSat.occF s (0, 0) (1, 0)
  | _, _ => ⊥

/-- The interpretation of Exact Cover instances in CNF instances. -/
noncomputable def ecInterp : FOInterpretation Language.sat Language.setSystem ECTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .elem => fun t => elemF (t 0)
    | _, .fam => fun t => famF (t 0)
    | _, .mem => fun t => memF (t 0) (t 1)
    | _, .marked => fun _ => ⊥

/-! ### The points -/

section Points

variable {A : Type}

/-- The point of tag `t` over the element `x`. -/
def ecPt (t : ECTag) (x : A) : ecInterp.Map A := (t, fun _ => x)

theorem ecPt_eq_iff {t t' : ECTag} {x x' : A} : ecPt t x = ecPt t' x' ↔ t = t' ∧ x = x' := by
  constructor
  · intro h
    exact ⟨by simpa [ecPt] using congrArg (fun p : ecInterp.Map A => p.1) h,
      by simpa [ecPt] using congrArg (fun p : ecInterp.Map A => p.2 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem ecPt_surj (q : ecInterp.Map A) : ∃ t x, q = ecPt t x :=
  ⟨q.1, q.2 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg q.2 (Subsingleton.elim i 0)⟩⟩

end Points

/-! ### Characterization of the four relations -/

section Characterizations

variable {A : Type} [Language.sat.Structure A]

@[simp]
theorem ssElem_velt (x : A) : SSElem (ecPt .velt x) ↔ SatOccurs A x := by
  rw [SSElem, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, elemF, realize_occursF]

@[simp]
theorem ssElem_celt (c : A) : SSElem (ecPt .celt c) ↔ IsCl c := by
  rw [SSElem, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, elemF, ThreeSatToSat.realize_clF, IsCl]

@[simp]
theorem ssElem_lset (s : Bool) (x : A) : ¬SSElem (ecPt (.lset s) x) := by
  rw [SSElem, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, elemF]

@[simp]
theorem ssFam_lset (s : Bool) (x : A) : SSFam (ecPt (.lset s) x) ↔ SatOccurs A x := by
  rw [SSFam, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, famF, realize_occursF]

@[simp]
theorem ssFam_velt (x : A) : ¬SSFam (ecPt .velt x) := by
  rw [SSFam, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, famF]

@[simp]
theorem ssFam_celt (x : A) : ¬SSFam (ecPt .celt x) := by
  rw [SSFam, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, famF]

@[simp]
theorem ssMem_velt_lset (x : A) (s : Bool) (y : A) :
    SSMem (ecPt .velt x) (ecPt (.lset s) y) ↔ x = y := by
  rw [SSMem, ecPt, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, memF, ThreeSatToSat.realize_eqF]

@[simp]
theorem ssMem_celt_lset (c : A) (s : Bool) (x : A) :
    SSMem (ecPt .celt c) (ecPt (.lset s) x) ↔ OccIn c x s := by
  rw [SSMem, ecPt, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, memF, ThreeSatToSat.realize_occF]

/-- The sets of the family are exactly the literal sets of the variables. -/
theorem ssFam_cases {q : ecInterp.Map A} (h : SSFam q) :
    ∃ s x, SatOccurs A x ∧ q = ecPt (.lset s) x := by
  obtain ⟨t, x, rfl⟩ := ecPt_surj q
  cases t with
  | velt => exact absurd h (ssFam_velt x)
  | celt => exact absurd h (ssFam_celt x)
  | lset s => exact ⟨s, x, (ssFam_lset s x).mp h, rfl⟩

/-- The ground elements are exactly the variables and the clauses. -/
theorem ssElem_cases {q : ecInterp.Map A} (h : SSElem q) :
    (∃ x, SatOccurs A x ∧ q = ecPt .velt x) ∨ ∃ c, IsCl c ∧ q = ecPt .celt c := by
  obtain ⟨t, x, rfl⟩ := ecPt_surj q
  cases t with
  | velt => exact Or.inl ⟨x, (ssElem_velt x).mp h, rfl⟩
  | celt => exact Or.inr ⟨x, (ssElem_celt x).mp h, rfl⟩
  | lset s => exact absurd h (ssElem_lset s x)

end Characterizations

/-! ### Correctness

Stated for an explicit assignment and an explicit cover, so that the same
lemmas give the equivalence of the two decision problems and the bijection
between their solutions (`DescriptiveComplexity.Problems.ExactCoverCounting`). -/

section Correctness

variable {A : Type} [Language.sat.Structure A]

/-- A literal occurring in a clause is a literal of a variable. -/
theorem satOccurs_of_occIn {c x : A} {s : Bool} (h : OccIn c x s) : SatOccurs A x := by
  cases s
  · exact ⟨c, h.1, Or.inr h.2⟩
  · exact ⟨c, h.1, Or.inl h.2⟩

/-- The subfamily of an assignment: the sets of its true literals. -/
def coverOf (ν : A → Prop) (S : ecInterp.Map A) : Prop :=
  ∃ s x, S = ecPt (.lset s) x ∧ LitTrue ν x s ∧ SatOccurs A x

/-- The assignment of a subfamily: the variables whose positive literal set is
chosen. -/
def assignOf (G : ecInterp.Map A → Prop) (z : A) : Prop := G (ecPt (.lset true) z)

/-- **The true literals of an exactly-one assignment form an exact cover.** -/
theorem exactCoverBy_coverOf {ν : A → Prop} (hν : OneInProper ν) :
    ExactCoverBy (SSElem (A := ecInterp.Map A)) SSFam SSMem (coverOf ν) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro S ⟨s, x, rfl, -, hx⟩
    exact (ssFam_lset s x).mpr hx
  · intro p hp
    rcases ssElem_cases hp with ⟨x, hocc, rfl⟩ | ⟨c, hc, rfl⟩
    · -- the element of a variable is covered by the literal it makes true
      by_cases hx : ν x
      · exact ⟨ecPt (.lset true) x, ⟨true, x, rfl, hx, hocc⟩,
          (ssMem_velt_lset x true x).mpr rfl⟩
      · exact ⟨ecPt (.lset false) x, ⟨false, x, rfl, hx, hocc⟩,
          (ssMem_velt_lset x false x).mpr rfl⟩
    · -- the element of a clause is covered by its unique true literal
      obtain ⟨x, s, hocc, hT, -⟩ := hν c hc
      exact ⟨ecPt (.lset s) x, ⟨s, x, rfl, hT, satOccurs_of_occIn hocc⟩,
        (ssMem_celt_lset c s x).mpr hocc⟩
  · rintro S S' ⟨s, x, rfl, hT, -⟩ ⟨s', x', rfl, hT', -⟩ hne p hp ⟨hm, hm'⟩
    rcases ssElem_cases hp with ⟨y, -, rfl⟩ | ⟨c, hc, rfl⟩
    · -- two literals of the same variable, both true
      obtain rfl : y = x := (ssMem_velt_lset y s x).mp hm
      obtain rfl : y = x' := (ssMem_velt_lset y s' x').mp hm'
      refine hne ?_
      obtain rfl : s = s' := by
        cases s <;> cases s' <;> simp_all [LitTrue]
      rfl
    · -- two true literals of the same clause
      obtain ⟨z, u, -, -, huniq⟩ := hν c hc
      obtain ⟨rfl, rfl⟩ := huniq x s ((ssMem_celt_lset c s x).mp hm) hT
      obtain ⟨rfl, rfl⟩ := huniq x' s' ((ssMem_celt_lset c s' x').mp hm') hT'
      exact hne rfl

/-- **The chosen sets of an exact cover are the true literals of its
assignment**, at every variable. -/
theorem exactCoverBy_lit {G : ecInterp.Map A → Prop}
    (hG : ExactCoverBy (SSElem (A := ecInterp.Map A)) SSFam SSMem G) {x : A}
    (hx : SatOccurs A x) (s : Bool) :
    G (ecPt (.lset s) x) ↔ LitTrue (assignOf G) x s := by
  obtain ⟨hGfam, hcov, hdisj⟩ := hG
  have hone : G (ecPt (.lset true) x) ∨ G (ecPt (.lset false) x) := by
    obtain ⟨S, hS, hmem⟩ := hcov (ecPt .velt x) ((ssElem_velt x).mpr hx)
    obtain ⟨u, y, -, rfl⟩ := ssFam_cases (hGfam S hS)
    obtain rfl : x = y := (ssMem_velt_lset x u y).mp hmem
    cases u
    · exact Or.inr hS
    · exact Or.inl hS
  have hnot : ¬(G (ecPt (.lset true) x) ∧ G (ecPt (.lset false) x)) := by
    rintro ⟨h1, h2⟩
    refine hdisj _ _ h1 h2 (by simp [ecPt_eq_iff]) (ecPt .velt x) ((ssElem_velt x).mpr hx) ?_
    exact ⟨(ssMem_velt_lset x true x).mpr rfl, (ssMem_velt_lset x false x).mpr rfl⟩
  cases s with
  | true => exact Iff.rfl
  | false =>
    change G (ecPt (.lset false) x) ↔ ¬G (ecPt (.lset true) x)
    constructor
    · exact fun h h' => hnot ⟨h', h⟩
    · exact fun h => hone.resolve_left h

/-- **An exact cover reads off an exactly-one assignment.** -/
theorem oneInProper_assignOf {G : ecInterp.Map A → Prop}
    (hG : ExactCoverBy (SSElem (A := ecInterp.Map A)) SSFam SSMem G) :
    OneInProper (assignOf G) := by
  intro c hc
  obtain ⟨hGfam, hcov, hdisj⟩ := hG
  obtain ⟨S, hS, hmem⟩ := hcov (ecPt .celt c) ((ssElem_celt c).mpr hc)
  obtain ⟨s, x, -, rfl⟩ := ssFam_cases (hGfam S hS)
  have hocc : OccIn c x s := (ssMem_celt_lset c s x).mp hmem
  refine ⟨x, s, hocc,
    (exactCoverBy_lit ⟨hGfam, hcov, hdisj⟩ (satOccurs_of_occIn hocc) s).mp hS,
    fun y t hy hTy => ?_⟩
  by_contra hne
  refine hdisj _ _
    ((exactCoverBy_lit ⟨hGfam, hcov, hdisj⟩ (satOccurs_of_occIn hy) t).mpr hTy) hS ?_
    (ecPt .celt c) ((ssElem_celt c).mpr hc) ⟨(ssMem_celt_lset c t y).mpr hy, hmem⟩
  rw [Ne, ecPt_eq_iff]
  rintro ⟨ht, rfl⟩
  exact hne ⟨rfl, by simpa using ht⟩

variable (A) in
/-- Correctness of the reduction: a CNF structure is exactly-one satisfiable
iff its literal set system has an exact cover. -/
theorem oneInSatisfiable_iff_hasExactCover :
    OneInSatisfiable A ↔ HasExactCover (ecInterp.Map A) :=
  ⟨fun ⟨ν, hν⟩ => ⟨coverOf ν, exactCoverBy_coverOf hν⟩,
    fun ⟨G, hG⟩ => ⟨assignOf G, oneInProper_assignOf hG⟩⟩

end Correctness

end ExactCoverRed

open ExactCoverRed in
/-- **1-in-SAT FO-reduces to Exact Cover**: the ground elements are the
variables and the clauses, and the family has one set per literal. No order,
no gadget and no counting. -/
noncomputable def oneInSat_fo_reduction_exactCover : OneInSAT ≤ᶠᵒ ExactCover where
  Tag := ECTag
  dim := 1
  toInterpretation := ecInterp
  correct A _ _ _ := oneInSatisfiable_iff_hasExactCover A

/-! ### NP-completeness -/

/-- Exact Cover is NP-hard: 1-in-SAT, which is NP-hard, FO-reduces to it. -/
theorem exactCover_NP_hard : NP.Hard ExactCover :=
  NP.hard_of_foReduction oneInSat_fo_reduction_exactCover oneInSat_NP_hard

/-- **Exact Cover is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem.
Registered in the Lax archive as
[`Lax799700.SetFamily.exactCover_NP_complete`](https://laxarchive.org/lax-799700/Lax799700.SetFamily.html#s-Lax799700.SetFamily.exactCover_NP_complete). -/
theorem exactCover_NP_complete : NP.Complete ExactCover :=
  ⟨exactCover_mem_NP, exactCover_NP_hard⟩

end DescriptiveComplexity
