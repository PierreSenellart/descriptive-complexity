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

* the ground elements are the variables and the clauses;
* the family has one set per literal `(x, s)`, namely `{x} ∪ {clauses where
  (x, s) occurs}`.

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

/-- Defining formula for the ground elements: the variables and the
clauses. -/
noncomputable def elemF : ECTag → Language.sat.Formula (Fin 1 × Fin 1)
  | .velt => ⊤
  | .celt => ThreeSatToSat.clF (0, 0)
  | .lset _ => ⊥

/-- Defining formula for the family: one set per literal. -/
noncomputable def famF : ECTag → Language.sat.Formula (Fin 1 × Fin 1)
  | .lset _ => ⊤
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
theorem ssElem_velt (x : A) : SSElem (ecPt .velt x) := by
  rw [SSElem, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, elemF]

@[simp]
theorem ssElem_celt (c : A) : SSElem (ecPt .celt c) ↔ IsCl c := by
  rw [SSElem, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, elemF, ThreeSatToSat.realize_clF, IsCl]

@[simp]
theorem ssElem_lset (s : Bool) (x : A) : ¬SSElem (ecPt (.lset s) x) := by
  rw [SSElem, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, elemF]

@[simp]
theorem ssFam_lset (s : Bool) (x : A) : SSFam (ecPt (.lset s) x) := by
  rw [SSFam, ecPt, FOInterpretation.relMap_map]
  simp [ecInterp, famF]

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

/-- The sets of the family are exactly the literal sets. -/
theorem ssFam_cases {q : ecInterp.Map A} (h : SSFam q) : ∃ s x, q = ecPt (.lset s) x := by
  obtain ⟨t, x, rfl⟩ := ecPt_surj q
  cases t with
  | velt => exact absurd h (ssFam_velt x)
  | celt => exact absurd h (ssFam_celt x)
  | lset s => exact ⟨s, x, rfl⟩

/-- The ground elements are exactly the variables and the clauses. -/
theorem ssElem_cases {q : ecInterp.Map A} (h : SSElem q) :
    (∃ x, q = ecPt .velt x) ∨ ∃ c, IsCl c ∧ q = ecPt .celt c := by
  obtain ⟨t, x, rfl⟩ := ecPt_surj q
  cases t with
  | velt => exact Or.inl ⟨x, rfl⟩
  | celt => exact Or.inr ⟨x, (ssElem_celt x).mp h, rfl⟩
  | lset s => exact absurd h (ssElem_lset s x)

end Characterizations

/-! ### Correctness -/

section Correctness

variable (A : Type) [Language.sat.Structure A]

/-- Correctness of the reduction: a CNF structure is exactly-one satisfiable
iff its literal set system has an exact cover. -/
theorem oneInSatisfiable_iff_hasExactCover :
    OneInSatisfiable A ↔ HasExactCover (ecInterp.Map A) := by
  constructor
  · -- the true literals of an exactly-one assignment form an exact cover
    rintro ⟨ν, hν⟩
    refine ⟨fun S => ∃ s x, S = ecPt (.lset s) x ∧ LitTrue ν x s, ?_, ?_, ?_⟩
    · rintro S ⟨s, x, rfl, -⟩
      exact ssFam_lset s x
    · intro p hp
      rcases ssElem_cases hp with ⟨x, rfl⟩ | ⟨c, hc, rfl⟩
      · -- the element of a variable is covered by the literal it makes true
        by_cases hx : ν x
        · exact ⟨ecPt (.lset true) x, ⟨true, x, rfl, hx⟩, (ssMem_velt_lset x true x).mpr rfl⟩
        · exact ⟨ecPt (.lset false) x, ⟨false, x, rfl, hx⟩, (ssMem_velt_lset x false x).mpr rfl⟩
      · -- the element of a clause is covered by its unique true literal
        obtain ⟨x, s, hocc, hT, -⟩ := hν c hc
        exact ⟨ecPt (.lset s) x, ⟨s, x, rfl, hT⟩, (ssMem_celt_lset c s x).mpr hocc⟩
    · rintro S S' ⟨s, x, rfl, hT⟩ ⟨s', x', rfl, hT'⟩ hne p hp ⟨hm, hm'⟩
      rcases ssElem_cases hp with ⟨y, rfl⟩ | ⟨c, hc, rfl⟩
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
  · -- an exact cover reads off an exactly-one assignment
    rintro ⟨G, hGfam, hcov, hdisj⟩
    -- the chosen sets are exactly the true literals
    have hkey : ∀ (x : A) (s : Bool),
        G (ecPt (.lset s) x) ↔ LitTrue (fun z => G (ecPt (.lset true) z)) x s := by
      intro x s
      have hone : G (ecPt (.lset true) x) ∨ G (ecPt (.lset false) x) := by
        obtain ⟨S, hS, hmem⟩ := hcov (ecPt .velt x) (ssElem_velt x)
        obtain ⟨u, y, rfl⟩ := ssFam_cases (hGfam S hS)
        obtain rfl : x = y := (ssMem_velt_lset x u y).mp hmem
        cases u
        · exact Or.inr hS
        · exact Or.inl hS
      have hnot : ¬(G (ecPt (.lset true) x) ∧ G (ecPt (.lset false) x)) := by
        rintro ⟨h1, h2⟩
        refine hdisj _ _ h1 h2 (by simp [ecPt_eq_iff]) (ecPt .velt x) (ssElem_velt x) ?_
        exact ⟨(ssMem_velt_lset x true x).mpr rfl, (ssMem_velt_lset x false x).mpr rfl⟩
      cases s with
      | true => exact Iff.rfl
      | false =>
        change G (ecPt (.lset false) x) ↔ ¬G (ecPt (.lset true) x)
        constructor
        · exact fun h h' => hnot ⟨h', h⟩
        · exact fun h => hone.resolve_left h
    refine ⟨fun z => G (ecPt (.lset true) z), fun c hc => ?_⟩
    obtain ⟨S, hS, hmem⟩ := hcov (ecPt .celt c) ((ssElem_celt c).mpr hc)
    obtain ⟨s, x, rfl⟩ := ssFam_cases (hGfam S hS)
    refine ⟨x, s, (ssMem_celt_lset c s x).mp hmem, (hkey x s).mp hS, fun y t hy hTy => ?_⟩
    by_contra hne
    refine hdisj _ _ ((hkey y t).mpr hTy) hS ?_ (ecPt .celt c) ((ssElem_celt c).mpr hc)
      ⟨(ssMem_celt_lset c t y).mpr hy, hmem⟩
    rw [Ne, ecPt_eq_iff]
    rintro ⟨ht, rfl⟩
    exact hne ⟨rfl, by simpa using ht⟩

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
  correct A _ _ := oneInSatisfiable_iff_hasExactCover A

/-! ### NP-completeness -/

/-- Exact Cover is NP-hard: 1-in-SAT, which is NP-hard, FO-reduces to it. -/
theorem exactCover_NP_hard : NP.Hard ExactCover :=
  NP.hard_of_foReduction oneInSat_fo_reduction_exactCover oneInSat_NP_hard

/-- **Exact Cover is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. -/
theorem exactCover_NP_complete : NP.Complete ExactCover :=
  ⟨exactCover_mem_NP, exactCover_NP_hard⟩

end DescriptiveComplexity
