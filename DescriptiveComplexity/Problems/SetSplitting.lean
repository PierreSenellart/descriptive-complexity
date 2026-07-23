/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily
import DescriptiveComplexity.Problems.NaeThreeSat
import DescriptiveComplexity.Problems.ThreeSat.ToSat

/-!
# Set Splitting is NP-complete

SET SPLITTING, also known as hypergraph 2-colourability: can the ground
elements of a set system be coloured with two colours so that no set of the
family is monochromatic? Like Exact Cover it lives on
`FirstOrder.Language.setSystem` unchanged (`DescriptiveComplexity.SetSplitting`,
`DescriptiveComplexity.Problems.SetFamily.Defs`) and carries no threshold – the
colouring, not a cardinality, is the whole question.

Hardness comes from NAE-SAT (`DescriptiveComplexity.Problems.NaeSat`) by a reduction
with **no gadget and no counting**, order-free and of dimension 1:

* the ground elements are the *literals* `(x, s)`;
* the family has one set `{x, ¬x}` per variable, and one set per clause,
  holding its literals.

A two-colouring splits the pair `{x, ¬x}` exactly when it gives the two
literals of `x` opposite colours – that *is* a truth assignment – and it
splits a clause set exactly when the clause has both a true and a false
literal, which is not-all-equal satisfaction. The correspondence is so direct
that the reduction is essentially the identity on clauses; only the pair sets
are new, and they are what turns an arbitrary colouring into an assignment.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace SetSplitRed

open Language Structure SatOcc

/-- Tags of the reduction: the ground element of a literal, the set of a
variable, and the set of a clause. -/
inductive SplTag : Type
  /-- The ground element of the literal `(x, s)`. -/
  | lit (s : Bool)
  /-- The set `{x, ¬x}` of the variable `x`. -/
  | pairSet
  /-- The set of the literals of a clause. -/
  | clSet
  deriving DecidableEq

instance : Fintype SplTag where
  elems := {SplTag.lit true, SplTag.lit false, SplTag.pairSet, SplTag.clSet}
  complete := by
    intro t
    cases t with
    | lit s => cases s <;> decide
    | pairSet => decide
    | clSet => decide

instance : Nonempty SplTag := ⟨SplTag.pairSet⟩

/-! ### The interpretation -/

/-- Defining formula for the ground elements: the literals. -/
noncomputable def elemF : SplTag → Language.sat.Formula (Fin 1 × Fin 1)
  | .lit _ => ⊤
  | _ => ⊥

/-- Defining formula for the family: one set per variable and one per
clause. -/
noncomputable def famF : SplTag → Language.sat.Formula (Fin 1 × Fin 1)
  | .pairSet => ⊤
  | .clSet => ThreeSatToSat.clF (0, 0)
  | .lit _ => ⊥

/-- Defining formula for incidence: the pair set of `x` holds both literals of
`x`, and the set of a clause holds the literals occurring in it. -/
noncomputable def memF : SplTag → SplTag → Language.sat.Formula (Fin 2 × Fin 1)
  | .lit _, .pairSet => ThreeSatToSat.eqF (0, 0) (1, 0)
  | .lit s, .clSet => ThreeSatToSat.occF s (1, 0) (0, 0)
  | _, _ => ⊥

/-- The interpretation of Set Splitting instances in CNF instances. -/
noncomputable def splInterp : FOInterpretation Language.sat Language.setSystem SplTag 1 where
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
def splPt (t : SplTag) (x : A) : splInterp.Map A := (t, fun _ => x)

theorem splPt_eq_iff {t t' : SplTag} {x x' : A} :
    splPt t x = splPt t' x' ↔ t = t' ∧ x = x' := by
  constructor
  · intro h
    exact ⟨by simpa [splPt] using congrArg (fun p : splInterp.Map A => p.1) h,
      by simpa [splPt] using congrArg (fun p : splInterp.Map A => p.2 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem splPt_surj (q : splInterp.Map A) : ∃ t x, q = splPt t x :=
  ⟨q.1, q.2 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg q.2 (Subsingleton.elim i 0)⟩⟩

end Points

/-! ### Characterization of the four relations -/

section Characterizations

variable {A : Type} [Language.sat.Structure A]

@[simp]
theorem ssElem_lit (s : Bool) (x : A) : SSElem (splPt (.lit s) x) := by
  rw [SSElem, splPt, FOInterpretation.relMap_map]
  simp [splInterp, elemF]

@[simp]
theorem ssElem_pairSet (x : A) : ¬SSElem (splPt .pairSet x) := by
  rw [SSElem, splPt, FOInterpretation.relMap_map]
  simp [splInterp, elemF]

@[simp]
theorem ssElem_clSet (x : A) : ¬SSElem (splPt .clSet x) := by
  rw [SSElem, splPt, FOInterpretation.relMap_map]
  simp [splInterp, elemF]

@[simp]
theorem ssFam_pairSet (x : A) : SSFam (splPt .pairSet x) := by
  rw [SSFam, splPt, FOInterpretation.relMap_map]
  simp [splInterp, famF]

@[simp]
theorem ssFam_clSet (c : A) : SSFam (splPt .clSet c) ↔ IsCl c := by
  rw [SSFam, splPt, FOInterpretation.relMap_map]
  simp [splInterp, famF, ThreeSatToSat.realize_clF, IsCl]

@[simp]
theorem ssFam_lit (s : Bool) (x : A) : ¬SSFam (splPt (.lit s) x) := by
  rw [SSFam, splPt, FOInterpretation.relMap_map]
  simp [splInterp, famF]

@[simp]
theorem ssMem_lit_pairSet (s : Bool) (x y : A) :
    SSMem (splPt (.lit s) x) (splPt .pairSet y) ↔ x = y := by
  rw [SSMem, splPt, splPt, FOInterpretation.relMap_map]
  simp [splInterp, memF, ThreeSatToSat.realize_eqF]

@[simp]
theorem ssMem_lit_clSet (s : Bool) (x c : A) :
    SSMem (splPt (.lit s) x) (splPt .clSet c) ↔ OccIn c x s := by
  rw [SSMem, splPt, splPt, FOInterpretation.relMap_map]
  simp [splInterp, memF, ThreeSatToSat.realize_occF]

/-- The ground elements are exactly the literals. -/
theorem ssElem_cases {q : splInterp.Map A} (h : SSElem q) : ∃ s x, q = splPt (.lit s) x := by
  obtain ⟨t, x, rfl⟩ := splPt_surj q
  cases t with
  | lit s => exact ⟨s, x, rfl⟩
  | pairSet => exact absurd h (ssElem_pairSet x)
  | clSet => exact absurd h (ssElem_clSet x)

/-- The sets of the family are the pair sets and the clause sets. -/
theorem ssFam_cases {q : splInterp.Map A} (h : SSFam q) :
    (∃ x, q = splPt .pairSet x) ∨ ∃ c, IsCl c ∧ q = splPt .clSet c := by
  obtain ⟨t, x, rfl⟩ := splPt_surj q
  cases t with
  | lit s => exact absurd h (ssFam_lit s x)
  | pairSet => exact Or.inl ⟨x, rfl⟩
  | clSet => exact Or.inr ⟨x, (ssFam_clSet x).mp h, rfl⟩

end Characterizations

/-! ### Correctness -/

section Correctness

variable (A : Type) [Language.sat.Structure A]

/-- Correctness of the reduction: a CNF structure is not-all-equal satisfiable
iff its literal set system can be split. -/
theorem naeSatisfiable_iff_hasSetSplitting :
    NAESatisfiable A ↔ HasSetSplitting (splInterp.Map A) := by
  constructor
  · -- the true literals of a not-all-equal assignment are a splitting colour
    rintro ⟨ν, hν⟩
    refine ⟨fun p => ∃ s x, p = splPt (.lit s) x ∧ LitTrue ν x s, fun f hf => ?_⟩
    have hcol : ∀ (s : Bool) (x : A),
        (∃ s' x', splPt (.lit s) x = splPt (.lit s') x' ∧ LitTrue ν x' s') ↔
          LitTrue ν x s := by
      intro s x
      constructor
      · rintro ⟨s', x', heq, hT⟩
        obtain ⟨hs, hx⟩ := splPt_eq_iff.mp heq
        obtain rfl : s = s' := by simpa using hs
        exact hx ▸ hT
      · exact fun hT => ⟨s, x, rfl, hT⟩
    rcases ssFam_cases hf with ⟨x, rfl⟩ | ⟨c, hc, rfl⟩
    · -- the pair of a variable is split by the assignment itself
      by_cases hx : ν x
      · exact ⟨⟨splPt (.lit true) x, ssElem_lit true x,
            (ssMem_lit_pairSet true x x).mpr rfl, (hcol true x).mpr hx⟩,
          splPt (.lit false) x, ssElem_lit false x,
            (ssMem_lit_pairSet false x x).mpr rfl, fun h => (hcol false x).mp h hx⟩
      · exact ⟨⟨splPt (.lit false) x, ssElem_lit false x,
            (ssMem_lit_pairSet false x x).mpr rfl, (hcol false x).mpr hx⟩,
          splPt (.lit true) x, ssElem_lit true x,
            (ssMem_lit_pairSet true x x).mpr rfl, fun h => hx ((hcol true x).mp h)⟩
    · -- a clause is split because it has a true and a false literal
      obtain ⟨⟨y, t, hy, hTy⟩, ⟨z, u, hz, hFz⟩⟩ := naeProper_occ hν c hc
      exact ⟨⟨splPt (.lit t) y, ssElem_lit t y, (ssMem_lit_clSet t y c).mpr hy,
          (hcol t y).mpr hTy⟩,
        splPt (.lit u) z, ssElem_lit u z, (ssMem_lit_clSet u z c).mpr hz,
          fun h => hFz ((hcol u z).mp h)⟩
  · -- a splitting colour reads off a not-all-equal assignment
    rintro ⟨S, hS⟩
    -- the two literals of a variable get opposite colours
    have hkey : ∀ (x : A) (s : Bool),
        S (splPt (.lit s) x) ↔ LitTrue (fun z => S (splPt (.lit true) z)) x s := by
      intro x s
      obtain ⟨⟨p, hp, hmp, hSp⟩, ⟨q, hq, hmq, hSq⟩⟩ := hS (splPt .pairSet x) (ssFam_pairSet x)
      obtain ⟨sp, yp, rfl⟩ := ssElem_cases hp
      obtain ⟨sq, yq, rfl⟩ := ssElem_cases hq
      rw [(ssMem_lit_pairSet sp yp x).mp hmp] at hSp
      rw [(ssMem_lit_pairSet sq yq x).mp hmq] at hSq
      have hne : sp ≠ sq := by
        rintro rfl
        exact hSq hSp
      cases s with
      | true => exact Iff.rfl
      | false =>
        change S (splPt (.lit false) x) ↔ ¬S (splPt (.lit true) x)
        cases sp <;> cases sq <;> simp_all
    refine ⟨fun z => S (splPt (.lit true) z), naeProper_of_occ fun c hc => ?_⟩
    obtain ⟨⟨p, hp, hmp, hSp⟩, ⟨q, hq, hmq, hSq⟩⟩ :=
      hS (splPt .clSet c) ((ssFam_clSet c).mpr hc)
    obtain ⟨sp, yp, rfl⟩ := ssElem_cases hp
    obtain ⟨sq, yq, rfl⟩ := ssElem_cases hq
    exact ⟨⟨yp, sp, (ssMem_lit_clSet sp yp c).mp hmp, (hkey yp sp).mp hSp⟩,
      yq, sq, (ssMem_lit_clSet sq yq c).mp hmq, fun h => hSq ((hkey yq sq).mpr h)⟩

end Correctness

end SetSplitRed

open SetSplitRed in
/-- **NAE-SAT FO-reduces to Set Splitting**: the ground elements are the
literals, the family holds one pair set per variable and one set per clause.
No order, no gadget and no counting. -/
noncomputable def naeSat_fo_reduction_setSplitting : NAESAT ≤ᶠᵒ SetSplitting where
  Tag := SplTag
  dim := 1
  toInterpretation := splInterp
  correct A _ _ := naeSatisfiable_iff_hasSetSplitting A

/-! ### NP-completeness -/

/-- Set Splitting is in NP: it is `Σ₁`-definable. -/
theorem setSplitting_mem_NP : SetSplitting ∈ NP :=
  setSplitting_sigmaSODefinable

/-- Set Splitting is NP-hard: NAE-SAT, which is NP-hard, FO-reduces to it. -/
theorem setSplitting_NP_hard : NP.Hard SetSplitting :=
  NP.hard_of_foReduction naeSat_fo_reduction_setSplitting naeSat_NP_hard

/-- **Set Splitting is NP-complete**, derived from the first-order reductions
of this library and the Cook–Levin theorem. -/
theorem setSplitting_NP_complete : NP.Complete SetSplitting :=
  ⟨setSplitting_mem_NP, setSplitting_NP_hard⟩

end DescriptiveComplexity
