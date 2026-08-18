/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogSpace
import DescriptiveComplexity.Problems.TwoSat.Defs

/-!
# 2SAT is SO-Krom definable, hence in NL

The membership half of the completeness of 2SAT for `DescriptiveComplexity.NL`: a Krom
program (`DescriptiveComplexity.TwoSatKrom.twoSatProgram`) whose satisfying assignments
are exactly the satisfying truth assignments of a width-two CNF structure, so
`DescriptiveComplexity.twoSat_mem_NL`.

The program is the natural one, and it shows what the guards of the Krom
fragment buy. Guess the truth assignment as the single unary relation variable
of `DescriptiveComplexity.satAssignBlock`, universally quantify three first-order
variables `c, x, y`, and emit:

* for each pair of signs `(s, u)`, the clause whose guard says “`c` is a clause,
  `(x, s)` and `(y, u)` are occurrences of `c`, and *every* occurrence of `c` is
  one of these two”, with the 2-clause `ℓ(x, s) ∨ ℓ(y, u)` as its body. A clause
  with a single occurrence is covered by instantiating `y := x`, `u := s`, which
  emits `ℓ(x, s) ∨ ℓ(x, s)`: no separate unit clause is needed;
* the goal clause guarded by “`c` is an empty clause” – an empty clause makes
  the CNF unsatisfiable;
* the goal clause guarded by “some clause has three distinct occurrences”
  (`DescriptiveComplexity.wideTwoOrdF`) – this is how the *width promise* of 2SAT is
  enforced from inside the fragment: guards are first-order over the input, so a
  promise costs one goal clause and no second-order machinery.

Correctness rests on `DescriptiveComplexity.exists_covering_pair`: under the width
bound, a clause with an occurrence has two signed occurrences covering all of
them, which is exactly the shape a single 2-clause can speak about.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

namespace TwoSatKrom

/-! ### The atoms and the guards -/

/-- The atom “the guessed truth assignment holds of the `p`-th universally
quantified variable”. -/
def nuAtom (p : Fin 3) : SOAtom satAssignBlock 3 where
  idx := ()
  args := fun _ => p

/-- The literal of the occurrence with sign `s` at the `p`-th variable: the
truth assignment must make it true. -/
def nuLit (p : Fin 3) (s : Bool) : KromLit satAssignBlock 3 where
  atom := nuAtom p
  positive := s

/-- The covering condition, as a formula over the ordered expansion: every
occurrence of the clause `0` is the occurrence `(1, s)` or the occurrence
`(2, u)`. -/
noncomputable def coverF (s u : Bool) : satOrd.Formula (Fin 3) :=
  (Formula.iInf fun t : Bool =>
    (occF t (Sum.inl 0) (Sum.inr 0)).imp
      ((if t = s then eqF (Sum.inr 0) (Sum.inl 1) else ⊥) ⊔
        if t = u then eqF (Sum.inr 0) (Sum.inl 2) else ⊥)).iAlls (Fin 1)

/-- The guard of the two-literal clause of the program: `0` is a clause whose
occurrences are exactly `(1, s)` and `(2, u)`. -/
noncomputable def pairGuard (s u : Bool) : satOrd.Formula (Fin 3) :=
  clF 0 ⊓ occF s 0 1 ⊓ occF u 0 2 ⊓ coverF s u

/-! ### Realization of the guards -/

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : Fin 3 → A}

theorem realize_coverF {s u : Bool} :
    (coverF s u).Realize v ↔
      ∀ z t, OccIn (v 0) z t → (z = v 1 ∧ t = s) ∨ (z = v 2 ∧ t = u) := by
  simp only [coverF, Formula.realize_iAlls, Formula.realize_iInf, Formula.realize_imp,
    Formula.realize_sup, realize_occF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h z t hz
    rcases h (fun _ => z) t hz with h' | h'
    · left
      cases s <;> cases t <;> simp_all
    · right
      cases u <;> cases t <;> simp_all
  · intro h i t hi
    rcases h (i 0) t hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      subst h2
      simpa using h1
    · right
      subst h2
      simpa using h1

theorem realize_pairGuard {s u : Bool} :
    (pairGuard s u).Realize v ↔
      IsCl (v 0) ∧ OccIn (v 0) (v 1) s ∧ OccIn (v 0) (v 2) u ∧
        ∀ z t, OccIn (v 0) z t → (z = v 1 ∧ t = s) ∨ (z = v 2 ∧ t = u) := by
  simp only [pairGuard, Formula.realize_inf, realize_clF, realize_occF, realize_coverF]
  tauto

end Realize

/-! ### The program -/

/-- The two-literal clause of the program, for a pair of signs. -/
noncomputable def pairClause (s u : Bool) : KromClause satOrd satAssignBlock 3 where
  guard := pairGuard s u
  lit₁ := some (nuLit 1 s)
  lit₂ := some (nuLit 2 u)

/-- The goal clause firing on an empty clause of the input. -/
noncomputable def emptyClause : KromClause satOrd satAssignBlock 3 where
  guard := emptyClF 0
  lit₁ := none
  lit₂ := none

/-- The goal clause firing when the width promise of 2SAT is violated. -/
noncomputable def wideClause : KromClause satOrd satAssignBlock 3 where
  guard := wideTwoOrdF
  lit₁ := none
  lit₂ := none

/-- The Krom program defining 2SAT: one two-literal clause per pair of signs,
plus the two goal clauses for the empty clause and for the width promise. -/
noncomputable def twoSatProgram : KromProgram satOrd satAssignBlock 3 :=
  [pairClause true true, pairClause true false, pairClause false true,
    pairClause false false, emptyClause, wideClause]

theorem pairClause_mem (s u : Bool) : pairClause s u ∈ twoSatProgram := by
  cases s <;> cases u <;> simp [twoSatProgram]

theorem emptyClause_mem : emptyClause ∈ twoSatProgram := by
  simp [twoSatProgram]

theorem wideClause_mem : wideClause ∈ twoSatProgram := by
  simp [twoSatProgram]

/-! ### Assignments on both sides -/

section Assignments

variable {A : Type} [Language.sat.Structure A]

/-- The block assignment induced by a truth assignment. -/
def ofTruth (ν : A → Prop) : satAssignBlock.Assignment A :=
  fun _ w => ν (w ⟨0, Nat.one_pos⟩)

/-- The truth assignment induced by a block assignment. -/
def toTruth (ρ : satAssignBlock.Assignment A) : A → Prop :=
  fun a => ρ () fun _ => a

omit [Language.sat.Structure A] in
theorem nuLit_holds_ofTruth (ν : A → Prop) (p : Fin 3) (s : Bool) (v : Fin 3 → A) :
    (nuLit p s).Holds (ofTruth ν) v ↔ LitTrue ν (v p) s := by
  cases s <;> exact Iff.rfl

omit [Language.sat.Structure A] in
theorem nuLit_holds_toTruth (ρ : satAssignBlock.Assignment A) (p : Fin 3) (s : Bool)
    (v : Fin 3 → A) : (nuLit p s).Holds ρ v ↔ LitTrue (toTruth ρ) (v p) s := by
  cases s <;> exact Iff.rfl

end Assignments

/-! ### The program holds of a satisfying truth assignment -/

section Soundness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {ν : A → Prop}

/-- A two-literal clause holds: the input clause has a true occurrence, and the
guard says that every occurrence of it is one of the clause's two literals. -/
theorem pairClause_holds (hν : ∀ c : A, IsCl c → ∃ x s, OccIn c x s ∧ LitTrue ν x s)
    (s u : Bool) (v : Fin 3 → A) :
    (pairClause s u).Holds (ofTruth ν) v := by
  intro hguard
  obtain ⟨hcl, -, -, hcov⟩ := realize_pairGuard.mp hguard
  obtain ⟨z, t, hzt, hzT⟩ := hν (v 0) hcl
  rcases hcov z t hzt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ((nuLit_holds_ofTruth ν 1 t v).mpr hzT)
  · exact Or.inr ((nuLit_holds_ofTruth ν 2 t v).mpr hzT)

/-- The empty-clause goal clause holds: a satisfied structure has no empty
clause, so its guard is false. -/
theorem emptyClause_holds (hν : ∀ c : A, IsCl c → ∃ x s, OccIn c x s ∧ LitTrue ν x s)
    (v : Fin 3 → A) : emptyClause.Holds (ofTruth ν) v := by
  intro hguard
  have hempty : EmptyCl (v 0) := realize_emptyClF.mp hguard
  obtain ⟨z, t, hzt, -⟩ := hν (v 0) hempty.1
  exact absurd hzt (hempty.2 z t)

/-- The width goal clause holds: under the promise, its guard is false. -/
theorem wideClause_holds (hw : WidthAtMostTwo A) (ν : A → Prop) (v : Fin 3 → A) :
    wideClause.Holds (ofTruth ν) v := by
  intro hguard
  exact absurd hw (wideTwo_iff_not_widthAtMostTwo.mp (realize_wideTwoOrdF.mp hguard))

end Soundness

end TwoSatKrom

/-! ### 2SAT is SO-Krom definable -/

open TwoSatKrom in
/-- **2SAT is SO-Krom definable**: guess the truth assignment, and let the
guards do the rest – one 2-clause per clause of the input (read through a
covering pair of occurrences), one goal clause for empty clauses and one for a
violated width promise. Since NL is *defined* as SO-Krom definability, this is
the statement `TwoSAT ∈ NL`. -/
theorem twoSat_sigmaSOKromDefinable : SigmaSOKromDefinable TwoSAT := by
  refine ⟨satAssignBlock, 3, twoSatProgram, ?_⟩
  intro A _ _ _ _
  constructor
  · -- a satisfying truth assignment of a width-two structure satisfies the program
    rintro ⟨hw, ν, hν⟩
    have hocc := satClauses_occ hν
    refine ⟨ofTruth ν, fun v c hc => ?_⟩
    simp only [twoSatProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact pairClause_holds hocc _ _ v
    · exact pairClause_holds hocc _ _ v
    · exact pairClause_holds hocc _ _ v
    · exact pairClause_holds hocc _ _ v
    · exact emptyClause_holds hocc v
    · exact wideClause_holds hw ν v
  · -- a satisfying assignment of the program is a width-two satisfying assignment
    rintro ⟨ρ, hρ⟩
    have hwidth : WidthAtMostTwo A := by
      by_contra hnw
      have hwide := (wideTwo_iff_not_widthAtMostTwo (A := A)).mpr hnw
      have h := hρ (fun _ => Classical.arbitrary A) wideClause wideClause_mem
      have hfalse := h (realize_wideTwoOrdF.mpr hwide)
      simp [wideClause, KromLit.slotHolds] at hfalse
    refine ⟨hwidth, toTruth ρ, fun c hcl => ?_⟩
    by_cases hocc : ∃ z t, OccIn c z t
    · -- read the clause of the program covering `c`
      obtain ⟨x, s, hx⟩ := hocc
      obtain ⟨y, u, hy, hcov⟩ := exists_covering_pair hwidth hx
      have h := hρ ![c, x, y] (pairClause s u) (pairClause_mem s u)
      have hguard : (pairGuard s u).Realize ![c, x, y] := by
        refine realize_pairGuard.mpr ⟨hcl, ?_, ?_, ?_⟩
        · simpa using hx
        · simpa using hy
        · simpa using hcov
      rcases h hguard with hlit | hlit
      · have hT := (nuLit_holds_toTruth ρ 1 s ![c, x, y]).mp hlit
        simp only [Matrix.cons_val_one] at hT
        cases s with
        | false => exact ⟨x, Or.inr ⟨hx.2, hT⟩⟩
        | true => exact ⟨x, Or.inl ⟨hx.2, hT⟩⟩
      · have hT := (nuLit_holds_toTruth ρ 2 u ![c, x, y]).mp hlit
        simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hT
        cases u with
        | false => exact ⟨y, Or.inr ⟨hy.2, hT⟩⟩
        | true => exact ⟨y, Or.inl ⟨hy.2, hT⟩⟩
    · -- no occurrence at all: the empty-clause goal clause is violated
      push Not at hocc
      have h := hρ (fun _ => c) emptyClause emptyClause_mem
      have hguard : (emptyClF (0 : Fin 3)).Realize (fun _ => c) :=
        realize_emptyClF.mpr ⟨hcl, fun z t => hocc z t⟩
      have hfalse := h hguard
      simp [emptyClause, KromLit.slotHolds] at hfalse

/-- **2SAT is in NL.** -/
theorem twoSat_mem_NL : TwoSAT ∈ NL :=
  twoSat_sigmaSOKromDefinable

end DescriptiveComplexity
