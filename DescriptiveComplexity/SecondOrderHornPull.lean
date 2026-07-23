/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderHorn
import DescriptiveComplexity.SecondOrderPull
import DescriptiveComplexity.OrderedComposition

/-!
# Pulling SO-Horn definability back through an interpretation

SO-Horn definability is closed under (ordered) first-order reductions
(`DescriptiveComplexity.SigmaSOHornDefinable.of_orderedReduction`). This is what makes
the fragment a `DescriptiveComplexity.ComplexityClass` – the class
`DescriptiveComplexity.PTIME` – rather than a mere definability predicate.

The closure is *not* an instance of the general pullback of
`DescriptiveComplexity.SecondOrderPull`, which only says that the pulled-back kernel is
some first-order formula: here the pulled-back kernel has to stay *Horn*. It
does, and for a structural reason worth stating, since it is exactly what the
Horn condition is careful about: the condition constrains the occurrences of
the *second-order* variables only, while an interpretation rewrites the
*input-vocabulary* atoms – which live in the guard, where anything is allowed.
Concretely, pulling a clause back through a `d`-dimensional interpretation
with tag type `Tag`:

* the block is pulled as in `DescriptiveComplexity.SOBlock.pull`: an `n`-ary relation
  variable on `Tag × A^d` becomes one `(n·d)`-ary relation variable on `A` per
  `n`-tuple of tags;
* a clause becomes one clause per assignment `t : Fin k → Tag` of tags to its
  universally quantified variables (`DescriptiveComplexity.HornClause.pull`), with the
  `k` variables replaced by `k · d` coordinates;
* its guard becomes the ordinary formula pullback
  `DescriptiveComplexity.FOInterpretation.pull` at the tag assignment `t` – an arbitrary
  first-order formula, which is fine, guards being unconstrained;
* each body and head atom becomes the atom of the corresponding pulled
  relation variable (`DescriptiveComplexity.SOAtom.pull`) – *still an atom*, which is
  what keeps the clause Horn.

The one place the order is needed is that the guards of the target may mention
it: the pullback interprets the target's order by the lexicographic order on
tagged tuples (`DescriptiveComplexity.FOInterpretation.ordExtend`), which is why the
definability notion quantifies over ordered structures in the first place.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}
variable {B : SOBlock} {k : ℕ}

/-! ### Pulling back an atom -/

/-- The pullback of a second-order atom at a static assignment of tags to the
universally quantified variables: the atom of the pulled relation variable
selected by the tags, its arguments the `d` coordinates of each original
argument. -/
def SOAtom.pull (a : SOAtom B k) (d : ℕ) (t : Fin k → Tag) :
    SOAtom (B.pull Tag d) (k * d) where
  idx := ⟨a.idx, fun j => t (a.args j)⟩
  args := fun m =>
    finProdFinEquiv (a.args (finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)

/-- The interpreted valuation determined by a tag assignment and a valuation
of the coordinates. -/
def tagVal (I : FOInterpretation L₁ L₂ Tag d) {A : Type} (t : Fin k → Tag)
    (w : Fin (k * d) → A) : Fin k → I.Map A :=
  fun p => (t p, fun j => w (finProdFinEquiv (p, j)))

theorem SOAtom.pull_holds {A : Type} (I : FOInterpretation L₁ L₂ Tag d) (a : SOAtom B k)
    (t : Fin k → Tag) (ρ : B.Assignment (I.Map A)) (w : Fin (k * d) → A) :
    (a.pull d t).Holds (B.pullAssign ρ) w ↔ a.Holds ρ (tagVal I t w) := by
  refine iff_of_eq (congrArg (ρ a.idx) (funext fun j => ?_))
  refine Prod.ext_iff.mpr ⟨rfl, funext fun i => ?_⟩
  refine congrArg w ?_
  change finProdFinEquiv (a.args (finProdFinEquiv.symm (finProdFinEquiv (j, i))).1,
    (finProdFinEquiv.symm (finProdFinEquiv (j, i))).2) = finProdFinEquiv (a.args j, i)
  rw [Equiv.symm_apply_apply]

/-! ### Pulling back a guard -/

variable [L₂.IsRelational]

/-- The pullback of a guard: the ordinary formula pullback at the tag
assignment `t`, its variables re-indexed as coordinates. -/
noncomputable def guardPull (I : FOInterpretation L₁ L₂ Tag d) (φ : L₂.Formula (Fin k))
    (t : Fin k → Tag) : L₁.Formula (Fin (k * d)) :=
  (I.pull (φ : L₂.BoundedFormula (Fin k) 0) (Sum.elim t finZeroElim)).relabel
    fun p => finProdFinEquiv (Sum.elim id finZeroElim p.1, p.2)

theorem realize_guardPull {A : Type} [L₁.Structure A] (I : FOInterpretation L₁ L₂ Tag d)
    (φ : L₂.Formula (Fin k)) (t : Fin k → Tag) (w : Fin (k * d) → A) :
    (guardPull I φ t).Realize w ↔ φ.Realize (M := I.Map A) (tagVal I t w) := by
  rw [guardPull, Formula.realize_relabel, I.realize_pull]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.Map A) (φ : L₂.BoundedFormula (Fin k) 0) a b)
    (funext fun _ => rfl) (Subsingleton.elim _ _))

/-! ### Pulling back a clause and a program -/

/-- The pullback of a Horn clause at a tag assignment: guards pull back as
formulas, atoms as atoms – so the result is again a Horn clause. -/
noncomputable def HornClause.pull (I : FOInterpretation L₁ L₂ Tag d)
    (c : HornClause L₂ B k) (t : Fin k → Tag) : HornClause L₁ (B.pull Tag d) (k * d) where
  guard := guardPull I c.guard t
  body := c.body.map fun a => a.pull d t
  head := c.head.map fun a => a.pull d t

theorem HornClause.pull_holds {A : Type} [L₁.Structure A]
    (I : FOInterpretation L₁ L₂ Tag d) (c : HornClause L₂ B k) (t : Fin k → Tag)
    (ρ : B.Assignment (I.Map A)) (w : Fin (k * d) → A) :
    (c.pull I t).Holds (B.pullAssign ρ) w ↔ c.Holds ρ (tagVal I t w) := by
  have hhead : (c.pull I t).HeadHolds (B.pullAssign ρ) w ↔ c.HeadHolds ρ (tagVal I t w) := by
    rw [HornClause.HeadHolds, HornClause.HeadHolds, HornClause.pull]
    cases c.head with
    | none => exact Iff.rfl
    | some a => exact a.pull_holds I t ρ w
  refine imp_congr (and_congr ?_ ?_) hhead
  · exact realize_guardPull I c.guard t w
  · rw [HornClause.pull]
    constructor
    · intro h a ha
      exact (a.pull_holds I t ρ w).mp (h _ (List.mem_map_of_mem ha))
    · intro h a' ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      exact (a.pull_holds I t ρ w).mpr (h a ha)

open Classical in
/-- All assignments of tags to the `k` universally quantified variables, as a
list: the pullback of a clause is instantiated at each of them. -/
noncomputable def allTagAssign (Tag : Type) [Finite Tag] (k : ℕ) : List (Fin k → Tag) :=
  letI : Fintype Tag := Fintype.ofFinite Tag
  (Finset.univ : Finset (Fin k → Tag)).toList

open Classical in
theorem mem_allTagAssign (t : Fin k → Tag) : t ∈ allTagAssign Tag k := by
  letI : Fintype Tag := Fintype.ofFinite Tag
  exact Finset.mem_toList.mpr (Finset.mem_univ t)

/-- The pullback of a Horn program: one clause per clause of the program and
per assignment of tags to its universally quantified variables. -/
noncomputable def HornProgram.pull (I : FOInterpretation L₁ L₂ Tag d)
    (prog : HornProgram L₂ B k) : HornProgram L₁ (B.pull Tag d) (k * d) :=
  prog.flatMap fun c => (allTagAssign Tag k).map fun t => c.pull I t

theorem HornProgram.pull_mem (I : FOInterpretation L₁ L₂ Tag d)
    {prog : HornProgram L₂ B k} {c : HornClause L₂ B k} (hc : c ∈ prog)
    (t : Fin k → Tag) : c.pull I t ∈ prog.pull I := by
  rw [HornProgram.pull, List.mem_flatMap]
  exact ⟨c, hc, List.mem_map.mpr ⟨t, mem_allTagAssign t, rfl⟩⟩

theorem HornProgram.pull_cases (I : FOInterpretation L₁ L₂ Tag d)
    {prog : HornProgram L₂ B k} {c' : HornClause L₁ (B.pull Tag d) (k * d)}
    (hc' : c' ∈ prog.pull I) : ∃ c ∈ prog, ∃ t : Fin k → Tag, c' = c.pull I t := by
  rw [HornProgram.pull, List.mem_flatMap] at hc'
  obtain ⟨c, hc, hmem⟩ := hc'
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hmem
  exact ⟨c, hc, t, rfl⟩

/-! ### Correctness of the pullback -/

section Correctness

variable {A : Type} [L₁.Structure A] (I : FOInterpretation L₁ L₂ Tag d)
variable (prog : HornProgram L₂ B k)

omit [Finite Tag] [L₂.IsRelational] [L₁.Structure A] in
/-- Splitting an interpreted valuation into its tags and its coordinates. -/
theorem tagVal_split (v : Fin k → I.Map A) :
    tagVal I (fun p => (v p).1)
      (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2) = v := by
  funext p
  refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
  rw [tagVal]
  exact congrArg₂ (fun (q : Fin k) (i : Fin d) => (v q).2 i)
    (congrArg Prod.fst (Equiv.symm_apply_apply _ _))
    (congrArg Prod.snd (Equiv.symm_apply_apply _ _))

/-- An assignment satisfies a program on the interpreted structure iff its
transfer satisfies the pulled program on the base structure. -/
theorem HornProgram.pull_holds (ρ : B.Assignment (I.Map A)) :
    (prog.pull I).Holds (B.pullAssign ρ) ↔ prog.Holds ρ := by
  constructor
  · intro h v c hc
    have hp := h (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2)
      (c.pull I fun p => (v p).1) (HornProgram.pull_mem I hc _)
    have h2 := (HornClause.pull_holds I c (fun p => (v p).1) ρ _).mp hp
    rwa [tagVal_split I v] at h2
  · intro h w c' hc'
    obtain ⟨c, hc, t, rfl⟩ := HornProgram.pull_cases I hc'
    exact (HornClause.pull_holds I c t ρ w).mpr (h (tagVal I t w) c hc)

/-- **The pullback is correct**: the program is satisfiable on the interpreted
structure iff its pullback is satisfiable on the base structure. -/
theorem exists_holds_pull :
    (∃ ρ : B.Assignment (I.Map A), prog.Holds ρ) ↔
      ∃ σ : (B.pull Tag d).Assignment A, (prog.pull I).Holds σ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨B.pullAssign ρ, (HornProgram.pull_holds I prog ρ).mpr hρ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨B.mergeAssign σ, (HornProgram.pull_holds I prog (B.mergeAssign σ)).mp ?_⟩
    rw [B.pullAssign_mergeAssign σ]
    exact hσ

end Correctness

/-! ### Closure under reductions -/

section Closure

variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **SO-Horn definability is closed under ordered first-order reductions.**
The Horn shape survives the pullback because an interpretation only rewrites
the input-vocabulary atoms, which live in the guards; the second-order atoms
are merely re-indexed. -/
theorem SigmaSOHornDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q)
    (h : SigmaSOHornDefinable Q) : SigmaSOHornDefinable P := by
  obtain ⟨B, k, prog, hprog⟩ := h
  letI := f.tagFinite
  letI := f.tagNonempty
  letI : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨B.pull f.Tag f.dim, k * f.dim,
    HornProgram.pull f.toInterpretation.ordExtend prog, ?_⟩
  intro A _ _ _ _
  letI := f.toInterpretation.mapLinearOrder A
  haveI := f.toInterpretation.map_finite A
  haveI := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hprog (f.toInterpretation.Map A)).trans ?_)
  refine Iff.trans ?_ (exists_holds_pull f.toInterpretation.ordExtend prog)
  exact (exists_holds_equiv (f.toInterpretation.ordExtendLEquiv A) prog).symm

/-- SO-Horn definability is closed under first-order reductions. -/
theorem SigmaSOHornDefinable.of_foReduction (f : P ≤ᶠᵒ Q)
    (h : SigmaSOHornDefinable Q) : SigmaSOHornDefinable P :=
  h.of_orderedReduction f.toOrdered

end Closure

end DescriptiveComplexity
