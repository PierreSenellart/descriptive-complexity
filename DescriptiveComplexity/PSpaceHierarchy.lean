/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.PSpaceCompl
import DescriptiveComplexity.SecondOrderMerge
import DescriptiveComplexity.Problems.HornSat

/-!
# `PH ⊆ PSPACE`

**The theorem**: every level of the polynomial hierarchy is inside polynomial
space (`DescriptiveComplexity.PH_subset_PSPACE`). A `Σₖ` sentence is not a walk,
so this is not a syntactic inclusion; it is two closure properties of SO(TC) put
together, alternated along the quantifier prefix:

* **complement** (`DescriptiveComplexity.SOTCDefinable.compl`, i.e.
  `PSPACE = coPSPACE`, proved in `DescriptiveComplexity.PSpaceCompl`), which turns
  a universal block into an existential one;
* **prefixing an existential block**
  (`DescriptiveComplexity.SOTCDefinable.exBlock`): a walk can carry a guessed
  block in its own state and never touch it again, so `∃R̄. (SO(TC) condition)` is
  again an SO(TC) condition.

The second is the construction of this file. The state of
`DescriptiveComplexity.SOTCSpec.exBlock` is an assignment of the merged block
`DescriptiveComplexity.SOBlock.cons`; its transition sentence is the conjunction
of `DescriptiveComplexity.fixedS` – the guessed component is unchanged, one
universally quantified equivalence per relation variable of it – with the inner
transition sentence read through `DescriptiveComplexity.consTwoLHom`; and its
endpoints are the inner ones read through `DescriptiveComplexity.consOneLHom`.
Because a step never moves the guessed component, a whole walk keeps it fixed
(`DescriptiveComplexity.exBlock_reach`), so accepting is accepting the inner walk
under *some* assignment of it (`DescriptiveComplexity.exBlock_accepts_iff`).

The prefix is then peeled one block at a time
(`DescriptiveComplexity.sotcDefinable_soProblem`), the base case being that a
first-order sentence is a walk with a trivial block and no step. Level `0` of the
hierarchy is not second-order at all and goes through `PTIME ⊆ NP ⊆ PSPACE`.
-/
namespace DescriptiveComplexity

open FirstOrder Language

/-! ### Reading a spec over a block expansion through the merge -/

section LHoms

variable (L : Language.{0, 0}) (B M : SOBlock)

/-- The renaming of a one-copy expansion: the symbols of the guessed block `B`
land in the left component of the merged block. -/
def consOneLHom :
    (((L.sum B.lang).sum Language.order).sum M.lang) →ᴸ
      ((L.sum Language.order).sum (SOBlock.cons B M).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => Sum.inl (Sum.inl g)
    | Sum.inl (Sum.inl (Sum.inr g)) => isEmptyElim g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl (Sum.inl s)) => Sum.inl (Sum.inl s)
    | Sum.inl (Sum.inl (Sum.inr s)) => Sum.inr ⟨Sum.inl s.1, s.2⟩
    | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr s)
    | Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

/-- The renaming of a two-copy expansion: the symbols of the guessed block land
in the left component of the *first* copy of the merged block. -/
def consTwoLHom :
    (((((L.sum B.lang).sum Language.order).sum M.lang).sum M.lang)) →ᴸ
      (((L.sum Language.order).sum (SOBlock.cons B M).lang).sum (SOBlock.cons B M).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl g))) => Sum.inl (Sum.inl (Sum.inl g))
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr g))) => isEmptyElim g
    | Sum.inl (Sum.inl (Sum.inr g)) => isEmptyElim g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl s))) => Sum.inl (Sum.inl (Sum.inl s))
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr s))) => Sum.inl (Sum.inr ⟨Sum.inl s.1, s.2⟩)
    | Sum.inl (Sum.inl (Sum.inr s)) => Sum.inl (Sum.inl (Sum.inr s))
    | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr ⟨Sum.inr s.1, s.2⟩)
    | Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

variable {L B M} {A : Type} [instL : L.Structure A] [LinearOrder A]

theorem consOneLHom_isExpansionOn (ρ₀ : B.Assignment A) (ρ₁ : M.Assignment A) :
    @LHom.IsExpansionOn _ _ (consOneLHom L B M) A
      (@SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
        (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ₀) _) ρ₁)
      (@SOBlock.structure₁ (L.sum Language.order) (SOBlock.cons B M) A
        (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁)) := by
  letI := @SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ₀) _) ρ₁
  letI := @SOBlock.structure₁ (L.sum Language.order) (SOBlock.cons B M) A
    (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁)
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => rfl
    | Sum.inl (Sum.inl (Sum.inr g)) => exact isEmptyElim g
    | Sum.inl (Sum.inr g) => exact isEmptyElim g
    | Sum.inr g => exact isEmptyElim g
  · match r with
    | Sum.inl (Sum.inl (Sum.inl s)) => rfl
    | Sum.inl (Sum.inl (Sum.inr s)) => rfl
    | Sum.inl (Sum.inr s) => rfl
    | Sum.inr s => rfl

theorem consTwoLHom_isExpansionOn (ρ₀ σ₀ : B.Assignment A) (ρ₁ σ₁ : M.Assignment A) :
    @LHom.IsExpansionOn _ _ (consTwoLHom L B M) A
      (@SOBlock.structure₂ ((L.sum B.lang).sum Language.order) M A
        (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ₀) _) ρ₁ σ₁)
      (@SOBlock.structure₂ (L.sum Language.order) (SOBlock.cons B M) A
        (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁) (consAssign σ₀ σ₁)) := by
  letI := @SOBlock.structure₂ ((L.sum B.lang).sum Language.order) M A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ₀) _) ρ₁ σ₁
  letI := @SOBlock.structure₂ (L.sum Language.order) (SOBlock.cons B M) A
    (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁) (consAssign σ₀ σ₁)
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl g))) => rfl
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr g))) => exact isEmptyElim g
    | Sum.inl (Sum.inl (Sum.inr g)) => exact isEmptyElim g
    | Sum.inl (Sum.inr g) => exact isEmptyElim g
    | Sum.inr g => exact isEmptyElim g
  · match r with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl s))) => rfl
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr s))) => rfl
    | Sum.inl (Sum.inl (Sum.inr s)) => rfl
    | Sum.inl (Sum.inr s) => rfl
    | Sum.inr s => rfl

end LHoms

/-! ### The guessed block does not change -/

section Fixed

variable (L : Language.{0, 0}) (B M : SOBlock)

/-- The relation variable `i` of the guessed block, in the first copy of the
merged block. -/
abbrev fstSym (i : B.ι) :
    (((L.sum Language.order).sum (SOBlock.cons B M).lang).sum
      (SOBlock.cons B M).lang).Relations (B.arity i) :=
  Sum.inl (Sum.inr ⟨Sum.inl i, rfl⟩)

/-- The relation variable `i` of the guessed block, in the second copy. -/
abbrev sndSym (i : B.ι) :
    (((L.sum Language.order).sum (SOBlock.cons B M).lang).sum
      (SOBlock.cons B M).lang).Relations (B.arity i) :=
  Sum.inr ⟨Sum.inl i, rfl⟩

/-- The relation variable `i` of the guessed block has the same value in the two
copies of the merged block. -/
noncomputable def fixedAtS (i : B.ι) :
    (((L.sum Language.order).sum (SOBlock.cons B M).lang).sum
      (SOBlock.cons B M).lang).Sentence :=
  Formula.iAlls (Fin (B.arity i))
    (((Relations.formula (fstSym L B M i) fun j => Term.var (Sum.inr j)).imp
        (Relations.formula (sndSym L B M i) fun j => Term.var (Sum.inr j))) ⊓
      ((Relations.formula (sndSym L B M i) fun j => Term.var (Sum.inr j)).imp
        (Relations.formula (fstSym L B M i) fun j => Term.var (Sum.inr j))))

open Classical in
/-- The whole guessed block is unchanged by a step. -/
noncomputable def fixedS :
    (((L.sum Language.order).sum (SOBlock.cons B M).lang).sum
      (SOBlock.cons B M).lang).Sentence :=
  letI := Fintype.ofFinite B.ι
  listInf ((Finset.univ.toList : List B.ι).map (fixedAtS L B M))

variable {L B M} {A : Type} [instL : L.Structure A] [LinearOrder A]

theorem realize_fixedAtS (ρ₀ σ₀ : B.Assignment A) (ρ₁ σ₁ : M.Assignment A) (i : B.ι) :
    @Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (SOBlock.cons B M) A
          (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁) (consAssign σ₀ σ₁))
        (fixedAtS L B M i) ↔
      ∀ x : Fin (B.arity i) → A, ρ₀ i x ↔ σ₀ i x := by
  letI := @SOBlock.structure₂ (L.sum Language.order) (SOBlock.cons B M) A
    (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁) (consAssign σ₀ σ₁)
  rw [fixedAtS, Sentence.Realize, Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  simp only [Formula.realize_inf, Formula.realize_imp, Formula.realize_rel, Term.realize_var,
    Sum.elim_inr]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem realize_fixedS (ρ₀ σ₀ : B.Assignment A) (ρ₁ σ₁ : M.Assignment A) :
    @Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (SOBlock.cons B M) A
          (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁) (consAssign σ₀ σ₁))
        (fixedS L B M) ↔ ρ₀ = σ₀ := by
  classical
  letI := @SOBlock.structure₂ (L.sum Language.order) (SOBlock.cons B M) A
    (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁) (consAssign σ₀ σ₁)
  letI := Fintype.ofFinite B.ι
  rw [fixedS, Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i x
    exact propext ((realize_fixedAtS ρ₀ σ₀ ρ₁ σ₁ i).mp
      (h _ (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩)) x)
  · rintro rfl ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (realize_fixedAtS ρ₀ ρ₀ ρ₁ σ₁ i).mpr fun _ => Iff.rfl

end Fixed

/-! ### Prefixing a specification with a guessed block -/

section ExBlock

variable {L : Language.{0, 0}} (B : SOBlock) (spec : SOTCSpec (L.sum B.lang))

/-- **The walk that guesses a block first**: its state is an assignment of the
merged block, its transition sentence says that the guessed part does not change
and that the rest takes a step of `spec`, and its endpoints are those of
`spec`. -/
noncomputable def SOTCSpec.exBlock : SOTCSpec L where
  B := SOBlock.cons B spec.B
  step := fixedS L B spec.B ⊓ (consTwoLHom L B spec.B).onSentence spec.step
  src := (consOneLHom L B spec.B).onSentence spec.src
  tgt := (consOneLHom L B spec.B).onSentence spec.tgt

variable {B spec} {A : Type} [instL : L.Structure A] [LinearOrder A]

theorem exBlock_isSrc_iff (ρ₀ : B.Assignment A) (ρ₁ : spec.B.Assignment A) :
    (spec.exBlock B).IsSrc (consAssign ρ₀ ρ₁) ↔
      @SOTCSpec.IsSrc (L.sum B.lang) spec A (B.structure₁ ρ₀) _ ρ₁ := by
  letI := B.structure₁ (L := L) ρ₀
  letI := @SOBlock.structure₁ ((L.sum B.lang).sum Language.order) spec.B A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ₀) _) ρ₁
  letI := @SOBlock.structure₁ (L.sum Language.order) (SOBlock.cons B spec.B) A
    (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁)
  haveI := consOneLHom_isExpansionOn (L := L) (B := B) (M := spec.B) ρ₀ ρ₁
  exact LHom.realize_onSentence (M := A) (consOneLHom L B spec.B) spec.src

theorem exBlock_isTgt_iff (ρ₀ : B.Assignment A) (ρ₁ : spec.B.Assignment A) :
    (spec.exBlock B).IsTgt (consAssign ρ₀ ρ₁) ↔
      @SOTCSpec.IsTgt (L.sum B.lang) spec A (B.structure₁ ρ₀) _ ρ₁ := by
  letI := B.structure₁ (L := L) ρ₀
  letI := @SOBlock.structure₁ ((L.sum B.lang).sum Language.order) spec.B A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ₀) _) ρ₁
  letI := @SOBlock.structure₁ (L.sum Language.order) (SOBlock.cons B spec.B) A
    (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁)
  haveI := consOneLHom_isExpansionOn (L := L) (B := B) (M := spec.B) ρ₀ ρ₁
  exact LHom.realize_onSentence (M := A) (consOneLHom L B spec.B) spec.tgt

theorem exBlock_step_iff (ρ₀ σ₀ : B.Assignment A) (ρ₁ σ₁ : spec.B.Assignment A) :
    (spec.exBlock B).Step (consAssign ρ₀ ρ₁) (consAssign σ₀ σ₁) ↔
      (ρ₀ = σ₀ ∧ @SOTCSpec.Step (L.sum B.lang) spec A (B.structure₁ ρ₀) _ ρ₁ σ₁) := by
  letI := B.structure₁ (L := L) ρ₀
  letI := @SOBlock.structure₂ ((L.sum B.lang).sum Language.order) spec.B A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ₀) _) ρ₁ σ₁
  letI inst₂ := @SOBlock.structure₂ (L.sum Language.order) (SOBlock.cons B spec.B) A
    (@sumOrderStructure L A instL _) (consAssign ρ₀ ρ₁) (consAssign σ₀ σ₁)
  letI : (((L.sum Language.order).sum (SOTCSpec.exBlock B spec).B.lang).sum
      (SOTCSpec.exBlock B spec).B.lang).Structure A := inst₂
  haveI := consTwoLHom_isExpansionOn (L := L) (B := B) (M := spec.B) ρ₀ σ₀ ρ₁ σ₁
  refine Iff.trans (b := _ ∧ _) Formula.realize_inf (and_congr (realize_fixedS ρ₀ σ₀ ρ₁ σ₁) ?_)
  exact LHom.realize_onSentence (M := A) (consTwoLHom L B spec.B) spec.step

theorem exBlock_step_split (c d : (SOBlock.cons B spec.B).Assignment A)
    (h : (spec.exBlock B).Step c d) :
    (fun i => c (Sum.inl i)) = (fun i => d (Sum.inl i)) ∧
      @SOTCSpec.Step (L.sum B.lang) spec A (B.structure₁ fun i => c (Sum.inl i)) _
        (fun j => c (Sum.inr j)) (fun j => d (Sum.inr j)) := by
  refine (exBlock_step_iff _ _ _ _).mp ?_
  rw [consAssign_split c, consAssign_split d]
  exact h

/-- The guessed block is the same all along a walk, and the rest of the state
walks in the inner specification. -/
theorem exBlock_reach (ρ σ : (SOBlock.cons B spec.B).Assignment A)
    (h : (spec.exBlock B).Reach ρ σ) :
    (fun i => ρ (Sum.inl i)) = (fun i => σ (Sum.inl i)) ∧
      @SOTCSpec.Reach (L.sum B.lang) spec A (B.structure₁ fun i => ρ (Sum.inl i)) _
        (fun j => ρ (Sum.inr j)) (fun j => σ (Sum.inr j)) := by
  induction h with
  | refl => exact ⟨rfl, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨hfst, hreach⟩ := ih
    obtain ⟨hcd₀, hcd₁⟩ := exBlock_step_split c d hcd
    rw [← hfst] at hcd₁
    exact ⟨hfst.trans hcd₀, hreach.tail hcd₁⟩

theorem exBlock_reach_of (ρ₀ : B.Assignment A) {ρ₁ σ₁ : spec.B.Assignment A}
    (h : @SOTCSpec.Reach (L.sum B.lang) spec A (B.structure₁ ρ₀) _ ρ₁ σ₁) :
    (spec.exBlock B).Reach (consAssign ρ₀ ρ₁) (consAssign ρ₀ σ₁) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail ((exBlock_step_iff ρ₀ ρ₀ c d).mpr ⟨rfl, hcd⟩)

/-- **What the guessing walk accepts**: exactly what the inner walk accepts,
under some assignment of the guessed block. -/
theorem exBlock_accepts_iff :
    (spec.exBlock B).Accepts A ↔
      ∃ ρ₀ : B.Assignment A, @SOTCSpec.Accepts (L.sum B.lang) spec A (B.structure₁ ρ₀) _ := by
  constructor
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    obtain ⟨hfst, hinner⟩ := exBlock_reach ρ σ hreach
    refine ⟨fun i => ρ (Sum.inl i), fun j => ρ (Sum.inr j), fun j => σ (Sum.inr j), ?_, ?_,
      hinner⟩
    · refine (exBlock_isSrc_iff _ _).mp ?_
      rw [consAssign_split ρ]
      exact hsrc
    · have htgt' : (spec.exBlock B).IsTgt
          (consAssign (fun i => σ (Sum.inl i)) fun j => σ (Sum.inr j)) := by
        rw [consAssign_split σ]
        exact htgt
      have := (exBlock_isTgt_iff _ _).mp htgt'
      rwa [← hfst] at this
  · rintro ⟨ρ₀, ρ₁, σ₁, hsrc, htgt, hreach⟩
    exact ⟨consAssign ρ₀ ρ₁, consAssign ρ₀ σ₁, (exBlock_isSrc_iff ρ₀ ρ₁).mpr hsrc,
      (exBlock_isTgt_iff ρ₀ σ₁).mpr htgt, exBlock_reach_of ρ₀ hreach⟩

end ExBlock

/-- **SO(TC) is closed under prefixing an existential second-order block**: the
walk carries the guessed block in its own state and never touches it again. -/
theorem SOTCDefinable.exBlock {L : Language.{0, 0}} {B : SOBlock}
    {Q : DecisionProblem (L.sum B.lang)} (hQ : SOTCDefinable Q) {P : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ ρ : B.Assignment A, @DecisionProblem.Holds _ Q A (B.structure₁ ρ)) :
    SOTCDefinable P := by
  obtain ⟨spec, hspec⟩ := hQ
  refine ⟨spec.exBlock B, fun A _ _ _ _ => ?_⟩
  rw [h A, exBlock_accepts_iff]
  exact exists_congr fun ρ => @hspec A (B.structure₁ ρ) _ _ _

/-! ### Down the quantifier prefix -/

section Prefix

/-- The decision problem defined by a second-order sentence with a given
quantifier prefix: isomorphism-invariant by
`DescriptiveComplexity.sorealize_iso`. -/
def soProblem (L : Language.{0, 0}) (Bs : List SOBlock) (φ : (soLang L Bs).Sentence)
    (pol : Bool) : DecisionProblem L where
  Holds := fun A inst => @SORealize L A inst Bs φ pol
  iso_invariant := fun e => sorealize_iso e Bs φ pol

/-- The base case: a first-order sentence is an SO(TC) condition – a walk with a
trivial block and no step. -/
theorem sotcDefinable_soProblem_nil (L : Language.{0, 0}) (φ : (soLang L []).Sentence)
    (pol : Bool) : SOTCDefinable (soProblem L [] φ pol) := by
  refine SOTCDefinable.of_sigmaSODefinable ⟨[SOBlock.trivial], rfl,
    (LHom.sumInl : L →ᴸ L.sum SOBlock.trivial.lang).onSentence φ, fun A _ _ _ => ?_⟩
  refine Iff.trans (b := @Sentence.Realize L A _ φ) Iff.rfl ?_
  constructor
  · intro h
    refine ⟨nilAssign A, ?_⟩
    letI := SOBlock.trivial.structure (nilAssign A)
    exact ((LHom.sumInl : L →ᴸ L.sum SOBlock.trivial.lang).realize_onSentence A φ).mpr h
  · rintro ⟨ρ, hρ⟩
    letI := SOBlock.trivial.structure ρ
    exact ((LHom.sumInl : L →ᴸ L.sum SOBlock.trivial.lang).realize_onSentence A φ).mp hρ

/-- **Every second-order sentence defines an SO(TC) condition**: peel the prefix
one block at a time, guessing an existential block into the state of the walk
and complementing at a universal one. -/
theorem sotcDefinable_soProblem :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (φ : (soLang L Bs).Sentence) (pol : Bool),
      SOTCDefinable (soProblem L Bs φ pol) := by
  intro Bs
  induction Bs with
  | nil => exact sotcDefinable_soProblem_nil
  | cons B Bs ih =>
    intro L φ pol
    cases pol
    · have hR : SOTCDefinable ((soProblem L (B :: Bs) φ false)ᶜ) := by
        refine SOTCDefinable.exBlock (B := B) (ih (L.sum B.lang) φ true).compl ?_
        intro A _ _ _
        classical
        exact not_forall
      have h := hR.compl
      rwa [DecisionProblem.compl_compl] at h
    · exact SOTCDefinable.exBlock (B := B) (ih (L.sum B.lang) φ false)
        fun A _ _ _ => Iff.rfl

end Prefix

/-! ### `PH ⊆ PSPACE` -/

variable {L : Language.{0, 0}}

/-- **Every `Σₖ`-definable problem is SO(TC) definable.** -/
theorem SOTCDefinable.of_sigmaSODefinable_any {k : ℕ} {P : DecisionProblem L}
    (h : SigmaSODefinable k P) : SOTCDefinable P := by
  obtain ⟨Bs, -, φ, hφ⟩ := h
  obtain ⟨spec, hspec⟩ := sotcDefinable_soProblem Bs L φ true
  exact ⟨spec, fun A _ _ _ _ => (hφ A).trans (hspec A)⟩

/-- **Every level of the polynomial hierarchy is inside PSPACE.** -/
theorem sigmaP_subset_PSPACE (k : ℕ) : SigmaP k ⊆ PSPACE := by
  cases k with
  | zero => exact fun _ _ h => NP_subset_PSPACE (PTIME_subset_NP h)
  | succ k => exact fun _ _ h => SOTCDefinable.of_sigmaSODefinable_any h

/-- **`PH ⊆ PSPACE`**: the polynomial hierarchy is inside polynomial space. -/
theorem PH_subset_PSPACE : PH ⊆ PSPACE :=
  fun _ _ h => h.elim fun k hk => sigmaP_subset_PSPACE k hk

/-- **`Πₖᵖ ⊆ PSPACE`** as well, since PSPACE is closed under complement. -/
theorem piP_subset_PSPACE (k : ℕ) : PiP k ⊆ PSPACE := by
  intro L P h
  rw [mem_piP_iff] at h
  exact (mem_PSPACE_compl_iff P).mp (sigmaP_subset_PSPACE k h)

end DescriptiveComplexity
