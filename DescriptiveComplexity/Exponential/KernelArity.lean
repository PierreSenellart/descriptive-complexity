/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Kernel
import DescriptiveComplexity.SecondOrderParam

/-!
# Giving every guessed variable an argument

A machine that stores a guessed relation on its tape addresses an entry by the
*encoding of its arguments*, so a relation variable of arity zero has the empty
address for its only entry – the cell the head starts on, below everything the
machine writes. Every construction that reads a stage on a tape therefore asks
that the guessed variables have an argument, and a kernel taken from an
arbitrary `Σ₁` definition need not.

The remedy is to give every variable one more argument and to say nothing about
it: `R(x̄)` becomes `R(z, x̄)` for a variable `z` quantified in front of the whole
kernel. An assignment of the extended block read at one value of the extra
argument is an assignment of the original (`SOBlock.atParam`), and the extension
that ignores the argument reads back as itself, so the two kernels hold at
exactly the same structures – as long as the universe is nonempty, which a
finite structure of a decision problem is.

This file is that transformation on formulas (`arityLift`), its correctness
(`realize_arityLift`), and the kernel it makes (`NexKernel.withArg`,
`NexKernel.withArg_holds`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The formula transformation -/

section Lift

variable {Lb : Language.{0, 0}} [Lb.IsRelational] (B : SOBlock) {α : Type} (p : α)

/-- A term of a relational vocabulary is a variable, so there is nothing to
do. -/
def argTerm {β : Type} :
    (Lb.sum B.lang).Term β → (Lb.sum B.withParam.lang).Term β
  | .var x => .var x
  | .func f _ => isEmptyElim f

/-- **The extra argument, put in front of every guessed atom**: a relation
variable of the block takes the parameter as a further argument, and everything
else – the base vocabulary, the equalities, the quantifiers – is left alone. -/
def arityLift :
    ∀ {n : ℕ}, (Lb.sum B.lang).BoundedFormula α n →
      (Lb.sum B.withParam.lang).BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (argTerm B t₁) (argTerm B t₂)
  | _, .rel r ts =>
    match r with
    | Sum.inl s => .rel (Sum.inl s) fun i => argTerm B (ts i)
    | Sum.inr b =>
        .rel (Sum.inr (B.paramSym b))
          (Fin.cons (Term.var (Sum.inl p)) fun i => argTerm B (ts i))
  | _, .imp φ ψ => .imp (arityLift φ) (arityLift ψ)
  | _, .all φ => .all (arityLift φ)

variable {B p} {N : Type} [instN : Lb.Structure N]

theorem realize_argTerm {β : Type} (ρ : B.withParam.Assignment N) (c : N)
    (v : β → N) (t : (Lb.sum B.lang).Term β) :
    letI := @sumStructure Lb B.withParam.lang N instN (B.withParam.structure ρ)
    letI := @sumStructure Lb B.lang N instN (B.structure (B.atParam ρ c))
    (argTerm B t).realize v = t.realize v := by
  match t with
  | .var _ => rfl
  | .func f _ => exact isEmptyElim f

/-- **The transformation is correct**: read at an assignment of the extended
block, the lifted formula says what the original said of that assignment read at
the value the parameter holds. -/
theorem realize_arityLift (ρ : B.withParam.Assignment N) (v : α → N) :
    ∀ {n : ℕ} (φ : (Lb.sum B.lang).BoundedFormula α n) (xs : Fin n → N),
      letI := @sumStructure Lb B.withParam.lang N instN (B.withParam.structure ρ)
      letI := @sumStructure Lb B.lang N instN (B.structure (B.atParam ρ (v p)))
      ((arityLift B p φ).Realize v xs ↔ φ.Realize v xs) := by
  letI := @sumStructure Lb B.withParam.lang N instN (B.withParam.structure ρ)
  letI := @sumStructure Lb B.lang N instN (B.structure (B.atParam ρ (v p)))
  intro n φ
  induction φ with
  | falsum => exact fun _ => Iff.rfl
  | equal t₁ t₂ =>
    intro xs
    change ((argTerm B t₁).realize _ = (argTerm B t₂).realize _) ↔ _
    rw [realize_argTerm ρ (v p) _ t₁, realize_argTerm ρ (v p) _ t₂]
    exact Iff.rfl
  | @rel _ l r ts =>
    intro xs
    have hts : ∀ i, (argTerm B (ts i)).realize (Sum.elim v xs) =
        (ts i).realize (Sum.elim v xs) := fun i => realize_argTerm ρ (v p) _ (ts i)
    match l, r with
    | _, Sum.inl s =>
      change (@RelMap (Lb.sum B.withParam.lang) N _ _
        (Sum.inl s) fun i => (argTerm B (ts i)).realize (Sum.elim v xs)) ↔ _
      rw [funext hts]
      exact Iff.rfl
    | _, Sum.inr b =>
      set w : Fin _ → N := fun j =>
        ((Fin.cons (Term.var (Sum.inl p)) fun i => argTerm B (ts i) : Fin _ →
          (Lb.sum B.withParam.lang).Term _) j).realize (Sum.elim v xs) with hwdef
      have hw0 : w 0 = v p := by
        rw [hwdef]
        simp only [Fin.cons_zero, Term.realize_var, Sum.elim_inl]
      have hwsucc : ∀ i, w i.succ = (ts i).realize (Sum.elim v xs) := by
        intro i
        rw [hwdef]
        simp only [Fin.cons_succ]
        exact hts i
      change (@RelMap (Lb.sum B.withParam.lang) N _ _
          (Sum.inr (B.paramSym b)) w) ↔
        (@RelMap (Lb.sum B.lang) N _ _ (Sum.inr b)
          fun i => (ts i).realize (Sum.elim v xs))
      rw [← funext hwsucc]
      exact SOBlock.relMap_paramSym B ρ (v p) b w hw0
  | imp φ ψ ihφ ihψ =>
    intro xs
    exact Iff.trans BoundedFormula.realize_imp
      (Iff.trans (imp_congr (ihφ xs) (ihψ xs)) BoundedFormula.realize_imp.symm)
  | all φ ih =>
    intro xs
    refine Iff.trans BoundedFormula.realize_all (Iff.trans ?_ BoundedFormula.realize_all.symm)
    exact forall_congr' fun x => ih (Fin.snoc xs x)

end Lift

/-! ### The kernel with an argument -/

section Kernel

variable {L : Language.{0, 0}}

/-- **A kernel whose guessed variables all have an argument**: every variable
takes one more, and the kernel says of it only that *some* value of it works. -/
noncomputable def NexKernel.withArg (K : NexKernel L) : NexKernel L where
  X := K.X
  B := K.B.withParam
  ker := Formula.iExs (Fin 1)
    (arityLift K.B (Sum.inr 0) (K.ker.relabel Sum.inl))

@[simp]
theorem NexKernel.withArg_X (K : NexKernel L) : K.withArg.X = K.X := rfl

@[simp]
theorem NexKernel.withArg_B (K : NexKernel L) : K.withArg.B = K.B.withParam := rfl

/-- **Every variable of the padded kernel's block has an argument.** -/
theorem NexKernel.withArg_arity_pos (K : NexKernel L) (i : K.withArg.B.ι) :
    0 < K.withArg.B.arity i := Nat.succ_pos _

/-- **An assignment that ignores the extra argument**: what the padded kernel is
satisfied by when the kernel is. -/
def SOBlock.ofParam (B : SOBlock) {M : Type} (ρ : B.Assignment M) :
    B.withParam.Assignment M :=
  fun i x => ρ i fun j => x j.succ

@[simp]
theorem SOBlock.atParam_ofParam (B : SOBlock) {M : Type} (ρ : B.Assignment M)
    (c : M) : B.atParam (B.ofParam ρ) c = ρ := rfl

/-- **Padding the arities changes no meaning**: an assignment of the padded
block read at the value the quantifier picks is an assignment of the original,
and an assignment of the original ignoring the extra argument satisfies the
padded kernel. The universe has to be nonempty for the quantifier to have
something to pick, which a finite structure of a decision problem is. -/
theorem NexKernel.withArg_holds (K : NexKernel L) {M : Type}
    [instM : K.X.E.Structure M] [instO : LinearOrder M] [Nonempty M] :
    @NexKernel.Holds L K.withArg M instM instO ↔ K.Holds M := by
  change (∃ ρ : K.B.withParam.Assignment M, @Sentence.Realize _ M
      (@sumStructure (K.X.E.sum Language.order) K.B.withParam.lang M
        (sumOrderStructure K.X.E M) (K.B.withParam.structure ρ))
      (Formula.iExs (Fin 1)
        (arityLift K.B (Sum.inr 0) (K.ker.relabel Sum.inl)))) ↔ _
  constructor
  · rintro ⟨ρ, hρ⟩
    letI := @sumStructure (K.X.E.sum Language.order) K.B.withParam.lang M
      (sumOrderStructure K.X.E M) (K.B.withParam.structure ρ)
    obtain ⟨w, hw⟩ := Formula.realize_iExs.mp hρ
    refine ⟨K.B.atParam ρ (w 0), ?_⟩
    letI := @sumStructure (K.X.E.sum Language.order) K.B.lang M
      (sumOrderStructure K.X.E M) (K.B.structure (K.B.atParam ρ (w 0)))
    have h := (realize_arityLift (B := K.B) (p := (Sum.inr 0 : Empty ⊕ Fin 1))
      (Lb := K.X.E.sum Language.order) ρ (Sum.elim default w)
      (K.ker.relabel Sum.inl) (default : Fin 0 → M)).mp hw
    have h2 := Formula.realize_relabel.mp h
    exact h2
  · rintro ⟨ρ, hρ⟩
    letI := @sumStructure (K.X.E.sum Language.order) K.B.withParam.lang M
      (sumOrderStructure K.X.E M) (K.B.withParam.structure (K.B.ofParam ρ))
    letI := @sumStructure (K.X.E.sum Language.order) K.B.lang M
      (sumOrderStructure K.X.E M) (K.B.structure ρ)
    refine ⟨K.B.ofParam ρ, ?_⟩
    refine Formula.realize_iExs.mpr ⟨fun _ => Classical.arbitrary M, ?_⟩
    refine (realize_arityLift (B := K.B) (p := (Sum.inr 0 : Empty ⊕ Fin 1))
      (Lb := K.X.E.sum Language.order) (K.B.ofParam ρ)
      (Sum.elim default fun _ => Classical.arbitrary M)
      (K.ker.relabel Sum.inl) (default : Fin 0 → M)).mpr ?_
    have h2 := Formula.realize_relabel (g := (Sum.inl : Empty → Empty ⊕ Fin 1))
      (φ := K.ker) (v := Sum.elim default fun _ => Classical.arbitrary M)
    exact h2.mpr hρ

end Kernel

end DescriptiveComplexity
