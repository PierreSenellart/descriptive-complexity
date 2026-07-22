/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qbf.Defs
import DescriptiveComplexity.SecondOrderMerge
import DescriptiveComplexity.Padding

/-!
# QBF is second-order definable

The membership half of the completeness of `DescriptiveComplexity.QBF`: a quantified
Boolean formula problem with `k` alternating blocks is `Σₖ`-definable when its
prefix starts existentially, and `Πₖ`-definable when it starts universally
(`DescriptiveComplexity.qbfProblem_sigmaSODefinable`,
`DescriptiveComplexity.qbfProblem_piSODefinable`).

The second-order prefix is `k` *monadic* blocks
(`DescriptiveComplexity.unaryBlock`: one unary relation variable each), one per
quantifier block of the formula, and the first-order kernel simply evaluates
the matrix: it says that every clause contains a true literal (or, for a
disjunctive matrix, that some term has all its literals true), reading the
truth value of a variable off the relation variable of a block marking it.
No Tseitin translation is involved here – the matrix is already part of the
input structure, so evaluating it is first-order.

The blocks are handled through `DescriptiveComplexity.SecondOrderMerge`: the kernel is
written over the *single* merged block, where the relation variable of block
`i` is the symbol `DescriptiveComplexity.blockSym k i`, and
`DescriptiveComplexity.sorealize_unmerge` transports it into the iterated block
expansion while turning the alternating second-order quantification into
`DescriptiveComplexity.altQuant`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The monadic blocks of a quantifier prefix -/

/-- The second-order block of a single propositional quantifier: one unary
relation variable, the truth assignment of one block of variables. -/
@[reducible]
def unaryBlock : SOBlock where
  ι := Unit
  arity := fun _ => 1

/-- The quantifier prefix of `QBF k`: `k` monadic blocks. -/
abbrev qbfBlocks (k : ℕ) : List SOBlock := List.replicate k unaryBlock

@[simp]
theorem qbfBlocks_length (k : ℕ) : (qbfBlocks k).length = k :=
  List.length_replicate ..

/-- The single block merging the whole prefix of `QBF k`. -/
abbrev qbfMergedBlock (k : ℕ) : SOBlock := mergeBlocks (qbfBlocks k)

/-- The relation symbol of the truth assignment of block `i`, in the merged
block's vocabulary. -/
def blockSym : ∀ (k : ℕ), Fin k → (qbfMergedBlock k).lang.Relations 1
  | 0, i => i.elim0
  | _ + 1, ⟨0, _⟩ => ⟨Sum.inl (), rfl⟩
  | k + 1, ⟨j + 1, hj⟩ =>
      ⟨Sum.inr (blockSym k ⟨j, Nat.lt_of_succ_lt_succ hj⟩).1,
        (blockSym k ⟨j, Nat.lt_of_succ_lt_succ hj⟩).2⟩

/-- The assignment of the merged block determined by `k` truth assignments. -/
def repAssign (A : Type) : ∀ (k : ℕ), (Fin k → A → Prop) → (qbfMergedBlock k).Assignment A
  | 0, _ => nilAssign A
  | k + 1, νs => consAssign (fun _ w => νs 0 (w 0)) (repAssign A k fun i => νs i.succ)

/-- Reading back the truth assignment of block `i` from the merged
assignment. -/
theorem repAssign_blockSym {A : Type} :
    ∀ (k : ℕ) (νs : Fin k → A → Prop) (i : Fin k) (x : A),
      @RelMap (qbfMergedBlock k).lang A ((qbfMergedBlock k).structure (repAssign A k νs)) 1
        (blockSym k i) ![x] ↔ νs i x := by
  intro k
  induction k with
  | zero => intro νs i; exact i.elim0
  | succ k ih =>
    intro νs i x
    obtain ⟨j, hj⟩ := i
    cases j with
    | zero => exact Iff.rfl
    | succ j => exact ih (fun i => νs i.succ) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ x

/-! ### The prefix quantifies the components of the merged assignment -/

private theorem unaryBlock_ext {A : Type} (ρ : unaryBlock.Assignment A) :
    (fun (_ : Unit) (w : Fin 1 → A) => ρ () fun _ => w 0) = ρ := by
  funext i w
  obtain rfl : i = () := Subsingleton.elim _ _
  exact congrArg (ρ ()) (funext fun j => congrArg w (Subsingleton.elim _ _))

/-- Alternating quantification over the components of the merged assignment of
a monadic prefix is alternating quantification over `k` truth assignments. -/
theorem altAssign_qbfBlocks {A : Type} :
    ∀ (k : ℕ) (P : (qbfMergedBlock k).Assignment A → Prop) (pol : Bool),
      altAssign A (qbfBlocks k) P pol ↔
        altQuant A k (fun νs => P (repAssign A k νs)) pol := by
  intro k
  induction k with
  | zero => intro P pol; exact Iff.rfl
  | succ k ih =>
    intro P pol
    have hrep : ∀ (ν : A → Prop) (νs : Fin k → A → Prop),
        repAssign A (k + 1) (Fin.cons ν νs) =
          consAssign (fun _ w => ν (w 0)) (repAssign A k νs) := by
      intro ν νs
      simp only [repAssign, Fin.cons_zero, Fin.cons_succ]
      rfl
    have key : ∀ ν : A → Prop,
        altAssign A (qbfBlocks k)
            (fun μ => P (consAssign (fun _ w => ν (w 0)) μ)) (!pol) ↔
          altQuant A k (fun νs => P (repAssign A (k + 1) (Fin.cons ν νs))) (!pol) := by
      intro ν
      refine (ih _ (!pol)).trans (altQuant_congr k _ _ (fun νs => ?_) (!pol))
      exact iff_of_eq (congrArg P (hrep ν νs).symm)
    cases pol with
    | true =>
      constructor
      · rintro ⟨ρ, hρ⟩
        refine ⟨fun a => ρ () fun _ => a, (key _).mp ?_⟩
        rw [unaryBlock_ext ρ]
        exact hρ
      · rintro ⟨ν, hν⟩
        exact ⟨fun _ w => ν (w 0), (key ν).mpr hν⟩
    | false =>
      constructor
      · intro h ν
        exact (key ν).mp (h fun _ w => ν (w 0))
      · intro h ρ
        have := (key fun a => ρ () fun _ => a).mpr (h _)
        rwa [unaryBlock_ext ρ] at this

/-! ### The first-order kernel -/

/-- The vocabulary of the kernel: quantified CNF instances together with the
`k` truth-assignment relation variables. -/
abbrev qbfSOLang (k : ℕ) : Language := (Language.qbf k).sum (qbfMergedBlock k).lang

/-- The symbol for “is a clause” in the kernel's vocabulary. -/
abbrev qIsClSym (k : ℕ) : (qbfSOLang k).Relations 1 := Sum.inl qbfIsClause

/-- The symbol for “occurs positively in” in the kernel's vocabulary. -/
abbrev qPosSym (k : ℕ) : (qbfSOLang k).Relations 2 := Sum.inl qbfPosIn

/-- The symbol for “occurs negatively in” in the kernel's vocabulary. -/
abbrev qNegSym (k : ℕ) : (qbfSOLang k).Relations 2 := Sum.inl qbfNegIn

/-- The block mark of block `i` in the kernel's vocabulary. -/
abbrev qBlkSym {k : ℕ} (i : Fin k) : (qbfSOLang k).Relations 1 := Sum.inl (qbfBlock i)

/-- The truth-assignment variable of block `i` in the kernel's vocabulary. -/
abbrev qNuSym {k : ℕ} (i : Fin k) : (qbfSOLang k).Relations 1 := Sum.inr (blockSym k i)

/-- The truth value of the variable `x`, as a formula: some block marking `x`
assigns it the value true. -/
noncomputable def qbfValF (k : ℕ) {γ : Type} (x : γ) : (qbfSOLang k).Formula γ :=
  listSup ((List.finRange k).map fun i =>
    Relations.formula₁ (qBlkSym i) (Term.var x) ⊓
      Relations.formula₁ (qNuSym i) (Term.var x))

section Realize

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] (νs : Fin k → A → Prop)

/-- The interpretation of the kernel's vocabulary determined by `k` truth
assignments. -/
@[instance_reducible]
def qbfSOStructure : (qbfSOLang k).Structure A :=
  letI := (qbfMergedBlock k).structure (repAssign A k νs)
  inferInstance

/-- The truth-assignment variables are read as the truth assignments. -/
theorem relMap_qNuSym (i : Fin k) (w : Fin 1 → A) :
    @RelMap (qbfSOLang k) A (qbfSOStructure νs) 1 (qNuSym i) w ↔ νs i (w 0) := by
  letI := (qbfMergedBlock k).structure (repAssign A k νs)
  have hw : w = ![w 0] := funext fun j => by rw [Subsingleton.elim j 0]; rfl
  calc @RelMap (qbfSOLang k) A (qbfSOStructure νs) 1 (qNuSym i) w
      ↔ @RelMap (qbfSOLang k) A (qbfSOStructure νs) 1 (qNuSym i) ![w 0] := by rw [← hw]
    _ ↔ νs i (w 0) := repAssign_blockSym k νs i (w 0)

theorem realize_qbfValF {γ : Type} (x : γ) (v : γ → A) :
    @Formula.Realize (qbfSOLang k) A (qbfSOStructure νs) γ (qbfValF k x) v ↔
      qbfVal νs (v x) := by
  letI := (qbfMergedBlock k).structure (repAssign A k νs)
  rw [qbfValF, realize_listSup, qbfVal]
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and,
    Formula.realize_inf, Formula.realize_rel₁, Term.realize_var]
  exact exists_congr fun i => and_congr Iff.rfl (relMap_qNuSym νs i _)

end Realize

/-- The kernel for a conjunctive matrix: every clause contains a true
literal. -/
noncomputable def qbfCnfKernel (k : ℕ) : (qbfSOLang k).Sentence :=
  ((Relations.formula₁ (qIsClSym k) (Term.var (Sum.inr 0))).imp
    (((Relations.formula₂ (qPosSym k) (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓ qbfValF k (Sum.inr ())) ⊔
      (Relations.formula₂ (qNegSym k) (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓ ∼(qbfValF k (Sum.inr ())))).iExs Unit)).iAlls (Fin 1)

/-- The kernel for a disjunctive matrix: some term has all its literals
true. -/
noncomputable def qbfDnfKernel (k : ℕ) : (qbfSOLang k).Sentence :=
  (Relations.formula₁ (qIsClSym k) (Term.var (Sum.inr 0)) ⊓
    (((Relations.formula₂ (qPosSym k) (Term.var (Sum.inl (Sum.inr 0)))
            (Term.var (Sum.inr ()))).imp (qbfValF k (Sum.inr ()))) ⊓
      ((Relations.formula₂ (qNegSym k) (Term.var (Sum.inl (Sum.inr 0)))
            (Term.var (Sum.inr ()))).imp (∼(qbfValF k (Sum.inr ()))))).iAlls Unit).iExs (Fin 1)

/-- The kernel of the `Σₖ`/`Πₖ` definition of a quantified Boolean formula
problem, for either shape of matrix. -/
noncomputable def qbfKernel (k : ℕ) (cnf : Bool) : (qbfSOLang k).Sentence :=
  match cnf with
  | true => qbfCnfKernel k
  | false => qbfDnfKernel k

/-- **The kernel defines the matrix**: under the interpretation of the
relation variables by `k` truth assignments, the kernel says exactly that the
matrix is satisfied. -/
theorem realize_qbfKernel (k : ℕ) (cnf : Bool) {A : Type} [(Language.qbf k).Structure A]
    (νs : Fin k → A → Prop) :
    @Sentence.Realize (qbfSOLang k) A (qbfSOStructure νs) (qbfKernel k cnf) ↔
      QbfMatrix cnf νs := by
  letI := (qbfMergedBlock k).structure (repAssign A k νs)
  cases cnf
  · rw [qbfKernel, qbfDnfKernel, QbfMatrix, DnfSat]
    simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_iAlls,
      Formula.realize_inf, Formula.realize_imp, Formula.realize_not,
      Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr,
      Sum.elim_inl, Language.relMap_sumInl, realize_qbfValF]
    constructor
    · rintro ⟨c, hc, h⟩
      refine ⟨c 0, hc, fun x => ?_⟩
      exact ⟨(h fun _ => x).1, (h fun _ => x).2⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨fun _ => c, hc, fun x => ⟨(h (x ())).1, (h (x ())).2⟩⟩
  · rw [qbfKernel, qbfCnfKernel, QbfMatrix]
    change _ ↔ CnfSatWith false νs
    rw [CnfSatWith]
    simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
      Formula.realize_imp, Formula.realize_sup, Formula.realize_inf,
      Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
      Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl,
      realize_qbfValF]
    constructor
    · intro h c hc
      obtain ⟨x, hx⟩ := h (fun _ => c) hc
      exact ⟨x (), hx⟩
    · intro h i hc
      obtain ⟨x, hx⟩ := h (i 0) hc
      exact ⟨fun _ => x, hx⟩

/-! ### Membership -/

section Definability

variable (k : ℕ) (cnf : Bool)

private theorem qbf_definable_aux (pol : Bool) (A : Type) (instA : (Language.qbf k).Structure A) :
    @DecisionProblem.Holds _ (QbfProblem k pol cnf) A instA ↔
      @SORealize (Language.qbf k) A instA (qbfBlocks k)
        ((unmergeHom (qbfBlocks k) (Language.qbf k)).onSentence (qbfKernel k cnf)) pol := by
  have h1 := sorealize_unmerge (qbfBlocks k) (Language.qbf k) A instA (qbfKernel k cnf) pol
  have h2 := altAssign_qbfBlocks (A := A) k
    (fun μ => @Sentence.Realize (qbfSOLang k) A
      (@sumStructure (Language.qbf k) (qbfMergedBlock k).lang A instA
        ((qbfMergedBlock k).structure μ)) (qbfKernel k cnf)) pol
  have h3 : altQuant A k (fun νs => @QbfMatrix k A instA cnf νs) pol ↔
      altQuant A k (fun νs => @Sentence.Realize (qbfSOLang k) A
        (@sumStructure (Language.qbf k) (qbfMergedBlock k).lang A instA
          ((qbfMergedBlock k).structure (repAssign A k νs))) (qbfKernel k cnf)) pol :=
    altQuant_congr k _ _ (fun νs => (realize_qbfKernel k cnf νs).symm) pol
  exact h3.trans (h2.symm.trans h1.symm)

/-- **QBF with an existential outermost block is `Σₖ`-definable**: quantify the
`k` truth assignments as monadic second-order variables, and evaluate the
matrix in first-order logic. -/
theorem qbfProblem_sigmaSODefinable : SigmaSODefinable k (QbfProblem k true cnf) :=
  ⟨qbfBlocks k, qbfBlocks_length k,
    (unmergeHom (qbfBlocks k) (Language.qbf k)).onSentence (qbfKernel k cnf),
    fun A instA _ _ => qbf_definable_aux k cnf true A instA⟩

/-- **QBF with a universal outermost block is `Πₖ`-definable.** -/
theorem qbfProblem_piSODefinable : PiSODefinable k (QbfProblem k false cnf) :=
  ⟨qbfBlocks k, qbfBlocks_length k,
    (unmergeHom (qbfBlocks k) (Language.qbf k)).onSentence (qbfKernel k cnf),
    fun A instA _ _ => qbf_definable_aux k cnf false A instA⟩

end Definability

end DescriptiveComplexity
