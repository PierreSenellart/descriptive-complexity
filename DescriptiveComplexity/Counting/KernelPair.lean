/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.SharpP
import DescriptiveComplexity.SecondOrderMerge

/-!
# The sum of two witness counts, as one witness count

Two kernels over two blocks are combined into one kernel over one block with
a **selector**, a relation variable of arity zero (`DescriptiveComplexity.boolBlock`):
when the selector holds, the first kernel must hold of the first block and the
second block must be empty; otherwise the second kernel must hold of the
second block and the first block must be empty
(`DescriptiveComplexity.pairKernel`). The witnesses of the pair kernel are,
bijectively, the witnesses of one kernel or the other
(`DescriptiveComplexity.pairWitnessEquiv`), so

* its witness count is the sum of the two (`DescriptiveComplexity.witnessCount_pairKernel`),
* and the selector reads the two summands back
  (`DescriptiveComplexity.card_pairWitness_sel`,
  `DescriptiveComplexity.card_pairWitness_not_sel`).

The first is what adding a constant to a witness count takes – the second
kernel being `⊤` over the block without variables, with exactly one witness
(`DescriptiveComplexity.witnessCount_trivial_top`) – and so what the closure
under complement of `⊕P` and `PP` rests on. The second is what the
completeness of a problem comparing two counts rests on: a single formula,
whose models are told apart by the value of the selector's variable.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The selector block and the lifting of kernels -/

/-- The block with one relation variable of arity zero: a Boolean. -/
@[reducible]
def boolBlock : SOBlock where
  ι := Unit
  arity := fun _ => 0

/-- The Boolean an assignment of the selector block holds. -/
def boolSel {A : Type} (ζ : boolBlock.Assignment A) : Prop :=
  ζ () finZeroElim

theorem boolSel_iff {A : Type} (ζ : boolBlock.Assignment A) (x : Fin 0 → A) :
    boolSel ζ ↔ ζ () x :=
  iff_of_eq (congrArg (ζ ()) (Subsingleton.elim _ _))

/-- Assignments of a merged block are pairs of assignments. -/
def SOBlock.consAssignEquiv (B M : SOBlock) (A : Type) :
    (SOBlock.cons B M).Assignment A ≃ B.Assignment A × M.Assignment A where
  toFun ρ := (fun i => ρ (Sum.inl i), fun j => ρ (Sum.inr j))
  invFun p := consAssign p.1 p.2
  left_inv ρ := consAssign_split ρ
  right_inv _ := rfl

variable {L : Language.{0, 0}}

/-- A sentence over the expansion by `B`, read over the expansion by the
merged block `SOBlock.cons B M`. -/
noncomputable def liftFst (B M : SOBlock) (φ : (L.sum B.lang).Sentence) :
    (L.sum (SOBlock.cons B M).lang).Sentence :=
  (mergeStep L B M).onSentence (LHom.sumInl.onSentence φ)

/-- A sentence over the expansion by `M`, read over the expansion by the
merged block `SOBlock.cons B M`. -/
noncomputable def liftSnd (B M : SOBlock) (φ : (L.sum M.lang).Sentence) :
    (L.sum (SOBlock.cons B M).lang).Sentence :=
  (mergeStep L B M).onSentence ((LHom.sumMap LHom.sumInl (LHom.id M.lang)).onSentence φ)

/-- “Every relation variable of the block is empty.” -/
noncomputable def emptyBlockS (B : SOBlock) : (L.sum B.lang).Sentence :=
  Formula.iInf fun i : B.ι => Formula.iAlls (Fin (B.arity i))
    (∼(Relations.formula (Sum.inr ⟨i, rfl⟩ : (L.sum B.lang).Relations (B.arity i))
      fun j => Term.var (Sum.inr j)))

/-- “The selector holds.” -/
noncomputable def selectorS (B : SOBlock) :
    (L.sum (SOBlock.cons B boolBlock).lang).Sentence :=
  Relations.formula (Sum.inr ⟨Sum.inr (), rfl⟩ :
    (L.sum (SOBlock.cons B boolBlock).lang).Relations 0) finZeroElim

section Realize

variable {A : Type} [L.Structure A]

theorem realize_liftFst (B M : SOBlock) (φ : (L.sum B.lang).Sentence) (ρ : B.Assignment A)
    (μ : M.Assignment A) :
    (@Sentence.Realize _ A (@sumStructure L _ A _ ((SOBlock.cons B M).structure (consAssign ρ μ)))
      (liftFst B M φ)) ↔
      @Sentence.Realize _ A (@sumStructure L _ A _ (B.structure ρ)) φ := by
  let := B.structure ρ
  let := M.structure μ
  let := (SOBlock.cons B M).structure (consAssign ρ μ)
  have := mergeStep_isExpansionOn L (A := A) inferInstance B M ρ μ
  rw [liftFst, LHom.realize_onSentence, LHom.realize_onSentence]

theorem realize_liftSnd (B M : SOBlock) (φ : (L.sum M.lang).Sentence) (ρ : B.Assignment A)
    (μ : M.Assignment A) :
    (@Sentence.Realize _ A (@sumStructure L _ A _ ((SOBlock.cons B M).structure (consAssign ρ μ)))
      (liftSnd B M φ)) ↔
      @Sentence.Realize _ A (@sumStructure L _ A _ (M.structure μ)) φ := by
  let := B.structure ρ
  let := M.structure μ
  let := (SOBlock.cons B M).structure (consAssign ρ μ)
  have := mergeStep_isExpansionOn L (A := A) inferInstance B M ρ μ
  have : (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum B.lang) (LHom.id M.lang)).IsExpansionOn A :=
    ⟨fun f _ => by rcases f with f | f <;> rfl, fun r _ => by rcases r with r | r <;> rfl⟩
  rw [liftSnd, LHom.realize_onSentence, LHom.realize_onSentence]

theorem realize_emptyBlockS (B : SOBlock) (ρ : B.Assignment A) :
    (@Sentence.Realize _ A (@sumStructure L _ A _ (B.structure ρ)) (emptyBlockS B)) ↔
      ∀ (i : B.ι) (x : Fin (B.arity i) → A), ¬ρ i x := by
  let := B.structure ρ
  rw [emptyBlockS, Sentence.Realize]
  simp only [Formula.realize_iInf, Formula.realize_iAlls, Formula.realize_not]
  refine forall_congr' fun i => forall_congr' fun x => not_congr (iff_of_eq ?_)
  change ρ i (fun j => x (Fin.cast rfl j)) = ρ i x
  rfl

theorem realize_selectorS (B : SOBlock) (ρ : B.Assignment A) (ζ : boolBlock.Assignment A) :
    (@Sentence.Realize _ A (@sumStructure L _ A _
      ((SOBlock.cons B boolBlock).structure (consAssign ρ ζ))) (selectorS B)) ↔ boolSel ζ := by
  let := (SOBlock.cons B boolBlock).structure (consAssign ρ ζ)
  change ζ () _ ↔ boolSel ζ
  exact (boolSel_iff ζ _).symm

end Realize

/-! ### The pair kernel -/

variable (B B' : SOBlock) (φ : (L.sum B.lang).Sentence) (φ' : (L.sum B'.lang).Sentence)

/-- The block of a pair of kernels: the two blocks and the selector. -/
abbrev pairBlock : SOBlock :=
  SOBlock.cons B (SOBlock.cons B' boolBlock)

/-- **The pair kernel**: the first kernel of the first block when the selector
holds, the second block being empty; the second kernel of the second block
otherwise, the first block being empty. -/
noncomputable def pairKernel : (L.sum (pairBlock B B').lang).Sentence :=
  ((liftSnd B _ (selectorS B') ⊓ liftFst B _ φ) ⊓
      liftSnd B _ (liftFst B' boolBlock (emptyBlockS B'))) ⊔
    ((∼(liftSnd B _ (selectorS B')) ⊓ liftSnd B _ (liftFst B' boolBlock φ')) ⊓
      liftFst B _ (emptyBlockS B))

section Witnesses

variable {A : Type} [L.Structure A]

/-- The witnesses of a kernel. -/
abbrev Witness (M : SOBlock) (ψ : (L.sum M.lang).Sentence) (A : Type) [L.Structure A] : Type :=
  {ρ : M.Assignment A // @Sentence.Realize _ A (@sumStructure L _ A _ (M.structure ρ)) ψ}

/-- The empty assignment of a block. -/
def SOBlock.emptyAssign (M : SOBlock) (A : Type) : M.Assignment A := fun _ _ => False

variable {B B' φ φ'}

theorem realize_pairKernel (ρ : B.Assignment A) (ρ' : B'.Assignment A)
    (ζ : boolBlock.Assignment A) :
    (@Sentence.Realize _ A (@sumStructure L _ A _
        ((pairBlock B B').structure (consAssign ρ (consAssign ρ' ζ)))) (pairKernel B B' φ φ')) ↔
      (boolSel ζ ∧ (@Sentence.Realize _ A (@sumStructure L _ A _ (B.structure ρ)) φ) ∧
          ρ' = SOBlock.emptyAssign B' A) ∨
        (¬boolSel ζ ∧ (@Sentence.Realize _ A (@sumStructure L _ A _ (B'.structure ρ')) φ') ∧
          ρ = SOBlock.emptyAssign B A) := by
  let := (pairBlock B B').structure (consAssign ρ (consAssign ρ' ζ))
  have hempty : ∀ (M : SOBlock) (μ : M.Assignment A),
      (∀ (i : M.ι) (x : Fin (M.arity i) → A), ¬μ i x) ↔ μ = SOBlock.emptyAssign M A :=
    fun M μ => ⟨fun h => funext fun i => funext fun x => propext ⟨h i x, False.elim⟩,
      fun h i x => by rw [h]; exact id⟩
  rw [pairKernel, Sentence.Realize, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_inf, Formula.realize_inf, Formula.realize_inf, Formula.realize_not]
  change ((Sentence.Realize _ _ ∧ Sentence.Realize _ _) ∧ Sentence.Realize _ _) ∨
    ((¬Sentence.Realize _ _ ∧ Sentence.Realize _ _) ∧ Sentence.Realize _ _) ↔ _
  simp only [realize_liftSnd, realize_liftFst, realize_selectorS, realize_emptyBlockS, hempty,
    and_assoc]

/-- The first component of an assignment of the pair block. -/
abbrev pairFst (ρ : (pairBlock B B').Assignment A) : B.Assignment A := fun i => ρ (Sum.inl i)

/-- The second component of an assignment of the pair block. -/
abbrev pairSnd (ρ : (pairBlock B B').Assignment A) : B'.Assignment A :=
  fun i => ρ (Sum.inr (Sum.inl i))

/-- The selector of an assignment of the pair block. -/
abbrev pairSel (ρ : (pairBlock B B').Assignment A) : Prop :=
  boolSel fun i => ρ (Sum.inr (Sum.inr i))

theorem pairAssign_eq (ρ : (pairBlock B B').Assignment A) :
    ρ = consAssign (pairFst ρ) (consAssign (pairSnd ρ) fun i => ρ (Sum.inr (Sum.inr i))) := by
  funext i
  rcases i with i | i | i <;> rfl

theorem realize_pairKernel' (ρ : (pairBlock B B').Assignment A) :
    (@Sentence.Realize _ A (@sumStructure L _ A _ ((pairBlock B B').structure ρ))
      (pairKernel B B' φ φ')) ↔
      (pairSel ρ ∧ (@Sentence.Realize _ A (@sumStructure L _ A _ (B.structure (pairFst ρ))) φ) ∧
          pairSnd ρ = SOBlock.emptyAssign B' A) ∨
        (¬pairSel ρ ∧
          (@Sentence.Realize _ A (@sumStructure L _ A _ (B'.structure (pairSnd ρ))) φ') ∧
          pairFst ρ = SOBlock.emptyAssign B A) := by
  have h := realize_pairKernel (φ := φ) (φ' := φ') (pairFst ρ) (pairSnd ρ)
    fun i => ρ (Sum.inr (Sum.inr i))
  rwa [← pairAssign_eq ρ] at h

open Classical in
/-- **The witnesses of the pair kernel are those of one kernel or the
other**, told apart by the selector. -/
noncomputable def pairWitnessEquiv :
    Witness (pairBlock B B') (pairKernel B B' φ φ') A ≃ Witness B φ A ⊕ Witness B' φ' A where
  toFun w :=
    if h : pairSel w.1 then
      Sum.inl ⟨pairFst w.1, by
        rcases (realize_pairKernel' w.1).mp w.2 with ⟨-, h1, -⟩ | ⟨h0, -, -⟩
        · exact h1
        · exact absurd h h0⟩
    else
      Sum.inr ⟨pairSnd w.1, by
        rcases (realize_pairKernel' w.1).mp w.2 with ⟨h0, -, -⟩ | ⟨-, h1, -⟩
        · exact absurd h0 h
        · exact h1⟩
  invFun w :=
    match w with
    | Sum.inl ⟨ρ, hρ⟩ => ⟨consAssign ρ (consAssign (SOBlock.emptyAssign B' A)
        (fun _ _ => True : boolBlock.Assignment A)),
        (realize_pairKernel _ _ _).mpr (Or.inl ⟨trivial, hρ, rfl⟩)⟩
    | Sum.inr ⟨ρ', hρ'⟩ => ⟨consAssign (SOBlock.emptyAssign B A) (consAssign ρ'
        (fun _ _ => False : boolBlock.Assignment A)),
        (realize_pairKernel _ _ _).mpr (Or.inr ⟨id, hρ', rfl⟩)⟩
  left_inv w := by
    have hw := (realize_pairKernel' w.1).mp w.2
    by_cases h : pairSel w.1
    · simp only [dite_eq_left h]
      refine Subtype.ext ?_
      rcases hw with ⟨-, -, h2⟩ | ⟨h0, -, -⟩
      · refine Eq.trans ?_ (pairAssign_eq w.1).symm
        change consAssign (pairFst w.1) (consAssign (SOBlock.emptyAssign B' A)
          (fun _ _ => True : boolBlock.Assignment A)) = _
        refine congrArg (consAssign _) (congrArg₂ consAssign h2.symm
          (funext fun i => funext fun x => propext ?_))
        exact ⟨fun _ => (boolSel_iff _ x).mp h, fun _ => trivial⟩
      · exact absurd h h0
    · simp only [dite_eq_right h]
      refine Subtype.ext ?_
      rcases hw with ⟨h0, -, -⟩ | ⟨-, -, h2⟩
      · exact absurd h0 h
      · refine Eq.trans ?_ (pairAssign_eq w.1).symm
        change consAssign (SOBlock.emptyAssign B A) (consAssign (pairSnd w.1)
          (fun _ _ => False : boolBlock.Assignment A)) = _
        refine congrArg₂ consAssign h2.symm (congrArg (consAssign _)
          (funext fun i => funext fun x => propext ?_))
        exact ⟨False.elim, fun hx => h ((boolSel_iff _ x).mpr hx)⟩
  right_inv w := by
    rcases w with ⟨ρ, hρ⟩ | ⟨ρ', hρ'⟩
    · exact dite_eq_left trivial
    · exact dite_eq_right id

/-- **The witness count of the pair kernel is the sum of the two witness
counts.** -/
theorem witnessCount_pairKernel [Finite A] :
    witnessCount (pairBlock B B') (pairKernel B B' φ φ') A =
      witnessCount B φ A + witnessCount B' φ' A := by
  rw [witnessCount, witnessCount, witnessCount, ← Nat.card_sum]
  exact Nat.card_congr pairWitnessEquiv

theorem pairWitnessEquiv_isLeft (w : Witness (pairBlock B B') (pairKernel B B' φ φ') A) :
    (pairWitnessEquiv w).isLeft = true ↔ pairSel w.1 := by
  simp only [pairWitnessEquiv, Equiv.coe_fn_mk]
  by_cases h : pairSel w.1
  · rw [dite_eq_left h]
    exact iff_of_true rfl h
  · rw [dite_eq_right h]
    exact iff_of_false (by simp) h

/-- The left summands of a sum type. -/
def subtypeIsLeftEquiv {X Y : Type} : {s : X ⊕ Y // s.isLeft = true} ≃ X where
  toFun s := s.1.getLeft s.2
  invFun x := ⟨Sum.inl x, rfl⟩
  left_inv := fun ⟨s, hs⟩ => by
    cases s with
    | inl x => rfl
    | inr y => exact absurd hs (by simp)
  right_inv _ := rfl

/-- The right summands of a sum type. -/
def subtypeIsRightEquiv {X Y : Type} : {s : X ⊕ Y // s.isLeft = false} ≃ Y where
  toFun s := s.1.getRight (by simpa using s.2)
  invFun y := ⟨Sum.inr y, rfl⟩
  left_inv := fun ⟨s, hs⟩ => by
    cases s with
    | inl x => exact absurd hs (by simp)
    | inr y => rfl
  right_inv _ := rfl

/-- **The witnesses of the pair kernel with the selector are the witnesses of
the first kernel.** -/
theorem card_pairWitness_sel :
    Nat.card {w : Witness (pairBlock B B') (pairKernel B B' φ φ') A // pairSel w.1} =
      witnessCount B φ A :=
  Nat.card_congr ((Equiv.subtypeEquiv pairWitnessEquiv fun w =>
    (pairWitnessEquiv_isLeft w).symm).trans subtypeIsLeftEquiv)

/-- **The witnesses of the pair kernel without the selector are the witnesses
of the second kernel.** -/
theorem card_pairWitness_not_sel :
    Nat.card {w : Witness (pairBlock B B') (pairKernel B B' φ φ') A // ¬pairSel w.1} =
      witnessCount B' φ' A :=
  Nat.card_congr ((Equiv.subtypeEquiv pairWitnessEquiv fun w => by
    rw [← pairWitnessEquiv_isLeft w, Bool.not_eq_true]).trans subtypeIsRightEquiv)

/-- The kernel `⊤` over the block without variables has exactly one
witness. -/
theorem witnessCount_trivial_top : witnessCount (L := L) SOBlock.trivial ⊤ A = 1 := by
  rw [witnessCount, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun w w' => Subtype.ext (funext fun i => (i : Empty).elim)⟩,
    ⟨⟨fun i => (i : Empty).elim, id⟩⟩⟩

end Witnesses

end DescriptiveComplexity
