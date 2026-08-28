/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Machine.AltMatrix
import DescriptiveComplexity.Problems.Machine.AltDefs

/-!
# The `Σₖ` kernel of alternating acceptance

The first-order kernel the `k` second-order blocks of the membership proof sit
under. It is the kernel of
`DescriptiveComplexity.Problems.Machine.Membership` – the same seventeen
clauses, transcribing the same relations – with three differences:

* the vocabulary is `DescriptiveComplexity.akLang`, the alternating machine's
  together with the *merged* block of `k` copies of the guessing block, so a
  clause names the round whose run it speaks of
  (`DescriptiveComplexity.akSt` and friends, read back by
  `DescriptiveComplexity.relMap_akSt`);
* the block marks are read as finite disjunctions over `Fin k`, which is what
  makes “the state at this time is in a block below `i`” first-order;
* the clauses are assembled not into a conjunction but into the alternating
  chain `DescriptiveComplexity.akLadderF`, matching the matrix of
  `DescriptiveComplexity.Problems.Machine.AltMatrix`.

Every builder here is parameterized by the round it reads, so the file writes
the clause layer once rather than `k` times.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The vocabulary of the kernel -/

section Symbols

variable (k : ℕ)

/-- The vocabulary of the kernel: the alternating machine's, expanded by the
merged block of one guessed run per round. -/
abbrev akLang : Language := (Language.turingAlt k).sum (repMerged tmGuessBlock k).lang

variable {k}

/-- The position symbol in the kernel's vocabulary. -/
abbrev akPosnSym : (akLang k).Relations 1 := Sum.inl atmPosn

/-- The transition symbol in the kernel's vocabulary. -/
abbrev akTrSym : (akLang k).Relations 1 := Sum.inl atmTr

/-- The start-state symbol in the kernel's vocabulary. -/
abbrev akStartSym : (akLang k).Relations 1 := Sum.inl atmStart

/-- The accepting-state symbol in the kernel's vocabulary. -/
abbrev akAccSym : (akLang k).Relations 1 := Sum.inl atmAcc

/-- The blank symbol in the kernel's vocabulary. -/
abbrev akBlankSym : (akLang k).Relations 1 := Sum.inl atmBlank

/-- The move-right symbol in the kernel's vocabulary. -/
abbrev akRightSym : (akLang k).Relations 1 := Sum.inl atmRight

/-- The order symbol in the kernel's vocabulary. -/
abbrev akLeSym : (akLang k).Relations 2 := Sum.inl atmLe

/-- The source symbol in the kernel's vocabulary. -/
abbrev akSrcSym : (akLang k).Relations 2 := Sum.inl atmSrc

/-- The read symbol in the kernel's vocabulary. -/
abbrev akReadSym : (akLang k).Relations 2 := Sum.inl atmRead

/-- The target symbol in the kernel's vocabulary. -/
abbrev akDstSym : (akLang k).Relations 2 := Sum.inl atmDst

/-- The write symbol in the kernel's vocabulary. -/
abbrev akWriteSym : (akLang k).Relations 2 := Sum.inl atmWrite

/-- The input symbol in the kernel's vocabulary. -/
abbrev akInpSym : (akLang k).Relations 2 := Sum.inl atmInp

/-- The mark of block `j` in the kernel's vocabulary. -/
abbrev akBlkSym (j : Fin k) : (akLang k).Relations 1 := Sum.inl (atmBlk j)

/-- The state variable of round `i`. -/
def akSt (i : Fin k) : (akLang k).Relations 2 :=
  Sum.inr (repSym tmGuessBlock TMIdx.state rfl k i)

/-- The head variable of round `i`. -/
def akHd (i : Fin k) : (akLang k).Relations 2 :=
  Sum.inr (repSym tmGuessBlock TMIdx.head rfl k i)

/-- The tape variable of round `i`. -/
def akTp (i : Fin k) : (akLang k).Relations 3 :=
  Sum.inr (repSym tmGuessBlock TMIdx.tape rfl k i)

end Symbols

/-! ### Formula builders -/

section Builders

variable {k : ℕ} {α : Type}

/-- `x` is a position, as a formula. -/
def akPosnF (x : α) : (akLang k).Formula α := fo%[x] akPosnSym(x)

/-- `x` is a transition, as a formula. -/
def akTrF (x : α) : (akLang k).Formula α := fo%[x] akTrSym(x)

/-- `x` is a start state, as a formula. -/
def akStartF (x : α) : (akLang k).Formula α := fo%[x] akStartSym(x)

/-- `x` is an accepting state, as a formula. -/
def akAccF (x : α) : (akLang k).Formula α := fo%[x] akAccSym(x)

/-- `x` is the blank symbol, as a formula. -/
def akBlankF (x : α) : (akLang k).Formula α := fo%[x] akBlankSym(x)

/-- `x` moves the head right, as a formula. -/
def akRightF (x : α) : (akLang k).Formula α := fo%[x] akRightSym(x)

/-- `x` carries the mark of block `j`, as a formula. -/
def akBlkF (j : Fin k) (x : α) : (akLang k).Formula α := fo%[x] (akBlkSym j)(x)

/-- `x ≤ y`, as a formula. -/
def akLeF (x y : α) : (akLang k).Formula α := fo%[x, y] akLeSym(x, y)

/-- `x = y`, as a formula. -/
def akEqF (x y : α) : (akLang k).Formula α := fo%[x, y] x ≐ y

/-- The transition `x` applies in the state `y`, as a formula. -/
def akSrcF (x y : α) : (akLang k).Formula α := fo%[x, y] akSrcSym(x, y)

/-- The transition `x` reads the symbol `y`, as a formula. -/
def akReadF (x y : α) : (akLang k).Formula α := fo%[x, y] akReadSym(x, y)

/-- The transition `x` moves to the state `y`, as a formula. -/
def akDstF (x y : α) : (akLang k).Formula α := fo%[x, y] akDstSym(x, y)

/-- The transition `x` writes the symbol `y`, as a formula. -/
def akWriteF (x y : α) : (akLang k).Formula α := fo%[x, y] akWriteSym(x, y)

/-- The cell `x` initially holds `y`, as a formula. -/
def akInpF (x y : α) : (akLang k).Formula α := fo%[x, y] akInpSym(x, y)

/-- In round `i`, the state at time `x` is `y`. -/
def akStF (i : Fin k) (x y : α) : (akLang k).Formula α := fo%[x, y] (akSt i)(x, y)

/-- In round `i`, the head at time `x` is on `y`. -/
def akHdF (i : Fin k) (x y : α) : (akLang k).Formula α := fo%[x, y] (akHd i)(x, y)

/-- In round `i`, at time `x` the cell `y` holds `z`. -/
def akTpF (i : Fin k) (x y z : α) : (akLang k).Formula α := fo%[x, y, z] (akTp i)(x, y, z)

/-- `x` is the lowest position, as a formula. -/
noncomputable def akMinPosF (x : α) : (akLang k).Formula α :=
  fo%[x] akPosnF⟨x⟩ ∧ ∀ y, akPosnF⟨y⟩ → akLeF⟨x, y⟩

/-- `x` is the highest position, as a formula. -/
noncomputable def akMaxPosF (x : α) : (akLang k).Formula α :=
  fo%[x] akPosnF⟨x⟩ ∧ ∀ y, akPosnF⟨y⟩ → akLeF⟨y, x⟩

/-- `y` is the position immediately above `x`, as a formula. -/
noncomputable def akSuccPosF (x y : α) : (akLang k).Formula α :=
  fo%[x, y] akPosnF⟨x⟩ ∧ akPosnF⟨y⟩ ∧ akLeF⟨x, y⟩ ∧ ¬ akEqF⟨x, y⟩ ∧
    ∀ z, akPosnF⟨z⟩ ∧ akLeF⟨x, z⟩ ∧ akLeF⟨z, y⟩ → akEqF⟨z, x⟩ ∨ akEqF⟨z, y⟩

/-- The cell `x` may initially hold `y`. -/
noncomputable def akInitTapeF (x y : α) : (akLang k).Formula α :=
  fo%[x, y] akInpF⟨x, y⟩ ∨ (∀ z, ¬ akInpF⟨x, z⟩) ∧ akBlankF⟨y⟩

/-- The state `x` is in a block at most `i`. -/
noncomputable def akBlkLeF (i : Fin k) (x : α) : (akLang k).Formula α :=
  Formula.iSup fun j : {j : Fin k // (j : ℕ) ≤ (i : ℕ)} => akBlkF j.1 x

/-- In round `i`, the state at time `t` is in a block at most `i` – that is, in
a block below `i + 1`. -/
noncomputable def akBlkLtF (i : Fin k) (t : α) : (akLang k).Formula α :=
  fo%[t] ∀ q, (akStF i)⟨t, q⟩ → (akBlkLeF i)⟨q⟩

/-- In round `i`, the state at time `t` is accepting. -/
noncomputable def akAccAtF (i : Fin k) (t : α) : (akLang k).Formula α :=
  fo%[t] ∀ q, (akStF i)⟨t, q⟩ → akAccF⟨q⟩

/-- In round `i`, the head at time `t` has somewhere to move in the direction
`dir`. -/
noncomputable def akMoveExF (i : Fin k) (t : α) (dir : Bool) : (akLang k).Formula α :=
  fo%[t] ∀ p, (akHdF i)⟨t, p⟩ → ∃ p', if dir then akSuccPosF⟨p, p'⟩ else akSuccPosF⟨p', p⟩

/-- In round `i`, the head moves from its cell at `t` to its cell at `t'`, in
the direction `dir`. -/
noncomputable def akMoveF (i : Fin k) (t t' : α) (dir : Bool) : (akLang k).Formula α :=
  fo%[t, t'] ∀ p p', (akHdF i)⟨t, p⟩ ∧ (akHdF i)⟨t', p'⟩ →
    if dir then akSuccPosF⟨p, p'⟩ else akSuccPosF⟨p', p⟩

/-- **The applicable-transition body**: the transition `τ` fires on the
configuration of round `i` at time `t`. -/
noncomputable def akAppBodyF (i : Fin k) (t τ : α) : (akLang k).Formula α :=
  fo%[t, τ] akTrF⟨τ⟩ ∧
    (∀ q, (akStF i)⟨t, q⟩ → akSrcF⟨τ, q⟩) ∧
    (∀ p a, (akHdF i)⟨t, p⟩ ∧ (akTpF i)⟨t, p, a⟩ → akReadF⟨τ, a⟩) ∧
    (∃ q, akDstF⟨τ, q⟩) ∧
    (∃ a, akWriteF⟨τ, a⟩) ∧
    ((akRightF⟨τ⟩ ∧ !(akMoveExF i t true)) ∨ (¬ akRightF⟨τ⟩ ∧ !(akMoveExF i t false)))

/-- In round `i`, some transition applies to the configuration at time `t`. -/
noncomputable def akAppTrF (i : Fin k) (t : α) : (akLang k).Formula α :=
  fo%[t] ∃ τ, (akAppBodyF i)⟨t, τ⟩

/-- **The step body**: in round `i`, the transition `τ` takes the configuration
at `t` to the one at `t'`. -/
noncomputable def akStepBodyF (i : Fin k) (t t' τ : α) : (akLang k).Formula α :=
  fo%[t, t', τ] akTrF⟨τ⟩ ∧
    (∀ q, (akStF i)⟨t, q⟩ → akSrcF⟨τ, q⟩) ∧
    (∀ p a, (akHdF i)⟨t, p⟩ ∧ (akTpF i)⟨t, p, a⟩ → akReadF⟨τ, a⟩) ∧
    (∀ q, (akStF i)⟨t', q⟩ → akDstF⟨τ, q⟩) ∧
    (∀ p a, (akHdF i)⟨t, p⟩ ∧ (akTpF i)⟨t', p, a⟩ → akWriteF⟨τ, a⟩) ∧
    (∀ p a, ¬ (akHdF i)⟨t, p⟩ → ((akTpF i)⟨t, p, a⟩ ↔ (akTpF i)⟨t', p, a⟩)) ∧
    ((akRightF⟨τ⟩ ∧ !(akMoveF i t t' true)) ∨ (¬ akRightF⟨τ⟩ ∧ !(akMoveF i t t' false)))

/-- In round `i`, the configuration at `t` steps to the one at `t'`. -/
noncomputable def akStepF (i : Fin k) (t t' : α) : (akLang k).Formula α :=
  fo%[t, t'] ∃ τ, (akStepBodyF i)⟨t, t', τ⟩

/-- The configuration of round `i'` at time `t'` is the one of round `i` at
time `t`. -/
noncomputable def akSameF (i i' : Fin k) (t t' : α) : (akLang k).Formula α :=
  fo%[t, t'] (∀ q, (akStF i')⟨t', q⟩ ↔ (akStF i)⟨t, q⟩) ∧
    (∀ p, (akHdF i')⟨t', p⟩ ↔ (akHdF i)⟨t, p⟩) ∧
    ∀ p a, (akTpF i')⟨t', p, a⟩ ↔ (akTpF i)⟨t, p, a⟩

/-- In round `i`, the configuration at time `t` is initial. -/
noncomputable def akInitAtF (i : Fin k) (t : α) : (akLang k).Formula α :=
  fo%[t] (∀ q, (akStF i)⟨t, q⟩ → akStartF⟨q⟩) ∧
    (∀ p, (akHdF i)⟨t, p⟩ → akMinPosF⟨p⟩) ∧
    ∀ p a, (akTpF i)⟨t, p, a⟩ → akInitTapeF⟨p, a⟩

end Builders

/-! ### Realization of the builders -/

section Realize

variable {k : ℕ} {A : Type} [instA : (Language.turingAlt k).Structure A]
  (ρs : Fin k → tmGuessBlock.Assignment A)

/-- The structure the kernel is read in: the instance expanded by one guessed
run per round. -/
@[instance_reducible]
def akStructure : (akLang k).Structure A :=
  letI := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  inferInstance

/-! #### The guessed relations -/

theorem relMap_akSt (i : Fin k) (v : Fin 2 → A) :
    @RelMap (akLang k) A (akStructure ρs) 2 (akSt i) v ↔ ρs i .state v := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  exact relMap_repSym tmGuessBlock TMIdx.state rfl k ρs i v

theorem relMap_akHd (i : Fin k) (v : Fin 2 → A) :
    @RelMap (akLang k) A (akStructure ρs) 2 (akHd i) v ↔ ρs i .head v := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  exact relMap_repSym tmGuessBlock TMIdx.head rfl k ρs i v

theorem relMap_akTp (i : Fin k) (v : Fin 3 → A) :
    @RelMap (akLang k) A (akStructure ρs) 3 (akTp i) v ↔ ρs i .tape v := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  exact relMap_repSym tmGuessBlock TMIdx.tape rfl k ρs i v

variable {α : Type} (v : α → A)

@[simp] theorem realize_akStF (i : Fin k) (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akStF i x y) v)
        ↔ runQ (ρs i) (v x) (v y) := by
  simp only [akStF, Formula.realize_rel₂, Term.realize_var]
  exact relMap_akSt ρs i _

@[simp] theorem realize_akHdF (i : Fin k) (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akHdF i x y) v)
        ↔ runH (ρs i) (v x) (v y) := by
  simp only [akHdF, Formula.realize_rel₂, Term.realize_var]
  exact relMap_akHd ρs i _

@[simp] theorem realize_akTpF (i : Fin k) (x y z : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akTpF i x y z) v) ↔
      runT (ρs i) (v x) (v y) (v z) := by
  simp only [akTpF, Formula.realize_rel]
  refine (relMap_akTp ρs i _).trans ?_
  exact iff_of_eq (congrArg (ρs i TMIdx.tape) (funext fun j => by fin_cases j <;> rfl))

/-! #### The machine relations -/

@[simp] theorem realize_akPosnF (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akPosnF x) v)
        ↔ (atmData k A).Posn (v x) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akPosnF, Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akTrF (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akTrF x) v) ↔ (atmData k A).Tr (v x) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akTrF, Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akStartF (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akStartF x) v)
      ↔ (atmData k A).Start (v x) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akStartF, Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akAccF (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akAccF x) v) ↔ (atmData k A).Acc (v x) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akAccF, Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akBlankF (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akBlankF x) v)
      ↔ (atmData k A).Blank (v x) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akBlankF, Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akRightF (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akRightF x) v)
      ↔ (atmData k A).Right (v x) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akRightF, Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akBlkF (j : Fin k) (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akBlkF j x) v)
      ↔ (atmData k A).Blk j (v x) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akBlkF, Formula.realize_rel₁, Term.realize_var]
  exact (atmBlk_iff j.isLt (v x)).symm

@[simp] theorem realize_akLeF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akLeF x y) v)
      ↔ (atmData k A).Le (v x) (v y) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akLeF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akEqF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akEqF x y) v) ↔ v x = v y := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp [akEqF]

@[simp] theorem realize_akSrcF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akSrcF x y) v)
      ↔ (atmData k A).Src (v x) (v y) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akSrcF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akReadF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akReadF x y) v)
      ↔ (atmData k A).Read (v x) (v y) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akReadF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akDstF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akDstF x y) v)
      ↔ (atmData k A).Dst (v x) (v y) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akDstF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akWriteF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akWriteF x y) v)
      ↔ (atmData k A).Write (v x) (v y) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akWriteF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_akInpF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akInpF x y) v)
      ↔ (atmData k A).Inp (v x) (v y) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  simp only [akInpF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

/-! #### The derived formulas -/

@[simp] theorem realize_akMinPosF (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akMinPosF x) v) ↔
      MinPos (atmData k A).Le (atmData k A).Posn (v x) := by
  simp only [akMinPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_akPosnF, realize_akLeF, Sum.elim_inl, Sum.elim_inr, MinPos]
  exact and_congr Iff.rfl ⟨fun h a => h (fun _ => a), fun h i => h (i 0)⟩

@[simp] theorem realize_akMaxPosF (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akMaxPosF x) v) ↔
      MaxPos (atmData k A).Le (atmData k A).Posn (v x) := by
  simp only [akMaxPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_akPosnF, realize_akLeF, Sum.elim_inl, Sum.elim_inr, MaxPos]
  exact and_congr Iff.rfl ⟨fun h a => h (fun _ => a), fun h i => h (i 0)⟩

@[simp] theorem realize_akSuccPosF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akSuccPosF x y) v) ↔
      SuccPos (atmData k A).Le (atmData k A).Posn (v x) (v y) := by
  simp only [akSuccPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_sup, realize_akPosnF, realize_akLeF, realize_akEqF,
    Sum.elim_inl, Sum.elim_inr, SuccPos, ne_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  exact ⟨fun h a ha h₁ h₂ => h (fun _ => a) ⟨ha, h₁, h₂⟩,
    fun h i hi => h (i 0) hi.1 hi.2.1 hi.2.2⟩

@[simp] theorem realize_akInitTapeF (x y : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akInitTapeF x y) v) ↔
      (atmData k A).Inp (v x) (v y) ∨ ((∀ b, ¬(atmData k A).Inp (v x) b) ∧ (atmData k A).Blank (v
          y)) := by
  simp only [akInitTapeF, Formula.realize_sup, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_not, realize_akInpF, realize_akBlankF, Sum.elim_inl, Sum.elim_inr]
  exact or_congr Iff.rfl (and_congr ⟨fun h b => h fun _ => b, fun h i => h (i 0)⟩ Iff.rfl)

@[simp] theorem realize_akBlkLeF (i : Fin k) (x : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akBlkLeF i x) v) ↔
      (atmData k A).BlkLt (i + 1) (v x) := by
  simp only [akBlkLeF, Formula.realize_iSup, realize_akBlkF, Subtype.exists]
  constructor
  · rintro ⟨j, hj, hb⟩
    exact ⟨j, by omega, hb⟩
  · rintro ⟨j, hj, hb⟩
    exact ⟨⟨j, hb.1⟩, by simpa using by omega, hb⟩

@[simp] theorem realize_akBlkLtF (i : Fin k) (t : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akBlkLtF i t) v) ↔
      (atmData k A).RunBlkLt (ρs i) (i + 1) (v t) := by
  simp only [akBlkLtF, Formula.realize_iAlls, Formula.realize_imp, realize_akStF,
    realize_akBlkLeF, Sum.elim_inl, Sum.elim_inr, ATMData.RunBlkLt]
  exact ⟨fun h q hq => h (fun _ => q) hq, fun h j hj => h (j 0) hj⟩

@[simp] theorem realize_akAccAtF (i : Fin k) (t : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akAccAtF i t) v) ↔
      (atmData k A).RunAcc (ρs i) (v t) := by
  simp only [akAccAtF, Formula.realize_iAlls, Formula.realize_imp, realize_akStF,
    realize_akAccF, Sum.elim_inl, Sum.elim_inr, ATMData.RunAcc]
  exact ⟨fun h q hq => h (fun _ => q) hq, fun h j hj => h (j 0) hj⟩

@[simp] theorem realize_akMoveExF (i : Fin k) (t : α) (dir : Bool) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akMoveExF i t dir) v) ↔
      ∀ p, runH (ρs i) (v t) p →
        ∃ p', if dir then SuccPos (atmData k A).Le (atmData k A).Posn p p' else SuccPos (atmData k
            A).Le (atmData k A).Posn p' p := by
  cases dir <;>
    simp only [akMoveExF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs,
      realize_akHdF, realize_akSuccPosF, Sum.elim_inl, Sum.elim_inr, if_true, if_false,
      Bool.false_eq_true] <;>
    exact ⟨fun h p hp => let ⟨j', hj'⟩ := h (fun _ => p) hp; ⟨j' 0, hj'⟩,
      fun h j hj => let ⟨p', hp'⟩ := h (j 0) hj; ⟨fun _ => p', hp'⟩⟩

@[simp] theorem realize_akMoveF (i : Fin k) (t t' : α) (dir : Bool) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akMoveF i t t' dir) v) ↔
      ∀ p p', runH (ρs i) (v t) p → runH (ρs i) (v t') p' →
        (if dir then SuccPos (atmData k A).Le (atmData k A).Posn p p' else SuccPos (atmData k A).Le
            (atmData k A).Posn p' p) := by
  cases dir <;>
    simp only [akMoveF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      realize_akHdF, realize_akSuccPosF, Sum.elim_inl, Sum.elim_inr, if_true, if_false,
      Bool.false_eq_true] <;>
    exact ⟨fun h p p' h₁ h₂ => h ![p, p'] ⟨h₁, h₂⟩, fun h j hj => h (j 0) (j 1) hj.1 hj.2⟩

/-! #### The composite formulas -/

@[simp] theorem realize_akAppBodyF (i : Fin k) (t τ : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akAppBodyF i t τ) v) ↔
      (atmData k A).Tr (v τ) ∧ (∀ q, runQ (ρs i) (v t) q → (atmData k A).Src (v τ) q) ∧
        (∀ p a, runH (ρs i) (v t) p → runT (ρs i) (v t) p a → (atmData k A).Read (v τ) a) ∧
        (∃ q, (atmData k A).Dst (v τ) q) ∧ (∃ a, (atmData k A).Write (v τ) a) ∧
        (((atmData k A).Right (v τ) ∧ ∀ p, runH (ρs i) (v t) p →
            ∃ p', SuccPos (atmData k A).Le (atmData k A).Posn p p') ∨
          (¬(atmData k A).Right (v τ) ∧ ∀ p, runH (ρs i) (v t) p →
            ∃ p', SuccPos (atmData k A).Le (atmData k A).Posn p' p)) := by
  simp only [akAppBodyF, Formula.realize_inf, Formula.realize_sup, Formula.realize_imp,
    Formula.realize_not, Formula.realize_iAlls, Formula.realize_iExs, realize_akTrF,
    realize_akStF, realize_akSrcF, realize_akHdF, realize_akTpF, realize_akReadF,
    realize_akDstF, realize_akWriteF, realize_akRightF, realize_akMoveExF, Sum.elim_inl,
    Sum.elim_inr, if_true, if_false, Bool.false_eq_true]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl))))
  · exact ⟨fun h q hq => h (fun _ => q) hq, fun h j hj => h (j 0) hj⟩
  · exact ⟨fun h p a h₁ h₂ => h ![p, a] ⟨h₁, h₂⟩, fun h j hj => h (j 0) (j 1) hj.1 hj.2⟩
  · exact ⟨fun ⟨j, hj⟩ => ⟨j 0, hj⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩
  · exact ⟨fun ⟨j, hj⟩ => ⟨j 0, hj⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, ha⟩⟩

@[simp] theorem realize_akAppTrF (i : Fin k) (t : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akAppTrF i t) v) ↔
      (atmData k A).RunAppTr (ρs i) (v t) := by
  simp only [akAppTrF, Formula.realize_iExs, realize_akAppBodyF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨j, hj⟩ => ⟨j 0, hj⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

@[simp] theorem realize_akStepBodyF (i : Fin k) (t t' τ : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akStepBodyF i t t' τ) v) ↔
      (atmData k A).Tr (v τ) ∧ (∀ q, runQ (ρs i) (v t) q → (atmData k A).Src (v τ) q) ∧
        (∀ p a, runH (ρs i) (v t) p → runT (ρs i) (v t) p a → (atmData k A).Read (v τ) a) ∧
        (∀ q, runQ (ρs i) (v t') q → (atmData k A).Dst (v τ) q) ∧
        (∀ p a, runH (ρs i) (v t) p → runT (ρs i) (v t') p a → (atmData k A).Write (v τ) a) ∧
        (∀ p a, ¬runH (ρs i) (v t) p →
          (runT (ρs i) (v t) p a ↔ runT (ρs i) (v t') p a)) ∧
        (((atmData k A).Right (v τ) ∧ ∀ p p', runH (ρs i) (v t) p → runH (ρs i) (v t') p' →
            SuccPos (atmData k A).Le (atmData k A).Posn p p') ∨
          (¬(atmData k A).Right (v τ) ∧ ∀ p p', runH (ρs i) (v t) p → runH (ρs i) (v t') p' →
            SuccPos (atmData k A).Le (atmData k A).Posn p' p)) := by
  simp only [akStepBodyF, Formula.realize_inf, Formula.realize_sup, Formula.realize_imp,
    Formula.realize_not, Formula.realize_iff, Formula.realize_iAlls, realize_akTrF,
    realize_akStF, realize_akSrcF, realize_akHdF, realize_akTpF, realize_akReadF,
    realize_akDstF, realize_akWriteF, realize_akRightF, realize_akMoveF, Sum.elim_inl,
    Sum.elim_inr, if_true, if_false, Bool.false_eq_true]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_
    (and_congr ?_ Iff.rfl)))))
  · exact ⟨fun h q hq => h (fun _ => q) hq, fun h j hj => h (j 0) hj⟩
  · exact ⟨fun h p a h₁ h₂ => h ![p, a] ⟨h₁, h₂⟩, fun h j hj => h (j 0) (j 1) hj.1 hj.2⟩
  · exact ⟨fun h q hq => h (fun _ => q) hq, fun h j hj => h (j 0) hj⟩
  · exact ⟨fun h p a h₁ h₂ => h ![p, a] ⟨h₁, h₂⟩, fun h j hj => h (j 0) (j 1) hj.1 hj.2⟩
  · exact ⟨fun h p a hp => h ![p, a] hp, fun h j hj => h (j 0) (j 1) hj⟩

@[simp] theorem realize_akStepF (i : Fin k) (t t' : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akStepF i t t') v) ↔
      (atmData k A).RunStep (ρ := ρs i) (v t) (v t') := by
  simp only [akStepF, Formula.realize_iExs, realize_akStepBodyF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨j, hj⟩ => ⟨j 0, hj⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

@[simp] theorem realize_akSameF (i i' : Fin k) (t t' : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akSameF i i' t t') v) ↔
      ATMData.RunSame (ρs i) (ρs i') (v t) (v t') := by
  simp only [akSameF, Formula.realize_inf, Formula.realize_iff, Formula.realize_iAlls,
    realize_akStF, realize_akHdF, realize_akTpF, Sum.elim_inl, Sum.elim_inr]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact ⟨fun h q => h fun _ => q, fun h j => h (j 0)⟩
  · exact ⟨fun h p => h fun _ => p, fun h j => h (j 0)⟩
  · exact ⟨fun h p a => h ![p, a], fun h j => h (j 0) (j 1)⟩

@[simp] theorem realize_akInitAtF (i : Fin k) (t : α) :
    (@Formula.Realize (akLang k) A (akStructure ρs) _ (akInitAtF i t) v) ↔
      (atmData k A).RunInit (ρs i) (v t) := by
  simp only [akInitAtF, Formula.realize_inf, Formula.realize_imp, Formula.realize_iAlls,
    realize_akStF, realize_akStartF, realize_akHdF, realize_akMinPosF, realize_akTpF,
    realize_akInitTapeF, Sum.elim_inl, Sum.elim_inr, ATMData.RunInit, TMData.InitTape]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact ⟨fun h q hq => h (fun _ => q) hq, fun h j hj => h (j 0) hj⟩
  · exact ⟨fun h p hp => h (fun _ => p) hp, fun h j hj => h (j 0) hj⟩
  · exact ⟨fun h p a hp => h ![p, a] hp, fun h j hj => h (j 0) (j 1) hj⟩

end Realize

/-! ### The clauses -/

section Clauses

variable {k : ℕ}

/-- In round `i` there is a state at each time. -/
noncomputable def akStateExClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t, ∃ q, (akStF i)⟨t, q⟩

/-- In round `i` there is only one state at each time. -/
noncomputable def akStateUniqClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t q q', (akStF i)⟨t, q⟩ ∧ (akStF i)⟨t, q'⟩ → akEqF⟨q, q'⟩

/-- In round `i` the head is somewhere at each time. -/
noncomputable def akHeadExClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t, ∃ p, (akHdF i)⟨t, p⟩

/-- In round `i` the head is in only one place at each time. -/
noncomputable def akHeadUniqClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t p p', (akHdF i)⟨t, p⟩ ∧ (akHdF i)⟨t, p'⟩ → akEqF⟨p, p'⟩

/-- In round `i` every cell holds a symbol at each time. -/
noncomputable def akTapeExClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t p, ∃ a, (akTpF i)⟨t, p, a⟩

/-- In round `i` every cell holds only one symbol at each time. -/
noncomputable def akTapeUniqClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t p a a', (akTpF i)⟨t, p, a⟩ ∧ (akTpF i)⟨t, p, a'⟩ → akEqF⟨a, a'⟩

/-- **The guess of round `i` is functional.** -/
noncomputable def akFunClause (i : Fin k) : (akLang k).Sentence :=
  akStateExClause i ⊓ (akStateUniqClause i ⊓ (akHeadExClause i ⊓ (akHeadUniqClause i ⊓
    (akTapeExClause i ⊓ akTapeUniqClause i))))

/-- In round `i` the configuration at the lowest time is initial. -/
noncomputable def akInitClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t, akMinPosF⟨t⟩ → (akInitAtF i)⟨t⟩

/-- In round `i` the blocks never decrease. -/
noncomputable def akBlkMonoClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t t' q q', akSuccPosF⟨t, t'⟩ ∧ (akStF i)⟨t, q⟩ ∧ (akStF i)⟨t', q'⟩ →
    ⋀ jj : {jj : Fin k × Fin k // ¬((jj.1 : ℕ) ≤ (jj.2 : ℕ))},
      ¬ ((akBlkF jj.1.1)⟨q⟩ ∧ (akBlkF jj.1.2)⟨q'⟩)

/-- In round `i` consecutive times step or stutter, as far as the round answers
for them. -/
noncomputable def akStepClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t t', akSuccPosF⟨t, t'⟩ ∧ (akBlkLtF i)⟨t⟩ →
    ((akStepF i)⟨t, t'⟩ ∧ ¬ (akAccAtF i)⟨t⟩) ∨
      ((akSameF i i)⟨t, t'⟩ ∧ ((akAccAtF i)⟨t⟩ ∨ ¬ (akAppTrF i)⟨t⟩))

/-- **The guess of round `i` is legal below block `i + 1`.** -/
noncomputable def akLegalClause (i : Fin k) : (akLang k).Sentence :=
  akInitClause i ⊓ (akBlkMonoClause i ⊓ akStepClause i)

/-- **Round `i` reproduces what round `j` committed.** -/
noncomputable def akAgreeClause (j i : Fin k) : (akLang k).Sentence :=
  fo% (∀ t, akPosnF⟨t⟩ ∧ (akBlkLtF j)⟨t⟩ → (akSameF j i)⟨t, t⟩) ∧
    ∀ t t', akSuccPosF⟨t, t'⟩ ∧ (akBlkLtF j)⟨t⟩ → (akSameF j i)⟨t', t'⟩

/-- **The guess of round `i` accepts.** -/
noncomputable def akAccClause (i : Fin k) : (akLang k).Sentence :=
  fo% ∀ t, akMaxPosF⟨t⟩ → (akAccAtF i)⟨t⟩

variable (k)

/-- The order is reflexive. -/
noncomputable def akReflClause : (akLang k).Sentence :=
  fo% ∀ a, akLeF⟨a, a⟩

/-- The order is transitive. -/
noncomputable def akTransClause : (akLang k).Sentence :=
  fo% ∀ a b c, akLeF⟨a, b⟩ ∧ akLeF⟨b, c⟩ → akLeF⟨a, c⟩

/-- The order is antisymmetric. -/
noncomputable def akAntisymClause : (akLang k).Sentence :=
  fo% ∀ a b, akLeF⟨a, b⟩ ∧ akLeF⟨b, a⟩ → akEqF⟨a, b⟩

/-- The order is total. -/
noncomputable def akTotalClause : (akLang k).Sentence :=
  fo% ∀ a b, akLeF⟨a, b⟩ ∨ akLeF⟨b, a⟩

/-- There is a position. -/
noncomputable def akPosnExClause : (akLang k).Sentence :=
  fo% ∃ p, akPosnF⟨p⟩

/-- The input is functional. -/
noncomputable def akInpFunClause : (akLang k).Sentence :=
  fo% ∀ p a b, akInpF⟨p, a⟩ ∧ akInpF⟨p, b⟩ → akEqF⟨a, b⟩

/-- There is a blank symbol. -/
noncomputable def akBlankExClause : (akLang k).Sentence :=
  fo% ∃ b, akBlankF⟨b⟩

/-- There is only one blank symbol. -/
noncomputable def akBlankUniqClause : (akLang k).Sentence :=
  fo% ∀ a b, akBlankF⟨a⟩ ∧ akBlankF⟨b⟩ → akEqF⟨a, b⟩

/-- **The instance is a well-formed machine.** -/
noncomputable def akWfClause : (akLang k).Sentence :=
  akReflClause k ⊓ (akTransClause k ⊓ (akAntisymClause k ⊓ (akTotalClause k ⊓
    (akPosnExClause k ⊓ (akInpFunClause k ⊓ (akBlankExClause k ⊓ akBlankUniqClause k))))))

/-- Every state carries exactly one block mark. -/
noncomputable def akOneBlkClause : (akLang k).Sentence :=
  fo% ∀ q, ⋁ j : Fin k, (akBlkF j)⟨q⟩ ∧ ⋀ j' : {j' : Fin k // j' ≠ j}, ¬ (akBlkF j'.1)⟨q⟩

/-- A transition stays in its block or moves to the next one. -/
noncomputable def akStepBlkClause : (akLang k).Sentence :=
  fo% ∀ τ q q', akTrF⟨τ⟩ ∧ akSrcF⟨τ, q⟩ ∧ akDstF⟨τ, q'⟩ →
    ⋀ jj : {jj : Fin k × Fin k // ¬((jj.1 : ℕ) ≤ (jj.2 : ℕ) ∧ (jj.2 : ℕ) ≤ (jj.1 : ℕ) + 1)},
      ¬ ((akBlkF jj.1.1)⟨q⟩ ∧ (akBlkF jj.1.2)⟨q'⟩)

/-- A start state is in block `0`. -/
noncomputable def akStartBlkClause : (akLang k).Sentence :=
  fo% ∀ q, akStartF⟨q⟩ → ⋁ j : {j : Fin k // (j : ℕ) = 0}, (akBlkF j.1)⟨q⟩

/-- **The block structure is well formed.** -/
noncomputable def akBwfClause : (akLang k).Sentence :=
  akOneBlkClause k ⊓ (akStepBlkClause k ⊓ akStartBlkClause k)

/-- There is a start state – the one existence clause of the game that is not
redundant. -/
noncomputable def akStartExClause : (akLang k).Sentence :=
  fo% ∃ q, akStartF⟨q⟩

end Clauses

/-! ### Realization of the clauses -/

section RealizeClauses

variable {k : ℕ} {A : Type} [instA : (Language.turingAlt k).Structure A]
  (ρs : Fin k → tmGuessBlock.Assignment A)

private theorem realize_inf_sentence (φ ψ : (akLang k).Sentence) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (φ ⊓ ψ)) ↔
      (@Sentence.Realize (akLang k) A (akStructure ρs) φ) ∧
        (@Sentence.Realize (akLang k) A (akStructure ρs) ψ) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  exact Formula.realize_inf

theorem realize_akStateExClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akStateExClause i)) ↔
      ∀ t, ∃ q, runQ (ρs i) t q := by
  simp only [akStateExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_akStF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h t => let ⟨j, hj⟩ := h fun _ => t; ⟨j 0, hj⟩,
    fun h j => let ⟨q, hq⟩ := h (j 0); ⟨fun _ => q, hq⟩⟩

theorem realize_akStateUniqClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akStateUniqClause i)) ↔
      ∀ t q q', runQ (ρs i) t q → runQ (ρs i) t q' → q = q' := by
  simp only [akStateUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_akStF, realize_akEqF, Sum.elim_inr]
  exact ⟨fun h t q q' h₁ h₂ => h ![t, q, q'] ⟨h₁, h₂⟩,
    fun h j hj => h (j 0) (j 1) (j 2) hj.1 hj.2⟩

theorem realize_akHeadExClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akHeadExClause i)) ↔
      ∀ t, ∃ p, runH (ρs i) t p := by
  simp only [akHeadExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_akHdF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h t => let ⟨j, hj⟩ := h fun _ => t; ⟨j 0, hj⟩,
    fun h j => let ⟨p, hp⟩ := h (j 0); ⟨fun _ => p, hp⟩⟩

theorem realize_akHeadUniqClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akHeadUniqClause i)) ↔
      ∀ t p p', runH (ρs i) t p → runH (ρs i) t p' → p = p' := by
  simp only [akHeadUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_akHdF, realize_akEqF, Sum.elim_inr]
  exact ⟨fun h t p p' h₁ h₂ => h ![t, p, p'] ⟨h₁, h₂⟩,
    fun h j hj => h (j 0) (j 1) (j 2) hj.1 hj.2⟩

theorem realize_akTapeExClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akTapeExClause i)) ↔
      ∀ t p, ∃ a, runT (ρs i) t p a := by
  simp only [akTapeExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_akTpF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h t p => let ⟨j, hj⟩ := h ![t, p]; ⟨j 0, hj⟩,
    fun h j => let ⟨a, ha⟩ := h (j 0) (j 1); ⟨fun _ => a, ha⟩⟩

theorem realize_akTapeUniqClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akTapeUniqClause i)) ↔
      ∀ t p a a', runT (ρs i) t p a → runT (ρs i) t p a' → a = a' := by
  simp only [akTapeUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_akTpF, realize_akEqF, Sum.elim_inr]
  exact ⟨fun h t p a a' h₁ h₂ => h ![t, p, a, a'] ⟨h₁, h₂⟩,
    fun h j hj => h (j 0) (j 1) (j 2) (j 3) hj.1 hj.2⟩

theorem realize_akFunClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akFunClause i)) ↔ RunFun (ρs i) := by
  simp only [akFunClause, realize_inf_sentence, realize_akStateExClause,
    realize_akStateUniqClause, realize_akHeadExClause, realize_akHeadUniqClause,
    realize_akTapeExClause, realize_akTapeUniqClause]
  exact Iff.rfl

theorem realize_akInitClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akInitClause i)) ↔
      ∀ p, MinPos (atmData k A).Le (atmData k A).Posn p → (atmData k A).RunInit (ρs i) p := by
  simp only [akInitClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    realize_akMinPosF, realize_akInitAtF, Sum.elim_inr]
  exact ⟨fun h p hp => h (fun _ => p) hp, fun h j hj => h (j 0) hj⟩

theorem realize_akBlkMonoClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akBlkMonoClause i)) ↔
      (atmData k A).RunBlkMono (ρs i) := by
  simp only [akBlkMonoClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_iInf, Formula.realize_not, realize_akSuccPosF,
    realize_akStF, realize_akBlkF, Sum.elim_inr, Subtype.forall, Prod.forall]
  constructor
  · intro h p q hpq x y hx hy j j' hj hj'
    by_contra hcon
    exact h ![p, q, x, y] ⟨hpq, hx, hy⟩ ⟨j, lt_of_atmBlk hj⟩ ⟨j', lt_of_atmBlk hj'⟩ hcon ⟨hj, hj'⟩
  · rintro h j hj a b hab ⟨hx, hy⟩
    exact hab (h (j 0) (j 1) hj.1 (j 2) (j 3) hj.2.1 hj.2.2 a b hx hy)

theorem realize_akStepClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akStepClause i)) ↔
      ∀ p q, SuccPos (atmData k A).Le (atmData k A).Posn p q →
        (atmData k A).RunBlkLt (ρs i) ((i : ℕ) + 1) p →
        ((atmData k A).RunStep (ρ := ρs i) p q ∧ ¬(atmData k A).RunAcc (ρs i) p) ∨
          (ATMData.RunSame (ρs i) (ρs i) p q ∧
            ((atmData k A).RunAcc (ρs i) p ∨ ¬(atmData k A).RunAppTr (ρs i) p)) := by
  simp only [akStepClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_sup, Formula.realize_not, realize_akSuccPosF,
    realize_akBlkLtF, realize_akStepF, realize_akAccAtF, realize_akSameF, realize_akAppTrF,
    Sum.elim_inr]
  exact ⟨fun h p q h₁ h₂ => h ![p, q] ⟨h₁, h₂⟩, fun h j hj => h (j 0) (j 1) hj.1 hj.2⟩

theorem realize_akLegalClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akLegalClause i)) ↔
      (atmData k A).RunLegalBelow (ρs i) ((i : ℕ) + 1) := by
  simp only [akLegalClause, realize_inf_sentence, realize_akInitClause, realize_akBlkMonoClause,
    realize_akStepClause]
  exact Iff.rfl

theorem realize_akAgreeClause (j i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akAgreeClause j i)) ↔
      (atmData k A).RunAgreeBelow (ρs j) (ρs i) ((j : ℕ) + 1) := by
  simp only [akAgreeClause, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_inf, realize_akPosnF, realize_akBlkLtF,
    realize_akSameF, realize_akSuccPosF, Sum.elim_inr]
  exact and_congr ⟨fun h t h₁ h₂ => h (fun _ => t) ⟨h₁, h₂⟩, fun h l hl => h (l 0) hl.1 hl.2⟩
    ⟨fun h t t' h₁ h₂ => h ![t, t'] ⟨h₁, h₂⟩, fun h l hl => h (l 0) (l 1) hl.1 hl.2⟩

theorem realize_akAccClause (i : Fin k) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akAccClause i)) ↔
      (atmData k A).RunAccAt (ρs i) := by
  simp only [akAccClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    realize_akMaxPosF, realize_akAccAtF, Sum.elim_inr]
  exact ⟨fun h p hp => h (fun _ => p) hp, fun h l hl => h (l 0) hl⟩

theorem realize_akWfClause :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akWfClause k)) ↔
      (atmData k A).toTMData.WellFormed := by
  simp only [akWfClause, akReflClause, akTransClause, akAntisymClause,
    akTotalClause, akPosnExClause, akInpFunClause, akBlankExClause, akBlankUniqClause,
    Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_sup, realize_akLeF, realize_akEqF, realize_akPosnF,
    realize_akInpF, realize_akBlankF, Sum.elim_inr, TMData.WellFormed, IsLinOrd]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨⟨fun x => h1 fun _ => x, fun x y z hxy hyz => h2 ![x, y, z] ⟨hxy, hyz⟩,
      fun x y hxy hyx => h3 ![x, y] ⟨hxy, hyx⟩, fun x y => h4 ![x, y]⟩, ?_, ?_, ?_, ?_⟩
    · exact let ⟨l, hl⟩ := h5; ⟨l 0, hl⟩
    · exact fun p a b ha hb => h6 ![p, a, b] ⟨ha, hb⟩
    · exact let ⟨l, hl⟩ := h7; ⟨l 0, hl⟩
    · exact fun a b ha hb => h8 ![a, b] ⟨ha, hb⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩
    refine ⟨fun l => h1 (l 0), fun l hl => h2 (l 0) (l 1) (l 2) hl.1 hl.2,
      fun l hl => h3 (l 0) (l 1) hl.1 hl.2, fun l => h4 (l 0) (l 1), ?_, ?_, ?_, ?_⟩
    · exact let ⟨p, hp⟩ := h5; ⟨fun _ => p, hp⟩
    · exact fun l hl => h6 (l 0) (l 1) (l 2) hl.1 hl.2
    · exact let ⟨b, hb⟩ := h7; ⟨fun _ => b, hb⟩
    · exact fun l hl => h8 (l 0) (l 1) hl.1 hl.2

theorem realize_akBwfClause :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akBwfClause k)) ↔
      (atmData k A).BlocksWellFormed k := by
  simp only [akBwfClause, akOneBlkClause, akStepBlkClause,
    akStartBlkClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iSup,
    Formula.realize_iInf, Formula.realize_imp, Formula.realize_inf, Formula.realize_not,
    realize_akBlkF, realize_akTrF, realize_akSrcF, realize_akDstF, realize_akStartF,
    Sum.elim_inr, Subtype.exists, Subtype.forall, Prod.forall, ATMData.BlocksWellFormed]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h q
      obtain ⟨j, hj, huniq⟩ := h fun _ => q
      refine ⟨j, j.isLt, hj, fun j' hj' => ?_⟩
      by_contra hne
      exact huniq ⟨j', lt_of_atmBlk hj'⟩ (fun hcon => hne (congrArg Fin.val hcon)) hj'
    · intro h l
      obtain ⟨j, hjk, hj, huniq⟩ := h (l 0)
      exact ⟨⟨j, hjk⟩, hj, fun j' hne hj' => hne (Fin.ext (huniq j' hj'))⟩
  · constructor
    · intro h τ q q' j j' hτ hsrc hdst hj hj'
      by_contra hcon
      exact h ![τ, q, q'] ⟨hτ, hsrc, hdst⟩ ⟨j, lt_of_atmBlk hj⟩ ⟨j', lt_of_atmBlk hj'⟩ hcon
        ⟨hj, hj'⟩
    · rintro h l hl a b hab ⟨hj, hj'⟩
      exact hab (h (l 0) (l 1) (l 2) a b hl.1 hl.2.1 hl.2.2 hj hj')
  · constructor
    · intro h q hq
      obtain ⟨j, hj0, hj⟩ := h (fun _ => q) hq
      exact hj0 ▸ hj
    · intro h l hl
      exact ⟨⟨0, lt_of_atmBlk (h (l 0) hl)⟩, rfl, h (l 0) hl⟩

theorem realize_akStartExClause :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akStartExClause k)) ↔
      ∃ q, (atmData k A).Start q := by
  simp only [akStartExClause, Sentence.Realize, Formula.realize_iExs, realize_akStartF,
    Sum.elim_inr]
  exact ⟨fun ⟨l, hl⟩ => ⟨l 0, hl⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩

end RealizeClauses

/-! ### The ladder and the kernel -/

/-- The connective a round of the ladder uses, as a formula: a conjunction
where the round is existential, an implication where it is universal. -/
noncomputable def polForm {k : ℕ} (pol : Bool) (φ ψ : (akLang k).Sentence) :
    (akLang k).Sentence :=
  match pol with
  | true => φ ⊓ ψ
  | false => φ.imp ψ

/-- The condition round `i` puts on its guess: functional, legal, and – unless
it is the first round – agreeing with the round before it. -/
noncomputable def akRoundF {k : ℕ} (i : Fin k) (prev : Option (Fin k)) : (akLang k).Sentence :=
  match prev with
  | none => akFunClause i ⊓ akLegalClause i
  | some j => akFunClause i ⊓ (akLegalClause i ⊓ akAgreeClause j i)

/-- **The ladder**, as a first-order sentence: the `m` rounds still to play
from round `i` on, chained by `DescriptiveComplexity.polForm`, with the last
guess required to accept. -/
noncomputable def akLadderF (start : Bool) (k : ℕ) :
    ∀ (m i : ℕ), i + m = k → Option (Fin k) → (akLang k).Sentence
  | 0, _, _, none => ⊥
  | 0, _, _, some j => akAccClause j
  | m + 1, i, h, prev =>
      polForm (blockPol start i) (akRoundF ⟨i, by omega⟩ prev)
        (akLadderF start k m (i + 1) (by omega) (some ⟨i, by omega⟩))

/-- **The kernel of the `Σₖ` sentence**: the instance is a well-formed
alternating machine with a start state, and the ladder holds of the guessed
rounds. -/
noncomputable def akKernel (start : Bool) (k : ℕ) : (akLang k).Sentence :=
  akWfClause k ⊓ (akBwfClause k ⊓ (akStartExClause k ⊓ akLadderF start k k 0 (by omega) none))

/-- The round before round `i`, where there is one, is round `i - 1`. -/
def PrevOk {k : ℕ} (i : ℕ) : Option (Fin k) → Prop
  | none => i = 0
  | some j => (j : ℕ) + 1 = i

section RealizeLadder

variable {k : ℕ} {A : Type} [instA : (Language.turingAlt k).Structure A]
  (ρs : Fin k → tmGuessBlock.Assignment A)

theorem realize_polForm (pol : Bool) (φ ψ : (akLang k).Sentence) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (polForm pol φ ψ)) ↔
      polConn pol (@Sentence.Realize (akLang k) A (akStructure ρs) φ)
        (@Sentence.Realize (akLang k) A (akStructure ρs) ψ) := by
  let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
  cases pol
  · exact Formula.realize_imp
  · exact Formula.realize_inf

theorem realize_akRoundF (i : Fin k) (prev : Option (Fin k)) (hprev : PrevOk (i : ℕ) prev) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akRoundF i prev)) ↔
      RunFun (ρs i) ∧ (atmData k A).RunGuard (i : ℕ) (prev.map ρs) (ρs i) := by
  cases prev with
  | none =>
    simp only [akRoundF, realize_inf_sentence, realize_akFunClause, realize_akLegalClause,
      Option.map_none, ATMData.RunGuard]
    have hi : (i : ℕ) = 0 := hprev
    rw [hi]
  | some j =>
    simp only [akRoundF, realize_inf_sentence, realize_akFunClause, realize_akLegalClause,
      realize_akAgreeClause, Option.map_some, ATMData.RunGuard, ATMData.RunRoundCond]
    rw [show (j : ℕ) + 1 = (i : ℕ) from hprev]

theorem realize_akLadderF (start : Bool) :
    ∀ (m i : ℕ) (h : i + m = k) (prev : Option (Fin k)) (_ : PrevOk i prev)
      (νs : Fin m → tmGuessBlock.Assignment A) (_ : ∀ j : Fin m, νs j = ρs ⟨i + j, by omega⟩),
      (@Sentence.Realize (akLang k) A (akStructure ρs) (akLadderF start k m i h prev)) ↔
        (atmData k A).runMatrix start m i (prev.map ρs) νs := by
  intro m
  induction m with
  | zero =>
    intro i h prev _ νs _
    cases prev with
    | none =>
      let := (repMerged tmGuessBlock k).structure (repBlockAssign tmGuessBlock A k ρs)
      exact Formula.realize_bot
    | some j => exact realize_akAccClause ρs j
  | succ m ih =>
    intro i h prev hprev νs hν
    have hik : i < k := by omega
    have h0 : νs 0 = ρs ⟨i, hik⟩ := by
      rw [hν 0]
      exact congrArg ρs (Fin.ext (by simp))
    have hstep : ∀ j : Fin m, (fun l : Fin m => νs l.succ) j = ρs ⟨i + 1 + j, by omega⟩ := by
      intro j
      change νs j.succ = _
      rw [hν j.succ]
      exact congrArg ρs (Fin.ext (by simp only [Fin.val_succ]; omega))
    rw [akLadderF, realize_polForm, realize_akRoundF ρs _ prev hprev,
      ih (i + 1) (by omega) (some ⟨i, hik⟩) rfl (fun l => νs l.succ) hstep]
    rw [show (atmData k A).runMatrix start (m + 1) i (prev.map ρs) νs =
        polConn (blockPol start i) (RunFun (νs 0) ∧ (atmData k A).RunGuard i (prev.map ρs) (νs 0))
          ((atmData k A).runMatrix start m (i + 1) (some (νs 0)) fun l => νs l.succ) from rfl,
      h0]
    exact Iff.rfl

theorem realize_akKernel (start : Bool) :
    (@Sentence.Realize (akLang k) A (akStructure ρs) (akKernel start k)) ↔
      (atmData k A).toTMData.WellFormed ∧ (atmData k A).BlocksWellFormed k ∧
        (∃ q, (atmData k A).Start q) ∧ (atmData k A).runMatrix start k 0 none ρs := by
  simp only [akKernel, realize_inf_sentence, realize_akWfClause, realize_akBwfClause,
    realize_akStartExClause]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  refine realize_akLadderF ρs start k 0 (by omega) none rfl ρs fun j => ?_
  exact congrArg ρs (Fin.ext (by simp))

end RealizeLadder

end DescriptiveComplexity
