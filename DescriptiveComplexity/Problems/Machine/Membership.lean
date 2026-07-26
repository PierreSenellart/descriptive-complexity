/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Walk
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.SecondOrder

/-!
# Machine acceptance is existential second-order definable

The membership half of the machine bridge: `NTMAccept` is `Σ₁`-definable, hence
in NP. This is Fagin's tableau argument, and – unlike the certificate of a
weighted problem – it needs no arithmetic at all: one existential block guesses
the run, and a first-order kernel checks it clause by clause.

## What is guessed

Three relation variables, indexed by the *positions*, which are simultaneously
the tape cells and the time steps:

* `Q t q` – at time `t` the machine is in state `q`;
* `H t p` – at time `t` the head is on the cell `p`;
* `T t p a` – at time `t` the cell `p` holds the symbol `a`.

That the guess is a run is exactly `DescriptiveComplexity.TMData.RelWalk`, and
`DescriptiveComplexity.TMData.exists_relWalk_iff_exists_walk` together with
`DescriptiveComplexity.TMData.accepts_iff_exists_walk` is what connects it back to
acceptance. So this file is a transcription: every clause below mirrors one
field of `RelWalk` or one conjunct of `DescriptiveComplexity.TMData.WellFormed`, and each
has its own realization lemma. Nothing here does mathematics; the mathematics is
in `DescriptiveComplexity.Problems.Machine.Walk`.

## Status

In progress. The block, the formula builders with their realization lemmas, and
the clauses transcribing the six functionality fields of `RelWalk` together with
its accepting clause are done. Still to write: the initial clause (which needs
`InitTape` as a formula), the step clause, the first-order transcription of
`WellFormed`, the kernel as their conjunction, and the two theorems
`ntmAccept_sigmaSODefinable` / `ntmAccept_mem_NP`.

## The order predicates

`MinPos`, `MaxPos` and `SuccPos` are relativized to the positions, so they are
not the ordered-structure guards of `DescriptiveComplexity.OrderWalk` but formulas over
the instance's own `le` and `posn` symbols, defined here as
`DescriptiveComplexity.tqMinPosF` and friends.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

/-! ### The block -/

/-- The relation variables of the certificate: the state, the head and the tape
of the configuration at each time. -/
inductive TMIdx : Type
  /-- The state at a time. -/
  | state
  /-- The head cell at a time. -/
  | head
  /-- The tape contents at a time. -/
  | tape
  deriving DecidableEq

instance : Fintype TMIdx where
  elems := {TMIdx.state, TMIdx.head, TMIdx.tape}
  complete := fun i => by cases i <;> decide

/-- The single existential block: the run, guessed as a state, a head position
and a tape contents for each time. -/
def tmGuessBlock : SOBlock where
  ι := TMIdx
  arity := fun i => match i with
    | .state => 2
    | .head => 2
    | .tape => 3

/-- The symbol of the state relation variable. -/
def tqStateRel : tmGuessBlock.lang.Relations 2 := ⟨.state, rfl⟩

/-- The symbol of the head relation variable. -/
def tqHeadRel : tmGuessBlock.lang.Relations 2 := ⟨.head, rfl⟩

/-- The symbol of the tape relation variable. -/
def tqTapeRel : tmGuessBlock.lang.Relations 3 := ⟨.tape, rfl⟩

/-- The vocabulary of the kernel: machine instances together with the guessed
run. -/
abbrev tqSOLang : Language := Language.turing.sum tmGuessBlock.lang

/-- The position symbol in the kernel's vocabulary. -/
abbrev tqPosnSym : tqSOLang.Relations 1 := Sum.inl tmPosn

/-- The transition symbol in the kernel's vocabulary. -/
abbrev tqTrSym : tqSOLang.Relations 1 := Sum.inl tmTr

/-- The start-state symbol in the kernel's vocabulary. -/
abbrev tqStartSym : tqSOLang.Relations 1 := Sum.inl tmStart

/-- The accepting-state symbol in the kernel's vocabulary. -/
abbrev tqAccSym : tqSOLang.Relations 1 := Sum.inl tmAcc

/-- The blank symbol in the kernel's vocabulary. -/
abbrev tqBlankSym : tqSOLang.Relations 1 := Sum.inl tmBlank

/-- The move-right symbol in the kernel's vocabulary. -/
abbrev tqRightSym : tqSOLang.Relations 1 := Sum.inl tmRight

/-- The order symbol in the kernel's vocabulary. -/
abbrev tqLeSym : tqSOLang.Relations 2 := Sum.inl tmLe

/-- The transition-source symbol in the kernel's vocabulary. -/
abbrev tqSrcSym : tqSOLang.Relations 2 := Sum.inl tmSrc

/-- The transition-read symbol in the kernel's vocabulary. -/
abbrev tqReadSym : tqSOLang.Relations 2 := Sum.inl tmRead

/-- The transition-destination symbol in the kernel's vocabulary. -/
abbrev tqDstSym : tqSOLang.Relations 2 := Sum.inl tmDst

/-- The transition-write symbol in the kernel's vocabulary. -/
abbrev tqWriteSym : tqSOLang.Relations 2 := Sum.inl tmWrite

/-- The input symbol in the kernel's vocabulary. -/
abbrev tqInpSym : tqSOLang.Relations 2 := Sum.inl tmInp

/-- The guessed-state symbol in the kernel's vocabulary. -/
abbrev tqStateSym : tqSOLang.Relations 2 := Sum.inr tqStateRel

/-- The guessed-head symbol in the kernel's vocabulary. -/
abbrev tqHeadSym : tqSOLang.Relations 2 := Sum.inr tqHeadRel

/-- The guessed-tape symbol in the kernel's vocabulary. -/
abbrev tqTapeSym : tqSOLang.Relations 3 := Sum.inr tqTapeRel

/-! ### Formula builders -/

section Builders

variable {α : Type}

/-- `x` is a position, as a formula. -/
def tqPosnF (x : α) : tqSOLang.Formula α := Relations.formula₁ tqPosnSym (Term.var x)

/-- `x` is a transition, as a formula. -/
def tqTrF (x : α) : tqSOLang.Formula α := Relations.formula₁ tqTrSym (Term.var x)

/-- `x` is a start state, as a formula. -/
def tqStartF (x : α) : tqSOLang.Formula α := Relations.formula₁ tqStartSym (Term.var x)

/-- `x` is an accepting state, as a formula. -/
def tqAccF (x : α) : tqSOLang.Formula α := Relations.formula₁ tqAccSym (Term.var x)

/-- `x` is the blank symbol, as a formula. -/
def tqBlankF (x : α) : tqSOLang.Formula α := Relations.formula₁ tqBlankSym (Term.var x)

/-- `x` moves the head right, as a formula. -/
def tqRightF (x : α) : tqSOLang.Formula α := Relations.formula₁ tqRightSym (Term.var x)

/-- `x ≤ y`, as a formula. -/
def tqLeF (x y : α) : tqSOLang.Formula α :=
  Relations.formula₂ tqLeSym (Term.var x) (Term.var y)

/-- `x = y`, as a formula. -/
def tqEqF (x y : α) : tqSOLang.Formula α := Term.equal (Term.var x) (Term.var y)

/-- The transition `x` applies in the state `y`, as a formula. -/
def tqSrcF (x y : α) : tqSOLang.Formula α :=
  Relations.formula₂ tqSrcSym (Term.var x) (Term.var y)

/-- The transition `x` reads the symbol `y`, as a formula. -/
def tqReadF (x y : α) : tqSOLang.Formula α :=
  Relations.formula₂ tqReadSym (Term.var x) (Term.var y)

/-- The transition `x` moves to the state `y`, as a formula. -/
def tqDstF (x y : α) : tqSOLang.Formula α :=
  Relations.formula₂ tqDstSym (Term.var x) (Term.var y)

/-- The transition `x` writes the symbol `y`, as a formula. -/
def tqWriteF (x y : α) : tqSOLang.Formula α :=
  Relations.formula₂ tqWriteSym (Term.var x) (Term.var y)

/-- The cell `x` initially holds `y`, as a formula. -/
def tqInpF (x y : α) : tqSOLang.Formula α :=
  Relations.formula₂ tqInpSym (Term.var x) (Term.var y)

/-- The state at time `x` is `y`, as a formula. -/
def tqStateF (x y : α) : tqSOLang.Formula α :=
  Relations.formula₂ tqStateSym (Term.var x) (Term.var y)

/-- The head at time `x` is on `y`, as a formula. -/
def tqHeadF (x y : α) : tqSOLang.Formula α :=
  Relations.formula₂ tqHeadSym (Term.var x) (Term.var y)

/-- At time `x` the cell `y` holds `z`, as a formula. -/
def tqTapeF (x y z : α) : tqSOLang.Formula α :=
  tqTapeSym.formula ![Term.var x, Term.var y, Term.var z]

/-- `x` is the lowest position, as a formula. -/
noncomputable def tqMinPosF (x : α) : tqSOLang.Formula α :=
  tqPosnF x ⊓ Formula.iAlls (Fin 1)
    ((tqPosnF (Sum.inr 0)).imp (tqLeF (Sum.inl x) (Sum.inr 0)))

/-- `x` is the highest position, as a formula. -/
noncomputable def tqMaxPosF (x : α) : tqSOLang.Formula α :=
  tqPosnF x ⊓ Formula.iAlls (Fin 1)
    ((tqPosnF (Sum.inr 0)).imp (tqLeF (Sum.inr 0) (Sum.inl x)))

/-- `y` is the position immediately above `x`, as a formula. -/
noncomputable def tqSuccPosF (x y : α) : tqSOLang.Formula α :=
  tqPosnF x ⊓ (tqPosnF y ⊓ (tqLeF x y ⊓ (∼(tqEqF x y) ⊓
    Formula.iAlls (Fin 1)
      ((tqPosnF (Sum.inr 0) ⊓ (tqLeF (Sum.inl x) (Sum.inr 0) ⊓
          tqLeF (Sum.inr 0) (Sum.inl y))).imp
        (tqEqF (Sum.inr 0) (Sum.inl x) ⊔ tqEqF (Sum.inr 0) (Sum.inl y))))))

end Builders

/-! ### Realization of the builders -/

section Realize

variable {A : Type} [Language.turing.Structure A] (ρ : tmGuessBlock.Assignment A)

/-- The structure the kernel is read in: the instance expanded by the guess. -/
local notation "SOStruc" => @sumStructure Language.turing tmGuessBlock.lang A _
  (tmGuessBlock.structure ρ)

variable {α : Type} (v : α → A)

@[simp] theorem realize_tqPosnF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqPosnF x) v) ↔ TMPosn (v x) := by
  letI := tmGuessBlock.structure ρ
  simp [tqPosnF, TMPosn, Language.relMap_sumInl]

@[simp] theorem realize_tqTrF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqTrF x) v) ↔ TMTr (v x) := by
  letI := tmGuessBlock.structure ρ
  simp [tqTrF, TMTr, Language.relMap_sumInl]

@[simp] theorem realize_tqStartF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqStartF x) v) ↔ TMStart (v x) := by
  letI := tmGuessBlock.structure ρ
  simp [tqStartF, TMStart, Language.relMap_sumInl]

@[simp] theorem realize_tqAccF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqAccF x) v) ↔ TMAcc (v x) := by
  letI := tmGuessBlock.structure ρ
  simp [tqAccF, TMAcc, Language.relMap_sumInl]

@[simp] theorem realize_tqBlankF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqBlankF x) v) ↔ TMBlank (v x) := by
  letI := tmGuessBlock.structure ρ
  simp [tqBlankF, TMBlank, Language.relMap_sumInl]

@[simp] theorem realize_tqRightF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqRightF x) v) ↔ TMRight (v x) := by
  letI := tmGuessBlock.structure ρ
  simp [tqRightF, TMRight, Language.relMap_sumInl]

@[simp] theorem realize_tqLeF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqLeF x y) v) ↔ TMLe (v x) (v y) := by
  letI := tmGuessBlock.structure ρ
  simp [tqLeF, TMLe, Language.relMap_sumInl]

@[simp] theorem realize_tqEqF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqEqF x y) v) ↔ v x = v y := by
  letI := tmGuessBlock.structure ρ
  simp [tqEqF]

@[simp] theorem realize_tqSrcF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqSrcF x y) v) ↔ TMSrc (v x) (v y) := by
  letI := tmGuessBlock.structure ρ
  simp [tqSrcF, TMSrc, Language.relMap_sumInl]

@[simp] theorem realize_tqReadF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqReadF x y) v) ↔ TMRead (v x) (v y) := by
  letI := tmGuessBlock.structure ρ
  simp [tqReadF, TMRead, Language.relMap_sumInl]

@[simp] theorem realize_tqDstF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqDstF x y) v) ↔ TMDst (v x) (v y) := by
  letI := tmGuessBlock.structure ρ
  simp [tqDstF, TMDst, Language.relMap_sumInl]

@[simp] theorem realize_tqWriteF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqWriteF x y) v) ↔ TMWrite (v x) (v y) := by
  letI := tmGuessBlock.structure ρ
  simp [tqWriteF, TMWrite, Language.relMap_sumInl]

@[simp] theorem realize_tqInpF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqInpF x y) v) ↔ TMInp (v x) (v y) := by
  letI := tmGuessBlock.structure ρ
  simp [tqInpF, TMInp, Language.relMap_sumInl]

@[simp] theorem realize_tqStateF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqStateF x y) v) ↔ ρ .state ![v x, v y] := by
  letI := tmGuessBlock.structure ρ
  simp only [tqStateF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_tqHeadF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqHeadF x y) v) ↔ ρ .head ![v x, v y] := by
  letI := tmGuessBlock.structure ρ
  simp only [tqHeadF, Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem realize_tqTapeF (x y z : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqTapeF x y z) v) ↔
      ρ .tape ![v x, v y, v z] := by
  letI := tmGuessBlock.structure ρ
  simp only [tqTapeF, Formula.realize_rel, Language.relMap_sumInr]
  exact iff_of_eq (congrArg (ρ TMIdx.tape) (funext fun i => by fin_cases i <;> rfl))

@[simp] theorem realize_tqMinPosF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqMinPosF x) v) ↔
      MinPos TMLe TMPosn (v x) := by
  letI := tmGuessBlock.structure ρ
  simp only [tqMinPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_tqPosnF, realize_tqLeF, Sum.elim_inl, Sum.elim_inr, MinPos]
  exact and_congr Iff.rfl ⟨fun h a => h (fun _ => a), fun h i => h (i 0)⟩

@[simp] theorem realize_tqMaxPosF (x : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqMaxPosF x) v) ↔
      MaxPos TMLe TMPosn (v x) := by
  letI := tmGuessBlock.structure ρ
  simp only [tqMaxPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_tqPosnF, realize_tqLeF, Sum.elim_inl, Sum.elim_inr, MaxPos]
  exact and_congr Iff.rfl ⟨fun h a => h (fun _ => a), fun h i => h (i 0)⟩

@[simp] theorem realize_tqSuccPosF (x y : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqSuccPosF x y) v) ↔
      SuccPos TMLe TMPosn (v x) (v y) := by
  letI := tmGuessBlock.structure ρ
  simp only [tqSuccPosF, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_sup, realize_tqPosnF, realize_tqLeF, realize_tqEqF,
    Sum.elim_inl, Sum.elim_inr, SuccPos, ne_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  exact ⟨fun h a ha h₁ h₂ => h (fun _ => a) ⟨ha, h₁, h₂⟩,
    fun h i hi => h (i 0) hi.1 hi.2.1 hi.2.2⟩

end Realize

/-! ### The clauses of the kernel

Each mirrors one field of `DescriptiveComplexity.TMData.RelWalk`. -/

section Clauses

/-- There is a state at each time. -/
noncomputable def tqStateExClause : tqSOLang.Sentence :=
  Formula.iAlls (Fin 1) (Formula.iExs (Fin 1) (tqStateF (Sum.inl (Sum.inr 0)) (Sum.inr 0)))

/-- There is only one state at each time. -/
noncomputable def tqStateUniqClause : tqSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((tqStateF (Sum.inr 0) (Sum.inr 1) ⊓ tqStateF (Sum.inr 0) (Sum.inr 2)).imp
      (tqEqF (Sum.inr 1) (Sum.inr 2)))

/-- The head is somewhere at each time. -/
noncomputable def tqHeadExClause : tqSOLang.Sentence :=
  Formula.iAlls (Fin 1) (Formula.iExs (Fin 1) (tqHeadF (Sum.inl (Sum.inr 0)) (Sum.inr 0)))

/-- The head is in only one place at each time. -/
noncomputable def tqHeadUniqClause : tqSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((tqHeadF (Sum.inr 0) (Sum.inr 1) ⊓ tqHeadF (Sum.inr 0) (Sum.inr 2)).imp
      (tqEqF (Sum.inr 1) (Sum.inr 2)))

/-- Every cell holds a symbol at each time. -/
noncomputable def tqTapeExClause : tqSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    (Formula.iExs (Fin 1)
      (tqTapeF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1)) (Sum.inr 0)))

/-- Every cell holds only one symbol at each time. -/
noncomputable def tqTapeUniqClause : tqSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((tqTapeF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓
        tqTapeF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3)).imp
      (tqEqF (Sum.inr 2) (Sum.inr 3)))

/-- At the highest time the state is accepting. -/
noncomputable def tqAccClause : tqSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    (((tqMaxPosF (Sum.inr 0)) ⊓ tqStateF (Sum.inr 0) (Sum.inr 1)).imp (tqAccF (Sum.inr 1)))

end Clauses

section RealizeClauses

variable {A : Type} [Language.turing.Structure A] (ρ : tmGuessBlock.Assignment A)

local notation "SOStruc" => @sumStructure Language.turing tmGuessBlock.lang A _
  (tmGuessBlock.structure ρ)

theorem realize_tqStateExClause :
    (@Sentence.Realize tqSOLang A SOStruc tqStateExClause) ↔
      ∀ t, ∃ q, ρ .state ![t, q] := by
  simp only [tqStateExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_tqStateF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h t
    obtain ⟨i, hi⟩ := h fun _ => t
    exact ⟨i 0, by simpa using hi⟩
  · intro h i
    obtain ⟨q, hq⟩ := h (i 0)
    exact ⟨fun _ => q, by simpa using hq⟩

theorem realize_tqStateUniqClause :
    (@Sentence.Realize tqSOLang A SOStruc tqStateUniqClause) ↔
      ∀ t q q', ρ .state ![t, q] → ρ .state ![t, q'] → q = q' := by
  simp only [tqStateUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqStateF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h t q q' h₁ h₂ => h ![t, q, q'] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

theorem realize_tqHeadExClause :
    (@Sentence.Realize tqSOLang A SOStruc tqHeadExClause) ↔
      ∀ t, ∃ p, ρ .head ![t, p] := by
  simp only [tqHeadExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_tqHeadF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h t
    obtain ⟨i, hi⟩ := h fun _ => t
    exact ⟨i 0, by simpa using hi⟩
  · intro h i
    obtain ⟨q, hq⟩ := h (i 0)
    exact ⟨fun _ => q, by simpa using hq⟩

theorem realize_tqHeadUniqClause :
    (@Sentence.Realize tqSOLang A SOStruc tqHeadUniqClause) ↔
      ∀ t p p', ρ .head ![t, p] → ρ .head ![t, p'] → p = p' := by
  simp only [tqHeadUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqHeadF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h t p p' h₁ h₂ => h ![t, p, p'] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

theorem realize_tqTapeExClause :
    (@Sentence.Realize tqSOLang A SOStruc tqTapeExClause) ↔
      ∀ t p, ∃ a, ρ .tape ![t, p, a] := by
  simp only [tqTapeExClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    realize_tqTapeF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h t p
    obtain ⟨i, hi⟩ := h ![t, p]
    exact ⟨i 0, by simpa using hi⟩
  · intro h i
    obtain ⟨a, ha⟩ := h (i 0) (i 1)
    exact ⟨fun _ => a, by simpa using ha⟩

theorem realize_tqTapeUniqClause :
    (@Sentence.Realize tqSOLang A SOStruc tqTapeUniqClause) ↔
      ∀ t p a a', ρ .tape ![t, p, a] → ρ .tape ![t, p, a'] → a = a' := by
  simp only [tqTapeUniqClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqTapeF, realize_tqEqF, Sum.elim_inr]
  exact ⟨fun h t p a a' h₁ h₂ => h ![t, p, a, a'] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) (i 3) hi.1 hi.2⟩

theorem realize_tqAccClause :
    (@Sentence.Realize tqSOLang A SOStruc tqAccClause) ↔
      ∀ t, MaxPos TMLe TMPosn t → ∀ q, ρ .state ![t, q] → TMAcc q := by
  simp only [tqAccClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqMaxPosF, realize_tqStateF, realize_tqAccF, Sum.elim_inr]
  exact ⟨fun h t ht q hq => h ![t, q] ⟨ht, hq⟩,
    fun h i hi => h (i 0) hi.1 (i 1) hi.2⟩

end RealizeClauses

end DescriptiveComplexity
