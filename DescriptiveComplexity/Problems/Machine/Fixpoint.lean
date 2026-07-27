/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.Problems.Machine.Walk
import DescriptiveComplexity.Problems.Machine.Program
import DescriptiveComplexity.FixedPoint
import DescriptiveComplexity.FixedPointHorn

/-!
# Deterministic machine acceptance is in PTIME

Stage 2b of the machine bridge: a *deterministic* run is exactly
a least fixed point, so `DescriptiveComplexity.DTMAccept` is FO(LFP) definable –
`DescriptiveComplexity.dtmAccept_lfpDefinable` – and hence, through the formalized
translation `DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`, SO-Horn
definable, that is, in PTIME (`DescriptiveComplexity.dtmAccept_mem_PTIME`).

## The fixed point

Three relation variables, indexed by the *time positions* of the run exactly as
in the `Σ₁` membership proof of `NTMAccept`: `Q t q` (the state at time `t`),
`H t p` (the head cell) and `T t p a` (the tape). The rules are the step
relation read as an inductive definition:

* at the lowest position, the state is a start state, the head is on the
  lowest position, and the tape is the input (`DescriptiveComplexity.TMData.InitTape`);
* along each `SuccPos t t'`, a transition applicable in the current state to
  the symbol under the head – *and able to fire*: a destination, a written
  symbol and a neighbour in its direction must exist, else the machine halts
  and nothing is derived at `t'` – advances the state, moves the head, writes
  its symbol, and leaves every other cell unchanged.

All the conditions are first-order over the input vocabulary, so they sit in
the *guards* of the Horn clauses; the body atoms are the three variables read
at time `t`, at most four per rule.

The output sentence is where FO(LFP) earns its keep over bare SO-Horn: it
states positively that an accepting state occurs in the fixed point – a thing
no goal clause can say – conjoined with the first-order promises
(`DescriptiveComplexity.TMData.WellFormed`, `DescriptiveComplexity.TMData.Deterministic`)
that `DTMAccept` folds into its yes-instances.

## Why determinism is what makes this correct

The fixed point derives everything *any* run does. For a deterministic machine
the run from the (unique) initial configuration is unique
(`DescriptiveComplexity.TMData.stepsIn_functional`), so the derived atoms describe it
and nothing else: soundness (`DescriptiveComplexity.DTFix.derives_sound`) is an
induction on derivations, completeness
(`DescriptiveComplexity.DTFix.derivedAt_of_run`) an induction along the rank of the
time position, and together they make the output read exactly “the machine
accepts within its budget”.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace DTFix

open Language Structure

/-- The ordered expansion of the machine vocabulary. -/
abbrev tmOrd : Language := Language.turing.sum Language.order

/-! ### Guards over the machine vocabulary -/

section Guards

/-- The position symbol over the ordered expansion. -/
abbrev dPosnSym : tmOrd.Relations 1 := Sum.inl tmPosn

/-- The transition symbol over the ordered expansion. -/
abbrev dTrSym : tmOrd.Relations 1 := Sum.inl tmTr

/-- The start-state symbol over the ordered expansion. -/
abbrev dStartSym : tmOrd.Relations 1 := Sum.inl tmStart

/-- The accepting-state symbol over the ordered expansion. -/
abbrev dAccSym : tmOrd.Relations 1 := Sum.inl tmAcc

/-- The blank symbol over the ordered expansion. -/
abbrev dBlankSym : tmOrd.Relations 1 := Sum.inl tmBlank

/-- The move-right symbol over the ordered expansion. -/
abbrev dRightSym : tmOrd.Relations 1 := Sum.inl tmRight

/-- The machine's own order symbol over the ordered expansion. -/
abbrev dLeSym : tmOrd.Relations 2 := Sum.inl tmLe

/-- The transition-source symbol over the ordered expansion. -/
abbrev dSrcSym : tmOrd.Relations 2 := Sum.inl tmSrc

/-- The transition-read symbol over the ordered expansion. -/
abbrev dReadSym : tmOrd.Relations 2 := Sum.inl tmRead

/-- The transition-destination symbol over the ordered expansion. -/
abbrev dDstSym : tmOrd.Relations 2 := Sum.inl tmDst

/-- The transition-write symbol over the ordered expansion. -/
abbrev dWriteSym : tmOrd.Relations 2 := Sum.inl tmWrite

/-- The input symbol over the ordered expansion. -/
abbrev dInpSym : tmOrd.Relations 2 := Sum.inl tmInp

variable {α : Type}

/-- `x` is a position, as a guard. -/
noncomputable def posnG (x : α) : tmOrd.Formula α :=
  Relations.formula₁ dPosnSym (Term.var x)

/-- `x` is a transition, as a guard. -/
noncomputable def trG (x : α) : tmOrd.Formula α :=
  Relations.formula₁ dTrSym (Term.var x)

/-- `x` is a start state, as a guard. -/
noncomputable def startG (x : α) : tmOrd.Formula α :=
  Relations.formula₁ dStartSym (Term.var x)

/-- `x` is an accepting state, as a guard. -/
noncomputable def accG (x : α) : tmOrd.Formula α :=
  Relations.formula₁ dAccSym (Term.var x)

/-- `x` is the blank symbol, as a guard. -/
noncomputable def blankG (x : α) : tmOrd.Formula α :=
  Relations.formula₁ dBlankSym (Term.var x)

/-- The transition `x` moves the head right, as a guard. -/
noncomputable def rightG (x : α) : tmOrd.Formula α :=
  Relations.formula₁ dRightSym (Term.var x)

/-- `x ≤ y` in the machine's own order, as a guard. -/
noncomputable def leG (x y : α) : tmOrd.Formula α :=
  Relations.formula₂ dLeSym (Term.var x) (Term.var y)

/-- The transition `x` applies in the state `y`, as a guard. -/
noncomputable def srcG (x y : α) : tmOrd.Formula α :=
  Relations.formula₂ dSrcSym (Term.var x) (Term.var y)

/-- The transition `x` reads the symbol `y`, as a guard. -/
noncomputable def readG (x y : α) : tmOrd.Formula α :=
  Relations.formula₂ dReadSym (Term.var x) (Term.var y)

/-- The transition `x` moves to the state `y`, as a guard. -/
noncomputable def dstG (x y : α) : tmOrd.Formula α :=
  Relations.formula₂ dDstSym (Term.var x) (Term.var y)

/-- The transition `x` writes the symbol `y`, as a guard. -/
noncomputable def writeG (x y : α) : tmOrd.Formula α :=
  Relations.formula₂ dWriteSym (Term.var x) (Term.var y)

/-- The cell `x` initially holds the symbol `y`, as a guard. -/
noncomputable def inpG (x y : α) : tmOrd.Formula α :=
  Relations.formula₂ dInpSym (Term.var x) (Term.var y)

/-- `x = y`, as a guard. -/
noncomputable def eqG (x y : α) : tmOrd.Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- `x ≠ y`, as a guard. -/
noncomputable def neG (x y : α) : tmOrd.Formula α :=
  ∼(eqG x y)

/-- `x` is the lowest position, as a guard. -/
noncomputable def minPosG (x : α) : tmOrd.Formula α :=
  posnG x ⊓ Formula.iAlls (Fin 1)
    (posnG (Sum.inr 0) ⟹ leG (Sum.inl x) (Sum.inr 0))

/-- `y` is the position immediately above `x`, as a guard. -/
noncomputable def succPosG (x y : α) : tmOrd.Formula α :=
  posnG x ⊓ posnG y ⊓ leG x y ⊓ neG x y ⊓
    Formula.iAlls (Fin 1)
      ((posnG (Sum.inr 0) ⊓ leG (Sum.inl x) (Sum.inr 0) ⊓ leG (Sum.inr 0) (Sum.inl y)) ⟹
        (eqG (Sum.inr 0) (Sum.inl x) ⊔ eqG (Sum.inr 0) (Sum.inl y)))

/-- The cell `x` initially holds the symbol `y`: the input where defined, the
blank elsewhere. -/
noncomputable def initTapeG (x y : α) : tmOrd.Formula α :=
  inpG x y ⊔ (Formula.iAlls (Fin 1) (∼(inpG (Sum.inl x) (Sum.inr 0))) ⊓ blankG y)

/-- The transition `x` has a destination, as a guard. -/
noncomputable def existsDstG (x : α) : tmOrd.Formula α :=
  Formula.iExs (Fin 1) (dstG (Sum.inl x) (Sum.inr 0))

/-- The transition `x` has a written symbol, as a guard. -/
noncomputable def existsWriteG (x : α) : tmOrd.Formula α :=
  Formula.iExs (Fin 1) (writeG (Sum.inl x) (Sum.inr 0))

/-- The transition `x`, with the head at `h`, can move: there is a neighbour
in its direction. Without this in every step rule the fixed point would run
past a halt. -/
noncomputable def canMoveG (x h : α) : tmOrd.Formula α :=
  (rightG x ⊓ Formula.iExs (Fin 1) (succPosG (Sum.inl h) (Sum.inr 0))) ⊔
    (∼(rightG x) ⊓ Formula.iExs (Fin 1) (succPosG (Sum.inr 0) (Sum.inl h)))

end Guards

/-! ### Realization of the guards -/

section GuardRealize

variable {A : Type} [Language.turing.Structure A] [LinearOrder A] {α : Type} {v : α → A}

@[simp]
theorem realize_posnG (x : α) : (posnG x).Realize v ↔ TMPosn (v x) := by
  rw [posnG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_trG (x : α) : (trG x).Realize v ↔ TMTr (v x) := by
  rw [trG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_startG (x : α) : (startG x).Realize v ↔ TMStart (v x) := by
  rw [startG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_accG (x : α) : (accG x).Realize v ↔ TMAcc (v x) := by
  rw [accG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_blankG (x : α) : (blankG x).Realize v ↔ TMBlank (v x) := by
  rw [blankG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_rightG (x : α) : (rightG x).Realize v ↔ TMRight (v x) := by
  rw [rightG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_leG (x y : α) : (leG x y).Realize v ↔ TMLe (v x) (v y) := by
  rw [leG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_srcG (x y : α) : (srcG x y).Realize v ↔ TMSrc (v x) (v y) := by
  rw [srcG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_readG (x y : α) : (readG x y).Realize v ↔ TMRead (v x) (v y) := by
  rw [readG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_dstG (x y : α) : (dstG x y).Realize v ↔ TMDst (v x) (v y) := by
  rw [dstG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_writeG (x y : α) : (writeG x y).Realize v ↔ TMWrite (v x) (v y) := by
  rw [writeG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_inpG (x y : α) : (inpG x y).Realize v ↔ TMInp (v x) (v y) := by
  rw [inpG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_eqG (x y : α) : (eqG x y).Realize v ↔ v x = v y := by
  simp [eqG]

@[simp]
theorem realize_neG (x y : α) : (neG x y).Realize v ↔ v x ≠ v y := by
  simp [neG]

@[simp]
theorem realize_minPosG (x : α) :
    (minPosG x).Realize v ↔ MinPos TMLe TMPosn (v x) := by
  simp only [minPosG, Formula.realize_inf, realize_posnG, Formula.realize_iAlls,
    Formula.realize_imp, realize_posnG, realize_leG, Sum.elim_inl, Sum.elim_inr, MinPos]
  exact and_congr Iff.rfl ⟨fun h q hq => h (fun _ => q) hq, fun h i hi => h (i 0) hi⟩

@[simp]
theorem realize_succPosG (x y : α) :
    (succPosG x y).Realize v ↔ SuccPos TMLe TMPosn (v x) (v y) := by
  simp only [succPosG, Formula.realize_inf, realize_posnG, realize_leG, realize_neG,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_sup, realize_eqG,
    Sum.elim_inl, Sum.elim_inr, SuccPos]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨h1, h2, h3, h4, fun r hr hxr hry => ?_⟩
    rcases h5 (fun _ => r) ⟨⟨hr, hxr⟩, hry⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, fun i hi =>
      h5 (i 0) hi.1.1 hi.1.2 hi.2⟩

@[simp]
theorem realize_initTapeG (x y : α) :
    (initTapeG x y).Realize v ↔ (tmData A).InitTape (v x) (v y) := by
  simp only [initTapeG, Formula.realize_sup, Formula.realize_inf, realize_inpG,
    Formula.realize_iAlls, Formula.realize_not, realize_blankG, Sum.elim_inl, Sum.elim_inr,
    TMData.InitTape]
  refine or_congr Iff.rfl (and_congr ⟨fun h b hb => h (fun _ => b) hb, fun h i hi => ?_⟩
    Iff.rfl)
  exact h (i 0) hi

@[simp]
theorem realize_existsDstG (x : α) :
    (existsDstG x).Realize v ↔ ∃ q : A, TMDst (v x) q := by
  simp only [existsDstG, Formula.realize_iExs, realize_dstG, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩

@[simp]
theorem realize_existsWriteG (x : α) :
    (existsWriteG x).Realize v ↔ ∃ a : A, TMWrite (v x) a := by
  simp only [existsWriteG, Formula.realize_iExs, realize_writeG, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, ha⟩⟩

@[simp]
theorem realize_canMoveG (x h : α) :
    (canMoveG x h).Realize v ↔
      ((TMRight (v x) ∧ ∃ p : A, SuccPos TMLe TMPosn (v h) p) ∨
        (¬ TMRight (v x) ∧ ∃ p : A, SuccPos TMLe TMPosn p (v h))) := by
  simp only [canMoveG, Formula.realize_sup, Formula.realize_inf, realize_rightG,
    Formula.realize_not, Formula.realize_iExs, realize_succPosG, Sum.elim_inl, Sum.elim_inr]
  refine or_congr (and_congr Iff.rfl ?_) (and_congr Iff.rfl ?_) <;>
    exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩

end GuardRealize

/-! ### The promises, as sentences -/

section Promises

/-- Reflexivity of the machine's order. -/
noncomputable def linReflS : tmOrd.Sentence :=
  Formula.iAlls (Fin 1) (leG (Sum.inr 0) (Sum.inr 0))

/-- Transitivity of the machine's order. -/
noncomputable def linTransS : tmOrd.Sentence :=
  Formula.iAlls (Fin 3)
    ((leG (Sum.inr 0) (Sum.inr 1) ⊓ leG (Sum.inr 1) (Sum.inr 2)) ⟹
      leG (Sum.inr 0) (Sum.inr 2))

/-- Antisymmetry of the machine's order. -/
noncomputable def linAntisymmS : tmOrd.Sentence :=
  Formula.iAlls (Fin 2)
    ((leG (Sum.inr 0) (Sum.inr 1) ⊓ leG (Sum.inr 1) (Sum.inr 0)) ⟹
      eqG (Sum.inr 0) (Sum.inr 1))

/-- Totality of the machine's order. -/
noncomputable def linTotalS : tmOrd.Sentence :=
  Formula.iAlls (Fin 2) (leG (Sum.inr 0) (Sum.inr 1) ⊔ leG (Sum.inr 1) (Sum.inr 0))

/-- There is a position. -/
noncomputable def exPosnS : tmOrd.Sentence :=
  Formula.iExs (Fin 1) (posnG (Sum.inr 0))

/-- The input is functional. -/
noncomputable def inpFunS : tmOrd.Sentence :=
  Formula.iAlls (Fin 3)
    ((inpG (Sum.inr 0) (Sum.inr 1) ⊓ inpG (Sum.inr 0) (Sum.inr 2)) ⟹
      eqG (Sum.inr 1) (Sum.inr 2))

/-- There is a blank symbol. -/
noncomputable def exBlankS : tmOrd.Sentence :=
  Formula.iExs (Fin 1) (blankG (Sum.inr 0))

/-- The blank symbol is unique. -/
noncomputable def blankUniqS : tmOrd.Sentence :=
  Formula.iAlls (Fin 2)
    ((blankG (Sum.inr 0) ⊓ blankG (Sum.inr 1)) ⟹ eqG (Sum.inr 0) (Sum.inr 1))

/-- The start state is unique. -/
noncomputable def startUniqS : tmOrd.Sentence :=
  Formula.iAlls (Fin 2)
    ((startG (Sum.inr 0) ⊓ startG (Sum.inr 1)) ⟹ eqG (Sum.inr 0) (Sum.inr 1))

/-- At most one transition applies in a given state on a given symbol. -/
noncomputable def trUniqS : tmOrd.Sentence :=
  Formula.iAlls (Fin 4)
    ((trG (Sum.inr 0) ⊓ trG (Sum.inr 1) ⊓ srcG (Sum.inr 0) (Sum.inr 2) ⊓
        srcG (Sum.inr 1) (Sum.inr 2) ⊓ readG (Sum.inr 0) (Sum.inr 3) ⊓
        readG (Sum.inr 1) (Sum.inr 3)) ⟹
      eqG (Sum.inr 0) (Sum.inr 1))

/-- The destination of a transition is unique. -/
noncomputable def dstFunS : tmOrd.Sentence :=
  Formula.iAlls (Fin 3)
    ((dstG (Sum.inr 0) (Sum.inr 1) ⊓ dstG (Sum.inr 0) (Sum.inr 2)) ⟹
      eqG (Sum.inr 1) (Sum.inr 2))

/-- The written symbol of a transition is unique. -/
noncomputable def writeFunS : tmOrd.Sentence :=
  Formula.iAlls (Fin 3)
    ((writeG (Sum.inr 0) (Sum.inr 1) ⊓ writeG (Sum.inr 0) (Sum.inr 2)) ⟹
      eqG (Sum.inr 1) (Sum.inr 2))

/-- Well-formedness, as a sentence. -/
noncomputable def wfS : tmOrd.Sentence :=
  listInf [linReflS, linTransS, linAntisymmS, linTotalS, exPosnS, inpFunS, exBlankS,
    blankUniqS]

/-- Determinism, as a sentence. -/
noncomputable def detS : tmOrd.Sentence :=
  listInf [startUniqS, trUniqS, dstFunS, writeFunS]

variable {A : Type} [Language.turing.Structure A] [LinearOrder A]

theorem realize_wfS : (A ⊨ wfS) ↔ (tmData A).WellFormed := by
  rw [wfS]
  simp only [Sentence.Realize, realize_listInf, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  rw [show ∀ p q r s t u v w : Prop, (p ∧ q ∧ r ∧ s ∧ t ∧ u ∧ v ∧ w) =
      ((p ∧ q ∧ r ∧ s) ∧ t ∧ u ∧ v ∧ w) from fun _ _ _ _ _ _ _ _ => by rw [and_assoc]; ac_rfl]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · -- IsLinOrd
    rw [IsLinOrd]
    refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
    · rw [linReflS]
      simp only [Formula.realize_iAlls, realize_leG, Sum.elim_inr]
      exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩
    · rw [linTransS]
      simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
        realize_leG, Sum.elim_inr]
      exact ⟨fun h a b c h1 h2 => h ![a, b, c] ⟨h1, h2⟩,
        fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩
    · rw [linAntisymmS]
      simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
        realize_leG, realize_eqG, Sum.elim_inr]
      exact ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩
    · rw [linTotalS]
      simp only [Formula.realize_iAlls, Formula.realize_sup, realize_leG, Sum.elim_inr]
      exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩
  · rw [exPosnS]
    simp only [Formula.realize_iExs, realize_posnG, Sum.elim_inr]
    exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩
  · rw [inpFunS]
    simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      realize_inpG, realize_eqG, Sum.elim_inr]
    exact ⟨fun h p a b h1 h2 => h ![p, a, b] ⟨h1, h2⟩,
      fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩
  · rw [exBlankS]
    simp only [Formula.realize_iExs, realize_blankG, Sum.elim_inr]
    exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩
  · rw [blankUniqS]
    simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      realize_blankG, realize_eqG, Sum.elim_inr]
    exact ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

theorem realize_detS : (A ⊨ detS) ↔ (tmData A).Deterministic := by
  rw [detS]
  simp only [Sentence.Realize, realize_listInf, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  rw [TMData.Deterministic]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · rw [startUniqS]
    simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      realize_startG, realize_eqG, Sum.elim_inr]
    exact ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩
  · rw [trUniqS]
    simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      realize_trG, realize_srcG, realize_readG, realize_eqG, Sum.elim_inr]
    exact ⟨fun h τ τ' q a h1 h2 h3 h4 h5 h6 =>
        h ![τ, τ', q, a] ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩,
      fun h i hi =>
        h (i 0) (i 1) (i 2) (i 3) hi.1.1.1.1.1 hi.1.1.1.1.2 hi.1.1.1.2 hi.1.1.2 hi.1.2 hi.2⟩
  · rw [dstFunS]
    simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      realize_dstG, realize_eqG, Sum.elim_inr]
    exact ⟨fun h τ a b h1 h2 => h ![τ, a, b] ⟨h1, h2⟩,
      fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩
  · rw [writeFunS]
    simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      realize_writeG, realize_eqG, Sum.elim_inr]
    exact ⟨fun h τ a b h1 h2 => h ![τ, a, b] ⟨h1, h2⟩,
      fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

end Promises

/-! ### The block and the rules -/

/-- The relation variables of the fixed point: the state `Q t q`, the head
`H t p` and the tape `T t p a` of the run, indexed by the time positions. -/
def dtBlock : SOBlock where
  ι := Option Bool
  arity := fun i => match i with
    | some true => 2
    | some false => 2
    | none => 3

/-- The atom `Q (xᵢ, xⱼ)`. -/
def qAt (i j : Fin 9) : SOAtom dtBlock 9 := ⟨some true, ![i, j]⟩

/-- The atom `H (xᵢ, xⱼ)`. -/
def hAt (i j : Fin 9) : SOAtom dtBlock 9 := ⟨some false, ![i, j]⟩

/-- The atom `T (xᵢ, xⱼ, xₗ)`. -/
def tAt (i j l : Fin 9) : SOAtom dtBlock 9 := ⟨none, ![i, j, l]⟩

/- Variable conventions of the rules, among the nine shared variables:
`0` = the time `t`, `1` = its successor `t'`, `2` = the transition `τ`,
`3` = the current state, `4` = the symbol read, `5` = what the rule writes or
moves to, `6` = the head, `7` = the new head or the frame cell, `8` = the
frame symbol. -/

/-- Initial state: at the lowest position, a start state. -/
noncomputable def dtCQInit : HornClause tmOrd dtBlock 9 :=
  { guard := minPosG 0 ⊓ startG 3, body := [], head := some (qAt 0 3) }

/-- Initial head: at the lowest position, on the lowest position – times and
cells being the same sort. -/
noncomputable def dtCHInit : HornClause tmOrd dtBlock 9 :=
  { guard := minPosG 0, body := [], head := some (hAt 0 0) }

/-- Initial tape: the input, with the blank elsewhere. -/
noncomputable def dtCTInit : HornClause tmOrd dtBlock 9 :=
  { guard := minPosG 0 ⊓ initTapeG 6 4, body := [], head := some (tAt 0 6 4) }

/-- The shared core of the step rules: consecutive times, an applicable
transition that can fire – a destination and a written symbol exist. -/
noncomputable def dtCoreG : tmOrd.Formula (Fin 9) :=
  succPosG 0 1 ⊓ trG 2 ⊓ srcG 2 3 ⊓ readG 2 4 ⊓ existsDstG 2 ⊓ existsWriteG 2

/-- The shared body of the step rules: the state, the head, and the symbol
under the head, at the current time. -/
noncomputable def dtBody : List (SOAtom dtBlock 9) := [qAt 0 3, hAt 0 6, tAt 0 6 4]

/-- Step, the state: the transition's destination. -/
noncomputable def dtCQStep : HornClause tmOrd dtBlock 9 :=
  { guard := dtCoreG ⊓ canMoveG 2 6 ⊓ dstG 2 5, body := dtBody, head := some (qAt 1 5) }

/-- Step, the head, moving right. -/
noncomputable def dtCHStepR : HornClause tmOrd dtBlock 9 :=
  { guard := dtCoreG ⊓ rightG 2 ⊓ succPosG 6 7, body := dtBody, head := some (hAt 1 7) }

/-- Step, the head, moving left. -/
noncomputable def dtCHStepL : HornClause tmOrd dtBlock 9 :=
  { guard := dtCoreG ⊓ ∼(rightG 2) ⊓ succPosG 7 6, body := dtBody, head := some (hAt 1 7) }

/-- Step, the written cell. -/
noncomputable def dtCWrite : HornClause tmOrd dtBlock 9 :=
  { guard := dtCoreG ⊓ canMoveG 2 6 ⊓ writeG 2 5, body := dtBody, head := some (tAt 1 6 5) }

/-- Step, the frame: every other cell is unchanged. -/
noncomputable def dtCFrame : HornClause tmOrd dtBlock 9 :=
  { guard := dtCoreG ⊓ canMoveG 2 6 ⊓ neG 7 6, body := dtBody ++ [tAt 0 7 8],
    head := some (tAt 1 7 8) }

/-- The rules of the fixed point: the step relation of the machine, read as an
inductive definition along the time positions. -/
noncomputable def dtRules : HornProgram tmOrd dtBlock 9 :=
  [dtCQInit, dtCHInit, dtCTInit, dtCQStep, dtCHStepR, dtCHStepL, dtCWrite, dtCFrame]

section CoreRealize

variable {A : Type} [Language.turing.Structure A] [LinearOrder A] {v : Fin 9 → A}

theorem realize_dtCoreG :
    (dtCoreG.Realize v) ↔
      (SuccPos TMLe TMPosn (v 0) (v 1) ∧ TMTr (v 2) ∧ TMSrc (v 2) (v 3) ∧
        TMRead (v 2) (v 4) ∧ (∃ q : A, TMDst (v 2) q) ∧ ∃ a : A, TMWrite (v 2) a) := by
  simp only [dtCoreG, Formula.realize_inf, realize_succPosG, realize_trG, realize_srcG,
    realize_readG, realize_existsDstG, realize_existsWriteG]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

end CoreRealize

/-! ### The output sentence -/

/-- The acceptance atom of the output, over two variables. -/
def dtAccAt : SOAtom dtBlock 2 := ⟨some true, ![0, 1]⟩

/-- The positive part of the output: some time carries an accepting state in
the fixed point – the statement no goal clause of a Horn program can make. -/
noncomputable def dtAccOut : (tmOrd.sum dtBlock.lang).Sentence :=
  Formula.iExs (Fin 2) (atomF dtAccAt ⊓ guardOutF (accG 1))

/-- The output sentence: the promises, and acceptance at the fixed point. -/
noncomputable def dtOut : (tmOrd.sum dtBlock.lang).Sentence :=
  LHom.sumInl.onSentence wfS ⊓ LHom.sumInl.onSentence detS ⊓ dtAccOut

section OutRealize

variable {A : Type} [Language.turing.Structure A] [LinearOrder A] (ρ : dtBlock.Assignment A)

omit [Language.turing.Structure A] [LinearOrder A] in
/-- Reading the acceptance atom off an assignment. -/
theorem dtAccAt_holds (w : Fin 2 → A) :
    dtAccAt.Holds ρ w ↔ ρ (some true) ![w 0, w 1] := by
  refine iff_of_eq (congrArg (ρ (some true)) (funext fun l => ?_))
  fin_cases l <;> rfl

theorem realize_dtAccOut :
    (@Sentence.Realize (tmOrd.sum dtBlock.lang) A
        (@sumStructure _ _ A _ (dtBlock.structure ρ)) dtAccOut) ↔
      ∃ t q : A, ρ (some true) ![t, q] ∧ TMAcc q := by
  letI := dtBlock.structure ρ
  rw [dtAccOut]
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_atomF, realize_guardOutF, realize_accG, Sum.elim_inr]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i 0, i 1, (dtAccAt_holds ρ _).mp h1, h2⟩
  · rintro ⟨t, q, h1, h2⟩
    exact ⟨![t, q], (dtAccAt_holds ρ ![t, q]).mpr h1, h2⟩

theorem realize_dtOut :
    (@Sentence.Realize (tmOrd.sum dtBlock.lang) A
        (@sumStructure _ _ A _ (dtBlock.structure ρ)) dtOut) ↔
      ((tmData A).WellFormed ∧ (tmData A).Deterministic ∧
        ∃ t q : A, ρ (some true) ![t, q] ∧ TMAcc q) := by
  letI := dtBlock.structure ρ
  rw [dtOut]
  simp only [Sentence.Realize, Formula.realize_inf]
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ (realize_dtAccOut ρ))
  · exact (LHom.sumInl.realize_onSentence A wfS).trans realize_wfS
  · exact (LHom.sumInl.realize_onSentence A detS).trans realize_detS

end OutRealize

/-! ### Correctness

Soundness – everything derived is true of the (unique) run – is one induction
on derivations; completeness – everything true of the run is derived – one
induction along the rank of the time position. Determinism enters exactly
where the plan said it would: a derived state atom carries *some* run to its
time, the head and tape atoms hold of *every* run to theirs, and uniqueness of
the run (`DescriptiveComplexity.TMData.stepsIn_functional`) is what lets the two
readings meet in the step cases. -/

section Correctness

variable {A : Type} [Language.turing.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The derived state atoms. -/
def DQ (t q : A) : Prop := Derives (A := A) dtRules ⟨some true, ![t, q]⟩

/-- The derived head atoms. -/
def DH (t p : A) : Prop := Derives (A := A) dtRules ⟨some false, ![t, p]⟩

/-- The derived tape atoms. -/
def DT (t p a : A) : Prop := Derives (A := A) dtRules ⟨none, ![t, p, a]⟩

omit [Finite A] [Nonempty A] in
theorem dq_iff {v : Fin 9 → A} {i j : Fin 9} :
    Derives (A := A) dtRules ⟨(qAt i j).idx, fun l => v ((qAt i j).args l)⟩ ↔
      DQ (v i) (v j) := by
  have heq : (⟨(qAt i j).idx, fun l => v ((qAt i j).args l)⟩ : BAtom dtBlock A) =
      ⟨some true, ![v i, v j]⟩ := by
    refine congrArg (Sigma.mk (some true)) (funext fun l => ?_)
    fin_cases l <;> rfl
  rw [heq]
  exact Iff.rfl

omit [Finite A] [Nonempty A] in
theorem dh_iff {v : Fin 9 → A} {i j : Fin 9} :
    Derives (A := A) dtRules ⟨(hAt i j).idx, fun l => v ((hAt i j).args l)⟩ ↔
      DH (v i) (v j) := by
  have heq : (⟨(hAt i j).idx, fun l => v ((hAt i j).args l)⟩ : BAtom dtBlock A) =
      ⟨some false, ![v i, v j]⟩ := by
    refine congrArg (Sigma.mk (some false)) (funext fun l => ?_)
    fin_cases l <;> rfl
  rw [heq]
  exact Iff.rfl

omit [Finite A] [Nonempty A] in
theorem dt_iff {v : Fin 9 → A} {i j l : Fin 9} :
    Derives (A := A) dtRules ⟨(tAt i j l).idx, fun m => v ((tAt i j l).args m)⟩ ↔
      DT (v i) (v j) (v l) := by
  have heq : (⟨(tAt i j l).idx, fun m => v ((tAt i j l).args m)⟩ : BAtom dtBlock A) =
      ⟨none, ![v i, v j, v l]⟩ := by
    refine congrArg (Sigma.mk none) (funext fun m => ?_)
    fin_cases m <;> rfl
  rw [heq]
  exact Iff.rfl

omit [LinearOrder A] [Nonempty A] in
/-- A position of rank `0` is the lowest. -/
theorem minPos_of_bitRank_eq_zero (hlin : IsLinOrd (TMLe (A := A))) {p : A} (hp : TMPosn p)
    (h : bitRank TMLe TMPosn p = 0) : MinPos TMLe TMPosn p := by
  refine ⟨hp, fun q hq => ?_⟩
  by_contra hcon
  have hqp : TMLe q p := (hlin.2.2.2 p q).resolve_left hcon
  have hne : q ≠ p := fun he => hcon (he ▸ hlin.1 p)
  have hpos : 0 < {r : A | TMPosn r ∧ TMLe r p ∧ r ≠ p}.ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨q, hq, hqp, hne⟩
  rw [bitRank] at h
  omega

omit [LinearOrder A] [Nonempty A] in
/-- Every rank below the position count is realized by a position: this is
where the run's `ℕ`-indexed clock is matched to the time positions. -/
theorem exists_pos_bitRank (hlin : IsLinOrd (TMLe (A := A))) :
    ∀ j : ℕ, j < Nat.card {p : A // TMPosn p} →
      ∃ t : A, TMPosn t ∧ bitRank TMLe TMPosn t = j := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hne : ∃ p : A, TMPosn p := by
      by_contra hcon
      push Not at hcon
      haveI : IsEmpty {p : A // TMPosn p} := ⟨fun x => hcon x.1 x.2⟩
      rw [Nat.card_of_isEmpty] at hj
      omega
    obtain ⟨t, ht⟩ := exists_minPos hlin hne
    exact ⟨t, ht.1, bitRank_eq_zero_of_minPos hlin ht⟩
  | succ j ih =>
    intro hj
    obtain ⟨t, ht, hrank⟩ := ih (by omega)
    have hnmax : ¬ MaxPos TMLe TMPosn t := by
      intro hmax
      have := bitRank_maxPos (Le := TMLe) hmax
      omega
    obtain ⟨t', ht'⟩ := TMData.exists_succPos' (M := tmData A) hlin ht hnmax
    have hsp : SuccPos TMLe TMPosn t t' := ht'
    exact ⟨t', hsp.2.1, by rw [bitRank_succPos hlin hsp, hrank]⟩

/-- The meaning of a state atom: some run reaches its time in that state. -/
def MeaningQ (w : Fin 2 → A) : Prop :=
  TMPosn (w 0) ∧ ∃ c₀ c : Config A, (tmData A).IsInit c₀ ∧
    (tmData A).StepsIn (bitRank TMLe TMPosn (w 0)) c₀ c ∧ c.state = w 1

/-- The meaning of a head atom: every run to its time has the head there. -/
def MeaningH (w : Fin 2 → A) : Prop :=
  TMPosn (w 0) ∧ ∀ c₀ c : Config A, (tmData A).IsInit c₀ →
    (tmData A).StepsIn (bitRank TMLe TMPosn (w 0)) c₀ c → c.head = w 1

/-- The meaning of a tape atom: every run to its time reads that symbol. -/
def MeaningT (w : Fin 3 → A) : Prop :=
  TMPosn (w 0) ∧ ∀ c₀ c : Config A, (tmData A).IsInit c₀ →
    (tmData A).StepsIn (bitRank TMLe TMPosn (w 0)) c₀ c → c.tape (w 1) = w 2

/-- What a derived atom says about the run: a state atom carries some run to
its time, a head or tape atom holds of every run to its time. The asymmetry is
deliberate – the head and tape rules alone cannot certify a run exists, and
the state rules can. -/
def Meaning : BAtom dtBlock A → Prop := fun x =>
  match x with
  | ⟨some true, w⟩ => MeaningQ w
  | ⟨some false, w⟩ => MeaningH w
  | ⟨none, w⟩ => MeaningT w

omit [Nonempty A] in
/-- **Soundness**: every derived atom is true of the run. Induction on
derivations, one case per rule; in the step cases the step the rule took is
compared with the run's own step through determinism. -/
theorem derives_sound (hwf : (tmData A).WellFormed) (hdet : (tmData A).Deterministic)
    {x : BAtom dtBlock A} (h : Derives dtRules x) : Meaning x := by
  have hlin : IsLinOrd (TMLe (A := A)) := hwf.1
  induction h with
  | @rule c hc a ha v hg hb ih =>
    simp only [dtRules, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    -- initial state
    · obtain rfl := Option.some.inj ha
      simp only [dtCQInit, Formula.realize_inf, realize_minPosG, realize_startG] at hg
      have hrk : bitRank TMLe TMPosn (v 0) = 0 := bitRank_eq_zero_of_minPos hlin hg.1
      obtain ⟨c₀, hinit, hstate⟩ := TMData.exists_isInit hwf hg.2
      have hsteps : (tmData A).StepsIn (bitRank TMLe TMPosn (v 0)) c₀ c₀ := by
        rw [hrk]
        rfl
      exact ⟨hg.1.1, c₀, c₀, hinit, hsteps, hstate⟩
    -- initial head
    · obtain rfl := Option.some.inj ha
      simp only [dtCHInit, realize_minPosG] at hg
      have hrk : bitRank TMLe TMPosn (v 0) = 0 := bitRank_eq_zero_of_minPos hlin hg
      refine ⟨hg.1, fun c₀ c hinit hrun => ?_⟩
      have hrun' : (tmData A).StepsIn 0 c₀ c := by
        rw [← hrk]
        exact hrun
      obtain rfl : c₀ = c := hrun'
      exact hlin.2.2.1 _ _ (hinit.2.1.2 (v 0) hg.1) (hg.2 c₀.head hinit.2.1.1)
    -- initial tape
    · obtain rfl := Option.some.inj ha
      simp only [dtCTInit, Formula.realize_inf, realize_minPosG, realize_initTapeG] at hg
      have hrk : bitRank TMLe TMPosn (v 0) = 0 := bitRank_eq_zero_of_minPos hlin hg.1
      refine ⟨hg.1.1, fun c₀ c hinit hrun => ?_⟩
      have hrun' : (tmData A).StepsIn 0 c₀ c := by
        rw [← hrk]
        exact hrun
      obtain rfl : c₀ = c := hrun'
      exact TMData.initTape_functional hwf (hinit.2.2 (v 6)) hg.2
    -- step, the state
    · obtain rfl := Option.some.inj ha
      simp only [dtCQStep, Formula.realize_inf, realize_dtCoreG, realize_canMoveG,
        realize_dstG] at hg
      obtain ⟨⟨⟨hsucc, hτ, hsrc, hread, -, aw, haw⟩, hmove⟩, hdst⟩ := hg
      obtain ⟨-, c₀, cc, hinit, hrun, hstate⟩ := ih (qAt 0 3) (by simp [dtCQStep, dtBody])
      have hhead : cc.head = v 6 :=
        (ih (hAt 0 6) (by simp [dtCQStep, dtBody])).2 c₀ cc hinit hrun
      have htape : cc.tape (v 6) = v 4 :=
        (ih (tAt 0 6 4) (by simp [dtCQStep, dtBody])).2 c₀ cc hinit hrun
      have hread' : (tmData A).Read (v 2) (cc.tape cc.head) := by
        rw [hhead, htape]
        exact hread
      have hsrc' : (tmData A).Src (v 2) cc.state := by
        rw [hstate]
        exact hsrc
      have hwaw : (tmData A).Write (v 2) (Function.update cc.tape cc.head aw cc.head) := by
        rw [Function.update_self]
        exact haw
      obtain ⟨h', hstep⟩ :
          ∃ h', (tmData A).Step cc ⟨v 5, h', Function.update cc.tape cc.head aw⟩ := by
        rcases hmove with ⟨hr, p', hp'⟩ | ⟨hr, p', hp'⟩
        · exact ⟨p', v 2, hτ, hsrc', hread', hdst, hwaw,
            fun r hr' => Function.update_of_ne hr' _ _,
            Or.inl ⟨hr, by rw [hhead]; exact hp'⟩⟩
        · exact ⟨p', v 2, hτ, hsrc', hread', hdst, hwaw,
            fun r hr' => Function.update_of_ne hr' _ _,
            Or.inr ⟨hr, by rw [hhead]; exact hp'⟩⟩
      have hrun' : (tmData A).StepsIn (bitRank TMLe TMPosn (v 1)) c₀
          ⟨v 5, h', Function.update cc.tape cc.head aw⟩ := by
        rw [bitRank_succPos hlin hsucc]
        exact hrun.trans_step hstep
      exact ⟨hsucc.2.1, c₀, _, hinit, hrun', rfl⟩
    -- step, the head, rightwards
    · obtain rfl := Option.some.inj ha
      simp only [dtCHStepR, Formula.realize_inf, realize_dtCoreG, realize_rightG,
        realize_succPosG] at hg
      obtain ⟨⟨⟨hsucc, hτ, hsrc, hread, -, -⟩, hr⟩, hsp⟩ := hg
      refine ⟨hsucc.2.1, fun c₀ c'' hinit hrun'' => ?_⟩
      have hrun2 : (tmData A).StepsIn (bitRank TMLe TMPosn (v 0) + 1) c₀ c'' := by
        rw [← bitRank_succPos hlin hsucc]
        exact hrun''
      obtain ⟨d, hd, hstep⟩ := TMData.stepsIn_succ_iff.mp hrun2
      obtain ⟨-, c₀', cc, hinit', hrun, hstate⟩ := ih (qAt 0 3) (by simp [dtCHStepR, dtBody])
      obtain rfl := TMData.isInit_unique hwf hdet.1 hinit' hinit
      obtain rfl := TMData.stepsIn_functional hlin hdet hrun hd
      have hhead : cc.head = v 6 :=
        (ih (hAt 0 6) (by simp [dtCHStepR, dtBody])).2 _ cc hinit hrun
      have htape : cc.tape (v 6) = v 4 :=
        (ih (tAt 0 6 4) (by simp [dtCHStepR, dtBody])).2 _ cc hinit hrun
      obtain ⟨σ, hσ, hsrc', hread', -, -, -, hmove'⟩ := hstep
      obtain rfl : σ = v 2 := by
        refine hdet.2.1 σ (v 2) cc.state (cc.tape cc.head) hσ hτ hsrc' ?_ hread' ?_
        · rw [hstate]
          exact hsrc
        · rw [hhead, htape]
          exact hread
      rcases hmove' with ⟨-, hsp'⟩ | ⟨hnr, -⟩
      · refine TMData.succPos_right_unique (M := tmData A) hlin ?_ hsp
        rw [← hhead]
        exact hsp'
      · exact absurd hr hnr
    -- step, the head, leftwards
    · obtain rfl := Option.some.inj ha
      simp only [dtCHStepL, Formula.realize_inf, realize_dtCoreG, Formula.realize_not,
        realize_rightG, realize_succPosG] at hg
      obtain ⟨⟨⟨hsucc, hτ, hsrc, hread, -, -⟩, hr⟩, hsp⟩ := hg
      refine ⟨hsucc.2.1, fun c₀ c'' hinit hrun'' => ?_⟩
      have hrun2 : (tmData A).StepsIn (bitRank TMLe TMPosn (v 0) + 1) c₀ c'' := by
        rw [← bitRank_succPos hlin hsucc]
        exact hrun''
      obtain ⟨d, hd, hstep⟩ := TMData.stepsIn_succ_iff.mp hrun2
      obtain ⟨-, c₀', cc, hinit', hrun, hstate⟩ := ih (qAt 0 3) (by simp [dtCHStepL, dtBody])
      obtain rfl := TMData.isInit_unique hwf hdet.1 hinit' hinit
      obtain rfl := TMData.stepsIn_functional hlin hdet hrun hd
      have hhead : cc.head = v 6 :=
        (ih (hAt 0 6) (by simp [dtCHStepL, dtBody])).2 _ cc hinit hrun
      have htape : cc.tape (v 6) = v 4 :=
        (ih (tAt 0 6 4) (by simp [dtCHStepL, dtBody])).2 _ cc hinit hrun
      obtain ⟨σ, hσ, hsrc', hread', -, -, -, hmove'⟩ := hstep
      obtain rfl : σ = v 2 := by
        refine hdet.2.1 σ (v 2) cc.state (cc.tape cc.head) hσ hτ hsrc' ?_ hread' ?_
        · rw [hstate]
          exact hsrc
        · rw [hhead, htape]
          exact hread
      rcases hmove' with ⟨hr', -⟩ | ⟨-, hsp'⟩
      · exact absurd hr' hr
      · refine succPos_left_unique hlin ?_ hsp
        rw [← hhead]
        exact hsp'
    -- step, the written cell
    · obtain rfl := Option.some.inj ha
      simp only [dtCWrite, Formula.realize_inf, realize_dtCoreG, realize_canMoveG,
        realize_writeG] at hg
      obtain ⟨⟨⟨hsucc, hτ, hsrc, hread, -, -⟩, -⟩, hw⟩ := hg
      refine ⟨hsucc.2.1, fun c₀ c'' hinit hrun'' => ?_⟩
      have hrun2 : (tmData A).StepsIn (bitRank TMLe TMPosn (v 0) + 1) c₀ c'' := by
        rw [← bitRank_succPos hlin hsucc]
        exact hrun''
      obtain ⟨d, hd, hstep⟩ := TMData.stepsIn_succ_iff.mp hrun2
      obtain ⟨-, c₀', cc, hinit', hrun, hstate⟩ := ih (qAt 0 3) (by simp [dtCWrite, dtBody])
      obtain rfl := TMData.isInit_unique hwf hdet.1 hinit' hinit
      obtain rfl := TMData.stepsIn_functional hlin hdet hrun hd
      have hhead : cc.head = v 6 :=
        (ih (hAt 0 6) (by simp [dtCWrite, dtBody])).2 _ cc hinit hrun
      have htape : cc.tape (v 6) = v 4 :=
        (ih (tAt 0 6 4) (by simp [dtCWrite, dtBody])).2 _ cc hinit hrun
      obtain ⟨σ, hσ, hsrc', hread', -, hwrite', -, -⟩ := hstep
      obtain rfl : σ = v 2 := by
        refine hdet.2.1 σ (v 2) cc.state (cc.tape cc.head) hσ hτ hsrc' ?_ hread' ?_
        · rw [hstate]
          exact hsrc
        · rw [hhead, htape]
          exact hread
      have hgoal : c''.tape (v 6) = v 5 := by
        rw [← hhead]
        refine hdet.2.2.2 (v 2) _ _ ?_ hw
        exact hwrite'
      exact hgoal
    -- step, the frame
    · obtain rfl := Option.some.inj ha
      simp only [dtCFrame, Formula.realize_inf, realize_dtCoreG, realize_canMoveG,
        realize_neG] at hg
      obtain ⟨⟨⟨hsucc, hτ, hsrc, hread, -, -⟩, -⟩, hne⟩ := hg
      refine ⟨hsucc.2.1, fun c₀ c'' hinit hrun'' => ?_⟩
      have hrun2 : (tmData A).StepsIn (bitRank TMLe TMPosn (v 0) + 1) c₀ c'' := by
        rw [← bitRank_succPos hlin hsucc]
        exact hrun''
      obtain ⟨d, hd, hstep⟩ := TMData.stepsIn_succ_iff.mp hrun2
      obtain ⟨-, c₀', cc, hinit', hrun, hstate⟩ := ih (qAt 0 3) (by simp [dtCFrame, dtBody])
      obtain rfl := TMData.isInit_unique hwf hdet.1 hinit' hinit
      obtain rfl := TMData.stepsIn_functional hlin hdet hrun hd
      have hhead : cc.head = v 6 :=
        (ih (hAt 0 6) (by simp [dtCFrame, dtBody])).2 _ cc hinit hrun
      have hprev : cc.tape (v 7) = v 8 :=
        (ih (tAt 0 7 8) (by simp [dtCFrame, dtBody])).2 _ cc hinit hrun
      obtain ⟨σ, hσ, hsrc', hread', -, -, hframe, -⟩ := hstep
      have hgoal : c''.tape (v 7) = v 8 := by
        rw [hframe (v 7) (by rw [hhead]; exact hne)]
        exact hprev
      exact hgoal

omit [Nonempty A] in
/-- **Completeness**: the run is derived, rank by rank. Determinism plays no
role in this direction – the rules fire on whatever run is given. -/
theorem derivedAt_of_run (hwf : (tmData A).WellFormed)
    {c₀ : Config A} (hinit : (tmData A).IsInit c₀) :
    ∀ (k : ℕ) (t : A), TMPosn t → bitRank TMLe TMPosn t = k →
      ∀ d : Config A, (tmData A).StepsIn k c₀ d →
        DQ t d.state ∧ DH t d.head ∧ ∀ p : A, DT t p (d.tape p) := by
  have hlin : IsLinOrd (TMLe (A := A)) := hwf.1
  intro k
  induction k with
  | zero =>
    intro t ht hrk d hrun
    obtain rfl : c₀ = d := hrun
    have hmin : MinPos TMLe TMPosn t := minPos_of_bitRank_eq_zero hlin ht hrk
    refine ⟨?_, ?_, fun p => ?_⟩
    · refine dq_iff.mp (Derives.rule (rules := dtRules) (c := dtCQInit)
        (by simp [dtRules]) (a := qAt 0 3) rfl
        (v := ![t, t, t, c₀.state, t, t, t, t, t]) ?_ ?_)
      · simp only [dtCQInit, Formula.realize_inf, realize_minPosG, realize_startG]
        exact ⟨hmin, hinit.1⟩
      · intro b hb
        exact (List.not_mem_nil hb).elim
    · have h := dh_iff.mp (Derives.rule (rules := dtRules) (c := dtCHInit)
        (by simp [dtRules]) (a := hAt 0 0) rfl (v := ![t, t, t, t, t, t, t, t, t])
        (by simp only [dtCHInit, realize_minPosG]; exact hmin)
        (fun b hb => (List.not_mem_nil hb).elim))
      rwa [show c₀.head = t from hlin.2.2.1 _ _ (hinit.2.1.2 t ht) (hmin.2 c₀.head hinit.2.1.1)]
    · refine dt_iff.mp (Derives.rule (rules := dtRules) (c := dtCTInit)
        (by simp [dtRules]) (a := tAt 0 6 4) rfl
        (v := ![t, t, t, t, c₀.tape p, t, p, t, t]) ?_ ?_)
      · simp only [dtCTInit, Formula.realize_inf, realize_minPosG, realize_initTapeG]
        exact ⟨hmin, hinit.2.2 p⟩
      · intro b hb
        exact (List.not_mem_nil hb).elim
  | succ k ih =>
    intro t ht hrk d hrun
    have hnmin : ¬ MinPos TMLe TMPosn t := fun hmin => by
      rw [bitRank_eq_zero_of_minPos hlin hmin] at hrk
      omega
    obtain ⟨t₀, hsucc⟩ := exists_predPos hlin ht hnmin
    have hrk₀ : bitRank TMLe TMPosn t₀ = k := by
      have := bitRank_succPos hlin hsucc
      omega
    obtain ⟨d₀, hrun₀, hstep⟩ := TMData.stepsIn_succ_iff.mp hrun
    obtain ⟨hQ, hH, hT⟩ := ih t₀ hsucc.1 hrk₀ d₀ hrun₀
    obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
    have hcanmove : (TMRight τ ∧ ∃ p : A, SuccPos TMLe TMPosn d₀.head p) ∨
        (¬ TMRight τ ∧ ∃ p : A, SuccPos TMLe TMPosn p d₀.head) := by
      rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨hr, _, hs⟩
      · exact Or.inr ⟨hr, _, hs⟩
    have hbody : ∀ (v : Fin 9 → A), v 0 = t₀ → v 3 = d₀.state → v 4 = d₀.tape d₀.head →
        v 6 = d₀.head → ∀ b ∈ dtBody,
          Derives (A := A) dtRules ⟨b.idx, fun j => v (b.args j)⟩ := by
      rintro v h0 h3 h4 h6 b hb
      simp only [dtBody, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · refine dq_iff.mpr ?_
        rw [h0, h3]
        exact hQ
      · refine dh_iff.mpr ?_
        rw [h0, h6]
        exact hH
      · refine dt_iff.mpr ?_
        rw [h0, h6, h4]
        exact hT d₀.head
    have hcore : ∀ (v : Fin 9 → A), v 0 = t₀ → v 1 = t → v 2 = τ → v 3 = d₀.state →
        v 4 = d₀.tape d₀.head → (dtCoreG.Realize v) := by
      intro v h0 h1 h2 h3 h4
      refine realize_dtCoreG.mpr ?_
      rw [h0, h1, h2, h3, h4]
      exact ⟨hsucc, hτ, hsrc, hread, ⟨d.state, hdst⟩, ⟨d.tape d₀.head, hwrite⟩⟩
    refine ⟨?_, ?_, fun p => ?_⟩
    · refine dq_iff.mp (Derives.rule (rules := dtRules) (c := dtCQStep)
        (by simp [dtRules]) (a := qAt 1 5) rfl
        (v := ![t₀, t, τ, d₀.state, d₀.tape d₀.head, d.state, d₀.head, t, t]) ?_ ?_)
      · simp only [dtCQStep, Formula.realize_inf, realize_canMoveG, realize_dstG]
        exact ⟨⟨hcore _ rfl rfl rfl rfl rfl, hcanmove⟩, hdst⟩
      · exact hbody _ rfl rfl rfl rfl
    · rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · refine dh_iff.mp (Derives.rule (rules := dtRules) (c := dtCHStepR)
          (by simp [dtRules]) (a := hAt 1 7) rfl
          (v := ![t₀, t, τ, d₀.state, d₀.tape d₀.head, t, d₀.head, d.head, t]) ?_ ?_)
        · simp only [dtCHStepR, Formula.realize_inf, realize_rightG, realize_succPosG]
          exact ⟨⟨hcore _ rfl rfl rfl rfl rfl, hr⟩, hs⟩
        · exact hbody _ rfl rfl rfl rfl
      · refine dh_iff.mp (Derives.rule (rules := dtRules) (c := dtCHStepL)
          (by simp [dtRules]) (a := hAt 1 7) rfl
          (v := ![t₀, t, τ, d₀.state, d₀.tape d₀.head, t, d₀.head, d.head, t]) ?_ ?_)
        · simp only [dtCHStepL, Formula.realize_inf, Formula.realize_not, realize_rightG,
            realize_succPosG]
          exact ⟨⟨hcore _ rfl rfl rfl rfl rfl, hr⟩, hs⟩
        · exact hbody _ rfl rfl rfl rfl
    · rcases eq_or_ne p d₀.head with rfl | hp
      · refine dt_iff.mp (Derives.rule (rules := dtRules) (c := dtCWrite)
          (by simp [dtRules]) (a := tAt 1 6 5) rfl
          (v := ![t₀, t, τ, d₀.state, d₀.tape d₀.head, d.tape d₀.head, d₀.head, t, t]) ?_ ?_)
        · simp only [dtCWrite, Formula.realize_inf, realize_canMoveG, realize_writeG]
          exact ⟨⟨hcore _ rfl rfl rfl rfl rfl, hcanmove⟩, hwrite⟩
        · exact hbody _ rfl rfl rfl rfl
      · have hfr : d.tape p = d₀.tape p := hframe p hp
        refine dt_iff.mp (Derives.rule (rules := dtRules) (c := dtCFrame)
          (by simp [dtRules]) (a := tAt 1 7 8) rfl
          (v := ![t₀, t, τ, d₀.state, d₀.tape d₀.head, t, d₀.head, p, d.tape p]) ?_ ?_)
        · simp only [dtCFrame, Formula.realize_inf, realize_canMoveG, realize_neG]
          exact ⟨⟨hcore _ rfl rfl rfl rfl rfl, hcanmove⟩, hp⟩
        · intro b hb
          simp only [dtCFrame, dtBody, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hb
          rcases hb with (rfl | rfl | rfl) | rfl
          · exact dq_iff.mpr hQ
          · exact dh_iff.mpr hH
          · exact dt_iff.mpr (hT d₀.head)
          · refine dt_iff.mpr ?_
            rw [show (![t₀, t, τ, d₀.state, d₀.tape d₀.head, t, d₀.head, p,
              d.tape p] : Fin 9 → A) 8 = d₀.tape p from hfr]
            exact hT p

omit [Nonempty A] in
/-- **The machine accepts exactly when the fixed point contains an accepting
state**: the two inductions above, glued by the surjectivity of the rank below
the position count. -/
theorem accepts_iff_derives (hwf : (tmData A).WellFormed)
    (hdet : (tmData A).Deterministic) :
    (tmData A).Accepts ↔ ∃ t q : A, DQ t q ∧ TMAcc q := by
  constructor
  · rintro ⟨c₀, c, n, hinit, hn, hrun, hacc⟩
    obtain ⟨t, ht, hrk⟩ := exists_pos_bitRank hwf.1 n hn
    obtain ⟨hQ, -, -⟩ := derivedAt_of_run hwf hinit n t ht hrk c hrun
    exact ⟨t, c.state, hQ, hacc⟩
  · rintro ⟨t, q, hQ, hacc⟩
    obtain ⟨ht, c₀, c, hinit, hrun, hstate⟩ := derives_sound hwf hdet hQ
    refine ⟨c₀, c, _, hinit, bitRank_lt_card ht, hrun, ?_⟩
    change TMAcc c.state
    rw [hstate]
    exact hacc

end Correctness

end DTFix

open DTFix in
/-- **Deterministic machine acceptance is FO(LFP) definable**: the run is the
least fixed point of the step rules, and the output states the promises and
that an accepting state occurs. -/
theorem dtmAccept_lfpDefinable : LFPDefinable DTMAccept := by
  refine ⟨⟨dtBlock, 9, dtRules, dtOut⟩, ?_⟩
  intro A _ _ _ _
  refine Iff.trans ?_ (realize_dtOut (lfpAssign dtRules)).symm
  constructor
  · rintro ⟨hwf, hdet, hacc⟩
    exact ⟨hwf, hdet, (accepts_iff_derives hwf hdet).mp hacc⟩
  · rintro ⟨hwf, hdet, hout⟩
    exact ⟨hwf, hdet, (accepts_iff_derives hwf hdet).mpr hout⟩

/-- **Deterministic machine acceptance is in PTIME**, through the formalized
translation of FO(LFP) into the Horn fragment. -/
theorem dtmAccept_mem_PTIME : DTMAccept ∈ PTIME :=
  (lfpDefinable_iff_sigmaSOHornDefinable DTMAccept).mp dtmAccept_lfpDefinable

end DescriptiveComplexity
