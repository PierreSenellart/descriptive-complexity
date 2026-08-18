/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointStepRel
import DescriptiveComplexity.Problems.Machine.SpaceHard

/-!
# PSPACE is contained in FO(≤, PFP)

The hard half of the capture theorem FO(≤, PFP) = PSPACE, by iterating the
PSPACE-complete deterministic machine problem: a partial fixed-point
definition `DescriptiveComplexity.mPfp` whose block holds one machine
configuration – the block of the SO(TC) membership proof of
`DescriptiveComplexity.Problems.Machine.Space` – and whose step formulas
advance it:

* from the empty assignment (recognized by its empty state mark, which no
  configuration has), one step *loads the initial configuration* – start
  state, head on the lowest position, initial tape;
* from a configuration that can move – some applicable transition with a
  destination, a written symbol and a neighboring position to move to
  (`DescriptiveComplexity.SpaceTM.GoOn`) – and is not yet accepting, one step
  is **the** machine step, determinism making the step formulas functional;
* from an accepting or stuck configuration, the step *stutters*, so that a
  halting run is exactly a converging iteration.

A machine that loops forever diverges the iteration, and under the
convergence-requiring semantics of `DescriptiveComplexity.FixedPointPartial`
that alone makes the definition false – no divergence detection, no counter.
The output sentence checks well-formedness and determinism (conditions on the
instance only) and reads acceptance off the stable configuration
(`DescriptiveComplexity.dtmAcceptSpace_pfpDefinable`).

Whence the capture: every PSPACE problem reduces to the machine problem by a
*relativized* ordered reduction
(`DescriptiveComplexity.le_dtmAcceptSpace_of_mem_PSPACE`), and FO(≤, PFP)
definability crosses such reductions
(`DescriptiveComplexity.PFPDefinable.of_relOrderedReduction`), so
`DescriptiveComplexity.pfpDefinable_of_mem_PSPACE` and, with the converse
inclusion of `DescriptiveComplexity.FixedPointPartialSpace`, the capture
theorem `DescriptiveComplexity.pfpDefinable_iff_mem_PSPACE`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

namespace SpaceTM

/-! ### Formula builders

In the parameterized style of `DescriptiveComplexity.Problems.Machine.Space`:
each builder takes the relation symbols it reads, so realization lemmas are
stated over `RelMap` and specialize to any expansion. -/

section Shapes

variable {L' : Language.{0, 0}} {M : Type} [L'.Structure M] {γ : Type}

/-- Some element carries both marks. -/
noncomputable def markMeetF (s r : L'.Relations 1) : L'.Formula γ :=
  (Relations.formula₁ s (Term.var (Sum.inr 0)) ⊓
    Relations.formula₁ r (Term.var (Sum.inr 0))).iExs (Fin 1)

/-- The binary relation holds of the term and some element. -/
noncomputable def someArgF (r : L'.Relations 2) (τ : L'.Term γ) : L'.Formula γ :=
  (Relations.formula₂ r (τ.relabel Sum.inl) (Term.var (Sum.inr 0))).iExs (Fin 1)

/-- The term is an applicable transition: a transition whose source is the
marked state and whose read symbol is the one held by the marked cell. -/
noncomputable def applF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (τ : L'.Term γ) : L'.Formula γ :=
  Relations.formula₁ tr τ ⊓ (markArgF src s τ ⊓ cellArgF rd h t τ)

/-- The head can move from the marked cell to `p'`, in the direction the
transition names. -/
noncomputable def moveToF (right : L'.Relations 1) (le : L'.Relations 2)
    (posn h : L'.Relations 1) (τ p' : L'.Term γ) : L'.Formula γ :=
  ((Relations.formula₁ h (Term.var (Sum.inr 0))) ⊓
    ((Relations.formula₁ right (τ.relabel Sum.inl) ⊓
        succPosF le posn (Term.var (Sum.inr 0)) ((p'.relabel Sum.inl))) ⊔
      (∼(Relations.formula₁ right (τ.relabel Sum.inl)) ⊓
        succPosF le posn ((p'.relabel Sum.inl)) (Term.var (Sum.inr 0))))).iExs (Fin 1)

/-- The machine takes a step: no accepting mark, and some applicable
transition with a destination, a written symbol, and a position to move
to. -/
noncomputable def goF (tr : L'.Relations 1) (src rd dst wr : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (acc right : L'.Relations 1)
    (le : L'.Relations 2) (posn : L'.Relations 1) : L'.Formula γ :=
  ∼(markMeetF s acc) ⊓
    ((applF tr src rd s h t (Term.var (Sum.inr 0)) ⊓
        (someArgF dst (Term.var (Sum.inr 0)) ⊓
          (someArgF wr (Term.var (Sum.inr 0)) ⊓
            moveToF right le posn h (Term.var (Sum.inr 0))
              (Term.var (Sum.inr 1))))).iExs (Fin 2))

/-- The cell initially holds this symbol: its input symbol, or the blank when
no input is given for it. -/
noncomputable def initTapeAtF (inp : L'.Relations 2) (blank : L'.Relations 1)
    (x y : L'.Term γ) : L'.Formula γ :=
  Relations.formula₂ inp x y ⊔
    (Formula.iAlls (Fin 1)
        (∼(Relations.formula₂ inp (x.relabel Sum.inl) (Term.var (Sum.inr 0))) :
          L'.Formula (γ ⊕ Fin 1)) ⊓
      Relations.formula₁ blank y)

/-- The term is the lowest position. -/
noncomputable def minPosAtF (le : L'.Relations 2) (posn : L'.Relations 1)
    (x : L'.Term γ) : L'.Formula γ :=
  Relations.formula₁ posn x ⊓
    ((Relations.formula₁ posn (Term.var (Sum.inr 0))).imp
      (Relations.formula₂ le (x.relabel Sum.inl) (Term.var (Sum.inr 0)))).iAlls (Fin 1)

variable {v : γ → M}

@[simp]
theorem realize_markMeetF (s r : L'.Relations 1) :
    (markMeetF (γ := γ) s r).Realize v ↔ ∃ q : M, RelMap s ![q] ∧ RelMap r ![q] := by
  rw [markMeetF]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁,
    Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩

@[simp]
theorem realize_someArgF (r : L'.Relations 2) (τ : L'.Term γ) :
    (someArgF r τ).Realize v ↔ ∃ b : M, RelMap r ![τ.realize v, b] := by
  rw [someArgF]
  simp only [Formula.realize_iExs, Formula.realize_rel₂, Term.realize_var,
    Term.realize_relabel, Sum.elim_comp_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩

@[simp]
theorem realize_applF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (τ : L'.Term γ) :
    (applF tr src rd s h t τ).Realize v ↔
      (RelMap tr ![τ.realize v] ∧
        ((∀ q : M, RelMap s ![q] → RelMap src ![τ.realize v, q]) ∧
          ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] →
            RelMap rd ![τ.realize v, a])) := by
  rw [applF]
  simp only [Formula.realize_inf, Formula.realize_rel₁, realize_markArgF,
    realize_cellArgF]

@[simp]
theorem realize_moveToF (right : L'.Relations 1) (le : L'.Relations 2)
    (posn h : L'.Relations 1) (τ p' : L'.Term γ) :
    (moveToF right le posn h τ p').Realize v ↔
      ∃ p : M, RelMap h ![p] ∧
        ((RelMap right ![τ.realize v] ∧
            SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) p
              (p'.realize v)) ∨
          (¬RelMap right ![τ.realize v] ∧
            SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a])
              (p'.realize v) p)) := by
  rw [moveToF]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_not, Formula.realize_rel₁, realize_succPosF, Term.realize_var,
    Term.realize_relabel, Sum.elim_comp_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩

@[simp]
theorem realize_goF (tr : L'.Relations 1) (src rd dst wr : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (acc right : L'.Relations 1)
    (le : L'.Relations 2) (posn : L'.Relations 1) :
    (goF (γ := γ) tr src rd dst wr s h t acc right le posn).Realize v ↔
      ((¬∃ q : M, RelMap s ![q] ∧ RelMap acc ![q]) ∧
        ∃ τ p' : M,
          ((RelMap tr ![τ] ∧
              ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
                ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
            ((∃ b : M, RelMap dst ![τ, b]) ∧
              ((∃ b : M, RelMap wr ![τ, b]) ∧
                ∃ p : M, RelMap h ![p] ∧
                  ((RelMap right ![τ] ∧
                      SuccPos (fun a b => RelMap le ![a, b])
                        (fun a => RelMap posn ![a]) p p') ∨
                    (¬RelMap right ![τ] ∧
                      SuccPos (fun a b => RelMap le ![a, b])
                        (fun a => RelMap posn ![a]) p' p)))))) := by
  rw [goF]
  simp only [Formula.realize_inf, Formula.realize_not, realize_markMeetF,
    Formula.realize_iExs, realize_applF, realize_someArgF, realize_moveToF,
    Term.realize_var, Sum.elim_inr]
  refine and_congr Iff.rfl
    ⟨fun ⟨i, hi⟩ => ⟨i 0, i 1, hi⟩, fun ⟨τ, p', hp⟩ => ⟨![τ, p'], hp⟩⟩

@[simp]
theorem realize_initTapeAtF (inp : L'.Relations 2) (blank : L'.Relations 1)
    (x y : L'.Term γ) :
    (initTapeAtF inp blank x y).Realize v ↔
      (RelMap inp ![x.realize v, y.realize v] ∨
        ((∀ b : M, ¬RelMap inp ![x.realize v, b]) ∧
          RelMap blank ![y.realize v])) := by
  rw [initTapeAtF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_not, Formula.realize_rel₂, Formula.realize_rel₁, Term.realize_var,
    Term.realize_relabel, Sum.elim_comp_inl, Sum.elim_inr]
  exact or_congr Iff.rfl (and_congr
    ⟨fun hh b => hh fun _ => b, fun hh i => hh (i 0)⟩ Iff.rfl)

@[simp]
theorem realize_minPosAtF (le : L'.Relations 2) (posn : L'.Relations 1)
    (x : L'.Term γ) :
    (minPosAtF le posn x).Realize v ↔
      MinPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a])
        (x.realize v) := by
  rw [minPosAtF, MinPos]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Term.realize_relabel,
    Sum.elim_comp_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun hh q => hh fun _ => q, fun hh i => hh (i 0)⟩

/-- The transition applies, with a destination, a written symbol, and this
new symbol written in the marked cell. -/
noncomputable def writeNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t wr : L'.Relations 2) (y : L'.Term γ) : L'.Formula γ :=
  (applF tr src rd s h t (Term.var (Sum.inr 0)) ⊓
    Relations.formula₂ wr (Term.var (Sum.inr 0)) (y.relabel Sum.inl)).iExs (Fin 1)

/-- The transition applies and moves to this new state. -/
noncomputable def dstNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t dst : L'.Relations 2) (y : L'.Term γ) : L'.Formula γ :=
  (applF tr src rd s h t (Term.var (Sum.inr 0)) ⊓
    Relations.formula₂ dst (Term.var (Sum.inr 0)) (y.relabel Sum.inl)).iExs (Fin 1)

/-- The transition applies and moves the head to this new position. -/
noncomputable def headNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (right : L'.Relations 1)
    (le : L'.Relations 2) (posn : L'.Relations 1) (y : L'.Term γ) : L'.Formula γ :=
  (applF tr src rd s h t (Term.var (Sum.inr 0)) ⊓
    moveToF right le posn h (Term.var (Sum.inr 0)) (y.relabel Sum.inl)).iExs (Fin 1)

variable {v : γ → M}

@[simp]
theorem realize_writeNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t wr : L'.Relations 2) (y : L'.Term γ) :
    (writeNewF tr src rd s h t wr y).Realize v ↔
      ∃ τ : M, (RelMap tr ![τ] ∧
          ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
            ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
        RelMap wr ![τ, y.realize v] := by
  rw [writeNewF]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_applF,
    Formula.realize_rel₂, Term.realize_var, Term.realize_relabel, Sum.elim_comp_inl,
    Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

@[simp]
theorem realize_dstNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t dst : L'.Relations 2) (y : L'.Term γ) :
    (dstNewF tr src rd s h t dst y).Realize v ↔
      ∃ τ : M, (RelMap tr ![τ] ∧
          ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
            ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
        RelMap dst ![τ, y.realize v] := by
  rw [dstNewF]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_applF,
    Formula.realize_rel₂, Term.realize_var, Term.realize_relabel, Sum.elim_comp_inl,
    Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

@[simp]
theorem realize_headNewF (tr : L'.Relations 1) (src rd : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (right : L'.Relations 1)
    (le : L'.Relations 2) (posn : L'.Relations 1) (y : L'.Term γ) :
    (headNewF tr src rd s h t right le posn y).Realize v ↔
      ∃ τ : M, (RelMap tr ![τ] ∧
          ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
            ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
        ∃ p : M, RelMap h ![p] ∧
          ((RelMap right ![τ] ∧
              SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) p
                (y.realize v)) ∨
            (¬RelMap right ![τ] ∧
              SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a])
                (y.realize v) p)) := by
  rw [headNewF]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_applF, realize_moveToF,
    Term.realize_var, Term.realize_relabel, Sum.elim_comp_inl, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

end Shapes

/-! ### The iterated definition and its semantics -/

section Machine

variable {A : Type} [Language.turing.Structure A]

/-- The state mark is empty: how the iteration recognizes the not-yet-started
assignment, which no configuration resembles. -/
def StateEmptyOn (ρ : mBlock.Assignment A) : Prop := ¬∃ q : A, mState ρ q

/-- The transition applies in the marked state, reading the marked cell. -/
def ApplOn (ρ : mBlock.Assignment A) (τ : A) : Prop :=
  TMTr τ ∧ ((∀ q : A, mState ρ q → TMSrc τ q) ∧
    ∀ p a : A, mHead ρ p → mTape ρ p a → TMRead τ a)

/-- The machine takes a step from this assignment: no accepting mark, and
some applicable transition with a destination, a written symbol and a
position to move to. -/
def GoOn (ρ : mBlock.Assignment A) : Prop :=
  (¬∃ q : A, mState ρ q ∧ TMAcc q) ∧
    ∃ τ p' : A, ApplOn ρ τ ∧
      ((∃ b : A, TMDst τ b) ∧ ((∃ b : A, TMWrite τ b) ∧
        ∃ p : A, mHead ρ p ∧ ((TMRight τ ∧ SuccPos TMLe TMPosn p p') ∨
          (¬TMRight τ ∧ SuccPos TMLe TMPosn p' p))))

variable (A) in
/-- The initial assignment: start states, lowest positions, the initial
tape. On a well-formed deterministic instance with a start state this is a
configuration – the initial one. -/
def mInitAssign : mBlock.Assignment A
  | none => fun x => (tmData A).InitTape (x 0) (x 1)
  | some false => fun x => TMStart (x 0)
  | some true => fun x => MinPos TMLe TMPosn (x 0)

/-- One application of the step formulas, semantically: load the initial
configuration from the empty assignment, take the machine step when one is
available and the state is not accepting, stutter otherwise. -/
def mNextAssign (ρ : mBlock.Assignment A) : mBlock.Assignment A
  | none => fun x =>
      (StateEmptyOn ρ ∧ (tmData A).InitTape (x 0) (x 1)) ∨
        (¬StateEmptyOn ρ ∧
          ((¬GoOn ρ ∧ mTape ρ (x 0) (x 1)) ∨
            (GoOn ρ ∧ ((¬mHead ρ (x 0) ∧ mTape ρ (x 0) (x 1)) ∨
              (mHead ρ (x 0) ∧ ∃ τ : A, ApplOn ρ τ ∧ TMWrite τ (x 1))))))
  | some false => fun x =>
      (StateEmptyOn ρ ∧ TMStart (x 0)) ∨
        (¬StateEmptyOn ρ ∧
          ((¬GoOn ρ ∧ mState ρ (x 0)) ∨
            (GoOn ρ ∧ ∃ τ : A, ApplOn ρ τ ∧ TMDst τ (x 0))))
  | some true => fun x =>
      (StateEmptyOn ρ ∧ MinPos TMLe TMPosn (x 0)) ∨
        (¬StateEmptyOn ρ ∧
          ((¬GoOn ρ ∧ mHead ρ (x 0)) ∨
            (GoOn ρ ∧ ∃ τ : A, ApplOn ρ τ ∧ ∃ p : A, mHead ρ p ∧
              ((TMRight τ ∧ SuccPos TMLe TMPosn p (x 0)) ∨
                (¬TMRight τ ∧ SuccPos TMLe TMPosn (x 0) p)))))

end Machine

/-! ### The step formulas -/

section Formulas

/-- The empty-state test, as a formula. -/
noncomputable def emptyF {γ : Type} : mLang₁.Formula γ := ∼(someF mS₁)

/-- The step condition, at the machine's symbols. -/
noncomputable def mGoF {γ : Type} : mLang₁.Formula γ :=
  goF (mIn₁ tmTr) (mIn₁ tmSrc) (mIn₁ tmRead) (mIn₁ tmDst) (mIn₁ tmWrite) mS₁ mH₁ mT₁
    (mIn₁ tmAcc) (mIn₁ tmRight) (mIn₁ tmLe) (mIn₁ tmPosn)

/-- The step formula of the tape variable. -/
noncomputable def stepTapeF : mLang₁.Formula (Fin 2) :=
  (emptyF ⊓ initTapeAtF (mIn₁ tmInp) (mIn₁ tmBlank) (Term.var 0) (Term.var 1)) ⊔
    (∼emptyF ⊓
      ((∼mGoF ⊓ Relations.formula₂ mT₁ (Term.var 0) (Term.var 1)) ⊔
        (mGoF ⊓ ((∼(Relations.formula₁ mH₁ (Term.var 0)) ⊓
            Relations.formula₂ mT₁ (Term.var 0) (Term.var 1)) ⊔
          (Relations.formula₁ mH₁ (Term.var 0) ⊓
            writeNewF (mIn₁ tmTr) (mIn₁ tmSrc) (mIn₁ tmRead) mS₁ mH₁ mT₁
              (mIn₁ tmWrite) (Term.var 1))))))

/-- The step formula of the state variable. -/
noncomputable def stepStateF : mLang₁.Formula (Fin 1) :=
  (emptyF ⊓ Relations.formula₁ (mIn₁ tmStart) (Term.var 0)) ⊔
    (∼emptyF ⊓
      ((∼mGoF ⊓ Relations.formula₁ mS₁ (Term.var 0)) ⊔
        (mGoF ⊓ dstNewF (mIn₁ tmTr) (mIn₁ tmSrc) (mIn₁ tmRead) mS₁ mH₁ mT₁
          (mIn₁ tmDst) (Term.var 0))))

/-- The step formula of the head variable. -/
noncomputable def stepHeadF : mLang₁.Formula (Fin 1) :=
  (emptyF ⊓ minPosAtF (mIn₁ tmLe) (mIn₁ tmPosn) (Term.var 0)) ⊔
    (∼emptyF ⊓
      ((∼mGoF ⊓ Relations.formula₁ mH₁ (Term.var 0)) ⊔
        (mGoF ⊓ headNewF (mIn₁ tmTr) (mIn₁ tmSrc) (mIn₁ tmRead) mS₁ mH₁ mT₁
          (mIn₁ tmRight) (mIn₁ tmLe) (mIn₁ tmPosn) (Term.var 0))))

/-- **The machine iteration**: one configuration in the block, one machine
step per stage, stuttering on halting configurations; the output checks the
instance and reads acceptance off the stable configuration. -/
noncomputable def mPfp : StepDef mBase where
  B := mBlock
  step := fun i => match i with
    | none => stepTapeF
    | some false => stepStateF
    | some true => stepHeadF
  out := wfF (mIn₁ tmLe) (mIn₁ tmInp) (mIn₁ tmPosn) (mIn₁ tmBlank) ⊓
    (detF (mIn₁ tmTr) (mIn₁ tmStart) (mIn₁ tmSrc) (mIn₁ tmRead) (mIn₁ tmDst)
        (mIn₁ tmWrite) ⊓
      markMeetF mS₁ (mIn₁ tmAcc))

end Formulas

/-! ### The step formulas mean the semantic step -/

section Master

variable {A : Type} [Language.turing.Structure A] [LinearOrder A]

theorem realize_emptyF (ρ : mBlock.Assignment A) {γ : Type} (v : γ → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ (emptyF (γ := γ)) v) ↔
      StateEmptyOn ρ := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [emptyF, Formula.realize_not, realize_someF]
  exact Iff.rfl

theorem realize_mGoF (ρ : mBlock.Assignment A) {γ : Type} (v : γ → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ (mGoF (γ := γ)) v) ↔
      GoOn ρ := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [mGoF, realize_goF]
  exact Iff.rfl

theorem realize_stepTapeF (ρ : mBlock.Assignment A) (x : Fin 2 → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ stepTapeF x) ↔
      mNextAssign ρ none x := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [stepTapeF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_emptyF, realize_mGoF, realize_initTapeAtF, realize_writeNewF,
    Formula.realize_rel₂, Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

theorem realize_stepStateF (ρ : mBlock.Assignment A) (x : Fin 1 → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ stepStateF x) ↔
      mNextAssign ρ (some false) x := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [stepStateF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_emptyF, realize_mGoF, realize_dstNewF, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

theorem realize_stepHeadF (ρ : mBlock.Assignment A) (x : Fin 1 → A) :
    (@Formula.Realize _ A (mBlock.structure₁ (L := mBase) ρ) _ stepHeadF x) ↔
      mNextAssign ρ (some true) x := by
  let := mBlock.structure₁ (L := mBase) ρ
  rw [stepHeadF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_emptyF, realize_mGoF, realize_minPosAtF, realize_headNewF,
    Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- **One application of the step formulas is the semantic step.** -/
theorem next_mPfp (ρ : mBlock.Assignment A) : mPfp.next ρ = mNextAssign ρ := by
  funext i x
  match i with
  | none => exact propext (realize_stepTapeF ρ x)
  | some false => exact propext (realize_stepStateF ρ x)
  | some true => exact propext (realize_stepHeadF ρ x)

end Master

/-! ### The iteration follows the run -/

section Run

variable {A : Type} [Language.turing.Structure A] [LinearOrder A]

omit [Language.turing.Structure A] [LinearOrder A] in
theorem not_stateEmptyOn_cfgAssign (c : Config A) : ¬StateEmptyOn (cfgAssign c) :=
  fun h => h ⟨c.state, rfl⟩

omit [Language.turing.Structure A] [LinearOrder A] in
theorem stateEmptyOn_botAssign : StateEmptyOn (mBlock.botAssign A) :=
  fun ⟨_, h⟩ => h

omit [LinearOrder A] in
/-- From an empty state mark, one step loads the initial assignment. -/
theorem mNextAssign_of_stateEmpty {ρ : mBlock.Assignment A} (h : StateEmptyOn ρ) :
    mNextAssign ρ = mInitAssign A := by
  funext i x
  match i with
  | none =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inl ⟨h, hh⟩⟩
    rcases hh with ⟨-, h2⟩ | ⟨hn, -⟩
    · exact h2
    · exact absurd h hn
  | some false =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inl ⟨h, hh⟩⟩
    rcases hh with ⟨-, h2⟩ | ⟨hn, -⟩
    · exact h2
    · exact absurd h hn
  | some true =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inl ⟨h, hh⟩⟩
    rcases hh with ⟨-, h2⟩ | ⟨hn, -⟩
    · exact h2
    · exact absurd h hn

omit [LinearOrder A] in
/-- On a configuration from which the machine takes no step, the iteration
stutters. -/
theorem mNextAssign_cfgAssign_of_not_goOn {c : Config A} (hng : ¬GoOn (cfgAssign c)) :
    mNextAssign (cfgAssign c) = cfgAssign c := by
  have hne := not_stateEmptyOn_cfgAssign c
  funext i x
  match i with
  | none =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inr ⟨hne, Or.inl ⟨hng, hh⟩⟩⟩
    rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨-, ht⟩ | ⟨hg, -⟩⟩
    · exact absurd hSE hne
    · exact ht
    · exact absurd hg hng
  | some false =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inr ⟨hne, Or.inl ⟨hng, hh⟩⟩⟩
    rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨-, ht⟩ | ⟨hg, -⟩⟩
    · exact absurd hSE hne
    · exact ht
    · exact absurd hg hng
  | some true =>
    refine propext ⟨fun hh => ?_, fun hh => Or.inr ⟨hne, Or.inl ⟨hng, hh⟩⟩⟩
    rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨-, ht⟩ | ⟨hg, -⟩⟩
    · exact absurd hSE hne
    · exact ht
    · exact absurd hg hng

omit [LinearOrder A] in
/-- On an accepting configuration, the iteration stutters. -/
theorem mNextAssign_cfgAssign_of_acc {c : Config A} (hacc : (tmData A).Acc c.state) :
    mNextAssign (cfgAssign c) = cfgAssign c :=
  mNextAssign_cfgAssign_of_not_goOn fun hgo => hgo.1 ⟨c.state, rfl, hacc⟩

/-- A configuration from which the step condition fires can take a machine
step. -/
theorem step_of_goOn {c : Config A} (hgo : GoOn (cfgAssign c)) :
    ∃ d, (tmData A).Step c d := by
  classical
  obtain ⟨-, τ, p', ⟨htr, hsrcs, hreads⟩, ⟨q₀, hq₀⟩, ⟨a₀, ha₀⟩, p, hp, hmv⟩ := hgo
  rw [show p = c.head from hp] at hmv
  refine ⟨⟨q₀, p', fun r => if r = c.head then a₀ else c.tape r⟩, τ, htr,
    hsrcs c.state rfl, hreads c.head (c.tape c.head) rfl rfl, hq₀, ?_, ?_, hmv⟩
  · change TMWrite τ (if c.head = c.head then a₀ else c.tape c.head)
    rw [if_pos rfl]
    exact ha₀
  · intro r hr
    change (if r = c.head then a₀ else c.tape r) = c.tape r
    rw [if_neg hr]

omit [LinearOrder A] in
/-- On a non-accepting configuration that steps, the iteration takes **the**
machine step. -/
theorem mNextAssign_cfgAssign_of_step (hwf : (tmData A).WellFormed)
    (hdet : (tmData A).Deterministic) {c d : Config A}
    (hnacc : ¬(tmData A).Acc c.state) (hstep : (tmData A).Step c d) :
    mNextAssign (cfgAssign c) = cfgAssign d := by
  obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  have happl : ApplOn (cfgAssign c) τ :=
    ⟨htr, fun q hq => (show q = c.state from hq) ▸ hsrc, fun p a hp ha => by
      rw [show p = c.head from hp] at ha
      have ha' : c.tape c.head = a := ha
      exact ha' ▸ hread⟩
  have hgo : GoOn (cfgAssign c) :=
    ⟨fun ⟨q, hq, hacc⟩ => hnacc (hq ▸ hacc), τ, d.head, happl,
      ⟨d.state, hdst⟩, ⟨d.tape c.head, hwrite⟩, c.head, rfl, hmove⟩
  have hne := not_stateEmptyOn_cfgAssign c
  have happl_uniq : ∀ τ' : A, ApplOn (cfgAssign c) τ' → τ' = τ := by
    rintro τ' ⟨htr', hsrcs', hreads'⟩
    exact hdet.2.1 τ' τ c.state (c.tape c.head) htr' htr (hsrcs' c.state rfl) hsrc
      (hreads' c.head (c.tape c.head) rfl rfl) hread
  funext i x
  match i with
  | none =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨hng, -⟩ | ⟨-, ⟨hnh, ht⟩ | ⟨hh, τ', happl', hw⟩⟩⟩
      · exact absurd hSE hne
      · exact absurd hgo hng
      · change d.tape (x 0) = x 1
        rw [hframe (x 0) (fun hcon => hnh hcon)]
        exact ht
      · have heq := happl_uniq τ' happl'
        subst heq
        change d.tape (x 0) = x 1
        rw [show (x 0) = c.head from hh]
        exact hdet.2.2.2 τ' _ _ hwrite hw
    · rcases eq_or_ne (x 0) c.head with hx | hx
      · refine Or.inr ⟨hne, Or.inr ⟨hgo, Or.inr ⟨hx, τ, happl, ?_⟩⟩⟩
        rw [← (show d.tape (x 0) = x 1 from hh), hx]
        exact hwrite
      · refine Or.inr ⟨hne, Or.inr ⟨hgo, Or.inl ⟨hx, ?_⟩⟩⟩
        change c.tape (x 0) = x 1
        rw [← hframe (x 0) hx]
        exact hh
  | some false =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨hng, -⟩ | ⟨-, τ', happl', hd'⟩⟩
      · exact absurd hSE hne
      · exact absurd hgo hng
      · have heq := happl_uniq τ' happl'
        subst heq
        exact hdet.2.2.1 τ' _ _ hd' hdst
    · exact Or.inr ⟨hne, Or.inr ⟨hgo, τ, happl,
        (show (x 0) = d.state from hh) ▸ hdst⟩⟩
  | some true =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hh with ⟨hSE, -⟩ | ⟨-, ⟨hng, -⟩ | ⟨-, τ', happl', p, hp, hmv'⟩⟩
      · exact absurd hSE hne
      · exact absurd hgo hng
      · have heq := happl_uniq τ' happl'
        subst heq
        rw [show p = c.head from hp] at hmv'
        change (x 0) = d.head
        rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩ <;> rcases hmv' with ⟨hr', hs'⟩ | ⟨hr', hs'⟩
        · exact (TMData.succPos_right_unique hwf.1 hs' hs :)
        · exact absurd hr hr'
        · exact absurd hr' hr
        · exact (succPos_left_unique hwf.1 hs' hs :)
    · refine Or.inr ⟨hne, Or.inr ⟨hgo, τ, happl, c.head, rfl, ?_⟩⟩
      rw [show (x 0) = d.head from hh]
      exact hmove

omit [LinearOrder A] in
/-- The initial assignment of a well-formed deterministic instance with an
initial configuration is that configuration. -/
theorem mInitAssign_eq_cfgAssign (hwf : (tmData A).WellFormed)
    (hdet : (tmData A).Deterministic) {c₀ : Config A}
    (hinit : (tmData A).IsInit c₀) : mInitAssign A = cfgAssign c₀ := by
  funext i x
  match i with
  | none =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · exact TMData.initTape_functional hwf (hinit.2.2 (x 0))
        (show (tmData A).InitTape (x 0) (x 1) from hh)
    · change (tmData A).InitTape (x 0) (x 1)
      rw [← (show c₀.tape (x 0) = x 1 from hh)]
      exact hinit.2.2 (x 0)
  | some false =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · exact hdet.1 _ _ hh hinit.1
    · exact show TMStart (x 0) from (show (x 0) = c₀.state from hh) ▸ hinit.1
  | some true =>
    refine propext ⟨fun hh => ?_, fun hh => ?_⟩
    · exact hwf.1.2.2.1 _ _ (hh.2 c₀.head hinit.2.1.1) (hinit.2.1.2 (x 0) hh.1)
    · exact show MinPos TMLe TMPosn (x 0) from
        (show (x 0) = c₀.head from hh) ▸ hinit.2.1

/-- The first stage of the iteration is the initial assignment. -/
theorem partStage_one : mPfp.partStage A 1 = mInitAssign A :=
  (mPfp.partStage_succ 0).trans ((next_mPfp _).trans
    (mNextAssign_of_stateEmpty stateEmptyOn_botAssign))

/-- **The stages follow the run**: as long as no accepting configuration has
been reached, stage `n + 1` is the `n`-th configuration of the run. -/
theorem partStage_run (hwf : (tmData A).WellFormed) (hdet : (tmData A).Deterministic)
    {c₀ : Config A} (hinit : (tmData A).IsInit c₀) :
    ∀ n c, (tmData A).StepsIn n c₀ c →
      (∀ k, k < n → ∀ e, (tmData A).StepsIn k c₀ e → ¬(tmData A).Acc e.state) →
      mPfp.partStage A (n + 1) = cfgAssign c := by
  intro n
  induction n with
  | zero =>
    intro c hsteps _
    rw [← (show c₀ = c from hsteps)]
    exact partStage_one.trans (mInitAssign_eq_cfgAssign hwf hdet hinit)
  | succ n ih =>
    intro c hsteps hnoacc
    obtain ⟨d, hd, hstep⟩ := TMData.stepsIn_succ_iff.mp hsteps
    have hstage := ih d hd fun k hk => hnoacc k (by omega)
    rw [mPfp.partStage_succ, hstage, next_mPfp]
    exact mNextAssign_cfgAssign_of_step hwf hdet (hnoacc n (by omega) d hd) hstep

omit [LinearOrder A] in
/-- The run reaches a configuration in some number of steps. -/
theorem stepsIn_of_reflTransGen {c d : Config A}
    (h : Relation.ReflTransGen (tmData A).Step c d) :
    ∃ n, (tmData A).StepsIn n c d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, hn.trans_step hstep⟩

/-- The semantics of the output sentence. -/
theorem realize_mOut (ρ : mBlock.Assignment A) :
    (@Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ) mPfp.out) ↔
      ((tmData A).WellFormed ∧ ((tmData A).Deterministic ∧
        ∃ q : A, mState ρ q ∧ TMAcc q)) := by
  let := mBlock.structure₁ (L := mBase) ρ
  simp only [mPfp, Sentence.Realize, Formula.realize_inf, realize_wfF, realize_detF,
    realize_markMeetF, relMap_mIn₁, relMap_mS₁]
  exact Iff.rfl

/-- **A well-formed deterministic accepting instance makes the iteration
converge with an accepting output**: run to the first accepting configuration
and stutter there. -/
theorem pfpHolds_mPfp_of_acceptsSpace (hwf : (tmData A).WellFormed)
    (hdet : (tmData A).Deterministic) (hacc : (tmData A).AcceptsSpace) :
    mPfp.PFPHolds A := by
  obtain ⟨c₀, c, hinit, hreach, haccst⟩ := hacc
  have hex : ∃ n, ∃ cA : Config A,
      (tmData A).StepsIn n c₀ cA ∧ (tmData A).Acc cA.state := by
    obtain ⟨n, hn⟩ := stepsIn_of_reflTransGen hreach
    exact ⟨n, c, hn, haccst⟩
  have hmem : sInf {n | ∃ cA, (tmData A).StepsIn n c₀ cA ∧ (tmData A).Acc cA.state} ∈
      {n | ∃ cA, (tmData A).StepsIn n c₀ cA ∧ (tmData A).Acc cA.state} :=
    Nat.sInf_mem hex
  obtain ⟨cA, hsteps, haccA⟩ := hmem
  have hnoacc : ∀ k, k < sInf {n | ∃ cA, (tmData A).StepsIn n c₀ cA ∧
      (tmData A).Acc cA.state} → ∀ e, (tmData A).StepsIn k c₀ e →
      ¬(tmData A).Acc e.state := by
    intro k hk e hst hacce
    have hmem : k ∈ {n | ∃ cA, (tmData A).StepsIn n c₀ cA ∧ (tmData A).Acc cA.state} :=
      ⟨e, hst, hacce⟩
    exact absurd (Nat.sInf_le hmem) (by omega)
  have hstage := partStage_run hwf hdet hinit _ cA hsteps hnoacc
  refine ⟨sInf {n | ∃ cA, (tmData A).StepsIn n c₀ cA ∧ (tmData A).Acc cA.state} + 1,
    ?_, ?_⟩
  · have h : mPfp.next (mPfp.partStage A (sInf {n | ∃ cA, (tmData A).StepsIn n c₀ cA ∧
        (tmData A).Acc cA.state} + 1)) = mPfp.partStage A (sInf {n | ∃ cA,
        (tmData A).StepsIn n c₀ cA ∧ (tmData A).Acc cA.state} + 1) := by
      rw [hstage, next_mPfp]
      exact mNextAssign_cfgAssign_of_acc haccA
    exact h
  · rw [hstage]
    exact (realize_mOut (cfgAssign cA)).mpr ⟨hwf, hdet, cA.state, rfl, haccA⟩

/-- **A converging accepting iteration means the instance is well-formed,
deterministic and accepting**: the stages only ever hold the empty
assignment, the initial assignment, or a configuration of the run. -/
theorem acceptsSpace_of_pfpHolds_mPfp [Finite A] (h : mPfp.PFPHolds A) :
    ((tmData A).WellFormed ∧ ((tmData A).Deterministic ∧
      (tmData A).AcceptsSpace)) := by
  obtain ⟨n, -, hout⟩ := h
  obtain ⟨hwf, hdet, q, hq, hqacc⟩ := (realize_mOut _).mp hout
  by_cases hstart : ∃ q₀ : A, TMStart q₀
  · obtain ⟨q₀, hq₀⟩ := hstart
    obtain ⟨c₀, hinit, -⟩ := TMData.exists_isInit hwf hq₀
    have hinv : ∀ m, mPfp.partStage A m = mBlock.botAssign A ∨
        ∃ k c, (tmData A).StepsIn k c₀ c ∧ mPfp.partStage A m = cfgAssign c := by
      intro m
      induction m with
      | zero => exact Or.inl rfl
      | succ m ihm =>
        rcases ihm with hm | ⟨k, c, hkc, hm⟩ <;> rw [mPfp.partStage_succ, hm, next_mPfp]
        · exact Or.inr ⟨0, c₀, rfl, (mNextAssign_of_stateEmpty
            stateEmptyOn_botAssign).trans (mInitAssign_eq_cfgAssign hwf hdet hinit)⟩
        · by_cases hgo : GoOn (cfgAssign c)
          · obtain ⟨d, hd⟩ := step_of_goOn hgo
            refine Or.inr ⟨k + 1, d, hkc.trans_step hd, ?_⟩
            exact mNextAssign_cfgAssign_of_step hwf hdet
              (fun hacc => hgo.1 ⟨c.state, rfl, hacc⟩) hd
          · exact Or.inr ⟨k, c, hkc, mNextAssign_cfgAssign_of_not_goOn hgo⟩
    rcases hinv n with hn | ⟨k, c, hkc, hn⟩
    · rw [hn] at hq
      exact hq.elim
    · rw [hn] at hq
      exact ⟨hwf, hdet, c₀, c, hinit, TMData.reflTransGen_of_stepsIn hkc,
        (show q = c.state from hq) ▸ hqacc⟩
  · have hstages : ∀ m, mPfp.partStage A m = mBlock.botAssign A ∨
        mPfp.partStage A m = mInitAssign A := by
      intro m
      induction m with
      | zero => exact Or.inl rfl
      | succ m ihm =>
        rcases ihm with hm | hm <;> rw [mPfp.partStage_succ, hm, next_mPfp]
        · exact Or.inr (mNextAssign_of_stateEmpty stateEmptyOn_botAssign)
        · exact Or.inr (mNextAssign_of_stateEmpty fun ⟨q', hq'⟩ => hstart ⟨q', hq'⟩)
    rcases hstages n with hn | hn <;> rw [hn] at hq
    · exact hq.elim
    · exact absurd ⟨q, hq⟩ hstart

end Run

end SpaceTM

open SpaceTM

/-! ### The capture theorem -/

/-- **The deterministic space-bounded machine problem is FO(≤, PFP)
definable**: iterate the machine, stuttering on halting configurations. -/
theorem dtmAcceptSpace_pfpDefinable : PFPDefinable DTMAcceptSpace := by
  refine ⟨mPfp, ?_⟩
  intro A _ _ _ _
  constructor
  · rintro ⟨hwf, hdet, hacc⟩
    exact pfpHolds_mPfp_of_acceptsSpace hwf hdet hacc
  · intro h
    exact acceptsSpace_of_pfpHolds_mPfp h

/-- **PSPACE is contained in FO(≤, PFP)**: reduce to the machine problem and
pull the iteration back through the relativized reduction. -/
theorem pfpDefinable_of_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : P ∈ PSPACE) : PFPDefinable P := by
  obtain ⟨f⟩ := le_dtmAcceptSpace_of_mem_PSPACE P h
  exact PFPDefinable.of_relOrderedReduction f dtmAcceptSpace_pfpDefinable

/-- **The capture theorem FO(≤, PFP) = PSPACE** ([Abiteboul–Vianu
1989][abiteboul1989fixpoint]; [Ebbinghaus–Flum 1995][ebbinghaus1995finite],
ch. 7): a problem is FO(≤, PFP) definable exactly when it is in PSPACE. -/
theorem pfpDefinable_iff_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    PFPDefinable P ↔ P ∈ PSPACE :=
  ⟨mem_PSPACE_of_pfpDefinable, pfpDefinable_of_mem_PSPACE⟩

/-- The capture theorem, logic to logic: FO(≤, PFP) and SO(TC) define the
same problems. -/
theorem pfpDefinable_iff_sotcDefinable {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    PFPDefinable P ↔ SOTCDefinable P :=
  (pfpDefinable_iff_mem_PSPACE P).trans (mem_PSPACE_iff P)

end DescriptiveComplexity
