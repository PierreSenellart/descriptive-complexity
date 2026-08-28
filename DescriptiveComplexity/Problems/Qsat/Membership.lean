/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Set.Card
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Qsat.Defs

/-!
# QSAT is in PSPACE

The membership half: the truth of a fully quantified Boolean formula is SO(TC)
definable, hence in `DescriptiveComplexity.PSPACE`.

The walk is the classical depth-first evaluation of the game tree, which is
where the polynomial space of PSPACE is spent: the stack is a *set* of
variables, and a set is one monadic relation variable. Four relation variables
make up a state:

* `D` (unary) – the variables already given a value, i.e., the current branch of
  the game tree; the variable played next is the `prefixLt`-least one outside
  `D` (`DescriptiveComplexity.QLeast`) and the one returned to is the greatest one inside
  it;
* `T` (unary) – the values they were given;
* `up` (nullary – a relation variable of arity `0` is a bit) – the mode:
  descending towards a leaf, or returning a value;
* `res` (nullary) – the value being returned.

No accumulator is needed, and that is what keeps the transition sentence
short: the evaluation *short-circuits*. Having returned the value `v` of the
first branch of a variable `x`, the walk pops `x` immediately when `v` already
settles the node (`v` true at an existential `x`, `v` false at a universal one)
and otherwise plays the second branch, whose value is then the value of the
node. So a value is never combined with a remembered one, and each of the four
transitions merely edits the state
(`DescriptiveComplexity.qsSpec_step_iff`).

## Why the walk computes the game value

The transition relation is *deterministic*
(`DescriptiveComplexity.qsSpec_step_unique`), and the run started at a position
`(D, τ)` in descending mode comes back to `D` in returning mode carrying
exactly `QsatWins D τ` (`DescriptiveComplexity.qsSpec_run`, by induction on the number
of variables outside `D`). Determinism turns that into an equivalence: the
returning state at `D = ∅` is a dead end, and two dead ends reachable from one
state coincide, so a walk accepting the specification has to be *the* run.

Well-formedness is checked by the source sentence, so a malformed instance –
where the prefix order is not a linear order on the variables, and neither the
next nor the last variable of a position need exist – has no starting state at
all.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Generic sentence shapes

Each shape is built over an arbitrary vocabulary and an arbitrary variable
type, so that the same builder and the same realization lemma serve the
current copy of the block, the next one, and the nesting inside a quantifier. -/

section Shapes

variable {L' : Language.{0, 0}} {γ M : Type} [L'.Structure M]

/-- A relation variable of arity `0` read as a formula: a propositional bit. -/
def bitF (R : L'.Relations 0) : L'.Formula γ :=
  R.formula (Fin.elim0 : Fin 0 → L'.Term γ)

theorem realize_bitF (R : L'.Relations 0) (v : γ → M) :
    (bitF R).Realize v ↔ RelMap R (![] : Fin 0 → M) := by
  rw [bitF, Formula.realize_rel]
  exact iff_of_eq (congrArg (RelMap R) (Subsingleton.elim _ _))

theorem realize_bitS (R : L'.Relations 0) :
    M ⊨ (bitF R : L'.Sentence) ↔ RelMap R (![] : Fin 0 → M) :=
  realize_bitF R default

/-- “`x` is marked, lies outside `d`, and no marked element outside `d`
precedes it”: the element a position plays next. -/
noncomputable def leastF (mark d : L'.Relations 1) (prec : L'.Relations 2)
    (x : γ) : L'.Formula γ :=
  fo%[x] (mark(x) ∧ ¬ d(x)) ∧ ∀ y, mark(y) ∧ ¬ d(y) → ¬ prec(y, x)

theorem realize_leastF (mark d : L'.Relations 1) (prec : L'.Relations 2)
    (x : γ) (v : γ → M) :
    (leastF mark d prec x).Realize v ↔
      (RelMap mark ![v x] ∧ ¬RelMap d ![v x] ∧
        ∀ y : M, RelMap mark ![y] → ¬RelMap d ![y] → ¬RelMap prec ![y, v x]) := by
  rw [leastF]
  simp only [Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_iAlls, Formula.realize_imp, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h y hy hd => ?_, fun h i hi => ?_⟩)
  · exact h (fun _ => y) ⟨hy, hd⟩
  · exact h (i 0) hi.1 hi.2

/-- “`x` is marked, lies inside `d`, and precedes no marked element of `d`”:
the element a position returns to. -/
noncomputable def greatestF (mark d : L'.Relations 1) (prec : L'.Relations 2)
    (x : γ) : L'.Formula γ :=
  fo%[x] (mark(x) ∧ d(x)) ∧ ∀ y, mark(y) ∧ d(y) → ¬ prec(x, y)

theorem realize_greatestF (mark d : L'.Relations 1) (prec : L'.Relations 2)
    (x : γ) (v : γ → M) :
    (greatestF mark d prec x).Realize v ↔
      (RelMap mark ![v x] ∧ RelMap d ![v x] ∧
        ∀ y : M, RelMap mark ![y] → RelMap d ![y] → ¬RelMap prec ![v x, y]) := by
  rw [greatestF]
  simp only [Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_iAlls, Formula.realize_imp, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h y hy hd => ?_, fun h i hi => ?_⟩)
  · exact h (fun _ => y) ⟨hy, hd⟩
  · exact h (i 0) hi.1 hi.2

/-- “Every marked element lies in `d`”: the position is a leaf. -/
noncomputable def coveredF (mark d : L'.Relations 1) : L'.Formula γ :=
  fo% ∀ y, mark(y) → d(y)

theorem realize_coveredF (mark d : L'.Relations 1) (v : γ → M) :
    (coveredF (γ := γ) mark d).Realize v ↔ ∀ y : M, RelMap mark ![y] → RelMap d ![y] := by
  rw [coveredF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h y hy => h (fun _ => y) hy, fun h i hi => h (i 0) hi⟩

/-- “No element lies in `d`”. -/
noncomputable def emptyF (d : L'.Relations 1) : L'.Formula γ :=
  fo% ∀ y, ¬ d(y)

theorem realize_emptyF (d : L'.Relations 1) (v : γ → M) :
    (emptyF (γ := γ) d).Realize v ↔ ∀ y : M, ¬RelMap d ![y] := by
  rw [emptyF]
  simp only [Formula.realize_iAlls, Formula.realize_not, Formula.realize_rel₁, Term.realize_var]
  exact ⟨fun h y => h fun _ => y, fun h i => h (i 0)⟩

/-- The matrix: every clause holds a literal on a marked element that `t`
makes true. -/
noncomputable def matrixF (cl mark : L'.Relations 1) (pos neg : L'.Relations 2)
    (t : L'.Relations 1) : L'.Formula γ :=
  fo% ∀ c, cl(c) → ∃ y, mark(y) ∧ ((pos(c, y) ∧ t(y)) ∨ (neg(c, y) ∧ ¬ t(y)))

theorem realize_matrixF (cl mark : L'.Relations 1) (pos neg : L'.Relations 2)
    (t : L'.Relations 1) (v : γ → M) :
    (matrixF (γ := γ) cl mark pos neg t).Realize v ↔
      ∀ c : M, RelMap cl ![c] → ∃ y : M, RelMap mark ![y] ∧
        ((RelMap pos ![c, y] ∧ RelMap t ![y]) ∨ (RelMap neg ![c, y] ∧ ¬RelMap t ![y])) := by
  rw [matrixF]
  simp only [Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_sup, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  constructor
  · intro h c hc
    obtain ⟨y, hy⟩ := h (fun _ => c) hc
    exact ⟨y 0, hy⟩
  · intro h i hc
    obtain ⟨y, hy⟩ := h (i 0) hc
    exact ⟨fun _ => y, hy⟩

/-- “`a'` holds of `y` exactly when `a` does”: an unchanged component. -/
def sameF (a' a : L'.Relations 1) (y : γ) : L'.Formula γ :=
  (Relations.formula₁ a' (Term.var y)).iff (Relations.formula₁ a (Term.var y))

theorem realize_sameF (a' a : L'.Relations 1) (y : γ) (v : γ → M) :
    (sameF a' a y).Realize v ↔ (RelMap a' ![v y] ↔ RelMap a ![v y]) := by
  rw [sameF]
  simp only [Formula.realize_iff, Formula.realize_rel₁, Term.realize_var]

/-- “`a'` is `a` with the value of `x` set to `φ`”: the one update shape the
walk needs – adding `x` (`φ = ⊤`) and removing it (`φ = ⊥`). -/
def updF (a' a : L'.Relations 1) (φ : L'.Formula γ) (x y : γ) : L'.Formula γ :=
  (Relations.formula₁ a' (Term.var y)).iff
    (((Term.var y).equal (Term.var x) ⊓ φ) ⊔
      (∼((Term.var y).equal (Term.var x)) ⊓ Relations.formula₁ a (Term.var y)))

theorem realize_updF (a' a : L'.Relations 1) (φ : L'.Formula γ) (x y : γ) (v : γ → M) :
    (updF a' a φ x y).Realize v ↔
      (RelMap a' ![v y] ↔ ((v y = v x ∧ φ.Realize v) ∨ (v y ≠ v x ∧ RelMap a ![v y]))) := by
  rw [updF]
  simp only [Formula.realize_iff, Formula.realize_rel₁, Formula.realize_sup,
    Formula.realize_inf, Formula.realize_not, Formula.realize_equal, Term.realize_var]

/-! #### Well-formedness

The prefix order is a strict linear order on the marked elements. -/

/-- The prefix order only relates marked elements. -/
noncomputable def wfMarkedF (mark : L'.Relations 1) (prec : L'.Relations 2) : L'.Formula γ :=
  fo% ∀ x y, prec(x, y) → mark(x) ∧ mark(y)

/-- The prefix order is irreflexive. -/
noncomputable def wfIrreflF (prec : L'.Relations 2) : L'.Formula γ :=
  fo% ∀ x, ¬ prec(x, x)

/-- The prefix order is transitive. -/
noncomputable def wfTransF (prec : L'.Relations 2) : L'.Formula γ :=
  fo% ∀ x y z, prec(x, y) ∧ prec(y, z) → prec(x, z)

/-- The prefix order is total on the marked elements. -/
noncomputable def wfTotalF (mark : L'.Relations 1) (prec : L'.Relations 2) : L'.Formula γ :=
  fo% ∀ x y, (mark(x) ∧ mark(y)) ∧ ¬ x ≐ y → prec(x, y) ∨ prec(y, x)

/-- The instance is well formed: the prefix order is a strict linear order on
the marked elements. -/
noncomputable def wfF (mark : L'.Relations 1) (prec : L'.Relations 2) : L'.Formula γ :=
  wfMarkedF mark prec ⊓ wfIrreflF prec ⊓ wfTransF prec ⊓ wfTotalF mark prec

theorem realize_wfF (mark : L'.Relations 1) (prec : L'.Relations 2) (v : γ → M) :
    (wfF (γ := γ) mark prec).Realize v ↔
      ((∀ x y : M, RelMap prec ![x, y] → RelMap mark ![x] ∧ RelMap mark ![y]) ∧
        (∀ x : M, ¬RelMap prec ![x, x]) ∧
        (∀ x y z : M, RelMap prec ![x, y] → RelMap prec ![y, z] → RelMap prec ![x, z]) ∧
        (∀ x y : M, RelMap mark ![x] → RelMap mark ![y] → x ≠ y →
          RelMap prec ![x, y] ∨ RelMap prec ![y, x])) := by
  rw [wfF, wfMarkedF, wfIrreflF, wfTransF, wfTotalF]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_sup, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun x y hxy => ?_, fun x => ?_, fun x y z hxy hyz => ?_, fun x y hx hy hne => ?_⟩
    · simpa using h1 ![x, y] (by simpa using hxy)
    · simpa using h2 fun _ => x
    · simpa using h3 ![x, y, z] ⟨by simpa using hxy, by simpa using hyz⟩
    · simpa using h4 ![x, y] ⟨by simpa using hx, by simpa using hy, by simpa using hne⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i hi => h1 (i 0) (i 1) hi, fun i => h2 (i 0), fun i hi => h3 (i 0) (i 1) (i 2)
      hi.1 hi.2, fun i hi => h4 (i 0) (i 1) hi.1 hi.2.1 hi.2.2⟩

theorem realize_wfS (mark : L'.Relations 1) (prec : L'.Relations 2) :
    M ⊨ (wfF mark prec : L'.Sentence) ↔
      ((∀ x y : M, RelMap prec ![x, y] → RelMap mark ![x] ∧ RelMap mark ![y]) ∧
        (∀ x : M, ¬RelMap prec ![x, x]) ∧
        (∀ x y z : M, RelMap prec ![x, y] → RelMap prec ![y, z] → RelMap prec ![x, z]) ∧
        (∀ x y : M, RelMap mark ![x] → RelMap mark ![y] → x ≠ y →
          RelMap prec ![x, y] ∨ RelMap prec ![y, x])) :=
  realize_wfF mark prec default

theorem realize_emptyS (d : L'.Relations 1) :
    M ⊨ (emptyF d : L'.Sentence) ↔ ∀ y : M, ¬RelMap d ![y] :=
  realize_emptyF d default

end Shapes

/-! ### The nine conjuncts of the transition sentence

One conjunct per case of the walk and per kind of component: the two unary
components are edited under a `∀ x y`, the two bits under a `∀ x`. All are
built over an arbitrary vocabulary, with the current copy of the block (`d`,
`t`, `u`, `r`) and the next one (`d'`, `t'`, `u'`, `r'`) as parameters. -/

section StepShapes

variable {L' : Language.{0, 0}} {M : Type} [L'.Structure M]

/-- “The subtree of `x` is finished”: either its second value has been played
already, or the value just returned settles the node – true at an existential
`x`, false at a universal one. -/
def popF (allv t : L'.Relations 1) (r : L'.Relations 0) {γ : Type} (x : γ) : L'.Formula γ :=
  Relations.formula₁ t (Term.var x) ⊔
    ((Relations.formula₁ allv (Term.var x) ⊓ ∼(bitF r)) ⊔
      (∼(Relations.formula₁ allv (Term.var x)) ⊓ bitF r))

theorem realize_popF (allv t : L'.Relations 1) (r : L'.Relations 0) {γ : Type}
    (x : γ) (v : γ → M) :
    (popF allv t r x).Realize v ↔
      (RelMap t ![v x] ∨
        ((RelMap allv ![v x] ∧ ¬RelMap r (![] : Fin 0 → M)) ∨
          (¬RelMap allv ![v x] ∧ RelMap r (![] : Fin 0 → M)))) := by
  rw [popF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, realize_bitF, Term.realize_var]

/-- Descending one step: the next variable joins the quantified set with the
value `false`. -/
noncomputable def downSetS (mark d t d' t' : L'.Relations 1) (prec : L'.Relations 2) :
    L'.Sentence :=
  fo% ∀ x y, (leastF mark d prec)⟨x⟩ → (updF d' d ⊤)⟨x, y⟩ ∧ (updF t' t ⊥)⟨x, y⟩

theorem realize_downSetS (mark d t d' t' : L'.Relations 1) (prec : L'.Relations 2) :
    M ⊨ downSetS mark d t d' t' prec ↔
      ∀ x y : M, (RelMap mark ![x] ∧ ¬RelMap d ![x] ∧
          ∀ z : M, RelMap mark ![z] → ¬RelMap d ![z] → ¬RelMap prec ![z, x]) →
        ((RelMap d' ![y] ↔ ((y = x ∧ True) ∨ (y ≠ x ∧ RelMap d ![y]))) ∧
          (RelMap t' ![y] ↔ ((y = x ∧ False) ∨ (y ≠ x ∧ RelMap t ![y])))) := by
  rw [downSetS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    realize_leastF, realize_updF, Sum.elim_inr, Formula.realize_top,
    Formula.realize_bot]
  exact ⟨fun h x y => h ![x, y], fun h i => h (i 0) (i 1)⟩

/-- Descending one step: the mode stays descending and the value is carried
along. -/
noncomputable def downBitsS (mark d : L'.Relations 1) (prec : L'.Relations 2)
    (u' r' r : L'.Relations 0) : L'.Sentence :=
  fo% ∀ x, (leastF mark d prec)⟨x⟩ → ¬ !(bitF u') ∧ (!(bitF r') ↔ !(bitF r))

theorem realize_downBitsS (mark d : L'.Relations 1) (prec : L'.Relations 2)
    (u' r' r : L'.Relations 0) :
    M ⊨ downBitsS mark d prec u' r' r ↔
      ∀ x : M, (RelMap mark ![x] ∧ ¬RelMap d ![x] ∧
          ∀ z : M, RelMap mark ![z] → ¬RelMap d ![z] → ¬RelMap prec ![z, x]) →
        (¬RelMap u' (![] : Fin 0 → M) ∧
          (RelMap r' (![] : Fin 0 → M) ↔ RelMap r (![] : Fin 0 → M))) := by
  rw [downBitsS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_not, Formula.realize_iff, realize_leastF, realize_bitF, Sum.elim_inr]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

/-- At a leaf the two unary components are unchanged. -/
noncomputable def leafSetS (mark d t d' t' : L'.Relations 1) : L'.Sentence :=
  fo% !(coveredF mark d) → ∀ y, (sameF d' d)⟨y⟩ ∧ (sameF t' t)⟨y⟩

theorem realize_leafSetS (mark d t d' t' : L'.Relations 1) :
    M ⊨ leafSetS mark d t d' t' ↔
      ((∀ z : M, RelMap mark ![z] → RelMap d ![z]) →
        ∀ y : M, (RelMap d' ![y] ↔ RelMap d ![y]) ∧ (RelMap t' ![y] ↔ RelMap t ![y])) := by
  rw [leafSetS]
  simp only [Sentence.Realize, Formula.realize_imp, Formula.realize_iAlls, Formula.realize_inf,
    realize_coveredF, realize_sameF, Sum.elim_inr]
  exact ⟨fun h hc y => h hc fun _ => y, fun h hc i => h hc (i 0)⟩

/-- At a leaf the walk starts returning, carrying the value of the matrix. -/
noncomputable def leafBitsS (cl mark d t : L'.Relations 1) (pos neg : L'.Relations 2)
    (u' r' : L'.Relations 0) : L'.Sentence :=
  (coveredF mark d).imp (bitF u' ⊓ (bitF r').iff (matrixF cl mark pos neg t))

theorem realize_leafBitsS (cl mark d t : L'.Relations 1) (pos neg : L'.Relations 2)
    (u' r' : L'.Relations 0) :
    M ⊨ leafBitsS cl mark d t pos neg u' r' ↔
      ((∀ z : M, RelMap mark ![z] → RelMap d ![z]) →
        (RelMap u' (![] : Fin 0 → M) ∧
          (RelMap r' (![] : Fin 0 → M) ↔
            ∀ c : M, RelMap cl ![c] → ∃ y : M, RelMap mark ![y] ∧
              ((RelMap pos ![c, y] ∧ RelMap t ![y]) ∨
                (RelMap neg ![c, y] ∧ ¬RelMap t ![y]))))) := by
  rw [leafBitsS]
  simp only [Sentence.Realize, Formula.realize_imp, Formula.realize_inf, Formula.realize_iff,
    realize_coveredF, realize_bitF, realize_matrixF]

/-- Returning is only possible from a nonempty branch. -/
noncomputable def upExS (mark d : L'.Relations 1) (prec : L'.Relations 2) : L'.Sentence :=
  fo% ∃ x, (greatestF mark d prec)⟨x⟩

theorem realize_upExS (mark d : L'.Relations 1) (prec : L'.Relations 2) :
    M ⊨ upExS mark d prec ↔
      ∃ x : M, RelMap mark ![x] ∧ RelMap d ![x] ∧
        ∀ z : M, RelMap mark ![z] → RelMap d ![z] → ¬RelMap prec ![x, z] := by
  rw [upExS]
  simp only [Sentence.Realize, Formula.realize_iExs, realize_greatestF, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩⟩

/-- Popping a finished variable: it leaves the quantified set, the values are
unchanged. -/
noncomputable def popSetS (mark allv d t d' t' : L'.Relations 1) (prec : L'.Relations 2)
    (r : L'.Relations 0) : L'.Sentence :=
  fo% ∀ x y, (greatestF mark d prec)⟨x⟩ ∧ (popF allv t r)⟨x⟩ →
    (updF d' d ⊥)⟨x, y⟩ ∧ (sameF t' t)⟨y⟩

/-- Playing the second value of an unfinished variable. -/
noncomputable def flipSetS (mark allv d t d' t' : L'.Relations 1) (prec : L'.Relations 2)
    (r : L'.Relations 0) : L'.Sentence :=
  fo% ∀ x y, (greatestF mark d prec)⟨x⟩ ∧ ¬ (popF allv t r)⟨x⟩ →
    (sameF d' d)⟨y⟩ ∧ (updF t' t ⊤)⟨x, y⟩

/-- Popping a finished variable: the walk keeps returning, with the same
value. -/
noncomputable def popBitsS (mark allv d t : L'.Relations 1) (prec : L'.Relations 2)
    (u' r' r : L'.Relations 0) : L'.Sentence :=
  fo% ∀ x, (greatestF mark d prec)⟨x⟩ ∧ (popF allv t r)⟨x⟩ →
    !(bitF u') ∧ (!(bitF r') ↔ !(bitF r))

/-- Playing the second value: the walk goes back to descending. -/
noncomputable def flipBitsS (mark allv d t : L'.Relations 1) (prec : L'.Relations 2)
    (u' r' r : L'.Relations 0) : L'.Sentence :=
  fo% ∀ x, (greatestF mark d prec)⟨x⟩ ∧ ¬ (popF allv t r)⟨x⟩ →
    ¬ !(bitF u') ∧ (!(bitF r') ↔ !(bitF r))

/-- The shared guard of the two returning cases: `x` is the last variable of
the branch. -/
private def isLastM (mark d : L'.Relations 1) (prec : L'.Relations 2) (x : M) : Prop :=
  RelMap mark ![x] ∧ RelMap d ![x] ∧
    ∀ z : M, RelMap mark ![z] → RelMap d ![z] → ¬RelMap prec ![x, z]

/-- The shared guard of the two returning cases: the subtree of `x` is
finished. -/
private def isPopM (allv t : L'.Relations 1) (r : L'.Relations 0) (x : M) : Prop :=
  RelMap t ![x] ∨ ((RelMap allv ![x] ∧ ¬RelMap r (![] : Fin 0 → M)) ∨
    (¬RelMap allv ![x] ∧ RelMap r (![] : Fin 0 → M)))

theorem realize_popSetS (mark allv d t d' t' : L'.Relations 1) (prec : L'.Relations 2)
    (r : L'.Relations 0) :
    M ⊨ popSetS mark allv d t d' t' prec r ↔
      ∀ x y : M, isLastM mark d prec x → isPopM allv t r x →
        ((RelMap d' ![y] ↔ ((y = x ∧ False) ∨ (y ≠ x ∧ RelMap d ![y]))) ∧
          (RelMap t' ![y] ↔ RelMap t ![y])) := by
  rw [popSetS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    realize_greatestF, realize_popF, realize_updF, realize_sameF, Sum.elim_inr,
    Formula.realize_bot, isLastM, isPopM, and_imp]
  exact ⟨fun h x y => h ![x, y], fun h i => h (i 0) (i 1)⟩

theorem realize_flipSetS (mark allv d t d' t' : L'.Relations 1) (prec : L'.Relations 2)
    (r : L'.Relations 0) :
    M ⊨ flipSetS mark allv d t d' t' prec r ↔
      ∀ x y : M, isLastM mark d prec x → ¬isPopM allv t r x →
        ((RelMap d' ![y] ↔ RelMap d ![y]) ∧
          (RelMap t' ![y] ↔ ((y = x ∧ True) ∨ (y ≠ x ∧ RelMap t ![y])))) := by
  rw [flipSetS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_not, realize_greatestF, realize_popF, realize_updF, realize_sameF,
    Sum.elim_inr, Formula.realize_top, isLastM, isPopM, and_imp]
  exact ⟨fun h x y => h ![x, y], fun h i => h (i 0) (i 1)⟩

theorem realize_popBitsS (mark allv d t : L'.Relations 1) (prec : L'.Relations 2)
    (u' r' r : L'.Relations 0) :
    M ⊨ popBitsS mark allv d t prec u' r' r ↔
      ∀ x : M, isLastM mark d prec x → isPopM allv t r x →
        (RelMap u' (![] : Fin 0 → M) ∧
          (RelMap r' (![] : Fin 0 → M) ↔ RelMap r (![] : Fin 0 → M))) := by
  rw [popBitsS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_iff, realize_greatestF, realize_popF, realize_bitF,
    Sum.elim_inr, isLastM, isPopM, and_imp]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

theorem realize_flipBitsS (mark allv d t : L'.Relations 1) (prec : L'.Relations 2)
    (u' r' r : L'.Relations 0) :
    M ⊨ flipBitsS mark allv d t prec u' r' r ↔
      ∀ x : M, isLastM mark d prec x → ¬isPopM allv t r x →
        (¬RelMap u' (![] : Fin 0 → M) ∧
          (RelMap r' (![] : Fin 0 → M) ↔ RelMap r (![] : Fin 0 → M))) := by
  rw [flipBitsS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_iff, Formula.realize_not, realize_greatestF, realize_popF, realize_bitF,
    Sum.elim_inr, isLastM, isPopM, and_imp]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

end StepShapes

/-! ### The block and the vocabularies -/

section Spec

/-- The block of the SO(TC) specification of QSAT: two unary relation
variables – the quantified set and the values it gave – and two relation
variables of arity `0`, i.e., two bits – the mode and the value being
returned. -/
abbrev qsBlock : SOBlock where
  ι := Bool ⊕ Bool
  arity := fun i => match i with | Sum.inl _ => 1 | Sum.inr _ => 0

/-- The unary relation variable of index `i`: the quantified set at `false`,
the valuation at `true`. -/
def qsSym₁ (i : Bool) : qsBlock.lang.Relations 1 := ⟨Sum.inl i, rfl⟩

/-- The nullary relation variable of index `i`: the mode at `false`, the value
being returned at `true`. -/
def qsSym₀ (i : Bool) : qsBlock.lang.Relations 0 := ⟨Sum.inr i, rfl⟩

/-- The input vocabulary together with the order, over which the sentences of
an SO(TC) specification live. -/
abbrev qsBase : Language := Language.qsat.sum Language.order

/-- The vocabulary of the endpoint sentences: one copy of the block. -/
abbrev qsLang₁ : Language := qsBase.sum qsBlock.lang

/-- The vocabulary of the transition sentence: two copies of the block. -/
abbrev qsLang₂ : Language := qsLang₁.sum qsBlock.lang

/-- An input symbol, in the endpoint vocabulary. -/
abbrev qsIn₁ {n : ℕ} (r : Language.qsat.Relations n) : qsLang₁.Relations n := Sum.inl (Sum.inl r)

/-- A unary relation variable, in the endpoint vocabulary. -/
abbrev qsVar₁ (i : Bool) : qsLang₁.Relations 1 := Sum.inr (qsSym₁ i)

/-- A bit of the block, in the endpoint vocabulary. -/
abbrev qsBit₁ (i : Bool) : qsLang₁.Relations 0 := Sum.inr (qsSym₀ i)

/-- An input symbol, in the transition vocabulary. -/
abbrev qsIn₂ {n : ℕ} (r : Language.qsat.Relations n) : qsLang₂.Relations n :=
  Sum.inl (Sum.inl (Sum.inl r))

/-- A unary relation variable of the *current* state. -/
abbrev qsCur₂ (i : Bool) : qsLang₂.Relations 1 := Sum.inl (Sum.inr (qsSym₁ i))

/-- A bit of the *current* state. -/
abbrev qsCurBit₂ (i : Bool) : qsLang₂.Relations 0 := Sum.inl (Sum.inr (qsSym₀ i))

/-- A unary relation variable of the *next* state. -/
abbrev qsNext₂ (i : Bool) : qsLang₂.Relations 1 := Sum.inr (qsSym₁ i)

/-- A bit of the *next* state. -/
abbrev qsNextBit₂ (i : Bool) : qsLang₂.Relations 0 := Sum.inr (qsSym₀ i)

/-- **The SO(TC) specification of QSAT**: the depth-first evaluation of the
game tree. Descending, the walk plays the next variable with the value
`false`, or – at a leaf – turns round carrying the value of the matrix;
returning, it pops the last variable when its subtree is settled and otherwise
plays its second value. -/
noncomputable def qsSpec : SOTCSpec Language.qsat where
  B := qsBlock
  step :=
    (∼(bitF (qsCurBit₂ false))).imp
        (downSetS (qsIn₂ qsIsVar) (qsCur₂ false) (qsCur₂ true) (qsNext₂ false) (qsNext₂ true)
              (qsIn₂ qsPrefixLt) ⊓
            downBitsS (qsIn₂ qsIsVar) (qsCur₂ false) (qsIn₂ qsPrefixLt) (qsNextBit₂ false)
              (qsNextBit₂ true) (qsCurBit₂ true) ⊓
          (leafSetS (qsIn₂ qsIsVar) (qsCur₂ false) (qsCur₂ true) (qsNext₂ false)
              (qsNext₂ true) ⊓
            leafBitsS (qsIn₂ qsIsClause) (qsIn₂ qsIsVar) (qsCur₂ false) (qsCur₂ true)
              (qsIn₂ qsPosIn) (qsIn₂ qsNegIn) (qsNextBit₂ false) (qsNextBit₂ true))) ⊓
      (bitF (qsCurBit₂ false)).imp
        (upExS (qsIn₂ qsIsVar) (qsCur₂ false) (qsIn₂ qsPrefixLt) ⊓
          ((popSetS (qsIn₂ qsIsVar) (qsIn₂ qsAllVar) (qsCur₂ false) (qsCur₂ true)
                (qsNext₂ false) (qsNext₂ true) (qsIn₂ qsPrefixLt) (qsCurBit₂ true) ⊓
              popBitsS (qsIn₂ qsIsVar) (qsIn₂ qsAllVar) (qsCur₂ false) (qsCur₂ true)
                (qsIn₂ qsPrefixLt) (qsNextBit₂ false) (qsNextBit₂ true) (qsCurBit₂ true)) ⊓
            (flipSetS (qsIn₂ qsIsVar) (qsIn₂ qsAllVar) (qsCur₂ false) (qsCur₂ true)
                (qsNext₂ false) (qsNext₂ true) (qsIn₂ qsPrefixLt) (qsCurBit₂ true) ⊓
              flipBitsS (qsIn₂ qsIsVar) (qsIn₂ qsAllVar) (qsCur₂ false) (qsCur₂ true)
                (qsIn₂ qsPrefixLt) (qsNextBit₂ false) (qsNextBit₂ true) (qsCurBit₂ true))))
  src :=
    wfF (qsIn₁ qsIsVar) (qsIn₁ qsPrefixLt) ⊓
      (emptyF (qsVar₁ false) ⊓ ∼(bitF (qsBit₁ false)))
  tgt := emptyF (qsVar₁ false) ⊓ (bitF (qsBit₁ false) ⊓ bitF (qsBit₁ true))

end Spec

/-! ### Reading the specification back -/

section Reading

variable {A : Type} [Language.qsat.Structure A] [LinearOrder A]

/-- The unary component `i` of a state. -/
def qsPred (ρ : qsBlock.Assignment A) (i : Bool) : A → Prop := fun a => ρ (Sum.inl i) fun _ => a

/-- The bit `i` of a state. -/
def qsBit (ρ : qsBlock.Assignment A) (i : Bool) : Prop := ρ (Sum.inr i) Fin.elim0

/-- The quantified set of a state. -/
abbrev qsSet (ρ : qsBlock.Assignment A) : A → Prop := qsPred ρ false

/-- The valuation of a state. -/
abbrev qsVal (ρ : qsBlock.Assignment A) : A → Prop := qsPred ρ true

/-- The mode of a state: `True` while returning a value. -/
abbrev qsUp (ρ : qsBlock.Assignment A) : Prop := qsBit ρ false

/-- The value a state is returning. -/
abbrev qsRes (ρ : qsBlock.Assignment A) : Prop := qsBit ρ true

/-- The state built from its four components. -/
def qsLift (D T : A → Prop) (u r : Prop) : qsBlock.Assignment A
  | Sum.inl false, v => D (v 0)
  | Sum.inl true, v => T (v 0)
  | Sum.inr false, _ => u
  | Sum.inr true, _ => r

omit [Language.qsat.Structure A] [LinearOrder A] in
@[simp]
theorem qsSet_qsLift (D T : A → Prop) (u r : Prop) : qsSet (qsLift D T u r) = D := rfl

omit [Language.qsat.Structure A] [LinearOrder A] in
@[simp]
theorem qsVal_qsLift (D T : A → Prop) (u r : Prop) : qsVal (qsLift D T u r) = T := rfl

omit [Language.qsat.Structure A] [LinearOrder A] in
@[simp]
theorem qsUp_qsLift (D T : A → Prop) (u r : Prop) : qsUp (qsLift D T u r) = u := rfl

omit [Language.qsat.Structure A] [LinearOrder A] in
@[simp]
theorem qsRes_qsLift (D T : A → Prop) (u r : Prop) : qsRes (qsLift D T u r) = r := rfl

omit [Language.qsat.Structure A] [LinearOrder A] in
/-- A state is determined by its four components. -/
theorem qsAssignment_ext {ρ σ : qsBlock.Assignment A}
    (hD : ∀ a : A, qsSet ρ a ↔ qsSet σ a) (hT : ∀ a : A, qsVal ρ a ↔ qsVal σ a)
    (hu : qsUp ρ ↔ qsUp σ) (hr : qsRes ρ ↔ qsRes σ) : ρ = σ := by
  funext i
  match i with
  | Sum.inl b =>
    funext v
    have hv : (fun _ : Fin 1 => v 0) = v := funext fun j => congrArg v (Subsingleton.elim _ _)
    cases b with
    | false => exact propext (hv ▸ hD (v 0))
    | true => exact propext (hv ▸ hT (v 0))
  | Sum.inr b =>
    funext v
    have hv : (Fin.elim0 : Fin 0 → A) = v := funext fun j => j.elim0
    cases b with
    | false => exact propext (hv ▸ hu)
    | true => exact propext (hv ▸ hr)

theorem relMap_qsVar₁ (ρ : qsBlock.Assignment A) (i : Bool) (w : Fin 1 → A) :
    @RelMap qsLang₁ A (qsBlock.structure₁ (L := qsBase) ρ) 1 (qsVar₁ i) w ↔ qsPred ρ i (w 0) := by
  change ρ _ _ ↔ ρ _ _
  exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))

theorem relMap_qsBit₁ (ρ : qsBlock.Assignment A) (i : Bool) (w : Fin 0 → A) :
    @RelMap qsLang₁ A (qsBlock.structure₁ (L := qsBase) ρ) 0 (qsBit₁ i) w ↔ qsBit ρ i := by
  change ρ _ _ ↔ ρ _ _
  exact iff_of_eq (congrArg _ (funext fun j => j.elim0))

theorem relMap_qsIn₁ {n : ℕ} (ρ : qsBlock.Assignment A) (r : Language.qsat.Relations n)
    (w : Fin n → A) :
    @RelMap qsLang₁ A (qsBlock.structure₁ (L := qsBase) ρ) n (qsIn₁ r) w ↔ RelMap r w :=
  Iff.rfl

theorem relMap_qsCur₂ (ρ σ : qsBlock.Assignment A) (i : Bool) (w : Fin 1 → A) :
    @RelMap qsLang₂ A (qsBlock.structure₂ (L := qsBase) ρ σ) 1 (qsCur₂ i) w ↔
      qsPred ρ i (w 0) := by
  change ρ _ _ ↔ ρ _ _
  exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))

theorem relMap_qsNext₂ (ρ σ : qsBlock.Assignment A) (i : Bool) (w : Fin 1 → A) :
    @RelMap qsLang₂ A (qsBlock.structure₂ (L := qsBase) ρ σ) 1 (qsNext₂ i) w ↔
      qsPred σ i (w 0) := by
  change σ _ _ ↔ σ _ _
  exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))

theorem relMap_qsCurBit₂ (ρ σ : qsBlock.Assignment A) (i : Bool) (w : Fin 0 → A) :
    @RelMap qsLang₂ A (qsBlock.structure₂ (L := qsBase) ρ σ) 0 (qsCurBit₂ i) w ↔ qsBit ρ i := by
  change ρ _ _ ↔ ρ _ _
  exact iff_of_eq (congrArg _ (funext fun j => j.elim0))

theorem relMap_qsNextBit₂ (ρ σ : qsBlock.Assignment A) (i : Bool) (w : Fin 0 → A) :
    @RelMap qsLang₂ A (qsBlock.structure₂ (L := qsBase) ρ σ) 0 (qsNextBit₂ i) w ↔ qsBit σ i := by
  change σ _ _ ↔ σ _ _
  exact iff_of_eq (congrArg _ (funext fun j => j.elim0))

theorem relMap_qsIn₂ {n : ℕ} (ρ σ : qsBlock.Assignment A) (r : Language.qsat.Relations n)
    (w : Fin n → A) :
    @RelMap qsLang₂ A (qsBlock.structure₂ (L := qsBase) ρ σ) n (qsIn₂ r) w ↔ RelMap r w :=
  Iff.rfl

/-! #### Splitting the connectives of a sentence

Instance search does not see through a specification's block, so the
propositional connectives of the three sentences are split by hand. -/

theorem qsRealize_inf₁ (ρ : qsBlock.Assignment A) (φ ψ : qsLang₁.Sentence) :
    @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) (φ ⊓ ψ) ↔
      (@Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) φ ∧
        @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) ψ) :=
  letI := qsBlock.structure₁ (L := qsBase) ρ
  Formula.realize_inf

theorem qsRealize_inf₂ (ρ σ : qsBlock.Assignment A) (φ ψ : qsLang₂.Sentence) :
    @Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) (φ ⊓ ψ) ↔
      (@Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) φ ∧
        @Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) ψ) :=
  letI := qsBlock.structure₂ (L := qsBase) ρ σ
  Formula.realize_inf

theorem qsRealize_imp₂ (ρ σ : qsBlock.Assignment A) (φ ψ : qsLang₂.Sentence) :
    @Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) (φ.imp ψ) ↔
      (@Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) φ →
        @Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) ψ) :=
  letI := qsBlock.structure₂ (L := qsBase) ρ σ
  Formula.realize_imp

theorem qsRealize_not₂ (ρ σ : qsBlock.Assignment A) (φ : qsLang₂.Sentence) :
    @Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) (∼φ) ↔
      ¬@Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) φ :=
  letI := qsBlock.structure₂ (L := qsBase) ρ σ
  Formula.realize_not

/-! #### The walk, read back -/

/-- The last variable of a branch: the `prefixLt`-greatest variable of `D`. -/
def QGreatest (D : A → Prop) (x : A) : Prop :=
  IsQVar x ∧ D x ∧ ∀ y : A, IsQVar y → D y → ¬QPrec x y

/-- The last variable of a branch is unique. -/
theorem QGreatest.unique (hwf : QsatWf A) {D : A → Prop} {x y : A}
    (hx : QGreatest D x) (hy : QGreatest D y) : x = y := by
  by_contra hne
  rcases hwf.total x y hx.1 hy.1 hne with h | h
  · exact hx.2.2 y hy.1 hy.2.1 h
  · exact hy.2.2 x hx.1 hx.2.1 h

/-- The subtree of `x` is settled by the value `r` just returned: either `x`
has been played twice already, or `r` is decisive for its quantifier – true at
an existential `x`, false at a universal one. -/
def QPop (T : A → Prop) (r : Prop) (x : A) : Prop :=
  T x ∨ ((IsQAll x ∧ ¬r) ∨ (¬IsQAll x ∧ r))

/-- Removing a variable from the quantified set. -/
def qRem (D : A → Prop) (x : A) : A → Prop := fun y => y ≠ x ∧ D y

/-- **The transition of the walk**, read back: descending, either the next
variable is played with the value `false` or the leaf is evaluated; returning,
the last variable of the branch is popped or played a second time. -/
theorem qsSpec_step_iff (ρ σ : qsBlock.Assignment A) :
    qsSpec.Step ρ σ ↔
      ((¬qsUp ρ →
          (((∀ x y : A, QLeast (qsSet ρ) x →
                (qsSet σ y ↔ qUpd (qsSet ρ) x true y) ∧
                  (qsVal σ y ↔ qUpd (qsVal ρ) x false y)) ∧
              (∀ x : A, QLeast (qsSet ρ) x → ¬qsUp σ ∧ (qsRes σ ↔ qsRes ρ))) ∧
            (((∀ z : A, IsQVar z → qsSet ρ z) →
                ∀ y : A, (qsSet σ y ↔ qsSet ρ y) ∧ (qsVal σ y ↔ qsVal ρ y)) ∧
              ((∀ z : A, IsQVar z → qsSet ρ z) →
                qsUp σ ∧ (qsRes σ ↔ QsatMatrix (qsVal ρ)))))) ∧
        (qsUp ρ →
          ((∃ x : A, QGreatest (qsSet ρ) x) ∧
            (((∀ x y : A, QGreatest (qsSet ρ) x → QPop (qsVal ρ) (qsRes ρ) x →
                  (qsSet σ y ↔ qRem (qsSet ρ) x y) ∧ (qsVal σ y ↔ qsVal ρ y)) ∧
                (∀ x : A, QGreatest (qsSet ρ) x → QPop (qsVal ρ) (qsRes ρ) x →
                  qsUp σ ∧ (qsRes σ ↔ qsRes ρ))) ∧
              ((∀ x y : A, QGreatest (qsSet ρ) x → ¬QPop (qsVal ρ) (qsRes ρ) x →
                  (qsSet σ y ↔ qsSet ρ y) ∧ (qsVal σ y ↔ qUpd (qsVal ρ) x true y)) ∧
                (∀ x : A, QGreatest (qsSet ρ) x → ¬QPop (qsVal ρ) (qsRes ρ) x →
                  ¬qsUp σ ∧ (qsRes σ ↔ qsRes ρ))))))) := by
  rw [show qsSpec.Step ρ σ =
    @Sentence.Realize _ A (qsBlock.structure₂ (L := qsBase) ρ σ) qsSpec.step from rfl]
  simp only [qsSpec, realize_bitS, qsRealize_inf₂, qsRealize_imp₂, qsRealize_not₂,
    realize_downSetS, realize_downBitsS, realize_leafSetS, realize_leafBitsS,
    realize_upExS, realize_popSetS, realize_popBitsS, realize_flipSetS, realize_flipBitsS,
    relMap_qsIn₂, relMap_qsCur₂, relMap_qsNext₂, relMap_qsCurBit₂, relMap_qsNextBit₂,
    Matrix.cons_val_zero, isLastM, isPopM, QLeast, QGreatest, QPop, qRem, qUpd,
    IsQVar, IsQAll, QPrec, QsatMatrix, qsSet, qsVal, qsUp, qsRes, and_true, and_false,
    and_assoc, Bool.false_eq_true, false_or]

theorem qsRealize_not₁ (ρ : qsBlock.Assignment A) (φ : qsLang₁.Sentence) :
    @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) (∼φ) ↔
      ¬@Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) φ :=
  letI := qsBlock.structure₁ (L := qsBase) ρ
  Formula.realize_not

/-- **The starting states**: a well-formed instance at the initial position –
nothing quantified, about to descend. -/
theorem qsSpec_isSrc_iff (ρ : qsBlock.Assignment A) :
    qsSpec.IsSrc ρ ↔ (QsatWf A ∧ ((∀ y : A, ¬qsSet ρ y) ∧ ¬qsUp ρ)) := by
  have h : qsSpec.IsSrc ρ ↔
      (((∀ x y : A, QPrec x y → IsQVar x ∧ IsQVar y) ∧ (∀ x : A, ¬QPrec x x) ∧
          (∀ x y z : A, QPrec x y → QPrec y z → QPrec x z) ∧
          (∀ x y : A, IsQVar x → IsQVar y → x ≠ y → QPrec x y ∨ QPrec y x)) ∧
        ((∀ y : A, ¬qsSet ρ y) ∧ ¬qsUp ρ)) := by
    rw [show qsSpec.IsSrc ρ =
      @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) qsSpec.src from rfl]
    simp only [qsSpec, qsRealize_inf₁, qsRealize_not₁, realize_wfS, realize_emptyS, realize_bitS,
      relMap_qsIn₁, relMap_qsVar₁, relMap_qsBit₁, Matrix.cons_val_zero, IsQVar, QPrec,
      qsSet, qsUp]
  rw [h]
  exact and_congr ⟨fun h' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩,
    fun h' => ⟨h'.isVar_of_prec, h'.irrefl, h'.trans, h'.total⟩⟩ Iff.rfl

/-- **The accepting states**: back at the initial position, returning the value
`true`. -/
theorem qsSpec_isTgt_iff (ρ : qsBlock.Assignment A) :
    qsSpec.IsTgt ρ ↔ ((∀ y : A, ¬qsSet ρ y) ∧ (qsUp ρ ∧ qsRes ρ)) := by
  rw [show qsSpec.IsTgt ρ =
    @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) qsSpec.tgt from rfl]
  simp only [qsSpec, qsRealize_inf₁, realize_emptyS, realize_bitS, relMap_qsVar₁,
    relMap_qsBit₁, Matrix.cons_val_zero, qsSet, qsUp, qsRes]

end Reading

/-! ### The walk is the depth-first evaluation -/

section Correctness

variable {A : Type}

/-- Setting a variable to `true` is adding it. -/
theorem qUpd_true_eq_qAdd (D : A → Prop) (x : A) : qUpd D x true = qAdd D x := by
  classical
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨he, -⟩ | ⟨-, hy⟩
    · exact Or.inl he
    · exact Or.inr hy
  · rcases h with he | hy
    · exact Or.inl ⟨he, rfl⟩
    · by_cases hyx : y = x
      · exact Or.inl ⟨hyx, rfl⟩
      · exact Or.inr ⟨hyx, hy⟩

theorem qsLift_congr {D D' T T' : A → Prop} {u u' r r' : Prop}
    (hD : ∀ y : A, D y ↔ D' y) (hT : ∀ y : A, T y ↔ T' y) (hu : u ↔ u') (hr : r ↔ r') :
    qsLift D T u r = qsLift D' T' u' r' :=
  qsAssignment_ext (by simpa using hD) (by simpa using hT) (by simpa using hu)
    (by simpa using hr)

variable [Language.qsat.Structure A]

/-- The quantified set of a position is downward closed for the prefix order:
the variables already played are an initial segment. -/
def QDownClosed (D : A → Prop) : Prop := ∀ y z : A, IsQVar y → QPrec y z → D z → D y

theorem qDownClosed_empty : QDownClosed (fun _ : A => False) := fun _ _ _ _ h => h.elim

theorem QLeast.qDownClosed_qAdd {D : A → Prop} {x : A} (hx : QLeast D x)
    (hD : QDownClosed D) : QDownClosed (qAdd D x) := by
  classical
  intro y z hy hyz hz
  rcases hz with hzx | hz
  · subst hzx
    by_cases hDy : D y
    · exact Or.inr hDy
    · exact absurd hyz (hx.2.2 y hy hDy)
  · exact Or.inr (hD y z hy hyz hz)

/-- The variable just played is the last one of the branch. -/
theorem QLeast.qGreatest_qAdd (hwf : QsatWf A) {D : A → Prop} {x : A} (hx : QLeast D x)
    (hD : QDownClosed D) : QGreatest (qAdd D x) x := by
  refine ⟨hx.1, qAdd_self D x, fun y hy hay hxy => ?_⟩
  rcases hay with hyx | hy'
  · exact hwf.irrefl x (hyx ▸ hxy)
  · exact hx.2.1 (hD x y hx.1 hxy hy')

/-- Popping the variable just played returns to the position before it. -/
theorem QLeast.qRem_qAdd {D : A → Prop} {x : A} (hx : QLeast D x) :
    qRem (qAdd D x) x = D := by
  funext y
  refine propext ⟨fun h => h.2.resolve_left h.1, fun h => ⟨fun hyx => hx.2.1 (hyx ▸ h), Or.inr h⟩⟩

/-! #### The four transitions -/

variable [LinearOrder A]

theorem qsStep_leaf {D τ : A → Prop} (hcov : ∀ z : A, IsQVar z → D z) (r : Prop) :
    qsSpec.Step (qsLift D τ False r) (qsLift D τ True (QsatMatrix τ)) := by
  refine (qsSpec_step_iff _ _).mpr ⟨fun _ => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, fun hup => hup.elim⟩
  · intro x _ hx
    exact absurd (hcov x hx.1) hx.2.1
  · intro x hx
    exact absurd (hcov x hx.1) hx.2.1
  · exact fun _ _ => ⟨Iff.rfl, Iff.rfl⟩
  · exact fun _ => ⟨trivial, Iff.rfl⟩

theorem qsStep_push (hwf : QsatWf A) {D τ : A → Prop} {x : A} (hx : QLeast D x) (r : Prop) :
    qsSpec.Step (qsLift D τ False r) (qsLift (qAdd D x) (qUpd τ x false) False r) := by
  refine (qsSpec_step_iff _ _).mpr ⟨fun _ => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, fun hup => hup.elim⟩
  · intro x' y hx'
    have hxx : x' = x := (hx' : QLeast D x').unique hwf hx
    subst hxx
    refine ⟨?_, Iff.rfl⟩
    change qAdd D x' y ↔ qUpd D x' true y
    rw [qUpd_true_eq_qAdd]
  · exact fun _ _ => ⟨id, Iff.rfl⟩
  · exact fun hcov => absurd (hcov x hx.1) hx.2.1
  · exact fun hcov => absurd (hcov x hx.1) hx.2.1

theorem qsStep_pop (hwf : QsatWf A) {D τ : A → Prop} {x : A} {v : Prop}
    (hx : QGreatest D x) (hp : QPop τ v x) :
    qsSpec.Step (qsLift D τ True v) (qsLift (qRem D x) τ True v) := by
  refine (qsSpec_step_iff _ _).mpr
    ⟨fun hup => absurd trivial hup, fun _ => ⟨⟨x, hx⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩⟩
  · intro x' y hx' _
    have hxx : x' = x := (hx' : QGreatest D x').unique hwf hx
    subst hxx
    exact ⟨Iff.rfl, Iff.rfl⟩
  · exact fun _ _ _ => ⟨trivial, Iff.rfl⟩
  · intro x' _ hx' hp'
    have hxx : x' = x := (hx' : QGreatest D x').unique hwf hx
    have hp'' : ¬QPop τ v x' := hp'
    exact absurd hp (hxx ▸ hp'')
  · intro x' hx' hp'
    have hxx : x' = x := (hx' : QGreatest D x').unique hwf hx
    have hp'' : ¬QPop τ v x' := hp'
    exact absurd hp (hxx ▸ hp'')

theorem qsStep_flip (hwf : QsatWf A) {D τ : A → Prop} {x : A} {v : Prop}
    (hx : QGreatest D x) (hp : ¬QPop τ v x) :
    qsSpec.Step (qsLift D τ True v) (qsLift D (qUpd τ x true) False v) := by
  refine (qsSpec_step_iff _ _).mpr
    ⟨fun hup => absurd trivial hup, fun _ => ⟨⟨x, hx⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩⟩
  · intro x' _ hx' hp'
    have hxx : x' = x := (hx' : QGreatest D x').unique hwf hx
    have hp'' : QPop τ v x' := hp'
    exact absurd (hxx ▸ hp'') hp
  · intro x' hx' hp'
    have hxx : x' = x := (hx' : QGreatest D x').unique hwf hx
    have hp'' : QPop τ v x' := hp'
    exact absurd (hxx ▸ hp'') hp
  · intro x' y hx' _
    have hxx : x' = x := (hx' : QGreatest D x').unique hwf hx
    subst hxx
    exact ⟨Iff.rfl, Iff.rfl⟩
  · exact fun _ _ _ => ⟨id, Iff.rfl⟩

/-! #### The next and the last variable exist -/

variable [Finite A]

omit [LinearOrder A] in
/-- On a finite well-formed instance a position that is not a leaf has a next
variable. -/
theorem exists_qLeast (hwf : QsatWf A) {D : A → Prop} (h : ∃ z : A, IsQVar z ∧ ¬D z) :
    ∃ x : A, QLeast D x := by
  have : IsTrans A (QPrec (A := A)) := ⟨fun a b c => hwf.trans a b c⟩
  have : Std.Irrefl (QPrec (A := A)) := ⟨hwf.irrefl⟩
  obtain ⟨x, hx, hmin⟩ :=
    (Finite.wellFounded_of_trans_of_irrefl (QPrec (A := A))).has_min {z : A | IsQVar z ∧ ¬D z} h
  exact ⟨x, hx.1, hx.2, fun y hy hd => hmin y ⟨hy, hd⟩⟩

/-! #### The walk is deterministic -/

/-- **The transition relation is functional**: every state has at most one
successor, which is what turns the run of the walk into the only walk there
is. -/
theorem qsSpec_step_unique (hwf : QsatWf A) {ρ σ σ' : qsBlock.Assignment A}
    (h : qsSpec.Step ρ σ) (h' : qsSpec.Step ρ σ') : σ = σ' := by
  classical
  obtain ⟨hd, hu⟩ := (qsSpec_step_iff ρ σ).mp h
  obtain ⟨hd', hu'⟩ := (qsSpec_step_iff ρ σ').mp h'
  by_cases hup : qsUp ρ
  · obtain ⟨⟨x, hx⟩, ⟨hps, hpb⟩, hfs, hfb⟩ := hu hup
    obtain ⟨-, ⟨hps', hpb'⟩, hfs', hfb'⟩ := hu' hup
    by_cases hp : QPop (qsVal ρ) (qsRes ρ) x
    · exact qsAssignment_ext (fun a => ((hps x a hx hp).1).trans ((hps' x a hx hp).1).symm)
        (fun a => ((hps x a hx hp).2).trans ((hps' x a hx hp).2).symm)
        (iff_of_true (hpb x hx hp).1 (hpb' x hx hp).1)
        (((hpb x hx hp).2).trans ((hpb' x hx hp).2).symm)
    · exact qsAssignment_ext (fun a => ((hfs x a hx hp).1).trans ((hfs' x a hx hp).1).symm)
        (fun a => ((hfs x a hx hp).2).trans ((hfs' x a hx hp).2).symm)
        (iff_of_false (hfb x hx hp).1 (hfb' x hx hp).1)
        (((hfb x hx hp).2).trans ((hfb' x hx hp).2).symm)
  · obtain ⟨⟨hns, hnb⟩, hls, hlb⟩ := hd hup
    obtain ⟨⟨hns', hnb'⟩, hls', hlb'⟩ := hd' hup
    by_cases hcov : ∀ z : A, IsQVar z → qsSet ρ z
    · exact qsAssignment_ext (fun a => ((hls hcov a).1).trans ((hls' hcov a).1).symm)
        (fun a => ((hls hcov a).2).trans ((hls' hcov a).2).symm)
        (iff_of_true (hlb hcov).1 (hlb' hcov).1)
        (((hlb hcov).2).trans ((hlb' hcov).2).symm)
    · obtain ⟨z, hz1, hz2⟩ : ∃ z : A, IsQVar z ∧ ¬qsSet ρ z := by
        obtain ⟨z, hz⟩ := not_forall.mp hcov
        exact ⟨z, Classical.not_imp.mp hz⟩
      obtain ⟨x, hx⟩ := exists_qLeast hwf ⟨z, hz1, hz2⟩
      exact qsAssignment_ext (fun a => ((hns x a hx).1).trans ((hns' x a hx).1).symm)
        (fun a => ((hns x a hx).2).trans ((hns' x a hx).2).symm)
        (iff_of_false (hnb x hx).1 (hnb' x hx).1)
        (((hnb x hx).2).trans ((hnb' x hx).2).symm)

omit [Finite A] in
/-- A state returning a value at the empty branch is a dead end: the walk is
over. -/
theorem qsSpec_no_step_of_empty {ρ σ : qsBlock.Assignment A} (hempty : ∀ y : A, ¬qsSet ρ y)
    (hup : qsUp ρ) : ¬qsSpec.Step ρ σ := by
  intro h
  obtain ⟨⟨x, hx⟩, -⟩ := ((qsSpec_step_iff ρ σ).mp h).2 hup
  exact hempty x hx.2.1

/-! #### The run of the walk -/

omit [Finite A] in
private theorem qsRun_leaf {D τ : A → Prop} (hcov : ∀ z : A, IsQVar z → D z) (r : Prop) :
    qsSpec.Reach (qsLift D τ False r) (qsLift D τ True (QsatWins D τ)) := by
  have he : qsLift D τ True (QsatMatrix τ) = qsLift D τ True (QsatWins D τ) :=
    qsLift_congr (fun _ => Iff.rfl) (fun _ => Iff.rfl) Iff.rfl (qsatWins_leaf_iff hcov).symm
  exact Relation.ReflTransGen.single (he ▸ qsStep_leaf hcov r)

/-- **The run of the walk computes the game value**: started at the position
`(D, τ)` in descending mode, the walk comes back to `D` in returning mode
carrying `QsatWins D τ`, having changed nothing on `D`. -/
theorem qsSpec_run (hwf : QsatWf A) :
    ∀ (n : ℕ) (D τ : A → Prop), QDownClosed D → Set.ncard {y : A | IsQVar y ∧ ¬D y} ≤ n →
      ∀ r : Prop, ∃ τ' : A → Prop, (∀ y : A, D y → (τ' y ↔ τ y)) ∧
        qsSpec.Reach (qsLift D τ False r) (qsLift D τ' True (QsatWins D τ)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro D τ _ hcard r
    have hcov : ∀ z : A, IsQVar z → D z := by
      intro z hz
      by_contra hd
      have hne : ({y : A | IsQVar y ∧ ¬D y}).Nonempty := ⟨z, hz, hd⟩
      have h0 : ({y : A | IsQVar y ∧ ¬D y}) = ∅ :=
        (Set.ncard_eq_zero (Set.toFinite _)).mp (Nat.le_zero.mp hcard)
      exact hne.ne_empty h0
    exact ⟨τ, fun _ _ => Iff.rfl, qsRun_leaf hcov r⟩
  | succ n ih =>
    intro D τ hdc hcard r
    by_cases hcov : ∀ z : A, IsQVar z → D z
    · exact ⟨τ, fun _ _ => Iff.rfl, qsRun_leaf hcov r⟩
    obtain ⟨z, hz1, hz2⟩ : ∃ z : A, IsQVar z ∧ ¬D z := by
      obtain ⟨z, hz⟩ := not_forall.mp hcov
      exact ⟨z, Classical.not_imp.mp hz⟩
    obtain ⟨x, hx⟩ := exists_qLeast hwf ⟨z, hz1, hz2⟩
    have hcard' : Set.ncard {y : A | IsQVar y ∧ ¬(qAdd D x) y} ≤ n := by
      have hlt : {y : A | IsQVar y ∧ ¬(qAdd D x) y} ⊂ {y : A | IsQVar y ∧ ¬D y} :=
        ⟨fun y hy => ⟨hy.1, fun hd => hy.2 (Or.inr hd)⟩,
          fun hsup => (hsup ⟨hx.1, hx.2.1⟩).2 (qAdd_self D x)⟩
      exact Nat.lt_succ_iff.mp
        (lt_of_lt_of_le (Set.ncard_lt_ncard hlt (Set.toFinite _)) hcard)
    have hdc' : QDownClosed (qAdd D x) := hx.qDownClosed_qAdd hdc
    have hgt : QGreatest (qAdd D x) x := hx.qGreatest_qAdd hwf hdc
    obtain ⟨τ₁, hτ₁, hreach₁⟩ := ih (qAdd D x) (qUpd τ x false) hdc' hcard' r
    have hstep₀ := qsStep_push hwf hx (D := D) (τ := τ) r
    have hreach₀ : qsSpec.Reach (qsLift D τ False r)
        (qsLift (qAdd D x) τ₁ True (QsatWins (qAdd D x) (qUpd τ x false))) :=
      Relation.ReflTransGen.head hstep₀ hreach₁
    have hx₁ : ¬τ₁ x := by
      rw [hτ₁ x (qAdd_self D x), qUpd_self]
      simp
    have hagree : ∀ y : A, D y → (τ₁ y ↔ τ y) := fun y hy =>
      (hτ₁ y (Or.inr hy)).trans (qUpd_ne τ false fun hyx => hx.2.1 (hyx ▸ hy))
    by_cases hp : QPop τ₁ (QsatWins (qAdd D x) (qUpd τ x false)) x
    · have hdec := hp.resolve_left hx₁
      have hval : QsatWins (qAdd D x) (qUpd τ x false) ↔ QsatWins D τ := by
        rcases hdec with ⟨hall, hnw⟩ | ⟨hnall, hw⟩
        · rw [qsatWins_all_iff hwf hx hall]
          exact iff_of_false hnw fun hall' => hnw (hall' false)
        · rw [qsatWins_ex_iff hwf hx hnall]
          exact iff_of_true hw ⟨false, hw⟩
      refine ⟨τ₁, hagree, hreach₀.tail ?_⟩
      have he : qsLift (qRem (qAdd D x) x) τ₁ True (QsatWins (qAdd D x) (qUpd τ x false)) =
          qsLift D τ₁ True (QsatWins D τ) :=
        qsLift_congr (fun y => iff_of_eq (congrFun hx.qRem_qAdd y)) (fun _ => Iff.rfl) Iff.rfl hval
      exact he ▸ qsStep_pop hwf hgt hp
    · have hstep₂ := qsStep_flip hwf hgt hp
      obtain ⟨τ₂, hτ₂, hreach₂⟩ := ih (qAdd D x) (qUpd τ₁ x true) hdc' hcard'
        (QsatWins (qAdd D x) (qUpd τ x false))
      have hx₂ : τ₂ x := (hτ₂ x (qAdd_self D x)).mpr ((qUpd_self τ₁ x true).mpr rfl)
      have hsame : ∀ y : A, qAdd D x y → (qUpd τ₁ x true y ↔ qUpd τ x true y) := by
        intro y hy
        by_cases hyx : y = x
        · subst hyx
          exact (qUpd_self τ₁ y true).trans (qUpd_self τ y true).symm
        · rw [qUpd_ne τ₁ true hyx, qUpd_ne τ true hyx]
          exact hagree y (hy.resolve_left hyx)
      have hw₁ : QsatWins (qAdd D x) (qUpd τ₁ x true) ↔ QsatWins (qAdd D x) (qUpd τ x true) :=
        ⟨fun hh => qsatWins_congr hh _ hsame,
          fun hh => qsatWins_congr hh _ fun y hy => (hsame y hy).symm⟩
      have hval : QsatWins (qAdd D x) (qUpd τ₁ x true) ↔ QsatWins D τ := by
        rw [hw₁]
        by_cases hall : IsQAll x
        · have hw₀ : QsatWins (qAdd D x) (qUpd τ x false) := by
            by_contra hnw
            exact hp (Or.inr (Or.inl ⟨hall, hnw⟩))
          rw [qsatWins_all_iff hwf hx hall, Bool.forall_bool]
          exact ⟨fun hh => ⟨hw₀, hh⟩, fun hh => hh.2⟩
        · have hw₀ : ¬QsatWins (qAdd D x) (qUpd τ x false) := fun hw =>
            hp (Or.inr (Or.inr ⟨hall, hw⟩))
          rw [qsatWins_ex_iff hwf hx hall, Bool.exists_bool]
          exact ⟨fun hh => Or.inr hh, fun hh => hh.resolve_left hw₀⟩
      have hagree₂ : ∀ y : A, D y → (τ₂ y ↔ τ y) := by
        intro y hy
        have hyx : y ≠ x := fun h => hx.2.1 (h ▸ hy)
        rw [hτ₂ y (Or.inr hy), qUpd_ne τ₁ true hyx]
        exact hagree y hy
      refine ⟨τ₂, hagree₂, ((hreach₀.tail hstep₂).trans hreach₂).tail ?_⟩
      have he : qsLift (qRem (qAdd D x) x) τ₂ True (QsatWins (qAdd D x) (qUpd τ₁ x true)) =
          qsLift D τ₂ True (QsatWins D τ) :=
        qsLift_congr (fun y => iff_of_eq (congrFun hx.qRem_qAdd y)) (fun _ => Iff.rfl) Iff.rfl hval
      exact he ▸ qsStep_pop hwf hgt (Or.inl hx₂)

/-! #### Correctness of the specification -/

omit [Finite A] in
/-- A state with no successor is the only state it reaches. -/
private theorem qsReach_eq_of_terminal {a b : qsBlock.Assignment A}
    (hna : ∀ c : qsBlock.Assignment A, ¬qsSpec.Step a c) (hab : qsSpec.Reach a b) : a = b := by
  rcases Relation.ReflTransGen.cases_head hab with h | ⟨c, hac, -⟩
  · exact h
  · exact absurd hac (hna c)

/-- **The specification is correct**: the walk accepts an instance exactly when
the quantified formula it describes is true. -/
theorem qsatHolds_iff_accepts : QsatHolds A ↔ qsSpec.Accepts A := by
  constructor
  · rintro ⟨hwf, hw⟩
    obtain ⟨τ', -, hreach⟩ := qsSpec_run hwf
      (Set.ncard {y : A | IsQVar y ∧ ¬(fun _ : A => False) y}) (fun _ => False) (fun _ => False)
      qDownClosed_empty le_rfl False
    refine ⟨qsLift (fun _ : A => False) (fun _ : A => False) False False,
      qsLift (fun _ : A => False) τ' True
        (QsatWins (fun _ : A => False) (fun _ : A => False)), ?_, ?_, hreach⟩
    · exact (qsSpec_isSrc_iff _).mpr ⟨hwf, fun _ => id, id⟩
    · exact (qsSpec_isTgt_iff _).mpr ⟨fun _ => id, trivial, hw⟩
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    obtain ⟨hwf, hempty, hup⟩ := (qsSpec_isSrc_iff ρ).mp hsrc
    obtain ⟨hempty', hup', hres'⟩ := (qsSpec_isTgt_iff σ).mp htgt
    refine ⟨hwf, ?_⟩
    have hρ : ρ = qsLift (fun _ : A => False) (qsVal ρ) False (qsRes ρ) :=
      qsAssignment_ext (fun a => iff_of_false (hempty a) id) (fun _ => Iff.rfl)
        (iff_of_false hup id) Iff.rfl
    obtain ⟨τ', -, hrun⟩ := qsSpec_run hwf
      (Set.ncard {y : A | IsQVar y ∧ ¬(fun _ : A => False) y}) (fun _ => False) (qsVal ρ)
      qDownClosed_empty le_rfl (qsRes ρ)
    rw [← hρ] at hrun
    set π := qsLift (fun _ : A => False) τ' True (QsatWins (fun _ : A => False) (qsVal ρ)) with hπ
    have hnπ : ∀ c : qsBlock.Assignment A, ¬qsSpec.Step π c :=
      fun c => qsSpec_no_step_of_empty (fun _ => id) trivial
    have hnσ : ∀ c : qsBlock.Assignment A, ¬qsSpec.Step σ c :=
      fun c => qsSpec_no_step_of_empty hempty' hup'
    have hru : Relator.RightUnique (fun ρ' σ' : qsBlock.Assignment A => qsSpec.Step ρ' σ') :=
      @fun _ _ _ h h' => qsSpec_step_unique hwf h h'
    have hσπ : σ = π := by
      rcases Relation.ReflTransGen.total_of_right_unique hru hreach hrun with h | h
      · exact qsReach_eq_of_terminal hnσ h
      · exact (qsReach_eq_of_terminal hnπ h).symm
    have hval : QsatWins (fun _ : A => False) (qsVal ρ) := by
      have h := hres'
      rw [hσπ, hπ] at h
      exact h
    exact qsatWins_congr hval _ fun _ hy => hy.elim

end Correctness

/-- **QSAT is SO(TC) definable**: the walk is the depth-first evaluation of the
game tree, whose stack is the set of variables already played. -/
theorem qsat_sotcDefinable : SOTCDefinable QSAT :=
  ⟨qsSpec, fun _ _ _ _ _ => qsatHolds_iff_accepts⟩

/-- **QSAT is in PSPACE.** -/
theorem qsat_mem_PSPACE : QSAT ∈ PSPACE :=
  qsat_sotcDefinable

end DescriptiveComplexity
