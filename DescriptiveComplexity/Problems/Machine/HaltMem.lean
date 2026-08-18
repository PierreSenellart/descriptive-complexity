/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltFin
import DescriptiveComplexity.RecursivelyEnumerable
import DescriptiveComplexity.Problems.FinSat

/-!
# The halting problem is in RE

The membership half of the RE machine line: acceptance of a Turing machine
with no step bound and no space bound is definable in `∃SO[new]`
(`DescriptiveComplexity.halt_sigmaSONewDefinable`), the logic defining RE.

The mathematical content is `DescriptiveComplexity.halt_iff_runRel`: the
machine accepts exactly when the invented values carry a *run* – two sorts with
their orders, an input page, and the state, the head and the tape contents at
each time point. This file is that statement written out in syntax:

* the invented values are the extension `A ⊕ Fin m`, `m` unbounded – the only
  difference from a `Σ₁` definition, and what puts the problem beyond NP;
* the nine components of
  `DescriptiveComplexity.TMData.RunRel` are the relation variables of a single
  existential second-order block
  (`DescriptiveComplexity.Halt.runBlock`);
* every condition is a conjunct of the first-order kernel, with each quantifier
  **guarded by its sort**: time points and pages by `¬old`, states, symbols and
  positions of the machine by `old`.

The corollary the file exists for is
`DescriptiveComplexity.halt_le_finsat`: the halting problem first-order-reduces
to finite satisfiability, which is Trakhtenbrot's theorem in the form it is
usually stated. It needs no new hardness work – FINSAT is already RE-hard.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Halt

/-! ### The second-order block -/

/-- The relation variables of the `∃SO[new]` definition of `HALT`: the two
sorts of invented values with their orders, the input page, and the state, the
head and the tape contents at each time point. -/
inductive RunIx : Type
  /-- The time points. -/
  | time
  /-- The order of time. -/
  | tle
  /-- The pages. -/
  | page
  /-- The order of the pages. -/
  | ple
  /-- The input page. -/
  | zero
  /-- `st t q`: the state at the time point `t`. -/
  | st
  /-- `hdP t z`: the page the head is on. -/
  | hdP
  /-- `hdC t p`: the position within that page. -/
  | hdC
  /-- `sym t z p a`: the cell `(z, p)` holds `a` at the time point `t`. -/
  | sym
  deriving DecidableEq

instance : Fintype RunIx where
  elems := {RunIx.time, RunIx.tle, RunIx.page, RunIx.ple, RunIx.zero, RunIx.st, RunIx.hdP,
    RunIx.hdC, RunIx.sym}
  complete := by intro i; cases i <;> decide

/-- The single existential block of the definition. -/
def runBlock : SOBlock where
  ι := RunIx
  arity
    | .time => 1
    | .tle => 2
    | .page => 1
    | .ple => 2
    | .zero => 1
    | .st => 2
    | .hdP => 2
    | .hdC => 2
    | .sym => 4

/-- The vocabulary of the kernel: that of the instance, the marker `old` of the
original elements, and the nine relation variables. -/
abbrev runLang : Language := soLang (newLang Language.turing) [runBlock]

/-- A relation symbol of the instance, in the kernel's vocabulary. -/
abbrev instSym {n : ℕ} (R : Language.turing.Relations n) : runLang.Relations n :=
  Sum.inl (Sum.inl R)

/-- The marker of the original elements, in the kernel's vocabulary. -/
abbrev oldSym : runLang.Relations 1 := Sum.inl (Sum.inr Language.oldSym)

/-- The relation variable of the time points. -/
abbrev timeSym : runLang.Relations 1 := Sum.inr ⟨RunIx.time, rfl⟩

/-- The relation variable of the order of time. -/
abbrev tleSym : runLang.Relations 2 := Sum.inr ⟨RunIx.tle, rfl⟩

/-- The relation variable of the pages. -/
abbrev pageSym : runLang.Relations 1 := Sum.inr ⟨RunIx.page, rfl⟩

/-- The relation variable of the order of the pages. -/
abbrev pleSym : runLang.Relations 2 := Sum.inr ⟨RunIx.ple, rfl⟩

/-- The relation variable of the input page. -/
abbrev zeroSym : runLang.Relations 1 := Sum.inr ⟨RunIx.zero, rfl⟩

/-- The relation variable of the state. -/
abbrev stSym : runLang.Relations 2 := Sum.inr ⟨RunIx.st, rfl⟩

/-- The relation variable of the page of the head. -/
abbrev hdPSym : runLang.Relations 2 := Sum.inr ⟨RunIx.hdP, rfl⟩

/-- The relation variable of the position of the head. -/
abbrev hdCSym : runLang.Relations 2 := Sum.inr ⟨RunIx.hdC, rfl⟩

/-- The relation variable of the tape contents. -/
abbrev symSym : runLang.Relations 4 := Sum.inr ⟨RunIx.sym, rfl⟩

/-! ### The extended universe -/

section Structures

variable {A : Type} [Language.turing.Structure A] {m : ℕ}

/-- The vocabulary of the instance, read on the extended universe. -/
noncomputable scoped instance extTuring : Language.turing.Structure (A ⊕ Fin m) :=
  extBase Language.turing A m

/-- The structure the kernel is read in: the extended structure together with
an assignment of the relation variables. -/
@[instance_reducible]
noncomputable def certStr (ρ : runBlock.Assignment (A ⊕ Fin m)) :
    runLang.Structure (A ⊕ Fin m) :=
  @sumStructure (newLang Language.turing) runBlock.lang (A ⊕ Fin m)
    (extStructure Language.turing A m) (runBlock.structure ρ)

/-! ### The instance, read on the extended universe -/

theorem relMap_inl {k : ℕ} (R : Language.turing.Relations k) (y : Fin k → A) :
    RelMap (L := Language.turing) (M := A ⊕ Fin m) R (fun i => Sum.inl (y i)) ↔ RelMap R y := by
  constructor
  · rintro ⟨y', hy', h⟩
    have hyy : y = y' := funext fun i => Sum.inl_injective (hy' i)
    rw [hyy]
    exact h
  · exact fun h => ⟨y, fun _ => rfl, h⟩

@[simp]
theorem relMap_inl₁ (R : Language.turing.Relations 1) (a : A) :
    RelMap (L := Language.turing) (M := A ⊕ Fin m) R ![Sum.inl a] ↔ RelMap R ![a] := by
  have h : (![Sum.inl a] : Fin 1 → A ⊕ Fin m) = fun i => Sum.inl (![a] i) := by
    funext i; fin_cases i; rfl
  rw [h, relMap_inl]

@[simp]
theorem relMap_inl₂ (R : Language.turing.Relations 2) (a b : A) :
    RelMap (L := Language.turing) (M := A ⊕ Fin m) R ![Sum.inl a, Sum.inl b] ↔
      RelMap R ![a, b] := by
  have h : (![Sum.inl a, Sum.inl b] : Fin 2 → A ⊕ Fin m) = fun i => Sum.inl (![a, b] i) := by
    funext i; fin_cases i <;> rfl
  rw [h, relMap_inl]

/-! ### The certificate an assignment carries

The nine relation variables, read at the sorts they are meant for: the two
sorts and their orders among the invented values, the state, the head and the
tape contents across the two sorts. -/

section Carried

omit [Language.turing.Structure A]

variable (ρ : runBlock.Assignment (A ⊕ Fin m))

/-- The run an assignment carries. -/
def certRun : TMData.RunRel A (Fin m) where
  Time t := ρ RunIx.time ![Sum.inr t]
  TLe t t' := ρ RunIx.tle ![Sum.inr t, Sum.inr t']
  Page z := ρ RunIx.page ![Sum.inr z]
  PLe z z' := ρ RunIx.ple ![Sum.inr z, Sum.inr z']
  Zero z := ρ RunIx.zero ![Sum.inr z]
  St t q := ρ RunIx.st ![Sum.inr t, Sum.inl q]
  HdP t z := ρ RunIx.hdP ![Sum.inr t, Sum.inr z]
  HdC t p := ρ RunIx.hdC ![Sum.inr t, Sum.inl p]
  Sym t z p a := ρ RunIx.sym ![Sum.inr t, Sum.inr z, Sum.inl p, Sum.inl a]

@[simp] theorem certRun_time (t : Fin m) :
    (certRun ρ).Time t ↔ ρ RunIx.time ![Sum.inr t] := Iff.rfl

@[simp] theorem certRun_tle (t t' : Fin m) :
    (certRun ρ).TLe t t' ↔ ρ RunIx.tle ![Sum.inr t, Sum.inr t'] := Iff.rfl

@[simp] theorem certRun_page (z : Fin m) :
    (certRun ρ).Page z ↔ ρ RunIx.page ![Sum.inr z] := Iff.rfl

@[simp] theorem certRun_ple (z z' : Fin m) :
    (certRun ρ).PLe z z' ↔ ρ RunIx.ple ![Sum.inr z, Sum.inr z'] := Iff.rfl

@[simp] theorem certRun_zero (z : Fin m) :
    (certRun ρ).Zero z ↔ ρ RunIx.zero ![Sum.inr z] := Iff.rfl

@[simp] theorem certRun_st (t : Fin m) (q : A) :
    (certRun ρ).St t q ↔ ρ RunIx.st ![Sum.inr t, Sum.inl q] := Iff.rfl

@[simp] theorem certRun_hdP (t z : Fin m) :
    (certRun ρ).HdP t z ↔ ρ RunIx.hdP ![Sum.inr t, Sum.inr z] := Iff.rfl

@[simp] theorem certRun_hdC (t : Fin m) (p : A) :
    (certRun ρ).HdC t p ↔ ρ RunIx.hdC ![Sum.inr t, Sum.inl p] := Iff.rfl

@[simp] theorem certRun_sym (t z : Fin m) (p a : A) :
    (certRun ρ).Sym t z p a ↔
      ρ RunIx.sym ![Sum.inr t, Sum.inr z, Sum.inl p, Sum.inl a] := Iff.rfl

end Carried

variable {ρ : runBlock.Assignment (A ⊕ Fin m)} {γ : Type}

/-! ### Atomic formulas -/

/-- An atom of a unary relation of the instance. -/
noncomputable def instF₁ (R : Language.turing.Relations 1) (x : γ) : runLang.Formula γ :=
  Relations.formula₁ (instSym R) (Term.var x)

/-- An atom of a binary relation of the instance. -/
noncomputable def instF₂ (R : Language.turing.Relations 2) (x y : γ) : runLang.Formula γ :=
  Relations.formula₂ (instSym R) (Term.var x) (Term.var y)

/-- `x` is an original element. -/
noncomputable def oldF (x : γ) : runLang.Formula γ :=
  Relations.formula₁ oldSym (Term.var x)

/-- Equality of two variables. -/
noncomputable def eqF (x y : γ) : runLang.Formula γ :=
  Term.equal (Term.var x) (Term.var y)

/-- `x` is a time point. -/
noncomputable def timeF (x : γ) : runLang.Formula γ := Relations.formula₁ timeSym (Term.var x)

/-- The time point `x` precedes `y`. -/
noncomputable def tleF (x y : γ) : runLang.Formula γ :=
  Relations.formula₂ tleSym (Term.var x) (Term.var y)

/-- `x` is a page. -/
noncomputable def pageF (x : γ) : runLang.Formula γ := Relations.formula₁ pageSym (Term.var x)

/-- The page `x` precedes `y`. -/
noncomputable def pleF (x y : γ) : runLang.Formula γ :=
  Relations.formula₂ pleSym (Term.var x) (Term.var y)

/-- `x` is the input page. -/
noncomputable def zeroF (x : γ) : runLang.Formula γ := Relations.formula₁ zeroSym (Term.var x)

/-- The state at the time point `t` is `q`. -/
noncomputable def stF (t q : γ) : runLang.Formula γ :=
  Relations.formula₂ stSym (Term.var t) (Term.var q)

/-- The head is on the page `z` at the time point `t`. -/
noncomputable def hdPF (t z : γ) : runLang.Formula γ :=
  Relations.formula₂ hdPSym (Term.var t) (Term.var z)

/-- The head is at the position `p` at the time point `t`. -/
noncomputable def hdCF (t p : γ) : runLang.Formula γ :=
  Relations.formula₂ hdCSym (Term.var t) (Term.var p)

/-- The cell `(z, p)` holds `a` at the time point `t`. -/
noncomputable def symF (t z p a : γ) : runLang.Formula γ :=
  symSym.formula ![Term.var t, Term.var z, Term.var p, Term.var a]

@[simp]
theorem realize_instF₁ (R : Language.turing.Relations 1) (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (instF₁ R x) v ↔
      RelMap (L := Language.turing) R ![v x] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₁, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_instF₂ (R : Language.turing.Relations 2) (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (instF₂ R x y) v ↔
      RelMap (L := Language.turing) R ![v x, v y] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₂, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_oldF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (oldF x) v ↔ IsOld (v x) := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [oldF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_eqF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (eqF x y) v ↔ v x = v y := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [eqF, Formula.realize_equal]
  exact Iff.rfl

@[simp]
theorem realize_timeF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (timeF x) v ↔ ρ RunIx.time ![v x] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [timeF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_tleF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (tleF x y) v ↔ ρ RunIx.tle ![v x, v y] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [tleF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_pageF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (pageF x) v ↔ ρ RunIx.page ![v x] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [pageF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_pleF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (pleF x y) v ↔ ρ RunIx.ple ![v x, v y] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [pleF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_zeroF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (zeroF x) v ↔ ρ RunIx.zero ![v x] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [zeroF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_stF (t q : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (stF t q) v ↔ ρ RunIx.st ![v t, v q] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [stF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_hdPF (t z : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (hdPF t z) v ↔ ρ RunIx.hdP ![v t, v z] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [hdPF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_hdCF (t p : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (hdCF t p) v ↔ ρ RunIx.hdC ![v t, v p] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [hdCF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_symF (t z p a : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (symF t z p a) v ↔
      ρ RunIx.sym ![v t, v z, v p, v a] := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [symF, realize_rel₄]
  exact Iff.rfl

/-! ### Naming the symbols of the instance -/

/-- Being a position. -/
noncomputable def posnF (x : γ) : runLang.Formula γ := instF₁ tmPosn x

/-- The order on positions. -/
noncomputable def leF (x y : γ) : runLang.Formula γ := instF₂ tmLe x y

/-- Being a transition. -/
noncomputable def trF (x : γ) : runLang.Formula γ := instF₁ tmTr x

/-- Being a start state. -/
noncomputable def startF (x : γ) : runLang.Formula γ := instF₁ tmStart x

/-- Being an accepting state. -/
noncomputable def accF (x : γ) : runLang.Formula γ := instF₁ tmAcc x

/-- Being the blank symbol. -/
noncomputable def blankF (x : γ) : runLang.Formula γ := instF₁ tmBlank x

/-- Moving the head right. -/
noncomputable def rightF (x : γ) : runLang.Formula γ := instF₁ tmRight x

/-- The state a transition applies in. -/
noncomputable def srcF (x y : γ) : runLang.Formula γ := instF₂ tmSrc x y

/-- The symbol a transition reads. -/
noncomputable def readF (x y : γ) : runLang.Formula γ := instF₂ tmRead x y

/-- The state a transition moves to. -/
noncomputable def dstF (x y : γ) : runLang.Formula γ := instF₂ tmDst x y

/-- The symbol a transition writes. -/
noncomputable def writeF (x y : γ) : runLang.Formula γ := instF₂ tmWrite x y

/-- The initial contents of a cell. -/
noncomputable def inpF (x y : γ) : runLang.Formula γ := instF₂ tmInp x y

/-! ### Guarded quantifiers

Every quantifier of the kernel ranges over one of the two sorts of the extended
universe – the original elements, marked by `old`, and the invented values –
and is guarded accordingly. A variable is named by its distance from its
binder: `vr0` is bound by the innermost guarded quantifier, `vr1` by the one
just outside it, and so on. -/

/-- A variable of the enclosing scope, seen from inside one guarded
quantifier. -/
abbrev up {γ : Type} (x : γ) : γ ⊕ Unit := Sum.inl x

/-- The variable bound by the innermost guarded quantifier. -/
abbrev vr0 {γ : Type} : γ ⊕ Unit := Sum.inr ()

/-- The variable bound one guarded quantifier further out. -/
abbrev vr1 {γ : Type} : (γ ⊕ Unit) ⊕ Unit := up vr0

/-- The variable bound two guarded quantifiers further out. -/
abbrev vr2 {γ : Type} : ((γ ⊕ Unit) ⊕ Unit) ⊕ Unit := up vr1

/-- The variable bound three guarded quantifiers further out. -/
abbrev vr3 {γ : Type} : (((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit := up vr2

/-- The variable bound four guarded quantifiers further out. -/
abbrev vr4 {γ : Type} : ((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit := up vr3

/-- The variable bound five guarded quantifiers further out. -/
abbrev vr5 {γ : Type} : (((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit := up vr4

/-- The variable bound six guarded quantifiers further out. -/
abbrev vr6 {γ : Type} :
    ((((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit := up vr5

/-- The variable bound seven guarded quantifiers further out. -/
abbrev vr7 {γ : Type} :
    (((((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit := up vr6

/-- The variable bound eight guarded quantifiers further out. -/
abbrev vr8 {γ : Type} :
    ((((((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit := up vr7

/-- The variable bound nine guarded quantifiers further out. -/
abbrev vr9 {γ : Type} :
    (((((((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit :=
  up vr8

/-- The variable bound ten guarded quantifiers further out. -/
abbrev vr10 {γ : Type} :
    ((((((((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕
      Unit) ⊕ Unit := up vr9

/-- The variable bound eleven guarded quantifiers further out. -/
abbrev vr11 {γ : Type} :
    (((((((((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕
      Unit) ⊕ Unit) ⊕ Unit := up vr10

/-- The variable bound twelve guarded quantifiers further out. -/
abbrev vr12 {γ : Type} :
    ((((((((((((γ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕
      Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit := up vr11

/-- `∃ x, old x ∧ φ`: a quantifier over the original elements. -/
noncomputable def exOldF (φ : runLang.Formula (γ ⊕ Unit)) : runLang.Formula γ :=
  Formula.iExs Unit (oldF vr0 ⊓ φ)

/-- `∀ x, old x → φ`: a quantifier over the original elements. -/
noncomputable def allOldF (φ : runLang.Formula (γ ⊕ Unit)) : runLang.Formula γ :=
  Formula.iAlls Unit (oldF vr0 ⟹ φ)

/-- `∃ d, ¬old d ∧ φ`: a quantifier over the invented values. -/
noncomputable def exNewF (φ : runLang.Formula (γ ⊕ Unit)) : runLang.Formula γ :=
  Formula.iExs Unit (∼(oldF vr0) ⊓ φ)

/-- `∀ d, ¬old d → φ`: a quantifier over the invented values. -/
noncomputable def allNewF (φ : runLang.Formula (γ ⊕ Unit)) : runLang.Formula γ :=
  Formula.iAlls Unit (∼(oldF vr0) ⟹ φ)

omit [Language.turing.Structure A] in
theorem exists_inr_of_not_isOld {x : A ⊕ Fin m} (h : ¬IsOld x) : ∃ j : Fin m, x = Sum.inr j := by
  cases x with
  | inl a => exact absurd (isOld_inl a) h
  | inr j => exact ⟨j, rfl⟩

@[simp]
theorem realize_exOldF (φ : runLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (exOldF φ) v ↔
      ∃ a : A, @Formula.Realize runLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inl a) := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [exOldF, Formula.realize_iExs, Formula.realize_inf, realize_oldF, Sum.elim_inr]
  constructor
  · rintro ⟨i, hi, hφ⟩
    obtain ⟨a, ha⟩ := isOld_iff.mp hi
    have hie : i = fun _ => Sum.inl a := funext fun u => by cases u; exact ha
    subst hie
    exact ⟨a, hφ⟩
  · rintro ⟨a, hφ⟩
    exact ⟨fun _ => Sum.inl a, isOld_inl a, hφ⟩

@[simp]
theorem realize_allOldF (φ : runLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (allOldF φ) v ↔
      ∀ a : A, @Formula.Realize runLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inl a) := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [allOldF, Formula.realize_iAlls, Formula.realize_imp, realize_oldF, Sum.elim_inr]
  constructor
  · exact fun h a => h (fun _ => Sum.inl a) (isOld_inl a)
  · intro h i hi
    obtain ⟨a, ha⟩ := isOld_iff.mp hi
    have hie : i = fun _ => Sum.inl a := funext fun u => by cases u; exact ha
    rw [hie]
    exact h a

@[simp]
theorem realize_exNewF (φ : runLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (exNewF φ) v ↔
      ∃ j : Fin m, @Formula.Realize runLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inr j) := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [exNewF, Formula.realize_iExs, Formula.realize_inf, Formula.realize_not,
    realize_oldF, Sum.elim_inr]
  constructor
  · rintro ⟨i, hi, hφ⟩
    obtain ⟨j, hj⟩ := exists_inr_of_not_isOld hi
    have hie : i = fun _ => Sum.inr j := funext fun u => by cases u; exact hj
    subst hie
    exact ⟨j, hφ⟩
  · rintro ⟨j, hφ⟩
    exact ⟨fun _ => Sum.inr j, not_isOld_inr j, hφ⟩

@[simp]
theorem realize_allNewF (φ : runLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (allNewF φ) v ↔
      ∀ j : Fin m, @Formula.Realize runLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inr j) := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [allNewF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_not,
    realize_oldF, Sum.elim_inr]
  constructor
  · exact fun h j => h (fun _ => Sum.inr j) (not_isOld_inr j)
  · intro h i hi
    obtain ⟨j, hj⟩ := exists_inr_of_not_isOld hi
    have hie : i = fun _ => Sum.inr j := funext fun u => by cases u; exact hj
    rw [hie]
    exact h j

/-! ### Realization of the named symbols -/

@[simp] theorem realize_posnF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (posnF x) v ↔
      RelMap (L := Language.turing) tmPosn ![v x] := realize_instF₁ _ _ _

@[simp] theorem realize_leF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (leF x y) v ↔
      RelMap (L := Language.turing) tmLe ![v x, v y] := realize_instF₂ _ _ _ _

@[simp] theorem realize_trF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (trF x) v ↔
      RelMap (L := Language.turing) tmTr ![v x] := realize_instF₁ _ _ _

@[simp] theorem realize_startF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (startF x) v ↔
      RelMap (L := Language.turing) tmStart ![v x] := realize_instF₁ _ _ _

@[simp] theorem realize_accF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (accF x) v ↔
      RelMap (L := Language.turing) tmAcc ![v x] := realize_instF₁ _ _ _

@[simp] theorem realize_blankF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (blankF x) v ↔
      RelMap (L := Language.turing) tmBlank ![v x] := realize_instF₁ _ _ _

@[simp] theorem realize_rightF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (rightF x) v ↔
      RelMap (L := Language.turing) tmRight ![v x] := realize_instF₁ _ _ _

@[simp] theorem realize_srcF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (srcF x y) v ↔
      RelMap (L := Language.turing) tmSrc ![v x, v y] := realize_instF₂ _ _ _ _

@[simp] theorem realize_readF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (readF x y) v ↔
      RelMap (L := Language.turing) tmRead ![v x, v y] := realize_instF₂ _ _ _ _

@[simp] theorem realize_dstF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (dstF x y) v ↔
      RelMap (L := Language.turing) tmDst ![v x, v y] := realize_instF₂ _ _ _ _

@[simp] theorem realize_writeF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (writeF x y) v ↔
      RelMap (L := Language.turing) tmWrite ![v x, v y] := realize_instF₂ _ _ _ _

@[simp] theorem realize_inpF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (inpF x y) v ↔
      RelMap (L := Language.turing) tmInp ![v x, v y] := realize_instF₂ _ _ _ _

/-! ### Well-formedness

The kernel has to *check* well-formedness, since junk instances are
no-instances: each conjunct of `DescriptiveComplexity.TMData.WellFormed` is one
sentence, every quantifier ranging over the original elements. -/

/-- The order on positions is reflexive. -/
noncomputable def leReflS : runLang.Sentence := allOldF (leF vr0 vr0)

/-- The order on positions is transitive. -/
noncomputable def leTransS : runLang.Sentence :=
  allOldF (allOldF (allOldF (leF vr2 vr1 ⊓ leF vr1 vr0 ⟹ leF vr2 vr0)))

/-- The order on positions is antisymmetric. -/
noncomputable def leAntisymmS : runLang.Sentence :=
  allOldF (allOldF (leF vr1 vr0 ⊓ leF vr0 vr1 ⟹ eqF vr1 vr0))

/-- The order on positions is total. -/
noncomputable def leTotalS : runLang.Sentence :=
  allOldF (allOldF (leF vr1 vr0 ⊔ leF vr0 vr1))

/-- There is a position. -/
noncomputable def posnExS : runLang.Sentence := exOldF (posnF vr0)

/-- The input is functional. -/
noncomputable def inpFunS : runLang.Sentence :=
  allOldF (allOldF (allOldF (inpF vr2 vr1 ⊓ inpF vr2 vr0 ⟹ eqF vr1 vr0)))

/-- There is a blank symbol. -/
noncomputable def blankExS : runLang.Sentence := exOldF (blankF vr0)

/-- There is at most one blank symbol. -/
noncomputable def blankUniqS : runLang.Sentence :=
  allOldF (allOldF (blankF vr1 ⊓ blankF vr0 ⟹ eqF vr1 vr0))

/-- **The machine is well-formed**: the conjuncts of
`DescriptiveComplexity.TMData.WellFormed`. -/
noncomputable def wfS : runLang.Sentence :=
  leReflS ⊓ (leTransS ⊓ (leAntisymmS ⊓ (leTotalS ⊓
    (posnExS ⊓ (inpFunS ⊓ (blankExS ⊓ blankUniqS))))))

theorem realize_wfS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) wfS ↔ (tmData A).WellFormed := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [wfS, leReflS, leTransS, leAntisymmS, leTotalS, posnExS, inpFunS, blankExS,
    blankUniqS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp, Formula.realize_sup,
    realize_allOldF, realize_exOldF, realize_leF, realize_posnF, realize_inpF, realize_blankF,
    realize_eqF, Sum.elim_inl, Sum.elim_inr, relMap_inl₁, relMap_inl₂, Sum.inl.injEq, and_imp]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ### The shapes that repeat

`MinPos`, `MaxPos` and `SuccPos` occur over the positions of the machine and
over each of the two guessed sorts; `InitTape` and
`DescriptiveComplexity.TMData.SuccCellRel` occur inside the initial and the step
clause. Each is a builder with one realization lemma, so that the conjuncts
below stay readable and their proofs stay one `simp only`. -/

/-- A lowest position of the machine. -/
noncomputable def minPosOldF (x : γ) : runLang.Formula γ :=
  posnF x ⊓ allOldF (posnF vr0 ⟹ leF (up x) vr0)

/-- A highest position of the machine. -/
noncomputable def maxPosOldF (x : γ) : runLang.Formula γ :=
  posnF x ⊓ allOldF (posnF vr0 ⟹ leF vr0 (up x))

/-- The next position of the machine. -/
noncomputable def succPosOldF (x y : γ) : runLang.Formula γ :=
  posnF x ⊓ posnF y ⊓ leF x y ⊓ ∼(eqF x y) ⊓
    allOldF (posnF vr0 ⟹ leF (up x) vr0 ⟹ leF vr0 (up y) ⟹ (eqF vr0 (up x) ⊔ eqF vr0 (up y)))

/-- A lowest time point. -/
noncomputable def minTimeF (x : γ) : runLang.Formula γ :=
  timeF x ⊓ allNewF (timeF vr0 ⟹ tleF (up x) vr0)

/-- A highest time point. -/
noncomputable def maxTimeF (x : γ) : runLang.Formula γ :=
  timeF x ⊓ allNewF (timeF vr0 ⟹ tleF vr0 (up x))

/-- The next time point. -/
noncomputable def succTimeF (x y : γ) : runLang.Formula γ :=
  timeF x ⊓ timeF y ⊓ tleF x y ⊓ ∼(eqF x y) ⊓
    allNewF (timeF vr0 ⟹ tleF (up x) vr0 ⟹ tleF vr0 (up y) ⟹ (eqF vr0 (up x) ⊔ eqF vr0 (up y)))

/-- The next page. -/
noncomputable def succPageF (x y : γ) : runLang.Formula γ :=
  pageF x ⊓ pageF y ⊓ pleF x y ⊓ ∼(eqF x y) ⊓
    allNewF (pageF vr0 ⟹ pleF (up x) vr0 ⟹ pleF vr0 (up y) ⟹ (eqF vr0 (up x) ⊔ eqF vr0 (up y)))

/-- The cell `p` initially holds `a`. -/
noncomputable def initTapeF (p a : γ) : runLang.Formula γ :=
  inpF p a ⊔ (allOldF (∼(inpF (up p) vr0)) ⊓ blankF a)

/-- The cell `(z', p')` is the next one after `(z, p)`. -/
noncomputable def succCellF (z p z' p' : γ) : runLang.Formula γ :=
  (eqF z' z ⊓ succPosOldF p p') ⊔ (succPageF z z' ⊓ maxPosOldF p ⊓ minPosOldF p')

@[simp]
theorem realize_minPosOldF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (minPosOldF x) v ↔
      RelMap (L := Language.turing) tmPosn ![v x] ∧
        ∀ a : A, RelMap (L := Language.turing) tmPosn ![(Sum.inl a : A ⊕ Fin m)] →
          RelMap (L := Language.turing) tmLe ![v x, Sum.inl a] := by
  simp only [minPosOldF, Formula.realize_inf, Formula.realize_imp, realize_posnF, realize_leF,
    realize_allOldF, Sum.elim_inl, Sum.elim_inr]

@[simp]
theorem realize_maxPosOldF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (maxPosOldF x) v ↔
      RelMap (L := Language.turing) tmPosn ![v x] ∧
        ∀ a : A, RelMap (L := Language.turing) tmPosn ![(Sum.inl a : A ⊕ Fin m)] →
          RelMap (L := Language.turing) tmLe ![Sum.inl a, v x] := by
  simp only [maxPosOldF, Formula.realize_inf, Formula.realize_imp, realize_posnF, realize_leF,
    realize_allOldF, Sum.elim_inl, Sum.elim_inr]

@[simp]
theorem realize_succPosOldF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (succPosOldF x y) v ↔
      RelMap (L := Language.turing) tmPosn ![v x] ∧ RelMap (L := Language.turing) tmPosn ![v y] ∧
        RelMap (L := Language.turing) tmLe ![v x, v y] ∧ v x ≠ v y ∧
        ∀ a : A, RelMap (L := Language.turing) tmPosn ![(Sum.inl a : A ⊕ Fin m)] →
          RelMap (L := Language.turing) tmLe ![v x, Sum.inl a] →
          RelMap (L := Language.turing) tmLe ![Sum.inl a, v y] →
          (Sum.inl a = v x ∨ Sum.inl a = v y) := by
  simp only [succPosOldF, Formula.realize_inf, Formula.realize_imp, Formula.realize_sup,
    Formula.realize_not, realize_posnF, realize_leF, realize_eqF, realize_allOldF, Sum.elim_inl,
    Sum.elim_inr, and_assoc]

@[simp]
theorem realize_minTimeF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (minTimeF x) v ↔
      ρ RunIx.time ![v x] ∧
        ∀ j : Fin m, ρ RunIx.time ![Sum.inr j] → ρ RunIx.tle ![v x, Sum.inr j] := by
  simp only [minTimeF, Formula.realize_inf, Formula.realize_imp, realize_timeF, realize_tleF,
    realize_allNewF, Sum.elim_inl, Sum.elim_inr]

@[simp]
theorem realize_maxTimeF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (maxTimeF x) v ↔
      ρ RunIx.time ![v x] ∧
        ∀ j : Fin m, ρ RunIx.time ![Sum.inr j] → ρ RunIx.tle ![Sum.inr j, v x] := by
  simp only [maxTimeF, Formula.realize_inf, Formula.realize_imp, realize_timeF, realize_tleF,
    realize_allNewF, Sum.elim_inl, Sum.elim_inr]

@[simp]
theorem realize_succTimeF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (succTimeF x y) v ↔
      ρ RunIx.time ![v x] ∧ ρ RunIx.time ![v y] ∧ ρ RunIx.tle ![v x, v y] ∧ v x ≠ v y ∧
        ∀ j : Fin m, ρ RunIx.time ![Sum.inr j] → ρ RunIx.tle ![v x, Sum.inr j] →
          ρ RunIx.tle ![Sum.inr j, v y] → (Sum.inr j = v x ∨ Sum.inr j = v y) := by
  simp only [succTimeF, Formula.realize_inf, Formula.realize_imp, Formula.realize_sup,
    Formula.realize_not, realize_timeF, realize_tleF, realize_eqF, realize_allNewF, Sum.elim_inl,
    Sum.elim_inr, and_assoc]

@[simp]
theorem realize_succPageF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (succPageF x y) v ↔
      ρ RunIx.page ![v x] ∧ ρ RunIx.page ![v y] ∧ ρ RunIx.ple ![v x, v y] ∧ v x ≠ v y ∧
        ∀ j : Fin m, ρ RunIx.page ![Sum.inr j] → ρ RunIx.ple ![v x, Sum.inr j] →
          ρ RunIx.ple ![Sum.inr j, v y] → (Sum.inr j = v x ∨ Sum.inr j = v y) := by
  simp only [succPageF, Formula.realize_inf, Formula.realize_imp, Formula.realize_sup,
    Formula.realize_not, realize_pageF, realize_pleF, realize_eqF, realize_allNewF, Sum.elim_inl,
    Sum.elim_inr, and_assoc]

@[simp]
theorem realize_initTapeF (p a : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (initTapeF p a) v ↔
      RelMap (L := Language.turing) tmInp ![v p, v a] ∨
        ((∀ b : A, ¬RelMap (L := Language.turing) tmInp ![v p, Sum.inl b]) ∧
          RelMap (L := Language.turing) tmBlank ![v a]) := by
  simp only [initTapeF, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_inpF, realize_blankF, realize_allOldF, Sum.elim_inl, Sum.elim_inr]

@[simp]
theorem realize_succCellF (z p z' p' : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize runLang _ (certStr ρ) γ (succCellF z p z' p') v ↔
      (v z' = v z ∧ @Formula.Realize runLang _ (certStr ρ) γ (succPosOldF p p') v) ∨
        (@Formula.Realize runLang _ (certStr ρ) γ (succPageF z z') v ∧
          @Formula.Realize runLang _ (certStr ρ) γ (maxPosOldF p) v ∧
          @Formula.Realize runLang _ (certStr ρ) γ (minPosOldF p') v) := by
  simp only [succCellF, Formula.realize_sup, Formula.realize_inf, realize_eqF, and_assoc]

/-! ### The certificate: the shape conditions

One sentence per field of `DescriptiveComplexity.TMData.RunRelOK`, every
quantifier guarded by its sort, and one realization lemma each so that the
assembly below is a conjunction and nothing more. -/

/-- There is a time point. -/
noncomputable def timeExS : runLang.Sentence := exNewF (timeF vr0)

/-- Time is linearly ordered. -/
noncomputable def tleLinS : runLang.Sentence :=
  allNewF (timeF vr0 ⟹ tleF vr0 vr0) ⊓
    (allNewF (allNewF (allNewF (timeF vr2 ⊓ timeF vr1 ⊓ timeF vr0 ⊓ tleF vr2 vr1 ⊓ tleF vr1 vr0 ⟹
      tleF vr2 vr0))) ⊓
      (allNewF (allNewF (timeF vr1 ⊓ timeF vr0 ⊓ tleF vr1 vr0 ⊓ tleF vr0 vr1 ⟹ eqF vr1 vr0)) ⊓
        allNewF (allNewF (timeF vr1 ⊓ timeF vr0 ⟹ tleF vr1 vr0 ⊔ tleF vr0 vr1))))

/-- There is a page. -/
noncomputable def pageExS : runLang.Sentence := exNewF (pageF vr0)

/-- The pages are linearly ordered. -/
noncomputable def pleLinS : runLang.Sentence :=
  allNewF (pageF vr0 ⟹ pleF vr0 vr0) ⊓
    (allNewF (allNewF (allNewF (pageF vr2 ⊓ pageF vr1 ⊓ pageF vr0 ⊓ pleF vr2 vr1 ⊓ pleF vr1 vr0 ⟹
      pleF vr2 vr0))) ⊓
      (allNewF (allNewF (pageF vr1 ⊓ pageF vr0 ⊓ pleF vr1 vr0 ⊓ pleF vr0 vr1 ⟹ eqF vr1 vr0)) ⊓
        allNewF (allNewF (pageF vr1 ⊓ pageF vr0 ⟹ pleF vr1 vr0 ⊔ pleF vr0 vr1))))

/-- There is an input page. -/
noncomputable def zeroExS : runLang.Sentence := exNewF (zeroF vr0)

/-- The input page is a page. -/
noncomputable def zeroPageS : runLang.Sentence := allNewF (zeroF vr0 ⟹ pageF vr0)

/-- There is at most one input page. -/
noncomputable def zeroUniqS : runLang.Sentence :=
  allNewF (allNewF (zeroF vr1 ⊓ zeroF vr0 ⟹ eqF vr1 vr0))

/-- Every time point has a state. -/
noncomputable def stTotS : runLang.Sentence := allNewF (timeF vr0 ⟹ exOldF (stF vr1 vr0))

/-- A time point has at most one state. -/
noncomputable def stFunS : runLang.Sentence :=
  allNewF (allOldF (allOldF (stF vr2 vr1 ⊓ stF vr2 vr0 ⟹ eqF vr1 vr0)))

/-- At every time point the head is on a page. -/
noncomputable def hdPTotS : runLang.Sentence :=
  allNewF (timeF vr0 ⟹ exNewF (pageF vr0 ⊓ hdPF vr1 vr0))

/-- The head is on at most one page. -/
noncomputable def hdPFunS : runLang.Sentence :=
  allNewF (allNewF (allNewF (hdPF vr2 vr1 ⊓ hdPF vr2 vr0 ⟹ eqF vr1 vr0)))

/-- At every time point the head is at a position. -/
noncomputable def hdCTotS : runLang.Sentence := allNewF (timeF vr0 ⟹ exOldF (hdCF vr1 vr0))

/-- The head is at most at one position. -/
noncomputable def hdCFunS : runLang.Sentence :=
  allNewF (allOldF (allOldF (hdCF vr2 vr1 ⊓ hdCF vr2 vr0 ⟹ eqF vr1 vr0)))

/-- Every cell holds a symbol at every time point. -/
noncomputable def symTotS : runLang.Sentence :=
  allNewF (allNewF (allOldF (timeF vr2 ⊓ pageF vr1 ⟹ exOldF (symF vr3 vr2 vr1 vr0))))

/-- A cell holds at most one symbol. -/
noncomputable def symFunS : runLang.Sentence :=
  allNewF (allNewF (allOldF (allOldF (allOldF
    (symF vr4 vr3 vr2 vr1 ⊓ symF vr4 vr3 vr2 vr0 ⟹ eqF vr1 vr0)))))

section ShapeRealize

variable (ρ)

private theorem realize_timeExS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) timeExS ↔ ∃ t, (certRun ρ).Time t := by
  simp only [timeExS, Sentence.Realize, realize_exNewF, realize_timeF, Sum.elim_inr, certRun_time]

private theorem realize_tleLinS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) tleLinS ↔
      TMData.IsLinOrdOn (certRun ρ).TLe (certRun ρ).Time := by
  simp only [tleLinS, TMData.IsLinOrdOn, Sentence.Realize, Formula.realize_inf,
    Formula.realize_imp, Formula.realize_sup, realize_allNewF, realize_timeF, realize_tleF,
    realize_eqF, Sum.elim_inl, Sum.elim_inr, certRun_time, certRun_tle, Sum.inr.injEq, and_imp]

private theorem realize_pageExS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) pageExS ↔ ∃ z, (certRun ρ).Page z := by
  simp only [pageExS, Sentence.Realize, realize_exNewF, realize_pageF, Sum.elim_inr, certRun_page]

private theorem realize_pleLinS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) pleLinS ↔
      TMData.IsLinOrdOn (certRun ρ).PLe (certRun ρ).Page := by
  simp only [pleLinS, TMData.IsLinOrdOn, Sentence.Realize, Formula.realize_inf,
    Formula.realize_imp, Formula.realize_sup, realize_allNewF, realize_pageF, realize_pleF,
    realize_eqF, Sum.elim_inl, Sum.elim_inr, certRun_page, certRun_ple, Sum.inr.injEq, and_imp]

private theorem realize_zeroExS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) zeroExS ↔ ∃ z, (certRun ρ).Zero z := by
  simp only [zeroExS, Sentence.Realize, realize_exNewF, realize_zeroF, Sum.elim_inr, certRun_zero]

private theorem realize_zeroPageS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) zeroPageS ↔
      ∀ z, (certRun ρ).Zero z → (certRun ρ).Page z := by
  simp only [zeroPageS, Sentence.Realize, Formula.realize_imp, realize_allNewF, realize_zeroF,
    realize_pageF, Sum.elim_inr, certRun_zero, certRun_page]

private theorem realize_zeroUniqS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) zeroUniqS ↔
      ∀ z z', (certRun ρ).Zero z → (certRun ρ).Zero z' → z = z' := by
  simp only [zeroUniqS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp,
    realize_allNewF, realize_zeroF, realize_eqF, Sum.elim_inl, Sum.elim_inr, certRun_zero,
    Sum.inr.injEq, and_imp]

private theorem realize_stTotS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) stTotS ↔
      ∀ t, (certRun ρ).Time t → ∃ q, (certRun ρ).St t q := by
  simp only [stTotS, Sentence.Realize, Formula.realize_imp, realize_allNewF, realize_exOldF,
    realize_timeF, realize_stF, Sum.elim_inl, Sum.elim_inr, certRun_time, certRun_st]

private theorem realize_stFunS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) stFunS ↔
      ∀ t q q', (certRun ρ).St t q → (certRun ρ).St t q' → q = q' := by
  simp only [stFunS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp, realize_allNewF,
    realize_allOldF, realize_stF, realize_eqF, Sum.elim_inl, Sum.elim_inr, certRun_st,
    Sum.inl.injEq, and_imp]

private theorem realize_hdPTotS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) hdPTotS ↔
      ∀ t, (certRun ρ).Time t → ∃ z, (certRun ρ).Page z ∧ (certRun ρ).HdP t z := by
  simp only [hdPTotS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp, realize_allNewF,
    realize_exNewF, realize_timeF, realize_pageF, realize_hdPF, Sum.elim_inl, Sum.elim_inr,
    certRun_time, certRun_page, certRun_hdP]

private theorem realize_hdPFunS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) hdPFunS ↔
      ∀ t z z', (certRun ρ).HdP t z → (certRun ρ).HdP t z' → z = z' := by
  simp only [hdPFunS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp, realize_allNewF,
    realize_hdPF, realize_eqF, Sum.elim_inl, Sum.elim_inr, certRun_hdP, Sum.inr.injEq, and_imp]

private theorem realize_hdCTotS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) hdCTotS ↔
      ∀ t, (certRun ρ).Time t → ∃ p, (certRun ρ).HdC t p := by
  simp only [hdCTotS, Sentence.Realize, Formula.realize_imp, realize_allNewF, realize_exOldF,
    realize_timeF, realize_hdCF, Sum.elim_inl, Sum.elim_inr, certRun_time, certRun_hdC]

private theorem realize_hdCFunS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) hdCFunS ↔
      ∀ t p p', (certRun ρ).HdC t p → (certRun ρ).HdC t p' → p = p' := by
  simp only [hdCFunS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp, realize_allNewF,
    realize_allOldF, realize_hdCF, realize_eqF, Sum.elim_inl, Sum.elim_inr, certRun_hdC,
    Sum.inl.injEq, and_imp]

private theorem realize_symTotS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) symTotS ↔
      ∀ t z p, (certRun ρ).Time t → (certRun ρ).Page z → ∃ a, (certRun ρ).Sym t z p a := by
  simp only [symTotS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp, realize_allNewF,
    realize_allOldF, realize_exOldF, realize_timeF, realize_pageF, realize_symF, Sum.elim_inl,
    Sum.elim_inr, certRun_time, certRun_page, certRun_sym, and_imp]

private theorem realize_symFunS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) symFunS ↔
      ∀ t z p a a', (certRun ρ).Sym t z p a → (certRun ρ).Sym t z p a' → a = a' := by
  simp only [symFunS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp, realize_allNewF,
    realize_allOldF, realize_symF, realize_eqF, Sum.elim_inl, Sum.elim_inr, certRun_sym,
    Sum.inl.injEq, and_imp]

end ShapeRealize

/-! ### The certificate: initial, step, accepting

The three conditions that say the data *is* a run. The step clause is the deep
one: eight guarded quantifiers for the two time points and the configuration
they relate, one more for the transition, and four more inside the frame
condition – thirteen in all, which is why the variables are named by their
distance from their binder. -/

/-- At the lowest time point the configuration is initial. -/
noncomputable def initS : runLang.Sentence :=
  allNewF (allOldF (allNewF (allOldF (
    minTimeF vr3 ⊓ stF vr3 vr2 ⊓ hdPF vr3 vr1 ⊓ hdCF vr3 vr0 ⟹
      startF vr2 ⊓ zeroF vr1 ⊓ minPosOldF vr0 ⊓
        allNewF (allOldF (allOldF (
          pageF vr2 ⊓ posnF vr1 ⊓ symF vr6 vr2 vr1 vr0 ⟹
            (zeroF vr2 ⟹ initTapeF vr1 vr0) ⊓ (∼(zeroF vr2) ⟹ blankF vr0))))))))

/-- Along every step of the time order, one transition applies. -/
noncomputable def stepS : runLang.Sentence :=
  allNewF (allNewF (allOldF (allOldF (allNewF (allOldF (allOldF (allOldF (
    succTimeF vr7 vr6 ⊓ stF vr7 vr5 ⊓ stF vr6 vr4 ⊓ hdPF vr7 vr3 ⊓ hdCF vr7 vr2 ⊓
      symF vr7 vr3 vr2 vr1 ⊓ symF vr6 vr3 vr2 vr0 ⟹
      exOldF (trF vr0 ⊓ srcF vr0 vr6 ⊓ readF vr0 vr2 ⊓ dstF vr0 vr5 ⊓ writeF vr0 vr1 ⊓
        allNewF (allOldF (allOldF (allOldF (
          pageF vr3 ⊓ ∼(eqF vr3 vr8 ⊓ eqF vr2 vr7) ⊓ symF vr12 vr3 vr2 vr1 ⊓
            symF vr11 vr3 vr2 vr0 ⟹ eqF vr1 vr0)))) ⊓
        allNewF (allOldF (
          hdPF vr9 vr1 ⊓ hdCF vr9 vr0 ⟹
            (rightF vr2 ⊓ succCellF vr6 vr5 vr1 vr0) ⊔
              (∼(rightF vr2) ⊓ succCellF vr1 vr0 vr6 vr5))))))))))))

/-- At the highest time point the state is accepting. -/
noncomputable def accS : runLang.Sentence :=
  allNewF (allOldF (maxTimeF vr1 ⊓ stF vr1 vr0 ⟹ accF vr0))

section RunRealize

variable (ρ)

private theorem realize_accS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) accS ↔
      ∀ t q, MaxPos (certRun ρ).TLe (certRun ρ).Time t → (certRun ρ).St t q →
        (tmData A).Acc q := by
  simp only [accS, MaxPos, tmData, TMAcc, Sentence.Realize, Formula.realize_inf,
    Formula.realize_imp, realize_allNewF, realize_allOldF, realize_maxTimeF, realize_stF,
    realize_accF, Sum.elim_inl, Sum.elim_inr, certRun_time, certRun_tle, certRun_st,
    relMap_inl₁, and_imp]

private theorem realize_initS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) initS ↔
      ∀ t q z p, MinPos (certRun ρ).TLe (certRun ρ).Time t → (certRun ρ).St t q →
        (certRun ρ).HdP t z → (certRun ρ).HdC t p →
        (tmData A).Start q ∧ (certRun ρ).Zero z ∧
          MinPos (tmData A).Le (tmData A).Posn p ∧
          ∀ z' p' a, (certRun ρ).Page z' → (tmData A).Posn p' → (certRun ρ).Sym t z' p' a →
            ((certRun ρ).Zero z' → (tmData A).InitTape p' a) ∧
              (¬(certRun ρ).Zero z' → (tmData A).Blank a) := by
  simp only [initS, MinPos, TMData.InitTape, tmData, TMStart, TMPosn, TMLe, TMBlank, TMInp,
    Sentence.Realize, Formula.realize_inf, Formula.realize_imp, Formula.realize_not,
    realize_allNewF, realize_allOldF, realize_minTimeF, realize_minPosOldF,
    realize_initTapeF, realize_stF, realize_hdPF, realize_hdCF, realize_startF, realize_zeroF,
    realize_pageF, realize_posnF, realize_symF, realize_blankF, Sum.elim_inl, Sum.elim_inr,
    certRun_time, certRun_tle, certRun_st, certRun_hdP, certRun_hdC, certRun_zero, certRun_page,
    certRun_sym, relMap_inl₁, relMap_inl₂, and_imp, and_assoc]

private theorem realize_stepS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) stepS ↔
      ∀ t t' q q' z p a a', SuccPos (certRun ρ).TLe (certRun ρ).Time t t' →
        (certRun ρ).St t q → (certRun ρ).St t' q' → (certRun ρ).HdP t z → (certRun ρ).HdC t p →
        (certRun ρ).Sym t z p a → (certRun ρ).Sym t' z p a' →
        ∃ τ, (tmData A).Tr τ ∧ (tmData A).Src τ q ∧ (tmData A).Read τ a ∧ (tmData A).Dst τ q' ∧
          (tmData A).Write τ a' ∧
          (∀ z₁ p₁ b b', (certRun ρ).Page z₁ → ¬(z₁ = z ∧ p₁ = p) →
            (certRun ρ).Sym t z₁ p₁ b → (certRun ρ).Sym t' z₁ p₁ b' → b = b') ∧
          ∀ z₂ p₂, (certRun ρ).HdP t' z₂ → (certRun ρ).HdC t' p₂ →
            ((tmData A).Right τ ∧ TMData.SuccCellRel (tmData A) (certRun ρ) z p z₂ p₂) ∨
              (¬(tmData A).Right τ ∧ TMData.SuccCellRel (tmData A) (certRun ρ) z₂ p₂ z p) := by
  simp only [stepS, SuccPos, MinPos, MaxPos, TMData.SuccCellRel, tmData, TMTr, TMSrc, TMRead,
    TMDst, TMWrite, TMRight, TMPosn, TMLe, Sentence.Realize, Formula.realize_inf,
    Formula.realize_imp, Formula.realize_not, Formula.realize_sup, realize_allNewF,
    realize_allOldF, realize_exOldF, realize_succTimeF, realize_succCellF, realize_succPosOldF,
    realize_succPageF, realize_maxPosOldF, realize_minPosOldF, realize_stF, realize_hdPF,
    realize_hdCF, realize_symF, realize_trF, realize_srcF, realize_readF, realize_dstF,
    realize_writeF, realize_rightF, realize_pageF, realize_eqF, Sum.elim_inl, Sum.elim_inr,
    certRun_time, certRun_tle, certRun_page, certRun_ple, certRun_st, certRun_hdP, certRun_hdC,
    certRun_sym, relMap_inl₁, relMap_inl₂, Sum.inl.injEq, Sum.inr.injEq, ne_eq, and_imp,
    and_assoc]

end RunRealize

/-! ### The kernel -/

/-- **The certificate**: the eighteen conditions of
`DescriptiveComplexity.TMData.RunRelOK`, conjoined. -/
noncomputable def certS : runLang.Sentence :=
  timeExS ⊓ (tleLinS ⊓ (pageExS ⊓ (pleLinS ⊓ (zeroExS ⊓ (zeroPageS ⊓ (zeroUniqS ⊓
    (stTotS ⊓ (stFunS ⊓ (hdPTotS ⊓ (hdPFunS ⊓ (hdCTotS ⊓ (hdCFunS ⊓ (symTotS ⊓
      (symFunS ⊓ (initS ⊓ (stepS ⊓ accS))))))))))))))))

/-- **The kernel**: the machine is well-formed and the invented values carry a
run of it. -/
noncomputable def kernelS : runLang.Sentence := wfS ⊓ certS

theorem realize_certS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) certS ↔
      TMData.RunRelOK (tmData A) (certRun ρ) := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [certS, Sentence.Realize, Formula.realize_inf]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    exact ⟨(realize_timeExS ρ).mp h1, (realize_tleLinS ρ).mp h2, (realize_pageExS ρ).mp h3,
      (realize_pleLinS ρ).mp h4, (realize_zeroExS ρ).mp h5, (realize_zeroPageS ρ).mp h6,
      (realize_zeroUniqS ρ).mp h7, (realize_stTotS ρ).mp h8, (realize_stFunS ρ).mp h9,
      (realize_hdPTotS ρ).mp h10, (realize_hdPFunS ρ).mp h11, (realize_hdCTotS ρ).mp h12,
      (realize_hdCFunS ρ).mp h13, (realize_symTotS ρ).mp h14, (realize_symFunS ρ).mp h15,
      (realize_initS ρ).mp h16, (realize_stepS ρ).mp h17, (realize_accS ρ).mp h18⟩
  · intro h
    exact ⟨(realize_timeExS ρ).mpr h.time_ne, (realize_tleLinS ρ).mpr h.tle_lin,
      (realize_pageExS ρ).mpr h.page_ne, (realize_pleLinS ρ).mpr h.ple_lin,
      (realize_zeroExS ρ).mpr h.zero_ex, (realize_zeroPageS ρ).mpr h.zero_page,
      (realize_zeroUniqS ρ).mpr h.zero_uniq, (realize_stTotS ρ).mpr h.st_tot,
      (realize_stFunS ρ).mpr h.st_fun, (realize_hdPTotS ρ).mpr h.hdP_tot,
      (realize_hdPFunS ρ).mpr h.hdP_fun, (realize_hdCTotS ρ).mpr h.hdC_tot,
      (realize_hdCFunS ρ).mpr h.hdC_fun, (realize_symTotS ρ).mpr h.sym_tot,
      (realize_symFunS ρ).mpr h.sym_fun, (realize_initS ρ).mpr h.init,
      (realize_stepS ρ).mpr h.step, (realize_accS ρ).mpr h.acc⟩

theorem realize_kernelS :
    @Sentence.Realize runLang (A ⊕ Fin m) (certStr ρ) kernelS ↔
      (tmData A).WellFormed ∧ TMData.RunRelOK (tmData A) (certRun ρ) := by
  letI : runLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [kernelS, Sentence.Realize, Formula.realize_inf]
  exact and_congr realize_wfS realize_certS

/-! ### The assignment a run induces

The converse reading: a `DescriptiveComplexity.TMData.RunRel` becomes an
assignment of the block by dispatching on the sort of each argument, so that
reading it back is the identity *definitionally* – which is what makes
`DescriptiveComplexity.Halt.certRun_runAssign` a `rfl`. -/

/-- The assignment a run induces. -/
def runAssign (c : TMData.RunRel A (Fin m)) : runBlock.Assignment (A ⊕ Fin m) := fun i =>
  match i with
  | RunIx.time => fun x => Sum.elim (fun _ => False) c.Time (x (0 : Fin 1))
  | RunIx.tle => fun x =>
    Sum.elim (fun _ => False)
      (fun t => Sum.elim (fun _ => False) (c.TLe t) (x (1 : Fin 2))) (x (0 : Fin 2))
  | RunIx.page => fun x => Sum.elim (fun _ => False) c.Page (x (0 : Fin 1))
  | RunIx.ple => fun x =>
    Sum.elim (fun _ => False)
      (fun z => Sum.elim (fun _ => False) (c.PLe z) (x (1 : Fin 2))) (x (0 : Fin 2))
  | RunIx.zero => fun x => Sum.elim (fun _ => False) c.Zero (x (0 : Fin 1))
  | RunIx.st => fun x =>
    Sum.elim (fun _ => False)
      (fun t => Sum.elim (c.St t) (fun _ => False) (x (1 : Fin 2))) (x (0 : Fin 2))
  | RunIx.hdP => fun x =>
    Sum.elim (fun _ => False)
      (fun t => Sum.elim (fun _ => False) (c.HdP t) (x (1 : Fin 2))) (x (0 : Fin 2))
  | RunIx.hdC => fun x =>
    Sum.elim (fun _ => False)
      (fun t => Sum.elim (c.HdC t) (fun _ => False) (x (1 : Fin 2))) (x (0 : Fin 2))
  | RunIx.sym => fun x =>
    Sum.elim (fun _ => False) (fun t =>
      Sum.elim (fun _ => False) (fun z =>
        Sum.elim (fun p =>
          Sum.elim (c.Sym t z p) (fun _ => False) (x (3 : Fin 4)))
          (fun _ => False) (x (2 : Fin 4))) (x (1 : Fin 4))) (x (0 : Fin 4))

omit [Language.turing.Structure A] in
@[simp]
theorem certRun_runAssign (c : TMData.RunRel A (Fin m)) : certRun (runAssign c) = c := rfl

end Structures

end Halt

/-! ### The theorems -/

/-- **The halting problem is definable in `∃SO[new]`**: the invented values are
the time points and the pages of an accepting run, and the kernel says that the
machine is well-formed and that they carry one. -/
theorem halt_sigmaSONewDefinable : SigmaSONewDefinable HALT := by
  refine ⟨Halt.runBlock, Halt.kernelS, ?_⟩
  intro A _ _ _
  rw [halt_iff_runRel]
  constructor
  · rintro ⟨hwf, m, c, hc⟩
    refine ⟨m, ?_⟩
    rw [sorealize_singleton]
    refine ⟨Halt.runAssign c, (Halt.realize_kernelS (ρ := Halt.runAssign c)).mpr ⟨hwf, ?_⟩⟩
    rwa [Halt.certRun_runAssign]
  · rintro ⟨m, hm⟩
    rw [sorealize_singleton] at hm
    obtain ⟨ρ, hρ⟩ := hm
    obtain ⟨hwf, hc⟩ := (Halt.realize_kernelS (ρ := ρ)).mp hρ
    exact ⟨hwf, m, Halt.certRun ρ, hc⟩

/-- **The halting problem is in RE.** A run is a finite object, but no function
of the instance bounds it, which is exactly the difference between `Σ₁` and
`∃SO[new]` – and between NP and RE. -/
theorem halt_mem_RE : HALT ∈ RE := halt_sigmaSONewDefinable

/-- **The halting problem first-order-reduces to finite satisfiability**:
Trakhtenbrot's theorem in the form it is usually stated. It needs no new
hardness work – `DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable` is
already proved for an arbitrary source vocabulary, so putting a problem in RE
reduces it to `DescriptiveComplexity.FINSAT` at once. -/
theorem halt_le_finsat : Nonempty (HALT ≤ʳᶠᵒ[≤] FINSAT) :=
  finsat_hard_of_sigmaSONewDefinable HALT halt_sigmaSONewDefinable

end DescriptiveComplexity
