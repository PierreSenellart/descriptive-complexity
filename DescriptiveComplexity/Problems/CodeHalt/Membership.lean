/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CodeHalt.Cert
import DescriptiveComplexity.RecursivelyEnumerable
import DescriptiveComplexity.Problems.FinSat

/-!
# `CODEHALT` is in RE

The syntax half of `DescriptiveComplexity.CodeHalt.codehalt_iff_cert`: the
certificate of a halting computation is written as an `∃SO[new]` sentence, the
logic defining RE.

* the invented values are the **numeral segment** – no other sort is needed, so
  every quantifier of the kernel is guarded either by `¬old` (a numeral) or by
  `old` (a node of the instance);
* the five components of `DescriptiveComplexity.CodeHalt.Cert` are the relation
  variables of a single existential second-order block
  (`DescriptiveComplexity.CodeHalt.evBlock`);
* the six conditions of `DescriptiveComplexity.CodeHalt.CertOK` are the
  conjuncts of the first-order kernel.

The deep conjunct is the justification of an evaluation fact
(`DescriptiveComplexity.CodeHalt.evOkS`): eleven guarded quantifiers, which is
why the variables are named by their distance from their binder, exactly as in
`DescriptiveComplexity.Problems.Machine.HaltMem`.

The corollary the file exists for is
`DescriptiveComplexity.codehalt_le_finsat`, and with it
`DescriptiveComplexity.finsat_not_computable`: Trakhtenbrot's theorem, now with
nothing left to assume.
-/

namespace DescriptiveComplexity

namespace CodeHalt

open FirstOrder

open Language Structure

open Nat.Partrec.Code

/-! ### The second-order block -/

/-- The relation variables of the `∃SO[new]` definition of `CODEHALT`: the
order of the numeral segment, addition and pairing on it, the code each node
draws, and the value each code takes on each argument. -/
inductive EvIx : Type
  /-- The order of the numeral segment. -/
  | le
  /-- Addition on the segment. -/
  | add
  /-- Cantor's pairing on the segment. -/
  | pr
  /-- The number of the code a node draws. -/
  | dec
  /-- The value a code takes on an argument. -/
  | ev
  deriving DecidableEq

instance : Fintype EvIx where
  elems := {EvIx.le, EvIx.add, EvIx.pr, EvIx.dec, EvIx.ev}
  complete := by intro i; cases i <;> decide

/-- The single existential block of the definition. -/
def evBlock : SOBlock where
  ι := EvIx
  arity
    | .le => 2
    | .add => 3
    | .pr => 3
    | .dec => 2
    | .ev => 3

/-- The vocabulary the kernel is written in. -/
abbrev certLang : Language := soLang (newLang Language.code) [evBlock]

/-- A relation symbol of the instance, in the kernel's vocabulary. -/
abbrev instSym {n : ℕ} (R : Language.code.Relations n) : certLang.Relations n :=
  Sum.inl (Sum.inl R)

/-- The symbol marking the original elements. -/
abbrev oldSym : certLang.Relations 1 := Sum.inl (Sum.inr Language.oldSym)

/-- The order symbol. -/
abbrev leSym : certLang.Relations 2 := Sum.inr ⟨EvIx.le, rfl⟩

/-- The addition symbol. -/
abbrev addSym : certLang.Relations 3 := Sum.inr ⟨EvIx.add, rfl⟩

/-- The pairing symbol. -/
abbrev prSym : certLang.Relations 3 := Sum.inr ⟨EvIx.pr, rfl⟩

/-- The decoding symbol. -/
abbrev decSym : certLang.Relations 2 := Sum.inr ⟨EvIx.dec, rfl⟩

/-- The evaluation symbol. -/
abbrev evSym : certLang.Relations 3 := Sum.inr ⟨EvIx.ev, rfl⟩

/-! ### The extended universe -/

section Structures

variable {A : Type} [Language.code.Structure A] {m : ℕ}

/-- The vocabulary of the instance, read on the extended universe. -/
noncomputable scoped instance extCode : Language.code.Structure (A ⊕ Fin m) :=
  extBase Language.code A m

/-- The structure the kernel is read in: the extended structure together with
an assignment of the relation variables. -/
@[instance_reducible]
noncomputable def certStr (ρ : evBlock.Assignment (A ⊕ Fin m)) :
    certLang.Structure (A ⊕ Fin m) :=
  @sumStructure (newLang Language.code) evBlock.lang (A ⊕ Fin m)
    (extStructure Language.code A m) (evBlock.structure ρ)

theorem relMap_inl {k : ℕ} (R : Language.code.Relations k) (y : Fin k → A) :
    RelMap (L := Language.code) (M := A ⊕ Fin m) R (fun i => Sum.inl (y i)) ↔ RelMap R y := by
  constructor
  · rintro ⟨y', hy', h⟩
    have hyy : y = y' := funext fun i => Sum.inl_injective (hy' i)
    rw [hyy]
    exact h
  · exact fun h => ⟨y, fun _ => rfl, h⟩

@[simp]
theorem relMap_inl₁ (R : Language.code.Relations 1) (a : A) :
    RelMap (L := Language.code) (M := A ⊕ Fin m) R ![Sum.inl a] ↔ RelMap R ![a] := by
  have h : (![Sum.inl a] : Fin 1 → A ⊕ Fin m) = fun i => Sum.inl (![a] i) := by
    funext i; fin_cases i; rfl
  rw [h, relMap_inl]

@[simp]
theorem relMap_inl₂ (R : Language.code.Relations 2) (a b : A) :
    RelMap (L := Language.code) (M := A ⊕ Fin m) R ![Sum.inl a, Sum.inl b] ↔
      RelMap R ![a, b] := by
  have h : (![Sum.inl a, Sum.inl b] : Fin 2 → A ⊕ Fin m) = fun i => Sum.inl (![a, b] i) := by
    funext i; fin_cases i <;> rfl
  rw [h, relMap_inl]

/-! ### The certificate an assignment carries -/

section Carried

omit [Language.code.Structure A]

variable (ρ : evBlock.Assignment (A ⊕ Fin m))

/-- The certificate an assignment carries: the relation variables read at the
sorts they are meant for. -/
def certOf : Cert A (Fin m) where
  Le x y := ρ EvIx.le ![Sum.inr x, Sum.inr y]
  Add x y z := ρ EvIx.add ![Sum.inr x, Sum.inr y, Sum.inr z]
  Pr a b p := ρ EvIx.pr ![Sum.inr a, Sum.inr b, Sum.inr p]
  Dec n e := ρ EvIx.dec ![Sum.inl n, Sum.inr e]
  Ev e x v := ρ EvIx.ev ![Sum.inr e, Sum.inr x, Sum.inr v]

@[simp] theorem certOf_le (x y : Fin m) :
    (certOf ρ).Le x y ↔ ρ EvIx.le ![Sum.inr x, Sum.inr y] := Iff.rfl

@[simp] theorem certOf_add (x y z : Fin m) :
    (certOf ρ).Add x y z ↔ ρ EvIx.add ![Sum.inr x, Sum.inr y, Sum.inr z] := Iff.rfl

@[simp] theorem certOf_pr (a b p : Fin m) :
    (certOf ρ).Pr a b p ↔ ρ EvIx.pr ![Sum.inr a, Sum.inr b, Sum.inr p] := Iff.rfl

@[simp] theorem certOf_dec (n : A) (e : Fin m) :
    (certOf ρ).Dec n e ↔ ρ EvIx.dec ![Sum.inl n, Sum.inr e] := Iff.rfl

@[simp] theorem certOf_ev (e x v : Fin m) :
    (certOf ρ).Ev e x v ↔ ρ EvIx.ev ![Sum.inr e, Sum.inr x, Sum.inr v] := Iff.rfl

end Carried

variable {ρ : evBlock.Assignment (A ⊕ Fin m)} {γ : Type}

/-! ### Atomic formulas -/

/-- An atom of a unary relation of the instance. -/
noncomputable def instF₁ (R : Language.code.Relations 1) (x : γ) : certLang.Formula γ :=
  Relations.formula₁ (instSym R) (Term.var x)

/-- An atom of a binary relation of the instance. -/
noncomputable def instF₂ (R : Language.code.Relations 2) (x y : γ) : certLang.Formula γ :=
  Relations.formula₂ (instSym R) (Term.var x) (Term.var y)

/-- `x` is an original element. -/
noncomputable def oldF (x : γ) : certLang.Formula γ :=
  Relations.formula₁ oldSym (Term.var x)

/-- Equality of two variables. -/
noncomputable def eqF (x y : γ) : certLang.Formula γ :=
  Term.equal (Term.var x) (Term.var y)

/-- The numeral `x` is at most the numeral `y`. -/
noncomputable def leF (x y : γ) : certLang.Formula γ :=
  Relations.formula₂ leSym (Term.var x) (Term.var y)

/-- `x + y = z`. -/
noncomputable def addF (x y z : γ) : certLang.Formula γ :=
  addSym.formula ![Term.var x, Term.var y, Term.var z]

/-- `⟨a, b⟩ = p`. -/
noncomputable def prF (a b p : γ) : certLang.Formula γ :=
  prSym.formula ![Term.var a, Term.var b, Term.var p]

/-- The node `n` draws the code numbered `e`. -/
noncomputable def decF (n e : γ) : certLang.Formula γ :=
  Relations.formula₂ decSym (Term.var n) (Term.var e)

/-- The code numbered `e` returns `v` on `x`. -/
noncomputable def evF (e x v : γ) : certLang.Formula γ :=
  evSym.formula ![Term.var e, Term.var x, Term.var v]

@[simp]
theorem realize_instF₁ (R : Language.code.Relations 1) (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (instF₁ R x) v ↔
      RelMap (L := Language.code) R ![v x] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₁, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_instF₂ (R : Language.code.Relations 2) (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (instF₂ R x y) v ↔
      RelMap (L := Language.code) R ![v x, v y] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₂, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_oldF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (oldF x) v ↔ IsOld (v x) := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [oldF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_eqF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (eqF x y) v ↔ v x = v y := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [eqF, Formula.realize_equal]
  exact Iff.rfl

@[simp]
theorem realize_leF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (leF x y) v ↔ ρ EvIx.le ![v x, v y] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [leF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_addF (x y z : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (addF x y z) v ↔
      ρ EvIx.add ![v x, v y, v z] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [addF, realize_rel₃]
  exact Iff.rfl

@[simp]
theorem realize_prF (a b p : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (prF a b p) v ↔
      ρ EvIx.pr ![v a, v b, v p] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [prF, realize_rel₃]
  exact Iff.rfl

@[simp]
theorem realize_decF (n e : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (decF n e) v ↔ ρ EvIx.dec ![v n, v e] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [decF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_evF (e x v' : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (evF e x v') v ↔
      ρ EvIx.ev ![v e, v x, v v'] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [evF, realize_rel₃]
  exact Iff.rfl

/-! ### Naming the symbols of the instance -/

/-- Being the root. -/
noncomputable def crootF (x : γ) : certLang.Formula γ := instF₁ cRoot x

/-- Drawing the constructor `zero`. -/
noncomputable def czeroF (x : γ) : certLang.Formula γ := instF₁ cZero x

/-- Drawing the constructor `succ`. -/
noncomputable def csuccF (x : γ) : certLang.Formula γ := instF₁ cSucc x

/-- Drawing the constructor `left`. -/
noncomputable def cleftF (x : γ) : certLang.Formula γ := instF₁ cLeft x

/-- Drawing the constructor `right`. -/
noncomputable def crightF (x : γ) : certLang.Formula γ := instF₁ cRight x

/-- Drawing the constructor `pair`. -/
noncomputable def cpairF (x : γ) : certLang.Formula γ := instF₁ cPair x

/-- Drawing the constructor `comp`. -/
noncomputable def ccompF (x : γ) : certLang.Formula γ := instF₁ cComp x

/-- Drawing the constructor `prec`. -/
noncomputable def cprecF (x : γ) : certLang.Formula γ := instF₁ cPrec x

/-- Drawing the constructor `rfind'`. -/
noncomputable def crfindF (x : γ) : certLang.Formula γ := instF₁ cRfind x

/-- Being the first child. -/
noncomputable def carg1F (x y : γ) : certLang.Formula γ := instF₂ cArg1 x y

/-- Being the second child. -/
noncomputable def carg2F (x y : γ) : certLang.Formula γ := instF₂ cArg2 x y

/-! ### Guarded quantifiers

Every quantifier of the kernel ranges over one of the two sorts of the extended
universe – the nodes of the instance, marked by `old`, and the numerals – and
is guarded accordingly. A variable is named by its distance from its binder. -/

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

/-- `∃ x, old x ∧ φ`: a quantifier over the nodes of the instance. -/
noncomputable def exOldF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iExs Unit (oldF vr0 ⊓ φ)

/-- `∀ x, old x → φ`: a quantifier over the nodes of the instance. -/
noncomputable def allOldF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iAlls Unit (oldF vr0 ⟹ φ)

/-- `∃ d, ¬old d ∧ φ`: a quantifier over the numerals. -/
noncomputable def exNewF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iExs Unit (∼(oldF vr0) ⊓ φ)

/-- `∀ d, ¬old d → φ`: a quantifier over the numerals. -/
noncomputable def allNewF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iAlls Unit (∼(oldF vr0) ⟹ φ)

omit [Language.code.Structure A] in
theorem exists_inr_of_not_isOld {x : A ⊕ Fin m} (h : ¬IsOld x) : ∃ j : Fin m, x = Sum.inr j := by
  cases x with
  | inl a => exact absurd (isOld_inl a) h
  | inr j => exact ⟨j, rfl⟩

@[simp]
theorem realize_exOldF (φ : certLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (exOldF φ) v ↔
      ∃ a : A, @Formula.Realize certLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inl a) := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
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
theorem realize_allOldF (φ : certLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (allOldF φ) v ↔
      ∀ a : A, @Formula.Realize certLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inl a) := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [allOldF, Formula.realize_iAlls, Formula.realize_imp, realize_oldF, Sum.elim_inr]
  constructor
  · exact fun h a => h (fun _ => Sum.inl a) (isOld_inl a)
  · intro h i hi
    obtain ⟨a, ha⟩ := isOld_iff.mp hi
    have hie : i = fun _ => Sum.inl a := funext fun u => by cases u; exact ha
    rw [hie]
    exact h a

@[simp]
theorem realize_exNewF (φ : certLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (exNewF φ) v ↔
      ∃ j : Fin m, @Formula.Realize certLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inr j) := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
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
theorem realize_allNewF (φ : certLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (allNewF φ) v ↔
      ∀ j : Fin m, @Formula.Realize certLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inr j) := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [allNewF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_not,
    realize_oldF, Sum.elim_inr]
  constructor
  · exact fun h j => h (fun _ => Sum.inr j) (not_isOld_inr j)
  · intro h i hi
    obtain ⟨j, hj⟩ := exists_inr_of_not_isOld hi
    have hie : i = fun _ => Sum.inr j := funext fun u => by cases u; exact hj
    rw [hie]
    exact h j

/-! ### The shapes that repeat

The order-theoretic shapes (`IsZ`, `IsS`, strictly below) and the arithmetic
of a code's number, each a builder used many times below. -/

/-- The numeral `x` is strictly below `y`. -/
noncomputable def ltF (x y : γ) : certLang.Formula γ := leF x y ⊓ ∼(eqF x y)

/-- `x` is the least numeral. -/
noncomputable def isZF (x : γ) : certLang.Formula γ := allNewF (leF (up x) vr0)

/-- `y` is the numeral just above `x`. -/
noncomputable def isSF (x y : γ) : certLang.Formula γ :=
  leF x y ⊓ ∼(eqF x y) ⊓
    allNewF (leF (up x) vr0 ⟹ leF vr0 (up y) ⟹ (eqF vr0 (up x) ⊔ eqF vr0 (up y)))

/-- `q` is four times `p`. -/
noncomputable def quadF (p q : γ) : certLang.Formula γ :=
  exNewF (addF (up p) (up p) vr0 ⊓ addF vr0 vr0 (up q))

/-- `e` is `q + 4`. -/
noncomputable def plus4F (q e : γ) : certLang.Formula γ :=
  exNewF (exNewF (exNewF (isSF (up (up (up q))) vr2 ⊓ isSF vr2 vr1 ⊓ isSF vr1 vr0 ⊓
    isSF vr0 (up (up (up e))))))

/-- `e` is `q + 5`. -/
noncomputable def plus5F (q e : γ) : certLang.Formula γ :=
  exNewF (plus4F (up q) vr0 ⊓ isSF vr0 (up e))

/-- `e` is `q + 6`. -/
noncomputable def plus6F (q e : γ) : certLang.Formula γ :=
  exNewF (plus5F (up q) vr0 ⊓ isSF vr0 (up e))

/-- `e` is `q + 7`. -/
noncomputable def plus7F (q e : γ) : certLang.Formula γ :=
  exNewF (plus6F (up q) vr0 ⊓ isSF vr0 (up e))

/-- `e` is the numeral `1`. -/
noncomputable def isOneF (e : γ) : certLang.Formula γ := exNewF (isZF vr0 ⊓ isSF vr0 (up e))

/-- `e` is the numeral `2`. -/
noncomputable def isTwoF (e : γ) : certLang.Formula γ := exNewF (isOneF vr0 ⊓ isSF vr0 (up e))

/-- `e` is the numeral `3`. -/
noncomputable def isThreeF (e : γ) : certLang.Formula γ := exNewF (isTwoF vr0 ⊓ isSF vr0 (up e))

/-- `e` numbers the code `pair e₁ e₂`. -/
noncomputable def isPairEF (e e₁ e₂ : γ) : certLang.Formula γ :=
  exNewF (exNewF (prF (up (up e₁)) (up (up e₂)) vr1 ⊓ quadF vr1 vr0 ⊓ plus4F vr0 (up (up e))))

/-- `e` numbers the code `prec e₁ e₂`. -/
noncomputable def isPrecEF (e e₁ e₂ : γ) : certLang.Formula γ :=
  exNewF (exNewF (prF (up (up e₁)) (up (up e₂)) vr1 ⊓ quadF vr1 vr0 ⊓ plus5F vr0 (up (up e))))

/-- `e` numbers the code `comp e₁ e₂`. -/
noncomputable def isCompEF (e e₁ e₂ : γ) : certLang.Formula γ :=
  exNewF (exNewF (prF (up (up e₁)) (up (up e₂)) vr1 ⊓ quadF vr1 vr0 ⊓ plus6F vr0 (up (up e))))

/-- `e` numbers the code `rfind' e₁`. -/
noncomputable def isRfindEF (e e₁ : γ) : certLang.Formula γ :=
  exNewF (quadF (up e₁) vr0 ⊓ plus7F vr0 (up e))

/-- `(a, b)` is the pair enumerated just after `(a', b')`. -/
noncomputable def nextPRF (a' b' a b : γ) : certLang.Formula γ :=
  (ltF a' b' ⊓ isSF a' a ⊓ ltF a b' ⊓ eqF b b') ⊔
    ((isSF a' b' ⊓ eqF a b' ⊓ isZF b) ⊔
      ((leF b' a' ⊓ isSF b' b ⊓ leF b a' ⊓ eqF a a') ⊔
        (eqF a' b' ⊓ isZF a ⊓ isSF b' b)))

/-! ### The order of the numeral segment -/

/-- The order is reflexive. -/
noncomputable def leReflS : certLang.Sentence := allNewF (leF vr0 vr0)

/-- The order is transitive. -/
noncomputable def leTransS : certLang.Sentence :=
  allNewF (allNewF (allNewF (leF vr2 vr1 ⟹ leF vr1 vr0 ⟹ leF vr2 vr0)))

/-- The order is antisymmetric. -/
noncomputable def leAntisymmS : certLang.Sentence :=
  allNewF (allNewF (leF vr1 vr0 ⟹ leF vr0 vr1 ⟹ eqF vr1 vr0))

/-- The order is total. -/
noncomputable def leTotalS : certLang.Sentence :=
  allNewF (allNewF (leF vr1 vr0 ⊔ leF vr0 vr1))

/-- The numeral segment is linearly ordered. -/
noncomputable def linS : certLang.Sentence :=
  leReflS ⊓ (leTransS ⊓ (leAntisymmS ⊓ leTotalS))

/-! ### The justification rules -/

/-- Every addition fact is justified by the recurrence. -/
noncomputable def addOkS : certLang.Sentence :=
  allNewF (allNewF (allNewF (addF vr2 vr1 vr0 ⟹
    (isZF vr1 ⊓ eqF vr0 vr2) ⊔
      exNewF (exNewF (isSF vr1 vr3 ⊓ isSF vr0 vr2 ⊓ addF vr4 vr1 vr0)))))

/-- Every pairing fact is justified by the successor rule. -/
noncomputable def prOkS : certLang.Sentence :=
  allNewF (allNewF (allNewF (prF vr2 vr1 vr0 ⟹
    (isZF vr0 ⊓ isZF vr2 ⊓ isZF vr1) ⊔
      exNewF (exNewF (exNewF (isSF vr2 vr3 ⊓ prF vr1 vr0 vr2 ⊓ nextPRF vr1 vr0 vr5 vr4))))))

/-- Every decoding fact is justified by the node's mark and its children. -/
noncomputable def decOkS : certLang.Sentence :=
  allOldF (allNewF (decF vr1 vr0 ⟹
    (czeroF vr1 ⊓ isZF vr0) ⊔
      ((csuccF vr1 ⊓ isOneF vr0) ⊔
        ((cleftF vr1 ⊓ isTwoF vr0) ⊔
          ((crightF vr1 ⊓ isThreeF vr0) ⊔
            ((cpairF vr1 ⊓ exOldF (exOldF (exNewF (exNewF (carg1F vr5 vr3 ⊓ carg2F vr5 vr2 ⊓
                decF vr3 vr1 ⊓ decF vr2 vr0 ⊓ isPairEF vr4 vr1 vr0))))) ⊔
              ((ccompF vr1 ⊓ exOldF (exOldF (exNewF (exNewF (carg1F vr5 vr3 ⊓ carg2F vr5 vr2 ⊓
                  decF vr3 vr1 ⊓ decF vr2 vr0 ⊓ isCompEF vr4 vr1 vr0))))) ⊔
                ((cprecF vr1 ⊓ exOldF (exOldF (exNewF (exNewF (carg1F vr5 vr3 ⊓ carg2F vr5 vr2 ⊓
                    decF vr3 vr1 ⊓ decF vr2 vr0 ⊓ isPrecEF vr4 vr1 vr0))))) ⊔
                  (crfindF vr1 ⊓ exOldF (exNewF (carg1F vr3 vr1 ⊓ decF vr1 vr0 ⊓
                    isRfindEF vr2 vr0)))))))))))

/-- Every evaluation fact is justified by the rules of its code. -/
noncomputable def evOkS : certLang.Sentence :=
  allNewF (allNewF (allNewF (evF vr2 vr1 vr0 ⟹
    (isZF vr2 ⊓ isZF vr0) ⊔
      ((isOneF vr2 ⊓ isSF vr1 vr0) ⊔
        ((isTwoF vr2 ⊓ exNewF (prF vr1 vr0 vr2)) ⊔
          ((isThreeF vr2 ⊓ exNewF (prF vr0 vr1 vr2)) ⊔
            (exNewF (exNewF (isPairEF vr4 vr1 vr0 ⊓
                exNewF (exNewF (evF vr3 vr5 vr1 ⊓ evF vr2 vr5 vr0 ⊓ prF vr1 vr0 vr4)))) ⊔
              (exNewF (exNewF (isCompEF vr4 vr1 vr0 ⊓
                  exNewF (evF vr1 vr4 vr0 ⊓ evF vr2 vr0 vr3))) ⊔
                (exNewF (exNewF (isPrecEF vr4 vr1 vr0 ⊓
                    (exNewF (exNewF (isZF vr0 ⊓ prF vr1 vr0 vr5 ⊓ evF vr3 vr1 vr4)) ⊔
                      exNewF (exNewF (exNewF (exNewF (exNewF (exNewF (exNewF
                        (isSF vr4 vr5 ⊓ prF vr6 vr5 vr10 ⊓ prF vr6 vr4 vr3 ⊓
                          evF vr11 vr3 vr2 ⊓ prF vr4 vr2 vr1 ⊓ prF vr6 vr1 vr0 ⊓
                          evF vr7 vr0 vr9)))))))))) ⊔
                  exNewF (isRfindEF vr3 vr0 ⊓
                    exNewF (exNewF (exNewF (exNewF (prF vr3 vr2 vr6 ⊓ leF vr2 vr5 ⊓
                      prF vr3 vr5 vr1 ⊓ isZF vr0 ⊓ evF vr4 vr1 vr0 ⊓
                      allNewF (leF vr3 vr0 ⟹ ltF vr0 vr6 ⟹
                        exNewF (exNewF (prF vr6 vr2 vr1 ⊓ evF vr7 vr1 vr0 ⊓
                          ∼(isZF vr0))))))))))))))))))

/-- The root draws a code that returns something on `0`. -/
noncomputable def rootS : certLang.Sentence :=
  exOldF (exNewF (exNewF (exNewF (crootF vr3 ⊓ decF vr3 vr2 ⊓ isZF vr1 ⊓ evF vr2 vr1 vr0))))

/-- **The kernel**: the invented values carry a halting computation. -/
noncomputable def kernelS : certLang.Sentence :=
  linS ⊓ (addOkS ⊓ (prOkS ⊓ (decOkS ⊓ (evOkS ⊓ rootS))))

/-! ### What the kernel says -/

section CertRealize

variable (ρ)

private theorem realize_linS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) linS ↔ IsLinOrd (certOf ρ).Le := by
  simp only [linS, leReflS, leTransS, leAntisymmS, leTotalS, IsLinOrd, Sentence.Realize,
    Formula.realize_inf, Formula.realize_imp, Formula.realize_sup, realize_allNewF, realize_leF,
    realize_eqF, Sum.elim_inl, Sum.elim_inr, certOf_le, Sum.inr.injEq]

private theorem realize_addOkS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) addOkS ↔
      ∀ x y z, (certOf ρ).Add x y z →
        (IsZ (certOf ρ).Le y ∧ z = x) ∨
          ∃ y' z', IsS (certOf ρ).Le y' y ∧ IsS (certOf ρ).Le z' z ∧ (certOf ρ).Add x y' z' := by
  simp only [addOkS, isZF, isSF, IsZ, IsS, Sentence.Realize, Formula.realize_inf,
    Formula.realize_imp, Formula.realize_sup, Formula.realize_not, realize_allNewF,
    realize_exNewF, realize_addF, realize_leF, realize_eqF, Sum.elim_inl, Sum.elim_inr,
    certOf_add, certOf_le, Sum.inr.injEq, ne_eq, and_assoc]

private theorem realize_prOkS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) prOkS ↔
      ∀ a b p, (certOf ρ).Pr a b p →
        (IsZ (certOf ρ).Le p ∧ IsZ (certOf ρ).Le a ∧ IsZ (certOf ρ).Le b) ∨
          ∃ p' a' b', IsS (certOf ρ).Le p' p ∧ (certOf ρ).Pr a' b' p' ∧
            (certOf ρ).NextPR a' b' a b := by
  simp only [prOkS, nextPRF, ltF, isZF, isSF, IsZ, IsS, Cert.NextPR, Cert.Lt, Sentence.Realize,
    Formula.realize_inf, Formula.realize_imp, Formula.realize_sup, Formula.realize_not,
    realize_allNewF, realize_exNewF, realize_prF, realize_leF, realize_eqF, Sum.elim_inl,
    Sum.elim_inr, certOf_pr, certOf_le, Sum.inr.injEq, ne_eq, and_assoc]

private theorem realize_decOkS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) decOkS ↔
      ∀ (n : A) (e : Fin m), (certOf ρ).Dec n e → (certOf ρ).DecStep n e := by
  simp only [decOkS, Cert.DecStep, Cert.IsPairE, Cert.IsCompE, Cert.IsPrecE, Cert.IsRfindE,
    Cert.Quad, Cert.Plus4, Cert.Plus5, Cert.Plus6, Cert.Plus7, Cert.IsOne, Cert.IsTwo,
    Cert.IsThree, IsZ, IsS, isZF, isSF, quadF, plus4F, plus5F, plus6F, plus7F, isOneF, isTwoF,
    isThreeF, isPairEF, isCompEF, isPrecEF, isRfindEF, czeroF, csuccF, cleftF, crightF, cpairF,
    ccompF, cprecF, crfindF, carg1F, carg2F, CZero, CSucc, CLeft, CRight, CPair, CComp, CPrec,
    CRfind, CArg1, CArg2, Sentence.Realize, Formula.realize_inf, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_not, realize_allOldF, realize_allNewF, realize_exOldF,
    realize_exNewF, realize_instF₁, realize_instF₂, realize_decF, realize_addF, realize_prF,
    realize_leF, realize_eqF, Sum.elim_inl, Sum.elim_inr, certOf_dec, certOf_add, certOf_pr,
    certOf_le, relMap_inl₁, relMap_inl₂, Sum.inr.injEq, ne_eq, and_assoc]

private theorem realize_evOkS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) evOkS ↔
      ∀ e x v, (certOf ρ).Ev e x v → (certOf ρ).EvStep e x v := by
  simp only [evOkS, Cert.EvStep, Cert.IsPairE, Cert.IsCompE, Cert.IsPrecE, Cert.IsRfindE,
    Cert.Quad, Cert.Plus4, Cert.Plus5, Cert.Plus6, Cert.Plus7, Cert.IsOne, Cert.IsTwo,
    Cert.IsThree, Cert.Lt, IsZ, IsS, isZF, isSF, ltF, quadF, plus4F, plus5F, plus6F, plus7F,
    isOneF, isTwoF, isThreeF, isPairEF, isCompEF, isPrecEF, isRfindEF, Sentence.Realize,
    Formula.realize_inf, Formula.realize_imp, Formula.realize_sup, Formula.realize_not,
    realize_allNewF, realize_exNewF, realize_evF, realize_addF, realize_prF, realize_leF,
    realize_eqF, Sum.elim_inl, Sum.elim_inr, certOf_ev, certOf_add, certOf_pr, certOf_le,
    Sum.inr.injEq, ne_eq, and_assoc]

private theorem realize_rootS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) rootS ↔
      ∃ (n : A) (e z v : Fin m), CRoot n ∧ (certOf ρ).Dec n e ∧ IsZ (certOf ρ).Le z ∧
        (certOf ρ).Ev e z v := by
  simp only [rootS, crootF, isZF, IsZ, CRoot, Sentence.Realize, Formula.realize_inf,
    realize_exOldF, realize_exNewF, realize_allNewF, realize_instF₁, realize_decF, realize_evF,
    realize_leF, Sum.elim_inl, Sum.elim_inr, certOf_dec, certOf_ev, certOf_le, relMap_inl₁,
    and_assoc]

end CertRealize

theorem realize_kernelS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) kernelS ↔ CertOK (certOf ρ) := by
  simp only [kernelS, Sentence.Realize, Formula.realize_inf]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨(realize_linS ρ).mp h1, (realize_addOkS ρ).mp h2, (realize_prOkS ρ).mp h3,
      (realize_decOkS ρ).mp h4, (realize_evOkS ρ).mp h5, (realize_rootS ρ).mp h6⟩
  · intro h
    exact ⟨(realize_linS ρ).mpr h.le_lin, (realize_addOkS ρ).mpr h.add_ok,
      (realize_prOkS ρ).mpr h.pr_ok, (realize_decOkS ρ).mpr h.dec_ok,
      (realize_evOkS ρ).mpr h.ev_ok, (realize_rootS ρ).mpr h.root⟩

/-! ### The assignment a certificate induces

Read back by `DescriptiveComplexity.CodeHalt.certOf`, this is the identity
*definitionally*, which is what makes the round trip a `rfl`. -/

/-- The assignment a certificate induces. -/
def certAssign (c : Cert A (Fin m)) : evBlock.Assignment (A ⊕ Fin m) := fun i =>
  match i with
  | EvIx.le => fun x =>
    Sum.elim (fun _ => False)
      (fun a => Sum.elim (fun _ => False) (c.Le a) (x (1 : Fin 2))) (x (0 : Fin 2))
  | EvIx.add => fun x =>
    Sum.elim (fun _ => False) (fun a =>
      Sum.elim (fun _ => False) (fun b =>
        Sum.elim (fun _ => False) (c.Add a b) (x (2 : Fin 3))) (x (1 : Fin 3))) (x (0 : Fin 3))
  | EvIx.pr => fun x =>
    Sum.elim (fun _ => False) (fun a =>
      Sum.elim (fun _ => False) (fun b =>
        Sum.elim (fun _ => False) (c.Pr a b) (x (2 : Fin 3))) (x (1 : Fin 3))) (x (0 : Fin 3))
  | EvIx.dec => fun x =>
    Sum.elim (fun n => Sum.elim (fun _ => False) (c.Dec n) (x (1 : Fin 2)))
      (fun _ => False) (x (0 : Fin 2))
  | EvIx.ev => fun x =>
    Sum.elim (fun _ => False) (fun a =>
      Sum.elim (fun _ => False) (fun b =>
        Sum.elim (fun _ => False) (c.Ev a b) (x (2 : Fin 3))) (x (1 : Fin 3))) (x (0 : Fin 3))

omit [Language.code.Structure A] in
@[simp]
theorem certOf_certAssign (c : Cert A (Fin m)) : certOf (certAssign c) = c := rfl

end Structures

end CodeHalt

/-! ### The theorems -/

/-- **`CODEHALT` is definable in `∃SO[new]`**: the invented values are the
numeral segment of a halting computation of the code the root draws, and the
kernel says that they carry one. -/
theorem codehalt_sigmaSONewDefinable : SigmaSONewDefinable CODEHALT := by
  refine ⟨CodeHalt.evBlock, CodeHalt.kernelS, ?_⟩
  intro A _ _ _
  rw [CodeHalt.codehalt_iff_cert]
  constructor
  · rintro ⟨m, c, hc⟩
    refine ⟨m, ?_⟩
    rw [sorealize_singleton]
    refine ⟨CodeHalt.certAssign c, (CodeHalt.realize_kernelS (ρ := CodeHalt.certAssign c)).mpr ?_⟩
    rwa [CodeHalt.certOf_certAssign]
  · rintro ⟨m, hm⟩
    rw [sorealize_singleton] at hm
    obtain ⟨ρ, hρ⟩ := hm
    exact ⟨m, CodeHalt.certOf ρ, (CodeHalt.realize_kernelS (ρ := ρ)).mp hρ⟩

/-- **`CODEHALT` is in RE.** The certificate is the whole computation of the
drawn code – its numbers, its pairings and its intermediate values – which is a
finite object, but no function of the instance bounds it: that is exactly the
difference between `Σ₁` and `∃SO[new]`, and between NP and RE. -/
theorem codehalt_mem_RE : CODEHALT ∈ RE := codehalt_sigmaSONewDefinable

/-- **`CODEHALT` first-order-reduces to finite satisfiability.** No new hardness
work is needed: `DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable` is
proved for an arbitrary source vocabulary, so putting a problem in RE reduces it
to `DescriptiveComplexity.FINSAT` at once. -/
theorem codehalt_le_finsat : Nonempty (CODEHALT ≤ʳᶠᵒ[≤] FINSAT) :=
  finsat_hard_of_sigmaSONewDefinable CODEHALT codehalt_sigmaSONewDefinable

end DescriptiveComplexity
