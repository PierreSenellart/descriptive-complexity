/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Pcp.Cert
import DescriptiveComplexity.RecursivelyEnumerable
import DescriptiveComplexity.Problems.FinSat

/-!
# `PCP` is in RE

The syntax half of `DescriptiveComplexity.Pcp.pcpOn_iff_cert`: the certificate
of a match is written as an `∃SO[new]` sentence, the logic defining RE.

* the invented values are the **slots** – the places of the sequence of
  dominoes – and no other sort is needed, so every quantifier of the kernel is
  guarded either by `¬old` (a slot) or by `old` (an element of the instance,
  playing whichever of the three roles the position it sits in asks for);
* the three components of `DescriptiveComplexity.Pcp.Cert` are the relation
  variables of a single existential second-order block
  (`DescriptiveComplexity.Pcp.certBlock`), the matching being the only one of
  arity 4;
* the conditions of `DescriptiveComplexity.Pcp.CertOK`, together with the
  well-formedness of the instance, are the conjuncts of the first-order kernel.

The deep conjunct is the one saying the matching reflects the lexicographic
order of the two parses: eight guarded quantifiers, alternating slot and
position, which is why the variables are named by their distance from their
binder, exactly as in `DescriptiveComplexity.Problems.CodeHalt.Membership`.

Nothing here is a machine model: `DescriptiveComplexity.pcp_mem_RE` is a
statement about the logic `∃SO[new]`, and it is what makes Post's problem
reduce to finite satisfiability (`DescriptiveComplexity.pcp_le_finsat`).
RE-*hardness* of `PCP` is a different matter – the computation-history
dominoes of `DescriptiveComplexity.Problems.Pcp.Hardness` – and with it Post's
problem is RE-complete (`DescriptiveComplexity.pcp_RE_complete`).
-/

namespace DescriptiveComplexity

namespace Pcp

open FirstOrder

open Language Structure

/-! ### The second-order block -/

/-- The relation variables of the `∃SO[new]` definition of `PCP`: the order of
the slots, the domino at a slot, and the matching between the two parses. -/
inductive CertIx : Type
  /-- The order of the slots. -/
  | sle
  /-- The domino at a slot. -/
  | dm
  /-- The matching between the two parses. -/
  | mt
  deriving DecidableEq

instance : Fintype CertIx where
  elems := {CertIx.sle, CertIx.dm, CertIx.mt}
  complete := by intro i; cases i <;> decide

/-- The single existential block of the definition. -/
def certBlock : SOBlock where
  ι := CertIx
  arity
    | .sle => 2
    | .dm => 2
    | .mt => 4

/-- The vocabulary the kernel is written in. -/
abbrev certLang : Language := soLang (newLang Language.pcp) [certBlock]

/-- A relation symbol of the instance, in the kernel's vocabulary. -/
abbrev instSym {n : ℕ} (R : Language.pcp.Relations n) : certLang.Relations n :=
  Sum.inl (Sum.inl R)

/-- The symbol marking the original elements. -/
abbrev oldSym : certLang.Relations 1 := Sum.inl (Sum.inr Language.oldSym)

/-- The symbol ordering the slots. -/
abbrev sleSym : certLang.Relations 2 := Sum.inr ⟨CertIx.sle, rfl⟩

/-- The symbol giving the domino at a slot. -/
abbrev dmSym : certLang.Relations 2 := Sum.inr ⟨CertIx.dm, rfl⟩

/-- The symbol matching the two parses. -/
abbrev mtSym : certLang.Relations 4 := Sum.inr ⟨CertIx.mt, rfl⟩

/-! ### The extended universe -/

section Structures

variable {A : Type} [Language.pcp.Structure A] [Nonempty A] {m : ℕ}

/-- The vocabulary of the instance, read on the extended universe. -/
noncomputable scoped instance extPcp : Language.pcp.Structure (A ⊕ Fin m) :=
  extBase Language.pcp A m

/-- The structure the kernel is read in: the extended structure together with
an assignment of the relation variables. -/
@[instance_reducible]
noncomputable def certStr (ρ : certBlock.Assignment (A ⊕ Fin m)) :
    certLang.Structure (A ⊕ Fin m) :=
  @sumStructure (newLang Language.pcp) certBlock.lang (A ⊕ Fin m)
    (extStructure Language.pcp A m) (certBlock.structure ρ)

/-! ### The instance, read on the extended universe

A relation of the instance holds on the extended universe only of original
elements, and there of what it holds of in the instance – so at original
arguments the kernel reads the instance itself. -/

theorem relMap_inl {k : ℕ} (R : Language.pcp.Relations k) (y : Fin k → A) :
    RelMap (L := Language.pcp) (M := A ⊕ Fin m) R (fun i => Sum.inl (y i)) ↔ RelMap R y := by
  constructor
  · rintro ⟨y', hy', h⟩
    have hyy : y = y' := funext fun i => Sum.inl_injective (hy' i)
    rw [hyy]
    exact h
  · exact fun h => ⟨y, fun _ => rfl, h⟩

@[simp]
theorem relMap_inl₁ (R : Language.pcp.Relations 1) (a : A) :
    RelMap (L := Language.pcp) (M := A ⊕ Fin m) R ![Sum.inl a] ↔ RelMap R ![a] := by
  have h : (![Sum.inl a] : Fin 1 → A ⊕ Fin m) = fun i => Sum.inl (![a] i) := by
    funext i; fin_cases i; rfl
  rw [h, relMap_inl]

@[simp]
theorem relMap_inl₂ (R : Language.pcp.Relations 2) (a b : A) :
    RelMap (L := Language.pcp) (M := A ⊕ Fin m) R ![Sum.inl a, Sum.inl b] ↔
      RelMap R ![a, b] := by
  have h : (![Sum.inl a, Sum.inl b] : Fin 2 → A ⊕ Fin m) = fun i => Sum.inl (![a, b] i) := by
    funext i; fin_cases i <;> rfl
  rw [h, relMap_inl]

@[simp]
theorem relMap_inl₃ (R : Language.pcp.Relations 3) (a b c : A) :
    RelMap (L := Language.pcp) (M := A ⊕ Fin m) R ![Sum.inl a, Sum.inl b, Sum.inl c] ↔
      RelMap R ![a, b, c] := by
  have h : (![Sum.inl a, Sum.inl b, Sum.inl c] : Fin 3 → A ⊕ Fin m) =
      fun i => Sum.inl (![a, b, c] i) := by
    funext i; fin_cases i <;> rfl
  rw [h, relMap_inl]

/-! ### The certificate an assignment carries -/

section Carried

omit [Language.pcp.Structure A] [Nonempty A]

variable (ρ : certBlock.Assignment (A ⊕ Fin m))

/-- The certificate an assignment carries: the relation variables read at the
sorts they are meant for – slots among the invented values, dominoes and
positions among the original elements. -/
def certOf : Cert A (Fin m) where
  SLe s t := ρ CertIx.sle ![Sum.inr s, Sum.inr t]
  Dm s d := ρ CertIx.dm ![Sum.inr s, Sum.inl d]
  Mt s p s' p' := ρ CertIx.mt ![Sum.inr s, Sum.inl p, Sum.inr s', Sum.inl p']

@[simp] theorem certOf_sle (s t : Fin m) :
    (certOf (A := A) ρ).SLe s t ↔ ρ CertIx.sle ![Sum.inr s, Sum.inr t] := Iff.rfl

@[simp] theorem certOf_dm (s : Fin m) (d : A) :
    (certOf ρ).Dm s d ↔ ρ CertIx.dm ![Sum.inr s, Sum.inl d] := Iff.rfl

@[simp] theorem certOf_mt (s : Fin m) (p : A) (s' : Fin m) (p' : A) :
    (certOf ρ).Mt s p s' p' ↔
      ρ CertIx.mt ![Sum.inr s, Sum.inl p, Sum.inr s', Sum.inl p'] := Iff.rfl

end Carried

variable {ρ : certBlock.Assignment (A ⊕ Fin m)} {γ : Type}

/-! ### Atomic formulas -/

/-- An atom of a unary relation of the instance. -/
noncomputable def instF₁ (R : Language.pcp.Relations 1) (x : γ) : certLang.Formula γ :=
  Relations.formula₁ (instSym R) (Term.var x)

/-- An atom of a binary relation of the instance. -/
noncomputable def instF₂ (R : Language.pcp.Relations 2) (x y : γ) : certLang.Formula γ :=
  Relations.formula₂ (instSym R) (Term.var x) (Term.var y)

/-- An atom of a ternary relation of the instance. -/
noncomputable def instF₃ (R : Language.pcp.Relations 3) (x y z : γ) : certLang.Formula γ :=
  (instSym R).formula ![Term.var x, Term.var y, Term.var z]

/-- `x` is an original element. -/
noncomputable def oldF (x : γ) : certLang.Formula γ :=
  Relations.formula₁ oldSym (Term.var x)

/-- Equality of two variables. -/
noncomputable def eqF (x y : γ) : certLang.Formula γ :=
  Term.equal (Term.var x) (Term.var y)

/-- The slot `s` is at most the slot `t`. -/
noncomputable def sleF (s t : γ) : certLang.Formula γ :=
  Relations.formula₂ sleSym (Term.var s) (Term.var t)

/-- The domino `d` sits at the slot `s`. -/
noncomputable def dmF (s d : γ) : certLang.Formula γ :=
  Relations.formula₂ dmSym (Term.var s) (Term.var d)

/-- The top index `(s, p)` is matched with the bottom index `(s', p')`. -/
noncomputable def mtF (s p s' p' : γ) : certLang.Formula γ :=
  mtSym.formula ![Term.var s, Term.var p, Term.var s', Term.var p']

@[simp]
theorem realize_instF₁ (R : Language.pcp.Relations 1) (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (instF₁ R x) v ↔
      RelMap (L := Language.pcp) R ![v x] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₁, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_instF₂ (R : Language.pcp.Relations 2) (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (instF₂ R x y) v ↔
      RelMap (L := Language.pcp) R ![v x, v y] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₂, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_instF₃ (R : Language.pcp.Relations 3) (x y z : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (instF₃ R x y z) v ↔
      RelMap (L := Language.pcp) R ![v x, v y, v z] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₃, realize_rel₃]
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
theorem realize_sleF (s t : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (sleF s t) v ↔ ρ CertIx.sle ![v s, v t] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [sleF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_dmF (s d : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (dmF s d) v ↔ ρ CertIx.dm ![v s, v d] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [dmF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_mtF (s p s' p' : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (mtF s p s' p') v ↔
      ρ CertIx.mt ![v s, v p, v s', v p'] := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [mtF, realize_rel₄]
  exact Iff.rfl

/-! ### Naming the symbols of the instance -/

/-- The position `x` precedes the position `y`. -/
noncomputable def ordF (x y : γ) : certLang.Formula γ := instF₂ Language.pcpLeSym x y

/-- The element `d` is one of the dominoes. -/
noncomputable def domF (d : γ) : certLang.Formula γ := instF₁ Language.pcpDomSym d

/-- The top word of `d` carries the letter `ℓ` at the position `p`. -/
noncomputable def uAtF (d p ℓ : γ) : certLang.Formula γ := instF₃ Language.pcpUSym d p ℓ

/-- The bottom word of `d` carries the letter `ℓ` at the position `p`. -/
noncomputable def vAtF (d p ℓ : γ) : certLang.Formula γ := instF₃ Language.pcpVSym d p ℓ

/-! ### Guarded quantifiers

Every quantifier of the kernel ranges over one of the two sorts of the extended
universe – the elements of the instance, marked by `old`, and the slots – and is
guarded accordingly. A variable is named by its distance from its binder. -/

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

/-- `∃ x, old x ∧ φ`: a quantifier over the elements of the instance. -/
noncomputable def exOldF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iExs Unit (oldF vr0 ⊓ φ)

/-- `∀ x, old x → φ`: a quantifier over the elements of the instance. -/
noncomputable def allOldF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iAlls Unit (oldF vr0 ⟹ φ)

/-- `∃ s, ¬old s ∧ φ`: a quantifier over the slots. -/
noncomputable def exNewF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iExs Unit (∼(oldF vr0) ⊓ φ)

/-- `∀ s, ¬old s → φ`: a quantifier over the slots. -/
noncomputable def allNewF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iAlls Unit (∼(oldF vr0) ⟹ φ)

omit [Language.pcp.Structure A] [Nonempty A] in
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

/-! ### Well-formedness of the instance -/

/-- The order of the positions is reflexive. -/
noncomputable def ordReflS : certLang.Sentence := allOldF (ordF vr0 vr0)

/-- The order of the positions is transitive. -/
noncomputable def ordTransS : certLang.Sentence :=
  allOldF (allOldF (allOldF (ordF vr2 vr1 ⟹ ordF vr1 vr0 ⟹ ordF vr2 vr0)))

/-- The order of the positions is antisymmetric. -/
noncomputable def ordAntisymmS : certLang.Sentence :=
  allOldF (allOldF (ordF vr1 vr0 ⟹ ordF vr0 vr1 ⟹ eqF vr1 vr0))

/-- The order of the positions is total. -/
noncomputable def ordTotalS : certLang.Sentence :=
  allOldF (allOldF (ordF vr1 vr0 ⊔ ordF vr0 vr1))

/-- A top word carries at most one letter at each position. -/
noncomputable def uFunS : certLang.Sentence :=
  allOldF (allOldF (allOldF (allOldF (uAtF vr3 vr2 vr1 ⟹ uAtF vr3 vr2 vr0 ⟹ eqF vr1 vr0))))

/-- A bottom word carries at most one letter at each position. -/
noncomputable def vFunS : certLang.Sentence :=
  allOldF (allOldF (allOldF (allOldF (vAtF vr3 vr2 vr1 ⟹ vAtF vr3 vr2 vr0 ⟹ eqF vr1 vr0))))

/-- **The instance is a well-formed Post system**: the six conditions of
`DescriptiveComplexity.Pcp.IsWF`, conjoined. -/
noncomputable def wfS : certLang.Sentence :=
  ordReflS ⊓ (ordTransS ⊓ (ordAntisymmS ⊓ (ordTotalS ⊓ (uFunS ⊓ vFunS))))

/-! ### The shapes that repeat -/

/-- The position `x` strictly precedes the position `y`. -/
noncomputable def ordLtF (x y : γ) : certLang.Formula γ := ordF x y ⊓ ∼(eqF x y)

/-- The slot `s` strictly precedes the slot `t`. -/
noncomputable def sltF (s t : γ) : certLang.Formula γ := sleF s t ⊓ ∼(eqF s t)

/-- The position `p` carries a letter of the top word of `d`. -/
noncomputable def usedUF (d p : γ) : certLang.Formula γ :=
  exOldF (uAtF (up d) (up p) vr0)

/-- The position `p` carries a letter of the bottom word of `d`. -/
noncomputable def usedVF (d p : γ) : certLang.Formula γ :=
  exOldF (vAtF (up d) (up p) vr0)

/-- `(s, p)` is an index of the top parse. -/
noncomputable def topIxF (s p : γ) : certLang.Formula γ :=
  exOldF (dmF (up s) vr0 ⊓ usedUF vr0 (up p))

/-- `(s, p)` is an index of the bottom parse. -/
noncomputable def botIxF (s p : γ) : certLang.Formula γ :=
  exOldF (dmF (up s) vr0 ⊓ usedVF vr0 (up p))

/-- `(s, p)` precedes `(t, q)` in the lexicographic order of a parse. -/
noncomputable def lexLtF (s p t q : γ) : certLang.Formula γ :=
  sltF s t ⊔ (eqF s t ⊓ ordLtF p q)

/-! ### The conditions on the certificate -/

/-- The order of the slots is reflexive. -/
noncomputable def sleReflS : certLang.Sentence := allNewF (sleF vr0 vr0)

/-- The order of the slots is transitive. -/
noncomputable def sleTransS : certLang.Sentence :=
  allNewF (allNewF (allNewF (sleF vr2 vr1 ⟹ sleF vr1 vr0 ⟹ sleF vr2 vr0)))

/-- The order of the slots is antisymmetric. -/
noncomputable def sleAntisymmS : certLang.Sentence :=
  allNewF (allNewF (sleF vr1 vr0 ⟹ sleF vr0 vr1 ⟹ eqF vr1 vr0))

/-- The order of the slots is total. -/
noncomputable def sleTotalS : certLang.Sentence :=
  allNewF (allNewF (sleF vr1 vr0 ⊔ sleF vr0 vr1))

/-- The slots are linearly ordered. -/
noncomputable def sleLinS : certLang.Sentence :=
  sleReflS ⊓ (sleTransS ⊓ (sleAntisymmS ⊓ sleTotalS))

/-- There is at least one slot. -/
noncomputable def slotExS : certLang.Sentence := exNewF (sleF vr0 vr0)

/-- Every slot carries a domino. -/
noncomputable def dmTotS : certLang.Sentence := allNewF (exOldF (dmF vr1 vr0))

/-- A slot carries only one domino. -/
noncomputable def dmFunS : certLang.Sentence :=
  allNewF (allOldF (allOldF (dmF vr2 vr1 ⟹ dmF vr2 vr0 ⟹ eqF vr1 vr0)))

/-- What a slot carries is a domino of the instance. -/
noncomputable def dmDomS : certLang.Sentence :=
  allNewF (allOldF (dmF vr1 vr0 ⟹ domF vr0))

/-- The matching relates an index of the top parse to one of the bottom
parse. -/
noncomputable def mtIxS : certLang.Sentence :=
  allNewF (allOldF (allNewF (allOldF (mtF vr3 vr2 vr1 vr0 ⟹
    topIxF vr3 vr2 ⊓ botIxF vr1 vr0))))

/-- Every index of the top parse is matched. -/
noncomputable def mtLeftS : certLang.Sentence :=
  allNewF (allOldF (topIxF vr1 vr0 ⟹ exNewF (exOldF (mtF vr3 vr2 vr1 vr0))))

/-- Every index of the bottom parse is matched. -/
noncomputable def mtRightS : certLang.Sentence :=
  allNewF (allOldF (botIxF vr1 vr0 ⟹ exNewF (exOldF (mtF vr1 vr0 vr3 vr2))))

/-- The matching reflects the lexicographic order of the two parses. Eight
guarded quantifiers, alternating slot and position: the two matched pairs on
the top side and the two on the bottom side. -/
noncomputable def mtMonoS : certLang.Sentence :=
  allNewF (allOldF (allNewF (allOldF (allNewF (allOldF (allNewF (allOldF (
    mtF vr7 vr6 vr5 vr4 ⟹ mtF vr3 vr2 vr1 vr0 ⟹
      (lexLtF vr7 vr6 vr3 vr2 ⇔ lexLtF vr5 vr4 vr1 vr0)))))))))

/-- Matched indices carry the same letter. -/
noncomputable def mtLabS : certLang.Sentence :=
  allNewF (allOldF (allNewF (allOldF (allOldF (allOldF (allOldF (
    mtF vr6 vr5 vr4 vr3 ⟹ dmF vr6 vr2 ⟹ dmF vr4 vr1 ⟹
      (uAtF vr2 vr5 vr0 ⇔ vAtF vr1 vr3 vr0))))))))

/-- **The assignment is a certificate**: the ten conditions of
`DescriptiveComplexity.Pcp.CertOK` beyond well-formedness, conjoined. -/
noncomputable def certS : certLang.Sentence :=
  sleLinS ⊓ (slotExS ⊓ (dmTotS ⊓ (dmFunS ⊓ (dmDomS ⊓ (mtIxS ⊓
    (mtLeftS ⊓ (mtRightS ⊓ (mtMonoS ⊓ mtLabS))))))))

/-- **The kernel**: the instance is a well-formed Post system, and the invented
slots carry a match of it. -/
noncomputable def kernelS : certLang.Sentence := wfS ⊓ certS

/-! ### What the kernel says -/

section CertRealize

variable (ρ)

private theorem realize_inf_sentence (φ ψ : certLang.Sentence) :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) (φ ⊓ ψ) ↔
      (@Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) φ ∧
        @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) ψ) := by
  letI : certLang.Structure (A ⊕ Fin m) := certStr ρ
  exact Formula.realize_inf

private theorem realize_wfS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) wfS ↔ IsWF A := by
  simp only [wfS, ordReflS, ordTransS, ordAntisymmS, ordTotalS, uFunS, vFunS, ordF,
    uAtF, vAtF, Sentence.Realize, Formula.realize_inf, Formula.realize_imp, Formula.realize_sup,
    realize_allOldF, realize_instF₂, realize_instF₃, realize_eqF, Sum.elim_inl, Sum.elim_inr,
    relMap_inl₂, relMap_inl₃, Sum.inl.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · intro h
    exact ⟨h.ord_refl, h.ord_trans, h.ord_antisymm, h.ord_total, h.uAt_fun, h.vAt_fun⟩

private theorem realize_sleLinS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) sleLinS ↔
      IsLinOrd (certOf (A := A) ρ).SLe := by
  simp only [sleLinS, sleReflS, sleTransS, sleAntisymmS, sleTotalS, IsLinOrd, Sentence.Realize,
    Formula.realize_inf, Formula.realize_imp, Formula.realize_sup, realize_allNewF, realize_sleF,
    realize_eqF, Sum.elim_inl, Sum.elim_inr, certOf_sle, Sum.inr.injEq]

private theorem realize_slotExS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) slotExS ↔
      ∃ s : Fin m, (certOf (A := A) ρ).SLe s s := by
  simp only [slotExS, Sentence.Realize, realize_exNewF, realize_sleF, Sum.elim_inr, certOf_sle]

private theorem realize_dmTotS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) dmTotS ↔
      ∀ s : Fin m, ∃ d : A, (certOf ρ).Dm s d := by
  simp only [dmTotS, Sentence.Realize, realize_allNewF, realize_exOldF, realize_dmF,
    Sum.elim_inl, Sum.elim_inr, certOf_dm]

private theorem realize_dmFunS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) dmFunS ↔
      ∀ (s : Fin m) (d d' : A), (certOf ρ).Dm s d → (certOf ρ).Dm s d' → d = d' := by
  simp only [dmFunS, Sentence.Realize, Formula.realize_imp, realize_allNewF, realize_allOldF,
    realize_dmF, realize_eqF, Sum.elim_inl, Sum.elim_inr, certOf_dm, Sum.inl.injEq]

private theorem realize_dmDomS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) dmDomS ↔
      ∀ (s : Fin m) (d : A), (certOf ρ).Dm s d → DomG d := by
  simp only [dmDomS, domF, DomG, Sentence.Realize, Formula.realize_imp, realize_allNewF,
    realize_allOldF, realize_dmF, realize_instF₁, Sum.elim_inl, Sum.elim_inr, certOf_dm,
    relMap_inl₁]

private theorem realize_mtIxS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) mtIxS ↔
      ∀ (s : Fin m) (p : A) (s' : Fin m) (p' : A), (certOf ρ).Mt s p s' p' →
        (certOf ρ).TopIx s p ∧ (certOf ρ).BotIx s' p' := by
  simp only [mtIxS, topIxF, botIxF, usedUF, usedVF, uAtF, vAtF, Cert.TopIx, Cert.BotIx,
    UsedU, UsedV, UAt, VAt, Sentence.Realize, Formula.realize_inf, Formula.realize_imp,
    realize_allNewF, realize_allOldF, realize_exOldF, realize_mtF, realize_dmF, realize_instF₃,
    Sum.elim_inl, Sum.elim_inr, certOf_mt, certOf_dm, relMap_inl₃]

private theorem realize_mtLeftS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) mtLeftS ↔
      ∀ (s : Fin m) (p : A), (certOf ρ).TopIx s p → ∃ (s' : Fin m) (p' : A),
        (certOf ρ).Mt s p s' p' := by
  simp only [mtLeftS, topIxF, usedUF, uAtF, Cert.TopIx, UsedU, UAt, Sentence.Realize,
    Formula.realize_inf, Formula.realize_imp, realize_allNewF, realize_allOldF, realize_exNewF,
    realize_exOldF, realize_mtF, realize_dmF, realize_instF₃, Sum.elim_inl, Sum.elim_inr,
    certOf_mt, certOf_dm, relMap_inl₃]

private theorem realize_mtRightS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) mtRightS ↔
      ∀ (s' : Fin m) (p' : A), (certOf ρ).BotIx s' p' → ∃ (s : Fin m) (p : A),
        (certOf ρ).Mt s p s' p' := by
  simp only [mtRightS, botIxF, usedVF, vAtF, Cert.BotIx, UsedV, VAt, Sentence.Realize,
    Formula.realize_inf, Formula.realize_imp, realize_allNewF, realize_allOldF, realize_exNewF,
    realize_exOldF, realize_mtF, realize_dmF, realize_instF₃, Sum.elim_inl, Sum.elim_inr,
    certOf_mt, certOf_dm, relMap_inl₃]

private theorem realize_mtMonoS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) mtMonoS ↔
      ∀ (s : Fin m) (p : A) (s' : Fin m) (p' : A) (t : Fin m) (q : A) (t' : Fin m) (q' : A),
        (certOf ρ).Mt s p s' p' → (certOf ρ).Mt t q t' q' →
        ((certOf ρ).LexLt s p t q ↔ (certOf ρ).LexLt s' p' t' q') := by
  simp only [mtMonoS, lexLtF, sltF, ordLtF, ordF, Cert.LexLt, Cert.SLt, OrdLt, Ord,
    Sentence.Realize, Formula.realize_inf, Formula.realize_imp, Formula.realize_sup,
    Formula.realize_iff, Formula.realize_not, realize_allNewF, realize_allOldF, realize_mtF,
    realize_sleF, realize_instF₂, realize_eqF, Sum.elim_inl, Sum.elim_inr, certOf_mt,
    certOf_sle, relMap_inl₂, Sum.inl.injEq, Sum.inr.injEq, ne_eq]

private theorem realize_mtLabS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) mtLabS ↔
      ∀ (s : Fin m) (p : A) (s' : Fin m) (p' : A) (d d' ℓ : A),
        (certOf ρ).Mt s p s' p' → (certOf ρ).Dm s d → (certOf ρ).Dm s' d' →
        (UAt d p ℓ ↔ VAt d' p' ℓ) := by
  simp only [mtLabS, uAtF, vAtF, UAt, VAt, Sentence.Realize, Formula.realize_imp,
    Formula.realize_iff, realize_allNewF, realize_allOldF, realize_mtF, realize_dmF,
    realize_instF₃, Sum.elim_inl, Sum.elim_inr, certOf_mt, certOf_dm, relMap_inl₃]

end CertRealize

theorem realize_kernelS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) kernelS ↔ CertOK (certOf ρ) := by
  simp only [kernelS, certS, realize_inf_sentence, realize_wfS, realize_sleLinS, realize_slotExS,
    realize_dmTotS, realize_dmFunS, realize_dmDomS, realize_mtIxS, realize_mtLeftS,
    realize_mtRightS, realize_mtMonoS, realize_mtLabS]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · intro h
    exact ⟨h.wf, h.sle_lin, h.slot_ex, h.dm_tot, h.dm_fun, h.dm_dom, h.mt_ix, h.mt_left,
      h.mt_right, h.mt_mono, h.mt_lab⟩

/-! ### The assignment a certificate induces

Read back by `DescriptiveComplexity.Pcp.certOf`, this is the identity
*definitionally*, which is what makes the round trip a `rfl`. -/

/-- The assignment a certificate induces. -/
def certAssign (c : Cert A (Fin m)) : certBlock.Assignment (A ⊕ Fin m) := fun i =>
  match i with
  | CertIx.sle => fun x =>
    Sum.elim (fun _ => False)
      (fun s => Sum.elim (fun _ => False) (c.SLe s) (x (1 : Fin 2))) (x (0 : Fin 2))
  | CertIx.dm => fun x =>
    Sum.elim (fun _ => False)
      (fun s => Sum.elim (c.Dm s) (fun _ => False) (x (1 : Fin 2))) (x (0 : Fin 2))
  | CertIx.mt => fun x =>
    Sum.elim (fun _ => False) (fun s =>
      Sum.elim (fun p =>
        Sum.elim (fun _ => False) (fun s' =>
          Sum.elim (fun p' => c.Mt s p s' p') (fun _ => False) (x (3 : Fin 4)))
          (x (2 : Fin 4)))
        (fun _ => False) (x (1 : Fin 4)))
      (x (0 : Fin 4))

omit [Language.pcp.Structure A] [Nonempty A] in
@[simp]
theorem certOf_certAssign (c : Cert A (Fin m)) : certOf (certAssign c) = c := rfl

end Structures

end Pcp

/-! ### The theorems -/

/-- **`PCP` is definable in `∃SO[new]`**: the invented values are the slots of
the sequence of dominoes, and the kernel says that they carry a match – with
the common word never written down, only the matching between the two ways of
cutting it into blocks. -/
theorem pcp_sigmaSONewDefinable : SigmaSONewDefinable PCP := by
  refine ⟨Pcp.certBlock, Pcp.kernelS, ?_⟩
  intro A _ _ _
  refine Iff.trans (Pcp.pcpOn_iff_cert A) ?_
  constructor
  · rintro ⟨n, c, hc⟩
    refine ⟨n, ?_⟩
    rw [sorealize_singleton]
    refine ⟨Pcp.certAssign c, (Pcp.realize_kernelS (ρ := Pcp.certAssign c)).mpr ?_⟩
    rwa [Pcp.certOf_certAssign]
  · rintro ⟨m, hm⟩
    rw [sorealize_singleton] at hm
    obtain ⟨ρ, hρ⟩ := hm
    exact ⟨m, Pcp.certOf ρ, (Pcp.realize_kernelS (ρ := ρ)).mp hρ⟩

/-- **`PCP` is in RE.** The certificate is a sequence of dominoes together with
a matching between the two parses of the word it spells – a finite object, but
no function of the instance bounds its length: that is exactly the difference
between `Σ₁` and `∃SO[new]`, and between NP and RE. -/
theorem pcp_mem_RE : PCP ∈ RE := pcp_sigmaSONewDefinable

/-- **`PCP` first-order-reduces to finite satisfiability.** No new hardness work
is needed: `DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable` is proved
for an arbitrary source vocabulary, so putting a problem in RE reduces it to
`DescriptiveComplexity.FINSAT` at once. -/
theorem pcp_le_finsat : Nonempty (PCP ≤ʳᶠᵒ[≤] FINSAT) :=
  finsat_hard_of_sigmaSONewDefinable PCP pcp_sigmaSONewDefinable

end DescriptiveComplexity
