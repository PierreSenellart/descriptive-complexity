/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.FinSat.Invented
import DescriptiveComplexity.RecursivelyEnumerable

/-!
# FINSAT is in RE

The membership half of Trakhtenbrot's theorem: finite satisfiability of an
encoded sentence is definable in `∃SO[new]`
(`DescriptiveComplexity.finsat_sigmaSONewDefinable`), the logic defining RE.

The mathematical content is
`DescriptiveComplexity.FinSat.finSatOn_iff_cert`: an encoded sentence has a
finite model exactly when a finite set of invented values carries a
*certificate* – a model, environments with their graph, and truth values for
the nodes and for the atoms. This file is that statement written out in
syntax:

* the invented values are the extension `A ⊕ Fin m` of the universe, `m`
  unbounded – the only difference from a `Σ₁` definition, and what puts the
  problem beyond NP;
* the five components of the certificate are the relation variables of a
  single existential second-order block
  (`DescriptiveComplexity.FinSat.certBlock`);
* every condition on them is a conjunct of the first-order kernel, with each
  quantifier **guarded by its sort**: the variables ranging over the instance
  by `old`, those ranging over the invented values by its negation. The guards
  are what make the kernel say exactly the certificate conditions, in both
  directions, rather than something stronger on one side.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace FinSat

/-! ### The second-order block -/

/-- The relation variables of the `∃SO[new]` definition of FINSAT: the model,
the environments, the graph of an environment, the truth values of the nodes
and the truth values of the atoms. -/
inductive CertIx : Type
  /-- The elements of the model. -/
  | elt
  /-- The environments. -/
  | env
  /-- `val e x d`: the environment `e` gives the variable `x` the value `d`. -/
  | val
  /-- `gv g e`: the node `g` holds under the environment `e`. -/
  | gv
  /-- `hv g e`: the atom at `g` holds under the environment `e`. -/
  | hv
  deriving DecidableEq

instance : Fintype CertIx where
  elems := {CertIx.elt, CertIx.env, CertIx.val, CertIx.gv, CertIx.hv}
  complete := by intro i; cases i <;> decide

/-- The single existential block of the definition. -/
def certBlock : SOBlock where
  ι := CertIx
  arity
    | .elt => 1
    | .env => 1
    | .val => 3
    | .gv => 2
    | .hv => 2

/-- The vocabulary of the kernel: that of the instance, the marker `old` of the
original elements, and the five relation variables. -/
abbrev certLang : Language := soLang (newLang Language.finsat) [certBlock]

/-- A relation symbol of the instance, in the kernel's vocabulary. -/
abbrev instSym {n : ℕ} (R : Language.finsat.Relations n) : certLang.Relations n :=
  Sum.inl (Sum.inl R)

/-- The marker of the original elements, in the kernel's vocabulary. -/
abbrev oldSym : certLang.Relations 1 := Sum.inl (Sum.inr Language.oldSym)

/-- The relation variable of the model. -/
abbrev eltSym : certLang.Relations 1 := Sum.inr ⟨CertIx.elt, rfl⟩

/-- The relation variable of the environments. -/
abbrev envSym : certLang.Relations 1 := Sum.inr ⟨CertIx.env, rfl⟩

/-- The relation variable of the graph of an environment. -/
abbrev valSym : certLang.Relations 3 := Sum.inr ⟨CertIx.val, rfl⟩

/-- The relation variable of the truth values of the nodes. -/
abbrev gSym : certLang.Relations 2 := Sum.inr ⟨CertIx.gv, rfl⟩

/-- The relation variable of the truth values of the atoms. -/
abbrev hSym : certLang.Relations 2 := Sum.inr ⟨CertIx.hv, rfl⟩

/-! ### The extended universe -/

section Structures

variable {A : Type} [Language.finsat.Structure A] {m : ℕ}

/-- The vocabulary of the instance, read on the extended universe: a relation
holds only of original elements, and there of what it holds of in the
instance. -/
noncomputable scoped instance extFinsat : Language.finsat.Structure (A ⊕ Fin m) :=
  extBase Language.finsat A m

/-- The structure the kernel is read in: the extended structure together with
an assignment of the relation variables. -/
@[instance_reducible]
noncomputable def certStr (ρ : certBlock.Assignment (A ⊕ Fin m)) :
    certLang.Structure (A ⊕ Fin m) :=
  @sumStructure (newLang Language.finsat) certBlock.lang (A ⊕ Fin m)
    (extStructure Language.finsat A m) (certBlock.structure ρ)

/-! ### The instance, read on the extended universe

A relation of the instance holds on the extended universe only of original
elements, and there of what it holds of in the instance – so at original
arguments the kernel reads the instance itself. -/

theorem relMap_inl {k : ℕ} (R : Language.finsat.Relations k) (y : Fin k → A) :
    RelMap (L := Language.finsat) (M := A ⊕ Fin m) R (fun i => Sum.inl (y i)) ↔ RelMap R y := by
  constructor
  · rintro ⟨y', hy', h⟩
    have hyy : y = y' := funext fun i => Sum.inl_injective (hy' i)
    rw [hyy]
    exact h
  · exact fun h => ⟨y, fun _ => rfl, h⟩

@[simp]
theorem relMap_inl₁ (R : Language.finsat.Relations 1) (a : A) :
    RelMap (L := Language.finsat) (M := A ⊕ Fin m) R ![Sum.inl a] ↔ RelMap R ![a] := by
  have h : (![Sum.inl a] : Fin 1 → A ⊕ Fin m) = fun i => Sum.inl (![a] i) := by
    funext i; fin_cases i; rfl
  rw [h, relMap_inl]

@[simp]
theorem relMap_inl₂ (R : Language.finsat.Relations 2) (a b : A) :
    RelMap (L := Language.finsat) (M := A ⊕ Fin m) R ![Sum.inl a, Sum.inl b] ↔
      RelMap R ![a, b] := by
  have h : (![Sum.inl a, Sum.inl b] : Fin 2 → A ⊕ Fin m) = fun i => Sum.inl (![a, b] i) := by
    funext i; fin_cases i <;> rfl
  rw [h, relMap_inl]

@[simp]
theorem relMap_inl₃ (R : Language.finsat.Relations 3) (a b c : A) :
    RelMap (L := Language.finsat) (M := A ⊕ Fin m) R ![Sum.inl a, Sum.inl b, Sum.inl c] ↔
      RelMap R ![a, b, c] := by
  have h : (![Sum.inl a, Sum.inl b, Sum.inl c] : Fin 3 → A ⊕ Fin m) =
      fun i => Sum.inl (![a, b, c] i) := by
    funext i; fin_cases i <;> rfl
  rw [h, relMap_inl]

/-! ### The certificate an assignment carries

The five relation variables, read at the sorts they are meant for: the model
and the environments among the invented values, the graph of an environment and
the truth values across the two sorts. These are the components of the
certificate `DescriptiveComplexity.FinSat.CertOK` the kernel says the
assignment is. -/

section Carried

omit [Language.finsat.Structure A]

variable (ρ : certBlock.Assignment (A ⊕ Fin m))

/-- The elements of the model an assignment carries. -/
def certElt (d : Fin m) : Prop := ρ CertIx.elt ![Sum.inr d]

/-- The environments an assignment carries. -/
def certEnv (e : Fin m) : Prop := ρ CertIx.env ![Sum.inr e]

/-- The graph of an environment, read off an assignment. -/
def certVal (e : Fin m) (x : A) (d : Fin m) : Prop :=
  ρ CertIx.val ![Sum.inr e, Sum.inl x, Sum.inr d]

/-- The truth values of the nodes an assignment carries. -/
def certG (g : A) (e : Fin m) : Prop := ρ CertIx.gv ![Sum.inl g, Sum.inr e]

/-- The truth values of the atoms an assignment carries. -/
def certH (g : A) (e : Fin m) : Prop := ρ CertIx.hv ![Sum.inl g, Sum.inr e]

end Carried

variable {ρ : certBlock.Assignment (A ⊕ Fin m)} {γ : Type}

/-! ### Atomic formulas -/

/-- An atom of a unary relation of the instance. -/
noncomputable def instF₁ (R : Language.finsat.Relations 1) (x : γ) : certLang.Formula γ :=
  fo%[x] (instSym R)(x)

/-- An atom of a binary relation of the instance. -/
noncomputable def instF₂ (R : Language.finsat.Relations 2) (x y : γ) : certLang.Formula γ :=
  fo%[x, y] (instSym R)(x, y)

/-- An atom of a ternary relation of the instance. -/
noncomputable def instF₃ (R : Language.finsat.Relations 3) (x y z : γ) : certLang.Formula γ :=
  fo%[x, y, z] (instSym R)(x, y, z)

/-- `x` is an original element. -/
noncomputable def oldF (x : γ) : certLang.Formula γ := fo%[x] oldSym(x)

/-- `x` is an element of the model. -/
noncomputable def eltF (x : γ) : certLang.Formula γ := fo%[x] eltSym(x)

/-- `x` is an environment. -/
noncomputable def envF (x : γ) : certLang.Formula γ := fo%[x] envSym(x)

/-- The environment `e` gives the variable `x` the value `d`. -/
noncomputable def valF (e x d : γ) : certLang.Formula γ := fo%[e, x, d] valSym(e, x, d)

/-- The node `g` holds under the environment `e`. -/
noncomputable def gF (g e : γ) : certLang.Formula γ := fo%[g, e] gSym(g, e)

/-- The atom at `g` holds under the environment `e`. -/
noncomputable def hF (g e : γ) : certLang.Formula γ := fo%[g, e] hSym(g, e)

@[simp]
theorem realize_instF₁ (R : Language.finsat.Relations 1) (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (instF₁ R x) v ↔
      RelMap (L := Language.finsat) R ![v x] := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₁, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_instF₂ (R : Language.finsat.Relations 2) (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (instF₂ R x y) v ↔
      RelMap (L := Language.finsat) R ![v x, v y] := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₂, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_instF₃ (R : Language.finsat.Relations 3) (x y z : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (instF₃ R x y z) v ↔
      RelMap (L := Language.finsat) R ![v x, v y, v z] := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [instF₃, realize_rel₃]
  exact Iff.rfl

@[simp]
theorem realize_oldF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (oldF x) v ↔ IsOld (v x) := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [oldF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_eltF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (eltF x) v ↔ ρ CertIx.elt ![v x] := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [eltF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_envF (x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (envF x) v ↔ ρ CertIx.env ![v x] := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [envF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_valF (e x d : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (valF e x d) v ↔
      ρ CertIx.val ![v e, v x, v d] := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [valF, realize_rel₃]
  exact Iff.rfl

@[simp]
theorem realize_gF (g e : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (gF g e) v ↔ ρ CertIx.gv ![v g, v e] := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [gF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_hF (g e : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (hF g e) v ↔ ρ CertIx.hv ![v g, v e] := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [hF, Formula.realize_rel₂]
  exact Iff.rfl

/-- Equality of two variables. -/
noncomputable def eqF (x y : γ) : certLang.Formula γ := fo%[x, y] x ≐ y

@[simp]
theorem realize_eqF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (eqF x y) v ↔ v x = v y := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  rw [eqF, Formula.realize_equal]
  exact Iff.rfl

/-! ### Naming the symbols of the instance -/

/-- The order of the syntax. -/
noncomputable def leF (x y : γ) : certLang.Formula γ := instF₂ Language.finsatLeSym x y

/-- The node `g` is a conjunction. -/
noncomputable def andNF (g : γ) : certLang.Formula γ := instF₁ Language.finsatAndSym g

/-- The node `g` is a disjunction. -/
noncomputable def orNF (g : γ) : certLang.Formula γ := instF₁ Language.finsatOrSym g

/-- The node `g` is a universal quantifier. -/
noncomputable def allNF (g : γ) : certLang.Formula γ := instF₁ Language.finsatAllSym g

/-- The node `g` is an existential quantifier. -/
noncomputable def exNF (g : γ) : certLang.Formula γ := instF₁ Language.finsatExSym g

/-- The node `c` is a child of the node `g`. -/
noncomputable def childF (g c : γ) : certLang.Formula γ := instF₂ Language.finsatChildSym g c

/-- The quantifier node `g` binds the variable `x`. -/
noncomputable def bindF (g x : γ) : certLang.Formula γ := instF₂ Language.finsatBindSym g x

/-- The node `g` is the literal `x = y`. -/
noncomputable def eqLF (g x y : γ) : certLang.Formula γ := instF₃ Language.finsatEqSym g x y

/-- The node `g` is the literal `x ≠ y`. -/
noncomputable def neqLF (g x y : γ) : certLang.Formula γ := instF₃ Language.finsatNeqSym g x y

/-- The node `g` is a positive atom of the symbol `s`. -/
noncomputable def posLF (g s : γ) : certLang.Formula γ := instF₂ Language.finsatPosSym g s

/-- The node `g` is a negated atom of the symbol `s`. -/
noncomputable def negLF (g s : γ) : certLang.Formula γ := instF₂ Language.finsatNegSym g s

/-- The argument of the atom `g` at position `p` is the variable `x`. -/
noncomputable def argF (g p x : γ) : certLang.Formula γ := instF₃ Language.finsatArgSym g p x

/-- The symbol `s` has an argument position `p`. -/
noncomputable def sigF (s p : γ) : certLang.Formula γ := instF₂ Language.finsatSigSym s p

/-- The node `g` is the root of the encoded sentence. -/
noncomputable def rootF (g : γ) : certLang.Formula γ := instF₁ Language.finsatRootSym g

@[simp]
theorem realize_leF (x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (leF x y) v ↔
      RelMap (L := Language.finsat) Language.finsatLeSym ![v x, v y] := realize_instF₂ _ _ _ _

@[simp]
theorem realize_andNF (g : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (andNF g) v ↔
      RelMap (L := Language.finsat) Language.finsatAndSym ![v g] := realize_instF₁ _ _ _

@[simp]
theorem realize_orNF (g : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (orNF g) v ↔
      RelMap (L := Language.finsat) Language.finsatOrSym ![v g] := realize_instF₁ _ _ _

@[simp]
theorem realize_allNF (g : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (allNF g) v ↔
      RelMap (L := Language.finsat) Language.finsatAllSym ![v g] := realize_instF₁ _ _ _

@[simp]
theorem realize_exNF (g : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (exNF g) v ↔
      RelMap (L := Language.finsat) Language.finsatExSym ![v g] := realize_instF₁ _ _ _

@[simp]
theorem realize_childF (g c : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (childF g c) v ↔
      RelMap (L := Language.finsat) Language.finsatChildSym ![v g, v c] := realize_instF₂ _ _ _ _

@[simp]
theorem realize_bindF (g x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (bindF g x) v ↔
      RelMap (L := Language.finsat) Language.finsatBindSym ![v g, v x] := realize_instF₂ _ _ _ _

@[simp]
theorem realize_eqLF (g x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (eqLF g x y) v ↔
      RelMap (L := Language.finsat) Language.finsatEqSym ![v g, v x, v y] :=
  realize_instF₃ _ _ _ _ _

@[simp]
theorem realize_neqLF (g x y : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (neqLF g x y) v ↔
      RelMap (L := Language.finsat) Language.finsatNeqSym ![v g, v x, v y] :=
  realize_instF₃ _ _ _ _ _

@[simp]
theorem realize_posLF (g s : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (posLF g s) v ↔
      RelMap (L := Language.finsat) Language.finsatPosSym ![v g, v s] := realize_instF₂ _ _ _ _

@[simp]
theorem realize_negLF (g s : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (negLF g s) v ↔
      RelMap (L := Language.finsat) Language.finsatNegSym ![v g, v s] := realize_instF₂ _ _ _ _

@[simp]
theorem realize_argF (g p x : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (argF g p x) v ↔
      RelMap (L := Language.finsat) Language.finsatArgSym ![v g, v p, v x] :=
  realize_instF₃ _ _ _ _ _

@[simp]
theorem realize_sigF (s p : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (sigF s p) v ↔
      RelMap (L := Language.finsat) Language.finsatSigSym ![v s, v p] := realize_instF₂ _ _ _ _

@[simp]
theorem realize_rootF (g : γ) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (rootF g) v ↔
      RelMap (L := Language.finsat) Language.finsatRootSym ![v g] := realize_instF₁ _ _ _

/-! ### Guarded quantifiers

Every quantifier of the kernel ranges over one of the two sorts of the extended
universe – the original elements, marked by `old`, and the invented values –
and is guarded accordingly. The guards are not decoration: one missing in a
*hypothesis* position (inside the update relation of the universal-quantifier
clause, or in the agreement hypotheses of `g_ext` and `atom_coh`) makes the
kernel demand of an assignment more than the certificate gives, and that
direction of the correspondence no longer closes.

A variable is named by its distance from its binder: `vr0` is bound by the
innermost guarded quantifier, `vr1` by the one just outside it, and so on – so
passing under one more quantifier increments every index, and `up` is that same
shift applied to a variable given by name. -/

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

/-- `∃ x, old x ∧ φ`: a quantifier over the original elements. -/
noncomputable def exOldF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iExs Unit (oldF vr0 ⊓ φ)

/-- `∀ x, old x → φ`: a quantifier over the original elements. -/
noncomputable def allOldF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iAlls Unit (oldF vr0 ⟹ φ)

/-- `∃ d, ¬old d ∧ φ`: a quantifier over the invented values. -/
noncomputable def exNewF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iExs Unit (∼(oldF vr0) ⊓ φ)

/-- `∀ d, ¬old d → φ`: a quantifier over the invented values. -/
noncomputable def allNewF (φ : certLang.Formula (γ ⊕ Unit)) : certLang.Formula γ :=
  Formula.iAlls Unit (∼(oldF vr0) ⟹ φ)

omit [Language.finsat.Structure A] in
theorem exists_inr_of_not_isOld {x : A ⊕ Fin m} (h : ¬IsOld x) : ∃ j : Fin m, x = Sum.inr j := by
  cases x with
  | inl a => exact absurd (isOld_inl a) h
  | inr j => exact ⟨j, rfl⟩

@[simp]
theorem realize_exOldF (φ : certLang.Formula (γ ⊕ Unit)) (v : γ → A ⊕ Fin m) :
    @Formula.Realize certLang _ (certStr ρ) γ (exOldF φ) v ↔
      ∃ a : A, @Formula.Realize certLang _ (certStr ρ) (γ ⊕ Unit) φ
        (Sum.elim v fun _ => Sum.inl a) := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
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
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
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
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
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
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [allNewF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_not,
    realize_oldF, Sum.elim_inr]
  constructor
  · exact fun h j => h (fun _ => Sum.inr j) (not_isOld_inr j)
  · intro h i hi
    obtain ⟨j, hj⟩ := exists_inr_of_not_isOld hi
    have hie : i = fun _ => Sum.inr j := funext fun u => by cases u; exact hj
    rw [hie]
    exact h j

/-! ### Well-formedness

The kernel has to *check* well-formedness, since junk instances are
no-instances: each condition of `DescriptiveComplexity.FinSat.IsWF` is one
conjunct, every quantifier ranging over the original elements. -/

/-- The order of the syntax is reflexive. -/
noncomputable def ordReflS : certLang.Sentence := allOldF (leF vr0 vr0)

/-- The order of the syntax is transitive. -/
noncomputable def ordTransS : certLang.Sentence :=
  allOldF (allOldF (allOldF (leF vr2 vr1 ⊓ leF vr1 vr0 ⟹ leF vr2 vr0)))

/-- The order of the syntax is antisymmetric. -/
noncomputable def ordAntisymmS : certLang.Sentence :=
  allOldF (allOldF (leF vr1 vr0 ⊓ leF vr0 vr1 ⟹ eqF vr1 vr0))

/-- The order of the syntax is total. -/
noncomputable def ordTotalS : certLang.Sentence :=
  allOldF (allOldF (leF vr1 vr0 ⊔ leF vr0 vr1))

/-- Children come strictly earlier in the order of the syntax. -/
noncomputable def childLtS : certLang.Sentence :=
  allOldF (allOldF (childF vr1 vr0 ⟹ leF vr0 vr1 ⊓ ∼(eqF vr0 vr1)))

/-- An atom has at most one argument at each position. -/
noncomputable def argFunS : certLang.Sentence :=
  allOldF (allOldF (allOldF (allOldF (argF vr3 vr2 vr1 ⊓ argF vr3 vr2 vr0 ⟹ eqF vr1 vr0))))

/-- An atom has at most one relation symbol. -/
noncomputable def atomSymS : certLang.Sentence :=
  allOldF (allOldF (allOldF ((posLF vr2 vr1 ⊔ negLF vr2 vr1) ⊓
    (posLF vr2 vr0 ⊔ negLF vr2 vr0) ⟹ eqF vr1 vr0)))

/-- An atom only has arguments at the positions of its symbol's signature. -/
noncomputable def argSigS : certLang.Sentence :=
  allOldF (allOldF (allOldF (allOldF ((posLF vr3 vr2 ⊔ negLF vr3 vr2) ⊓ argF vr3 vr1 vr0 ⟹
    sigF vr2 vr1))))

/-- An atom has an argument at every position of its symbol's signature. -/
noncomputable def argTotS : certLang.Sentence :=
  allOldF (allOldF (allOldF ((posLF vr2 vr1 ⊔ negLF vr2 vr1) ⊓ sigF vr1 vr0 ⟹
    exOldF (argF vr3 vr1 vr0))))

/-- **The instance is well-formed**: the nine conditions of
`DescriptiveComplexity.FinSat.IsWF`, conjoined. -/
noncomputable def wfS : certLang.Sentence :=
  ordReflS ⊓ (ordTransS ⊓ (ordAntisymmS ⊓ (ordTotalS ⊓ (childLtS ⊓
    (argFunS ⊓ (atomSymS ⊓ (argSigS ⊓ argTotS)))))))

theorem realize_wfS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) wfS ↔ IsWF A := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [wfS, ordReflS, ordTransS, ordAntisymmS, ordTotalS, childLtS, argFunS, atomSymS,
    argSigS, argTotS, Sentence.Realize, Formula.realize_inf, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_not, realize_allOldF, realize_exOldF, realize_leF,
    realize_childF, realize_argF, realize_sigF, realize_posLF, realize_negLF, realize_eqF,
    Sum.elim_inl, Sum.elim_inr, relMap_inl₂, relMap_inl₃, Sum.inl.injEq, and_imp]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, h3, h4, fun g c hgc => ⟨(h5 g c hgc).1, (h5 g c hgc).2⟩, h6, h7, h8, h9⟩
  · intro h
    exact ⟨h.ord_refl, h.ord_trans, h.ord_antisymm, h.ord_total,
      fun g c hgc => ⟨(h.child_lt g c hgc).1, (h.child_lt g c hgc).2⟩,
      h.arg_fun, h.atom_sym, h.arg_sig, h.arg_tot⟩

/-! ### The truth definition

`DescriptiveComplexity.FinSat.CertStep` written out: one disjunct per kind of
node, the environments and the values of the model ranging over the invented
values and everything read off the encoding over the original elements. -/

/-- `e'` is the environment `e` with the variable `x` set to the value `d`
(`DescriptiveComplexity.FinSat.UpdAt`). Its inner quantifiers carry guards
like every other, and here it matters: this clause occurs in a *hypothesis*
position inside the universal-quantifier disjunct below. -/
noncomputable def updF (e e' x d : γ) : certLang.Formula γ :=
  valF e' x d ⊓ allOldF (∼(eqF vr0 (up x)) ⟹
    allNewF (valF (up (up e')) vr1 vr0 ⇔ valF (up (up e)) vr1 vr0))

/-- The value of the node `g` under the environment `e`, one disjunct per kind
of node. -/
noncomputable def stepBodyF (g e : γ) : certLang.Formula γ :=
  (andNF g ⊓ allOldF (childF (up g) vr0 ⟹ gF vr0 (up e))) ⊔
  ((orNF g ⊓ exOldF (childF (up g) vr0 ⊓ gF vr0 (up e))) ⊔
    ((allNF g ⊓ allOldF (bindF (up g) vr0 ⟹
        allNewF (eltF vr0 ⟹
          allNewF (envF vr0 ⟹ (updF (up (up (up e))) vr0 vr2 vr1 ⟹
            allOldF (childF (up (up (up (up g)))) vr0 ⟹ gF vr0 vr1)))))) ⊔
      ((exNF g ⊓ exOldF (bindF (up g) vr0 ⊓
          exNewF (eltF vr0 ⊓
            exNewF (envF vr0 ⊓ (updF (up (up (up e))) vr0 vr2 vr1 ⊓
              exOldF (childF (up (up (up (up g)))) vr0 ⊓ gF vr0 vr1)))))) ⊔
        (exOldF (exOldF (eqLF (up (up g)) vr1 vr0 ⊓
            allNewF (valF (up (up (up e))) vr2 vr0 ⇔ valF (up (up (up e))) vr1 vr0))) ⊔
          (exOldF (exOldF (neqLF (up (up g)) vr1 vr0 ⊓
              exNewF (valF (up (up (up e))) vr2 vr0 ⊓
                ∼(valF (up (up (up e))) vr1 vr0)))) ⊔
            (exOldF (posLF (up g) vr0 ⊓ hF (up g) (up e)) ⊔
              exOldF (negLF (up g) vr0 ⊓ ∼(hF (up g) (up e)))))))))

/-- The disjunction is the truth definition read on the certificate the
assignment carries. -/
theorem realize_stepBodyF (g e : γ) (v : γ → A ⊕ Fin m) (a : A) (i : Fin m)
    (hg : v g = Sum.inl a) (he : v e = Sum.inr i) :
    @Formula.Realize certLang _ (certStr ρ) γ (stepBodyF g e) v ↔
      CertStep (certElt ρ) (certEnv ρ) (certVal ρ) (certG ρ) (certH ρ) a i := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [stepBodyF, updF, CertStep, UpdAt, certElt, certEnv, certVal, certG, certH,
    AndG, OrG, AllG, ExG, ChildG, BindG, EqG, NeqG, PosG, NegG,
    Formula.realize_inf, Formula.realize_sup, Formula.realize_imp, Formula.realize_iff,
    Formula.realize_not, realize_allOldF, realize_exOldF, realize_allNewF, realize_exNewF,
    realize_andNF, realize_orNF, realize_allNF, realize_exNF, realize_childF, realize_bindF,
    realize_eqLF, realize_neqLF, realize_posLF, realize_negLF, realize_eltF, realize_envF,
    realize_valF, realize_gF, realize_hF, realize_eqF, Sum.elim_inl, Sum.elim_inr,
    relMap_inl₁, relMap_inl₂, relMap_inl₃, hg, he, ne_eq, Sum.inl.injEq]

/-! ### The certificate

One conjunct per field of `DescriptiveComplexity.FinSat.CertOK`. -/

/-- The model is nonempty. -/
noncomputable def eltNeS : certLang.Sentence := exNewF (eltF vr0)

/-- There is at least one environment. -/
noncomputable def envNeS : certLang.Sentence := exNewF (envF vr0)

/-- An environment gives every variable a value in the model. -/
noncomputable def valTotalS : certLang.Sentence :=
  allNewF (envF vr0 ⟹ allOldF (exNewF (eltF vr0 ⊓ valF vr2 vr1 vr0)))

/-- An environment gives every variable at most one value. -/
noncomputable def valFunS : certLang.Sentence :=
  allNewF (envF vr0 ⟹ allOldF (allNewF (allNewF
    (valF vr3 vr2 vr1 ⟹ (valF vr3 vr2 vr0 ⟹ eqF vr1 vr0)))))

/-- Environments are closed under updating one variable. -/
noncomputable def valUpdateS : certLang.Sentence :=
  allNewF (envF vr0 ⟹ allOldF (allNewF (eltF vr0 ⟹
    exNewF (envF vr0 ⊓ updF vr3 vr0 vr2 vr1))))

/-- The truth value of a node depends on the environment only through the
values it gives. -/
noncomputable def gExtS : certLang.Sentence :=
  allOldF (allNewF (allNewF (envF vr1 ⟹ (envF vr0 ⟹
    (allOldF (allNewF (valF vr3 vr1 vr0 ⇔ valF vr2 vr1 vr0)) ⟹
      (gF vr2 vr1 ⇔ gF vr2 vr0))))))

/-- The truth values obey the truth definition. -/
noncomputable def stepS : certLang.Sentence :=
  allOldF (allNewF (envF vr0 ⟹ (gF vr1 vr0 ⇔ stepBodyF vr1 vr0)))

/-- Two atoms of the same relation symbol whose arguments have the same values
have the same truth value. -/
noncomputable def atomCohS : certLang.Sentence :=
  allOldF (allOldF (allOldF (allNewF (allNewF (envF vr1 ⟹ (envF vr0 ⟹
    ((posLF vr4 vr2 ⊔ negLF vr4 vr2) ⟹ ((posLF vr3 vr2 ⊔ negLF vr3 vr2) ⟹
      (allOldF (allOldF (allOldF (argF vr7 vr2 vr1 ⟹ (argF vr6 vr2 vr0 ⟹
        allNewF (valF vr5 vr2 vr0 ⇔ valF vr4 vr1 vr0))))) ⟹
        (hF vr4 vr1 ⇔ hF vr3 vr0))))))))))

/-- The root holds under every environment. -/
noncomputable def rootHoldsS : certLang.Sentence :=
  allOldF (rootF vr0 ⟹ allNewF (envF vr0 ⟹ gF vr1 vr0))

/-- **The assignment is a certificate**: the nine conditions of
`DescriptiveComplexity.FinSat.CertOK`, conjoined. -/
noncomputable def certS : certLang.Sentence :=
  eltNeS ⊓ (envNeS ⊓ (valTotalS ⊓ (valFunS ⊓ (valUpdateS ⊓ (gExtS ⊓
    (stepS ⊓ (atomCohS ⊓ rootHoldsS)))))))

theorem realize_eltNeS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) eltNeS ↔ ∃ d, certElt ρ d := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, eltNeS, realize_exNewF, realize_eltF, Sum.elim_inr, certElt]

theorem realize_envNeS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) envNeS ↔ ∃ e, certEnv ρ e := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, envNeS, realize_exNewF, realize_envF, Sum.elim_inr, certEnv]

theorem realize_valTotalS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) valTotalS ↔
      ∀ e, certEnv ρ e → ∀ x : A, ∃ d, certElt ρ d ∧ certVal ρ e x d := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, valTotalS, realize_allNewF, realize_allOldF, realize_exNewF,
    Formula.realize_imp, Formula.realize_inf, realize_envF, realize_eltF, realize_valF,
    Sum.elim_inl, Sum.elim_inr, certEnv, certElt, certVal]

theorem realize_valFunS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) valFunS ↔
      ∀ e, certEnv ρ e → ∀ (x : A) (d d' : Fin m), certVal ρ e x d → certVal ρ e x d' → d = d' := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, valFunS, realize_allNewF, realize_allOldF, Formula.realize_imp,
    realize_envF, realize_valF, realize_eqF, Sum.elim_inl, Sum.elim_inr, Sum.inr.injEq,
    certEnv, certVal]

theorem realize_valUpdateS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) valUpdateS ↔
      ∀ e, certEnv ρ e → ∀ (x : A) (d : Fin m), certElt ρ d →
        ∃ e', certEnv ρ e' ∧ UpdAt (certVal ρ) e e' x d := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, valUpdateS, updF, UpdAt, realize_allNewF, realize_allOldF,
    realize_exNewF, Formula.realize_imp, Formula.realize_inf, Formula.realize_iff,
    Formula.realize_not, realize_envF, realize_eltF, realize_valF, realize_eqF,
    Sum.elim_inl, Sum.elim_inr, ne_eq, Sum.inl.injEq, certEnv, certElt, certVal]

theorem realize_gExtS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) gExtS ↔
      ∀ (g : A) (e e' : Fin m), certEnv ρ e → certEnv ρ e' →
        (∀ x d, certVal ρ e x d ↔ certVal ρ e' x d) → (certG ρ g e ↔ certG ρ g e') := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, gExtS, realize_allOldF, realize_allNewF, Formula.realize_imp,
    Formula.realize_iff, realize_envF, realize_valF, realize_gF, Sum.elim_inl, Sum.elim_inr,
    certEnv, certVal, certG]

theorem realize_stepS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) stepS ↔
      ∀ (g : A) (e : Fin m), certEnv ρ e →
        (certG ρ g e ↔
          CertStep (certElt ρ) (certEnv ρ) (certVal ρ) (certG ρ) (certH ρ) g e) := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, stepS, realize_allOldF, realize_allNewF, Formula.realize_imp,
    Formula.realize_iff, realize_envF, realize_gF, Sum.elim_inl, Sum.elim_inr, certEnv, certG]
  refine forall_congr' fun a => forall_congr' fun i => imp_congr_right fun _ => ?_
  exact iff_congr Iff.rfl (realize_stepBodyF vr1 vr0 _ a i rfl rfl)

theorem realize_atomCohS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) atomCohS ↔
      ∀ (g g' s : A) (e e' : Fin m), certEnv ρ e → certEnv ρ e' →
        (PosG g s ∨ NegG g s) → (PosG g' s ∨ NegG g' s) →
        (∀ p x x', ArgG g p x → ArgG g' p x' → ∀ d, (certVal ρ e x d ↔ certVal ρ e' x' d)) →
        (certH ρ g e ↔ certH ρ g' e') := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, atomCohS, PosG, NegG, ArgG, realize_allOldF, realize_allNewF,
    Formula.realize_imp, Formula.realize_iff, Formula.realize_sup, realize_envF, realize_posLF,
    realize_negLF, realize_argF, realize_valF, realize_hF, Sum.elim_inl, Sum.elim_inr,
    relMap_inl₂, relMap_inl₃, certEnv, certVal, certH]

theorem realize_rootHoldsS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) rootHoldsS ↔
      ∀ g : A, RootG g → ∀ e, certEnv ρ e → certG ρ g e := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  simp only [Sentence.Realize, rootHoldsS, RootG, realize_allOldF, realize_allNewF,
    Formula.realize_imp, realize_rootF, realize_envF, realize_gF, Sum.elim_inl, Sum.elim_inr,
    relMap_inl₁, certEnv, certG]

private theorem realize_inf_sentence (φ ψ : certLang.Sentence) :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) (φ ⊓ ψ) ↔
      (@Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) φ ∧
        @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) ψ) := by
  let : certLang.Structure (A ⊕ Fin m) := certStr ρ
  exact Formula.realize_inf

theorem realize_certS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) certS ↔
      CertOK (certElt ρ) (certEnv ρ) (certVal ρ) (certG ρ) (certH ρ) := by
  simp only [certS, realize_inf_sentence, realize_eltNeS, realize_envNeS, realize_valTotalS,
    realize_valFunS, realize_valUpdateS, realize_gExtS, realize_stepS, realize_atomCohS,
    realize_rootHoldsS]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · intro h
    exact ⟨h.elt_nonempty, h.env_nonempty, h.val_total, h.val_fun, h.val_update, h.g_ext,
      h.step, h.atom_coh, h.root_holds⟩

/-! ### The kernel -/

/-- **The first-order kernel of the `∃SO[new]` definition of FINSAT**: the
instance is a well-formed encoding, and the guessed relations are a certificate
of finite satisfiability. -/
noncomputable def kernelS : certLang.Sentence := wfS ⊓ certS

theorem realize_kernelS :
    @Sentence.Realize certLang (A ⊕ Fin m) (certStr ρ) kernelS ↔
      IsWF A ∧ CertOK (certElt ρ) (certEnv ρ) (certVal ρ) (certG ρ) (certH ρ) := by
  rw [kernelS, realize_inf_sentence, realize_wfS, realize_certS]

/-! ### The assignment a certificate determines -/

section Building

omit [Language.finsat.Structure A]

variable (Elt Env : Fin m → Prop) (Val : Fin m → A → Fin m → Prop) (G H : A → Fin m → Prop)

/-- **The assignment of the relation variables a certificate determines**: each
variable holds exactly at the sort its component is meant for, and nowhere else
– which is what makes the sort guards of the kernel harmless in this
direction. -/
def certAssign : certBlock.Assignment (A ⊕ Fin m) := fun i =>
  match i with
  | .elt => fun (x : Fin 1 → A ⊕ Fin m) => ∃ d, x 0 = Sum.inr d ∧ Elt d
  | .env => fun (x : Fin 1 → A ⊕ Fin m) => ∃ e, x 0 = Sum.inr e ∧ Env e
  | .val => fun (x : Fin 3 → A ⊕ Fin m) =>
      ∃ e y d, x 0 = Sum.inr e ∧ x 1 = Sum.inl y ∧ x 2 = Sum.inr d ∧ Val e y d
  | .gv => fun (x : Fin 2 → A ⊕ Fin m) => ∃ g e, x 0 = Sum.inl g ∧ x 1 = Sum.inr e ∧ G g e
  | .hv => fun (x : Fin 2 → A ⊕ Fin m) => ∃ g e, x 0 = Sum.inl g ∧ x 1 = Sum.inr e ∧ H g e

theorem certElt_certAssign : certElt (certAssign Elt Env Val G H) = Elt := by
  funext d
  refine propext ⟨?_, fun h => ⟨d, rfl, h⟩⟩
  rintro ⟨d', hd', h⟩
  obtain rfl : d = d' := by simpa using hd'
  exact h

theorem certEnv_certAssign : certEnv (certAssign Elt Env Val G H) = Env := by
  funext e
  refine propext ⟨?_, fun h => ⟨e, rfl, h⟩⟩
  rintro ⟨e', he', h⟩
  obtain rfl : e = e' := by simpa using he'
  exact h

theorem certVal_certAssign : certVal (certAssign Elt Env Val G H) = Val := by
  funext e x d
  refine propext ⟨?_, fun h => ⟨e, x, d, rfl, rfl, rfl, h⟩⟩
  rintro ⟨e', y, d', he', hy, hd', h⟩
  obtain rfl : e = e' := by simpa using he'
  obtain rfl : x = y := by simpa using hy
  obtain rfl : d = d' := by simpa using hd'
  exact h

theorem certG_certAssign : certG (certAssign Elt Env Val G H) = G := by
  funext g e
  refine propext ⟨?_, fun h => ⟨g, e, rfl, rfl, h⟩⟩
  rintro ⟨g', e', hg', he', h⟩
  obtain rfl : g = g' := by simpa using hg'
  obtain rfl : e = e' := by simpa using he'
  exact h

theorem certH_certAssign : certH (certAssign Elt Env Val G H) = H := by
  funext g e
  refine propext ⟨?_, fun h => ⟨g, e, rfl, rfl, h⟩⟩
  rintro ⟨g', e', hg', he', h⟩
  obtain rfl : g = g' := by simpa using hg'
  obtain rfl : e = e' := by simpa using he'
  exact h

end Building

end Structures

end FinSat

/-! ### Membership -/

open FinSat in
/-- **FINSAT is definable in `∃SO[new]`**, the logic defining RE: the invented
values carry a finite model of the encoded sentence together with the
environments – a *certificate*
(`DescriptiveComplexity.FinSat.finSatOn_iff_certFin`) – and the first-order
kernel `DescriptiveComplexity.FinSat.kernelS` checks that the encoding is well
formed and that the guessed relations are one.

The number of invented values is unbounded in the instance, which is exactly
what takes the problem beyond NP: a finite model of a satisfiable sentence can
be arbitrarily larger than the sentence. -/
theorem finsat_sigmaSONewDefinable : SigmaSONewDefinable FINSAT := by
  refine ⟨certBlock, kernelS, fun A _ _ _ => ?_⟩
  have hFS : FINSAT A ↔ FinSatOn A := Iff.rfl
  rw [hFS, finSatOn_iff_certFin A]
  constructor
  · rintro ⟨hwf, m, Elt, Env, Val, G, H, hc⟩
    refine ⟨m, certAssign Elt Env Val G H,
      (realize_kernelS (ρ := certAssign Elt Env Val G H)).mpr ⟨hwf, ?_⟩⟩
    rw [certElt_certAssign, certEnv_certAssign, certVal_certAssign, certG_certAssign,
      certH_certAssign]
    exact hc
  · rintro ⟨m, ρ, hρ⟩
    obtain ⟨hwf, hc⟩ := (realize_kernelS (ρ := ρ)).mp hρ
    exact ⟨hwf, m, _, _, _, _, _, hc⟩

/-- **FINSAT is in RE**. -/
theorem finsat_mem_RE : FINSAT ∈ RE :=
  (mem_RE_iff FINSAT).mpr finsat_sigmaSONewDefinable

end DescriptiveComplexity
