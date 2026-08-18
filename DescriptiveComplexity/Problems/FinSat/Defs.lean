/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation

/-!
# FINSAT: finite satisfiability of a first-order sentence

The problem of Trakhtenbrot's theorem ([Trakhtenbrot 1950][trakhtenbrot1950],
[Libkin 2004][libkin2004elements], ch. 9): *does the given first-order
sentence have a finite model?* This file carries the instance encoding – a
sentence, presented as a finite structure – and its semantics; membership in
RE and RE-hardness live in the sibling files, and the completeness theorem in
`DescriptiveComplexity.Problems.FinSat`.

## The encoding

An instance is a *parse DAG in negation normal form*. Its elements play
several roles at once – nodes, variables, relation symbols, argument
positions – and nothing forces those roles to be disjoint:

* `andN`, `orN` mark the **n-ary** conjunction and disjunction nodes: such a
  node is the conjunction (disjunction) of *all* the nodes its `child`
  relation gives it. Nothing is a binary tree, which is what lets a reduction
  write an unbounded conjunction as a single node;
* `allN`, `exN` mark the quantifier nodes, `bind` giving the variable
  quantified; a quantifier node is again read over all its children;
* the leaves are literals: `eqL g x y` and `neqL g x y` for `x = y` and
  `x ≠ y`, and `posL g s` / `negL g s` for `s(…)` and `¬s(…)`, the arguments
  of the atom being given by `arg g p x` (“the argument at position `p` is the
  variable `x`”) and the argument positions of the symbol `s` by `sig s p`;
* `root` marks the node the sentence starts at;
* `le` is a linear order on the instance. A sentence is a *string*, so an
  encoding of one may certainly carry the order of its own syntax; what the
  order buys is that `child g c → c < g` – acyclicity of the parse DAG –
  becomes first-order, while acyclicity itself is not. The membership proof
  has to *check* well-formedness, so this matters.

Negation normal form is not a matter of economy: with negation confined to the
leaves the value of a node is **monotone** in the values of its children, so
satisfaction is a least fixed point (`DescriptiveComplexity.FinSat.Gval`,
below) and no well-founded recursion on a decoded parse tree is needed
anywhere. Every first-order formula has a negation normal form, and the
hardness reduction produces one directly.

## The semantics

There is deliberately **no decoding into a `FirstOrder.Language.Sentence`**:
the relation symbols of the encoded sentence are *elements of the instance*,
so the decoded vocabulary would depend on the instance. Satisfaction is
instead defined on the encoding, Tarski-style, by
`DescriptiveComplexity.FinSat.gstep` – one clause per node kind, which is what
a reader has to check anyway – iterated on a fuel counter
(`DescriptiveComplexity.FinSat.gval`) and closed up
(`DescriptiveComplexity.FinSat.Gval`).

A *model* is a finite nonempty type `M` together with an interpretation
`I : A → (A → M) → Prop` reading a symbol and an assignment of argument
positions, required to be **local**: `I s` may only look at the positions of
the signature of `s`. Locality is what makes `I s` a relation of the arity of
`s` rather than of the whole universe, and what makes the negative-atom clause
unambiguous.

`DescriptiveComplexity.FINSAT` then holds of an instance when it is
well-formed and the *universal closure* of the encoded formula has a finite
model. Taking the universal closure costs nothing – the sentences the
reduction produces are closed – and avoids conditioning on “every variable is
bound by an ancestor”, which is a reachability property and so not
first-order.

## What is and is not claimed

RE is the logically defined class of
`DescriptiveComplexity.RecursivelyEnumerable` (definability in `∃SO[new]`), so
completeness of FINSAT for it is a statement about that logic. It becomes
*undecidability* of finite satisfiability only through the bridge to Mathlib's
computability layer (`DescriptiveComplexity.finsat_not_computable`).
-/

/- The language of encoded sentences lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.sat` and `Language.qbf`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of encoded first-order sentences in
negation normal form. -/
inductive finsatRel : ℕ → Type
  /-- `le x y`: the order of the syntax. -/
  | le : finsatRel 2
  /-- `andN g`: the node `g` is the conjunction of its children. -/
  | andN : finsatRel 1
  /-- `orN g`: the node `g` is the disjunction of its children. -/
  | orN : finsatRel 1
  /-- `allN g`: the node `g` universally quantifies its bound variable. -/
  | allN : finsatRel 1
  /-- `exN g`: the node `g` existentially quantifies its bound variable. -/
  | exN : finsatRel 1
  /-- `child g c`: the node `c` is one of the children of the node `g`. -/
  | child : finsatRel 2
  /-- `bind g x`: the quantifier node `g` binds the variable `x`. -/
  | bind : finsatRel 2
  /-- `eqL g x y`: the node `g` is the literal `x = y`. -/
  | eqL : finsatRel 3
  /-- `neqL g x y`: the node `g` is the literal `x ≠ y`. -/
  | neqL : finsatRel 3
  /-- `posL g s`: the node `g` is a positive atom of the relation symbol
  `s`. -/
  | posL : finsatRel 2
  /-- `negL g s`: the node `g` is a negated atom of the relation symbol
  `s`. -/
  | negL : finsatRel 2
  /-- `arg g p x`: the argument of the atom `g` at position `p` is the
  variable `x`. -/
  | arg : finsatRel 3
  /-- `sig s p`: the relation symbol `s` has an argument position `p`. -/
  | sig : finsatRel 2
  /-- `root g`: the node `g` is the root of the encoded sentence. -/
  | root : finsatRel 1
  deriving DecidableEq

/-- The relational vocabulary of encoded first-order sentences: a parse DAG in
negation normal form, ordered by the order of its own syntax. -/
protected def finsat : Language :=
  ⟨fun _ => Empty, finsatRel⟩

instance : IsRelational Language.finsat :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The order symbol of the syntax. -/
abbrev finsatLeSym : Language.finsat.Relations 2 := .le

/-- The symbol marking conjunction nodes. -/
abbrev finsatAndSym : Language.finsat.Relations 1 := .andN

/-- The symbol marking disjunction nodes. -/
abbrev finsatOrSym : Language.finsat.Relations 1 := .orN

/-- The symbol marking universal quantifier nodes. -/
abbrev finsatAllSym : Language.finsat.Relations 1 := .allN

/-- The symbol marking existential quantifier nodes. -/
abbrev finsatExSym : Language.finsat.Relations 1 := .exN

/-- The symbol of the child relation of the parse DAG. -/
abbrev finsatChildSym : Language.finsat.Relations 2 := .child

/-- The symbol binding a variable to a quantifier node. -/
abbrev finsatBindSym : Language.finsat.Relations 2 := .bind

/-- The symbol of positive equality literals. -/
abbrev finsatEqSym : Language.finsat.Relations 3 := .eqL

/-- The symbol of negated equality literals. -/
abbrev finsatNeqSym : Language.finsat.Relations 3 := .neqL

/-- The symbol of positive atoms. -/
abbrev finsatPosSym : Language.finsat.Relations 2 := .posL

/-- The symbol of negated atoms. -/
abbrev finsatNegSym : Language.finsat.Relations 2 := .negL

/-- The symbol giving the arguments of an atom. -/
abbrev finsatArgSym : Language.finsat.Relations 3 := .arg

/-- The symbol giving the signature of a relation symbol. -/
abbrev finsatSigSym : Language.finsat.Relations 2 := .sig

/-- The symbol marking the root node. -/
abbrev finsatRootSym : Language.finsat.Relations 1 := .root

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace FinSat

/-! ### Reading the encoding -/

section Reading

variable {A : Type} [Language.finsat.Structure A]

/-- `x` precedes `y` in the order of the syntax. -/
def Ord (x y : A) : Prop := RelMap Language.finsatLeSym ![x, y]

/-- `x` strictly precedes `y` in the order of the syntax. -/
def OrdLt (x y : A) : Prop := Ord x y ∧ x ≠ y

/-- The node `g` is a conjunction. -/
def AndG (g : A) : Prop := RelMap Language.finsatAndSym ![g]

/-- The node `g` is a disjunction. -/
def OrG (g : A) : Prop := RelMap Language.finsatOrSym ![g]

/-- The node `g` is a universal quantifier. -/
def AllG (g : A) : Prop := RelMap Language.finsatAllSym ![g]

/-- The node `g` is an existential quantifier. -/
def ExG (g : A) : Prop := RelMap Language.finsatExSym ![g]

/-- The node `c` is a child of the node `g`. -/
def ChildG (g c : A) : Prop := RelMap Language.finsatChildSym ![g, c]

/-- The quantifier node `g` binds the variable `x`. -/
def BindG (g x : A) : Prop := RelMap Language.finsatBindSym ![g, x]

/-- The node `g` is the literal `x = y`. -/
def EqG (g x y : A) : Prop := RelMap Language.finsatEqSym ![g, x, y]

/-- The node `g` is the literal `x ≠ y`. -/
def NeqG (g x y : A) : Prop := RelMap Language.finsatNeqSym ![g, x, y]

/-- The node `g` is a positive atom of the symbol `s`. -/
def PosG (g s : A) : Prop := RelMap Language.finsatPosSym ![g, s]

/-- The node `g` is a negated atom of the symbol `s`. -/
def NegG (g s : A) : Prop := RelMap Language.finsatNegSym ![g, s]

/-- The argument of the atom `g` at position `p` is the variable `x`. -/
def ArgG (g p x : A) : Prop := RelMap Language.finsatArgSym ![g, p, x]

/-- The symbol `s` has an argument position `p`. -/
def SigG (s p : A) : Prop := RelMap Language.finsatSigSym ![s, p]

/-- The node `g` is the root of the encoded sentence. -/
def RootG (g : A) : Prop := RelMap Language.finsatRootSym ![g]

end Reading

/-! ### Well-formedness

Little is required of an instance, and all of it is first-order: the order
symbol is a linear order and children come strictly earlier in it – so the
parse DAG is acyclic, on a finite instance well-founded – together with the
shape of an *atom*, which carries one symbol and exactly one argument at each
position of that symbol's signature. Nothing is required of the *kinds* of a
node nor of the multiplicity of binders: the semantics below reads every clause
of `gstep` as a disjunction, so a node with two kinds simply means the
disjunction of its two readings, and the membership kernel can mirror `gstep`
clause by clause.

The atom conditions are the ones that cannot be dispensed with, and their
reason is the membership proof rather than the semantics: there the model's
interpretation of a symbol is *recovered* from the guessed truth values of the
atoms, and two atoms of the same symbol whose arguments have the same values
must therefore have the same truth value – which they need not, if an atom may
carry two symbols, or lack an argument at a position its symbol declares. -/

/-- **Well-formedness of an encoded sentence**: the order symbol is a linear
order and the parse DAG descends along it. -/
structure IsWF (A : Type) [Language.finsat.Structure A] : Prop where
  /-- The order of the syntax is reflexive. -/
  ord_refl : ∀ x : A, Ord x x
  /-- The order of the syntax is transitive. -/
  ord_trans : ∀ x y z : A, Ord x y → Ord y z → Ord x z
  /-- The order of the syntax is antisymmetric. -/
  ord_antisymm : ∀ x y : A, Ord x y → Ord y x → x = y
  /-- The order of the syntax is total. -/
  ord_total : ∀ x y : A, Ord x y ∨ Ord y x
  /-- Children come strictly earlier: the parse DAG is acyclic. -/
  child_lt : ∀ g c : A, ChildG g c → OrdLt c g
  /-- An atom has at most one argument at each position. -/
  arg_fun : ∀ g p x x' : A, ArgG g p x → ArgG g p x' → x = x'
  /-- An atom has at most one relation symbol. -/
  atom_sym : ∀ g s s' : A, (PosG g s ∨ NegG g s) → (PosG g s' ∨ NegG g s') → s = s'
  /-- An atom only has arguments at the positions of its symbol's signature. -/
  arg_sig : ∀ g s p x : A, (PosG g s ∨ NegG g s) → ArgG g p x → SigG s p
  /-- An atom has an argument at every position of its symbol's signature. -/
  arg_tot : ∀ g s p : A, (PosG g s ∨ NegG g s) → SigG s p → ∃ x, ArgG g p x

/-! ### Environments -/

open Classical in
/-- Updating an environment at one variable. (Classical: the instance is a
bare type, with no decidable equality.) -/
noncomputable def upd {A M : Type} (v : A → M) (x : A) (d : M) : A → M :=
  fun z => if z = x then d else v z

@[simp]
theorem upd_self {A M : Type} (v : A → M) (x : A) (d : M) : upd v x d x = d := by
  classical
  simp [upd]

theorem upd_of_ne {A M : Type} (v : A → M) {x z : A} (d : M) (h : z ≠ x) :
    upd v x d z = v z := by
  classical
  simp [upd, h]

/-! ### Satisfaction

`gstep` is the Tarskian truth definition of a node, one clause per kind of
node, with the values of the children supplied by the parameter `rec`. It is
monotone in `rec` – this is what negation normal form buys – so iterating it
from the everywhere-false valuation gives an increasing sequence whose union
`Gval` is the least fixed point, and on a well-formed instance the fixed point
is unique (`DescriptiveComplexity.FinSat.Membership`). -/

section Semantics

variable {A M : Type} [Language.finsat.Structure A]

/-- **One unfolding of the truth definition**: the value of the node `g` under
the environment `v`, given the values `rec` of the nodes below it. A
conjunction node holds when all its children do, a disjunction node when one
of them does, a quantifier node when all (respectively one) of the values of
its bound variable make all (one of) its children hold; a literal reads the
environment, an atom the interpretation `I`, on an assignment `w` of the
argument positions matching the environment on the arguments of the atom. -/
noncomputable def gstep (I : A → (A → M) → Prop) (rec : (A → M) → A → Prop)
    (v : A → M) (g : A) : Prop :=
  (AndG g ∧ ∀ c, ChildG g c → rec v c) ∨
  (OrG g ∧ ∃ c, ChildG g c ∧ rec v c) ∨
  (AllG g ∧ ∀ x, BindG g x → ∀ d : M, ∀ c, ChildG g c → rec (upd v x d) c) ∨
  (ExG g ∧ ∃ x, BindG g x ∧ ∃ d : M, ∃ c, ChildG g c ∧ rec (upd v x d) c) ∨
  (∃ x y, EqG g x y ∧ v x = v y) ∨
  (∃ x y, NeqG g x y ∧ v x ≠ v y) ∨
  (∃ s, PosG g s ∧ ∃ w : A → M, (∀ p x, ArgG g p x → w p = v x) ∧ I s w) ∨
  (∃ s, NegG g s ∧ ∃ w : A → M, (∀ p x, ArgG g p x → w p = v x) ∧ ¬I s w)

/-- The truth definition is monotone in the values of the nodes below: no
clause of `DescriptiveComplexity.FinSat.gstep` uses `rec` negatively, because
negation is confined to the leaves. -/
theorem gstep_mono (I : A → (A → M) → Prop) {rec rec' : (A → M) → A → Prop}
    (h : ∀ v g, rec v g → rec' v g) (v : A → M) (g : A) :
    gstep I rec v g → gstep I rec' v g := by
  intro hg
  simp only [gstep] at hg ⊢
  rcases hg with ⟨hk, hall⟩ | ⟨hk, c, hc, hv⟩ | ⟨hk, hall⟩ | ⟨hk, x, hx, d, c, hc, hv⟩ |
    hl | hl | hl | hl
  · exact Or.inl ⟨hk, fun c hc => h _ _ (hall c hc)⟩
  · exact Or.inr (Or.inl ⟨hk, c, hc, h _ _ hv⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hk, fun x hx d c hc => h _ _ (hall x hx d c hc)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, x, hx, d, c, hc, h _ _ hv⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))

/-- **Satisfaction, by iteration**: `gval I k v g` is the `k`-th approximant of
the truth of the node `g` under the environment `v`. -/
noncomputable def gval (I : A → (A → M) → Prop) : ℕ → (A → M) → A → Prop
  | 0 => fun _ _ => False
  | k + 1 => gstep I (gval I k)

@[simp]
theorem gval_succ (I : A → (A → M) → Prop) (k : ℕ) :
    gval I (k + 1) = gstep I (gval I k) := rfl

/-- **The node `g` holds under the environment `v`**: the least fixed point of
the truth definition, reached because a finite parse DAG has finite depth. -/
def Gval (I : A → (A → M) → Prop) (v : A → M) (g : A) : Prop :=
  ∃ k, gval I k v g

theorem gval_mono (I : A → (A → M) → Prop) :
    ∀ (k : ℕ) (v : A → M) (g : A), gval I k v g → gval I (k + 1) v g := by
  intro k
  induction k with
  | zero => intro v g h; exact h.elim
  | succ k ih => intro v g h; exact gstep_mono I ih v g h

theorem gval_of_le (I : A → (A → M) → Prop) {k k' : ℕ} (hk : k ≤ k') (v : A → M) (g : A)
    (h : gval I k v g) : gval I k' v g := by
  induction hk with
  | refl => exact h
  | step _ ih => exact gval_mono I _ _ _ ih

/-- An interpretation is **local** when the value of a symbol depends only on
the arguments its signature declares. -/
def Local (I : A → (A → M) → Prop) : Prop :=
  ∀ (s : A) (w w' : A → M), (∀ p, SigG s p → w p = w' p) → (I s w ↔ I s w')

end Semantics

/-! ### The problem -/

/-- **The encoded sentence has a finite model**: the instance is well-formed
and there is a finite nonempty universe with a local interpretation of the
relation symbols under which every environment satisfies the root – that is, a
finite model of the universal closure of the encoded formula. -/
def FinSatOn (A : Type) [Language.finsat.Structure A] : Prop :=
  IsWF A ∧ ∃ (M : Type) (_ : Finite M) (_ : Nonempty M) (I : A → (A → M) → Prop),
    Local I ∧ ∀ (v : A → M) (g : A), RootG g → Gval I v g

/-! ### Isomorphism-invariance

Everything the semantics reads is a relation of the instance, so an
isomorphism transports it. The model is carried over unchanged, its
interpretation composed with the isomorphism
(`DescriptiveComplexity.FinSat.mapI`); the substance is the transport of
`gval`, an induction on the fuel with one step per clause of the truth
definition. Only one direction is proved: the converse is the same statement
at the inverse isomorphism. -/

section Iso

variable {A B : Type} [Language.finsat.Structure A] [Language.finsat.Structure B]
variable (e : A ≃[Language.finsat] B)

theorem ord_equiv (x y : A) : Ord x y ↔ Ord (e x) (e y) := relMap_equiv₂ e _ x y

theorem ordLt_equiv (x y : A) : OrdLt x y ↔ OrdLt (e x) (e y) :=
  and_congr (ord_equiv e x y)
    (not_congr ⟨fun h => h ▸ rfl, fun h => EmbeddingLike.injective e h⟩)

theorem and_equiv (g : A) : AndG g ↔ AndG (e g) := relMap_equiv₁ e _ g

theorem or_equiv (g : A) : OrG g ↔ OrG (e g) := relMap_equiv₁ e _ g

theorem all_equiv (g : A) : AllG g ↔ AllG (e g) := relMap_equiv₁ e _ g

theorem ex_equiv (g : A) : ExG g ↔ ExG (e g) := relMap_equiv₁ e _ g

theorem child_equiv (g c : A) : ChildG g c ↔ ChildG (e g) (e c) := relMap_equiv₂ e _ g c

theorem bind_equiv (g x : A) : BindG g x ↔ BindG (e g) (e x) := relMap_equiv₂ e _ g x

theorem eqG_equiv (g x y : A) : EqG g x y ↔ EqG (e g) (e x) (e y) := relMap_equiv₃ e _ g x y

theorem neqG_equiv (g x y : A) : NeqG g x y ↔ NeqG (e g) (e x) (e y) := relMap_equiv₃ e _ g x y

theorem pos_equiv (g s : A) : PosG g s ↔ PosG (e g) (e s) := relMap_equiv₂ e _ g s

theorem neg_equiv (g s : A) : NegG g s ↔ NegG (e g) (e s) := relMap_equiv₂ e _ g s

theorem arg_equiv (g p x : A) : ArgG g p x ↔ ArgG (e g) (e p) (e x) := relMap_equiv₃ e _ g p x

theorem sig_equiv (s p : A) : SigG s p ↔ SigG (e s) (e p) := relMap_equiv₂ e _ s p

theorem root_equiv (g : A) : RootG g ↔ RootG (e g) := relMap_equiv₁ e _ g

/-- The positive-or-negative reading of an atom transports along an
isomorphism. -/
theorem posneg_equiv (g s : A) :
    (PosG g s ∨ NegG g s) ↔ (PosG (e g) (e s) ∨ NegG (e g) (e s)) :=
  or_congr (pos_equiv e g s) (neg_equiv e g s)

/-! The same transports read backwards, at the inverse isomorphism: the shape
every field of `DescriptiveComplexity.FinSat.isWF_map` needs. -/

theorem ord_equiv' (x y : B) : Ord x y ↔ Ord (e.symm x) (e.symm y) := by
  have h := (ord_equiv e (e.symm x) (e.symm y)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem ordLt_equiv' (x y : B) : OrdLt x y ↔ OrdLt (e.symm x) (e.symm y) := by
  have h := (ordLt_equiv e (e.symm x) (e.symm y)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem child_equiv' (g c : B) : ChildG g c ↔ ChildG (e.symm g) (e.symm c) := by
  have h := (child_equiv e (e.symm g) (e.symm c)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem arg_equiv' (g p x : B) : ArgG g p x ↔ ArgG (e.symm g) (e.symm p) (e.symm x) := by
  have h := (arg_equiv e (e.symm g) (e.symm p) (e.symm x)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h

theorem sig_equiv' (s p : B) : SigG s p ↔ SigG (e.symm s) (e.symm p) := by
  have h := (sig_equiv e (e.symm s) (e.symm p)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem root_equiv' (g : B) : RootG g ↔ RootG (e.symm g) := by
  have h := (root_equiv e (e.symm g)).symm
  rwa [e.apply_symm_apply] at h

theorem posneg_equiv' (g s : B) :
    (PosG g s ∨ NegG g s) ↔ (PosG (e.symm g) (e.symm s) ∨ NegG (e.symm g) (e.symm s)) := by
  have h := (posneg_equiv e (e.symm g) (e.symm s)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

private theorem eq_of_symm_eq {x y : B} (h : e.symm x = e.symm y) : x = y := by
  have h' := congrArg e h
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h'

/-- Well-formedness transports along an isomorphism. -/
theorem isWF_map (e : A ≃[Language.finsat] B) (h : IsWF A) : IsWF B where
  ord_refl x := (ord_equiv' e x x).mpr (h.ord_refl _)
  ord_trans x y z hxy hyz := (ord_equiv' e x z).mpr
    (h.ord_trans _ _ _ ((ord_equiv' e x y).mp hxy) ((ord_equiv' e y z).mp hyz))
  ord_antisymm x y hxy hyx := eq_of_symm_eq e
    (h.ord_antisymm _ _ ((ord_equiv' e x y).mp hxy) ((ord_equiv' e y x).mp hyx))
  ord_total x y := (h.ord_total (e.symm x) (e.symm y)).imp
    (ord_equiv' e x y).mpr (ord_equiv' e y x).mpr
  child_lt g c hgc := (ordLt_equiv' e c g).mpr (h.child_lt _ _ ((child_equiv' e g c).mp hgc))
  arg_fun g p x x' hx hx' := eq_of_symm_eq e
    (h.arg_fun _ _ _ _ ((arg_equiv' e g p x).mp hx) ((arg_equiv' e g p x').mp hx'))
  atom_sym g s s' hs hs' := eq_of_symm_eq e
    (h.atom_sym _ _ _ ((posneg_equiv' e g s).mp hs) ((posneg_equiv' e g s').mp hs'))
  arg_sig g s p x hs ha := (sig_equiv' e s p).mpr
    (h.arg_sig _ _ _ _ ((posneg_equiv' e g s).mp hs) ((arg_equiv' e g p x).mp ha))
  arg_tot g s p hs hp := by
    obtain ⟨x, hx⟩ := h.arg_tot _ _ _ ((posneg_equiv' e g s).mp hs) ((sig_equiv' e s p).mp hp)
    exact ⟨e x, (arg_equiv' e g p (e x)).mpr (by rwa [e.symm_apply_apply])⟩

/-- The interpretation of the symbols, transported along an isomorphism of
instances: the model is unchanged, and its interpretation reads the symbol and
the argument positions through the isomorphism. -/
def mapI {M : Type} (I : A → (A → M) → Prop) : B → (B → M) → Prop :=
  fun s w => I (e.symm s) fun a => w (e a)

theorem local_map {M : Type} {I : A → (A → M) → Prop} (h : Local I) : Local (mapI e I) := by
  intro s w w' hw
  refine h (e.symm s) _ _ fun p hp => ?_
  refine hw (e p) ?_
  rw [sig_equiv e] at hp
  rwa [e.apply_symm_apply] at hp

/-- Reading the transported interpretation at a transported argument is
reading the original one. -/
theorem mapI_apply {M : Type} (I : A → (A → M) → Prop) (s : A) (w : A → M) :
    mapI e I (e s) (fun b => w (e.symm b)) ↔ I s w := by
  have hs : e.symm (e s) = s := e.symm_apply_apply s
  have hfun : (fun a => w (e.symm (e a))) = w := funext fun a => by rw [e.symm_apply_apply]
  change I (e.symm (e s)) (fun a => w (e.symm (e a))) ↔ I s w
  rw [hs, hfun]

theorem upd_map {M : Type} (v : A → M) (x : A) (d : M) :
    (fun b => upd v x d (e.symm b)) = upd (fun b => v (e.symm b)) (e x) d := by
  classical
  funext b
  by_cases hb : b = e x
  · subst hb
    rw [upd_self, e.symm_apply_apply, upd_self]
  · rw [upd_of_ne _ d hb, upd_of_ne]
    intro hc
    exact hb (by rw [← hc, e.apply_symm_apply])

/-- **Satisfaction transports along an isomorphism**, one clause of the truth
definition at a time. -/
theorem gval_map {M : Type} (I : A → (A → M) → Prop) :
    ∀ (k : ℕ) (v : A → M) (g : A),
      gval I k v g → gval (mapI e I) k (fun b => v (e.symm b)) (e g) := by
  intro k
  induction k with
  | zero => intro v g h; exact h.elim
  | succ k ih =>
    intro v g hg
    simp only [gval] at hg ⊢
    rcases hg with ⟨hk, hall⟩ | ⟨hk, c, hc, hv⟩ | ⟨hk, hall⟩ | ⟨hk, x, hx, d, c, hc, hv⟩ |
      ⟨x, y, hl, hval⟩ | ⟨x, y, hl, hval⟩ | ⟨s, hl, w, hw, hI⟩ | ⟨s, hl, w, hw, hI⟩
    · refine Or.inl ⟨(and_equiv e g).mp hk, fun c hc => ?_⟩
      have hc' : ChildG g (e.symm c) := by
        rw [child_equiv e, e.apply_symm_apply]; exact hc
      have := ih v _ (hall _ hc')
      rwa [e.apply_symm_apply] at this
    · exact Or.inr (Or.inl ⟨(or_equiv e g).mp hk, e c,
        (child_equiv e g c).mp hc, ih v c hv⟩)
    · refine Or.inr (Or.inr (Or.inl ⟨(all_equiv e g).mp hk, fun x hx d c hc => ?_⟩))
      have hx' : BindG g (e.symm x) := by
        rw [bind_equiv e, e.apply_symm_apply]; exact hx
      have hc' : ChildG g (e.symm c) := by
        rw [child_equiv e, e.apply_symm_apply]; exact hc
      have := ih _ _ (hall _ hx' d _ hc')
      rwa [upd_map e, e.apply_symm_apply, e.apply_symm_apply] at this
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨(ex_equiv e g).mp hk, e x,
        (bind_equiv e g x).mp hx, d, e c, (child_equiv e g c).mp hc, ?_⟩)))
      have := ih _ _ hv
      rwa [upd_map e] at this
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e x, e y,
        (eqG_equiv e g x y).mp hl, by simpa only [e.symm_apply_apply] using hval⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e x, e y,
        (neqG_equiv e g x y).mp hl,
        by simpa only [e.symm_apply_apply] using hval⟩)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e s, (pos_equiv e g s).mp hl, fun b => w (e.symm b), fun p x hp => ?_, ?_⟩))))))
      · have hp' : ArgG g (e.symm p) (e.symm x) := by
          rw [arg_equiv e, e.apply_symm_apply, e.apply_symm_apply]; exact hp
        exact hw _ _ hp'
      · exact (mapI_apply e I s w).mpr hI
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e s, (neg_equiv e g s).mp hl, fun b => w (e.symm b), fun p x hp => ?_, ?_⟩))))))
      · have hp' : ArgG g (e.symm p) (e.symm x) := by
          rw [arg_equiv e, e.apply_symm_apply, e.apply_symm_apply]; exact hp
        exact hw _ _ hp'
      · exact fun hcon => hI ((mapI_apply e I s w).mp hcon)

/-- The problem transports along an isomorphism (one direction; the converse
is this statement at `e.symm`). -/
theorem finSatOn_map (e : A ≃[Language.finsat] B) (h : FinSatOn A) : FinSatOn B := by
  obtain ⟨hwf, M, hfin, hne, I, hloc, hroot⟩ := h
  refine ⟨isWF_map e hwf, M, hfin, hne, mapI e I, local_map e hloc, fun w g hg => ?_⟩
  have hg' : RootG (e.symm g) := (root_equiv' e g).mp hg
  obtain ⟨k, hk⟩ := hroot (fun a => w (e a)) _ hg'
  refine ⟨k, ?_⟩
  have := gval_map e I k _ _ hk
  have hw : (fun b => w (e (e.symm b))) = w := by
    funext b; rw [e.apply_symm_apply]
  rwa [hw, e.apply_symm_apply] at this

end Iso

end FinSat

open FinSat in
/-- **FINSAT**: does the encoded first-order sentence have a finite model?
Trakhtenbrot's problem, and the first RE-complete problem of the catalog. -/
def FINSAT : DecisionProblem Language.finsat where
  Holds A _ := FinSatOn A
  iso_invariant e := ⟨finSatOn_map e, finSatOn_map e.symm⟩

end DescriptiveComplexity
