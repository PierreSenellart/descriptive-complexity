import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Lax904597.Classes
import Lax624099.Problems

/-!
---
title: Finite satisfiability of first-order sentences
type: definition
---
An instance of finite satisfiability is a first-order sentence in negation
normal form, presented as a finite structure: its elements are the nodes of
the sentence's parse DAG, its variables, its relation symbols and their
argument positions, with relations marking the conjunction, disjunction and
quantifier nodes, the child relation, the variable a quantifier binds, the
equality and atomic literals with their arguments and the signature of each
symbol, the root, and a linear order on the syntax along which children
precede their parents. A model of such an instance is a finite nonempty type
with a local interpretation of the symbols, local meaning that the value of
a symbol depends only on the positions of its signature; the truth of a node
under an environment is the least fixed point of the Tarski clauses, one per
node kind. The instance is satisfiable when it is well-formed and the
universal closure of its root has a finite model, the problem of Trakhtenbrot
(1950); see Libkin (2004), chapter 9. FINSAT is the decision
problem of the structures isomorphic to a satisfiable instance.
-/

namespace Lax624099.FiniteSatisfiability

open FirstOrder

open FirstOrder.Language

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
def finsat : Language :=
  ⟨fun _ => Empty, finsatRel⟩

instance instIsRelationalFinsat : IsRelational finsat :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The order symbol of the syntax. -/
abbrev finsatLeSym : finsat.Relations 2 := .le

/-- The symbol marking conjunction nodes. -/
abbrev finsatAndSym : finsat.Relations 1 := .andN

/-- The symbol marking disjunction nodes. -/
abbrev finsatOrSym : finsat.Relations 1 := .orN

/-- The symbol marking universal quantifier nodes. -/
abbrev finsatAllSym : finsat.Relations 1 := .allN

/-- The symbol marking existential quantifier nodes. -/
abbrev finsatExSym : finsat.Relations 1 := .exN

/-- The symbol of the child relation of the parse DAG. -/
abbrev finsatChildSym : finsat.Relations 2 := .child

/-- The symbol binding a variable to a quantifier node. -/
abbrev finsatBindSym : finsat.Relations 2 := .bind

/-- The symbol of positive equality literals. -/
abbrev finsatEqSym : finsat.Relations 3 := .eqL

/-- The symbol of negated equality literals. -/
abbrev finsatNeqSym : finsat.Relations 3 := .neqL

/-- The symbol of positive atoms. -/
abbrev finsatPosSym : finsat.Relations 2 := .posL

/-- The symbol of negated atoms. -/
abbrev finsatNegSym : finsat.Relations 2 := .negL

/-- The symbol giving the arguments of an atom. -/
abbrev finsatArgSym : finsat.Relations 3 := .arg

/-- The symbol giving the signature of a relation symbol. -/
abbrev finsatSigSym : finsat.Relations 2 := .sig

/-- The symbol marking the root node. -/
abbrev finsatRootSym : finsat.Relations 1 := .root

open FirstOrder

open Language Structure

namespace FinSat

section Reading

variable {A : Type} [finsat.Structure A]

/-- `x` precedes `y` in the order of the syntax. -/
def Ord (x y : A) : Prop := RelMap finsatLeSym ![x, y]

/-- `x` strictly precedes `y` in the order of the syntax. -/
def OrdLt (x y : A) : Prop := Ord x y ∧ x ≠ y

/-- The node `g` is a conjunction. -/
def AndG (g : A) : Prop := RelMap finsatAndSym ![g]

/-- The node `g` is a disjunction. -/
def OrG (g : A) : Prop := RelMap finsatOrSym ![g]

/-- The node `g` is a universal quantifier. -/
def AllG (g : A) : Prop := RelMap finsatAllSym ![g]

/-- The node `g` is an existential quantifier. -/
def ExG (g : A) : Prop := RelMap finsatExSym ![g]

/-- The node `c` is a child of the node `g`. -/
def ChildG (g c : A) : Prop := RelMap finsatChildSym ![g, c]

/-- The quantifier node `g` binds the variable `x`. -/
def BindG (g x : A) : Prop := RelMap finsatBindSym ![g, x]

/-- The node `g` is the literal `x = y`. -/
def EqG (g x y : A) : Prop := RelMap finsatEqSym ![g, x, y]

/-- The node `g` is the literal `x ≠ y`. -/
def NeqG (g x y : A) : Prop := RelMap finsatNeqSym ![g, x, y]

/-- The node `g` is a positive atom of the symbol `s`. -/
def PosG (g s : A) : Prop := RelMap finsatPosSym ![g, s]

/-- The node `g` is a negated atom of the symbol `s`. -/
def NegG (g s : A) : Prop := RelMap finsatNegSym ![g, s]

/-- The argument of the atom `g` at position `p` is the variable `x`. -/
def ArgG (g p x : A) : Prop := RelMap finsatArgSym ![g, p, x]

/-- The symbol `s` has an argument position `p`. -/
def SigG (s p : A) : Prop := RelMap finsatSigSym ![s, p]

/-- The node `g` is the root of the encoded sentence. -/
def RootG (g : A) : Prop := RelMap finsatRootSym ![g]

end Reading

/-- **Well-formedness of an encoded sentence**: the order symbol is a linear
order and the parse DAG descends along it. -/
structure IsWF (A : Type) [finsat.Structure A] : Prop where
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

open Classical in
/-- Updating an environment at one variable. (Classical: the instance is a
bare type, with no decidable equality.) -/
noncomputable def upd {A M : Type} (v : A → M) (x : A) (d : M) : A → M :=
  fun z => if z = x then d else v z

section Semantics

variable {A M : Type} [finsat.Structure A]

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

/-- **Satisfaction, by iteration**: `gval I k v g` is the `k`-th approximant of
the truth of the node `g` under the environment `v`. -/
noncomputable def gval (I : A → (A → M) → Prop) : ℕ → (A → M) → A → Prop
  | 0 => fun _ _ => False
  | k + 1 => gstep I (gval I k)

/-- **The node `g` holds under the environment `v`**: the least fixed point of
the truth definition, reached because a finite parse DAG has finite depth. -/
def Gval (I : A → (A → M) → Prop) (v : A → M) (g : A) : Prop :=
  ∃ k, gval I k v g

/-- An interpretation is **local** when the value of a symbol depends only on
the arguments its signature declares. -/
def Local (I : A → (A → M) → Prop) : Prop :=
  ∀ (s : A) (w w' : A → M), (∀ p, SigG s p → w p = w' p) → (I s w ↔ I s w')

end Semantics

/-- **The encoded sentence has a finite model**: the instance is well-formed
and there is a finite nonempty universe with a local interpretation of the
relation symbols under which every environment satisfies the root – that is, a
finite model of the universal closure of the encoded formula. -/
def FinSatOn (A : Type) [finsat.Structure A] : Prop :=
  IsWF A ∧ ∃ (M : Type) (_ : Finite M) (_ : Nonempty M) (I : A → (A → M) → Prop),
    Local I ∧ ∀ (v : A → M) (g : A), RootG g → Gval I v g

end FinSat

open Lax904597.Problems Lax624099.Problems

/-- FINSAT: does the encoded first-order sentence have a finite model? -/
def FINSAT : DecisionProblem finsat :=
  DecisionProblem.ofPred FinSat.FinSatOn

end Lax624099.FiniteSatisfiability
