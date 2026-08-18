/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation

/-!
# EPR: satisfiability of an `∃*∀*` sentence

The Bernays–Schönfinkel–Ramsey class ([Lewis 1980][lewis1980complexity]): *is
the given `∃*∀*` sentence satisfiable?* A sentence of that shape has no
function symbols and its quantifier prefix is a block of existentials followed
by a block of universals, so it is satisfiable exactly when it has a model with
one element per existential variable – a *small* model, of which the sentence
nevertheless speaks exponentially much, since a clause is checked at every
assignment of its universal variables. That gap is the whole of the problem's
complexity, and it is why the class sits at NEXPTIME rather than at NP.

## The encoding

An instance is a **flat** description, with no parse tree at all:

* `evar x` marks the existential variables; every other variable of the
  sentence is universally quantified, so no mark is needed for those;
* `cl c` marks the clauses of the matrix, which is in conjunctive normal form,
  and `inCl c l` gives the literals of a clause – a clause is the disjunction
  of *all* the literals it names, so nothing is a binary tree;
* `posL l s` and `negL l s` say that the literal `l` is the atom of the
  relation symbol `s`, positive or negated, and `arg l p x` gives its argument
  at the position `p`; `sig s p` gives the argument positions of `s`.

Nothing here is a chain or a tree, so the encoding needs no order of its own –
unlike `DescriptiveComplexity.FINSAT`, whose parse DAG has to be acyclic. That
is what a prenex form with a quantifier-free matrix buys.

## The semantics

There is deliberately no decoding into a `FirstOrder.Language.Sentence`: the
relation symbols of the encoded sentence are *elements of the instance*, so the
decoded vocabulary would depend on the instance. Satisfaction is defined on the
encoding directly, and being quantifier-free the matrix needs no fixed point:
one clause per kind of literal is the whole truth definition.

A *model* is a finite nonempty type `M`, an interpretation
`I : A → (A → M) → Prop` reading a symbol and an assignment of argument
positions – required to be **local**, so that `I s` is a relation of the arity
of `s` rather than of the whole universe – and a witness `e` for the
existential variables. The sentence holds when *every* assignment of the
universal variables satisfies every clause.

Equality is not part of the encoding. The class is NEXPTIME-complete either
way, and a reduction that wants equality can carry its own equality symbol with
the axioms it needs.
-/

/- The language of encoded `∃*∀*` sentences lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.finsat`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of encoded `∃*∀*` sentences in conjunctive
normal form. -/
inductive eprRel : ℕ → Type
  /-- `evar x`: the variable `x` is existentially quantified. -/
  | evar : eprRel 1
  /-- `cl c`: `c` is a clause of the matrix. -/
  | cl : eprRel 1
  /-- `inCl c l`: the literal `l` occurs in the clause `c`. -/
  | inCl : eprRel 2
  /-- `posL l s`: the literal `l` is the positive atom of the symbol `s`. -/
  | posL : eprRel 2
  /-- `negL l s`: the literal `l` is the negated atom of the symbol `s`. -/
  | negL : eprRel 2
  /-- `arg l p x`: the argument of the literal `l` at the position `p` is the
  variable `x`. -/
  | arg : eprRel 3
  /-- `sig s p`: the relation symbol `s` has the argument position `p`. -/
  | sig : eprRel 2
  deriving DecidableEq

/-- The relational vocabulary of encoded `∃*∀*` sentences: a set of clauses of
literals over relation symbols, with the existential variables marked. -/
protected def epr : Language :=
  ⟨fun _ => Empty, eprRel⟩

instance : IsRelational Language.epr :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The symbol marking existential variables. -/
abbrev eprEVarSym : Language.epr.Relations 1 := .evar

/-- The symbol marking clauses. -/
abbrev eprClSym : Language.epr.Relations 1 := .cl

/-- The symbol giving the literals of a clause. -/
abbrev eprInClSym : Language.epr.Relations 2 := .inCl

/-- The symbol of positive literals. -/
abbrev eprPosSym : Language.epr.Relations 2 := .posL

/-- The symbol of negated literals. -/
abbrev eprNegSym : Language.epr.Relations 2 := .negL

/-- The symbol giving the arguments of a literal. -/
abbrev eprArgSym : Language.epr.Relations 3 := .arg

/-- The symbol giving the signature of a relation symbol. -/
abbrev eprSigSym : Language.epr.Relations 2 := .sig

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Epr

/-! ### Reading the encoding -/

section Reading

variable {A : Type} [Language.epr.Structure A]

/-- The variable `x` is existentially quantified. -/
def EVarG (x : A) : Prop := RelMap Language.eprEVarSym ![x]

/-- `c` is a clause of the matrix. -/
def ClauseG (c : A) : Prop := RelMap Language.eprClSym ![c]

/-- The literal `l` occurs in the clause `c`. -/
def InClG (c l : A) : Prop := RelMap Language.eprInClSym ![c, l]

/-- The literal `l` is the positive atom of the symbol `s`. -/
def PosG (l s : A) : Prop := RelMap Language.eprPosSym ![l, s]

/-- The literal `l` is the negated atom of the symbol `s`. -/
def NegG (l s : A) : Prop := RelMap Language.eprNegSym ![l, s]

/-- The argument of the literal `l` at the position `p` is the variable `x`. -/
def ArgG (l p x : A) : Prop := RelMap Language.eprArgSym ![l, p, x]

/-- The relation symbol `s` has the argument position `p`. -/
def SigG (s p : A) : Prop := RelMap Language.eprSigSym ![s, p]

end Reading

/-! ### Satisfaction -/

section Semantics

variable {A M : Type} [Language.epr.Structure A]

open Classical in
/-- **The value of a variable**: the witness chosen for it if it is
existentially quantified, and the assignment being tested otherwise. Every
variable the encoding does not mark counts as universally quantified, which is
what lets the encoding get away with one mark instead of two. -/
noncomputable def eprVal (e u : A → M) : A → M := fun x => if EVarG x then e x else u x

/-- **A literal is true**: its symbol holds (or fails, for a negated literal)
of an assignment of the argument positions matching the environment on the
arguments the encoding declares. -/
def LitTrue (I : A → (A → M) → Prop) (v : A → M) (l : A) : Prop :=
  (∃ s, PosG l s ∧ ∃ w : A → M, (∀ p x, ArgG l p x → w p = v x) ∧ I s w) ∨
    (∃ s, NegG l s ∧ ∃ w : A → M, (∀ p x, ArgG l p x → w p = v x) ∧ ¬I s w)

/-- **Well-formedness**, folded into the yes-instances as
`DescriptiveComplexity.FINSAT`'s is: an atom names *one* variable at each
argument position, and names one at every position of its symbol's signature.

Both are what makes an atom an atom, and both are needed for the small-model
property (`DescriptiveComplexity.Epr.selfModel_of_eprSatOn`): an atom whose
arguments are ambiguous, or missing where the signature asks for one, reads
differently on a universe the sentence has collapsed than on the instance
itself. -/
def IsWF (A : Type) [Language.epr.Structure A] : Prop :=
  (∀ l p x y : A, ArgG l p x → ArgG l p y → x = y) ∧
    ∀ l s p : A, (PosG l s ∨ NegG l s) → SigG s p → ∃ x, ArgG l p x

/-- An interpretation is **local** when the value of a symbol depends only on
the arguments its signature declares. -/
def Local (I : A → (A → M) → Prop) : Prop :=
  ∀ (s : A) (w w' : A → M), (∀ p, SigG s p → w p = w' p) → (I s w ↔ I s w')

/-- **The matrix holds** at an environment: every clause has a true literal. -/
def MatrixTrue (I : A → (A → M) → Prop) (v : A → M) : Prop :=
  ∀ c, ClauseG c → ∃ l, InClG c l ∧ LitTrue I v l

end Semantics

/-! ### The problem -/

/-- **The encoded `∃*∀*` sentence is satisfiable**: some finite nonempty
universe carries a local interpretation of the relation symbols and a witness
for the existential variables under which every assignment of the universal
variables satisfies every clause.

Finiteness of the model costs nothing: a satisfiable `∃*∀*` sentence has a
model with one element per existential variable, which is what
`DescriptiveComplexity.Epr.Membership` proves and uses. -/
def EprSatOn (A : Type) [Language.epr.Structure A] : Prop :=
  ∃ (M : Type) (_ : Finite M) (_ : Nonempty M) (I : A → (A → M) → Prop) (e : A → M),
    Local I ∧ ∀ u : A → M, MatrixTrue I (eprVal e u)

/-! ### Isomorphism-invariance

Everything the semantics reads is a relation of the instance, so an isomorphism
transports it: the model is carried over unchanged and its interpretation
composed with the isomorphism, exactly as for
`DescriptiveComplexity.FINSAT`. -/

section Transport

variable {A B : Type} [Language.epr.Structure A] [Language.epr.Structure B]
variable (e : A ≃[Language.epr] B)

theorem eVarG_map (x : A) : EVarG x ↔ EVarG (e x) := relMap_equiv₁ e Language.eprEVarSym x

theorem clauseG_map (c : A) : ClauseG c ↔ ClauseG (e c) := relMap_equiv₁ e Language.eprClSym c

theorem inClG_map (c l : A) : InClG c l ↔ InClG (e c) (e l) :=
  relMap_equiv₂ e Language.eprInClSym c l

theorem posG_map (l s : A) : PosG l s ↔ PosG (e l) (e s) :=
  relMap_equiv₂ e Language.eprPosSym l s

theorem negG_map (l s : A) : NegG l s ↔ NegG (e l) (e s) :=
  relMap_equiv₂ e Language.eprNegSym l s

theorem sigG_map (s p : A) : SigG s p ↔ SigG (e s) (e p) :=
  relMap_equiv₂ e Language.eprSigSym s p

theorem argG_map (l p x : A) : ArgG l p x ↔ ArgG (e l) (e p) (e x) :=
  relMap_equiv₃ e Language.eprArgSym l p x

variable {M : Type}

/-- The interpretation the image carries: read the symbol back through the
isomorphism. -/
def mapI (I : A → (A → M) → Prop) : B → (B → M) → Prop :=
  fun s w => I (e.symm s) (fun x => w (e x))

theorem local_mapI {I : A → (A → M) → Prop} (h : Local I) : Local (mapI e I) := by
  intro s w w' hw
  refine h (e.symm s) _ _ fun p hp => ?_
  have hs : SigG s (e p) := by
    have := (sigG_map e (e.symm s) p).mp hp
    rwa [e.apply_symm_apply] at this
  exact hw (e p) hs

theorem litTrue_map {I : A → (A → M) → Prop} {v : A → M} {l : A} (h : LitTrue I v l) :
    LitTrue (mapI e I) (fun y => v (e.symm y)) (e l) := by
  have hw : ∀ (w : A → M) (s : A), I s w ↔ mapI e I (e s) (fun y => w (e.symm y)) := by
    intro w s
    rw [mapI, e.symm_apply_apply]
    refine iff_of_eq (congrArg (I s) (funext fun x => ?_))
    rw [e.symm_apply_apply]
  have harg : ∀ (w : A → M) (l : A), (∀ p x, ArgG l p x → w p = v x) →
      ∀ p' x', ArgG (e l) p' x' → (fun y => w (e.symm y)) p' = (fun y => v (e.symm y)) x' := by
    intro w l hwa p' x' hp
    have h' : ArgG l (e.symm p') (e.symm x') := by
      have := (argG_map e l (e.symm p') (e.symm x')).symm
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact this.mp hp
    exact hwa _ _ h'
  rcases h with ⟨s, hs, w, hwa, hI⟩ | ⟨s, hs, w, hwa, hI⟩
  · exact Or.inl ⟨e s, (posG_map e l s).mp hs, fun y => w (e.symm y),
      harg w l hwa, (hw w s).mp hI⟩
  · exact Or.inr ⟨e s, (negG_map e l s).mp hs, fun y => w (e.symm y),
      harg w l hwa, fun hc => hI ((hw w s).mpr hc)⟩

theorem eVarG_map' (x : B) : EVarG x ↔ EVarG (e.symm x) := by
  have h := (eVarG_map e (e.symm x)).symm
  rwa [e.apply_symm_apply] at h

theorem clauseG_map' (c : B) : ClauseG c ↔ ClauseG (e.symm c) := by
  have h := (clauseG_map e (e.symm c)).symm
  rwa [e.apply_symm_apply] at h

theorem posG_map' (l s : B) : PosG l s ↔ PosG (e.symm l) (e.symm s) := by
  have h := (posG_map e (e.symm l) (e.symm s)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem negG_map' (l s : B) : NegG l s ↔ NegG (e.symm l) (e.symm s) := by
  have h := (negG_map e (e.symm l) (e.symm s)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem sigG_map' (s p : B) : SigG s p ↔ SigG (e.symm s) (e.symm p) := by
  have h := (sigG_map e (e.symm s) (e.symm p)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem argG_map' (l p x : B) : ArgG l p x ↔ ArgG (e.symm l) (e.symm p) (e.symm x) := by
  have h := (argG_map e (e.symm l) (e.symm p) (e.symm x)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h

include e in
/-- **Well-formedness transports along an isomorphism.** -/
theorem isWF_map (h : IsWF A) : IsWF B := by
  refine ⟨fun l p x y hx hy => ?_, fun l s p hls hsp => ?_⟩
  · exact e.symm.injective
      (h.1 _ _ _ _ ((argG_map' e l p x).mp hx) ((argG_map' e l p y).mp hy))
  · obtain ⟨x, hx⟩ := h.2 (e.symm l) (e.symm s) (e.symm p)
      (hls.imp (posG_map' e l s).mp (negG_map' e l s).mp) ((sigG_map' e s p).mp hsp)
    refine ⟨e x, ?_⟩
    have := (argG_map e (e.symm l) (e.symm p) x).mp hx
    rwa [e.apply_symm_apply, e.apply_symm_apply] at this

include e in
/-- **Satisfiability transports along an isomorphism**: the model is carried
over unchanged, its interpretation read back through the isomorphism. -/
theorem eprSatOn_map (h : EprSatOn A) : EprSatOn B := by
  obtain ⟨M, hfin, hne, I, ε, hlocal, hsat⟩ := h
  refine ⟨M, hfin, hne, mapI e I, fun y => ε (e.symm y), local_mapI e hlocal, ?_⟩
  intro u c hc
  have hc' : ClauseG (e.symm c) := by
    have := (clauseG_map e (e.symm c)).symm
    rw [e.apply_symm_apply] at this
    exact this.mp hc
  obtain ⟨l, hl, htrue⟩ := hsat (fun x => u (e x)) (e.symm c) hc'
  have hval : (fun y => eprVal ε (fun x => u (e x)) (e.symm y)) =
      eprVal (fun y => ε (e.symm y)) u := by
    classical
    funext y
    rw [eprVal, eprVal]
    by_cases hy : EVarG (e.symm y)
    · have hy' : EVarG y := by
        have := (eVarG_map e (e.symm y)).mp hy
        rwa [e.apply_symm_apply] at this
      rw [if_pos hy, if_pos hy']
    · have hy' : ¬EVarG y := by
        intro hcy
        refine hy ?_
        have := (eVarG_map e (e.symm y)).symm
        rw [e.apply_symm_apply] at this
        exact this.mp hcy
      rw [if_neg hy, if_neg hy', e.apply_symm_apply]
  refine ⟨e l, ?_, ?_⟩
  · have := (inClG_map e (e.symm c) l).mp hl
    rwa [e.apply_symm_apply] at this
  · have := litTrue_map e htrue
    rwa [hval] at this

end Transport




end Epr

open Epr in
/-- **Satisfiability of an `∃*∀*` sentence.** The instance is the sentence, in
prenex form with a conjunctive-normal-form matrix; the question is whether it
has a model. -/
def EPR : DecisionProblem Language.epr where
  Holds A _ := IsWF A ∧ EprSatOn A
  iso_invariant e :=
    ⟨fun h => ⟨isWF_map e h.1, eprSatOn_map e h.2⟩,
      fun h => ⟨isWF_map e.symm h.1, eprSatOn_map e.symm h.2⟩⟩

end DescriptiveComplexity
