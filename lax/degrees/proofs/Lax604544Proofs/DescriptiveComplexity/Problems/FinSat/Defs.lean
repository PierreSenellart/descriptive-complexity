/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.Interpretation
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099.FiniteSatisfiability
end Lax624099.FiniteSatisfiability

namespace Lax624099.FiniteSatisfiability.FinSat
end Lax624099.FiniteSatisfiability.FinSat

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax604544Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax624099.FiniteSatisfiability (finsat finsatAllSym finsatAndSym finsatArgSym finsatBindSym finsatChildSym finsatEqSym finsatExSym finsatLeSym finsatNegSym finsatNeqSym finsatOrSym finsatPosSym finsatRel finsatRootSym finsatSigSym instIsRelationalFinsat)
end FirstOrder.Language

namespace Lax604544Proofs.DescriptiveComplexity.FinSat
export Lax624099.FiniteSatisfiability.FinSat (AllG AndG ArgG BindG ChildG EqG ExG FinSatOn Gval IsWF Local NegG NeqG OrG Ord OrdLt PosG RootG SigG gstep gval upd)
end Lax604544Proofs.DescriptiveComplexity.FinSat

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

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace FinSat

/-! ### Reading the encoding -/

section Reading

variable {A : Type} [Lax624099.FiniteSatisfiability.finsat.Structure A]

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

/-! ### Environments -/

@[simp]
theorem upd_self {A M : Type} (v : A → M) (x : A) (d : M) : Lax624099.FiniteSatisfiability.FinSat.upd v x d x = d := by
  classical
  simp [Lax624099.FiniteSatisfiability.FinSat.upd]

theorem upd_of_ne {A M : Type} (v : A → M) {x z : A} (d : M) (h : z ≠ x) :
    Lax624099.FiniteSatisfiability.FinSat.upd v x d z = v z := by
  classical
  simp [Lax624099.FiniteSatisfiability.FinSat.upd, h]

/-! ### Satisfaction

`gstep` is the Tarskian truth definition of a node, one clause per kind of
node, with the values of the children supplied by the parameter `rec`. It is
monotone in `rec` – this is what negation normal form buys – so iterating it
from the everywhere-false valuation gives an increasing sequence whose union
`Gval` is the least fixed point, and on a well-formed instance the fixed point
is unique (`DescriptiveComplexity.Problems.FinSat.Membership`). -/

section Semantics

variable {A M : Type} [Lax624099.FiniteSatisfiability.finsat.Structure A]

/-- The truth definition is monotone in the values of the nodes below: no
clause of `DescriptiveComplexity.FinSat.gstep` uses `rec` negatively, because
negation is confined to the leaves. -/
theorem gstep_mono (I : A → (A → M) → Prop) {rec rec' : (A → M) → A → Prop}
    (h : ∀ v g, rec v g → rec' v g) (v : A → M) (g : A) :
    Lax624099.FiniteSatisfiability.FinSat.gstep I rec v g → Lax624099.FiniteSatisfiability.FinSat.gstep I rec' v g := by
  intro hg
  simp only [Lax624099.FiniteSatisfiability.FinSat.gstep] at hg ⊢
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

@[simp]
theorem gval_succ (I : A → (A → M) → Prop) (k : ℕ) :
    Lax624099.FiniteSatisfiability.FinSat.gval I (k + 1) = Lax624099.FiniteSatisfiability.FinSat.gstep I (Lax624099.FiniteSatisfiability.FinSat.gval I k) := rfl

theorem gval_mono (I : A → (A → M) → Prop) :
    ∀ (k : ℕ) (v : A → M) (g : A), Lax624099.FiniteSatisfiability.FinSat.gval I k v g → Lax624099.FiniteSatisfiability.FinSat.gval I (k + 1) v g := by
  intro k
  induction k with
  | zero => intro v g h; exact h.elim
  | succ k ih => intro v g h; exact gstep_mono I ih v g h

theorem gval_of_le (I : A → (A → M) → Prop) {k k' : ℕ} (hk : k ≤ k') (v : A → M) (g : A)
    (h : Lax624099.FiniteSatisfiability.FinSat.gval I k v g) : Lax624099.FiniteSatisfiability.FinSat.gval I k' v g := by
  induction hk with
  | refl => exact h
  | step _ ih => exact gval_mono I _ _ _ ih

end Semantics

/-! ### The problem -/

/-! ### Isomorphism-invariance

Everything the semantics reads is a relation of the instance, so an
isomorphism transports it. The model is carried over unchanged, its
interpretation composed with the isomorphism
(`DescriptiveComplexity.FinSat.mapI`); the substance is the transport of
`gval`, an induction on the fuel with one step per clause of the truth
definition. Only one direction is proved: the converse is the same statement
at the inverse isomorphism. -/

section Iso

variable {A B : Type} [Lax624099.FiniteSatisfiability.finsat.Structure A] [Lax624099.FiniteSatisfiability.finsat.Structure B]

variable (e : A ≃[Lax624099.FiniteSatisfiability.finsat] B)

theorem ord_equiv (x y : A) : Lax624099.FiniteSatisfiability.FinSat.Ord x y ↔ Lax624099.FiniteSatisfiability.FinSat.Ord (e x) (e y) := relMap_equiv₂ e _ x y

theorem ordLt_equiv (x y : A) : Lax624099.FiniteSatisfiability.FinSat.OrdLt x y ↔ Lax624099.FiniteSatisfiability.FinSat.OrdLt (e x) (e y) :=
  and_congr (ord_equiv e x y)
    (not_congr ⟨fun h => h ▸ rfl, fun h => EmbeddingLike.injective e h⟩)

theorem and_equiv (g : A) : Lax624099.FiniteSatisfiability.FinSat.AndG g ↔ Lax624099.FiniteSatisfiability.FinSat.AndG (e g) := relMap_equiv₁ e _ g

theorem or_equiv (g : A) : Lax624099.FiniteSatisfiability.FinSat.OrG g ↔ Lax624099.FiniteSatisfiability.FinSat.OrG (e g) := relMap_equiv₁ e _ g

theorem all_equiv (g : A) : Lax624099.FiniteSatisfiability.FinSat.AllG g ↔ Lax624099.FiniteSatisfiability.FinSat.AllG (e g) := relMap_equiv₁ e _ g

theorem ex_equiv (g : A) : Lax624099.FiniteSatisfiability.FinSat.ExG g ↔ Lax624099.FiniteSatisfiability.FinSat.ExG (e g) := relMap_equiv₁ e _ g

theorem child_equiv (g c : A) : Lax624099.FiniteSatisfiability.FinSat.ChildG g c ↔ Lax624099.FiniteSatisfiability.FinSat.ChildG (e g) (e c) := relMap_equiv₂ e _ g c

theorem bind_equiv (g x : A) : Lax624099.FiniteSatisfiability.FinSat.BindG g x ↔ Lax624099.FiniteSatisfiability.FinSat.BindG (e g) (e x) := relMap_equiv₂ e _ g x

theorem eqG_equiv (g x y : A) : Lax624099.FiniteSatisfiability.FinSat.EqG g x y ↔ Lax624099.FiniteSatisfiability.FinSat.EqG (e g) (e x) (e y) := relMap_equiv₃ e _ g x y

theorem neqG_equiv (g x y : A) : Lax624099.FiniteSatisfiability.FinSat.NeqG g x y ↔ Lax624099.FiniteSatisfiability.FinSat.NeqG (e g) (e x) (e y) := relMap_equiv₃ e _ g x y

theorem pos_equiv (g s : A) : Lax624099.FiniteSatisfiability.FinSat.PosG g s ↔ Lax624099.FiniteSatisfiability.FinSat.PosG (e g) (e s) := relMap_equiv₂ e _ g s

theorem neg_equiv (g s : A) : Lax624099.FiniteSatisfiability.FinSat.NegG g s ↔ Lax624099.FiniteSatisfiability.FinSat.NegG (e g) (e s) := relMap_equiv₂ e _ g s

theorem arg_equiv (g p x : A) : Lax624099.FiniteSatisfiability.FinSat.ArgG g p x ↔ Lax624099.FiniteSatisfiability.FinSat.ArgG (e g) (e p) (e x) := relMap_equiv₃ e _ g p x

theorem sig_equiv (s p : A) : Lax624099.FiniteSatisfiability.FinSat.SigG s p ↔ Lax624099.FiniteSatisfiability.FinSat.SigG (e s) (e p) := relMap_equiv₂ e _ s p

theorem root_equiv (g : A) : Lax624099.FiniteSatisfiability.FinSat.RootG g ↔ Lax624099.FiniteSatisfiability.FinSat.RootG (e g) := relMap_equiv₁ e _ g

/-- The positive-or-negative reading of an atom transports along an
isomorphism. -/
theorem posneg_equiv (g s : A) :
    (Lax624099.FiniteSatisfiability.FinSat.PosG g s ∨ Lax624099.FiniteSatisfiability.FinSat.NegG g s) ↔ (Lax624099.FiniteSatisfiability.FinSat.PosG (e g) (e s) ∨ Lax624099.FiniteSatisfiability.FinSat.NegG (e g) (e s)) :=
  or_congr (pos_equiv e g s) (neg_equiv e g s)

/-! The same transports read backwards, at the inverse isomorphism: the shape
every field of `DescriptiveComplexity.FinSat.isWF_map` needs. -/

theorem ord_equiv' (x y : B) : Lax624099.FiniteSatisfiability.FinSat.Ord x y ↔ Lax624099.FiniteSatisfiability.FinSat.Ord (e.symm x) (e.symm y) := by
  have h := (ord_equiv e (e.symm x) (e.symm y)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem ordLt_equiv' (x y : B) : Lax624099.FiniteSatisfiability.FinSat.OrdLt x y ↔ Lax624099.FiniteSatisfiability.FinSat.OrdLt (e.symm x) (e.symm y) := by
  have h := (ordLt_equiv e (e.symm x) (e.symm y)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem child_equiv' (g c : B) : Lax624099.FiniteSatisfiability.FinSat.ChildG g c ↔ Lax624099.FiniteSatisfiability.FinSat.ChildG (e.symm g) (e.symm c) := by
  have h := (child_equiv e (e.symm g) (e.symm c)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem arg_equiv' (g p x : B) : Lax624099.FiniteSatisfiability.FinSat.ArgG g p x ↔ Lax624099.FiniteSatisfiability.FinSat.ArgG (e.symm g) (e.symm p) (e.symm x) := by
  have h := (arg_equiv e (e.symm g) (e.symm p) (e.symm x)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h

theorem sig_equiv' (s p : B) : Lax624099.FiniteSatisfiability.FinSat.SigG s p ↔ Lax624099.FiniteSatisfiability.FinSat.SigG (e.symm s) (e.symm p) := by
  have h := (sig_equiv e (e.symm s) (e.symm p)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

theorem root_equiv' (g : B) : Lax624099.FiniteSatisfiability.FinSat.RootG g ↔ Lax624099.FiniteSatisfiability.FinSat.RootG (e.symm g) := by
  have h := (root_equiv e (e.symm g)).symm
  rwa [e.apply_symm_apply] at h

theorem posneg_equiv' (g s : B) :
    (Lax624099.FiniteSatisfiability.FinSat.PosG g s ∨ Lax624099.FiniteSatisfiability.FinSat.NegG g s) ↔ (Lax624099.FiniteSatisfiability.FinSat.PosG (e.symm g) (e.symm s) ∨ Lax624099.FiniteSatisfiability.FinSat.NegG (e.symm g) (e.symm s)) := by
  have h := (posneg_equiv e (e.symm g) (e.symm s)).symm
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

private theorem eq_of_symm_eq {x y : B} (h : e.symm x = e.symm y) : x = y := by
  have h' := congrArg e h
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h'

/-- Well-formedness transports along an isomorphism. -/
theorem isWF_map (e : A ≃[Lax624099.FiniteSatisfiability.finsat] B) (h : Lax624099.FiniteSatisfiability.FinSat.IsWF A) : Lax624099.FiniteSatisfiability.FinSat.IsWF B where
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

theorem local_map {M : Type} {I : A → (A → M) → Prop} (h : Lax624099.FiniteSatisfiability.FinSat.Local I) : Lax624099.FiniteSatisfiability.FinSat.Local (mapI e I) := by
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
    (fun b => Lax624099.FiniteSatisfiability.FinSat.upd v x d (e.symm b)) = Lax624099.FiniteSatisfiability.FinSat.upd (fun b => v (e.symm b)) (e x) d := by
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
      Lax624099.FiniteSatisfiability.FinSat.gval I k v g → Lax624099.FiniteSatisfiability.FinSat.gval (mapI e I) k (fun b => v (e.symm b)) (e g) := by
  intro k
  induction k with
  | zero => intro v g h; exact h.elim
  | succ k ih =>
    intro v g hg
    simp only [Lax624099.FiniteSatisfiability.FinSat.gval] at hg ⊢
    rcases hg with ⟨hk, hall⟩ | ⟨hk, c, hc, hv⟩ | ⟨hk, hall⟩ | ⟨hk, x, hx, d, c, hc, hv⟩ |
      ⟨x, y, hl, hval⟩ | ⟨x, y, hl, hval⟩ | ⟨s, hl, w, hw, hI⟩ | ⟨s, hl, w, hw, hI⟩
    · refine Or.inl ⟨(and_equiv e g).mp hk, fun c hc => ?_⟩
      have hc' : Lax624099.FiniteSatisfiability.FinSat.ChildG g (e.symm c) := by
        rw [child_equiv e, e.apply_symm_apply]; exact hc
      have := ih v _ (hall _ hc')
      rwa [e.apply_symm_apply] at this
    · exact Or.inr (Or.inl ⟨(or_equiv e g).mp hk, e c,
        (child_equiv e g c).mp hc, ih v c hv⟩)
    · refine Or.inr (Or.inr (Or.inl ⟨(all_equiv e g).mp hk, fun x hx d c hc => ?_⟩))
      have hx' : Lax624099.FiniteSatisfiability.FinSat.BindG g (e.symm x) := by
        rw [bind_equiv e, e.apply_symm_apply]; exact hx
      have hc' : Lax624099.FiniteSatisfiability.FinSat.ChildG g (e.symm c) := by
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
      · have hp' : Lax624099.FiniteSatisfiability.FinSat.ArgG g (e.symm p) (e.symm x) := by
          rw [arg_equiv e, e.apply_symm_apply, e.apply_symm_apply]; exact hp
        exact hw _ _ hp'
      · exact (mapI_apply e I s w).mpr hI
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e s, (neg_equiv e g s).mp hl, fun b => w (e.symm b), fun p x hp => ?_, ?_⟩))))))
      · have hp' : Lax624099.FiniteSatisfiability.FinSat.ArgG g (e.symm p) (e.symm x) := by
          rw [arg_equiv e, e.apply_symm_apply, e.apply_symm_apply]; exact hp
        exact hw _ _ hp'
      · exact fun hcon => hI ((mapI_apply e I s w).mp hcon)

/-- The problem transports along an isomorphism (one direction; the converse
is this statement at `e.symm`). -/
theorem finSatOn_map (e : A ≃[Lax624099.FiniteSatisfiability.finsat] B) (h : Lax624099.FiniteSatisfiability.FinSat.FinSatOn A) : Lax624099.FiniteSatisfiability.FinSat.FinSatOn B := by
  obtain ⟨hwf, M, hfin, hne, I, hloc, hroot⟩ := h
  refine ⟨isWF_map e hwf, M, hfin, hne, mapI e I, local_map e hloc, fun w g hg => ?_⟩
  have hg' : Lax624099.FiniteSatisfiability.FinSat.RootG (e.symm g) := (root_equiv' e g).mp hg
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
def FINSAT : Lax904597.Problems.DecisionProblem Lax624099.FiniteSatisfiability.finsat where
  Holds A _ := Lax624099.FiniteSatisfiability.FinSat.FinSatOn A
  iso_invariant e := ⟨finSatOn_map e, finSatOn_map e.symm⟩

end Lax604544Proofs.DescriptiveComplexity


