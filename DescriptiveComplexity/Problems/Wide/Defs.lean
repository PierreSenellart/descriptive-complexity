/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Machines
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Exponential.AddrExp

/-!
# The wide machine: a machine addressed by the subsets of its instance

The machine model of the exponential classes. A `DescriptiveComplexity.TMData`
read over the instance itself is a machine with polynomially many cells, and the
library's bounds are unary by construction, so `DescriptiveComplexity.NTMAccept`
lands in NP and `DescriptiveComplexity.NTMAcceptSpace` in PSPACE. The **wide
machine** is the same model with one exponent added *in the semantics of the
problem*, and nowhere else:

> its tape is addressed by the **subsets** of the instance, while its control –
> the transitions, the states, the symbols – stays an ordinary part of the
> instance.

So an instance of size `n` describes a machine with `2^n` cells and `2^n` time
steps, and the two resource variants land one exponential up:
`DescriptiveComplexity.WideAccept` in NEXPTIME and
`DescriptiveComplexity.WideAcceptSpace` in EXPSPACE
(`DescriptiveComplexity.Problems.Wide.Membership`). A reduction of dimension `d`
buys itself `2^(nᵈ)` cells exactly as a reduction into
`DescriptiveComplexity.NTMAccept` buys itself `nᵈ`.

## The universe of the machine

The machine runs over `DescriptiveComplexity.WPoint`, the disjoint union of

* the **addresses** `A → Prop` – the subsets of the instance, which are the tape
  cells and equally the time steps; and
* the **control elements**, the elements of the instance themselves, which are
  its states, its symbols and its transitions.

That is exactly the universe an exponential expansion of the instance has, with
one tag for each summand (`DescriptiveComplexity.Problems.Wide.Expansion`), and
it is why the membership proofs are the composition `NTMAccept ∘ expansion`
rather than an argument about resources.

## Where the order comes from

`DescriptiveComplexity.TMData` needs a linear order on its universe, and a
decision problem may not read the ambient order of its instance. So the
instance carries its own order `wmLe`, and the order on addresses is the
**binary-number order** it induces: one subset is below another when, at the
`wmLe`-least element where they differ, the second contains it and the first
does not (`DescriptiveComplexity.WMSetLe`). Addresses come below control
elements, so the least *position* is the empty address. That the resulting
relation is linear is a promise, folded into the yes-instances through
`DescriptiveComplexity.TMData.WellFormed` exactly as for
`DescriptiveComplexity.NTMAccept`.

## Where the input goes

The initial tape is described by the binary symbol `wmInp` of the instance, read
at the **initial-segment addresses**: the address `{y | y ≤ x}` holds the input
symbol of `x`, and every other address – including the empty one, where the head
starts – holds the blank. Initial segments are ordered like the elements they
come from, so the input appears along the tape in the instance's own order, and
the whole of it is first-order describable over the instance, which is what the
expansion needs.
-/

/- The vocabulary of wide machines lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.turing`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of wide-machine instances: the control of
`FirstOrder.Language.turing`, with the positions and their order replaced by an
order on the elements – the digits of an address. -/
inductive wideRel : ℕ → Type
  /-- `wmLe x y`: the order on the elements, along which an address is read as a
  binary number. -/
  | wle : wideRel 2
  /-- `wmTr τ`: `τ` is a transition. -/
  | tr : wideRel 1
  /-- `wmStart q`: `q` is a start state. -/
  | start : wideRel 1
  /-- `wmAcc q`: `q` is an accepting state. -/
  | acc : wideRel 1
  /-- `wmBlank a`: `a` is the blank symbol. -/
  | blank : wideRel 1
  /-- `wmRight τ`: the transition `τ` moves the head right. -/
  | right : wideRel 1
  /-- `wmSrc τ q`: `τ` applies in the state `q`. -/
  | src : wideRel 2
  /-- `wmRead τ a`: `τ` applies when reading the symbol `a`. -/
  | read : wideRel 2
  /-- `wmDst τ q`: `τ` moves to the state `q`. -/
  | dst : wideRel 2
  /-- `wmWrite τ a`: `τ` writes the symbol `a`. -/
  | write : wideRel 2
  /-- `wmInp x a`: the address `{y | y ≤ x}` initially holds the symbol `a`. -/
  | inp : wideRel 2
  deriving DecidableEq

/-- The relational vocabulary of wide-machine instances. -/
protected def wide : Language :=
  ⟨fun _ => Empty, wideRel⟩
  deriving IsRelational

/-- The order on the elements of the instance. -/
abbrev wmLe : Language.wide.Relations 2 := .wle

/-- The transition symbol. -/
abbrev wmTr : Language.wide.Relations 1 := .tr

/-- The start-state symbol. -/
abbrev wmStart : Language.wide.Relations 1 := .start

/-- The accepting-state symbol. -/
abbrev wmAcc : Language.wide.Relations 1 := .acc

/-- The blank symbol. -/
abbrev wmBlank : Language.wide.Relations 1 := .blank

/-- The move-right symbol. -/
abbrev wmRight : Language.wide.Relations 1 := .right

/-- The transition-source symbol. -/
abbrev wmSrc : Language.wide.Relations 2 := .src

/-- The transition-read symbol. -/
abbrev wmRead : Language.wide.Relations 2 := .read

/-- The transition-destination symbol. -/
abbrev wmDst : Language.wide.Relations 2 := .dst

/-- The transition-write symbol. -/
abbrev wmWrite : Language.wide.Relations 2 := .write

/-- The input symbol. -/
abbrev wmInp : Language.wide.Relations 2 := .inp

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Language.wide.Structure A]

/-- The order on the elements of the instance. -/
def WMLe (a b : A) : Prop := RelMap wmLe ![a, b]

/-- Being a transition. -/
def WMTr (a : A) : Prop := RelMap wmTr ![a]

/-- Being a start state. -/
def WMStart (a : A) : Prop := RelMap wmStart ![a]

/-- Being an accepting state. -/
def WMAcc (a : A) : Prop := RelMap wmAcc ![a]

/-- Being the blank symbol. -/
def WMBlank (a : A) : Prop := RelMap wmBlank ![a]

/-- Moving the head right. -/
def WMRight (a : A) : Prop := RelMap wmRight ![a]

/-- The state a transition applies in. -/
def WMSrc (a b : A) : Prop := RelMap wmSrc ![a, b]

/-- The symbol a transition reads. -/
def WMRead (a b : A) : Prop := RelMap wmRead ![a, b]

/-- The state a transition moves to. -/
def WMDst (a b : A) : Prop := RelMap wmDst ![a, b]

/-- The symbol a transition writes. -/
def WMWrite (a b : A) : Prop := RelMap wmWrite ![a, b]

/-- The input at an initial-segment address. -/
def WMInp (a b : A) : Prop := RelMap wmInp ![a, b]

end Shorthands

/-! ### The universe and the machine -/

section Machine

variable (A : Type)

/-- **The universe of a wide machine**: the addresses – the subsets of the
instance, which are its tape cells and its time steps – together with the
elements of the instance, which are its control. An `abbrev`, so that the sum
structure stays visible to `rw` and to the elaborator. -/
abbrev WPoint : Type := (A → Prop) ⊕ A

variable {A} [Language.wide.Structure A]

/-- Being a position: the addresses are the positions, the control elements are
not. -/
def wpPosn : WPoint A → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The order on the universe: addresses first, in the binary-number order they
inherit from the instance's own order, then the control elements in that same
order. -/
def wpLe : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inl t => WMSetLe WMLe s t
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr x, Sum.inr y => WMLe x y

/-- A mark of the control, read on the universe of the machine: no address
carries it. -/
def wpMark (R : A → Prop) : WPoint A → Prop
  | Sum.inl _ => False
  | Sum.inr x => R x

/-- A binary attribute of the control, read on the universe of the machine. -/
def wpAttr (R : A → A → Prop) : WPoint A → WPoint A → Prop
  | Sum.inr x, Sum.inr y => R x y
  | _, _ => False

/-- The initial tape: the address cutting the initial segment of `x` holds the
input symbol of `x`. -/
def wpInp : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMDown WMLe s x ∧ WMInp x y
  | _, _ => False

variable (A) in
/-- **The wide machine an instance describes**: the control read off the
instance, the positions being the addresses. -/
def wideData : TMData (WPoint A) where
  Posn := wpPosn
  Le := wpLe
  Tr := wpMark WMTr
  Start := wpMark WMStart
  Acc := wpMark WMAcc
  Blank := wpMark WMBlank
  Right := wpMark WMRight
  Src := wpAttr WMSrc
  Read := wpAttr WMRead
  Dst := wpAttr WMDst
  Write := wpAttr WMWrite
  Inp := wpInp

end Machine

/-! ### Isomorphism-invariance -/

section Transport

variable {A B : Type} [Language.wide.Structure A] [Language.wide.Structure B]

/-- **An isomorphism of instances is a bijection of the machines' universes**:
addresses transport by taking preimages, control elements by the isomorphism
itself. -/
def wpointEquiv (e : A ≃[Language.wide] B) : WPoint A ≃ WPoint B where
  toFun := Sum.map (fun s y => s (e.toEquiv.symm y)) e.toEquiv
  invFun := Sum.map (fun t x => t (e.toEquiv x)) e.toEquiv.symm
  left_inv := by
    rintro (s | x)
    · exact congrArg Sum.inl (funext fun x =>
        congrArg s (e.toEquiv.symm_apply_apply x))
    · exact congrArg Sum.inr (e.toEquiv.symm_apply_apply x)
  right_inv := by
    rintro (t | y)
    · exact congrArg Sum.inl (funext fun y => congrArg t (e.toEquiv.apply_symm_apply y))
    · exact congrArg Sum.inr (e.toEquiv.apply_symm_apply y)

@[simp]
theorem wpointEquiv_addr (e : A ≃[Language.wide] B) (s : A → Prop) :
    wpointEquiv e (Sum.inl s) = Sum.inl fun y => s (e.symm y) :=
  rfl

@[simp]
theorem wpointEquiv_ctrl (e : A ≃[Language.wide] B) (x : A) :
    wpointEquiv e (Sum.inr x) = Sum.inr (e x) :=
  rfl

/-- **An isomorphism makes the two wide machines agree**, fieldwise: every
symbol of the vocabulary transports, and the two derived notions – the order on
addresses and the initial segment of an element – transport by
`DescriptiveComplexity.wmSetLe_congr` and
`DescriptiveComplexity.wmDown_congr`. -/
theorem wideData_agree (e : A ≃[Language.wide] B) :
    TMData.Agree (wpointEquiv e) (wideData A) (wideData B) := by
  have hle : ∀ x y : A, WMLe x y ↔ WMLe (e x) (e y) := fun x y =>
    relMap_equiv₂ e wmLe x y
  have hmark : ∀ (r : Language.wide.Relations 1) (x : A),
      (RelMap r ![x] : Prop) ↔ RelMap r ![(e x : B)] := fun r x => relMap_equiv₁ e r x
  have hattr : ∀ (r : Language.wide.Relations 2) (x y : A),
      (RelMap r ![x, y] : Prop) ↔ RelMap r ![(e x : B), (e y : B)] := fun r x y =>
    relMap_equiv₂ e r x y
  refine ⟨?_, ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro (s | x) <;> exact Iff.rfl
  · rintro (s | x) <;> rintro (t | y)
    · exact wmSetLe_congr e.toEquiv hle s t
    · exact Iff.rfl
    · exact Iff.rfl
    · exact hle x y
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark wmTr x
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark wmStart x
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark wmAcc x
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark wmBlank x
  · match p with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr x => exact hmark wmRight x
  · rintro (s | x) <;> rintro (t | y) <;> first
      | exact Iff.rfl
      | exact hattr wmSrc x y
  · rintro (s | x) <;> rintro (t | y) <;> first
      | exact Iff.rfl
      | exact hattr wmRead x y
  · rintro (s | x) <;> rintro (t | y) <;> first
      | exact Iff.rfl
      | exact hattr wmDst x y
  · rintro (s | x) <;> rintro (t | y) <;> first
      | exact Iff.rfl
      | exact hattr wmWrite x y
  · rintro (s | x) <;> rintro (t | y) <;> try exact Iff.rfl
    constructor
    · rintro ⟨z, hd, hi⟩
      exact ⟨e.toEquiv z, (wmDown_congr e.toEquiv hle s z).mp hd, (hattr wmInp z y).mp hi⟩
    · rintro ⟨z, hd, hi⟩
      have hinp : ∀ x y : A, WMInp x y ↔ WMInp (e.toEquiv x) (e.toEquiv y) := fun x y =>
        relMap_equiv₂ e wmInp x y
      refine ⟨e.toEquiv.symm z, ?_, (hinp _ y).mpr ?_⟩
      · rw [wmDown_congr e.toEquiv hle, Equiv.apply_symm_apply]
        exact hd
      · rw [Equiv.apply_symm_apply]
        exact hi

end Transport

/-! ### The problems -/

section Problems

/-- **Wide machine acceptance.** Does the machine described by the instance –
its tape addressed by the *subsets* of the instance – accept its input within as
many steps as there are addresses? The well-formedness promises of
`DescriptiveComplexity.TMData.WellFormed` are folded into the yes-instances, as
for `DescriptiveComplexity.NTMAccept`; here they amount to the instance's order
being linear, its input functional and its blank unique. -/
def WideAccept : DecisionProblem Language.wide where
  Holds := fun A _ => (wideData A).WellFormed ∧ (wideData A).Accepts
  iso_invariant := fun {A B} _ _ e => by
    have h := wideData_agree e
    exact and_congr h.wellFormed h.accepts

/-- **Wide machine acceptance in bounded space**: the same question with the
step bound dropped. The space is still bounded by construction – the tape is
indexed by the addresses – but a run may now visit doubly exponentially many
configurations. -/
def WideAcceptSpace : DecisionProblem Language.wide where
  Holds := fun A _ => (wideData A).WellFormed ∧ (wideData A).AcceptsSpace
  iso_invariant := fun {A B} _ _ e => by
    have h := wideData_agree e
    exact and_congr h.wellFormed h.acceptsSpace

/-- **Deterministic wide machine acceptance in bounded space**, with determinism
folded into the yes-instances as in `DescriptiveComplexity.DTMAcceptSpace`. -/
def DWideAcceptSpace : DecisionProblem Language.wide where
  Holds := fun A _ => (wideData A).WellFormed ∧ (wideData A).Deterministic ∧
    (wideData A).AcceptsSpace
  iso_invariant := fun {A B} _ _ e => by
    have h := wideData_agree e
    exact and_congr h.wellFormed (and_congr h.deterministic h.acceptsSpace)

end Problems

end DescriptiveComplexity
