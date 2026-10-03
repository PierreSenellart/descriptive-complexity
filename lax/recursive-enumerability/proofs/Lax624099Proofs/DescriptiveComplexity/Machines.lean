/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Numbers.BinRel
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099Proofs.DescriptiveComplexity.Config
end Lax624099Proofs.DescriptiveComplexity.Config

namespace Lax624099Proofs.DescriptiveComplexity.TMData
end Lax624099Proofs.DescriptiveComplexity.TMData

namespace Lax624099Proofs.DescriptiveComplexity.TMData.Agree
end Lax624099Proofs.DescriptiveComplexity.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity.TMData.ReachesIn
end Lax624099Proofs.DescriptiveComplexity.TMData.ReachesIn

namespace Lax624099Proofs.DescriptiveComplexity.TMData.StepsIn
end Lax624099Proofs.DescriptiveComplexity.TMData.StepsIn

/-!
# Turing machines over a universe, without a vocabulary

The semantics half of the machine bridge: what it means for a nondeterministic
Turing machine, presented as *relations on a universe*, to accept. No
vocabulary appears here – `Lax624099Proofs.DescriptiveComplexity.Problems.Machine.Defs` supplies one and
reads these definitions off a structure – so that the reductions, which build
machines rather than read them, can reason about runs without unfolding any
`RelMap`.

## The model

A machine is `Lax624099Proofs.DescriptiveComplexity.TMData`: the sorts (`Posn`, `Tr`), the marks
(`Start`, `Acc`, `Blank`, `Right`), the binary attributes of a transition
(`Src`, `Read`, `Dst`, `Write`), the initial tape `Inp`, and a linear order
`Le`. Two decisions are visible in the types.

* **Transitions are elements.** A transition is an element `τ` of the universe
  with four binary attributes, rather than a 5-ary relation; every relation
  here has arity at most two, which is what keeps the defining formulas of an
  interpretation indexed by *pairs* of tags.
* **Time steps and tape cells are the same sort.** A configuration's head is a
  position, and the time bound of `Lax624099Proofs.DescriptiveComplexity.TMData.Accepts` is the *number*
  of positions – a unary bound by construction, with no arithmetic. A head at
  the last position moving right has no successor
  (`Lax624099Proofs.DescriptiveComplexity.SuccPos` fails), and the run simply stops.

A run is read in three ways, and which one a construction uses is what its
resource bound can see. `Lax624099Proofs.DescriptiveComplexity.TMData.StepsIn` counts exactly, so
two phases of unknown length do not compose; `Relation.ReflTransGen` composes but
carries no count, so `Lax624099Proofs.DescriptiveComplexity.TMData.Accepts` cannot read it; and
`Lax624099Proofs.DescriptiveComplexity.TMData.ReachesIn` – a run of *at most* `n` steps – does
both, composing by adding budgets and weakening upwards. A clocked program is
written with the third and a space-bounded one with its erasure, which is how the
two share their phase lemmas.

The tape is a total function `A → A`, so the semantics is total: reading a cell
never fails. Which functions count as *initial* tapes is
`Lax624099Proofs.DescriptiveComplexity.TMData.InitTape` – the input where it is defined, blank elsewhere –
stated as a relation so that no choice is needed and so that the first-order
kernel of the membership proof can check it literally.

## Transport

`Lax624099Proofs.DescriptiveComplexity.TMData.Agree` records that two machines over different universes
correspond along an equivalence, fieldwise; `Lax624099Proofs.DescriptiveComplexity.TMData.Agree.accepts`
transports acceptance along it. This is all the isomorphism-invariance proof of
the decision problems needs.
-/

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-! ### The algebra of budgets -/

end Steps

section Unique

variable {M}

/-- **A well-formed initial tape is functional**: a cell holds either its
unique input symbol or the unique blank, and the two cases exclude each
other. -/
theorem initTape_functional (hwf : M.WellFormed) {p a b : A}
    (ha : M.InitTape p a) (hb : M.InitTape p b) : a = b := by
  rcases ha with ha | ⟨hna, ha⟩ <;> rcases hb with hb | ⟨hnb, hb⟩
  · exact hwf.2.2.1 p _ _ ha hb
  · exact absurd ha (hnb _)
  · exact absurd hb (hna _)
  · exact hwf.2.2.2.2 _ _ ha hb

end Unique

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax624099Proofs.DescriptiveComplexity.TMData (initTape_functional)

end Lax904597.Machines.TMData

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Unique

variable {M}

end Unique

/-! ### Transport along an equivalence of universes -/

section Transport

variable {B : Type}

variable {M}

/-- Two machines over different universes **agree** along an equivalence when
every relation of one is the pullback of the other's. -/
structure Agree (u : B ≃ A) (N : Lax904597.Machines.TMData B) (M : Lax904597.Machines.TMData A) : Prop where
  /-- The positions correspond. -/
  posn : ∀ b, N.Posn b ↔ M.Posn (u b)
  /-- The orders correspond. -/
  le : ∀ b b', N.Le b b' ↔ M.Le (u b) (u b')
  /-- The transitions correspond. -/
  tr : ∀ b, N.Tr b ↔ M.Tr (u b)
  /-- The start states correspond. -/
  start : ∀ b, N.Start b ↔ M.Start (u b)
  /-- The accepting states correspond. -/
  acc : ∀ b, N.Acc b ↔ M.Acc (u b)
  /-- The blanks correspond. -/
  blank : ∀ b, N.Blank b ↔ M.Blank (u b)
  /-- The directions correspond. -/
  right : ∀ b, N.Right b ↔ M.Right (u b)
  /-- The sources correspond. -/
  src : ∀ b b', N.Src b b' ↔ M.Src (u b) (u b')
  /-- The read symbols correspond. -/
  read : ∀ b b', N.Read b b' ↔ M.Read (u b) (u b')
  /-- The destinations correspond. -/
  dst : ∀ b b', N.Dst b b' ↔ M.Dst (u b) (u b')
  /-- The written symbols correspond. -/
  write : ∀ b b', N.Write b b' ↔ M.Write (u b) (u b')
  /-- The inputs correspond. -/
  inp : ∀ b b', N.Inp b b' ↔ M.Inp (u b) (u b')

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax624099Proofs.DescriptiveComplexity.TMData (Agree)

end Lax904597.Machines.TMData

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (acc blank dst inp le posn read right src start tr write)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Linearity of corresponding orders, in both directions. -/
private theorem isLinOrd_congr (u : B ≃ A) {LeB : B → B → Prop} {LeA : A → A → Prop}
    (hle : ∀ b b', LeB b b' ↔ LeA (u b) (u b')) : Lax904597.Machines.IsLinOrd LeB ↔ Lax904597.Machines.IsLinOrd LeA :=
  ⟨IsLinOrd.of_equiv u hle, IsLinOrd.of_equiv u.symm fun a a' => by
    rw [hle, Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩

theorem Agree.minPos (h : Agree u N M) {b : B} :
    Lax904597.Machines.MinPos N.Le N.Posn b ↔ Lax904597.Machines.MinPos M.Le M.Posn (u b) := by
  refine and_congr (h.posn b) ⟨fun hm a ha => ?_, fun hm a ha => ?_⟩
  · have := hm (u.symm a) ((h.posn _).mpr (by rwa [Equiv.apply_symm_apply]))
    rwa [(h.le _ _), Equiv.apply_symm_apply] at this
  · exact (h.le _ _).mpr (hm (u a) ((h.posn a).mp ha))

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (minPos)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.succPos (h : Agree u N M) {b b' : B} :
    Lax904597.Machines.SuccPos N.Le N.Posn b b' ↔ Lax904597.Machines.SuccPos M.Le M.Posn (u b) (u b') := by
  refine and_congr (h.posn b) (and_congr (h.posn b') (and_congr (h.le _ _)
    (and_congr u.injective.ne_iff.symm ⟨fun hs a ha h₁ h₂ => ?_, fun hs a ha h₁ h₂ => ?_⟩)))
  · have := hs (u.symm a) ((h.posn _).mpr (by rwa [Equiv.apply_symm_apply]))
      ((h.le _ _).mpr (by rwa [Equiv.apply_symm_apply]))
      ((h.le _ _).mpr (by rwa [Equiv.apply_symm_apply]))
    rcases this with h' | h' <;> [left; right] <;>
      exact u.symm_apply_eq.mp h'
  · rcases hs (u a) ((h.posn a).mp ha) ((h.le _ _).mp h₁) ((h.le _ _).mp h₂) with h' | h' <;>
      [left; right] <;> exact u.injective h'

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (succPos)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.initTape (h : Agree u N M) {b b' : B} :
    N.InitTape b b' ↔ M.InitTape (u b) (u b') := by
  refine or_congr (h.inp _ _) (and_congr ⟨fun hn a ha => ?_, fun hn a ha => ?_⟩ (h.blank _))
  · exact hn (u.symm a) ((h.inp _ _).mpr (by rwa [Equiv.apply_symm_apply]))
  · exact hn (u a) ((h.inp _ _).mp ha)

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (initTape)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- **Well-formedness transports along an equivalence.** -/
theorem Agree.wellFormed (h : Agree u N M) : N.WellFormed ↔ M.WellFormed := by
  have hinp : ∀ p a : A, M.Inp p a ↔ N.Inp (u.symm p) (u.symm a) := by
    intro p a; rw [h.inp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hblank : ∀ a : A, M.Blank a ↔ N.Blank (u.symm a) := by
    intro a; rw [h.blank, Equiv.apply_symm_apply]
  refine and_congr (isLinOrd_congr u fun b b' => h.le b b')
    (and_congr ⟨fun ⟨p, hp⟩ => ⟨u p, (h.posn p).mp hp⟩,
        fun ⟨p, hp⟩ => ⟨u.symm p, (h.posn _).mpr (by rwa [Equiv.apply_symm_apply])⟩⟩
      (and_congr ⟨fun hf p a b ha hb => ?_, fun hf p a b ha hb => ?_⟩
        (and_congr ⟨fun ⟨b, hb⟩ => ⟨u b, (h.blank b).mp hb⟩,
            fun ⟨b, hb⟩ => ⟨u.symm b, (h.blank _).mpr (by rwa [Equiv.apply_symm_apply])⟩⟩
          ⟨fun hb x y hx hy => ?_, fun hb x y hx hy => ?_⟩)))
  · exact u.symm.injective
      (hf (u.symm p) (u.symm a) (u.symm b) ((hinp p a).mp ha) ((hinp p b).mp hb))
  · exact u.injective (hf (u p) (u a) (u b) ((h.inp _ _).mp ha) ((h.inp _ _).mp hb))
  · exact u.symm.injective (hb (u.symm x) (u.symm y) ((hblank x).mp hx) ((hblank y).mp hy))
  · exact u.injective (hb (u x) (u y) ((h.blank _).mp hx) ((h.blank _).mp hy))

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (wellFormed)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {B : Type}

variable {M}

variable {u : B ≃ A} {N : Lax904597.Machines.TMData B}

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity


