import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Hom.Set
import Lax799700.SetFamily
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems

/-!
---
title: Counting exact covers, packings, set covers, and hitting sets
type: definition
---
The instances are set systems: a universe of elements, a family of sets, and
a membership relation, with a marked threshold where a size is asked.
#Exact Cover counts the subfamilies covering every element exactly once.
#Set Packing counts the subfamilies of pairwise disjoint sets of exactly the
threshold size, #Set Cover the covering subfamilies of exactly the threshold
size, and #Hitting Set the sets of elements of exactly the threshold size
meeting every set of the family.
-/

namespace Lax280166.CountingSetFamilies

open Lax799700.SetFamily

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [setSystem.Structure A]

/-- The subfamily `G` is a packing with exactly as many sets as the marked set,
in a finite set system. -/
def PackingOfSize (G : A → Prop) : Prop :=
  Finite A ∧ (∀ s, G s → SSFam s) ∧
    (∀ s s', G s → G s' → s ≠ s' → ∀ x : A, SSElem x → ¬(SSMem x s ∧ SSMem x s')) ∧
    {s | G s}.ncard = {x : A | SSMarked x}.ncard

end Solutions

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The subfamily `G` of the `Fp`-sets covers every `Ep`-element and has
exactly as many members as the `Kp`-marked set. -/
def CoverFamOfSizeOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop)
    (G : A → Prop) : Prop :=
  (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    {s | G s}.ncard = {x | Kp x}.ncard

end Generic

section Problems

variable (A : Type) [setSystem.Structure A]

/-- The subfamily `G` is a cover with exactly as many sets as the marked set,
in a finite set system. -/
def SetCoverOfSize (G : A → Prop) : Prop :=
  Finite A ∧ CoverFamOfSizeOn (fun x : A => SSElem x) (fun s => SSFam s)
    (fun x s => SSMem x s) (fun x => SSMarked x) G

/-- The set `H` of ground elements is a hitting set with exactly as many
elements as the marked set, in a finite set system. -/
def HittingSetOfSize (H : A → Prop) : Prop :=
  Finite A ∧ CoverFamOfSizeOn (fun s : A => SSFam s) (fun x => SSElem x)
    (fun s x => SSMem x s) (fun x => SSMarked x) H

end Problems

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

/-- The subfamily `G` is an exact cover: it consists of `Fp`-sets, covers every
`Ep`-element, and no element belongs to two distinct members. This is the body
of `ExactlyCoversOn`, named for the statements that are about a
particular cover and not only about the existence of one. -/
def ExactCoverBy (Ep Fp : A → Prop) (Mp : A → A → Prop) (G : A → Prop) : Prop :=
  (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    ∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')

end Generic

open Lax366625.CountingProblems Lax799700.SetFamily

/-- **#Exact Cover**, as a counting problem. -/
noncomputable def SharpExactCover : CountingProblem Lax799700.SetFamily.setSystem :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {G : A → Prop // ExactCoverBy (SSElem (A := A)) SSFam SSMem G}

/-- **#Set Packing**, as a counting problem. -/
noncomputable def SharpSetPacking : CountingProblem Lax799700.SetFamily.setSystem :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {G : A → Prop // PackingOfSize A G}

/-- **#Set Cover**, as a counting problem. -/
noncomputable def SharpSetCover : CountingProblem Lax799700.SetFamily.setSystem :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {G : A → Prop // SetCoverOfSize A G}

/-- **#Hitting Set**, as a counting problem. -/
noncomputable def SharpHittingSet : CountingProblem Lax799700.SetFamily.setSystem :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {H : A → Prop // HittingSetOfSize A H}

end Lax280166.CountingSetFamilies
