import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.ModelTheory.Syntax
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Set Cover, Hitting Set, Set Packing, Exact Cover and Set Splitting
type: theorem
---
Five problems on set systems: a universe carrying two unary marks that
separate the ground elements from the sets of a family, a binary
incidence relation between them, and a third unary mark whose
cardinality is the threshold $k$, in unary representation. SetCover asks
for at most $k$ sets covering every element, HittingSet for at most $k$
elements meeting every set, SetPacking for at least $k$ pairwise disjoint
sets, ExactCover for a subfamily covering every element exactly once, and
SetSplitting for a two-coloring of the elements leaving no set
monochromatic. Nothing forces an element of the universe to be an element
or a set, and disjointness in a packing is required of the ground
elements only; both conventions are what let a first-order interpretation
build a set system inside a tagged power of its input.

All five are in NP by existential second-order definitions except Hitting
Set, which reduces to Set Cover by reading incidence backwards, the same
interpretation reducing Set Cover to Hitting Set. Hardness comes by
first-order reductions: Set Cover from Vertex Cover, Set Packing from
Independent Set, Exact Cover from 1-in-SAT, Set Splitting from NAE-SAT.

-/

namespace Lax799700.SetFamily

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive setSystemRel : ℕ → Type where
/-- `elem a`: the element `a` belongs to the ground set. -/
  | elem : setSystemRel 1
/-- `fam a`: the element `a` is one of the sets of the family. -/
  | fam : setSystemRel 1
/-- `mem a b`: the ground element `a` belongs to the set `b`. -/
  | mem : setSystemRel 2
/-- `marked a`: the element `a` belongs to the marked set. -/
  | marked : setSystemRel 1
  deriving DecidableEq

/-- The relational language of set systems: a bipartite incidence structure
between ground elements and sets of a family, together with a marked subset of
the universe whose cardinality serves as threshold. -/
def setSystem : FirstOrder.Language :=
  ⟨fun _ => Empty, setSystemRel⟩

instance instIsRelationalSetSystem : FirstOrder.Language.IsRelational setSystem := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `elem a`: the element `a` belongs to the ground set. -/
abbrev ssElem : setSystem.Relations 1 :=
  .elem

/-- `fam a`: the element `a` is one of the sets of the family. -/
abbrev ssFam : setSystem.Relations 1 :=
  .fam

/-- `mem a b`: the ground element `a` belongs to the set `b`. -/
abbrev ssMem : setSystem.Relations 2 :=
  .mem

/-- `marked a`: the element `a` belongs to the marked set. -/
abbrev ssMarked : setSystem.Relations 1 :=
  .marked

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

/-- Some subfamily of the `Fp`-sets covers every `Ep`-element and is at most
as large as the number encoded by the `Kp`-marked elements: “some cover is at
most as large as the marked set”. -/
def CoversOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    {s | G s}.ncard ≤ {x | Kp x}.ncard

/-- Some set of `Ep`-elements meets every `Fp`-set and is at most as large as
the number encoded by the `Kp`-marked elements: “some hitting set is at most
as large as the marked set”. This is `DescriptiveComplexity.CoversOn` with the roles
of elements and sets exchanged and the incidence relation transposed. -/
def HitsOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  CoversOn Fp Ep (fun s x => Mp x s) Kp

/-- Some subfamily of the `Fp`-sets is pairwise disjoint – no `Ep`-element
belongs to two distinct members – and is at least as large as the number
encoded by the `Kp`-marked elements: “some packing is at least as large as the
marked set”. -/
def PacksOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
    (∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')) ∧
    {x | Kp x}.ncard ≤ {s | G s}.ncard

/-- Some subfamily of the `Fp`-sets covers every `Ep`-element *exactly once*:
it covers, and no element belongs to two distinct members. Unlike the three
properties above this one carries no threshold – exactness is the whole
constraint. -/
def ExactlyCoversOn (Ep Fp : A → Prop) (Mp : A → A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    ∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')

/-- Some two-coloring of the ground elements *splits* every set of the
family: no set is monochromatic. Like `DescriptiveComplexity.ExactlyCoversOn` this
property carries no threshold. -/
def SplitsOn (Ep Fp : A → Prop) (Mp : A → A → Prop) : Prop :=
  ∃ S : A → Prop, ∀ f, Fp f →
    (∃ x, Ep x ∧ Mp x f ∧ S x) ∧ ∃ x, Ep x ∧ Mp x f ∧ ¬S x

end Generic

section Problems

section Shorthands

variable {A : Type} [setSystem.Structure A]

/-- `elem a`: the element `a` belongs to the ground set.  -/
def SSElem {A : Type} [setSystem.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ssElem ![a0]

/-- `fam a`: the element `a` is one of the sets of the family.  -/
def SSFam {A : Type} [setSystem.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ssFam ![a0]

/-- `mem a b`: the ground element `a` belongs to the set `b`.  -/
def SSMem {A : Type} [setSystem.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ssMem ![a0, a1]

/-- `marked a`: the element `a` belongs to the marked set.  -/
def SSMarked {A : Type} [setSystem.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ssMarked ![a0]

end Shorthands

variable (A : Type) [setSystem.Structure A]

/-- A set system admits a cover at most as large as its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallSetCover : Prop :=
  Finite A ∧ CoversOn (SSElem (A := A)) SSFam SSMem SSMarked

/-- A set system admits a hitting set at most as large as its marked set. -/
def HasSmallHittingSet : Prop :=
  Finite A ∧ HitsOn (SSElem (A := A)) SSFam SSMem SSMarked

/-- A set system admits a packing at least as large as its marked set. -/
def HasLargeSetPacking : Prop :=
  Finite A ∧ PacksOn (SSElem (A := A)) SSFam SSMem SSMarked

/-- A set system admits an exact cover: a subfamily covering every ground
element exactly once. There is no threshold here, so no finiteness
assumption either. -/
def HasExactCover : Prop :=
  ExactlyCoversOn (SSElem (A := A)) SSFam SSMem

/-- A set system admits a splitting two-coloring: no set of the family is
monochromatic. -/
def HasSetSplitting : Prop :=
  SplitsOn (SSElem (A := A)) SSFam SSMem

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasSmallSetCover` is isomorphism-invariant. -/
axiom hasSmallSetCover_iso : ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B],
  (A ≃[Lax799700.SetFamily.setSystem] B) → (HasSmallSetCover A ↔ HasSmallSetCover B)

/-- The problem SetCover: does the structure satisfy `HasSmallSetCover`? -/
def SetCover : DecisionProblem Lax799700.SetFamily.setSystem :=
  DecisionProblem.ofPred HasSmallSetCover

/-- The yes-instances of SetCover are exactly the structures satisfying
`HasSmallSetCover`. -/
axiom setCover_iff : ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], SetCover A ↔ HasSmallSetCover A

/-- SetCover is NP-complete. -/
axiom setCover_NP_complete : NP.Complete SetCover

/-- The property `HasExactCover` is isomorphism-invariant. -/
axiom hasExactCover_iso : ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B],
  (A ≃[Lax799700.SetFamily.setSystem] B) → (HasExactCover A ↔ HasExactCover B)

/-- The problem ExactCover: does the structure satisfy `HasExactCover`? -/
def ExactCover : DecisionProblem Lax799700.SetFamily.setSystem :=
  DecisionProblem.ofPred HasExactCover

/-- The yes-instances of ExactCover are exactly the structures satisfying
`HasExactCover`. -/
axiom exactCover_iff : ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], ExactCover A ↔ HasExactCover A

/-- ExactCover is NP-complete. -/
axiom exactCover_NP_complete : NP.Complete ExactCover

/-- The property `HasSmallHittingSet` is isomorphism-invariant. -/
axiom hasSmallHittingSet_iso : ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B],
  (A ≃[Lax799700.SetFamily.setSystem] B) → (HasSmallHittingSet A ↔ HasSmallHittingSet B)

/-- The problem HittingSet: does the structure satisfy `HasSmallHittingSet`? -/
def HittingSet : DecisionProblem Lax799700.SetFamily.setSystem :=
  DecisionProblem.ofPred HasSmallHittingSet

/-- The yes-instances of HittingSet are exactly the structures satisfying
`HasSmallHittingSet`. -/
axiom hittingSet_iff : ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], HittingSet A ↔ HasSmallHittingSet A

/-- HittingSet is NP-complete. -/
axiom hittingSet_NP_complete : NP.Complete HittingSet

/-- The property `HasLargeSetPacking` is isomorphism-invariant. -/
axiom hasLargeSetPacking_iso : ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B],
  (A ≃[Lax799700.SetFamily.setSystem] B) → (HasLargeSetPacking A ↔ HasLargeSetPacking B)

/-- The problem SetPacking: does the structure satisfy `HasLargeSetPacking`? -/
def SetPacking : DecisionProblem Lax799700.SetFamily.setSystem :=
  DecisionProblem.ofPred HasLargeSetPacking

/-- The yes-instances of SetPacking are exactly the structures satisfying
`HasLargeSetPacking`. -/
axiom setPacking_iff : ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], SetPacking A ↔ HasLargeSetPacking A

/-- SetPacking is NP-complete. -/
axiom setPacking_NP_complete : NP.Complete SetPacking

/-- The property `HasSetSplitting` is isomorphism-invariant. -/
axiom hasSetSplitting_iso : ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B],
  (A ≃[Lax799700.SetFamily.setSystem] B) → (HasSetSplitting A ↔ HasSetSplitting B)

/-- The problem SetSplitting: does the structure satisfy `HasSetSplitting`? -/
def SetSplitting : DecisionProblem Lax799700.SetFamily.setSystem :=
  DecisionProblem.ofPred HasSetSplitting

/-- The yes-instances of SetSplitting are exactly the structures satisfying
`HasSetSplitting`. -/
axiom setSplitting_iff : ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], SetSplitting A ↔ HasSetSplitting A

/-- SetSplitting is NP-complete. -/
axiom setSplitting_NP_complete : NP.Complete SetSplitting

end Lax799700.SetFamily
