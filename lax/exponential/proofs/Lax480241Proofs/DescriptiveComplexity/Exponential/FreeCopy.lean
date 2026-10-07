/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Free
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

/-!
# The copies of an order-guessing expansion, and the problem read in one of them

`DescriptiveComplexity.ExpExpansion.orderFree` guesses the order into the block,
and its universe is therefore the **disjoint union, over the linear orders of
the instance, of copies** of the intended one. The copies are the classes of the
symbol `DescriptiveComplexity.ExpExpansion.sameSym`, and this file reads the
inner problem inside one of them:

* `DescriptiveComplexity.ExpExpansion.clsPart` is the part of a structure over
  the order-guessing vocabulary that a set of points carves out, read over the
  **original** vocabulary – a nullary symbol being read off its unary shift;
* `DescriptiveComplexity.ExpExpansion.IsCls` says that a set of points is one of
  the copies: nonempty, and consisting of exactly the points that carry the
  order of any one of its members;
* `DescriptiveComplexity.ExpExpansion.someCls` is “**some copy answers yes**”,
  the problem that replaces the inner one, and
  `DescriptiveComplexity.ExpExpansion.someCls_map_iff` is its correctness: on
  the expansion of a structure carrying no order, it says that the inner problem
  holds of the expanded universe **for some linear order** of the instance.
  Together with order-invariance – the equivalence being asked at *every* linear
  order in `DescriptiveComplexity.ExpDefinable` – that is what removes the order
  from the statement.

The whole content is the identification of a copy: a set of points satisfying
`IsCls` is the image of the copy map at the order its members carry
(`DescriptiveComplexity.ExpExpansion.eq_range_copyIn`), so it is isomorphic, over
the original vocabulary, to the expanded universe read at that order
(`DescriptiveComplexity.ExpExpansion.clsEquiv`).
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Reducts along a language morphism -/

/-- An isomorphism restricts to the reducts along a language morphism. -/
def reductEquiv {F F' : Language.{0, 0}} (φ : F →ᴸ F') {M N : Type} [F'.Structure M]
    [F'.Structure N] (e : M ≃[F'] N) :
    letI := φ.reduct M
    letI := φ.reduct N
    M ≃[F] N :=
  letI := φ.reduct M
  letI := φ.reduct N
  { toEquiv := e.toEquiv
    map_fun' := fun f x => e.map_fun' (φ.onFunction f) x
    map_rel' := fun r x => e.map_rel' (φ.onRelation r) x }

theorem vec_one_eq {M : Type} (z : M) : (![z] : Fin 1 → M) = fun _ => z := by
  funext i
  fin_cases i
  rfl

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-! ### A part of the order-guessing universe, over the original vocabulary -/

section Part

variable {N : Type} [X.orderFree.E.Structure N]

/-- The part of a structure over the order-guessing vocabulary that a set of
points carves out. The expansion is a parameter although the carrier does not
depend on it: it is what the structure below is read over. -/
def clsPart (X : Lax480241.Expansions.ExpExpansion L) {N : Type} [X.orderFree.E.Structure N] (S : Set N) : Type :=
  {x : N // x ∈ S}

end Part

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (clsPart)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Part

variable {N : Type} [X.orderFree.E.Structure N]

/-- **The part, read over the original vocabulary**: a symbol of arity at least
one holds of a tuple of the part as it held in the whole, and a nullary symbol
holds when its unary shift holds of a point of the part. -/
instance clsPartStructure (S : Set N) : X.E.Structure (X.clsPart S) where
  funMap f := isEmptyElim f
  RelMap {n} r xs :=
    match n, r, xs with
    | 0, r, _ => ∃ x : N, x ∈ S ∧ RelMap (X.nullSym r) fun _ => x
    | (_ + 1), r, xs => RelMap (X.origSym r) fun i => (xs i).1

end Part

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (clsPartStructure)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Part

variable {N : Type} [X.orderFree.E.Structure N]

variable {X}

theorem relMap_clsPart_zero {S : Set N} (r : X.E.Relations 0) (xs : Fin 0 → X.clsPart S) :
    RelMap r xs ↔ ∃ x : N, x ∈ S ∧ RelMap (X.nullSym r) fun _ => x :=
  Iff.rfl

end Part

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (relMap_clsPart_zero)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Part

variable {N : Type} [X.orderFree.E.Structure N]

variable {X}

theorem relMap_clsPart_succ {S : Set N} {m : ℕ} (r : X.E.Relations (m + 1))
    (xs : Fin (m + 1) → X.clsPart S) :
    RelMap r xs ↔ RelMap (X.origSym r) fun i => (xs i).1 :=
  Iff.rfl

end Part

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (relMap_clsPart_succ)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Part

variable {N : Type} [X.orderFree.E.Structure N]

variable {X}

variable (X)

/-- **A set of points is a copy**: it is nonempty, and it consists of exactly
the points carrying the order of any one of its members. -/
def IsCls (X : Lax480241.Expansions.ExpExpansion L) {N : Type} [X.orderFree.E.Structure N] (S : Set N) : Prop :=
  (∃ x, x ∈ S) ∧ ∀ x ∈ S, ∀ y, (y ∈ S ↔ RelMap X.sameSym ![x, y])

end Part

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (IsCls)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Part

variable {N : Type} [X.orderFree.E.Structure N]

variable {X}

variable (X)

end Part

/-! ### Transporting a part along an isomorphism -/

section Transport

variable {N N' : Type} [X.orderFree.E.Structure N] [X.orderFree.E.Structure N']
  (e : N ≃[X.orderFree.E] N') (S : Set N)

/-- A part is carried along an isomorphism of the ambient structures, over the
original vocabulary. -/
noncomputable def clsPartEquiv : X.clsPart S ≃[X.E] X.clsPart (e '' S) where
  toFun x := ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
  invFun y := ⟨e.symm y.1, by
    obtain ⟨x, hx, hex⟩ := y.2
    have : e.symm y.1 = x := by rw [← hex, e.symm_apply_apply]
    rw [this]
    exact hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_fun' f := isEmptyElim f
  map_rel' {n} r x := by
    match n, r with
    | 0, r =>
      refine Iff.trans (relMap_clsPart_zero r _) (Iff.trans ?_ (relMap_clsPart_zero r x).symm)
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
        exact ⟨z, hz, (StrongHomClass.map_rel e (X.nullSym r) fun _ => z).mp hy⟩
      · rintro ⟨z, hz, hzr⟩
        exact ⟨e z, ⟨z, hz, rfl⟩,
          (StrongHomClass.map_rel e (X.nullSym r) fun _ => z).mpr hzr⟩
    | (m + 1), r =>
      refine Iff.trans (relMap_clsPart_succ r _) (Iff.trans ?_ (relMap_clsPart_succ r x).symm)
      exact StrongHomClass.map_rel e (X.origSym r) fun i => (x i).1

end Transport

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (clsPartEquiv)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Transport

variable {N N' : Type} [X.orderFree.E.Structure N] [X.orderFree.E.Structure N']
  (e : N ≃[X.orderFree.E] N') (S : Set N)

/-- Membership of a transported copy. -/
theorem isCls_image (h : IsCls X S) : IsCls X (e '' S) := by
  obtain ⟨⟨x₀, hx₀⟩, hmem⟩ := h
  refine ⟨⟨e x₀, ⟨x₀, hx₀, rfl⟩⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩ z
  constructor
  · rintro ⟨z', hz', rfl⟩
    exact (relMap_equiv₂ e X.sameSym x z').mp ((hmem x hx z').mp hz')
  · intro hrel
    have hz : e.symm z ∈ S := by
      refine (hmem x hx (e.symm z)).mpr ((relMap_equiv₂ e X.sameSym x (e.symm z)).mpr ?_)
      rw [e.apply_symm_apply z]
      exact hrel
    exact ⟨e.symm z, hz, e.apply_symm_apply z⟩

end Transport

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (isCls_image)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Transport

variable {N N' : Type} [X.orderFree.E.Structure N] [X.orderFree.E.Structure N']
  (e : N ≃[X.orderFree.E] N') (S : Set N)

end Transport

/-! ### Some copy answers yes -/

/-- **Some copy answers yes**: the problem read inside one of the copies of an
order-guessing expansion. -/
def someCls (Q : Lax904597.Problems.DecisionProblem X.E) : Lax904597.Problems.DecisionProblem X.orderFree.E where
  Holds N _ := ∃ S : Set N, IsCls X S ∧ Q (X.clsPart S)
  iso_invariant := by
    intro N N' _ _ e
    constructor
    · rintro ⟨S, hS, hQ⟩
      exact ⟨e '' S, isCls_image X e S hS, (Q.iso_invariant (clsPartEquiv X e S)).mp hQ⟩
    · rintro ⟨S, hS, hQ⟩
      refine ⟨e.symm '' S, isCls_image X e.symm S hS, ?_⟩
      exact (Q.iso_invariant (clsPartEquiv X e.symm S)).mp hQ

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (someCls)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-! ### A copy is the image of the copy map -/

section Copy

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

/-- **Every copy is the image of a copy map**: a set of points satisfying
`DescriptiveComplexity.ExpExpansion.IsCls`, one of whose members carries the
ambient order, consists of exactly the placed points. -/
theorem eq_range_copyIn {S : Set (X.orderFree.Map A)} (hS : IsCls X S)
    {p : X.orderFree.Map A} (hp : p ∈ S)
    (hord : ∀ w : Fin 2 → A, pointOrd p w ↔ loRel w) :
    S = Set.range (copyIn (X := X) (A := A)) := by
  have key : ∀ y : X.orderFree.Map A, y ∈ S ↔ ∀ w : Fin 2 → A, pointOrd y w ↔ loRel w := by
    intro y
    refine Iff.trans (hS.2 p hp y) ?_
    refine Iff.trans (relMap_sameSym ![p, y]) ?_
    exact ⟨fun h w => (h w).symm.trans (hord w), fun h w => (hord w).trans (h w).symm⟩
  ext y
  refine Iff.trans (key y) ?_
  constructor
  · intro h
    exact exists_copyIn h
  · rintro ⟨x, rfl⟩
    exact pointOrd_copyIn x

end Copy

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (eq_range_copyIn)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Copy

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

/-- The placed points, as a part of the order-guessing universe. -/
def toCls {S : Set (X.orderFree.Map A)} (hS : S = Set.range (copyIn (X := X) (A := A)))
    (x : X.Map A) : X.clsPart S :=
  ⟨copyIn x, hS ▸ Set.mem_range_self x⟩

end Copy

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (toCls)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Copy

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

/-- **A copy is the expanded universe**, over the original vocabulary and at the
order its points carry. -/
noncomputable def clsEquiv {S : Set (X.orderFree.Map A)}
    (hS : S = Set.range (copyIn (X := X) (A := A))) [Finite A] [Nonempty A] :
    X.Map A ≃[X.E] X.clsPart S := by
  have hbij : Function.Bijective (toCls hS) := by
    constructor
    · intro x y h
      exact copyIn_injective (congrArg (fun z : X.clsPart S => z.1) h)
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hS ▸ hy
      exact ⟨x, rfl⟩
  refine
    { toEquiv := Equiv.ofBijective _ hbij
      map_fun' := fun f => isEmptyElim f
      map_rel' := fun {n} r x => ?_ }
  match n, r with
  | 0, r =>
    refine Iff.trans (relMap_clsPart_zero r _) ?_
    constructor
    · rintro ⟨z, hz, hzr⟩
      obtain ⟨u, rfl⟩ := hS ▸ hz
      exact (relMap_nullCopyIn r (fun _ => u) x).mp hzr
    · intro hr
      obtain ⟨u⟩ := (inferInstance : Nonempty (X.Map A))
      exact ⟨copyIn u, hS ▸ Set.mem_range_self u, (relMap_nullCopyIn r (fun _ => u) x).mpr hr⟩
  | (m + 1), r =>
    refine Iff.trans (relMap_clsPart_succ r _) ?_
    exact relMap_copyIn r x

end Copy

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (clsEquiv)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

section Copy

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

end Copy

/-! ### The correctness of “some copy answers yes” -/

variable {X} {Q : Lax904597.Problems.DecisionProblem X.E} {A : Type} [L.Structure A] [Finite A] [Nonempty A]

/-- **Some copy answers yes exactly when the inner problem does, at some linear
order of the instance.** The expansion is read on a structure carrying no order
at all; each copy is the expanded universe at the order it guesses. -/
theorem someCls_map_iff :
    (someCls X Q) (X.orderFree.Map A) ↔
      ∃ lo : LinearOrder A, letI := lo; Q (X.Map A) := by
  constructor
  · rintro ⟨S, hS, hQ⟩
    obtain ⟨p, hp⟩ := hS.1
    let lo := guessedLinearOrder p
    refine ⟨lo, ?_⟩
    have hord : ∀ w : Fin 2 → A, pointOrd p w ↔ loRel (A := A) w :=
      fun w => (le_guessedLinearOrder p w).symm
    exact (Q.iso_invariant (clsEquiv (eq_range_copyIn hS hp hord))).mpr hQ
  · rintro ⟨lo, hQ⟩
    let := lo
    refine ⟨Set.range (copyIn (X := X) (A := A)), ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨u⟩ := (inferInstance : Nonempty (X.Map A))
      exact ⟨copyIn u, Set.mem_range_self u⟩
    · rintro y ⟨u, rfl⟩ z
      refine Iff.trans ?_ (relMap_sameSym ![copyIn u, z]).symm
      constructor
      · rintro ⟨v, rfl⟩ w
        exact (pointOrd_copyIn u w).trans (pointOrd_copyIn v w).symm
      · intro h
        exact exists_copyIn fun w => (h w).symm.trans (pointOrd_copyIn u w)
    · exact (Q.iso_invariant (clsEquiv rfl)).mp hQ

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (someCls_map_iff)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {Q : Lax904597.Problems.DecisionProblem X.E} {A : Type} [L.Structure A] [Finite A] [Nonempty A]

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


