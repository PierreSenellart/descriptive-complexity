/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.IsoGadget
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

namespace Lax604544Proofs.Foreign.FirstOrder.Language
end Lax604544Proofs.Foreign.FirstOrder.Language

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax604544Proofs.DescriptiveComplexity

/-!
# Two marked copies of a vocabulary, and the isomorphism problem they carry

Every problem of the GI degree has the same shape: one universe holding two
marked structures over the same vocabulary, and the question whether they are
isomorphic. `DescriptiveComplexity.Problems.DigraphIso` and
`DescriptiveComplexity.Problems.DagIso` each hand-roll that shape
(`FirstOrder.Language.twoGraphs`, `FirstOrder.Language.twoDags`), which is fine
for one problem and wasteful for a family.

`FirstOrder.Language.twoCopies L₁` builds it once: two unary marks, and two
copies of every relation symbol of `L₁`. A structure over it carries an
`L₁`-structure on each marked set
(`DescriptiveComplexity.patSideStructure`,
`DescriptiveComplexity.hostSideStructure`), and
`DescriptiveComplexity.TwoCopiesIso` is the decision problem asking whether
those two `L₁`-structures are isomorphic.

The reason to have it is the *gadget* layer this file is written for: a
construction on single `L₁`-structures can be doubled – run relativized to each
mark – only if the target vocabulary is known to be two copies of something,
since the defining formulas have to be given symbol by symbol. Problems added
to the degree from here on should be stated over `twoCopies`; the two existing
hand-rolled vocabularies stay as they are, their results being already proved.
-/

namespace FirstOrder

namespace Language

open Lax604544Proofs.Foreign.FirstOrder.Language in
/-- Relation symbols of the two-copy vocabulary: a mark for each side, and two
copies of every relation symbol of the base vocabulary. -/
inductive _root_.Lax604544Proofs.Foreign.FirstOrder.Language.twoCopiesRel (L₁ : Language.{0, 0}) : ℕ → Type
  /-- `patMark a`: `a` belongs to the pattern side. -/
  | patMark : Lax604544Proofs.Foreign.FirstOrder.Language.twoCopiesRel L₁ 1
  /-- `hostMark a`: `a` belongs to the host side. -/
  | hostMark : Lax604544Proofs.Foreign.FirstOrder.Language.twoCopiesRel L₁ 1
  /-- The pattern copy of a relation symbol of the base vocabulary. -/
  | pat {n : ℕ} (r : L₁.Relations n) : Lax604544Proofs.Foreign.FirstOrder.Language.twoCopiesRel L₁ n
  /-- The host copy of a relation symbol of the base vocabulary. -/
  | host {n : ℕ} (r : L₁.Relations n) : Lax604544Proofs.Foreign.FirstOrder.Language.twoCopiesRel L₁ n

export Lax604544Proofs.Foreign.FirstOrder.Language (twoCopiesRel)

open Lax604544Proofs.Foreign.FirstOrder.Language in
/-- Two marked copies of a relational vocabulary, sharing one universe. -/
protected def _root_.Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies (L₁ : Language.{0, 0}) : Language :=
  ⟨fun _ => Empty, Lax604544Proofs.Foreign.FirstOrder.Language.twoCopiesRel L₁⟩

export Lax604544Proofs.Foreign.FirstOrder.Language (twoCopies)

open Lax604544Proofs.Foreign.FirstOrder.Language in
instance _root_.Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies_isRelational (L₁ : Language.{0, 0}) : (Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

export Lax604544Proofs.Foreign.FirstOrder.Language (twoCopies_isRelational)

open Lax604544Proofs.Foreign.FirstOrder.Language in
/-- The pattern mark. -/
abbrev _root_.Lax604544Proofs.Foreign.FirstOrder.Language.tcPatMark (L₁ : Language.{0, 0}) : (Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).Relations 1 := .patMark

export Lax604544Proofs.Foreign.FirstOrder.Language (tcPatMark)

open Lax604544Proofs.Foreign.FirstOrder.Language in
/-- The host mark. -/
abbrev _root_.Lax604544Proofs.Foreign.FirstOrder.Language.tcHostMark (L₁ : Language.{0, 0}) : (Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).Relations 1 := .hostMark

export Lax604544Proofs.Foreign.FirstOrder.Language (tcHostMark)

open Lax604544Proofs.Foreign.FirstOrder.Language in
/-- The pattern copy of a base relation symbol. -/
abbrev _root_.Lax604544Proofs.Foreign.FirstOrder.Language.tcPat {L₁ : Language.{0, 0}} {n : ℕ} (r : L₁.Relations n) :
    (Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).Relations n := .pat r

export Lax604544Proofs.Foreign.FirstOrder.Language (tcPat)

open Lax604544Proofs.Foreign.FirstOrder.Language in
/-- The host copy of a base relation symbol. -/
abbrev _root_.Lax604544Proofs.Foreign.FirstOrder.Language.tcHost {L₁ : Language.{0, 0}} {n : ℕ} (r : L₁.Relations n) :
    (Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).Relations n := .host r

export Lax604544Proofs.Foreign.FirstOrder.Language (tcHost)

end Language

end FirstOrder

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Sides

variable {L₁ : Language.{0, 0}} [L₁.IsRelational] {A : Type}

variable [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).Structure A]

/-- Belonging to the pattern side. -/
def TCPatMark (a : A) : Prop := RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcPatMark L₁) ![a]

/-- Belonging to the host side. -/
def TCHostMark (a : A) : Prop := RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcHostMark L₁) ![a]

/-- The pattern side, as a structure over the base vocabulary. -/
instance patSideStructure : L₁.Structure {x : A // TCPatMark (L₁ := L₁) x} where
  funMap f := isEmptyElim f
  RelMap {_} r w := RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcPat r) fun i => (w i).1

/-- The host side, as a structure over the base vocabulary. -/
instance hostSideStructure : L₁.Structure {x : A // TCHostMark (L₁ := L₁) x} where
  funMap f := isEmptyElim f
  RelMap {_} r w := RelMap (Lax604544Proofs.Foreign.FirstOrder.Language.tcHost r) fun i => (w i).1

/-- An isomorphism of the two sides, over the base vocabulary. -/
abbrev TCSideEquiv (A : Type) [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).Structure A] : Type :=
  {x : A // TCPatMark (L₁ := L₁) x} ≃[L₁] {y : A // TCHostMark (L₁ := L₁) y}

end Sides

/-! ### Isomorphism-invariance -/

section Invariance

variable {L₁ : Language.{0, 0}} [L₁.IsRelational] {A B : Type}

variable [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).Structure A] [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁).Structure B]

/-- An isomorphism of the ambient structures restricts to the pattern sides. -/
def patSideMap (e : A ≃[Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁] B) (x : {x : A // TCPatMark (L₁ := L₁) x}) :
    {y : B // TCPatMark (L₁ := L₁) y} :=
  ⟨e x.1, by
    have h := relMap_equiv₁ e (Lax604544Proofs.Foreign.FirstOrder.Language.tcPatMark L₁) x.1
    exact h.mp x.2⟩

/-- An isomorphism of the ambient structures restricts to the host sides. -/
def hostSideMap (e : A ≃[Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁] B) (x : {x : A // TCHostMark (L₁ := L₁) x}) :
    {y : B // TCHostMark (L₁ := L₁) y} :=
  ⟨e x.1, by
    have h := relMap_equiv₁ e (Lax604544Proofs.Foreign.FirstOrder.Language.tcHostMark L₁) x.1
    exact h.mp x.2⟩

/-- The restriction of an ambient isomorphism to the pattern sides is itself an
isomorphism over the base vocabulary. -/
def patSideEquiv (e : A ≃[Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁] B) :
    {x : A // TCPatMark (L₁ := L₁) x} ≃[L₁] {y : B // TCPatMark (L₁ := L₁) y} where
  toFun := patSideMap e
  invFun := patSideMap e.symm
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_fun' f := isEmptyElim f
  map_rel' {n} r x := by
    have h := e.map_rel' (Lax604544Proofs.Foreign.FirstOrder.Language.tcPat r) fun i => (x i).1
    exact h

/-- The restriction of an ambient isomorphism to the host sides. -/
def hostSideEquiv (e : A ≃[Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁] B) :
    {x : A // TCHostMark (L₁ := L₁) x} ≃[L₁] {y : B // TCHostMark (L₁ := L₁) y} where
  toFun := hostSideMap e
  invFun := hostSideMap e.symm
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_fun' f := isEmptyElim f
  map_rel' {n} r x := by
    have h := e.map_rel' (Lax604544Proofs.Foreign.FirstOrder.Language.tcHost r) fun i => (x i).1
    exact h

/-- Isomorphic sides transport along an isomorphism of the ambient
structures. -/
theorem nonempty_tcSideEquiv_congr (e : A ≃[Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁] B) :
    Nonempty (TCSideEquiv (L₁ := L₁) A) ↔ Nonempty (TCSideEquiv (L₁ := L₁) B) :=
  ⟨fun ⟨i⟩ => ⟨((hostSideEquiv e).comp i).comp (patSideEquiv e).symm⟩,
    fun ⟨i⟩ => ⟨((hostSideEquiv e).symm.comp i).comp (patSideEquiv e)⟩⟩

end Invariance

/-- **The isomorphism problem of a vocabulary**: are the two marked
`L₁`-structures of the instance isomorphic? Every entry of the GI degree added
from here on is an instance of this shape. -/
def TwoCopiesIso (L₁ : Language.{0, 0}) [L₁.IsRelational] :
    Lax904597.Problems.DecisionProblem (Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies L₁) where
  Holds := fun A _inst => Finite A ∧ Nonempty (TCSideEquiv (L₁ := L₁) A)
  iso_invariant := fun e => and_congr e.toEquiv.finite_iff (nonempty_tcSideEquiv_congr e)

end Lax604544Proofs.DescriptiveComplexity


