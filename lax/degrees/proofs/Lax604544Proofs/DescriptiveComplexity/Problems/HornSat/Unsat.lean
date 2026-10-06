/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax604544Proofs.DescriptiveComplexity.Problems.HornSat.Defs
import Mathlib.Data.Set.Card
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

namespace Lax535992.HornSat
end Lax535992.HornSat

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Sat (Satisfiable)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax535992.HornSat (AtMostOnePositive HornSatisfiable)
end Lax604544Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# Horn *un*satisfiability has a short certificate

`HORNSATᶜ ∈ NP` (`DescriptiveComplexity.hornSat_compl_mem_NP`), equivalently
`HORNSAT ∈ coNP`: an unsatisfiable Horn formula admits a polynomial-size,
first-order checkable certificate of its unsatisfiability.

This is what makes level 0 of the hierarchy behave like the levels above it.
Complementing the Horn discharge turns it into the two *crossing* inclusions
`PTIME ⊆ coNP` and `co-PTIME ⊆ NP` (`DescriptiveComplexity.PTIME_subset_coNP`,
`DescriptiveComplexity.coPTIME_subset_NP`), which state closure properties of level 0
that the Horn fragment does not obviously have.

## The certificate

A Horn formula is unsatisfiable exactly when unit propagation derives the
premises of some clause that has no positive literal. The certificate guesses

* a set `T` of variables, meant to be (part of) the propagation closure, and
* a strict order `≺`, meant to record the order of derivation,

and checks, first-order, that

* `≺` is irreflexive and transitive – on a finite structure that already makes
  it well-founded, which is all the induction below needs;
* every `x ∈ T` is the positive literal of some clause all of whose negative
  literals lie in `T` and are strictly `≺`-earlier. This is what pins `T`
  *inside* the propagation closure: without the ordering condition one could
  take `T` to be everything;
* some clause has no positive literal and all its negative literals in `T`.

Soundness (`DescriptiveComplexity.subset_of_derivClosed`): in any model, `T` is
contained in the set of true variables – by well-founded induction along `≺`,
using the Horn condition, which is what makes the positive literal of a
satisfied clause *unique* and hence identifiable. The exhibited clause is then
falsified, so there is no model.

Completeness: the propagation closure itself (`DescriptiveComplexity.Forced`, defined by
its stages `DescriptiveComplexity.ForcedIn`) is a certificate, ordered by the stage at
which a variable enters it (`DescriptiveComplexity.dep`). If it were *not* one – if
every clause whose negative literals are all forced had a positive literal –
then `Forced` would itself be a model, so the formula would be satisfiable
(`DescriptiveComplexity.exists_goalClause`).
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

/-! ### Unit propagation and its least model -/

section LeastModel

variable {A : Type} [Lax904597.Sat.sat.Structure A]

/-- The stages of unit propagation: `ForcedIn n x` says that `x` is the
positive literal of a clause whose negative literals are all forced in fewer
than `n` rounds. -/
def ForcedIn : ℕ → A → Prop
  | 0, _ => False
  | n + 1, x => ∃ c : A, RelMap Lax904597.Sat.satIsClause ![c] ∧ RelMap Lax904597.Sat.satPosIn ![c, x] ∧
      ∀ y : A, RelMap Lax904597.Sat.satNegIn ![c, y] → ForcedIn n y

/-- A variable is *forced* when some stage forces it. On a Horn formula this
is the least model of the implications. -/
def Forced (x : A) : Prop := ∃ n, ForcedIn n x

theorem forcedIn_succ {n : ℕ} {x : A} (h : ForcedIn n x) : ForcedIn (n + 1) x := by
  induction n generalizing x with
  | zero => exact h.elim
  | succ n ih =>
    obtain ⟨c, hc, hp, hneg⟩ := h
    exact ⟨c, hc, hp, fun y hy => ih (hneg y hy)⟩

theorem forcedIn_le {m n : ℕ} (hmn : m ≤ n) {x : A} (h : ForcedIn m x) : ForcedIn n x := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact forcedIn_succ (ih (Nat.lt_succ_iff.mp hlt))
    · rwa [heq] at h

/-- The stage at which a variable becomes forced. -/
noncomputable def dep (x : A) : ℕ := sInf {n | ForcedIn n x}

theorem forcedIn_dep {x : A} (h : Forced x) : ForcedIn (dep x) x :=
  Nat.sInf_mem h

theorem dep_le {n : ℕ} {x : A} (h : ForcedIn n x) : dep x ≤ n :=
  Nat.sInf_le h

/-- Every forced variable is forced by a clause whose negative literals are
forced *strictly earlier*: the propagation closure is derivation-closed along
the stage order. -/
theorem derivClosed_forced (x : A) (hx : Forced x) :
    ∃ c : A, RelMap Lax904597.Sat.satIsClause ![c] ∧ RelMap Lax904597.Sat.satPosIn ![c, x] ∧
      ∀ y : A, RelMap Lax904597.Sat.satNegIn ![c, y] → Forced y ∧ dep y < dep x := by
  have h := forcedIn_dep hx
  cases hd : dep x with
  | zero =>
    rw [hd] at h
    exact h.elim
  | succ m =>
    rw [hd] at h
    obtain ⟨c, hc, hp, hneg⟩ := h
    refine ⟨c, hc, hp, fun y hy => ?_⟩
    have hy' := hneg y hy
    exact ⟨⟨m, hy'⟩, lt_of_le_of_lt (dep_le hy') (by omega)⟩

/-- On a finite structure the stages stabilize: one stage forces everything
that is forced at all. -/
theorem exists_forcedIn_bound [Finite A] :
    ∃ N : ℕ, ∀ x : A, Forced x → ForcedIn N x := by
  classical
  have := Fintype.ofFinite A
  refine ⟨Finset.univ.sup (dep (A := A)), fun x hx => ?_⟩
  exact forcedIn_le (Finset.le_sup (Finset.mem_univ x)) (forcedIn_dep hx)

/-- **Soundness of the certificate**: a derivation-closed set sits inside every
model. The Horn condition is what makes this work – it identifies the positive
literal by which a satisfied clause is satisfied. -/
theorem subset_of_derivClosed [Finite A] (hhorn : Lax535992.HornSat.AtMostOnePositive A)
    {R : A → A → Prop} (hirr : ∀ x, ¬R x x) (htr : ∀ x y z, R x y → R y z → R x z)
    {T : A → Prop}
    (hderiv : ∀ x : A, T x → ∃ c : A, RelMap Lax904597.Sat.satIsClause ![c] ∧ RelMap Lax904597.Sat.satPosIn ![c, x] ∧
      ∀ y : A, RelMap Lax904597.Sat.satNegIn ![c, y] → T y ∧ R y x)
    {ν : A → Prop}
    (hν : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] →
      ∃ x : A, (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ν x) ∨ (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ν x))
    (x : A) (hx : T x) : ν x := by
  have : IsTrans A R := ⟨htr⟩
  have : Std.Irrefl R := ⟨hirr⟩
  have hwf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  induction x using hwf.induction with
  | _ x ih =>
    obtain ⟨c, hc, hp, hneg⟩ := hderiv x hx
    obtain ⟨z, hz⟩ := hν c hc
    rcases hz with ⟨hpz, hνz⟩ | ⟨hnz, hνz⟩
    · rwa [hhorn c z x hc hpz hp] at hνz
    · exact absurd (ih z (hneg z hnz).2 (hneg z hnz).1) hνz

/-- The propagation closure sits inside every model: the instance of
`DescriptiveComplexity.subset_of_derivClosed` at the closure itself, ordered by its
stages. -/
theorem forced_subset_model [Finite A] (hhorn : Lax535992.HornSat.AtMostOnePositive A) {ν : A → Prop}
    (hν : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] →
      ∃ x : A, (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ν x) ∨ (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ν x))
    (x : A) (hx : Forced x) : ν x :=
  subset_of_derivClosed (R := fun a b : A => dep a < dep b) (T := Forced) hhorn
    (fun a => lt_irrefl (dep a)) (fun _ _ _ hab hbc => lt_trans hab hbc)
    derivClosed_forced hν x hx

/-- A clause whose negative literals are all forced forces its positive
literal. -/
theorem forced_of_allNeg [Finite A] {c x : A} (hc : RelMap Lax904597.Sat.satIsClause ![c])
    (hp : RelMap Lax904597.Sat.satPosIn ![c, x]) (hall : ∀ y : A, RelMap Lax904597.Sat.satNegIn ![c, y] → Forced y) :
    Forced x := by
  obtain ⟨N, hN⟩ := exists_forcedIn_bound (A := A)
  exact ⟨N + 1, c, hc, hp, fun y hy => hN y (hall y hy)⟩

end LeastModel

/-! ### The `Σ₁` definition -/

section SigmaOne

/-! #### Realization of the kernel -/

section Realize

end Realize

/-! ### Horn unsatisfiability is in NP -/

end SigmaOne

end Lax604544Proofs.DescriptiveComplexity


