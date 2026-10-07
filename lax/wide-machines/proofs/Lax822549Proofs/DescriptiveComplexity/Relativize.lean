/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.SecondOrderNew
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Relativization of a formula to a unary predicate

Restricting every quantifier of a first-order formula to the elements
satisfying a unary relation symbol (`DescriptiveComplexity.relativizeTo`), so
that the formula, read in a structure `M`, says exactly what it says in the
part of `M` that the symbol marks
(`DescriptiveComplexity.realize_relativizeTo`).

The statement takes the marked part as a `FirstOrder.Language.Substructure`
whose carrier the symbol defines (for the relational vocabularies of this
library there is nothing to be closed under, so any marked part qualifies).
Marking by a *symbol* rather than by an arbitrary formula is what the users
below need, and keeps the guard a one-line atom.

## Where this is used

Value invention (`DescriptiveComplexity.SecondOrderNew`) puts the instance `A`
and `m` invented values in one universe `A ⊕ Fin m`. A formula about `A` – in
particular a defining formula of an interpretation being pulled back – must
then be read with its quantifiers restricted to the original elements, which
is exactly relativization to the predicate `old`. The specialization
`DescriptiveComplexity.relOld` and its correctness
`DescriptiveComplexity.realize_relOld` package that instance: the old part of
`A ⊕ Fin m` is a substructure isomorphic to `A`
(`DescriptiveComplexity.oldSubEquiv`).

The same machinery is what a relativized *membership* pullback – one through
an interpretation whose domain is cut out by a formula – would want.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Relativization to a unary relation symbol -/

section Relativize

variable {L : Language.{0, 0}} {α : Type}

/-- The guard “the last bound variable satisfies `R`”. -/
def lastGuard (R : L.Relations 1) (n : ℕ) : L.BoundedFormula α (n + 1) :=
  R.boundedFormula₁ (Term.var (Sum.inr (Fin.last n)))

/-- **Relativization**: the formula obtained by restricting every quantifier
to the elements satisfying the unary relation symbol `R`. Atoms are left
untouched, so this is a purely syntactic guard insertion. -/
def relativizeTo (R : L.Relations 1) :
    ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel r ts => .rel r ts
  | _, .imp φ ψ => .imp (relativizeTo R φ) (relativizeTo R ψ)
  | n, .all φ => .all ((lastGuard R n).imp (relativizeTo R φ))

variable {M : Type} [L.Structure M] {R : L.Relations 1}

theorem realize_lastGuard {n : ℕ} (v : α → M) (xs : Fin (n + 1) → M) :
    (lastGuard R n).Realize v xs ↔ RelMap R ![xs (Fin.last n)] := by
  rw [lastGuard, BoundedFormula.realize_rel₁]
  rfl

/-- **Relativization is correct**: the relativized formula, read in `M` at
arguments taken from the substructure the symbol `R` defines, says what the
original formula says in that substructure. -/
theorem realize_relativizeTo (S : L.Substructure M) (hS : ∀ x : M, x ∈ S ↔ RelMap R ![x]) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → S) (xs : Fin n → S),
      (relativizeTo R φ).Realize (fun a => ((v a : M))) (fun i => ((xs i : M))) ↔
        φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    have hcomp : Sum.elim (fun a => ((v a : M))) (fun i => ((xs i : M))) =
        (S.subtype : S → M) ∘ Sum.elim v xs :=
      (Sum.comp_elim (S.subtype : S → M) v xs).symm
    change (Term.realize _ t₁ = Term.realize _ t₂) ↔ _
    rw [hcomp, HomClass.realize_term, HomClass.realize_term]
    exact ⟨fun h => S.subtype.injective h, fun h => congrArg _ h⟩
  | rel r ts =>
    intro v xs
    have hcomp : Sum.elim (fun a => ((v a : M))) (fun i => ((xs i : M))) =
        (S.subtype : S → M) ∘ Sum.elim v xs :=
      (Sum.comp_elim (S.subtype : S → M) v xs).symm
    change RelMap r (fun i => Term.realize _ (ts i)) ↔ _
    rw [hcomp]
    simp only [HomClass.realize_term]
    exact S.subtype.map_rel' r _
  | imp φ ψ ihφ ihψ =>
    intro v xs
    change ((relativizeTo R φ).Realize _ _ → (relativizeTo R ψ).Realize _ _) ↔ _
    rw [ihφ v xs, ihψ v xs]
    exact Iff.rfl
  | all φ ih =>
    intro v xs
    rw [relativizeTo]
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp]
    constructor
    · intro h b
      have hguard : RelMap R ![((b : M))] := (hS _).mp b.2
      have hb := h (b : M) ((realize_lastGuard _ _).mpr (by simpa using hguard))
      rw [show Fin.snoc (fun i => ((xs i : M))) ((b : M)) =
          fun i => (((Fin.snoc xs b : Fin _ → S) i : M)) by
        funext i
        exact congrFun (Fin.comp_snoc (S.subtype : S → M) xs b).symm i] at hb
      exact (ih v (Fin.snoc xs b)).mp hb
    · intro h a hguard
      have ha : a ∈ S := (hS a).mpr (by simpa using (realize_lastGuard _ _).mp hguard)
      have hb := (ih v (Fin.snoc xs ⟨a, ha⟩)).mpr (h ⟨a, ha⟩)
      rw [show (fun i => (((Fin.snoc xs (⟨a, ha⟩ : S) : Fin _ → S) i : M))) =
          Fin.snoc (fun i => ((xs i : M))) a by
        funext i
        exact congrFun (Fin.comp_snoc (S.subtype : S → M) xs ⟨a, ha⟩) i] at hb
      exact hb

end Relativize

/-! ### Relativization to the original elements of an extended universe -/

section Old

end Old

end Lax822549Proofs.DescriptiveComplexity


