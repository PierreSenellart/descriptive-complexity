import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.ModelTheory.Graph
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Hom.Set
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise

/-!
---
title: The queries h₀ and ∃x y, R(x) ∧ S(x, y)
type: definition
---
The schema has a unary relation $R$, a binary relation $S$, and a unary
relation $T$. The query $h_0 = \exists x\, y,\ R(x) \wedge S(x, y) \wedge
T(y)$ is the smallest query whose probability is hard to compute, after
Dalvi and Suciu; the query $\exists x\, y,\ R(x) \wedge S(x, y)$ is
hierarchical, on the easy side of their dichotomy.
-/

namespace Lax794877.Queries

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive rstRel : ℕ → Type where
/-- `r a`. -/
  | r : rstRel 1
/-- `s a b`. -/
  | s : rstRel 2
/-- `t b`. -/
  | t : rstRel 1
  deriving DecidableEq

/-- The schema of the example: two unary relations and a binary one. -/
def rst : FirstOrder.Language :=
  ⟨fun _ => Empty, rstRel⟩

instance instIsRelationalRst : FirstOrder.Language.IsRelational rst := fun _ =>
    (inferInstance : IsEmpty Empty)

/-- `r a`. -/
abbrev rstR : rst.Relations 1 :=
  .r

/-- `s a b`. -/
abbrev rstS : rst.Relations 2 :=
  .s

/-- `t b`. -/
abbrev rstT : rst.Relations 1 :=
  .t

open FirstOrder

open Language Structure

instance instFiniteSigmaNatRelationsRst : Finite (Σ n, rst.Relations n) :=
  Finite.of_surjective
    (fun i : Fin 3 => match i with
      | 0 => (⟨1, rstR⟩ : Σ n, rst.Relations n)
      | 1 => ⟨2, rstS⟩
      | 2 => ⟨1, rstT⟩)
    (by
      rintro ⟨n, R⟩
      cases R
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)

/-- The query `h₀ = ∃ x y, R(x) ∧ S(x, y) ∧ T(y)`. -/
noncomputable def h0 : rst.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 2)
  (FirstOrder.Language.Relations.formula₁ rstR (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
    (FirstOrder.Language.Relations.formula₂ rstS (FirstOrder.Language.Term.var (Sum.inr 0))
        (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
      FirstOrder.Language.Relations.formula₁ rstT (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- The query `∃ x y, R(x) ∧ S(x, y)`. -/
noncomputable def rs : rst.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 2)
  (FirstOrder.Language.Relations.formula₁ rstR (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
    FirstOrder.Language.Relations.formula₂ rstS (FirstOrder.Language.Term.var (Sum.inr 0))
      (FirstOrder.Language.Term.var (Sum.inr 1)))

end Lax794877.Queries
