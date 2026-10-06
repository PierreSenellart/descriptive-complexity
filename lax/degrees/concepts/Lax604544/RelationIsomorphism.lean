import Mathlib.Logic.Basic

/-!
---
title: Isomorphism of two marked relations
type: definition
---
Given two subsets $P_V$ and $H_V$ of a set and two binary relations $P_E$
and $H_E$ on it, the marked relations are isomorphic when some map restricts
to a bijection from $P_V$ onto $H_V$ such that, for $x, y \in P_V$,
$P_E(x, y)$ holds if and only if $H_E(f(x), f(y))$ does.
-/

namespace Lax604544.RelationIsomorphism

section Generic

variable {A : Type}

/-- Some map is a bijection of the `PV`-vertices onto the `HV`-vertices
carrying `PE`-edges to `HE`-edges *and back*: an isomorphism of the two marked
graphs. -/
def RelIsoOn (PV HV : A → Prop) (PE HE : A → A → Prop) : Prop :=
  ∃ f : A → A, (∀ x, PV x → HV (f x)) ∧
    (∀ x y, PV x → PV y → f x = f y → x = y) ∧
    (∀ y, HV y → ∃ x, PV x ∧ f x = y) ∧
    ∀ x y, PV x → PV y → (PE x y ↔ HE (f x) (f y))

end Generic

end Lax604544.RelationIsomorphism
