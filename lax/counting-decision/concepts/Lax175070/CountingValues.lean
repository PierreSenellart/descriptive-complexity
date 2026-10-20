import Lax904597.Problems
import Lax485149.Problems
import Lax485149.Complement
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Interpretations
import Lax904597.Machines
import Lax564036.Hierarchy
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax366625.CountingRuns
import Lax175070.CountDefinability
import Lax175070.SelectedSat

/-!
---
title: Values of the decision versions and of #SelSAT
type: lemma
---
The decision version of a counting problem by a property of numbers holds on
a structure exactly when its count has the property. The number of models of
an instance with a selected variable in which the selected variables have a
given value is invariant under isomorphism, so it is the value of
#SelSAT$_b$; SelMajSAT and SelEqSAT hold exactly when these counts compare
as they ask.
-/

namespace Lax175070.CountingValues

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Sat Lax904597.Interpretations
    Lax904597.Machines Lax564036.Hierarchy
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax366625.CountingRuns Lax175070.CountDefinability Lax175070.SelectedSat Lax485149.Problems
open Lax485149.Complement

/-- The decision version holds when the count has the property. -/
axiom decide_iff :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (R : ℕ → Prop) (C : CountingProblem L)
    (A : Type) [L.Structure A], decide R C A ↔ R (C A)

/-- The number of models with the selected variables at `b` is isomorphism-invariant. -/
axiom sharpSelSat_count_iso :
  ∀ (b : Bool) {A B : Type} [satSel.Structure A] [satSel.Structure B],
    (A ≃[satSel] B) → Nat.card {ν : A → Prop // SelModel A b ν} = Nat.card {ν : B → Prop //
        SelModel B b ν}

/-- The value of #SelSAT is the number it counts. -/
axiom sharpSelSat_eq :
  ∀ (b : Bool) (A : Type) [satSel.Structure A],
    SharpSelSAT b A = Nat.card {ν : A → Prop // SelModel A b ν}

/-- SelMajSAT compares the two counts. -/
axiom selMajSat_iff :
  ∀ (A : Type) [satSel.Structure A], SelMajSAT A ↔ SharpSelSAT false A < SharpSelSAT true A

/-- SelEqSAT compares the two counts. -/
axiom selEqSat_iff :
  ∀ (A : Type) [satSel.Structure A], SelEqSAT A ↔ SharpSelSAT true A = SharpSelSAT false A

end Lax175070.CountingValues
