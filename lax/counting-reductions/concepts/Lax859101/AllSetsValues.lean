import Lax904597.Problems
import Lax904597.Sat
import Mathlib.ModelTheory.Graph
import Lax799700.SetFamily
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite

/-!
---
title: The values of #3-Colorability, counting all independent sets, and counting all vertex covers
type: lemma
---
The number counted by each of #3-Colorability, counting all independent
sets, and counting all vertex covers is invariant under isomorphism of
instances, so the value of each problem on an instance is the number it
counts.
-/

namespace Lax859101.AllSetsValues

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- The number counted by #3-Colorability is isomorphism-invariant. -/
axiom sharpThreeCol_count_iso :
  ∀ {A B : Type} [FirstOrder.Language.graph.Structure A] [FirstOrder.Language.graph.Structure B],
    (A ≃[FirstOrder.Language.graph] B) → Nat.card
        {χ : A → Fin 3 // ∀ x y : A, RelMap Language.adj ![x, y] → χ x ≠ χ y} = Nat.card
            {χ : B → Fin 3 // ∀ x y : B, RelMap Language.adj ![x, y] → χ x ≠ χ y}

/-- The value of #3-Colorability is the number it counts. -/
axiom sharpThreeCol_eq :
  ∀ (A : Type) [FirstOrder.Language.graph.Structure A], SharpThreeCol A = Nat.card
      {χ : A → Fin 3 // ∀ x y : A, RelMap Language.adj ![x, y] → χ x ≠ χ y}

/-- The number counted by counting all independent sets is isomorphism-invariant. -/
axiom sharpAllIndependentSets_count_iso :
  ∀ {A B : Type} [FirstOrder.Language.graph.Structure A] [FirstOrder.Language.graph.Structure B],
    (A ≃[FirstOrder.Language.graph] B) → Nat.card {S : A → Prop // IndepSet (fun x y : A =>
        RelMap Language.adj ![x, y]) S} = Nat.card {S : B → Prop // IndepSet (fun x y : B =>
            RelMap Language.adj ![x, y]) S}

/-- The value of counting all independent sets is the number it counts. -/
axiom sharpAllIndependentSets_eq :
  ∀ (A : Type) [FirstOrder.Language.graph.Structure A], SharpAllIndependentSets A = Nat.card
      {S : A → Prop // IndepSet (fun x y : A => RelMap Language.adj ![x, y]) S}

/-- The number counted by counting all vertex covers is isomorphism-invariant. -/
axiom sharpAllVertexCovers_count_iso :
  ∀ {A B : Type} [FirstOrder.Language.graph.Structure A] [FirstOrder.Language.graph.Structure B],
    (A ≃[FirstOrder.Language.graph] B) → Nat.card {C : A → Prop // GVertexCover A C} = Nat.card
        {C : B → Prop // GVertexCover B C}

/-- The value of counting all vertex covers is the number it counts. -/
axiom sharpAllVertexCovers_eq :
  ∀ (A : Type) [FirstOrder.Language.graph.Structure A], SharpAllVertexCovers A = Nat.card
      {C : A → Prop // GVertexCover A C}

end Lax859101.AllSetsValues
