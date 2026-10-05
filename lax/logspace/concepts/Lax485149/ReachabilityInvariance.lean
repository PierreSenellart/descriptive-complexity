import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.SecondOrderAtoms
import Lax485149.KromFragment
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.Reachability
import Lax485149.DeterministicReachability
import Lax485149.TwoSat
import Lax485149.ClassNL
import Lax485149.ClassL

/-!
---
title: Invariance and characterization of reachability
type: lemma
---
Reachability of a marked target from a marked source is invariant under
isomorphism of graphs, and a graph is a yes-instance of REACH exactly when
some marked target is reachable from some marked source.
-/

namespace Lax485149.ReachabilityInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- Reachability is isomorphism-invariant. -/
axiom reachable_iso : ∀ {A B : Type} [stGraph.Structure A] [stGraph.Structure B],
  (A ≃[stGraph] B) → (Reachable A ↔ Reachable B)

/-- The yes-instances of REACH are exactly the graphs where a marked target is
reachable from a marked source. -/
axiom reach_iff : ∀ (A : Type) [stGraph.Structure A], REACH A ↔ Reachable A

/-- The yes-instances of UNREACH are exactly the graphs where no marked target
is reachable from a marked source. -/
axiom unreach_iff : ∀ (A : Type) [stGraph.Structure A], UNREACH A ↔ ¬Reachable A

end Lax485149.ReachabilityInvariance
