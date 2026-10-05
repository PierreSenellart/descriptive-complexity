import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.ClassNL
import Lax485149.ClassL
import Lax535992.HornFragment
import Lax535992.LeastFixedPoint
import Lax535992.InflationaryFixedPoint
import Lax535992.HornSat
import Lax535992.CircuitValue
import Lax535992.Game
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME

/-!
---
title: Invariance and characterization of GAME
type: lemma
---
Having a winning starting position is invariant under isomorphism of and-or
graphs, and an and-or graph is a yes-instance of GAME exactly when some
starting position is winning.
-/

namespace Lax535992.GameInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- Having a winning starting position is isomorphism-invariant. -/
axiom gameWon_iso : ∀ {A B : Type} [andOrGraph.Structure A] [andOrGraph.Structure B],
  (A ≃[andOrGraph] B) → (GameWon A ↔ GameWon B)

/-- The yes-instances of GAME are exactly the instances with the defining
property. -/
axiom game_iff : ∀ (A : Type) [andOrGraph.Structure A], GAME A ↔ GameWon A

end Lax535992.GameInvariance
