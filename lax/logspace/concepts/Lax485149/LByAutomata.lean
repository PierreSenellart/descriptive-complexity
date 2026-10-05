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
title: L is acceptance by deterministic two-way multihead automata
type: theorem
---
A decision problem $P$ over a relational vocabulary $L$ is in L if and only
if there are a number $k$ and a deterministic two-way $k$-head automaton
over $L$ that accepts, for every nonempty finite $L$-structure $A$ and every
linear order on $A$, exactly when $A$ is a yes-instance of $P$. The same
holds for FO(DTC) definability.
-/

namespace Lax485149.LByAutomata

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- L is acceptance by a deterministic two-way multihead automaton. -/
axiom mem_LOGSPACE_iff_automaton : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  LOGSPACE.Mem P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k), M.IsDeterministic ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A

/-- FO(DTC) definability is acceptance by a deterministic two-way multihead
automaton. -/
axiom dtcDefinable_iff_automaton : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  DTCDefinable P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k), M.IsDeterministic ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A

end Lax485149.LByAutomata
