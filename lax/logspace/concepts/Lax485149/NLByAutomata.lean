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
title: NL is acceptance by two-way multihead automata
type: theorem
---
A decision problem $P$ over a relational vocabulary $L$ is in NL if and only
if there are a number $k$ and a two-way $k$-head automaton over $L$ that
accepts, for every nonempty finite $L$-structure $A$ and every linear order
on $A$, exactly when $A$ is a yes-instance of $P$. The same holds for FO(TC)
definability, a configuration of the automaton being a node of a
transitive-closure specification and conversely. This relates the logically
defined class to a machine model with logarithmic storage: $k$ heads on a
structure of size $n$ hold $k \log n$ bits.
-/

namespace Lax485149.NLByAutomata

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- NL is acceptance by a two-way multihead automaton. -/
axiom mem_NL_iff_automaton : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  NL.Mem P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A

/-- FO(TC) definability is acceptance by a two-way multihead automaton. -/
axiom tcDefinable_iff_automaton : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  TCDefinable P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A

end Lax485149.NLByAutomata
