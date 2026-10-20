import Lax904597.Problems
import Lax904597.Classes
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.ClassNL
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.AlternatingMachines
import Lax134656.ClassPSPACE
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax480241.AlternatingSpace
import Lax480241.ExponentialClasses

/-!
---
title: Alternating acceptance in bounded space, characterized
type: lemma
---
The conditions of acceptance by alternating machines in bounded space are
invariant under isomorphism, so the problem holds of an instance exactly
when the instance is well formed, its states are split in two, and it
accepts in bounded space.
-/

namespace Lax480241.AlternatingSpaceValue

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax485149.Complement Lax485149.ClassNL
open Lax535992.ClassPTIME Lax564036.Hierarchy Lax564036.AlternatingMachines Lax134656.ClassPSPACE
open Lax480241.Expansions Lax480241.SecondOrderFixedPoints Lax480241.AlternatingSpace
    Lax480241.ExponentialClasses

/-- Alternating acceptance in bounded space holds exactly when its conditions do. -/
axiom atmAcceptSpace_iff :
  ∀ (A : Type) [(turingAlt 2).Structure A],
    ATMAcceptSpace A ↔ TMData.WellFormed (atmData 2 A).toTMData ∧
      ATMData.BlocksSplit (atmData 2 A) ∧ ATMData.AltAcceptsSpace (atmData 2 A) true

end Lax480241.AlternatingSpaceValue
