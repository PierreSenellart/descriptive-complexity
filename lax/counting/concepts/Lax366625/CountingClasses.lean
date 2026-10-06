import Lax904597.Problems
import Lax366625.CountingProblems

/-!
---
title: Counting classes
type: definition
---
A counting class is given by a membership predicate and a hardness predicate
on counting problems over arbitrary relational vocabularies. The classes of
this submission are built from their membership predicate: a problem $C$ is
parsimoniously hard for the class when every member of the class reduces to
$C$ by a relativized ordered parsimonious reduction, and parsimoniously
complete when it is moreover a member.
-/

namespace Lax366625.CountingClasses

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax366625.CountingProblems

/-- A counting class: a membership predicate and a hardness predicate on
counting problems, over arbitrary relational vocabularies. -/
structure CountingClass where
  /-- The counting problems belonging to the class. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], CountingProblem L → Prop
  /-- The counting problems every problem of the class reduces to. -/
  ParsimoniousHard : ∀ {L : Language.{0, 0}} [L.IsRelational], CountingProblem L → Prop

/-- The class with the given membership, a problem being hard when every member
reduces to it by a relativized ordered parsimonious reduction. -/
def CountingClass.ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], CountingProblem L₀ → Prop) :
    CountingClass where
  Mem C := Mem C
  ParsimoniousHard C := ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
    Mem D → Nonempty (RelOrderedParsimoniousReduction D C)

/-- A counting problem is parsimoniously complete for a class when it belongs
to it and is parsimoniously hard for it. -/
def CountingClass.ParsimoniousComplete (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : Prop :=
  K.Mem C ∧ K.ParsimoniousHard C

end Lax366625.CountingClasses
