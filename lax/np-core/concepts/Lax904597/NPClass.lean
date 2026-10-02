import Lax904597.Classes

/-!
---
title: NP is a complexity class
type: theorem
---
What makes the classes built from a membership predicate complexity classes
in the sense of the library this submission comes from, where closure under
reductions is part of the definition of a class: membership in NP travels
backward along first-order and ordered first-order reductions and depends
only on the finite instances of a problem, and cofinal hardness, for any
membership predicate, travels forward along first-order, ordered and
relativized ordered reductions and depends only on finite instances.

Finally, cofinal hardness is the usual notion: over a relational
vocabulary, `P` is cofinally hard for a collection exactly when every
problem of the collection reduces to `P`.
-/

namespace Lax904597.NPClass

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
  Lax904597.Classes

/-- Membership in NP travels backward along first-order reductions. -/
axiom NP_mem_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'}, FOReduction P Q → NP.Mem Q → NP.Mem P

/-- Membership in NP travels backward along ordered first-order reductions. -/
axiom NP_mem_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'}, OrderedFOReduction P Q → NP.Mem Q → NP.Mem P

/-- Membership in NP depends only on the finite instances of a problem. -/
axiom NP_mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L},
  (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (NP.Mem P ↔ NP.Mem Q)

/-- Cofinal hardness travels forward along first-order reductions. -/
axiom cofinalHard_of_foReduction :
  ∀ {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂},
    FOReduction P Q → CofinalHard Mem P → CofinalHard Mem Q

/-- Cofinal hardness travels forward along ordered first-order reductions. -/
axiom cofinalHard_of_orderedReduction :
  ∀ {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂},
    OrderedFOReduction P Q → CofinalHard Mem P → CofinalHard Mem Q

/-- Cofinal hardness travels forward along relativized ordered first-order
reductions. -/
axiom cofinalHard_of_relOrderedReduction :
  ∀ {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂},
    RelOrderedFOReduction P Q → CofinalHard Mem P → CofinalHard Mem Q

/-- Cofinal hardness depends only on the finite instances of a problem. -/
axiom cofinalHard_congr :
  ∀ {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ : Language.{0, 0}} [L₁.IsRelational] {P P' : DecisionProblem L₁},
    (∀ (A : Type) [L₁.Structure A] [Finite A], P A ↔ P' A) →
      CofinalHard Mem P → CofinalHard Mem P'

/-- Over a relational vocabulary, cofinal hardness is the usual notion: every
problem of the collection reduces to `P`. -/
axiom cofinalHard_iff : ∀ {L : Language.{0, 0}} [L.IsRelational]
  (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
  (P : DecisionProblem L),
  CofinalHard Mem P ↔
    ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
      Mem Q → Nonempty (RelOrderedFOReduction Q P)

end Lax904597.NPClass
