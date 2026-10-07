/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Qsat.Membership
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.Qsat
end Lax134656.Qsat

namespace FirstOrder.Language
export Lax134656.Qsat (qsat)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.Qsat (IsQAll IsQVar QLeast QPrec QsatWf QsatWins qAdd qUpd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Playing a whole quantifier block at once

`DescriptiveComplexity.QsatWins` plays *one variable at a time*, in the order the
instance prescribes: that is what makes it the honest reading of a quantifier
prefix, and what the membership walk of `DescriptiveComplexity.Problems.Qsat.Membership`
follows step by step. Every *hardness* proof needs the opposite reading, the
one the textbooks write: the prefix is a sequence of **blocks** of like
polarity, and a block is a single quantifier over an assignment of the whole
block.

This file proves the two peeling lemmas that turn one reading into the other,
`DescriptiveComplexity.qsatWins_block_ex` and `DescriptiveComplexity.qsatWins_block_all`: if `B`
is a set of unplayed variables of the same polarity that comes first among the
unplayed ones (`DescriptiveComplexity.QBlock`), then winning the position `(D, τ)` is
winning `(D ∪ B, τ)` for some (resp. every) assignment of `B`. Iterating them
along the blocks of a constructed instance is how a reduction into QSAT states
its correctness.

Both go by induction on the size of `B`: the next variable to play lies in `B`
as soon as `B` is nonempty, and the induction hypothesis applies to `B` minus
that variable. The bookkeeping is done with `Prop`-valued updates
(`DescriptiveComplexity.qSet`) rather than the `Bool`-valued ones of the game rules, so
that a block assignment `ν : A → Prop` never has to be converted; the two are
related by `DescriptiveComplexity.qsatWins_ex_iff'` and
`DescriptiveComplexity.qsatWins_all_iff'`.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Blocks

variable {A : Type} [Lax134656.Qsat.qsat.Structure A]

/-! ### Propositional updates -/

/-- Giving the variable `x` the value `P`, a proposition rather than a Boolean:
the shape a block assignment produces. -/
def qSet (τ : A → Prop) (x : A) (P : Prop) : A → Prop :=
  fun y => (y = x ∧ P) ∨ (y ≠ x ∧ τ y)

omit [Lax134656.Qsat.qsat.Structure A] in
@[simp]
theorem qSet_self (τ : A → Prop) (x : A) (P : Prop) : qSet τ x P x ↔ P := by
  refine ⟨fun h => ?_, fun h => Or.inl ⟨rfl, h⟩⟩
  rcases h with ⟨-, hP⟩ | ⟨hne, -⟩
  · exact hP
  · exact absurd rfl hne

omit [Lax134656.Qsat.qsat.Structure A] in
theorem qSet_ne (τ : A → Prop) {x y : A} (P : Prop) (h : y ≠ x) : qSet τ x P y ↔ τ y := by
  refine ⟨fun hy => ?_, fun hy => Or.inr ⟨h, hy⟩⟩
  rcases hy with ⟨he, -⟩ | ⟨-, hy⟩
  · exact absurd he h
  · exact hy

omit [Lax134656.Qsat.qsat.Structure A] in
/-- A Boolean update is a propositional one. -/
theorem qUpd_eq_qSet (τ : A → Prop) (x : A) (b : Bool) : Lax134656.Qsat.qUpd τ x b = qSet τ x (b = true) := rfl

omit [Lax134656.Qsat.qsat.Structure A] in
theorem qSet_congr (τ : A → Prop) (x : A) {P Q : Prop} (h : P ↔ Q) :
    qSet τ x P = qSet τ x Q := by
  funext y
  exact propext (or_congr (and_congr_right fun _ => h) Iff.rfl)

omit [Lax134656.Qsat.qsat.Structure A] in
theorem qSet_self_eq (τ : A → Prop) (x : A) : qSet τ x (τ x) = τ := by
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨he, hP⟩ | ⟨-, hy⟩
    · exact he ▸ hP
    · exact hy
  · by_cases hyx : y = x
    · exact Or.inl ⟨hyx, hyx ▸ h⟩
    · exact Or.inr ⟨hyx, h⟩

open Classical in
/-- A proposition as a Boolean. -/
private noncomputable def boolOf (P : Prop) : Bool := if P then true else false

private theorem boolOf_iff (P : Prop) : (boolOf P = true) ↔ P := by
  classical
  by_cases h : P
  · simp [boolOf, h]
  · simp [boolOf, h]

/-! ### The one-variable rules, propositionally -/

variable [Finite A]

omit [Finite A] in
/-- The existential rule, with the played value a proposition. -/
theorem qsatWins_ex_iff' (hwf : Lax134656.Qsat.QsatWf A) {D τ : A → Prop} {x : A} (hx : Lax134656.Qsat.QLeast D x)
    (hq : ¬Lax134656.Qsat.IsQAll x) :
    Lax134656.Qsat.QsatWins D τ ↔ ∃ P : Prop, Lax134656.Qsat.QsatWins (Lax134656.Qsat.qAdd D x) (qSet τ x P) := by
  rw [qsatWins_ex_iff hwf hx hq]
  refine ⟨fun ⟨b, hb⟩ => ⟨b = true, hb⟩, fun ⟨P, hP⟩ => ⟨boolOf P, ?_⟩⟩
  rwa [qUpd_eq_qSet, qSet_congr τ x (boolOf_iff P)]

omit [Finite A] in
/-- The universal rule, with the played value a proposition. -/
theorem qsatWins_all_iff' (hwf : Lax134656.Qsat.QsatWf A) {D τ : A → Prop} {x : A} (hx : Lax134656.Qsat.QLeast D x)
    (hq : Lax134656.Qsat.IsQAll x) :
    Lax134656.Qsat.QsatWins D τ ↔ ∀ P : Prop, Lax134656.Qsat.QsatWins (Lax134656.Qsat.qAdd D x) (qSet τ x P) := by
  rw [qsatWins_all_iff hwf hx hq]
  refine ⟨fun h P => ?_, fun h b => h (b = true)⟩
  have := h (boolOf P)
  rwa [qUpd_eq_qSet, qSet_congr τ x (boolOf_iff P)] at this

/-! ### Blocks -/

/-- The union of the played variables and a block. -/
def qUnion (D B : A → Prop) : A → Prop := fun y => D y ∨ B y

/-- The valuation that reads `ν` on the block `B` and `τ` outside it. -/
def qOver (B τ ν : A → Prop) : A → Prop := fun y => (B y ∧ ν y) ∨ (¬B y ∧ τ y)

/-- `B` is the **next block** of the position `(D, ·)`: a set of unplayed
variables that comes first among the unplayed ones. Together with a uniform
polarity this is what lets the whole of `B` be played by one quantifier. -/
structure QBlock (D B : A → Prop) : Prop where
  /-- A block holds variables. -/
  isVar : ∀ x : A, B x → Lax134656.Qsat.IsQVar x
  /-- A block holds unplayed variables. -/
  unplayed : ∀ x : A, B x → ¬D x
  /-- A block comes first among the unplayed variables. -/
  first : ∀ x y : A, B x → Lax134656.Qsat.IsQVar y → ¬D y → ¬B y → Lax134656.Qsat.QPrec x y

omit [Finite A] in
/-- The next variable to play lies in the block, as soon as the block is
nonempty. -/
theorem QBlock.mem_of_qLeast {D B : A → Prop} (hB : QBlock D B) {x z : A} (hx : Lax134656.Qsat.QLeast D x)
    (hz : B z) : B x := by
  by_contra hBx
  exact hx.2.2 z (hB.isVar z hz) (hB.unplayed z hz) (hB.first z x hz hx.1 hx.2.1 hBx)

omit [Finite A] [Lax134656.Qsat.qsat.Structure A] in
private theorem qOver_qSet {B : A → Prop} {x : A} (hBx : B x) (τ ν : A → Prop) (P : Prop) :
    qOver (qRem B x) (qSet τ x P) ν = qOver B τ (qSet ν x P) := by
  classical
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hyx : y = x
    · subst hyx
      refine Or.inl ⟨hBx, (qSet_self ν y P).mpr ?_⟩
      rcases h with ⟨⟨hne, -⟩, -⟩ | ⟨-, hs⟩
      · exact absurd rfl hne
      · exact (qSet_self τ y P).mp hs
    · rcases h with ⟨⟨-, hBy⟩, hν⟩ | ⟨hnB, hs⟩
      · exact Or.inl ⟨hBy, (qSet_ne ν P hyx).mpr hν⟩
      · refine Or.inr ⟨fun hBy => hnB ⟨hyx, hBy⟩, ?_⟩
        exact (qSet_ne τ P hyx).mp hs
  · by_cases hyx : y = x
    · subst hyx
      refine Or.inr ⟨fun hr => hr.1 rfl, (qSet_self τ y P).mpr ?_⟩
      rcases h with ⟨-, hν⟩ | ⟨hnB, -⟩
      · exact (qSet_self ν y P).mp hν
      · exact absurd hBx hnB
    · rcases h with ⟨hBy, hν⟩ | ⟨hnB, hτ⟩
      · exact Or.inl ⟨⟨hyx, hBy⟩, (qSet_ne ν P hyx).mp hν⟩
      · exact Or.inr ⟨fun hr => hnB hr.2, (qSet_ne τ P hyx).mpr hτ⟩

omit [Finite A] [Lax134656.Qsat.qsat.Structure A] in
private theorem qUnion_qAdd_qRem {D B : A → Prop} {x : A} (hBx : B x) :
    qUnion (Lax134656.Qsat.qAdd D x) (qRem B x) = qUnion D B := by
  classical
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with hyx | hr
    · rcases hyx with hyx | hD
      · exact Or.inr (hyx ▸ hBx)
      · exact Or.inl hD
    · exact Or.inr hr.2
  · by_cases hyx : y = x
    · exact Or.inl (Or.inl hyx)
    · rcases h with hD | hB
      · exact Or.inl (Or.inr hD)
      · exact Or.inr ⟨hyx, hB⟩

omit [Finite A] in
private theorem qBlock_qRem {D B : A → Prop} {x : A} (hB : QBlock D B) :
    QBlock (Lax134656.Qsat.qAdd D x) (qRem B x) where
  isVar y hy := hB.isVar y hy.2
  unplayed y hy hd := by
    rcases hd with he | hd
    · exact hy.1 he
    · exact hB.unplayed y hy.2 hd
  first y w hy hw hdw hrw := by
    have hwx : w ≠ x := fun h => hdw (Or.inl h)
    exact hB.first y w hy.2 hw (fun hd => hdw (Or.inr hd)) fun hBw => hrw ⟨hwx, hBw⟩

omit [Finite A] [Lax134656.Qsat.qsat.Structure A] in
private theorem qOver_of_empty {B τ ν : A → Prop} (hB : ∀ y : A, ¬B y) :
    qOver B τ ν = τ := by
  funext y
  exact propext ⟨fun h => h.resolve_left (fun hh => hB y hh.1) |>.2, fun h => Or.inr ⟨hB y, h⟩⟩

omit [Finite A] [Lax134656.Qsat.qsat.Structure A] in
private theorem qUnion_of_empty {D B : A → Prop} (hB : ∀ y : A, ¬B y) : qUnion D B = D := by
  funext y
  exact propext ⟨fun h => h.resolve_right (hB y), Or.inl⟩

/-- **Playing a block, in one induction for both polarities.** -/
private theorem qsatWins_block_aux (hwf : Lax134656.Qsat.QsatWf A) :
    ∀ (n : ℕ) (D B τ : A → Prop), QDownClosed D → QBlock D B →
      Set.ncard {y : A | B y} ≤ n →
      ((∀ x : A, B x → ¬Lax134656.Qsat.IsQAll x) →
          (Lax134656.Qsat.QsatWins D τ ↔ ∃ ν : A → Prop, Lax134656.Qsat.QsatWins (qUnion D B) (qOver B τ ν))) ∧
        ((∀ x : A, B x → Lax134656.Qsat.IsQAll x) →
          (Lax134656.Qsat.QsatWins D τ ↔ ∀ ν : A → Prop, Lax134656.Qsat.QsatWins (qUnion D B) (qOver B τ ν))) := by
  classical
  intro n
  induction n with
  | zero =>
    intro D B τ _ _ hcard
    have hempty : ∀ y : A, ¬B y := by
      intro y hy
      have h0 : ({y : A | B y}) = ∅ :=
        (Set.ncard_eq_zero (Set.toFinite _)).mp (Nat.le_zero.mp hcard)
      exact (Set.Nonempty.ne_empty ⟨y, hy⟩) h0
    rw [qUnion_of_empty hempty]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact ⟨fun h => ⟨fun _ => False, by rwa [qOver_of_empty hempty]⟩,
        fun ⟨ν, hν⟩ => by rwa [qOver_of_empty hempty] at hν⟩
    · exact ⟨fun h ν => by rwa [qOver_of_empty hempty],
        fun h => by have := h fun _ => False; rwa [qOver_of_empty hempty] at this⟩
  | succ n ih =>
    intro D B τ hdc hB hcard
    by_cases hempty : ∀ y : A, ¬B y
    · rw [qUnion_of_empty hempty]
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      · exact ⟨fun h => ⟨fun _ => False, by rwa [qOver_of_empty hempty]⟩,
          fun ⟨ν, hν⟩ => by rwa [qOver_of_empty hempty] at hν⟩
      · exact ⟨fun h ν => by rwa [qOver_of_empty hempty],
          fun h => by have := h fun _ => False; rwa [qOver_of_empty hempty] at this⟩
    obtain ⟨z, hz⟩ : ∃ z : A, B z := by
      obtain ⟨z, hz⟩ := not_forall.mp hempty
      exact ⟨z, not_not.mp hz⟩
    obtain ⟨x, hx⟩ := exists_qLeast hwf ⟨z, hB.isVar z hz, hB.unplayed z hz⟩
    have hBx : B x := hB.mem_of_qLeast hx hz
    have hcard' : Set.ncard {y : A | qRem B x y} ≤ n := by
      have hlt : {y : A | qRem B x y} ⊂ {y : A | B y} :=
        ⟨fun y hy => hy.2, fun hsup => (hsup hBx).1 rfl⟩
      exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (Set.ncard_lt_ncard hlt (Set.toFinite _)) hcard)
    have hdc' : QDownClosed (Lax134656.Qsat.qAdd D x) := hx.qDownClosed_qAdd hdc
    have hB' : QBlock (Lax134656.Qsat.qAdd D x) (qRem B x) := qBlock_qRem hB
    have hstep : ∀ P : Prop,
        (((∀ y : A, qRem B x y → ¬Lax134656.Qsat.IsQAll y) →
            (Lax134656.Qsat.QsatWins (Lax134656.Qsat.qAdd D x) (qSet τ x P) ↔
              ∃ ν : A → Prop, Lax134656.Qsat.QsatWins (qUnion D B) (qOver B τ (qSet ν x P)))) ∧
          ((∀ y : A, qRem B x y → Lax134656.Qsat.IsQAll y) →
            (Lax134656.Qsat.QsatWins (Lax134656.Qsat.qAdd D x) (qSet τ x P) ↔
              ∀ ν : A → Prop, Lax134656.Qsat.QsatWins (qUnion D B) (qOver B τ (qSet ν x P))))) := by
      intro P
      obtain ⟨he, ha⟩ := ih (Lax134656.Qsat.qAdd D x) (qRem B x) (qSet τ x P) hdc' hB' hcard'
      constructor
      · intro hpol
        rw [he hpol, qUnion_qAdd_qRem hBx]
        exact exists_congr fun ν => iff_of_eq (congrArg _ (qOver_qSet hBx τ ν P))
      · intro hpol
        rw [ha hpol, qUnion_qAdd_qRem hBx]
        exact forall_congr' fun ν => iff_of_eq (congrArg _ (qOver_qSet hBx τ ν P))
    refine ⟨fun hpol => ?_, fun hpol => ?_⟩
    · rw [qsatWins_ex_iff' hwf hx (hpol x hBx)]
      constructor
      · rintro ⟨P, hP⟩
        obtain ⟨ν, hν⟩ := ((hstep P).1 fun y hy => hpol y hy.2).mp hP
        exact ⟨qSet ν x P, hν⟩
      · rintro ⟨ν, hν⟩
        refine ⟨ν x, ((hstep (ν x)).1 fun y hy => hpol y hy.2).mpr ⟨ν, ?_⟩⟩
        rwa [qSet_self_eq]
    · rw [qsatWins_all_iff' hwf hx (hpol x hBx)]
      constructor
      · intro h ν
        have := ((hstep (ν x)).2 fun y hy => hpol y hy.2).mp (h (ν x)) ν
        rwa [qSet_self_eq] at this
      · intro h P
        refine ((hstep P).2 fun y hy => hpol y hy.2).mpr fun ν => ?_
        exact h (qSet ν x P)

/-- **An existential block is played by one quantifier**: if `B` is the next
block of the position `(D, τ)` and all its variables are existential, winning
`(D, τ)` is winning `(D ∪ B, τ)` under *some* assignment of `B`. -/
theorem qsatWins_block_ex (hwf : Lax134656.Qsat.QsatWf A) {D B τ : A → Prop} (hdc : QDownClosed D)
    (hB : QBlock D B) (hpol : ∀ x : A, B x → ¬Lax134656.Qsat.IsQAll x) :
    Lax134656.Qsat.QsatWins D τ ↔ ∃ ν : A → Prop, Lax134656.Qsat.QsatWins (qUnion D B) (qOver B τ ν) :=
  (qsatWins_block_aux hwf _ D B τ hdc hB le_rfl).1 hpol

/-- **A universal block is played by one quantifier**: dually, under *every*
assignment of `B`. -/
theorem qsatWins_block_all (hwf : Lax134656.Qsat.QsatWf A) {D B τ : A → Prop} (hdc : QDownClosed D)
    (hB : QBlock D B) (hpol : ∀ x : A, B x → Lax134656.Qsat.IsQAll x) :
    Lax134656.Qsat.QsatWins D τ ↔ ∀ ν : A → Prop, Lax134656.Qsat.QsatWins (qUnion D B) (qOver B τ ν) :=
  (qsatWins_block_aux hwf _ D B τ hdc hB le_rfl).2 hpol

end Blocks

end Lax822549Proofs.DescriptiveComplexity


