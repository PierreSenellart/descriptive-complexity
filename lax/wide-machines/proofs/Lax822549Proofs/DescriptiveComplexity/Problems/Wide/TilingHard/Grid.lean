/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.TilingHard.Emit
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Increment
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

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549.WideTilings
end Lax822549.WideTilings

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMLe WMSetLe WPoint)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideTilings (MaxPos wideTileData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd MinPos SuccPos)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The grid of the emitted tiling is the machine's tape

The bridge the hardness reduction is built on: the coordinates of
`DescriptiveComplexity.WideTiling` at the emitted instance are exactly the
addresses of the machine's own instance, in the machine's own order.

A coordinate is an address of the emitted universe holding digits alone
(`DescriptiveComplexity.wtpPosn`), a digit is the diagonal triple of an element
(`DescriptiveComplexity.tpDig`), and the emitted order puts every point that is
not a digit *below* every digit. So a coordinate is a set of digits, the two
coordinates being compared differ at a digit, and there the emitted order is the
machine's: the binary-number order on coordinates *is* the binary-number order on
the machine's addresses (`tpCol_setLe`).
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

section Grid

variable {A : Type} [LinearOrder A] [Lax822549.WideMachines.wide.Structure A]

/-- **The coordinate an address of the machine is**: the digits of its
elements. -/
def tpCol (s : A → Prop) : TilePt A → Prop := fun p => ∃ a, s a ∧ p = tpDig a

omit [LinearOrder A] [Lax822549.WideMachines.wide.Structure A] in
@[simp]
theorem tpCol_dig (s : A → Prop) (x : A) : tpCol s (tpDig (A := A) x) ↔ s x := by
  refine ⟨fun ⟨a, ha, heq⟩ => ?_, fun h => ⟨x, h, rfl⟩⟩
  exact (tpDig_injective heq.symm) ▸ ha

omit [LinearOrder A] [Lax822549.WideMachines.wide.Structure A] in
/-- A coordinate holds digits alone, which is what makes it a position. -/
theorem tpCol_dig_of_mem {s : A → Prop} {p : TilePt A} (h : tpCol s p) : TPDig p := by
  obtain ⟨a, -, rfl⟩ := h
  exact tpDig_isDig a

omit [LinearOrder A] [Lax822549.WideMachines.wide.Structure A] in
/-- **A digit is the digit of its own first coordinate.** -/
theorem tpDig_eq_self {p : TilePt A} (h : TPDig p) : tpDig (A := A) (p.2 0) = p := by
  obtain ⟨h1, h2, h3⟩ := h
  refine Prod.ext h1.symm (funext fun i => ?_)
  fin_cases i
  · rfl
  · exact h2
  · exact h2.trans h3

omit [LinearOrder A] [Lax822549.WideMachines.wide.Structure A] in
/-- Two addresses with the same coordinate are the same address. -/
theorem tpCol_injective : Function.Injective (tpCol (A := A)) := by
  intro s t h
  funext x
  exact propext (by rw [← tpCol_dig s x, ← tpCol_dig t x, h])

omit [LinearOrder A] [Lax822549.WideMachines.wide.Structure A] in
/-- **Every position is a coordinate**: an address holding digits alone is the
coordinate of the elements those digits belong to. -/
theorem exists_tpCol {u : TilePt A → Prop} (h : ∀ p, u p → TPDig p) :
    ∃ s : A → Prop, u = tpCol s := by
  refine ⟨fun a => u (tpDig a), funext fun p => propext ⟨fun hp => ⟨p.2 0, ?_, ?_⟩, ?_⟩⟩
  · change u (tpDig (p.2 0))
    rw [tpDig_eq_self (h p hp)]
    exact hp
  · exact (tpDig_eq_self (h p hp)).symm
  · rintro ⟨a, ha, rfl⟩
    exact ha

/-- **The order on coordinates is the machine's order on addresses**: they
differ at a digit, and there the emitted order is the machine's. -/
theorem tpCol_setLe (s t : A → Prop) :
    Lax822549.WideMachines.WMSetLe (tpLe (A := A)) (tpCol s) (tpCol t) ↔ Lax822549.WideMachines.WMSetLe (Lax822549.WideMachines.WMLe (A := A)) s t := by
  constructor
  · rintro (heq | ⟨p, hbelow, hns, ht⟩)
    · exact Or.inl fun x => by rw [← tpCol_dig s x, ← tpCol_dig t x]; exact heq _
    · -- the witness is a digit, since it lies in the second coordinate
      obtain ⟨a, ha, rfl⟩ := ht
      refine Or.inr ⟨a, fun y hy => ?_, fun hc => hns ((tpCol_dig s a).mpr hc), ha⟩
      have hy' : tpLe (tpDig (A := A) y) (tpDig (A := A) a) ∧
          ¬tpLe (tpDig (A := A) a) (tpDig (A := A) y) :=
        ⟨(tpLe_dig y a).mpr hy.1, fun hc => hy.2 ((tpLe_dig a y).mp hc)⟩
      have := hbelow (tpDig y) hy'
      rwa [tpCol_dig, tpCol_dig] at this
  · rintro (heq | ⟨x, hbelow, hns, ht⟩)
    · refine Or.inl fun p => ⟨fun ⟨a, ha, hp⟩ => ⟨a, (heq a).mp ha, hp⟩,
        fun ⟨a, ha, hp⟩ => ⟨a, (heq a).mpr ha, hp⟩⟩
    · refine Or.inr ⟨tpDig x, fun p hp => ?_, ?_, (tpCol_dig t x).mpr ht⟩
      · by_cases hd : TPDig p
        · obtain ⟨s', hs'⟩ : ∃ y, p = tpDig y := ⟨p.2 0, (tpDig_eq_self hd).symm⟩
          subst hs'
          have hlt : WMLt (Lax822549.WideMachines.WMLe (A := A)) s' x :=
            ⟨(tpLe_dig s' x).mp hp.1, fun hc => hp.2 ((tpLe_dig x s').mpr hc)⟩
          rw [tpCol_dig, tpCol_dig]
          exact hbelow s' hlt
        · exact iff_of_false (fun hc => hd (tpCol_dig_of_mem hc))
            (fun hc => hd (tpCol_dig_of_mem hc))
      · exact fun hc => hns ((tpCol_dig s x).mp hc)

end Grid

/-! ### The bottom row and the step from one row to the next -/

section Steps

variable {A : Type} [LinearOrder A] [Finite A] [Lax822549.WideMachines.wide.Structure A]

variable (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A)))

omit [LinearOrder A] [Finite A] [Lax822549.WideMachines.wide.Structure A] hlin in
/-- The empty coordinate holds nothing. -/
theorem not_tpCol_bot (p : TilePt A) : ¬tpCol (fun _ : A => False) p :=
  fun h => h.choose_spec.1

include hlin

omit [Finite A] hlin in
/-- Every position of the emitted tiling is the coordinate of an address of the
machine. -/
theorem exists_tpCol_of_posn {p : Lax822549.WideMachines.WPoint (TilePt A)}
    (hp : letI := tileStr A; (Lax822549.WideTilings.wideTileData (TilePt A)).Posn p) :
    ∃ s : A → Prop, p = Sum.inl (tpCol s) := by
  let := tileStr A
  rcases p with u | t
  · obtain ⟨s, hs⟩ := exists_tpCol (u := u) fun q hq => hp q hq
    exact ⟨s, congrArg Sum.inl hs⟩
  · exact hp.elim

/-- **The empty coordinate is the least position**, which is where the machine's
head starts and where the bottom row is. -/
theorem minPos_tpCol_bot :
    letI := tileStr A
    Lax904597.Machines.MinPos (Lax822549.WideTilings.wideTileData (TilePt A)).Le (Lax822549.WideTilings.wideTileData (TilePt A)).Posn
      (Sum.inl (tpCol (fun _ : A => False))) := by
  let := tileStr A
  refine ⟨fun q hq => (not_tpCol_bot q hq).elim, fun q hq => ?_⟩
  obtain ⟨r, rfl⟩ := exists_tpCol_of_posn hq
  exact wmSetLe_of_empty (isLinOrd_tpLe hlin) not_tpCol_bot (tpCol r)

/-- **And it is the only one**: a least position is the empty coordinate. -/
theorem eq_bot_of_minPos {p : Lax822549.WideMachines.WPoint (TilePt A)}
    (h : letI := tileStr A
      Lax904597.Machines.MinPos (Lax822549.WideTilings.wideTileData (TilePt A)).Le (Lax822549.WideTilings.wideTileData (TilePt A)).Posn p) :
    p = Sum.inl (tpCol (fun _ : A => False)) := by
  let := tileStr A
  obtain ⟨s, rfl⟩ := exists_tpCol_of_posn h.1
  have h1 : Lax822549.WideMachines.WMSetLe (tpLe (A := A)) (tpCol s) (tpCol (fun _ : A => False)) :=
    h.2 (Sum.inl (tpCol (fun _ : A => False)))
      (fun q hq => (not_tpCol_bot (A := A) q hq).elim)
  have h2 : Lax822549.WideMachines.WMSetLe (tpLe (A := A)) (tpCol (fun _ : A => False)) (tpCol s) :=
    wmSetLe_of_empty (isLinOrd_tpLe hlin) not_tpCol_bot (tpCol s)
  exact congrArg Sum.inl
    ((isLinOrd_wmSetLe (isLinOrd_tpLe hlin)).2.2.1 _ _ h1 h2)

/-- **The full coordinate is the last position**, which is the other column with
a neighbor missing. -/
theorem maxPos_tpCol_top :
    letI := tileStr A
    Lax822549.WideTilings.MaxPos (Lax822549.WideTilings.wideTileData (TilePt A)).Le (Lax822549.WideTilings.wideTileData (TilePt A)).Posn
      (Sum.inl (tpCol (fun _ : A => True))) := by
  let := tileStr A
  refine ⟨fun q hq => tpCol_dig_of_mem hq, fun q hq => ?_⟩
  obtain ⟨r, rfl⟩ := exists_tpCol_of_posn hq
  exact (tpCol_setLe r _).mpr (wmSetLe_of_full hlin (fun _ => trivial) r)

/-- **And it is the only one**: a last position is the full coordinate. -/
theorem eq_top_of_maxPos {p : Lax822549.WideMachines.WPoint (TilePt A)}
    (h : letI := tileStr A
      Lax822549.WideTilings.MaxPos (Lax822549.WideTilings.wideTileData (TilePt A)).Le (Lax822549.WideTilings.wideTileData (TilePt A)).Posn p) :
    p = Sum.inl (tpCol (fun _ : A => True)) := by
  let := tileStr A
  obtain ⟨s, rfl⟩ := exists_tpCol_of_posn h.1
  have h1 : Lax822549.WideMachines.WMSetLe (tpLe (A := A)) (tpCol (fun _ : A => True)) (tpCol s) :=
    h.2 (Sum.inl (tpCol (fun _ : A => True))) (maxPos_tpCol_top hlin).1
  have h2 : Lax822549.WideMachines.WMSetLe (tpLe (A := A)) (tpCol s) (tpCol (fun _ : A => True)) :=
    (maxPos_tpCol_top hlin).2 (Sum.inl (tpCol s)) (fun q hq => tpCol_dig_of_mem hq)
  exact congrArg Sum.inl
    ((isLinOrd_wmSetLe (isLinOrd_tpLe hlin)).2.2.1 _ _ h2 h1)

/-- **The successor of a coordinate is the increment of the address**: nothing
lies strictly between an address and its increment, and every position is a
coordinate. -/
theorem succPos_tpCol (s t : A → Prop) :
    letI := tileStr A
    (Lax904597.Machines.SuccPos (Lax822549.WideTilings.wideTileData (TilePt A)).Le (Lax822549.WideTilings.wideTileData (TilePt A)).Posn
        (Sum.inl (tpCol s)) (Sum.inl (tpCol t)) ↔
      WMIncr (Lax822549.WideMachines.WMLe (A := A)) s t) := by
  let := tileStr A
  constructor
  · rintro ⟨-, -, hle, hne, hbetween⟩
    have hsle : Lax822549.WideMachines.WMSetLe (Lax822549.WideMachines.WMLe (A := A)) s t := (tpCol_setLe s t).mp hle
    have hst : s ≠ t := fun hc => hne (congrArg (fun r => Sum.inl (tpCol r)) hc)
    have hslt : WMSetLt (Lax822549.WideMachines.WMLe (A := A)) s t := (wmSetLt_iff _ _).mpr ⟨hsle, hst⟩
    obtain ⟨x, -, hx, -⟩ := hslt
    obtain ⟨s', hincr⟩ := exists_wmIncr hlin ⟨x, hx⟩
    -- the increment is at or below the target, since the target is above `s`
    have hs'le : Lax822549.WideMachines.WMSetLe (Lax822549.WideMachines.WMLe (A := A)) s' t := by
      by_contra hc
      rcases (isLinOrd_wmSetLe hlin).2.2.2 s' t with h1 | h1
      · exact hc h1
      · have h2 : WMSetLt (Lax822549.WideMachines.WMLe (A := A)) t s' :=
          (wmSetLt_iff _ _).mpr ⟨h1, fun hcc => hc (hcc ▸ (isLinOrd_wmSetLe hlin).1 s')⟩
        exact hst ((isLinOrd_wmSetLe hlin).2.2.1 _ _ hsle
          ((wmSetLt_iff_of_wmIncr hlin hincr t).mp h2))
    have hmid := hbetween (Sum.inl (tpCol s')) (fun q hq => tpCol_dig_of_mem hq)
      ((tpCol_setLe s s').mpr (wmSetLe_of_wmIncr hincr))
      ((tpCol_setLe s' t).mpr hs'le)
    rcases hmid with hc | hc
    · exact absurd (tpCol_injective (Sum.inl.inj hc)) (ne_of_wmIncr hincr).symm
    · exact (tpCol_injective (Sum.inl.inj hc)) ▸ hincr
  · intro hincr
    refine ⟨fun q hq => tpCol_dig_of_mem hq, fun q hq => tpCol_dig_of_mem hq,
      (tpCol_setLe s t).mpr (wmSetLe_of_wmIncr hincr),
      fun hc => (ne_of_wmIncr hincr) (tpCol_injective (Sum.inl.inj hc)),
      fun u hu h1 h2 => ?_⟩
    obtain ⟨r, rfl⟩ := exists_tpCol_of_posn hu
    rcases eq_of_between_wmIncr hlin hincr ((tpCol_setLe s r).mp h1)
      ((tpCol_setLe r t).mp h2) with hc | hc
    · exact Or.inl (congrArg (fun w => Sum.inl (tpCol w)) hc)
    · exact Or.inr (congrArg (fun w => Sum.inl (tpCol w)) hc)

end Steps

end TilingHard

end Lax822549Proofs.DescriptiveComplexity


