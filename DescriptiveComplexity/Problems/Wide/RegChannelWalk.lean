/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelEnum

/-!
# The opening's walk at the register channel

The opening of a handed program leaves the marker, walks up to the file, steps
onto its first register, turns, comes home, guesses, and enters the evaluation.
What it asks of the instance is four addresses and five order facts
(`DescriptiveComplexity.Pfp.PfpData.reachesIn_openingHanded`), and at this
channel they are all forced:

* the marker is the **empty address**, and the walk's first step is its
  increment;
* the file's first register is the **singleton of the element the reduction
  marks below the argument tags** (`DescriptiveComplexity.wmRegSeg_least`), so
  the address the walk stops on is that singleton's predecessor;
* the walk reaches it as long as the singleton is not itself the second address
  – which it is not, there being an argument element above the marked one.

So the whole geometry follows from the marking, and this file derives it.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

section Walk

variable {L : Language.{0, 0}} {dt : PfpData L} {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
variable (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] in
include h in
/-- **The opening's walk exists**: the marker's increment, the address the walk
stops on, the file's first register and its own increment, with the five order
facts the opening asks of them.

The one thing the instance has to bring is an element **above** the one the
channel marks below the argument tags – any argument element will do – which is
what makes the file's first register more than one step above the marker. -/
theorem exists_openingWalkReg {botE : Univ A R' P' dt.KIx dt.dd}
    (hbotm : WMHasInp botE)
    (hleast : ∀ y : Univ A R' P' dt.KIx dt.dd, WMHasInp y → WMLe botE y)
    (habove : ∃ z : Univ A R' P' dt.KIx dt.dd, WMLt WMLe botE z) :
    ∃ v₁ x y' : Univ A R' P' dt.KIx dt.dd → Prop,
      WMIncr WMLe (fun _ => False) v₁ ∧ WMSetLe WMLe v₁ x ∧
        WMIncr WMLe x (wmRegSeg botE) ∧ WMIncr WMLe (wmRegSeg botE) y' ∧
        WMSetLe WMLe (fun _ => False) (wmRegSeg botE) := by
  classical
  obtain ⟨z, hz⟩ := habove
  -- the first register is the marked element's own singleton
  have hcell : wmRegSeg botE = fun w => w = botE := wmRegSeg_least h hbotm hleast
  have hne : ∃ w, wmRegSeg botE w := ⟨botE, h.1 botE, hbotm⟩
  -- the marker's increment, and the address the walk stops on
  obtain ⟨v₁, hvi₁⟩ := exists_wmIncr h (s := fun _ : Univ A R' P' dt.KIx dt.dd => False)
    ⟨botE, not_false⟩
  obtain ⟨x, hxy⟩ := exists_wmPred h hne
  obtain ⟨y', hyy'⟩ := exists_wmIncr h (s := wmRegSeg botE) ⟨z, fun hc => hz.2 hc.1⟩
  refine ⟨v₁, x, y', hvi₁, ?_, hxy, hyy',
    wmSetLe_of_empty h (fun _ => not_false) _⟩
  -- the walk reaches the register's predecessor: the register is not the
  -- marker's own increment, since an element lies above the one it holds
  refine (wmSetLt_iff_of_wmIncr h hxy v₁).mp ?_
  refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_succ_bot_of_nonempty h hvi₁ hne, fun hc => ?_⟩
  -- were they equal, the register would be the least nonempty address, and the
  -- singleton of an element above the marked one is below it
  have hz1 : WMSetLt WMLe (fun w => w = z) (wmRegSeg botE) := by
    rw [hcell]
    refine ⟨botE, fun w hw => iff_of_false ?_ ?_, fun hcz => hz.2 ?_, rfl⟩
    · rintro rfl
      exact hw.2 hz.1
    · rintro rfl
      exact hw.2 (h.1 w)
    · rw [← hcz]
      exact h.1 botE
  have hle : WMSetLe WMLe v₁ (fun w => w = z) :=
    wmSetLe_succ_bot_of_nonempty h hvi₁ ⟨z, rfl⟩
  rw [hc] at hle
  exact ((wmSetLt_iff _ _).mp hz1).2
    ((isLinOrd_wmSetLe h).2.2.1 _ _ ((wmSetLt_iff _ _).mp hz1).1 hle)

end Walk

end PfpData

end Pfp

end DescriptiveComplexity
