/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.RE
import DescriptiveComplexity.Problems.CodeHalt.Hardness.Draw
import DescriptiveComplexity.RecursivelyEnumerable

/-!
# Every semi-decidable problem reduces to CODEHALT

**`DescriptiveComplexity.orderedReduction_codehalt`**: a decision problem
whose concrete instances form a recursively enumerable set – in Mathlib's
sense, `REPred` – reduces to `DescriptiveComplexity.CODEHALT` by an ordered
first-order reduction.

This is the pivot of the library's undecidability results: it makes
`CODEHALT` RE-hard (instantiate at a problem already known to be RE-hard) and
it makes “RE is exactly the recursively enumerable properties of finite
structures” a theorem (instantiate at an arbitrary problem and push membership
forward along the reduction). Both readings are drawn in
`DescriptiveComplexity.Computability.CodeHaltComplete`.

## Why the code model, and not a machine

The reduction has to *produce a program*. For a machine that would mean
writing a transition table and proving its run correct – the evaluator with
addressed storage, the expensive object the library has so far always avoided.
Here the program is a `Nat.Partrec.Code`, and “a program semi-deciding this
problem exists” is a theorem of Mathlib
(`Nat.Partrec.Code.exists_code`): the reduction *names* the procedure `cP`
instead of building it, and only has to write the instance beside it, as the
argument of one `comp`.

## The three pieces

* the value the instance is written as, and its decoding
  (`DescriptiveComplexity.structVal`, `DescriptiveComplexity.structOf`, in
  `DescriptiveComplexity.Problems.CodeHalt.Hardness.Value`);
* the drawing of `comp cP (pair numeral nest)` as a first-order interpretation
  (`DescriptiveComplexity.codeProgInterp`, in
  `DescriptiveComplexity.Problems.CodeHalt.Hardness.Interp`) and its
  correctness (`DescriptiveComplexity.decodesTo_rootPt`,
  `DescriptiveComplexity.codeWF_codeProg`, in
  `DescriptiveComplexity.Problems.CodeHalt.Hardness.Draw`);
* the two lines this file adds: evaluating the drawn code is running `cP` on
  the value, and decoding the value gives the instance back.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Nat.Partrec (Code)

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L) (cP : Code)
  (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The drawn code computes the value of the instance -/

open Classical in
omit [L.IsRelational] in
/-- **The drawn code runs the procedure on the value of the instance.** Every
branch is evaluated at input `0`, so the argument of the `comp` is a constant:
the pair of the numeral of the universe size with the nest of the tables. -/
theorem eval_drawnCode :
    Code.eval (Code.comp cP (Code.pair (numCode (Nat.card A))
        (codeNestFrom (blockCode V (Nat.card A) (ordEnum A) (botTup V A)) 0))) 0 =
      Code.eval cP (structVal V (Nat.card A) (ordEnum A) (botTup V A)) := by
  refine eval_comp_zero ?_
  refine eval_pair_zero (eval_numCode _) ?_
  exact eval_codeNestFrom _ _ (fun j => eval_levelCode _ _ j _ _) 0

open Classical in
omit [L.IsRelational] in
/-- **The instance is a yes-instance of CODEHALT exactly when the procedure
halts on the value of the instance.** -/
theorem codehalt_codeProg :
    CODEHALT ((codeProgInterp V cP).Map A) ↔
      (Code.eval cP (structVal V (Nat.card A) (ordEnum A) (botTup V A))).Dom := by
  have hev := eval_drawnCode V cP A
  constructor
  · rintro ⟨q, c, hroot, hdec, hh⟩
    obtain ⟨t, u, rfl⟩ := exists_progPt q
    obtain ⟨hok, rfl⟩ := (cRoot_pt t u).mp hroot
    obtain rfl : u = botTup V A := canon0_ext hok (canon_botTup 0)
    obtain rfl := decodesTo_unique (codeWF_codeProg V cP A) c _ _ hdec (decodesTo_rootPt cP)
    rwa [hev] at hh
  · intro hd
    exact ⟨progPt ProgTag.root (botTup V A), _, (cRoot_pt _ _).mpr ⟨canon_botTup 0, rfl⟩,
      decodesTo_rootPt cP, by rw [hev]; exact hd⟩

/-! ### The value is decoded back into the instance -/

variable {A}

open Classical in
/-- **Decoding the value of an instance answers about the instance.** -/
theorem toPred_structOf_structVal (P : DecisionProblem L) :
    P.toPred V (structOf V (structVal V (Nat.card A) (ordEnum A) (botTup V A))) ↔ P A :=
  P.iso_invariant
    (structValEquiv V (Nat.card A) Nat.card_pos (ordEnum A).toEquiv (botTup V A))

/-! ### The reduction -/

variable {V}

/-- **A semi-decidable problem reduces to CODEHALT.** The reduction draws the
instance as the program `comp cP (pair numeral nest)`, where `cP` is a code
semi-deciding the problem – which `Nat.Partrec.Code.exists_code` supplies –
and the rest is a constant the first-order formulas can write. -/
theorem orderedReduction_codehalt (P : DecisionProblem L) (h : REPred (P.toPred V)) :
    Nonempty (P ≤ᶠᵒ[≤] CODEHALT) := by
  classical
  obtain ⟨cP, hcP⟩ : ∃ cP : Code, ∀ N : ℕ,
      (Code.eval cP N).Dom ↔ P.toPred V (structOf V N) := by
    have hcomp : Partrec fun N : ℕ =>
        (Part.assert (P.toPred V (structOf V N)) fun _ => Part.some ()).map
          fun _ => (0 : ℕ) :=
      (h.comp (primrec_structOf V).to_comp).map (Computable.const (0 : ℕ)).to₂
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hcomp)
    refine ⟨c, fun N => ?_⟩
    rw [hc]
    simp only [Part.map, Part.assert]
    exact ⟨fun hh => hh.1, fun hp => ⟨hp, trivial⟩⟩
  exact ⟨{ Tag := ProgTag V cP
           dim := dimOf V
           toInterpretation := codeProgInterp V cP
           correct := fun A _ _ _ _ => by
             rw [codehalt_codeProg V cP A, hcP, toPred_structOf_structVal V P] }⟩

end DescriptiveComplexity
