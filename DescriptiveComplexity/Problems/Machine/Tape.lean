/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Program
import DescriptiveComplexity.OrderedComposition

/-!
# The tape of the SAT machine

The layout half of `SAT ≤ᶠᵒ[≤] NTMAccept`: which tagged tuples are positions, in
what order they sit, and why there are enough of them. The program that runs on
this tape – states, symbols, transitions – is separate.

## The layout

The machine's tape is one cell per element of the instance, bracketed by two
markers, followed by filler cells that exist only to supply time:

```
  ⊢   x₁ x₂ … xₙ   ⊣   fillers…
```

`Satisfiable` assigns a truth value to *every* element (elements that are not
variables of any clause are harmless), so there is no need to single out the
variables: one cell per element is both simpler and correct.

Tags are ordered so that this is exactly the order of the interpreted universe.
That order comes for free: `DescriptiveComplexity.lexLeF` is the defining formula of
`le` – tags first, then the tuple lexicographically – and
`DescriptiveComplexity.tagTupleOrder` is already a `LinearOrder`, so the well-formedness
obligation `IsLinOrd` of `DescriptiveComplexity.TMData.WellFormed` is discharged without
a single tag-pair case.

Only the *position* tags are fixed here. The symbol, state and transition tags
of the program get higher indices, which leaves the order of the positions
undisturbed – `DescriptiveComplexity.satTagIdx` is what has to stay monotone, not the
constructor list.

## The budget

The machine needs one sweep to guess an assignment and one sweep per clause to
check it, so `(m + 1) · (n + 2)` steps for `n` elements and `m ≤ n` clauses.
Four filler tags at dimension two give `4n² + n + 2` positions, and
`DescriptiveComplexity.sat_budget` says that is always more. Following the plan's advice
on risk #3, the filler is over-provisioned rather than the bound tightened:
nothing downstream depends on the constant, and an off-by-one here would only
surface at the very end of the correctness proof.
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### The tags of the positions -/

/-- The tags carrying the tape of the SAT machine. The order of the
constructors is the order of the tape; `DescriptiveComplexity.satTagIdx` is what makes
that official.

The program's tags (symbols, states, transitions) will be added after these
with higher indices, which does not disturb the order of the positions. -/
inductive SatTag : Type
  /-- The left marker cell. -/
  | pStart
  /-- The cell of an element: one per element of the instance. -/
  | pCell
  /-- The right marker cell. -/
  | pEnd
  /-- Filler cells, four tags' worth, supplying the time budget. -/
  | pFill (i : Fin 4)
  deriving DecidableEq

instance : Fintype SatTag where
  elems :=
    {SatTag.pStart, SatTag.pCell, SatTag.pEnd,
      SatTag.pFill 0, SatTag.pFill 1, SatTag.pFill 2, SatTag.pFill 3}
  complete := fun t => by cases t with
    | pFill i => fin_cases i <;> decide
    | _ => decide

instance : Nonempty SatTag := ⟨SatTag.pStart⟩

/-- The position of a tag in the tape order. -/
def satTagIdx : SatTag → ℕ
  | .pStart => 0
  | .pCell => 1
  | .pEnd => 2
  | .pFill i => 3 + (i : ℕ)

theorem satTagIdx_injective : Function.Injective satTagIdx := by
  intro s t h
  cases s <;> cases t <;> simp only [satTagIdx] at h ⊢ <;>
    first
      | rfl
      | omega
      | (rename_i i j; exact congrArg _ (Fin.ext (by omega)))

/-- The tape order on tags. -/
instance : LinearOrder SatTag := LinearOrder.lift' satTagIdx satTagIdx_injective

theorem satTag_lt_iff {s t : SatTag} : s < t ↔ satTagIdx s < satTagIdx t := Iff.rfl

theorem satTag_le_iff {s t : SatTag} : s ≤ t ↔ satTagIdx s ≤ satTagIdx t := Iff.rfl

/-! ### The intended positions

Stated as a plain predicate on tagged tuples, in the style of
`DescriptiveComplexity.IAdjRaw`: the interpretation's `posn` formula will be shown to
realize exactly this, and every fact proved here transfers. -/

section Positions

variable {A : Type} [LinearOrder A]

/-- The tagged tuples that are positions: the two markers are the single tuple
of minima, an element's cell is that element in the first coordinate, and the
fillers are unrestricted. -/
def SatPosn (p : SatTag × (Fin 2 → A)) : Prop :=
  match p.1 with
  | .pStart => ∀ a : A, p.2 0 ≤ a ∧ p.2 1 ≤ a
  | .pCell => ∀ a : A, p.2 1 ≤ a
  | .pEnd => ∀ a : A, p.2 0 ≤ a ∧ p.2 1 ≤ a
  | .pFill _ => True

/-- There is exactly one start marker. -/
theorem satPosn_pStart_iff {w : Fin 2 → A} :
    SatPosn (SatTag.pStart, w) ↔ (∀ a : A, w 0 ≤ a) ∧ ∀ a : A, w 1 ≤ a :=
  ⟨fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩, fun h a => ⟨h.1 a, h.2 a⟩⟩

/-- A cell is a position exactly when its second coordinate is the minimum: one
cell per element, indexed by the first coordinate. -/
theorem satPosn_pCell_iff {w : Fin 2 → A} :
    SatPosn (SatTag.pCell, w) ↔ ∀ a : A, w 1 ≤ a := Iff.rfl

/-- Every filler tuple is a position. -/
theorem satPosn_pFill {i : Fin 4} {w : Fin 2 → A} : SatPosn (SatTag.pFill i, w) := trivial

end Positions

/-! ### The budget -/

/-- **There are enough positions.** The machine takes one sweep to guess an
assignment and one per clause to check it, `(m + 1) · (n + 2)` steps in all for
`n` elements and `m ≤ n` clauses; the tape has `4n² + n + 2` positions.

The inequality is strict, as `DescriptiveComplexity.TMData.Accepts` requires: `N`
positions are `N` time points and so `N - 1` steps. -/
theorem sat_budget {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    (m + 1) * (n + 2) < 4 * n ^ 2 + n + 2 := by
  have hstep : (m + 1) * (n + 2) ≤ (n + 1) * (n + 2) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_succ hm)
  have hsq : n ^ 2 = n * n := sq n
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  nlinarith [hstep, hsq, hnn]

end DescriptiveComplexity
