/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltTable

/-!
# The positions of the QBF machine's tape, concretely

Where the head is, and what follows what: the left marker is the lowest
position, the cell of the least element follows it, the right marker follows
the cell of the greatest element, and cells are ordered as their elements are.

Every fact about the *tags* here is a `decide`: `DescriptiveComplexity.AltQbf.AltBase`
does not depend on `k`, and a tag's sweep index only ever refines the order
inside a family (`DescriptiveComplexity.AltQbf.altTag_lt_of_base_lt`). That is what the
pair-shaped tag of `DescriptiveComplexity.Problems.Machine.AltTape` buys.

The file ends with the determinism of the machine away from the guessing
choice, which is what makes the `⇐` half of correctness a corollary of
`DescriptiveComplexity.AltQbf.altTr_unique` rather than a second induction.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Positions

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The three kinds of position -/

omit [(Language.qbf k).Structure A] in
/-- The left marker is a position. -/
theorem altPosn_posStart : AltPosn (posStart : AltV k A) :=
  ⟨rfl, fun a => ⟨qbotA_le a, qbotA_le a⟩⟩

omit [(Language.qbf k).Structure A] in
/-- The cell of an element is a position. -/
theorem altPosn_posCell (x : A) : AltPosn (posCell x : AltV k A) :=
  ⟨rfl, fun a => qbotA_le a⟩

omit [(Language.qbf k).Structure A] in
/-- The right marker is a position. -/
theorem altPosn_posEnd : AltPosn (posEnd : AltV k A) :=
  ⟨rfl, fun a => ⟨qbotA_le a, qbotA_le a⟩⟩

/-! ### The tape order -/

omit [(Language.qbf k).Structure A] [Finite A] [Nonempty A] in
/-- The tape order is reflexive. -/
theorem altTagTupleLe_refl (p : AltV k A) : tagTupleLe p p := Or.inr ⟨rfl, Or.inl rfl⟩

omit [(Language.qbf k).Structure A] [Finite A] [Nonempty A] in
/-- A tag strictly below another puts its tuples below all of theirs. -/
theorem altTagTupleLe_of_tag_lt {p q : AltV k A} (h : p.1 < q.1) : tagTupleLe p q := Or.inl h

/-- **A lower base tag is a lower tag**, whatever the sweep indices: the order
on tags is the base tag first. -/
theorem altTag_lt_of_base_lt {t t' : AltBase} (h : altBaseIdx t < altBaseIdx t')
    (i i' : Fin (k + 1)) : ((t, i) : AltTag k) < (t', i') :=
  Prod.Lex.left _ _ h

omit [(Language.qbf k).Structure A] [Finite A] [Nonempty A] in
/-- The tape order refines the tag order. -/
theorem altTagTupleLe_tag_le {p q : AltV k A} (h : tagTupleLe p q) : p.1 ≤ q.1 := by
  rcases h with h | ⟨h, -⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- The tag order refines the base-tag numbering. -/
theorem altBaseIdx_le_of_tag_le {t t' : AltTag k} (h : t ≤ t') :
    altBaseIdx t.1 ≤ altBaseIdx t'.1 := by
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, -⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-! ### Singling the markers and the cells out -/

omit [(Language.qbf k).Structure A] in
/-- There is only one left marker. -/
theorem eq_posStart_of_posn {p : AltV k A} (hp : AltPosn p) (h : p.1.1 = AltBase.pStart) :
    p = posStart := by
  obtain ⟨⟨t, i⟩, w⟩ := p
  simp only at h
  subst h
  obtain ⟨hi, hw⟩ := hp
  refine Prod.ext (Prod.ext rfl (Fin.ext hi)) (funext fun j => ?_)
  fin_cases j
  · exact le_antisymm (hw qbotA).1 (qbotA_le _)
  · exact le_antisymm (hw qbotA).2 (qbotA_le _)

omit [(Language.qbf k).Structure A] in
/-- A cell is the cell of the element it carries. -/
theorem eq_posCell_of_posn {p : AltV k A} (hp : AltPosn p) (h : p.1.1 = AltBase.pCell) :
    p = posCell (p.2 0) := by
  obtain ⟨⟨t, i⟩, w⟩ := p
  simp only at h
  subst h
  obtain ⟨hi, hw⟩ := hp
  refine Prod.ext (Prod.ext rfl (Fin.ext hi)) (funext fun j => ?_)
  fin_cases j
  · simp [aoneI]
  · exact le_antisymm (hw qbotA) (qbotA_le _)

omit [(Language.qbf k).Structure A] in
/-- There is only one right marker. -/
theorem eq_posEnd_of_posn {p : AltV k A} (hp : AltPosn p) (h : p.1.1 = AltBase.pEnd) :
    p = posEnd := by
  obtain ⟨⟨t, i⟩, w⟩ := p
  simp only at h
  subst h
  obtain ⟨hi, hw⟩ := hp
  refine Prod.ext (Prod.ext rfl (Fin.ext hi)) (funext fun j => ?_)
  fin_cases j
  · exact le_antisymm (hw qbotA).1 (qbotA_le _)
  · exact le_antisymm (hw qbotA).2 (qbotA_le _)

/-! ### The order between the three kinds -/

omit [(Language.qbf k).Structure A] in
theorem posStart_le_posCell (x : A) : tagTupleLe (posStart : AltV k A) (posCell x) :=
  altTagTupleLe_of_tag_lt (altTag_lt_of_base_lt (by decide) _ _)

omit [(Language.qbf k).Structure A] in
theorem posCell_le_posEnd (x : A) : tagTupleLe (posCell x : AltV k A) posEnd :=
  altTagTupleLe_of_tag_lt (altTag_lt_of_base_lt (by decide) _ _)

omit [(Language.qbf k).Structure A] in
theorem posStart_le_posEnd : tagTupleLe (posStart : AltV k A) posEnd :=
  altTagTupleLe_of_tag_lt (altTag_lt_of_base_lt (by decide) _ _)

/-- Every base tag other than the left marker's is above it. -/
theorem pStart_idx_lt {t : AltBase} (h : t ≠ AltBase.pStart) :
    altBaseIdx AltBase.pStart < altBaseIdx t := by
  revert h; revert t; decide

omit [(Language.qbf k).Structure A] in
/-- **The left marker is the lowest position**: the head starts there. -/
theorem minPos_posStart : MinPos tagTupleLe AltPosn (posStart : AltV k A) := by
  refine ⟨altPosn_posStart, fun q hq => ?_⟩
  rcases eq_or_ne q.1.1 AltBase.pStart with h | h
  · rw [eq_posStart_of_posn hq h]
    exact altTagTupleLe_refl _
  · exact altTagTupleLe_of_tag_lt (altTag_lt_of_base_lt (pStart_idx_lt h) _ _)

omit [(Language.qbf k).Structure A] in
/-- **Cells are ordered as their elements are**: the tape order between two
cells is the source order between the elements they belong to, which is what
makes a sweep over the cells a walk along the instance. -/
theorem posCell_le_iff {x y : A} : tagTupleLe (posCell x : AltV k A) (posCell y) ↔ x ≤ y := by
  constructor
  · rintro (h | ⟨-, h | ⟨j, hlt, hj⟩⟩)
    · exact absurd h (lt_irrefl _)
    · exact le_of_eq (by simpa [aoneI] using congrFun h 0)
    · fin_cases j
      · exact le_of_lt (by simpa [aoneI] using hj)
      · exact le_of_eq (by simpa [aoneI] using hlt 0 (by decide))
  · intro h
    refine Or.inr ⟨rfl, ?_⟩
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨0, fun i hi => absurd hi (by omega), by simpa [aoneI] using hlt⟩

/-! ### The head's first and last moves of a sweep -/

/-- Only the two lowest base tags are at or below a cell's. -/
theorem base_le_pCell {t : AltBase} (h : altBaseIdx t ≤ altBaseIdx AltBase.pCell) :
    t = AltBase.pStart ∨ t = AltBase.pCell := by
  revert h; revert t; decide

/-- Only the two highest of the bracketing base tags lie between a cell's and
the right marker's. -/
theorem base_between {t : AltBase} (h₁ : altBaseIdx AltBase.pCell ≤ altBaseIdx t)
    (h₂ : altBaseIdx t ≤ altBaseIdx AltBase.pEnd) :
    t = AltBase.pCell ∨ t = AltBase.pEnd := by
  revert h₁ h₂; revert t; decide

omit [(Language.qbf k).Structure A] in
/-- **The head's first move.** The cell of the least element follows the left
marker immediately: a sweep starts by stepping over `⊢`. -/
theorem succPos_posStart_posCell :
    SuccPos tagTupleLe AltPosn (posStart : AltV k A) (posCell qbotA) := by
  refine ⟨altPosn_posStart, altPosn_posCell _, posStart_le_posCell _, ?_, ?_⟩
  · intro h
    exact absurd (congrArg (fun p => p.1.1) h)
      (show ¬(AltBase.pStart = AltBase.pCell) by decide)
  · intro r hr h1 h2
    rcases base_le_pCell (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le h2)) with h | h
    · exact Or.inl (eq_posStart_of_posn hr h)
    · refine Or.inr ?_
      have hcell := eq_posCell_of_posn hr h
      have hle : r.2 0 ≤ qbotA := posCell_le_iff.mp (hcell ▸ h2)
      rw [hcell, le_antisymm hle (qbotA_le _)]

/-- The greatest element of the instance: the last cell of the tape. -/
def qtopA : A := (Finite.exists_max (id : A → A)).choose

omit [(Language.qbf k).Structure A] in
theorem le_qtopA (a : A) : a ≤ qtopA (A := A) := (Finite.exists_max (id : A → A)).choose_spec a

omit [(Language.qbf k).Structure A] in
/-- **The head's last move of a sweep.** The right marker follows the cell of
the greatest element: this is where a sweep turns round. -/
theorem succPos_posCell_posEnd :
    SuccPos tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) posEnd := by
  refine ⟨altPosn_posCell _, altPosn_posEnd, posCell_le_posEnd _, ?_, ?_⟩
  · intro h
    exact absurd (congrArg (fun p => p.1.1) h)
      (show ¬(AltBase.pCell = AltBase.pEnd) by decide)
  · intro r hr h1 h2
    rcases base_between (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le h1))
      (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le h2)) with h | h
    · refine Or.inl ?_
      have hcell := eq_posCell_of_posn hr h
      have hx : qtopA ≤ r.2 0 := posCell_le_iff.mp (hcell ▸ h1)
      rw [hcell, le_antisymm (le_qtopA _) hx]
    · exact Or.inr (eq_posEnd_of_posn hr h)

/-! ### Determinism away from the guess -/

/-- **The machine is deterministic away from the guessing choice.** Once the
transition is pinned (`DescriptiveComplexity.AltQbf.altTr_unique`), the successor
configuration is too: its state by `altDst_functional`, the cell under the head
by `altWrite_functional`, every other cell by the frame condition, and the head
itself by uniqueness of the neighbor in the direction the transition names. -/
theorem step_functional_off_guess {cnf : Bool} {c c₁ c₂ : Config (AltV k A)}
    (hguess : ¬∃ (i : Fin (k + 1)) (x : A), c.state = stG i true ∧ c.tape c.head = symV false x)
    (h₁ : (altMachine k A cnf).Step c c₁) (h₂ : (altMachine k A cnf).Step c c₂) : c₁ = c₂ := by
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := h₁
  obtain ⟨σ, hσ, hsrc', hread', hdst', hwrite', hframe', hmove'⟩ := h₂
  have hteq : τ = σ := altTr_unique hτ hσ hsrc hsrc' hread hread' hguess
  subst hteq
  refine Config.ext (altDst_functional hdst hdst') ?_ (funext fun p => ?_)
  · rcases hmove with ⟨hrt, hsp⟩ | ⟨hrt, hsp⟩ <;>
      rcases hmove' with ⟨hrt', hsp'⟩ | ⟨hrt', hsp'⟩
    · exact TMData.succPos_right_unique isLinOrd_altTagTupleLe hsp hsp'
    · exact absurd hrt hrt'
    · exact absurd hrt' hrt
    · exact succPos_left_unique isLinOrd_altTagTupleLe hsp hsp'
  · rcases eq_or_ne p c.head with rfl | hne
    · exact altWrite_functional hwrite hwrite'
    · rw [hframe p hne, hframe' p hne]

end Positions

end AltQbf

end DescriptiveComplexity
