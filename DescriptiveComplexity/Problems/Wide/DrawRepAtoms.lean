/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawAtoms
import DescriptiveComplexity.Exponential.Block

/-!
# The atoms of a defining sentence, classified

The element loops of the EXPSPACE program evaluate the matrices of the
expansion's defining sentences – `X.relSentence`, over the base vocabulary
expanded by a **replicated** block (one copy per argument point), and
`X.dom`, over the same expanded by the block itself. Both are the same
shape, so the classification is stated at an arbitrary block: the
base-vocabulary atoms – equalities, base relations, order – are **guards**,
evaluated on the control-held elements by the transition table itself; the
block atoms are the **read leaves**, one named-bit trip each, at the cell of
the point whose payload the loop variables spell.

This file mirrors `DescriptiveComplexity.Problems.Wide.DrawAtoms` at that
language: `DescriptiveComplexity.Draw.BlkAtom` is the kind,
`DescriptiveComplexity.Draw.blkAtom?` the total-on-atoms classifier,
`DescriptiveComplexity.Draw.BlkAtom.holds` the semantic reading at a block
assignment, and
`DescriptiveComplexity.Draw.realize_iff_qfValue_blkHolds` the capstone: a
quantifier-free matrix realizes as its Boolean function at the kinds'
readings. For a defining sentence the assignment is
`DescriptiveComplexity.SOBlock.replicateAssign`, so a block atom's index
splits into the copy – *which argument point* – and the point's own relation
variable.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational] {B : SOBlock}

/-! ### The kinds -/

/-- **An atom of a defining sentence, classified**: the base-vocabulary
kinds are guards, the block kind is a read leaf. -/
inductive BlkAtom (L : Language.{0, 0}) (B : SOBlock) (n : ℕ) : Type
  /-- An equality between two prefix levels: a guard. -/
  | eqA : Fin n → Fin n → BlkAtom L B n
  /-- A base-vocabulary relation at prefix levels: a guard. -/
  | baseA : ∀ {m : ℕ}, L.Relations m → (Fin m → Fin n) → BlkAtom L B n
  /-- An order comparison between two prefix levels: a guard. -/
  | ordA : Fin n → Fin n → BlkAtom L B n
  /-- A relation variable of the block at prefix levels: a read leaf. -/
  | blkA : (i : B.ι) → (Fin (B.arity i) → Fin n) → BlkAtom L B n

/-- The classification of a relation atom, by its symbol's summand. -/
def blkRelAtom : ∀ {n m : ℕ},
    ((L.sum Language.order).sum B.lang).Relations m →
    (Fin m → ((L.sum Language.order).sum B.lang).Term (Empty ⊕ Fin n)) →
    BlkAtom L B n
  | _, _, Sum.inl (Sum.inl r), ts => .baseA r fun j => matVar (ts j)
  | _, _, Sum.inl (Sum.inr .le), ts => .ordA (matVar (ts 0)) (matVar (ts 1))
  | _, _, Sum.inr b, ts => .blkA b.1 fun j => matVar (ts (Fin.cast b.2 j))

/-- **The classifier**: the kind of an atom, read off the syntax; `none`
only on non-atoms. -/
def blkAtom? : ∀ {n : ℕ},
    ((L.sum Language.order).sum B.lang).BoundedFormula Empty n →
      Option (BlkAtom L B n)
  | _, .equal t₁ t₂ => some (.eqA (matVar t₁) (matVar t₂))
  | _, .rel r ts => some (blkRelAtom r ts)
  | _, .falsum => none
  | _, .imp _ _ => none
  | _, .all _ => none

/-- **Every atom of a matrix classifies.** -/
theorem isSome_blkAtom?_of_mem_qfAtoms :
    ∀ {n : ℕ}
      (ψ φ : ((L.sum Language.order).sum B.lang).BoundedFormula Empty n),
      φ ∈ qfAtoms ψ → (blkAtom? φ).isSome := by
  intro n ψ
  induction ψ with
  | falsum => exact fun φ h => absurd h (List.not_mem_nil)
  | equal t₁ t₂ =>
    intro φ h
    rw [qfAtoms] at h
    rcases List.mem_singleton.mp h with rfl
    rfl
  | rel r ts =>
    intro φ h
    rw [qfAtoms] at h
    rcases List.mem_singleton.mp h with rfl
    rfl
  | imp f g ihf ihg =>
    intro φ h
    rw [qfAtoms] at h
    rcases List.mem_append.mp h with h | h
    · exact ihf φ h
    · exact ihg φ h
  | all f _ => exact fun φ h => absurd h (List.not_mem_nil)

/-! ### The atoms that need a tape

Only the **block** atoms are read leaves: an equality, a base relation or an
order comparison on the loop's own elements is a guard, evaluated by the
transition table where it stands. So a round of an element loop makes one
trip per block atom and no more – which matters, because a defining sentence
may well have no block atom at all, and there is in general no cell a
harmless trip could be sent to. -/

omit [L.IsRelational] in
/-- **Is this atom a read leaf?** – decided by the relation symbol's
summand, so no term analysis and no relationality is needed. -/
def isBlkAtom : ∀ {n : ℕ},
    ((L.sum Language.order).sum B.lang).BoundedFormula Empty n → Bool
  | _, .rel (Sum.inr _) _ => true
  | _, _ => false

omit [L.IsRelational] in
/-- **The read leaves of a matrix**, in evaluation order. -/
def blkAtoms {n : ℕ}
    (mat : ((L.sum Language.order).sum B.lang).BoundedFormula Empty n) :
    List (((L.sum Language.order).sum B.lang).BoundedFormula Empty n) :=
  (qfAtoms mat).filter isBlkAtom

omit [L.IsRelational] in
theorem mem_qfAtoms_of_mem_blkAtoms {n : ℕ}
    {mat φ : ((L.sum Language.order).sum B.lang).BoundedFormula Empty n}
    (h : φ ∈ blkAtoms mat) : φ ∈ qfAtoms mat :=
  List.mem_of_mem_filter h

omit [L.IsRelational] in
theorem isBlkAtom_of_mem_blkAtoms {n : ℕ}
    {mat φ : ((L.sum Language.order).sum B.lang).BoundedFormula Empty n}
    (h : φ ∈ blkAtoms mat) : isBlkAtom φ = true :=
  List.of_mem_filter h

/-! ### The semantic reading -/

section Semantics

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **What an atom says**, at a block assignment and a valuation of the
prefix. -/
def BlkAtom.holds (ρ : B.Assignment A) {n : ℕ} (w : Fin n → A) :
    BlkAtom L B n → Prop
  | .eqA j₁ j₂ => w j₁ = w j₂
  | .baseA r ts => RelMap (M := A) r fun j => w (ts j)
  | .ordA j₁ j₂ => w j₁ ≤ w j₂
  | .blkA i ts => ρ i fun j => w (ts j)

/-- **The reading is correct**: a classified atom realizes at a valuation
of the prefix exactly as its kind says. -/
theorem realize_blkAtom (ρ : B.Assignment A) {n : ℕ}
    {φ : ((L.sum Language.order).sum B.lang).BoundedFormula Empty n}
    {κ : BlkAtom L B n} (h : blkAtom? φ = some κ) (w : Fin n → A) :
    (@BoundedFormula.Realize _ A
        (B.structure₁ (L := L.sum Language.order) ρ) _ _ φ default w ↔
      κ.holds ρ w) := by
  let inst := B.structure₁ (L := L.sum Language.order) ρ
  match φ with
  | .falsum => simp [blkAtom?] at h
  | .imp _ _ => simp [blkAtom?] at h
  | .all _ => simp [blkAtom?] at h
  | .equal t₁ t₂ =>
    obtain rfl : BlkAtom.eqA (L := L) (B := B) (matVar t₁) (matVar t₂) = κ :=
      Option.some.inj h
    change t₁.realize (Sum.elim default w) = t₂.realize (Sum.elim default w) ↔ _
    rw [realize_matVar, realize_matVar]
    exact Iff.rfl
  | .rel r ts =>
    obtain rfl : blkRelAtom r ts = κ := Option.some.inj h
    change RelMap r (fun i => (ts i).realize (Sum.elim default w)) ↔ _
    simp only [realize_matVar]
    rcases r with (e | o) | b
    · exact Iff.rfl
    · cases o
      exact Iff.rfl
    · exact Iff.rfl

/-- **A read leaf is a block atom**: the syntactic test and the classifier
agree, so an element loop's `r`-th trip has a relation variable, a copy and a
tuple of levels to read. -/
theorem exists_blkA_of_isBlkAtom {n : ℕ}
    {φ : ((L.sum Language.order).sum B.lang).BoundedFormula Empty n}
    (h : isBlkAtom φ = true) :
    ∃ (i : B.ι) (ts : Fin (B.arity i) → Fin n), blkAtom? φ = some (.blkA i ts) := by
  match φ with
  | .falsum => exact absurd h (by simp [isBlkAtom])
  | .imp _ _ => exact absurd h (by simp [isBlkAtom])
  | .all _ => exact absurd h (by simp [isBlkAtom])
  | .equal _ _ => exact absurd h (by simp [isBlkAtom])
  | .rel r ts =>
    rcases r with (r' | o) | b
    · exact absurd h (by simp [isBlkAtom])
    · cases o
      exact absurd h (by simp [isBlkAtom])
    · exact ⟨b.1, _, rfl⟩

/-- The converse test: a classified block atom passes the syntactic one. -/
theorem isBlkAtom_of_blkA {n : ℕ}
    {φ : ((L.sum Language.order).sum B.lang).BoundedFormula Empty n}
    {i : B.ι} {ts : Fin (B.arity i) → Fin n}
    (h : blkAtom? φ = some (.blkA i ts)) : isBlkAtom φ = true := by
  match φ with
  | .falsum => exact absurd h (by simp [blkAtom?])
  | .imp _ _ => exact absurd h (by simp [blkAtom?])
  | .all _ => exact absurd h (by simp [blkAtom?])
  | .equal _ _ => exact nomatch (Option.some.inj h)
  | .rel r ts' =>
    rcases r with (r' | o) | b
    · exact nomatch (Option.some.inj h)
    · cases o
      exact nomatch (Option.some.inj h)
    · rfl

/-- **The matrix through its classified atoms**: a quantifier-free matrix
realizes exactly as its Boolean function at the kinds' readings. -/
theorem realize_iff_qfValue_blkHolds {n : ℕ}
    {mat : ((L.sum Language.order).sum B.lang).BoundedFormula Empty n}
    (hqf : mat.IsQF) (ρ : B.Assignment A) (w : Fin n → A) :
    (@BoundedFormula.Realize _ A
        (B.structure₁ (L := L.sum Language.order) ρ) _ _ mat default w ↔
      qfValue mat fun a => (blkAtom? a).elim False (BlkAtom.holds ρ w)) := by
  let inst := B.structure₁ (L := L.sum Language.order) ρ
  refine (realize_qfValue hqf default w).trans (qfValue_congr _ _ _ fun a ha => ?_)
  obtain ⟨κ, hκ⟩ :=
    Option.isSome_iff_exists.mp (isSome_blkAtom?_of_mem_qfAtoms mat a ha)
  rw [hκ]
  exact realize_blkAtom ρ hκ w

end Semantics

end Draw

end DescriptiveComplexity
