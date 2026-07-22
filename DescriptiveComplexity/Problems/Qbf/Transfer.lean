/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qbf.Defs
import DescriptiveComplexity.SecondOrderMerge

/-!
# Transferring an alternating prefix from valuations to block assignments

The hardness proof for `DescriptiveComplexity.QBF` reduces a `Σₖ`-definable problem to a
quantified Boolean formula whose propositional variables encode the relation
variables of the `k` second-order blocks. Both sides are alternating
quantifications – `DescriptiveComplexity.altQuant` over truth assignments of the QBF
instance, `DescriptiveComplexity.altAssign` over the components of a merged block
assignment – so what is needed is a way to move between them block by block.

`DescriptiveComplexity.altQuant_iff_altAssign` does exactly that. It is parameterized by a
*reading* `DescriptiveComplexity.BlockRead`, which says how the relation assigned to each
merged relation variable is read off a truth assignment, and it needs only two
things: that the quantified predicates correspond under the reading, and that
the reading is surjective at every block (`DescriptiveComplexity.ReadSurj`) – the
propositional variables of a block are free enough to realize any relation.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A A' : Type}

/-! ### Which block a merged relation variable belongs to -/

/-- The block a relation variable of the merged block comes from. -/
def blockOf : ∀ (Bs : List SOBlock), (mergeBlocks Bs).ι → Fin Bs.length
  | [], i => Empty.elim (i : Empty)
  | _ :: _, Sum.inl _ => 0
  | _ :: Bs, Sum.inr i => (blockOf Bs i).succ

/-! ### Reading block assignments off a truth assignment -/

/-- A reading of relations off a truth assignment of the propositional
variables: `rd i ν` is the relation that the valuation `ν` assigns to the
merged relation variable `i`. -/
abbrev BlockRead (A A' : Type) (Bs : List SOBlock) : Type :=
  ∀ i : (mergeBlocks Bs).ι, (A' → Prop) → (Fin ((mergeBlocks Bs).arity i) → A) → Prop

/-- The merged assignment read off a tuple of truth assignments: each relation
variable is read from the truth assignment of the block it belongs to. -/
def readAll : ∀ (Bs : List SOBlock), BlockRead A A' Bs →
    (Fin Bs.length → A' → Prop) → (mergeBlocks Bs).Assignment A
  | [], _, _ => nilAssign A
  | _ :: Bs, rd, νs =>
      consAssign (fun i a => rd (Sum.inl i) (νs 0) a)
        (readAll Bs (fun i => rd (Sum.inr i)) fun j => νs j.succ)

theorem readAll_cons (B : SOBlock) (Bs : List SOBlock) (rd : BlockRead A A' (B :: Bs))
    (ν : A' → Prop) (νs : Fin Bs.length → A' → Prop) :
    readAll (B :: Bs) rd (Fin.cons ν νs) =
      consAssign (fun i a => rd (Sum.inl i) ν a)
        (readAll Bs (fun i => rd (Sum.inr i)) νs) := by
  simp only [readAll, Fin.cons_zero, Fin.cons_succ]
  rfl

/-- The reading is surjective at every block: the propositional variables of a
block can realize an arbitrary relation. -/
def ReadSurj : ∀ (Bs : List SOBlock), BlockRead A A' Bs → Prop
  | [], _ => True
  | B :: Bs, rd =>
      (∀ ρ : B.Assignment A, ∃ ν : A' → Prop, (fun i a => rd (Sum.inl i) ν a) = ρ) ∧
      ReadSurj Bs fun i => rd (Sum.inr i)

/-! ### Reading an enlarged prefix

When the innermost block has been enlarged by a block `Gt` of auxiliary
variables (`DescriptiveComplexity.consLast`), a reading built from
`DescriptiveComplexity.splitIdx` decomposes along `DescriptiveComplexity.combineLast`: the
original relation variables are read from the truth assignment of their own
block, the auxiliary ones from the innermost. The index map
`DescriptiveComplexity.markC` says which, and is stated at
`Fin (consLast Gt B Bs).length` – the type `readAll` uses – so that the
induction needs no transport along
`DescriptiveComplexity.consLast_length`. -/

/-- Which quantifier block of the enlarged prefix a variable belongs to: its
own block for a relation variable of the original prefix, the innermost one
for a variable of the extra block. -/
def markC (Gt : SOBlock) : ∀ (B : SOBlock) (Bs : List SOBlock),
    (mergeBlocks (B :: Bs)).ι ⊕ Gt.ι → Fin (consLast Gt B Bs).length
  | _, [], Sum.inl (Sum.inl _) => 0
  | _, [], Sum.inl (Sum.inr e) => Empty.elim (e : Empty)
  | _, [], Sum.inr _ => 0
  | _, _ :: _, Sum.inl (Sum.inl _) => 0
  | _, B' :: Bs, Sum.inl (Sum.inr y) => (markC Gt B' Bs (Sum.inl y)).succ
  | _, B' :: Bs, Sum.inr j => (markC Gt B' Bs (Sum.inr j)).succ

/-- **The reading of an enlarged prefix splits**: reading each variable from
the truth assignment of the block `markC` assigns it is the same as assembling
the original assignment and the auxiliary one with
`DescriptiveComplexity.combineLast`. -/
theorem readAll_consLast (Gt : SOBlock) {D : ℕ}
    (pdf : ∀ {m : ℕ}, (Fin m → A) → (Fin D → A)) :
    ∀ (B : SOBlock) (Bs : List SOBlock)
      (el : ((mergeBlocks (B :: Bs)).ι ⊕ Gt.ι) → (Fin D → A) → A')
      (νs : Fin (consLast Gt B Bs).length → A' → Prop),
      readAll (consLast Gt B Bs)
          (fun i ν a => ν (el (splitIdx Gt B Bs i) (pdf a))) νs =
        combineLast Gt B Bs
          (fun i' a => νs (markC Gt B Bs (Sum.inl i')) (el (Sum.inl i') (pdf a)))
          (fun j x => νs (markC Gt B Bs (Sum.inr j)) (el (Sum.inr j) (pdf x))) := by
  intro B Bs
  induction Bs generalizing B with
  | nil =>
    intro el νs
    funext i
    rcases i with i | e
    · rcases i with i | j <;> rfl
    · exact Empty.elim (e : Empty)
  | cons B' Bs ih =>
    intro el νs
    funext i
    rcases i with i | i
    · rfl
    · exact congrFun
        (ih B' (fun z => el (Sum.elim (fun x => Sum.inl (Sum.inr x)) Sum.inr z))
          fun j => νs j.succ) i

/-- A reading built from an injective tagging is surjective at every block: a
truth assignment realizing a prescribed relation is obtained by reading the
tag back off each propositional variable. -/
theorem readSurj_consLast (Gt : SOBlock) {D : ℕ}
    (pdf : ∀ {m : ℕ}, (Fin m → A) → (Fin D → A)) :
    ∀ (B : SOBlock) (Bs : List SOBlock)
      (el : ((mergeBlocks (B :: Bs)).ι ⊕ Gt.ι) → (Fin D → A) → A'),
      (∀ z z' u u', el z u = el z' u' → z = z' ∧ u = u') →
      (∀ (i : (mergeBlocks (consLast Gt B Bs)).ι)
        (a a' : Fin ((mergeBlocks (consLast Gt B Bs)).arity i) → A), pdf a = pdf a' → a = a') →
      ReadSurj (consLast Gt B Bs) fun i ν a => ν (el (splitIdx Gt B Bs i) (pdf a)) := by
  intro B Bs
  induction Bs generalizing B with
  | nil =>
    intro el hel hpdf
    refine ⟨fun ρ => ⟨fun y =>
      (∃ (i : B.ι) (a : Fin (B.arity i) → A),
          y = el (Sum.inl (Sum.inl i)) (pdf a) ∧ ρ (Sum.inl i) a) ∨
      (∃ (j : Gt.ι) (a : Fin (Gt.arity j) → A),
          y = el (Sum.inr j) (pdf a) ∧ ρ (Sum.inr j) a), ?_⟩, trivial⟩
    funext i
    rcases i with i | j
    · funext a
      refine propext ⟨?_, fun h => Or.inl ⟨i, a, rfl, h⟩⟩
      rintro (⟨i', a', heq, h'⟩ | ⟨j', a', heq, h'⟩)
      · obtain ⟨hz, hu⟩ := hel _ _ _ _ heq
        simp only [splitIdx] at hz
        obtain rfl : i = i' := Sum.inl.inj (Sum.inl.inj hz)
        obtain rfl : a = a' := hpdf (Sum.inl (Sum.inl i)) a a' hu
        exact h'
      · exact absurd (hel _ _ _ _ heq).1 (by simp [splitIdx])
    · funext a
      refine propext ⟨?_, fun h => Or.inr ⟨j, a, rfl, h⟩⟩
      rintro (⟨i', a', heq, h'⟩ | ⟨j', a', heq, h'⟩)
      · exact absurd (hel _ _ _ _ heq).1 (by simp [splitIdx])
      · obtain ⟨hz, hu⟩ := hel _ _ _ _ heq
        simp only [splitIdx] at hz
        obtain rfl : j = j' := Sum.inr.inj hz
        obtain rfl : a = a' := hpdf (Sum.inl (Sum.inr j)) a a' hu
        exact h'
  | cons B' Bs ih =>
    intro el hel hpdf
    refine ⟨fun ρ => ⟨fun y => ∃ (i : B.ι) (a : Fin (B.arity i) → A),
      y = el (Sum.inl (Sum.inl i)) (pdf a) ∧ ρ i a, ?_⟩, ?_⟩
    · funext i a
      refine propext ⟨?_, fun h => ⟨i, a, rfl, h⟩⟩
      rintro ⟨i', a', heq, h'⟩
      obtain ⟨hz, hu⟩ := hel _ _ _ _ heq
      simp only [splitIdx] at hz
      obtain rfl : i = i' := Sum.inl.inj (Sum.inl.inj hz)
      obtain rfl : a = a' := hpdf (Sum.inl i) a a' hu
      exact h'
    · refine ih B' (fun z => el (Sum.elim (fun x => Sum.inl (Sum.inr x)) Sum.inr z))
        (fun z z' u u' h => ?_) fun i => hpdf (Sum.inr i)
      obtain ⟨hz, hu⟩ := hel _ _ _ _ h
      refine ⟨?_, hu⟩
      rcases z with z | z <;> rcases z' with z' | z' <;>
        simp only [Sum.elim_inl, Sum.elim_inr] at hz
      · exact congrArg Sum.inl (Sum.inr.inj (Sum.inl.inj hz))
      · exact absurd hz (by simp)
      · exact absurd hz (by simp)
      · exact congrArg Sum.inr (Sum.inr.inj hz)

/-! ### The transfer -/

/-- **Transfer of an alternating prefix**: alternating quantification over
truth assignments of the propositional variables is alternating quantification
over the components of the merged block assignment they encode. -/
theorem altQuant_iff_altAssign :
    ∀ (Bs : List SOBlock) (rd : BlockRead A A' Bs), ReadSurj Bs rd →
      ∀ (F : (Fin Bs.length → A' → Prop) → Prop)
        (G : (mergeBlocks Bs).Assignment A → Prop),
        (∀ νs, F νs ↔ G (readAll Bs rd νs)) →
        ∀ pol : Bool, altQuant A' Bs.length F pol ↔ altAssign A Bs G pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro rd _ F G hF pol
    refine (hF Fin.elim0).trans (iff_of_eq (congrArg G ?_))
    funext i
    exact Empty.elim (i : Empty)
  | cons B Bs ih =>
    intro rd hsurj F G hF pol
    have key : ∀ ν : A' → Prop,
        altQuant A' Bs.length (fun νs => F (Fin.cons ν νs)) (!pol) ↔
          altAssign A Bs (fun μ => G (consAssign (fun i a => rd (Sum.inl i) ν a) μ))
            (!pol) := by
      intro ν
      refine ih (fun i => rd (Sum.inr i)) hsurj.2 _ _ (fun νs => ?_) (!pol)
      refine (hF (Fin.cons ν νs)).trans (iff_of_eq (congrArg G ?_))
      exact readAll_cons B Bs rd ν νs
    cases pol with
    | true =>
      constructor
      · rintro ⟨ν, hν⟩
        exact ⟨_, (key ν).mp hν⟩
      · rintro ⟨ρ, hρ⟩
        obtain ⟨ν, hν⟩ := hsurj.1 ρ
        exact ⟨ν, (key ν).mpr (hν ▸ hρ)⟩
    | false =>
      constructor
      · intro h ρ
        obtain ⟨ν, hν⟩ := hsurj.1 ρ
        exact hν ▸ (key ν).mp (h ν)
      · intro h ν
        exact (key ν).mpr (h _)

end DescriptiveComplexity
