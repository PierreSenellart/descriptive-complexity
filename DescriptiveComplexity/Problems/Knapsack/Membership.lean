/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Knapsack.Chain
import DescriptiveComplexity.SecondOrder

/-!
# Knapsack is in NP

The `Σ₁` definition of `DescriptiveComplexity.Knapsack`. Verifying that a set of
binary weights sums to the target is the one place in the catalog where the
certificate has to carry *arithmetic*: the guess is

* `sel`, the chosen items;
* `psum i p`, the bits of the running total over the chosen items up to `i`;
* `carry i p`, the carries of the addition that appends `i` to that total,

and the kernel checks, first-order, that each step is a ripple-carry addition
– every bit the exclusive or of the three inputs, every carry their majority –
with no carry into the lowest position and none out of the highest. That the
chain really computes the sum is `DescriptiveComplexity.binNum_ripple`, and that a
chain exists whenever the sum fits is `DescriptiveComplexity.exists_ripple`
(`DescriptiveComplexity.Numbers.BinRel`).

Walking the items in order is what makes a *single* relation `psum` enough, and
it is why the vocabulary orders the items and not only the bit positions.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block of the `Σ₁` definition of Knapsack: the
chosen items (unary), the running partial sums and the carries (binary, an
item and a bit position). -/
def knapsackGuessBlock : SOBlock where
  ι := Option Bool
  arity := fun i => match i with
    | none => 1
    | some _ => 2

/-- The symbol of the chosen-items relation variable. -/
def ksSelRel : knapsackGuessBlock.lang.Relations 1 := ⟨none, rfl⟩

/-- The symbol of the partial-sum relation variable. -/
def ksPSRel : knapsackGuessBlock.lang.Relations 2 := ⟨some true, rfl⟩

/-- The symbol of the carry relation variable. -/
def ksCarryRel : knapsackGuessBlock.lang.Relations 2 := ⟨some false, rfl⟩

/-- The vocabulary of the kernel. -/
abbrev ksSOLang : Language := Language.binWeights.sum knapsackGuessBlock.lang

/-- The item symbol in the kernel's vocabulary. -/
abbrev ksItemSym : ksSOLang.Relations 1 := Sum.inl bwItem

/-- The position symbol in the kernel's vocabulary. -/
abbrev ksPosnSym : ksSOLang.Relations 1 := Sum.inl bwPosn

/-- The bit symbol in the kernel's vocabulary. -/
abbrev ksBitSym : ksSOLang.Relations 2 := Sum.inl bwBit

/-- The target symbol in the kernel's vocabulary. -/
abbrev ksTgtSym : ksSOLang.Relations 1 := Sum.inl bwTgt

/-- The order symbol in the kernel's vocabulary. -/
abbrev ksLeSym : ksSOLang.Relations 2 := Sum.inl bwLe

/-- The chosen-items symbol in the kernel's vocabulary. -/
abbrev ksSelSym : ksSOLang.Relations 1 := Sum.inr ksSelRel

/-- The partial-sum symbol in the kernel's vocabulary. -/
abbrev ksPSSym : ksSOLang.Relations 2 := Sum.inr ksPSRel

/-- The carry symbol in the kernel's vocabulary. -/
abbrev ksCarrySym : ksSOLang.Relations 2 := Sum.inr ksCarryRel

/-! ### Formula builders -/

section Builders

variable {α : Type}

/-- `x` is an item, as a formula. -/
def kItemF (x : α) : ksSOLang.Formula α := Relations.formula₁ ksItemSym (Term.var x)

/-- `x` is a bit position, as a formula. -/
def kPosnF (x : α) : ksSOLang.Formula α := Relations.formula₁ ksPosnSym (Term.var x)

/-- The weight of `i` has bit 1 at `p`, as a formula. -/
def kBitF (i p : α) : ksSOLang.Formula α :=
  Relations.formula₂ ksBitSym (Term.var i) (Term.var p)

/-- The target has bit 1 at `p`, as a formula. -/
def kTgtF (p : α) : ksSOLang.Formula α := Relations.formula₁ ksTgtSym (Term.var p)

/-- `x ≤ y`, as a formula. -/
def kLeF (x y : α) : ksSOLang.Formula α :=
  Relations.formula₂ ksLeSym (Term.var x) (Term.var y)

/-- `x` is chosen, as a formula. -/
def kSelF (x : α) : ksSOLang.Formula α := Relations.formula₁ ksSelSym (Term.var x)

/-- Bit `p` of the running total at `i`, as a formula. -/
def kPSF (i p : α) : ksSOLang.Formula α :=
  Relations.formula₂ ksPSSym (Term.var i) (Term.var p)

/-- The carry at `p` of the step appending `i`, as a formula. -/
def kCarryF (i p : α) : ksSOLang.Formula α :=
  Relations.formula₂ ksCarrySym (Term.var i) (Term.var p)

/-- `x = y`, as a formula. -/
def kEqF (x y : α) : ksSOLang.Formula α := Term.equal (Term.var x) (Term.var y)

/-- The bit that the item `i` contributes at `p`: its weight's bit, if it is
chosen. -/
def kAddF (i p : α) : ksSOLang.Formula α := kSelF i ⊓ kBitF i p

/-- The exclusive or of three formulas, as `x ↔ (y ↔ z)`. -/
def kXor3F (x y z : ksSOLang.Formula α) : ksSOLang.Formula α := x.iff (y.iff z)

/-- The majority of three formulas. -/
def kMaj3F (x y z : ksSOLang.Formula α) : ksSOLang.Formula α :=
  (x ⊓ y) ⊔ ((x ⊓ z) ⊔ (y ⊓ z))

/-- `i` is the first item, as a formula. -/
noncomputable def kMinItemF (i : α) : ksSOLang.Formula α :=
  kItemF i ⊓ Formula.iAlls Unit
    ((kItemF (Sum.inr ())).imp (kLeF (Sum.inl i) (Sum.inr ())))

/-- `i` is the last item, as a formula. -/
noncomputable def kMaxItemF (i : α) : ksSOLang.Formula α :=
  kItemF i ⊓ Formula.iAlls Unit
    ((kItemF (Sum.inr ())).imp (kLeF (Sum.inr ()) (Sum.inl i)))

/-- `j` is the item right after `i`, as a formula. -/
noncomputable def kSuccItemF (i j : α) : ksSOLang.Formula α :=
  kItemF i ⊓ (kItemF j ⊓ (kLeF i j ⊓ (∼(kEqF i j) ⊓
    Formula.iAlls Unit
      ((kItemF (Sum.inr ())).imp ((kLeF (Sum.inl i) (Sum.inr ())).imp
        ((kLeF (Sum.inr ()) (Sum.inl j)).imp
          (kEqF (Sum.inr ()) (Sum.inl i) ⊔ kEqF (Sum.inr ()) (Sum.inl j))))))))

/-- `p` is the lowest position, as a formula. -/
noncomputable def kMinPosnF (p : α) : ksSOLang.Formula α :=
  kPosnF p ⊓ Formula.iAlls Unit
    ((kPosnF (Sum.inr ())).imp (kLeF (Sum.inl p) (Sum.inr ())))

/-- `p` is the highest position, as a formula. -/
noncomputable def kMaxPosnF (p : α) : ksSOLang.Formula α :=
  kPosnF p ⊓ Formula.iAlls Unit
    ((kPosnF (Sum.inr ())).imp (kLeF (Sum.inr ()) (Sum.inl p)))

/-- `q` is the position right above `p`, as a formula. -/
noncomputable def kSuccPosnF (p q : α) : ksSOLang.Formula α :=
  kPosnF p ⊓ (kPosnF q ⊓ (kLeF p q ⊓ (∼(kEqF p q) ⊓
    Formula.iAlls Unit
      ((kPosnF (Sum.inr ())).imp ((kLeF (Sum.inl p) (Sum.inr ())).imp
        ((kLeF (Sum.inr ()) (Sum.inl q)).imp
          (kEqF (Sum.inr ()) (Sum.inl p) ⊔ kEqF (Sum.inr ()) (Sum.inl q))))))))

end Builders

/-! ### The clauses -/

/-- Kernel clause: the order is reflexive. -/
private noncomputable def ksReflClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 1) (kLeF (Sum.inr 0) (Sum.inr 0))

/-- Kernel clause: the order is transitive. -/
private noncomputable def ksTransClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((kLeF (Sum.inr 0) (Sum.inr 1) ⊓ kLeF (Sum.inr 1) (Sum.inr 2)).imp
      (kLeF (Sum.inr 0) (Sum.inr 2)))

/-- Kernel clause: the order is antisymmetric. -/
private noncomputable def ksAntisymmClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    ((kLeF (Sum.inr 0) (Sum.inr 1) ⊓ kLeF (Sum.inr 1) (Sum.inr 0)).imp
      (kEqF (Sum.inr 0) (Sum.inr 1)))

/-- Kernel clause: the order is total. -/
private noncomputable def ksTotalClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 2) (kLeF (Sum.inr 0) (Sum.inr 1) ⊔ kLeF (Sum.inr 1) (Sum.inr 0))

/-- Kernel clause: only items are chosen. -/
private noncomputable def ksSelClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 1) ((kSelF (Sum.inr 0)).imp (kItemF (Sum.inr 0)))

/-- Kernel clause: at the first item the running total is that item's
contribution. -/
private noncomputable def ksBaseClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    ((kMinItemF (Sum.inr 0) ⊓ kPosnF (Sum.inr 1)).imp
      ((kPSF (Sum.inr 0) (Sum.inr 1)).iff (kAddF (Sum.inr 0) (Sum.inr 1))))

/-- Kernel clause: each step adds a bit. -/
private noncomputable def ksSumClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((kSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ kPosnF (Sum.inr 2)).imp
      ((kPSF (Sum.inr 1) (Sum.inr 2)).iff
        (kXor3F (kPSF (Sum.inr 0) (Sum.inr 2)) (kAddF (Sum.inr 1) (Sum.inr 2))
          (kCarryF (Sum.inr 1) (Sum.inr 2)))))

/-- Kernel clause: each step propagates its carry. -/
private noncomputable def ksCarryClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((kSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ kSuccPosnF (Sum.inr 2) (Sum.inr 3)).imp
      ((kCarryF (Sum.inr 1) (Sum.inr 3)).iff
        (kMaj3F (kPSF (Sum.inr 0) (Sum.inr 2)) (kAddF (Sum.inr 1) (Sum.inr 2))
          (kCarryF (Sum.inr 1) (Sum.inr 2)))))

/-- Kernel clause: nothing is carried into the lowest position. -/
private noncomputable def ksBottomClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((kSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ kMinPosnF (Sum.inr 2)).imp
      ∼(kCarryF (Sum.inr 1) (Sum.inr 2)))

/-- Kernel clause: nothing is carried out of the highest position. -/
private noncomputable def ksTopClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((kSuccItemF (Sum.inr 0) (Sum.inr 1) ⊓ kMaxPosnF (Sum.inr 2)).imp
      ∼(kMaj3F (kPSF (Sum.inr 0) (Sum.inr 2)) (kAddF (Sum.inr 1) (Sum.inr 2))
        (kCarryF (Sum.inr 1) (Sum.inr 2))))

/-- Kernel clause: at the last item the running total is the target. -/
private noncomputable def ksFinalClause : ksSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    ((kMaxItemF (Sum.inr 0) ⊓ kPosnF (Sum.inr 1)).imp
      ((kPSF (Sum.inr 0) (Sum.inr 1)).iff (kTgtF (Sum.inr 1))))

/-- Kernel clause: with no item at all, the target must be zero. -/
private noncomputable def ksEmptyClause : ksSOLang.Sentence :=
  (Formula.iAlls (Fin 1) ∼(kItemF (Sum.inr 0))).imp
    (Formula.iAlls (Fin 1) ((kPosnF (Sum.inr 0)).imp ∼(kTgtF (Sum.inr 0))))

/-- The first-order kernel of the `Σ₁` definition of Knapsack. -/
noncomputable def knapsackKernel : ksSOLang.Sentence :=
  (ksReflClause ⊓ (ksTransClause ⊓ (ksAntisymmClause ⊓ ksTotalClause))) ⊓
    (ksSelClause ⊓ (ksBaseClause ⊓ (ksSumClause ⊓ (ksCarryClause ⊓
      (ksBottomClause ⊓ (ksTopClause ⊓ (ksFinalClause ⊓ ksEmptyClause)))))))

/-! ### Realization -/

section Realize

variable {A : Type} [Language.binWeights.Structure A] (ρ : knapsackGuessBlock.Assignment A)

/-- The chosen items, read off an assignment of the block. -/
private def Sel (i : A) : Prop := ρ none ![i]

/-- The running total, read off an assignment of the block. -/
private def PSum (i p : A) : Prop := ρ (some true) ![i, p]

/-- The carries, read off an assignment of the block. -/
private def Cy (i p : A) : Prop := ρ (some false) ![i, p]

/-- The bit that an item contributes. -/
private def Add (i p : A) : Prop := Sel ρ i ∧ BWBit i p

private theorem realize_knapsackKernel :
    (@Sentence.Realize ksSOLang A
        (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ)) knapsackKernel) ↔
      IsLinOrd (BWLe (A := A)) ∧
        (∀ i : A, Sel ρ i → BWItem i) ∧
        (∀ i p : A, MinPos BWLe BWItem i → BWPosn p →
          (PSum ρ i p ↔ Add ρ i p)) ∧
        (∀ i j p : A, SuccPos BWLe BWItem i j → BWPosn p →
          (PSum ρ j p ↔ (PSum ρ i p ↔ (Add ρ j p ↔ Cy ρ j p)))) ∧
        (∀ i j p q : A, SuccPos BWLe BWItem i j → SuccPos BWLe BWPosn p q →
          (Cy ρ j q ↔ maj (PSum ρ i p) (Add ρ j p) (Cy ρ j p))) ∧
        (∀ i j p : A, SuccPos BWLe BWItem i j → MinPos BWLe BWPosn p → ¬Cy ρ j p) ∧
        (∀ i j p : A, SuccPos BWLe BWItem i j → MaxPos BWLe BWPosn p →
          ¬maj (PSum ρ i p) (Add ρ j p) (Cy ρ j p)) ∧
        (∀ i p : A, MaxPos BWLe BWItem i → BWPosn p → (PSum ρ i p ↔ BWTgt p)) ∧
        ((∀ i : A, ¬BWItem i) → ∀ p : A, BWPosn p → ¬BWTgt p) := by
  letI := knapsackGuessBlock.structure ρ
  have hsubS : ∀ w : Fin 1 → A,
      RelMap (L := ksSOLang) (M := A) ksSelSym w ↔ ρ none w := fun _ => Iff.rfl
  have hsubP : ∀ w : Fin 2 → A,
      RelMap (L := ksSOLang) (M := A) ksPSSym w ↔ ρ (some true) w := fun _ => Iff.rfl
  have hsubC : ∀ w : Fin 2 → A,
      RelMap (L := ksSOLang) (M := A) ksCarrySym w ↔ ρ (some false) w := fun _ => Iff.rfl
  rw [knapsackKernel]
  simp only [ksReflClause, ksTransClause, ksAntisymmClause, ksTotalClause, ksSelClause,
    ksBaseClause, ksSumClause, ksCarryClause, ksBottomClause, ksTopClause, ksFinalClause,
    ksEmptyClause, kItemF, kPosnF, kBitF, kTgtF, kLeF, kSelF, kPSF, kCarryF, kEqF, kAddF,
    kXor3F, kMaj3F, kMinItemF, kMaxItemF, kSuccItemF, kMinPosnF, kMaxPosnF, kSuccPosnF,
    Sentence.Realize, Formula.realize_inf, Formula.realize_sup, Formula.realize_imp,
    Formula.realize_iff, Formula.realize_not, Formula.realize_iAlls, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr,
    Sum.elim_inl, Language.relMap_sumInl, hsubS, hsubP, hsubC]
  constructor
  · rintro ⟨⟨hrefl, htrans, hanti, htot⟩, hsel, hbase, hsum, hcarry, hbot, htop, hfin, hemp⟩
    have hmin : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Unit → A, P (y ()) → BWLe x (y ())) → MinPos BWLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hmax : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Unit → A, P (y ()) → BWLe (y ()) x) → MaxPos BWLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hsucc : ∀ (P : A → Prop) (x y : A), SuccPos BWLe P x y →
        (P x ∧ (P y ∧ (BWLe x y ∧ (¬x = y ∧ ∀ r : Unit → A,
          P (r ()) → BWLe x (r ()) → BWLe (r ()) y → r () = x ∨ r () = y)))) :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (r ()) hr h1 h2⟩
    refine ⟨⟨fun a => hrefl (fun _ => a), fun a b c hab hbc => htrans ![a, b, c] ⟨hab, hbc⟩,
      fun a b hab hba => hanti ![a, b] ⟨hab, hba⟩, fun a b => htot ![a, b]⟩,
      fun i hi => hsel (fun _ => i) hi,
      fun i p hi hp => hbase ![i, p] ⟨⟨hi.1, fun j hj => hi.2 (j ()) hj⟩, hp⟩,
      fun i j p hij hp => hsum ![i, j, p] ⟨hsucc _ i j hij, hp⟩,
      fun i j p q hij hpq => hcarry ![i, j, p, q] ⟨hsucc _ i j hij, hsucc _ p q hpq⟩,
      fun i j p hij hp => hbot ![i, j, p]
        ⟨hsucc _ i j hij, ⟨hp.1, fun q hq => hp.2 (q ()) hq⟩⟩,
      fun i j p hij hp => htop ![i, j, p]
        ⟨hsucc _ i j hij, ⟨hp.1, fun q hq => hp.2 (q ()) hq⟩⟩,
      fun i p hi hp => hfin ![i, p] ⟨⟨hi.1, fun j hj => hi.2 (j ()) hj⟩, hp⟩,
      fun hno p hp => hemp (fun i => hno (i 0)) (fun _ => p) hp⟩
  · rintro ⟨⟨hrefl, htrans, hanti, htot⟩, hsel, hbase, hsum, hcarry, hbot, htop, hfin, hemp⟩
    have hsucc : ∀ (P : A → Prop) (x y : A),
        (P x ∧ (P y ∧ (BWLe x y ∧ (¬x = y ∧ ∀ r : Unit → A,
          P (r ()) → BWLe x (r ()) → BWLe (r ()) y → r () = x ∨ r () = y)))) →
        SuccPos BWLe P x y :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (fun _ => r) hr h1 h2⟩
    refine ⟨⟨fun i => hrefl (i 0), fun i hi => htrans (i 0) (i 1) (i 2) hi.1 hi.2,
      fun i hi => hanti (i 0) (i 1) hi.1 hi.2, fun i => htot (i 0) (i 1)⟩,
      fun i hi => hsel (i 0) hi,
      fun i hi => hbase (i 0) (i 1) ⟨hi.1.1, fun j hj => hi.1.2 (fun _ => j) hj⟩ hi.2,
      fun i hi => hsum (i 0) (i 1) (i 2) (hsucc _ _ _ hi.1) hi.2,
      fun i hi => hcarry (i 0) (i 1) (i 2) (i 3) (hsucc _ _ _ hi.1) (hsucc _ _ _ hi.2),
      fun i hi => hbot (i 0) (i 1) (i 2) (hsucc _ _ _ hi.1)
        ⟨hi.2.1, fun q hq => hi.2.2 (fun _ => q) hq⟩,
      fun i hi => htop (i 0) (i 1) (i 2) (hsucc _ _ _ hi.1)
        ⟨hi.2.1, fun q hq => hi.2.2 (fun _ => q) hq⟩,
      fun i hi => hfin (i 0) (i 1) ⟨hi.1.1, fun j hj => hi.1.2 (fun _ => j) hj⟩ hi.2,
      fun hno i hi => hemp (fun j => hno (fun _ => j)) (i 0) hi⟩

end Realize

/-! ### Membership -/

open Classical in
/-- **Knapsack is `Σ₁`-definable**: guess the chosen items, the running totals
and the carries, and check first-order that each step is a ripple-carry
addition whose last total is the target. Since NP is defined as
`Σ₁`-definability, this is the membership half of the NP-completeness of
Knapsack. -/
theorem knapsack_sigmaSODefinable : SigmaSODefinable 1 Knapsack := by
  refine ⟨[knapsackGuessBlock], rfl, knapsackKernel, ?_⟩
  intro A _ _ _
  constructor
  · -- a solution yields a certificate: the walk of `exists_chain`
    rintro ⟨hfin, hlin, S, hSitem, hsumeq⟩
    have htot : (∑ᶠ j ∈ {j : A | S j}, binNum BWLe BWPosn (BWBit j)) <
        2 ^ ({p : A | BWPosn p} : Set A).ncard := by
      rw [show (∑ᶠ j ∈ {j : A | S j}, binNum BWLe BWPosn (BWBit j)) =
        ∑ᶠ j ∈ {j : A | S j}, BWWeight j from rfl, hsumeq, BWTarget]
      exact binNum_lt_two_pow hlin _ BWPosn rfl BWTgt
    obtain ⟨PS, Cy, hchain⟩ := exists_chain (wt := BWBit) hlin hlin hSitem htot
    refine ⟨fun idx => match idx with
      | none => fun w : Fin 1 → A => S (w 0)
      | some true => fun w : Fin 2 → A => PS (w 0) (w 1)
      | some false => fun w : Fin 2 → A => Cy (w 0) (w 1), ?_⟩
    refine (realize_knapsackKernel _).mpr ⟨hlin, hSitem, hchain.1, hchain.2.1,
      hchain.2.2.1, hchain.2.2.2.1, hchain.2.2.2.2, ?_, ?_⟩
    · -- at the last item the running total is the target
      intro i p hi hp
      refine binNum_inj_on hlin _ BWPosn rfl (PS i) BWTgt ?_ p hp
      rw [chain_sound hlin hlin hSitem hchain i hi.1, partSum_max hSitem hi]
      rw [show (∑ᶠ j ∈ {j : A | S j}, binNum BWLe BWPosn (BWBit j)) =
        ∑ᶠ j ∈ {j : A | S j}, BWWeight j from rfl, hsumeq, BWTarget]
    · -- with no items the target must vanish
      intro hno p hp
      have hSempty : {j : A | S j} = (∅ : Set A) := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hj => hno j (hSitem j hj)
      have hzero : binNum (BWLe (A := A)) BWPosn BWTgt = 0 := by
        have htarget : BWTarget A = 0 := by
          rw [← hsumeq, hSempty, finsum_mem_empty]
        exact htarget
      have := binNum_inj_on hlin _ BWPosn rfl BWTgt (fun _ => False)
        (by rw [hzero, binNum_bot]) p hp
      exact this.mp
  · -- a certificate yields a solution: the walk is sound
    rintro ⟨ρ, hρ⟩
    obtain ⟨hlin, hsel, hbase, hstepsum, hstepcarry, hstepbot, hsteptop, hfinal, hempty⟩ :=
      (realize_knapsackKernel ρ).mp hρ
    have hchain : IsChain BWLe BWItem BWLe BWPosn (Sel ρ) BWBit (PSum ρ) (Cy ρ) :=
      ⟨hbase, hstepsum, hstepcarry, hstepbot, hsteptop⟩
    refine ⟨‹Finite A›, hlin, Sel ρ, hsel, ?_⟩
    by_cases hitems : ∃ i : A, BWItem i
    · obtain ⟨imax, himax⟩ := exists_maxPos hlin hitems
      have h1 := chain_sound hlin hlin hsel hchain imax himax.1
      have h2 : binNum BWLe BWPosn (PSum ρ imax) = BWTarget A :=
        binNum_congr_on fun p hp => hfinal imax p himax hp
      rw [show (∑ᶠ j ∈ {j : A | Sel ρ j}, BWWeight j) =
        ∑ᶠ j ∈ {j : A | Sel ρ j}, binNum BWLe BWPosn (BWBit j) from rfl,
        ← partSum_max hsel himax, ← h1, h2]
    · have hno : ∀ i, ¬BWItem i := fun i hi => hitems ⟨i, hi⟩
      have hSempty : {i : A | Sel ρ i} = (∅ : Set A) := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hi => hno i (hsel i hi)
      have htgt : {p : A | BWPosn p ∧ BWTgt p} = (∅ : Set A) := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hempty hno p h.1 h.2
      rw [hSempty, finsum_mem_empty, BWTarget, binNum, htgt, finsum_mem_empty]

end SigmaOne

end DescriptiveComplexity
