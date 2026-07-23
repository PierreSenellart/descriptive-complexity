/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ZeroOneIP.Defs
import DescriptiveComplexity.Problems.Knapsack.Chain
import DescriptiveComplexity.SecondOrder

/-!
# 0-1 integer programming is in NP

The certificate guesses the `0-1` vector and, for **each row**, a ripple-carry
walk along the columns:

* `x j`, the columns set to `1`;
* `ps r j p`, the bits of the running total of the row `r` over the chosen
  columns up to `j`;
* `cy r j p`, the carries of the step appending `j` to that total,

and the kernel asks that each row's walk be a ripple-carry addition ending on
that row's right-hand side. It is Knapsack's certificate
(`DescriptiveComplexity.Problems.Knapsack.Membership`) with a row argument
threaded through the two arithmetic relations and a guard `row r` in front of
every clause: the rows do not interact, so the walks are independent and the
semantic work is `DescriptiveComplexity.chain_sound` and
`DescriptiveComplexity.exists_chain` (`DescriptiveComplexity.Problems.Knapsack.Chain`)
applied once per row – the reason those two are stated over an arbitrary walk
order and item predicate rather than over one vocabulary.

Unlike Partition, the walks run on the *instance's own* positions: each row's
total is its right-hand side, which is written there, so it fits.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block of the `Σ₁` definition of 0-1 integer
programming: the columns set to `1` (unary), and the running partial sums and
the carries (ternary: a row, a column and a bit position). -/
def zeroOneIPGuessBlock : SOBlock where
  ι := Option Bool
  arity := fun i => match i with
    | none => 1
    | some _ => 3

/-- The symbol of the chosen-columns relation variable. -/
def zoXRel : zeroOneIPGuessBlock.lang.Relations 1 := ⟨none, rfl⟩

/-- The symbol of the partial-sum relation variable. -/
def zoPSRel : zeroOneIPGuessBlock.lang.Relations 3 := ⟨some true, rfl⟩

/-- The symbol of the carry relation variable. -/
def zoCyRel : zeroOneIPGuessBlock.lang.Relations 3 := ⟨some false, rfl⟩

/-- The vocabulary of the kernel. -/
abbrev zoSOLang : Language := Language.zeroOneIP.sum zeroOneIPGuessBlock.lang

/-- The column symbol in the kernel's vocabulary. -/
abbrev zoColSym : zoSOLang.Relations 1 := Sum.inl ipCol

/-- The row symbol in the kernel's vocabulary. -/
abbrev zoRowSym : zoSOLang.Relations 1 := Sum.inl ipRow

/-- The position symbol in the kernel's vocabulary. -/
abbrev zoPosnSym : zoSOLang.Relations 1 := Sum.inl ipPosn

/-- The entry symbol in the kernel's vocabulary. -/
abbrev zoCoefSym : zoSOLang.Relations 3 := Sum.inl ipCoef

/-- The right-hand-side symbol in the kernel's vocabulary. -/
abbrev zoRhsSym : zoSOLang.Relations 2 := Sum.inl ipRhs

/-- The order symbol in the kernel's vocabulary. -/
abbrev zoLeSym : zoSOLang.Relations 2 := Sum.inl ipLe

/-- The chosen-columns symbol in the kernel's vocabulary. -/
abbrev zoXSym : zoSOLang.Relations 1 := Sum.inr zoXRel

/-- The partial-sum symbol in the kernel's vocabulary. -/
abbrev zoPSSym : zoSOLang.Relations 3 := Sum.inr zoPSRel

/-- The carry symbol in the kernel's vocabulary. -/
abbrev zoCySym : zoSOLang.Relations 3 := Sum.inr zoCyRel

/-! ### Formula builders -/

section Builders

variable {α : Type}

/-- `x` is a column, as a formula. -/
def zoColF (x : α) : zoSOLang.Formula α := Relations.formula₁ zoColSym (Term.var x)

/-- `x` is a row, as a formula. -/
def zoRowF (x : α) : zoSOLang.Formula α := Relations.formula₁ zoRowSym (Term.var x)

/-- `x` is a bit position, as a formula. -/
def zoPosnF (x : α) : zoSOLang.Formula α := Relations.formula₁ zoPosnSym (Term.var x)

/-- The entry of the row `r` in the column `j` has bit 1 at `p`, as a
formula. -/
def zoCoefF (r j p : α) : zoSOLang.Formula α :=
  zoCoefSym.formula ![Term.var r, Term.var j, Term.var p]

/-- The right-hand side of the row `r` has bit 1 at `p`, as a formula. -/
def zoRhsF (r p : α) : zoSOLang.Formula α :=
  Relations.formula₂ zoRhsSym (Term.var r) (Term.var p)

/-- `x ≤ y`, as a formula. -/
def zoLeF (x y : α) : zoSOLang.Formula α :=
  Relations.formula₂ zoLeSym (Term.var x) (Term.var y)

/-- `x = y`, as a formula. -/
def zoEqF (x y : α) : zoSOLang.Formula α := Term.equal (Term.var x) (Term.var y)

/-- The column `x` is set to `1`, as a formula. -/
def zoXF (x : α) : zoSOLang.Formula α := Relations.formula₁ zoXSym (Term.var x)

/-- Bit `p` of the running total of the row `r` at the column `j`, as a
formula. -/
def zoPSF (r j p : α) : zoSOLang.Formula α :=
  zoPSSym.formula ![Term.var r, Term.var j, Term.var p]

/-- The carry at `p` of the step appending the column `j` to the total of the
row `r`, as a formula. -/
def zoCyF (r j p : α) : zoSOLang.Formula α :=
  zoCySym.formula ![Term.var r, Term.var j, Term.var p]

/-- The bit that the column `j` contributes to the row `r` at `p`: the entry's
bit, if the column is set to `1`. -/
def zoAddF (r j p : α) : zoSOLang.Formula α := zoXF j ⊓ zoCoefF r j p

/-- The exclusive or of three formulas, as `x ↔ (y ↔ z)`. -/
def zoXor3F (x y z : zoSOLang.Formula α) : zoSOLang.Formula α := x.iff (y.iff z)

/-- The majority of three formulas. -/
def zoMaj3F (x y z : zoSOLang.Formula α) : zoSOLang.Formula α :=
  (x ⊓ y) ⊔ ((x ⊓ z) ⊔ (y ⊓ z))

/-- `j` is the first column, as a formula. -/
noncomputable def zoMinColF (j : α) : zoSOLang.Formula α :=
  zoColF j ⊓ Formula.iAlls Unit
    ((zoColF (Sum.inr ())).imp (zoLeF (Sum.inl j) (Sum.inr ())))

/-- `j` is the last column, as a formula. -/
noncomputable def zoMaxColF (j : α) : zoSOLang.Formula α :=
  zoColF j ⊓ Formula.iAlls Unit
    ((zoColF (Sum.inr ())).imp (zoLeF (Sum.inr ()) (Sum.inl j)))

/-- `j` is the column right after `i`, as a formula. -/
noncomputable def zoSuccColF (i j : α) : zoSOLang.Formula α :=
  zoColF i ⊓ (zoColF j ⊓ (zoLeF i j ⊓ (∼(zoEqF i j) ⊓
    Formula.iAlls Unit
      ((zoColF (Sum.inr ())).imp ((zoLeF (Sum.inl i) (Sum.inr ())).imp
        ((zoLeF (Sum.inr ()) (Sum.inl j)).imp
          (zoEqF (Sum.inr ()) (Sum.inl i) ⊔ zoEqF (Sum.inr ()) (Sum.inl j))))))))

/-- `p` is the lowest position, as a formula. -/
noncomputable def zoMinPosnF (p : α) : zoSOLang.Formula α :=
  zoPosnF p ⊓ Formula.iAlls Unit
    ((zoPosnF (Sum.inr ())).imp (zoLeF (Sum.inl p) (Sum.inr ())))

/-- `p` is the highest position, as a formula. -/
noncomputable def zoMaxPosnF (p : α) : zoSOLang.Formula α :=
  zoPosnF p ⊓ Formula.iAlls Unit
    ((zoPosnF (Sum.inr ())).imp (zoLeF (Sum.inr ()) (Sum.inl p)))

/-- `q` is the position right above `p`, as a formula. -/
noncomputable def zoSuccPosnF (p q : α) : zoSOLang.Formula α :=
  zoPosnF p ⊓ (zoPosnF q ⊓ (zoLeF p q ⊓ (∼(zoEqF p q) ⊓
    Formula.iAlls Unit
      ((zoPosnF (Sum.inr ())).imp ((zoLeF (Sum.inl p) (Sum.inr ())).imp
        ((zoLeF (Sum.inr ()) (Sum.inl q)).imp
          (zoEqF (Sum.inr ()) (Sum.inl p) ⊔ zoEqF (Sum.inr ()) (Sum.inl q))))))))

end Builders

/-! ### The clauses

Every clause of a walk is guarded by `row r`: the rows do not interact, so the
kernel is Knapsack's read once per row. -/

/-- Kernel clause: the order is reflexive. -/
private noncomputable def zoReflClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 1) (zoLeF (Sum.inr 0) (Sum.inr 0))

/-- Kernel clause: the order is transitive. -/
private noncomputable def zoTransClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((zoLeF (Sum.inr 0) (Sum.inr 1) ⊓ zoLeF (Sum.inr 1) (Sum.inr 2)).imp
      (zoLeF (Sum.inr 0) (Sum.inr 2)))

/-- Kernel clause: the order is antisymmetric. -/
private noncomputable def zoAntisymmClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    ((zoLeF (Sum.inr 0) (Sum.inr 1) ⊓ zoLeF (Sum.inr 1) (Sum.inr 0)).imp
      (zoEqF (Sum.inr 0) (Sum.inr 1)))

/-- Kernel clause: the order is total. -/
private noncomputable def zoTotalClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 2) (zoLeF (Sum.inr 0) (Sum.inr 1) ⊔ zoLeF (Sum.inr 1) (Sum.inr 0))

/-- Kernel clause: only columns are set to `1`. -/
private noncomputable def zoXClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 1) ((zoXF (Sum.inr 0)).imp (zoColF (Sum.inr 0)))

/-- Kernel clause: at the first column each row's running total is that
column's contribution. -/
private noncomputable def zoBaseClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((zoRowF (Sum.inr 0) ⊓ (zoMinColF (Sum.inr 1) ⊓ zoPosnF (Sum.inr 2))).imp
      ((zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).iff
        (zoAddF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))))

/-- Kernel clause: each step adds a bit. -/
private noncomputable def zoSumClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((zoRowF (Sum.inr 0) ⊓ (zoSuccColF (Sum.inr 1) (Sum.inr 2) ⊓ zoPosnF (Sum.inr 3))).imp
      ((zoPSF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)).iff
        (zoXor3F (zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3))
          (zoAddF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
          (zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)))))

/-- Kernel clause: each step propagates its carry. -/
private noncomputable def zoCarryClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 5)
    ((zoRowF (Sum.inr 0) ⊓ (zoSuccColF (Sum.inr 1) (Sum.inr 2) ⊓
        zoSuccPosnF (Sum.inr 3) (Sum.inr 4))).imp
      ((zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 4)).iff
        (zoMaj3F (zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3))
          (zoAddF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
          (zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)))))

/-- Kernel clause: nothing is carried into the lowest position. -/
private noncomputable def zoBottomClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((zoRowF (Sum.inr 0) ⊓ (zoSuccColF (Sum.inr 1) (Sum.inr 2) ⊓
        zoMinPosnF (Sum.inr 3))).imp
      ∼(zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)))

/-- Kernel clause: nothing is carried out of the highest position. -/
private noncomputable def zoTopClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((zoRowF (Sum.inr 0) ⊓ (zoSuccColF (Sum.inr 1) (Sum.inr 2) ⊓
        zoMaxPosnF (Sum.inr 3))).imp
      ∼(zoMaj3F (zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3))
        (zoAddF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
        (zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))))

/-- Kernel clause: at the last column each row's running total is that row's
right-hand side. -/
private noncomputable def zoFinalClause : zoSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((zoRowF (Sum.inr 0) ⊓ (zoMaxColF (Sum.inr 1) ⊓ zoPosnF (Sum.inr 2))).imp
      ((zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).iff (zoRhsF (Sum.inr 0) (Sum.inr 2))))

/-- Kernel clause: with no column at all, every right-hand side must be
zero. -/
private noncomputable def zoEmptyClause : zoSOLang.Sentence :=
  (Formula.iAlls (Fin 1) ∼(zoColF (Sum.inr 0))).imp
    (Formula.iAlls (Fin 2)
      ((zoRowF (Sum.inr 0) ⊓ zoPosnF (Sum.inr 1)).imp ∼(zoRhsF (Sum.inr 0) (Sum.inr 1))))

/-- The first-order kernel of the `Σ₁` definition of 0-1 integer
programming. -/
noncomputable def zeroOneIPKernel : zoSOLang.Sentence :=
  (zoReflClause ⊓ (zoTransClause ⊓ (zoAntisymmClause ⊓ zoTotalClause))) ⊓
    (zoXClause ⊓ (zoBaseClause ⊓ (zoSumClause ⊓ (zoCarryClause ⊓
      (zoBottomClause ⊓ (zoTopClause ⊓ (zoFinalClause ⊓ zoEmptyClause)))))))

/-! ### Realization -/

section Realize

variable {A : Type} [Language.zeroOneIP.Structure A]
variable (ρ : zeroOneIPGuessBlock.Assignment A)

/-- The columns set to `1`, read off an assignment of the block. -/
def ZX (j : A) : Prop := ρ none ![j]

/-- The running total of a row, read off an assignment of the block. -/
def ZPS (r j p : A) : Prop := ρ (some true) ![r, j, p]

/-- The carries of a row, read off an assignment of the block. -/
def ZCy (r j p : A) : Prop := ρ (some false) ![r, j, p]

private theorem realize_zeroOneIPKernel :
    (@Sentence.Realize zoSOLang A
        (@sumStructure _ _ A _ (zeroOneIPGuessBlock.structure ρ)) zeroOneIPKernel) ↔
      IsLinOrd (IPLe (A := A)) ∧
        (∀ j : A, ZX ρ j → IPCol j) ∧
        (∀ r j p : A, IPRow r → MinPos IPLe IPCol j → IPPosn p →
          (ZPS ρ r j p ↔ ChainAdd (ZX ρ) (IPCoef r) j p)) ∧
        (∀ r i j p : A, IPRow r → SuccPos IPLe IPCol i j → IPPosn p →
          (ZPS ρ r j p ↔ (ZPS ρ r i p ↔
            (ChainAdd (ZX ρ) (IPCoef r) j p ↔ ZCy ρ r j p)))) ∧
        (∀ r i j p q : A, IPRow r → SuccPos IPLe IPCol i j → SuccPos IPLe IPPosn p q →
          (ZCy ρ r j q ↔
            maj (ZPS ρ r i p) (ChainAdd (ZX ρ) (IPCoef r) j p) (ZCy ρ r j p))) ∧
        (∀ r i j p : A, IPRow r → SuccPos IPLe IPCol i j → MinPos IPLe IPPosn p →
          ¬ZCy ρ r j p) ∧
        (∀ r i j p : A, IPRow r → SuccPos IPLe IPCol i j → MaxPos IPLe IPPosn p →
          ¬maj (ZPS ρ r i p) (ChainAdd (ZX ρ) (IPCoef r) j p) (ZCy ρ r j p)) ∧
        (∀ r j p : A, IPRow r → MaxPos IPLe IPCol j → IPPosn p →
          (ZPS ρ r j p ↔ IPRhs r p)) ∧
        ((∀ j : A, ¬IPCol j) → ∀ r p : A, IPRow r → IPPosn p → ¬IPRhs r p) := by
  letI := zeroOneIPGuessBlock.structure ρ
  have hsubX : ∀ w : Fin 1 → A,
      RelMap (L := zoSOLang) (M := A) zoXSym w ↔ ρ none w := fun _ => Iff.rfl
  have hsubP : ∀ w : Fin 3 → A,
      RelMap (L := zoSOLang) (M := A) zoPSSym w ↔ ρ (some true) w := fun _ => Iff.rfl
  have hsubC : ∀ w : Fin 3 → A,
      RelMap (L := zoSOLang) (M := A) zoCySym w ↔ ρ (some false) w := fun _ => Iff.rfl
  rw [zeroOneIPKernel]
  simp only [zoReflClause, zoTransClause, zoAntisymmClause, zoTotalClause, zoXClause,
    zoBaseClause, zoSumClause, zoCarryClause, zoBottomClause, zoTopClause, zoFinalClause,
    zoEmptyClause, zoColF, zoRowF, zoPosnF, zoCoefF, zoRhsF, zoLeF, zoEqF, zoXF, zoPSF,
    zoCyF, zoAddF, zoXor3F, zoMaj3F, zoMinColF, zoMaxColF, zoSuccColF, zoMinPosnF,
    zoMaxPosnF, zoSuccPosnF, Sentence.Realize, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_imp, Formula.realize_iff, Formula.realize_not, Formula.realize_iAlls,
    Formula.realize_rel₁, Formula.realize_rel₂, realize_rel₃, Formula.realize_equal,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsubX, hsubP,
    hsubC]
  constructor
  · rintro ⟨⟨hrefl, htrans, hanti, htot⟩, hx, hbase, hsum, hcarry, hbot, htop, hfin, hemp⟩
    have hminU : ∀ (P : A → Prop) (x : A), MinPos IPLe P x →
        P x ∧ ∀ y : Unit → A, P (y ()) → IPLe x (y ()) :=
      fun P x h => ⟨h.1, fun y hy => h.2 (y ()) hy⟩
    have hmaxU : ∀ (P : A → Prop) (x : A), MaxPos IPLe P x →
        P x ∧ ∀ y : Unit → A, P (y ()) → IPLe (y ()) x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (y ()) hy⟩
    have hsuccU : ∀ (P : A → Prop) (x y : A), SuccPos IPLe P x y →
        P x ∧ (P y ∧ (IPLe x y ∧ (¬x = y ∧ ∀ r : Unit → A,
          P (r ()) → IPLe x (r ()) → IPLe (r ()) y → r () = x ∨ r () = y))) :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (r ()) hr h1 h2⟩
    exact ⟨⟨fun a => hrefl (fun _ => a), fun a b c hab hbc => htrans ![a, b, c] ⟨hab, hbc⟩,
        fun a b hab hba => hanti ![a, b] ⟨hab, hba⟩, fun a b => htot ![a, b]⟩,
      fun j hj => hx (fun _ => j) hj,
      fun r j p hr hj hp => hbase ![r, j, p] ⟨hr, hminU _ _ hj, hp⟩,
      fun r i j p hr hij hp => hsum ![r, i, j, p] ⟨hr, hsuccU _ _ _ hij, hp⟩,
      fun r i j p q hr hij hpq =>
        hcarry ![r, i, j, p, q] ⟨hr, hsuccU _ _ _ hij, hsuccU _ _ _ hpq⟩,
      fun r i j p hr hij hp => hbot ![r, i, j, p] ⟨hr, hsuccU _ _ _ hij, hminU _ _ hp⟩,
      fun r i j p hr hij hp => htop ![r, i, j, p] ⟨hr, hsuccU _ _ _ hij, hmaxU _ _ hp⟩,
      fun r j p hr hj hp => hfin ![r, j, p] ⟨hr, hmaxU _ _ hj, hp⟩,
      fun hno r p hr hp => hemp (fun j => hno (j 0)) ![r, p] ⟨hr, hp⟩⟩
  · rintro ⟨⟨hrefl, htrans, hanti, htot⟩, hx, hbase, hsum, hcarry, hbot, htop, hfin, hemp⟩
    have hminM : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Unit → A, P (y ()) → IPLe x (y ())) → MinPos IPLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hmaxM : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Unit → A, P (y ()) → IPLe (y ()) x) → MaxPos IPLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hsuccM : ∀ (P : A → Prop) (x y : A),
        (P x ∧ (P y ∧ (IPLe x y ∧ (¬x = y ∧ ∀ r : Unit → A,
          P (r ()) → IPLe x (r ()) → IPLe (r ()) y → r () = x ∨ r () = y)))) →
        SuccPos IPLe P x y :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (fun _ => r) hr h1 h2⟩
    exact ⟨⟨fun w => hrefl (w 0), fun w h => htrans (w 0) (w 1) (w 2) h.1 h.2,
        fun w h => hanti (w 0) (w 1) h.1 h.2, fun w => htot (w 0) (w 1)⟩,
      fun w h => hx (w 0) h,
      fun w h => hbase (w 0) (w 1) (w 2) h.1 (hminM _ _ h.2.1) h.2.2,
      fun w h => hsum (w 0) (w 1) (w 2) (w 3) h.1 (hsuccM _ _ _ h.2.1) h.2.2,
      fun w h => hcarry (w 0) (w 1) (w 2) (w 3) (w 4) h.1 (hsuccM _ _ _ h.2.1)
        (hsuccM _ _ _ h.2.2),
      fun w h => hbot (w 0) (w 1) (w 2) (w 3) h.1 (hsuccM _ _ _ h.2.1) (hminM _ _ h.2.2),
      fun w h => htop (w 0) (w 1) (w 2) (w 3) h.1 (hsuccM _ _ _ h.2.1) (hmaxM _ _ h.2.2),
      fun w h => hfin (w 0) (w 1) (w 2) h.1 (hmaxM _ _ h.2.1) h.2.2,
      fun hno w h => hemp (fun j => hno (fun _ => j)) (w 0) (w 1) h.1 h.2⟩

end Realize

/-! ### Membership -/

section Membership

variable {A : Type} [Finite A] [Language.zeroOneIP.Structure A]

/-- **0-1 integer programming is `Σ₁`-definable**: guess the `0-1` vector and,
for each row, the running totals and the carries of a ripple-carry addition,
and check first-order that every row's walk ends on that row's right-hand
side. Since NP is defined as `Σ₁`-definability, this is the membership half of
the NP-completeness of 0-1 integer programming. -/
theorem zeroOneIP_sigmaSODefinable : SigmaSODefinable 1 ZeroOneIP := by
  refine ⟨[zeroOneIPGuessBlock], rfl, zeroOneIPKernel, ?_⟩
  intro A _ _ _
  constructor
  · -- a solution yields a certificate: one walk per row
    rintro ⟨hfin, hlin, S, hScol, hsumeq⟩
    have hex : ∀ r : A, ∃ PS Cy : A → A → Prop,
        IPRow r → IsChain IPLe IPCol IPLe IPPosn S (IPCoef r) PS Cy := by
      intro r
      by_cases hr : IPRow r
      · have hbound : (∑ᶠ j ∈ {j : A | S j}, binNum IPLe IPPosn (IPCoef r j)) <
            2 ^ ({p : A | IPPosn p} : Set A).ncard := by
          rw [show (∑ᶠ j ∈ {j : A | S j}, binNum IPLe IPPosn (IPCoef r j)) =
            ∑ᶠ j ∈ {j : A | S j}, IPCoefVal r j from rfl, hsumeq r hr, IPRhsVal]
          exact binNum_lt_two_pow hlin _ IPPosn rfl (IPRhs r)
        obtain ⟨PS, Cy, hchain⟩ := exists_chain (ILe := IPLe) (IItem := IPCol)
          (PLe := IPLe) (PPosn := IPPosn) (S := S) (wt := IPCoef r) hlin hlin hScol hbound
        exact ⟨PS, Cy, fun _ => hchain⟩
      · exact ⟨fun _ _ => False, fun _ _ => False, fun h => absurd h hr⟩
    choose PS Cy hchain using hex
    refine ⟨fun idx => match idx with
      | none => fun w : Fin 1 → A => S (w 0)
      | some true => fun w : Fin 3 → A => PS (w 0) (w 1) (w 2)
      | some false => fun w : Fin 3 → A => Cy (w 0) (w 1) (w 2), ?_⟩
    refine (realize_zeroOneIPKernel _).mpr ⟨hlin, hScol,
      fun r j p hr => (hchain r hr).1 j p,
      fun r i j p hr => (hchain r hr).2.1 i j p,
      fun r i j p q hr => (hchain r hr).2.2.1 i j p q,
      fun r i j p hr => (hchain r hr).2.2.2.1 i j p,
      fun r i j p hr => (hchain r hr).2.2.2.2 i j p, ?_, ?_⟩
    · -- at the last column the running total is the right-hand side
      intro r j p hr hj hp
      refine binNum_inj_on hlin _ IPPosn rfl (PS r j) (IPRhs r) ?_ p hp
      rw [chain_sound hlin hlin hScol (hchain r hr) j hj.1, partSum_max hScol hj]
      rw [show (∑ᶠ j ∈ {j : A | S j}, binNum IPLe IPPosn (IPCoef r j)) =
        ∑ᶠ j ∈ {j : A | S j}, IPCoefVal r j from rfl, hsumeq r hr, IPRhsVal]
    · -- with no columns every right-hand side must vanish
      intro hno r p hr hp
      have hSempty : {j : A | S j} = (∅ : Set A) := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hj => hno j (hScol j hj)
      have hzero : binNum (IPLe (A := A)) IPPosn (IPRhs r) = 0 := by
        rw [show binNum (IPLe (A := A)) IPPosn (IPRhs r) = IPRhsVal r from rfl,
          ← hsumeq r hr, hSempty, finsum_mem_empty]
      have := binNum_inj_on hlin _ IPPosn rfl (IPRhs r) (fun _ => False)
        (by rw [hzero, binNum_bot]) p hp
      exact this.mp
  · -- a certificate yields a solution: every row's walk is sound
    rintro ⟨ρ, hρ⟩
    obtain ⟨hlin, hx, hbase, hsum, hcarry, hbot, htop, hfin, hemp⟩ :=
      (realize_zeroOneIPKernel ρ).mp hρ
    refine ⟨‹Finite A›, hlin, ZX ρ, hx, ?_⟩
    intro r hr
    have hchain : IsChain IPLe IPCol IPLe IPPosn (ZX ρ) (IPCoef r) (ZPS ρ r) (ZCy ρ r) :=
      ⟨fun j p => hbase r j p hr, fun i j p => hsum r i j p hr,
        fun i j p q => hcarry r i j p q hr, fun i j p => hbot r i j p hr,
        fun i j p => htop r i j p hr⟩
    by_cases hcols : ∃ j : A, IPCol j
    · obtain ⟨jmax, hjmax⟩ := exists_maxPos hlin hcols
      have h1 := chain_sound hlin hlin hx hchain jmax hjmax.1
      have h2 : binNum IPLe IPPosn (ZPS ρ r jmax) = IPRhsVal r :=
        binNum_congr_on fun p hp => hfin r jmax p hr hjmax hp
      rw [show (∑ᶠ j ∈ {j : A | ZX ρ j}, IPCoefVal r j) =
        ∑ᶠ j ∈ {j : A | ZX ρ j}, binNum IPLe IPPosn (IPCoef r j) from rfl,
        ← partSum_max hx hjmax, ← h1, h2]
    · have hno : ∀ j : A, ¬IPCol j := fun j hj => hcols ⟨j, hj⟩
      have hSempty : {j : A | ZX ρ j} = (∅ : Set A) := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hj => hno j (hx j hj)
      have hrhs : {p : A | IPPosn p ∧ IPRhs r p} = (∅ : Set A) := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hemp hno r p hr h.1 h.2
      rw [hSempty, finsum_mem_empty, IPRhsVal, binNum, hrhs, finsum_mem_empty]

end Membership

end SigmaOne

end DescriptiveComplexity
