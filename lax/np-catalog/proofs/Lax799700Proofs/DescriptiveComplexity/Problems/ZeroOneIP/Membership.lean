/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.Knapsack.Chain
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

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
(`Lax799700Proofs.DescriptiveComplexity.Problems.Knapsack.Membership`) with a row argument
threaded through the two arithmetic relations and a guard `row r` in front of
every clause: the rows do not interact, so the walks are independent and the
semantic work is `Lax799700Proofs.DescriptiveComplexity.chain_sound` and
`Lax799700Proofs.DescriptiveComplexity.exists_chain` (`Lax799700Proofs.DescriptiveComplexity.Problems.Knapsack.Chain`)
applied once per row – the reason those two are stated over an arbitrary walk
order and item predicate rather than over one vocabulary.

Unlike Partition, the walks run on the *instance's own* positions: each row's
total is its right-hand side, which is written there, so it fits.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive ZeroOneIPGuessBlockIx where
/-- The columns set to `1`. -/

  | x
/-- The running partial sums: `pS r j p` is the bit `p` of the total of the
  row `r` up to the column `j`. -/

  | pS
/-- The carries of the step appending a column to a row's total. -/

  | cy
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.ZeroOneIPGuessBlockIx :=
  ⟨List.toFinset [.x, .pS, .cy], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition of 0-1 integer
programming: the columns set to `1` (unary), and the running partial sums and
the carries (ternary: a row, a column and a bit position). -/
def zeroOneIPGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.ZeroOneIPGuessBlockIx
  arity := fun i =>
    match i with
    | .x => 1
    | .pS => 3
    | .cy => 3

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev zoSOLang : FirstOrder.Language :=
  (Lax799700.ZeroOneIP.zeroOneIP).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.zeroOneIPGuessBlock)

/-- The `col` symbol over the sum. -/
abbrev zoColSym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 1 :=
  Sum.inl Lax799700.ZeroOneIP.ipCol

/-- The `row` symbol over the sum. -/
abbrev zoRowSym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 1 :=
  Sum.inl Lax799700.ZeroOneIP.ipRow

/-- The `posn` symbol over the sum. -/
abbrev zoPosnSym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 1 :=
  Sum.inl Lax799700.ZeroOneIP.ipPosn

/-- The `coef` symbol over the sum. -/
abbrev zoCoefSym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 3 :=
  Sum.inl Lax799700.ZeroOneIP.ipCoef

/-- The `rhs` symbol over the sum. -/
abbrev zoRhsSym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 2 :=
  Sum.inl Lax799700.ZeroOneIP.ipRhs

/-- The `le` symbol over the sum. -/
abbrev zoLeSym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 2 :=
  Sum.inl Lax799700.ZeroOneIP.ipLe

/-- The `x` relation variable. -/
def zoXRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.zeroOneIPGuessBlock).Relations 1 :=
  ⟨.x, rfl⟩

/-- The `x` symbol over the sum. -/
abbrev zoXSym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 1 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.zoXRel

/-- The `pS` relation variable. -/
def zoPSRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.zeroOneIPGuessBlock).Relations 3 :=
  ⟨.pS, rfl⟩

/-- The `pS` symbol over the sum. -/
abbrev zoPSSym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 3 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.zoPSRel

/-- The `cy` relation variable. -/
def zoCyRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.zeroOneIPGuessBlock).Relations 3 :=
  ⟨.cy, rfl⟩

/-- The `cy` symbol over the sum. -/
abbrev zoCySym : (_root_.Lax799700Proofs.DescriptiveComplexity.zoSOLang).Relations 3 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.zoCyRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

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
  zoColF j ⊓ FirstOrder.Language.Formula.iAlls (Fin 1) ((zoColF (Sum.inr 0)).imp (zoLeF (Sum.inl j) (Sum.inr 0)))

/-- `j` is the last column, as a formula. -/
noncomputable def zoMaxColF (j : α) : zoSOLang.Formula α :=
  zoColF j ⊓ FirstOrder.Language.Formula.iAlls (Fin 1) ((zoColF (Sum.inr 0)).imp (zoLeF (Sum.inr 0) (Sum.inl j)))

/-- `j` is the column right after `i`, as a formula. -/
noncomputable def zoSuccColF (i j : α) : zoSOLang.Formula α :=
  zoColF i ⊓
      (zoColF j ⊓
        (zoLeF i j ⊓
          (FirstOrder.Language.BoundedFormula.not (zoEqF i j) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 1)
              ((zoColF (Sum.inr 0)).imp
                ((zoLeF (Sum.inl i) (Sum.inr 0)).imp
                  ((zoLeF (Sum.inr 0) (Sum.inl j)).imp (zoEqF (Sum.inr 0) (Sum.inl i) ⊔ zoEqF (Sum.inr 0) (Sum.inl j))))))))

/-- `p` is the lowest position, as a formula. -/
noncomputable def zoMinPosnF (p : α) : zoSOLang.Formula α :=
  zoPosnF p ⊓ FirstOrder.Language.Formula.iAlls (Fin 1) ((zoPosnF (Sum.inr 0)).imp (zoLeF (Sum.inl p) (Sum.inr 0)))

/-- `p` is the highest position, as a formula. -/
noncomputable def zoMaxPosnF (p : α) : zoSOLang.Formula α :=
  zoPosnF p ⊓ FirstOrder.Language.Formula.iAlls (Fin 1) ((zoPosnF (Sum.inr 0)).imp (zoLeF (Sum.inr 0) (Sum.inl p)))

/-- `q` is the position right above `p`, as a formula. -/
noncomputable def zoSuccPosnF (p q : α) : zoSOLang.Formula α :=
  zoPosnF p ⊓
      (zoPosnF q ⊓
        (zoLeF p q ⊓
          (FirstOrder.Language.BoundedFormula.not (zoEqF p q) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 1)
              ((zoPosnF (Sum.inr 0)).imp
                ((zoLeF (Sum.inl p) (Sum.inr 0)).imp
                  ((zoLeF (Sum.inr 0) (Sum.inl q)).imp (zoEqF (Sum.inr 0) (Sum.inl p) ⊔ zoEqF (Sum.inr 0) (Sum.inl q))))))))

end Builders

/-! ### The clauses

Every clause of a walk is guarded by `row r`: the rows do not interact, so the
kernel is Knapsack's read once per row. -/

/-- Kernel clause: the order is reflexive. -/
private noncomputable def zoReflClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (zoLeF (Sum.inr 0) (Sum.inr 0))

/-- Kernel clause: the order is transitive. -/
private noncomputable def zoTransClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((zoLeF (Sum.inr 0) (Sum.inr 1) ⊓ zoLeF (Sum.inr 1) (Sum.inr 2)).imp (zoLeF (Sum.inr 0) (Sum.inr 2)))

/-- Kernel clause: the order is antisymmetric. -/
private noncomputable def zoAntisymmClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((zoLeF (Sum.inr 0) (Sum.inr 1) ⊓ zoLeF (Sum.inr 1) (Sum.inr 0)).imp (zoEqF (Sum.inr 0) (Sum.inr 1)))

/-- Kernel clause: the order is total. -/
private noncomputable def zoTotalClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2) (zoLeF (Sum.inr 0) (Sum.inr 1) ⊔ zoLeF (Sum.inr 1) (Sum.inr 0))

/-- Kernel clause: only columns are set to `1`. -/
private noncomputable def zoXClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) ((zoXF (Sum.inr 0)).imp (zoColF (Sum.inr 0)))

/-- Kernel clause: at the first column each row's running total is that
column's contribution. -/
private noncomputable def zoBaseClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((zoRowF (Sum.inr 0) ⊓ (zoMinColF (Sum.inr 1) ⊓ zoPosnF (Sum.inr 2))).imp
        ((zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).iff (zoAddF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))))

/-- Kernel clause: each step adds a bit. -/
private noncomputable def zoSumClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
      ((zoRowF (Sum.inr 0) ⊓ (zoSuccColF (Sum.inr 1) (Sum.inr 2) ⊓ zoPosnF (Sum.inr 3))).imp
        ((zoPSF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)).iff
          (zoXor3F (zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3)) (zoAddF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
            (zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)))))

/-- Kernel clause: each step propagates its carry. -/
private noncomputable def zoCarryClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 5)
      ((zoRowF (Sum.inr 0) ⊓ (zoSuccColF (Sum.inr 1) (Sum.inr 2) ⊓ zoSuccPosnF (Sum.inr 3) (Sum.inr 4))).imp
        ((zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 4)).iff
          (zoMaj3F (zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3)) (zoAddF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
            (zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)))))

/-- Kernel clause: nothing is carried into the lowest position. -/
private noncomputable def zoBottomClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
      ((zoRowF (Sum.inr 0) ⊓ (zoSuccColF (Sum.inr 1) (Sum.inr 2) ⊓ zoMinPosnF (Sum.inr 3))).imp
        (FirstOrder.Language.BoundedFormula.not (zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))))

/-- Kernel clause: nothing is carried out of the highest position. -/
private noncomputable def zoTopClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
      ((zoRowF (Sum.inr 0) ⊓ (zoSuccColF (Sum.inr 1) (Sum.inr 2) ⊓ zoMaxPosnF (Sum.inr 3))).imp
        (FirstOrder.Language.BoundedFormula.not
          (zoMaj3F (zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3)) (zoAddF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3))
            (zoCyF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)))))

/-- Kernel clause: at the last column each row's running total is that row's
right-hand side. -/
private noncomputable def zoFinalClause : zoSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((zoRowF (Sum.inr 0) ⊓ (zoMaxColF (Sum.inr 1) ⊓ zoPosnF (Sum.inr 2))).imp
        ((zoPSF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).iff (zoRhsF (Sum.inr 0) (Sum.inr 2))))

/-- Kernel clause: with no column at all, every right-hand side must be
zero. -/
private noncomputable def zoEmptyClause : zoSOLang.Sentence :=
  (FirstOrder.Language.Formula.iAlls (Fin 1) (FirstOrder.Language.BoundedFormula.not (zoColF (Sum.inr 0)))).imp
      (FirstOrder.Language.Formula.iAlls (Fin 2)
        ((zoRowF (Sum.inr 0) ⊓ zoPosnF (Sum.inr 1)).imp
          (FirstOrder.Language.BoundedFormula.not (zoRhsF (Sum.inr 0) (Sum.inr 1)))))

/-- The first-order kernel of the `Σ₁` definition of 0-1 integer
programming. -/
noncomputable def zeroOneIPKernel : zoSOLang.Sentence :=
  (zoReflClause ⊓ (zoTransClause ⊓ (zoAntisymmClause ⊓ zoTotalClause))) ⊓
    (zoXClause ⊓ (zoBaseClause ⊓ (zoSumClause ⊓ (zoCarryClause ⊓
      (zoBottomClause ⊓ (zoTopClause ⊓ (zoFinalClause ⊓ zoEmptyClause)))))))

/-! ### Realization -/

section Realize

variable {A : Type} [Lax799700.ZeroOneIP.zeroOneIP.Structure A]

variable (ρ : zeroOneIPGuessBlock.Assignment A)

/-- The columns set to `1`, read off an assignment of the block. -/
def ZX (j : A) : Prop := ρ .x ![j]

/-- The running total of a row, read off an assignment of the block. -/
def ZPS (r j p : A) : Prop := ρ .pS ![r, j, p]

/-- The carries of a row, read off an assignment of the block. -/
def ZCy (r j p : A) : Prop := ρ .cy ![r, j, p]

private theorem realize_zeroOneIPKernel :
    (@Sentence.Realize zoSOLang A
        (@sumStructure _ _ A _ (zeroOneIPGuessBlock.structure ρ)) zeroOneIPKernel) ↔
      Lax904597.Machines.IsLinOrd (Lax799700.ZeroOneIP.IPLe (A := A)) ∧
        (∀ j : A, ZX ρ j → Lax799700.ZeroOneIP.IPCol j) ∧
        (∀ r j p : A, Lax799700.ZeroOneIP.IPRow r → Lax904597.Machines.MinPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol j → Lax799700.ZeroOneIP.IPPosn p →
          (ZPS ρ r j p ↔ ChainAdd (ZX ρ) (Lax799700.ZeroOneIP.IPCoef r) j p)) ∧
        (∀ r i j p : A, Lax799700.ZeroOneIP.IPRow r → Lax904597.Machines.SuccPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol i j → Lax799700.ZeroOneIP.IPPosn p →
          (ZPS ρ r j p ↔ (ZPS ρ r i p ↔
            (ChainAdd (ZX ρ) (Lax799700.ZeroOneIP.IPCoef r) j p ↔ ZCy ρ r j p)))) ∧
        (∀ r i j p q : A, Lax799700.ZeroOneIP.IPRow r → Lax904597.Machines.SuccPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol i j → Lax904597.Machines.SuccPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn p q →
          (ZCy ρ r j q ↔
            maj (ZPS ρ r i p) (ChainAdd (ZX ρ) (Lax799700.ZeroOneIP.IPCoef r) j p) (ZCy ρ r j p))) ∧
        (∀ r i j p : A, Lax799700.ZeroOneIP.IPRow r → Lax904597.Machines.SuccPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol i j → Lax904597.Machines.MinPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn p →
          ¬ZCy ρ r j p) ∧
        (∀ r i j p : A, Lax799700.ZeroOneIP.IPRow r → Lax904597.Machines.SuccPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol i j → MaxPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn p →
          ¬maj (ZPS ρ r i p) (ChainAdd (ZX ρ) (Lax799700.ZeroOneIP.IPCoef r) j p) (ZCy ρ r j p)) ∧
        (∀ r j p : A, Lax799700.ZeroOneIP.IPRow r → MaxPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol j → Lax799700.ZeroOneIP.IPPosn p →
          (ZPS ρ r j p ↔ Lax799700.ZeroOneIP.IPRhs r p)) ∧
        ((∀ j : A, ¬Lax799700.ZeroOneIP.IPCol j) → ∀ r p : A, Lax799700.ZeroOneIP.IPRow r → Lax799700.ZeroOneIP.IPPosn p → ¬Lax799700.ZeroOneIP.IPRhs r p) := by
  let := zeroOneIPGuessBlock.structure ρ
  have hsubX : ∀ w : Fin 1 → A,
      RelMap (L := zoSOLang) (M := A) zoXSym w ↔ ρ .x w := fun _ => Iff.rfl
  have hsubP : ∀ w : Fin 3 → A,
      RelMap (L := zoSOLang) (M := A) zoPSSym w ↔ ρ .pS w := fun _ => Iff.rfl
  have hsubC : ∀ w : Fin 3 → A,
      RelMap (L := zoSOLang) (M := A) zoCySym w ↔ ρ .cy w := fun _ => Iff.rfl
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
    have hminU : ∀ (P : A → Prop) (x : A), Lax904597.Machines.MinPos Lax799700.ZeroOneIP.IPLe P x →
        P x ∧ ∀ y : Fin 1 → A, P (y 0) → Lax799700.ZeroOneIP.IPLe x (y 0) :=
      fun P x h => ⟨h.1, fun y hy => h.2 (y 0) hy⟩
    have hmaxU : ∀ (P : A → Prop) (x : A), MaxPos Lax799700.ZeroOneIP.IPLe P x →
        P x ∧ ∀ y : Fin 1 → A, P (y 0) → Lax799700.ZeroOneIP.IPLe (y 0) x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (y 0) hy⟩
    have hsuccU : ∀ (P : A → Prop) (x y : A), Lax904597.Machines.SuccPos Lax799700.ZeroOneIP.IPLe P x y →
        P x ∧ (P y ∧ (Lax799700.ZeroOneIP.IPLe x y ∧ (¬x = y ∧ ∀ r : Fin 1 → A,
          P (r 0) → Lax799700.ZeroOneIP.IPLe x (r 0) → Lax799700.ZeroOneIP.IPLe (r 0) y → r 0 = x ∨ r 0 = y))) :=
      fun P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (r 0) hr h1 h2⟩
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
        (P x ∧ ∀ y : Fin 1 → A, P (y 0) → Lax799700.ZeroOneIP.IPLe x (y 0)) → Lax904597.Machines.MinPos Lax799700.ZeroOneIP.IPLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hmaxM : ∀ (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Fin 1 → A, P (y 0) → Lax799700.ZeroOneIP.IPLe (y 0) x) → MaxPos Lax799700.ZeroOneIP.IPLe P x :=
      fun P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hsuccM : ∀ (P : A → Prop) (x y : A),
        (P x ∧ (P y ∧ (Lax799700.ZeroOneIP.IPLe x y ∧ (¬x = y ∧ ∀ r : Fin 1 → A,
          P (r 0) → Lax799700.ZeroOneIP.IPLe x (r 0) → Lax799700.ZeroOneIP.IPLe (r 0) y → r 0 = x ∨ r 0 = y)))) →
        Lax904597.Machines.SuccPos Lax799700.ZeroOneIP.IPLe P x y :=
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

variable {A : Type} [Finite A] [Lax799700.ZeroOneIP.zeroOneIP.Structure A]

/-- **0-1 integer programming is `Σ₁`-definable**: guess the `0-1` vector and,
for each row, the running totals and the carries of a ripple-carry addition,
and check first-order that every row's walk ends on that row's right-hand
side. Since NP is defined as `Σ₁`-definability, this is the membership half of
the NP-completeness of 0-1 integer programming. -/
theorem zeroOneIP_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 ZeroOneIP := by
  refine ⟨[zeroOneIPGuessBlock], rfl, zeroOneIPKernel, ?_⟩
  intro A _ _ _
  constructor
  · -- a solution yields a certificate: one walk per row
    rintro ⟨hfin, hlin, S, hScol, hsumeq⟩
    have hex : ∀ r : A, ∃ PS Cy : A → A → Prop,
        Lax799700.ZeroOneIP.IPRow r → IsChain Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn S (Lax799700.ZeroOneIP.IPCoef r) PS Cy := by
      intro r
      by_cases hr : Lax799700.ZeroOneIP.IPRow r
      · have hbound : (∑ᶠ j ∈ {j : A | S j}, Lax799700.Common.binNum Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn (Lax799700.ZeroOneIP.IPCoef r j)) <
            2 ^ ({p : A | Lax799700.ZeroOneIP.IPPosn p} : Set A).ncard := by
          rw [show (∑ᶠ j ∈ {j : A | S j}, Lax799700.Common.binNum Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn (Lax799700.ZeroOneIP.IPCoef r j)) =
            ∑ᶠ j ∈ {j : A | S j}, Lax799700.ZeroOneIP.IPCoefVal r j from rfl, hsumeq r hr, Lax799700.ZeroOneIP.IPRhsVal]
          exact binNum_lt_two_pow hlin _ Lax799700.ZeroOneIP.IPPosn rfl (Lax799700.ZeroOneIP.IPRhs r)
        obtain ⟨PS, Cy, hchain⟩ := exists_chain (ILe := Lax799700.ZeroOneIP.IPLe) (IItem := Lax799700.ZeroOneIP.IPCol)
          (PLe := Lax799700.ZeroOneIP.IPLe) (PPosn := Lax799700.ZeroOneIP.IPPosn) (S := S) (wt := Lax799700.ZeroOneIP.IPCoef r) hlin hlin hScol hbound
        exact ⟨PS, Cy, fun _ => hchain⟩
      · exact ⟨fun _ _ => False, fun _ _ => False, fun h => absurd h hr⟩
    choose PS Cy hchain using hex
    refine ⟨fun idx => match idx with
      | .x => fun w : Fin 1 → A => S (w 0)
      | .pS => fun w : Fin 3 → A => PS (w 0) (w 1) (w 2)
      | .cy => fun w : Fin 3 → A => Cy (w 0) (w 1) (w 2), ?_⟩
    refine (realize_zeroOneIPKernel _).mpr ⟨hlin, hScol,
      fun r j p hr => (hchain r hr).1 j p,
      fun r i j p hr => (hchain r hr).2.1 i j p,
      fun r i j p q hr => (hchain r hr).2.2.1 i j p q,
      fun r i j p hr => (hchain r hr).2.2.2.1 i j p,
      fun r i j p hr => (hchain r hr).2.2.2.2 i j p, ?_, ?_⟩
    · -- at the last column the running total is the right-hand side
      intro r j p hr hj hp
      refine binNum_inj_on hlin _ Lax799700.ZeroOneIP.IPPosn rfl (PS r j) (Lax799700.ZeroOneIP.IPRhs r) ?_ p hp
      rw [chain_sound hlin hlin hScol (hchain r hr) j hj.1, partSum_max hScol hj]
      rw [show (∑ᶠ j ∈ {j : A | S j}, Lax799700.Common.binNum Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn (Lax799700.ZeroOneIP.IPCoef r j)) =
        ∑ᶠ j ∈ {j : A | S j}, Lax799700.ZeroOneIP.IPCoefVal r j from rfl, hsumeq r hr, Lax799700.ZeroOneIP.IPRhsVal]
    · -- with no columns every right-hand side must vanish
      intro hno r p hr hp
      have hSempty : {j : A | S j} = (∅ : Set A) := by
        ext j
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hj => hno j (hScol j hj)
      have hzero : Lax799700.Common.binNum (Lax799700.ZeroOneIP.IPLe (A := A)) Lax799700.ZeroOneIP.IPPosn (Lax799700.ZeroOneIP.IPRhs r) = 0 := by
        rw [show Lax799700.Common.binNum (Lax799700.ZeroOneIP.IPLe (A := A)) Lax799700.ZeroOneIP.IPPosn (Lax799700.ZeroOneIP.IPRhs r) = Lax799700.ZeroOneIP.IPRhsVal r from rfl,
          ← hsumeq r hr, hSempty, finsum_mem_empty]
      have := binNum_inj_on hlin _ Lax799700.ZeroOneIP.IPPosn rfl (Lax799700.ZeroOneIP.IPRhs r) (fun _ => False)
        (by rw [hzero, binNum_bot]) p hp
      exact this.mp
  · -- a certificate yields a solution: every row's walk is sound
    rintro ⟨ρ, hρ⟩
    obtain ⟨hlin, hx, hbase, hsum, hcarry, hbot, htop, hfin, hemp⟩ :=
      (realize_zeroOneIPKernel ρ).mp hρ
    refine ⟨‹Finite A›, hlin, ZX ρ, hx, ?_⟩
    intro r hr
    have hchain : IsChain Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn (ZX ρ) (Lax799700.ZeroOneIP.IPCoef r) (ZPS ρ r) (ZCy ρ r) :=
      ⟨fun j p => hbase r j p hr, fun i j p => hsum r i j p hr,
        fun i j p q => hcarry r i j p q hr, fun i j p => hbot r i j p hr,
        fun i j p => htop r i j p hr⟩
    by_cases hcols : ∃ j : A, Lax799700.ZeroOneIP.IPCol j
    · obtain ⟨jmax, hjmax⟩ := exists_maxPos hlin hcols
      have h1 := chain_sound hlin hlin hx hchain jmax hjmax.1
      have h2 : Lax799700.Common.binNum Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn (ZPS ρ r jmax) = Lax799700.ZeroOneIP.IPRhsVal r :=
        binNum_congr_on fun p hp => hfin r jmax p hr hjmax hp
      rw [show (∑ᶠ j ∈ {j : A | ZX ρ j}, Lax799700.ZeroOneIP.IPCoefVal r j) =
        ∑ᶠ j ∈ {j : A | ZX ρ j}, Lax799700.Common.binNum Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn (Lax799700.ZeroOneIP.IPCoef r j) from rfl,
        ← partSum_max hx hjmax, ← h1, h2]
    · have hno : ∀ j : A, ¬Lax799700.ZeroOneIP.IPCol j := fun j hj => hcols ⟨j, hj⟩
      have hSempty : {j : A | ZX ρ j} = (∅ : Set A) := by
        ext j
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hj => hno j (hx j hj)
      have hrhs : {p : A | Lax799700.ZeroOneIP.IPPosn p ∧ Lax799700.ZeroOneIP.IPRhs r p} = (∅ : Set A) := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hemp hno r p hr h.1 h.2
      rw [hSempty, finsum_mem_empty, Lax799700.ZeroOneIP.IPRhsVal, Lax799700.Common.binNum, hrhs, finsum_mem_empty]

end Membership

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity


