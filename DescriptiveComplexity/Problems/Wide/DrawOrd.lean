/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawEnc
import DescriptiveComplexity.Problems.Wide.Increment
import DescriptiveComplexity.Exponential.Order
import DescriptiveComplexity.OrderedComposition
import DescriptiveComplexity.OrderWalk

/-!
# The order the reduction puts on the points

`DescriptiveComplexity.PFPDefinable` quantifies over *every* linear order on
the expanded universe, so the EXPSPACE reduction may choose the one its
machine can compare: the **pullback of the binary block-value order along the
encoding** (`DescriptiveComplexity.Draw.encOrder`). An order atom on two points
is then exactly the comparison of their encodings in the machine's own reading
– `DescriptiveComplexity.WMSetLe` at the lexicographic order on tuples, the
order the register file walks – which is
`DescriptiveComplexity.Draw.encOrder_le_iff`.

The junction between the two languages for orders on block values –
the address layer's `DescriptiveComplexity.WMSetLe tupLeLex` and the library's
`DescriptiveComplexity.setLinearOrder` – is
`DescriptiveComplexity.Draw.wmSetLe_iff_setLe`: both say *at the most
significant differing tuple, the second contains it*, with most significant =
lexicographically least.

(The library's canonical order on the expanded universe,
`DescriptiveComplexity.ExpExpansion.mapLinearOrder`, orders by tag first and
padded atoms second; nothing here conflicts with it – the reduction simply
instantiates the definition's order quantifier differently.)
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language

/-! ### The two readings of the binary order on block values -/

section SetLe

variable {dd : ℕ} {A : Type} [LinearOrder A]

/-- The lexicographic comparison of tuples is the `Lex` order. -/
theorem tupLeLex_iff_toLex_le (x y : Fin dd → A) :
    tupLeLex x y ↔ toLex x ≤ toLex y := by
  rw [tupLeLex, le_iff_lt_or_eq]
  constructor
  · rintro (rfl | h)
    · exact Or.inr rfl
    · exact Or.inl (lex_lt_iff.mpr h)
  · rintro (h | h)
    · exact Or.inr (lex_lt_iff.mp h)
    · exact Or.inl (toLex.injective h)

/-- The strict lexicographic comparison of tuples is the strict `Lex` order. -/
theorem wmLt_tupLeLex_iff (x y : Fin dd → A) :
    WMLt tupLeLex x y ↔ toLex x < toLex y := by
  rw [WMLt, tupLeLex_iff_toLex_le, tupLeLex_iff_toLex_le]
  exact ⟨fun h => lt_of_le_not_ge h.1 h.2, fun h => ⟨le_of_lt h, not_le_of_gt h⟩⟩

variable [Finite A]

/-- **The two readings of the binary order on block values agree**: the address
layer's `DescriptiveComplexity.WMSetLe` at the lexicographic tuple order is the
library's `DescriptiveComplexity.setLinearOrder` on subsets of the `Lex`
tuples. -/
theorem wmSetLe_iff_setLe (S T : (Fin dd → A) → Prop) :
    WMSetLe tupLeLex S T ↔ (setLinearOrder (Lex (Fin dd → A))).le S T := by
  have hsplit := @le_iff_lt_or_eq _ (setLinearOrder (Lex (Fin dd → A))).toPartialOrder S T
  refine Iff.trans ?_ hsplit.symm
  constructor
  · rintro (hag | ⟨x, hbelow, hS, hT⟩)
    · exact Or.inr (funext fun x => propext (hag x))
    · refine Or.inl ((setLinearOrder_lt_iff (I := Lex (Fin dd → A)) S T).mpr
        ⟨toLex x, fun j hj => ?_, hS, hT⟩)
      exact hbelow (ofLex j) ((wmLt_tupLeLex_iff (ofLex j) x).mpr hj)
  · rintro (hlt | heq)
    · obtain ⟨i, hag, hS, hT⟩ := (setLinearOrder_lt_iff (I := Lex (Fin dd → A)) S T).mp hlt
      exact Or.inr ⟨ofLex i,
        fun y hy => hag (toLex y) ((wmLt_tupLeLex_iff y (ofLex i)).mp hy), hS, hT⟩
    · exact Or.inl fun x => iff_of_eq (congrFun heq x)

end SetLe

/-! ### The pulled-back order on the points -/

section EncOrder

variable {L : Language.{0, 0}} {X : ExpExpansion L}
variable {dd : ℕ} (ly : EncLayout (PtCode X) (blockArityBound X.B) dd)
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable (zero one : A)

/-- **The order the reduction puts on the expanded universe**: the pullback of
the binary block-value order along the encoding. An order atom on two points is
then the comparison of their encodings, which the machine can run on its
register file. -/
@[instance_reducible]
noncomputable def encOrder (hne : zero ≠ one) : LinearOrder (X.Map A) :=
  letI : LinearOrder ((Fin dd → A) → Prop) := setLinearOrder (Lex (Fin dd → A))
  LinearOrder.lift' (encMap ly zero one) (encMap_injective ly hne)

/-- **What the chosen order says**: the machine's own comparison of the two
encodings. -/
theorem encOrder_le_iff (hne : zero ≠ one) (m m' : X.Map A) :
    (encOrder ly zero one hne).le m m' ↔
      WMSetLe tupLeLex (encMap ly zero one m) (encMap ly zero one m') :=
  (wmSetLe_iff_setLe _ _).symm

end EncOrder

end Draw

end DescriptiveComplexity
