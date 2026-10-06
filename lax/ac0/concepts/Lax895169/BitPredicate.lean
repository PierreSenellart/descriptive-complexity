import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Basic

/-!
---
title: Ranks in a finite linear order and the BIT predicate
type: definition
---
In a finite linear order, the rank of an element is the number of elements
strictly below it, so that the elements are numbered $0, \dots, n - 1$. The
number of bit positions of the order is $\lceil \log_2 n \rceil$, enough
to write every rank in binary. The predicate BIT$(i, x)$ holds when the bit
of weight $2^{r}$ is set in the binary expansion of the rank of $x$, where
$r$ is the rank of $i$: an element names a position by its rank.

A quantifier prefix over $m$ variables is given by a polarity per variable,
existential or universal; it holds of a property of $m$-tuples when the
variables, quantified in order with the first outermost, make the property
true.
-/

namespace Lax895169.BitPredicate

/-- The rank of an element of a finite linear order: the number of its strict
predecessors. -/
noncomputable def orank {A : Type} [LinearOrder A] (z : A) : ℕ :=
  {y : A | y < z}.ncard

/-- **The number of bit positions** of the ranks of `A`: the ranks are the
numbers below `Nat.card A`, so they are exactly the numbers whose bits live
below `Nat.clog 2 (Nat.card A)`. -/
noncomputable def posCount (A : Type) [LinearOrder A] [Finite A] : ℕ :=
  Nat.clog 2 (Nat.card A)

/-- **The bit of `x` at the index `i`**: the `BIT` of the classical vocabulary
`FO(≤, BIT)`, the position being named by the element whose *rank* is the
exponent. Total, and with no guard – above the bit positions of the universe
every bit is simply clear. -/
def BitIx {A : Type} [LinearOrder A] (i x : A) : Prop :=
  (orank x).testBit (orank i) = true

/-- A quantifier prefix, peeled from the innermost variable outwards: the
variable of index `0` is quantified outermost, existentially when its polarity
is `true`. -/
def prefixHolds {A : Type} : (m : ℕ) → (Fin m → Bool) → ((Fin m → A) → Prop) → Prop
  | 0, _, P => P Fin.elim0
  | m + 1, pol, P =>
      prefixHolds m (fun j => pol j.castSucc)
        (fun v => if pol (Fin.last m) = true then ∃ a, P (Fin.snoc v a)
          else ∀ a, P (Fin.snoc v a))

end Lax895169.BitPredicate
