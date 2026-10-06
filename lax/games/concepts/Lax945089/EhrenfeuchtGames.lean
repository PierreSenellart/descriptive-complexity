import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: Ehrenfeucht–Fraïssé games
type: definition
---
The quantifier depth of a first-order formula is the maximal nesting of its
quantifiers. A position of the Ehrenfeucht–Fraïssé game on two structures
$M$ and $N$ over a relational vocabulary is a pair of tuples of the same
length, one in each structure; it is legal when the two tuples satisfy the
same equalities and the same atomic relations, that is, when matching them
coordinate by coordinate is a partial isomorphism. The duplicator survives
$n$ rounds from a position when the position is legal and, if $n > 0$,
whichever element the spoiler appends to one of the tuples, the duplicator
can append an element to the other so as to survive $n - 1$ rounds from the
new position. The structures $M$ and $N$ are $n$-round equivalent when the
duplicator survives $n$ rounds from the empty position.
-/

namespace Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- The quantifier depth of a bounded formula: the number of pebbles the
invariance argument spends on it. -/
def qdepth {L : Language.{0, 0}} {α : Type*} : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f₁ f₂ => max (qdepth f₁) (qdepth f₂)
  | _, .all f => qdepth f + 1

/-- A **legal position** of the Ehrenfeucht–Fraïssé game: two tuples of equal
length, one on each side, satisfying the same equalities between their
coordinates and the same base relations at every selection of coordinates.
Equivalently, matching coordinate to coordinate is a partial isomorphism. -/
def PartialIso (L : Language.{0, 0}) {M N : Type} [L.Structure M] [L.Structure N] {j : ℕ}
    (a : Fin j → M) (b : Fin j → N) : Prop :=
  (∀ i i' : Fin j, a i = a i' ↔ b i = b i') ∧
    ∀ (l : ℕ) (R : L.Relations l) (g : Fin l → Fin j),
      ((RelMap R fun p => a (g p)) ↔ RelMap R fun p => b (g p))

/-- **The stages of the Ehrenfeucht–Fraïssé refinement**: `efStage L n a b`
says that from the position `(a, b)` the duplicator survives `n` further
rounds – the position is legal, and whichever element the spoiler appends on
either side, the duplicator can append one on the other and survive `n - 1`
more rounds. -/
def efStage (L : Language.{0, 0}) {M N : Type} [L.Structure M] [L.Structure N] :
    ℕ → ∀ {j : ℕ}, (Fin j → M) → (Fin j → N) → Prop
  | 0, _, a, b => PartialIso L a b
  | n + 1, _, a, b =>
      PartialIso L a b ∧
        (∀ c : M, ∃ d : N, efStage L n (Fin.snoc a c) (Fin.snoc b d)) ∧
        (∀ d : N, ∃ c : M, efStage L n (Fin.snoc a c) (Fin.snoc b d))

/-- **`n`-round equivalence**: the duplicator survives `n` rounds of the
Ehrenfeucht–Fraïssé game on `M` and `N` played from the empty position. -/
def EFEquiv (L : Language.{0, 0}) (M N : Type) [L.Structure M] [L.Structure N] (n : ℕ) : Prop :=
  efStage L n (default : Fin 0 → M) (default : Fin 0 → N)

end Lax945089.EhrenfeuchtGames
