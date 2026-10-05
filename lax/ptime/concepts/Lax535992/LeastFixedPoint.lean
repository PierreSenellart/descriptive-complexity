import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.SecondOrder
import Lax485149.SecondOrderAtoms
import Lax535992.HornFragment

/-!
---
title: First-order logic with least fixed points
type: definition
---
A definition in FO(LFP), in clausal normal form, over a vocabulary $L$
consists of a block of relation variables, a finite list of rules, which
are Horn clauses over $L \cup \{\le\}$ and the block with a head, and an
output sentence, an arbitrary first-order sentence over $L \cup \{\le\}$
expanded by the relation variables. On a linearly ordered $L$-structure the
rules define the least relations closed under them: a tuple is derived when
some rule, at some valuation satisfying its guard and whose body atoms are
already derived, has it as head. The definition holds on the structure when
the output sentence is true with the relation variables interpreted by
these least fixed points. The output may negate the fixed-point atoms.

A decision problem $P$ over $L$ is FO(LFP) definable when some definition
holds, for every nonempty finite $L$-structure $A$ and every linear order on
$A$, exactly when $A$ is a yes-instance of $P$. This is the logic FO(LFP) of
Immerman and Vardi on ordered structures, in the normal form of one
simultaneous induction under a first-order formula.
-/

namespace Lax535992.LeastFixedPoint

open Lax485149.SecondOrderAtoms Lax535992.HornFragment Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

section Derives

variable {Lg : Language.{0, 0}} {B : SOBlock} {k : ℕ}

variable {A : Type} [Lg.Structure A]

/-- The tuples derivable by a system of rules: the least fixed point, as an
inductive predicate. A rule fires when its guard holds and all its body atoms
are already derived, and it derives its head atom. -/
inductive Derives (rules : List (HornClause Lg B k)) :
    (Σ i : B.ι, Fin (B.arity i) → A) → Prop
  | rule {c : HornClause Lg B k} (hc : c ∈ rules) {a : SOAtom B k}
      (ha : c.head = some a) {v : Fin k → A} (hg : c.guard.Realize v)
      (hb : ∀ b ∈ c.body, Derives rules ⟨b.idx, fun j => v (b.args j)⟩) :
      Derives rules ⟨a.idx, fun j => v (a.args j)⟩

/-- The least fixed point of a rule system, as an assignment of the block. -/
def lfpAssign (rules : List (HornClause Lg B k)) : B.Assignment A :=
  fun i x => Derives rules ⟨i, x⟩

end Derives

/-- A definition in FO(LFP), in clausal normal form: a block of relation
variables, a list of rules defining them inductively, and a first-order output
sentence over the vocabulary expanded by the variables, read at the least fixed
point. -/
structure LFPDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the fixed point. -/
  B : SOBlock
  /-- The number of first-order variables shared by the rules. -/
  k : ℕ
  /-- The rules defining the variables. Rules with no head derive nothing. -/
  rules : List (HornClause (L.sum Language.order) B k)
  /-- The first-order output, over the expanded vocabulary – *unrestricted*,
  in particular free to negate fixed-point atoms. -/
  out : ((L.sum Language.order).sum B.lang).Sentence

namespace LFPDef

variable {L : Language.{0, 0}} (d : LFPDef L)

/-- The value of a definition on a structure: the output read at the least
fixed point of the rules. -/
def Holds (A : Type) [L.Structure A] [LinearOrder A] : Prop :=
  @Sentence.Realize ((L.sum Language.order).sum d.B.lang) A
    (@sumStructure _ _ A _ (d.B.structure (lfpAssign d.rules))) d.out

end LFPDef

/-- A decision problem is *FO(LFP) definable* if, on nonempty finite ordered
structures, it is the value of a definition in FO(LFP). The equivalence is
required for every linear order, so the notion is order-invariant. -/
def LFPDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : LFPDef L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ d.Holds A

end Lax535992.LeastFixedPoint
