/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Block
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.Exponential.Expansion
import DescriptiveComplexity.Exponential.Pull
import DescriptiveComplexity.Exponential.Order
import DescriptiveComplexity.Exponential.OrdFormula
import DescriptiveComplexity.Exponential.OrdExtend
import DescriptiveComplexity.Exponential.Class
import DescriptiveComplexity.Exponential.SecondOrderFixedPoint
import DescriptiveComplexity.Exponential.Classes
import DescriptiveComplexity.Exponential.Reach
import DescriptiveComplexity.Exponential.Inclusions

/-!
# The exponential classes, by expansion

EXPTIME, NEXPTIME and EXPSPACE, defined by reading the polynomial-level logics
over a universe that is one exponential larger.

## The idea in one line

> A **second-order** fixed point is a first-order fixed point **read over a
> structure whose universe is the assignments of a second-order block**.

A block with a variable of arity `a` has `2^(n^a)` assignments on a universe of
size `n`. An **exponential expansion** (`DescriptiveComplexity.ExpExpansion`)
maps a finite ordered `L`-structure `A` to a structure whose universe is a
definable set of tagged block assignments, each relation being defined by a
first-order sentence over the base vocabulary expanded by as many copies of the
block as the symbol has arguments. Reading a class `C` there is the operator
`DescriptiveComplexity.ComplexityClass.exp`, and

```
EXPTIME := SO(≤, LFP)        EXPSPACE := SO(≤, PFP)        NEXPTIME := NP.exp
EXPTIME  = PTIME.exp         EXPSPACE  = PSPACE.exp
```

the first two equalities being theorems
(`DescriptiveComplexity.EXPTIME_eq_PTIME_exp`,
`DescriptiveComplexity.EXPSPACE_eq_PSPACE_exp`) that hold because the library
already proves FO(≤, LFP) = PTIME and FO(≤, PFP) = PSPACE: they are those two
capture theorems read on the expanded universe.

No third-order syntax is introduced and none is needed: the expansion has
already made the second-order objects the first-order elements of a new sort,
which is the type-lowering translation of higher-order logic into many-sorted
first-order logic over the power type ([Henkin 1950][henkin1950completeness]).

## What the design buys

`exp` is an operator on an **abstract**
`DescriptiveComplexity.ComplexityClass`, so the structural results transfer
instead of being reproved:

* `DescriptiveComplexity.ComplexityClass.exp_compl` carries closure under
  complement one exponential up, whence `EXPTIME = coEXPTIME` from
  `DescriptiveComplexity.piP_zero_eq` and `EXPSPACE = coEXPSPACE` from
  `DescriptiveComplexity.PSPACE_eq_coPSPACE` – two facts that each cost a large
  development, and neither is spent twice;
* `DescriptiveComplexity.ComplexityClass.exp_mono` carries every
  polynomial-level inclusion, whence `EXPTIME ⊆ NEXPTIME ⊆ EXPSPACE` and
  `EXPTIME ⊆ EXPSPACE` (which reads, on the definitions, **SO(LFP) ⊆
  SO(PFP)**).

The one inclusion with content is `DescriptiveComplexity.PSPACE_subset_EXPTIME`:
an `DescriptiveComplexity.SOTCSpec` *is* the graph REACH reads on the expansion
whose points are its states, so SO(TC) ⊆ SO(LFP) – the second-order shadow of
`NL ⊆ PTIME`. It also gives `PSPACE ⊆ NL.exp`, and `NL.exp ⊆ EXPTIME` comes
back by monotonicity.

## The expanded universe is ordered, definably

An expansion's own universe carries a linear order — tag first, then the
assignment read as a **binary number**, `ρ` below `σ` at the least atom where
they differ (`DescriptiveComplexity.ExpExpansion.mapLinearOrder`) — and that
order is itself **first-order definable over the base**
(`DescriptiveComplexity.SOBlock.realize_ordLtF`), because a padded atom is one
of finitely many relation variables together with a tuple of *base* elements.
`DescriptiveComplexity.ExpExpansion.ordExtend` adds the order symbol to the
expanded vocabulary and defines it that way, exactly as
`DescriptiveComplexity.FOInterpretation.ordExtend` does one level down.

This is what any composition reading an expansion's order needs. It is not by
itself enough for such a composition: an interpretation's *quantifiers* range
over the points of the expanded universe, hence over block assignments, which
is a second-order condition over the base — see `ROADMAP.md` §3.

## Layout

| file | content |
|---|---|
| `Exponential.Block` | `SOBlock.replicate`, commuting with the block pullback |
| `Exponential.Copies` | reading stacked block expansions inside a replicated one |
| `Exponential.Expansion` | `ExpExpansion`, its universe, its expanded structure |
| `Exponential.Pull` | an interpretation followed by an expansion is an expansion |
| `Exponential.Order` | the order on an expanded universe, semantically |
| `Exponential.OrdFormula` | that order as a first-order sentence, and its correctness |
| `Exponential.OrdExtend` | the expansion extended with its own order |
| `Exponential.Class` | `ExpDefinable`, `ComplexityClass.exp`, `exp_mono`, `exp_compl` |
| `Exponential.SecondOrderFixedPoint` | SO(LFP), SO(PFP) and the two bridge theorems |
| `Exponential.Classes` | EXPTIME, NEXPTIME, EXPSPACE and their hardness discharges |
| `Exponential.Reach` | an SO(TC) walk is REACH on an expansion |
| `Exponential.Inclusions` | the complement equalities and the inclusions |

## Literature

The succinctness upgrade is [Galperin–Wigderson 1983][galperin1983succinct],
[Papadimitriou–Yannakakis 1986][papadimitriou1986note] and, in general form,
[Veith 1998][veith1998succinct]. Naming the deterministic classes after their
fixpoint logics follows [Abiteboul–Vardi–Vianu
1997][abiteboul1997fixpoint]; that work is stated in the relational
(order-free, generic) setting, so it is cited here as motivation for the
*names* and never as a capture theorem – SO(LFP) and SO(PFP) are definitions in
this development, and what is proved in their place are the bridge theorems
above. For NEXPTIME the literature's characterization is existential
*third*-order logic ([Leivant 1989][leivant1989descriptive];
[Hella–Turull-Torres 2006][hella2006higher]); this development does not build a
third-order syntax layer and so does not state that equivalence – an honest and
narrow gap, recorded in `DescriptiveComplexity.Exponential.Classes`.
-/
