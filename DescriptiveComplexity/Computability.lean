/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Computability.Realize
import DescriptiveComplexity.Computability.FinStruct
import DescriptiveComplexity.Computability.Vocab
import DescriptiveComplexity.Computability.Eval
import DescriptiveComplexity.Computability.REPred
import DescriptiveComplexity.Computability.Reduction
import DescriptiveComplexity.Computability.Catalog

/-!
# The bridge to Mathlib's computability layer

Umbrella file for the passage from *problems* – isomorphism-closed properties
of finite structures – to *sets of naturals*, on which `ComputablePred` and
`REPred` are defined. The layer is generic: it is built once for the whole
catalog, and a problem needs nothing of its own to be read through it beyond a
list of the symbols of its vocabulary.

## The layer, in four steps

1. `DescriptiveComplexity.Computability.Realize` – satisfaction of a
   first-order formula is *decidable* on a finite structure with decidable
   relations. Small, self-contained, and the first formal justification of the
   claim, elsewhere by inspection, that first-order interpretations are
   effective.
2. `DescriptiveComplexity.Computability.FinStruct` – a finite structure over a
   finitely presented relational vocabulary, as data: a universe `Fin (n + 1)`
   and a list of Boolean tables. This is the `Primcodable` type, and the
   universe is nonempty and linearly ordered by construction – which is what
   an *ordered* reduction would need, with no order to encode.
   `DescriptiveComplexity.Computability.Vocab` presents the vocabularies, and
   in particular closes the presentations under `Language.sum`.
3. `DescriptiveComplexity.Computability.Eval` – for each *fixed* formula, the
   evaluation of that formula on a concrete structure is **primitive
   recursive**. Everything else is an application of this.
4. `DescriptiveComplexity.Computability.REPred` – **`RE ⊆ REPred`**: a problem
   definable in `∃SO[new]` denotes a recursively enumerable set of concrete
   instances. The `∃SO[new]` certificate – a number of invented values and an
   assignment of the relation variables – is a finite object, so it is
   searched for; the first-order kernel is checked on it by (3). No machine
   model is involved anywhere.
   `DescriptiveComplexity.Computability.Catalog` reads this at the two
   problems the machine bridge is about
   (`DescriptiveComplexity.halt_rePred`, `DescriptiveComplexity.finsat_rePred`).
5. `DescriptiveComplexity.Computability.Reduction` – **first-order reductions
   are computable**, so `¬ComputablePred` transfers backwards along `≤ᶠᵒ`,
   `≤ᶠᵒ[≤]` and `≤ʳᶠᵒ[≤]`
   (`DescriptiveComplexity.not_computablePred_of_relOrderedReduction` and its
   two corollaries). Three things have to be computed: the order (free – the
   universe of a concrete instance is already `Fin (n + 1)`), the renumbering
   forced by a definable target domain, and the tags of a defining formula,
   which are known only at run time.

## What this layer does not yet do

Nothing here says *undecidable*, and exactly one step is missing: a
**computable map of a known-undecidable set** into concrete machine instances,
i.e. the simulation of Mathlib's halting problem by a
`DescriptiveComplexity.TMData` (`ROADMAP.md` §8, which records why Mathlib's
`Nat.Partrec.Code` chain does not supply it). Everything downstream of it is in
place – `DescriptiveComplexity.finsat_not_computable_of_halt` is Trakhtenbrot's
theorem with that single hypothesis left open.
-/
