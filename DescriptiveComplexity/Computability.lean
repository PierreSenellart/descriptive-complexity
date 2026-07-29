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
import DescriptiveComplexity.Computability.CodeHalt

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

6. `DescriptiveComplexity.Computability.CodeHalt` – **undecidability**. The
   known-undecidable set is Mathlib's halting problem, and it is carried into
   the catalog by making the *code the instance*: a
   `Nat.Partrec.Code` is drawn as its syntax tree
   (`DescriptiveComplexity.codeStruct`), which is a plain tree flattening and
   so primitive recursive, and the problem
   `DescriptiveComplexity.CODEHALT` asks whether the drawn code halts on `0`.
   Whence `DescriptiveComplexity.not_computablePred_codehalt`: the library's
   first problem proved **undecidable outright**. With
   `DescriptiveComplexity.codehalt_mem_RE` it gives
   `DescriptiveComplexity.not_computablePred_of_RE_hard` – *every* RE-hard
   problem is undecidable, since hardness here is cofinal and reductions are
   computable – and hence
   `DescriptiveComplexity.finsat_not_computable`, Trakhtenbrot's theorem.

## What this layer does not yet do

Only one inclusion, `RE ⊆ REPred`. The converse, that every recursively
enumerable predicate is `∃SO[new]`-definable, is the RE machine bridge and is
priced in `ROADMAP.md` (§7, §8): it needs an evaluator with addressed storage,
and nothing here approaches it. So a problem shown to be in RE is honestly
semi-decidable, but a semi-decidable problem is not thereby known to be in the
library's RE.
-/
