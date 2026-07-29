/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CodeHalt.Defs
import DescriptiveComplexity.Problems.CodeHalt.Membership

/-!
# CODEHALT: does the partial recursive code drawn in the instance halt?

The umbrella of the `CODEHALT` files. The instance is a **syntax tree**, one
element per node, and the yes-instances are those whose root draws a
`Nat.Partrec.Code` halting on `0` (`DescriptiveComplexity.CODEHALT`, in
`DescriptiveComplexity.Problems.CodeHalt.Defs`).

It is the problem the undecidability of the whole development goes through, and
it has both halves:

* **membership** – `DescriptiveComplexity.codehalt_mem_RE`: the computation of
  the drawn code is *invented*, as a numeral segment carrying its arithmetic and
  its intermediate values, and a first-order kernel checks that every fact of it
  is justified by a rule of the code it is about
  (`DescriptiveComplexity.Problems.CodeHalt.Cert` for the mathematics,
  `DescriptiveComplexity.Problems.CodeHalt.Membership` for the syntax);
* **undecidability** – `DescriptiveComplexity.not_computablePred_codehalt`, in
  `DescriptiveComplexity.Computability.CodeHalt`: the map `code ↦ instance` is a
  plain tree flattening, hence primitive recursive, so Mathlib's halting problem
  maps into it. No machine is simulated anywhere: the code *is* the instance.

Together with the RE-hardness of `DescriptiveComplexity.FINSAT` the two give
`DescriptiveComplexity.finsat_not_computable`, Trakhtenbrot's theorem.

RE-*hardness* of `CODEHALT` is not proved, and is not needed for any of this.
-/
