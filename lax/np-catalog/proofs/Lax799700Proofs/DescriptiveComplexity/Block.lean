/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
import Lax799700Proofs.DescriptiveComplexity.Vocabulary
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
# Declaring a second-order block

A `Lax799700Proofs.DescriptiveComplexity.SigmaSODefinable` witness guesses its certificate in a
`Lax799700Proofs.DescriptiveComplexity.SOBlock`, and its kernel is a sentence over the base
vocabulary summed with the block's. Setting that up means an index type with a
`Fintype` instance, the block itself, one `⟨.i, rfl⟩` symbol per relation
variable, the summed language, and – for *every* symbol of the base vocabulary
as well – an abbreviation injecting it into the sum. None of that is guessable
from the mathematics, and all of it is determined by the arities.

`fo_block` writes it:

```
/-- The existential block of Subgraph Isomorphism. -/
fo_block isoGuessBlock over Language.twoGraphs tg into subgraphSOLang with sg where
  /-- The guessed map from the pattern to the host. -/
  map : 2
```

reads the symbols of `Language.twoGraphs` out of the environment, and declares
`IsoGuessBlockIx` (with `DecidableEq` and `Fintype`), `isoGuessBlock`,
`subgraphSOLang`, the relation variable `sgMapRel`, and the symbols of the sum:
`sgPatVSym`, `sgHostVSym`, `sgPatESym`, `sgHostESym` on the left and `sgMapSym`
on the right. The base vocabulary is named with the prefix its symbols carry,
so that the command can find `tgPatV` from the constructor `patV`; it must
therefore have been declared by `Lax799700Proofs.DescriptiveComplexity.fo_language`, or by hand
following the same convention.

The generated declarations are the hand-written ones. The index type is a named
inductive rather than `Unit` or `Fin k` even for a single variable: a numeral
does not elaborate at the `ι` field, and a named constructor is what the
`⟨.i, rfl⟩` symbols and the assignment `ρ` read.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open Lean Elab Command Meta FOVocabulary

/-- One relation variable of a block: `map : 2`. -/
syntax foVarDecl := (docComment)? ident " : " num

/-- Declare a `Lax799700Proofs.DescriptiveComplexity.SOBlock`, the summed vocabulary and every
symbol of the sum; see the module docstring. -/
syntax (name := foBlock) (docComment)?
  "fo_block " ident " over " ident ident " into " ident " with " ident " where"
    manyIndent(ppLine foVarDecl) : command

end Lax799700Proofs.DescriptiveComplexity


