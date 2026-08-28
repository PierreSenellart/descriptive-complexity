/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrder
import DescriptiveComplexity.Vocabulary

/-!
# Declaring a second-order block

A `DescriptiveComplexity.SigmaSODefinable` witness guesses its certificate in a
`DescriptiveComplexity.SOBlock`, and its kernel is a sentence over the base
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
therefore have been declared by `DescriptiveComplexity.fo_language`, or by hand
following the same convention.

The generated declarations are the hand-written ones. The index type is a named
inductive rather than `Unit` or `Fin k` even for a single variable: a numeral
does not elaborate at the `ι` field, and a named constructor is what the
`⟨.i, rfl⟩` symbols and the assignment `ρ` read.
-/

namespace DescriptiveComplexity

open Lean Elab Command Meta FOVocabulary

/-- One relation variable of a block: `map : 2`. -/
syntax foVarDecl := (docComment)? ident " : " num

/-- Declare a `DescriptiveComplexity.SOBlock`, the summed vocabulary and every
symbol of the sum; see the module docstring. -/
syntax (name := foBlock) (docComment)?
  "fo_block " ident " over " ident ident " into " ident " with " ident " where"
    manyIndent(ppLine foVarDecl) : command

/-- Elaborate `fo_block`. -/
@[command_elab foBlock]
def elabFoBlock : CommandElab := fun stx => do
  let blockId : Ident := ⟨stx[2]⟩
  let baseLang : Ident := ⟨stx[4]⟩
  let basePfx : Name := stx[5].getId
  let sumId : Ident := ⟨stx[7]⟩
  let pfx : Name := stx[9].getId
  let vars := stx[11].getArgs.map fun d =>
    (d[0].getOptional?, (⟨d[1]⟩ : Ident), (⟨d[3]⟩ : TSyntax `num))
  let ns ← getCurrNamespace
  -- the index type of the block, and its finiteness
  let ixId := mkIdentFrom blockId (Name.mkSimple (blockId.getId.toString.capitalize ++ "Ix"))
  let ctors ← vars.mapM fun (d?, n, _) =>
    `(Lean.Parser.Command.ctor| $(docOr d? "A relation variable."):docComment | $n:ident)
  elabCommand (← `(command| $(mkDoc "The relation variables of the block."):docComment
    inductive $ixId where $ctors* deriving DecidableEq))
  let ixFull := mkIdentFrom ixId (`_root_ ++ ns ++ ixId.getId)
  let elems ← vars.mapM fun (_, n, _) => `(term| .$n)
  elabCommand (← `(command|
    instance : Fintype $ixFull := ⟨List.toFinset [$elems,*], by intro x; cases x <;> simp⟩))
  -- the block
  let arms ← vars.mapM fun (_, n, k) => `(Lean.Parser.Term.matchAltExpr| | .$n => $k)
  elabCommand (← `(command|
    $(docOr (stx[0].getOptional?) "A second-order block."):docComment
    def $blockId : DescriptiveComplexity.SOBlock where
      ι := $ixFull
      arity := fun i => match i with $arms:matchAlt*))
  let blockFull := mkIdentFrom blockId (`_root_ ++ ns ++ blockId.getId)
  -- the summed vocabulary
  elabCommand (← `(command|
    $(mkDoc "The vocabulary of the kernel: the instance expanded by the block."):docComment
    abbrev $sumId : FirstOrder.Language :=
      ($baseLang).sum (DescriptiveComplexity.SOBlock.lang $blockFull)))
  let sumFull := mkIdentFrom sumId (`_root_ ++ ns ++ sumId.getId)
  -- one symbol of the sum per symbol of the base vocabulary …
  let base ← baseSymbols (← relInductive baseLang)
  for (c, _, _) in base do
    if vars.any fun (_, n, _) => n.getId == c then
      throwError "the base vocabulary and the block both have a symbol named \
        '{c}', so both would claim the name of one symbol of the sum: rename \
        the relation variable"
  for (c, k, _) in base do
    let symId := mkIdentFrom baseLang ((prefixed pfx c).appendAfter "Sym")
    elabCommand (← `(command| $(mkDoc s!"The `{c}` symbol over the sum."):docComment
      abbrev $symId : ($sumFull).Relations $(Syntax.mkNumLit (toString k)) :=
        Sum.inl $(mkIdentFrom baseLang (prefixed basePfx c))))
  -- … and one per relation variable of the block
  for (_, n, k) in vars do
    let relId := mkIdentFrom n ((prefixed pfx n.getId).appendAfter "Rel")
    elabCommand (← `(command| $(mkDoc s!"The `{n.getId}` relation variable."):docComment
      def $relId : (DescriptiveComplexity.SOBlock.lang $blockFull).Relations $k := ⟨.$n, rfl⟩))
    let symId := mkIdentFrom n ((prefixed pfx n.getId).appendAfter "Sym")
    elabCommand (← `(command| $(mkDoc s!"The `{n.getId}` symbol over the sum."):docComment
      abbrev $symId : ($sumFull).Relations $k :=
        Sum.inr $(mkIdentFrom n (`_root_ ++ ns ++ relId.getId))))

end DescriptiveComplexity
