/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lean.Elab.Command
import DescriptiveComplexity.Vocabulary
import DescriptiveComplexity.Strings.Vocab

/-!
# Numbering a vocabulary declared by `fo_language`

`fo_fin_vocab satVocab := Language.sat` declares the
`DescriptiveComplexity.Strings.FinVocab` numbering the symbols of a vocabulary declared
by `fo_language`, in the order of their declaration. It reads the symbols out of the
environment, as `fo_predicates` does. The numbering stays a command of its own so that a
vocabulary, which every problem of the catalog starts from, need not import the string
side of the library.
-/

namespace DescriptiveComplexity.Strings

open Lean Elab Command

/-- Declare the numbering of the symbols of a vocabulary declared by `fo_language`, in the
order of their declaration. -/
syntax (name := foFinVocab) "fo_fin_vocab " ident " := " ident : command

open FOVocabulary in
/-- Elaborate `fo_fin_vocab`. -/
@[command_elab foFinVocab]
def elabFoFinVocab : CommandElab := fun stx => do
  let name : Ident := ⟨stx[1]⟩
  let langId : Ident := ⟨stx[3]⟩
  let relName ← relInductive langId
  let syms ← baseSymbols relName
  let items ← syms.mapM fun (c, k, _) => do
    let ctor := mkCIdent (relName ++ c)
    let kstx := Syntax.mkNumLit (toString k)
    `(term| ⟨$kstx, $ctor:ident⟩)
  elabCommand (← `(command|
    $(mkDoc s!"The numbering of the symbols of `{langId.getId}`, in the order of their \
      declaration."):docComment
    noncomputable def $name : DescriptiveComplexity.Strings.FinVocab $langId :=
      DescriptiveComplexity.Strings.FinVocab.ofList [$items,*]
        (by simp [$langId:ident])
        (by rintro ⟨_, r⟩; cases r <;> simp)))

end DescriptiveComplexity.Strings
