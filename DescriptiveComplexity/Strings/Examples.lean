/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import DescriptiveComplexity.Problems.Sat.Hardness
public import DescriptiveComplexity.Problems.ThreeColorability
public import DescriptiveComplexity.Problems.CliqueFamily
public import DescriptiveComplexity.Problems.HornSat
public import DescriptiveComplexity.Strings.NP
public import DescriptiveComplexity.Strings.PTime
public import DescriptiveComplexity.Strings.VocabCommand

/-!
# Problems of the catalog, on bit strings

Three vocabularies of the catalog, numbered, and what the bridge says of some of their
problems: the language of the binary encodings of the yes-instances of SAT,
3-colorability, or clique has polynomially checked certificates, and that of HORN-SAT is
decided in polynomial time.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings

open FirstOrder
open Lax.FiniteStructures Lax.NondeterministicPolynomialTime Lax.PolynomialTime

fo_fin_vocab satVocab := Language.sat

fo_fin_vocab markedGraphVocab := Language.markedGraph

/-- The numbering of the only symbol of `Language.graph`. -/
noncomputable def graphVocab : FinVocab Language.graph :=
  .ofList [⟨2, Language.graphRel.adj⟩] (by simp) (by rintro ⟨_, r⟩; cases r; simp)

/-- The encodings of satisfiable CNF instances form a language in NP. -/
theorem SAT_languageInNP (h : Lax.FaginCaptures) :
    LanguageInNP (language (toProperty satVocab SAT)) :=
  (mem_NP_iff_languageInNP h satVocab SAT).mp SAT_NP_complete.1

/-- The encodings of 3-colorable graphs form a language in NP. -/
theorem threeCol_languageInNP (h : Lax.FaginCaptures) :
    LanguageInNP (language (toProperty graphVocab ThreeCol)) :=
  (mem_NP_iff_languageInNP h graphVocab ThreeCol).mp threeCol_NP_complete.1

/-- The encodings of the yes-instances of Clique form a language in NP. -/
theorem clique_languageInNP (h : Lax.FaginCaptures) :
    LanguageInNP (language (toProperty markedGraphVocab Clique)) :=
  (mem_NP_iff_languageInNP h markedGraphVocab Clique).mp clique_NP_complete.1

/-- A polynomial-time machine decides the encodings of the satisfiable Horn instances. -/
theorem HORNSAT_inP (h : Lax.ImmermanVardiCaptures) : InP (toQuery satVocab HORNSAT) :=
  (mem_PTIME_iff_inP h satVocab HORNSAT).mp HORNSAT_PTIME_complete.1

end DescriptiveComplexity.Strings
