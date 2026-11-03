/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import DescriptiveComplexity.Hierarchy
public import DescriptiveComplexity.Strings.ExistentialSecondOrder
public import DescriptiveComplexity.Strings.Lax.Captures

/-!
# The class NP, against certificates checked by a machine

The class `DescriptiveComplexity.NP` of this library is defined by second-order
logic. The theorems of this file say that, over a vocabulary with finitely many
relation symbols, it is the textbook class: a problem belongs to it exactly when the
language of the binary encodings of its yes-instances has polynomially bounded
certificates checked by a polynomial-time Mathlib `Turing.FinTM2`.

The logical half, `DescriptiveComplexity.Strings.mem_NP_iff_definable`, is
unconditional. The machine half takes Fagin's theorem as a hypothesis
(`DescriptiveComplexity.Strings.Lax.FaginCaptures`), which the Lax archive registers
as `lax-988886`.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings

open FirstOrder
open Lax.FiniteStructures Lax.NondeterministicPolynomialTime

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A problem is in `NP` exactly when it reads as a property of the archive's structures
defined by an existential second-order sentence of the archive.
Registered in the Lax archive as
[`Lax832283.LogicalBridge.mem_NP_iff_definable`](https://laxarchive.org/lax-832283/Lax832283.LogicalBridge.html#s-Lax832283.LogicalBridge.mem_NP_iff_definable). -/
theorem mem_NP_iff_definable (V : FinVocab L) (P : DecisionProblem L) :
    P ∈ NP ↔ Lax.ExistentialSecondOrder.Definable (toProperty V P) :=
  sigmaSODefinable_one_iff V P

/-- **`NP` is the textbook class**: from Fagin's theorem, a problem is in `NP` exactly
when the property it reads as is in NP as the archive defines it.
Registered in the Lax archive as
[`Lax832283.MachineBridge.mem_NP_iff_inNP`](https://laxarchive.org/lax-832283/Lax832283.MachineBridge.html#s-Lax832283.MachineBridge.mem_NP_iff_inNP). -/
theorem mem_NP_iff_inNP (h : Lax.FaginCaptures) (V : FinVocab L) (P : DecisionProblem L) :
    P ∈ NP ↔ InNP (toProperty V P) :=
  (mem_NP_iff_definable V P).trans (h _ (toProperty_isoInvariant V P))

/-- **`NP`, on bit strings**: from Fagin's theorem, a problem is in `NP` exactly when the
language of the binary encodings of its yes-instances has polynomially bounded
certificates that a machine checks in polynomial time.
Registered in the Lax archive as
[`Lax832283.MachineBridge.mem_NP_iff_languageInNP`](https://laxarchive.org/lax-832283/Lax832283.MachineBridge.html#s-Lax832283.MachineBridge.mem_NP_iff_languageInNP). -/
theorem mem_NP_iff_languageInNP (h : Lax.FaginCaptures) (V : FinVocab L)
    (P : DecisionProblem L) :
    P ∈ NP ↔ LanguageInNP (language (toProperty V P)) :=
  mem_NP_iff_inNP h V P

/-- **`coNP`, by its complement problem**: from Fagin's theorem, a problem is in `coNP`
exactly when its complement reads as a property in NP as the archive defines it. -/
theorem mem_coNP_iff_inNP_compl (h : Lax.FaginCaptures) (V : FinVocab L)
    (P : DecisionProblem L) :
    P ∈ coNP ↔ InNP (toProperty V Pᶜ) :=
  (mem_piP_iff 1 P).trans (mem_NP_iff_inNP h V Pᶜ)

end DescriptiveComplexity.Strings
