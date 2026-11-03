/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder
public import DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime
public import DescriptiveComplexity.Strings.Lax.FixedPointSemantics
public import DescriptiveComplexity.Strings.Lax.PolynomialTime

/-!
# The capture theorems of the Lax archive, as statements

Fagin's theorem (`lax-988886`) and the Immerman–Vardi theorem (`lax-751879`), as
stated in the archive, for the mirrored definitions of this directory. They are
propositions here, hypotheses of the bridge theorems of
`DescriptiveComplexity.Strings`, and nothing in this library proves them: a Lax
submission replaces the mirror by the two entries, where each is one application
of a registered statement.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings.Lax

/-- **Fagin's theorem**, as registered: on finite structures, an
isomorphism-invariant property is existential second-order definable exactly when
its language of encodings is in NP. -/
def FaginCaptures : Prop :=
  ∀ {σ : FiniteStructures.Vocabulary} (Q : FiniteStructures.Property σ),
    FiniteStructures.IsomorphismInvariant Q →
      (ExistentialSecondOrder.Definable Q ↔ NondeterministicPolynomialTime.InNP Q)

/-- **The Immerman–Vardi theorem**, as registered: on finite ordered structures, a
query is FO(LFP)-definable exactly when a machine decides its language of
encodings in polynomial time. -/
def ImmermanVardiCaptures : Prop :=
  ∀ {σ : OrderedStructures.Vocabulary} {k : ℕ} (Q : OrderedStructures.Query σ k),
    FixedPointSemantics.Definable Q ↔ PolynomialTime.InP Q

end DescriptiveComplexity.Strings.Lax
