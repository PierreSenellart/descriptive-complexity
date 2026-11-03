/-
Mirror of `Lax751879.PolynomialTime`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
module

public import DescriptiveComplexity.Strings.Lax.StructureEncoding
public import Mathlib.Computability.TuringMachine.Computable

/-!
# Polynomial-time queries on ordered structures

A query is polynomial-time decidable when a finite deterministic Turing machine
decides the language of encodings of its satisfying pointed structures within a
polynomial in the input bit length. Malformed encodings are rejected. The machine
and polynomial are fixed for the query.

The machine model and step count are Mathlib's bundled finite multi-stack Turing
machines (`Turing.TM2ComputableInPolyTime`), with identity encoding on input bit
strings and a single output bit.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings.Lax.PolynomialTime

open OrderedStructures StructureEncoding

/-- The language of the encodings of the pointed structures satisfying a query. -/
def language {σ : Vocabulary} {k : Nat} (Q : Query σ k) (w : List Bool) : Prop :=
  ∃ A : PointedStructure σ k, encode A = w ∧ Q A

/-- A query whose language a machine decides in polynomial time. -/
def InP {σ : Vocabulary} {k : Nat} (Q : Query σ k) : Prop :=
  ∃ f : List Bool → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime id (fun b => [b]) f) ∧
    ∀ w, f w = true ↔ language Q w

end DescriptiveComplexity.Strings.Lax.PolynomialTime
