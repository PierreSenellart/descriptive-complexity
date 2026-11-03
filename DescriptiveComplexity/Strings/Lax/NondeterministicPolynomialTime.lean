/-
Mirror of `Lax988886.NondeterministicPolynomialTime`: lax-988886, “Fagin's theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/fagin at commit
333e9cbdbd8a389561da30908cabf36051048a13. Released under Apache 2.0 license.
-/
module

public import DescriptiveComplexity.Strings.Lax.FiniteStructures
public import Mathlib.Computability.TuringMachine.Computable

/-!
# NP through polynomially bounded certificates

A bit-string language belongs to NP if membership is equivalent to the existence
of a certificate of polynomially bounded length accepted by a deterministic
polynomial-time verifier: the usual certificate definition of NP, the verifier
being a concrete finite multi-stack Turing machine of Mathlib with its
machine-step polynomial bound.

The verifier reads a pair of bit strings: each input bit is preceded by a
one-bit, a zero-bit terminates the input, and the remaining bits form the
certificate. A property belongs to NP when its language of structure encodings
does; the language excludes malformed encodings.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime

open FiniteStructures

/-- The uniquely decodable encoding of a pair of bit strings. -/
def encodePair (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ false :: p.2

/-- A bit-string language with polynomially bounded certificates, polynomially checked. -/
def LanguageInNP (L : List Bool → Prop) : Prop :=
  ∃ (V : List Bool × List Bool → Bool) (p : Polynomial Nat),
    Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) V) ∧
    ∀ w, L w ↔ ∃ c : List Bool, c.length ≤ p.eval w.length ∧ V (w, c) = true

/-- A property whose language of encodings is in NP. -/
def InNP {σ : Vocabulary} (Q : Property σ) : Prop :=
  LanguageInNP (language Q)

end DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime
