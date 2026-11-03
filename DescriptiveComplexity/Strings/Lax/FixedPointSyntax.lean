/-
Mirror of `Lax751879.FixedPointSyntax`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
module

public import DescriptiveComplexity.Strings.Lax.OrderedStructures

/-!
# First-order logic with least fixed points

FO(LFP) extends first-order logic with `[lfp_{R, x̄} φ](ȳ)`, where every
occurrence of `R` in `φ` is positive (under an even number of negations). Fixed
points may be nested, negated, and have free first-order parameters. Equality,
order, relation atoms, negation, conjunction, and existential quantification
form the first-order basis; truth is included explicitly.

The indices record the number of available element variables and the arities of
available relation variables. A quantifier binds element variable zero. A fixed
point binds relation variable zero and the first `k` element variables of its
body; the remaining variables are parameters.

Raw syntax is separated from admissibility solely to express the positivity
check. A `Formula` always includes admissibility at every nested fixed point.
`positiveAt` traverses nested binders, shifting the relation-variable index, and
tracks the parity of negations.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings.Lax.FixedPointSyntax

open OrderedStructures

/-- The raw syntax of FO(LFP). -/
inductive RawFormula (σ : Vocabulary) : Nat → List Nat → Type
  | truth {m ρ} : RawFormula σ m ρ
  | equal {m ρ} (x y : Fin m) : RawFormula σ m ρ
  | less {m ρ} (x y : Fin m) : RawFormula σ m ρ
  | relation {m ρ} (r : Symbol σ) (args : Fin (σ.get r) → Fin m) :
      RawFormula σ m ρ
  | variable {m ρ} (r : Fin ρ.length) (args : Fin (ρ.get r) → Fin m) :
      RawFormula σ m ρ
  | neg {m ρ} (φ : RawFormula σ m ρ) : RawFormula σ m ρ
  | conj {m ρ} (φ ψ : RawFormula σ m ρ) : RawFormula σ m ρ
  | exists' {m ρ} (φ : RawFormula σ (m + 1) ρ) : RawFormula σ m ρ
  | lfp {m ρ} (k : Nat) (body : RawFormula σ (k + m) (k :: ρ))
      (args : Fin k → Fin m) : RawFormula σ m ρ

/-- Every occurrence of `r` has the required polarity. `true` means positive. -/
def RawFormula.positiveAt {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (r : Fin ρ.length) (polarity : Bool) : Prop :=
  match φ with
  | .truth | .equal _ _ | .less _ _ | .relation _ _ => True
  | .variable s _ => s = r → polarity = true
  | .neg ψ => ψ.positiveAt r (!polarity)
  | .conj ψ χ => ψ.positiveAt r polarity ∧ χ.positiveAt r polarity
  | .exists' ψ => ψ.positiveAt r polarity
  | .lfp _ body _ => body.positiveAt r.succ polarity

/-- Every fixed-point binder has a positive defining body. -/
def RawFormula.Admissible {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) : Prop :=
  match φ with
  | .truth | .equal _ _ | .less _ _ | .relation _ _ | .variable _ _ => True
  | .neg ψ | .exists' ψ => ψ.Admissible
  | .conj ψ χ => ψ.Admissible ∧ χ.Admissible
  | .lfp _ body _ => body.Admissible ∧ body.positiveAt 0 true

/-- An admissible formula, with no free relation variable. -/
abbrev Formula (σ : Vocabulary) (m : Nat) :=
  {φ : RawFormula σ m [] // φ.Admissible}

/-- An admissible formula with no free variable at all. -/
abbrev Sentence (σ : Vocabulary) := Formula σ 0

end DescriptiveComplexity.Strings.Lax.FixedPointSyntax
