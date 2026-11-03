/-
Mirror of `Lax751879.FixedPointSemantics`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.LeastFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax751879.FixedPointSemantics
import Lax751879.FixedPointSyntax
import Lax751879.LeastFixedPoints
import Lax751879.OrderedStructures
import Lax751879.PolynomialTime
import Lax751879.StructureEncoding
import Lax832283.StringProblems
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax988886.ExistentialSecondOrder
import Lax988886.FiniteStructures
import Lax988886.NondeterministicPolynomialTime

namespace Lax751879.FixedPointSemantics
end Lax751879.FixedPointSemantics

namespace Lax751879.FixedPointSyntax
end Lax751879.FixedPointSyntax

namespace Lax751879.LeastFixedPoints
end Lax751879.LeastFixedPoints

namespace Lax751879.OrderedStructures
end Lax751879.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (OrderedStructure PointedStructure Query Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.LeastFixedPoints
export Lax751879.LeastFixedPoints (leastFixedPoint)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.LeastFixedPoints

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax
export Lax751879.FixedPointSyntax (Formula RawFormula)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics
export Lax751879.FixedPointSemantics (Definable RelationEnv Satisfies bodyOperator eval extend)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics

/-!
# Semantics and definability in FO(LFP)

First-order operations have their usual semantics. A fixed-point body, with its
parameters held fixed, defines an operator on `k`-ary relations; the fixed-point
formula tests membership of its argument tuple in the least fixed point of that
operator. Positivity of an admissible body implies monotonicity
(`positiveBodyMonotone`).

A query is FO(LFP)-definable if one admissible formula defines it on every
finite ordered structure and every assignment to its free variables. The formula
is chosen once for the query, independently of the structure.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics

open OrderedStructures FixedPointSyntax LeastFixedPoints

/-- Two environments agree everywhere but at `r`, where they are ordered. -/
private def EnvLE {n : Nat} {ρ : List Nat} (r : Fin ρ.length)
    (η η' : Lax751879.FixedPointSemantics.RelationEnv n ρ) : Prop :=
  η r ⊆ η' r ∧ ∀ s, s ≠ r → η s = η' s

private theorem EnvLE.extend {n k : Nat} {ρ : List Nat} {r : Fin ρ.length}
    {η η' : Lax751879.FixedPointSemantics.RelationEnv n ρ} (h : EnvLE r η η') (R : Set (Fin k → Fin n)) :
    EnvLE (ρ := k :: ρ) r.succ (Lax751879.FixedPointSemantics.extend R η)
      (Lax751879.FixedPointSemantics.extend R η') := by
  refine ⟨h.1, fun s => ?_⟩
  refine Fin.cases (fun _ => rfl) (fun s (hs : Fin.succ s ≠ r.succ) => ?_) s
  exact h.2 s fun e => hs (congrArg Fin.succ e)

/-- A formula with the required polarity at `r` varies with `η r` accordingly: up when the
polarity is positive, down when it is negative. -/
private theorem eval_mono_polarity {σ : Lax751879.OrderedStructures.Vocabulary} {A : Lax751879.OrderedStructures.OrderedStructure σ} {m : Nat}
    {ρ : List Nat} (φ : Lax751879.FixedPointSyntax.RawFormula σ m ρ) (r : Fin ρ.length) (p : Bool)
    (hφ : φ.Admissible) (hp : φ.positiveAt r p) (v : Fin m → Fin A.size)
    {η η' : Lax751879.FixedPointSemantics.RelationEnv A.size ρ} (hη : EnvLE r η η') :
    (p = true → Lax751879.FixedPointSemantics.eval φ A v η → Lax751879.FixedPointSemantics.eval φ A v η') ∧
      (p = false → Lax751879.FixedPointSemantics.eval φ A v η' → Lax751879.FixedPointSemantics.eval φ A v η) := by
  induction φ generalizing p with
  | truth | equal | less | relation =>
    exact ⟨fun _ h => h, fun _ h => h⟩
  | @«variable» m ρ s args =>
    by_cases hs : s = r
    · subst hs
      have hpt : p = true := hp rfl
      refine ⟨fun _ h => hη.1 h, fun hf => absurd hpt (by simp [hf])⟩
    · have := hη.2 s hs
      simp only [Lax751879.FixedPointSemantics.eval, this]
      exact ⟨fun _ h => h, fun _ h => h⟩
  | neg ψ ih =>
    have := ih r (!p) hφ hp v hη
    cases p with
    | true => exact ⟨fun _ h h' => h (this.2 rfl h'), by simp⟩
    | false => exact ⟨by simp, fun _ h h' => h (this.1 rfl h')⟩
  | conj ψ χ ih₁ ih₂ =>
    have h₁ := ih₁ r p hφ.1 hp.1 v hη
    have h₂ := ih₂ r p hφ.2 hp.2 v hη
    exact ⟨fun e h => ⟨h₁.1 e h.1, h₂.1 e h.2⟩, fun e h => ⟨h₁.2 e h.1, h₂.2 e h.2⟩⟩
  | exists' ψ ih =>
    exact ⟨fun e ⟨a, h⟩ => ⟨a, (ih r p hφ hp (Fin.cons a v) hη).1 e h⟩,
      fun e ⟨a, h⟩ => ⟨a, (ih r p hφ hp (Fin.cons a v) hη).2 e h⟩⟩
  | lfp k body args ih =>
    have hmono : ∀ η₀ : Lax751879.FixedPointSemantics.RelationEnv A.size _,
        Monotone (fun R => {a | Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η₀)}) := by
      intro η₀ R R' hR a ha
      exact (ih 0 true hφ.1 hφ.2 _ (η := Lax751879.FixedPointSemantics.extend R η₀) (η' := Lax751879.FixedPointSemantics.extend R' η₀)
        ⟨hR, fun s => Fin.cases (fun h => absurd rfl h) (fun s _ => rfl) s⟩).1 rfl ha
    have hop : ∀ (R : Set (Fin k → Fin A.size)) (a : Fin k → Fin A.size),
        (p = true → Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η) →
          Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η')) ∧
        (p = false → Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η') →
          Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η)) :=
      fun R a => ih r.succ p hφ.1 hp _ (hη.extend R)
    refine ⟨fun e h => ?_, fun e h => ?_⟩
    · refine least (fun R => {a | Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η)})
        (Lax751879.LeastFixedPoints.leastFixedPoint fun R => {a | Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η')}) ?_ h
      intro a ha
      exact (fixedPoint _ (hmono η')).subset ((hop _ a).1 e ha)
    · refine least (fun R => {a | Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η')})
        (Lax751879.LeastFixedPoints.leastFixedPoint fun R => {a | Lax751879.FixedPointSemantics.eval body A (Fin.append a v) (Lax751879.FixedPointSemantics.extend R η)}) ?_ h
      intro a ha
      exact (fixedPoint _ (hmono η)).subset ((hop _ a).2 e ha)

theorem positiveBodyMonotone {σ : Lax751879.OrderedStructures.Vocabulary} {m k : Nat} {ρ : List Nat}
    (body : Lax751879.FixedPointSyntax.RawFormula σ (k + m) (k :: ρ))
    (hbody : body.Admissible) (hpositive : body.positiveAt 0 true)
    (A : Lax751879.OrderedStructures.OrderedStructure σ) (v : Fin m → Fin A.size)
    (η : Lax751879.FixedPointSemantics.RelationEnv A.size ρ) : Monotone (Lax751879.FixedPointSemantics.bodyOperator body A v η) := by
  intro R R' hR a ha
  exact (eval_mono_polarity body 0 true hbody hpositive _
    (η := Lax751879.FixedPointSemantics.extend R η) (η' := Lax751879.FixedPointSemantics.extend R' η)
    ⟨hR, fun s => Fin.cases (fun h => absurd rfl h) (fun s _ => rfl) s⟩).1 rfl ha

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics


