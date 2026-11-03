/-
Mirror of `Lax751879.FixedPointSemantics`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import DescriptiveComplexity.Strings.Lax.FixedPointSyntax
import DescriptiveComplexity.Strings.Lax.LeastFixedPoints

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

namespace DescriptiveComplexity.Strings.Lax.FixedPointSemantics

open OrderedStructures FixedPointSyntax LeastFixedPoints

/-- An assignment of relations to the relation variables. -/
abbrev RelationEnv (n : Nat) (ρ : List Nat) :=
  (r : Fin ρ.length) → Set (Fin (ρ.get r) → Fin n)

/-- Bind relation variable zero. -/
def extend {n k : Nat} {ρ : List Nat} (R : Set (Fin k → Fin n))
    (η : RelationEnv n ρ) : RelationEnv n (k :: ρ) :=
  Fin.cons R η

/-- The semantics of FO(LFP). -/
def eval {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) : Prop :=
  match φ with
  | .truth => True
  | .equal x y => v x = v y
  | .less x y => v x < v y
  | .relation r args => A.relation r (v ∘ args) = true
  | .variable r args => η r (v ∘ args)
  | .neg ψ => ¬ eval ψ A v η
  | .conj ψ χ => eval ψ A v η ∧ eval χ A v η
  | .exists' ψ => ∃ a, eval ψ A (Fin.cons a v) η
  | .lfp _ body args =>
      leastFixedPoint (fun R => {a | eval body A (Fin.append a v) (extend R η)})
        (v ∘ args)

/-- The operator a fixed-point body defines, its parameters held fixed. -/
def bodyOperator {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (body : RawFormula σ (k + m) (k :: ρ)) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    Set (Fin k → Fin A.size) → Set (Fin k → Fin A.size) :=
  fun R => {a | eval body A (Fin.append a v) (extend R η)}

/-- Two environments agree everywhere but at `r`, where they are ordered. -/
private def EnvLE {n : Nat} {ρ : List Nat} (r : Fin ρ.length)
    (η η' : RelationEnv n ρ) : Prop :=
  η r ⊆ η' r ∧ ∀ s, s ≠ r → η s = η' s

private theorem EnvLE.extend {n k : Nat} {ρ : List Nat} {r : Fin ρ.length}
    {η η' : RelationEnv n ρ} (h : EnvLE r η η') (R : Set (Fin k → Fin n)) :
    EnvLE (ρ := k :: ρ) r.succ (FixedPointSemantics.extend R η)
      (FixedPointSemantics.extend R η') := by
  refine ⟨h.1, fun s => ?_⟩
  refine Fin.cases (fun _ => rfl) (fun s (hs : Fin.succ s ≠ r.succ) => ?_) s
  exact h.2 s fun e => hs (congrArg Fin.succ e)

/-- A formula with the required polarity at `r` varies with `η r` accordingly: up when the
polarity is positive, down when it is negative. -/
private theorem eval_mono_polarity {σ : Vocabulary} {A : OrderedStructure σ} {m : Nat}
    {ρ : List Nat} (φ : RawFormula σ m ρ) (r : Fin ρ.length) (p : Bool)
    (hφ : φ.Admissible) (hp : φ.positiveAt r p) (v : Fin m → Fin A.size)
    {η η' : RelationEnv A.size ρ} (hη : EnvLE r η η') :
    (p = true → eval φ A v η → eval φ A v η') ∧
      (p = false → eval φ A v η' → eval φ A v η) := by
  induction φ generalizing p with
  | truth | equal | less | relation =>
    exact ⟨fun _ h => h, fun _ h => h⟩
  | @«variable» m ρ s args =>
    by_cases hs : s = r
    · subst hs
      have hpt : p = true := hp rfl
      refine ⟨fun _ h => hη.1 h, fun hf => absurd hpt (by simp [hf])⟩
    · have := hη.2 s hs
      simp only [eval, this]
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
    have hmono : ∀ η₀ : RelationEnv A.size _,
        Monotone (fun R => {a | eval body A (Fin.append a v) (extend R η₀)}) := by
      intro η₀ R R' hR a ha
      exact (ih 0 true hφ.1 hφ.2 _ (η := extend R η₀) (η' := extend R' η₀)
        ⟨hR, fun s => Fin.cases (fun h => absurd rfl h) (fun s _ => rfl) s⟩).1 rfl ha
    have hop : ∀ (R : Set (Fin k → Fin A.size)) (a : Fin k → Fin A.size),
        (p = true → eval body A (Fin.append a v) (extend R η) →
          eval body A (Fin.append a v) (extend R η')) ∧
        (p = false → eval body A (Fin.append a v) (extend R η') →
          eval body A (Fin.append a v) (extend R η)) :=
      fun R a => ih r.succ p hφ.1 hp _ (hη.extend R)
    refine ⟨fun e h => ?_, fun e h => ?_⟩
    · refine least (fun R => {a | eval body A (Fin.append a v) (extend R η)})
        (leastFixedPoint fun R => {a | eval body A (Fin.append a v) (extend R η')}) ?_ h
      intro a ha
      exact (fixedPoint _ (hmono η')).subset ((hop _ a).1 e ha)
    · refine least (fun R => {a | eval body A (Fin.append a v) (extend R η')})
        (leastFixedPoint fun R => {a | eval body A (Fin.append a v) (extend R η)}) ?_ h
      intro a ha
      exact (fixedPoint _ (hmono η)).subset ((hop _ a).2 e ha)

theorem positiveBodyMonotone {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (body : RawFormula σ (k + m) (k :: ρ))
    (hbody : body.Admissible) (hpositive : body.positiveAt 0 true)
    (A : OrderedStructure σ) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) : Monotone (bodyOperator body A v η) := by
  intro R R' hR a ha
  exact (eval_mono_polarity body 0 true hbody hpositive _
    (η := extend R η) (η' := extend R' η)
    ⟨hR, fun s => Fin.cases (fun h => absurd rfl h) (fun s _ => rfl) s⟩).1 rfl ha

/-- A pointed structure satisfies a formula. -/
def Satisfies {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k)
    (φ : Formula σ k) : Prop :=
  eval φ.val A.structureValue A.tuple (fun r => Fin.elim0 r)

/-- A query defined by one formula. -/
def Definable {σ : Vocabulary} {k : Nat} (Q : Query σ k) : Prop :=
  ∃ φ : Formula σ k, ∀ A, Q A ↔ Satisfies A φ

end DescriptiveComplexity.Strings.Lax.FixedPointSemantics
